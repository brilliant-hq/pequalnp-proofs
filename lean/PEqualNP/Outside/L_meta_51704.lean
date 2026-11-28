import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_51704_aux
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

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xeeeeeeeeeeeeeeeeaa00aa00aa00aa00eeeeeeeeeeeeeeeeaa00aa00aa00aa00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfafafafafafafafaaa00aa00aa00aa00fafafafafafafafaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfefefefefefefefeaa00aa00aa00aa00fefefefefefefefeaa00aa00aa00aa00
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_82 : Nat := 0x500050000000000050005
def goal_82 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_82 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffeeeeffffeeeecccc0000cccc0000ffffeeeeffffeeeecccc0000cccc0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_84 : Nat := 0x1100110000000000110011
def goal_84 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_84 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffffafafffffafaf0f00000f0f00000fffffafafffffafaf0f00000f0f00000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffffcfcfffffcfcfcfc0000fcfc0000fffffcfcfffffcfcfcfc0000fcfc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffefefffffefefcfc0000fcfc0000fffffefefffffefefcfc0000fcfc0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffaaaaffffaaaaaa00aa00aa00aa00ffffaaaaffffaaaaaa00aa00aa00aa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffeeeeffffeeeeeeccaa00eeccaa00ffffeeeeffffeeeeeeccaa00eeccaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffafafffffafafaf0aa00faf0aa00fffffafafffffafafaf0aa00faf0aa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffcfcfffffcfcfcfc0000fcfc0000fffffcfcfffffcfcfcfc0000fcfc0000
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffefefffffefefefcaa00fefcaa00fffffefefffffefefefcaa00fefcaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfafafafafafafafaaaaaaaaa00000000fafafafafafafafaaaaaaaaa00000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfcfcfcfcfcfcfcfccccccccc00000000fcfcfcfcfcfcfcfccccccccc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefefefefefeeeeeeeee00000000fefefefefefefefeeeeeeeee00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffaaffaaaaaaaaaaffaaffaaaa00aa00ffaaffaaaaaaaaaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccccccccccffccffcc00000000ffccffccccccccccffccffcc00000000
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeeeeeeeeeffeeffeeaa00aa00ffeeffeeeeeeeeeeffeeffeeaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffafafafafaffaaffaaaa00aa00fffafffafafafafaffaaffaaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefefefefeffeeffeeaa00aa00fffefffefefefefeffeeffeeaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffccccffffcccccccccccccccc0000ffffccccffffcccccccccccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffeeeeeeeeeeeecccc0000ffffeeeeffffeeeeeeeeeeeecccc0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafafffffafafafaaaaaf0f00000fffffafafffffafafafaaaaaf0f00000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcfffffcfcfcfcccccfcfc0000fffffcfcfffffcfcfcfcccccfcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefefffffefefefeeeeefcfc0000fffffefefffffefefefeeeeefcfc0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffaaaaffaaffaaaa00aa00ffffffaaffffaaaaffaaffaaaa00aa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffccccffccffcccccc0000ffffffccffffccccffccffcccccc0000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffeeeeffeeffeeeeccaa00ffffffeeffffeeeeffeeffeeeeccaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0fffff0f0fff0ff00f0f00000fffffff0fffff0f0fff0ff00f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffafafffaffaafaf0aa00fffffffafffffafafffaffaafaf0aa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcfffffcfcfffcffccfcfc0000fffffffcfffffcfcfffcffccfcfc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffefefffeffeefefcaa00fffffffefffffefefffeffeefefcaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeaa00aa00aa00aa00aa00aa00aa00aa00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeecccc0000cccc0000cccc0000cccc0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfefeeeeefefeeeeefefeeeeefefeeeeefcfc0000fcfc0000fcfc0000fcfc0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffccffccffccffccffccffccffccffcccccc0000cccc0000cccc0000cccc0000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeeeccaa00eeccaa00eeccaa00eeccaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffaffaafffaffaafffaffaafffaffaafaf0aa00faf0aa00faf0aa00faf0aa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffcffccfffcffccfffcffccfffcffccfcfc0000fcfc0000fcfc0000fcfc0000
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffeffeefffeffeefffeffeefffeffeefefcaa00fefcaa00fefcaa00fefcaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_161 : Nat := 0x30000000300000000000000000000000300000003
def goal_161 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeee00000000eeeeeeee00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_168 : Nat := 0x1010000010100000000000000000000010100000101
def goal_168 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_168 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffffccffccffffffffffccffccffccffcc00000000ffccffcc00000000
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xffffffffffccffccffffffffffccffccffccffcc00000000ffccffcc00000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffccccccccffffffffcccccccccccccccccccc0000cccccccccccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeeecccc0000eeeeeeeecccc0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffafaaaaafffffffffafaaaaafafaaaaaf0f00000fafaaaaaf0f00000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffcfcccccfffffffffcfcccccfcfcccccfcfc0000fcfcccccfcfc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffefeeeeefffffffffefeeeeefefeeeeefcfc0000fefeeeeefcfc0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffccffccffffffffffccffccffccffcccccc0000ffccffcccccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeeeccaa00ffeeffeeeeccaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffff0ff00fffffffffff0ff00fff0ff00f0f00000fff0ff00f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffcffccfffffffffffcffccfffcffccfcfc0000fffcffccfcfc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffeffeefffffffffffeffeefffeffeefefcaa00fffeffeefefcaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_193 : Nat := 0x3000000000000000300000000000000030000000000000003
def goal_193 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000
def roots_193 : List Nat := [xs256.getD 0 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_194 : Nat := 0x5000000000000000500000000000000050000000000000005
def goal_194 : Nat := 0xffffffffffffffffcccccccccccccccccccccccccccccccc0000000000000000
def roots_194 : List Nat := [xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaafafafafafafafafa0000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xffffffffffffffffccccccccccccccccfcfcfcfcfcfcfcfc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeefefefefefefefefe0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaaaaaaaaaaaaaaaaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffffccffccffccffcccccccccccccccccc0000000000000000
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffeeffeeffeeffeeeeeeeeeeeeeeeeeeaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xffffffffffffffffff00ff00ff00ff00f0f0f0f0f0f0f0f00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xffffffffffffffffffaaffaaffaaffaafafafafafafafafaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xffffffffffffffffffccffccffccffccfcfcfcfcfcfcfcfc0000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xffffffffffffffffffeeffeeffeeffeefefefefefefefefeaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaffffaaaaffffaaaa0000000000000000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffccccccccccccccccffffccccffffcccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeffffeeeeffffeeeecccc0000cccc0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffff0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffafaaaaafafaaaaafffffafafffffafaf0f00000f0f00000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffcfcccccfcfcccccfffffcfcfffffcfcfcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffefeeeeefefeeeeefffffefefffffefefcfc0000fcfc0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffffffffffffffff00ff00ff00ff00ffff0000ffff00000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffffaaaaffffaaaaaa00aa00aa00aa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffccffccffccffccffffccccffffcccccccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffffeeeeffffeeeeeeccaa00eeccaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffff0ff00fff0ff00fffff0f0fffff0f0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffaffaafffaffaafffffafafffffafafaf0aa00faf0aa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffcffccfffcffccfffffcfcfffffcfcfcfc0000fcfc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffeffeefffeffeefffffefefffffefefefcaa00fefcaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffffffffffffffffffcccccccccccccccccccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xffffffffffffffffffffffffaaaaaaaafafafafafafafafaaaaaaaaa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xffffffffffffffffffffffffccccccccfcfcfcfcfcfcfcfccccccccc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xffffffffffffffffffffffffeeeeeeeefefefefefefefefeeeeeeeee00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffffaaffaaffaaffaaaaaaaaaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffffccffccffccffccccccccccffccffcc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffeeffeeffeeffeeeeeeeeeeffeeffeeaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xffffffffffffffffffffffffff00ff00fff0fff0f0f0f0f0ff00ff0000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xffffffffffffffffffffffffffaaffaafffafffafafafafaffaaffaaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xffffffffffffffffffffffffffccffccfffcfffcfcfcfcfcffccffcc00000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xffffffffffffffffffffffffffeeffeefffefffefefefefeffeeffeeaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffffffaaaaaaaaffffaaaaffffaaaaaaaaaaaa00000000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffccccccccffffccccffffcccccccccccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffeeeeeeeeffffeeeeffffeeeeeeeeeeeecccc0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffafaaaaafffffafafffffafafafaaaaaf0f00000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffcfcccccfffffcfcfffffcfcfcfcccccfcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffefeeeeefffffefefffffefefefeeeeefcfc0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffaaffffaaaaffaaffaaaa00aa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffccffccffffffccffffccccffccffcccccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffeeffeeffffffeeffffeeeeffeeffeeeeccaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffffffff0ff00fffffff0fffff0f0fff0ff00f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffaffaafffffffafffffafafffaffaafaf0aa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffcffccfffffffcfffffcfcfffcffccfcfc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffeffeefffffffefffffefefffeffeefefcaa00
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
def isoMvS_82:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_82:Lower true dom_82 roots_82 goal_82 4:=lower_iso_b isoMvS_82 (by decide +kernel) lowS_41
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_41
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_41
def isoMvS_161:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_161:Lower true dom_161 roots_161 goal_161 4:=lower_iso_b isoMvS_161 (by decide +kernel) lowS_41
def isoMvS_168:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_168:Lower true dom_168 roots_168 goal_168 4:=lower_iso_b isoMvS_168 (by decide +kernel) lowS_41
def isoMvS_193:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_193:Lower true dom_193 roots_193 goal_193 4:=lower_iso_b isoMvS_193 (by decide +kernel) lowS_41
def isoMvS_194:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_194:Lower true dom_194 roots_194 goal_194 4:=lower_iso_b isoMvS_194 (by decide +kernel) lowS_41
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
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_slice_b [(0x4400440000000000440044,16,18)] (by decide +kernel) lowS_84
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
|0=>0x14815240925545514055248550405
|_=>0
def oO:Nat→Nat→Nat
|3,0=>0x20000
|4,0=>0x82620000004222
|5,0=>0xb1a1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfa7530
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>0x40
|4,0=>0x110021
|5,0=>0xed
|6,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_168 4 roots_168 ops++addP pm 1 dom_137 4 roots_137 ops++addP pm 2 dom_161 4 roots_161 ops++addP pm 3 dom_41 4 roots_41 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_169 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_161 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_41 _ g hchk
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
def isoMvS_54:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 4:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_51
def isoMvS_58:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 4:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_51
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 4:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_51
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 4:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_51
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_43
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_43
def isoMvS_89:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 4:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_51
def isoMvS_101:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 4:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_51
def isoMvS_102:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 4:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_51
def isoMvS_105:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_43
def isoMvS_106:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 4:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_51
def isoMvS_114:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_43
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_43
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 4:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_51
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 4:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_51
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_86
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_86
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_43
def isoMvS_195:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_86
def isoMvS_197:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 5:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_43
def isoMvS_198:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_43
def isoMvS_201:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_86
def isoMvS_202:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_43
def isoMvS_204:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 4:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_51
def isoMvS_209:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 5:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_43
def isoMvS_210:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_86
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_43
def isoMvS_216:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 4:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_51
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 5:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_86
def isoMvS_226:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_86
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
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
|0=>0x1f59040
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x8b
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_43 5 roots_43 ops++addP pm 1 dom_51 4 roots_51 ops++addP pm 2 dom_58 4 roots_58 ops++addP pm 3 dzo_43_16 5 roots_43 ops++addP pm 4 dom_41 4 roots_41 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_43_16_41 _ g hchk
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
theorem lowS_79:Lower true dom_79 roots_79 goal_79 5:=lower_slice_b [(0xcccc000000000000cccc,64,66)] (by decide +kernel) lowS_77
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_slice_b [(0xaa00aa0000000000aa00aa,64,65)] (by decide +kernel) lowS_86
theorem lowS_103:Lower true dom_103 roots_103 goal_103 5:=lower_slice_b [(0xaa000000aa000000aa000000aa,32,33)] (by decide +kernel) lowS_102
theorem lowS_107:Lower true dom_107 roots_107 goal_107 6:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c,32,34)] (by decide +kernel) lowS_105
def dzo_86_32:=0x550055000000000055005500000000
def gzo_86_32:=0x550054000000000054004400000000
def gsh_86_32:=0x5500540000000000540044
theorem lowS_zo_86_32_84:Lower true dzo_86_32 roots_86 gzo_86_32 5:=lower_iso_b (d1:=dom_86) (r1:=roots_86) (T1:=gsh_86_32) [(dom_86,32)] (by decide +kernel) (lower_slice_b (T:=gsh_86_32) [(0x4400440000000000440044,0,2)] (by decide +kernel) lowS_84)
namespace S_118
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,66),(4,20),(4,68),(6,22),(6,38),(6,70),(16,18),(16,20),(16,80),(32,34),(36,38),(36,52),(36,100),(48,50),(48,52),(48,112),(64,66),(64,68),(64,80),(96,98),(96,100),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_118.map (·&&&dom_118)
def gM:=goal_118&&&dom_118
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xa3e74
|5,0=>0xfe3b5
|6,0=>0x93d49
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x154015401540154015400000154000280028002800280028002800280028550055000000000055005500000000aa000000aa000000aa000000aa000110011001100110011001100110011028002800280028002800000028000550055005500550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8ea133a84688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 119 0x7fffffffffffffffffffffffffffff
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
addP pm 0 dom_114 5 roots_114 ops++addP pm 1 dom_102 4 roots_102 ops++addP pm 2 dzo_86_32 5 roots_86 ops++addP pm 3 dom_86 5 roots_86 ops++addP pm 4 dom_84 4 roots_84 ops++addP pm 5 dom_54 4 roots_54 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_118 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_86_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_54 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_114 5 s (0,roots_114.map (·&&&dom_114)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_118 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_114 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_118==dom_118)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_118 gM v ys):RunD true dom_118 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_118 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_118 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_118 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_118 roots_118 goal_118 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_118
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=S_118.noCircuit
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_slice_b [(0xc0c00000c0c000000000000000000000c0c00000c0c,32,34)] (by decide +kernel) lowS_169
namespace S_203
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(2,66),(2,130),(3,11),(3,67),(3,131),(8,9),(8,136),(10,11),(10,74),(10,138),(64,65),(64,66),(64,192),(72,73),(72,74),(72,200),(128,129),(128,130),(128,136),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_203.map (·&&&dom_203)
def gM:=goal_203&&&dom_203
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x8dfbc
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000000000000000f000000000000000f000000000000000f00c0c0000000000000c0c0000000000000c0c0000000000000c0ca0a0000000000000a0a0000000000000a0a0000000000000a0af0f00000000000000000000000000000f0f0000000000000000f0f0000000000000f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 204 0xfffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_202 5 roots_202 ops++addP pm 1 dom_139 5 roots_139 ops++addP pm 2 dom_201 5 roots_201 ops++addP pm 3 dom_195 5 roots_195 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_203 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_195 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_202 5 s (0,roots_202.map (·&&&dom_202)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_203 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_202 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_203==dom_203)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_203 gM v ys):RunD true dom_203 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_203 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_203 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_203 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_203 roots_203 goal_203 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_203
theorem lowS_203:Lower true dom_203 roots_203 goal_203 7:=S_203.noCircuit
theorem lowS_206:Lower true dom_206 roots_206 goal_206 6:=lower_slice_b [(0x5050000000000000505000000000000050500000000000005050,64,68)] (by decide +kernel) lowS_202
namespace S_213
def pG:List (Nat×Nat):=[(1,65),(1,129),(4,20),(4,68),(5,21),(5,69),(5,133),(16,20),(16,80),(17,21),(17,81),(17,145),(64,65),(64,68),(64,80),(64,192),(128,129),(128,192),(132,133),(132,148),(132,196),(144,145),(144,148),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_213.map (·&&&dom_213)
def gM:=goal_213&&&dom_213
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xabab
|4,0=>0x277b610b8804ea604a2f
|5,0=>0x64132406af2243c1e6141812b144480e07309fec05869057f0
|6,0=>0x724b8683d440e8c0a86a
|7,0=>0x724b8
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc00cc0000000000cc00cc0000000000c000c00000000000c000c330033000000000033003300000000003300330000000000000000cc00cc0000000000cc00000000000000cc00cc0000000000cc0000000330000000000000000000000000000003300000000000000000c000c00000000000c000800000000000c000c00000000000c000b30033000000000022002200000000003300330000000000220022c800c800000000000000000000000000c800c8000000000000000330000000000000033000000000000003300000000000000330000cc00c80000000000c000c00000000000cc00c80000000000c000c3000300000000000300030000000000030003000000000003000300000c400000000000000c000000000000000c400000000000000c330033000000000000000000000000003300330000000000000000cc00c80000000000cc00000000000000cc00c80000000000cc00033003300000000003000300000000000330033000000000030003088008800000000008800880000000000880088000000000088008b30033000000000033003300000000000000000000000000000000
|0,1=>0x30003000000000000000000000000000300030000000000000000000000000000000000000000000000000000cc00000000000000033003300000000003300330000000000000033000000000000000000000000000000000000000000000000cc00cc000000000088008800000000000000033002200000000000000000000000000330022cc00880000000000cc00880000000000cc00880000000000cc008b300220000000000000000000000000033002200000000000000000000cc00000000000000cc00000000000000cc000000000000000030003000000000003000000000000000300030000000000030000cc00cc0000000000cc00cc0000000000cc00000000000000cc000330033000000000033003300000000003300330000000000330000
|_,_=>0
def sP:Nat→Nat
|0=>0x20c1201060900879824020c12680832824020c12640830498020cab849641824020c1250083049302032202083048043cc1711a60918040564020ca48107090060948018820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682ced9ab2f654a918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 27 214 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x30121b205223503205a90891201
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x513200210000110100
|6,0=>0x817161
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0x3ff77d6244f30a080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x150400263
|6,0=>0x7a98
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_212 5 roots_212 ops++addP pm 1 dom_84 4 roots_84 ops++addP pm 2 dom_197 5 roots_197 ops++addP pm 3 dom_193 4 roots_193 ops++addP pm 4 dom_85 5 roots_85 ops++addP pm 5 dom_209 5 roots_209 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_213 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_209 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_212 5 s (0,roots_212.map (·&&&dom_212)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_213 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_212 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_213==dom_213)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_213 gM v ys):RunD true dom_213 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_213 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_213 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_213 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_213 roots_213 goal_213 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_213
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=S_213.noCircuit
theorem lowS_227:Lower true dom_227 roots_227 goal_227 6:=lower_slice_b [(0xa0000000a0000000a0000000a0000000a0000000a0000000a0000000a,32,33)] (by decide +kernel) lowS_226
def isoMvS_62:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 5:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_55
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 7:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_59
def isoMvS_93:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 7:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_59
def isoMvS_109:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 7:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_59
def isoMvS_115:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 6:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_107
def isoMvS_117:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 7:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_59
def isoMvS_121:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 7:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_59
def isoMvS_122:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_59
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 6:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_61
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 5:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_55
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 7:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_59
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 6:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_61
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 5:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_55
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_118
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 6:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_61
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 7:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_59
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_118
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 6:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_61
def isoMvS_199:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 6:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_87
def isoMvS_205:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 7:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_118
def isoMvS_211:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 7:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_203
def isoMvS_214:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 7:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_203
def isoMvS_217:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 7:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_118
def isoMvS_218:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 7:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_118
def isoMvS_220:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 7:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_59
def isoMvS_229:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 7:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_118
def isoMvS_230:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 7:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_118
def isoMvS_233:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_171
def isoMvS_234:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 7:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_203
def isoMvS_236:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 7:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_59
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 7:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_118
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccccccccccccccccccc,126),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 7:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_203
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xf0f0f0f0f0f0f0f0,16,20)] (by decide +kernel) lowS_59
theorem lowS_95:Lower true dom_95 roots_95 goal_95 8:=lower_slice_b [(0xcccccccc00000000cccccccc,16,18)] (by decide +kernel) lowS_93
theorem lowS_111:Lower true dom_111 roots_111 goal_111 8:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc,32,34)] (by decide +kernel) lowS_109
def dzo_87_32:=0xff00ff0000000000ff00ff00000000
def gzo_87_32:=0xff00fe0000000000fe00ee00000000
def gsh_87_32:=0xff00fe0000000000fe00ee
theorem lowS_zo_87_32_84:Lower true dzo_87_32 roots_87 gzo_87_32 6:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_32) [(dom_87,32)] (by decide +kernel) (lower_slice_b (T:=gsh_87_32) [(0xaa00aa0000000000aa00aa,0,1),(0xcc00cc0000000000cc00cc,0,2)] (by decide +kernel) lowS_84)
namespace S_119
def pG:List (Nat×Nat):=[(1,33),(1,65),(2,18),(2,34),(2,66),(3,19),(3,35),(3,67),(4,20),(4,68),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,23),(7,39),(7,71),(16,18),(16,20),(16,80),(17,19),(17,21),(17,49),(17,81),(32,33),(32,34),(36,37),(36,38),(36,52),(36,100),(48,49),(48,50),(48,52),(48,112),(64,65),(64,66),(64,68),(64,80),(96,97),(96,98),(96,100),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_119.map (·&&&dom_119)
def gM:=goal_119&&&dom_119
def NN:Nat→Nat
|4=>5
|5=>15
|6=>37
|7=>10
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xe7e0dcefe6a65d7559a226c99
|5,0=>0xe1eecd8193d7806cf4d8b55d4a8e4890cd65ab19588555473d3ad1137f5a28b6e1dc8b1b6e6
|6,0=>0xfeae0fd584faed6f89ecf89d7f3e42eba18dae64bce6cbcd62bc114b65c6b23e2a8e48905458bd48894b181b677c0d07925f73eed72e6b6dff2633535d38a57d3a4f84745218442063eb1e3a3dc36d7e2c6f42b7ce219941fbc91f0fd
|7,0=>0xf2fd6e8d9fd5f9ecfbaacc518c5484c28926aedf5d38a093c2
|8,0=>0xdaa04
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000f000f0000000000000000ff000000ff00000000000000000000ff00f000ff00f000ff00f000ff00f0ff00ff00ff00ff00f000f000f000f000000f0000000f000f0000000f00000000ff000000ff00ff000000ff0000cc00cc00cc00cc00cc00cc00cc00ccff000000ff000000ff000000ff0000fe00fe00fe00fe00fe00ee00fe00eefc00fc00fc00fc00fc00cc00fc00ccff00ff00ff00ff0000000000000000ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff000000ff0000ff00cc00ff00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa0f000f000f000f000f0000000f0000
|0,1=>0xf000f000f000f000ff00f000ff00f0f0000000f0000000ff000000ff0000ff00ff00ff00ff00ff00f000ff00f0ff00ff000f000f00ff00ff00000000ff00ff00ff000000ff00ff00000000ff00f000ff00f000f000f000f000f00000000000000000ff000000ff00000000ff000000ff0000000000000000ff000f00ff000f00ff000000ff0000f000f000f000f000f0000000f000000000000000000000ff00ff00000000ff00ff00ff00ff000f0000000f0000ff00ff00ff00ff00ff00ff000000000000000000000000ff00f000ff00f0f000f000f000f000f000f000f000f00f0000000f0000000f0000000f0000
|0,2=>0xff00aa00ff00aa00aa00aa00aa00aa0000ff0000000000ff00ff000000000000f0000000f000f000f000f000f0ff00ff000000ff00ff00ff0000000000000000000000000f0000000f0000ff00000000000000ff00ff00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2411445c844904510d6512411440da24110a4490532090401445c90501442060451082410055482410051032912411034420442090543d34884490440c81811440c90503c40c904038434330904428904b1032412c42890401081c61440c2040
|1=>0x44904510d0d12411447c84490451087912411440c844904f10844204510320c44904474844904511944905810321124115c2112411440d12413950c84490451082414053db2112411442162411443483090451084490401440c82410054c8651
|2=>0x15521124114421124114e10321124115321124114421126514421a2411532112414059084490451088c90454cd2112411444884490455486512411622112411440c85890451084490541442112418458084490451082410051034490501530c8
|3=>0x421124114421944904510844904560421124114f10831124114421124140510d211241
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a94caa5f62cb15149cc4862130f546ec31615b09583ec196
|6,0=>0x15f6acb549e98d4669fbce1e62f2b6923c75e2cf10685340ddf8ef57773b9ddc0eda669bb31d8ccbf75cb2cd958ea574fb265924e8b74239f5cece6f7
|7,0=>0x344f9b7ca3e35f0cf7f7bcb5c9ed6f656
|8,0=>0x1a96
|_,_=>0
def wAt:=mkWire dB 38 120 0xffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x817205911644548472114417205081510541392051139205041510ec81444ec8141054461205846320583472054815205483f20549392050815205c81610f51162054814205443920503442054815205d1392054814658481720596250d1081524e48152050815
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xa31cc00000430000000013000000000000001
|6,0=>0x2f2b4ac1a8a829c40000252000000023284a01001f1001e1745b26840060800589424c400448f20000038400000d1
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xfafe9ebfadeaf6fca721384e0344a5220842088018c481082f08c2104c0a0200700800
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1ce0008000940008004
|6,0=>0x1298e902019408014329a403df120269aadc0a20201b003
|7,0=>0x35bc66d6c6f57
|8,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_118 7 roots_118 ops++addP pm 1 dom_51 4 roots_51 ops++addP pm 2 dom_83 5 roots_83 ops++addP pm 3 dom_115 6 roots_115 ops++addP pm 4 dom_101 4 roots_101 ops++addP pm 5 dom_117 7 roots_117 ops++addP pm 6 dom_103 5 roots_103 ops++addP pm 7 dom_55 5 roots_55 ops++addP pm 8 dzo_87_32 6 roots_87 ops++addP pm 9 dom_87 6 roots_87 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_119 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_87_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_87 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_118 7 s (0,roots_118.map (·&&&dom_118)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_119 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_118 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_119 gM v ys):RunD true dom_119 gM v (ori ys):=h
def Z (s:Nat):=barP dom_119 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 37 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 37 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 10 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 0 = true)
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
def dzo_115_8:=0xf000f000f000f000f000f000f000f00
def gzo_115_8:=0xf000f000f000e000f000f000e000a00
def gsh_115_8:=0xf000f000f000e000f000f000e000a
theorem lowS_zo_115_8_82:Lower true dzo_115_8 roots_115 gzo_115_8 6:=lower_iso_b (d1:=dom_115) (r1:=roots_115) (T1:=gsh_115_8) [(dom_115,8)] (by decide +kernel) (lower_slice_b (T:=gsh_115_8) [(0xa000a000a000a000a000a000a000a,0,1),(0xf000f00000000000f000f00000000,0,32)] (by decide +kernel) lowS_82)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,40),(10,11),(10,26),(10,42),(10,74),(16,18),(16,80),(17,19),(17,25),(17,49),(17,81),(24,25),(24,26),(24,56),(24,88),(32,33),(32,34),(32,40),(48,49),(48,50),(48,56),(48,112),(64,65),(64,66),(64,80),(72,73),(72,74),(72,88),(72,104),(96,97),(96,98),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>6
|_,_=>0
def wAt:=mkWire dB 6 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0x3f80
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_121 7 roots_121 ops++addP pm 2 dom_59 7 roots_59 ops++addP pm 3 dom_91 7 roots_91 ops++addP pm 4 dom_115 6 roots_115 ops++addP pm 5 dzo_115_8 6 roots_115 ops++addP pm 6 dom_107 6 roots_107 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_115_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_107 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 7 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
  · simp [NN] at hi
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
def dzo_109_16:=0x33330000333300003333000033330000
def gzo_109_16:=0x33330000333300003332000032300000
def gsh_109_16:=0x3333000033330000333200003230
theorem lowS_zo_109_16_41:Lower true dzo_109_16 roots_109 gzo_109_16 6:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_16) [(dom_109,16)] (by decide +kernel) (lower_slice_b (T:=gsh_109_16) [(0x3030000030300000303000003030,0,4),(0x3333000033330000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_57_4:=0x3030303030303030
def gzo_57_4:=0x3030302030302000
def gsh_57_4:=0x303030203030200
theorem lowS_zo_57_4_41:Lower true dzo_57_4 roots_57 gzo_57_4 5:=lower_iso_b (d1:=dom_57) (r1:=roots_57) (T1:=gsh_57_4) [(dom_57,4)] (by decide +kernel) (lower_slice_b (T:=gsh_57_4) [(0x303000003030000,0,16)] (by decide +kernel) lowS_41)
def dzo_116_8:=0x11001100110011001100110011001100
def gzo_116_8:=0x11001100110010001100110010000000
def gsh_116_8:=0x110011001100100011001100100000
theorem lowS_zo_116_8_84:Lower true dzo_116_8 roots_116 gzo_116_8 5:=lower_iso_b (d1:=dom_116) (r1:=roots_116) (T1:=gsh_116_8) [(dom_116,8)] (by decide +kernel) (lower_slice_b (T:=gsh_116_8) [(0x110011000000000011001100000000,0,32)] (by decide +kernel) lowS_84)
def dzo_45_16:=0x3333000033330000
def gzo_45_16:=0x3332000032300000
def gsh_45_16:=0x333200003230
theorem lowS_zo_45_16_41:Lower true dzo_45_16 roots_45 gzo_45_16 5:=lower_iso_b (d1:=dom_45) (r1:=roots_45) (T1:=gsh_45_16) [(dom_45,16)] (by decide +kernel) (lower_slice_b (T:=gsh_45_16) [(0x303000003030,0,4)] (by decide +kernel) lowS_41)
def dzo_92_32:=0x11111111000000001111111100000000
def gzo_92_32:=0x11111110000000001110110000000000
def gsh_92_32:=0x111111100000000011101100
theorem lowS_zo_92_32_84:Lower true dzo_92_32 roots_92 gzo_92_32 5:=lower_iso_b (d1:=dom_92) (r1:=roots_92) (T1:=gsh_92_32) [(dom_92,32)] (by decide +kernel) (lower_slice_b (T:=gsh_92_32) [(0x110011000000000011001100,0,8)] (by decide +kernel) lowS_84)
def dzo_105_4:=0x3030000030300000303000003030
def gzo_105_4:=0x3030000030300000302000002000
def gsh_105_4:=0x303000003030000030200000200
theorem lowS_zo_105_4_41:Lower true dzo_105_4 roots_105 gzo_105_4 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_4) [(dom_105,4)] (by decide +kernel) (lower_slice_b (T:=gsh_105_4) [(0x303000003030000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_121_4:=0x30303030303030303030303030303030
def gzo_121_4:=0x30303030303030303030302030302000
def gsh_121_4:=0x3030303030303030303030203030200
theorem lowS_zo_121_4_41:Lower true dzo_121_4 roots_121 gzo_121_4 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_4) [(dom_121,4)] (by decide +kernel) (lower_slice_b (T:=gsh_121_4) [(0x3030000030300000303000003030000,0,16),(0x3030303030303030000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_117_8:=0x33003300330033003300330033003300
def gzo_117_8:=0x33003300330032003300330032002200
def gsh_117_8:=0x330033003300320033003300320022
theorem lowS_zo_117_8_84:Lower true dzo_117_8 roots_117 gzo_117_8 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_8) [(dom_117,8)] (by decide +kernel) (lower_slice_b (T:=gsh_117_8) [(0x220022002200220022002200220022,0,1),(0x330033000000000033003300000000,0,32)] (by decide +kernel) lowS_84)
def dzo_85_8:=0x330033000000000033003300
def gzo_85_8:=0x330032000000000032002200
def gsh_85_8:=0x3300320000000000320022
theorem lowS_zo_85_8_84:Lower true dzo_85_8 roots_85 gzo_85_8 5:=lower_iso_b (d1:=dom_85) (r1:=roots_85) (T1:=gsh_85_8) [(dom_85,8)] (by decide +kernel) (lower_slice_b (T:=gsh_85_8) [(0x2200220000000000220022,0,1)] (by decide +kernel) lowS_84)
def dzo_93_32:=0x33333333000000003333333300000000
def gzo_93_32:=0x33333332000000003332332200000000
def gsh_93_32:=0x333333320000000033323322
theorem lowS_zo_93_32_84:Lower true dzo_93_32 roots_93 gzo_93_32 6:=lower_iso_b (d1:=dom_93) (r1:=roots_93) (T1:=gsh_93_32) [(dom_93,32)] (by decide +kernel) (lower_slice_b (T:=gsh_93_32) [(0x222222220000000022222222,0,1),(0x330033000000000033003300,0,8)] (by decide +kernel) lowS_84)
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(4,20),(4,68),(5,13),(5,21),(5,37),(5,69),(8,9),(8,40),(12,13),(12,28),(12,44),(12,76),(16,20),(16,80),(17,21),(17,25),(17,49),(17,81),(24,25),(24,28),(24,56),(24,88),(32,33),(32,40),(36,37),(36,44),(36,52),(36,100),(48,49),(48,52),(48,56),(48,112),(64,65),(64,68),(64,80),(72,73),(72,76),(72,88),(72,104),(96,97),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|4=>1
|5=>3
|6=>9
|7=>18
|8=>10
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x2851c
|5,0=>0x434b32fd5319808
|6,0=>0xfbe8cecf4a4c00937d1f2c57f245cf173500784d0170c
|7,0=>0x8e226592ef56fe25336643d003e634300df2faee29a611f9761f1a21aadc18ecb0d89108ea50404a02f7100ab4
|8,0=>0xc4d75c2f648e2267f2e4534134624f228b5213f10f7ba067c2
|9,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc88cc88cc88cc88cc88cc88cc88cc880003333222233330000000022222222cccccccccccccccccccc0000cccc00000220022002200220022002200220022cccc0000cccc0000cccc0000cccc0000303030303030303030300000303000000000000cc88cc8800000000cc88cc880003333000033330000303000003030cc88cc8800000000cc88cc88000000033003300330033003300330033003300cccc0000cccc0000c0c00000c0c000033333333000000003333333300000000cccccc00cccc8800ccc0cc00c8c0880303030303030303030303030303030308888888888888888888888888888888b3333333333333330000000000000000
|0,1=>0xcccc0000cccc00000000000000033333333330033003333333333003300cc44cc44cc44cc44000000000000000030303030303030300000000000000008c8c8c8c8c8c8c8c888888888888888b3330022333300223333002233330022cccccccccccccccc888888888888888a2222222222222220000000000000000444444444444444488888888888888880330033002200220033003300220022cccccccc88888888cccccccc8888888b3333030333330303333303033333030cc00cc0088008800cc00cc00880088033333333333333333030303030303030c0c0c0c0c0c0c0c0c0c00000c0c000000000000222222220000000022222222
|0,2=>0xcccc8888cccc8888cccc8888cccc888b330333033303330333033303330333000000000cccccccc000000000000000330033003333333333003300330033000000000000000000888888888888888911111111111111100000000000000000000888800008888000088880000888b03010103030101030301010303010104444000044440000cccc0000cccc00032323232323232323030303030303030
|_,_=>0
def sP:Nat→Nat
|0=>0x4010b18265810b1820407551142c60810042c64820500042c609b04011a2c60810042c60995c42c60971142c205600450b4c20402c71920810042c644140010b3c604a0042c608138010b18128c00b1812890071820480071821410040c2040
|1=>0x42c6081004a4b18204010ba060810042c60818c07842c608101510b18204010b1820407042c609904010b98204010b18205001c10b1829645442c648204010b4c204010b1a204012118204010b1a00407842c608101f10b18128078450b182
|2=>0x10b18204010b1820409042c608101810b182641
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x45816c056
|6,0=>0x4d6242905c74e337163895c3ce177
|7,0=>0x190ec265d42d19590a66503269928c8c84331fa0f0c71734c1860b4e537
|8,0=>0x21af0677fbbe59e4eeb7723b75dacecf7
|9,0=>0x1146
|_,_=>0
def wAt:=mkWire dB 42 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x4081000404b051824b0610644050808191040869d1008406080810304082011015518101428f2c18b63040026104004192c08d0b2c04b0910641010400033181840508b420110181710808b3118199630404100658c101040151b10155181014f1018144063420b01342cb01342cb01
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1031a62c84907208608800002
|7,0=>0x1a9332624bc9692b25249c9292324247c8e91b23245c8a9132
|8,0=>0x1f8be17a2001e0bb1742e45c0b71
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x940cd8444441019382dd31009130091025d0d8ed0c7ed0895f0857d0704101dfd01c6d00edd00cdd00c4d00bdf00bdd007fd005fd0045d00419003fd003ed001dd0004d000400000e0000100000
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x73042110c03
|7,0=>0x17642b582be5d8ccf4cf215
|8,0=>0x16b5a5b767b6e
|9,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 20 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 7 roots_121 ops++addP pm 1 dzo_109_16 6 roots_109 ops++addP pm 2 dom_109 7 roots_109 ops++addP pm 3 dom_93 7 roots_93 ops++addP pm 4 dom_124 6 roots_124 ops++addP pm 5 dzo_57_4 5 roots_57 ops++addP pm 6 dom_117 7 roots_117 ops++addP pm 7 dzo_116_8 5 roots_116 ops++addP pm 8 dzo_45_16 5 roots_45 ops++addP pm 9 dzo_92_32 5 roots_92 ops++addP pm 10 dom_61 6 roots_61 ops++addP pm 11 dzo_105_4 5 roots_105 ops++addP pm 12 dzo_121_4 6 roots_121 ops++addP pm 13 dom_105 5 roots_105 ops++addP pm 14 dzo_117_8 6 roots_117 ops++addP pm 15 dzo_85_8 5 roots_85 ops++addP pm 16 dzo_93_32 6 roots_93 ops++addP pm 17 dom_84 4 roots_84 ops++addP pm 18 dom_41 4 roots_41 ops++addP pm 19 dom_85 5 roots_85 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_109_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_57_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_116_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_45_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_92_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_105_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_121_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_117_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_85_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_93_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_85 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 7 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_125==dom_125)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 18 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
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
def dzo_171_16:=0xf0f00000f0f000000000000000000000f0f00000f0f0000
def gzo_171_16:=0xf0f00000f0e000000000000000000000f0e00000e0c0000
def gsh_171_16:=0xf0f00000f0e000000000000000000000f0e00000e0c
theorem lowS_zo_171_16_169:Lower true dzo_171_16 roots_171 gzo_171_16 8:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_16) [(dom_171,16)] (by decide +kernel) (lower_slice_b (T:=gsh_171_16) [(0xc0c00000c0c000000000000000000000c0c00000c0c,0,2)] (by decide +kernel) lowS_169)
namespace S_187
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(2,18),(2,34),(2,130),(3,11),(3,19),(3,35),(3,131),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,138),(16,18),(17,19),(17,25),(17,49),(17,145),(24,25),(24,26),(24,56),(24,152),(32,33),(32,34),(32,40),(32,160),(48,49),(48,50),(48,56),(48,176),(128,129),(128,130),(128,136),(128,160),(144,145),(144,146),(144,152),(144,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_187.map (·&&&dom_187)
def gM:=goal_187&&&dom_187
def NN:Nat→Nat
|4=>3
|5=>15
|6=>35
|7=>15
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x7100e541173d10b
|5,0=>0xc88cd870774d49f4706839f513728933d2f317db312fb17fba0ed5a0e7fc0d9d207afe038bf
|6,0=>0xe74b9d359cae7e48ac5d848d0803426ca926473b6425b5b7f4586c64b06c47a2f4416842ab23f1c03e51f3dede39f512ed982df9b2d2bb283f3275002550a2330c1f1931de0b15cee13fb60b4ce08cf20780003c490252b
|7,0=>0xf79787d43f5a460523a54f67f4641f4519f35ff7308282e55a2b4d122f9a1705f06719064fc
|8,0=>0xe5ea9d514626f6b
|9,0=>0x3dbb0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0000000000000000000000000f0f0f0f00000000f0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000000000000000000f0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0f0f0f0f0f0f0f00000000000000000f0a0f0a0f0a0f0af0f0f0f0e0e0e0e00000000000000000f0c0f0c0e0c0e0cf000f000f000f0000000000000000000f000f000f000f00a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000f0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0f0af0f0f0f0a0a0a0a00000000000000000f000f000a000a00f0f0f0f0a0a0a0a00000000000000000f0f0f0f0a0a0a0af0f00000f0f000000000000000000000f0f00000f0f0000f0f0f0f0f0f0f0f00000000000000000f000f000f000f00c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0cf0f0f0f0f000f0000000000000000000a0a0a0a0a000a00
|0,1=>0xf0f0f0f0f0f0f0f0000000000000000000f000f000a000af000f000f000f0000000000000000000f000f000a000a0000000000000000000000000000000000f0f0f0f0f0a0f0aa0a0a0a0f0f0f0f00000000000000000a0a0a0a0f0a0f0a00000000000000000000000000000000f0f0f0f0f000f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f0000f000f000f000f0000000000000000000f000f000a000af0f0f0f0f0a0f0a00000000000000000f0f0f0f0f0a0f0af0f0f0f0f0c0f0c00000000000000000e0e0e0e0e0c0e0c50505050505050500000000000000000505050505000500a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a000a0000f000f000f000f0000000000000000000f000f0000000000000000f0f0f0f0000000000000000000000000f000f0050505050505050500000000000000000505050500000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0a0a0a0a50505050500050000000000000000000505050505000500
|0,2=>0xf000f000a000a0000000000000000000f000f000a000a00000000000000000000000000000000f0f0f0f0a0a0a0af050f050f050f0500000000000000000f050f050f000f000050005000500050000000000000000000500050000000000f000f000f000f0000000000000000000a000a000a000af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0a0f0a00000000505050500000000000000000000000005000500
|_,_=>0
def sP:Nat→Nat
|0=>0x64d3c32412003473c32413923040c204834f0c61413470c91412183c308138f0c95c834f0c905634f0c15543513c318204c1c318138f0c604e4cc0c204848c44308120c1030813870c204840f0c914138c1c32c12070ca2481c31850440c2040
|1=>0x3c318904d84f0c904834f0de04834f0c904880d3c324121f34f0c90563443c378120d74f0c904834f0c905c20d3032412123443c318204d3070c604834c3c324158d3110c90483470c904840d10f0cb24135b3c318120d30f0c121434f0c9048
|2=>0x483443c318904d30f0c20483653c324120d1cf0c224120c10324120d1cf0de04834c10318134c1c308120f0e424120d68f0c90563473c304864d68f0c121434c1c32413883c32413884c73c32c90483c32412233443c324188d44f0de048351
|3=>0x3c324120d1cf0c904834f0c624120d30f0c90483473c32412123473c31890483443c308904834f0c904898d3c32412123513c324120d60f0c904835110f0c904835a1cf0c904835830f0c9
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x18d8bac57628b12d88ac3f61cb0cd85ac27610b06d82ac0f6
|6,0=>0x54de9ad476a03ce5e64f2b7923c75e2cf0f7843c05df4ef3776b399dbeed96693b2dd88ebd75b3abdd50ea174d3a4dd18e8573f39ddce0e697
|7,0=>0x7063731b18d53e8df38f957c6c6162fb1767b7bda1ec2f5a7
|8,0=>0x75dfa0fc97
|9,0=>0x1de6
|_,_=>0
def wAt:=mkWire dB 39 188 0xfffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x24f423f349422124d494a1c8cf35389c83510d483d449043520f442720f5a2330d493d449043560dc63d24847233cd4f35688cc3538f4835308c93d088493530dc93d689cc3524f4e3020d493d1c8cd3d102083d24d421020f4935308493d1c84d3d3cd4e3d20d421020f493518d4921
|1=>0xf35248493d1c8cf353cd492120f4935109c83d1c8cf3510d483d18f492110d483d1c94f35308493d20f492124d493d10dc83d34f49353c8493d44907213cd4f2520f49213c94d3d24d47233cd4c3524f51271c84f35689cc35
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x3cc618a2000000000820e20000005200000011802
|6,0=>0x13ce61c938e514a11bf3000f49d93836c4001a1000626001792c35449cc00252000905112023c4708d117300050c91000
|7,0=>0x1b8b616a2d0598b21622c0578ae15a2b0558aa1522
|8,0=>0x1c8788f01
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x5cf5af59f45c3e73a72c72411ef1bf1af1a719f18d0bf0ab08b08908308108004502e02802202001000c008004002000
|1=>0xdafc285ff
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x41c6000002140002000201
|6,0=>0xf4d408335800304e04008048018c0cb0020050821810ca015200
|7,0=>0x104497958a085971d6de69f
|8,0=>0x15597
|9,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_171 8 roots_171 ops++addP pm 1 dom_155 7 roots_155 ops++addP pm 2 dom_179 7 roots_179 ops++addP pm 3 dom_186 7 roots_186 ops++addP pm 4 dom_178 5 roots_178 ops++addP pm 5 dom_59 7 roots_59 ops++addP pm 6 dom_147 4 roots_147 ops++addP pm 7 dzo_171_16 8 roots_171 ops++addP pm 8 dom_169 7 roots_169 ops++addP pm 9 dom_51 4 roots_51 ops++addP pm 10 dom_154 4 roots_154 ops++addP pm 11 dom_58 4 roots_58 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_187 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_171_16_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_58 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_171 8 s (0,roots_171.map (·&&&dom_171)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_187 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_171 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff00000000ffffffff00000000,96),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_187==dom_187)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_187 gM v ys):RunD true dom_187 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_187 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 35 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 15 0 = true)
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
def dzo_139_4:=0xf0f00000000000000000000000000000f0f0
def gzo_139_4:=0xf0e00000000000000000000000000000a000
def gsh_139_4:=0xf0e00000000000000000000000000000a00
theorem lowS_zo_139_4_139:Lower true dzo_139_4 roots_139 gzo_139_4 5:=lower_iso_b (d1:=dom_139) (r1:=roots_139) (T1:=gsh_139_4) [(dom_139,4)] (by decide +kernel) (lower_slice_b (T:=gsh_139_4) [] (by decide +kernel) lowS_139)
def dzo_201_4:=0x3030000000000000303000000000000030300000000000003030
def gzo_201_4:=0x3030000000000000302000000000000030300000000000002000
def gsh_201_4:=0x303000000000000030200000000000003030000000000000200
theorem lowS_zo_201_4_137:Lower true dzo_201_4 roots_201 gzo_201_4 5:=lower_iso_b (d1:=dom_201) (r1:=roots_201) (T1:=gsh_201_4) [(dom_201,4)] (by decide +kernel) (lower_slice_b (T:=gsh_201_4) [(0x303000000000000000000000000000003030000000000000000,0,64)] (by decide +kernel) lowS_137)
def dzo_203_4:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0
def gzo_203_4:=0xf0f0000000000000f0e0000000000000f0f0000000000000a000
def gsh_203_4:=0xf0f0000000000000f0e0000000000000f0f0000000000000a00
theorem lowS_zo_203_4_139:Lower true dzo_203_4 roots_203 gzo_203_4 6:=lower_iso_b (d1:=dom_203) (r1:=roots_203) (T1:=gsh_203_4) [(dom_203,4)] (by decide +kernel) (lower_slice_b (T:=gsh_203_4) [(0xf0f00000000000000000000000000000f0f0000000000000000,0,64)] (by decide +kernel) lowS_139)
namespace S_207
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(2,66),(2,130),(3,11),(3,67),(3,131),(4,68),(5,13),(5,69),(5,133),(6,70),(6,134),(7,15),(7,71),(7,135),(8,9),(8,136),(10,11),(10,74),(10,138),(12,13),(12,76),(12,140),(14,15),(14,78),(14,142),(64,65),(64,66),(64,68),(64,192),(72,73),(72,74),(72,76),(72,200),(128,129),(128,130),(128,136),(128,192),(132,133),(132,134),(132,140),(132,196)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_207.map (·&&&dom_207)
def gM:=goal_207&&&dom_207
def NN:Nat→Nat
|3=>1
|4=>30
|5=>85
|6=>62
|7=>14
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x13e51
|4,0=>0xf2a33ee4a5e720ce6066dce5ec8337c285bbbafaa29117a34b776907298f6f59d66c93643205aaac55a7a54cbe497032961327fbb220f91cdda174af118d80e55d07e3f05ae703440015ad
|5,0=>0xff6cffede8fe1acf7adaf1374f0a47eeb62ed546eb106de7d7d733cd56c8d4e51d2a99d0789cd18dcc67bcc470cac3bc7d6fc742cc608cc3c5ec35bac23dfc08a1bf0fdbc2c4b9c78b61b4b5b68b1581afbdca8e92a7b00a33d39f10d9ccad9c5459c1ce95d5c94a818feea8a9bb7d74474f3b6fb3c6df0e62f666139f5dc475ca5c5ac3956cb44c09d48cac45875442ad440293d167387fc33289327032fc992f3122e0142c7cf2aceb270ae2606e24d5d2133616a7210bfc10b710ee6f0c6770b676084fc07f31037a3036c802e6d02d9000a2c
|6,0=>0xfaf44f69d5f6215f3943eea45ea52de9519e2b33dd16fdd03bdbf78d56fdc9a8ac460fc39fcc276fc0d50bc016b5da8b09a9af788aeb87acb37a7faca446ba0e0a9f3209dee69baa691fc091d0a8f1778e9918e61280f4380e567e50e7db2d771be6ea556a972698b4689c764cd0639b35ad7351c2a50fee4d64d495cc478ca466fc441b627c93258db1f6441efd5163fc136e30d2dd083df022f2
|7,0=>0xe18edd7b68c9b4cc25deb00f0aa0629c40e5f21e3c9222eeae1f9cf0e83105caa025ca
|8,0=>0x22f88
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff000000000000ffff0000000000000f0f0000000000000000ffff000000000000ff00000000000000ffff000000000000ff00cccc000000000000cccc000000000000cccc000000000000ccccffff000000000000ffaa000000000000aaaa000000000000aaaaffff000000000000aaaa000000000000ffff000000000000aaaaeeee000000000000eeee000000000000eeee0000000000000000ffff000000000000ffcc000000000000cccc000000000000ccccff00000000000000ff00000000000000ff00000000000000ff00aaaa000000000000aaaa000000000000aaaa000000000000aaaaffff0000000000000000000000000000ffff00000000000000001313000000000000111100000000000003030000000000000000ffff000000000000ffff00000000000000000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0eeee000000000000eeee000000000000eeee000000000000eeeeffff000000000000ff00000000000000aaaa000000000000aa00ffff000000000000ffff000000000000ffff0000000000000000
|0,1=>0xffff000000000000eeee000000000000cccc000000000000cccc5555000000000000555500000000000054540000000000005454111100000000000011110000000000000000000000000000000000000000000000000000000000000000ffff000000000000aaaaffff0000000000000000000000000000fefe00000000000000000333000000000000003300000000000003030000000000000000ffff000000000000ffff000000000000afaf000000000000aaaabbbb000000000000bbbb000000000000abab000000000000aaaaffff000000000000ffaa000000000000ff00000000000000ff00ffff000000000000ffff000000000000ffff000000000000ff0000000000000000000000000000000000afaf000000000000aaaaffff000000000000ffff000000000000ff00000000000000ff00111100000000000011110000000000000101000000000000000000000000000000000000000000000000fefe000000000000fefe3333000000000000333300000000000023230000000000002222ffff000000000000ffff000000000000aaaa000000000000aaaa
|0,2=>0xaa000000000000aaaa000000000000aaaa0000000000000000ffff0000000000000000000000000000ff00ffff00000000000000ff000000000000ffff00000000000000aaefef000000000000eeee000000000000efef000000000000eeeeffff000000000000ffff000000000000fafa000000000000fafa00ff00000000000000ff00000000000000aa00000000000000aaaaaa000000000000aaaa000000000000aaaa000000000000aa0033330000000000003333000000000000333300000000000033000f0f00000000000000000000000000000f0f0000000000000000ffff000000000000ff000000000000000000000000000000000000ff00000000000000ff00000000000000ff00000000000000aaafaf000000000000aaaa000000000000afaf000000000000aaaafefe000000000000fefe000000000000fefe000000000000fefeffff000000000000ffff000000000000ffff000000000000aaaa0fff00000000000000ff0000000000000faf00000000000000aa000000000000000000ff000000000000ffff000000000000ff00
|0,3=>0xffff0000000000005555000000000000ffff0000000000000000ffff00000000000000ff000000000000ffff0000000000000000f0ff000000000000f0ff000000000000f0fa000000000000f0fa3333000000000000333300000000000033330000000000002222bbbb000000000000bbbb000000000000bbbb000000000000aaaa3333000000000000333300000000000003030000000000000000ffff000000000000aaaa000000000000000000000000000000005f5f00000000000055550000000000000f0f000000000000000033330000000000000033000000000000333300000000000000000fff00000000000000ff0000000000000f0f000000000000000055550000000000005555000000000000050500000000000000005555000000000000555500000000000055550000000000005500111100000000000011110000000000001010000000000000101055550000000000005500000000000000555500000000000055005555000000000000555500000000000055550000000000000000f1f1000000000000f1f1000000000000f0f0000000000000f0f0
|0,4=>0x333300000000000033330000000000003333000000000000000000ff00000000000000ff000000000000000000000000000000000000000000000000ffff0000000000000000000000000000aaaa111100000000000011110000000000001111000000000000000055550000000000005555000000000000000000000000000000003333000000000000111100000000000033330000000000000000000000000000000000ff000000000000000000000000000000aa0000000000000000ffff00000000000000000000000000000000aaaa000000000000ffff000000000000aaaa000000000000aaaabbbb000000000000bbbb000000000000aaaa000000000000aaaaffff000000000000ff00000000000000ffff000000000000000000000000000000000000000000000000ffff000000000000ff00000000000000000000ff0000000000000000000000000000000000ff00000000000000ff00000000000000ee00000000000000ee00aa00000000000000ff00000000000000aa00000000000000aaffff000000000000ffff000000000000f0f0000000000000f0f0
|0,5=>0xff000000000000000000000000000000ff00fafa000000000000fafa000000000000fafa000000000000fafaf5f5000000000000f5f5000000000000f0f0000000000000f0f05555000000000000555500000000000050500000000000005050ff00000000000000ffff000000000000ff00000000000000ff0000ff00000000000000ff00000000000000ff0000000000000000ffff000000000000ffff000000000000eeee000000000000eeee0000000000000000555500000000000000000000000000000000ffff000000000000ffaa000000000000ffff000000000000ffaaffff000000000000eeee000000000000ffff000000000000eeeef0ff000000000000f0ff000000000000f0f0000000000000f0f0ffff000000000000ffff000000000000fefe000000000000fefe
|_,_=>0
def sP:Nat→Nat
|0=>0x634386100cf87002011e0c104120e18e8e0608e04100839b0820386341040232182031a1c0801060386085c18d2018b031a3030304043041008a86085018d18184070c4c20e06088001c0c487002090220184072218208044030f1c0c68c002018b1410403121c0080e182840608080
|1=>0x8218020e1820e063578608397031a1c2031a1d68608201240c1042c041c304060882a0c1158d0ea83041c0c6a90c10703041c0041c0c3a80c1040220193842c0c6870c984033e1c30406343a50c1040d484030410481070c1070304882080634600100c80614343a10c1018d1604220
|2=>0xe01c885608806083818220182081a403861e381890e182081a1c338082018d1640008061c337083818d681820e0634606083818d441c2080624386085c18d0e182081a1c336082118220182081a1c335082018d6818208041d986082018d181820e0609906083818d0ec42080608e06
|3=>0x100c1470c1040305183041c0c6878a122031a1c3431c0c68b64107031a1c02606083c20c1018d0f043041a1d5064e1018d0e04304100c1220c1200d0ea83041c0c6877e1040d2a1c304100c68700987031a1df047a343aa0c104030ef0304100dd870c104070ce820e0634807002018d
|4=>0x1e10403042c00411401070c104030ea03041c0c3809e107031a2c8041c0c687012ca031a1c326880c6870d384030534304100c11000184030e185041c0c69c0e104030e1a6041d1018d0e0040d0e187cb100c38694104031a4033906343c90c104230e1821d100c1100d2040d321c304
|5=>0x634587082200d201c304100c6877e182080608806082158d0e1820806343be0c104031a2c380082018d0f34304100c6900e0030e0634386092c403a408386082018d201c348100c6c70e1820e880c6870c10b0e0634386082288d0e182080e187ba0838182161044004403041008386
|6=>0x100c3800d3c20806345900c104030e1a784100c6870c12a0806343800d2e98e0634386082018d0e1824328206870c9c20e06343b20c107031a1c004100c69c0e1821411006870c104020e1938410343861e1040d481c30410343864e127088008386080c6900ea830410348070c9c20e
|7=>0x1a1c331082018d0e182261c5018d0e182085c0c6870c10703041c30410343864e1258e0634386093ab880634386082158d201c304100c107001820e06348070c104031a1c304722018216182080634386ac10403041c304903818d0e18243100ea820e1820e100c6870010423041c304
|8=>0x100c6870c10403041c304100c6870c1270806348070c107080634386083818d0e1820806343800c104031a1c3049022d0d0e182080634386092c4031a2c38608201820e1821d1c0c6870c1130806351070c12208063438608584031a1c30406343aa0c104591a1c30410343d80c10403
|9=>0x8063438608206870c9c2088034386096c18d0e18214
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x4aa8905116a219440a87c50eea1c9436a86850c6a17942ca854509ea129422a8405076a0d9418a82c504ea08940ea8185026a039404a8045
|5,0=>0x424c831903320063f4c7d18f731e863c4c7718eb31d06394c7118df31b86364c6b18d331a06334c6518c731895306c5f58bbb17162d6c5958afb15962a6c5358a3b1416276c4d5897b1296246c47588bb1116216c41587fb0f961e6c3b5873b0e251b8c35986830ca6188c2f985c30b26158c299850309a6
|5,1=>0x28f6514aa1193f327864e4c9b1933326064b4c95192732486484c8f191b32306454c89190f32186
|6,0=>0x2183c297844f06de0a3c0e6810d0099fdbbf477daef99df033d977a4ef2dde23bbd776ceebddd4b3a27736ee51dc6bb867700cde5db93b6c66caed79dabbb507692ed09d9e3335765ceca1991331c662aec3d9843b0175f6cbd1d76bae765c2cb69d69bacc758aeaf9d5bbab07552ea89d4dba956
|7,0=>0x246b4876902d1e9e3a346d78ccf17de2cb4527896f115a1f3c377
|8,0=>0x4936
|_,_=>0
def wAt:=mkWire dB 92 208 0xffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 1000003 zs)
def oP:Nat→Nat
|0=>0x10120c11201b0e110e110c110e12101904191a1d0e110c120f210c121c1310191c1110190739101210191a1d0e1906111a1d1a020e110e12201b04000c111c13161004121a1d0c1204121c1f1c101c4016110e191a3e0e11161006410e110c110c1106090e111c1f1a1d1a1d061a1a1d0e110e111a1d061a46131a1d0c111c40
|1=>0x6410e110c111a1d0e11101916100e191a1d0e190c121a1d1c12101904111a1d0c1106091a1d1a020c110e111a020c1116120e190e121c1d10191c121019061a1c1f10190c11101916130e1906111a1d061a4e11061a0e9d061a1012061a1a1d061110420e110e11061a0e1910190e1106110d2d0e120e111a1d06410e110d39
|2=>0x61a0611101b10111a1d10120e11101910190c110c12061d0e120e1904121a1d1c10101916110e191c13101910010c1110420e11072d0e12801f06110e020c111c1010191011281b10111a1d10190e12061a10191012
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11000000000000000000000000000000000000000000000000001000000000000000000000000000000000000
|5,0=>0x1d20000001c11b10000001a11910000000001811620000000000000000000000001511411311210000000000001020000000000f10000000000d20000000000000b2000000000000000000092000072061000051000041000000000000022
|5,1=>0x2932810002710000002612512410000002310002120000002010000001f1
|6,0=>0x9b29929729529329128f28d28b28928818628428228020007e27c27a27827620007427227026f16d26b26a16826626516326126015e25c25a25915725525325124f24d24b24924724524324123f23e13c23a23823623423223022e22c2
|7,0=>0xaa1a91a81a71a61a51a41a31a21a11a019f19e19d1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x9a004c0025e012d0096004940248011f008e004580222010d00860041c020c010500820040001860024001000070002800100006000280010000400018000800020000
|1=>0x404310284613f308f904f48276311f149f8a07c43fe213f109d884bc42362109101008048402019120889020080800020000c0005fc02f6017300a0004fc027a013b
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x80000000000000000000000002000000000000000000
|5,0=>0x7c200400010410000200100010000800e0000820001040000020c0000000000005105a8000000a00000200000d000a402c0000000006a4ba00100080000027
|6,0=>0x8d4493495ef841d15986d4c0b175d89805cff4cd541d33c758f2df70f2f3c31bf47ae86b424d9a251297f8945b432
|7,0=>0xcfc8b9979e6287aeb7e62
|8,0=>0x20
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 17 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_205 7 roots_205 ops++addP pm 1 dom_198 5 roots_198 ops++addP pm 2 dzo_139_4 5 roots_139 ops++addP pm 3 dom_139 5 roots_139 ops++addP pm 4 dom_206 6 roots_206 ops++addP pm 5 dom_199 6 roots_199 ops++addP pm 6 dom_204 4 roots_204 ops++addP pm 7 dom_201 5 roots_201 ops++addP pm 8 dom_203 7 roots_203 ops++addP pm 9 dom_195 5 roots_195 ops++addP pm 10 dzo_201_4 5 roots_201 ops++addP pm 11 dom_202 5 roots_202 ops++addP pm 12 dom_75 4 roots_75 ops++addP pm 13 dzo_203_4 6 roots_203 ops++addP pm 14 dom_79 5 roots_79 ops++addP pm 15 dom_77 4 roots_77 ops++addP pm 16 dom_137 4 roots_137 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_207 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_139_4_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_201_4_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_203_4_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_137 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_205 7 s (0,roots_205.map (·&&&dom_205)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_207 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_205 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_207 gM v ys):RunD true dom_207 gM v (ori ys):=h
def Z (s:Nat):=barP dom_207 gM mpG SD SS NN hAt idxH ori 1000003 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 30 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 30 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 85 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 85 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 62 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 62 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 14 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_207 gM mpG SD SS NN hAt idxH ori 1000003 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_207 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_207 roots_207 goal_207 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_207
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=S_207.noCircuit
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_slice_b [(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,16,18)] (by decide +kernel) lowS_213
def dzo_82_8:=0x50005000000000005000500
def gzo_82_8:=0x50004000000000004000000
def gsh_82_8:=0x500040000000000040000
theorem lowS_zo_82_8_82:Lower true dzo_82_8 roots_82 gzo_82_8 4:=lower_iso_b (d1:=dom_82) (r1:=roots_82) (T1:=gsh_82_8) [(dom_82,8)] (by decide +kernel) (lower_slice_b (T:=gsh_82_8) [] (by decide +kernel) lowS_82)
def dzo_137_16:=0x303000000000000000000000000000003030000
def gzo_137_16:=0x302000000000000000000000000000002000000
def gsh_137_16:=0x30200000000000000000000000000000200
theorem lowS_zo_137_16_137:Lower true dzo_137_16 roots_137 gzo_137_16 4:=lower_iso_b (d1:=dom_137) (r1:=roots_137) (T1:=gsh_137_16) [(dom_137,16)] (by decide +kernel) (lower_slice_b (T:=gsh_137_16) [] (by decide +kernel) lowS_137)
def dzo_203_16:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000
def gzo_203_16:=0xf0f0000000000000f0e0000000000000f0f0000000000000e0c0000
def gsh_203_16:=0xf0f0000000000000f0e0000000000000f0f0000000000000e0c
theorem lowS_zo_203_16_137:Lower true dzo_203_16 roots_203 gzo_203_16 6:=lower_iso_b (d1:=dom_203) (r1:=roots_203) (T1:=gsh_203_16) [(dom_203,16)] (by decide +kernel) (lower_slice_b (T:=gsh_203_16) [(0xc0c0000000000000c0c0000000000000c0c0000000000000c0c,0,2),(0xf0f00000000000000000000000000000f0f0000000000000000,0,64)] (by decide +kernel) lowS_137)
def dzo_210_8:=0x5000500000000000500050000000000050005000000000005000500
def gzo_210_8:=0x5000500000000000500050000000000050004000000000004000000
def gsh_210_8:=0x50005000000000005000500000000000500040000000000040000
theorem lowS_zo_210_8_82:Lower true dzo_210_8 roots_210 gzo_210_8 5:=lower_iso_b (d1:=dom_210) (r1:=roots_210) (T1:=gsh_210_8) [(dom_210,8)] (by decide +kernel) (lower_slice_b (T:=gsh_210_8) [(0x50005000000000005000500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_139_16:=0xf0f00000000000000000000000000000f0f0000
def gzo_139_16:=0xf0e00000000000000000000000000000e0c0000
def gsh_139_16:=0xf0e00000000000000000000000000000e0c
theorem lowS_zo_139_16_137:Lower true dzo_139_16 roots_139 gzo_139_16 5:=lower_iso_b (d1:=dom_139) (r1:=roots_139) (T1:=gsh_139_16) [(dom_139,16)] (by decide +kernel) (lower_slice_b (T:=gsh_139_16) [(0xc0c00000000000000000000000000000c0c,0,2)] (by decide +kernel) lowS_137)
def dzo_211_8:=0xf000f00000000000f000f00000000000f000f00000000000f000f00
def gzo_211_8:=0xf000f00000000000f000f00000000000f000e00000000000e000a00
def gsh_211_8:=0xf000f00000000000f000f00000000000f000e00000000000e000a
theorem lowS_zo_211_8_82:Lower true dzo_211_8 roots_211 gzo_211_8 6:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_8) [(dom_211,8)] (by decide +kernel) (lower_slice_b (T:=gsh_211_8) [(0xa000a00000000000a000a00000000000a000a00000000000a000a,0,1),(0xf000f00000000000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_83_8:=0xf000f00000000000f000f00
def gzo_83_8:=0xf000e00000000000e000a00
def gsh_83_8:=0xf000e00000000000e000a
theorem lowS_zo_83_8_82:Lower true dzo_83_8 roots_83 gzo_83_8 5:=lower_iso_b (d1:=dom_83) (r1:=roots_83) (T1:=gsh_83_8) [(dom_83,8)] (by decide +kernel) (lower_slice_b (T:=gsh_83_8) [(0xa000a00000000000a000a,0,1)] (by decide +kernel) lowS_82)
def dzo_201_16:=0x3030000000000000303000000000000030300000000000003030000
def gzo_201_16:=0x3030000000000000302000000000000030300000000000002000000
def gsh_201_16:=0x303000000000000030200000000000003030000000000000200
theorem lowS_zo_201_16_137:Lower true dzo_201_16 roots_201 gzo_201_16 5:=lower_iso_b (d1:=dom_201) (r1:=roots_201) (T1:=gsh_201_16) [(dom_201,16)] (by decide +kernel) (lower_slice_b (T:=gsh_201_16) [(0x303000000000000000000000000000003030000000000000000,0,64)] (by decide +kernel) lowS_137)
namespace S_219
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(2,18),(2,66),(2,130),(3,11),(3,19),(3,67),(3,131),(8,9),(8,136),(10,11),(10,26),(10,74),(10,138),(16,18),(16,80),(17,19),(17,25),(17,81),(17,145),(24,25),(24,26),(24,88),(24,152),(64,65),(64,66),(64,80),(64,192),(72,73),(72,74),(72,88),(72,200),(128,129),(128,130),(128,136),(128,192),(144,145),(144,146),(144,152),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_219.map (·&&&dom_219)
def gM:=goal_219&&&dom_219
def NN:Nat→Nat
|4=>7
|5=>18
|6=>46
|7=>36
|8=>12
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xcdf99c76478eead84b9d62c2c4c1352fa33
|5,0=>0xd69a9a9137a81cf7dbd178ec46a39f61a525c5135aadd560a254b4552aca4f4af38b6c21f121a1c80cb4005973
|6,0=>0xe10d7cacd0b224bad947ac8e9a65b89d45e96aa593baf8f795865e17fe09755f172e2c6bf4568dca631576023e5c3ad5083a4f3d04ee044eddf4e4d448e6c3fb0f3c66e3c66a3831338161355593500c2fae52f1da2bfe22aa8524c2822bd81f81719b3b0cd5c0c14b067cd0501204e3900e67
|7,0=>0xd9d1ecab0aca990b295ea0c109a7d684f6c7b6db7a8de782b3717da6d64a6c99961d8f5747e504004580b44e26427fb42654419403d7c73c9ac396cd29b3526b0d25b2c235011edc01edac1c56715d8f1370d06f50031e90140c
|8,0=>0xae93da92a3a019f798d460ca9544f14c5014af0f488e43f7382fd77088ca
|9,0=>0x798d4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a0000f0f0000000000000f0c0000000000000f0f0000000000000e0cf0f0f0f000000000a0a0a0a000000000c0c0c0c0000000008080808f0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000f0f0f0f000000000f0c0f0c000000000f0f0f0f000000000e0c0e0cf000f00000000000f000f00000000000f000f00000000000f000f00f0f0f0f000000000f0f0f0f000000000c0c0c0c000000000c0c0c0cf0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0ae0e0e0e000000000e0e0e0e000000000e0e0e0e0000000000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0cf0f0f0f0000000000000000000000000f0f0f0f0000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000e0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0ef0f0f0f000000000c0c0c0c000000000f0f0f0f000000000c0c0c0cf0f0f0f000000000f000f00000000000f0f0f0f000000000a000a00f0f0f0f000000000f0f0f0f00000000000000000000000000000000
|0,1=>0xf0f0f0f0000000000000000000000000c0c0c0c00000000000000000000000000000000e0e0e0e000000000e0e0e0ef0f0f0f000000000f0f0f0f000000000e0e0e0e000000000e0e0e0e0000000000000000f0f0f0f0000000000000000000000000e0e0e0ef0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f00003030303000000000300030000000000030303030000000002000200f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f000050505050000000005050505000000000505050500000000000000005050505000000000505050500000000040404040000000004040404f0f0000000000000c0c0000000000000f0f0000000000000c0c0000f0f0f0f000000000f0f0f0f000000000f0f0000000000000c0c0000f000f00000000000f000f00000000000a000a00000000000a000a0000f000f00000000000f000f00000000000a000a00000000000a000af0f0f0f000000000e0e0e0e000000000f0f0f0f000000000e0e0e0ef0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0a0000f0f0000000000000c0c0000000000000f0f0000000000000c0c
|0,2=>0xf0a0f0a000000000f0a0f0a000000000f0a0f0a000000000f0a0f0a1010101000000000101010100000000010101010000000000000000f0f0f0f00000000000f000f000000000f0f0f0f00000000000a000a50505050000000005050505000000000505050500000000040404040000000000000000505050500000000000000000000000004040404000000000000000000000000000000000000000000000000e0e0e0e3030303000000000303030300000000030303030000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0af0f0f0f000000000f0f0f0f0000000000000000000000000e0e0e0ef0f0f0f000000000f000f00000000000f0f0f0f000000000f000f00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000c0c0c0cf0f0f0f000000000f0f0f0f00000000030303030000000002020202b0b0b0b000000000b0b0b0b000000000b0b0b0b000000000a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000e0e0e0ec0c0c0c000000000c0c0c0c000000000f0f0f0f000000000e0e0e0ef0f0c0c000000000f0f0c0c000000000f0f0c0c000000000f0f0c0c
|0,3=>0xf0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0af0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f00f0f0f0f000000000f0f0f0f000000000f000f00000000000f000f000000000000000000f000f000000000000000000000000000f000f0000000000000000000000000000000000f0f0000000000000f0f0000f0f0f0f000000000f0c0f0c000000000f0f0f0f000000000f0c0f0c0000000000000000e0e0e0e0000000000000000000000000e0e0e0e5050505000000000505050500000000050500000000000005050000
|_,_=>0
def sP:Nat→Nat
|0=>0x3c168010a19114710a0cd14028354f15928620c6042823d73042863cd30a0d64450042832483063d440500a0d53c50042c63c10063d34050042893c51c42921913040863c100428244718f0500063c138010a0cd3040cb04010a2481c40c2040
|1=>0x2463c510a8863c50040c65050192863cc15864a1883cc2865913c50042891883cc10a7823c500428324f30510a8463c50201063d314010a0df3c50042863d730510a78620500429c18f1406c418f4c500429219114010a0c244c10a4893cc106
|2=>0x2831913051260c62001063c114010a24f16900428620c60010a18f1470199863cc10218f4c5004286a0560010a08f5c50042a718f14010a18f34500428644c15810a18844c10a0c920500418f0401269463cc0042863e414010a1a33c501929d
|3=>0x42a52463c50042891883c500428644f3051261883c010a18f15800429218f14010a18f305a402863d014010a18f16e0042830911401063ed14010a7463cc1442821913cc10a18fb0500429224f14010a18fac50042831a814010aa863c5004
|4=>0x28318f3050049863cc004c8a18f14010a18fc050199863c5004286a0f30501b10a1913c500428319114010a18844500429d2463c50042b118f14010a74318f14064a18fc0500428620f30010a1a83c5004bca0863c501928318f14064a1883c5
|5=>0x3c5004bca18f14064a18f140dc42863c500428318f14010a1883c500428218f1401352863c503610a18f140cf418f14028658f14010a18f5c500428318814010a08644f1406c4d4a18f14067418f14010a19f3c503328318f140cca1883c5004
|6=>0x42863c501910a18f140cca18f14010a18f305004286
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x1e5065414503d40a50154005
|5,0=>0x22188261f187661c186b519585f61658536135847610583b60d582f60a58236
|6,0=>0x6fddb876c99ab7691d9d7659d8f7621d8175e9d7465b99677581d59755154d7519d3f74e1d3174a9d246475d185445d0a740dcfc73d5cef63a1ce2636dcd47335cc672fdcb872c5caa728dc9c7255c8e7
|7,0=>0xb01aba6acdeac7a9229c8a59a8f7a21e8179e627369b1e65797da57893e2487905e3988c9e2a888de1c7855e0d8819dff77de1ef87a1de2676ddd477321c66
|8,0=>0xc41f0a6c0defd6bd9ef06ba5ee27b6ded47b35ec67
|9,0=>0x3176
|_,_=>0
def wAt:=mkWire dB 56 220 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3c04a15005463210046012484a443c0463d3cc840114044013c5401510206150c0cf19200ca463c049171804f26180430318f5d172918f0108f46153c043153c654152910f010cc063d58044081854f1924806013c54615580440818546055054a443c0433018f43153c646150464615
|1=>0x3cc450128f461518f44011004f1524546011804f153c045012854f153cc85011884f1518c801510286153c053152918f010c0463d3c048193c54f311404a1518f4f155054a443c049153cc80150cc063d140450128544012918f01140431724806013c54f3214045013c04f155054a44
|2=>0x401100c50128f440110f463d3c546152804429285c40310206153c9860118f4f153c046151054a011004a17245c60118f4403100cf1518f45012854015282461564fc40128544013cc45011054f013c0463d3c04f153c946010c5cf190c0463d64fc4013c54015
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11000001
|5,0=>0x1d11b21831620001240000000f30e10000000b3074000052032021
|6,0=>0x6716436226110005f20005d20000005a35735615425134e34c24b10004a14734524230003f33d20003c13a23913633333032e20002c20002b12922722522322212021e2
|7,0=>0xae2ac2aa2a82a62a42a22a029e29c29a29829629429229028e28c28a28828628428228027e27c27a27827627427227026e26c26a2682
|8,0=>0xba1b91b81000b71b61b51b41b31b21b11b01
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x19f4000628000117400045400010c0000420000106400040800010100004010000d2400030900008c400021800008240002080000344000048000011000004100001000000200000048000010000003400000c0000020000004000000c0000020000004000000
|1=>0x1b4354068cd501687e404f0d50135b5404c4f5012db7404aadd012435403e0dd00b03540280f5009893401e1dd004011000f4dd0038f7400e1d5003837400a0fd00283dc0080d70020354008095002005c008000001d11400634d001891400614500031c0000c10
|2=>0x813c35509a0d521ec3544380d7104004c219080082400c14a5f505297c414a4f50528a7414a0d50402864100a0d03e93540880d701fd37406d4d5
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x8002
|5,0=>0x504101800f000068200000890010202
|6,0=>0xa62385002e009000af5520187e088280080d0e8cc2736008113ca03a506005853420b0e1c41304
|7,0=>0x5509c492731dbe56b0eb686f2095971d2459111e225f35cb042659b25b28e37
|8,0=>0x7ed1aa99d028c65cea84f
|9,0=>0x29
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 26 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_218 7 roots_218 ops++addP pm 1 dom_194 4 roots_194 ops++addP pm 2 dom_91 7 roots_91 ops++addP pm 3 dzo_82_8 4 roots_82 ops++addP pm 4 dom_217 7 roots_217 ops++addP pm 5 dom_137 4 roots_137 ops++addP pm 6 dom_155 7 roots_155 ops++addP pm 7 dom_211 7 roots_211 ops++addP pm 8 dom_154 4 roots_154 ops++addP pm 9 dom_82 4 roots_82 ops++addP pm 10 dzo_137_16 4 roots_137 ops++addP pm 11 dom_89 4 roots_89 ops++addP pm 12 dzo_203_16 6 roots_203 ops++addP pm 13 dzo_210_8 5 roots_210 ops++addP pm 14 dzo_139_16 5 roots_139 ops++addP pm 15 dom_203 7 roots_203 ops++addP pm 16 dzo_211_8 6 roots_211 ops++addP pm 17 dzo_83_8 5 roots_83 ops++addP pm 18 dzo_201_16 5 roots_201 ops++addP pm 19 dom_193 4 roots_193 ops++addP pm 20 dom_216 4 roots_216 ops++addP pm 21 dom_139 5 roots_139 ops++addP pm 22 dom_210 5 roots_210 ops++addP pm 23 dom_195 5 roots_195 ops++addP pm 24 dom_83 5 roots_83 ops++addP pm 25 dom_202 5 roots_202 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_82_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_137_16_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_203_16_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_210_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_139_16_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_211_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_83_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_201_16_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_202 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_218 7 s (0,roots_218.map (·&&&dom_218)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_218 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_219==dom_219)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_219 gM v ys):RunD true dom_219 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_219 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 46 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
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
def dzo_84_8:=0x110011000000000011001100
def gzo_84_8:=0x110010000000000010000000
def gsh_84_8:=0x1100100000000000100000
theorem lowS_zo_84_8_84:Lower true dzo_84_8 roots_84 gzo_84_8 4:=lower_iso_b (d1:=dom_84) (r1:=roots_84) (T1:=gsh_84_8) [(dom_84,8)] (by decide +kernel) (lower_slice_b (T:=gsh_84_8) [] (by decide +kernel) lowS_84)
def dzo_212_8:=0x11001100000000001100110000000000110011000000000011001100
def gzo_212_8:=0x11001100000000001100110000000000110010000000000010000000
def gsh_212_8:=0x110011000000000011001100000000001100100000000000100000
theorem lowS_zo_212_8_84:Lower true dzo_212_8 roots_212 gzo_212_8 5:=lower_iso_b (d1:=dom_212) (r1:=roots_212) (T1:=gsh_212_8) [(dom_212,8)] (by decide +kernel) (lower_slice_b (T:=gsh_212_8) [(0x110011000000000011001100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_153_4:=0x3030303000000000000000000000000030303030
def gzo_153_4:=0x3030302000000000000000000000000030302000
def gsh_153_4:=0x303030200000000000000000000000003030200
theorem lowS_zo_153_4_137:Lower true dzo_153_4 roots_153 gzo_153_4 5:=lower_iso_b (d1:=dom_153) (r1:=roots_153) (T1:=gsh_153_4) [(dom_153,4)] (by decide +kernel) (lower_slice_b (T:=gsh_153_4) [(0x303000000000000000000000000000003030000,0,16)] (by decide +kernel) lowS_137)
def dzo_141_16:=0x3333000000000000000000000000000033330000
def gzo_141_16:=0x3332000000000000000000000000000032300000
def gsh_141_16:=0x333200000000000000000000000000003230
theorem lowS_zo_141_16_137:Lower true dzo_141_16 roots_141 gzo_141_16 5:=lower_iso_b (d1:=dom_141) (r1:=roots_141) (T1:=gsh_141_16) [(dom_141,16)] (by decide +kernel) (lower_slice_b (T:=gsh_141_16) [(0x303000000000000000000000000000003030,0,4)] (by decide +kernel) lowS_137)
def dzo_205_16:=0x33330000000000003333000000000000333300000000000033330000
def gzo_205_16:=0x33330000000000003332000000000000333300000000000032300000
def gsh_205_16:=0x3333000000000000333200000000000033330000000000003230
theorem lowS_zo_205_16_137:Lower true dzo_205_16 roots_205 gzo_205_16 6:=lower_iso_b (d1:=dom_205) (r1:=roots_205) (T1:=gsh_205_16) [(dom_205,16)] (by decide +kernel) (lower_slice_b (T:=gsh_205_16) [(0x3030000000000000303000000000000030300000000000003030,0,4),(0x3333000000000000000000000000000033330000000000000000,0,64)] (by decide +kernel) lowS_137)
def dzo_213_8:=0x33003300000000003300330000000000330033000000000033003300
def gzo_213_8:=0x33003300000000003300330000000000330032000000000032002200
def gsh_213_8:=0x330033000000000033003300000000003300320000000000320022
theorem lowS_zo_213_8_84:Lower true dzo_213_8 roots_213 gzo_213_8 6:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_8) [(dom_213,8)] (by decide +kernel) (lower_slice_b (T:=gsh_213_8) [(0x220022000000000022002200000000002200220000000000220022,0,1),(0x330033000000000033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_217_4:=0x30303030000000003030303000000000303030300000000030303030
def gzo_217_4:=0x30303030000000003030302000000000303030300000000030302000
def gsh_217_4:=0x3030303000000000303030200000000030303030000000003030200
theorem lowS_zo_217_4_137:Lower true dzo_217_4 roots_217 gzo_217_4 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_4) [(dom_217,4)] (by decide +kernel) (lower_slice_b (T:=gsh_217_4) [(0x3030000000000000303000000000000030300000000000003030000,0,16),(0x3030303000000000000000000000000030303030000000000000000,0,64)] (by decide +kernel) lowS_137)
namespace S_221
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(4,20),(4,68),(5,13),(5,21),(5,69),(5,133),(8,9),(8,136),(12,13),(12,28),(12,76),(12,140),(16,20),(16,80),(17,21),(17,25),(17,81),(17,145),(24,25),(24,28),(24,88),(24,152),(64,65),(64,68),(64,80),(64,192),(72,73),(72,76),(72,88),(72,200),(128,129),(128,136),(128,192),(132,133),(132,140),(132,148),(132,196),(144,145),(144,148),(144,152),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_221.map (·&&&dom_221)
def gM:=goal_221&&&dom_221
def NN:Nat→Nat
|5=>4
|6=>15
|7=>24
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x33c67225b8024e7012ac
|6,0=>0xf1c08d8cf0c7501c6af1c553ca4e5c8462e722075e4755100e3859f229641fd41110910fce2
|7,0=>0xf1341eb3bbab28087e0185d67817ce80dbe773ec76be2601cc5735f55c0e4004836d3934f4b32ec630a05266021d8661596e1373e0eb4a0798c06f7c
|8,0=>0xd84b291acb820eb72d815868c125d80c3460bcff
|9,0=>0x7369e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccc000000008888888800000000cccccccc00000000888888880003333000000000000000000000000000033330000000000000000cccccccc00000000cccccccc0000000088888888000000008888888b3333333000000003333333300000000000033330000000000000000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc000000000000000000000000000000000333333330000000022222222444444440000000044444444000000004444444400000000000000033330000000000003030000000000000333300000000000030300000cccc000000000000cccc000000000000cccc000000000000cccc00000333333000000000033003300000000002233330000000000220022c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c2222222200000000222222220000000022222222000000002222222200cc00cc0000000000cc00cc000000000088008800000000008800880003333000000000000303000000000000033330000000000003030cccccccc000000000000000000000000cccccccc00000000000000033333333000000003333333300000000000000000000000000000000
|0,1=>0xcccc888800000000cccc888b3333333000000003333333300000000323232320000000032323232444444440000000000000000000000004444444400000000000000033033303000000003300330000000000330333030000000033003300cccccccc0000000000cc00cc00000000cccccccc00000000008800883030303000000000303000000000000030303030000000003030000ccccc0c000000000ccccc0c000000000ccccc0c000000000ccccc0c333333330000000033333333000000000303030300000000000000000c0c0c0c0000000000000000000000000c0c0c0c00000000000000033333333000000003333333300000000232323230000000022222222444444440000000044444444000000000404040400000000000000033333333000000003030303000000000333333330000000030303030cccccccc00000000cccc000000000000cccccccc00000000cccc00030303030000000003030000000000000303030300000000030300000cccccccc00000000cccccccc00000000cccccccc000000008888888b3333333000000003333333300000000333333330000000000000000
|0,2=>0x33333333000000003333333300000000303030300000000030303030000000000000000000000000000000004444444400000000000000033333333000000003333333300000000111111110000000000000000cccccccc00000000cc00cc0000000000cccccccc00000000cc00cc000000000000000000000000000000000333333330000000000000000cc00cc0000000000cc00cc0000000000cccccccc00000000cc00cc033332222000000003333222200000000333322220000000033332222
|_,_=>0
def sP:Nat→Nat
|0=>0x71446c10071440c13801cb14f3500472c53cd4072cd11a0406471440c10072c55840401cb1440550075051030401cb48d1010072c53ca1101cb1512840472c53ca3411cb14f0490072c534404c1cb14a0491481030401c51060401440c2040
|1=>0x14f1010078c53c40191cb14d1010072c54444010072c53ca1010078c512200b1481010071440c10078451010072c51012407c72c51010072d414d1010072c46810072c51013001cb7851010072c51107401dc1440401cb14f1100401cb14f110
|2=>0x72c51010191cb1440401cb5051010072c53c40401e31440401cb1440620072c53440401cb14404e0072e61440401cb1511010072c53444011cb14d1013801cb1440650072c51019001e3
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x9303180cc006
|6,0=>0x1e58e4e6b732b179caee50724b909c76e34716b899c3ee187
|7,0=>0x8fbc61e211097813beddeaced872c3761aecd1665b31597ceb7757c2a5944e9b74a3a3990d07f7
|8,0=>0xab3d3de90f4269dbcd1e5af267
|9,0=>0x15d6
|_,_=>0
def wAt:=mkWire dB 39 222 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x444b05040c7501414b361004b89040d01304060031c44401141454e1c14e011c1853510041130404b5d1418101044410104444011c18b36100440104041111014011040454e10047052cd840111857011418b36100454c10047053c0c11100a4f030444f030444405404c1013804706
|1=>0x71514141112c1410310047061404f01044401104047061004d061004075044cb050444b05044471510050110404f03
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x884f99c332658ca11130003c8618a20e614811802
|7,0=>0xa253ca694b29251ca29432824fc9e93b2724dc9a9332624bc9692b25249c929232
|8,0=>0xb43646c0d71ac3546a0d31
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x111e2127c41dfd81bfb031720400005fd80bf3017e202edc05d9808b701162020000218803e7007ca00f84007b800e3001c4003000053800a200046000840010000180000e0000c000100000
|1=>0x21dfda4db149042727c4a4108c9f119366326c45c7d88eb1
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40000
|6,0=>0x1a10c3c648201244a0c81c5
|7,0=>0x59035861972724ba5e6dd5609647e342130e
|8,0=>0xa265dd5d47e2
|9,0=>0x13
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_213 8 roots_213 ops++addP pm 1 dzo_84_8 4 roots_84 ops++addP pm 2 dom_84 4 roots_84 ops++addP pm 3 dzo_212_8 5 roots_212 ops++addP pm 4 dom_205 7 roots_205 ops++addP pm 5 dom_220 7 roots_220 ops++addP pm 6 dom_157 6 roots_157 ops++addP pm 7 dom_93 7 roots_93 ops++addP pm 8 dzo_153_4 5 roots_153 ops++addP pm 9 dzo_141_16 5 roots_141 ops++addP pm 10 dzo_205_16 6 roots_205 ops++addP pm 11 dom_217 7 roots_217 ops++addP pm 12 dzo_213_8 6 roots_213 ops++addP pm 13 dzo_85_8 5 roots_85 ops++addP pm 14 dzo_217_4 6 roots_217 ops++addP pm 15 dzo_201_4 5 roots_201 ops++addP pm 16 dom_137 4 roots_137 ops++addP pm 17 dom_201 5 roots_201 ops++addP pm 18 dom_85 5 roots_85 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_221 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_84_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_212_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_153_4_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_141_16_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_205_16_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_213_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_85_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_217_4_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_201_4_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_85 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_213 8 s (0,roots_213.map (·&&&dom_213)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_221 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_213 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_221==dom_221)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_221 gM v ys):RunD true dom_221 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_221 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 15 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_221 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_221 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_221 roots_221 goal_221 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_221
theorem lowS_221:Lower true dom_221 roots_221 goal_221 10:=S_221.noCircuit
def dzo_86_8:=0x550055000000000055005500
def gzo_86_8:=0x550054000000000054000000
def gsh_86_8:=0x5500540000000000540000
theorem lowS_zo_86_8_86:Lower true dzo_86_8 roots_86 gzo_86_8 5:=lower_iso_b (d1:=dom_86) (r1:=roots_86) (T1:=gsh_86_8) [(dom_86,8)] (by decide +kernel) (lower_slice_b (T:=gsh_86_8) [] (by decide +kernel) lowS_86)
def dzo_214_8:=0x55005500000000005500550000000000550055000000000055005500
def gzo_214_8:=0x55005500000000005500550000000000550054000000000054000000
def gsh_214_8:=0x550055000000000055005500000000005500540000000000540000
theorem lowS_zo_214_8_86:Lower true dzo_214_8 roots_214 gzo_214_8 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_8) [(dom_214,8)] (by decide +kernel) (lower_slice_b (T:=gsh_214_8) [(0x550055000000000055005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_86)
namespace S_222
def pG:List (Nat×Nat):=[(2,18),(2,66),(2,130),(4,20),(4,68),(6,22),(6,70),(6,134),(8,136),(10,26),(10,74),(10,138),(12,28),(12,76),(12,140),(14,30),(14,78),(14,142),(16,18),(16,20),(16,80),(24,26),(24,28),(24,88),(24,152),(64,66),(64,68),(64,80),(64,192),(72,74),(72,76),(72,88),(72,200),(128,130),(128,136),(128,192),(132,134),(132,140),(132,148),(132,196),(144,146),(144,148),(144,152),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_222.map (·&&&dom_222)
def gM:=goal_222&&&dom_222
def NN:Nat→Nat
|4=>3
|5=>10
|6=>17
|7=>7
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xf95978d3416fe49
|5,0=>0xf16d3eb95cde9bece464afe95879847ef406916e68b4c1c0eb
|6,0=>0xefc94ed420dea34d8865d3131be262aaaf7aa8766c2a15004643aa33e10d35d6d2a9f925d1c0e4b008824
|7,0=>0xfa83ad9300c049278bdf66b6d0c45705964
|8,0=>0xbad5e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaa000000000000000000000000aaaa0000000000000000000014141414000000001414141400000000141414140000000014140002aaaaaaa800000002a802a80000000002aaaaaaa800000002a802a80050505050000000005050000000000000505050500000000050500000a0a0000000000000a0a0000000000000a0a0a0a000000000a0a000001555554000000000154015400000000000155540000000000000002aaaaaaa8000000000000000000000002aaaaaaa8000000000000000555555550000000050505050000000005555505000000000505050508888888800000000888888880000000088888888000000008888888955555554000000015554000000000001555555540000000155540002aaaaaaa800000002aaaaaaa8000000000000000000000000000000055550000000000005555000000000000555500000000000055550000aa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa0141414140000000014141414000000001414141400000000141414142aaaaaaa8000000022222222000000002aaaa222000000002222222255555555000000005555555500000000555555550000000000000000
|0,1=>0x2a802aaa800000002a802a80000000002a802aaa800000002a802a8000000000000000000000000000000000555555550000000000000000aaaa000000000000aaaa000000000000aaaaaaaa00000000aaaa000000000000000000000000000000000000000155540000000000000002aaaaaaa80000000002a802a800000002aaaaaaa800000000000000000000000000000000000000000000000555555550000000055550000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaa0000000000000000000155555554000000000000000000000001555400000002aaa8000000000002aaa8000000000002aaa8000000000000000555555550000000055555555000000000000555500000000000000000000aaaa0000000000000000000000000000aaaa00000000000000015555555400000001555555540000000155540000000000015554000002a802a80000000002a802a8000000000000000000000000000000011111111000000001111111100000000111111110000000011110000
|_,_=>0
def sP:Nat→Nat
|0=>0x11d25258623a4a4188e9a948311d34290474ccb1348623a4a4188e979644188e0490ec49626188ef29062824a4188e0790620a4a419dc9291a7624a419d69290474a8a41a0e929868394c3104a418820
|1=>0x20c474948311d3c290474962620c4749644188e9291a23a4a4188e99948311c09293a23a4bb20c47494c411d25898833b12520cec4948311d3a29047ca4b820c47494c4688e92dc83
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa5055005
|5,0=>0x4563f63963362d62762161b61560f6
|6,0=>0xb96b27ab7a479e69779168a78377c77576e76776075975274b7
|7,0=>0xe77e16da7d37cd6c67bf7
|8,0=>0xee6
|_,_=>0
def wAt:=mkWire dB 30 223 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x4971962252151a52264951cd22627149719622530b22530b2259262154c51963172251a5225925215927215995226196226225215924215495215
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1e2709a26096250922408e2308a2000821884208802
|7,0=>0x261946418c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xffdfdd7d5f5d5448474035280e060500
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x568812528720249b3
|7,0=>0xecdbfde
|8,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_220 7 roots_220 ops++addP pm 1 dzo_86_8 5 roots_86 ops++addP pm 2 dom_214 7 roots_214 ops++addP pm 3 dom_206 6 roots_206 ops++addP pm 4 dom_86 5 roots_86 ops++addP pm 5 dzo_214_8 6 roots_214 ops++addP pm 6 dom_218 7 roots_218 ops++addP pm 7 dom_158 5 roots_158 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_222 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_86_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_214_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_158 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_220 7 s (0,roots_220.map (·&&&dom_220)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_222 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_220 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_222 gM v ys):RunD true dom_222 gM v (ori ys):=h
def Z (s:Nat):=barP dom_222 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_222 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_222 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_222 roots_222 goal_222 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_222
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=S_222.noCircuit
theorem lowS_231:Lower true dom_231 roots_231 goal_231 8:=lower_slice_b [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,32,33)] (by decide +kernel) lowS_230
namespace S_235
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,34),(2,66),(2,130),(3,11),(3,35),(3,67),(3,131),(8,9),(8,40),(8,136),(10,11),(10,42),(10,74),(10,138),(32,33),(32,34),(32,40),(32,160),(64,65),(64,66),(64,192),(72,73),(72,74),(72,104),(72,200),(96,97),(96,98),(96,104),(96,224),(128,129),(128,130),(128,136),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_235.map (·&&&dom_235)
def gM:=goal_235&&&dom_235
def NN:Nat→Nat
|4=>21
|5=>61
|6=>70
|7=>45
|8=>10
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xe1876d8d52c92d3a745174c246f6665b886481d5449514398642f4d3fbfc33e253361e2203d2077e1bd610ecd3068c206398034ee
|5,0=>0xea29dd3fcdce101c94a2bc1ebb859eb422bb320dab607a1e269ed9e999f7984e596425963af90e9188cdb866d78659c801b77f1267b37b79156783eb769e76a01b6996a5e75c59ec1588515426d539244489a3e1ba3dcc93d8ec3d0213bd7937ccf3778c35f3f33fc132e0630f942da462a37c25b58240db219031ef4c1e4661c08919d5a152de145e7137df1100f09f720856e05db203a21
|6,0=>0xf09e3e5d15e3e31d9b9ad0b5fcfbadc1d8cb9bc2a7401a6625a25fba00f09f6339ba2197d6596bad95f75917028f36578d597526173c4d709306f9026a16468cf66606d64aa45fa035ac1a58fbb55f6a55e2854b6e53da8512314ebf54bbbc4585f441794106e3aa133a23e388ba3822e3811e35fc830c9c304a42e14e2df3f2da822c6e329cda290851fae41f8501e6941de2517c191621513e13111420fd140f6d00aeed07ba405bc100a95000a9
|7,0=>0xea1c1e9e72e6975d7909bf393bd9f7bb6baa6085a37909c96999c848b5f08a9b48a50c7b9de7a24e77bdf7338c712886fe1a6b71b609935aa7e4e2864aa8e488544755538a223400f2ff862ff102eccc27a6d2649117d95168de1439c113ed0ee0e0e79c0bb3609799082ac05c0503e38
|8,0=>0xf55a6e3ebfacda19ee637ccdc51d3d434563aaf12ff10040d9
|9,0=>0xfffda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0cf0f00000f0f00000f0f00000f0a00000a0a00000a0a00000a0a00000a0af0f00000f0e00000f0f00000f0e00000f0f0000000000000f0f00000000f0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0af0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000f0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f00b0b00000b0b00000b0b00000b0b00000b0b00000a0a00000b0b00000a0af0f00000f0f00000f0f00000f0f00000000000000000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0f00000f0e00000f0f00000f0e00000f0000000f0000000f0000000f00e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0ef0f00000f0f00000f0f00000f0f00000a0a00000a0a00000a0a00000a0af0f00000f0f000000000000000000000f0f00000f0f0000000000000000
|0,1=>0xf0f00000f0f00000f0f00000a0a00000f0f0000000000000f0f00000000f0f00000b0b00000f0f00000b0b00000f0f00000a0a00000f0f00000a0af0f00000f0f00000f0f00000f0a00000f0000000f0000000f0000000f00f0f00000f0f00000f0f00000a0a00000f0f00000f0f00000f0f00000a0ae0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000000f0e00000f0e00000f0e00000f0e00000a0a00000a0a00000a0a00000a0a000000000000000000000000f0f00000000000000000000000000000e0ef0f00000f0f00000f0f00000f0f00000e0e00000e0e00000e0e00000e0ef0f00000f0f00000f0e00000f0e00000f0f00000f0f0000000000000000f0f00000a0a00000f0f00000a0a00000f0f00000a0a00000f0f00000a0af0f00000f0f00000f0f00000f0f00000f0f00000a0a00000f0f00000a0a00f0000000f0000000f0000000f0000000f0000000a0000000f0000000a00000000000000000000000000000000f0f00000e0e00000f0f00000e0ef0f00000f0f00000f0f0000000000000e0e00000e0e00000e0e00000000f0f00000f0f00000f0f00000e0e00000c0c00000c0c00000c0c00000c0c50500000505000005050000050500000505000004040000050500000404
|0,2=>0x10100000101000001010000010100000101000001010000010100000000f0f0000000000000f0f0000050500000f0f0000000000000f0f00000000f0f00000f0f00000f0f00000f0000000f0f00000f0f00000f0f00000f0010100000101000001010000010100000000000000000000000000000000f0f0000010100000f0f0000010100000f0f0000000000000f0f00000000000000000000000000000000f0f000000000000000000000000000000003030000030300000303000001010000030300000303000003030000000000000000f0f0000000000000f0f0000000000000e0e0000000000000e0ef0100000f0100000f0100000f0100000f0000000f0000000f0000000f005000000050000000500000005000000050000000500000005000000050010100000101000001010000010100000101000000000000010100000000b0b00000b0b00000b0b00000b0b00000b0b00000b0b00000b0b00000a0af0e00000f0e00000f0e00000f0e00000f0e00000f0e00000f0e00000f0ef0e00000f0e00000f0e00000f0e000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000f0e00000f0ef0f0000000000000f0f00000f0f00000f0f0000000000000f0f00000000
|0,3=>0xf0f0000000000000f0f0000000000000f0f0000000000000a0aa0b00000a0b00000a0b00000a0b00000a0a00000a0a00000a0a00000a0af0f00000f0f00000f0f00000a0a0000000000000000000000000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0010100000101000001010000010100000100000001000000010000000100b0b00000b0b00000b0b00000b0b00000b0a00000b0a00000b0a00000b0a5050000050500000505000005050000050500000505000005050000050000f0000000f0000000f0000000f0000000f0000000f0000000f0000000af0f00000e0e00000f0f00000e0e00000f0f00000e0e00000f0f00000e0e00000000000000000000000000000000f0f00000f0f00000f0f00000a0a303000003030000030300000003000003030000030300000303000000003030000030300000303000003030000030300000303000003030000020200000000000000000000000000000000f0f00000f0f00000f0f00000f0000000000f000000000000000f0f0000000000000f000000000000000f000000000000000000f0f00000f0f000000000000000000000e0e00000e0ef0f00000f0f00000f0f00000f0c00000c0c00000c0c00000c0c00000c0c
|0,4=>0xf0f00000f0000000f0f00000f0000000f0f0000000000000f0f0000000000000000f0f0000000000000f0f0000000000000a0a0000000000000a0a00000000f0f0000000000000f0f0000000000000f000000000000000f00f0f00000f0f00000f0f0000050500000f0f00000f0f00000f0f0000000050500000505000005050000050500000000000000000000000000000000f0f00000f0f00000f0f0000000f00000f0f00000f0f00000f0f00000000f0000000f0000000f0000000f000000000000000000000000000000000000f0000000f0000000f0000000f00000f0000000f0000000f0000000f0000f0000000f0000000f0000000f00000000000000000000000000000000f0f00000f0f00000f0f00000f0000000000000000000000000000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000a0a00f0000000f0000000f0000000f0000000f0000000f0000000f0000000000000000f000000000000000f000000000000000f000000000000000f00b0b00000b0b00000b0b00000b0b00000a0a00000a0a00000a0a00000a0aa0f00000a0f00000a0f00000a0f00000a0e00000a0e00000a0e00000a0ef0f00000e0e00000f0f00000e0e00000000000000000000000000000000
|0,5=>0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f00f0f00000f0f00000f0f00000f0f00000f0f00000e0e00000f0f00000e0e00f0000000f0000000f0000000f0000000e0000000e0000000e0000000e000000000000000000000000f0f00000000000000000000000000000a0a00100000001000000010000000100000000000000000000000000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f0f00000f0000000000f0f0000000000000f0f00000000000000000000000000000000a0a00000f0f00000a0a00000f0f00000a0a00000a0a00000a0a00000a0af0f00000f0f00000f0f00000f0f000005000000050000000500000005005050000050500000505000005050000050000000500000005000000050000000000000000000000000000000000f0e00000f0e00000f0e00000f0ef0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f00f0000000f0000000f0000000f0f00000f0000000f0000000f0000000f00f0f00000f0f00000f0f00000f0f00000f0a00000f0a00000f0a00000f0aa0a00000a0a00000a0a00000f0f00000a0a00000a0a00000a0a00000a0aa0f00000a0f00000a0f00000a0f00000a0a00000a0a00000a0a00000a0a
|0,6=>0xf0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000000000000000000000000000000f0000000f0000000f0000000f000000000000f000000000000000f00000000000000000000000000000000f0f00000f0f00000f0000000f0000000f0f00000f0f000000000000000000000000505000000000000050500000000000000000000000000000000f0500000f0500000f0500000f0500000f0000000f0000000f0000000f0000a0000000a0000000a0000000a00000a0a00000a0a00000a0a00000a0a00f0000000f0000000f0000000f0000000f000000000000000f00000000f0a00000f0a00000f0a00000f0a00000a0a00000a0a00000a0a00000a0aa0f00000a0f00000a0f00000a0f0000000000000000000000000000000000000000000000000000000050500000000000000000000000000000000f0f00000f0f00000f0f00000e0e00000f0f00000f0f00000f0f00000e0e
|_,_=>0
def sP:Nat→Nat
|0=>0xe0808044103981401108081c88a0a110870428288401c101107c38e02784070414b0704482880874701381039b0a1058234004090e445040e080972c1c1190a10398145ca880450293101c101121c112143038202007840e445080e088051e1038e1a30582140040704182840608080
|1=>0xa103826298288081d80a0a2020714bc2885c1c70a0a58487300800812385140ab44091638508121c10a58204870404288561c10a0a584070415508081c5290a2020736282960e094000a103823400288087470a0a5440e14502844e093000a203821494295101c1010a202074828284
|2=>0x1c29e05081c13a00144200e08505101038e7215b08121c70a107c38e1414f040e08005382048704144041c29c056e243820201b890e605006c2020704144040e29a851e202070404a880e08296101c701545820704c429c1e103820a2020714d02b3102438e145840730082880e38532
|3=>0x400284161c1010016508081c70a0a204871c045051e202070428284172070a00204871c2a388121c101101058e151a288081c105181c10a00142070418005081c101010040e1512185121038284002070504005121c10a01004071c29f85081c13e00147840e3853d2cac3820014407
|4=>0x14584071c04295102438e1415b840e080800a202071d445052c2438e02002070540005102c70a8614e0f081c70a0b3c58e14002070538005101c70a9a1420704c45056e2438214002cc101038e1414788081c70a96111870404005088c3981400295121038200144071c2a1855454207
|5=>0xa1038214a0005081c10a0016d890e3854d00142070428005805820704002ac102c38e15342840e0853b00142070560005081c15700142520e3ab000a245871c2a680095438214002d4122c70a00210071c282b6101038e1414404a61c70a0a2048b0e38504a41c1010014788081c701
|6=>0xa584070417008081c10a0a3c4071c2a185be202071c28288081c70114a84840e08080083808a28002840e601311416f040e085000a202071c282c62c3c4071c28288121c10a0b5048b1c28005081c10aba00288081c70ab814b090e380800a103820202c88081c10a0aaaa0b1c2a680
|7=>0x81c70ac8002840e085000ab02070428005b21038e1558005094838e0228005081c763001420b0e3854d0016a090e385000a2020704282d4082c70a00142071d405000a1038e14002e2081c70a9c002ad101058e141420e14500056e2038214144040e38505c21240e1400a841c28a00
|8=>0xe385680a1038e14002e7121038e0228016081c1000a105870428005099838e14002ad101038e14142071c045008e103824c00284a41c70a00144090e38505081c7011402c840e3b2800a242070428005081c10a0016389082c38e14002840e3ac0a001420b0e385000a1038e155c005
|9=>0xa582071c28005081c10a00142071c293000a105871c28005121038e1400284163850092542071c2800509a870a011cb090e385000a103980428005121038e0228005082c70a4c00284161c7011400a840e3808a00142071c28005d2dc2070428005082c38e1402584a42c38e1400284
|10=>0x81c70a00142071c280058e103ea1c28005081c70a00164840e385000b2c26b0e38500
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x6450bea16942aa8505096a119420a83c506ea0c9416a8285046a07940ca814501ea029402a8005
|5,0=>0x1d05394c7118df31b86364c6b18d331a06334c6518c731886304c5f18bb317062d4c5918af315862a4c5318a331406274c4d189731295246c47588bb1116216c41587fb0f961e6c3b5873b0e161b6c355867b0c96186c2f585bb0b16156c29584fb0996126c235843b08160f6c1d5837b0696
|6,0=>0x6f4adcddb63b6576bced619a8bb4a7686ecf1d9abb2f6650ec85d8d3b13761acc19d7fbaf875e2eba9d71badc75aaeb39d6432c26576ead1d56baa76542ca69d49ba8d650ce9fdd3cb27274d6e991d2f325864a4c92dd232a406474c8d1916ba26743ee861d08ba0a7406e7f58fb39ef73d0e785cedb1d56
|6,1=>0x1cf3b986724ce2ddc32b7f7
|7,0=>0x4d769a0f329a61bcbc796912b5e533c9e892ef241e44bc8188f6d1d1e36bc6768c0f165e293c4b788ad0f9e1c34317856d091e0ebc15881cf01de003bf977e4efaddf23bdc87accf3a1e3bbc16774eecddd63ba57
|8,0=>0x28dbd147a1af419e7fbcf879e4d3ade723cdd7
|9,0=>0x5226
|_,_=>0
def wAt:=mkWire dB 108 236 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2111415143914150e151439111d0e16080108011415081514391015080117270e150e140e16081508011e2910150801120b6e146e141439381414ed160b0e15041608151439081508150415143938171c292c1508010011081504151439101d0e15081508011016143908011e081015080108012c15461404162c150801120b
|1=>0x8150e110e1508a910160801381714210ea91016001108150e151c2914151415101508010011141508290815080114151439101608010829141508151c29151d0e160e130e1508011015080109250e150e1402131415143916130e1508013003041514390815112d141608010801141504150e09143912290815143910160801
|2=>0x101608011439081514152a1f02113003041514396e15080914395a140e2108011411101508010815143908010e110e150e6204150829141508151c2914150816101614390801082e0e15086204151439b413121d08156e14080914390416143916130e1508011565081614391c294c150e2b1559162b0e1516130e1546170e09
|3=>0x81615270e14081514390e16143908150e15156508160f1d0e164c150e2b121f08150416143908161439162b0e15021d141515250e1416130e15081d0815080114390e110e15151d0e164c160e2b021314150e150e212a1f2c15082908010809143917270e150e142c15082908011439100908010e13101508015a150e210801
|4=>0xe160e170e1414160e29082914390e2b0e1508150e150e142c1508290e170e160815141104151439141508150e150e2b14150e1502111415a8160e11080914390e1514160e1501250e142c16082914150815143914110e1514390f2d14160e21080114150e160e2b143916290e15081508011415
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0xc40000000000000000000000000002400000000000000000000000002000
|5,0=>0xa0c00027113080000000001210000000231000000040600000000000001f10e900003821930c080002e215200000000000000000504000000000000000011300003c80000d2000028c000073000000000005200000000000000208000000000
|6,0=>0x641b189866c035f12ecd724b63599ac0d5a6aa35412988000a33501a74d364983000254d2469024698001146873421a0890047d33d19e08ec47333891b8cd666923391948c465f32e19688ae6543289938c9a24a324892048a64232010f4c7463731a18c4c5c62b3
|6,1=>0x1aa4d236798001986cb1
|7,0=>0x12e29614a8a505262921488a4051e28e1468a3051718a944ca2250f286942ca12507282940ca024ff27e93ec9f24f727a93cc9e24ef27693ac9d24e7272938c9c24df26e936c9b24d72
|8,0=>0x27233819b8cd866a3341998cc86623301
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 13
def pmP:Nat→Nat
|0=>0x2c0400408000808001002001c40002830004108006200009000010800014880029000047a00084000100000120000220000400000408000800000c0000100000180000200000200000380000600000500000800000800000800000
|1=>0xdc4a01b0c40333380662500c4ee0188dc0311180566700ac4e01581c02913805011009c5a01198c02316804627008c0a0111b0021378042670084c80108bc0211080420200800800f0d401e1000342000682a00c0800101a801813
|2=>0x8945e1119902213304422708805e10480820710040a2c080458100808200018262670400c008010008100010042018cc60308040610000c04000f84a01e89403b1380762300ec4201d0940393080724000e44601c88403812806e35
|3=>0x80e46b0000c1c00200a62771084fe11d80422b03844e25
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0xc0000000000000010000000000000180
|5,0=>0x1000314000001000007000008000000031e0050b1c0060600000000028000000000b00240110048001000000200002801400000
|6,0=>0x3329c801c82c795a0423788cc4e84aba2c440185c48f4d006558b4401844aa5a8c67c40426385099aa6458af4045cdd833a90d2f414573b6cf8d3651ca3
|7,0=>0x43bf219cfb38b0d87951b5690c302d70df3b68b720318ef5c25612214a64f5bda90925bb8cde3dc
|8,0=>0x24c890c1aaa590a4bf
|9,0=>0x29
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_233 8 roots_233 ops++addP pm 1 dom_226 5 roots_226 ops++addP pm 2 dom_194 4 roots_194 ops++addP pm 3 dom_202 5 roots_202 ops++addP pm 4 dom_139 5 roots_139 ops++addP pm 5 dom_203 7 roots_203 ops++addP pm 6 dom_232 5 roots_232 ops++addP pm 7 dom_43 5 roots_43 ops++addP pm 8 dom_170 5 roots_170 ops++addP pm 9 dom_234 7 roots_234 ops++addP pm 10 dom_107 6 roots_107 ops++addP pm 11 dom_75 4 roots_75 ops++addP pm 12 dom_227 6 roots_227 ops++addP pm 13 dom_195 5 roots_195 ops++addP pm 14 dom_171 8 roots_171 ops++addP pm 15 dom_105 5 roots_105 ops++addP pm 16 dom_225 5 roots_225 ops++addP pm 17 dom_201 5 roots_201 ops++addP pm 18 dom_106 4 roots_106 ops++addP pm 19 dom_169 7 roots_169 ops++addP pm 20 dom_137 4 roots_137 ops++addP pm 21 dom_168 4 roots_168 ops++addP pm 22 dom_163 5 roots_163 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_235 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_163 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_233 8 s (0,roots_233.map (·&&&dom_233)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_235 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_233 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_235==dom_235)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_235 gM v ys):RunD true dom_235 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_235 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 21 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 61 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 61 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 70 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 70 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 45 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_235 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_227_16:=0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000
def gzo_227_16:=0xf0000000f0000000f0000000e0000000f0000000f0000000e0000000c0000
def gsh_227_16:=0xf0000000f0000000f0000000e0000000f0000000f0000000e0000000c
theorem lowS_zo_227_16_161:Lower true dzo_227_16 roots_227 gzo_227_16 6:=lower_iso_b (d1:=dom_227) (r1:=roots_227) (T1:=gsh_227_16) [(dom_227,16)] (by decide +kernel) (lower_slice_b (T:=gsh_227_16) [(0xc0000000c0000000c0000000c0000000c0000000c0000000c0000000c,0,2),(0xf0000000f00000000000000000000000f0000000f0000000000000000,0,64)] (by decide +kernel) lowS_161)
namespace S_243
def pG:List (Nat×Nat):=[(1,33),(1,65),(1,129),(2,18),(2,34),(2,66),(2,130),(3,19),(3,35),(3,67),(3,131),(16,18),(16,80),(17,19),(17,49),(17,81),(17,145),(32,33),(32,34),(32,160),(48,49),(48,50),(48,112),(48,176),(64,65),(64,66),(64,80),(64,192),(96,97),(96,98),(96,112),(96,224),(128,129),(128,130),(128,160),(128,192),(144,145),(144,146),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_243.map (·&&&dom_243)
def gM:=goal_243&&&dom_243
def NN:Nat→Nat
|7=>2
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xcf866295de
|8,0=>0x7a9f6
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000f000f00000000000f000f00000000000f000f00000000000f000f0000000000000000000000000000000000000000f0000000f0000000f0000000f0000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000ca000a000a000a000a000a000a000a000a000a000a000a000a000a000a000af000f000f000f0000000000000000000f000f000f000f0000000000000000f000f000f000f000f000f000f000f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2e688bda22c688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xcc06
|8,0=>0xc6
|_,_=>0
def wAt:=mkWire dB 8 244 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_242 7 roots_242 ops++addP pm 1 dom_179 7 roots_179 ops++addP pm 2 dom_241 7 roots_241 ops++addP pm 3 dom_227 6 roots_227 ops++addP pm 4 dom_211 7 roots_211 ops++addP pm 5 dom_115 6 roots_115 ops++addP pm 6 dzo_227_16 6 roots_227 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_243 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_227_16_161 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_242 7 s (0,roots_242.map (·&&&dom_242)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_243 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_242 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_243==dom_243)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_243 gM v ys):RunD true dom_243 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_243 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_243 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_243 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_243 roots_243 goal_243 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_243
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=S_243.noCircuit
def isoMvS_159:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_159:Lower true dom_159 roots_159 goal_159 8:=lower_iso_b isoMvS_159 (by decide +kernel) lowS_63
def isoMvS_183:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 8:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_126
def isoMvS_190:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 8:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_126
def isoMvS_237:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 10:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_187
def isoMvS_238:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_222
def isoMvS_245:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 10:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_221
def isoMvS_246:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_219
def isoMvS_249:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_187
def isoMvS_250:List (Nat×Nat):=[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_219
def isoMvS_252:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccccccccccccccccccc,126),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 10:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_125
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xcccccccccccccccccccccccccccccccc,16,18)] (by decide +kernel) lowS_125
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_slice_b [(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,16,20)] (by decide +kernel) lowS_187
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_slice_b [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,16,18)] (by decide +kernel) lowS_221
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,32,34)] (by decide +kernel) lowS_237
def dzo_167_16:=0xff000000ff0000000000000000000000ff000000ff0000
def gzo_167_16:=0xff000000fe0000000000000000000000fe000000fc0000
def gsh_167_16:=0xff000000fe0000000000000000000000fe000000fc
theorem lowS_zo_167_16_161:Lower true dzo_167_16 roots_167 gzo_167_16 6:=lower_iso_b (d1:=dom_167) (r1:=roots_167) (T1:=gsh_167_16) [(dom_167,16)] (by decide +kernel) (lower_slice_b (T:=gsh_167_16) [(0xcc000000cc0000000000000000000000cc000000cc,0,2),(0xf0000000f00000000000000000000000f0000000f0,0,4)] (by decide +kernel) lowS_161)
def dzo_225_16:=0x3000000030000000300000003000000030000000300000003000000030000
def gzo_225_16:=0x3000000030000000300000002000000030000000300000002000000000000
def gsh_225_16:=0x300000003000000030000000200000003000000030000000200000000
theorem lowS_zo_225_16_161:Lower true dzo_225_16 roots_225 gzo_225_16 5:=lower_iso_b (d1:=dom_225) (r1:=roots_225) (T1:=gsh_225_16) [(dom_225,16)] (by decide +kernel) (lower_slice_b (T:=gsh_225_16) [(0x300000003000000000000000000000003000000030000000000000000,0,64)] (by decide +kernel) lowS_161)
def dzo_163_4:=0xf0000000f00000000000000000000000f0000000f0
def gzo_163_4:=0xf0000000e00000000000000000000000e000000000
def gsh_163_4:=0xf0000000e00000000000000000000000e00000000
theorem lowS_zo_163_4_163:Lower true dzo_163_4 roots_163 gzo_163_4 5:=lower_iso_b (d1:=dom_163) (r1:=roots_163) (T1:=gsh_163_4) [(dom_163,4)] (by decide +kernel) (lower_slice_b (T:=gsh_163_4) [] (by decide +kernel) lowS_163)
def dzo_227_4:=0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0
def gzo_227_4:=0xf0000000f0000000f0000000e0000000f0000000f0000000e000000000
def gsh_227_4:=0xf0000000f0000000f0000000e0000000f0000000f0000000e00000000
theorem lowS_zo_227_4_163:Lower true dzo_227_4 roots_227 gzo_227_4 6:=lower_iso_b (d1:=dom_227) (r1:=roots_227) (T1:=gsh_227_4) [(dom_227,4)] (by decide +kernel) (lower_slice_b (T:=gsh_227_4) [(0xf0000000f00000000000000000000000f0000000f0000000000000000,0,64)] (by decide +kernel) lowS_163)
def dzo_231_16:=0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
def gzo_231_16:=0xff000000ff000000ff000000fe000000ff000000ff000000fe000000fc0000
def gsh_231_16:=0xff000000ff000000ff000000fe000000ff000000ff000000fe000000fc
theorem lowS_zo_231_16_161:Lower true dzo_231_16 roots_231 gzo_231_16 7:=lower_iso_b (d1:=dom_231) (r1:=roots_231) (T1:=gsh_231_16) [(dom_231,16)] (by decide +kernel) (lower_slice_b (T:=gsh_231_16) [(0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc,0,2),(0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0,0,4),(0xff000000ff0000000000000000000000ff000000ff0000000000000000,0,64)] (by decide +kernel) lowS_161)
def dzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
def gzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00ee00000000
def gsh_215_32:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00ee
theorem lowS_zo_215_32_84:Lower true dzo_215_32 roots_215 gzo_215_32 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_32) [(dom_215,32)] (by decide +kernel) (lower_slice_b (T:=gsh_215_32) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,0,2),(0xff00ff0000000000ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_179_4:=0xf000f000f000f0000000000000000000f000f000f000f0
def gzo_179_4:=0xf000f000f000e0000000000000000000f000e000f00000
def gsh_179_4:=0xf000f000f000e0000000000000000000f000e000f0000
theorem lowS_zo_179_4_163:Lower true dzo_179_4 roots_179 gzo_179_4 6:=lower_iso_b (d1:=dom_179) (r1:=roots_179) (T1:=gsh_179_4) [(dom_179,4)] (by decide +kernel) (lower_slice_b (T:=gsh_179_4) [(0xf0000000f00000000000000000000000f0000000f0000,0,16)] (by decide +kernel) lowS_163)
def dzo_243_4:=0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0
def gzo_243_4:=0xf000f000f000f000f000f000f000e000f000f000f000f000f000e000f00000
def gsh_243_4:=0xf000f000f000f000f000f000f000e000f000f000f000f000f000e000f0000
theorem lowS_zo_243_4_163:Lower true dzo_243_4 roots_243 gzo_243_4 7:=lower_iso_b (d1:=dom_243) (r1:=roots_243) (T1:=gsh_243_4) [(dom_243,4)] (by decide +kernel) (lower_slice_b (T:=gsh_243_4) [(0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000,0,16),(0xf000f000f000f0000000000000000000f000f000f000f0000000000000000,0,64)] (by decide +kernel) lowS_163)
def dzo_229_16:=0x33000000330000003300000033000000330000003300000033000000330000
def gzo_229_16:=0x33000000330000003300000032000000330000003300000032000000300000
def gsh_229_16:=0x3300000033000000330000003200000033000000330000003200000030
theorem lowS_zo_229_16_161:Lower true dzo_229_16 roots_229 gzo_229_16 6:=lower_iso_b (d1:=dom_229) (r1:=roots_229) (T1:=gsh_229_16) [(dom_229,16)] (by decide +kernel) (lower_slice_b (T:=gsh_229_16) [(0x3000000030000000300000003000000030000000300000003000000030,0,4),(0x3300000033000000000000000000000033000000330000000000000000,0,64)] (by decide +kernel) lowS_161)
def dzo_163_16:=0xf0000000f00000000000000000000000f0000000f0000
def gzo_163_16:=0xf0000000e00000000000000000000000e0000000c0000
def gsh_163_16:=0xf0000000e00000000000000000000000e0000000c
theorem lowS_zo_163_16_161:Lower true dzo_163_16 roots_163 gzo_163_16 5:=lower_iso_b (d1:=dom_163) (r1:=roots_163) (T1:=gsh_163_16) [(dom_163,16)] (by decide +kernel) (lower_slice_b (T:=gsh_163_16) [(0xc0000000c00000000000000000000000c0000000c,0,2)] (by decide +kernel) lowS_161)
def dzo_165_16:=0x3300000033000000000000000000000033000000330000
def gzo_165_16:=0x3300000032000000000000000000000032000000300000
def gsh_165_16:=0x330000003200000000000000000000003200000030
theorem lowS_zo_165_16_161:Lower true dzo_165_16 roots_165 gzo_165_16 5:=lower_iso_b (d1:=dom_165) (r1:=roots_165) (T1:=gsh_165_16) [(dom_165,16)] (by decide +kernel) (lower_slice_b (T:=gsh_165_16) [(0x300000003000000000000000000000003000000030,0,4)] (by decide +kernel) lowS_161)
def dzo_214_32:=0x55005500000000005500550000000000550055000000000055005500000000
def gzo_214_32:=0x55005500000000005500550000000000550054000000000054004400000000
def gsh_214_32:=0x550055000000000055005500000000005500540000000000540044
theorem lowS_zo_214_32_84:Lower true dzo_214_32 roots_214 gzo_214_32 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_32) [(dom_214,32)] (by decide +kernel) (lower_slice_b (T:=gsh_214_32) [(0x440044000000000044004400000000004400440000000000440044,0,2),(0x550055000000000055005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
namespace S_247
def pG:List (Nat×Nat):=[(1,33),(1,65),(1,129),(2,18),(2,34),(2,66),(2,130),(3,19),(3,35),(3,67),(3,131),(4,20),(4,68),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,23),(7,39),(7,71),(7,135),(16,18),(16,20),(16,80),(17,19),(17,21),(17,49),(17,81),(17,145),(32,33),(32,34),(32,160),(36,37),(36,38),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,112),(48,176),(64,65),(64,66),(64,68),(64,80),(64,192),(96,97),(96,98),(96,100),(96,112),(96,224),(128,129),(128,130),(128,160),(128,192),(132,133),(132,134),(132,148),(132,164),(132,196),(144,145),(144,146),(144,148),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_247.map (·&&&dom_247)
def gM:=goal_247&&&dom_247
def NN:Nat→Nat
|5=>7
|6=>35
|7=>129
|8=>282
|9=>190
|10=>21
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x9e2628d5a15271540f6b162360f73202a36
|6,0=>0xf020aec497e3df2e2743de5b8da464d4119d3ad0d2370d12becc063bc193ba5dbb8605b7a65b4147b2bebb1bd4a73479b8ee93daf73fa86d21361c5e5bb805a6a159c41520ac4d3152cd212bb8b1c1671a3e90835505f29
|7,0=>0xfecfafe62efa912f9cbef7ff1f558bf464ef3ea4f3b33f25d7f0f0deec17eebcaee5ceed0c3e5ed7e4694e2c09df107ded1cde09bdce16dcb94dcb70dc0a5dba5cd8cc2d7ddbd5ef4d5dd8d1556cfa35cca37cc95fcc6d2cae31ca205c8106c4f11c347abc19fb9b60b9aecb9349b7e5ab43c2b29e9aa678a7347a0f179e3639d72d9bf7197dfc96e1495bfe947d593bfa9336a921969125c8d9888b8448a9c08906e873c58631484c17830e17f2d17f1f47f0b17d06c7c7db7919a749c46a8306a6e968b816501e605e35a2fd59867597ae57cbe54a5e5489a5319451ebf515274d5e547da947961466894620a445573c46337903371273615634ee733bae33b17317343107e2de602cd0b2686c26286223752212f217581cd471b43b1aef418e711537514803142c50edb20ab29075ac05cb50542401552008300059f00568
|7,1=>0xff00d
|8,0=>0x7670876470763af740c673316732c772e727296b7169f7118170d416fef36f5176dcea6d4056c6f76b6456a1de69c2c68ded6725c6704066a4d6625864f5663518624865fab35e5bd5aae35a5e859c5657d5d57a15571395611954d61541ef53c6a533755240151b4e504eb4eb444e9fa4d31b4c6a54bb7c49e3149c6148c98481f047717475f547559456a145189429c441ece40833403353feda3f88f3ecea3d9793d6153c8fc3c2c83c1c13b6493a6da390d63900a38e2537ba13403a3396f2fcab2f9d62c1552a99d2a7f22a29b2a24f29fcd2964f28173260fb2549123bdf2343c22569214e1213702115720dfd204ec1fbff1f56b1eaf31d69b1bd121a36519b8a191fb1763e15cb81537514bc712c72113d00fe6f0e1fd0e1830c9180c34b0ab29087cd084bc076a105774048fd048eb041710394502ee20106d001d7
|8,1=>0xeffeaef3f8edfdced854ed1d4ec56beb970eb8d0eab95e9752e92e7e8b2be8989e832ce77d5e715fe6ca8e6bd0e69d9e539de4b20e328de1cace0e9ce0c4edf953df605de695de197ddd4fdd119dcb9edc582dad6bda4abd5025d4026d317ed2f2bd28e2d0fedd0ec1cfacfceec0ced18ce252ce00ecce06caf04cad7cca875ca5a7c9ab1c996fc86edc8146c7f34c7401c481bc4680c3c9ac3673c2ee1c2cc5bee48be98dbc77cbc34ebb6c8ba242b7e5ab702fb68eeb450db2607b2566b2385b09e6ae4b3ad7d3ad481abd5aaabb1aa921a9ec7a8fa3a8486a7a0fa778ea35f2a31759f9f69eed29ccd39bdf09b8279b8189a1eb991e8980c397f5397f4d9591494e9d94dd694d5b93574911f38fb0b8b65b8b08089b0e87ab78734d86c388456083e3e82e2682080808fd801047cdb57cc047b9d87b0197a8877a3d676c5d
|8,2=>0xff929fea1ffe963fe64efd707fc864f981af9539f911bf7fe5f7692f71c5f610ff60a2f4d4df4515f37c0f377ef3610f3161f30c6f2ebff23d5f1f52f13b8f00f2
|9,0=>0xb0856afca2af571a9c2fa9b84a7987a63bba3d7ca2241a0be3a02449f49f95b059463993ea092d619188990afe9006e8d7138cd078c92d8c79a8bd23896fc888448862b87aef8794986b6985d9685c8e84b7684b758218f8021f7fd217f89d7e6d67de4c7ddc07d2007d1ae7b98c781d3744ac736127311c715e1707c66fb636b2da6a68e6a6126a1de6935a67b5f6713a651b364e7d641cf633fa60b435d0ec5bbf55a233596df5766c5754f55a5c54d615420751b184f4c84df404dbe94d3184908a48c354601e45a6d43b5d424bd413cf403353e40b3c4633ba603afba3a32e3a1ef37b9a3671534a6b30b1530a91300542fe902f9d62e77329b37299fd28f9b277bc22fba22d9518eb618a2917c83179111362f135a51294611ab4108ad104480f5380e78e0c8b60b4670a261080d9057740420702d7f02040019af01756
|9,1=>0xfef42fd924fcd5ffc7e9fc168f76eff5a94f5a42f5567f49fdf4780f2e8cf2c02f1f52f1695eee44eb7b2e9627e9229e726ee6d67e39e1e2b61e1a1be031adf3e0de8beddb2edd668dc118db9a6db339daa90d8de6d8c40d7ad4d6d19d6743d60ebd4406d420bd3f63d0091cff03cde25cdb14c7691c7335c6be2c2d7bc1a6cc1903bed16bde8cbc7a1bbffebb3c4baa05b9339b68eeb31d4b2322
|10,0=>0xff591fd8d6f9dd7f4e48c7335c7110b47c3af7e2a9ffe9ac0299c1f975b0931bf85a0a81ea97fd217be4f6aad43c1d5343e91e642
|11,0=>0x3ef7d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff000000ff000000ff000000ff000000ff000000ff00ff000000ff0000fe00fe00fe00fe00fe00ee00fe00ee00fe00fe00fe00fe00fe00ee00fe00eefc00fc00fc00fc00fc00cc00fc00cc00fc00fc00fc00fc00fc00cc00fc00cc00000000ff00ff0000000000ff00ff0000000000fe00fe0000000000fe00eeff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000000000000000005500550055005500000055000000550055005500000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccff00ff00ff00ff00ff00ff00aa00aa00ff00aa00ff00aa00aa00aa00aa00aaff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0ff00ff00ff00ff00ff00ff00cc00cc00ff00cc00ff00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000
|0,1=>0xff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f0000000f0000ff00ff00ff00ff00ff00ff0000000000ff000000ff000000ff000000000000000000000000000000000000ff00ff000000ff000000ff0000000000000000000000000000000000000000000000000000000000000000ff000000ff00000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000ff00ff00ff00ff000000000000000000ff000000ff00000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000f000f000f000f000f0000000f0000000f000f000f000f000f0000000f00000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff00cc00cc00cc00cc00ff00cc00ff00cc00cc00cc00cc00cc5500550055005500550055005500550055005500550055005500550000000000000000000000000000000000000000fe00fe00fe00fe00fe00ee00fe00eeff00ff00ff00ff00ff00ff00ff00ff00fc00fc00fc00fc00fc00cc00fc00cc00000000000000000000000000000000ff00ff00ff00ff00ff00ff00000000
|0,2=>0xff00ff00ff00ff000000ff000000ff00ff00ff00000000000000000000000000000000000000000000ff000000ff00ff00ff00000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff000000000000ff000000ff0000000000000000000000ff000000ff000000000000000000000000ff000000ff00ff000000ff0000000000ff000000ff00ff000000ff000000000f0000000f000f0000000f00000000000f0000000f000f0000000f0000f000f000f000f000f0000000f0000000f000f000f000f000f0000000f000f000000000000000000000ff000000ff0000000000000000000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000fc00fc00fc00fc00fc00cc00fc00cc00fc00fc00fc00fc00fc00cc00fc00fcf000f000f000f000f000f000f000f000f000f000f000f000f0000000f00000ff00ff00ff00ff00ff00ff0000000000ff000000ff00000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00fe00fe00fe00fe00fe00ee00fe00ee0f000f000f000f000f0000000f0000000f000f000f000f000f0000000f0000ff00ff00ff00ff00aa00aa00aa00aa00ff00aa00ff00aa00aa00aa00aa00aa
|0,3=>0xff000000ff000000ff000000ff000000ff000000ff00ff00ff00000000ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff000000000000ff00ff0000000000ff00ff0000000000ff00ff00000000000000000000000000000000ff000000ff00ff000000000000000000ff000000ff00000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000ff00f000ff00f000ff00f000ff00f000ff00f000ff00f000ff00f000ff00f0ff000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000ff000000ff0000000000000000000000ff00ff00ff0000000000000000ff000000ff000000ff000000ff000000ff00000000000000ff000000000000ff00ff000000ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff000000ff000000000000000000000000ff00ff00ff00ff000000000000000000ff00ff00000000ff00cc00ff00cc00cc00cc00cc00cc00ff00cc00ff00cc00cc00cc00cc00ccff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000ff000000ff000000ff000000ff000000ff000000ff000000000000000000000000000000000000ff00f000ff00f0000000000000000000ff00f000ff00f0
|0,4=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff000f000f00ff00ff00000000ff00ff000f000f00ff00ff0000000000ff00ff000f000f00ff00ff00000000ff00f000ff00f000f000f000f000f000ff00f000ff00f000f000f000f000f0ff00000000000000ff00000000000000ff00000000000000ff000000ff0000ff00ff00ff00ff00ff00000000000000ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000f000f000f0ff000000ff000000ff00000000000000ff000000ff000000ff000000000000ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000000000000000000000000000000000000000ff00ff000000ff00ff00ff000000000000000000000000ff000000ff0000000000000000000000ff000000ff00000f000f000f000f000f000f000f000f000f000f000f000f000000000000000055005500550055005500550055005500550055000500050055005500000000ff00ff00ff00ff00ff00ff00ff00ff000f000f000f000f0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000000000ff000f00ff000f00ff000000ff000000ff000f00ff000f00ff000000ff00000f000f000f000f0000000000000000000f000f000f000f0000000000000000
|0,5=>0xff000000ff000000ff00ff00ff000000ff000000ff0000000000000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff000000000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000ff000000ff000000ff000000ff00ff00ff000000ff00000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00f000f000f000f000f000f000f000f0ff00ff00ff00ff00ff00ff0000000000f000f000f000f000f000f000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000f000f00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000550055005500550055005500550055005500550000005500550055000000000000ff000000ff000000ff000000ff000000ff000000ff000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00000000ff000000ff0000000000000000000000ff000000ff00000000000000ff0000ff00aa00ff00aa00aa00aa00aa00aa00ff00aa00ff00aa00aa00aa00ff00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000033003300330033003300330033003300330033003300330033003300330000
|0,6=>0xff000000ff000000ff00ff0000000000ff000000ff000000ff00ff00000000000000000000ff00ff00ff00ff000000ff000000ff0000000000000000ff000000ff0000000000000000000000ff000000ff00ff00000000000000000000ff000000ff000000ff000000ff000000ff00000000000000ff00000000ff00ff00ff000000ff00ff0000000000ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000000000000000000000000000000f000f000f000f000f000f00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00000000ff00ff00ff00ff00f000f000f000f000ff00ff00ff00ff00f000f000f000f00f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000000000000ff00ff0000000000ff00ff0000000000ff00ff00ff000000ff0000ff00ff00ff00ff00f000f000f000f000ff00f000ff00f000f000f000f000f0ff000000ff000000ff00000000000000ff000000ff000000ff00ff0000000000000000000000000000000000000000ff000000ff000000ff000000ff0000ff00ff000000ff00ff00ff0000000000ff00ff000000ff00ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff0000000000000000
|0,7=>0xff00ff0000000000ff00ff0000000000ff00000000000000ff00ff00000000ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000000055005500550055005500550055005500550055005500550055005500550000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000f0550055005500550055005500550055005500550055005500550055005000500000ff000000ff000000ff000000ff000000f0000000f0000000f0000000f00f00ff000f00ff000f00ff000f00ff000f00f0000f00f0000f00f0000f00f0000000000000000000000000000000000000ff000000ff000000ff00000000ff00ff00ff00ff000f0000000f000000ff00ff00ff00ff000f0000000f0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00ff00000000ff000000ff000000ff00000000000000ff000000ff00ff00ff00000000ff00ff000000ff00ff00ff000000ff00ff00ff000000ff0000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00000f000f000f000f000f000ff00f000ff00f000f000f000f000f000ff00f000f0000000000000000000000000ff000000000000000000000000000000ff0000
|0,8=>0xff000000ff00ff00ff000000ff00ff00ff000000ff00f000ff000000ff00f000000000ff00ff0000000000ff00ff00000000000000ff000000000000000000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff0000f000f000ff00ff00f000f000ff00ff00f000f000ff00f000f000f000ff00f0ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff00000000ff00ff00ff00ff0000000000000000000000ff000000ff00000000000000000000000000000000ff00ff0000000000ff00000000000000ff00ff00000000ff00ff000f000000ff00ff000f000000ff00ff000f000000ff00ff000f000000000000ff00000000000000ff00000000000000ff00000000000000ff0000ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00000000000000ff00000000000000000000000000000000000000000000ff00ff0000000000000000ff00ff0000000000ff00ff0000000000ff00ff00ff00ff00ff00ff00000000ff00aa00ff00aa00aa00aa00aa00aa00ff00aa00ff00aa00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff000000ff000000000000ff00ff0000000000ff00ff00000000000000000000000000ff0000000000000000000000000000000000000000ff000000ff0000000000000000
|0,9=>0xff00ff00ff00000000000000000000000000000000000000000000ff00000000000000ff0000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00ff00aa00aa00aa00ff00aaff00ff0000000000ff00ff0000000000ff00ff000000ff00ff00ff00000000ff00ff00ff00ff000000ff000000ff00ff00ff00000000000000ff000000000000000000000000000000000000000000000000ff00ff0000000000ff0000ff00ff00ff00ff0000000000ff000000ff00ff00ff00ff0000000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff000000000000000000000000000000000000ff00ff000f000f00ff00ff00000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff000000ff00ff00000000ff00ff00ff00ff00ff00f000ff00f000ff00ff00ff00ff00ff00f000ff00f0ff00ff00ff00ff00ff00ff00000000000000ff000000ff000000ff000000000f000f000f000f000f000f000f000f000f000f00000000000f000f00000000ff000f00ff000f00ff000f00ff000f00ff000f00ff000000ff000f00ff0000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff000000000000ff00ff0000000000ff00ff0000000000f000f00000000000f000f0
|0,10=>0xff00ff00ff000000ff00ff00ff000000ff00ff00ff000000000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000000000f000f000f000f000f000f000f0000000f000f000f000f000f000f000f00000f000f000f000f000f000f00000000000f000f000f000f000f000f00000000ff00ff00ff00ff00ff00ff00ff00ff000f000f000f000f000f000f00000000ff000000ff000000ff000000ff000000ff000000ff00ff00ff000000ff00000000000000000000ff00ff00000000000000ff0000000000ff00ff00000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00ff0000ff000000ff000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff0000ff00ff000000ff000000000000000000ff00ff000000ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000000000000000ff00ff000f000f00ff00ff000f000f00ff00ff000f000f00ff00ff000000000000000000000000ff00ff00ff00ff000000000000000000ff000000ff000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff000000000000000000000000000000000000ff000000ff000000ff000000000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000
|0,11=>0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000ff000000000000ff00ff0000000000ff00000000000000ff00ff0000000000ff000000000000ff00ff0000000000ff00ff00000000000f000f00000000000000000000000000000000ff00ff00ff0000000000000000000000ff00ff00ff00000000f0000000f000f000f000f000f0000000f0000000f000f000f000f000f0ff00ff00ff000000ff00ff0000000000ff00ff00ff000000ff00ff00000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff000000ff000000ff0000ff000000ff000000ff00ff00ff00ff00ff00000000000000ff00ff00000000ff00ff00ff00ff00ff00ff0000000000ff00ff000000ff00ff00ff000000000000000000000000ff000000ff00000000000000ff000000ff000000ff0000ff000000ff000000ff000000ff000000ff00000000000000ff000000ff000000000000000000000000000000000000ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00000000000000000000000000ff00ff00000000f000f000f000f000f000f000f0000000f000f000f000f000f000f000f00000ff00ff00ff00ff000000000000000000ff00ff000000000000000000000000000000000000ff000000000000000000000000000000ff0000000000000000
|0,12=>0xf000f000ff00ff00f000f000ff00ff00f000f000ff00ff00f000f000f000f00000ff000000ff00ff00ff00ff00ff000000ff0000000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00f000ff00f000ff00f000ff00f000000000ff00ff0000000000ff00ff0000000000ff00f00000000000ff00f0ff00ff00ff00ff000000000000000000ff00ff000000ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000f000000ff00ff000f000000000000000000000000000000000000ff00ff00ff00ff00ff000000ff0000ff00ff0000000000ff00ff0000000000ff00ff00ff00ff00ff00ff00ff000000000000ff00ff0000000000ff00ff0000000000ff00000000000000000000000000000000000000000000ff00ff00000000000000000000000000ff0000ff000000ff000000ff000000ff000000ff00ff00ff00ff00ff000000ff00000f0000000f0000000f0000000f0000000f000f000f000f000f0000000f0000ff00ff00ff00ff00ff000000ff000000ff00ff0000000000ff00000000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000f000f0ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff0000000000ff00000000000000000000ff00ff00000000000000000000000000ff00ff00000000
|0,13=>0xff00ff00f000f000ff00ff00f000f000ff00ff00f000f000ff00ff00f000f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000f000ff00ff00f000f0ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000f000f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000ff000000ff000000ff000000ff000000f0000000f0000000f0000000f000000000000000000000f000f000f000f0000000f0000000f000f000f000f000f0ff00ff00ff0000000000000000000000ff00ff00ff00000000000000000000ff00ff00ff00ff00ff00ff00ff00ff000f0000000f0000000f0000000f000000000000ff00ff0000000000ff00ff00000000000f000000000000000f0000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000000000ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff000000000000ff00f00000000000ff00f00000000000ff00f00000000000ff00f0ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00f00000000000ff00f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000ff00ff00ff00f0ff00ff00ff00ff000f000f000f000f00ff00ff00ff00ff000f000f00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00ff0000
|0,14=>0xff00ff00ff00f000ff00ff00ff00f000ff00ff00ff00f000ff00ff00ff00f0ff000000ff00ff00ff000000ff000000ff000000ff00ff00ff000000ff0000f000f000ff00f000f000f000ff00f000f000f000ff00f000f000f000ff00f0ff00ff0000000000ff00ff00000000000000000000000000ff00ff0000000000000000ff00ff00000000000000000000000000ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff0000000000000000f0000000f0000000ff000000ff000000f0000000f0000000ff000000ff0000f000f000f000f000ff00f000ff00f000f000f000f000f000ff00f000ff00f0000000000000000000000000000000000f0000000f0000000f0000000f00000f000f000f0000000f000f000f0000000f000f000f0000000f000f000f000000000000000000000000000000000000ff00f000ff00f000ff00f000ff00f0ff00ff00ff00ff00ff00ff00f000f000ff00ff00ff00ff00ff00ff00f000f00000ff0000000000ff00ff00000000000000ff0000000000ff00ff00000000f000f000f000f000f000f000f000f000ff00f000ff00f000ff00f000ff00f00000ff000000ff00ff00ff00ff00ff00000000000000000000000000000000ff00ff0000000000ff00ff00ff000000ff00ff0000000000ff00ff00ff0000
|0,15=>0xff00ff00ff00ff000000000000000000f000f000f000f0ff000000ff000000ff000000ff0000000000000000000000ff000000ff000000000000000000000f0000000f00000000000000000000000f0000000f0000000000000f000000000000000f000000000000000f000000000000000f0000ff00000000000000ff000000ff000000ff00000000000000ff000000ff00000f000f000f000f000f000f000f000f000f0000000f0000000f0000000f000000000000000000000000000000000000ff00ff00ff000000ff00ff00ff0000f000f00000000000ff00ff0000000000f000f00000000000ff00ff00000000ff00ff0000000000ff00ff0000000000ff00ff00ff000000ff00ff00ff0000ff00000000000000ff00ff0000000000ff00000000000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x10a050403070100240523040307010005090f0307010a0904220e0d0b0a09040713210b0a1709040307200009040307130b1f05100407011e000504030701001c05101b0307011a1709040314010009040e120d0b0a09040314130009040e12110b05100f030701040e0d0c0b0a090403070800050403070600050403020100
|1=>0x9040e110b0a05040713210b0a05103203070131051004250701000530040307130a092f0403070100090407131e0b0a09040307130019052e040307010027091507012a0a10042d0307010027092b0701210a27092b07012a0a051004070121000504030701001f090426010b0a0904030701001c09042507130b0a050f0307
|2=>0x100403070100312709040701210b0a2709150701212c0a093f040307010b0a053415040307010a09043c030701000a05040307133b0b0a270915040d010b0a0515040307130b0a053a040307130b0a091839030701000b36040307010b0a09180d010b0a09180307130b31100403070135000534040701210a2709153301210a
|3=>0x420307010017090407011e0b0a051b0307011a0a470904030701000b05090407011e000a0904460307130b0a051004030701004509040307130b1a0a27094107013b0b0a27091507013b400a170904030701001905091b0307011a0a09153301210a09040307440b430a09042907010b0a090442030701000b09150314010a05
|4=>0x307010b31091b030701550b0a050403070154000a050918030701003109041d0307010009041b0307130b0a09040307520b0a09040301500b0a090f0307010b0a4e040307440b0a05042d030701000a2709154d07010a050407011e000a094b04030701000a1705040701210b0a170530040307010a0510044a030701000504
|5=>0x510040701210b0a0504030701005f0a0932390307010b0a0932040307130b0a051030040307010a09040307133b0b0a5e0918030701000b0915040307130b0a050403070135000a093a040307130b0a0504030701005c0a051803070100310504035a070100090407011e0b3d0a050403070159000a09040307560b0a170918
|6=>0x1660b0a0504030701001f09040314010027092b0307010a0527040701210b0a0904650307010b0a09156407010a1709040307010b1f0904110d010b0a050904030701001f056304030701000a09620d010b0a09040e0d0b0a0510044603070100051004030701001a61040307560b0a09040307560b600a09045b030713000b
|7=>0xb450a0904030701006e6b040307010b0a2709150333010a0504070121000a05046a030701000a050403070169000934040701210b0a2709040d010b0a053404460307010a1709040701210b0a050904070121000a0504460307130b0a09040307130b310a6809040307010b1f0510041b0307010027093a156707010a090407
|8=>0x1000a09040307440b0a0904030720000918030701000b7305103204030701002709152b0307010a0510040307013b001709042507010b0a05041d03070100051015040307010009047207010b0a050932030701310a050904250701000a05103a040307010009044a0307130b0a09047107010b0a0307016f0b0a0904030713
|9=>0xa7f040307010b0a05040307015d000a09040307017e0b0a1009040701210b0a091804030713000b090403077d0b0a090403077b0b0a090701790b0a091507012a0a05040307017800270904070177400a750904030701000a092b0701210a092b07012a0a057404030701000a0532030701310a09040701210b3d0a05042507
|10=>0x40307010b0a09040307010b8e0a09048c0307010b0a05040307018b0b0a27093a046707010b0a89040307010b0a0504420307010b0a09150333010a05091804030701008809045b07010b0a051004030701000b090403070186000b84040307010b0a09040d010b0a7509040307010b0a2709040307830b0a0904030701810b
|11=>0xa5861040307010b0a270904030701770b0a05090403070100310a5809040307010b600a0932040307010b3d0a9109620307010b0a09152b0307010a0518040307010009040307013b0b3d0a4f09040307010b0a0915040307010b3d0a091b0307010b1a0a0904030701690b0a093a040307010b3d0a2709040701210b0a098f
|12=>0x701000b0a09040307010b1f1009040307013b0b0a090407011e000b0a6127040307010b0a91490307010b0a09041d0307010b0a100915040307010b0a9609040307010b0a2709040333010b0a10093a040307010b0a270995040307010b0a170504460307010b0a1709040307010b310a0904030701940b0a0992040307010b
|13=>0x7010b0a0509044a030701000a27091504030701400a9c09040307010b0a09040307019b0b0a09040307019a0b0a09040307130b0a96040307010b0a1709040307010b450a0534040307010b0a0904030701980b0a05090403070100450a0915030701190a9709040307010b0a0904070177400a050403070100310a48090403
|14=>0x904a3030701000a050403070100450a09621607010b0a0904030701a2000b0a097604030701000a5e0904030701000b0a0904a10307010b0a9f0904030701000b0a090403079d0b0a0915040d010b0a270941040307010b0a0904030701780b0a1709044a0307010b0a270904030701210b0a270915040307010b0a0504035a
|15=>0x30701000b0a091803070187000ba709040307010b0a7c09040307010b0a09040307010ba50a270915040701210b0a09040701210b0a09150701212c0aa40904030701000b0a2709150307013b0b0a05044a030701000a09040307010b730a9c040307010b0a0918030701000b314f09040307010b430a27093a150307010b0a
|16=>0x50449030701000a094107013b0b0a17053a040307010b0a61040307010b0a0504030701a60a17091804030701000b09040307010baf0a0904030701ae0b0a051004460307010b0a091507013b400a05040701ad0b0a0904030701ab0b0a09aa040307010b0a4e27040307010b0a09044c0307010b0aa9040307010b0aa80904
|17=>0x7010b0a68ba040307010b0a09042507010b0a09040314010b0a09b9040307010b0a09b8040307010b0ab709040307010b0a0904b60307010b0a0904b50307010b0a0307015d700b0a05b3040307010a1705040307013b0b0a0904030701550b0a0504b207010b0a0504030701b10a170515040307010b0a0904390307010b0a
|18=>0x701000b1f090407013b0b430a0504030701930b0a09040307018b0b0a09154d07010ab7040307010b0a0904420307010b0a09040307010bbd0abc05040307010a27090407013b0b400a093e040307010b0a100904030701000b052704460307010b0a6809040307010b1f0a2709041607010b0a270904bb07010b0a4f4e0403
|19=>0xa05100403070100170904460307010b0a091804030701000b3d5109040307010b0a05090446030701000a4e97040307010b0a1709040307010b1a0a0904030713000b0a050904030701001a0a0509045b0307010009040307010b380a090403070198000b0aa0490307010b0a0904030701bf0b0a0918030701be0b0a090403
|20=>0x5103a040307010b0a0904030701000b730a0904c30307010b0a050446030701000a0904030701c20b0a0504030701940b0a0904030701c10b0ac0040701210b0a0504030701001a0a05045b03070100093404460307010b0a0918030701990b0a2709044d07010b0a0504030701690b0a270946030701570a4709040307010b
|21=>0x1000baf0a0904030701ae000b0a090403070100191709041b0307010b0a270915041607010b0a0509041b030701000a09040307200b0a09044c030701000b0a6809040307010b1f09181607010b0a0504030701000a0510040307013b0b0a05041d0307010b0aba27040307010b0a051015040307010b0a0904070121000b0a
|22=>0x7010a090403070155000b0a09040307010b1fc70504030701780b0a0527040307013b0b0a0509040701210b0a0904030701c60b0a090439030701000b0a052715040307010b0a09040701c40b0a6147040307010b0a6809040307010b0a05273a040307010b0a05040307130b0a0907013b7a0b0a0504030701990a09040307
|23=>0x1210b0a09040701ad0b0a093e04030701000b0a0504030701ac000a09040307010bc70a0530040307010a4809040307010b0ac809040307010b0a09320307010b310a0904250701000b0a05040307016c0b0a27091504670307010a0504a10307010b0a05041b030701000a090407011e0b0a0904460307010b3d0a05340403
|24=>0xa170915040307010b0a0509040307013b000ad209040307010b0a0904030701d10b0ad009040307010b0a05091504030701000a17093a040307010b0a0904cf0307010b0a09ce040307010b0a05093a04030701000a0904030701cc0b0a09040307010bcb0a100904460307010b0aca09040307010b0a092b0307010a050407
|25=>0x504030701d90a2709040307010b1f0504030701ae0b0a0904030701a20b0a0904030701d70b0a170932040307010b0a5e09040307010b0a9f09040307010b0a0504030701ab0b0a05093204030701000a0904030701530b0a1709040307013b0b0a0904d60307010b0a0904b207010b0a0904030701d50b0a0904030701d30b
|26=>0x1280b0aa409040307010b0a051504030701000a09040307010b6d0a5809040307010b0a0504390307010b0a091803db07010b0307015d870b0a053a04030701000a0904da07010b0a09046407010b0a1709045b030701000b093415040307010b0a09180307010b31093a156707010aba040307010b0a09041b0307010b3d0a
|27=>0x13b0b0a0515040307010b0a84040307010b0a053a040307010b0ade09040307010b0a170904030701000b0a091804030701000b0904030701930b0a0904030701dd0b0a2709150307012c0aa809040307010b0a09040307010bdc0a053204030701000a0504370307010b0a05040307013b000a0504030701550b0a09040307
|28=>0xa090403070187000b0a9105040307010b0ae3040307010b0a0904030701000b310a09040307019e0b0a09e2040307010b0a09040307010be1e009040307010b0a05040307015d0b0a091504670307010a050904030701000b0a0918040307018d0b0a0915620307010b0a09045b07013b0b0adf0904030701000b0a05040307
|29=>0x504030701b40adf09045b07010b0adf05040307010b0a09044a030701000b0a0904030701000b3d0a09040307010b1a0a0904030701e70b0a0918460307010b0a0904030701000b450a09040307010b1f1705040307010b0a0904030701e60b0a09e5040307010b0ae405040307010b0a050904030701b40a0504030701000b
|30=>0x30701870b0a09040307010ba60a093a046707010b0a09040307010b800ac0045b0307010b0a09040307016c0b0a2709040307010b570a0904030701700b0a09040307830b0a2709040307013b0b0a093a460307010b0a270915040307010b0a09150307012c0a27093a040307010b0a0904030701d80b0a09040307010b850a
|31=>0x307010b0a09e8040307010b0a0995040307010b0a0904820307010b0a0904030701ac0b0a0904030701770b0a0904a30307010b0a0918045b0307010b2709040307010b2c0a0976040307010b0a6109040307010b0a09041b0307010b0aa00904030701000b0a09040701210b0a09040307010bb10ac004620307010b0a0504
|32=>0x10b0aa0df040307010b0a0915180307010b0a09040307010bea0a0904370307010b0a09040307010b430a050904620307010b0a0510040307010b0a0904030701860b0a0904e90307010b0a050904490307010b0a0509045b0307010b0a2709040307010b400a61040307010b0a09040307010b600a09040333010b0abc0904
|33=>0x7010b0ac004460307010b0a0904ed0307010b0a0527040307010b0a090403070100eb0a0932040307010b0a0504620307010b0a09040307010b8a0a0941040307010b0aa005040307010b0a0904030701210b0a0915040307010b0aec040307010b0a091504030701400a0504490307010b0a8809040307010b0a05045b0307
|34=>0x10b0a09040307010bb00a4e040307010b0a0915040701210b0a09040307010b190a0904030701be0b0a09150307013b0b0a09ee040307010b0a9109040307010b0a090446030701000b0a0904030701d40b0a093a150307010b0a4e09040307010b0a0904030701000b1a0a09045b030701000b09040307015d0b0aa0096203
|35=>0x10b310a09041607010b0a0904bb07010b0a0930040307010b0a0504030701000a09041b030701000b0a0934040307010b0af1040307010b0aa009045b0307010b0af009040307010b0a050904460307010b0aef09040307010b0a0904030701990b0a1709040307010b0a050904030701000a09cd040307010b0ae409040307
|36=>0x307010bd90a09040307010b450ac015040307010b0ac03a040307010b0af3040307010b0a0504030701700b0af209040307010b0a09c5040307010b0a05040307010b0a0904675b07010b0a0918030701870b0a090407013b0b400a09c9040307010b0ac018040307010b0a090403db07010b0a0504460307010b0a09040307
|37=>0xa050918040307010b0aba09040307010b0a0946030701570a09040307013b000b0a0904f60307010b0a09040307017a0b0a091504030701000b0adf0918040307010b0a09044a0307010b0a09040307010b3d0a050904030701ac0b0a093a04030701000b0a0904030701f50b0af409040307010b0ac0040307013b0b0a0904
|38=>0x915040307010b0a270904460307010b0a09040307010b1f0a0518040307010b0a8409040307010b0aba040307010b0a05093a040307010b0ac004030701000b0a0504030701ac0b0a0904030701900b0a1009040307010b0a0904030701f80b0a0904030701f70b0a09040307018d0b0a09044d07010b0a093204030701000b
|39=>0x10b570a09040307013b0b0a0915040307010b0a093a040307010b0a0918040307010b0a0904670307010b0a0904460307010b0a09040307010bb40a0509040307015d0b0a090403fa07010b0a0904f90307010b0a270904670307010b0a0915041607010b0a0509040307013b0b0a0904490307010b0aa009180307010b0a05
|40=>0x9040307010b0a2709040307010b0a0904620307010b0aa009040307010b0a09045b0307010b0a05040307010b0a0904030701870b0a0509040307010b0adf09040307010b0a09040307010b400a0904030701000b0a09040307010b2c0a09040307010beb0ac0040307010b0a09040307
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x91803cc018600930031800cc0006
|6,0=>0x455c21ce1077080383e981e6e0ec7072b8379c1aee0d07064b8309c176e0b47056b8299c13ee09870493022dc108e07e603bb81c1c0d2e062702db8151c09ae046701fb80e1c062e02a7
|7,0=>0x18040be205e102e8817040b6205a102c8816040ae2056102a88150b8a69c525028a8141b89ee04e7026b8131c0971c4a9024d7123388fdc470e2308114b8889c435021281054080a03f6e1f380f63879203b901d480e640712037901b480d640692033cc19680c7b861e0302c17980b8c05a602c3015980a8c0526028301398098c04a60244e11c6
|7,1=>0x26c41345c994e4c4625f312ddc95f04a78250b126d8927048c7242411f5c8ece47062344118208b10450822441105c873043272154108a083504128205b901587fb03f671f7b8fa1c7c2e3d981e938f2a0786e3bb81d9c0eae0747039b81c9c0e2e0707037c71bab8dbd86d0e36081ac40d4986950343719dc0cce065ac327618fc0c5e0620e3088
|7,2=>0x4e08
|8,0=>0x37141b6a0da506cb736239aee4d6706ab835149a6dcd27068c7342419ee4ce8e66b9331c196e0ca8e64c8321c98ee0c67062a9310c98624c1f260782ffc17de0bdd25e592ee4974e4b9705c472deb96d24b5905a392cdc164e0b15258282bd415ca0ad5056282acc9549ca950544629e414d20a590524828eb945d8a1f0507827fc13e1c9e104e88
|8,1=>0x4733a37a11ad08ce8463422fa116ee8b07453ca27e1130e89174444a20210f1087174344a185d0b4e8519424c21061071283174153a08a1035081284054200dcff527f283f541f8a0fb507d193e539f0dcf7527b193d4c1e860f34e79283c4c9e024ef1077083b4b9d824eb1074f93a3c1cfa4e6ee7307393c9c7e0e2d270d938249bf20de726ea9
|8,2=>0x575bab8a55b32ad09564bab0255710ab175553aa8655330a9185444aa0214ef2a6e95334297a14ad0a4e8523428fdd46f0a307513ca87e142f0a0f8503c27fe13f0e9ef94f34a77a13ab29cd84e24a6f2136729ab84d1c266a5326e98b84c1c25ee12e7096b84b1c257592ace94e84a3424fdd26d292e8493424765229290c8482423f211e908ed7
|8,3=>0x678c33a619c30cd986684b32219810cb88657cb29e193d2c968647bb21e18ff0c769636cb19618bb0c5586264b10e58770c3386154b08a18350c119604c300d97f8ebf575f64af9217b90bd575e6c2f16177b0bb585d6c2e9257390b9485c6bae1256faeb7495b642d9216b72b5385a5c2d0a56732b32759542c8a16332b127585bac11d5f72af29
|8,4=>0x1b790db486d6436921b390d9486c6436121af90d7486b6435921ab90d5486a6bb519da7d0d3776983b49e5a3d2d1776883b425da012cf97
|9,0=>0x7e1c3eea5f650faa87d143e665f24ef8a87c143dea1ee50f6a87b143d6a1ea50f4997a0c3ce9de632f2987904bc65de212f08878043be5dde30ee987704bb5e5d9f0ec7875fc3ada5d5eeea7874fc3a5e1d1f0e87873fc39da5cdd0e67772f4b95a1c9d0e47771fc38de1c5f0e26970ecb8561c1b0e0496fe437d21bdaede586eec37525b990dc48
|9,1=>0x8e3bc6fa636d11ad98d2c4676232b118d88c2c45f622eb116e78b34457a22ad114e88a3444fa226b312d8892c44762229310c8882443f221e910ec88724437221a910cc8862442f2216910ac885244275e12b108d8842c41f620eb106d8832c417620ab104c9822440f22069102b98114c0666024f00a8801bbfee1fe70feb87f1c3f6e1fa70fcb8
|9,2=>0x277733b389d5c4e8a6735139199c4c4e0626f1336f99b3c4d7e26af135079a3cccfe266f132f8993c4c7e262f130f89843cbfe65ed32ee8973bcb7a65ad12ce8962ccaf2656912ac8951cca6a6525128a8941449ea24e5126a89314496de4a7124b8921c48f1e469122c8912448722429120c8902447f223eaf1ee78f34477de3ad31ce8
|10,0=>0x14628a2d4514a289514437a1dc50ce285714238a0dc504e2817140479fe44fd227d913e489ee44f52279913c48
|11,0=>0x146a7
|_,_=>0
def wAt:=mkWire dB 251 248 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x40b410291503c1cb1040b4102c0d014342916074540c040b4ac0f152cc102d040b0540f152cc102d040b0ac0f152cc102d040b0a41d0328c9c57040b42429090b46c690400810030b0a4740005180242d051ac1002090b4242d1b1a410020400c38290d014581d15030102d090040465180b010290b0a47402071942401180b010290b0a4382b0d014581d15030102d
|1=>0x44040c2e0403c0c2e040b42401180b010290b0a41003090b410021503c1cb1040b4102c0328c9c57040b42429390a45c10090042c2907194602c040b41029090b410004103c1101030b8102c1503c102d040b424293e0bc10f5090082c291701c1429090b4242916074540c040b45c07050a45c07050a4242d040a45c10090042c2909384dc2e27040242916074540c
|2=>0x5107c9c55040b424291b1a410020400c2c294f01d3829094040c2e053201001090b42c29090a40cb1040b4102c3203c1001090b42c294c0b410f7090082c291503c1429040b4242d050a4242d3a0bc100d0b0a4142b090b5242905040242d0b0a4c80f0900410010b0a4100304008242d0b0a5202b04008242d3203c10010b0a45c0709004142b03008242d0b0a4100f
|3=>0x5801d842909574102e1701c24010b0a4540f040b4142b090b5240205040242d050ac242d3a0bc100d1701c1429090b41000040a42c291701c1429051bc242d0400c2c291701c9c2d090a574020504c242d04000242d040a42c290b0a4156c090b40c295801c9d5d040b82429090041000040a42c29090b41000040a42c290b0a41460040a4242d01534d012270bc2429
|4=>0x40b42c291701c14291800010290b0a41003050ac0c2d040b4100d090a5440f27154102d090a46000090b410290b0a41c65180b010290b0a5195d040bc102e090a4540f040b42429090b40c65180b0102d040a424011800010290b0a4342916074540c040b4242d1800010290b0a4146b04008242d0b0a4581d040ac540c040b4340516074540c040b4142b04008242d
|5=>0xb0a41460090b410290b0a4102d050ad440c27154102d090a41001090b41000090b4c80c040042c290b0a4142b090b40ca12715c102d090a575c10504c1412090b40067180b010290b0a425b56c0b89c13090a42429072c4102d040b02c291503c102d090b4400f0b0a4142b090b4540f040b49c2f16074242915030102d050a4102f1503c1429040b4242d090b4540f
|6=>0x7c01c9d9d030b424293b7a4100f045b80c29154dc0cb1040b4102c1004c2c29050ac242d3b0b40c2e0403c25d91b0b410030b0a454b3040b0540f040b4ac0f152cc102d040b014c7090b410000b0a41001090b410000b0a4c80c04004242d0b0a53c074e0a42501030b80465180b010290b0a4142b0400454b3040b4102c090a42c290403c142b090b4c80c090041001
|7=>0x40b80e350918810295d0a41413090b40c2d040342429098ad882e040ad242905040242d072c4102d040b0242d040a42c29093b40c290403c2c29050ac242d0b0a61c29090482615270b8242916074540c040b425d9620b4102b012c4102c090a4260a460a4102f0980c602e040a41413090b42c296c0b49c13090a4540f040b4242d1701c24015101c9c55040b42429
|8=>0x90b42429046740c2d050a4102f090b42401040002c290562c102b090b4124d2703c2429610a4255d040b824293b0b4100f090b410000b0a42581570a4102e0b0a42455040b4102b152cc102d040b0242d040a42c2909008100f0b0a53829094040c2e040b424020b0a410020400c2c291003c142b090b42402040342c291503c102d090a41241095b80c29096095c29
|9=>0x40b424291701c1429090b42465180b01029090040c020b0a49c2f090a4242d990a61c2d09048242d030082c29180b0102d040a5382b094040c2e030b8ec2d0403c242d040002c29091a410020b0a46000040a42c290403c142b090b4c80f040042c2909574102e090a4141005044242d051801029090b4142b040b4242d09194602c040a41cb1040b0242904034142b
|10=>0x40b4100d090a4c82f040042c2903008242d0b0a4102b15030102d0932810010b0a46c2d0400c2c290931410000b0a44010050ac242da000c24110b0a4067927048242916074540c040b42429044040c2e1004c142b090b40c01090042c29090a4540f040b4115d040b82429055b0242d030a40c010b0a4242d030b8102d090a42601180b810292746c102f090a49c56
|11=>0x403e440f05044242dac0a4140f090b41215270b82429090a42501030b810f7090082c290919c602c040a4246d0400c2c290904810290b0a4d011270bc2429276740c2d090a69829870b82412090a4540f040b4545b15030102d040b0540f040b42515030082c29040b424290403c0c01090b42c29870082c29090482601180b810290400010290b0a4250d400a40c2e
|12=>0x40b82429098a5882e040ac12c7270b024290485c9c2e090a4141305048242d05b4c2c2b090b41429090b4100f1704c1429090b6440c05044242d270b02429090b41429040b4242d170401429090b41410090b42c290403c1101030b8142904034242d09b06802e09044242d870b824120900410290b0a68000090442c291703c1429090b4102f050ac242d040b40c2e
|13=>0x40a46000040a42c29400a40c2e0403c242d2703c24295d0a41413090b40cb1040b4102c098a5882e040ad242905040242d094390029030ba442f05044242d030b8100f043d424020b0a45c2b090042c29040bc2429090b4247d2c0a4102c090a4540c040b40cb3040b024294e0a42501030bae829092c4102c3203010010b0a41c65180b0102904b149c2c090a49d5f
|14=>0x90b42c29270bc102f090a41029870b42412032c4102c090a4400f050ac242d040bc102e090a5842b09574102e0b0a4142b090b42401040bc2c290900810290b0a49c55040b42429090b4102f0b0a5382b094040c2e0900410020b0a45c07090042c29090b410020b0a42c29030a4242d370b89c10090a61c010b0a42412090441410090b6782d27048242909158102d
|15=>0x90a4540c040b4242d0400c2c2901194602c040a410f7090082c29091f4b029040b0540c040b410290b0a7002d090bc100f050ac242d05180242d040a42429092c4102c040b4142b090b4540f040b42c2904034142b090b61c020b0a4241227150102d090a4242d040bc2c29094a80c010b0a4158b090b4102bbe0a42456040b4540f040b4242f04008242d0b0a40c29
|16=>0x40042c2909008102f270bc2429090b45c13090042c29091f8b029040b04013050ac242d0403c2429090b4540f040b4242d09a38602f040a45c10090042c29040b42429090b7140f04b442c2b610ac255d040bae829092c4102c040342429090b45c07050a4242d0403c116e030a4242d870b42412a000024110b0a45c0f090042c29180b010290b0a424010400c2c29
|17=>0x272cc102c090a4242d040342c2909cd8600d040a6782e270482429050ac102f090b49ced090a4100f152cc102d040b0540f040b4242d9103c1411090b410f5090082c290503c242d0b0a4247e2c0a4102c090b4e82f040342469040082c2909c94542b040b41001040002c293203010010b0a4242d2704c2429090a4102d030b44010050ac242d090b410030b0a4c80f
|18=>0x90b424ca040042c2909d88ec290403c2401040042c290931410000b0a68003090442c29ac0a4140f090b4242d040042c29340489c2f090a424010403c2c29370b49c10090a6440c05044242d8d0b42462040a75029093a8100d050a4102d090b4242d0403c2c29273a4100d090a64c2d2703c242927464102f090a42c29040b4242d270b4100d090a40cf5090082c29
|19=>0x270402429090b4100f0b0a45c13050a4242d2715c102d090a42515030082c29040b4242d0b0a5b02e2704c242927574102e090a45c10050a4242d045b00c29040a41413090b4241204034242d0b0a40c67180b0102903194602c040a40c29090042c29040b49c2f090a41000040a42c2904034102d030b4252505040242d090b6802c0904424292c0a4102c1703c1429
|20=>0x90b42c290b0a4241205044242d092cc102c040002c2927048242962034102b2c0a8102c09464102f0504c242d040b40c2d0b0a4242d091881029040b4102b030a4100f090342c29090b4100f040b4242d09b442c2b04034242ddf0a4240d090042c29040a42c292703c2429900b4256e030a4102d040b02429091b410030b0a76429a00b0241104004242d0b0a4242d
|21=>0x40ac242f090b42412870b82412040340c2d180b81029030a4242f2704c2429040b8242905048242d012c4102c090a4100f04034102f040b42429040b4102c0403424293b0a4100f270b824290b0ac242d030a4240d09034242d030042c29090082c29040082c29045bc0c29040bc1029030082c292c0a4102c050a4242da003c24113a0ac100d05034242d0b0ac242d
|22=>0x93b4100f090b40c2909044240d040b41029eb0a4242e270402429400a40c2e040ac242d050ac242d870a424120440c0c2e05040242d030a4242d030b8242909574102e570a4102e072c4102ca00bc241146034102f046740c2d460a4102f0503c242d3b0b4100f180bc1029030a41029040b02429620b4102b09574102e0400c2c29090442c291503c102d270b02429
|23=>0x18034102905034242da00b82411094040c2e1503c102d180b0102909158102d040b4100f04eb4242e05044242d040bc2c29093a8100d040b4100d094040c2e040082c29030a42c290504c242d09044102b040bc242f038742412090a4242d090b82c29040042c29090b4102b620b8102b044040c2e09044242d1503c102d460b4102f09b4c2c2b040b40c2e05040242d
|24=>0x403c242fa00b02411030082c29040b4242f04034242f0940c0c2e05048242d09624102b04b442c2bc00b4242f030b40c29040a42412030b8100f150ac102d040a4242f045b00c29040bc242d040002c2915030102d032cc102c3a0bc100d090b42c290400c2c29270bc24290957c102e030a42411091841029040bc242ddf044240d870b42412050a4242d0b0a4242d
|25=>0x5040242d090441029040b4242d040bc24292c0a4102c090b4102909b442c2b092c4102c04034242d0b0a4242f0503c242d095b80c29050ac242d0467c0c2ddf048240d091881029032c4102c040042c29040a4242d092c4102c040b8102f0403c2c2904ebc242e045b80c29040b42c29090341029030042c29090082c290503c242d040342c291803c1029a00ac2411
|26=>0x2429040ac2411030a4242d09048242d090340c2e0b0a4102c090b8242f040b8100f040b4100d040a40c2d040bc2c2b0504c242d5b0bc0c2904b4c2c2b030b4242915030102d0403c242d
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x7480d5400000000000000000000000000000018a000005a80a500000000048a000000001f50386064c0aa0105000002d400000000142000002a8005
|7,0=>0x1f263d50791800000003b907598e831cc438906f98dc31b08351000000001a0833100000000190831100000c0417882e105a20b0415882a105220a041388264c4aa091411a822c843a0852102800003f187b30ee81d0c38200000d881a1032206220be6170c00005a20ac814cc27a04d20946119021203e4
|7,1=>0x38847010de21b8436886c10d699a9434a86850cea199400006550c8a18d4000062c8c3a18342fe85ed0bc917542e465b90b5980002ce858d000015f42b6855d0a9a000029e8530ca42146228484f909e1000027264dc899a12f4256849d091a11f4000046d08ba113421e842d083a1034204240087e20000
|7,2=>0x1c63
|8,0=>0x5086a04d3f1a7b34f069d4d391a6f34d869a4d331a6334c06974d2d1a5734a86944d271a4b34906914d211a3f347868e4d1b1a33346068b4d151a273448688c5101a1d3434685cd0a1a11341c682cd041a05340467fccfe19f933ec67cccf819ed33d4679ccf219e133bc676ccec19d533a4673cce619c93
|8,1=>0x6886d04d9f1b3b36706cd4d991b2f36586ca4d931b2336406c74d8d1b1736286c44d871b0b36106c14d811aff35f86be4d7b1af335e06bb4d751ae735c86b84d6f1adb35b06b54d691acf35986b24d631ac335806af4d5d1ab735686ac4d571aab35506a94d511a9f35386a64d4b1a9335206a34d451a873
|8,2=>0x8067000dfe9bfa37ee6fd0df89bee37d66fa0df29be237be6f70dec9bd637a66f40de69bca378e6f10de09bbe37766ee0dda9bb2375e6eb0dd49ba637466e80dce9b9a372e6e50dc89b8e37166e20dc29b8236fe6df0dbc9b7636e66dc0db69b6a36ce6d90db1135f36b86d64dab1b5336a06d34da51b473
|8,3=>0x98472fce5e1cb9396c72cce581cad3954729ce521ca1393c726ce4c1c953924723ce461c89390c720ce401c7d38f471dce3a1c7138dc71ace341c6538c4717ce2e1c5938ac714ce281c4d3894711ce221c41387c70f0a1c9c36386670c0e169c2a384e7090e109c1e38367060e0a9c12381e7030e049c063
|8,4=>0x2869d0a3a0e7410e809cfe39f673e0e7a9cf239de73b0e749ce639c67380e6e9cda39ae7350e689cce39967320c0004c53
|9,0=>0xb1c5630ac515882b0c5610ac115802afc55f0abd15782aec55d0ab915702adc55b0ab515682acc5590ab115602abc5570aad15582aac5550aa915502a9c5530aa515482a8c5510aa115402a7c54f0a9d15382a6c54d0a9915302a5c54b0a9515282a4c5490a9115202a3c5470a8d15182a2c5450a8915102
|9,1=>0xc1c5830b0516082c0c5810b0116002bfc57f0afd15f82bec57d0af915f02bdc57b0af515e82bcc5790af115e02bbc5770aed15d82bac5750ae915d02b9c5730ae515c82b8c5710ae115c02b7c56f0add15b82b6c56d0ad915b02b5c56b0ad515a82b4c5690ad115a02b3c5670acd15982b2c5650ac915902
|9,2=>0x34516882d0c5a10b4116802cfc59f0b3d16782cec59d0b3916702cdc59b0b3516682ccc5990b3116602cbc5970b2d16582cac5950b2916502c9c5930b2516482c8c5910b2116402c7c58f0b1d16382c6c58d0b1916302c5c58b0b1516282c4c5890b1116202c3c5870b0d16182c2c5850b0916102
|10,0=>0x6a01d3e3a7874e8e9c1d363a6874c8e981d2e3a5874a8e941d263a487488e901d1e3a387468e8c1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x204e800000010254000000081200000000401800000002006000000010020000000080080000000400000000001e1680000000861c0000000411a000000020160000000100a0000000018100000000030e000000000990000000004c00000000024c00000000122000000000440000000001e8000000000600000000002c00000000014000000000088000000000400000000000c00000000005000000000020000000000080000000000200000000000
|1=>0xa84e80000005065c0000002813e0000001409d0000000a00800000004f0f40000002783a0000001383d000000090c38000000482740000002402c00000012003000000088ca80000004061c000000201200000001000800000008003000000040010000000200000000000e1950000000606b80000002435c0000001212e00000008091000000040480000000200080000000e32a000000061970000000304e8000000180400000000a13a00000004197
|2=>0x1100a00000008804c00000044020000000210060000001000b00000008004000000040004000000200000000000f86b80000007c2740000003c32e0000001e0d70000000f04f8000000782740000003a13a0000001c1970000000e04e80000006865c0000003400e0000001a0060000000b8cf80000005c6740000002e1be0000001709d0000000b84b80000005c2540000002c33e0000001619d0000000b04f8000000582740000002c12a00000016085
|3=>0x2b04e8000001580740000008a32a0000003f0df0000001f86b8000000fc27c0000007e13a0000003e09d0000001e0cb8000000f035c0000007813a0000003c0950000001c0618000000dc67c0000006e13e0000003709d0000001b04e8000000d42740000006832e000000340d70000001a04a8000000c86540000006400800000030016000000178ee8000000b86540000005a1ae0000002c0950000001386b8000000986540000004a1ae00000022016
|4=>0x5684a80000029865400000144008000000a001e0000005000b000000280028000001400000000009f0950000004f04a80000026803c0000013001c0000009719d0000004b84f80000025c2740000012c33e0000009619d0000004a04f80000024e2f40000011c32a000000880080000004384e8000002186540000010a13e0000008509d0000004280800000021027c00000106030000000820900000004084e8000002040600000010002800000080000
|5=>0x2038cf80000101427c0000080833a0000040119d0000018b04a800000c106740000060000a000001a401c000000c606e8000004d00500000024802200000117195000000898ca8000004100500000020800000000100014000000800000000003142740000018a03a000000bf09d0000005f0cf8000002f86740000017c32e000000be0950000005e04f8000002f023c0000016c33a000000b61950000005a04f8000002d023c0000016003c000000ad09d
|6=>0x41b86b8000020d86540000106c31e0000082f097000004170ca80000209c6540000104c32a000008200140000040f8cf80000207867c0000103c13a0000081609d0000040800600000200000400000f6e12a0000079709d0000038384a800001a3c27400000d0c33a0000060709d000002ca0ee8000014b827400000a583ba0000050d09d0000028304e8000014107740000092e13a00000480010000002160ee8000010907740000082e33a0000041419d
|7=>0x82da0ee80004165077400020a683aa0001051c1dd000082160ee800041010774000203381ba0001012401c0000808e06080004041c274000102480280000601709d000020ca0ee8000102dc35c0000816c32e000040970d70000204b0cb8000102486140000804402c000040200160000200b8cb80001005c35c0000802e13a0000401609d0000200a0cb80000805c274000020a503a00001013c3d0000068304a80000229c2540000107e33e0000083f0df
|8=>0x40828606a802040650774010203281ba008040340950040040000000200005c27400e0802e1ba007000170dd0028000286e8002804380140010100e12e000801360950004009300a0002004980100010024c002000801240000004008f04e8002004582740010005e12e000800260000004000a0ce800200038274000800100220003053c1950001828a0ee8000c101c7740004031801a00020013c1d0001000700600008001c25c00030008010000105bc0d5
|9=>0x100040b84f80800201c65404000f3e13a0200071709d0100034384e808001a1867404000c2c33a0200051c1dd0100009200a00800049001004000248000020001140dd0100008606e8080004300040400020c13a020000be1970100005f0ca8080002d86740400016c12a020000a60950100004f04a8080002586740400012c13a020000960950100004304e80800005825c0400001c32a020000061950080000b04e8040000582640200002218e008105141dd
|10=>0x40000cb8cb8200004fc65c1000022e32e080001171950400008b84e82000045827410000200020080000970dd0400001b86f8200000dc35c100000583ba0800001f0df0400000b8ce82000005c65c1000002e32a080000170df0400000b84f82000004c6541000001a12e080000070970400000284b820000010440100000002200400001609d0200000b04e0100000386540410082c13a0203053c1dd0101828a06e8080804300300400106e12e02000827097
|11=>0x800004b84a8400002586542000012813e1000003c09f0800001b86b8400000d02542000005813e10000027197080000130cb84000007c2742000003c1ae1000001e09d0800000e04e84000005c35c2000002c32e100000120120800000604a84000000005c1406184e3ba0a0000870990404040704e8202000982741010000e12e0808000609d040082038ee82000301c7741000122e32e0800041719d040002038ee8200010107741000042e32a0800021709d
|12=>0x2800000a04e9000000702745400005e33a280000271dd1100029e0ee88001065035440000b783ba2000052f09d100002860ce880001410674400002783ba200001341dd100000898ca88000001077440000000002120a001c19d0901030784e84808007065c240008183ba1200001e1950900000e06e84008007825c2004003813a1002001c0970801000784b8400800382742004001812a1000010401d0800004f86a84000027027c200001340341000009a00b
|13=>0x4400000502551000007e1be8200013c1dd400002de0eea000000fc35d0000004012a80000020011
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x305c0000000000000000000c000301800000580000110600c06120001c0000010000e04
|7,0=>0x189c1eba5e1cc0c08120801016001083af42c2650510008a9341001821620007374001506ab466807b81a0826008205a00031643828214650c2e00084023a04021cae40100c62000d8205c00002c0305a18024300523c7c00af1880400022e8a40084848c83a81418cc26045cc049c011b964102d0c8000c060380cfa000f8262e0303018008c0486104300d0201a38
|7,1=>3
|8,0=>0x8c108904221108e5798b5d4f44f4b4a1524a82958f16ea0ccc6b60af318845096108b777c52f4de8760895ea228e98890ebd0072439a2117ddc5b969728c8ea49b16b4a42bf1f03b245c5319f24647049e5b0fca0bb779824712a9159c25750920fd3662134028db115ab25fd046e7c89ab430a0d31bcd26b4eaa9b8ce7b0510552ae3db8c7a6a278e5b34712108f702
|8,1=>0x91adcc36a2f37a80c94dca2228a38995418089b218c554e4ca66429baf8a43585219696576c00decfbdb886f1ac407150f1ae8bf0a14919da0793318512ab42b14a859e7b198b8b2749790460733b6444853c4cae5250acd7069bf90d848d4fad1d4fdb85e06cf921144c83476534285069698d10821275ae2ca63a0818bb9220857e36b700c2bd0931b04820940a448
|8,2=>0x1868b6c9c1e52b8a15296c249920ac97b612da24624613024b629480079
|9,0=>0x245b69853cc246e6745fe6ce03eaf921595b49b8086ce629ddd520aa36886cd27df6a0a521544f964490f2c2abb5bff3b4f51c91cf2f3aa7a4d30a263890e93fcfe72c522ce2b449b3dd120794837eb83c94aa884c52450f0f76975230d39c1a2f1f681e28b2d958f472a13125bcc844fb34ef337c51a90f84277c9674426b696a6a3a62518f948724d46d0cbdeaa18d
|9,1=>0x3450721e41250f95531278c91d5d4ed49ea3f46fb3ad15950d213c0f6d521438870649e71fc75d2342c7408712196939e0f954db49a99817820a4aa12721a4090419e1addf89
|10,0=>0x16f45455f43c451d7243e1e1091e3c2408eb0ccb4c2c888f
|11,0=>0x1e
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 45 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_246 10 roots_246 ops++addP pm 1 dzo_167_16 6 roots_167 ops++addP pm 2 dom_119 9 roots_119 ops++addP pm 3 dom_179 7 roots_179 ops++addP pm 4 dom_215 9 roots_215 ops++addP pm 5 dzo_225_16 5 roots_225 ops++addP pm 6 dzo_163_4 5 roots_163 ops++addP pm 7 dom_245 10 roots_245 ops++addP pm 8 dzo_227_4 6 roots_227 ops++addP pm 9 dom_118 7 roots_118 ops++addP pm 10 dom_193 4 roots_193 ops++addP pm 11 dom_241 7 roots_241 ops++addP pm 12 dzo_231_16 7 roots_231 ops++addP pm 13 dom_231 8 roots_231 ops++addP pm 14 dom_243 9 roots_243 ops++addP pm 15 dzo_215_32 7 roots_215 ops++addP pm 16 dom_183 8 roots_183 ops++addP pm 17 dzo_87_32 6 roots_87 ops++addP pm 18 dom_229 7 roots_229 ops++addP pm 19 dom_163 5 roots_163 ops++addP pm 20 dzo_179_4 6 roots_179 ops++addP pm 21 dom_227 6 roots_227 ops++addP pm 22 dzo_243_4 7 roots_243 ops++addP pm 23 dom_199 6 roots_199 ops++addP pm 24 dom_225 5 roots_225 ops++addP pm 25 dom_182 7 roots_182 ops++addP pm 26 dom_55 5 roots_55 ops++addP pm 27 dom_147 4 roots_147 ops++addP pm 28 dom_115 6 roots_115 ops++addP pm 29 dom_83 5 roots_83 ops++addP pm 30 dzo_229_16 6 roots_229 ops++addP pm 31 dzo_163_16 5 roots_163 ops++addP pm 32 dzo_165_16 5 roots_165 ops++addP pm 33 dom_117 7 roots_117 ops++addP pm 34 dom_181 6 roots_181 ops++addP pm 35 dom_51 4 roots_51 ops++addP pm 36 dom_103 5 roots_103 ops++addP pm 37 dom_195 5 roots_195 ops++addP pm 38 dom_230 7 roots_230 ops++addP pm 39 dzo_227_16 6 roots_227 ops++addP pm 40 dom_87 6 roots_87 ops++addP pm 41 dom_211 7 roots_211 ops++addP pm 42 dzo_214_32 6 roots_214 ops++addP pm 43 dom_151 5 roots_151 ops++addP pm 44 dzo_86_32 5 roots_86 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_247 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_167_16_161 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_225_16_161 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_163_4_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_227_4_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_231_16_161 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_215_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_87_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_179_4_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_243_4_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_229_16_161 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_163_16_161 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_165_16_161 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_zo_227_16_161 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_zo_214_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_zo_86_32_84 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_246 10 s (0,roots_246.map (·&&&dom_246)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_247 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_246 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_247 gM v ys):RunD true dom_247 gM v (ori ys):=h
def Z (s:Nat):=barP dom_247 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 7 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 35 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 129 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 129 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 282 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 26 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 282 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 190 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 62 128 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 190 → Z 9 i = true := (range_split z9_0 z9_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 21 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 21 0 = true)
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
def dzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def gzo_235_16:=0xf0f00000f0f00000f0f00000f0e00000f0f00000f0f00000f0e00000e0c0000
def gsh_235_16:=0xf0f00000f0f00000f0f00000f0e00000f0f00000f0f00000f0e00000e0c
theorem lowS_zo_235_16_169:Lower true dzo_235_16 roots_235 gzo_235_16 9:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_16) [(dom_235,16)] (by decide +kernel) (lower_slice_b (T:=gsh_235_16) [(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c,0,2),(0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_169)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,18),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(16,18),(16,80),(17,19),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,160),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,66),(64,80),(64,192),(72,73),(72,74),(72,88),(72,104),(72,200),(96,97),(96,98),(96,104),(96,112),(96,224),(128,129),(128,130),(128,136),(128,160),(128,192),(144,145),(144,146),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|10=>2
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|10,0=>0xd8a863ecf2
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f000f00f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x7643210784321076543210
|_=>0
def sO:Nat→Nat→Nat
|10,0=>0x10e08
|11,0=>0xf7
|_,_=>0
def wAt:=mkWire dB 9 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x60501
|_=>0
def oO:Nat→Nat→Nat
|10,0=>0x441
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 6
def pmP:Nat→Nat
|0=>0xff7f00
|_=>0
def pmB:Nat→Nat→Nat
|10,0=>9
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_187 10 roots_187 ops++addP pm 2 dom_249 10 roots_249 ops++addP pm 3 dom_243 9 roots_243 ops++addP pm 4 dom_123 9 roots_123 ops++addP pm 5 dom_235 10 roots_235 ops++addP pm 6 dom_219 10 roots_219 ops++addP pm 7 dzo_235_16 9 roots_235 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_235_16_169 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 2 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 2 0 = true)
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
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(4,20),(4,68),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,40),(8,136),(12,13),(12,28),(12,44),(12,76),(12,140),(16,20),(16,80),(17,21),(17,25),(17,49),(17,81),(17,145),(24,25),(24,28),(24,56),(24,88),(24,152),(32,33),(32,40),(32,160),(36,37),(36,44),(36,52),(36,100),(36,164),(48,49),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,80),(64,192),(72,73),(72,76),(72,88),(72,104),(72,200),(96,97),(96,100),(96,104),(96,112),(96,224),(128,129),(128,136),(128,160),(128,192),(132,133),(132,140),(132,148),(132,164),(132,196),(144,145),(144,148),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffff
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
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_125 10 roots_125 ops++addP pm 2 dom_249 10 roots_249 ops++addP pm 3 dom_245 10 roots_245 ops++addP pm 4 dom_237 10 roots_237 ops++addP pm 5 dom_221 10 roots_221 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_221 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
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
def dzo_186_4:=0x505050505050505000000000000000005050505050505050
def gzo_186_4:=0x505050505050504000000000000000005050504050500000
def gsh_186_4:=0x50505050505050400000000000000000505050405050000
theorem lowS_zo_186_4_170:Lower true dzo_186_4 roots_186 gzo_186_4 6:=lower_iso_b (d1:=dom_186) (r1:=roots_186) (T1:=gsh_186_4) [(dom_186,4)] (by decide +kernel) (lower_slice_b (T:=gsh_186_4) [(0x50500000505000000000000000000000505000005050000,0,16)] (by decide +kernel) lowS_170)
def dzo_118_8:=0x55005500550055005500550055005500
def gzo_118_8:=0x55005500550054005500550054000000
def gsh_118_8:=0x550055005500540055005500540000
theorem lowS_zo_118_8_86:Lower true dzo_118_8 roots_118 gzo_118_8 6:=lower_iso_b (d1:=dom_118) (r1:=roots_118) (T1:=gsh_118_8) [(dom_118,8)] (by decide +kernel) (lower_slice_b (T:=gsh_118_8) [(0x550055000000000055005500000000,0,32)] (by decide +kernel) lowS_86)
def dzo_174_16:=0x555500005555000000000000000000005555000055550000
def gzo_174_16:=0x555500005554000000000000000000005554000054540000
def gsh_174_16:=0x55550000555400000000000000000000555400005454
theorem lowS_zo_174_16_168:Lower true dzo_174_16 roots_174 gzo_174_16 6:=lower_iso_b (d1:=dom_174) (r1:=roots_174) (T1:=gsh_174_16) [(dom_174,16)] (by decide +kernel) (lower_slice_b (T:=gsh_174_16) [(0x44440000444400000000000000000000444400004444,0,2),(0x50500000505000000000000000000000505000005050,0,4)] (by decide +kernel) lowS_168)
def dzo_94_32:=0x55555555000000005555555500000000
def gzo_94_32:=0x55555554000000005554554400000000
def gsh_94_32:=0x555555540000000055545544
theorem lowS_zo_94_32_84:Lower true dzo_94_32 roots_94 gzo_94_32 6:=lower_iso_b (d1:=dom_94) (r1:=roots_94) (T1:=gsh_94_32) [(dom_94,32)] (by decide +kernel) (lower_slice_b (T:=gsh_94_32) [(0x444444440000000044444444,0,2),(0x550055000000000055005500,0,8)] (by decide +kernel) lowS_84)
def dzo_222_32:=0x5555555500000000555555550000000055555555000000005555555500000000
def gzo_222_32:=0x5555555500000000555555550000000055555554000000005554554400000000
def gsh_222_32:=0x55555555000000005555555500000000555555540000000055545544
theorem lowS_zo_222_32_84:Lower true dzo_222_32 roots_222 gzo_222_32 7:=lower_iso_b (d1:=dom_222) (r1:=roots_222) (T1:=gsh_222_32) [(dom_222,32)] (by decide +kernel) (lower_slice_b (T:=gsh_222_32) [(0x44444444000000004444444400000000444444440000000044444444,0,2),(0x55005500000000005500550000000000550055000000000055005500,0,8),(0x55555555000000005555555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_170_4:=0x50500000505000000000000000000000505000005050
def gzo_170_4:=0x50500000504000000000000000000000504000000000
def gsh_170_4:=0x5050000050400000000000000000000050400000000
theorem lowS_zo_170_4_170:Lower true dzo_170_4 roots_170 gzo_170_4 5:=lower_iso_b (d1:=dom_170) (r1:=roots_170) (T1:=gsh_170_4) [(dom_170,4)] (by decide +kernel) (lower_slice_b (T:=gsh_170_4) [] (by decide +kernel) lowS_170)
def dzo_172_16:=0x111100001111000000000000000000001111000011110000
def gzo_172_16:=0x111100001110000000000000000000001110000010100000
def gsh_172_16:=0x11110000111000000000000000000000111000001010
theorem lowS_zo_172_16_168:Lower true dzo_172_16 roots_172 gzo_172_16 5:=lower_iso_b (d1:=dom_172) (r1:=roots_172) (T1:=gsh_172_16) [(dom_172,16)] (by decide +kernel) (lower_slice_b (T:=gsh_172_16) [(0x10100000101000000000000000000000101000001010,0,4)] (by decide +kernel) lowS_168)
def dzo_238_16:=0x5555000055550000555500005555000055550000555500005555000055550000
def gzo_238_16:=0x5555000055550000555500005554000055550000555500005554000054540000
def gsh_238_16:=0x555500005555000055550000555400005555000055550000555400005454
theorem lowS_zo_238_16_168:Lower true dzo_238_16 roots_238 gzo_238_16 7:=lower_iso_b (d1:=dom_238) (r1:=roots_238) (T1:=gsh_238_16) [(dom_238,16)] (by decide +kernel) (lower_slice_b (T:=gsh_238_16) [(0x444400004444000044440000444400004444000044440000444400004444,0,2),(0x505000005050000050500000505000005050000050500000505000005050,0,4),(0x555500005555000000000000000000005555000055550000000000000000,0,64)] (by decide +kernel) lowS_168)
def dzo_236_16:=0x1111000011110000111100001111000011110000111100001111000011110000
def gzo_236_16:=0x1111000011110000111100001110000011110000111100001110000010100000
def gsh_236_16:=0x111100001111000011110000111000001111000011110000111000001010
theorem lowS_zo_236_16_168:Lower true dzo_236_16 roots_236 gzo_236_16 6:=lower_iso_b (d1:=dom_236) (r1:=roots_236) (T1:=gsh_236_16) [(dom_236,16)] (by decide +kernel) (lower_slice_b (T:=gsh_236_16) [(0x101000001010000010100000101000001010000010100000101000001010,0,4),(0x111100001111000000000000000000001111000011110000000000000000,0,64)] (by decide +kernel) lowS_168)
def dzo_234_4:=0x505000005050000050500000505000005050000050500000505000005050
def gzo_234_4:=0x505000005050000050500000504000005050000050500000504000000000
def gsh_234_4:=0x50500000505000005050000050400000505000005050000050400000000
theorem lowS_zo_234_4_170:Lower true dzo_234_4 roots_234 gzo_234_4 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_4) [(dom_234,4)] (by decide +kernel) (lower_slice_b (T:=gsh_234_4) [(0x50500000505000000000000000000000505000005050000000000000000,0,64)] (by decide +kernel) lowS_170)
def dzo_234_16:=0x505000005050000050500000505000005050000050500000505000005050000
def gzo_234_16:=0x505000005050000050500000504000005050000050500000504000004040000
def gsh_234_16:=0x50500000505000005050000050400000505000005050000050400000404
theorem lowS_zo_234_16_168:Lower true dzo_234_16 roots_234 gzo_234_16 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_16) [(dom_234,16)] (by decide +kernel) (lower_slice_b (T:=gsh_234_16) [(0x40400000404000004040000040400000404000004040000040400000404,0,2),(0x50500000505000000000000000000000505000005050000000000000000,0,64)] (by decide +kernel) lowS_168)
namespace S_254
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,66),(2,130),(4,20),(4,68),(6,22),(6,38),(6,70),(6,134),(8,40),(8,136),(10,26),(10,42),(10,74),(10,138),(12,28),(12,44),(12,76),(12,140),(14,30),(14,46),(14,78),(14,142),(16,18),(16,20),(16,80),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,40),(32,160),(36,38),(36,44),(36,52),(36,100),(36,164),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,68),(64,80),(64,192),(72,74),(72,76),(72,88),(72,104),(72,200),(96,98),(96,100),(96,104),(96,112),(96,224),(128,130),(128,136),(128,160),(128,192),(132,134),(132,140),(132,148),(132,164),(132,196),(144,146),(144,148),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
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
|5,0=>0xa1cd169c5d606d52a998
|6,0=>0xf43b8c531fae28481baf7ff7b7b5b667a2352a8251b504ffe94d26d39e4733cf61f9d91e7611d61e01e9b
|7,0=>0xfc8e1e5f42dec72db9ffb8d6eb69a4b0451a07e59ffdf98ec0955098faa38e9ae8e12182d0d82cfd7d7e87c1db77d6f6e7956dd6b688b968644681726333460ab0583e457f355095b4cb664b7a03fe3e3792b30427301652b3032ab61235451deee1403f13268115a8104fa0dd9a018cf
|8,0=>0xf24aaf1f2af1cd2e707be700fe43a3ccacbc638ec5ebcbaa8db6048ac7e1a9a99a9145a4ccca2d57a13b29f9ae9cac098af8982f28aa8e8a9e0851a684b6982d0d77a067478c73a7d71dd270afc6d3326adc863a1d6077c5eb985b0265afbf5a95a58a47585ad52c99521e65092f4fbf74e4a2407503bc363591e33120326703043e2e24d2d5e22ce252a89329b1824571215ae212d91f42d1dd3e1cd50190ef163e81617f15eaa1511212c9c0c0690bf370a84606ce7066150627704df6043fe01dde019ab
|9,0=>0xfc636fb6a9dc5c1c638ec5d3ec1ebcbfc8aa8774a57bba5351a0f2c9da0a9a022941c08cec3854cd8085572f416dd176645d64b8f5acf6585ad56d69569d154eb654e79535625123c500544c8784b93a3fef23d4323b7e638d9031e4a2f2ea2d67c2ab442ab1e286c92146819edb18eaf17bb713ad4109440c00805515
|10,0=>0xd1192c5d3e8a5a07553b5b02e46dd4406e82224d
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a0001555555555555555400000000000000015555555555555554000000000000000002a802a802a802a802a802a802a802a802a802a802a802a802a802a800000005555000055550000555500005555000055550000555500005555000055550000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa0155555555555555555555555511111111111111111111111111111111111111102828282828282828282800002828000028282828282828282828000028280005555555555555555555555555555555555555555555555550000000000000000aaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0aaaaa0a0aaaaa0a0a0a0a0a0a0a0a0a11111111111111111111111111111111111111111111111111111111111111112aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002aaaaaaa800000005555555555555555555500005555000055555555555555555555000055550000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a1555555555555555511111111111111115555111155551111111111111111111002a802a802a802a802a802a802a802a802a802a80000000002a802a800000005555555555555555555555555555555500000000000000000000000000000000
|0,1=>0xaaaaaaaaaaaaaaaaaa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa8955555555555555555151515151515151515151515151515151515151515151500000000000000002aaaaaaaaaaaaaaa80002aaa80002aaaaaaaaaaa800000000000000000000000000000005555555500005555000055550000000000000000aaaaaaaa8888aaaaaaaaaaaa88888888888888888888888888888888888888880154015400000000015401540154015401540154000000000154015400000002aaaaaaaaaaaaaaaaaaaaaaa80000000000000000000000000000000000000005555555555555555555555550000000055555555555555555555555500000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaa00015555555400015555555555540000000000000000000000000000000000000002aaaaaaa80002aaaaaaaaaaa800000002aaaaaaa80002aaaaaaaaaaa800000000000555500005555000000000000000000005555000055550000000000000000aaaaaaaaaa00aaaaaaaaaaaaaa00aa00aa00aa00aa00aa00aa00aa00aa00aa015555555555555554000000000000000155540001555400000000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaa80002aaa80002aaa80005555555555555555555555555555555555555555000000005555555500000000
|0,2=>0xa0a0a0a0a0a0a0a0a0a0aaaaa0a0aaaaa0a0a0a0a0a0a0a0a0a0aaaaa0a0a0a00000000155555554000000015555555400000001555555540000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000505050505050505050505050505050505050505050505050505050505050000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000015555555555540001555555555555555555555554000000015555555400000002aaa80002aaa80002aaaaaaaaaaaaaaa800000000000000000000000000000000055005500550000005500550055005500550055000000000055005500000000000000000000000000000000aaaaaaaa0000000000000000000000000000000155555555555555555555555555555554000155540001555400000000000000000000000000000002aaaaaaaaaaaaaaa8000000000000000000000000000000055555555000000005555555555555555555555550000000055555555000000000000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaa0000aaaa00015555555555555555555555555401540154015401540154015401540154015402aaaaaaaaaaaaaaaa222222222222222222222222222222222222222222222225555555555555555000000000000000000000000000000000000000000000000
|0,3=>0xaaaa0000aaaaaaaa0000000000000000aaaa0000aaaa00000001555400015554000155540001555400015554000155540000000000000002aaa80002aaaaaaa80000000000000002aaa80002aaa800000000000000000005555000055555555555500005555555555550000555500005555000055550000aaaaaa00aaaaaaaaaa00aa00aa00aa00aaaaaa00aaaaaa00aa00aa00aa00aa015555555555555555555400015555555555555555555555555554000155540002aaaaaaaaaaaaaaa800000002aaaaaaaaaaaaaaaaaaaaaaa800000000000000000000000555555550000000055555555000000000000000000000000000000000a0a0a0a0a0a0a0a0a0a00000a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a00015555555555555555555555554141414141414141414141414141414141414142aaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaaaaaa80002aaaaaaa8000000055555555555555555555555555550000555500005555000055550000555500000000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaa00000000444444444444444444444444444444444444444444444444444444444444000002a802a802a802a802a802a802a802a802a802a8000002a802a802a800000000000000000000000000055550000555500000000000000000000555500000000
|0,4=>0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000000155555555555555540000000000000002aaa80002aaa80002aaa80002aaa80002aaaaaaaaaaaaaaaaaaa80002aaa80005555555555550000555555555555000055555555555500000000000000000000aaaaaaaaaaaaaaaaaa00aa00aa00aa00aaaaaa00aaaaaa00aa00aa00aa00aa015555555555540000000000000000000155555555555400000000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000000000000000000000000000000000000000000000000000005555000055550000000000000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa0000aaaaaaaaaaaa000000000001555400000000000000000000000000015554000155540000000000000002aaaaaaaaaaa80002aaaaaaaaaaa80002aaaaaaaaaaa80002aaaaaaaaaaa80005555555555550000555555555555000000000000000000000000000000000000aaaaaaaaaaaaaaaaaaaaaaaa00000000aaaa0000aaaa0000aaaa00000000000000000000000000000000000155555555555555555555555400000000000000000000000000000000888888888888888888888888888888880000000000000005555000055555555555500005555555555550000555555555555000055550000
|0,5=>0xaaaaaaaa000000000000aaaa00000000aaaaaaaa000000000000000155555554000000015554000000000001555555540000000155540002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaa800000002aaa80000000000000005555000000000000555500000000000000000000000000000000a0a0a0a0a0a0aaaaa0a0a0a0a0a0aaaaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000000155555554000000015555555400000001555555540000000155540002aaaaaaa800000002aaa8000000000002aaaaaaaaaaaaaaaaaaa80002aaa8000555555555555555555555555555555555555555500005555555555550000000000000000aaaaaaaa00000000aaaaaaaa000000000000aaaa000000000000000000015554000155540001555400015554000000000000000000000000000000028282aaaa8282aaaa8282aaaa8282aaaa82828282828282828282828282828280000000000000000000000000000000055555555555555555555555500000000000000000000000000000000000000000000aaaa0000aaaa0000aaaa000000015555555555555555555400015554000000000000000000000000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaaaaaa800000002aaaaaaa800000000000000000000000000000000000000055555555555555555555000055550000
|0,6=>0xaaaa0000aaaa0000aaaa000000000000aaaa0000aaaa0000aaaa0000000155555555555555555555555555555554000155540001555400015554000000000002aaaaaaaaaaa800000002aaaaaaa80002aaa80002aaa80000000000000005555555500005555555555550000555555555555000055555555555500000000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaa0000000000000000000000015555555400000000000000000000000155555555555555540000000000000002aaaaaaaaaaa80002aaa80002aaa80002aaaaaaaaaaaaaaaaaaa80002aaa80000000000000000000000000000000000000000000555555550000000000000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aaaaaaaaaa00aa00aa00aa000000000000000000000155540001555400000000000000000000000000000002aaaaaaa800000002aaaaaaa80002aaaaaaaaaaa800000002aaaaaaa8000000000000000000000000000000000000000555555550000555555555555000000000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa000000015554000155540000000000000000000155540001555555540000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaaaaaaaaaaaaaaaaaaaaaaaaaa80000505050505050505050505050505000005050505050505050505050505050000
|0,7=>0x1555400015554000000000000000000015555555555555554000000000000000000000000000000000000000000000002aaaaaaaaaaa80002aaaaaaaaaaa800055555555555555555555555555555555555555555555000055555555555500000000000000000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa00015554000155540001555555555555555555540001555400015554000155540002aaa80002aaaaaaaaaaa80002aaa80002aaa80002aaaaaaaaaaa80002aaa8000555555555555555555005500550055005500550055005500550055005500550000000000aaaaaaaa000000000000000000000000aaaaaaaa0000000000000001555555555555555555555555555555540000000155555554000000000000000000000002aaaaaaa800000002aaaaaaa800000002aaa8000000000002aaa800000000000000055550000000000000000000000000000555500000000000000000000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000015555555555555555555400015554000155555554000000015554000000000002aaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaa800000002aaaaaaa800000000000000000000000000000000000000000000000000000005555555555550000
|_,_=>0
def sP:Nat→Nat
|0=>0x2209100830583143828c0c2468e00146220c247000a30f9e10142030c049000a7460b0618405182c186107080c160cd8e0a305861e20c85182c5091c0028c0c24d0e0014b8c160c50820309830c38805182c18210146061e347000a301821a2028c16284880a1038602002840608080
|1=>0x422028c3e78700304060b0c247000a5c6030c347000a3018650380180a305861220005182c3091c01385180c3011c980100a305870c380052e3018602380240a305861238010182c1861c58804182c1861c6428c160cd8e0014623061808e001420c160c308324020c440c30e0a30186
|2=>0xa305831420284161c3000ad05830c380052e305830c20c900a305861e38005663058612380050830309023800508305831438005182c1b21c0028c061988e4c00284180c31a1c0028c0c2408e001460b5e187000a305861e397000a10583040028c161960e001460b06084000a3059e
|3=>0x14623160c308001488b0618744201420c061808e001460b061980e004060b06187190a3218b0618405182c186110828c260c30e001460b06844410a31f8b06184000a301860239f00301460b0c3c4000a31d830c38005182c3371c0028c16d83081c146030c0471200d460b0618400
|4=>0x182c186103a6000a305861e207009e1460b06187000a30186023a7000a3059e42380100b3460b06187000a4460b061840e5c1460b061874c001460b0c3c7000a1060b061872e00146030c04714001464b06187000a1060b0619c8e001460b0618749011c28c160c30e001460b0618746
|5=>0x6187000a305db0c38005182c186b438005b2305830c380100a305830c3a400b01460b0618726001460b06187570040291182c186103828c160c3081c6428c17543081c402d0182c1861c00291180c3011c0028c160c3531c00805182c1861c480510a305830c3800574305830c38005
|6=>0xc400c1008305830c38005182c3601c0158522305830c2072b0a1060b0618700be305830c380540a1060b06187000a445830d787000a1060b0c24700701460b06287000a305830d6840e005480c160c30e0060291182c18610146030c687000a305830c393000a305830d747006a1460b
|7=>0x160c36e1c03605182c1861038005182c1861db4005182c1861cf400518881861c0028c160d088d81460b061870030305830dac00508301860238005d2305830c38005180c3011038005199c1861c01585182c1861cf80650a305830c380640a305830c38005682c1861c0028c160c30e
|8=>0x22305830dd47000a305830c380298a6060b06187000a305830c2072e001460b0618774001460b061872e001460b06184735614b8c160c30e001460b06184190a305830dcc28ce42c1861c01685182c1861c0028c862c1861c0388c160c30e01c028c160c3081c03805182c1861c0028c
|9=>0x182c1861c0028c160c30e009c291182c1861c94297182c1861c0028c160c3081d582fb160c30e0014623160c30e009028c160c30e0040284182c1861c002fa182c1861c00805182c18610380180a4460b06187000be460b06187000a305830d8c7000a33c030c38005182c1861dd8005
|10=>0x6187000a305830c3bf000a30186023800508305830c380382a1460b06187000a305834238005182c186de3800522305830c20700304060b0618700fa1460b06187000a305830c393000a5c60b061840e001420c160c30e0094c05182c186100028c160c30e019b885182c1861c03e05
|11=>0x160c30e001460b06187004a1460b0618714004028c160c30e001460b061a7250a305830c38a00711428c160c3081c0388c160c30e001460b061840e001460b0618700321460baa187000a305830c3a5000a1060b0c247000a305830c2100566305830c38005182c1861dac0180a1060b
|12=>0x28c160c30e011428c160c30e001460b061840e001460b0618777001460b0618700401488c
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x24c03180330006
|6,0=>0x8470fae1d9c37b86870c6a171c2ab84e7090c105c1d38337058e09980fb8187
|7,0=>0x1d17394e70dcde39b4835906920ceb996731ee61e0c0397a62e8c5b5cb2c15d82ab05360a2c13e726d04ba093b92072310449885b90471fcc3e187840e881c2e366068c0c9818302e6058c0aa7145026dc49c08b8
|8,0=>0x7a8cf321e2bbbd876b0eb61d33b9d972b0e361c33b7e86eb2db9db2cb5c96aaed325a2433b9668ecae591c31b8628ec3218242fc85eaebb6172c2dc95a72b2e1614aba8566eaaa551429a85232a26140c27894e109a2130425974a1291e51fc238745f289e1103a17941f081e0ffc1f783e0e79e4efc1d87
|8,1=>0x1121e1fcc387864d0aa211441a8826f02a60143fa87e32fa61f0c3da7
|9,0=>0x2ee3dd39b95370deddc5b38b58f6922ce45957b1b16162be4d748adaf5926ae45557a9b151269e45348a59148e68d4d128a15140a27d44f289d5138a26d44d37997130e25d4cb28953328264c44908912f20623c4c7088d1117e62bc44f8
|10,0=>0xc37184e305c6038bf717ce2f5c5e38
|11,0=>0x6237
|_,_=>0
def wAt:=mkWire dB 127 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x39064922380a011801202f22390a011801080f18390a951c022a000a010a51183a183930000a010a390c592a000a51183a0039300018390a391839166530000a010a390c65183930000a010a391c01168506850c811c000a010c592a000a51183a0c651821300000390a390a0116592a000a51183a0c491c0122380a011801
|1=>0x390a392e0f22390a011801080f202f0a0118390c65300018390a395a1b201118390a01482f18390a951c02080f202f0a01183906c108420a0118390c492238183918015a0f201118390a0100390c492238180106850c811c001c01168506850c811c000a39080f18390a01562f18210a210039542f0aa52802183a080f1839
|2=>0x183908420a01183930000a010a393044180100390a391067300000390a3916592a000a51183a42220c811c001c01803b18b90a2200392e0f18211c0116f5783818e10a02740f18e570390a020039066530000a39202f22380a01180100390a49223818011c010c6530000a39064922381839180118592a000a51183a18213000
|3=>0xa3922380a0118010b490800183918e570390a021c012e0f18211c01a01508031839202f0a01003a06850c811c000a011939003a18010a2200398a200a311c012e0f2239180118390a220039183a202f0a01164922381801183970390a0294018a3818150b21223a1801783a18e10a021c01223b180118018a000a31202f0a01
|4=>0x183918010a02080f18390c6530000a390a5e18211c010a010a51183a180100390a39482f0a951c020121223a1801bc01081718390a492238180107718a020a310a5e2239180108e318390a020a01223a18010a992801183a0a9a2801183a00390a011801300000390a391c0107591802080318390a01202f0a01180119523003
|5=>0x28e10a02183a783818e10a02166530000a390c811c001c010af918221c0120380a010a39202f0a01183919a9703a0a02202f0a011c0117a1203a0a010a2118221c010b99080218392a030a51183a186530000a39c63a20330a0118390a010a39c20f18610a390a211c011801300118390a390a4b22381801183930030a390817
|6=>0xa951c0218390a0118951c020a011c010a39180119dd0a3a20330a0116810038ee010a3a0a4618012802183a18150a390a2200398a3a18150a22003910831c001c010a2118211c01300000390a3910831c001c01201018390a01201118390a0130440a39180130400a010a391c018a230a311c01de0118620a390af918221c01
|7=>0xa8100381c951c0230000a39075918028a381815080f18391c001c01203b0a0120380a0118390a39ac3a1802202f0a0118390a020a51183a0c811c0018620a391c0118010a010a398a030a312801183a18211c0118391c0200390a39080218390a8100380a45180130020a3918011c022239180118021c0118831c00223b1801
|8=>0xa311c010a3a1c0018011c02183a0a011c031c020a02183a0a311c01
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1e5000019500000000514000000000003d4000000000002940550014000
|7,0=>0xb542c50ad42a50a540000a2327909a4259092423908a421908241f907a400007641c906e400006a4199062400005e4169056414904e4129046410903f300000000ed03740cd02f40ad02740000234
|8,0=>0x5d0d7135b8d6b35a0d653588d5f3570d593558d533540d4d3528d473510d4134f8d3b34e0d3534c8d2f34b0d293498d233480d1d3468d173450d113438d0b3420d053408cff33f0cf933d8cf513c8cef33b0ce93398ce33380cdd3368cd73350cd13338ccb3320cc53308cbf32f0cb93
|8,1=>0x19f3670d993658d933640d8d3628d891618d833600d7d35e8d773
|9,0=>0x810a0228009fe27f09fa27e09f627d09f227c09ee27b09ea27a09e627909e227809de27709da27609d627509d227409ce27309ca27209c627109c227009be26f09ba26e09b626d09b226c09ae26b09aa26a09a626909a22
|10,0=>0x83460c182c60a1824608181c6061
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 14
def pmP:Nat→Nat
|0=>0x81d900000081b900000081a90000008100000000800100000041b90000004098000000402100000020a000000011fb00000011f90000000f8000000009e9000000090100000001fe00000001f900000001f800000001a90000000198000000016000000001210000000120000000010000000000f800000000880000000080000000007800000000390000000030000000002000000000010000000000
|1=>0x8089f900008041f900008041b900008001f900008001b90000800160000080005000001807a9000008c1e9000008c1b9000008c1a900000841a9000008407800000440ed000003e1a9000000d1f9000000d1bb000000c9e9000000c9b9000000c9a9000000c7a0000000c1f9000000c1e9000000c1c9000000c1bf000000c1b9000000c1a9000000c00100000089e900000089a900000081f900000081e9
|2=>0x2000c1b9001000c1ad001000c0ad000c80c9a9000c00c1a9000880c1f9000880c1b9000880c1a900088081f900088040a8000800c1f9000800c1b9000800898800080081f900048049b9000400c9e9000400c9a9000400c1e9000400c1b900040085a900040049a900040045e900040009a8000400017800040001380002000180000100e1210000e0c1a9000083f1a9000080c9f9000080c1f9000080c1b9
|3=>0x800000c1f980000041f980000041a9600000c1a9102000c5a910100040a9080010c7a9040000016003400081b903088081b9030000c1b9010000c1b9009000c0a900900041a9004080c1f900408081e900408041f900408041b900408001f9004000c1e900400040d800400001f000400001b90040000100003000c0a9
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x7001c000220000028000000e48480
|7,0=>0x41660a8300092018ac9438886c38a001c3c6001c081010c0b12c9ce06020800014184ac0eac017
|8,0=>0x407b4216de2a58e713b0a952f52af16ec4d82fe1348934ca7c238d3a21ed6e415642bc809e5ecf128ce282436f0eb9a19594d39dba6eafc6cd56ec9b3a19408129f7b25eac
|9,0=>0x1325d499525ee837a19f36929d7611b07ea97686b52d2e4cb73a58166aa58142e419d0abd1be99f257edd02e
|10,0=>0xcc94f267aa4ecb
|11,0=>0xe
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 40 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dzo_186_4 6 roots_186 ops++addP pm 2 dzo_118_8 6 roots_118 ops++addP pm 3 dom_238 9 roots_238 ops++addP pm 4 dzo_174_16 6 roots_174 ops++addP pm 5 dom_222 9 roots_222 ops++addP pm 6 dzo_94_32 6 roots_94 ops++addP pm 7 dom_250 10 roots_250 ops++addP pm 8 dom_246 10 roots_246 ops++addP pm 9 dzo_92_32 5 roots_92 ops++addP pm 10 dzo_86_8 5 roots_86 ops++addP pm 11 dzo_222_32 7 roots_222 ops++addP pm 12 dom_188 6 roots_188 ops++addP pm 13 dzo_170_4 5 roots_170 ops++addP pm 14 dom_126 8 roots_126 ops++addP pm 15 dom_190 8 roots_190 ops++addP pm 16 dzo_172_16 5 roots_172 ops++addP pm 17 dom_236 7 roots_236 ops++addP pm 18 dzo_86_32 5 roots_86 ops++addP pm 19 dom_62 5 roots_62 ops++addP pm 20 dom_124 6 roots_124 ops++addP pm 21 dom_186 7 roots_186 ops++addP pm 22 dom_234 7 roots_234 ops++addP pm 23 dzo_238_16 7 roots_238 ops++addP pm 24 dom_218 7 roots_218 ops++addP pm 25 dzo_236_16 6 roots_236 ops++addP pm 26 dom_86 5 roots_86 ops++addP pm 27 dom_170 5 roots_170 ops++addP pm 28 dzo_214_8 6 roots_214 ops++addP pm 29 dom_182 7 roots_182 ops++addP pm 30 dom_206 6 roots_206 ops++addP pm 31 dzo_214_32 6 roots_214 ops++addP pm 32 dzo_234_4 6 roots_234 ops++addP pm 33 dzo_234_16 6 roots_234 ops++addP pm 34 dom_158 5 roots_158 ops++addP pm 35 dom_220 7 roots_220 ops++addP pm 36 dom_230 7 roots_230 ops++addP pm 37 dom_118 7 roots_118 ops++addP pm 38 dom_214 7 roots_214 ops++addP pm 39 dom_122 7 roots_122 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_186_4_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_118_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_174_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_94_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_92_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_86_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_222_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_170_4_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_172_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_86_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_238_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_236_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_214_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_214_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_234_4_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_234_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_122 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 45 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 79 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 79 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 50 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 50 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
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
def dzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0f0f0f0f0f0f0f0f0e0f0f0a000
def gsh_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0f0f0f0f0f0f0f0f0e0f0f0a00
theorem lowS_zo_251_4_171:Lower true dzo_251_4 roots_251 gzo_251_4 10:=lower_iso_b (d1:=dom_251) (r1:=roots_251) (T1:=gsh_251_4) [(dom_251,4)] (by decide +kernel) (lower_slice_b (T:=gsh_251_4) [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,0,16),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,0,64)] (by decide +kernel) lowS_171)
def dzo_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0
def gzo_235_4:=0xf0f00000f0f00000f0f00000f0e00000f0f00000f0f00000f0e00000a000
def gsh_235_4:=0xf0f00000f0f00000f0f00000f0e00000f0f00000f0f00000f0e00000a00
theorem lowS_zo_235_4_171:Lower true dzo_235_4 roots_235 gzo_235_4 9:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_4) [(dom_235,4)] (by decide +kernel) (lower_slice_b (T:=gsh_235_4) [(0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_171)
def dzo_175_16:=0xffff0000ffff00000000000000000000ffff0000ffff0000
def gzo_175_16:=0xffff0000fffe00000000000000000000fffe0000fefc0000
def gsh_175_16:=0xffff0000fffe00000000000000000000fffe0000fefc
theorem lowS_zo_175_16_169:Lower true dzo_175_16 roots_175 gzo_175_16 9:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_16) [(dom_175,16)] (by decide +kernel) (lower_slice_b (T:=gsh_175_16) [(0xcccc0000cccc00000000000000000000cccc0000cccc,0,2),(0xf0f00000f0f000000000000000000000f0f00000f0f0,0,4)] (by decide +kernel) lowS_169)
def dzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def gzo_239_16:=0xffff0000ffff0000ffff0000fffe0000ffff0000ffff0000fffe0000fefc0000
def gsh_239_16:=0xffff0000ffff0000ffff0000fffe0000ffff0000ffff0000fffe0000fefc
theorem lowS_zo_239_16_169:Lower true dzo_239_16 roots_239 gzo_239_16 10:=lower_iso_b (d1:=dom_239) (r1:=roots_239) (T1:=gsh_239_16) [(dom_239,16)] (by decide +kernel) (lower_slice_b (T:=gsh_239_16) [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,0,2),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,0,64)] (by decide +kernel) lowS_169)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,18),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,68),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,28),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,18),(16,20),(16,80),(17,19),(17,21),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,160),(36,37),(36,38),(36,44),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,68),(64,80),(64,192),(72,73),(72,74),(72,76),(72,88),(72,104),(72,200),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,130),(128,136),(128,160),(128,192),(132,133),(132,134),(132,140),(132,148),(132,164),(132,196),(144,145),(144,146),(144,148),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|10=>1
|11=>15
|12=>6
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|10,0=>0x329c7
|11,0=>0xf7f3ef2f5cc3e3fc1893b944cb41029d9fc9b4f27e9c3732c86c4d718846092f707de901f4c
|12,0=>0xdd9d2c33a39892d8fd7c792e40eef7
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff000000000000000000000000ffffffffffffffff0000000000000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|0,1=>0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff000000000000ffffffff00000000ffffffff00000000ffff000000000000ffff000000000000000000000000000000000000ffffffffffffffffffffffff0000000000000000ffffffff00000000ffffffff00000000ffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x398a920d80398a920e6101cc520c41048e62a483081af398a920c20398a920c31040e62a483081e8315241840d41cc54906101dc62a48308107518a920c2069cc54906c080e62a48358408398a418820
|1=>0xe62a483081073152418415398a920c203d0c54906101d462a483080e62a4836040f398a920c20820e62a483081a7315241840f
|_=>0
def sO:Nat→Nat→Nat
|10,0=>9
|11,0=>0x8aa8197896f96785e954a4b94293992fa2691ca12a099
|12,0=>0xc19b89af9a699d9949
|13,0=>0xca8
|_,_=>0
def wAt:=mkWire dB 22 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3813993013050813854193817813850813853d23015273057833857813853b20814193813813854053814073813813053b108141b381381527305
|_=>0
def oO:Nat→Nat→Nat
|10,0=>3
|11,0=>0x1f2749b26497254932448f2348b22487214832
|12,0=>0x986519063188611
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0x903fd1cff463fd0cff423fce8ff1a3fc48ff063fc0cff013fc03ff003fc0000
|_=>0
def pmB:Nat→Nat→Nat
|10,0=>2
|11,0=>0x8cb629c56ac4dc6
|12,0=>0x376d59
|13,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 18 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_191 11 roots_191 ops++addP pm 2 dom_127 11 roots_127 ops++addP pm 3 dom_253 12 roots_253 ops++addP pm 4 dom_247 12 roots_247 ops++addP pm 5 dom_239 11 roots_239 ops++addP pm 6 dom_223 11 roots_223 ops++addP pm 7 dom_251 12 roots_251 ops++addP pm 8 dzo_251_4 10 roots_251 ops++addP pm 9 dzo_235_4 9 roots_235 ops++addP pm 10 dom_95 8 roots_95 ops++addP pm 11 dzo_175_16 9 roots_175 ops++addP pm 12 dom_63 8 roots_63 ops++addP pm 13 dom_207 9 roots_207 ops++addP pm 14 dzo_239_16 10 roots_239 ops++addP pm 15 dom_111 8 roots_111 ops++addP pm 16 dom_159 8 roots_159 ops++addP pm 17 dom_171 8 roots_171 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_251_4_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_235_4_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_175_16_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_239_16_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_171 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 15 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 15 0 = true)
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
  · simp [NN] at hi
  · simp [NN] at hi
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [6, 5] }, { op := GateOp.or, inputs := [1, 0] }, { op := GateOp.or, inputs := [3, 9] }, { op := GateOp.or, inputs := [7, 5] }, { op := GateOp.or, inputs := [0, 7] }, { op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [4, 6] }, { op := GateOp.or, inputs := [8, 3] }, { op := GateOp.and, inputs := [11, 10] }, { op := GateOp.and, inputs := [14, 13] }, { op := GateOp.and, inputs := [12, 15] }, { op := GateOp.and, inputs := [6, 4] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_51704_aux

theorem PEqualNP.Outside.L_meta_51704 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_51704_aux.main
