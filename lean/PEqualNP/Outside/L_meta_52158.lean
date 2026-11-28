import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52158_aux
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
def goal_23 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_23 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfefaeca0fefaeca0fefaeca0fefaeca0fefaeca0fefaeca0fefaeca0fefaeca0
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_42 : Nat := 0x50500000505
def goal_42 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00
def roots_42 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xffecffececa0eca0ffecffececa0eca0ffecffececa0eca0ffecffececa0eca0
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefeececfafaa0a0fefeececfafaa0a0fefeececfafaa0a0fefeececfafaa0a0
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffcceeaacc00ffeeffcceeaacc00ffeeffcceeaacc00ffeeffcceeaacc00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffaffa0fafaa0a0fffaffa0fafaa0a0fffaffa0fafaa0a0fffaffa0fafaa0a0
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffeffecfefaeca0fffeffecfefaeca0fffeffecfefaeca0fffeffecfefaeca0
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_69 : Nat := 0x330000000000000033
def goal_69 : Nat := 0xfafafafafafafafaa0a0a0a0a0a0a0a0fafafafafafafafaa0a0a0a0a0a0a0a0
def roots_69 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0]

def dom_81 : Nat := 0x300030000000000030003
def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_84 : Nat := 0x1100110000000000110011
def goal_84 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_84 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffffafafffffafafafaa0a0fafaa0a0fffffafafffffafafafaa0a0fafaa0a0
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffafafffffafafafaa0a0fafaa0a0fffffafafffffafafafaa0a0fafaa0a0
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffeeaaffffeeaaeeaacc00eeaacc00ffffeeaaffffeeaaeeaacc00eeaacc00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffafafffffafafafaa0a0fafaa0a0fffffafafffffafafafaa0a0fafaa0a0
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffefafffffefafefaeca0fefaeca0fffffefafffffefafefaeca0fefaeca0
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeeeaaeeaaffccffcccc00cc00ffeeffeeeeaaeeaaffccffcccc00cc00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfcf0fcf0ffccffcccc00cc00fffcfffcfcf0fcf0ffccffcccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefefafefaffecffececa0eca0fffefffefefafefaffecffececa0eca0
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafafffffafafafaa0a0fafaa0a0fffffafafffffafafafaa0a0fafaa0a0
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefefffffafafefeececfafaa0a0fffffefefffffafafefeececfafaa0a0
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffcc00ffccffcccc00cc00ffffffccffffcc00ffccffcccc00cc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffeeaaffeeffcceeaacc00ffffffeeffffeeaaffeeffcceeaacc00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffafafffaffa0fafaa0a0fffffffafffffafafffaffa0fafaa0a0
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcfffffcf0fffcffccfcf0cc00fffffffcfffffcf0fffcffccfcf0cc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffefafffeffecfefaeca0fffffffefffffefafffeffecfefaeca0
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_133 : Nat := 0x3300000000000000000000000000000033
def goal_133 : Nat := 0xfafafafafafafafafafafafafafafafaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def roots_133 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 7 0]

def dom_135 : Nat := 0xff000000000000000000000000000000ff
def goal_135 : Nat := 0xfefefefefefefefefefefefefefefefea0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def roots_135 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 7 0]

def dom_138 : Nat := 0x50500000000000000000000000000000505
def goal_138 : Nat := 0xffccffccffccffccffccffccffccffcccc00cc00cc00cc00cc00cc00cc00cc00
def roots_138 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeecc00cc00cc00cc00cc00cc00cc00cc00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_142 : Nat := 0x555500000000000000000000000000005555
def goal_142 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffccc00cc00cc00cc00cc00cc00cc00cc00
def roots_142 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffefffefffefffefffefffefffefffeeca0eca0eca0eca0eca0eca0eca0eca0
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaa0000aaaa0000aaaa0000aaaa0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfafafafafafafafafafafafafafafafafafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcf0f00000f0f00000f0f00000f0f00000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfefefefefefefefefefefefefefefefefafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffccffccffccffccffccffccffccffcccc00cc00cc00cc00cc00cc00cc00cc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeeeaacc00eeaacc00eeaacc00eeaacc00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffafffafffafffafffafffafffafffafafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcfcf0cc00fcf0cc00fcf0cc00fcf0cc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffefffefffefffefffefffefffefffefefaeca0fefaeca0fefaeca0fefaeca0
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffefefefefffffffffefefefeececececa0a0a0a0ececececa0a0a0a0
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffffccffccffffffffffccffccffccffcccc00cc00ffccffcccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffccffcccc00cc00ffccffcccc00cc00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffaffa0ffa0a0a0a0a0ffa0ffa0a0a0a0a0
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffffcfffcfffffffffffcfffcffccffcccc00cc00ffccffcccc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffefffefffffffffffefffeffecffececa0eca0ffecffececa0eca0
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeccccaaaa0000eeeeccccaaaa0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffefefefefffffffffefefefefefeececfafaa0a0fefeececfafaa0a0
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaff00aaaa0000ffaaff00aaaa0000
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffccffccffffffffffccffccffccffcccc00cc00ffccffcccc00cc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffcceeaacc00ffeeffcceeaacc00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffafffafffffffffffafffafffaffa0fafaa0a0fffaffa0fafaa0a0
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfffcffccfcf0cc00fffcffccfcf0cc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffefffefffffffffffefffefffeffecfefaeca0fffeffecfefaeca0
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f00000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfefefefefefefefefefefefefefefefefafafafafafafafaa0a0a0a0a0a0a0a0
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffccffccffccffccffccffccffccffcccc00cc00cc00cc00cc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeeeaaeeaaeeaaeeaacc00cc00cc00cc00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffefffefffefffefffefefafefafefafefaeca0eca0eca0eca0
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffaaaaffffaaaaaaaaaaaaaaaaaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeeeeeeeeeeeeeeeeeffffaaaaffffaaaaaaaa0000aaaa0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffafafffffafafafafafafafafafafffffafafffffafafafaa0a0fafaa0a0
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfcfcfcfcfcfcfcfcfffff0f0fffff0f0f0f00000f0f00000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefefefefefefefefefffffafafffffafafafaa0a0fafaa0a0
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffaaffaaffaaffaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffccffccffccffccffffcc00ffffcc00cc00cc00cc00cc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffeeffeeffeeffeeffffeeaaffffeeaaeeaacc00eeaacc00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffff0fffffff0fff0fff0fff0fff0fffff0f0fffff0f0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffafffffffafffafffafffafffafffffafafffffafafafaa0a0fafaa0a0
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcfffcfffcfffcfffcfffffcf0fffffcf0fcf0cc00fcf0cc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffefffefffefffefffffefafffffefafefaeca0fefaeca0
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefefffffffffefefefefefefefefafafafaececececa0a0a0a0
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffffccffccffccffcccc00cc00ffccffcccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeeeaaeeaaffccffcccc00cc00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffafffffffffffafffafffafffafafafafaffa0ffa0a0a0a0a0
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfffcfffcfcf0fcf0ffccffcccc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffffffffffefffefffefffefefafefaffecffececa0eca0
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffffffeeeeeeeeffffeeeeffffaaaaeeeeccccaaaa0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffafafffffffffafafafafffffafafffffafafafaa0a0fafaa0a0
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffffffcfcfcfcfffffcfcfffff0f0fcfcccccf0f00000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffffffefefefefffffefefffffafafefeececfafaa0a0
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffffffaaffaaffffffaaffffaaaaffaaff00aaaa0000
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffffffccffccffffffccffffcc00ffccffcccc00cc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffeeffeeffffffeeffffeeaaffeeffcceeaacc00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffff0fffffffffff0fff0fffffff0fffff0f0fff0ff00f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffffffafffafffffffafffffafafffaffa0fafaa0a0
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffffffcfffcfffffffcfffffcf0fffcffccfcf0cc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffffffefffefffffffefffffefafffeffecfefaeca0
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
def isoMvS_42:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_42:Lower true dom_42 roots_42 goal_42 4:=lower_iso_b isoMvS_42 (by decide +kernel) lowS_21
def isoMvS_69:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_69:Lower true dom_69 roots_69 goal_69 4:=lower_iso_b isoMvS_69 (by decide +kernel) lowS_21
def isoMvS_81:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_21
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_21
def isoMvS_133:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_133:Lower true dom_133 roots_133 goal_133 4:=lower_iso_b isoMvS_133 (by decide +kernel) lowS_21
def isoMvS_138:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_138:Lower true dom_138 roots_138 goal_138 4:=lower_iso_b isoMvS_138 (by decide +kernel) lowS_21
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
|0,0=>0x33003300000000003200324400440000000000440000000320000000000000032cc00880000000000cc00880003300000000000000300000000000000000c800c9100110000000000110010c000c00000000000c00083300000000000000330000c000c00000000000c000c3300330000000000000000cc00c00000000000cc00c3300330000000000330000cc00cc0000000000c000c2200220000000000220022
|_,_=>0
def sP:Nat→Nat
|0=>0x6504365042650465046e504650d4650c43b50436104650a42615069504658467043210
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
|0=>0x5659160595545595459164551
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
theorem lowS_135:Lower true dom_135 roots_135 goal_135 5:=lower_slice_b [(0xcc000000000000000000000000000000cc,128,130)] (by decide +kernel) lowS_133
namespace S_147
def pG:List (Nat×Nat):=[(1,17),(1,129),(2,130),(3,19),(3,131),(16,17),(18,19),(18,146),(128,129),(128,130),(144,145),(144,146)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_147.map (·&&&dom_147)
def gM:=goal_147&&&dom_147
def NN:Nat→Nat
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x944c4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0000000000000000000000000000000f0000c000c000000000000000000000000000c000ca000a000000000000000000000000000a000af000f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xe4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|_,_=>0
def wAt:=mkWire dB 4 148 0xfffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_147 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_147 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_147==dom_147)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_147 gM v ys):RunD true dom_147 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_147 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_147 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_147 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_147 roots_147 goal_147 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_147
theorem lowS_147:Lower true dom_147 roots_147 goal_147 4:=S_147.noCircuit
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_slice_b [(0x33000000000000000000000000000000330000,1,17)] (by decide +kernel) lowS_133
def isoMvS_139:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_135
def isoMvS_141:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_135
def isoMvS_142:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 5:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_135
def isoMvS_150:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 4:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_147
def isoMvS_153:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 4:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_147
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 7:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_85
def isoMvS_177:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 4:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_147
def isoMvS_195:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 4:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_147
def isoMvS_198:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 4:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_147
def isoMvS_209:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 5:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_135
theorem lowS_31:Lower true dom_31 roots_31 goal_31 6:=lower_slice_b [(0xcccccccc,8,10),(0xff00ff00,2,10)] (by decide +kernel) lowS_21
namespace S_143
def pG:List (Nat×Nat):=[(1,5),(1,129),(2,10),(2,130),(3,7),(3,11),(3,131),(4,5),(4,132),(6,7),(6,14),(6,134),(8,10),(8,136),(9,11),(9,13),(9,137),(12,13),(12,14),(12,140),(128,129),(128,130),(128,132),(128,136)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_143.map (·&&&dom_143)
def gM:=goal_143&&&dom_143
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xfe67
|4,0=>0x2898427e6e131bf06050
|5,0=>0x8f2443a3b5246cf22f5717f421180b0e7340e0660382500bdf
|6,0=>0xb9ac72e14e1715c082e3
|7,0=>0xb9ac7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaff0000000000000000000000000000aaaafff00000000000000000000000000000fff0fff000000000000000000000000000000000005500000000000000000000000000000000ffff0000000000000000000000000000aaaaffaa000000000000000000000000000000000f0f00000000000000000000000000000f0afffc0000000000000000000000000000ccccf0f00000000000000000000000000000f0f0aaaa0000000000000000000000000000aaaa00cf000000000000000000000000000000ccffff00000000000000000000000000000000ff000000000000000000000000000000ff00ffff0000000000000000000000000000f0f0cccc0000000000000000000000000000ccccfefe0000000000000000000000000000aaaa
|0,1=>0x5555000000000000000000000000000000000f0f00000000000000000000000000000a0a55550000000000000000000000000000505000ff000000000000000000000000000000f0ffff0000000000000000000000000000ccccffff0000000000000000000000000000fcfc0f0f0000000000000000000000000000000000000000000000000000000000000000ffaa
|_,_=>0
def sP:Nat→Nat
|0=>0xce131067098833cc262386709883384c4b8c2b35883386a419c26a1072384c418826245c3104c480ce1310670bcc419c26234670988c19c2b50c264906741887098a418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b48584cf19b330654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 24 144 0xffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x9119d3123ae31199d091391192710
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x52000032002100110100
|6,0=>0x918171
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0x3ff77d5e491286080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x4003520160
|6,0=>0x79a8
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_142 5 roots_142 ops++addP pm 1 dom_138 4 roots_138 ops++addP pm 2 dom_135 5 roots_135 ops++addP pm 3 dom_133 4 roots_133 ops++addP pm 4 dom_139 5 roots_139 ops++addP pm 5 dom_141 5 roots_141 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_143 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_135 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_133 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_141 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_142 5 s (0,roots_142.map (·&&&dom_142)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_143 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_142 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_143==dom_143)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_143 gM v ys):RunD true dom_143 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_143 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_143 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_143 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_143 roots_143 goal_143 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_143
theorem lowS_143:Lower true dom_143 roots_143 goal_143 8:=S_143.noCircuit
def dzo_149_2:=0xcc00cc00000000000000000000000000cc00cc
def gzo_149_2:=0xcc00cc00000000000000000000000000c80080
def gsh_149_2:=0x33003300000000000000000000000000320020
theorem lowS_zo_149_2_21:Lower true dzo_149_2 roots_149 gzo_149_2 5:=lower_iso_b (d1:=dom_149) (r1:=roots_149) (T1:=gsh_149_2) [(dom_149,2)] (by decide +kernel) (lower_slice_b (T:=gsh_149_2) [(0x33003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
namespace S_151
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,129),(2,130),(3,7),(3,19),(3,131),(4,5),(4,20),(4,132),(6,7),(6,22),(6,134),(16,17),(16,20),(18,19),(18,22),(18,146),(128,129),(128,130),(128,132),(144,145),(144,146),(144,148)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_151.map (·&&&dom_151)
def gM:=goal_151&&&dom_151
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x88037
|5,0=>0xd5a17
|6,0=>0xaada
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff000000000000000000000000000000ff0000fa00fa00000000000000000000000000fa00faf000f000000000000000000000000000f000f0cc00cc00000000000000000000000000cc00ccaa00aa00000000000000000000000000aa00aa0000fa000000000000000000000000000000faff00ff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xd1a1ac684688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 152 0xffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_149 5 roots_149 ops++addP pm 1 dom_150 4 roots_150 ops++addP pm 2 dzo_149_2 5 roots_149 ops++addP pm 3 dom_135 5 roots_135 ops++addP pm 4 dom_21 4 roots_21 ops++addP pm 5 dom_147 4 roots_147 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_151 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_149_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_135 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_147 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_149 5 s (0,roots_149.map (·&&&dom_149)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_151 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_149 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_151==dom_151)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_151 gM v ys):RunD true dom_151 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_151 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_151 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_151 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_151 roots_151 goal_151 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_151
theorem lowS_151:Lower true dom_151 roots_151 goal_151 7:=S_151.noCircuit
def dzo_139_16:=0xf0f00000000000000000000000000000f0f0000
def gzo_139_16:=0xf0e00000000000000000000000000000e0a0000
def gsh_139_16:=0xf0e00000000000000000000000000000e0a
theorem lowS_zo_139_16_138:Lower true dzo_139_16 roots_139 gzo_139_16 5:=lower_iso_b (d1:=dom_139) (r1:=roots_139) (T1:=gsh_139_16) [(dom_139,16)] (by decide +kernel) (lower_slice_b (T:=gsh_139_16) [(0xa0a00000000000000000000000000000a0a,0,1)] (by decide +kernel) lowS_138)
namespace S_155
def pG:List (Nat×Nat):=[(1,17),(1,129),(2,10),(2,130),(3,11),(3,19),(3,131),(8,10),(8,136),(9,11),(9,25),(9,137),(16,17),(18,19),(18,26),(18,146),(24,25),(24,26),(24,152),(128,129),(128,130),(128,136),(144,145),(144,146),(144,152)]
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
|4,0=>0xcb52009a66
|5,0=>0xb7822a791e0b8b0
|6,0=>0x9aa9
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0c0f0c0000000000000000000000000f0c0f0c00f000f00000000000000000000000000000000f0f0f0f0000000000000000000000000c0c0c0cf000f000000000000000000000000000f000f00303030300000000000000000000000003000300f0f00000000000000000000000000000f0f0000c0c0c0c0000000000000000000000000c0c0c0cf000f000000000000000000000000000c000c00a0a0a0a0000000000000000000000000a0a0a0af0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x463104963104631084673104615043210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 156 0xfffffffffffffffffffffffffffffffffffffff
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
|0=>0xfa0e0
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x26
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_139 5 roots_139 ops++addP pm 1 dzo_139_16 5 roots_139 ops++addP pm 2 dom_147 4 roots_147 ops++addP pm 3 dom_153 4 roots_153 ops++addP pm 4 dom_138 4 roots_138 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_155 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_139_16_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_138 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_139 5 s (0,roots_139.map (·&&&dom_139)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_155 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_139 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
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
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_slice_b [(0xa0a00000a0a000000000000000000000a0a00000a0a,128,129)] (by decide +kernel) lowS_170
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=lower_slice_b [(0x330033000000000033003300000000000000000000000000000000,1,129)] (by decide +kernel) lowS_85
def isoMvS_47:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_47:Lower true dom_47 roots_47 goal_47 6:=lower_iso_b isoMvS_47 (by decide +kernel) lowS_31
def isoMvS_55:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_55:Lower true dom_55 roots_55 goal_55 6:=lower_iso_b isoMvS_55 (by decide +kernel) lowS_31
def isoMvS_59:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_59:Lower true dom_59 roots_59 goal_59 6:=lower_iso_b isoMvS_59 (by decide +kernel) lowS_31
def isoMvS_61:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 6:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_31
def isoMvS_62:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 6:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_31
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 6:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_31
def isoMvS_107:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 6:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_31
def isoMvS_122:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 6:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_31
def isoMvS_157:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 7:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_151
def isoMvS_158:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 7:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_155
def isoMvS_167:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 8:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_143
def isoMvS_173:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_143
def isoMvS_174:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 8:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_171
def isoMvS_179:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_155
def isoMvS_185:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 7:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_155
def isoMvS_199:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 7:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_151
def isoMvS_203:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 7:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_155
def isoMvS_211:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 7:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_155
def isoMvS_214:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 7:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_155
def isoMvS_217:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 7:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_155
def isoMvS_218:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 6:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_31
def isoMvS_220:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 7:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_155
def dzo_62_1:=0xaaaaaaaaaaaaaaaa
def gzo_62_1:=0xaaaaaaa8aaaaa8a0
def gsh_62_1:=0x5555555455555450
theorem lowS_zo_62_1_42:Lower true dzo_62_1 roots_62 gzo_62_1 6:=lower_iso_b (d1:=dom_62) (r1:=roots_62) (T1:=gsh_62_1) [(dom_62,1)] (by decide +kernel) (lower_slice_b (T:=gsh_62_1) [(0x5050505050505050,0,4),(0x5555000055550000,0,16)] (by decide +kernel) lowS_42)
def dzo_61_2:=0xcccccccccccccccc
def gzo_61_2:=0xccccccccccc8cc80
def gsh_61_2:=0x3333333333323320
theorem lowS_zo_61_2_21:Lower true dzo_61_2 roots_61 gzo_61_2 6:=lower_iso_b (d1:=dom_61) (r1:=roots_61) (T1:=gsh_61_2) [(dom_61,2)] (by decide +kernel) (lower_slice_b (T:=gsh_61_2) [(0x3300330033003300,0,8),(0x3333333300000000,0,32)] (by decide +kernel) lowS_21)
def dzo_59_4:=0xf0f0f0f0f0f0f0f0
def gzo_59_4:=0xf0f0f0e0f0f0e0a0
def gsh_59_4:=0xf0f0f0e0f0f0e0a
theorem lowS_zo_59_4_42:Lower true dzo_59_4 roots_59 gzo_59_4 6:=lower_iso_b (d1:=dom_59) (r1:=roots_59) (T1:=gsh_59_4) [(dom_59,4)] (by decide +kernel) (lower_slice_b (T:=gsh_59_4) [(0xa0a0a0a0a0a0a0a,0,1),(0xf0f00000f0f0000,0,16)] (by decide +kernel) lowS_42)
def dzo_55_8:=0xff00ff00ff00ff00
def gzo_55_8:=0xff00ff00fe00ec00
def gsh_55_8:=0xff00ff00fe00ec
theorem lowS_zo_55_8_21:Lower true dzo_55_8 roots_55 gzo_55_8 6:=lower_iso_b (d1:=dom_55) (r1:=roots_55) (T1:=gsh_55_8) [(dom_55,8)] (by decide +kernel) (lower_slice_b (T:=gsh_55_8) [(0xcc00cc00cc00cc,0,2),(0xff00ff00000000,0,32)] (by decide +kernel) lowS_21)
def dzo_47_16:=0xffff0000ffff0000
def gzo_47_16:=0xfffe0000fefa0000
def gsh_47_16:=0xfffe0000fefa
theorem lowS_zo_47_16_42:Lower true dzo_47_16 roots_47 gzo_47_16 6:=lower_iso_b (d1:=dom_47) (r1:=roots_47) (T1:=gsh_47_16) [(dom_47,16)] (by decide +kernel) (lower_slice_b (T:=gsh_47_16) [(0xaaaa0000aaaa,0,1),(0xf0f00000f0f0,0,4)] (by decide +kernel) lowS_42)
namespace S_63
def pG:List (Nat×Nat):=[(1,5),(1,17),(2,10),(2,34),(3,7),(3,11),(3,19),(3,35),(4,5),(4,20),(6,7),(6,14),(6,22),(6,38),(8,10),(8,40),(9,11),(9,13),(9,25),(9,41),(12,13),(12,14),(12,28),(12,44),(16,17),(16,20),(18,19),(18,22),(18,26),(18,50),(24,25),(24,26),(24,28),(24,56),(32,34),(32,40),(33,35),(33,37),(33,41),(33,49),(36,37),(36,38),(36,44),(36,52),(48,49),(48,50),(48,52),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffff
def xsM:=roots_63.map (·&&&dom_63)
def gM:=goal_63&&&dom_63
def NN:Nat→Nat
|7=>1
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xc6758
|8,0=>0xc6758
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ffff0000ffff0000ff00ff00ff00ff00f0f0f0f0f0f0f0f0ccccccccccccccccaaaaaaaaaaaaaaaa
|_,_=>0
def sP:Nat→Nat
|0=>0xb1a22c688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>6
|8,0=>0x66
|_,_=>0
def wAt:=mkWire dB 6 64 0xffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0x1ffc0f800
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>1
|8,0=>2
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 11 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_62 6 roots_62 ops++addP pm 1 dom_61 6 roots_61 ops++addP pm 2 dom_59 6 roots_59 ops++addP pm 3 dom_55 6 roots_55 ops++addP pm 4 dom_47 6 roots_47 ops++addP pm 5 dzo_62_1 6 roots_62 ops++addP pm 6 dom_31 6 roots_31 ops++addP pm 7 dzo_61_2 6 roots_61 ops++addP pm 8 dzo_59_4 6 roots_59 ops++addP pm 9 dzo_55_8 6 roots_55 ops++addP pm 10 dzo_47_16 6 roots_47 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_63 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_62_1_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_61_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_59_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_55_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_62 6 s (0,roots_62.map (·&&&dom_62)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_63 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_62 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_63==dom_63)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_63 gM v ys):RunD true dom_63 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_63 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_63 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_95:Lower true dom_95 roots_95 goal_95 9:=lower_slice_b [(0xcccccccc00000000cccccccc,8,10),(0xff00ff0000000000ff00ff00,2,10)] (by decide +kernel) lowS_85
def dzo_138_16:=0x505000000000000000000000000000005050000
def gzo_138_16:=0x504000000000000000000000000000004000000
def gsh_138_16:=0x50400000000000000000000000000000400
theorem lowS_zo_138_16_138:Lower true dzo_138_16 roots_138 gzo_138_16 4:=lower_iso_b (d1:=dom_138) (r1:=roots_138) (T1:=gsh_138_16) [(dom_138,16)] (by decide +kernel) (lower_slice_b (T:=gsh_138_16) [] (by decide +kernel) lowS_138)
def dzo_151_8:=0xff00ff00000000000000000000000000ff00ff00
def gzo_151_8:=0xff00ff00000000000000000000000000fe00ec00
def gsh_151_8:=0xff00ff00000000000000000000000000fe00ec
theorem lowS_zo_151_8_21:Lower true dzo_151_8 roots_151 gzo_151_8 6:=lower_iso_b (d1:=dom_151) (r1:=roots_151) (T1:=gsh_151_8) [(dom_151,8)] (by decide +kernel) (lower_slice_b (T:=gsh_151_8) [(0xcc00cc00000000000000000000000000cc00cc,0,2),(0xff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
def dzo_142_16:=0x5555000000000000000000000000000055550000
def gzo_142_16:=0x5554000000000000000000000000000054500000
def gsh_142_16:=0x555400000000000000000000000000005450
theorem lowS_zo_142_16_138:Lower true dzo_142_16 roots_142 gzo_142_16 5:=lower_iso_b (d1:=dom_142) (r1:=roots_142) (T1:=gsh_142_16) [(dom_142,16)] (by decide +kernel) (lower_slice_b (T:=gsh_142_16) [(0x505000000000000000000000000000005050,0,4)] (by decide +kernel) lowS_138)
def dzo_143_16:=0xffff0000000000000000000000000000ffff0000
def gzo_143_16:=0xfffe0000000000000000000000000000fefa0000
def gsh_143_16:=0xfffe0000000000000000000000000000fefa
theorem lowS_zo_143_16_138:Lower true dzo_143_16 roots_143 gzo_143_16 6:=lower_iso_b (d1:=dom_143) (r1:=roots_143) (T1:=gsh_143_16) [(dom_143,16)] (by decide +kernel) (lower_slice_b (T:=gsh_143_16) [(0xaaaa0000000000000000000000000000aaaa,0,1),(0xf0f00000000000000000000000000000f0f0,0,4)] (by decide +kernel) lowS_138)
def dzo_29_2:=0xcccccccc
def gzo_29_2:=0xccc8cc80
def gsh_29_2:=0x33323320
theorem lowS_zo_29_2_21:Lower true dzo_29_2 roots_29 gzo_29_2 5:=lower_iso_b (d1:=dom_29) (r1:=roots_29) (T1:=gsh_29_2) [(dom_29,2)] (by decide +kernel) (lower_slice_b (T:=gsh_29_2) [(0x33003300,0,8)] (by decide +kernel) lowS_21)
def dzo_23_8:=0xff00ff00
def gzo_23_8:=0xfe00ec00
def gsh_23_8:=0xfe00ec
theorem lowS_zo_23_8_21:Lower true dzo_23_8 roots_23 gzo_23_8 5:=lower_iso_b (d1:=dom_23) (r1:=roots_23) (T1:=gsh_23_8) [(dom_23,8)] (by decide +kernel) (lower_slice_b (T:=gsh_23_8) [(0xcc00cc,0,2)] (by decide +kernel) lowS_21)
def dzo_157_2:=0xcccccccc000000000000000000000000cccccccc
def gzo_157_2:=0xcccccccc000000000000000000000000ccc8cc80
def gsh_157_2:=0x3333333300000000000000000000000033323320
theorem lowS_zo_157_2_21:Lower true dzo_157_2 roots_157 gzo_157_2 6:=lower_iso_b (d1:=dom_157) (r1:=roots_157) (T1:=gsh_157_2) [(dom_157,2)] (by decide +kernel) (lower_slice_b (T:=gsh_157_2) [(0x3300330000000000000000000000000033003300,0,8),(0x3333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
namespace S_159
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,129),(2,10),(2,130),(3,7),(3,11),(3,19),(3,131),(4,5),(4,20),(4,132),(6,7),(6,14),(6,22),(6,134),(8,10),(8,136),(9,11),(9,13),(9,25),(9,137),(12,13),(12,14),(12,28),(12,140),(16,17),(16,20),(18,19),(18,22),(18,26),(18,146),(24,25),(24,26),(24,28),(24,152),(128,129),(128,130),(128,132),(128,136),(144,145),(144,146),(144,148),(144,152)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_159.map (·&&&dom_159)
def gM:=goal_159&&&dom_159
def NN:Nat→Nat
|5=>4
|6=>15
|7=>24
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xbde0e3af71395751bbcb
|6,0=>0xfa493e46e7e37f0d11079f1f099c6981a0e7659e496cf380cd30d3f1afd91a09d18c3318a9e
|7,0=>0xe73dddf416c9606b628fa1dc099b9e91b687a18a6c53062bd15f7e53adfa33d5d2cb802bc892ba272a1221fbed1d25516489144be1246608ee303214
|8,0=>0xd97607da7f74778738814b6ad32be3289ea025ea
|9,0=>0x932a5
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfafafafa000000000000000000000000fafafafa00ff00ff00000000000000000000000000000000fafffaff000000000000000000000000fafafafa5151515100000000000000000000000050505050ffff0000000000000000000000000000ffff000055555555000000000000000000000000505050500f0f0f0f0000000000000000000000000a0a0a0aff00ff00000000000000000000000000cc00cc0000ff00ff00000000000000000000000000cc00cc0000fafa0000000000000000000000000000fafaff00ff00000000000000000000000000ff00ff00f0f0f0f0000000000000000000000000f0f0f0f0cccccccc000000000000000000000000ccccccccaaaaaaaa000000000000000000000000aaaaaaaa00fffaff0000000000000000000000000000fafaffffffff00000000000000000000000000000000
|0,1=>0xfefefefe000000000000000000000000fefefefeffffffff000000000000000000000000ffff0000ffff3333000000000000000000000000ffff0000f3f3f3f3000000000000000000000000f0f0f0f00f0f0f0f00000000000000000000000000000000afafafaf000000000000000000000000aaaaaaaaffffffff000000000000000000000000ccccccccffffffff0000000000000000000000000000fafaffccffcc000000000000000000000000ffccffccffffffff000000000000000000000000aaaaaaaa3333333300000000000000000000000000000000bbbbbbbb000000000000000000000000aaaaaaaaffffffff000000000000000000000000ff00ff00cccccccc000000000000000000000000cc00cc00ffffffff000000000000000000000000f0f0f0f0ffffffff000000000000000000000000fafafafa
|0,2=>0xfff0fff0000000000000000000000000fff0fff00505050500000000000000000000000000000000fcfcfcfc000000000000000000000000fcfcfcfc54545454000000000000000000000000545454545555555500000000000000000000000000000000ffff5555000000000000000000000000ffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0xb1510c22404c51030860051030860152c53d10d600b14f4432802c544358224b3c40c21c01440c26005c510308600b14f44358b14f1035002c53c448200b1501032802c53440c200b1440c23002c50ca2401032021801030871801440c2040
|1=>0x8a00b5c53c40c201e1440c284b14f4430802c51120802c510308090b15110358200b1440c28802d314f1030802c53c40c20158051030802c57c40c200b15010358201e1440d609d1440c200b15c1030802c510368200b15110308a005103086
|2=>0xb1440c200b5c51030807851030802d31440c200b1440c20152c53c40c200b9451030802c510308084b1511030802c54040c200b1440d609b2c40c21c078510358200b1511035822c5103
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x9303180cc006
|6,0=>0x1e1ce2e6a731b971caae4e7243105c76c34716b899c3ee187
|7,0=>0x8fbc61e24d0b7823bf5deb0ef6743b899b6ed38663b121790b6657ba9e142c9b64a3a35d0b07f6
|8,0=>0xab3d41a92f4279dbcd1e5af267
|9,0=>0x15d6
|_,_=>0
def wAt:=mkWire dB 38 160 0xffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1404f021024201100630b0c4440914044090c08b850808f0d102561108042012c04b550c084550c0826d100910b1004b3e102501344244012cf84092cf84090c082011004211442c401584c20110259170c044092cf8409080440108442550c084094c3050109191091004f391024502
|1=>0x50d2c045010c0840914442021004f01102420110099170c042012c04201100510b100450d10242022c04401084530c
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x80cf11b3306588a1113202388598920c60cc01800
|7,0=>0xa253ca694b29251ca29432824fc9e93b2724dc9a9332624bc9692b25249c929232
|8,0=>0xb43646c0d71ac3546a0d31
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x7d7e07afc0d5f819b703276064e40c5f818bd0316e060e4087e806b50080000a0000dd801b7002660040c005a80080000aa000ec001d00032000500008c001000011000080000c000100000
|1=>0x1443f600aab06bf43d7e622dcc45a910f5211fa402f4647a8c091
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40000
|6,0=>0x60d22881c44cc6852ce080
|7,0=>0x71b8dd59781f6d564a96945e98f7a8899254
|8,0=>0x867aa2424618
|9,0=>0xd
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_143 8 roots_143 ops++addP pm 1 dzo_138_16 4 roots_138 ops++addP pm 2 dom_151 7 roots_151 ops++addP pm 3 dom_31 6 roots_31 ops++addP pm 4 dom_158 7 roots_158 ops++addP pm 5 dom_155 7 roots_155 ops++addP pm 6 dzo_151_8 6 roots_151 ops++addP pm 7 dom_157 7 roots_157 ops++addP pm 8 dom_138 4 roots_138 ops++addP pm 9 dzo_142_16 5 roots_142 ops++addP pm 10 dzo_143_16 6 roots_143 ops++addP pm 11 dzo_29_2 5 roots_29 ops++addP pm 12 dzo_23_8 5 roots_23 ops++addP pm 13 dom_142 5 roots_142 ops++addP pm 14 dom_149 5 roots_149 ops++addP pm 15 dzo_157_2 6 roots_157 ops++addP pm 16 dzo_149_2 5 roots_149 ops++addP pm 17 dzo_139_16 5 roots_139 ops++addP pm 18 dom_21 4 roots_21 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_159 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_138_16_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_151_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_142_16_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_143_16_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_29_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_23_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_157_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_149_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_139_16_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_21 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_143 8 s (0,roots_143.map (·&&&dom_143)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_159 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_143 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_159==dom_159)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_159 gM v ys):RunD true dom_159 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_159 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 15 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_159 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
namespace S_175
def pG:List (Nat×Nat):=[(1,5),(1,129),(2,10),(2,34),(2,130),(3,7),(3,11),(3,35),(3,131),(4,5),(4,132),(6,7),(6,14),(6,38),(6,134),(8,10),(8,40),(8,136),(9,11),(9,13),(9,41),(9,137),(12,13),(12,14),(12,44),(12,140),(32,34),(32,40),(32,160),(33,35),(33,37),(33,41),(33,161),(36,37),(36,38),(36,44),(36,164),(128,129),(128,130),(128,132),(128,136),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_175.map (·&&&dom_175)
def gM:=goal_175&&&dom_175
def NN:Nat→Nat
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0x3e74a
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff0000000000000000000000000000ffff00000000ff000000ff0000000000000000000000ff000000ff00f0f00000f0f000000000000000000000f0f00000f0f0cccc0000cccc00000000000000000000cccc0000ccccaaaa0000aaaa00000000000000000000aaaa0000aaaaffff0000ffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c688
|_=>0
def sO:Nat→Nat→Nat
|9,0=>6
|_,_=>0
def wAt:=mkWire dB 6 176 0xffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0x3e0
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_174 8 roots_174 ops++addP pm 1 dom_173 8 roots_173 ops++addP pm 2 dom_171 8 roots_171 ops++addP pm 3 dom_167 8 roots_167 ops++addP pm 4 dom_143 8 roots_143 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_175 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_143 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_174 8 s (0,roots_174.map (·&&&dom_174)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_175 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_174 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_175==dom_175)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_175 gM v ys):RunD true dom_175 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_175 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_175 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_175 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_175 roots_175 goal_175 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_175
theorem lowS_175:Lower true dom_175 roots_175 goal_175 10:=S_175.noCircuit
def dzo_171_16:=0xf0f00000f0f000000000000000000000f0f00000f0f0000
def gzo_171_16:=0xf0f00000f0e000000000000000000000f0e00000e0a0000
def gsh_171_16:=0xf0f00000f0e000000000000000000000f0e00000e0a
theorem lowS_zo_171_16_170:Lower true dzo_171_16 roots_171 gzo_171_16 8:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_16) [(dom_171,16)] (by decide +kernel) (lower_slice_b (T:=gsh_171_16) [(0xa0a00000a0a000000000000000000000a0a00000a0a,0,1)] (by decide +kernel) lowS_170)
namespace S_187
def pG:List (Nat×Nat):=[(1,17),(1,129),(2,10),(2,34),(2,130),(3,11),(3,19),(3,35),(3,131),(8,10),(8,40),(8,136),(9,11),(9,25),(9,41),(9,137),(16,17),(18,19),(18,26),(18,50),(18,146),(24,25),(24,26),(24,56),(24,152),(32,34),(32,40),(32,160),(33,35),(33,41),(33,49),(33,161),(48,49),(48,50),(48,56),(48,176),(128,129),(128,130),(128,136),(128,160),(144,145),(144,146),(144,152),(144,176)]
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
|4,0=>0x17690127ac0065a
|5,0=>0xd139b92659636b1568ed446ab419a8315262900324e1b1577a14e3812f051199210ca110a930f1120911508c3508091077fe0508301f0000fad0065a
|6,0=>0xeedc1bac4cae7e4a948298d8589c1177e68722e27081d6f4b16df69698c7635dd604045d0f25cddb54a4d52d2a4f5834e59b446ab4195f3e60e390163821b35b4f34d69342ad335ad2f29b2df492be23294b4292d02333e22d102256e210da1e0b8174291720c1658516401136e1117a910a930a2c409de40809107a850689d036b102f94004bf004a1
|7,0=>0xb5976ad6c97ea7a72a65719cc718ea5cddb5a8394ea473f0ba3bf262abb3261d322f9a1b8b612b8110a1e0adbb06719050d4
|8,0=>0x824c96a88826f6b
|9,0=>0x3dbb0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0000000000000000000000000f0f0f0f00000000f0c0f0c0f0c0f0c00000000000000000000000000000000f0c0f0c0f0c0f0c00000000000000000f0c0f0c0f0c0f0cf0f0f0f0f0f0f0f00000000000000000000000000000000f000f000f000f0000000000000000000f000f000f000f00f0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0f0f0f0c0c0c0c00000000000000000f000f000c000c00f0f0f0f0f0f0f0f00000000000000000c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000c0f0c0f0c0f0c0f00000000000000000c0c0c0c0c0c0c0c00f000f000c000c0000000000000000000f000f000c000cf0f0f0f0f0c0f0c00000000000000000f0f0f0f00000000f0f00000f0f000000000000000000000f0f00000f0f0000f0f0f0f0f0f0f0f00000000000000000f000f000f000f00c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a
|0,1=>0xf000f000f000f00000000000000000000000000000000f0f0f0f000f000f00000000000000000f0f0f0f00000000f0f0f0f0e0e0e0e00000000000000000f0a0f0a0e0a0e0af030f030f030f0300000000000000000f000f000f000f0030303030300030000000000000000000303030303000300f0f0f0f0f000f0000000000000000000c0c0c0c0c000c00f000f000f000f0000000000000000000f000f000c000c0000000000f0f0f0f0000000000000000000000000c0c0c0c00000000f0f0f0f0000000000000000000000000f000f00f0f0f0f0000000000000000000000000f0c0f0c0000000000000000f0c0f0c0000000000000000000000000f0c0f0cf0f0f0f0c0c0c0c00000000000000000f0f0f0f0c0c0c0cf0f0f0f0f0f0f0f00000000000000000f0c0f0c0f0c0f0cf0f0f0f0f0f0f0f0000000000000000000000000f0c0f0c00000000f0f0f0f00000000000000000000000000000000f0c0f0c0f0c0f0c00000000000000000f0c0f0c00000000
|0,2=>0xf000f000f0f0f0f00000000000000000f000f000f0c0f0c00000000f0f0f0f0000000000000000000000000f0c0f0cf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0c0f0c000000003030303000000000000000000000000000000000000000000000000000000000000000000f000f000c000c00f000f000f000f0000000000000000000c000c000c000c00c000c000f000f0000000000000000000c000c000c000cf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c000c0000000000000000000000000000000000f0f0f0f0c0c0c0c00f000f000f000f0000000000000000000f000f00000000f0f0f0f0f0e0f0e00000000000000000a0a0a0a0a0a0a0a00f000f000f000f0000000000000000000f000f000c000c00300030003000300000000000000000f000f000f000f00f0f0f0f0f0c0f0c00000000000000000f0f0f0f0f0c0f0cf0f0f0f0f0c0f0c00000000000000000000000000000000
|0,3=>0xf0c0f0c0000000000000000000000000f0c0f0c0f0c0f0cf0f0f0f0c0c0c0c0000000000000000000000000000000000000000300030000000000000000000f000f000f000f00c0c0c0c0c0c0c0c00000000000000000f0f0f0f0f0c0f0c30303030303030300000000000000000303030303000300f0f0f0f0f000f000000000000000000000000000000000000000000303030300000000000000000000000003000300f0f0f0f0f0f0f0f0000000000000000000f000f000c000cf0c0f0c0f0f0f0f00000000000000000f0c0f0c0f0c0f0c0000000000f000f00000000000000000000000000000000c0c0c0c0c0f0c0f00000000000000000c0c0c0c0c0c0c0cf0e0f0e0f0e0f0e00000000000000000a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0c0c0c0c3030303030303030000000000000000030303030000000000000000000000000000000000000000f0f0f0f0f0c0f0cf0f0f0f0003000300000000000000000000000000000000
|0,4=>0xf0f0f0f0f000f0030303030303030300000000000000000000000000000000003000300030003000000000000000000000000000000003030303030303030000000000000000030003000300030000000000003000300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1e0c122020108f06084001e0c5880080a1e062c4001e0ce8b02307833800d8c1e0c1013400507064c080083c1820200203160400c0664080303050706344001e0c688005c196160400c062c4002a44514064c00c062c0802444503200400c080c101002818910003830c002840608080
|1=>0x5c3168f062c080185018b1000c0c1e0c10b02016141e0c5860030203160400c141c18b100400f062c401005c196160400c1e0c58100ac60f0634080543018d2c2c080183c18b020148c503c18b4e00607062c0803630526063400c06040252e30783160520c0e0c5880014783020118c
|2=>0x608080743c18b0201c8c1e0c58100e060a660c5810030196042c080183c1b7160400c147818b020060f062da8100307831605a0c1e0c58800c86311e0c581003130f0634580183c18b026800c0e0c5880200c0f062c08018c020f062c080181c78316180801e0d78b02006031620080
|3=>0x2006201e0df8b020060f06f4080183c18b0200c1f143c18b00ec60a280c680183c18d1600c0c1e0c98b02008871e0c98b0201e0f062c08018503831a2c00c283c18b1000fb31e0c5810030783160403b183c181001461f064c58100b8633062c0803030783020118c423c18b100060f
|4=>0x3198f062c0801878783160400c1e0c5810031d0f062c0800a30783160402a183c18b02006421e0c68b0200642143c182020060f060858101046071e0c10b0200621283c18b020060f0608581004438f060858100cc38f062c080183c18b0200640141c182020060a0e0c101003c18b
|5=>0x783160400c1e0c5810030f8f0608581003050f062c0801884783160400c883c18b020060a1e0c588020060a1e0c581003218a280c581003140a1e0c581
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa50154005
|5,0=>0x2618926231886620187a61d186e61a18626171856614184a611183e60e183260b1826608181a605180f5
|6,0=>0x2107825e0367f1df577bd9e87785ddb6751dcd7719dbf76e1db176a9da37671d957639d886605d7b65d1d6d7599d5f7561d517529d4464f5d3674bdd287485d1a744dd0c7415cfe73ddcf073a5ce273718d57339cc86305cba72cdcac7295c9e7
|7,0=>0xa91e9d7a5628d8a19e7e89dde7079a5e62796de54793224578f623588b6226787de178
|8,0=>0x2b97ac9eab7
|9,0=>0x2c06
|_,_=>0
def wAt:=mkWire dB 69 188 0xfffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x163d00391a3016056607103d023142331405163d2833023d14200231163d103f02312a321a3f022d027d1632103f0231263f102d103f02312832023d027d16321e391a301605043f1631263c1a31022d262f1a311605263c1a31008142301405163d1e7d1632142002311a31022d1a3116050e341e3116051e391a3016311605
|1=>0x16051631163d040716311e311631282d023d16311e321e3116310e051e3142321405163d1e2d1e3116311e311631163d42301405163d1a47022d16fb2830023d5007143116051e051e2d103f02311a31022d1a3116051e051a31022d103d103f0231662f2831023d14301631163d280a16311e210231263c040516311ed91432
|2=>0x16321631163d1405163d1433163d0231163d1e2d02321e051e2d1431163d2831023d1e7d16321430163d282f023d102f02311a3216051a32
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xf40000000000000000d20000000b2092000000000000000000000072000043004
|6,0=>0x6e36b36836536326030005e25b35925725520000005410000000005224f34c30004934720004524230003f30003c33933633423132f22c30002a22822620002422222021d30001b2183000153132000000000
|7,0=>0x9729529329128f28d28b28928728528328127f27d27b2792772752732712
|8,0=>0x9b19a1991
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x84a01655113bcdf33ca827c9d2608f224822007f17c450801f0741a0601204410028080140400800
|1=>0xdff3897e3f
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x80000000180004040000000000040143
|6,0=>0x35193810c010c1010400110000017830191801090130161c210f48b00110600810158018f01c18000d
|7,0=>0x8d029781885a6a13da75b55489b65f
|8,0=>0x1a690
|9,0=>0xf
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_171 8 roots_171 ops++addP pm 1 dom_155 7 roots_155 ops++addP pm 2 dzo_171_16 8 roots_171 ops++addP pm 3 dom_179 7 roots_179 ops++addP pm 4 dom_185 7 roots_185 ops++addP pm 5 dom_147 4 roots_147 ops++addP pm 6 dom_170 7 roots_170 ops++addP pm 7 dom_59 6 roots_59 ops++addP pm 8 dom_177 4 roots_177 ops++addP pm 9 dom_153 4 roots_153 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_187 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_171_16_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_153 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_171 8 s (0,roots_171.map (·&&&dom_171)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_187 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_171 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
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
def dzo_213_2:=0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc
def gzo_213_2:=0xcc00cc0000000000cc00cc0000000000cc00c80000000000c80080
def gsh_213_2:=0x330033000000000033003300000000003300320000000000320020
theorem lowS_zo_213_2_85:Lower true dzo_213_2 roots_213 gzo_213_2 8:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_2) [(dom_213,2)] (by decide +kernel) (lower_slice_b (T:=gsh_213_2) [(0x330033000000000033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
namespace S_215
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,65),(1,129),(2,130),(3,7),(3,19),(3,67),(3,131),(4,5),(4,20),(4,68),(4,132),(6,7),(6,22),(6,70),(6,134),(16,17),(16,20),(16,80),(18,19),(18,22),(18,82),(18,146),(64,65),(64,68),(64,80),(66,67),(66,70),(66,82),(66,194),(128,129),(128,130),(128,132),(144,145),(144,146),(144,148),(144,208),(192,193),(192,194),(192,196),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_215.map (·&&&dom_215)
def gM:=goal_215&&&dom_215
def NN:Nat→Nat
|4=>3
|5=>15
|6=>35
|7=>15
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x94f108fae2530c1
|5,0=>0xe6664d68c571f6150d2f422f23a5512abaf2553d2227f207b31757616bbc0f60f0b9520ab59
|6,0=>0xd85b5d3457bce9cb9443b2b1ba6b91963fc8fa3f71f076271a61c3f5caf45c2ad58d4455bd250bcd4a71e472de46fc53197030ca030b772a7e1290b3266242553d168e8167a90efbb0d20f0d20b0b77f08099063cb026f3
|7,0=>0x542dd4a6d536ffd36d5a318c32b1361b22b1891e1861517bab11398078b0062b604f3f04146
|8,0=>0xaf223335f02ce63
|9,0=>0xde6cd
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff0000000000fa00fa0000000000ff00ff0000000000fa00faff00f00000000000ff00f00000000000ff00f00000000000ff00f0ff00ff0000000000aa00aa0000000000ff00ff0000000000aa00aaaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aaf000f00000000000f000f00000000000f000f00000000000f000f0ff00ff0000000000ff00000000000000ff00ff0000000000ff0000ff00aa0000000000f000a00000000000ff00aa0000000000f000a0ff00aa0000000000ff00aa0000000000ff00aa0000000000ff00aaff00ff0000000000f000f00000000000ff00ff0000000000f000f0ff00f00000000000aa00a00000000000ff00f00000000000aa00a0ff00ff0000000000ff00ff00000000000000000000000000000000ff00000000000000ff00000000000000ff00000000000000ff0000fa00fa0000000000fa00fa0000000000fa00fa0000000000fa00facc00cc0000000000cc00cc0000000000cc00cc0000000000cc00ccff00ff0000000000ff00ff0000000000ff00f00000000000aa00a0ff00ff00000000000000000000000000ff00ff0000000000000000
|0,1=>0xff00ff0000000000ff00aa0000000000ff00ff0000000000ff00aaff000f0000000000ff000a0000000000ff000f0000000000ff000a0000000000000000ff00f000000000000000000000000000ff00f0ff00000000000000fa00000000000000ff00000000000000fa0000f000ff0000000000f000fa0000000000f000ff0000000000f000fa0000000000000000fa00fa00000000000000000000000000fa00fa0000ff00000000000000fa00000000000000ff00000000000000fa550055000000000055005000000000005500550000000000550050ff00fa00000000000000000000000000ff00fa0000000000000000ff00fa0000000000ff00fa0000000000ff00fa0000000000ff00fa0000000000000000ff00aa00000000000000000000000000ff00aa0f000f00000000000a000a00000000000f000f00000000000a000a0000000000000000ff00fa00000000000000000000000000ff00faff00ff0000000000ff00ff0000000000ff00aa0000000000f000a00000fa00000000000000fa00000000000000fa00000000000000faff00ff0000000000ff00f00000000000ff00ff0000000000ff00f0
|0,2=>0xff00ff0000000000ff00fa0000000000ff00ff0000000000ff00faff00000000000000ff00fa0000000000ff00000000000000ff00fa00000000000000000000fa000000000000000000000000000000fa0000ff00000000000000aa00000000000000ff00000000000000aa0000550000000000000050000000000000005500000000000000500f000a00000000000f000a00000000000f000a00000000000f000a
|_,_=>0
def sP:Nat→Nat
|0=>0x801472c231900510b08c5c510b08c60014a2c908c14b08c45715610708d14e54308015020b08d14e24230014828b09415310b08c1442d208c0040c90801441c235115010308d14e28f08c14e20708d1482831c214a0c90852070861440c2040
|1=>0x1032c28801432c23190052842c23141442c232100510b08d80014a10f2c23053841c234c15f1072c23052840c708c15e10b08c00511a2c234c14e28708c15310b08c15d20b08c0055841c230015c1cb08c00510b08c6401446cb08c00520468b
|2=>0x2040cb0801440cb08c44015f10b08c0053842c234c0052840cb08c00559310b08c16510b08c0059042c230015610b08c5c57c40cb0801440da1c23052040c70801440c708d1442c908c00510b08c8c01562c23110050dc2c23001482872c2305
|3=>0x10b08c0051032c230014a10b08c0053842c23001442c231400510f2c23001503842c23001442c231100520a2c230014e20b08c00510f0cb08c0052042c234015d10b08c00558810b08c005
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x18d8bac57628b12d88ac3f61cb0cd85ac27610b06d82ac0f6
|6,0=>0x54de98f4579f3cdde60f29791b471e2af0e783bc01df2ef2775bb91dbaed6767bb21d82eba759bab594eca074cba49d16e8473eb9d9ce0c697
|7,0=>0x709f76fb38d63e95f3cf968c7be21f011797b8c5a9ec515a8
|8,0=>0x75dfa0fc97
|9,0=>0x1de6
|_,_=>0
def wAt:=mkWire dB 38 216 0xffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc4cb3110f03012cc4d13300443e0c04b3134bcc012c88c110c04b31344403130b4f0334b4c011004b012c4405a0c44b31380c42d30e4b113c40731344cc010c0cb313c4c73101603112cc503328b44011c80c112c04c392c44a2d100481c2c04c111c80c112c04e012c447312c04c2d
|1=>0xb311004b1134bcc010c04b313804b110c4cb31304401110c4b110c04b313004c11380cb1120b4c113044b310c4cb3128c44013004b112cc44010c44b310c0cb312004c110038c2d2cc40312c047203044b012838b31100440d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x3cc000d20002c8418000000002980006404800001
|6,0=>0x1408004e200130a510008e710e09be3766001c936368400191302000b89688005469cd21a22404788001c2344608a9923
|7,0=>0x1b8b616a2d0598b21622c0578ae15a2b0558aa1522
|8,0=>0x1c8788f01
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x6f56306015ff5dd4f54df2fd1fd1110ff0fd0f90ef0bf0b509909108508108003c03002802402001000c008004002000
|1=>0xa2a9fd999
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40030051c0000240142001
|6,0=>0x30020062004d435d3c018e0800c20060405923050c600608650b
|7,0=>0x178625197e06d879a41c291
|8,0=>0x14558
|9,0=>0x14
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_213 8 roots_213 ops++addP pm 1 dom_135 5 roots_135 ops++addP pm 2 dom_199 7 roots_199 ops++addP pm 3 dom_151 7 roots_151 ops++addP pm 4 dom_214 7 roots_214 ops++addP pm 5 dom_211 7 roots_211 ops++addP pm 6 dom_85 7 roots_85 ops++addP pm 7 dzo_213_2 8 roots_213 ops++addP pm 8 dom_150 4 roots_150 ops++addP pm 9 dom_195 4 roots_195 ops++addP pm 10 dom_198 4 roots_198 ops++addP pm 11 dom_147 4 roots_147 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_215 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_135 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_213_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_147 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_213 8 s (0,roots_213.map (·&&&dom_213)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_215 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_213 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_215==dom_215)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_215 gM v ys):RunD true dom_215 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_215 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 35 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_215 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_215 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_215 roots_215 goal_215 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_215
theorem lowS_215:Lower true dom_215 roots_215 goal_215 10:=S_215.noCircuit
def dzo_154_64:=0x5050505000000000000000000000000050505050000000000000000
def gzo_154_64:=0x5050504000000000000000000000000050504000000000000000000
def gsh_154_64:=0x505050400000000000000000000000005050400
theorem lowS_zo_154_64_138:Lower true dzo_154_64 roots_154 gzo_154_64 5:=lower_iso_b (d1:=dom_154) (r1:=roots_154) (T1:=gsh_154_64) [(dom_154,64)] (by decide +kernel) (lower_slice_b (T:=gsh_154_64) [(0x505000000000000000000000000000005050000,0,16)] (by decide +kernel) lowS_138)
def dzo_89_2:=0xc0c0c0c000000000c0c0c0c
def gzo_89_2:=0xc0c0c08000000000c080c00
def gsh_89_2:=0x30303020000000003020300
theorem lowS_zo_89_2_81:Lower true dzo_89_2 roots_89 gzo_89_2 5:=lower_iso_b (d1:=dom_89) (r1:=roots_89) (T1:=gsh_89_2) [(dom_89,2)] (by decide +kernel) (lower_slice_b (T:=gsh_89_2) [(0x30003000000000003000300,0,8)] (by decide +kernel) lowS_81)
def dzo_83_8:=0xf000f00000000000f000f00
def gzo_83_8:=0xf000e00000000000e000c00
def gsh_83_8:=0xf000e00000000000e000c
theorem lowS_zo_83_8_81:Lower true dzo_83_8 roots_83 gzo_83_8 5:=lower_iso_b (d1:=dom_83) (r1:=roots_83) (T1:=gsh_83_8) [(dom_83,8)] (by decide +kernel) (lower_slice_b (T:=gsh_83_8) [(0xc000c00000000000c000c,0,2)] (by decide +kernel) lowS_81)
def dzo_202_16:=0x5050000000000000505000000000000050500000000000005050000
def gzo_202_16:=0x5050000000000000504000000000000050500000000000004000000
def gsh_202_16:=0x505000000000000050400000000000005050000000000000400
theorem lowS_zo_202_16_138:Lower true dzo_202_16 roots_202 gzo_202_16 5:=lower_iso_b (d1:=dom_202) (r1:=roots_202) (T1:=gsh_202_16) [(dom_202,16)] (by decide +kernel) (lower_slice_b (T:=gsh_202_16) [(0x505000000000000000000000000000005050000000000000000,0,64)] (by decide +kernel) lowS_138)
def dzo_203_16:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000
def gzo_203_16:=0xf0f0000000000000f0e0000000000000f0f0000000000000e0a0000
def gsh_203_16:=0xf0f0000000000000f0e0000000000000f0f0000000000000e0a
theorem lowS_zo_203_16_138:Lower true dzo_203_16 roots_203 gzo_203_16 6:=lower_iso_b (d1:=dom_203) (r1:=roots_203) (T1:=gsh_203_16) [(dom_203,16)] (by decide +kernel) (lower_slice_b (T:=gsh_203_16) [(0xa0a0000000000000a0a0000000000000a0a0000000000000a0a,0,1),(0xf0f00000000000000000000000000000f0f0000000000000000,0,64)] (by decide +kernel) lowS_138)
def dzo_217_2:=0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c
def gzo_217_2:=0xc0c0c0c000000000c0c0c0c000000000c0c0c08000000000c080c00
def gsh_217_2:=0x3030303000000000303030300000000030303020000000003020300
theorem lowS_zo_217_2_81:Lower true dzo_217_2 roots_217 gzo_217_2 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_2) [(dom_217,2)] (by decide +kernel) (lower_slice_b (T:=gsh_217_2) [(0x3000300000000000300030000000000030003000000000003000300,0,8),(0x3030303000000000303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_81)
def dzo_211_8:=0xf000f00000000000f000f00000000000f000f00000000000f000f00
def gzo_211_8:=0xf000f00000000000f000f00000000000f000e00000000000e000c00
def gsh_211_8:=0xf000f00000000000f000f00000000000f000e00000000000e000c
theorem lowS_zo_211_8_81:Lower true dzo_211_8 roots_211 gzo_211_8 6:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_8) [(dom_211,8)] (by decide +kernel) (lower_slice_b (T:=gsh_211_8) [(0xc000c00000000000c000c00000000000c000c00000000000c000c,0,2),(0xf000f00000000000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_81)
def dzo_209_2:=0xc000c00000000000c000c00000000000c000c00000000000c000c
def gzo_209_2:=0xc000c00000000000c000c00000000000c00080000000000080000
def gsh_209_2:=0x30003000000000003000300000000000300020000000000020000
theorem lowS_zo_209_2_81:Lower true dzo_209_2 roots_209 gzo_209_2 5:=lower_iso_b (d1:=dom_209) (r1:=roots_209) (T1:=gsh_209_2) [(dom_209,2)] (by decide +kernel) (lower_slice_b (T:=gsh_209_2) [(0x30003000000000003000300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_81)
def dzo_155_64:=0xf0f0f0f0000000000000000000000000f0f0f0f0000000000000000
def gzo_155_64:=0xf0f0f0e0000000000000000000000000f0f0e0a0000000000000000
def gsh_155_64:=0xf0f0f0e0000000000000000000000000f0f0e0a
theorem lowS_zo_155_64_138:Lower true dzo_155_64 roots_155 gzo_155_64 6:=lower_iso_b (d1:=dom_155) (r1:=roots_155) (T1:=gsh_155_64) [(dom_155,64)] (by decide +kernel) (lower_slice_b (T:=gsh_155_64) [(0xa0a0a0a0000000000000000000000000a0a0a0a,0,1),(0xf0f00000000000000000000000000000f0f0000,0,16)] (by decide +kernel) lowS_138)
namespace S_219
def pG:List (Nat×Nat):=[(1,17),(1,65),(1,129),(2,10),(2,130),(3,11),(3,19),(3,67),(3,131),(8,10),(8,136),(9,11),(9,25),(9,73),(9,137),(16,17),(16,80),(18,19),(18,26),(18,82),(18,146),(24,25),(24,26),(24,88),(24,152),(64,65),(64,80),(66,67),(66,74),(66,82),(66,194),(72,73),(72,74),(72,88),(72,200),(128,129),(128,130),(128,136),(144,145),(144,146),(144,152),(144,208),(192,193),(192,194),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffff
def xsM:=roots_219.map (·&&&dom_219)
def gM:=goal_219&&&dom_219
def NN:Nat→Nat
|4=>1
|5=>3
|6=>9
|7=>18
|8=>10
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x4e3f
|5,0=>0x538f811b3807150
|6,0=>0xf8774a2ea0608d359c4c2b21913d6210aac02c6300866
|7,0=>0xdadaccb3d6c9374a8cd47a7c175c6440282300362c0c9274e41a1701621012d0b089d203c980399c029a401256
|8,0=>0xdadacb456dab7b1798d44af0f2fd772626f088ca0794606cbf
|9,0=>0x798d4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0af0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0a00f000f00000000000f000f0000000000000000000000000000000000f000f00000000000f000f00000000000c000c00000000000c000c0000f0f0000000000000a0a0000000000000f0f0000000000000a0af0f0000000000000f0f0000000000000f0f0000000000000f0f0000f000f00000000000f000f00000000000f000f00000000000f000f003030303000000000303030300000000030003000000000003000300f0f0a0a0000000000000000000000000f0f0a0a0000000000000000f000f00000000000f000f00000000000c000c00000000000c000c00f0f0000000000000a0a0000000000000f0f0000000000000a0a0000f0f0f00000000000f0a0f00000000000f0f0c00000000000e0a0c00c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0ca0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f0000000000000000000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f00000000000000000000000000000000
|0,1=>0xa0a0000000000000a0a0000000000000a0a0000000000000a0a0000000000000000f0f0f0f00000000000000000000000000000000f0f00000000000000000000000000000f0f0000000000000f0f0000b0b0b0b000000000b0b0b0b000000000a0a0a0a000000000a0a0a0a00000000000000000000000000000000a0a0a0a000000000a0a0a0a50505050000000005050505000000000000000000000000000000003030303000000000b0b0b0b0000000000000000000000000a0a0a0aa0a0a0a000000000a0a0a0a00000000000000000000000000000000f0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0a50505050000000005050505000000000a0a0a0a000000000a0a0a0af0c0f0c000000000f0c0f0c000000000f0c0f0c000000000f0c0f0cf0f0f0f000000000f0f0f0f000000000f000f00000000000f000f00f0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f0000c0c0c0c000000000c0c0c0c000000000c000c00000000000c000c003030303000000000303030300000000000000000000000000000000f0f0f0f000000000f0f0f0f000000000c0c0c0c000000000c0c0c0c
|0,2=>0xe0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0ef0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f00f0f0f0f0000000005050505000000000000000000000000000000002020202000000000202020200000000020202020000000002020202f020f02000000000f020f02000000000f020f02000000000f020f02f0f0a0a000000000f0f0a0a000000000f0f0000000000000f0f00000000000000000000a0a0a0a0000000000000000000000000a0a0a0af000f00000000000f0a0f0a000000000f000f00000000000f0a0f0a50500000000000005050000000000000f0f0000000000000f0f0000
|_,_=>0
def sP:Nat→Nat
|0=>0xc20408090c20402890880402890c27c10117490c20403ca5090c20402890dc08100a24358128338230100a2430990402890d75815490c22c10132894820402890c21c044f28318204024308b04034308c2c100a2422070031821410040c2040
|1=>0xa24308100a2680c204029424308100a24308101e9ca24308100a2430810112890c26c100a2435c20402890c204098a2435c160a2436c168a5490ce08100a90308102324308100a0c608100a5090c27c100a5490c288100a8490c20404ca549
|2=>0x2890c20402890d708100a243081018295243081
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x45816c056
|6,0=>0x4e523b901c74c337163895c3ce177
|7,0=>0x190ec175db2d595b0a7650b26d92708b84239f20ecc7063441898b50537
|8,0=>0x21af0677fbbe59e4eeb7723b75dacecf7
|9,0=>0x1146
|_,_=>0
def wAt:=mkWire dB 41 220 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x20108003250c2490104089290c0800a080408b0428200080420200282050c949950c28a6108010240c0422b24042070c949890428a050c94a63080140f240422b0c08a7b040822924042450c09b69080800a409c3015d8c2000804e2b042540c240400f3c10a09409030138ac109
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x103388002cc921c84308802
|7,0=>0xd4732c4af2b4ab2a4a7294a32849f2749b26497254932
|8,0=>0xf87d1f0400ec7a1e4781dc761
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0x943e7041fd0601921501e0e628bcc516d8985b125ae2414c456f86250058b60616c09fd812ff025f6049ec092981241020f60380c06a0802ff00282003fc0029800400002000008000080000
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x61010121c83
|7,0=>0x1af43fb98ca8ad25d862f97
|8,0=>0x2109b6bbf7ed0
|9,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_217 7 roots_217 ops++addP pm 1 dom_155 7 roots_155 ops++addP pm 2 dzo_154_64 5 roots_154 ops++addP pm 3 dzo_89_2 5 roots_89 ops++addP pm 4 dom_211 7 roots_211 ops++addP pm 5 dzo_83_8 5 roots_83 ops++addP pm 6 dom_203 7 roots_203 ops++addP pm 7 dzo_202_16 5 roots_202 ops++addP pm 8 dzo_203_16 6 roots_203 ops++addP pm 9 dom_218 6 roots_218 ops++addP pm 10 dom_209 5 roots_209 ops++addP pm 11 dzo_217_2 6 roots_217 ops++addP pm 12 dom_91 6 roots_91 ops++addP pm 13 dzo_211_8 6 roots_211 ops++addP pm 14 dom_81 4 roots_81 ops++addP pm 15 dzo_209_2 5 roots_209 ops++addP pm 16 dom_138 4 roots_138 ops++addP pm 17 dzo_155_64 6 roots_155 ops++addP pm 18 dzo_139_16 5 roots_139 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_154_64_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_89_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_83_8_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_202_16_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_203_16_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_217_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_211_8_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_209_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_155_64_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_139_16_138 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_217 7 s (0,roots_217.map (·&&&dom_217)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_217 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_219==dom_219)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_219 gM v ys):RunD true dom_219 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_219 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 18 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 18 0 = true)
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
def isoMvS_111:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_111:Lower true dom_111 roots_111 goal_111 9:=lower_iso_b isoMvS_111 (by decide +kernel) lowS_63
def isoMvS_119:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_119:Lower true dom_119 roots_119 goal_119 9:=lower_iso_b isoMvS_119 (by decide +kernel) lowS_95
def isoMvS_123:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)]
theorem lowS_123:Lower true dom_123 roots_123 goal_123 9:=lower_iso_b isoMvS_123 (by decide +kernel) lowS_63
def isoMvS_125:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=lower_iso_b isoMvS_125 (by decide +kernel) lowS_95
def isoMvS_126:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_iso_b isoMvS_126 (by decide +kernel) lowS_63
def isoMvS_183:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 10:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_159
def isoMvS_189:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 10:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_159
def isoMvS_190:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 10:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_187
def isoMvS_207:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_207:Lower true dom_207 roots_207 goal_207 10:=lower_iso_b isoMvS_207 (by decide +kernel) lowS_159
def isoMvS_221:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 10:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_215
def isoMvS_222:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 10:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_219
def isoMvS_231:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 10:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_159
def isoMvS_235:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_235:Lower true dom_235 roots_235 goal_235 10:=lower_iso_b isoMvS_235 (by decide +kernel) lowS_187
def isoMvS_237:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 10:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_159
def isoMvS_238:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 10:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_187
def isoMvS_243:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 10:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_219
def isoMvS_245:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 10:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_215
def isoMvS_246:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_219
def isoMvS_249:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_219
def isoMvS_250:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 9:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_95
def isoMvS_252:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 10:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_219
def dzo_125_2:=0xcccccccccccccccccccccccccccccccc
def gzo_125_2:=0xccccccccccccccc8ccccccccccc8cc80
def gsh_125_2:=0x33333333333333323333333333323320
theorem lowS_zo_125_2_85:Lower true dzo_125_2 roots_125 gzo_125_2 9:=lower_iso_b (d1:=dom_125) (r1:=roots_125) (T1:=gsh_125_2) [(dom_125,2)] (by decide +kernel) (lower_slice_b (T:=gsh_125_2) [(0x33003300330033003300330033003300,0,8),(0x33333333000000003333333300000000,0,32)] (by decide +kernel) lowS_85)
def dzo_119_8:=0xff00ff00ff00ff00ff00ff00ff00ff00
def gzo_119_8:=0xff00ff00ff00fe00ff00ff00fe00ec00
def gsh_119_8:=0xff00ff00ff00fe00ff00ff00fe00ec
theorem lowS_zo_119_8_85:Lower true dzo_119_8 roots_119 gzo_119_8 9:=lower_iso_b (d1:=dom_119) (r1:=roots_119) (T1:=gsh_119_8) [(dom_119,8)] (by decide +kernel) (lower_slice_b (T:=gsh_119_8) [(0xcc00cc00cc00cc00cc00cc00cc00cc,0,2),(0xff00ff0000000000ff00ff00000000,0,32)] (by decide +kernel) lowS_85)
def dzo_95_32:=0xffffffff00000000ffffffff00000000
def gzo_95_32:=0xfffffffe00000000fffeffec00000000
def gsh_95_32:=0xfffffffe00000000fffeffec
theorem lowS_zo_95_32_85:Lower true dzo_95_32 roots_95 gzo_95_32 9:=lower_iso_b (d1:=dom_95) (r1:=roots_95) (T1:=gsh_95_32) [(dom_95,32)] (by decide +kernel) (lower_slice_b (T:=gsh_95_32) [(0xcccccccc00000000cccccccc,0,2),(0xff00ff0000000000ff00ff00,0,8)] (by decide +kernel) lowS_85)
def dzo_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0e0f0f0e0a0
def gsh_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0e0f0f0e0a
theorem lowS_zo_123_4_42:Lower true dzo_123_4 roots_123 gzo_123_4 7:=lower_iso_b (d1:=dom_123) (r1:=roots_123) (T1:=gsh_123_4) [(dom_123,4)] (by decide +kernel) (lower_slice_b (T:=gsh_123_4) [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0,1),(0xf0f00000f0f00000f0f00000f0f0000,0,16),(0xf0f0f0f0f0f0f0f0000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_122_4:=0x50505050505050505050505050505050
def gzo_122_4:=0x50505050505050505050504050504000
def gsh_122_4:=0x5050505050505050505050405050400
theorem lowS_zo_122_4_42:Lower true dzo_122_4 roots_122 gzo_122_4 6:=lower_iso_b (d1:=dom_122) (r1:=roots_122) (T1:=gsh_122_4) [(dom_122,4)] (by decide +kernel) (lower_slice_b (T:=gsh_122_4) [(0x5050000050500000505000005050000,0,16),(0x5050505050505050000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000ffff0000fffe0000fefa0000
def gsh_111_16:=0xffff0000ffff0000fffe0000fefa
theorem lowS_zo_111_16_42:Lower true dzo_111_16 roots_111 gzo_111_16 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xaaaa0000aaaa0000aaaa0000aaaa,0,1),(0xf0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff0000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_126_1:=0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def gzo_126_1:=0xaaaaaaaaaaaaaaaaaaaaaaa8aaaaa8a0
def gsh_126_1:=0x55555555555555555555555455555450
theorem lowS_zo_126_1_42:Lower true dzo_126_1 roots_126 gzo_126_1 7:=lower_iso_b (d1:=dom_126) (r1:=roots_126) (T1:=gsh_126_1) [(dom_126,1)] (by decide +kernel) (lower_slice_b (T:=gsh_126_1) [(0x50505050505050505050505050505050,0,4),(0x55550000555500005555000055550000,0,16),(0x55555555555555550000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_122_1:=0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def gzo_122_1:=0xa0a0a0a0a0a0a0a0a0a0a080a0a0800
def gsh_122_1:=0x5050505050505050505050405050400
theorem lowS_zo_122_1_42:Lower true dzo_122_1 roots_122 gzo_122_1 6:=lower_iso_b (d1:=dom_122) (r1:=roots_122) (T1:=gsh_122_1) [(dom_122,1)] (by decide +kernel) (lower_slice_b (T:=gsh_122_1) [(0x5050000050500000505000005050000,0,16),(0x5050505050505050000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_110_16:=0x55550000555500005555000055550000
def gzo_110_16:=0x55550000555500005554000054500000
def gsh_110_16:=0x5555000055550000555400005450
theorem lowS_zo_110_16_42:Lower true dzo_110_16 roots_110 gzo_110_16 6:=lower_iso_b (d1:=dom_110) (r1:=roots_110) (T1:=gsh_110_16) [(dom_110,16)] (by decide +kernel) (lower_slice_b (T:=gsh_110_16) [(0x5050000050500000505000005050,0,4),(0x5555000055550000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_107_16:=0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16:=0xf0f00000f0f00000f0e00000e0a0000
def gsh_107_16:=0xf0f00000f0f00000f0e00000e0a
theorem lowS_zo_107_16_42:Lower true dzo_107_16 roots_107 gzo_107_16 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_16) [(dom_107,16)] (by decide +kernel) (lower_slice_b (T:=gsh_107_16) [(0xa0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_63_64:=0xffffffffffffffff0000000000000000
def gzo_63_64:=0xfffffffefffffefa0000000000000000
def gsh_63_64:=0xfffffffefffffefa
theorem lowS_zo_63_64_42:Lower true dzo_63_64 roots_63 gzo_63_64 7:=lower_iso_b (d1:=dom_63) (r1:=roots_63) (T1:=gsh_63_64) [(dom_63,64)] (by decide +kernel) (lower_slice_b (T:=gsh_63_64) [(0xaaaaaaaaaaaaaaaa,0,1),(0xf0f0f0f0f0f0f0f0,0,4),(0xffff0000ffff0000,0,16)] (by decide +kernel) lowS_42)
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0f00000f0e00000e0a0
def gsh_107_4:=0xf0f00000f0f00000f0e00000e0a
theorem lowS_zo_107_4_42:Lower true dzo_107_4 roots_107 gzo_107_4 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xa0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_47_64:=0xffff0000ffff0000000000000000
def gzo_47_64:=0xfffe0000fefa0000000000000000
def gsh_47_64:=0xfffe0000fefa
theorem lowS_zo_47_64_42:Lower true dzo_47_64 roots_47 gzo_47_64 6:=lower_iso_b (d1:=dom_47) (r1:=roots_47) (T1:=gsh_47_64) [(dom_47,64)] (by decide +kernel) (lower_slice_b (T:=gsh_47_64) [(0xaaaa0000aaaa,0,1),(0xf0f00000f0f0,0,4)] (by decide +kernel) lowS_42)
def dzo_59_64:=0xf0f0f0f0f0f0f0f0000000000000000
def gzo_59_64:=0xf0f0f0e0f0f0e0a0000000000000000
def gsh_59_64:=0xf0f0f0e0f0f0e0a
theorem lowS_zo_59_64_42:Lower true dzo_59_64 roots_59 gzo_59_64 6:=lower_iso_b (d1:=dom_59) (r1:=roots_59) (T1:=gsh_59_64) [(dom_59,64)] (by decide +kernel) (lower_slice_b (T:=gsh_59_64) [(0xa0a0a0a0a0a0a0a,0,1),(0xf0f00000f0f0000,0,16)] (by decide +kernel) lowS_42)
def dzo_46_1:=0xaaaa0000aaaa
def gzo_46_1:=0xaaa80000a8a0
def gsh_46_1:=0x555400005450
theorem lowS_zo_46_1_42:Lower true dzo_46_1 roots_46 gzo_46_1 5:=lower_iso_b (d1:=dom_46) (r1:=roots_46) (T1:=gsh_46_1) [(dom_46,1)] (by decide +kernel) (lower_slice_b (T:=gsh_46_1) [(0x505000005050,0,4)] (by decide +kernel) lowS_42)
def dzo_106_1:=0xa0a00000a0a00000a0a00000a0a
def gzo_106_1:=0xa0a00000a0a00000a0800000800
def gsh_106_1:=0x505000005050000050400000400
theorem lowS_zo_106_1_42:Lower true dzo_106_1 roots_106 gzo_106_1 5:=lower_iso_b (d1:=dom_106) (r1:=roots_106) (T1:=gsh_106_1) [(dom_106,1)] (by decide +kernel) (lower_slice_b (T:=gsh_106_1) [(0x505000005050000000000000000,0,64)] (by decide +kernel) lowS_42)
namespace S_127
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,65),(2,10),(2,34),(3,7),(3,11),(3,19),(3,35),(3,67),(4,5),(4,20),(4,68),(6,7),(6,14),(6,22),(6,38),(6,70),(8,10),(8,40),(9,11),(9,13),(9,25),(9,41),(9,73),(12,13),(12,14),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(18,19),(18,22),(18,26),(18,50),(18,82),(24,25),(24,26),(24,28),(24,56),(24,88),(32,34),(32,40),(33,35),(33,37),(33,41),(33,49),(33,97),(36,37),(36,38),(36,44),(36,52),(36,100),(48,49),(48,50),(48,52),(48,56),(48,112),(64,65),(64,68),(64,80),(66,67),(66,70),(66,74),(66,82),(66,98),(72,73),(72,74),(72,76),(72,88),(72,104),(96,97),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|8=>6
|9=>9
|10=>3
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x880ae8327b6f82f3f2d03ab5e2a7ce
|9,0=>0xdcbcfa399360eb95766a52ef83e88c18d210b65c0b27d
|10,0=>0x5254f3b65b2654f
|11,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfffffffffffffffffffff0f0fffff0f0aaaaaaaaaaaaaaaaaaaaa0a0aaaaa0a0ffffaaaaffffaaaaffffaaaaffffaaaafffff0f0fffff0f0fffff0f0fffff0f0ffffffffffffffffffff0000ffff0000fffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffffafafafafafafafaffff0000ffff0000ffff0000ffff0000ffffffffffffffffaaaaaaaaaaaaaaaaffffffff00000000ffffffff00000000ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000ffff0000ffff0000fafa0000fafaffffffffffffffff0000000000000000
|0,1=>0xfffffafafffffafafffffafafffffafa555550505555505055555050555550500f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0000ffff0000ffff0000f0f00000f0f055555555555555555555505055555050ffffffffffffffffffffaaaaffffaaaaf0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0
|_,_=>0
def sP:Nat→Nat
|0=>0x414833880641483100cf41483100d641483100cd59483100cd41483380cc41543100c82a883388c829062a80c829062a00c829062980c8290720190580c40320a41b8066aca419ccc59543118a418820
|1=>0x320a4188065a0a418806
|_=>0
def sO:Nat→Nat→Nat
|8,0=>0x2371c71570e7077007
|9,0=>0x6a86285a85284a84283a83282a8
|10,0=>0x818798727
|11,0=>0x897
|_,_=>0
def wAt:=mkWire dB 23 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x40110159140123512140940140910141120120110160b41121e10142a20178b5914018900351217885914014094011014014112014a321d101
|_=>0
def oO:Nat→Nat→Nat
|8,0=>0x3ccc324c630cc03
|9,0=>0x222809e2709a26096250922
|10,0=>0x25190400
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0x90023ff60013ff18067ff07017ff0286fff01917ff00633ff00433ff001afff00073ff00063ff0001fff0000fff00003ff00001ff000007d0000000
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>0x6211ca3
|9,0=>0xb4a8c4621cd
|10,0=>0x3e01
|11,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 28 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_126 9 roots_126 ops++addP pm 1 dom_63 9 roots_63 ops++addP pm 2 dom_111 9 roots_111 ops++addP pm 3 dom_125 9 roots_125 ops++addP pm 4 dom_123 9 roots_123 ops++addP pm 5 dom_119 9 roots_119 ops++addP pm 6 dom_95 9 roots_95 ops++addP pm 7 dzo_125_2 9 roots_125 ops++addP pm 8 dzo_119_8 9 roots_119 ops++addP pm 9 dzo_95_32 9 roots_95 ops++addP pm 10 dzo_123_4 7 roots_123 ops++addP pm 11 dzo_122_4 6 roots_122 ops++addP pm 12 dzo_111_16 7 roots_111 ops++addP pm 13 dzo_126_1 7 roots_126 ops++addP pm 14 dzo_122_1 6 roots_122 ops++addP pm 15 dom_107 6 roots_107 ops++addP pm 16 dzo_110_16 6 roots_110 ops++addP pm 17 dzo_107_16 6 roots_107 ops++addP pm 18 dzo_62_1 6 roots_62 ops++addP pm 19 dzo_63_64 7 roots_63 ops++addP pm 20 dzo_107_4 6 roots_107 ops++addP pm 21 dzo_47_64 6 roots_47 ops++addP pm 22 dom_59 6 roots_59 ops++addP pm 23 dzo_59_64 6 roots_59 ops++addP pm 24 dom_62 6 roots_62 ops++addP pm 25 dzo_46_1 5 roots_46 ops++addP pm 26 dom_47 6 roots_47 ops++addP pm 27 dzo_106_1 5 roots_106 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_125_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_119_8_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_95_32_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_123_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_122_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_111_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_126_1_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_122_1_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_110_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_107_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_62_1_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_63_64_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_107_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_47_64_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_59_64_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_46_1_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_106_1_42 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_126 9 s (0,roots_126.map (·&&&dom_126)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_126 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 6 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 9 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 3 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 3 0 = true)
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
  · simp [NN] at hi
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
namespace S_191
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,129),(2,10),(2,34),(2,130),(3,7),(3,11),(3,19),(3,35),(3,131),(4,5),(4,20),(4,132),(6,7),(6,14),(6,22),(6,38),(6,134),(8,10),(8,40),(8,136),(9,11),(9,13),(9,25),(9,41),(9,137),(12,13),(12,14),(12,28),(12,44),(12,140),(16,17),(16,20),(18,19),(18,22),(18,26),(18,50),(18,146),(24,25),(24,26),(24,28),(24,56),(24,152),(32,34),(32,40),(32,160),(33,35),(33,37),(33,41),(33,49),(33,161),(36,37),(36,38),(36,44),(36,52),(36,164),(48,49),(48,50),(48,52),(48,56),(48,176),(128,129),(128,130),(128,132),(128,136),(128,160),(144,145),(144,146),(144,148),(144,152),(144,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffff
def xsM:=roots_191.map (·&&&dom_191)
def gM:=goal_191&&&dom_191
def NN:Nat→Nat
|10=>1
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|10,0=>0x4eb99
|11,0=>0x2bff1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff0000ffff00000000000000000000ffff0000ffff0000ffffffff000000000000000000000000ffffffff00000000ffffffffffffffff0000000000000000ffff0000ffff0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0cccccccccccccccc0000000000000000ccccccccccccccccaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaaffffffffffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x378d11ac688
|_=>0
def sO:Nat→Nat→Nat
|10,0=>7
|11,0=>0x77
|_,_=>0
def wAt:=mkWire dB 8 192 0xffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xe1
|_=>0
def oO:Nat→Nat→Nat
|10,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 5
def pmP:Nat→Nat
|0=>0xfc0
|_=>0
def pmB:Nat→Nat→Nat
|10,0=>1
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_190 10 roots_190 ops++addP pm 1 dom_189 10 roots_189 ops++addP pm 2 dom_187 10 roots_187 ops++addP pm 3 dom_183 10 roots_183 ops++addP pm 4 dom_175 10 roots_175 ops++addP pm 5 dom_159 10 roots_159 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_191 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_159 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_190 10 s (0,roots_190.map (·&&&dom_190)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_191 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_190 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_191==dom_191)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_191 gM v ys):RunD true dom_191 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_191 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_191 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,65),(1,129),(2,10),(2,130),(3,7),(3,11),(3,19),(3,67),(3,131),(4,5),(4,20),(4,68),(4,132),(6,7),(6,14),(6,22),(6,70),(6,134),(8,10),(8,136),(9,11),(9,13),(9,25),(9,73),(9,137),(12,13),(12,14),(12,28),(12,76),(12,140),(16,17),(16,20),(16,80),(18,19),(18,22),(18,26),(18,82),(18,146),(24,25),(24,26),(24,28),(24,88),(24,152),(64,65),(64,68),(64,80),(66,67),(66,70),(66,74),(66,82),(66,194),(72,73),(72,74),(72,76),(72,88),(72,200),(128,129),(128,130),(128,132),(128,136),(144,145),(144,146),(144,148),(144,152),(144,208),(192,193),(192,194),(192,196),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffff
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
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
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
namespace S_251
def pG:List (Nat×Nat):=[(1,17),(1,65),(1,129),(2,10),(2,34),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,10),(8,40),(8,136),(9,11),(9,25),(9,41),(9,73),(9,137),(16,17),(16,80),(18,19),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,56),(24,88),(24,152),(32,34),(32,40),(32,160),(33,35),(33,41),(33,49),(33,97),(33,161),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,80),(66,67),(66,74),(66,82),(66,98),(66,194),(72,73),(72,74),(72,88),(72,104),(72,200),(96,97),(96,98),(96,104),(96,112),(96,224),(128,129),(128,130),(128,136),(128,160),(144,145),(144,146),(144,152),(144,176),(144,208),(192,193),(192,194),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7ffffffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|10=>1
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|10,0=>0x54836
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0aa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1f5888fac688
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
|0=>0x41
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
addP pm 0 dom_249 10 roots_249 ops++addP pm 1 dom_187 10 roots_187 ops++addP pm 2 dom_250 9 roots_250 ops++addP pm 3 dom_123 9 roots_123 ops++addP pm 4 dom_243 10 roots_243 ops++addP pm 5 dom_235 10 roots_235 ops++addP pm 6 dom_219 10 roots_219 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_219 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_249 10 s (0,roots_249.map (·&&&dom_249)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_249 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]]
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
def isoMvS_239:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_239:Lower true dom_239 roots_239 goal_239 12:=lower_iso_b isoMvS_239 (by decide +kernel) lowS_191
def isoMvS_247:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_247:Lower true dom_247 roots_247 goal_247 12:=lower_iso_b isoMvS_247 (by decide +kernel) lowS_223
def isoMvS_253:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_223
def isoMvS_254:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_251
def dzo_253_2:=0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def gzo_253_2:=0xccccccccccccccccccccccccccccccccccccccccccccccc8ccccccccccc8cc80
def gsh_253_2:=0x3333333333333333333333333333333333333333333333323333333333323320
theorem lowS_zo_253_2_85:Lower true dzo_253_2 roots_253 gzo_253_2 10:=lower_iso_b (d1:=dom_253) (r1:=roots_253) (T1:=gsh_253_2) [(dom_253,2)] (by decide +kernel) (lower_slice_b (T:=gsh_253_2) [(0x3300330033003300330033003300330033003300330033003300330033003300,0,8),(0x3333333300000000333333330000000033333333000000003333333300000000,0,32),(0x3333333333333333333333333333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
def dzo_245_2:=0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc
def gzo_245_2:=0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00c800cc00cc00c80080
def gsh_245_2:=0x33003300330033003300330033003300330033003300320033003300320020
theorem lowS_zo_245_2_85:Lower true dzo_245_2 roots_245 gzo_245_2 9:=lower_iso_b (d1:=dom_245) (r1:=roots_245) (T1:=gsh_245_2) [(dom_245,2)] (by decide +kernel) (lower_slice_b (T:=gsh_245_2) [(0x33003300000000003300330000000000330033000000000033003300000000,0,32),(0x33003300330033003300330033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
def dzo_223_32:=0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def gzo_223_32:=0xffffffff00000000ffffffff00000000fffffffe00000000fffeffec00000000
def gsh_223_32:=0xffffffff00000000ffffffff00000000fffffffe00000000fffeffec
theorem lowS_zo_223_32_85:Lower true dzo_223_32 roots_223 gzo_223_32 10:=lower_iso_b (d1:=dom_223) (r1:=roots_223) (T1:=gsh_223_32) [(dom_223,32)] (by decide +kernel) (lower_slice_b (T:=gsh_223_32) [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,0,2),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,0,8),(0xffffffff00000000ffffffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
def dzo_191_64:=0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def gzo_191_64:=0xfffffffffffffffe0000000000000000fffffffefffffefa0000000000000000
def gsh_191_64:=0xfffffffffffffffe0000000000000000fffffffefffffefa
theorem lowS_zo_191_64_170:Lower true dzo_191_64 roots_191 gzo_191_64 10:=lower_iso_b (d1:=dom_191) (r1:=roots_191) (T1:=gsh_191_64) [(dom_191,64)] (by decide +kernel) (lower_slice_b (T:=gsh_191_64) [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,0,1),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,0,4),(0xffff0000ffff00000000000000000000ffff0000ffff0000,0,16)] (by decide +kernel) lowS_170)
def dzo_221_2:=0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc
def gzo_221_2:=0xcccccccc00000000cccccccc00000000ccccccc800000000ccc8cc80
def gsh_221_2:=0x33333333000000003333333300000000333333320000000033323320
theorem lowS_zo_221_2_85:Lower true dzo_221_2 roots_221 gzo_221_2 9:=lower_iso_b (d1:=dom_221) (r1:=roots_221) (T1:=gsh_221_2) [(dom_221,2)] (by decide +kernel) (lower_slice_b (T:=gsh_221_2) [(0x33003300000000003300330000000000330033000000000033003300,0,8),(0x33333333000000003333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
def dzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def gzo_239_16:=0xffff0000ffff0000ffff0000fffe0000ffff0000ffff0000fffe0000fefa0000
def gsh_239_16:=0xffff0000ffff0000ffff0000fffe0000ffff0000ffff0000fffe0000fefa
theorem lowS_zo_239_16_170:Lower true dzo_239_16 roots_239 gzo_239_16 10:=lower_iso_b (d1:=dom_239) (r1:=roots_239) (T1:=gsh_239_16) [(dom_239,16)] (by decide +kernel) (lower_slice_b (T:=gsh_239_16) [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,0,1),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,0,64)] (by decide +kernel) lowS_170)
def dzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def gzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fe00ff00ff00fe00ec00
def gsh_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fe00ff00ff00fe00ec
theorem lowS_zo_247_8_85:Lower true dzo_247_8 roots_247 gzo_247_8 10:=lower_iso_b (d1:=dom_247) (r1:=roots_247) (T1:=gsh_247_8) [(dom_247,8)] (by decide +kernel) (lower_slice_b (T:=gsh_247_8) [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,0,2),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000,0,32),(0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
def dzo_245_8:=0x3300330033003300330033003300330033003300330033003300330033003300
def gzo_245_8:=0x3300330033003300330033003300330033003300330032003300330032002000
def gsh_245_8:=0x33003300330033003300330033003300330033003300320033003300320020
theorem lowS_zo_245_8_85:Lower true dzo_245_8 roots_245 gzo_245_8 9:=lower_iso_b (d1:=dom_245) (r1:=roots_245) (T1:=gsh_245_8) [(dom_245,8)] (by decide +kernel) (lower_slice_b (T:=gsh_245_8) [(0x33003300000000003300330000000000330033000000000033003300000000,0,32),(0x33003300330033003300330033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
def dzo_175_16:=0xffff0000ffff00000000000000000000ffff0000ffff0000
def gzo_175_16:=0xffff0000fffe00000000000000000000fffe0000fefa0000
def gsh_175_16:=0xffff0000fffe00000000000000000000fffe0000fefa
theorem lowS_zo_175_16_170:Lower true dzo_175_16 roots_175 gzo_175_16 9:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_16) [(dom_175,16)] (by decide +kernel) (lower_slice_b (T:=gsh_175_16) [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0,0,4)] (by decide +kernel) lowS_170)
def dzo_175_64:=0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000
def gzo_175_64:=0xffff0000fffe00000000000000000000fffe0000fefa0000000000000000
def gsh_175_64:=0xffff0000fffe00000000000000000000fffe0000fefa
theorem lowS_zo_175_64_170:Lower true dzo_175_64 roots_175 gzo_175_64 9:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_64) [(dom_175,64)] (by decide +kernel) (lower_slice_b (T:=gsh_175_64) [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0,0,4)] (by decide +kernel) lowS_170)
def dzo_221_32:=0x3333333300000000333333330000000033333333000000003333333300000000
def gzo_221_32:=0x3333333300000000333333330000000033333332000000003332332000000000
def gsh_221_32:=0x33333333000000003333333300000000333333320000000033323320
theorem lowS_zo_221_32_85:Lower true dzo_221_32 roots_221 gzo_221_32 9:=lower_iso_b (d1:=dom_221) (r1:=roots_221) (T1:=gsh_221_32) [(dom_221,32)] (by decide +kernel) (lower_slice_b (T:=gsh_221_32) [(0x33003300000000003300330000000000330033000000000033003300,0,8),(0x33333333000000003333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
def dzo_238_16:=0x5555000055550000555500005555000055550000555500005555000055550000
def gzo_238_16:=0x5555000055550000555500005554000055550000555500005554000054500000
def gsh_238_16:=0x555500005555000055550000555400005555000055550000555400005450
theorem lowS_zo_238_16_170:Lower true dzo_238_16 roots_238 gzo_238_16 9:=lower_iso_b (d1:=dom_238) (r1:=roots_238) (T1:=gsh_238_16) [(dom_238,16)] (by decide +kernel) (lower_slice_b (T:=gsh_238_16) [(0x505000005050000050500000505000005050000050500000505000005050,0,4),(0x555500005555000000000000000000005555000055550000000000000000,0,64)] (by decide +kernel) lowS_170)
def dzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
def gzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00ec00000000
def gsh_215_32:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00ec
theorem lowS_zo_215_32_85:Lower true dzo_215_32 roots_215 gzo_215_32 9:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_32) [(dom_215,32)] (by decide +kernel) (lower_slice_b (T:=gsh_215_32) [(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,0,2),(0xff00ff0000000000ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
def dzo_186_64:=0x505050505050505000000000000000005050505050505050000000000000000
def gzo_186_64:=0x505050505050504000000000000000005050504050504000000000000000000
def gsh_186_64:=0x50505050505050400000000000000000505050405050400
theorem lowS_zo_186_64_170:Lower true dzo_186_64 roots_186 gzo_186_64 8:=lower_iso_b (d1:=dom_186) (r1:=roots_186) (T1:=gsh_186_64) [(dom_186,64)] (by decide +kernel) (lower_slice_b (T:=gsh_186_64) [(0x50500000505000000000000000000000505000005050000,0,16)] (by decide +kernel) lowS_170)
def dzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00
def gzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00ec00
def gsh_215_8:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00ec
theorem lowS_zo_215_8_85:Lower true dzo_215_8 roots_215 gzo_215_8 9:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_8) [(dom_215,8)] (by decide +kernel) (lower_slice_b (T:=gsh_215_8) [(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,0,2),(0xff00ff0000000000ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
def dzo_234_16:=0x505000005050000050500000505000005050000050500000505000005050000
def gzo_234_16:=0x505000005050000050500000504000005050000050500000504000004000000
def gsh_234_16:=0x50500000505000005050000050400000505000005050000050400000400
theorem lowS_zo_234_16_170:Lower true dzo_234_16 roots_234 gzo_234_16 8:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_16) [(dom_234,16)] (by decide +kernel) (lower_slice_b (T:=gsh_234_16) [(0x50500000505000000000000000000000505000005050000000000000000,0,64)] (by decide +kernel) lowS_170)
def dzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def gzo_235_16:=0xf0f00000f0f00000f0f00000f0e00000f0f00000f0f00000f0e00000e0a0000
def gsh_235_16:=0xf0f00000f0f00000f0f00000f0e00000f0f00000f0f00000f0e00000e0a
theorem lowS_zo_235_16_170:Lower true dzo_235_16 roots_235 gzo_235_16 9:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_16) [(dom_235,16)] (by decide +kernel) (lower_slice_b (T:=gsh_235_16) [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_170)
def dzo_174_16:=0x555500005555000000000000000000005555000055550000
def gzo_174_16:=0x555500005554000000000000000000005554000054500000
def gsh_174_16:=0x55550000555400000000000000000000555400005450
theorem lowS_zo_174_16_170:Lower true dzo_174_16 roots_174 gzo_174_16 8:=lower_iso_b (d1:=dom_174) (r1:=roots_174) (T1:=gsh_174_16) [(dom_174,16)] (by decide +kernel) (lower_slice_b (T:=gsh_174_16) [(0x50500000505000000000000000000000505000005050,0,4)] (by decide +kernel) lowS_170)
def dzo_190_64:=0x5555555555555555000000000000000055555555555555550000000000000000
def gzo_190_64:=0x5555555555555554000000000000000055555554555554500000000000000000
def gsh_190_64:=0x555555555555555400000000000000005555555455555450
theorem lowS_zo_190_64_170:Lower true dzo_190_64 roots_190 gzo_190_64 9:=lower_iso_b (d1:=dom_190) (r1:=roots_190) (T1:=gsh_190_64) [(dom_190,64)] (by decide +kernel) (lower_slice_b (T:=gsh_190_64) [(0x505050505050505000000000000000005050505050505050,0,4),(0x555500005555000000000000000000005555000055550000,0,16)] (by decide +kernel) lowS_170)
def dzo_187_64:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000
def gzo_187_64:=0xf0f0f0f0f0f0f0e00000000000000000f0f0f0e0f0f0e0a0000000000000000
def gsh_187_64:=0xf0f0f0f0f0f0f0e00000000000000000f0f0f0e0f0f0e0a
theorem lowS_zo_187_64_170:Lower true dzo_187_64 roots_187 gzo_187_64 9:=lower_iso_b (d1:=dom_187) (r1:=roots_187) (T1:=gsh_187_64) [(dom_187,64)] (by decide +kernel) (lower_slice_b (T:=gsh_187_64) [(0xa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0000,0,16)] (by decide +kernel) lowS_170)
def dzo_117_2:=0xcc00cc00cc00cc00cc00cc00cc00cc
def gzo_117_2:=0xcc00cc00cc00c800cc00cc00c80080
def gsh_117_2:=0x330033003300320033003300320020
theorem lowS_zo_117_2_85:Lower true dzo_117_2 roots_117 gzo_117_2 8:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_2) [(dom_117,2)] (by decide +kernel) (lower_slice_b (T:=gsh_117_2) [(0x330033000000000033003300000000,0,32)] (by decide +kernel) lowS_85)
def dzo_93_2:=0xcccccccc00000000cccccccc
def gzo_93_2:=0xccccccc800000000ccc8cc80
def gsh_93_2:=0x333333320000000033323320
theorem lowS_zo_93_2_85:Lower true dzo_93_2 roots_93 gzo_93_2 8:=lower_iso_b (d1:=dom_93) (r1:=roots_93) (T1:=gsh_93_2) [(dom_93,2)] (by decide +kernel) (lower_slice_b (T:=gsh_93_2) [(0x330033000000000033003300,0,8)] (by decide +kernel) lowS_85)
def dzo_87_8:=0xff00ff0000000000ff00ff00
def gzo_87_8:=0xff00fe0000000000fe00ec00
def gsh_87_8:=0xff00fe0000000000fe00ec
theorem lowS_zo_87_8_85:Lower true dzo_87_8 roots_87 gzo_87_8 8:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_8) [(dom_87,8)] (by decide +kernel) (lower_slice_b (T:=gsh_87_8) [(0xcc00cc0000000000cc00cc,0,2)] (by decide +kernel) lowS_85)
def dzo_87_32:=0xff00ff0000000000ff00ff00000000
def gzo_87_32:=0xff00fe0000000000fe00ec00000000
def gsh_87_32:=0xff00fe0000000000fe00ec
theorem lowS_zo_87_32_85:Lower true dzo_87_32 roots_87 gzo_87_32 8:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_32) [(dom_87,32)] (by decide +kernel) (lower_slice_b (T:=gsh_87_32) [(0xcc00cc0000000000cc00cc,0,2)] (by decide +kernel) lowS_85)
def dzo_254_1:=0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def gzo_254_1:=0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8aaaaa8a0
def gsh_254_1:=0x5555555555555555555555555555555555555555555555555555555455555450
theorem lowS_zo_254_1_42:Lower true dzo_254_1 roots_254 gzo_254_1 8:=lower_iso_b (d1:=dom_254) (r1:=roots_254) (T1:=gsh_254_1) [(dom_254,1)] (by decide +kernel) (lower_slice_b (T:=gsh_254_1) [(0x5050505050505050505050505050505050505050505050505050505050505050,0,4),(0x5555000055550000555500005555000055550000555500005555000055550000,0,16),(0x5555555555555555000000000000000055555555555555550000000000000000,0,64),(0x5555555555555555555555555555555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0e0a0
def gsh_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0e0a
theorem lowS_zo_251_4_42:Lower true dzo_251_4 roots_251 gzo_251_4 8:=lower_iso_b (d1:=dom_251) (r1:=roots_251) (T1:=gsh_251_4) [(dom_251,4)] (by decide +kernel) (lower_slice_b (T:=gsh_251_4) [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0,1),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,0,16),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,0,64),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_117_8:=0x33003300330033003300330033003300
def gzo_117_8:=0x33003300330032003300330032002000
def gsh_117_8:=0x330033003300320033003300320020
theorem lowS_zo_117_8_85:Lower true dzo_117_8 roots_117 gzo_117_8 8:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_8) [(dom_117,8)] (by decide +kernel) (lower_slice_b (T:=gsh_117_8) [(0x330033000000000033003300000000,0,32)] (by decide +kernel) lowS_85)
def dzo_93_32:=0x33333333000000003333333300000000
def gzo_93_32:=0x33333332000000003332332000000000
def gsh_93_32:=0x333333320000000033323320
theorem lowS_zo_93_32_85:Lower true dzo_93_32 roots_93 gzo_93_32 8:=lower_iso_b (d1:=dom_93) (r1:=roots_93) (T1:=gsh_93_32) [(dom_93,32)] (by decide +kernel) (lower_slice_b (T:=gsh_93_32) [(0x330033000000000033003300,0,8)] (by decide +kernel) lowS_85)
def dzo_238_1:=0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa
def gzo_238_1:=0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaa80000a8a0
def gsh_238_1:=0x555500005555000055550000555500005555000055550000555400005450
theorem lowS_zo_238_1_42:Lower true dzo_238_1 roots_238 gzo_238_1 7:=lower_iso_b (d1:=dom_238) (r1:=roots_238) (T1:=gsh_238_1) [(dom_238,1)] (by decide +kernel) (lower_slice_b (T:=gsh_238_1) [(0x505000005050000050500000505000005050000050500000505000005050,0,4),(0x555500005555000000000000000000005555000055550000000000000000,0,64),(0x555500005555000055550000555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_213_8:=0x33003300000000003300330000000000330033000000000033003300
def gzo_213_8:=0x33003300000000003300330000000000330032000000000032002000
def gsh_213_8:=0x330033000000000033003300000000003300320000000000320020
theorem lowS_zo_213_8_85:Lower true dzo_213_8 roots_213 gzo_213_8 8:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_8) [(dom_213,8)] (by decide +kernel) (lower_slice_b (T:=gsh_213_8) [(0x330033000000000033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
def dzo_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0
def gzo_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000e0a0
def gsh_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000e0a
theorem lowS_zo_235_4_42:Lower true dzo_235_4 roots_235 gzo_235_4 7:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_4) [(dom_235,4)] (by decide +kernel) (lower_slice_b (T:=gsh_235_4) [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000,0,64),(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_190_1:=0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa
def gzo_190_1:=0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaa8aaaaa8a0
def gsh_190_1:=0x555555555555555500000000000000005555555455555450
theorem lowS_zo_190_1_42:Lower true dzo_190_1 roots_190 gzo_190_1 7:=lower_iso_b (d1:=dom_190) (r1:=roots_190) (T1:=gsh_190_1) [(dom_190,1)] (by decide +kernel) (lower_slice_b (T:=gsh_190_1) [(0x505050505050505000000000000000005050505050505050,0,4),(0x555500005555000000000000000000005555000055550000,0,16),(0x555555555555555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_171_64:=0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000
def gzo_171_64:=0xf0f00000f0e000000000000000000000f0e00000e0a0000000000000000
def gsh_171_64:=0xf0f00000f0e000000000000000000000f0e00000e0a
theorem lowS_zo_171_64_170:Lower true dzo_171_64 roots_171 gzo_171_64 8:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_64) [(dom_171,64)] (by decide +kernel) (lower_slice_b (T:=gsh_171_64) [(0xa0a00000a0a000000000000000000000a0a00000a0a,0,1)] (by decide +kernel) lowS_170)
def dzo_187_4:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0
def gzo_187_4:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0e0f0f0e0a0
def gsh_187_4:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0e0f0f0e0a
theorem lowS_zo_187_4_42:Lower true dzo_187_4 roots_187 gzo_187_4 7:=lower_iso_b (d1:=dom_187) (r1:=roots_187) (T1:=gsh_187_4) [(dom_187,4)] (by decide +kernel) (lower_slice_b (T:=gsh_187_4) [(0xa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0000,0,16),(0xf0f0f0f0f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_174_64:=0x555500005555000000000000000000005555000055550000000000000000
def gzo_174_64:=0x555500005554000000000000000000005554000054500000000000000000
def gsh_174_64:=0x55550000555400000000000000000000555400005450
theorem lowS_zo_174_64_170:Lower true dzo_174_64 roots_174 gzo_174_64 8:=lower_iso_b (d1:=dom_174) (r1:=roots_174) (T1:=gsh_174_64) [(dom_174,64)] (by decide +kernel) (lower_slice_b (T:=gsh_174_64) [(0x50500000505000000000000000000000505000005050,0,4)] (by decide +kernel) lowS_170)
def dzo_186_4:=0x505050505050505000000000000000005050505050505050
def gzo_186_4:=0x505050505050505000000000000000005050504050504000
def gsh_186_4:=0x50505050505050500000000000000000505050405050400
theorem lowS_zo_186_4_42:Lower true dzo_186_4 roots_186 gzo_186_4 6:=lower_iso_b (d1:=dom_186) (r1:=roots_186) (T1:=gsh_186_4) [(dom_186,4)] (by decide +kernel) (lower_slice_b (T:=gsh_186_4) [(0x50500000505000000000000000000000505000005050000,0,16),(0x50505050505050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_171_4:=0xf0f00000f0f000000000000000000000f0f00000f0f0
def gzo_171_4:=0xf0f00000f0f000000000000000000000f0e00000e0a0
def gsh_171_4:=0xf0f00000f0f000000000000000000000f0e00000e0a
theorem lowS_zo_171_4_42:Lower true dzo_171_4 roots_171 gzo_171_4 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_4) [(dom_171,4)] (by decide +kernel) (lower_slice_b (T:=gsh_171_4) [(0xa0a00000a0a000000000000000000000a0a00000a0a,0,1),(0xf0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_234_4:=0x505000005050000050500000505000005050000050500000505000005050
def gzo_234_4:=0x505000005050000050500000505000005050000050500000504000004000
def gsh_234_4:=0x50500000505000005050000050500000505000005050000050400000400
theorem lowS_zo_234_4_42:Lower true dzo_234_4 roots_234 gzo_234_4 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_4) [(dom_234,4)] (by decide +kernel) (lower_slice_b (T:=gsh_234_4) [(0x50500000505000000000000000000000505000005050000000000000000,0,64),(0x50500000505000005050000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_234_1:=0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a
def gzo_234_1:=0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0800000800
def gsh_234_1:=0x50500000505000005050000050500000505000005050000050400000400
theorem lowS_zo_234_1_42:Lower true dzo_234_1 roots_234 gzo_234_1 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_1) [(dom_234,1)] (by decide +kernel) (lower_slice_b (T:=gsh_234_1) [(0x50500000505000000000000000000000505000005050000000000000000,0,64),(0x50500000505000005050000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_174_1:=0xaaaa0000aaaa00000000000000000000aaaa0000aaaa
def gzo_174_1:=0xaaaa0000aaaa00000000000000000000aaa80000a8a0
def gsh_174_1:=0x55550000555500000000000000000000555400005450
theorem lowS_zo_174_1_42:Lower true dzo_174_1 roots_174 gzo_174_1 6:=lower_iso_b (d1:=dom_174) (r1:=roots_174) (T1:=gsh_174_1) [(dom_174,1)] (by decide +kernel) (lower_slice_b (T:=gsh_174_1) [(0x50500000505000000000000000000000505000005050,0,4),(0x55550000555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_213_32:=0x33003300000000003300330000000000330033000000000033003300000000
def gzo_213_32:=0x33003300000000003300330000000000330032000000000032002000000000
def gsh_213_32:=0x330033000000000033003300000000003300320000000000320020
theorem lowS_zo_213_32_85:Lower true dzo_213_32 roots_213 gzo_213_32 8:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_32) [(dom_213,32)] (by decide +kernel) (lower_slice_b (T:=gsh_213_32) [(0x330033000000000033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
namespace S_255
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,65),(1,129),(2,10),(2,34),(2,130),(3,7),(3,11),(3,19),(3,35),(3,67),(3,131),(4,5),(4,20),(4,68),(4,132),(6,7),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,136),(9,11),(9,13),(9,25),(9,41),(9,73),(9,137),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(18,19),(18,22),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,40),(32,160),(33,35),(33,37),(33,41),(33,49),(33,97),(33,161),(36,37),(36,38),(36,44),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,80),(66,67),(66,70),(66,74),(66,82),(66,98),(66,194),(72,73),(72,74),(72,76),(72,88),(72,104),(72,200),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,130),(128,132),(128,136),(128,160),(144,145),(144,146),(144,148),(144,152),(144,176),(144,208),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|7=>1
|8=>22
|9=>101
|10=>176
|11=>249
|12=>108
|13=>13
|14=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x1eb
|8,0=>0x85bd16b9aa69d646905168dfc6307e531814ee2a4c27c446393f61f38f5a340152d85e28c0c289362783f21f0216b290c08c091490253b
|9,0=>0xcd15bb2f34b038684412701966ea226a1eb6763d65f47618bf6080f5d9d259a8352dfd4d33f4940a486ed448a4447ae40b7d408953fdc23dfcf3dde33c4343b84c3aea738dc938bd63708d368663660736028346623462832704323d52fb562cc1a2bb6d2b7d42b6cb2b4af2a9c52a1692902d2849d2835b27d242744d26c822526022545202371fc831dbae1b6211b5e51a4e51a3a11a2181814c17aa816ea415c9d15855148db13bea1225011faa11e541113b10c721009f0ff420ef980ee060dbcb0d89f0d3940d3580c9130c2580c1210bf8b0a76c093290828e06c140664e05a5c056790532c02eae01fc201bd801830015570125c0102e00bf5
|10,0=>0x4449443ea2430e543056413e540e903fe0f3fbbb3f8703e1cf3cf2f3ce6f3bdf33ac75398a13975038f50389e8385c737ada3718736a45355b532e3932a49328b3327c2325e831b24309d7307642fa4d2d01e2cd7c2be382b5a92ab3a29cf028fe028f6328efa28c4027d4426ee426e4626cde26883262922416f23b6822e6521eb421d1c21429212332101820d3d20c261eea21db641d8c01d4191d2fd1cef41c9e31c9931c3ef1b5801ad531ad341a9b719a771656f16441161a31591915764145631327a12d6c11e7111e5e11ad0110130fea10f9bd0f4470e6e70e65c0e4010d7d90d2f30cf4b0cc780cbdf0caa70c66e0c50b0c3bf0c0e00bb990b7300b6e60b5fe0b0300ab490aa2509bcd097fb08e9c08a1508774086f1086c207b6a075a80748e06aba0694f05c7d048a8042a401bb5019ad01854017110087100803
|10,1=>0xa980ea7bce9d61694a9f9437192a1e90fe98fc778cc8e8be2e8b04e7a878784f977cca75e9e7517e6fe416d2db68f6965bc36549f5ffce5ebd95dc105d23f5ce63593855686156522555fb54e27548e25429854085529dd4fc624f9aa4f4334ea254e0664c45c4c2d04954c47e3c477ca46f2e46b9b4600b
|11,0=>0x2d98a2d94c2cad02c9132c47b2be032b3c12adcb2a6792a3b129b76295c929208287b0283112818f27cad27a832795d275cb2700f2700a269922599625954256042530e243d323ff823e14235f7233f92283d224eb221792207b21b562155721422205302035b1f72a1edd31ed741e7fd1e4781de661db781d1341d08b1ceec1c65f1c2261bdc01bbae1b46a1abb51a06619eea19c2f19bbe193b51899318675177c616d1616b7b166151618d15b861575b146c913e26138941336413251130e211d9e11c8d11881114a310e900f4370f3cc0e51e0e4930d5680cfdd0caeb0c5520bde00bc570b73a0b5f90b4320ad7c0ac690a9a20a456093fa0933308b2a0888807e4107ddc07a090749206bf10630305b900545c04f1604e8404dbe043b403d36039e802fef02bc00249301de601c220190c010a900e1900dde00c3c009d6
|11,1=>0xef158db93dd9fa8d2f8ccc434ca24eb5f9ab0027ad479ab889ab161a804fa640fa11c497cea969bd91ce49125f910dd909b58f86b8debe89b98844d58416b83cf4817c0810237fa547dc267d5287ca4b770ce76ab676a3a74dfa74a5e73db46d9576d6e56d2896b8816a61d67ad266be265f1b652c964ea4642f96428261f18607f9600c85fc4a5f3ab5beb85b3965aead59f2458830584c957942575bb56e7c54680537725340852ffa524a54fa574f28e4ec564eb9c4dda64dc744dac14d09f4ceb34c9974c4454c26f4c1664b02a49b1d495964720c471b944fa944f654482b4444d444044351e425694239d4220a41c80413563ff7a3f0723e64b3e63b3dcfc3d4613d1fa3ce8e3b42c38f5037fda37fb237c4836fb636d5e35e7a32ec1326f83209c31ee1306a42da252d9f0
|12,0=>0xe1038c688cc366db6a9ca18ec9aa788f6d38cd6a88f218714c8284e821467eaef78ccd729a9717036f4956b54d62b1461bbb5e4dc5e3015d93e5997d5792855e545474e5444553fac5393f53615519d550c194fea94b6514a57949fad469544663f4443741f7140da83ff753fc543d62f3c3f43bca23ab613978538a5535c5935a2c356ba33e6632b70326a8318a6314943072b306592d17029e1a2799326d2525a23253c624d1d2095b1ff311fb471eb911e3c01d7021d2801b4a91b3b81a8bb19c4c1942c192ed1842617aaa17147163921570e1454613f8e13d70135341308811d8f1179511713109ea0f9d50e79e0d48409ad3089aa0873b0273e022b501c3201be301830017a20122e00894
|13,0=>0xec24bd709b9736a93ab07ec636dd274766c42c443ff2c360431ce4e12dcb11ebd
|14,0=>0x4766c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3333333333333333333333333333333333333333330033003333333333003300ffffffff00000000ffffffff00000000ffccffcc00000000ffccffcc00000000ffff0000ffff0000fafa0000fafa0000ffff0000ffff0000fafa0000fafa0000ffffffffffffffffffffffffffffffffffccffccffccffccffccffccffccffccffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000fffffffffffffffffafafafafafafafafffffffffffffffffafafafafafafafaffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00fffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0ffffffffffff0000fffffffffafa0000ffffffccffff0000fffeffccfafa0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|0,1=>0xcccccccccccccccccccccccccccccccccccccccccc00cc00cccccccccc00cc00ffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00ff00ff00cc00ccffffffffffffffffffffffffffffffffffffffffccccccccffffffffccccccccffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00ff00ff00cc00cc00ffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc0000ffff0000ffff0000fafa0000fafa0000ffff0000ffff0000fafa0000fafaffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0ffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa
|0,2=>0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffccffccffffffffffccffccffffffffffccffccffffffffffccffcc00000000ffffffff00000000ffffffff00000000cccccccc00000000cccccccc00000000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc00cc00cc00cc00cc00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff000000000000000000000000fafafafafafafafa0000000000000000fafafafafafafafa3333333333333333333333333333333333003300330033003300330033003300fffffffffffffffffffff0f0fffff0f0fffffffffffffffffffff0f0fffff0f0ffffffffffffffffffffaaaaffffaaaaffffffffffffffffffffaaaaffffaaaa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa33333333333333333333333333333333333333330000000033333333000000000000000000000000fffffafafffffafa0000000000000000fffffafafffffafafffffafafffffafafffffafafffffafafffffafafffffafafffffafafffffafafffffafafffffafa0000000000000000fffffafafffffafa000000000000000000000000ffffffff00000000ffffffff00000000ffccffcc00000000ffccffcc
|0,3=>0xffffffff00000000fffffffffafafafaffffffff00000000fffffffffafafafa00000000000000000000000000000000ffffffff00000000fffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafa00000000000000000000000000000000fffffffffafafafafffffffffafafafaffffffffffffffffffffffffffffffffffffffff00000000fffffffffafafafaffffffffffffffffffffffffffffffff0000000000000000fafafafafafafafa3232323232323232323232323232323232323232323232323232323232323232ffffffff0000fafaffffffff0000fafaffffffff0000fafaffffffff0000fafa3333333300003232333333330000323233333333000032323333333300003232ffffffffffffffff0505050505050505ff00ff00ff00ff00050005000500050000000000000000000000000000000000fffafffafffafffafffafffafffafffafffffffffffffffffffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfffffffffffffffffffffffffffffffffffafffafffafffafffafffafffafffafffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafaffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa5555555555555555555555555555555555505550555055505550555055505550
|0,4=>0xffffffffccccfefeffffffffccccfefeffffffffccccfefeffffffffccccfefeccccfefeccccfefeccccfefeccccfefeccccfefeccccfefeccccfefeccccfefe00000000ccccfefe00000000ccccfefe00000000ccccfefe00000000ccccfefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefe5555555555555555555555555555555554545454545454545454545454545454ffffffffffffffffffffffffffffffff0000fafa0000fafa0000fafa0000fafa33333333333333333333333333333333000032320000323200003232000032320032003200320032003200320032003200320032003200320032003200320032ffcdffcd00000000ffcdffcd00000000ffcdffcd00000000ffcdffcd00000000ffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaafffffffffffffffffffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff00505050505050505050505050505050505050505000000000505050500000000f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f0f0f0f0f5f5f5f5f0f0f0f00000000032323232000000003232323200000000323232320000000032323232ff00ff00ff32ff32ff00ff00ff32ff32ff00ff00ff32ff32ff00ff00ff32ff320f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a
|0,5=>0x5555555555555555555555555555555550505050505050505050505050505050dddddddddddddddddddddddddddddddddcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdc0000ffff0000ffff0000ffff0000ffff0000fcfc0000fcfc0000fcfc0000fcfcffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000000000000000ffffffffeeeeeeee0000000000000000ffffffffeeeeeeee00000000ffffffff00000000ffffffff00000000ffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000f0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000000000000000ffff0000ffff00000000000000000000ff000000ff000505050505050505050505050505050505000500050005000500050005000500afafafafafafafafafafafafafafafafafaaafaaafaaafaaafaaafaaafaaafaafffffffffffffffffffffffffffffffffffffffffafafafafffffffffafafafafffffffffffffffffffffffffffffffffefefefefefefefefefefefefefefefefffafffafffafffafffafffafffafffafffafffafffafffafffafffafffafffa00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000fa00fa00fa00fa
|0,6=>0xffffffffffffffffffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaa00000000ffffffff00000000ffffffff00000000ffffaaaa00000000ffffaaaafffffffcfffffffcfffffffcfffffffcfffffffcfffffffcfffffffcfffffffcfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfc55555555545454545555555554545454555555555454545455555555545454540f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f000f00ffffffffffffffaaffffffffffffffaaffffffffffffffaaffffffffffffffaafffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0
|0,7=>0xffffffffffffffff0000000000000000fff0fff0fff0fff05555555555555555555555555555555544444444444444444444444444444444ffffffffffffffff5555555555555555ffffffffffffffff4444444444444444ffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffff0000fffffffffffffffffffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0ffffffffffffffffffffffffffffffffffffffffffffaaaaffffffffffffaaaafffffffffffffffffffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f055555555555555555555555555555555555555555050505055555555505050500000000000000000ffffffffffffffff0000000000000000ffffffff00000000fffffffffff0fff0fffffffffff0fff0fffffffffff0fff0fffffffffff0fff00000000000000000fffffffffff0fff00000000000000000fffffffffff0fff0ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa00000000fafafafa00000000fafafafa00000000fafafafa00000000fafafafaccccccccfefefefeccccccccfefefefeccccccccfefefefeccccccccfefefefe0000ffff0000ffff0000ffff0000ffff0000f0f00000f0f00000f0f00000f0f0ffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa
|0,8=>0x5555555555555555555555555555555555005500550055005500550055005500f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f0f5f0f5f0f5f0f5f0f5f0f5f0f5f03333333333333333333333333333333322222222222222222222222222222222ffff0f0fffff0f0fffff0f0fffff0f0fffff0c0cffff0c0cffff0c0cffff0c0c0000ffff0000fcfc0000ffff0000fcfc0000ffff0000fcfc0000ffff0000fcfcffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000000000000000ffffffffffffffff0000000000000000ff00ff00ff00ff00aaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaffaaffaaffaaffaa0000ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff0000000000ff00ff00ff00ff00ff00ff00ff00ff00fa00fa00fa00fa00fa00fa00fa00fa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0affffffff0f0f0f0fffffffff0f0f0f0fffffffff0a0a0a0affffffff0a0a0a0a00000000ffffffff00000000ffffffff00000000fafafafa00000000fafafafa0000ffff0000ffff0000ffff0000ffff0000ffff0000f0f00000ffff0000f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000ffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaa
|0,9=>0xf0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0aff00fffaff00fffaff00fffaff00fffaff00fffaff00fffaff00fffaff00fffa00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000aaffaaffaaffaaffaaffaaffaaffaaffaaffaaaaaaffaaaaaaffaaaaaaffaaaa00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00feffffffffffffffffffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffffffffffffffffff3232323232323232323232323232323200ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00ff00aa00ff00aa00ff00aa00000000000000000000000000000000fafafafafafafafafafafafafafafafaffffffff00000000ffffffff00000000fffffffffafafafafffffffffafafafafafafafafafafafafafafafafafafafafa00fa00fa00fa00fa00fa00fa00fa0000ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aaffffffff0000ffffffffffff0000ffffffffffff0000f0f0ffffffff0000f0f00000ffff0000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff00ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ff000000ff000000000000000000000000000000000032323232323232323232323232323232
|0,10=>0x5555555555555555555555555555555555555555555555550000000000000000fffffffffffffffffffcfffcfffcfffcfffffffffffffffffffcfffcfffcfffcfffffffffffafffafffffffffffafffafffffffffffafffafffffffffffafffa0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc3333333333333333333333333333333333333030333330303333303033333030ffffffffffffffff00000000ffffffffffffffffffffffff00000000f0f0f0f000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f000000000000000000000000ffffffffffffffff0000000000000000ffff0000ffff000055555555555555555555555555555555555555550000000055555555000000003333333333333333333333333333333330303030303030303030303030303030ffff3333ffff3333ffff3333ffff3333ffff3030ffff3030ffff3030ffff303000000000ffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa00000000ffffffff00000000ffffffff00000000f0f0f0f000000000f0f0f0f0aaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaafafafafaaaaaaaaafafafafa00ff00ff00fa00fa00ff00ff00fa00fa00ff00ff00fa00fa00ff00ff00fa00fa0000000000000000555555555555555500000000000000005500550055005500
|0,11=>0xffffffffffffffffccccccccccccccccffffffffffffffffccccccccccccccccffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffccccfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff000505050505050505050505050505050504040404040404040404040404040404ffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffee33333333333333333333333333333333333333333333333333330000333300000000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000ffff0000aaaa0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aaffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000fffffffffefefefefffffffffefefefefffffffffefefefefffffffffefefefeffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffff00
|0,12=>0xffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00fffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000fffffff0fffffff0fffffff0fffffff0fffffff0fffffff0fffffff0fffffff0ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xb190d04030201000b09191007031800121a0507030220000905040302202100050d0403022001001d13121a080703020b111a05041f18001d17111a1e0418001d13080d04030201111a0e05040318000b111a0403181c0017131211051016010b111a190403180017130504160215010b121105100f010006050403020100
|1=>0x1140b090510070318001d1711091e100401001a09050403180220001d13090804030225010b121a0507030224001d13111a05040318000b220919040302010011090e0510040301001d1723091e0402001d171e0d0402010005040302152001000b230919040302001d17091e100718000b111a1e0804161823090504030220
|2=>0x160201130b090510071603181d17091e10041801000b09100703021c01001d0b09081007031800140b09050403022100090e051004031801000b05040302281501000b1a091e08070416020b11090403181c01000b11090510041f01000b09100403181c0100140b050d04030201001d13270908040302011713260905041602
|3=>0x3022001000b12111904030201000b121a0403021c01000b110905041f180100090e051007030201000b090510041f180100090504030225200100140b121a05070302000b09052904020f01000b2309050403022400130b050d04160302011d1711091e041801001d0b080d040302010011090e0504031801000b111a1e0804
|4=>0x40302241501001713090529041602011713120905101602010b121a05041f020100140b230905040302001d1722091e04020100130b121a05071603021d17121a1e040201001d0b121a08070302001d1312090807030201121a0e0504030201000b12110510032801000b1a091904031802000b22090403021c010027090504
|5=>0x1d1712111e040201000b0905100703182a001b0b090510070318000b27091904030201000b111a0504020f01000b12110403021c01000b091e080704161802120905070302200100130b230905041603021d0b230908040302000b091e080a041602011713111a05040318000b09190403022501001d17111a05040318000b05
|6=>0x2010b0905100703182c000b121a050703022a000b11091e081004160117131a0905070416021b0b121a05070302000b09050403022a21000b1e080d0403020100130b121a0805070302140b050403021501000b111a050403182b000b091e0810070318000b12110510032401001d171a091e041802000b050d0403022a0100
|7=>0x70318002609050403022001000b111a0805041603181d0b111a1e040318001713090507041618020b111a0c05040318000b23091e08040302000b270905041f0201000b11091e08041618011d1727091e040201001d17091e04022501000b111a050403182d000b050d0403022c01000b12091907030201001713111a050416
|8=>0xb11090504020f0100130b12090507160302010b1a091e080403180200171311090510040301001d0b12090807030201001d1711090510040301002e0b230905040302002e0b050d04030201002e0b090510070318001d17230905040302002e0b111a0504031800170b1e050d040201001d17050d04030201001d17090510
|9=>0x2c001d0b0905102f033101170b12090510160201000b090534102f033101130b27090805040302011b0b09050403022501000b1a09080507041603020b1211050403022c01000b09050403313001001d0b1a091e07040302000b2609050403022801001d0b110905102f030100130b09080504030225010b111a0c0504030201
|10=>0x1801000b09050403023601001b0b27090504030201001d13090807040302010b111a080504160302011d170905100403180100170b09052904160201000b12091e0510160201000b09050403022a2501001d0b111a1e04030201000b0935052f040302011d1312110504030201000b09050a0403022d01000b1a090504031802
|11=>0x3022501001d0b0905102f031801000b08050d04030201000b1109051004032b01000b2709050403022a0100171311090504031801000b23090504160302000b091e052904160201001d1711090504031801000b09080510070318000b09050418020f01001d131a090504031802000b090507040318022d0017130905100403
|12=>0x13121a0504030201002e0b111a0504030201000b0905040302252c01003b0b090504030201002e0b1a090507040302001713110905041602010b27091e080403020100170b09053a04030201001713090510041602010b09052f03313901171309051007030201000b09050403023701001d1709051007030201000b091e0804
|13=>0x132709050403020100170b22091e05040201000b090c050a04030201000b1109051004032d01000b2709050403022c0100130b1209080507030201171322090504030201001d1309050403022501000905070403022001000b1109050403182b01001d1722090504030201000b121a0805070302000b0905100403182b010017
|14=>0xb09053203024001003e0b090504030201000b0908050a04160302010b090529040302280100170b111a0504160201000b1209050703022a01000b1209051003022801000b2609050403022401000b090c05070403180200170b1a090507041602003c0b0905102f0302011b0b12090507030201000b0905100703022b01001d
|15=>0x3020100460b0905102f0331010b11091e05102f0301000b09052f0403313001170b110905102f0301000b12091e08041602010b2209050403022b01000b1109050403182d01000b0908050704160318020b121a050403022b01000b09051043030201000b0905100403182d01001d0b091e0704031802000b09410403020100
|16=>0xb09054c102f033101130b111a05040318002e0b09050704031802001d0b111a05040318000b121a050403022d01000b09053204034b01002e0b09050a04030201000b11090c051004030100140b26090504030201000b09190704030201000b09050403024901000b1209050703022c01001713121105040302010009470504
|17=>0x1000b09050403025001000b111a05040302280100170b09050a04160201000b11090c0504031801004f0b090504030201000b09050403024d01000b090c05100403180100130b26090504160302010b1a09050704030228001d0b26090804030201000b1109080510041603013c0b090510040331010b2209050403022d0100
|18=>0x1000b22090c050403020100090e050704030201000b121a0c0504030201000b0908051007160302012e0b1109051004030100171327090504030201000b0905102f033001001d1727090504030201001d0b11091e04031801000b0908051004160318010b090c05100703020100170b09050704161802001d17090504030225
|19=>0x2f04030201130b09052904160302010b1a09050704030224000b2209080504160302012e0b11090504031801000b09050403314b0100170b11090510041601002e0b09051004031801000b121a080504160302010b090507041f0201000b0905100403300100140b12090510030201001d131a0908040302011d17091e070402
|20=>0x1001d0b050d04030201000b09050a0403022401001d0b090510070318000b1a091904030201000905100403022001000b09350532040302010b1a0908050416031802140b1a090507040302000b26091e0804030201000b1a090c0504031802001a0905040302200100170b111a05040318000b09051004035401003c0b0905
|21=>0x2000b09055704030201000b09050403025601000b1a09050403022801001d1711091e040201001d17091e10040201003f13090504030201001d0b230905040302000b09054c2f0331011d171a091e040201000b09051003024001002e0b27090504030201000b11091904030201002e0b09050403022501000b091910040302
|22=>0x650b09050403020100170b1a09050704030200640b1a09056303020100620b090504030201000b09050403025501000b09054c1004160201001d17091e040201000b610960052f0302010b0905045e030201000b09050403025d0100090e0504030201000b1209080507030201005a0b09050403020100130b090507040318
|23=>0x180201000b096f05320403020100170b111a0504030201000b110960052f030201000b1a096e05045b0301000b09050403026c01000b6b090504030201000b093305320403020100170b09050416180201000b12090510033101000b0960056a2f030201000b0905040318026901000b09050403026701000b09050403540201
|24=>0x90504030201000b0951051004033101000b1209050403022d01006477090504030201000b0905045b033158010b0960052f03310201750b09050403020100740b12096e05040301000b09050472030201001d0b6109050403310201460b0905040370020100170b0905040302710100170b09050403700201000b0945050403
|25=>0x960052f03180201003d13090504030201000b7c090504030201000b7b09450504030201001b0b090507040302010064131109050403020100130b11090510040301000b096e05320403310100170b12610504030201007a0b090504030201001d0b1109051004030100130b09080507040302010b0905040302780100760b1a
|26=>0x840b090504030201000b09052f040302830100740b09052f040331010b09050403028201000b090552100403020100170b0905321004030201000b110905040302280100170b0905040302018100800b1a090504030201000b097f052f04030201000b0905070403022a01000b0905100403022801000b09050403027d01000b
|27=>0x9050403180201001d0b11090504031801000b09052f0403024b0100130b09051004031801000b7b0960052f030201000b1a09050403022401000b091e080704030201001d0b09051004031801000b096f05070403020100640b11090563030201001d0b6d09050403310201007409050403028701000b090532040302860100
|28=>0xc0504030201001d0b09051007030201001d0b0905322f0403020100170b1a09050403310201000b0905045b03703101000b8c090504030201000b2609050416030201000b09050403028b01001d0b09050403180258000b0905048a03700201000b0988050403020100130b11090504031801001d0b61090504030258016413
|29=>0xb1a0905040302940100930b09050403020100170b09050704031802000b0933050403310201000b09050403029101000b09050403029001000b09058e0403020100760b11090504030201000b0905070403028d0100170b09050a04030201000b09053a04030201000b096e05070403310100130b09051007030201000b1209
|30=>0x20100130b121a0504030201000b1209050403027e01000b1209080504160302010b09050403029901000b090563322f030201001d0b12091e04030201000b09050403029801000b0905045b02690100960b090504030201001d0b09050403310258010b09059504030201001d130905070403020100640b1a09052f03020100
|31=>0x80403020100460b6109050403310201170b61090504033102010b0905100403022401000b090510040302a10100760b09050403180201000b0905040302a001000b09050403029f0100130b22090504030201000b099e050403020100140b1a090504030201000b090504039c0201000b0905100403029b01000b0905049a03
|32=>0x1000b0905102f0331010b1209051016030201000b120905040302a401000b091e08041602011d0b0905040370310201000b2609080504030201000b110905102f0301002e0b1209050403020100640b6109052f0302010b09050403a20201000b0905040302480100130b1a090504160302010b09054c2f030201001d0b1a09
|33=>0x13d0b09054c0403020100170b1109050403180100170b12090504160201000b0905040302830100130b1a090504031802001d0b0905040302850100170b6d09050403310201000ba509050403020100530b0905040331020100140b09051004030201000b09052904160302010074131a090504030201000b09050403180224
|34=>0x11d1709050704030201000b0905040302a901001d0b09a80504030201000b12096e0804030201001d0b0905320403020100680b11090504030201000b090534320403020100130b09051004160302011d0b0908100403020100640905040302a701000b0905522f04030201000b1a09050403026601000b610905048a033102
|35=>0xb1a09050704160302001d0b27090504030201000b0905630402ac0100130b09050403022501001d0b09050403022501000b09052f040302ab01000b0905040302aa0100640b7b09052f03020100460b0905040331025801170b0905040331025801140b09050403180201000b096f052f0403310201130b11090504160302
|36=>0x20100170b0905040370310201000b09052f03027301000b0905040331026c0100b00b090504030201001d0b090504030201af000b1a091e0804030201000b1a096f0504030201000b111a050416030201000b090504020f01000b09ae0504030201001d0b120905040331020100ad0b09050403020100130b27090504030201
|37=>0x804030201000b091e081004030201000b0905040302b601000b09055204030201000b0905040302b501000b1a0905040302a601000b111a05040318001d0b0905040302b40100170b09050403028501000b12096e05045b0301000b1a096e0504033101000b090504033102b301001d0bb209050403020100b10b0905100403
|38=>0x1000b0935051004030201000b110905040302a601000b0905100403028601000b12091e050403310201000b096f05100403310100170b1209050403310201000b1a0905040302a701000b0905040302ab01000b1209b70504030201000b09054c3204030201001d0b1a09052f04030201000b09050a0416030201000b11091e
|39=>0xb0905102f030201000b090534102f030201001d1711090504030201001d1709051004030201000b1a09053404030201000b090510040302b801002e0b09050704030201000b1a09600804030201001d171a090504030201001d0b09052f04033102010b0905342f04033102010b090504031802a601001d0b1109052f040302
|40=>0x30201001d1709050403020100130b12090504030201000b0951051004030201001d0b12090504030201002e0b09051004030201000b09054c102f030201002e0b1a090504030201001d0b09059704030201001d0b7b090504030201000b230905040302001d0b09056a04030201000b050d04030201000b090510070318001d
|41=>0x100bd0b096e0504030201000b09053404030201000bbabc0504030201000b09050403022b0100640b0905040302580100170b09052f0403020100740b09600504030201000b09bb0504030201000b09058904030201000b09059704030201001713090504030201000b0960080403020100b90b090504030201000b7b090504
|42=>0x4030201c0000b61096e0504030201000b0905040302710100790b09052f04030201000b09052f045b030201000b111a0504030201000b09056304160201000b096e050704030201000bbc09052f04030201000b1109600504030201000bbc0905045b0201000b61090504bf030201000b1a09050704030200be0b0905040302
|43=>0xb090532100403020100640b096e0504030201000b09050403020181000b09606e04030201000b090504bf030258000b1261050403020100640b090504bf030201000b09050403022d0100740bba090504030201000b090504bf0331020100740b096e05040301000b1a0905041603020100c10b09600504030201000b0905
|44=>0x5040302a301000bba096e04030201000bc4090504030201000b09050704031802000b090c050403020100640b1a090504030201000b09050a04030201000bba09056304030201000b0905040302c301000b1a09050403310201000b0905100416030201000bc2090504030201000bbc61050403020100170b12090504030201
|45=>0x504030201000b6109056304030201000b096e0504bf030201000b11090510040301000b0960c604030201000b09054c04030201000b61090504033102010b09600563030201000bc5090504030201000b0905041603180201000b09050403027e01000b0908050416030201c1bd09050403020100460b090504030201000b09
|46=>0x201000b09050403310258010b1a096e0504030201000b0905322f0403020100170b090504160201000b09050403026901000bba09052f04030201000b61090504030258010b0905630403310201000b11090504031801000b09051004031801000b6d09050403310201000b0905045b033101000b090504c7030201002e0b09
|47=>0xb0905040302250100800b090504030201000b09a80504030201000b0905320403020100760b090504030201000b09050403028501000b090504037031020100c10b090504bf030201000b09050403027301001d0b09050403310201000b0960052f030201001d0b61090504030201000b096e0804030201001d0b0905070403
|48=>0x5045b030201000bbc090504030201000b12090504030201000b09052f0403020100130b090504030201001d0b090504030201000b0905102f030201000b09052f04033102010b1109052f04030201001d0b09051004030201001d0b1a090504030201000bb2090504030201000b1209050403310201000b2709050403020100
|49=>0xb090504030201000b09051004030201000b1a090504030201000b61090504030201000b09050704030201000bba090504030201000b09600504030201000b090504030201000b09
|_=>0
def sO:Nat→Nat→Nat
|7,0=>7
|8,0=>0x15f00a7804fc025e011f0087803fc01de00df0067802fc015e009f0047801fc00de005f0027800fc005e001f00078
|9,0=>0x17748b9645b922d3916548b06457122af915348a764529228b9141489e644e12267912f4895644992243911d488c64451221f910b48836440921fb90f9487a643c121d790e748716437921b390d5486864331218f90c3485f642e9216b90b14856642a12147909f484d642592123908d48446421120ff907b483b641c920db906948326418120b79
|9,1=>0x43b9219490a64841241792074901647f923f391f548f8647b123cf91e348ef6476923ab91d148e664721238791bf48dd646d9236391ad48d464691233f919b48cb64649231b918948c26460122f79
|10,0=>0x35449a7a8d29468b9340d19de8cdb4663a32d499428c8f263da319d18aa4c450618a307c98168bf745f1a2f44977a8ba945caa2e0c96de8b5b45a492cdc96468b0f457da2ba495aa8ac32557a2a6d150e8a73452fa292d14724a254508a27f513d649d744e2926c5133a898944baa258c929e893b4493a244d11fe88ed246ca23151162889d4444a
|10,1=>0x4895242291fd48f59475d238691af48ce9462ca2ee916348a7a44ed224e91152880a43bca1ba50c9485b9428d2122507d4834a415520865031280ea40251ff20fe727e9a3f049f5a8f9b27c3a3dcd1ebe8f4b479c93c951e228f01077793b749d928eb54750a3a351cf28e654728a38f51c564e174701a37bd1bb68dc746d9a367d1b168d7746b1a
|10,2=>0x56ccab42558f2abe955b42ab655492a9aa548caa1e94fd2a759535d298a54b32a509523ca8f694674a29a50fd285a541b2a0494fdca7c693cf49dda4e9d272a538149b6a4d65268e53352990a4c3ca5fa52e9496b94b0d255e929b4943a49d4a4c2924d491ca
|11,0=>0x69e534ca9a514d1ea68a5342a9a032cf7a6774b39659b74cd1a663d32f699674ca9a6504b25a99194c83963cd31be98cb4c5c9629cb12a58832c37a6174b09298354c10a60352ff297e54be8a5ef52f5297972bc295dc52eba974b2b9ba5c8d2e2256ff2b7695b652d8a96b32b5095a352cfa166b2b2c9591cac6e16234b08957f52bd655d92ae2a
|11,1=>0x7d653e8e5f334f9097c353df65ee74f69a7afd3d5a5e994f42a79ccbcc25e4f2f1da78a4bc2a9e014ef6a776cbb8e9db34ed09763cbafa5d694eaaa75053a5e5d1b4e83a73cd39be9cc96e59b727d391a5c794e339714d387e9c2d2e0ca701537e29bdd4de4a6ed537429b8d4dbca6d9536a29b3d4d93b6c54b6029aef2d6da6b24b56e5aa34d46b
|11,2=>0x90ecc84ae41331ffa8fad47aea3c531d8a8e754712a37731b1a8d3d4676a3275189a8bfd45d6a2d93162a8ac5453aa289513aa8985449aa23b3113a884d43fea1eb50eba870d4362619d50c4a85cdc2c2614d509ca84954222a0fd507688365418aa0b5104fb822d40f26065502998104c05e601b500497fd53fc29fcd4fdca7e953f229f7f2fb69
|11,3=>0x144baa20d50dea85b5423aa0dc5046a813140189fbd4fb6a7c753d9a9e7d4f16a77753b1a9d3d4e76a7275389a9bf5cdd2a6d55360a9aadcd2ea6817336a996ccc8ea633530eb98254beaa5e152e7996f4cb56659752c3895cd4abea54b529ba948d4a1ea4fb5272b934cc97ea4ad324ca921548e2a45d52268
|12,0=>0xb5355a766d29368b9b414d9e66ce136679b2f4d9566c9756429b1c558be6c4b561bab094d8266bff55f5aaf5d578a6bb335d09ae3cd6f6ab6935aaaad05565e6b1b5583aabd4d5c2aacf355daaa9d552a6a833537aa96d548eaa353510aa83cd3fa69e954eb9a714d366699f54c5aa5dd52ca695334a09a4bcd23a690b347c9a39cd1a6a8bf5455a
|12,1=>0xc21ce0ea70615826ac0e5604e701358009bfbcdfba6fcb37dc9be9cdf2a6f8157b6abd6cde8eaf353790abc3cddf6aee9376aabb055d5e6e9d3744ab9dcdcc6ae51371f9b8ad5c326e0736fa9b7855b9aadbb36d49b65cdb0a6d7336b09
|13,0=>0x18b79c574e296713938939c454e20a30f338709c33ce17a70ab384c9
|14,0=>0x18c08
|_,_=>0
def wAt:=mkWire dB 200 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 1000003 zs)
def oP:Nat→Nat
|0=>0x500424110401408051403008250513404250b004140d050b42409010940c2d020142c010a0901c09050042c150401408050902424050b0c0200d050040805090140825051b8582d030042c0d030042c01090440825040242405051b05c010b0342409020142c0d090a80c010702410050b004500f090444c150204408250b00438350c0b02824080341c09040141401
|1=>0x50048807100941009050342c0d0b0542c150a090140d070242c0d040148807120241025051b04c0d0b004140d010442c0d0b0540805040242405020141401050340825030046c140a0904c0d0702410050b0046c14010444c0d0204408050b004302f16054241109014100503004302f2201058151202410250300428241804408050b0c85815030042c01050b42405
|2=>0x1403024091d0040811050b4100902014146e160b40c01080b428240702410050500468110b0042c150901414011a0242c010b034240503004202d050040411020141009020941009050342c0d0b0542c32160542405020140c010b0044027050041009050b44c0f090442405040142c010b0042409010942c1502014480904094146c130342c010b0c0200d020440825
|3=>0x503424090b0342c15050b42824070241005050042c301e004140d090240805090240c01030542405050040c010b0040411020141009020140811050342c0d0b054100504024146e130342c01010440805050041009050b48804130544809040942c010204408050b0c0200d050040c220a09c1c09040141401040140c0103054240505004080502094146e160b40c01
|4=>0x9014080503004441102094146e160b40c010c0bc200d12014102505004082504094146c130342c01090442405051b84c0d0b004240914030144d020142c010402410050b0c0200d05004081114030144d020142c010910810090b0c8200d050044c15090442405040142c011403c2c211001c1009050040c4e2201c4809040942c010300428240702410050b0040805
|5=>0x30b40805090a810610313808050b0042c011001c2c0d040240c010b0041025030040811030b4500c04094144d010942c010513488071202410250b004402504024140d0b0342c150300424110901410050b00424050503424110b0342c15050b42405050042411040141005050b424110b00414010904424050b0c0200d05004200f050042411020941009051b0582d
|6=>0xb054144e0b0040411020141009010444c0d0204408050b0046c14130344805040942c0109014082503148202d05004241102094146e160b40c0101024140d010440c010500424110b0c80411080341401012280c011202410250b004048a041142c15020941401030041c09050040c15040142c01090240425030b408051b0502c591009c100903004142d090240425
|7=>0x503414010402408250300404110b0042c0d010940c01170042411010942c0d0401488041305c4809040942c010a0901c09050040c15040141401090442405040142c01090a8202d070241005050045817090242405020140c010102410090503410050500424111303c0811020942c01020142405050342c0d0b054144e0a0901c09040142c0109044140d090242c0d
|8=>0xb0341005020142c0109024581509014080503004880712024140103054102514030202d05004681109014080505004140d020940c0112014140d090442c0d0b054402704024140d0b0342c1509024582f090140805030042428041842c22020141401090441005051b04c0d0b00408250b0042c0d010940c010401410090b088080505004144e090142c01090441005
|9=>0x5004142d0904410050b0342c15020941009012284809170542c0d040942428070245c150b034100504014081102014740d050b488070b05448090b0341025170542409010942c0d020142824050341c090b03410050a0902c15070242c0d0401404110b0342c150201410090c0bc200d05004680909014080503004042502094140109024042502014140d050b40c01
|10=>0x40240c010b0341025032f408110400408010b00414011a04424050b1644027040240c01010940411030041401080bc10250209414013302c14c931044080101094100505034142d091840c220201414010b05410010209410090b0044027040241401080340425020941401020940c52080b41401040142c01040940c010503424050201414010402424090b0342c01
|11=>0x40142c5a020140c01040240c2d020142c01290884007040241401130344805040942c010b00414010b05410050300404250209414010b03408110b05408051001c0c01040240c2d040240c15040940c011305c2c011009c1009030542c150902424053300c14c92f02410010b0541025020942c01041842c5a020140c01080bc240502014140104024080104004142d
|12=>0x2004400f0400408110b0341005040242c013803c2c951009c10090402410050b0342c150503414011009c10090400408110b05408050a0901c090401414011605c0811020940c011305c4805040942c01090240c2d020142c012201c4809040940c011001c140d040240c010b0342c15090240805050040411020141009020140c52080b414010b0542405020142c01
|13=>0x120242c01030b410250b004402704024142d0b0c8041108034140102014145a020940c010b05448090b03410250901414010904410051605c1009020140c01090142c01030b4102509024740d050b42405091081009080bc1401291344007040242c01010945c150b03410050b0042c0d020940c01120142411050341401290044007040240c2d0b0040c01040240c2d
|14=>0x1001c10090803c14010b0340c01090242405051382c010904410050803c1025040241401031382461020142c01080341005020141401090142c0d040140c0104004f403100b41009130342c010904410051605c1005040240c010b0544805040942c010503448090b0341025080341c09040141401160bc0811020940c0112014202f040941401050042411040142c01
|15=>0x40242cc50200410010503410010209410094502c14bd0400408010b03410010209410090503424110300414011605c4809040940c01090242c5a020140c01030041005020141401051680c0109044240504444404e040242c01040242c5a020140c010305404090b0541005054245c42040242c0d3304cc8151000408113f00c2ca51001c1009030041c09040141401
|16=>0x3d00c0801100b41009160bc4809040940c01040040801100341009090242405020142c011705404090b034100509014142d090240805160bc0c010904424053402cbc092f0341001070245c150b0341005080340811020941401080b414011a024240504014146c130342c014a03c94011009c1009080bc1401090441005090242c01030b410250b48c784204024140d
|17=>0x2014082505034142d050041009020140c01080341005040241401040142c0d020140c010b0344027040242c15053a8a4011001c1009010940c22020941401041842c0d020140c011e004140d090240805172544027040240c2d0b4e80c951009c1009040241459020140c01030042c011a0242405040140c22090141401091842c15020141401030040811020941401
|18=>0x20940c01040240c2d0204408051d034142d050040c0109044240514030144d040142c013302d440110054100909044740104024142d0b0042c150901414010b034100505034142d160544809040940c01040142c300803414011e0042405050341025030041005040241401020445c150b0340825120142c01030b4102504025140b2f05410011201410250b0342c15
|19=>0x9014146c130342c01040242c320803414013300cc815100041009050042405020140c0104014144d090142c01030542461020141401160542405020140c01090142c320803414010902404250b03408050255440220402414015300c2cc92f02410010b0044007040240c01090144c0f040142c01050044809040940c011d034142d0902408055202cc80d310440801
|20=>0x580bc04011a0882405050040c220901414010503424090b0342c1504024140d0b0342c15290b44007040242c010122848090b054102502004400d04004081109014140d0b0342c153304d4401100541009120145c150b034102509024146c130342c011d034402704024142d04024146c130342c01090a01c090b0541005070244c0f040142c01050b40411020141009
|21=>0x320544001040242c0d020140c0102004102502044bc0504004141104168080503005a00b0b6340c1102664201305004744502094142d010942c0d04014100d0b04424051a13424050b004402204024140103004400d04024140d0b0342c15090041001050440d7d2f02c10013409c5811030042c300803414010500424110401570070b5b40c090401408050b0041165
|22=>0xb005e40b130442c011d044142d090140801100541009160bc1025030044c070b0042c110302408010100408010400414117601c15910b0441025050242c0903734402f04024142d02004240131014c42d02004bc27040040c2d580240c2d01004102102014140105314c411020042c0d090242405020941001050442405050240c090b6d98409090047849050341025
|23=>0x130442c014c004400d040244001040240c2d030880825050042c0d5804c04016e0b414090901514072f05410011305c10050b00410090803c14017e014580b030041001020141411100b410090b0042565580bc0401092f4bc15040042c59040140c01090242c010b0440811020942c01310440801050242c0d0904424011311408250b004142d020941009050041005
|24=>0x1024142d010040cc5013140801890242007050042409020142c0101004142d09004102d020142c01050b4240902014d00b2f03410010402408050b0041411092f410010313824050b004140d040141401020140811050b420090401414010403408250b044c42502004142d1309c2c090b004c8171000410090b854c41302004c82f2f02410010200410010b025e427
|25=>0xb04414c60200424050b714bc270400404090b034100505324c4110200406490809c14011016c100903004123d0802c14011d0440825050b40cc6020041005070242c0d04014a4011001c1009050240801040141005040242c0109044200d0500410090b05410052f0241001050b40801030b424053101408010302425a51604c0c010918408050300425a20b6340c11
|26=>0x201414110818c08050500600130b6e414091202410250b00414951009c10090513424050b0040a756105c24014c05c400d040245861020140c010b004241109014580b040940c01090440c0105004e4011003c100904034bc0904004102505034142d6d05d8409090045813030040c09970b4400304024142d010040801100801009050042c15040142c01090141001
|27=>0x1001c1009030042c09090142c010313808050b0041009020041001090441009030042411310bc080103004140d05004142d310140801050046809090141001020440825170542c0d040942c1104004240102a34bc2f04004784204024140d0b004240503004400d0400408110b0542405050042cc5020042401090040801030b40c4e040242c01053d8402d040242d81
|28=>0xb004142d6101c240104094140905004bc0904004142d170442c0d02094bc092f03410010b004100903004140104024142d1302c2c110b004c80d2f0241001040882405050040cc509004080110034402d0402408050b0340825030042c0d04094c82f1000410090901408050b00410c602004142d093140801030b426992f03c10010b324c41102004740104024142d
|29=>0x90141401030042409090140c52080b414011e07410050503408010b05410251d1041009050b44805040942c010401424050300448050b0541025091680c01030442c011009c10091009c1009050b5ec0f092f41001a3014bc2f040042c11092f4100101004c42d020040401020040c2d0513408050b00414c50200410010b00408250300410050b0342c151307c1005
|30=>0x4184080503004240905034140103054100905006c80f610142401101641009030051827130242c0109014bc0f0400408050902424053109c0801050b4c413020040c2d03024102505024140902004240505708c405020058405050b424013d034402d04024c405020040c2d100bc1001020442db63109408011d1a4142d09015600b050b40401030542405050042009
|31=>0xb05410090b0342c1504164240503004405a040240c0104014740d050b42405050041411090142c0d0b054080104004142d02004bc0d0400408052f03c1001020941001050b544031005410092f03c082504004c8171000410090503410250200414c5020041009090440801030b44c0b090142c017b03d841109005b80d04094140910004400d040241001050b42405
|32=>0x30042c11010041001030b414110b024158d030442007050044003040242c0d0b004141105006e82d050958411090042c0d0b05410250b0044015040241025050b4740d04024142d10034100102044740d050b42405050b4400304024142d610442401012284809040956011050b40401090a01c09040140411020141009040241001050b410092f0341001090242c0d
|33=>0x90042c0d040944001040242c1105025601301004101505024040d010042411090040c050b044582f030042c090509408010301414090b02424050300414110b095601701004140909004bc2704004bc2d040041001030242409090140c01030441005050241001030940825050440c09030940c0509004100509015842d0900414090b014581103004240d050945817
|34=>0x304424090201408110201424c5020040801030256c0503024740d050b4100d090040c0505024082504024140505044116d03024080109004100d05044258d03044080503004580b030040c01050042c050b0944c090b004bc2f04004140905094681509014080504014200d050042c11090141c0904014100d05095841309004080109014100903006e811050940c25
|35=>0x30941025040042c01050b41001020440801040040825040041009050b4142d090158405090040801040946811090144027040242db9050258407090044001040247411050b4c41302004c405020040c050b094402f040240801050b4100105044142d090041409050041005050b4040102004140909014bc09040040c01030b45813030041425040040401090040801
|36=>0x1009090142401040141425050440c09
|_=>0
def oO:Nat→Nat→Nat
|7,0=>7
|8,0=>0x7960736000006d606760616000005b6055604f60496043603d60376031602b6025601f60196013600d60076
|9,0=>0x1ba51b551b051ab51a651a1519c51975192518d51885183517e51795174516f516a51655160515b51565151514c51475142513d51385133512e51295124511f511a51155110510b5106510150fc50f750f250ed50e850e350de50d950d450cf50ca50c550c050bb50b650b150ac50a750a2509d50985093508e50895084507f5
|9,1=>0x273526e52695264525f525a52555250524b52465241523c52375232522d52285223521e52195214520f520a5205520051fb51f651f151ec51e751e251dd51d851d351ce51c951c451bf5
|10,0=>0x3744370436c436843644360435c435843544350434c434843444340433c433843344330432c432843244320431c431843144310430c43084304430042fc42f842f442f042ec42e842e442e042dc42d842d442d042cc42c842c442c042bc42b842b442b042ac42a842a442a0429c429842944290428c428842844280427c42784
|10,1=>0x4744470446c446844644460445c445844544450444c444844444440443c443844344430442c442844244420441c441844144410440c44084404440043fc43f843f443f043ec43e843e443e043dc43d843d443d043cc43c843c443c043bc43b843b443b043ac43a843a443a0439c439843944390438c438843844380437c43784
|10,2=>0x5344530452c452845244520451c451845144510450c45084504450044fc44f844f444f044ec44e844e444e044dc44d844d444d044cc44c844c444c044bc44b844b444b044ac44a844a444a0449c449844944490448c448844844480447c44784
|11,0=>0x5f535f235ef35ec35e935e635e335e035dd35da35d735d435d135ce35cb35c835c535c235bf35bc35b935b635b335b035ad35aa35a735a435a1359e359b359835953592358f358c3589358635833580357d357a357735743571356e356b356835653562355f355c3559355635533550354d354a354735443541353e353b35383
|11,1=>0x6b536b236af36ac36a936a636a336a0369d369a369736943691368e368b368836853682367f367c3679367636733670366d366a366736643661365e365b365836553652364f364c3649364636433640363d363a363736343631362e362b362836253622361f361c3619361636133610360d360a36073604360135fe35fb35f83
|11,2=>0x7753772376f376c3769376637633760375d375a375737543751374e374b374837453742373f373c3739373637333730372d372a372737243721371e371b371837153712370f370c370937063703370036fd36fa36f736f436f136ee36eb36e836e536e236df36dc36d936d636d336d036cd36ca36c736c436c136be36bb36b83
|11,3=>0x820381d381a381738143811380e380b38083805380237ff37fc37f937f637f337f037ed37ea37e737e437e137de37db37d837d537d237cf37cc37c937c637c337c037bd37ba37b737b437b137ae37ab37a837a537a2379f379c3799379637933790378d378a378737843781377e377b37783
|12,0=>0x8a1289f289d289b28992897289528932891288f288d288b28892887288528832881287f287d287b28792877287528732871286f286d286b28692867286528632861285f285d285b28592857285528532851284f284d284b28492847284528432841283f283d283b28392837283528332831282f282d282b28292827282528232
|12,1=>0x8f928f728f528f328f128ef28ed28eb28e928e728e528e328e128df28dd28db28d928d728d528d328d128cf28cd28cb28c928c728c528c328c128bf28bd28bb28b928b728b528b328b128af28ad28ab28a928a728a528a32
|13,0=>0x906190519041903190219011000090018ff18fe18fd18fc18fb1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 16
def pmP:Nat→Nat
|0=>0x3149f6600000000000000006290cdc0000000000000000c5213b800000000000000018a407300000000000000003148046000000000000000020109cc00000000000000003823318000000000000000070427700000000000000000e084ce00000000000000001c0098c0000000000000000373faa80000000000000000605f7500000000000000000c01ea0000000000000000017deb54000000000000000028ad7a80000000000000000510ad0000000000000000004086ee000000000000000007fc35c000000000000000008e17b800000000000000000e7257000000000000000001ce0ae0000000000000000039c05c000000000000000007380380000000000000000005277000000000000000000097ee000000000000000000109dc000000000000000000213a8000000000000000000407700000000000000000001f66000000000000000000001fc000000000000000000003880000000000000000000000
|1=>0x82ae95e8000000000000001045f0bdc000000000000002083213b00000000000000041064036000000000000000820c804c000000000000000f801dbdc000000000000001c40233980000000000000008c042730000000000000001080a4ee000000000000000210109dc0000000000000003f8233300000000000000007f042660000000000000000f0080ec0000000000000001e010098000000000000000338193380000000000000006603f750000000000000000ca275ea0000000000000001847cbdc000000000000000308d87b80000000000000006007bf70000000000000000c00e4ee0000000000000001800fedc0000000000000003001ddb800000000000000060030770000000000000000933c1ae0000000000000001221895c000000000000000244300b8000000000000000488600700000000000000006ecaccc0000000000000000dd94998000000000000000183281300000000000000001db4af1
|2=>0xc1c80e4ee00000000000001819c1c9dc000000000000030300393b8000000000000031e00767700000000000000473148cee0000000000000070c1939dc00000000000000e083271b00000000000000184886e1700000000000000303149cee000000000000006062938cc00000000000000c0073f0b80000000000000180004e77000000000000002b60cacee0000000000000047e0119dc000000000000008c00233b800000000000000c3574af7000000000000001810585ee0000000000000021905fbdc00000000000000426cb56a800000000000000818b4af700000000000000101829de600000000000000201452bdc000000000000004020af7b80000000000000080015af5000000000000000f60cacee000000000000001e00019dc000000000000002238013b80000000000000043765677000000000000000860cbfee0000000000000010c1949dc000000000000002183213b80000000000000041824277
|3=>0x41000086ee000000000000082000109dc000000000000101c02237b8000000000000200844427700000000000004000e88cee00000000000008001d109dc000000000000100002213b80000000000001882114277000000000000031003284ee000000000000060080309dc000000000000088d08233b80000000000001082514af700000000000002100b295ee000000000000040332189dc000000000000080520213b8000000000000100499e2f70000000000000200910c4ee00000000000004009c119dc000000000000080100213b8000000000000100028437700000000000002000109fee000000000000040002109dc00000000000004618ba13b80000000000000886113077000000000000011002280ee000000000000022004401cc0000000000000431a32b3b8000000000000084306c07700000000000001041808ce6000000000000020810119dc000000000000040308b9bb8000000000000070600fe77
|4=>0x8241048cee000000000000102013dfbdc000000000000202003213b800000000000040084e7277000000000000080003f81ae000000000000100003fcbdc0000000000002000073ffb800000000000040000e7277000000000000080001c9f2e00000000000010000392e5c000000000000200007213b800000000000040000e400700000000000005d002284ee0000000000000b8000309dc00000000000014400aa13b8000000000000280004c27700000000000004d00a295ee000000000000098e0011bdc000000000000130420213b8000000000000260070427700000000000004c00009fee000000000000098000109dc000000000000129000233b8000000000000248000c2f7000000000000049000087ee00000000000009000030fdc00000000000011001021b38000000000000220001c2f700000000000004400009fee00000000000008800012fdc000000000000109000233b80000000000002080554af7
|5=>0x100920d85ee00000000000020124190fdc000000000000401fc0611b0000000000000803e00b23700000000000010070018466000000000000200e00208cc0000000000004007007b7b8000000000000800e00f2f70000000000001001911c5ee00000000000020032218fdc0000000000004004cd21fb800000000000080098ac6f7000000000000100110085e600000000000020020410fdc000000000000400407797b800000000000080080e73f700000000000010010018dee0000000000001e800650ddc00000000000039c004271980000000000007280594af10000000000000e4109084ee0000000000001c8006703cc00000000000039000425d9800000000000072000842770000000000000e4001084e60000000000001c8002100cc00000000000038b001233b800000000000070c00243f70000000000000e0800587ee000000000000120007d0ddc000000000000240007783b80000000000004160024677
|6=>0x404137484ee00000000000080020c009dc000000000000c00480637b80000000000012241704677000000000000244820381e600000000000048904013ecc00000000000091208025d980000000000012160024677000000000000215002284ee000000000000428000301dc000000000000818c09233b800000000000102c1594af700000000000020500a295ee000000000000408210909dc000000000000810038233b80000000000010200024277000000000000204000084ee0000000000004041e0339dc00000000000080400023fb800000000000100380066f7000000000000200022385ee00000000000040004012fdc00000000000080001031bb80000000000010000006bf70000000000001e4101185ee0000000000003c820210fdc000000000000600407217b8000000000000a63800c6f700000000000014470018dee000000000000280e0131bdc000000000000481c04637b8000000000000807b06d236
|7=>0x8904488acee00000000000110209157bdc000000000002201d022b3b8000000000004400215d0f60000000000008800408bf6c00000000000110008116ed8000000000002200102293b8000000000004008400d2f7000000000000700126087ee000000000000c8924c109dc000000000001858c08233b80000000000030a081246770000000000005e4105082e6000000000000b0020b9055c00000000000140249320bb0000000000002800e3073f70000000000005001c4062ee000000000000a0026e90fdc00000000000140041821fb800000000000280082e7157000000000000480107c84ee00000000000089820c10bdc000000000001110418297b800000000000220083442f700000000000043234208cee00000000000084020e10bdc000000000001050708393b8000000000002095b0652660000000000004123f0084cc0000000000008203e4109dc0000000000010404cd213b80000000000020808104277
|8=>0x200080aaf5aa0000000000040010017cbdc000000000008002002382b80000000000100040047007000000000002000080187ee000000000003100095749d0000000000004811020233b8000000000009000151c277000000000001080806084ee00000000000210002c909dc00000000000420002fe12a800000000000840005f4f7700000000000104800608cee00000000000209000c109dc000000000004081120233b8000000000008006346467700000000000100043948cc60000000000020008139d91c000000000004000328d93a80000000000080004d9e25500000000000100000bfe4aa000000000001e48288005dc00000000000360051228bb0000000000006400a345277000000000000b24140087ee0000000000014f808450ddc0000000000029b0520213b80000000000051382000e37000000000000a24040004ee0000000000014480800009c00000000000282400029fb8000000000004c00a0452f7
|9=>0x8080001c94ee00000000001009820c10fdc0000000000200003003d3b80000000000390200516f7700000000000520400a69fee00000000000a09801453fdc00000000001410002aa7fb80000000000281002514ff70000000000050040ca2feee00000000000a0001365bddc000000000014000028a7fb80000000000210081414ef70000000000040e500929dee0000000000080030d1d3bdc000000000010004320bf7b80000000000180060447647000000000002704104042ee000000000004a012091c55c00000000000904240a393b8000000000011820800e2f70000000000023041000c7ee000000000004498210189dc000000000008930000f17b8000000000011260000627700000000000220700005c6e00000000000440a0144abd4000000000008810000113b800000000001102000020370000000000022040000404e0000000000040230075c9dc00000000000804600ab82b800000000001000407c7277
|10=>0x2104c108084ee000000000042001270909dc00000000008289013007ba80000000001010200604f770000000000200e400d09ee200000000004009801813ddc00000000008010003227bb80000000001001002604f7700000000002002000d09eee000000000040003060929dc0000000000800021b327bb80000000001000004e86f5500000000002000003d49eee00000000004000001813ddc00000000006080440061fb80000000000c070480242f7000000000018081900587ee00000000003009220010bdc00000000006000644161fb80000000000900050047677000000000010080201cecee000000000020080a0031fdc000000000040002883233b8000000000080002800c7f700000000001000050018dee0000000000200005801d9dc0000000000222001022d3b80000000000430007904277000000000008400862ca4ee000000000010800004109dc000000000020980241293b800000000004040000e7a77
|11=>0x8004c000084ee000000000100000000109dc0000000001c0209041233b8000000000380312002467700000000007004e40008cee0000000000e0094800119dc0000000001c0100000233b8000000000294140000567700000000005224c2000ccee0000000000a14d8480119dc000000000142102802233b800000000028400040052770000000000502e081048cee0000000000a0408400919dc000000000140390804233b8000000000280404082427f00000000005004800008cee0000000000a0050000119dc000000000140080a44333b80000000002800010004677000000000049090016484ee0000000000920b800c109dc000000000124140018213b8000000000241200010427700000000004005e10608cee0000000000540021001e9dc0000000000a01040002d3b800000000011800044072770000000000228284020a4ee0000000000444080180bdd4000000000086000720293b80000000001084048464277
|12=>0x40840c0c20e4ee000000000810101000909dc000000001020130000213b800000000104240001e7277000000000202400907ce5ee0000000004042012039cbdc000000000808003c073b7b8000000001000c0380ef6f700000000020008000fce4ee0000000002200014c1919dc00000000040104ad8b2b3b8000000000802084b164677000000000100002b62c8cee0000000002000050c1b3bdc0000000004000025a3213b800000000080000430652770000000000d004c00008cee0000000001a0000000119dc0000000002a0184001253b80000000005400080004a770000000000a30c0108884ee000000000146088010189dc000000000284290024213b800000000050850084842770000000000a104c108084ee00000000014014a002129dc000000000268300402217b80000000004d030080062f70000000000980a0101085ee00000000013009220030fdc000000000204294004a13b80000000004003000024277
|13=>0x205004c000084ee0000000031920b800c109dc000000006324120000213a800000000c2402400004277000000001818048100084ee000000002810098000109dc0000000023c0129000233b800000000464224000042770000000008a804d000094ee000000001142098210109dc000000002284120420213b80000000044c0a6080042f500000000088004c000084ee000000001100090000109dc0000000021c0129000233b80000000042810041004677000000000848840802884ee000000001051083001129dc0000000020a0806080253b80000000041402480004a77000000000821240108484ee000000001042401250109dc000000002084120420213b80000000041080008404277000000000818a40140085ee000000001022403040509dc000000002000120000213b8000000002052600014427700000000040a0000800a4ee000000000811410000149dc000000001021120000213b80000000020422000004277
|14=>0x14008000104086ee00000002800000200070bdc000000048320130000213b800000008c2482c003042770000000100cb8280020a4ee0000000201960c0000189dc000000040324280004213b800000008064800000042770000000100400d2100084fe0000000200041a000d109dc0000000400081c0018313b800000008000008003042770000000098f004e60008cee0000000130e0098000109dc0000000223c0120000213b8000000040004216004467700000000800024260148cee000000010000004800119dc00000001a26053440061fb80000000344c02688004277000000004898149100187ee000000009030092200109dc000000010260520400217b8000000020010600004c3f7000000004000160000587ee00000000800000000030fdc00000000c324130000213b8000000018000a60000c3f700000000300005c004084ee00000000503009a200109dc0000000083c0120000213b80000000106482400004277
|15=>0x10800004a40008cee000000208024100a01309dc000000410040281404613b80000008200005080084ff70000001020f004c000084ee0000002030e0094800119dc0000004003c8300002213b800000080001031200066770000001000000a240108cee000000200000094c00119dc0000004000000a98002b3b800000040028000118a46770000000800000100c22e7ee0000001000000001801c9dc0000002000000000c5e17b80000002000010820506677000000040000204000497ee0000000800000a0815119dc000000100000130038233b80000002000001002004bf7000000040000010002287ee00000004f13009a20030fdc00000009e26011440061fb80000001304c0268800c3f700000002400004c000187ee00000004800009200030fdc00000008826012440061fb80000001040c00088004277000000020098049100084ee000000040030000200109dc00000008000052000061fb80000000c02002908004277
|16=>0xc000001e0900484ee00000180000029820010bdc000003000000510400297b8000006000000a0080442f7000000c00000100100085ee00000080000068924010bdc000000c00100148400213b80000011000440048244377000000220008200924086ee00000044000242104450fdc000000846124170018213b8000001084648240000427700000021004904c002084ee0000004200020a000c109dc00000082010084a480213b8000001040200090800427700000020800184080e884ee00000041000200001c109dc000000806325170018213b800000100c64826000042770000002008c9458006084ee000000401093480080109dc000000802126102002213b80000010000052802304277000000200000850806884ee00000040000042104c109dc000000800000040018213b8000000978080262800c7f70000001100030c000e88cee0000002200060c001c189dc00000044000428003c233b80000008800080000704677
|17=>0x2000800a080000e4ee000004001001410000149dc0000080000a80a40002d3b800001000010d04084052770000020000020280000a4ee000002400092481000909dc0000044083c0382081213b80000088007807000024277000001020818341900587ee0000020241929e104c909dc000004048324382081213b80000080806487000024277000001008870242e0048cee0000020080301c2200909dc0000040021c0909001233b800000800414120c00a4a77000001000828241800494ee000002001042481212909dc000004002084902421213b800000800400120400a4277000001000800240800484ee0000020001300c2200b0fdc000004000084980461293b800000800010930084242770000010000002600104a4ee0000020000004c0000909dc000004000000380001213b8000006400000800e0072f7000000c000021601000c5ee000001800001610200149dc000003000000c02480217b800000600000180080062f7
|18=>0x20000005020022008cee000400000000400250109dc000800000000800080213b8000c00000000200000527700010000288004c000084ee000200003100098000109dc000210806125170018213b8000200000400720008427700003000302004e00019dee000010c200820b800c109dc000021800102900100213b800004300020420400442770000084100400a0001084ee000010820080000000109dc000021000104840019213b80000404000400006007a770000080000080200910d4ee000008001000489040109dc00000c000084980661293b800001800000130048252770000021000720280000a4ee0000040430316122003cfdc000008086062824400393b80000101040c504880052770000020120cb8280400a4ee0000040130e1414c001d9dc0000080221c28298002b3b80000100042490c00305277000002000828a090000f4ee000004001051412000169dc000008002086820420393b800001000410d0408405277
|19=>0x200000000800200820084ee302010800080101005909dc4000000400040c0018213b8200001000205090800427704000000002004241008cfe0400020000304c2320909dc08000080002280041021bb8100000800090102800c2770200000200002090001c7ee040000001031412200109dc08000000006a004600293b8100000000080202c80c27f01c0001000f000260008cee020000000100140002109dc00c00000000020245121bb8010000100000208000c3f7002000004000061020187ee0040000001301c2200109dc008000000060980400213b80100000000c040c8824277001008400040260000084ee0020004000020a000c109dc0040000400040420d9213b800800004020029480042770010000040080c0104086ee0020000001921c0000109dc004000000004202079213f80050100002400400105277000a000004084080020a4ee00088000c13029a20030fdc000820000020800080253b800100020000108011143f7
|20=>0x1000001200804180001109de000002001000130000233ba0000000040042040044277
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>2
|8,0=>0x4011000010bc0e000040a0210100408c0a048190300907c0b00c1b
|9,0=>0x4b1253704c9e120140c0a13b10b0a89a1984209c5034cb13803325ce514caa3ec4314467390452c06816d1f14420170601049406c2d0c8ba0582e154cf0544620cda0f063350c00fc220d43d37d1d078640703b09503490d6194850e4bb134170989b2f1264083118925378fc090a648c1811099178ac470d111d0e074a7
|10,0=>0x41829571693ac2c1c0cd51d2966108480f3748b47a94b1389c2fdc24c4ae65c6d544e21587e74d816e18632cb52dcef2f9bf4b10d1fdc55e4f03a496148f6664613e9fb339074404c7ccc7650e315d191d8b654d434ac59450f4204fe1ac695948b6d1045215d35d8a508c664c582cc845519f325302e127681921b8f25888236cd5455c043cb94b5b6365cd655ef424e16f11a66d893d4a21b0bd484ad0d15b
|10,1=>0x1cc8f204387a48070d321a93b228370e85f1e4926f52e3fd2247890501ba704c33f4ee4d9bb2a53c3c46d70cdc1ec747c46d0f90a4cc5a775554312f
|11,0=>0x7d2517b9684f91b526213dd4e731185ade15ee40675117e5af5f13d77141219a1805a79425c82976981056d9ae9261f668a45924a6896d935f81c9c95de351f4784aa087f62e73dbe6c5b9744a5711b739a3d83ddb1d4ea889da7fd738d9ec7dd718315627cab39c8980e15375f59221458e1152a2d9198d599d58353f766185f44f6f8c893a4788c8768516515fe281a179c4a8d18228c06511015196e678e8
|11,1=>0x13a7a13957d5e069610205d61e6255d5a7221e4e1d6565b572d846221360d6a69a596b575536167a98b8907724d4f218d8614986adac85e099116095e4363e3145e3c246073140f3e1aa44d964019171d7234a2a5e239916427c20b305585d229819b67f1cd3108c7d9e5692378124f3297a531a98c1507e9ed875d0331b3869b003641672584d2385bc88309e81ea338bc8e59e0268d12
|12,0=>0x5fdb29c88d1f09d9fd903420e89db3801a58fe74a05a876228814718fa5496c0786e66931ca1bd288b1e49dd358ca792a27d79a2b77e6f8821b3b67b7398e9aa7e0adeba09f299e25a021e9a66c9865a8663b84a75102782be689da10871d79923a6027378c9571a559ba539c27a3e5709f1c69c4b292d8c781de98c8a151d49944054a5f95a5e
|13,0=>0x8a1e6261b66b9480578a6d9757e5b036
|14,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 10 (j%128);fld (pmP (k/32)) 91 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_127 12 roots_127 ops++addP pm 2 dom_191 12 roots_191 ops++addP pm 3 dom_207 10 roots_207 ops++addP pm 4 dom_253 12 roots_253 ops++addP pm 5 dom_251 12 roots_251 ops++addP pm 6 dom_247 12 roots_247 ops++addP pm 7 dzo_253_2 10 roots_253 ops++addP pm 8 dzo_245_2 9 roots_245 ops++addP pm 9 dom_223 12 roots_223 ops++addP pm 10 dzo_223_32 10 roots_223 ops++addP pm 11 dom_221 10 roots_221 ops++addP pm 12 dzo_191_64 10 roots_191 ops++addP pm 13 dom_190 10 roots_190 ops++addP pm 14 dom_239 12 roots_239 ops++addP pm 15 dzo_221_2 9 roots_221 ops++addP pm 16 dom_245 10 roots_245 ops++addP pm 17 dzo_239_16 10 roots_239 ops++addP pm 18 dom_175 10 roots_175 ops++addP pm 19 dom_238 10 roots_238 ops++addP pm 20 dzo_247_8 10 roots_247 ops++addP pm 21 dzo_245_8 9 roots_245 ops++addP pm 22 dom_215 10 roots_215 ops++addP pm 23 dzo_175_16 9 roots_175 ops++addP pm 24 dom_235 10 roots_235 ops++addP pm 25 dom_187 10 roots_187 ops++addP pm 26 dzo_175_64 9 roots_175 ops++addP pm 27 dzo_213_2 8 roots_213 ops++addP pm 28 dom_95 9 roots_95 ops++addP pm 29 dzo_221_32 9 roots_221 ops++addP pm 30 dzo_238_16 9 roots_238 ops++addP pm 31 dzo_125_2 9 roots_125 ops++addP pm 32 dzo_215_32 9 roots_215 ops++addP pm 33 dom_250 9 roots_250 ops++addP pm 34 dzo_186_64 8 roots_186 ops++addP pm 35 dzo_215_8 9 roots_215 ops++addP pm 36 dzo_171_16 8 roots_171 ops++addP pm 37 dzo_234_16 8 roots_234 ops++addP pm 38 dzo_235_16 9 roots_235 ops++addP pm 39 dom_125 9 roots_125 ops++addP pm 40 dzo_174_16 8 roots_174 ops++addP pm 41 dom_119 9 roots_119 ops++addP pm 42 dzo_190_64 9 roots_190 ops++addP pm 43 dzo_119_8 9 roots_119 ops++addP pm 44 dzo_187_64 9 roots_187 ops++addP pm 45 dom_213 8 roots_213 ops++addP pm 46 dzo_117_2 8 roots_117 ops++addP pm 47 dzo_93_2 8 roots_93 ops++addP pm 48 dzo_95_32 9 roots_95 ops++addP pm 49 dzo_87_8 8 roots_87 ops++addP pm 50 dom_123 9 roots_123 ops++addP pm 51 dom_171 8 roots_171 ops++addP pm 52 dom_174 8 roots_174 ops++addP pm 53 dzo_87_32 8 roots_87 ops++addP pm 54 dom_126 9 roots_126 ops++addP pm 55 dzo_254_1 8 roots_254 ops++addP pm 56 dzo_251_4 8 roots_251 ops++addP pm 57 dom_249 10 roots_249 ops++addP pm 58 dom_222 10 roots_222 ops++addP pm 59 dom_243 10 roots_243 ops++addP pm 60 dom_252 10 roots_252 ops++addP pm 61 dom_85 7 roots_85 ops++addP pm 62 dom_170 7 roots_170 ops++addP pm 63 dom_219 10 roots_219 ops++addP pm 64 dom_246 10 roots_246 ops++addP pm 65 dzo_117_8 8 roots_117 ops++addP pm 66 dzo_93_32 8 roots_93 ops++addP pm 67 dom_111 9 roots_111 ops++addP pm 68 dom_63 9 roots_63 ops++addP pm 69 dzo_238_1 7 roots_238 ops++addP pm 70 dzo_213_8 8 roots_213 ops++addP pm 71 dom_217 7 roots_217 ops++addP pm 72 dom_220 7 roots_220 ops++addP pm 73 dzo_235_4 7 roots_235 ops++addP pm 74 dzo_190_1 7 roots_190 ops++addP pm 75 dom_122 6 roots_122 ops++addP pm 76 dzo_171_64 8 roots_171 ops++addP pm 77 dzo_187_4 7 roots_187 ops++addP pm 78 dzo_174_64 8 roots_174 ops++addP pm 79 dom_231 10 roots_231 ops++addP pm 80 dom_237 10 roots_237 ops++addP pm 81 dzo_186_4 6 roots_186 ops++addP pm 82 dzo_171_4 6 roots_171 ops++addP pm 83 dzo_234_4 6 roots_234 ops++addP pm 84 dom_189 10 roots_189 ops++addP pm 85 dom_159 10 roots_159 ops++addP pm 86 dom_167 8 roots_167 ops++addP pm 87 dom_183 10 roots_183 ops++addP pm 88 dzo_234_1 6 roots_234 ops++addP pm 89 dzo_174_1 6 roots_174 ops++addP pm 90 dzo_213_32 8 roots_213 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54|h55|h56|h57|h58|h59|h60|h61|h62|h63|h64|h65|h66|h67|h68|h69|h70|h71|h72|h73|h74|h75|h76|h77|h78|h79|h80|h81|h82|h83|h84|h85|h86|h87|h88|h89|h90
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_253_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_245_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_223_32_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_191_64_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_221_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_239_16_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_247_8_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_245_8_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_175_16_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_175_64_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_213_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_221_32_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_238_16_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_125_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_215_32_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_186_64_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_215_8_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_171_16_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_234_16_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_235_16_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_174_16_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_zo_190_64_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_zo_119_8_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_zo_187_64_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_zo_117_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_zo_93_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_zo_95_32_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_zo_87_8_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h52;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h53;exact cpcs (by decide +kernel) lowS_zo_87_32_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h54;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h55;exact cpcs (by decide +kernel) lowS_zo_254_1_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h56;exact cpcs (by decide +kernel) lowS_zo_251_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h57;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h58;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h59;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h60;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h61;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h62;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h63;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h64;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h65;exact cpcs (by decide +kernel) lowS_zo_117_8_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h66;exact cpcs (by decide +kernel) lowS_zo_93_32_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h67;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h68;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h69;exact cpcs (by decide +kernel) lowS_zo_238_1_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h70;exact cpcs (by decide +kernel) lowS_zo_213_8_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h71;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h72;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h73;exact cpcs (by decide +kernel) lowS_zo_235_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h74;exact cpcs (by decide +kernel) lowS_zo_190_1_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h75;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h76;exact cpcs (by decide +kernel) lowS_zo_171_64_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h77;exact cpcs (by decide +kernel) lowS_zo_187_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h78;exact cpcs (by decide +kernel) lowS_zo_174_64_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h79;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h80;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h81;exact cpcs (by decide +kernel) lowS_zo_186_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h82;exact cpcs (by decide +kernel) lowS_zo_171_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h83;exact cpcs (by decide +kernel) lowS_zo_234_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h84;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h85;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h86;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h87;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h88;exact cpcs (by decide +kernel) lowS_zo_234_1_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h89;exact cpcs (by decide +kernel) lowS_zo_174_1_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h90;exact cpcs (by decide +kernel) lowS_zo_213_32_85 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 1000003 zs symsG zs (hk 1000003 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 1000003 ys h symsG ys (hk 1000003 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 1000003 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 22 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 22 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 101 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 101 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 176 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 48 128 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 176 → Z 10 i = true := (range_split z10_0 z10_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11_0 : ∀ i, 0 ≤ i → i < 128 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11_128 : ∀ i, 128 ≤ i → i < 249 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 121 128 = true)
private theorem z11 : ∀ i, 0 ≤ i → i < 249 → Z 11 i = true := (range_split z11_0 z11_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 108 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 108 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z13 : ∀ i, 0 ≤ i → i < 13 → Z 13 i = true := span_ok (by decide +kernel : span (Z 13) 13 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z14 : ∀ i, 0 ≤ i → i < 1 → Z 14 i = true := span_ok (by decide +kernel : span (Z 14) 1 0 = true)
theorem checked (s:Nat) (hs:s≤14):∀ i<NN s,bar dom_255 gM mpG SD SS NN hAt idxH ori 1000003 mkCut s i=true:=by
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
  · exact z14 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 8 7=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤14) (h:RunD true dom_255 gM s xsM):False:=by
  have hmin:7≤s:=by have hl:=run_len h;change 8≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_255 roots_255 goal_255 15:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_255
theorem lowS_255:Lower true dom_255 roots_255 goal_255 15:=S_255.noCircuit
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
    (hhas : ∃ g ∈ gates, isNotGate g = true) : 16 ≤ gates.length := by
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [4, 6] }, { op := GateOp.or, inputs := [9, 7] }, { op := GateOp.and, inputs := [8, 10] }, { op := GateOp.or, inputs := [1, 3] }, { op := GateOp.or, inputs := [5, 7] }, { op := GateOp.and, inputs := [12, 13] }, { op := GateOp.and, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 3] }, { op := GateOp.and, inputs := [4, 6] }, { op := GateOp.and, inputs := [5, 7] }, { op := GateOp.or, inputs := [11, 14] }, { op := GateOp.or, inputs := [19, 15] }, { op := GateOp.or, inputs := [20, 16] }, { op := GateOp.or, inputs := [21, 17] }, { op := GateOp.or, inputs := [22, 18] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 23⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  have hwit : (execN witGates xs256).getD 23 0 &&& mask256 = goal_255 &&& mask256 := by decide +kernel
  intro x
  have hlt : natOfBits8 x < 256 := natOfBits8_lt x
  have hpt : pt8 (natOfBits8 x) = x := pt8_natOfBits8 x
  generalize hr : natOfBits8 x = r at hlt hpt
  have h1 := execN_bit witGates xs256 r hlt (fun g hg => by
    have hm := wit_mono g hg
    rcases hm.1 with h | h <;> simp [h])
  have h2 := congrArg (fun l => l.getD 23 false) h1
  rw [xs256_bits ⟨r, hlt⟩, hpt] at h2
  have hgd : ((execN witGates xs256).map (·.testBit r)).getD 23 false =
      ((execN witGates xs256).getD 23 0).testBit r := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (execN witGates xs256)[23]? with | none => simp | some v => rfl
  rw [hgd] at h2
  have hbit : ((execN witGates xs256).getD 23 0).testBit r = goal_255.testBit r := by
    have hb := congrArg (fun v => v.testBit r) hwit
    simp only [Nat.testBit_and, mask256_bit, hlt, decide_true, Bool.and_true] at hb
    exact hb
  have hres := h2.symm.trans (hbit.trans (goal_eq_f ⟨r, hlt⟩))
  rw [hpt] at hres
  exact hres

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfan _h1not hev
  by_cases hhas : ∃ g ∈ gates, isNotGate g = true
  · have hfan' : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨h1, h2⟩ := hfan g hg
      refine ⟨?_, h2⟩
      rcases h1 with h1 | h1 | h1 <;> simp [h1]
    have hlb : 16 ≤ gates.length := lb_with_not gates o hfan' hev hhas
    refine ⟨witGates, 23, wit_mono, ?_, wit_eval⟩
    have hlen : witGates.length = 16 := rfl
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

end PEqualNP.Outside.L_meta_52158_aux

theorem PEqualNP.Outside.L_meta_52158 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52158_aux.main
