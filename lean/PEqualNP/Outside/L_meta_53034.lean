import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_53034_aux
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

def dom_74 : Nat := 0x5050000000000000505
def goal_74 : Nat := 0xffccffccffccffcccc00cc00cc00cc00ffccffccffccffcccc00cc00cc00cc00
def roots_74 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffeeffeeffeeffeecc00cc00cc00cc00ffeeffeeffeeffeecc00cc00cc00cc00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfffefffefffefffeeca0eca0eca0eca0fffefffefffefffeeca0eca0eca0eca0
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_81 : Nat := 0x300030000000000030003
def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffeeeeffffeeeeeeee0000eeee0000ffffeeeeffffeeeeeeee0000eeee0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_84 : Nat := 0x1100110000000000110011
def goal_84 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_84 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffffafafffffafafafaa0a0fafaa0a0fffffafafffffafafafaa0a0fafaa0a0
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffefefffffefefefea0a0fefea0a0fffffefefffffefefefea0a0fefea0a0
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffffaaffffffaaaaaa0000aaaa0000ffffffaaffffffaaaaaa0000aaaa0000
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffffccffffffcccccccc00cccccc00ffffffccffffffcccccccc00cccccc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffeeffffffeeeeeecc00eeeecc00ffffffeeffffffeeeeeecc00eeeecc00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfffffff0fffffff0f0f00000f0f00000fffffff0fffffff0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffffafffffffafafaa0a0fafaa0a0fffffffafffffffafafaa0a0fafaa0a0
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffffcfffffffcfcfccc00fcfccc00fffffffcfffffffcfcfccc00fcfccc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffffefffffffefefeeca0fefeeca0fffffffefffffffefefeeca0fefeeca0
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfafafafafafafafafafafafaa0a0a0a0fafafafafafafafafafafafaa0a0a0a0
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefefefefefefefefefea0a0a0a0fefefefefefefefefefefefea0a0a0a0
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccffccffccffccffcccc00cc00ffccffccffccffccffccffcccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeffeeffeeffeeffeecc00cc00ffeeffeeffeeffeeffeeffeecc00cc00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffafffafffafffafffaa0a0a0a0fffafffafffafffafffafffaa0a0a0a0
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfffcfffcfffcfffccc00cc00fffcfffcfffcfffcfffcfffccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefffefffefffefffeeca0eca0fffefffefffefffefffefffeeca0eca0
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffaaaaffffaaaaaaaaaaaaaaaa0000ffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffccccffffcccccccccccccccc0000ffffccccffffcccccccccccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffeeeeeeeeeeeeeeee0000ffffeeeeffffeeeeeeeeeeeeeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffff0f0fffff0f0f0f0f0f0f0f00000fffff0f0fffff0f0f0f0f0f0f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafafffffafafafafafafafaa0a0fffffafafffffafafafafafafafaa0a0
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcfffffcfcfcfcfcfcfcfc0000fffffcfcfffffcfcfcfcfcfcfcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefefffffefefefefefefefea0a0fffffefefffffefefefefefefefea0a0
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffff00ffffff00ff00ff0000000000ffffff00ffffff00ff00ff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffffaaffaaffaaaaaa0000ffffffaaffffffaaffaaffaaaaaa0000
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffffccffccffcccccccc00ffffffccffffffccffccffcccccccc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffffeeffeeffeeeeeecc00ffffffeeffffffeeffeeffeeeeeecc00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0fffffff0fff0fff0f0f00000fffffff0fffffff0fff0fff0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffffafffafffafafaa0a0fffffffafffffffafffafffafafaa0a0
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcfffffffcfffcfffcfcfccc00fffffffcfffffffcfffcfffcfcfccc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffffefffefffefefeeca0fffffffefffffffefffefffefefeeca0
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_133 : Nat := 0x3300000000000000000000000000000033
def goal_133 : Nat := 0xfafafafafafafafafafafafafafafafaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def roots_133 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 7 0]

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

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaeeee0000eeee0000eeee0000eeee0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafafafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffafafffffafafffffafafffffafafefea0a0fefea0a0fefea0a0fefea0a0
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

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

def dom_161 : Nat := 0x30000000300000000000000000000000300000003
def goal_161 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_164 : Nat := 0x110000001100000000000000000000001100000011
def goal_164 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_164 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfffffffffafafafafffffffffafafafafafafafaa0a0a0a0fafafafaa0a0a0a0
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffff00ff00ffffffffff00ff00ffccffcccc00cc00ffccffcccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffeeffeecc00cc00ffeeffeecc00cc00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffafffafffaa0a0a0a0fffafffaa0a0a0a0
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fffcfffccc00cc00fffcfffccc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffafffafffffffffffafffafffefffeeca0eca0fffefffeeca0eca0
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffffaaaaffffffffffffaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffaaaaffffffffffffaaaaeeeeeeeeeeee0000eeeeeeeeeeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f0f0f0f0f00000f0f0f0f0f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffffffafafffffffffffffafafafafafafafaa0a0fafafafafafaa0a0
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fcfcfcfcfcfc0000fcfcfcfcfcfc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffafafffffffffffffafafefefefefefea0a0fefefefefefea0a0
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

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

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0fff0fff0f0f00000fff0fff0f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffffafffffffffffffffafffafffafafaa0a0fffafffafafaa0a0
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffff0fffffffffffffff0fffcfffcfcfccc00fffcfffcfcfccc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffafffffffffffffffafffefffefefeeca0fffefffefefeeca0
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_193 : Nat := 0x3000000000000000300000000000000030000000000000003
def goal_193 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000
def roots_193 : List Nat := [xs256.getD 0 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfffffffffffffffffafafafafafafafafafafafafafafafaa0a0a0a0a0a0a0a0
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaa0000000000000000
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffff00ff00ff00ff00ffccffccffccffcccc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffeeffeeffeeffeecc00cc00cc00cc00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffafffafffafffafffefffefffefffeeca0eca0eca0eca0
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffffff0000ffff0000ffffccccffffcccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffeeeeffffeeeeeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffffafafffffafafffffafafffffafafafaa0a0fafaa0a0
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffafafffffafafffffefefffffefefefea0a0fefea0a0
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaaaaa0000aaaa0000
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffff00ffffff00ffffffccffffffcccccccc00cccccc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffeeffffffeeeeeecc00eeeecc00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffffafffffffafffffffafffffffafafaa0a0fafaa0a0
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffff0fffffff0fffffffcfffffffcfcfccc00fcfccc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffafffffffafffffffefffffffefefeeca0fefeeca0
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffffffffffafafafafafafafafafafafafafafafaa0a0a0a0
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffaaffaaffeeffeeffeeffeeffeeffeecc00cc00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffffffffff0fff0fffcfffcfffcfffcfffcfffccc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffafffafffefffefffefffefffefffeeca0eca0
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffffffffffffffffffff0000ffff0000ffff00000000000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffffffffffff0f0fffff0f0fffff0f0f0f0f0f0f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffffffafafffffafafffffafafafafafafafaa0a0
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffffffafafffffefefffffefefefefefefefea0a0
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffffffaaffffffaaffffffaaffaaffaaaaaa0000
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffffff00ffffffccffffffccffccffcccccccc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffffaaffffffeeffffffeeffeeffeeeeeecc00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffffffafffffffafffffffafffafffafafaa0a0
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffffff0fffffffcfffffffcfffcfffcfcfccc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffffffafffffffefffffffefffefffefefeeca0
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
def isoMvS_74:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_74:Lower true dom_74 roots_74 goal_74 4:=lower_iso_b isoMvS_74 (by decide +kernel) lowS_21
def isoMvS_81:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_21
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_21
def isoMvS_133:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_133:Lower true dom_133 roots_133 goal_133 4:=lower_iso_b isoMvS_133 (by decide +kernel) lowS_21
def isoMvS_161:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_161:Lower true dom_161 roots_161 goal_161 4:=lower_iso_b isoMvS_161 (by decide +kernel) lowS_21
def isoMvS_164:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_164:Lower true dom_164 roots_164 goal_164 4:=lower_iso_b isoMvS_164 (by decide +kernel) lowS_21
def isoMvS_193:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_193:Lower true dom_193 roots_193 goal_193 4:=lower_iso_b isoMvS_193 (by decide +kernel) lowS_21
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
|0,0=>0x33003300000000003200324400440000000000440000000320000000000000032cc00880000000000cc00880003300000000000000300000000000000000c800c9100110000000000110010c000c00000000000c00083000300000000000300030cc00000000000000cc0003300330000000000000000cc00c00000000000cc00c3300330000000000330000cc00cc0000000000c000c2200220000000000220022
|_,_=>0
def sP:Nat→Nat
|0=>0x5604356042560456045e604560d4560c43b60435104560a42516059604568457043210
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
|0=>0x6555150559645956455164551
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
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_23
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_53
def isoMvS_89:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_23
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_53
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 5:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_23
def isoMvS_101:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 5:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_53
def isoMvS_106:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_53
def isoMvS_113:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_23
def isoMvS_114:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_23
def isoMvS_116:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_23
def isoMvS_120:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 4:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_27
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 4:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_27
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 4:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_27
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_23
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 7:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_85
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_23
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 7:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_85
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_53
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_53
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_53
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 5:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_23
def isoMvS_195:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_23
def isoMvS_197:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 7:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_85
def isoMvS_201:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_53
def isoMvS_202:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_53
def isoMvS_209:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 7:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_85
def isoMvS_210:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_53
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 7:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_85
def isoMvS_216:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 5:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_53
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 5:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_53
def isoMvS_228:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 5:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_53
def isoMvS_240:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_240:Lower true dom_240 roots_240 goal_240 5:=lower_iso_b isoMvS_240 (by decide +kernel) lowS_23
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
|0=>0x1f41c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x53
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_23 5 roots_23 ops++addP pm 1 dom_30 4 roots_30 ops++addP pm 2 dzo_23_8 5 roots_23 ops++addP pm 3 dom_27 4 roots_27 ops++addP pm 4 dom_21 4 roots_21 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_31 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_23 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_23_8_21 _ g hchk
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
|0=>0x3ff7adf590c286080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40028135
|6,0=>0x697a
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_46 5 roots_46 ops++addP pm 1 dom_42 4 roots_42 ops++addP pm 2 dom_39 5 roots_39 ops++addP pm 3 dom_37 4 roots_37 ops++addP pm 4 dom_43 5 roots_43 ops++addP pm 5 dom_45 5 roots_45 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_47 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_39 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_37 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_45 _ g hchk
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
namespace S_91
def pG:List (Nat×Nat):=[(1,17),(1,65),(2,10),(2,18),(2,66),(3,11),(3,19),(3,67),(8,10),(8,72),(9,11),(9,25),(9,73),(16,17),(16,18),(16,80),(24,25),(24,26),(24,88),(64,65),(64,66),(64,72),(64,80)]
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
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
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
theorem lowS_93:Lower true dom_93 roots_93 goal_93 8:=lower_slice_b [(0x330033000000000033003300,64,72)] (by decide +kernel) lowS_85
theorem lowS_181:Lower true dom_181 roots_181 goal_181 8:=lower_slice_b [(0x3300000033000000000000000000000033000000330000,1,17)] (by decide +kernel) lowS_165
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
def isoMvS_79:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_79:Lower true dom_79 roots_79 goal_79 8:=lower_iso_b isoMvS_79 (by decide +kernel) lowS_47
def isoMvS_94:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 7:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_91
def isoMvS_103:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_55
def isoMvS_107:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 6:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_55
def isoMvS_109:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 6:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_55
def isoMvS_110:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_55
def isoMvS_115:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 6:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_55
def isoMvS_117:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 8:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_87
def isoMvS_118:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 6:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_55
def isoMvS_121:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 6:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_59
def isoMvS_122:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_91
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 6:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_59
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 7:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_31
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 8:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_93
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 6:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_59
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 8:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_93
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 6:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_59
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 7:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_91
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_87
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 7:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_91
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 6:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_55
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 6:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_55
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 7:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_91
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 6:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_55
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 7:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_91
def isoMvS_203:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 7:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_91
def isoMvS_211:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 8:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_87
def isoMvS_217:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 8:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_87
def isoMvS_229:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 8:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_181
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 8:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_87
def isoMvS_244:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 8:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_87
theorem lowS_63:Lower true dom_63 roots_63 goal_63 9:=lower_slice_b [(0xffff0000ffff0000,1,17)] (by decide +kernel) lowS_47
namespace S_95
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,65),(2,10),(2,18),(2,66),(3,7),(3,11),(3,19),(3,67),(4,5),(4,20),(4,68),(6,7),(6,14),(6,22),(6,70),(8,10),(8,72),(9,11),(9,13),(9,25),(9,73),(12,13),(12,14),(12,28),(12,76),(16,17),(16,18),(16,20),(16,80),(24,25),(24,26),(24,28),(24,88),(64,65),(64,66),(64,68),(64,72),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_95.map (·&&&dom_95)
def gM:=goal_95&&&dom_95
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x28a88
|7,0=>0x47df241a713325e268f01a6c5
|8,0=>0x8047773606
|9,0=>0xc3264
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000fafafafa0f0f0f0f000000000a0a0a0af0f0f0f000000000f0f0f0f0aaaaaaaa00000000aaaaaaaaffffffff0000000000000000ffff000000000000ffff0000ff00ff0000000000ff00ff00fafafafa00000000fafafafaffffffff00000000f0f0f0f0cccccccc00000000ccccccccffffffff00000000aaaaaaaa
|_,_=>0
def sP:Nat→Nat
|0=>0x54817654810765438176542810754a8176543217654a281765481796543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d5736067
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 96 0xffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1d987619764d987619785c9866027661d865d9
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
|7,0=>0x3f72
|8,0=>0x14
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_93 8 roots_93 ops++addP pm 1 dom_94 7 roots_94 ops++addP pm 2 dom_91 7 roots_91 ops++addP pm 3 dom_31 7 roots_31 ops++addP pm 4 dom_79 8 roots_79 ops++addP pm 5 dom_87 8 roots_87 ops++addP pm 6 dom_27 4 roots_27 ops++addP pm 7 dom_30 4 roots_30 ops++addP pm 8 dom_90 5 roots_90 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_95 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_90 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_93 8 s (0,roots_93.map (·&&&dom_93)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_95 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_93 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_95==dom_95)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_95 gM v ys):RunD true dom_95 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_95 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_95 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_95 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_95 roots_95 goal_95 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_95
theorem lowS_95:Lower true dom_95 roots_95 goal_95 10:=S_95.noCircuit
theorem lowS_111:Lower true dom_111 roots_111 goal_111 9:=lower_slice_b [(0xffff000000000000ffff00000000,1,33)] (by decide +kernel) lowS_79
theorem lowS_119:Lower true dom_119 roots_119 goal_119 9:=lower_slice_b [(0xcc00cc00cc00cc00cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_117
namespace S_123
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(2,10),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(8,10),(8,40),(8,72),(9,11),(9,25),(9,41),(9,73),(16,17),(16,18),(16,80),(24,25),(24,26),(24,56),(24,88),(32,33),(32,34),(32,40),(48,49),(48,50),(48,56),(48,112),(64,65),(64,66),(64,72),(64,80),(96,97),(96,98),(96,104),(96,112)]
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
|5,0=>0xdea2e4ef2009085
|6,0=>0xca36c761a86878b3557719b80
|7,0=>0x7f4936900d4f9493cae4
|8,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f0f000f000f000f00f0f0f000f0f0f000f0f0f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0cf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cf0f0f0f0f0f0f0f0f0f0f0f0f000f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0e0e0e0e0e0e0e0ef0f0f0f000000000f0f0f0f00000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0000f0f00000f0f00000e0e00000e0ef0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f00000000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f00e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c
|_,_=>0
def sP:Nat→Nat
|0=>0x8327a583f27a58e327a54327a583207a543217543207ad4327a58c3215b4327a543291782176543210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x2d82b005
|6,0=>0x2b64ac79cc3117
|7,0=>0x8aef9dc3317
|8,0=>0x4c6
|_,_=>0
def wAt:=mkWire dB 16 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x9532615755e98561575615a74dd855e9
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x10000
|6,0=>0x7252412211
|7,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xa0020a0f5a5fd2de87f400c000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40
|6,0=>0x35af
|7,0=>0x6e3
|8,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_58 5 roots_58 ops++addP pm 2 dom_43 5 roots_43 ops++addP pm 3 dom_121 6 roots_121 ops++addP pm 4 dom_59 6 roots_59 ops++addP pm 5 dom_113 5 roots_113 ops++addP pm 6 dom_27 4 roots_27 ops++addP pm 7 dom_107 6 roots_107 ops++addP pm 8 dom_91 7 roots_91 ops++addP pm 9 dom_120 4 roots_120 ops++addP pm 10 dom_115 6 roots_115 ops++addP pm 11 dom_89 5 roots_89 ops++addP pm 12 dom_83 5 roots_83 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_83 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 7 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
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
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=lower_slice_b [(0x33003300330033003300330033003300,32,40)] (by decide +kernel) lowS_117
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_slice_b [(0xcccccccc000000000000000000000000cccccccc,8,10)] (by decide +kernel) lowS_157
theorem lowS_183:Lower true dom_183 roots_183 goal_183 9:=lower_slice_b [(0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_181
def dzo_181_8:=0x330033003300330000000000000000003300330033003300
def gzo_181_8:=0x330033003300330000000000000000003300330032002000
def gsh_181_8:=0x3300330033003300000000000000000033003300320020
theorem lowS_zo_181_8_21:Lower true dzo_181_8 roots_181 gzo_181_8 6:=lower_iso_b (d1:=dom_181) (r1:=roots_181) (T1:=gsh_181_8) [(dom_181,8)] (by decide +kernel) (lower_slice_b (T:=gsh_181_8) [(0x3300330000000000000000000000000033003300000000,0,32),(0x3300330033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
namespace S_189
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,129),(4,5),(4,20),(4,36),(4,132),(8,40),(8,136),(9,13),(9,25),(9,41),(9,137),(12,13),(12,28),(12,44),(12,140),(16,17),(16,20),(16,144),(24,25),(24,28),(24,56),(24,152),(32,33),(32,36),(32,40),(32,160),(48,49),(48,52),(48,56),(48,176),(128,129),(128,132),(128,136),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_189.map (·&&&dom_189)
def gM:=goal_189&&&dom_189
def NN:Nat→Nat
|5=>2
|6=>8
|7=>9
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x590de0d734
|6,0=>0xacc49a218a9f15691ccd7fb2771bdf369ea2cd74
|7,0=>0xf45fcd4727b7c578a3587880e5d236311e217fef14387
|8,0=>0xa1e989130f67cf5
|9,0=>0x3abd3
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c0c0c0c0c0c0c0000000000000000080808080808080b33333333333333300000000000000003232323232323232ccc0ccc0ccc0ccc00000000000000000ccc0ccc0ccc0ccc111011101110111000000000000000001110111011101110cc00cc00cc00cc000000000000000000cc00cc00cc00cc032323232323232320000000000000000323232323232323288888888888888880000000000000000888888888888888b33300003333000000000000000000003333000033330000ccc8ccc8ccc8ccc80000000000000000ccc8ccc8ccc8cccb33333333333333300000000000000003030303030303030cccccccc000000000000000000000000cccccccc0000000332233223322332200000000000000003322332233223322c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c3333333333333333000000000000000022222222222222220000cccc0000cccc00000000000000000000c8c80000c8cb33333333333333300000000000000000000000000000000
|0,1=>0x30203020302030200000000000000000302030203020302
|_,_=>0
def sP:Nat→Nat
|0=>0x58c490150d189202a069800a85a8620150b70c49015071a40542dc3480a8598624950b1a5e02a1a6480ab189210156e1a4202a0e3100a8218622ac69080a85a8c22a1ae324054192c01507308a418820
|1=>0x542c69015041a40542d43480a8
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x65006
|6,0=>0x3773072a62461e61861170b6
|7,0=>0x7476e66775f85965274b74473e6
|8,0=>0x8968277b7
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 17 190 0x3fffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x5a51a548148158d20f5a51a548118948120d5a518948118148118a48118158d43a1891894815a91a54814811815a543a1894811811a548158d4991811816a758d5a91811a5481
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0x609624cd0334ca31cc43
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xe75f3829d73ef675a3ad0c07fa2758fbc7d62fb17707f81d60c902000f8040000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40
|6,0=>0x184cc239a7
|7,0=>0xa43e499c570
|8,0=>0x21cb
|9,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_181 8 roots_181 ops++addP pm 1 dom_61 7 roots_61 ops++addP pm 2 dom_177 5 roots_177 ops++addP pm 3 dom_157 8 roots_157 ops++addP pm 4 dom_180 5 roots_180 ops++addP pm 5 dom_173 8 roots_173 ops++addP pm 6 dom_188 7 roots_188 ops++addP pm 7 dom_185 7 roots_185 ops++addP pm 8 dzo_53_8 5 roots_53 ops++addP pm 9 dzo_181_8 6 roots_181 ops++addP pm 10 dom_60 4 roots_60 ops++addP pm 11 dom_184 5 roots_184 ops++addP pm 12 dom_57 4 roots_57 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_189 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_53_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_181_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_57 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_181 8 s (0,roots_181.map (·&&&dom_181)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_189 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_181 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_189==dom_189)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_189 gM v ys):RunD true dom_189 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_189 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_189 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_215:Lower true dom_215 roots_215 goal_215 10:=lower_slice_b [(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,16,18)] (by decide +kernel) lowS_213
namespace S_219
def pG:List (Nat×Nat):=[(1,17),(1,65),(1,129),(2,10),(2,18),(2,66),(3,11),(3,19),(3,67),(3,131),(8,10),(8,72),(8,136),(9,11),(9,25),(9,73),(9,137),(16,17),(16,18),(16,80),(16,144),(24,25),(24,26),(24,88),(24,152),(64,65),(64,66),(64,72),(64,80),(64,192),(128,129),(128,136),(128,144),(128,192),(130,131),(130,138),(130,146),(130,194)]
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
|4,0=>0xcf44db542caaf80a3e999d2b88e3188d71379745720b56fe906b6cc4b3c343f9a427fa3702a369e2304671bda30c9aa07e8f0255f
|5,0=>0xd68c9ca59ab6390b4aedb1ac0b16a6ad15ba80839ffb49f8c69e2d1923ce8bc6f89eed856f38266f8223e7f4126ed226e32a65e8f64491548914e6ff4e6dd4b8dc477c74720145da741ef040a61408033f89a3a23e371ac34f1f32b63314e0308282ed602d7c02c2a32a9a929e8227b5d2599223554218881d24d1ab601a740180bf16d0a0e76b0e0d30a8520a334093c405c0f05af300da0
|6,0=>0xe803dc5c6ec22d0c0663b81b3b742faf0fba2735a102d919518d1b08a52d898c4836e87e26b7756f749f673565725d76f85f6ac4566be16610964357628296281b5db1a5cbd65c9e95ae8958ca8505805020b4d3004ca0f4c19b4a67d49d3f495fd4465d4385341bbe3eedd3b8913b883388cd34ecd33ef132e3630f3b303ed2f15a2ddcf2a64d268e92593e1b1dd17922135f612ad10d2870af0c0a31d09a90078f606fa10644f04dff031f200589
|7,0=>0xd639ece45dcbe3dc44abc40b0bdb87bc156b431ca6b66a5cada3ee3a1d0f9b2939836f967628b6d687c9e86b1d849ac7245e6dd916aacc69ff64f0014d18748f3d44b103dabc3bf933b20f38a15330222f5562c4ee221dd20d46204131da9d196d3163820e9ed0ab82047ea02ec40014c
|8,0=>0xc40b0b73348d2a572cb7619cd4b7f31da8f1ae0c0a8fd02a82
|9,0=>0xebdb4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f0f0f0f000000000f0f0f00000000000f0f0f00f0f0f0f000000000f0f0f00000000000c0c0c0c000000000c0c0c00f0f0f0f0000000000000000000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0000000000000f0f0e0e000000000f0f0000f0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f0000f0f0f00000000000f0f0f00000000000f0f0f00000000000c0c0c00f0f0f0f000000000f0f0f0f00000000000000000000000000000000f0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f00f0f000f000000000f0f0000000000000f0f000f000000000f0f0000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000f000f00000000000f000f00000000000f000f00000000000f000f00f0f0f0f000000000f0f0f0f000000000c0c0c0c000000000c0c0c0cf0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0af0f0f0f000000000f0f0f0f000000000e0e0e0e0000000000000000
|0,1=>0xf0f0f0f000000000f0f0f0f000000000f0f0f0a0000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f00005050505000000000505050500000000050505050000000005050000f0f0f0f000000000f0f0f0f000000000f0f0303000000000f0f0000f0f0f0f000000000f0f0f0f00000000030303030000000003030000f0f0f0f000000000f0f0f0f000000000f0f0c0c0000000000000000f0f0f0f000000000f000f00000000000f0e0f0e000000000f000f00c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0cf0f0f0f000000000a0a0a0a000000000f0f0f0a000000000a0a0a0af0f0f0f000000000f000f00000000000f0f0f0c000000000f000f00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000c0c0c0c000000f000000000000000f000000000000000f000000000000000cf0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000f0f0f0f000000000c0c0c0c000000000f0f0f0c000000000c0c0c0c00000000000000000000000000000000f0f0f0f000000000f0f0c0c0000000000000000f0f0f0f0000000000000000000000000f0f0c0c
|0,2=>0xa0a0a0f000000000a0a0a0a000000000a0a0a0f000000000a0a0a0a0000a0a0000000000000a0a0000000000000a0a0000000000000a0a303030300000000030303020000000003030303000000000303030230303010000000003030300000000000303030100000000030303003030300000000000303030000000000030303030000000003030300f0f0f0f000000000f0f0f0f00000000030303030000000003030300f0f0f0f0000000000000000000000000f0f0c0c0000000000000000f0f0f0f0000000000000000000000000e0e0e0e0000000000000000f0f0f0f000000000f0f0f0f000000000000000f0000000000000000f0f0f0f000000000f0f0f0f000000000f0f0c0c000000000f0f0c0c000000f0000000000000000000000000000000f0000000000000000000000f000000000000000f000000000000000f0000000000000000f0f0f0a000000000f0f0f0a000000000f0f0f0a000000000f0f0f0af0f0f0a0000000000000000000000000f0f0f0a0000000000000000f0f0f0e000000000c0c0c0c000000000f0f0f0e000000000c0c0c0cf0f0f0f000000000f0f0f00000000000f0f0f0f000000000f0f0f00
|0,3=>0xf0f0000000000000f0f0000000000000f0f0303000000000f0f00000000000000000000000000000000000030303030000000000000000f0f0505000000000f0f0500000000000f0f0505000000000f0f0500f0f0f0f0000000000000000000000000f0f0f0000000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000e0e00f000f00000000000f000f00000000000f000f00000000000f000c000000f000000000000000a000000000000000f000000000000000af0f000f000000000f0f000a000000000f0f000f000000000f0f000a505050500000000050505000000000005050505000000000505050000000000000000000000000000000000a0a0a0a000000000a0a0a0a00f000f00000000000f000f00000000000f000f00000000000c000c00000000000000000000000000000000f0f0f0f000000000e0e0e0e0000000000000000f0f0f0f0000000000000000000000000f0f0f00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0c0c0000000000000000000000000000000030303030000000003030300f0f0f0f000000000f0f0f0f00000000010101010000000000000000
|0,4=>0xf0f0000000000000a0a0000000000000f0f0000000000000a0af0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0af0f0f0f000000000f0f0f0f000000000d0d0d0d000000000c0c0c0c00000050000000000000000000000000000000500000000000000003030303000000000303030000000000030303030000000003030300f0f0f0f000000000f0f0f0f0000000000000f0f000000000000000050505050000000000000000000000000505050500000000000000000000f0f00000000000000000000000000000f0f0000000000000000f0f0f0f000000000f0f0a0a000000000f0f0f0f000000000f0f0a0af0f0f0f000000000f0f0f0f000000000e0e0e0e000000000e0e0e0ef0f0f0f000000000f0f0f0f000000000f0f0f0f000000000e0e0e0ef0f0000000000000f0f0000000000000f0f000f000000000f0f000000000000000000000000000000000000b0b0b0b000000000a0a0a0a0000000000000000f0f0f0a0000000000000000000000000f0f0f0a00000000000000000000000000000000f0f0f0f000000000f0f0f005050505000000000505050500000000050505050000000005050404
|0,5=>0xf0f0000000000000f0f0000000000000f0f0000000000000000f0f0f0f0000000000000000000000000f0f0f0f000000000a0a0a0a00000000000000000000000000000000000000f00000000000000005050505000000000505050500000000050505050000000004040404000000000000000000000000000000003030303000000000303000000000000000000000000000000000000303030300000000020202020000000000000000a0a0a0a0000000000000000000000000a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0a00000000000000000000000000000000f0f0f0f000000000a0a0a0af0f0f0f000000000f0f0f0f000000000a0a0a0a0000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f00f0f0f0f000000000f0f0f0f0000000005050505000000000000000000000000000000000000000000000000f0f0f0f0000000000000000f0f0f00000000000f0f0f00000000000f0f0f0f000000000f0f0f00a0a0a0a0000000000000000000000000a0a0a0a00000000000000005050505000000000a0a0a0a0000000005050505000000000a0a0a0a
|0,6=>0xf0f00000000000000000000505000000000000000000000000000005050000000000000000f0f0f0f0000000000000000000000000505050500000000000000005050000000000000f0f00000000000005050000000000000f0f0000f0f0505000000000f0f0000000000000f0f0505000000000f0f0000e0e0e0e000000000c0c0c0c000000000e0e0e0e000000000c0c0c0cf0f0000000000000f0f0000000000000f0f0f0f000000000f0f0000f0f0a0a000000000f0f0000000000000f0f0a0a000000000f0f0000f0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0aa0a0f0f000000000a0a0a0a000000000a0a0f0f000000000a0a0a0a5050505000000000505000000000000050505050000000005050000f0f0f0f000000000f0f0f0f000000000f0f0f0c000000000f0f0f0cf0f0f0f000000000f0f0f0f00000000030303030000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x160c1060a209820c35288080830d48205980c8848816843094010c063e20f023a34404305c288380830d100831b1a2c1820c682192a184881660b890858a86124c1062834982141868c0608089102c90612208820c34410041828f083830d180c1060a2c10a0c2440704182840608080
|1=>0x12202066234488083830d127020304186883c60e8d1220f020c14684060830d6020c2f5c344a0104c1061a202065a34484060830d34209980c15284060831b1a804040418288081960d12202065634488081950d12101950ca448406080a812213020c14688266030d4e202182e344a6
|2=>0x2a19409403c2020c34603041868910781061a205980cf04880e0830d120c10676344a3102cc0112101067434488706030d1221984041868830dd70d128041330182840419b351a2c1820ca44840608e851a10c820c34484060830d00101b40418688662cc061210b020c34488640830d
|3=>0xd24484060830590202180c35e09403c2180c344888e2cc061a2441e3018689080e2820c34488886030d12442030418684060a1861a205820c146c2102cc06130441330186881608305080c1401a2500f086030510fc1061a249840419a8d102c1067c24407301828910f4c061a24203
|4=>0x66008d12205980c1468910785980c344ce160cc0112fc2030418689102cc060a24804060830d12101cd04186891010c061b30488080830d7c2498406541061a2c2030419f09080e30202344840660e8d12205820c34488081a58d12101820cd86be82202180c34484060830d9420598
|5=>0x9e3448816600861a24583300434f121019803591a0086030d1220598021848f10101061b544043018689080c1016c34593060830d080c1061aa048f102cc061a2441304186c21010c061a245840660e8d1278584060830d080c1061b52908086030d121019803404ce06600cf1a2670b
|6=>0xc342032a08348128c40b301868940202180c14488086030dba24583301a78d1220c069e34484060835c1a25008080830d1210a820cd4689080c106b634484060835a1a2440430bc30d122c983301828d4c2c1820c3448b260cc060a10198a0242033162b861a4c20304186be1060086
|7=>0xcc101980c344840662c061a272833018689080cc640c1468406631861a24203301a78d12101980c16489080c1060a34203301b10d1210198035c30d1210198b00430d124c203301828d4c101820c344e110101061a2420304186e03c101983a344a0106032e1a2420304186df080c15e
|8=>0x30186893c101980c3448406603059024203300435312101820cd86e9066030d1210198021828d12101820c36409080cc010c144e8080cc061a242033006889080c1010c3448406600e41a24f0406603051a24203300570d12101980c36f89080cc5e0c34484079c30d128c4043018689
|9=>0x12101980d6468916101980c34488086030d12101980cd86899c101980c34488086030d4a24413301868916101980c1468916101980c1448406600861a242032a0830d1210198b324484066030dd824584060830d12101980c3758910101061a2440430186c912101980c375098e2c203
|10=>0x80cc061a24203300430d12101980c36989080cc061b44484066030d9224984066030d
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x6450bea16942aa8505096a119420a83c506ea0c9416a8285046a07940ca814501ea029402a8005
|5,0=>0x1cf6392c70d8deb1b76362c6b14d331a06334c6518c731886304c5f18bb317062d6a5958afb15962a6c5358a3b1416276c4d5897b1296246c47588bb1116216c41587fb0f961e6c3b5873b0e161b6c355867b0c96186c2f585bb0b16156c29584fb0996126c235843b08160f6c1d5837b0696
|6,0=>0x6eeedc1db4bb6276b6ed559a73b477680ece5d993b2b7648ec75d8bb3125616ec11d7ebaf675deeba9571badd65aecb41d6532c4657aead9d58aaaa7546ea71d4b328f7512ca09d3dba7474dae99d9303a5a64a6e931d22ba3e746ee8c1d14ba23643ac85d9083a097406c7f58fbb1f073d2e789cee31d57
|6,1=>0x1cf3b986722ee29dc2337e6
|7,0=>0x4d679a0d322260bcba7966f2b5a533c9f7930f249a45bc8478f911d5e373c6778c2d16da29c44c788af0f9e1c34317854f08a20dbc14781af01da003bf977e4efb19f2bbde77aeef41de533c377770ece1d63ba57
|8,0=>0x28dbd147a1af419e7fbcf879e2f3ada723cdd7
|9,0=>0x5226
|_,_=>0
def wAt:=mkWire dB 109 220 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 1000003 zs)
def oP:Nat→Nat
|0=>0x90251a133025083506110c3630251a131a251e341025061110350611080d1a110611263512118c35041930251a25126110351a250611162512611e3410190c35721110060c351e3710351a2506114c3430254c3504113025400810350611043626353025160b30254c341235080d08353025103606114634302526350436160b
|1=>0x30250611463710193c1b1625126116251a11132530250c36114d1a27061103470c350c3402130c350c110c35123508350611083506111a110c350c11043630251235083506114c370411052530250c36061104363025082504353025043630250c3504193c1b2635082512610835061130821035061104363025128210350611
|2=>0x1a11080d02130c352a1b04351035061130250656043530250c95103608251a251a11083508351a250825b3250c370c36022502270c3504363025061102130c3506110c351a1102130c350c35a2250c341035101906110c35083506111261102506111e35102506110c270c35302512611a1112118c34041930251a1106110825
|3=>0xc340c3530250c350c250a111a250c350c130a131a256c350c2731450c3410190611094d1a27c8350c25a2110c3412350c250d211a1302130c351a250c3612353025161b1a1102270c350c351a250825041130251009302512f90436302526350c131035061130250a131a2530256c350c273025083510351a2506118e131619
|4=>0xc351a270c340c3608250c371a1106110c270c1110360611061112111a251a111a251a110d250c36043530250c370c36263608251a1130259c360c113025061106110c366c360c2716191a11263508251a131a251a270c3530250c27a2120c340c351a251a1330250c351a2592110c360c35
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x880000110008000000000000000000000000000000000000000000000000
|5,0=>0x504000000000000025300000000000000000000000000119088400000010100003a61c1000064c0001720000000000000000000028600008984041e200000000001c200000000001a20c100000000000b10000248000000040814c000041
|6,0=>0x630b1458460005f9af0d744b735a18000000b22579ab85566a83529a8c94069d34d9260d2a6923479a30d126863419a048fc67c23d11dcce867133719b08d44673329188cc045d32d9160c00055329194089c44b3241914c8644031e98e8c6e63431910c085a62a3
|6,1=>0x1a84d13680b34d946c73
|7,0=>0x12d29594a4a4e5252919484a3e51d28d9464a2e5152899444a1e50d2859424a0e50528194049fe4fd27d93e49ee4f527993c49de4ed27593a49ce4e527193849be4dd26d93685b04d62
|8,0=>0x27033719b0cd46683331990cc466032f1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 13
def pmP:Nat→Nat
|0=>0x1c6e00389c00673800c37001842003024004010008000008800010cc0020800040900080a00100000103000202000260000400000600000a00000800000e0000180000200000200000240000400000400000600000800000800000
|1=>0x2280804390808711810c6702186a04309c0841181042002080002b5dc0473b806c2300c04001800402c22004ce600984e01188801e12802c7700584a00a18800e32801c2700384a00701c00c0880140400280000410000802000e62
|2=>0x698460d108019e00831c2706282e0c405c1861383043306084009389c12311021c2704280808289c1020082022202f04605c0800b631816861029c4604f18c09e13813c2502784204e08c09810012c2302386e04709c08e12811c07
|3=>0xc100204070dc802001000141258c224000040c32080c4010108020200029e12840060
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x100020400000000000000000000000000
|5,0=>0x900000000900000000000000221c0002a00c0e002401200000000000c80020821000003800000105000000b00340001624007
|6,0=>0x35cc0895865cda0500a29840ac6000127035eab645d23f6eac9db6c0d8a0543dae924b9c86568dbd7a1009581988017c84b01b38691147569f161086919
|7,0=>0x3b3f7afc8cf21d3c74b21c1a759ec6531e73c9f716ca8d56eaf4f8755969227c2851a6d48ace59d
|8,0=>0x24c49124f48b2713a8
|9,0=>0x1b
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_217 8 roots_217 ops++addP pm 1 dom_74 4 roots_74 ops++addP pm 2 dom_202 5 roots_202 ops++addP pm 3 dom_147 5 roots_147 ops++addP pm 4 dom_195 5 roots_195 ops++addP pm 5 dom_91 7 roots_91 ops++addP pm 6 dom_89 5 roots_89 ops++addP pm 7 dom_201 5 roots_201 ops++addP pm 8 dom_83 5 roots_83 ops++addP pm 9 dom_75 5 roots_75 ops++addP pm 10 dom_203 7 roots_203 ops++addP pm 11 dom_211 8 roots_211 ops++addP pm 12 dom_218 6 roots_218 ops++addP pm 13 dom_90 5 roots_90 ops++addP pm 14 dom_27 4 roots_27 ops++addP pm 15 dom_209 7 roots_209 ops++addP pm 16 dom_155 6 roots_155 ops++addP pm 17 dom_139 4 roots_139 ops++addP pm 18 dom_216 5 roots_216 ops++addP pm 19 dom_153 5 roots_153 ops++addP pm 20 dom_210 5 roots_210 ops++addP pm 21 dom_193 4 roots_193 ops++addP pm 22 dom_81 4 roots_81 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_81 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_217 8 s (0,roots_217.map (·&&&dom_217)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_217 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff0000ffff0000ffff0000,112),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_219==dom_219)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 1000003 zs symsG zs (hk 1000003 zs)
theorem ori_ok {v ys} (h:RunD true dom_219 gM v ys):RunD true dom_219 gM v (ori ys):=pickMin_runD 1000003 ys h symsG ys (hk 1000003 ys) symsG_ok h
def Z (s:Nat):=barP dom_219 gM mpG SD SS NN hAt idxH ori 1000003 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 21 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 61 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 61 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 70 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 70 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 45 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_219 gM mpG SD SS NN hAt idxH ori 1000003 mkCut s i=true:=by
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
theorem lowS_235:Lower true dom_235 roots_235 goal_235 8:=lower_slice_b [(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f00000000,1,33)] (by decide +kernel) lowS_203
namespace S_245
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,65),(1,129),(4,5),(4,20),(4,36),(4,68),(4,132),(16,17),(16,20),(16,80),(16,144),(32,33),(32,36),(32,160),(48,49),(48,52),(48,112),(48,176),(64,65),(64,68),(64,80),(64,192),(96,97),(96,100),(96,112),(96,224),(128,129),(128,132),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffff
def xsM:=roots_245.map (·&&&dom_245)
def gM:=goal_245&&&dom_245
def NN:Nat→Nat
|4=>5
|5=>62
|6=>140
|7=>83
|8=>19
|9=>4
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x726196f380685d84e0a222228
|5,0=>0xb6ee48e7888542f7ef2f75d25740136edfb6cba16564c623f35fb5056278501154c6ff490f5482374761143e854346640148386b736aed36999311962ebd72eba02b8ca2b7fd2a85228616279642261e221d11fdc61ec1b1eacc1e1941d1601cdb31c9a919a1918a79181a415a021234611d9310e140e9390e5b70c43d0bf6f0be850aed709478060a205418046810270801f2b01578006d200444
|6,0=>0x7b7c27b58873a766d6f3680b1679646793e630ef62f5f62a15615605f0675dbcf5c4c05b7ee5982e5824c540dc5313f4f9a34d4ca4c6ff4987d48740474914614a43377416bf412dd406e23f6143e38f3e24f3d7023ab4a3aa6d3a4853a212386b737c32378c0369c2363683486933f5333cbc32df83200c2f8fa2ee5d2ca372c5282b3f22a8d8291f328dcf283be27fed2772822f822212021ab3216c81fd3f1fb901dfa91de1f1dc8a1d3801d06a1ccf81c9c01c7351c67b1ba151b4291ad691a8b41a0ca1985518cc9183e717dfc17265168af1648c15e0415de2157b614e73149ce13866129ea11caf11b5c11617109380fe700fc1a0f9f50f4fe0e9be0ddf50db9d0cf850bbd90ba2a0af600ae4f0a5f90a0e609aef078a70780206fbc06f3d06b4a062c60626205f3d058d40520f04c9c043f60314002b15007f5004e4
|6,1=>0xcfc88b20faa8acea53dda4a919e1d3902a48fd758f5d08cdb7811fd7ef2f
|7,0=>0xd4211a4173a35829e4fe9d90d8a371806fc76ab66e6bf6cf86647be60ca95f3f55b76f5b62d5aa3c5978055b885585e551f84ffd14da924d3d34adc3452e64449e433d34058c386f9370643698a34d5b329de3250a30d18304352f8e42e9d32a35a29e73292592913728d2a265a024b8c2452223b43238ff23880231a422b6221fbb215fc202b41e9721e1241cfc51ba6b1afd6180fb17da4168af1525214e8e0f7470e3fa0cd5b0c54d0bbb20b44609a0c07c310729c07052066930446703df602d3c01a3901051009ac009040049d
|8,0=>0x8ffe66691e514104ac084673b40c0a312d029ee527c30234181ddd814b00142b90f8960d1000ad7404fe802879020c2
|9,0=>0x6d48e474a0356de07d37
|10,0=>0xbf1f1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc000c000c000c000c000c000c000c000c000c000c000c000800080008000b3003300330000003300330033000000330033003300000033003300330000440044004400440044004400440044004400400044004000440040004400403000300030003000300030003000300030002000300020003000200030002cc00cc00cc00cc00c000c000c000c0008800880088008800800080008000833000000330000003300000033000000330000003300000033000000330000cc00cc00cc00cc00cc00cc00cc00cc0088008800880088008800880088008b3003300330033003000300030003000330033003300330030003000300030cc00cc00cc00cc00cc00cc00cc00cc000000000000000000000000000000022002200220022002200220022002200220022002200220022002200220022cc00cc00cc00cc000000000000000000cc00cc00cc00cc00000000000000030003000300030003000300030003000300030003000300030003000300030cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc000000033003300330033003300300033003000330022003300220033002000330020c800c800c800c800c800c800c800c800c800c800c800c800c800c800c800cb3003300330033003300330033003300330033003300330000000000000000
|0,1=>0xcc000000cc00cc00cc000000cc00cc00cc000000cc00c800cc000000cc00c80003300000033000000330000003300000032000000320000003200000032cc00c800cc00c800cc00c800cc00c800cc00c800cc00c800cc00c800cc00cb3003300330033003300330033003300330022003300220033002200330022cc00cc00cc00cc00cc00cc00cc00cc00c000c000c000c000c000c000c000c32003200320032003200320032003200320032003200320000000000000000cc00c800cc00c800cc00c800cc00c800cc00c800cc00c800cc000000cc00033003300330033002200220022002200330033003300330022002200220022c800c800c800c800c800c800c800c800c8000000c8000000c8000000c800033003300330033003200320032003200330033003300330032000000320000cc00c000cc00c000cc00c000cc00c0008800800088008000880080008800833003000330030003300300033003000330030003300300033003000330030cc00cc00cc00cc00cc00cc00cc00cc00cc000000cc000000cc000000cc00033003300330033003300300033003000330033003300330022002000220020cc00cc00cc00cc00cc00cc0000000000cc00cc00cc00cc00cc00cc000000000000000000000000000000000000000330033003300330032003200320032
|0,2=>0xcc008800cc008800cc008800cc008800c0008000c0008000c0008000c000833003300330033003200320032003200330033003300330032003200320032cc00cc00cc00cc0000000000cc00cc00cc00cc00cc00cc0000000000c800c80003300000033000000000000003300000033000000330000000000000032000000000000000000000000cc00cc00000000000000000000000000cc00cb30033003300330033003300330033003300330033003300320032003200320000cc000000cc000000cc000000cc000000cc000000cc000000c8000000cb0003000300030003000300030003000330032003300320033003200330032cc008800cc008800cc008800cc008800cc008800cc008800cc008800cc008b300330033003300330033003300330032003200320032003200320032003200000000cc00cc0000000000cc00cc0000000000c800c80000000000c800c8000000000000000330033003300330000000000000000003300320033003200000000cc00cc0000000000cc00cc0000000000cc00c80000000000cc00cb300330033003300330033003300330033003000330030003300300033003000000000000000000000000000000000cc00c800cc00c800cc00c800cc00c80000000000000000000000033003300000000000000000000000000320032
|0,3=>0xc0008000c0008000c0008000c00091001100110011001100110011001100110011001100110000000000000000000000000000000044004400440044000000000000000000400040004000400000000000000003300330033003300000000000000000032003200320032c000cc00c000cc00c000cc00c000cc00c000c800c000c800c000c800c000c80000000000000000000000000000000000032000000320000003200000032cc00cc00cc00cc00cc00cc00cc00cc000000c8000000c8000000c8000000cb3003300320032003300330032003200330033003200000033003300320000cc00cc00cc00cc00cc00cc00cc00cc00cc00c800cc00c800cc00c800cc00cb3003300330033003300330033003300330033003300330022002200220022440044004400440044004400440044004400440044004400400040004000400000000000033000000000000003300000000000000320000000000000032cc00cc00cc00cc00cc008800cc008800cc00cc00cc00cc00c0008000c000800000000000000003300000033003300000000000000000033000000330032cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00c000c000c000c33003300330022003300330033002200330033003000200033003300300020
|0,4=>0xc800c800c800cb30033003300330000000000000000003300330033003300320032003200320000000000000000c800c800c800c8000000000000000000c800c800c800c81000100010001000100010001000100010001000100010000000000000000cc00cc00cc00cc004400440044004400cc00cc00cc00cc004000400040004000000000000000000000000000000003300220033002200330022003300220c000c000c000c000c000c000c000c000800080008000800080008000800091001100110011001000100010001000110011001100110010001000100010440044004400440044004400440044004000400040004000400040004000422002200220022003300330033003300220022002200220032003200320032440044004400440044004400440044004400000044000000440000004400000001100000011000000110000001100000010000000100000001000000010c000c000c000c000cc00cc00cc00cc00c000c000c000c000c800c800c800c8000000000000000330033003300330000000000000000002200220022002200000000c000c00000000000cc00cc0000000000c000c00000000000c800c83000200030002000300020003000200030002000300020003000200030002
|0,5=>0x44004400440044004000400040004000000000000000003000300030003000000000000000000020002000200020000cc000000cc000000cc000000cc000000c0000000c0000000c0000000c000032000000320000003200000032000000320000003200000032000000320c000c000c000c000c000c000c000c000c0000000c0000000c0000000c00000000000000000000000000000000000030003000300030002000200020002cc00cc00cc00cc00cc00cc00cc00cc000000000000000000c800c800c800c80000000330033000000000033003300000000000000000000000000320032cc00cc00cc00cc00cc00cc00cc00cc00440044004400440040004000400040000000000000000000000000000000011001000110010001100100011001000000000000000000000000000000000c800c800c800c800c800c800c800c80000000000000003300330033003300000000000000000030003000300030cc00cc00cc00cc000c000c000c000c00cc00cc00cc00cc00080008000800083000300030003000200020002000200030003000300030002000200020002cc00cc00cc00cc00cc00cc00cc00cc000c000c000c000c000800080008000b3000000330000003300000033000000330032003300320033003200330032
|0,6=>0xcc00c000cc00c000cc00c000cc00c00003300000033000000330000003300000022000000220000002200000022
|_,_=>0
def sP:Nat→Nat
|0=>0x22b8206521c7214e104851c4c2091a14d840cb02874828206561c8aa08194871ca0d860a1d3934c112850628d8624905040c8c38e4404d890a3909c081828a3610320007c2063c1438e3a50d890a0c5100c3c28e362430c0a0cc84301c1942c24193024888a201878e1a302870608080
|1=>0xa88206681438e6e106850e4451b121878e026c6850e0c30c3c143a414103250e293080c803832604a85222988412d470108342871c90a040c1c9841219a051c75084121471d386c3051c90e040c1c19466183b2146c2060e393041a1438e44500890a44501622580a08242832605785
|2=>0xa982065814391140430f0e10325581439114a82060e284040c803840cb02871cdc30c0a1c5040cb50071c8830c0a1c71c026c4851c51d860a1c7130819c850628d98340c20652143911404db670282090a382091a1438e424c2060a7d90a08183b70819a050e2820646143a726104a5
|3=>0x626cc073e282060a1c18a10187850e0c5100210485222971b301838e38042050e38d840cfc28706893813614383140448f0a1c51b08196850e0c504302c38e28983050e4451b0819f03441031e0a1ce0a08192850e0c53108604831404a850e38d840c3428722297046c18383449c209
|4=>0x12143831405b0f0a1c727081a2050e445040c3c007069c9841a143834228d840c1538a08252850e0ce0a026c2a714103230a1c18a2e6c30514103410a1c18a02607850e0db840c782871c104c00a1c18a4c10c09000ca1c022428706749a6081828314b841b0c001a72698d840a0c501
|5=>0xa1c88a101a38706284360c3c38e281a3850e7c5040c94287064cd840c7828315182180a1c1a2289c0850e0ca260c78287222951b081838a78103250a1c18a1018d07067450618143831420c061e1c1b714103050e38a040c3428706297100818003286c3450a0c52e106c4851c74a04
|6=>0xa445310824300069051b081838a0818f340a1c18a0221b071c8898412182835028d860a1c18a02187850e44526361030006885013624283149830f0a1c50412190050e0ca010c78287062971008242833a5051b121418a08189070629308301c7134c104860a4451b08d831d1410323
|7=>0x81838e6e982060a1c19d3828d860a293080c94287062808812001a438282060e282064614383287139b0c1418a54187850e445040d2c38e386c2090c141944e984850e39126081828706525010a1c18a5c04d890a39384921438314c4404302418a361a40006280b16a14383284c089
|8=>0x1404d890a445040d44383a04c2060a1d80a0818287062a7040c0039f14042060a1c88a08d830f0e7c526081828706103290a1c18a9a6c4851cdd1040c14383284d3060a3910136182871cdc0840c14391141034c0e39381361438a02203250a1c18a78202060e38ea708242870690a0a
|9=>0xc95a050e38e2608182876e2820646143834c103290a1c5040cd02871404206461439114a82060e2ac840d602871498206461438e28984860a1c88a021048022288040c1c88a081ab871c103560a1c88a026cc0706513d50a1c18a035048506702063c1439114103530e0ca130d1c28e
|10=>0x4450504121828329282060a1c7133610305065050112143831404209001418a082435b0a0c50836603071c103450a1c18a361035a0a1c18a20103050e0c5310819a850e0c5040d5c2870650984121828a4c103340a1db8a08192850e39b94081828706a8206521438e6e702060a1c504
|11=>0xa0c53136104860a0c52e10103000e0c559081828706280b1101828706a05040c1439114980840c143911411b180c1c18a786c2060a1c1b714103050e3939b081828707405040c143911411b090c1c18a1010486000c52610243050e0ce1314042050e38a010c1438a4c104864a14383
|12=>0xe3851b0824305069c5040d102871c103400a1c18a5c6c3050e0c5041300287068939308182870628d86b81438328103450a1c70aaa103050e38e27081828706282069200283146c236121828314044180e0ce0a02102870628d840cd42870628b840c1438328293060a1c18a4c10300
|13=>0x81af850e0c52e106c3050e0c5040d78287068852608182870674e0a08182871c702060a1c18a082435d0a0c50836243050629884301838314a84040c14383449c2060a1c194141a3850e4451b08603070628254121828e4e042050e0c5260210c050e0ca0a08186850e0ce930210305
|14=>0xe0c501362428314042063c1438a02103250a1c18a4c1031e0a1c52608192850e38526081828706284040d78287062952e0818287222aa840c14383141030f0a1c1b744282060a1c18a5c982060a1c1b714042060a1c1a214104860a0c5040c7828714103250a1c1b714982060a1c18a
|15=>0x14b80840c1438e28103050e0c52602103050e0c50108180050e0ce2714103050e0d38a36103050e4451b081828706505010c1438314103057c1c18a5c103050e0c5043024287062809b0c14383c2282060a1c1a214103050e0c50430180070628206921438314103600a1c18a4c10305
|16=>0x314103050e0ca0a08182871c282060a1c18a08603050e0c50108182871c280840c14383
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x12400e4009500450004
|5,0=>0x1796173616d61676161615c51566150614a6144613e61386133512d61285123511d61176111610b610560ff60f960f360ed60e760e160db60d560d050ca60c460be60b860b260ac60a660a1509b6095608f608a50855080507a6074606e60686062605c60566050604b5045603f60396033602d60276021601b60165
|6,0=>0x325731e73186312630b730562fe72f862f172eb62e472dd72d672cf72c872c172ba72b462ad72a6729f72987291728b6284727d7276726f72687261725a7253724d62467240623a6233722c7226621f72187211720a720371fc71f661ef71e871e171db61d471cd71c671bf71b961b361ad61a6719f71996193618c7185717f6
|6,1=>0x4cc74c574be74b864b264ac64a664a0649a6494648d74876481647b6475646e74686461745a7453744c7446644064397433642c7425741f64196412740b740473fd73f673ef73e873e263db73d563ce73c773c163ba73b373ac73a6639f73996392738c6385737f63787371736a7364635d7356734f73487341733a7333732c7
|6,2=>0x51e751775107509750274fb74f474ed74e674e064d974d36
|7,0=>0x6ec76e486dc86d666cf76c876c176b986b276ab76a4769d7697668f8687867f86787670866a6663765c7654864d7646763f7638763176298623661c7614860d760675ff75f785ef85e875e085d975d185ca75c285bb75b475ad75a6759f7597858f8589658185798572756c6565755e75577550754a6542853b7533852c75257
|7,1=>0x7796771876a7762875b7754774c8744873d7736772e8726871e87177710770a670286fb76f38
|8,0=>0x80177f987f367eb87e387db87d387cc77c577be77b777b077a977a2779b7794778d7786777f7
|9,0=>0x81c7816680f78087
|10,0=>0x8236
|_,_=>0
def wAt:=mkWire dB 98 246 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1106150c110a1d0c1d06bd4e6c081d14194e6c0e1114190c11141d14b64a15069a36190615542b306d081d0a19069a3619081d081d2a1528240e191411146d0629081d0c1d0c110c1d06290c51141138130a193429000408190a1d0e1914112e1526040819141d141d08192a1528240c1d14111629122008190a1d0e190a11
|1=>0xc11062912290c110e110e1928260c1d0ee9260608190e1102000a190c110a1d0a2506150c110e110e19065d26040e190819141d14964c29069a021d0c11069a12110e19141d6c130c8a021d081912500819141d0e1914110cc63a1f06294e114e1d141914115e154e6c081d14193e171495069a36190e19281d141106290c1d
|2=>0x2150c110e1130110a190615261906290819141d4e6f062914190c293629081d08da12150e194a15069a361912200a190c1d0a110629021d08191411081d001b0a1d0615149a146d36190e1100110a1d0c1d0a1912500c1d081914110629441b36290e1106153011301d0a19261114190e19141d30f5306e081d0a1906f2021d
|3=>0x141d6e1f4e6d081d14190c29069a12110c1d0c110e110e9d141906de4e6d081d26040e110c11141d070e090912170c1d6c13301d0a196e2b4e6d081d14194e1306290c1d141912110a190e190a1d12290c1d1411141d1405021d0c11081d0c210a110a1d3619081d14190c1536150e11069a021d0c11541310250c1d0a115c1f
|4=>0xc114c2b36190e110cf5306e081d0a19281d14110c1114194c2b021d0819306d0615081d0a194c17021d0c110a11000408190a1d38134e1d4e1114196c130e610a194f114e6e081d1419441b281d141106295c1f08610a19081d08290c4e141d10190c1d0a11062928190c1d14116c130c010a1d08da00190a1d0615441b2611
|5=>0x141d06297e114e6f0e1114195413000508190a1d061536190e110a1d0c110e193629081d6c130a2512110e1906f24c1712110e19149a021d0c115c1f08610a1928190e1914112a1528240e1914110c15021d08190a11121106290e19141d06150e110e610a190815361b081d06156c130a250c1d361b081d14110629069a021d
|6=>0x4e1d0e1114195413306d0e110a198e15361b081d061506290e1112290c1d12110c1d14110629146d36190e114e1f14190819141102150c1d081d0819121306290c1d14190e190e210a11101b0a1d081d0a11621b00110a1d08290c110e19141d0c1d00110a1d06156e174e6d14194c2b021d0c110a110c110c010a1d0c1d2611
|7=>0x306d081d0a190c1d0e1102170c11441906290e511411141d12110c1d14110c1106293629081d062926050819141d061500070c110a1d0c1106290e1114190815069a021d0c11541710250c1d0a110629089d0c1d14190ade28250c1d4c29021d0c11081d4e114e1d1419069a021d08190e190a1108190a1d06de4e6d081d1419
|8=>0xf21101b0a110615282706290c1d141106150c110e110a19021f14190819141108190c1d36170e116e2b38110e9d14190615921512130c1d141d1411361b081d06290c1d081d081906150f4908620a1914e926060819141d06bd4e6c081d14199e1502030a1d0c111495069a021d06156c130c010a1d4a29069a021d0c11542b
|9=>0x14110e19141d069a021d0c11069a021d0c114419281d1411542b306d081d0a19062938110e9d1419069a021d0c110629122912110c1d06de4e6d081d1419542b4c15021d0c11067a4c2b021d0c1106de2605141d0615306d081d0a190f3502170c114c29021d0c11062912110c1d141106150c110e190a1d06155c1f08610a19
|10=>0x36190e114e6d081d14190629081d1419aa29021f0c11061512150c1d0e150a110e1912110c1d0a1126190c11141d062908191411069a12110c1d281d0c1d141114114e1f14190e11141d06290c110c1d14110c110e190a1d26130e19141d0a11081d0a19261b141d0629306f0a195c1f08610a19621b08010a1d0f210c220a11
|11=>0x89e0c1d141914192611141d0e11022b0c1108290c4e141d0629021f0c114e1d1419062912130e190a1d0e1112150c1d0a1908190a114e1d0c111419621b36150e1126040819141d12110c1d141112110e190a1d0e1936150e110c210a110a1d0f3502170c11101d08190a1194114e1f14190615021d0c11301d0a1906154c17
|12=>0xc1d0a110c21081d0a1110260c1d0a11146d36190e114e114e1d141906290e9d14190c1d362b0e11081d0c1d0a110a1908010a1d10250c1d0a11146d081d14191411361b081d06150a190e1136170e110e1906290c111419021d0c110a19441b281d141114050819141d0e19081d06294e6e081d06294e131419081d08610a19
|13=>0x819281f1411281d14110a1d0a1912130c1d122b0c1d021d0c110c1d081d0819149a021d0c11069a021d0c114c2b021d0c11069a021d0c110629021d0c1112230c1d5c1d08610a19021f081906156c13301d0a194419281d14110215021d0c1126050819141d0c1d281d14114c2b021d0c11069a021d0c114c29021d0c111027
|14=>0x141106290a190c110819062902150c1114110629021d0c110a1d0c114e1d1419081d1419081d0615081914110c020a1d08610a190c1d0a19081d
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0xc601980000000006
|5,0=>0x824000000000007f300007a51e087531c140001ad46650000000000061500005d4000000017045b10000000164854514c4000000000014844e40000495115000010503c50dd4325000000000002e400002950000263085400007140000000000061000005c4125
|6,0=>0x580d5d3565155454514d40001494518d4244fcd3c34e113444c4d2d44a8d26448911f346d1174450d104434d094418c0004090ff33ed0f743cd0f033b10e84394ce143750d94358cd243390cb3320cc533050be32e90b642cccb032b4caa32990a2427909a4000096424908e42290864
|6,1=>0x93ce4c3921244490123c48e123448c122c48a1224488121c4861214484120c4824e0548051fd47e51f547c51ed47a51e547851dd47651d54748dcf372d1c8371100007011bd36e51b546c51ae36a91a6468919e466cd974650d9046311893618d8245f917a45d917245b916a45991633
|6,2=>0x9e8e7739d0e7049b1269399526149752594958e524
|7,0=>0xce0f353cc8f2f3cb0f293c98f233c80f1d3c68f173c50f113c38f0b3c20f062c0cf003bf4efa3bdcef43bc4eee3bacee83b94ee23b7cedc3b64ed63b4ced03b34eca3b1cec43b04ebe3aeceb83ad4eb23abceac3aa4ea63a8cea03a74e9a3a5ce943a44e8e3a2ce892a18e833a00e7d3
|7,1=>0x3703db4f6a3d9cf643d84f5f2d70f593d58f533d40f4d3d28f473d10f413cf8f3b3
|8,0=>0x3972e54b932e44b8f2e34b8b2e24b872e14b832e04b7f2df4b7b2de4b772dd4b732
|9,0=>0xe7079b1e687991
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 14
def pmP:Nat→Nat
|0=>0xc3000182000208000400000352000640000c08001800002f0000464000858001080002020004000006480009100011200020400040000078000090000100000140000200000220000400000480000800000a00000c00000800000
|1=>0x12260024080040c48080580100a0020000038cc00400000640000c000012480024180048200082440100c0020100023320046600088d8011080022000042040081000101800202a004040004c080091800120000220000400000688
|2=>0x1023f22041e040834081058100d32201820401040801781002002003e4400140530980931301246a4248940490b908643010c000209000411d90823921046e42081004009904201204d26008a4c01119802000002636004c4c0091b9
|3=>0x380232700064c8004181119301020600400a08dc94068128020050038488a4c1098982123b2424664840e89081582100b042004081a489020102023f2400400800489000101833103046646040c0c0100126130226260448cc889099
|4=>0x4833329056652094ca411b948233284d665098cca1159841b13282676504ccca098d941233280d6650194ca0319940337280666500c5c2015994027328046e5008cca011984021308040250030c200008400002800000e08cc9c0189
|5=>0x782022f00265e000cbc0018703332e04a65a0a4cb400196123b2c0c6658120c301699602532c046658014cac3091582332a44665448cca859d9506532a0c26540b4ca816085023f2a01861288cca4d99948673290ca652190c243208
|6=>0x389acce419b9c033b3004e61e88043c1999782332f04465e084cbc1081
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x302000002
|5,0=>0xe0000000d003c38214800351a0000000e001400001c080000431b1c0000003a260047060009201a3d000000060013001215000c00000029000a27
|6,0=>0x101657544c68d5450b0012f608e39132e8304341383be0f805d11985384073f062528827800193b012f6f772452a1741eb159761f06016d0c07057d580184574e492dc07b4600633362186a055e6432019d011d0e0b374b4d3e6c003109072b71046687680e41bd6e2ca17a5918073637420655300691674501005b4a172656
|6,1=>0x23220e131012240e0188042f
|7,0=>0xc37cc27fc2c4062aa5890f86115f8989198ba0b216289461baa9695f6199aaa4bf5c51bb0497a2725e664c9f96b3b5a373859b81c1a64f9ba893c59ab889959bc9b4bc70c87e5e40ac79b94cabc706895a8b6b
|8,0=>0x9fa38fc29eb7adae9c8ca3b6af8aa792b2b2c3
|9,0=>0x8a8e909b
|10,0=>0x89
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_213 9 roots_213 ops++addP pm 1 dom_161 4 roots_161 ops++addP pm 2 dom_37 4 roots_37 ops++addP pm 3 dom_244 8 roots_244 ops++addP pm 4 dom_241 8 roots_241 ops++addP pm 5 dom_225 5 roots_225 ops++addP pm 6 dom_101 5 roots_101 ops++addP pm 7 dom_165 7 roots_165 ops++addP pm 8 dom_229 8 roots_229 ops++addP pm 9 dom_177 5 roots_177 ops++addP pm 10 dom_53 5 roots_53 ops++addP pm 11 dom_197 7 roots_197 ops++addP pm 12 dom_117 8 roots_117 ops++addP pm 13 dom_180 5 roots_180 ops++addP pm 14 dom_209 7 roots_209 ops++addP pm 15 dom_228 5 roots_228 ops++addP pm 16 dom_149 7 roots_149 ops++addP pm 17 dom_164 4 roots_164 ops++addP pm 18 dom_240 5 roots_240 ops++addP pm 19 dom_113 5 roots_113 ops++addP pm 20 dom_116 5 roots_116 ops++addP pm 21 dom_181 8 roots_181 ops++addP pm 22 dom_212 7 roots_212 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_245 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_161 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_37 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_212 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_213 9 s (0,roots_213.map (·&&&dom_213)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_245 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_213 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_245==dom_245)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_245 gM v ys):RunD true dom_245 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_245 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 62 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 62 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 140 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 140 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 83 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 83 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 19 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 19 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 4 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_245 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_245 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_245 roots_245 goal_245 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_245
theorem lowS_245:Lower true dom_245 roots_245 goal_245 11:=S_245.noCircuit
def isoMvS_126:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_iso_b isoMvS_126 (by decide +kernel) lowS_123
def isoMvS_175:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_175:Lower true dom_175 roots_175 goal_175 10:=lower_iso_b isoMvS_175 (by decide +kernel) lowS_95
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_123
def isoMvS_190:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_123
def isoMvS_207:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_207:Lower true dom_207 roots_207 goal_207 10:=lower_iso_b isoMvS_207 (by decide +kernel) lowS_95
def isoMvS_221:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 10:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_215
def isoMvS_222:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 10:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_219
def isoMvS_238:List (Nat×Nat):=[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 8:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_235
def isoMvS_249:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_219
def isoMvS_250:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 8:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_235
def dzo_119_8:=0xff00ff00ff00ff00ff00ff00ff00ff00
def gzo_119_8:=0xff00ff00ff00ff00ff00ff00fe00ec00
def gsh_119_8:=0xff00ff00ff00ff00ff00ff00fe00ec
theorem lowS_zo_119_8_21:Lower true dzo_119_8 roots_119 gzo_119_8 7:=lower_iso_b (d1:=dom_119) (r1:=roots_119) (T1:=gsh_119_8) [(dom_119,8)] (by decide +kernel) (lower_slice_b (T:=gsh_119_8) [(0xcc00cc00cc00cc00cc00cc00cc00cc,0,2),(0xff00ff0000000000ff00ff00000000,0,32),(0xff00ff00ff00ff0000000000000000,0,64)] (by decide +kernel) lowS_21)
def dzo_55_8:=0xff00ff00ff00ff00
def gzo_55_8:=0xff00ff00fe00ec00
def gsh_55_8:=0xff00ff00fe00ec
theorem lowS_zo_55_8_21:Lower true dzo_55_8 roots_55 gzo_55_8 6:=lower_iso_b (d1:=dom_55) (r1:=roots_55) (T1:=gsh_55_8) [(dom_55,8)] (by decide +kernel) (lower_slice_b (T:=gsh_55_8) [(0xcc00cc00cc00cc,0,2),(0xff00ff00000000,0,32)] (by decide +kernel) lowS_21)
def dzo_117_8:=0x33003300330033003300330033003300
def gzo_117_8:=0x33003300330033003300330032002000
def gsh_117_8:=0x330033003300330033003300320020
theorem lowS_zo_117_8_21:Lower true dzo_117_8 roots_117 gzo_117_8 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_8) [(dom_117,8)] (by decide +kernel) (lower_slice_b (T:=gsh_117_8) [(0x330033000000000033003300000000,0,32),(0x330033003300330000000000000000,0,64)] (by decide +kernel) lowS_21)
namespace S_127
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,65),(2,10),(2,18),(2,34),(2,66),(3,7),(3,11),(3,19),(3,35),(3,67),(4,5),(4,20),(4,36),(4,68),(6,7),(6,14),(6,22),(6,38),(6,70),(8,10),(8,40),(8,72),(9,11),(9,13),(9,25),(9,41),(9,73),(12,13),(12,14),(12,28),(12,44),(12,76),(16,17),(16,18),(16,20),(16,80),(24,25),(24,26),(24,28),(24,56),(24,88),(32,33),(32,34),(32,36),(32,40),(48,49),(48,50),(48,52),(48,56),(48,112),(64,65),(64,66),(64,68),(64,72),(64,80),(96,97),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|5=>6
|6=>46
|7=>107
|8=>128
|9=>61
|10=>10
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xb1f97728df717904f5e306d2e0652c
|6,0=>0xe50b0d889bd5b4cd5339d3b80cddbaa09f99d7c89a8a596f41913368e8c47c6367286861f12610e85eecf53708524cb516a14f57c4be094b353438813cbe4343e333d81339462c48225bcc2022d1ee501d8b81cc3719716167711569415357148ad14431140bc0ee6209c160935e037bb0047a
|7,0=>0xffc2cf3684efe56dc274d9196d8f19d3a1fcd213ccc38c73e2c1c36c122ac0f30bfb6bb181eaf56aadf37ab097a604aa38e1a2a8ca089e9ac6a932749303d917e99019c8c49087f47852508424f7f7a37bd907a0ec75dac757506e1436d5ff6d0136b5d66a7b4688f0683385f287565f0545894ffaa4f24d4ef004e06b4a6e047f1f45743439394391d40e733b0f738ac63729c36f40367783543034bbf3390531d653185b312a9311132f8c72c6372c4392918d27e73272ec2654a2651e25faf237502311522c1b21d38206612016f1fb1f1ed641ea301cb121a83e19dc517a391731912e7111bd0114df114c30f41b0eed00e08f0bc3107bbe0753d0666e04a0b0487a024cc01a370146e
|8,0=>0xffdecf6acff3a3fef186dc870da688d8292d5175d3421cfdd3cfb20ce1cec56a2c4f7fc2af1c26b0be81cb7619b4a8cb169fa6eafa5675a1026a07759e7239c5c099ad9953368cb098ae4c89deb871da852ec851c6851568390a823fb7beb679ff279ecc777937698475be9741b270b556e18c6c1e46b77167f5b6767f65522655066491e62494619b35d9915bb1855ecf54c56547ff52eae52e9252b6a5023b4eaf74e0224de9f48d14442d341bcf4123d410bf40c043e9eb3cf8a3ce343b9ae3af5c3ac8e3a82d395cf3813d374df3474333f3f3354732a202fc2a2cf5c2be512b6a52aa4f29d592940626a53265f425b9f23057220eb1d8c61a921172d015a13157721526d1052610389100a20e7a40dca90bc9f0870f07b1a071ff06a5205c3605b250428b036050343d032fb02bf9023b802005013530100900ee3000d0
|9,0=>0xf96b8e9e82e9b32e5e72d2632cdf0fc9b06bb6c2b9cdbb2c55afb5ba904ea8842a5099a39939987d92afc917868c01e8b85885b427f23979a8474789719096b1ed69a565c7525bce154f2646b3244cca42e873e88c3e2c43e0063cb5b375fc3549130394292d4291b81fc3a1b6f51914a18d211685b1643f1285f10fcf101700f9760ce710b65c0a79209fe006e0805b690414303dcb01b47
|10,0=>0xf90dcf69edbbe948f8cb6c3bf581863fcd23da333b65b2fbbe
|11,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000fefefefefefefefefefefefefefefefeccccccccccccccccccccccccccccccccf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffffffffffff0f0f0f0fcfcfcfcfcfcfcfcfcfcfcfca8a8a8a8ffffffffffffffffccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffaaaaaaaaffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00fcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfceeeeeeeeeeeeeeeeeeeeeeeee0e0e0e0ffffffffffffffff0000000000000000
|0,1=>0xfffffffffffffffffefefefefefefefefffffffffffffffffcfcfcfcfcfcfcfcaaaaaaaaaaaaaaaaaaaaaaaafefefefeffffffffffffffffeeeeeeeeeeeeeeee0000ffff0000ffff0000fefe0000fefe0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a00cf00cf00cf00cf00cf00cf00ce00cefffffffffffffffff0f0f0f0f0f0f0f000ff00ff00ff00ff00ff00ff00ee00ee0000000000000000fffffffffefefefe5555555555555555505050505050505000ff00ff00ff00ff00ff00ff00cc00ccffffffffffffffff000000000e0e0e0efffffffffffffffffcfcfcfca8a8a8a8ffffffffffffffffaaaaaaaaaaaaaaaa00dd00dd00dd00dd00dd00dd00dc00dc
|0,2=>0xf3f3f3f3f3f3f3f3f3f3f3f3f2f2f2f2333333333333333333333333323232320000ffff0000ffff0000ffff0000fefeffffffffffffffffffffffffcccccccc0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a5555555555555555555555555050505055555555555555555555555554545454ffffffffffffffffff00ff00ff00ff00fafafafafafafafafafafafafafafafaffffffffffffffff00000000eeeeeeeefffffffffffffffff0f0f0f0fefefefe000000000000000000000000fcfcfcfcdddddddddddddddddddddddddcdcdcdc54545454545454545454545454545454ffffffffffffffffffffffffeeeeeeeefffffffffffffffffafafafafafafafa
|0,3=>0xfffafffafffafffafffafffafffafffafffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff055555555555555555550555055505550ff55ff55ff55ff55ff50ff50ff50ff5055555555555555555500550055005500f5f5f5f5f5f5f5f5f5f0f5f0f5f0f5f00e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e555555505555555055555550555555500f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0affffffffffffffff00000000fefefefeffffffffffffffffeeeeeeeee0e0e0e000ff00ff00ff00ff00ff00ff00fe00fe555554545555545455555454555554540f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e03030303030303030303030302020202
|0,4=>0xf0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e000000000000000000000000eeeeeeeefffff0f0fffff0f0fffff0f0fffff0f0fffffefefffffefefffffefefffffefefffffffffffffffffffffffffefefefe33333333333333333333333330303030fffffffffffffffffffafffafffafffa55555555555555555454545454545454cfcfcfcfcfcfcfcfcfcfcfcfcecececeffffeeeeffffeeeeffffeeeeffffeeeefffffcfcfffffcfcfffffcfcfffffcfcffffccccffffccccffffccccffffcccc55505550555055505550555055505550ffffffffffffffff5550555055505550dddddddddddddddddcdcdcdcdcdcdcdcffffffffffffffffffffffffff00ff00
|0,5=>0x33333333333333333030303030303030fffffffffffffffffffffffffcfcfcfccfcfcececfcfcececfcfcececfcfcece0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0afffffafafffffafafffffafafffffafafffffffafffffffafffffffafffffffaffffffffffffffffffffffff0e0e0e0e000000000000000000000000fefefefe05050505050505050500050005000500ffffffffffffffff0e0e0e0e0e0e0e0e33333333333333333333333322222222fffffffffffffffffffffffffafafafaffaaffaaffaaffaaffaaffaaffaaffaa0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0affffaaaaffffaaaaffffaaaaffffaaaa00000000000000000000000054545454
|0,6=>0xffffffffffffffffffaaffaaffaaffaa0f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a55555050555550505555505055555050ff55ff50ff55ff50ff55ff50ff55ff50ff0fff0fff0fff0fff0aff0aff0aff0acfcfcfcfcfcfcfcfcecececececececeffffffffffffffff54545454545454540000fcfc0000fcfc0000fcfc0000fcfcaaaafefeaaaafefeaaaafefeaaaafefe0f0f0f0f0f0f0f0f0f000f000f000f00afafafafafafafafafaaafaaafaaafaaffffffffffffffff0f0a0f0a0f0a0f0affffff00ffffff00ffffff00ffffff00555555005555550055555500555555000000000000000000eeeeeeeeeeeeeeeef0f0f0f0f0f0f0f0fefefefefefefefe
|0,7=>0x5050500050505000505050005050500ffff5454ffff5454ffff5454ffff5454fffffff0fffffff0fffffff0fffffff0ffffffaaffffffaaffffffaaffffffaa050504040505040405050404050504040000fefe0000fefe0000fefe0000fefe000000000000000054545454545454540f0f0f000f0f0f000f0f0f000f0f0f00afafafaaafafafaaafafafaaafafafaa00ff00ff00ff00ff00aa00aa00aa00aa00000e0e00000e0e00000e0e00000e0effff0f0affff0f0affff0f0affff0f0a0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cafafaeaeafafaeaeafafaeaeafafaeae555544445555444455554444555544440000000000000000fefefefefefefefe
|0,8=>0x333333333333333322222222222222223333303033333030333330303333303000ff00ff00ff00ff00f000f000f000f00000000000000000ffaaffaaffaaffaa0000ffaa0000ffaa0000ffaa0000ffaa00ff00f000ff00f000ff00f000ff00f0
|_,_=>0
def sP:Nat→Nat
|0=>0x6090e04030c070609050403020f000e031f0a0b061b050e04031e0a0f0e04030a0b1d110e030a1c0b061b0e04030207061a0e040a0b0619000e04180a0b0617090403080b0600160e04030a0b060e040a0b0615140e04030a0b06130e04030201110e0403120a0f0e040a0b1110090504030c07090403080706050403020100
|1=>0xb06302c0e04031806222c0e04030c18060e04032f0a0706090504030c0b000e04030a07062e0e030a0b062d002c0e040302062b0e04030a1c0b2a050e040302180f0e04030a0b11290905042803270b0e040308180b060e0403250a0b060e04030a0f11240e04030a230b110e040a0f070617090e0403070622210e04030218
|2=>0xa0b06090504030a0f0b00090e042803270b060e04030a0b11380d04030b3736000e04200a0b06140e04030a0b06350905040327070b0e0403020106000e04030a340b060e04030a0706300e040a0b0633000e0427180b06140e0403020a0626090504030207060d04030b323100050e04030c180b0e0403080a07060e040318
|3=>0xb063a0e040a0b1106140e04030c0a0b11210e04030a0f07060e0403020b061a000e04030a410b06400e04030a0b062b0e043f03180b060e04030c180f0b060e04030a0b063c2c0e0403180a0f060e043b030a0b060e040a0b061700050e040a0b0617000e04031e020a0f06210e0403180a0b062c0e0403270a0b110e040339
|4=>0xb0d04030c180b110d04030c0b0631000e04031f0c0a0b062c0e04030218060e04030a470b0600050e04030a0f070e04030c0a1c0b060e04031f0a1c0b060e040a0f0b0617002c0e0403200a0b06090e04030b0622000d4504030b0631000e04030a070638090e04030c0b06000d440403020631000e04030a0b06420e043d0a
|5=>0x43f03180b110d04030c180f0b11050e0403270a070b0e04030a0b06260e04030c0a07060e04030a0b064f000e04030a0b1d06000e0403180a0b064e0d03020a0b061b002c0e04030a0b062b0d4c04030a0b32004b0e04030a0b06000e04030a07064a0e04030c0a0f0b110e0449030a0b060e04030a0b0648050e0403180a0f
|6=>0x152c0e04031e020a060d030c0a0b061b00090e0403270b110d031f0a0b061b000d030a1c0b061b00540e04030a070b06210e0403020a06000e04032f0a0b06000e04030a0b062e000e04030c0a0f07060d04030a0f0b32000e0428030a0b062a0e04030a0f0624000e04280a0b06520d4d51030c020b000e04030a0b0650000d
|7=>0xe043f280a0b062c0e04030c0a06000d4d5103020f000e04031f0a0f0b060e04031e0a0f060d46040302063100050e04031e0a0b060e04030a0b11064a2c0e04030a063800050e0403020a0f000e04030a0b0657210e040a0b0617000e04031f0a0b06090504030a070b060e04030a0b06560e0403080a0b06000e04030a0f0b
|8=>0x270a0b06140009050428030a0b060e04030a0b11520d4d51030c0b000d5a04030a0b3700090e04030a0f0706540e0428030a0b06400e040327180b060e040302180f060d030a0b061b0009050403270b00590e04030a0b06000e04030a0b065800090e04030a0f0b110d0403020a0f32000e0403180b061a0e04030a0b063000
|9=>0x20f06000d5104030c0a0f0b005e090e04030a0b0600400e0403270a0b0600210e04030a0b06000d043d03180b11060e0403020a0f06000d04030a5d0b06000d4404030a0622000d043d030b065c000d04030c020a0706000e0403020a0706050e0428030a0b06400e0403200a0b060d040302180f110e04030a070b062a0e04
|10=>0xb06210e04030a0f0b06000d4404030c0a0f06000e0453030a0b110d4d5103020b06000d040302180f06000d04030a0b066400090e04030a0b11062c0e0403180a0b060d454404030a0f06000d043d0a0b0662002c0e04030a0f06000e04031e020a0b060d4404030a0b0631000d0403600a0b06000e04030a0b065f0d4d0403
|11=>0xd046b030a0b06000e04030a0b064e000e04030a0b0643000d04030a6a0b06000d04030a0b1152000d04030a0b066900050e0403270a0b000d04030a0b6706000d0403020a1c0600050e04030a0f0b000d04030a0b6506002c0e0403270a0b06000d0403020a0b0632000e04030a0b0638000d4c04030a0b06000e042803270a
|12=>0x31f020a0b0600400e04030a0b11060d0403020a1c0f06000d4d5103270b000d4d04030b0622000d4d04030c0b06000d63040a0b0652000d450403020a0f06000e04030c0a0b06000d0403020b062b000d460403020a06000e045303180a0b060d4c04030a0f0b06000e04030a0b063a0d046c030a0b06000e04030a0b064a00
|13=>0x6000d04030a0b7206000d0403020a0671000d0403020a6106000e0403020a0b11060d4d04030c0f0b06000d4504030a0b0632000e04031e180a0b060e043f030a0b06000e04030c0a0f0b0600540e04030a0b06000d0403180b06220054050e04030a0b06000d04030c180b06000d0403700a0b06000d04030a0b066e000d04
|14=>0x31f0c0a0b06000d04030c0a1c0b06000e04030a1c0b060d04031f0a1c0b06000d5a04030a0b06000d4504030c0a0b06000d04030a070638000d043d0a0b063a000d040302180b11060d0403020b065c000d7404030a0b06000d4c4404030a0b06000e040327180b060d043f03180b06000d04030c180f0b0600090504030a0b
|15=>0x60e0403200a0b06050e04030a070b060d04030a0b7706000d04280a0b0652000e04030a0b06760d040327180b110d63043f0a0b06000d04030c0a0706000d04030a0f0668000d04030a0b0675000e0453280a0b060d04030c0a0f0b11000e04030a0f0b110d0449030a0b06000d04030a0b0648000d454604030a0b06000d04
|16=>0xe04030a0b062a000d04030a0b0657000e046f030a0b060d04030a0b0636000d04031f0a0b0600090e04030a0f0b06000d4c04030c0a0b06000d4c4504030a0b06000d04030a0b067b000e040a0b0614000d04030a0b067a000e0403270a070b060e04030a0b062b0d04030a0b0679000d04030a0b0632000e043e03180a0b
|17=>0x630403270a0b06000d454404030a0b06002c0e04030a0b06000d04030a0b062b000d7d4d04030a0b06000d7c04030a0b06000d4d0403020b06000d04030a0b0671000e0428030a0b060e0403020a0b06000d04030a610b06000d4404030c0a06000d043f280a0b06000d04030a0b067f000d7e04030a0b06000d7d04530a0b06
|18=>0xb1106000d450403020a0b06000d043d280a0b06000e0453030a0b06000d04030a0b0685000d510403020a0b06000d04030a0b0662000d046f030a0b06000d04030a0b0684000d04030a0b0683000d0482030a0b06000d04030a0b066d000d04030a0b0681000d040302180b06000d0403270a070b06000d04030a0b0680000d
|19=>0xa0b06000d440403270a0b06000d4d0453030a0b06000d6304530a0b06000d465104030a0b06000d042803270a0b06000d4404030a0f06000d0453030a0b11000d04031e020a0b06000d510403270a0b000d0403020a0706000d04030c020a0b06000d043d030a0b1106000d04030a0b0666000d0403180a0b11060d046f030a
|20=>0xa0b06000d04030c0a0b06000d04030a1c0b06000d4504030a0b06000d040327180b06000d04030a0b0638000d043d530a0b06000d0403020a0b1106000e0403270a0b06000d04031e180a0b06000e04030a070b060d5b04030a0b06000d0403020a0f06000e0403180a0b060d04030a0b0652000d04030a0b066800050e0403
|21=>0xd04030a0b06000d04030a070b06000d6304030a0b06000d5104030a0b06000e04030a0b06000d4404030a0b06000d0428030a0b06000d0403270a0b06000d04030a0f0b06000d04030a0b1106000d043d030a0b06000d0403200a0b0600400e04030a0b06000d043f030a0b06000d4d5103
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x1e60186012600c600660006
|6,0=>0x15f71587151714a7143713c7135712e7127712071197112710b710470fd70f670ef70e870e170da70d370cc70c570be70b770b070a970a2709b7094708d7086707f70787071706a7063705c7055704e7047704070397032702b70247
|7,0=>0x34883408338833083288320831883117309830182fa72f282ea82e372dc72d482cc82c482bc82b482ac82a4829d7295828e7287727f827872708268826172598252724a8242823a8232822a8222821b7213820b820471fd71f671ef71e781df81d871d081c971c181ba71b281ab71a4719c8194818c8184817d7175816d81667
|7,1=>0x491848a7482847a8472846b7464745c8454844c8444843d7436742f7427841f8417840f8408740083f973f183ea73e283db73d383cb83c383bb83b383ac73a4839d7395838e7386837f7377836f83687360835883508
|8,0=>0x69a9692868a8682867996718668966176598651864986409638863086288620861796107608860085f885f085e885e085d885d085c885c085b885b085a8859f9596958e8586857e8575956c9565755d8555854d8545853d8534952c8524851c8513950b850474fc84f394ea94e194d984d184c984c184b984b184a894a174998
|8,1=>0x89f8897888f8887887f8877886f886878608858884f9846983d9835882e7826881e8817780f880787ff87f877f087e887e087d977d277ca87c287ba87b287ab77a2979b7793878b878297799770976977609758874f9747873f8737872f8727871e9717770f870696fe86f686ee86e686de86d596cc96c486bc86b396ab86a38
|9,0=>0xa948a8c8a848a7c8a748a6c8a648a5c8a548a4c8a439a3b8a329a2b7a238a1b8a147a0c8a0489fc89f399ea99e289d999d099c889c089b799af89a7899e9995998d8985897c9973996b8963895b8952994a8942893a8932892a8922891a89128909990188f898ef98e788df88d698ce88c688be88b778af88a78
|10,0=>0xae38adb8ad38acc7ac48abc8ab48aac8aa48a9c8
|11,0=>0xaeb7
|_,_=>0
def wAt:=mkWire dB 134 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xb06414080b0a428010d004180a270b428190a004382d0d004283d0e0a434010b064442b060043401060b438190d00428190300438290e06434010502038190d0042c290a264383e0b064180a0b0a4383d0a00434010b06418090e0a42c290d0042c010e0a434010b0a43401200b42845060040801060b438190d00414080b0a42c010a0f438290d0042c19050202c29
|1=>0xa00434010b06434013e06cf401030a42c190a004382d0d0040c550d00418620a004840f0e0f434010b064840f050b43401020043401060b42c292c06428010e0b43401060a418010e0b434010d00428e92806c0c010e06438290d0042c19030043829060a434010600434010a0f82c190e0c808190b0a438290e06434010b0042c010e0a434010b0a438190f0a43401
|2=>0xd0042871070642c012103c383d0d0042c191806428010d004180a0b0a51029460ad1019040b434010b004283e0b064283d0e0a434010b0651019040b50c013d06c3401030a434012806c0c01030a4b00f06004382d0d00408190600434010b0a4383d0b06434010b004142b0e06434010b0a434010b15418620a004284606004380d0d00428010327418290d0043c29
|3=>0xd0042c19041f8300106024442b06004382d0d00514194506d342d040a4243d0e0a434010b064242f0e0a434010b00418010d0042c190d0040c810a1141801061e81c290d0042c010e06428010d0042c19060049c2d060a428010f0a5182b040f42c190d00430010a0f42c190a0b428010e0b434010b1a4142b0e06434010e0642c190d0042c010d0043c010a0f42c19
|4=>0xb004b0190e0b434010a554142f0e0643401540bc389d0a06434010f0a42c190d0042c014c06c10310a0f42c190906c38290d0040c010e02834010b0a54c2b0d0040c01030640819040a4282d04064140a0e0643401060040c9d060a428010a004283d0b06438190d0042c014e004383e0d0042c19020642c290d0042c01210ac383d0d0042c190e02834010b0a4383e
|5=>0xb005442d040643819070a434010b0041801090bc38290d004283e0e0b434010b064182d0e06434010b0a434012827c281903004840f0e0f434010b06428710706434010b0042c010e0a438190d004340138004283e0b06414080e06434010b0a43401060b418620a00408010e0b434010b0a4107e0c004283d060043829060a43401200b4284506004389d0a0643401
|6=>0x206410290a0b410195a06d6c0d510a410190e0a42c190d0042c01050a438190d0040c01060a428010e03434010b0a428010d0042c19041f8802d0a11418010e0a438190a06434010600438290d0042c19040242c290a004142b0e06434010502c38190b0a40c010327428190d004283d0e0b434010b0642c19040a4282d040643c610a00434010b0641c290b0643401
|7=>0xb1882801040a4182d0b0a410190a0f42c19090b438290d004380d0a06434010e0f434010b0642801060040c290d004282d0b0642d71510ac1019040b4180a0b0a5442b040640c290b00418090b0a42c290d0042c010e06434010300434010a1141801060042801060b42c290906c38290d0042c010a064b00f0e0b434010300438290e0643401060054c2b0d0040c19
|8=>0xe06434010b0641999280ac0c010e0b428190d005141b040242c290d004283e0b065109d0a064102d0300428190d004383d0d0042c19040b4283d0b0643401060040c19040a4282d040642801060b42c29520054c2b0306418010e0a434010a004382d0d0051029040b42c196306c100d030a4382d0d0042c190200434010b0a5182b44064102d0a6143c030b0643401
|9=>0x40641029060282c290f0a4182d040a54c2b040340c1904024182d0b0a408190d0042c290a0b42846060051019040b42c290d00428010306410310a0f42c192806c3401030040db54d06c1029090bc38290d0040cad0a11818010e0f834010b064f41b0d0040c290b2b42846060054c2b060040c1922004180a0b0a438190a064340106684100a0b0a41c190b0a42c01
|10=>0x60a428010a004283d0b06438290e064340106735102b040b5101b040b42c290a0b43c030b06418010d0042c29040a4283d0b065141b4d0b410290d0042c610a0040c9d0a06434010d004283d0b064389d0a06434010a004180a0b0a414290e0643401270b418290a00430030a0f42c196f0ad4c01030643001060242c2906004380d0d0043c010a0b42c19040a42819
|11=>0x4028182d0b0a5343e060b410290d0040c010306418010a0f42c190600434010b0640c810a1141801061e81c290b0051019440a4102d0c004283d0b0643c010a0f42c190706434010b0042871070642c015b0354429040641009060242c290b004283e0b064a01b030040c290b0a418010a005442b0a0b41019045254c2b03065109d0a064102d0a00418290d0040c9d
|12=>0x530040c197c0ac114d03064802d0a11418010e0a434010b06410310a0f42c194d0b410294427c2819040b4b00f0e0b43401040c8283d0b06428190d0042c010d0042846060040847060042c294506d342d040a434010318428010d00428450600438190d0042c01067858c2b040354c2b030040c190d0040c46060041801060a4280103274100d0a06408190b0a42c01
|13=>0x6306c100d530040c194d0bc10290318828015300c0c194d06c1029045380c190a0042c290a0642c014d03c1029040342819440a4102d0e0b434010a11818014d0341029045340c190b0a410294406c102d0d0040c010d0042c290f00c2c19270b42819040b40c9d0a0640c016327c100d0a0641089060282c294d034102903064241b0e0a434012827c2819030043401
|14=>0xa0f82c19030640c29060042c290a06434010b18428010d0042c01510a410190a0b42c190a0043401530ac0c19040282c290e06434010a064102d040a40c19040340c19510b410190a0640c01040b42c19060040c19020042c290a06410190b0a42c01060242c29060040c29280ac0c010a0041801031141801040242c29030040c290d0040c190b11818010a0b41019
|15=>0xb004100d040643401040b40c010a0642c19060040c290a11418010e03434013d0640c29040a410190a0f42c19070642c014d0b41029060a42801
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x250008000
|6,0=>0x12cc47400000000000000000000010d00000fd03d200003a30d540000c5000000002e300002b3000026508901f3000000000001d20650145044c0d402500000000000000000001c80000000000
|7,0=>0x4f0d3844d113044b11284494d21447511a34591133440d0c44211044404cfe33eccf743cd0ef43ad0e833910e043710d843510d043310c843110c042f10b842d4cb322bd0ab429d0a5228509d4265095424508d4225085420507d41e507541c506d41a8c66418905e4169056414904e4
|7,1=>0x1d437411cc47211c447011bc46e11b446c11ac46a11a44681000000019c4668996464cd8f462d187460d17f45f497945d517145b5169459516145751594555151453514a3519143300013f4
|8,0=>0xa50e913a38e8b3a20e853a08e7f39f0e7939d8e7339c0e6d39a8e673990e613978e5b3960e553948e4f3930e493918e433900e3d38e8e3738d0e3138b8e2b38a0e253888e1f3870e193858e133840e0d3828e073810e0137f8dfb37e0df537c8def37b0de93798de33780ddd3768dd73
|8,1=>0xd4cf503d34f4a3d1cf443d04f3e3cecf383cd4f323cc0b2d3ca8f273c90f213c78f1b3c60f153c48f0f3c30f093c18f033c00efd3be8ef73bd0ef13bb8eeb3ba0ee53b88edf3b70ed93b58ed33b40ecd3b28ec73b10ec13af8ebb3ae0eb53ac8eaf3ab0ea93a98ea33a80e9d3a68e973
|9,0=>0x3ce2f30bca2f20bc62f10bc22f00bbe2ef0bba2ee0bb62ed0bb22ec0bae2eb0baa2ea0ba62e90ba22e80b9e2e70b9a2e60b962e50b922e40b8e2e30b8a2e20b862e10b822e00b7e2df0b7a2de0b762dd0b722dc0b6e2db0b6a2da0b662d90b622d80b5e2d70b5a2d60b562
|10,0=>0xf647d81f5c7d61f547d41f4c7d21f447d01
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x231d000000008175000000020250000000080440000000201080000000800000000000d5d8000000022760000000075d800000001044000000004100000000010040000000015d400000000244000000000830000000001000000000002400000000005000000000012000000000044000000000108000000000400000000000c00000000002000000000006800000000010000000000018000000000050000000000100000000000200000000000400000000000
|1=>0x8615d40000020c5750000008311d40000020a7770000008295d40000020a47d0000008291d40000020857f0000008215f4000002085770000008215d40000020227600000080400000000200042000000800010000002000010000007205d4000001c0060000000630080000001081150000003020900000008cd7f0000001245d8000000280180000000840480000001e4760000000415d40000000a7770000000295f40000000a5750000000265d800000009000
|2=>0x80001200000128cc75000004a315d400001288d750000048311d4000012085770000048215d400001008c740000040004300000100004c0000038611f400000e08439000002a795d400000a1a7770000028695d400000a0e4750000028295d400000a08575000001869ddc0000061863e0000018295d4000003c0024000000c001100000028cd7d000000a335d40000028c577000000a315d40000028ad75000000a235fc00000288d7d000000a235dc00000248575
|3=>0x400315dc000100080440000400009bc0001000000600004000000800008008071000012a715d400004698d770000108295fc0000420a57d0000108295dc0000420a5750000108215d4000040015760000100015d800003288c7500000c8215fc0000320857500000c8211f40000320847500000c8001d80000320004c00000c2121940000300857500000c0215b40000300014c00000c0001100000220c47a0000088215dc000022085750000088000300000200c476
|4=>0x400020410001000000040001000200100004000800000010000180000038008000000088c315d40002230c475000088c10110000222084750000884315dc000220090760000880201d800021288d77000084a235d400021248d750000848215dc000212085750000841021100002020857f0000808215f4000202085770000808215d40002004887400008000014c000190280d0000060a21d9c000182087670000608215dc000180800040000408201100001020136e
|5=>0x2000020410008000000050010849235dc0040228c5770010088a15dc004010284720010008a15dc0040022801c00100080001400400088d77001000080158004000080500010000200400040000001e000e0c00019400381008565000e008215f400380208575000a048215d40028020857d000a008215d400201008575000804021594002002085750008000215d40020000804400060c0215d4001812085750006008295d40018020857500060000001000100208575
|6=>0x820000000402010000600008003869dfc02000a0a57500800187b1d40200061e57500800086bddc0200021a57d0080008695d401000a9e7770040002395dc0100000040000240c0215b400880208575002200020020008800001040022000000100088000000100200c8231f40080320857d00200c8215740080320847d00200c8201200080320004c00200c0215f40080300814800200c000530008003c8575002000f00090008003000440020008215d4008001c0060
|7=>0x8000000215f5404002085672006018215d48000020a57d2000008295d48000020857510100082049c400002081050840008695dc210002185770840008410302000400b577080000825ddc200000104080800000091d0144022200170500088a15dc10402209577040120821db41004800104c0400808255dc10018201367040000825ddc1000020136f040000200d940800000040401000000100004000000050010000000100040000000000086028295d402080208575
|8=>0x2002822085758008080215d600101208575800404000512000022085758000008215f600000208575
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x140400
|6,0=>0x40300000000000000018001602000180e0002800000f000280012058200000000081c05018401400000000000010000000
|7,0=>0x350d29a188484c676f83136f22c0c100e2001f806e7198d164b115a201416412d02a71728bc181e1907d0e033e840009c7227538650237806182b868a861068b0d6e301828341d67024f45f128a4366d5f12974e44a1245cb7599ec02933e02826f17c9904e2010b9898560cad42ef80a235c828390302260
|8,0=>0x638e9f45911210e6241db1102d067c01fcc1461fcb2353c0a9d6fa1cb549023651a0c43c64af07e400e30d8495603817e961d1794e4e6890caa6a75401fe6c231993c926e9a9da5b76335823b16bd92eaf54b4c4503378f60ad950bd140831f18c9a3e28165d0594c3b8e6b84f98da47778315acb0381390ab98188d76bd531896ca563219eaef6d9b950aa53b211ef3
|9,0=>0x487bb615ccc4cc1084626b9747091452bcdc4127965d301708ee0c768114d20ac4732db474239e6083b291155afb1da88885150370b88b51bf208b91f3f476a4801d4b462
|10,0=>0x112fb558da00741b9888a4b
|11,0=>0x35
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 46 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_95 10 roots_95 ops++addP pm 1 dom_31 7 roots_31 ops++addP pm 2 dom_126 9 roots_126 ops++addP pm 3 dom_122 7 roots_122 ops++addP pm 4 dom_117 8 roots_117 ops++addP pm 5 dom_47 8 roots_47 ops++addP pm 6 dom_123 9 roots_123 ops++addP pm 7 dom_89 5 roots_89 ops++addP pm 8 dom_111 9 roots_111 ops++addP pm 9 dzo_23_8 5 roots_23 ops++addP pm 10 dom_119 9 roots_119 ops++addP pm 11 dom_59 6 roots_59 ops++addP pm 12 dom_94 7 roots_94 ops++addP pm 13 dzo_119_8 7 roots_119 ops++addP pm 14 dom_62 6 roots_62 ops++addP pm 15 dom_125 9 roots_125 ops++addP pm 16 dzo_55_8 6 roots_55 ops++addP pm 17 dom_21 4 roots_21 ops++addP pm 18 dom_57 4 roots_57 ops++addP pm 19 dom_58 5 roots_58 ops++addP pm 20 dom_60 4 roots_60 ops++addP pm 21 dom_63 9 roots_63 ops++addP pm 22 dom_115 6 roots_115 ops++addP pm 23 dom_118 6 roots_118 ops++addP pm 24 dom_121 6 roots_121 ops++addP pm 25 dom_124 6 roots_124 ops++addP pm 26 dom_55 6 roots_55 ops++addP pm 27 dom_27 4 roots_27 ops++addP pm 28 dom_91 7 roots_91 ops++addP pm 29 dom_61 7 roots_61 ops++addP pm 30 dom_90 5 roots_90 ops++addP pm 31 dom_106 5 roots_106 ops++addP pm 32 dom_107 6 roots_107 ops++addP pm 33 dom_110 6 roots_110 ops++addP pm 34 dom_93 8 roots_93 ops++addP pm 35 dom_120 4 roots_120 ops++addP pm 36 dom_87 8 roots_87 ops++addP pm 37 dom_114 5 roots_114 ops++addP pm 38 dom_92 5 roots_92 ops++addP pm 39 dom_83 5 roots_83 ops++addP pm 40 dom_30 4 roots_30 ops++addP pm 41 dom_23 5 roots_23 ops++addP pm 42 dzo_117_8 6 roots_117 ops++addP pm 43 dom_103 6 roots_103 ops++addP pm 44 dzo_53_8 5 roots_53 ops++addP pm 45 dom_109 6 roots_109 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_23_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_119_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_55_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_23 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_zo_117_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_zo_53_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_109 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_95 10 s (0,roots_95.map (·&&&dom_95)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_95 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 6 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 46 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 107 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 107 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 61 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 61 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 10 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 10 0 = true)
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
def dzo_157_2:=0xcccccccc000000000000000000000000cccccccc
def gzo_157_2:=0xccccccc8000000000000000000000000cccccc80
def gsh_157_2:=0x3333333200000000000000000000000033333320
theorem lowS_zo_157_2_133:Lower true dzo_157_2 roots_157 gzo_157_2 6:=lower_iso_b (d1:=dom_157) (r1:=roots_157) (T1:=gsh_157_2) [(dom_157,2)] (by decide +kernel) (lower_slice_b (T:=gsh_157_2) [(0x3300330000000000000000000000000033003300,0,8),(0x3333000000000000000000000000000033330000,0,16)] (by decide +kernel) lowS_133)
def dzo_189_2:=0xcccccccccccccccc0000000000000000cccccccccccccccc
def gzo_189_2:=0xccccccccccccccc80000000000000000cccccccccccccc80
def gsh_189_2:=0x333333333333333200000000000000003333333333333320
theorem lowS_zo_189_2_133:Lower true dzo_189_2 roots_189 gzo_189_2 7:=lower_iso_b (d1:=dom_189) (r1:=roots_189) (T1:=gsh_189_2) [(dom_189,2)] (by decide +kernel) (lower_slice_b (T:=gsh_189_2) [(0x330033003300330000000000000000003300330033003300,0,8),(0x333300003333000000000000000000003333000033330000,0,16),(0x333333330000000000000000000000003333333300000000,0,32)] (by decide +kernel) lowS_133)
def dzo_173_2:=0xcccc0000cccc00000000000000000000cccc0000cccc
def gzo_173_2:=0xcccc0000ccc800000000000000000000cccc0000cc80
def gsh_173_2:=0x33330000333200000000000000000000333300003320
theorem lowS_zo_173_2_133:Lower true dzo_173_2 roots_173 gzo_173_2 6:=lower_iso_b (d1:=dom_173) (r1:=roots_173) (T1:=gsh_173_2) [(dom_173,2)] (by decide +kernel) (lower_slice_b (T:=gsh_173_2) [(0x33000000330000000000000000000000330000003300,0,8),(0x33330000000000000000000000000000333300000000,0,32)] (by decide +kernel) lowS_133)
def dzo_181_2:=0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc
def gzo_181_2:=0xcc00cc00cc00c8000000000000000000cc00cc00cc0080
def gsh_181_2:=0x3300330033003200000000000000000033003300330020
theorem lowS_zo_181_2_133:Lower true dzo_181_2 roots_181 gzo_181_2 6:=lower_iso_b (d1:=dom_181) (r1:=roots_181) (T1:=gsh_181_2) [(dom_181,2)] (by decide +kernel) (lower_slice_b (T:=gsh_181_2) [(0x3300000033000000000000000000000033000000330000,0,16),(0x3300330000000000000000000000000033003300000000,0,32)] (by decide +kernel) lowS_133)
def dzo_183_8:=0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00
def gzo_183_8:=0xff00ff00ff00ff000000000000000000ff00ff00fe00ec00
def gsh_183_8:=0xff00ff00ff00ff000000000000000000ff00ff00fe00ec
theorem lowS_zo_183_8_21:Lower true dzo_183_8 roots_183 gzo_183_8 7:=lower_iso_b (d1:=dom_183) (r1:=roots_183) (T1:=gsh_183_8) [(dom_183,8)] (by decide +kernel) (lower_slice_b (T:=gsh_183_8) [(0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc,0,2),(0xff00ff00000000000000000000000000ff00ff00000000,0,32),(0xff00ff00ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
def dzo_141_2:=0xcccc0000000000000000000000000000cccc
def gzo_141_2:=0xccc80000000000000000000000000000cc80
def gsh_141_2:=0x333200000000000000000000000000003320
theorem lowS_zo_141_2_133:Lower true dzo_141_2 roots_141 gzo_141_2 5:=lower_iso_b (d1:=dom_141) (r1:=roots_141) (T1:=gsh_141_2) [(dom_141,2)] (by decide +kernel) (lower_slice_b (T:=gsh_141_2) [(0x330000000000000000000000000000003300,0,8)] (by decide +kernel) lowS_133)
namespace S_191
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,129),(2,10),(2,18),(2,34),(3,7),(3,11),(3,19),(3,35),(3,131),(4,5),(4,20),(4,36),(4,132),(6,7),(6,14),(6,22),(6,38),(6,134),(8,10),(8,40),(8,136),(9,11),(9,13),(9,25),(9,41),(9,137),(12,13),(12,14),(12,28),(12,44),(12,140),(16,17),(16,18),(16,20),(16,144),(24,25),(24,26),(24,28),(24,56),(24,152),(32,33),(32,34),(32,36),(32,40),(32,160),(48,49),(48,50),(48,52),(48,56),(48,176),(128,129),(128,132),(128,136),(128,144),(128,160),(130,131),(130,134),(130,138),(130,146),(130,162)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_191.map (·&&&dom_191)
def gM:=goal_191&&&dom_191
def NN:Nat→Nat
|5=>11
|6=>97
|7=>173
|8=>123
|9=>51
|10=>8
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xd02dec6fd4979238e0407395b458b93c5af23ec30c49707456058f1
|6,0=>0xfdcbcf9515f5c87f3613ecc60dddfbd31bfcd4e0cb61dc9008c6feec5865be2bbb893fb62aab50f9b4003b3395b280bac0d3abdefa8b59a865fa4957a03639e8e69d57b94e939332e92abd8aa2e8847b7e8677c90e77db27555d742d9703666e2146c4126b6896af43690976879e67cc967a15669d75f7c95f1185a6ff595ff4ee9549bd7495fd471804544540fef40a423f6d938e8338120365bb36109359813460e2ee162e34c2d2b1289f127fa027c682563524da8242ed22c5821ecf1ebe21e58b1d0571cda11c69f1c2ce1c01819ad01760016b1413713108670f7670ab98096950928c0771d0547603e2803222016bd
|7,0=>0x8e3978ddcb8dc2f8b5828a323894c68549184e998411083d7d806b37f4427d3547bb027b5557a91a7a1267939d7892e77e4a74e4874d1973c387248371cb97192c717926ce9e6b37d689af67c9366dd36604a659ff64d80613575ed025dac95c2ab5828f56c5354c3a511af504264d1394c8304c6ca4b2d54b2444accb49090487154498a4357d41a1840b1f407d33fa4a3f51a3eac53e7ad3db1c3cd933c1d03b6803941838c8f37fd937f0637d8336ffa35a3b33d0d3290a3106630e6d2e4f72d99c2c96f2c8bc2c6872bee12ae812ab3c2858927c0327753268f525e4e24660238f42331822eee21bbc21a531feee1f7351e51a1e2b01e0ec1da941d3631cc621b9131b13717702166ca15f7d106010df6c0cdbb0c7990c2b40bcc50b2560b0570ac340a74f0981908daa076df05154040cf02c8f02ba10256a022fd01fb6
|7,1=>0xff909fdb27fba37f65a8eedf7ee0a7e4d9de260bda990d6217d05e0cdcf2cce3dcb645c9f4bc9e04c925ec8028c63b2c6351c40d4c1441c0460be699bc7adb403ab3a11aef19ae4ecae26aad287ab289a03639f09f9e31699d6198cb1976a1966c89618e95d959276191c468ff908fa53
|8,0=>0xfdbd7faacef871ff6d61f2babf2280e1f68e0770dd153dcc8adb4dddb47cd1de8d18d8d0836cf005cca7dc25fbbff7dbf955b791cb41caac7ccaaec0aa431a8dcaa788ca4774a34c2a2f06a0fd1a0ad19fd489d6149c64c98ea897dc996787957de909518fa458cf75896db86a5785cf0843497c331763987438d735f3723af6e2b56b8356681b662da6555163be763b0562264617f56154f5aa015a8525a53f5902d5615a55c4a52c3f4c39e4bb1d47a3546ab945e4d45d693fc673fb533f2b43d6b43af6738a1f378b534860333db32bbf32a4931d8d3126f2f2da2ded92d5232d3b52ba93254d525343239f222c6921ca9219861f7ab1dd2c1cd2118eaf14a021299a1182f10dee10b620e8380b6d30adc90a179093f0093df084f107b3b06ee106a9e0615805f2c0563d054a002890011e9
|9,0=>0xe43f9e1ba8de30ddb435db075d6de4d0476cf022cb2b5c3587bdef5b60fcaa901a49caa39859e8069b2388b4948871e8390982b80809607cc777a5ff78c3074c656f97d6f66a64801614c95e21b5a55258cc952512444054264e3e38d3a46e35b5b33fec1ebec1e50a1bbc91a2bd147f10e38a0be8c0a15708eca079f106025
|10,0=>0xe03e0b0363af5c957e5d57a9d2eaa6266a611d8d
|11,0=>0x2bff1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffff0000000000000000fafafafafafafafaffffffffffffffff0000000000000000f0f0f0f0f0f0f0f055555555555555550000000000000000555555555555000055555555505050500000000000000000555555555050505000000000000000000000000000000000fffffffffffff0f0ffffffffffffffff0000000000000000ffffffff00000000fafafafafafafafa0000000000000000fafafafafafafafacccccccccccccccc0000000000000000ccccccccccccccccffffffffffffaaaa0000000000000000ffffffffffffaaaaffffffff000000000000000000000000ffffffff00000000fffffffffffff0f00000000000000000fffffffffffff0f0ffffffffffff00000000000000000000ffffffffffff0000ffffffffaaaaaaaa0000000000000000ffffffffaaaaaaaaff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000000000000000000000fafafafafafafafaffffffffffffffff0000000000000000cccccccccccccccc
|0,1=>0xf0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0a00000000000000000000000000000000fffffffffffffafafffffffffffffafa0000000000000000fffffffffffffafafffffffffafafafa0000000000000000fffffffffafafafa555555555555555500000000000000005050505050505050ffffffffffffffff0000000000000000fffffffffffff0f05555555555555050000000000000000055555555555550500f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f00000f0f0f0f0f0f0a0a00000000000000000f0f0f0f0f0f0a0affff0000ffff00000000000000000000ffff0000ffff0000ffffffffffffffff0000000000000000aaaaaaaaaaaaaaaaf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaaffffffffffffffff00000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffff0000fffffffff0f0f0f00000000000000000fffffffff0f0f0f0
|0,2=>0x555555555555555500000000000000005555555555555050ffffffff000000000000000000000000fffffffffafafafa00ff00ff00ff00ff000000000000000000ff00ff00cc00ccffffffffffffffff00000000000000000f0f0f0f0f0f0a0a00000000000000000000000000000000fffffffff0f0f0f000000000000000000000000000000000ffffffffffffaaaaffffffffffffffff0000000000000000ffffffffcccccccc050505050505050500000000000000000505050505050000f5f5f5f5f5f5f5f50000000000000000f5f5f5f5f5f5f0f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0a0a00000000000000000000000000000000fffffffffafafafaffffffffffffffff0000000000000000ffffffffaaaaaaaaffffffffffffffff0000000000000000fffffffff0f0f0f00f0f0f0f0a0a0a0a00000000000000000f0f0f0f0a0a0a0aaaaaaaaaaaaaaaaa0000000000000000fffffffffffffafa000000000000000000000000000000005555555555555050
|0,3=>0xffffffffffff0f0f0000000000000000ffffffffffff0a0a00000000000000000000000000000000ffffffffaaaaaaaaf0f0f0f0f0f0f0f00000000000000000fffffffffafafafa000000000000ffff0000000000000000000000000000f0f0ffffffff0000ffff0000000000000000ffffffff0000f0f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0a0a0a0afffafffafffafffa0000000000000000fffafffafffafffa00000000000000000000000000000000fffafffafffafffaffffffffffffffff0000000000000000fefefefefefefefe0000ffff0000ffff00000000000000000000fefe0000fefeffffffffffffffff00000000000000005555555555555050ffffffffffff00000000000000000000fffffffffffffafaffffffffffffffff0000000000000000fffffffffafafafaffffffffffffffff0000000000000000ffffffffffffaaaaf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0a0a0aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaa0a0
|0,4=>0x555555555555555500000000000000005454545454545454000000000000000000000000000000000f0f0f0f0a0a0a0afff0fff0fff0fff00000000000000000fff0fff0fff0fff0555555555555555500000000000000005500550055005500ffffffffffffffff0000000000000000fffffffffffffafaffffffffffffffff0000000000000000ffccffccffccffccffffffff0f0f0f0f0000000000000000ffffffff0a0a0a0affffffffffffffff00000000000000000f0f0f0f0a0a0a0a000000000000fafa0000000000000000000000000000fafaffffffff0000fafa0000000000000000ffffffff0000fafa000000000000000000000000000000005555555550505050afafafafafafafaf0000000000000000afafafafafafaaaaff00ff00ff00ff000000000000000000fffafffafffafffaffaaffaaffaaffaa0000000000000000ffaaffaaffaaffaa0f0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0f0affffffffffffffff0000000000000000ff00ff00ff00ff00
|0,5=>0xffaaffaaffaaffaaffffffffffffffff0000000000000000eeeeeeeeeeeeeeee00fa00fa00fa00fa000000000000000000fa00fa00fa00faccfeccfeccfeccfe0000000000000000ccfeccfeccfeccfe050505050505050500000000000000000500050005000500ffffffffffffffff0000000000000000fffafffafffafffaf5f5f5f5f5f5f5f50000000000000000f5f0f5f0f5f0f5f0ffffffffffffffff0000000000000000fff0fff0fff0fff0555555555555555500000000000000005550555055505550000000000000000000000000000000005550555055505550ffffffffffffffff00000000000000000f0a0f0a0f0a0f0a00ff00ff00ff00ff000000000000000000aa00aa00aa00aaccffccffccffccff0000000000000000cceecceecceeccee555055505550555000000000000000005550555055505550ff55ff55ff55ff550000000000000000ff50ff50ff50ff50ffffffffffffffff0000000000000000fcfcfcfcfcfcfcfc
|0,6=>0xfafafafa000000000000000000000000fafafafa00000000ffffffff000000000000000000000000aaaaaaaa0f0f0f0f0f0f0f0f00000000000000000f000f000f000f00ffffffffffffffff0000000000000000ffaaffaaffaaffaa
|_,_=>0
def sP:Nat→Nat
|0=>0x2218114107c283045040d247820604500130a10502120099d082811410548843808a082a44210042099b341c302122091a080c109104828714084800a1c5021e2088304384190e401082a6089004009970e448021200391200878808087081a3058714084880a1c30202002840608080
|1=>0x104821c4a087082610802004cb9208281082a4d30446084882a11290045001308948021c209844a90114104c3842008088241050228009990a441822800987088c114105420a0438413321488304384132210114004d1210828114104ce840c087082a1050228209a00a443021220a87
|2=>0x20084882410e100438415080c10e10649045208094004c5841408488264019604040040608a08404821004209a824101824e504120a1c3021200905080c10900483840c080940068206042441522181141054b850e1810f104820a04504151a14203043c412087128228009850e28109
|3=>0x4c202282068c2444210040099822108021e2098b0e18109104822e04500130a441822820a9d2218114004ce910c0870826442022820aa20c58094004d6850e28114004c21004209ac241438a04384130840101004c3845608488241438604044120a105021220a870828114107d504
|4=>0x1408a00261c8860424a002210e022800991081811400bc884060848e10108021c2098d0e443021e504040c08430304822320084882a2c38a0450413081811410bc9044a08a00261c8900424412341c3022820a9a080c114105421004209a6241c22304244120e108021c20a910840109
|5=>0x2c087082a101822820998241030228209a624142060438415261439c04244123c105022820987082810f2821a040c08a0026143021c2098d08711822820a910c08a0026642334a08a082644802104cb920a1c3021c20a842008415266021c04384152210302620098522181002660e84
|6=>0x26482910c084133048e841408a0826483910c0849410485870c08a0826482870c08488244421c045041324442030424a082444206045042f242c20304504132414203042441238903160438413480c31604247080c08a0026d8923065810910483860450413304820604504136a48803
|7=>0x6410302104d3120e11182282099208ec114104c9050e181141054905080c11410549040450413744820304504192410e022820a923a10302280099208cd20228209923a103021c209920840108266c9040c08714104c6a3200cb022820ab20840114104c9062ce0114004c8840c09888
|8=>0x2c08a082a8883e2c0848824c82060438a08267128a2c08a08261c21c0424a0824c8206045040d2418b3980500132210302280098d2218114104cc92088c109104c90420087082a4d2901458114104d9040c0988826482060438a085e49f840c08a08264820a04504133611e822820992
|9=>0x43841322103021250415644420604500130a10302104cc123894316045001338943160438413341030212209922028b021e209a30c5810910542841408a0026119830450413241420a04384134a4031604500134a4031604384130e4480228209924a9031604504130808a00268890a
|10=>0x2428b02280098c0870802280099208708021c20992087120228209920e443021c5041308901821250412681030228209920c5a014004e091080c10e2820991080c11410349110818114104cf901458109004c3910c08a082a442030450415088c8022820a93380c5160450013380c516
|11=>0x65810900482330450413244420228209a22410302282221324412160438413200cb021e209062d0c114004c3840c0849400483840c0848e10482840c08a085e4821004209982478206045041324708062c087082a1c206043ca0824a43160404a0026159060450413241c20a0424a08
|12=>0x4500133248206043841332482022820aa22410e25045041324842060450413244420604504151a4031604040130818114104d012089480228209923828b02280099c145810e104c18a2c0848e10114821250013242c20a04504130828114104cc920e1030262209920808a082714910
|13=>0x4d692200cb020220904200848026483841408714104c20604504151a4820a043ca082610e030438413247018a2c08a082a442240450415261c210045001324108021e209920e1030202504120a11f02282099208f8109282091a082810e28209a3200cb02122092e0c58114004c206
|14=>0x9208a08264820228209c824748860450413241c206045041f241438a045041324108020220992088c11410549848c08a0826492862c08a00261030228209a82474210042441324442100450013161030212209920818131104c9040c08a085e4820a0424a00261050212384130c58494
|15=>0x9610302282099208cce0228209920894114104c9052218114004c8840c08494004c8840c08794104d9a50c58114104ce062c087082a1030202500130a1c30228009920a101821c209920870114004c904060848e104880a2c084133618b4a0404a002618b39043841508b8114104c904
|16=>0x104cfa50c58114104c9332018b022820992200cb022800992200cb021c20992080c114004c9030c581012820903145811410542060424a00264820228209a2241030212384132444210045041324283160424a082a18b0228209ce2418b400424a002618b4d28209cc24103021238415
|17=>0xc08a0826f09043840114104c9062c08a0027489062c0870827489062ce41141054923200cb0228209920c5a88228209923a10302125041324442060438a082610302282098d24ac31604244132418b0228009cf24c82060450415264818a2c08714104d99c0c58114104c90a0c58114
|18=>0x818114104cc122018b021c20a930e1030212504127a18b0228209921458114104d1120c58114104dd123818b022820a92669031604504132418b4d04384152640316042099b24682840c08a08264822b04504132410302025041324105022820a930c5a6c028009b20818114104c904
|19=>0x2410302282099f2414206045041526482030450415241118228209920818114104cc9238405160450413248c8062c08a082a4c3160404a00261148228009920c58114104ea920c58114004d1120a443022820992200cb021220911081810928209924618b0212209920c58114a64c911
|20=>0x104c9062c08a08275c9062ce6014104c9062c0848e105420604504138e4880a2c08a00261050228009ab0658114104c9062c500135a4821004244132418b0228209d624708062c08a002648e100c5810e104c9070840114104c9040608714104c91c4818b022820992480c3160424a08
|21=>0x2018b021e209920c5a014104e0920870114104c9050818114004c905081810e104c9230658114104c9101458109104c9062c08a082a889040c0871410549b22210302282099238943160450413241420a045041324948062c08a0826494862c08494004c904480c114104c9330c58114
|22=>0x1458114104c9230c5811410549862ce4114004c9062c08a08276c9043808494104c9110818114004c316b408a0826483168608a082648e850818114104c90a0c5810928009900c58109004c90a0c5810f28209862c0ac94104c9044808a082a4c91c0618b021c209920a1c3022820992
|23=>0x2c08a0827749062c08a08266c9062c08a5e004c9062d0a014104c9040c08794104c9062d2810928009920c581372800992082810928209920c58114b84c91d0818114104c91c0c58114004c9030c581091c2092e0c58114104c90b0818114104c9490c58114104c9062c08a08272091c
|24=>0x28209920c58114104f0920c5a10228009925618b0228209921418b022820a930c5b0022820a9324708062c08a0826482060438a082648316b008a082648316be08a0826481862c08a002648316045041344488840c08a0826483160438a082a4c18a2c08a0826485062c08494104c906
|25=>0x104c9042008a0826483169a08a082a4c90a0c58114004c3160424a002648316042470826488062c0848826483169b08a082648316043ca0826481862c08714104c9050818114104c9030c5811410549230c58114104c9062c08a0827889290c58114004c9062c08a0827509062d00109
|26=>0x26483160450413c648e062c08494104c9100658114104c9040c08a0026482060424a0826483168008a002618b390424a0826483169408a00264820a04504132418b0228209c1249031604504152648e062c08a0826483160404a0826483167208a0826483168408a082a492030c58114
|27=>0x18b0228209921418b0228209922018b0228209920818114104c9062c08a0026483160424a0826483168008a0826483168408a0826483160450415
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x3c60366030602a6024601e60186012600c600660006
|6,0=>0x1f771f071e971e271dc61d571ce71c771c071b971b271ab71a4719e6197719071897182717b7174716d7166715f71596152714b7144713d7136712f71287121711a7113710c710570fe70f770f070e970e360dc70d570ce70c770c070b970b270ab70a4709d7096708f70887081707a7073706c7065705e70577050704970427
|6,1=>0x2dc72d572ce72c772c072b972b272ab72a4729d7296729062897282727b7274726d7266725f72587251724a7243723c7235722f62287221721a7213720c720571fe7
|7,0=>0x4c574be74b774af84a874a08498849084888481747a7473746b8463845b8453844c7444843c8435742e7426841e8416840e8407740073f883f083e973e183d983d273cb73c473bc83b483ac83a5739d8395838d8386737e8376836e8366835e8357734f8347833f833783307328832083197312730a830282fb72f382eb82e38
|7,1=>0x6b076a886a08699769186898682767a8672866b7663865b8653864c7644863c8635762e7627761f861876108608860175fa75f375eb85e385dc75d575ce75c685be85b685af75a7859f8597858f8587857f857875708568856085588550854885417539853185298522751b7514750c850484fc84f484ec84e484dc84d484cc8
|7,2=>0x80077f887f087e977e277da87d287ca87c377bc77b487ac87a5779e7797778f87887781777a7773776b8763875b8754774d7746773f7737872f8728772087197712770b770476fc86f576ee76e686de86d776cf86c786bf86b78
|8,0=>0x9ff99f789ee99e779e079d889cf99c699bf79b879b089a889a089997990998889817978997089688960895889508948893f9937892f8926991f791789107909790188f988f188e988e188d988d098c888bf98b788af88a7889f8896988e8885987d8875886c9864885c8855784d8846783e8837782f8827881f8817880f88078
|8,1=>0xbd98bd09bc88bc08bb97bb18ba98ba18b998b918b898b818b798b718b698b618b598b527b4a8b428b399b318b298b218b198b118b089b008af88af08ae97ae18ad98ad18ac98ac18ab98ab09aa79a9f8a969a8d9a858a7d8a758a6d8a667a5e8a577a516a498a427a3b7a338a2a9a219a198a118a089
|9,0=>0xd768d6d9d658d5e7d568d4f7d469d3e8d377d2f8d269d1e8d168d0e8d068cfd9cf67ced9ce67cde8cd68cce8cc68cbe8cb59cad8ca58c9d8c958c8d8c858c7c9c748c6c8c648c5c8c539c4a9c428c3a8c328c2a8c228c1a8c128c0a8c019bf98bf18be98be18
|10,0=>0xdb48dac8da57d9e7d968d8e8d868d7e8
|11,0=>0xdbc7
|_,_=>0
def wAt:=mkWire dB 100 192 0xffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x8510c59124b1049083928490c59285526491c4d28490c49084d08510c59384b0c39265128490c592649124b284d0c590a4f085108490c4d08510c590825284d0c590c593a4b1049085126510c490c5910490a4d08510c590c252651263a284908390c59284908390c592849084d08510c490c5910491249284d0c592a512649
|1=>0xa4908510c59225108490c590c590c59104926510c59104908490c592a5126490c5908250c59284d0a4d08510c59065308490c590c491049084d08510c590c591049124b0c59284d0c51204b084d0c590c59285626490c592649204d0c510c59124b0c010c59284d1049124b10490c4d284d0c511049084d08510c5926511049
|2=>0x225308490c5932490a4f08510c590c4d28490c5126490c4d225308490c59645308550c59264926490c590c25284d084d08510c591c4d28491049204d0c5920490c510c590c25284d26490c5928496450224d08490c5910490825284d0c490c5910490c590c25284d344f22510c59224f0c511c4d284920490c590c5126490c59
|3=>0xc59264920490c510e49084d0c590c51724b0425284d10496450224d08490c59225308490c5908250c59284d0c490c590a4b08510c59284d084d08510c590c25284d0c590c4d0849284d0c59344f22510c590a4b08510c590c4d265108510c590c4d064906510c4d284906490c4d28492cde1201284d10490c39284d0c4d2849
|4=>0xc592649384b204d0c516450344f08390c5928492a532649263a0c490c5928497c510c59064b0c4d645308550c59264920490c590c510cf1083a0c5928490c59264908510c590c4d0c5948530c5526490a4f08510c590c4d0c2526510c59264908250c59284d10490c550c5926490a4d08510c59263a0c510c592849224f0849
|5=>0xc490c5910490c4908510c5928491049384b204d384b204d0c510849084d0c590c510649384b06510c4d0c5906530c4d104906530c490c4d26490c512651064b0c4d085526490c59384b204d0c51084d0c590c25284d2635224f08490c59042510490449284d1049224f08490c590a4f08510c590c59284d0c3928490c512849
|6=>0x449044d0c4d08490c5928490c4d224f08490c592a5326490c510c49265110490849084d0c5926490c4d08490c5926490c59264920490c5106510c490c4d104906510c4d284926510c59224d08490c59104934530a4908510c59384b06510c4d1049384b06510c4d08390c5928492a510c490c512649204926510c5126490851
|7=>0x284912490c4d284d0c5110490405124b284d084d0c59284d10490c592849344f0a490c590c51225308490c593a4b0825284d204d0c5126492a512649124b0c01284d10490e49084d0c59084d0c59284d0c490c49204f0c511049204d0c590c511049204d0c510c5928490c59065106490c4d0c5906490c5926510c4d10498453
|8=>0x224f08490c59124b26510c5110490a57085126490c59384b204d0c510c250c49284d104906510c490c4d28490c49284d0c4d28490c010c59284d10490c490a4b08510c590a4f08510c490c5964500e490c5920570c510c59264910490c4d284d0c510c5906390c4d2849065308490c590c4d2661225308490c59144d0c490c51
|9=>0x264912490c59284d0c490c5906510c4d284906510c490c4d26490c5508490c5926491049084d0c590c510c512a510c592649124b284d064b08510c590c4d064b0c5926510c4d0c490c59284920490c5126510c4d10490c05124b284d0a4f08510c5910490a4f08510c590c59264906530c4d0c59384b204d0c51164d0a4b0851
|10=>0x124b0c59284d0c510c3928490c5926490d1d0826284d0c591049384b204d0c512836224f08490c59284d0c51104908490c590c510a4b08510c59645008550c592649344f08390c592849284d0c490c5910490c49284d0c592849284d520b0c011049124b0c4d284d0c5110490c59284d0c51084d0c490c592849644f08550c59
|11=>0x284d0c591c4d2849664b06390c4d2849204d28490c512649124b0c59284d10491049084d08510c590c4d08510c5928490c5906510c4d10490c59284d0c4d2849263a0c490c512849124b284d104928490425284d26490c590c05124b284d0c590c7d2856264944490c5906530c4d0825284d0c592a5326490c49084d08510c59
|12=>0x28562649384b204d0c51464d20490c510c510c4d10490c510c4d28490c590c4d10490c4d124b284d0c490c4d26490c59284d10490c5906530c4d284d0c59284908490c590c51284d0c492649063b0c4d284910490449284d804f04490451284d26490c5928490c59204d0c510c59384b204d0c511049085108490c5910490849
|13=>0x28490a4908510c590c59204b0c510c59124b284d0c490c59264910490449045108550c592649083a0c5928490c59204d0c519a4f104904519a4f284904510425284d26490c4d20490c51046d263a28490825284d0c5908490c592849224f08490c59284d204b0c5127420051104908550c5926490c490c4d2849204d0c510c49
|14=>0xa4f08510c590c49204d0c51264920490c51124b284d10490c010c59104982498453044d06530c4d1049085108490c590c4d284d0c510849284d0c59284d0c392849115104562649225308490c5928490c512649084d284d0c597c51064b0c4d0c4906530c4d48530c552649204d0c5126490c5526492649284904510c51263a
|15=>0xc4d06390c4d2849b04f9a49045104250449284d284d284926490826284d0c590c490c5110490c490c5910490c4d204b0c51520b0c0110490c59284d0c519a5726490451204d0c5110492849204d0c51084d0c590c510c4d0c592849065106490c4d284d06490c4d2a530c59264908510c5926490c4d0c5926490c390c592849
|16=>0x284d104926510c51104928550c4926492931804f04490c550c59264906510c4d2849084d08510c592a510c51264984530449044d0c59204d0c5108510c59104908510c5928490c390c4d28490c49284d0c51264906530c4d26490c592849224d08490c59384b204d0c5108510c490c59384b204d0c510c01284d10490c590649
|17=>0x1c4d0c5928490401284d10491201284d10490c59284d0c4911750426284d0825284d0c5906510c4d1049284d0c4d28490c05124b284d0a4b08510c590c7d28562649444906530c4d0c49204d0c5120490c5126490425284d104980270449284d0c590c25284d08490c59104980250449284d0405124b284d0a4d08510c590c49
|18=>0x284d104926512849284d0c510451044d285526490c4d284908510c590c4d26490c3928490c5626490c011049045626490449284d805304491049044d204b0c510c49264904552649204d0c510c5928499a490451844b044d0c4d104906530c4d08490c59284926490c490c4d284d0c490426284d263a2849004d10490449044d
|19=>0xc490c510c591049284d0449044d26490c26284d0c25284d0c4d0c510c591049284d0c59044910490425284d040110490c490c598453044d0c552649204d0c51124b284d8451044d2649044d06490c4d0c590c51264904510c491049
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1540190000000000000108002000000000000000
|6,0=>0x1c8c381000000001bc436186930cc6000030a80000c0216d42c180000ae215482a08504000012d4000046500000000000042407c80f081c9800006e400001a9000006280c040000000056a0000000000005240000000028104c40890000000003e600000f08000000007080ba81430244040806980a3
|6,1=>0xa6500002908518800013e80000000000013c200004ca8945000023d447088c2114422444390852000020500000000000020043e987a300001e443c08753
|7,0=>0x30a86050bea00002f285d8cb9996f42d6859d0b1a15f42b86564caaa151429a85250a31942427c84ecc9d0936426844c10962128424a6485090091c42308451088210c42126418c8120ff31f863e107a20f041da63a507408e531c28378c6d20d731a6833d065a0c83188830105e98b9416a82c5056a0ab2
|7,1=>0x4ce8994930a25d44b46959129224e4496691d121a240347a68e511b1a32445c88a91132222443c886910b9a13441e882d103a20343fe87ed0fba1f343e247b8cf521e733c867888ef21db33ae874d0e7a1cb438e87184e12000037c86e90db21b4236086b10d421a443408674ccd91974326863d0c619893
|7,2=>0x30d40000c28d83230245fc8bf097c22f445e08bb117422e445c08b7116c9ad545a28b35164a2c635884b0115e22b845688ac115622aa254c8a8cd4fa29b452e8a4d147a28b450e8a0d13fa27b44ee89cd137a26b4
|8,0=>0x7986f24de31bc337806ef4ddd1bb737686ec4dd71bab37506e94dd11b9f37386e64dcb1b9337206e34dc51b87370a4e08dbf9b7c36f26dd8db99b7036da6da8db39b6436c26d78dad9b5836aa6d48da79b4c36926d18da19b41267c6cecd9c1b3536646cbcd961b29364c6c8cd901b1d36346c5cd8a1b113
|8,1=>0x11f4e3d1c7738e871c4e371c6b38d07194e311c5f38b87164e2b1c5338a07134e251c4738887104e1f1c3b387070d4e191c2f385870a4e131c2338407074e0d1c1738287044e071c0b38107014e011bff37f86fe4dfb1bf337e06fb4df51be737c86f84def1bdb37b06f54de91bcf3
|9,0=>0x1390a7114e029bc5370a6d14d829ac5350a6914d0299c5330a6514c8298c5310a6114c0297c52f0a5d14b8296c52d0a5914b0295c52b0a5514a8294c5290a5114a0293c5270a4d1498292c5250a491490291c5230a451488290c5210a4114802
|10,0=>0x9da33b06758cea19d233a06738ce61
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 15
def pmP:Nat→Nat
|0=>0x11800000000086000000000420000000001b9000000000dc0000000006c000000000340000000001390000000009c000000000480000000001400000000009000000000040000000000190000000000c0000000000400000000001c0000000000d0000000000600000000002e000000000140000000000800000000003c000000000180000000000a0000000000400000000001800000000008000000000030000000000100000000000400000000000
|1=>0x84480000000404e40000002005a00000010010000000030110000000180800000000c0140000000600800000003001800000018000000000092500000000403800000002014000000010004000000080000000000200000000000e0a0000000044300000000203000000000890000000004000000000010c000000000858000000004200000000020a0000000010400000000081800000000408000000002020000000010080000000080000000000238
|2=>0x6881c8000003048a400000182072000000914bd0000004381c8000002040f4000001020560000008101b0000004029c8000002010e40000010017a0000005800100000028c9c8000001446e4000000a2002000000414080000002021f00000010105800000080820000000401b00000002002000000008007000000040024000000200100000001000600000008001000000040004000000200000000000c00080000004a2e40000002517000000011000
|3=>0xe881f8000007440e40000032717a000001538b9000000a9c5c0000005464ec000002a3120000001511bb000000a889c8000004464e4000002231620000011083a0000008840e8000004404f400000220174000001028b80000008045c0000003c10d4000001ae076000000d503900000068c9c8000003460fc000001a307a000000d183900000068a1e8000003446e4000001a227e000000d11390000006885e8000003442e4000001a207a000000d103b
|4=>0x1688dc800000b442fc000005a2176000002d103f0000016881e800000b440ec000005a2072000002d1019000001488de800000964000000004a317600000251839000001288dc8000009446c4000004a2340000002510b90000012880c0000009006e0000004803600000024013800000108c1c8000008446c00000042106a0000021013b000001000dc0000008006a000000400140000002000200000010000400000074e2e4000003a285a000001d113b
|5=>0x800001000003b460ec00001da237200000ed103f00000668c5c8000033460f4000019a307200000cd142d0000066889e8000033444e4000019a207a00000c9081e00000528c4c0000029442e4000014a207200000a500bd000004488dc8000021446e400000da2076000006d1019000003088dc0000013440e40000092203200000411898000001e881d800000d444ec000006a006a0000031190200000168c1d800000b446fc000005a237a000002d11bb
|6=>0x1068c9d8000083460fc000041a3076000020d153f0000106889d8000083440f4000041a2076000020d103900001028c8c0000081460e4000040a22720000204492800001008c8c0000080450d40000400801400002001411000010000840000072440f0000031202720000120101d00000888c168000043800740000212227a0000108403d0000084009e8000041000f80000208000000001000024000008000100000040000400000200001000001000006
|7=>0x10868c1e8000843450b4000421a207a000210008240001080000b000084000024000400a005a000200200040001000800e8000613640e4000308b00640001841803000003000208000010100020000080000300000400000c0000200000400001000001000008000000000023d103f000011e881d800008d440ec000046a20420000235101100001128c1d0000087440ec000042a21740000215001d000010808c10000083564f4000041ab272000020d1d3f
|8=>0x10000000000052013440e4028009a2072011000d10390084104881c8040083440ec02000822072010004110190080016881d8040003440e402000122072008212000580041087080e802080b441f4010404820a8008060d103d00403020a0b0020180010c00100c000002008002e101d0040007881e80180200408400811982072004004c9039000c016881d800600a44084002001a2072000800d10390002034880c000100200000000423a285a00021100228
|9=>0x8020466881ca001213440e500090100064604000d103b2020466081c8810003440e4302041a2076115004d10390888106881d8444003440e422104322076110820d103b0880006881c841601b440e420300522072094006d103b04a0026881c824000b440ec120001a2072080000d10390200c26c81e8100073450b0080039a207a04000cd143d
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x200400000000202000000000
|6,0=>0x2d000082000068006c00008003226000440221108044202000500000000040c0600004020300010040000004140a030001000008f008000080802150010c0040000000008039103a000100004000404c00001f80000310100000011582c0000088000200000400e0a108080c06
|7,0=>0x529183c3e601bd2cc261860364b1523d8a1755a2948f47cbf090555896c40f169ba6064722b047a4b42918a80423aa0344c198046a108c0941c23599b9a42c4306444f37d2110a1d741e59c3065a0d080d19335ae92778645d0d8c8a8144238859da50771ccaeef24964020c643dc38111c044e424163c1522a028480206650a018287db301ecf851d40c1f7189de4bf
|7,1=>0x608f8e8ad222708c6e914c02188af441da05062e9698e0a2302112412c1449af85c308ba5e5a1d01a8b58025a0e40ca385e4a
|8,0=>0x3b26b33354d224bd53265fad83224cf72a9228a41164cc517cb275491c08789baa2a9790c04f8956ab9a1c8e7fa31eae236c5a2aeb4e2ed74528427a088746c2cca346a3698cdc3ebf50e6f5648e0ab67f2809e7c990a5cb0c3214cd8931ccb4ef002e26dbd1d881fd431e8dca4e07e88a04ce9084c3cf43b6b17da2ae3c2dd28df5e3254e67739925115
|9,0=>0x26940665aa724f079b1a638df4fa66572f7098e58b956a9d3b2b75a01fadb41365ed1a9349660626ecc53e7f8b4b96c6433b98d6a38b9fa6f16
|10,0=>0x34188c2aa4d49638d9
|11,0=>0x5f
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 45 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_189 10 roots_189 ops++addP pm 1 dom_58 5 roots_58 ops++addP pm 2 dom_143 7 roots_143 ops++addP pm 3 dom_187 9 roots_187 ops++addP pm 4 dom_190 9 roots_190 ops++addP pm 5 dom_63 9 roots_63 ops++addP pm 6 dom_170 5 roots_170 ops++addP pm 7 dom_155 6 roots_155 ops++addP pm 8 dom_158 6 roots_158 ops++addP pm 9 dom_43 5 roots_43 ops++addP pm 10 dom_47 8 roots_47 ops++addP pm 11 dom_31 7 roots_31 ops++addP pm 12 dom_175 10 roots_175 ops++addP pm 13 dom_27 4 roots_27 ops++addP pm 14 dom_30 4 roots_30 ops++addP pm 15 dom_157 8 roots_157 ops++addP pm 16 dom_151 8 roots_151 ops++addP pm 17 dom_174 7 roots_174 ops++addP pm 18 dom_159 9 roots_159 ops++addP pm 19 dom_183 9 roots_183 ops++addP pm 20 dom_59 6 roots_59 ops++addP pm 21 dom_186 6 roots_186 ops++addP pm 22 dom_61 7 roots_61 ops++addP pm 23 dzo_157_2 6 roots_157 ops++addP pm 24 dom_171 7 roots_171 ops++addP pm 25 dom_62 6 roots_62 ops++addP pm 26 dom_46 5 roots_46 ops++addP pm 27 dzo_189_2 7 roots_189 ops++addP pm 28 dom_21 4 roots_21 ops++addP pm 29 dom_139 4 roots_139 ops++addP pm 30 dom_181 8 roots_181 ops++addP pm 31 dom_179 6 roots_179 ops++addP pm 32 dom_182 6 roots_182 ops++addP pm 33 dzo_173_2 6 roots_173 ops++addP pm 34 dzo_181_2 6 roots_181 ops++addP pm 35 dom_142 4 roots_142 ops++addP pm 36 dzo_183_8 7 roots_183 ops++addP pm 37 dom_42 4 roots_42 ops++addP pm 38 dzo_141_2 5 roots_141 ops++addP pm 39 dom_55 6 roots_55 ops++addP pm 40 dzo_55_8 6 roots_55 ops++addP pm 41 dzo_181_8 6 roots_181 ops++addP pm 42 dom_184 5 roots_184 ops++addP pm 43 dom_53 5 roots_53 ops++addP pm 44 dom_188 7 roots_188 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_191 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_157_2_133 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_189_2_133 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_173_2_133 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_181_2_133 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_183_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_141_2_133 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_55_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_zo_181_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_188 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_189 10 s (0,roots_189.map (·&&&dom_189)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_191 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_189 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_191==dom_191)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_191 gM v ys):RunD true dom_191 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_191 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 11 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 97 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 97 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 173 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 45 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 173 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 123 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 123 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 51 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 51 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
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
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,65),(1,129),(2,10),(2,18),(2,66),(3,7),(3,11),(3,19),(3,67),(3,131),(4,5),(4,20),(4,68),(4,132),(6,7),(6,14),(6,22),(6,70),(6,134),(8,10),(8,72),(8,136),(9,11),(9,13),(9,25),(9,73),(9,137),(12,13),(12,14),(12,28),(12,76),(12,140),(16,17),(16,18),(16,20),(16,80),(16,144),(24,25),(24,26),(24,28),(24,88),(24,152),(64,65),(64,66),(64,68),(64,72),(64,80),(64,192),(128,129),(128,132),(128,136),(128,144),(128,192),(130,131),(130,134),(130,138),(130,146),(130,194)]
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
addP pm 0 dom_222 10 roots_222 ops++addP pm 1 dom_95 10 roots_95 ops++addP pm 2 dom_221 10 roots_221 ops++addP pm 3 dom_219 10 roots_219 ops++addP pm 4 dom_215 10 roots_215 ops++addP pm 5 dom_207 10 roots_207 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_223 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_207 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_222 10 s (0,roots_222.map (·&&&dom_222)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_223 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_222 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
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
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xffff000000000000ffff000000000000ffff000000000000ffff00000000,1,33)] (by decide +kernel) lowS_207
theorem lowS_247:Lower true dom_247 roots_247 goal_247 12:=lower_slice_b [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_245
theorem lowS_251:Lower true dom_251 roots_251 goal_251 11:=lower_slice_b [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,8,10)] (by decide +kernel) lowS_249
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_slice_b [(0x3300330033003300330033003300330033003300330033003300330033003300,32,40)] (by decide +kernel) lowS_245
def isoMvS_254:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 11:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_251
namespace S_255
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,65),(1,129),(2,10),(2,18),(2,34),(2,66),(3,7),(3,11),(3,19),(3,35),(3,67),(3,131),(4,5),(4,20),(4,36),(4,68),(4,132),(6,7),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(8,136),(9,11),(9,13),(9,25),(9,41),(9,73),(9,137),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,18),(16,20),(16,80),(16,144),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,36),(32,40),(32,160),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,68),(64,72),(64,80),(64,192),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,132),(128,136),(128,144),(128,160),(128,192),(130,131),(130,134),(130,138),(130,146),(130,162),(130,194)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|10=>1
|11=>7
|12=>2
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|10,0=>0x50648
|11,0=>0xd5b43cb51bc8fbdbfa67a65ea051cb03b34
|12,0=>0x86e2a7d8d4
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfffffafafffffafafffffafafffffafafffffafafffffafafffffafafffffafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa5555505055555050555550505555505055555050555550505555505055555050ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0ffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafaccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x7a48291076a4829107a438291076548291076a4329107d6a4829107da43829107da4829107a4829c107a4829b1076543210
|_=>0
def sO:Nat→Nat→Nat
|10,0=>8
|11,0=>0x1025bcada4746a48c889
|12,0=>0x294c99
|13,0=>0x5b8
|_,_=>0
def wAt:=mkWire dB 14 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2a1896a5a86a1985a5a868d8968d8968e895a7a86a5a8661
|_=>0
def oO:Nat→Nat→Nat
|10,0=>3
|11,0=>0x3c9a4b2491c8a432
|12,0=>0x24311
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 9
def pmP:Nat→Nat
|0=>0x1fff7fbff5fe7fc7f800
|_=>0
def pmB:Nat→Nat→Nat
|10,0=>1
|11,0=>0x166d93
|12,0=>0x1a
|13,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 11 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_253 12 roots_253 ops++addP pm 1 dom_191 12 roots_191 ops++addP pm 2 dom_127 12 roots_127 ops++addP pm 3 dom_247 12 roots_247 ops++addP pm 4 dom_223 12 roots_223 ops++addP pm 5 dom_251 11 roots_251 ops++addP pm 6 dom_254 11 roots_254 ops++addP pm 7 dom_239 11 roots_239 ops++addP pm 8 dom_250 8 roots_250 ops++addP pm 9 dom_235 8 roots_235 ops++addP pm 10 dom_238 8 roots_238 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_238 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_253 12 s (0,roots_253.map (·&&&dom_253)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_253 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 7 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 2 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 2 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [1, 7] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [4, 9] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.and, inputs := [11, 12] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.and, inputs := [3, 14] }, { op := GateOp.and, inputs := [7, 10] }, { op := GateOp.and, inputs := [6, 4] }, { op := GateOp.and, inputs := [0, 2] }, { op := GateOp.or, inputs := [13, 15] }, { op := GateOp.or, inputs := [19, 16] }, { op := GateOp.or, inputs := [20, 17] }, { op := GateOp.or, inputs := [21, 18] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_53034_aux

theorem PEqualNP.Outside.L_meta_53034 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_53034_aux.main
