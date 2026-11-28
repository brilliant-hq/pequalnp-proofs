import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52388_aux
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
def goal_27 : Nat := 0xeeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfefaee00fefaee00fefaee00fefaee00fefaee00fefaee00fefaee00fefaee00
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xfcfcfcfccc00cc00fcfcfcfccc00cc00fcfcfcfccc00cc00fcfcfcfccc00cc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfefefefeee00ee00fefefefeee00ee00fefefefeee00ee00fefefefeee00ee00
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfcfcfcf0f00000fcfcfcfcf0f00000fcfcfcfcf0f00000fcfcfcfcf0f00000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefefefafa0000fefefefefafa0000fefefefefafa0000fefefefefafa0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfafafafafafaaa00fafafafafafaaa00fafafafafafaaa00fafafafafafaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfcfcfcfcfcf0cc00fcfcfcfcfcf0cc00fcfcfcfcfcf0cc00fcfcfcfcfcf0cc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfefefefefefaee00fefefefefefaee00fefefefefefaee00fefefefefefaee00
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

def dom_81 : Nat := 0x300030000000000030003
def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffeeeeffffeeeeaaaa0000aaaa0000ffffeeeeffffeeeeaaaa0000aaaa0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xffffaaaaffffaaaafafa0000fafa0000ffffaaaaffffaaaafafa0000fafa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xffffccccffffccccf0f00000f0f00000ffffccccffffccccf0f00000f0f00000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xffffeeeeffffeeeefafa0000fafa0000ffffeeeeffffeeeefafa0000fafa0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffffaaffffffaaaaaaaa00aaaaaa00ffffffaaffffffaaaaaaaa00aaaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffffccffffffcccc00cc00cc00cc00ffffffccffffffcccc00cc00cc00cc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffeeffffffeeeeaaee00eeaaee00ffffffeeffffffeeeeaaee00eeaaee00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xffffff00ffffff00f0f00000f0f00000ffffff00ffffff00f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xffffffaaffffffaafafaaa00fafaaa00ffffffaaffffffaafafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xffffffccffffffccfcf0cc00fcf0cc00ffffffccffffffccfcf0cc00fcf0cc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xffffffeeffffffeefefaee00fefaee00ffffffeeffffffeefefaee00fefaee00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfafafafaaaaaaaaafafafafa00000000fafafafaaaaaaaaafafafafa00000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfcfcfcfcccccccccfcfcfcfc00000000fcfcfcfcccccccccfcfcfcfc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefeeeeeeeeefefefefe00000000fefefefeeeeeeeeefefefefe00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccffccffcccccccccccc00cc00ffccffccffccffcccccccccccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeffeeffeeeeeeeeeeee00ee00ffeeffeeffeeffeeeeeeeeeeee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffaffaaffaafafafafaaa00aa00fffafffaffaaffaafafafafaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcffccffccfcfcfcfccc00cc00fffcfffcffccffccfcfcfcfccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffeffeeffeefefefefeee00ee00fffefffeffeeffeefefefefeee00ee00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffaaaaffffaaaaaaaaaaaaaaaa0000ffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffccccffffcccccccccccc00000000ffffccccffffcccccccccccc00000000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffeeeeeeeeeeeeaaaa0000ffffeeeeffffeeeeeeeeeeeeaaaa0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffff0f0ffff0000f0f0f0f0f0f00000fffff0f0ffff0000f0f0f0f0f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafaffffaaaafafafafafafa0000fffffafaffffaaaafafafafafafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcffffccccfcfcfcfcf0f00000fffffcfcffffccccfcfcfcfcf0f00000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefeffffeeeefefefefefafa0000fffffefeffffeeeefefefefefafa0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffffaaaaaaaaaaaaaaaa00ffffffaaffffffaaaaaaaaaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffffcccccccccccc00cc00ffffffccffffffcccccccccccc00cc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffffeeeeeeeeeeeeaaee00ffffffeeffffffeeeeeeeeeeeeaaee00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0ffffff00f0f0f0f0f0f00000fffffff0ffffff00f0f0f0f0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffaffffffaafafafafafafaaa00fffffffaffffffaafafafafafafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcffffffccfcfcfcfcfcf0cc00fffffffcffffffccfcfcfcfcfcf0cc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffeffffffeefefefefefefaee00fffffffeffffffeefefefefefefaee00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaee00ee00ee00ee00ee00ee00ee00ee00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_142 : Nat := 0x555500000000000000000000000000005555
def goal_142 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0cc00cc00cc00cc00cc00cc00cc00cc00
def roots_142 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffafffafffafffafffafffafffafffaee00ee00ee00ee00ee00ee00ee00ee00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_145 : Nat := 0x3000300000000000000000000000000030003
def goal_145 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_145 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_148 : Nat := 0x11001100000000000000000000000000110011
def goal_148 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_148 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafafafa0000fafa0000fafa0000fafa0000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffff00ffffff00ffffff00ffffff00cc00cc00cc00cc00cc00cc00cc00cc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffaaffffffaaffffffaaffffffaaeeaaee00eeaaee00eeaaee00eeaaee00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfffffff0fffffff0fffffff0fffffff0f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffafafaaa00fafaaa00fafaaa00fafaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fcf0cc00fcf0cc00fcf0cc00fcf0cc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffafffffffafffffffafffffffafefaee00fefaee00fefaee00fefaee00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0fcfcfcfc00000000fcfcfcfc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfefefefefafafafafefefefefafafafafefefefe00000000fefefefe00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffeeffeeffaaffaaffeeffeeffaaffaaeeeeeeeeee00ee00eeeeeeeeee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0f0f0f0f000000000f0f0f0f000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffafffafffafffafffafffafffafffafafafafaaa00aa00fafafafaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffcfffcfff0fff0fffcfffcfff0fff0fcfcfcfccc00cc00fcfcfcfccc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffefffefffafffafffefffefffafffafefefefeee00ee00fefefefeee00ee00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffaaffffffaaffffffaaffffffaaaaaaaaaaaaaaaa00aaaaaaaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffeeffffffaaffffffeeffffffaaeeeeeeeeeeaaee00eeeeeeeeeeaaee00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffff0fffffff0fffffff0fffffff0f0f0f0f0f0f00000f0f0f0f0f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffafffffffafffffffafffffffafafafafafafaaa00fafafafafafaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffcfffffff0fffffffcfffffff0fcfcfcfcfcf0cc00fcfcfcfcfcf0cc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffefffffffafffffffefffffffafefefefefefaee00fefefefefefaee00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_193 : Nat := 0x3000000000000000300000000000000030000000000000003
def goal_193 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000
def roots_193 : List Nat := [xs256.getD 0 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0cccccccccccccccc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

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
def goal_202 : Nat := 0xffffffffffffffffff00ff00ff00ff00ffccffccffccffcccc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffeeffeeffeeffeeee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfffffffffffffffffff0fff0fff0fff0ff00ff00ff00ff000000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffffafffafffafffaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffffffffffffffffff0fff0fff0fff0ffccffccffccffcccc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffafffafffafffaffeeffeeffeeffeeee00ee00ee00ee00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_208 : Nat := 0x10001000000000001000100000000000100010000000000010001
def goal_208 : Nat := 0xffffffffffffffffffff0000ffff0000ffff0000ffff00000000000000000000
def roots_208 : List Nat := [xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffeeeeffffeeeeaaaa0000aaaa0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffffffff0f0fffff0f0ffff0000ffff0000f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffffafafffffafaffffaaaaffffaaaafafa0000fafa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffffff0f0fffff0f0ffffccccffffccccf0f00000f0f00000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffafafffffafaffffeeeeffffeeeefafa0000fafa0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffff00ffffff00ffffffccffffffcccc00cc00cc00cc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffeeffffffeeeeaaee00eeaaee00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffffffff0fffffff0ffffff00ffffff00f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffffafffffffaffffffaaffffffaafafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffff0fffffff0ffffffccffffffccfcf0cc00fcf0cc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffafffffffaffffffeeffffffeefefaee00fefaee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffffffffffcccccccc00000000cccccccccccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffeeeeeeeeaaaaaaaaeeeeeeeeeeeeeeeeeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffafafafafafafafafafafafaaaaaaaaafafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffcfcfcfcf0f0f0f0fcfcfcfcccccccccfcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffefefefefafafafafefefefeeeeeeeeefefefefe00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaaaaaaaaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffccffccff00ff00ffccffccffccffcccccccccccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffeeffeeffaaffaaffeeffeeffeeffeeeeeeeeeeee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0ff00ff00f0f0f0f000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffafffafffafffafffafffaffaaffaafafafafaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffcfffcfff0fff0fffcfffcffccffccfcfcfcfccc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffefffefffafffafffefffeffeeffeefefefefeee00ee00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffcfcfffff0f0fffffcfcffffccccfcfcfcfcf0f00000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffefefffffafafffffefeffffeeeefefefefefafa0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaaaaaaaaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffccffffff00ffffffccffffffcccccccccccc00cc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffeeffffffaaffffffeeffffffeeeeeeeeeeeeaaee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffff0fffffff0fffffff0ffffff00f0f0f0f0f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffafffffffafffffffaffffffaafafafafafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffcfffffff0fffffffcffffffccfcfcfcfcfcf0cc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffefffffffafffffffeffffffeefefefefefefaee00
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_73
def pG:List (Nat×Nat):=[(1,9),(1,65),(8,9),(8,72),(64,65),(64,72)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3f
def xsM:=roots_73.map (·&&&dom_73)
def gM:=goal_73&&&dom_73
def NN:Nat→Nat
|2=>1
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|2,0=>0x7d42
|3,0=>0x7d42
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3000000000000000300808000000000000080b030000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x924
|_=>0
def sO:Nat→Nat→Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wAt:=mkWire dB 3 74 0x3ffffffffffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_73 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_73 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_73==dom_73)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_73 gM v ys):RunD true dom_73 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_73 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_73 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_73 gM s xsM):False:=by
  have hmin:2≤s:=by have hl:=run_len h;change 3≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_73 roots_73 goal_73 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_73
theorem lowS_73:Lower true dom_73 roots_73 goal_73 4:=S_73.noCircuit
def isoMvS_74:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_74:Lower true dom_74 roots_74 goal_74 4:=lower_iso_b isoMvS_74 (by decide +kernel) lowS_73
def isoMvS_81:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_73
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_73
def isoMvS_145:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_145:Lower true dom_145 roots_145 goal_145 4:=lower_iso_b isoMvS_145 (by decide +kernel) lowS_73
def isoMvS_148:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_148:Lower true dom_148 roots_148 goal_148 4:=lower_iso_b isoMvS_148 (by decide +kernel) lowS_73
def isoMvS_193:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_193:Lower true dom_193 roots_193 goal_193 4:=lower_iso_b isoMvS_193 (by decide +kernel) lowS_73
def isoMvS_200:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_200:Lower true dom_200 roots_200 goal_200 4:=lower_iso_b isoMvS_200 (by decide +kernel) lowS_73
def isoMvS_208:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_208:Lower true dom_208 roots_208 goal_208 4:=lower_iso_b isoMvS_208 (by decide +kernel) lowS_73
namespace S_27
def pG:List (Nat×Nat):=[(1,9),(1,17),(2,10),(3,11),(3,19),(8,9),(8,10),(16,17),(18,19),(18,26),(24,25),(24,26)]
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
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_slice_b [(0xa0a0000000000000a0a,8,9)] (by decide +kernel) lowS_74
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_slice_b [(0xc000c00000000000c000c,64,66)] (by decide +kernel) lowS_81
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
|0=>0x4045124501414412150514501
|_=>0
def oO:Nat→Nat→Nat
|3,0=>0x20000
|4,0=>0x6242220000
|5,0=>0x9181
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfca7630
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>0x40
|4,0=>0x2940
|5,0=>0xf6
|6,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_200 4 roots_200 ops++addP pm 1 dom_137 4 roots_137 ops++addP pm 2 dom_193 4 roots_193 ops++addP pm 3 dom_73 4 roots_73 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_201 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_73 _ g hchk
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
def isoMvS_29:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_29:Lower true dom_29 roots_29 goal_29 4:=lower_iso_b isoMvS_29 (by decide +kernel) lowS_27
def isoMvS_45:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_45:Lower true dom_45 roots_45 goal_45 4:=lower_iso_b isoMvS_45 (by decide +kernel) lowS_27
def isoMvS_46:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_46:Lower true dom_46 roots_46 goal_46 4:=lower_iso_b isoMvS_46 (by decide +kernel) lowS_27
def isoMvS_51:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=lower_iso_b isoMvS_51 (by decide +kernel) lowS_27
def isoMvS_54:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 4:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_27
def isoMvS_85:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_83
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 4:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_27
def isoMvS_89:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_75
def isoMvS_90:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_83
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 4:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_27
def isoMvS_101:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 4:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_27
def isoMvS_102:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 4:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_27
def isoMvS_106:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_83
def isoMvS_113:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_83
def isoMvS_114:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 4:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_27
def isoMvS_116:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 4:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_27
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_83
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 4:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_27
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_75
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 4:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_27
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_83
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 4:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_27
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 4:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_27
def isoMvS_172:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 4:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_27
def isoMvS_195:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_83
def isoMvS_198:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 4:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_27
def isoMvS_202:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_75
def isoMvS_204:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 5:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_83
def isoMvS_209:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 7:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_201
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_75
def isoMvS_216:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 5:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_75
def isoMvS_226:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 4:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_27
def isoMvS_228:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 4:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_27
theorem lowS_31:Lower true dom_31 roots_31 goal_31 5:=lower_slice_b [(0xcccccccc,8,10)] (by decide +kernel) lowS_29
theorem lowS_47:Lower true dom_47 roots_47 goal_47 5:=lower_slice_b [(0xaaaa0000aaaa,8,9)] (by decide +kernel) lowS_46
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_slice_b [(0xcc00cc0000000000cc00cc,64,66)] (by decide +kernel) lowS_85
namespace S_91
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,10),(2,66),(3,11),(3,19),(3,67),(8,9),(8,10),(8,72),(16,17),(16,80),(18,19),(18,26),(18,82),(24,25),(24,26),(24,88),(64,65),(64,66),(64,72),(64,80)]
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
def dzo_89_4:=0x303030300000000030303030
def gzo_89_4:=0x303030200000000030302000
def gsh_89_4:=0x30303020000000003030200
theorem lowS_zo_89_4_73:Lower true dzo_89_4 roots_89 gzo_89_4 5:=lower_iso_b (d1:=dom_89) (r1:=roots_89) (T1:=gsh_89_4) [(dom_89,4)] (by decide +kernel) (lower_slice_b (T:=gsh_89_4) [(0x30300000000000003030000,0,16)] (by decide +kernel) lowS_73)
namespace S_93
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(4,20),(5,13),(5,21),(5,69),(8,9),(8,72),(12,13),(12,28),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,88),(64,65),(64,72),(64,80),(68,69),(68,76),(68,84)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_93.map (·&&&dom_93)
def gM:=goal_93&&&dom_93
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xc09ca
|5,0=>0x1e1fd
|6,0=>0x4011c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x330033000000000033003300cccccccc000000008888888b33300000000000033330000c0c0c0c000000000c0c0c0c22222222000000002222222200cc00cc000000000088008b33333330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x99a133a84688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 94 0x3fffffffffffffffffffffff
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
addP pm 0 dom_89 5 roots_89 ops++addP pm 1 dom_92 4 roots_92 ops++addP pm 2 dzo_89_4 5 roots_89 ops++addP pm 3 dom_85 5 roots_85 ops++addP pm 4 dom_29 4 roots_29 ops++addP pm 5 dom_73 4 roots_73 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_93 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_89_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_73 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_89 5 s (0,roots_89.map (·&&&dom_89)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_93 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_89 h
def symsG:List (List (Nat×Nat)):=[[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_93==dom_93)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_93 gM v ys):RunD true dom_93 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_93 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_93 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_90_4:=0x505050500000000050505050
def gzo_90_4:=0x505050400000000050504000
def gsh_90_4:=0x50505040000000005050400
theorem lowS_zo_90_4_74:Lower true dzo_90_4 roots_90 gzo_90_4 5:=lower_iso_b (d1:=dom_90) (r1:=roots_90) (T1:=gsh_90_4) [(dom_90,4)] (by decide +kernel) (lower_slice_b (T:=gsh_90_4) [(0x50500000000000005050000,0,16)] (by decide +kernel) lowS_74)
namespace S_94
def pG:List (Nat×Nat):=[(2,10),(2,66),(4,20),(6,14),(6,22),(6,70),(8,10),(8,72),(12,14),(12,28),(12,76),(16,20),(16,80),(18,22),(18,26),(18,82),(24,26),(24,28),(24,88),(64,66),(64,72),(64,80),(68,70),(68,76),(68,84)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_94.map (·&&&dom_94)
def gM:=goal_94&&&dom_94
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x46ac13f102
|5,0=>0x7fa89609c039d9b
|6,0=>0x4c25d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x2aaaaaaa800000002a802a80111111110000000000000000aa88aa8800000000aa88aa8954015400000000015401540002a802a8000000000220022555500000000000055550000a0a0a0a000000000a0a0a0a1111111100000000111111112a802a800000000022002200555555550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x463204963204632084763204325043210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 95 0x7fffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x82
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x20
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0x1f6a040
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x5a
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_90 5 roots_90 ops++addP pm 1 dom_86 4 roots_86 ops++addP pm 2 dzo_90_4 5 roots_90 ops++addP pm 3 dom_92 4 roots_92 ops++addP pm 4 dom_74 4 roots_74 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_94 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_90_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_74 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_90 5 s (0,roots_90.map (·&&&dom_90)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_94 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_90 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_94==dom_94)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_94 gM v ys):RunD true dom_94 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_94 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_94 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_94 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_94 roots_94 goal_94 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_94
theorem lowS_94:Lower true dom_94 roots_94 goal_94 7:=S_94.noCircuit
theorem lowS_107:Lower true dom_107 roots_107 goal_107 6:=lower_slice_b [(0xa0a00000a0a00000a0a00000a0a,8,9)] (by decide +kernel) lowS_106
theorem lowS_115:Lower true dom_115 roots_115 goal_115 6:=lower_slice_b [(0xc000c000c000c000c000c000c000c,32,34)] (by decide +kernel) lowS_113
namespace S_118
def pG:List (Nat×Nat):=[(2,34),(2,66),(4,20),(4,36),(6,22),(6,38),(6,70),(16,20),(16,80),(18,22),(18,50),(18,82),(32,34),(32,36),(48,50),(48,52),(48,112),(64,66),(64,80),(68,70),(68,84),(68,100),(96,98),(96,100),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_118.map (·&&&dom_118)
def gM:=goal_118&&&dom_118
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x2fc5f0cf0f
|5,0=>0x93d491ec6e02a1b
|6,0=>0x93d49
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x550050005500500055005000550050a800a800a800a800a800a800a800a800000000000000015401100154011220022002200220022002200220022550055000000000055005500000000aa000000aa000000aa000000aa000140014001400140014001400140014220022002200220022002200000000550055005500550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x43250432504832504372504632543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x165418a6
|6,0=>0x1b5
|_,_=>0
def wAt:=mkWire dB 9 119 0x7fffffffffffffffffffffffffffff
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
|5,0=>9
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_116 4 roots_116 ops++addP pm 1 dom_114 4 roots_114 ops++addP pm 2 dom_54 4 roots_54 ops++addP pm 3 dom_102 4 roots_102 ops++addP pm 4 dom_86 4 roots_86 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_118 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_86 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_116 4 s (0,roots_116.map (·&&&dom_116)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_118 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_116 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_118==dom_118)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_118 gM v ys):RunD true dom_118 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_118 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
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
theorem lowS_121:Lower true dom_121 roots_121 goal_121 6:=lower_slice_b [(0x3000300030003000300030003000300,1,9)] (by decide +kernel) lowS_113
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_slice_b [(0xc0c0000000000000c0c0000000000000c0c0000000000000c0c,8,10)] (by decide +kernel) lowS_201
theorem lowS_205:Lower true dom_205 roots_205 goal_205 8:=lower_slice_b [(0x3030000000000000303000000000000030300000000000003030,128,132)] (by decide +kernel) lowS_201
theorem lowS_217:Lower true dom_217 roots_217 goal_217 8:=lower_slice_b [(0x3000300000000000300030000000000030003000000000003000300,1,9)] (by decide +kernel) lowS_209
def isoMvS_55:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_iso_b isoMvS_55 (by decide +kernel) lowS_47
def isoMvS_61:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 5:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_47
def isoMvS_62:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 5:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_31
def isoMvS_103:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 5:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_47
def isoMvS_109:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 7:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_94
def isoMvS_110:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 7:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_94
def isoMvS_117:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_115
def isoMvS_122:List (Nat×Nat):=[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 6:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_87
def isoMvS_124:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 5:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_31
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 6:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_87
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 7:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_93
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 7:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_94
def isoMvS_167:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 5:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_47
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 6:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_115
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 6:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_115
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 7:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_118
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 6:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_121
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 6:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_87
def isoMvS_199:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 6:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_87
def isoMvS_206:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 7:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_93
def isoMvS_211:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 8:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_205
def isoMvS_213:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_203
def isoMvS_214:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 7:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_93
def isoMvS_218:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 7:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_91
def isoMvS_220:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 7:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_91
def isoMvS_227:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 6:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_115
def isoMvS_229:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 6:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_115
def isoMvS_230:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 7:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_118
def isoMvS_233:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_205
def isoMvS_234:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 7:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_93
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 7:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_94
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 8:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_205
namespace S_63
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,34),(3,11),(3,19),(3,35),(4,20),(4,36),(5,13),(5,21),(5,37),(6,14),(6,22),(6,38),(7,15),(7,23),(7,39),(8,9),(8,10),(12,13),(12,14),(12,28),(12,44),(16,17),(16,20),(18,19),(18,22),(18,26),(18,50),(24,25),(24,26),(24,28),(32,33),(32,34),(32,36),(40,41),(40,42),(40,44),(48,49),(48,50),(48,52),(56,57),(56,58),(56,60)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffff
def xsM:=roots_63.map (·&&&dom_63)
def gM:=goal_63&&&dom_63
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xc6758
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ffff0000ffff0000ff00ff00ff00ff00f0f0f0f0f0f0f0f0ccccccccccccccccaaaaaaaaaaaaaaaa
|_,_=>0
def sP:Nat→Nat
|0=>0x2c688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|_,_=>0
def wAt:=mkWire dB 6 64 0xffffffffffffffff
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
addP pm 0 dom_62 5 roots_62 ops++addP pm 1 dom_31 5 roots_31 ops++addP pm 2 dom_55 5 roots_55 ops++addP pm 3 dom_47 5 roots_47 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_63 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_47 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_62 5 s (0,roots_62.map (·&&&dom_62)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_63 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_62 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_63==dom_63)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_63 gM v ys):RunD true dom_63 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_63 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_63 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_63 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_63 roots_63 goal_63 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_63
theorem lowS_63:Lower true dom_63 roots_63 goal_63 7:=S_63.noCircuit
def dzo_75_4:=0xf0f0000000000000f0f0
def gzo_75_4:=0xf0e0000000000000e000
def gsh_75_4:=0xf0e0000000000000e00
theorem lowS_zo_75_4_75:Lower true dzo_75_4 roots_75 gzo_75_4 5:=lower_iso_b (d1:=dom_75) (r1:=roots_75) (T1:=gsh_75_4) [(dom_75,4)] (by decide +kernel) (lower_slice_b (T:=gsh_75_4) [] (by decide +kernel) lowS_75)
def dzo_91_4:=0xf0f0f0f000000000f0f0f0f0
def gzo_91_4:=0xf0f0f0e000000000f0f0e000
def gsh_91_4:=0xf0f0f0e000000000f0f0e00
theorem lowS_zo_91_4_75:Lower true dzo_91_4 roots_91 gzo_91_4 6:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_4) [(dom_91,4)] (by decide +kernel) (lower_slice_b (T:=gsh_91_4) [(0xf0f0000000000000f0f0000,0,16)] (by decide +kernel) lowS_75)
namespace S_95
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,10),(2,66),(3,11),(3,19),(3,67),(4,20),(5,13),(5,21),(5,69),(6,14),(6,22),(6,70),(7,15),(7,23),(7,71),(8,9),(8,10),(8,72),(12,13),(12,14),(12,28),(12,76),(16,17),(16,20),(16,80),(18,19),(18,22),(18,26),(18,82),(24,25),(24,26),(24,28),(24,88),(64,65),(64,66),(64,72),(64,80),(68,69),(68,70),(68,76),(68,84)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_95.map (·&&&dom_95)
def gM:=goal_95&&&dom_95
def NN:Nat→Nat
|4=>3
|5=>10
|6=>17
|7=>7
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x674f144f9801dec
|5,0=>0xf7f3feecefe9624d96cf9cedb84b6c5821852383419c02fe2a
|6,0=>0xf4153d6302c9547c2218c0be3b4f33b1d89af52e700976f9fe6346962b884fe62382e723e950cded0c6f3
|7,0=>0xe1246da081bf2a182ebc4d1952a99627e58
|8,0=>0xc3264
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3300333300000000330033005555555500000000555555003333333300000000330033000f0f0000000000000f0f00000fff00ff000000000f0f0000ffffff000000000000000000ffffffff0000000000000000ffffffcc00000000ccccccccaaaaaaaa00000000aaaaaaaaffff000000000000ffff0000ffffffff00000000ff00ff00ffffffff00000000ffff0000ff00ff0000000000ff00ff00f0f0f0f000000000f0f0f0f0cccccccc00000000ccccccccffffffaa00000000aaaaaaaa
|0,1=>0xff00000000000000000000000000000000ffffff0000ff00ff0000000000ff0000ffffffff000000000f0f00000000ffff0000000000000000ff00ffff00000000ff00ff00ffff00ff00000000ffff0000f0fff0ff00000000f0f0f0f0ffffffff00000000ffffff000000ffff000000000000ff0000ff00ff0000000000000000ffffff0000000000ffffff00ffffffff00000000f0f0f0f0333333330000000033333300
|_,_=>0
def sP:Nat→Nat
|0=>0x188274a8c3b04e9a986209d2618827a24c311da930c276266628e213a64628827498713b526188f0498623bd261882e498676b12628827518613ad26189074906209d4618820498a241cc51040418820
|1=>0x30c413a4c3104e9cc8c3104e930c413a6661c427498a3104e92186209d26184ec4986209d3de186209d3220c413a4c5188ed4986209f6930c27d24c5184ec49b03104e9b986209d26
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa5055005
|5,0=>0x4563f63963362d62762161b61560f6
|6,0=>0xb87b17aa7a379c79668f78878177a77466d76676065975274b7
|7,0=>0xe77e07d97d36cc7c57bf6
|8,0=>0xee6
|_,_=>0
def wAt:=mkWire dB 30 96 0xffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x32630d1a61251a532530b92630d92730d32530d2871a562530b30b1a51e532634d1a692430d14d1a692530d3161a52871a530b1a61a51251a530d
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1e2709a2608005894248902388c2288821884208802
|7,0=>0x261946418c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xffbfbd7d60553f3d28261c0f08060500
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x22670a7329a421b75
|7,0=>0xe9dfdec
|8,0=>8
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_94 7 roots_94 ops++addP pm 1 dzo_75_4 5 roots_75 ops++addP pm 2 dom_91 7 roots_91 ops++addP pm 3 dom_93 7 roots_93 ops++addP pm 4 dom_75 5 roots_75 ops++addP pm 5 dom_87 6 roots_87 ops++addP pm 6 dzo_91_4 6 roots_91 ops++addP pm 7 dom_31 5 roots_31 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_95 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_75_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_91_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_31 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_94 7 s (0,roots_94.map (·&&&dom_94)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_95 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_94 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_95 gM v ys):RunD true dom_95 gM v (ori ys):=h
def Z (s:Nat):=barP dom_95 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_95 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_95 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_95 roots_95 goal_95 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_95
theorem lowS_95:Lower true dom_95 roots_95 goal_95 9:=S_95.noCircuit
theorem lowS_111:Lower true dom_111 roots_111 goal_111 8:=lower_slice_b [(0xaaaa0000aaaa0000aaaa0000aaaa,8,9)] (by decide +kernel) lowS_110
namespace S_119
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(2,34),(2,66),(3,19),(3,35),(3,67),(4,20),(4,36),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,23),(7,39),(7,71),(16,17),(16,20),(16,80),(18,19),(18,22),(18,50),(18,82),(32,33),(32,34),(32,36),(48,49),(48,50),(48,52),(48,112),(64,65),(64,66),(64,80),(68,69),(68,70),(68,84),(68,100),(96,97),(96,98),(96,100),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_119.map (·&&&dom_119)
def gM:=goal_119&&&dom_119
def NN:Nat→Nat
|4=>5
|5=>16
|6=>36
|7=>9
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xce7ec9aa595e44126c46256ea
|5,0=>0xe3448e0385d8193ca840c96c7930455bbe75ab19589ff572904cd5a4071d3eb1e3ead43abeb253cf
|6,0=>0xfeae0f89ecd8383cdcf2bdbbdbc114ba40cad941a0b88873f77925f76b0673eed72e6b6dff2633535d38a4f8474872e40ec93eb1e36d7e35ac63222e2c6f4281ee268281fbc91446e0d7770bd4c0b8f30b658097260371c02dda
|7,0=>0xe8d9fbe7e0b3398721ca6aedf5d38a4ec5b4930603cbe
|8,0=>0xdaa04
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00cc00ff00cc00cc00cc00cc00ccff000000ff00000000000000000000ff000000ff000000ff000000ff0000f000f000f000ff00f000f000f000f0ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00000000ff000000ff00ff00ff00ff0000ff00ff0000000000ff00ff0000000000000000ff00ff0000000000ff0000f000f000f000f000f000f000f000f0ff00aa00ff00aa00aa00aa00aa00aaff00ff00ff000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00000000ff00f000ff00f000f000f000f000f0cc00cc00cc00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa
|0,1=>0xff0000000000000000330000003300000033000000330000cc00ff00cc00ff0000000000000000cc00ff00cc00ff00cc00cc00cc00cc33003300330033003300330000000000000000ff00000000000000ff00005500550055005500550055005500000000ff000000ff0000000000000000330033000000330033003300000000ff00ff00ff00ff00ff000000ff00000000ff000000ff00ff000000ff00000000000000000000ff000000ff00000000ff000000ff000000ff000000000f000f000f000f000f000f000f0000ff000000ff000000ff000000000000ff00ff00ff000000ff00ff00000000
|0,2=>0xff000000ff000000cc000000cc0000000000000000ff00ff00ff00000f000f000f000f0000000000000000000033000000330000000000000000ff00ff00ff00ff00ff00f000ff00f0ff00ff0033000000ff00ff00330000ff00f000ff00f000ff00f000ff00f0ff00ff00ff00ff00f000f000f000f0ff00ff00ff000000000000000000000f000f000f000f000f0000000f0000ff00ff00ff00ff0000000000ff0000ff00000000000000ff000000ff0000ff000f00ff000f00ff000000ff00000f000f000f0000000f000f000f00000000cc000000cc00cc00cc00cc00ccff00ff0000000000ff00ff00ff0000
|0,3=>0xff00cc00ff00cc00ff00cc00ff00cc330033003300330000000000000000ff00ff00ff00ff00cc00cc00cc00cc0000ff0000000000ff00ff0000000000000000ff00ff0000000000000000f000f000ff00ff00f000f000f000f0ff00ff00ff00ff000f0000000f0000
|_,_=>0
def sP:Nat→Nat
|0=>0x6cb20604068b60858604520d18164b21518100818100738320d1811440c60403883460172c85951810085060404c83410122c42063c02c44460402d03460402c320d18f00a20604038834c0402ca2060452481810081811471031811440c2040
|1=>0x182163460402c858604038a20d18100ba8d18100b40d18100b2293680402c320d18100e20d18100b9c834604098b20d1810252c836418100b2233460402c420d04088b20d1a100b8083460402c83460402df20d18100b74834670100b20d180
|2=>0xb20d18100bd48346d0100b20d18101e2c83460452f33460402c83460401cb20dc4100b0c8354181008346040c0b4083460402c8346040bcb1033460402ee20d18100b216346040b483460402ec20d18f00b216368181008acd18100b214181
|3=>0x20d18100b20d18100b608d8d18100b20d18101a2c420d18100b20d18100b38858d181
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x3929b18cea6162db15589ec49621b0f586ec31615b09583ec196
|6,0=>0xb1b575aacf506a4bd09e76f34796bc99e3ef18789342de08efe67bbbc59d4ee466f335dda0ec97613aedd68ead7533a81932e92745ba11cfcc777
|7,0=>0x1a17cd3e4df18f857bf3dddee0f697
|8,0=>0x1a86
|_,_=>0
def wAt:=mkWire dB 55 120 0xffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x34b813520d883534b0d2d04b812d04d883b34b06c920b8b3610bc13934b0b3534bcd2e34b0d2d10b483521e413620e4d2c2cd1a2d106c83504ecd2c2cd842e78b830720b546134bcd2e
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xc00000000000000000000000000000000
|6,0=>0x1f2001d27040000000001b100000649810016200142489023880034400000c100000288821c461144000c800
|7,0=>0x291a0671986519063188611
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xed5cf58f58dd7f13f12f12222211801000fd0c006004104003002102000d00c008002001000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x10020000000000000000
|6,0=>0x8a801480002240083c1031ca10b92002c006046340020
|7,0=>0x13bb5b496316
|8,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_118 7 roots_118 ops++addP pm 1 dom_102 4 roots_102 ops++addP pm 2 dom_85 5 roots_85 ops++addP pm 3 dom_83 5 roots_83 ops++addP pm 4 dom_117 6 roots_117 ops++addP pm 5 dom_103 5 roots_103 ops++addP pm 6 dom_87 6 roots_87 ops++addP pm 7 dom_115 6 roots_115 ops++addP pm 8 dom_51 4 roots_51 ops++addP pm 9 dom_55 5 roots_55 ops++addP pm 10 dom_101 4 roots_101 ops++addP pm 11 dom_113 5 roots_113 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_119 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_113 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_118 7 s (0,roots_118.map (·&&&dom_118)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_119 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_118 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_119==dom_119)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_119 gM v ys):RunD true dom_119 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_119 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
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
theorem lowS_123:Lower true dom_123 roots_123 goal_123 8:=lower_slice_b [(0xf0f0f0f000000000f0f0f0f00000000,1,33)] (by decide +kernel) lowS_91
def dzo_121_4:=0x30303030303030303030303030303030
def gzo_121_4:=0x30303030303030203030303030302000
def gsh_121_4:=0x3030303030303020303030303030200
theorem lowS_zo_121_4_73:Lower true dzo_121_4 roots_121 gzo_121_4 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_4) [(dom_121,4)] (by decide +kernel) (lower_slice_b (T:=gsh_121_4) [(0x3030000030300000303000003030000,0,16),(0x3030303000000000303030300000000,0,32)] (by decide +kernel) lowS_73)
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(4,20),(4,36),(5,13),(5,21),(5,37),(5,69),(8,9),(8,72),(12,13),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,88),(32,33),(32,36),(40,41),(40,44),(40,104),(48,49),(48,52),(48,112),(56,57),(56,60),(56,120),(64,65),(64,72),(64,80),(68,69),(68,76),(68,84),(68,100),(96,97),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|4=>5
|5=>15
|6=>37
|7=>10
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xed7f646e2d2d2ba13c5b054f5
|5,0=>0xfbe8cf4125ecf4ae303dd91c7d33d7b00d3a11917909f72dae6e90861eff31d07257bf0d130
|6,0=>0xfd71cfa6c0f8cdee8109e5696e141cdfcd3db521db0cfd91c7cf858cd339c79c3c218fbc7afba6eeb1d7fa91848e2268bb347d47053366528b3508c1439713dc6e29a61274a4231381bd1d18ecb11c1e0d8910bf9807eb3041ae01a5b
|7,0=>0xf353bc68b0c6757c4d75c2f64b324d9a2428e226774926184e
|8,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc00cc00cc00cc00cc00cc00cc00cc022222222222222220000000000000000cc88cc88cc88cc88cc00cc00cc00cc032323232323232323232323232323232cccc8888cccc8888cccc0000cccc0003333333333333333222222222222222200cc00cc00cc00cc008800880088008b3333333333333003333333333332200cccccc00cccccc00cccc8800cccc88022222222222222222222222222222222cccccccccccccccc00000000000000033333333000000003333333300000000cccc0000cccc0000cccc0000cccc00030303030303030303030303030303030444444444444444488888888888888880110011001100110022002200220022
|0,1=>0x44004400440044000000000000000323232323232323230303030303030304444444444444444000000000000000331133113311331100000000000000000000000000000000888888888888888b0303030303030301010101010101010cccccccccccccccccc88cc88cc88cc890101010101010101010101010101010cccccccccccccccc008800880088008b300330033003300220022002200220000cc00cc00cc00cc000000000000000223322332233223322222222222222220088008800880088008800880088008b3223322332233223322332233223322cccccccccccccccccc00cc00cc00cc011111111111111111100110011001100
|0,2=>0xcccccccc88888888cccccccc000000011001100110011003300330033003300c0c0c0c0c0c0c0c0c8c8c8c8c8c8c8cb03230323032303230323032303230324040404040404040c0c0c0c0c0c0c0c33113311331133113300330033003300
|_,_=>0
def sP:Nat→Nat
|0=>0x8a1951033c668510364f0861440cf08a0440c66091440cf0811030865d510308624510b3c22841c22861441c218510308a4d510308a24e1030944c510349108a1033cc4051033422840cc1891440c22801030812442c22892070861440c2040
|1=>0x3e11851033c22931440cf2866051033c22861440cf08624510b3c21851033c26dd10308a1961440e03c21851030865851033c21857c40cf7861440cf3061551030864c55440cf0865c51033c228e10344f0867440cf08615c1034910861440cf
|2=>0x1033c66051033c22861440d23c21851033c21931440cf09418510344f3061440cf30615d10308a1891650cf0861440e40861440cf19815d1033e318510344f08a1840c21891440cd0861440cf8861440d23c22851033cc2861440cf086405103
|3=>0x40cf0861440cf0861551033c219b1440d13c21851033c21857440cf08614e1033cc185
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a58c6c5e52c314989aa4762128f186cc30615309183ea196
|6,0=>0x15e7abbd41e92f4369eb4d9e60d29791b475a2ed10784bc09df8cf57773b9ddc0eda66a3335d8cec065cbacd958ea574f3a61922e8a741b9f1cecc6f7
|7,0=>0x344f9b7ca3e35f0cf806bd35cded8f657
|8,0=>0x1a96
|_,_=>0
def wAt:=mkWire dB 38 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xf16185cf151858614086421b1854f193c6821918544391850f3b185026d185c6153ca86153ce46140934f1a185423b185061518543391850616185cf281854239185021918506151859316185426f185ca3b18506150ce461418543593ca06151854f391850615
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xa3000001cc0010c00000000c40000c00
|6,0=>0xc0400bc6d2ac800a4a8198a4288a11000007c9e174400001b2648000017200152504000012244501000f134800
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0x3dbf670ec06fb841fb7e5db4811042d0240500364c93043b0a8120400e00c0200400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x803000823800030060
|6,0=>0x330ad6b1460dd66701308b818b8808024a003cb015520
|7,0=>0x2dab67529e693
|8,0=>0xb
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_109 7 roots_109 ops++addP pm 1 dom_116 4 roots_116 ops++addP pm 2 dom_45 4 roots_45 ops++addP pm 3 dom_93 7 roots_93 ops++addP pm 4 dom_117 6 roots_117 ops++addP pm 5 dom_113 5 roots_113 ops++addP pm 6 dzo_121_4 6 roots_121 ops++addP pm 7 dom_121 6 roots_121 ops++addP pm 8 dom_124 5 roots_124 ops++addP pm 9 dom_61 5 roots_61 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_121_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_61 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_109 7 s (0,roots_109.map (·&&&dom_109)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_109 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 37 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 37 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 10 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 0 = true)
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
def dzo_122_4:=0x50505050505050505050505050505050
def gzo_122_4:=0x50505050505050405050505050504000
def gsh_122_4:=0x5050505050505040505050505050400
theorem lowS_zo_122_4_74:Lower true dzo_122_4 roots_122 gzo_122_4 6:=lower_iso_b (d1:=dom_122) (r1:=roots_122) (T1:=gsh_122_4) [(dom_122,4)] (by decide +kernel) (lower_slice_b (T:=gsh_122_4) [(0x5050000050500000505000005050000,0,16),(0x5050505000000000505050500000000,0,32)] (by decide +kernel) lowS_74)
namespace S_126
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(4,20),(4,36),(6,14),(6,22),(6,38),(6,70),(8,10),(8,72),(12,14),(12,28),(12,44),(12,76),(16,20),(16,80),(18,22),(18,26),(18,50),(18,82),(24,26),(24,28),(24,88),(32,34),(32,36),(40,42),(40,44),(40,104),(48,50),(48,52),(48,112),(56,58),(56,60),(56,120),(64,66),(64,72),(64,80),(68,70),(68,76),(68,84),(68,100),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffff
def xsM:=roots_126.map (·&&&dom_126)
def gM:=goal_126&&&dom_126
def NN:Nat→Nat
|4=>3
|5=>5
|6=>9
|7=>3
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xea7cb1d54804247
|5,0=>0xf73466d1415207a399792f7e7
|6,0=>0xf615dd4e5fc3b7e87f277e99579cbc71e1a3997915f2b
|7,0=>0xafb698bf857e995
|8,0=>0x464f4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x2020202020202020a0a0a0a0a0a0a0a155555555111111115555555400000000000000000000000222222222222222211111111111111110000000000000000aa88aa88aa88aa88aa00aa00aa00aa0111111111111111100000000000000002222222222222222222222222222222255555555555555550000000000000000aa00aa00aa00aa00aa00aa00aa00aa0001540154015401540110011001100112aaaaaaaaaaaaaaaa22222222222222255555555000000005555555500000000aaaa0000aaaa0000aaaa0000aaaa000141414141414141414141414141414140888888888888888a22222222222222200110011001100110044004400440044
|0,1=>0x54545454545454545050505050505050
|_,_=>0
def sP:Nat→Nat
|0=>0x833892820ce24a14419c4943083388a9410678250419de941067135841ac49410671152820ce22a88311526410624990e19c494106710483114ca20d62290624990419c4509062098831140418820
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2942a805
|5,0=>0x26540c6d4ab0f6
|6,0=>0x5d6aed45a5b4477ccddd8b2b6
|7,0=>0x1c5f53e37
|8,0=>0x786
|_,_=>0
def wAt:=mkWire dB 17 127 0x7fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x4a04a24a14b14a24a14a04a16b14a34a24a14a02ab4a14a0
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x53000c80003
|6,0=>0xb2492040000
|7,0=>0x3c5c2d1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 9
def pmP:Nat→Nat
|0=>0xffb490f0608080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1041
|6,0=>0x16b842
|7,0=>0x1ff
|8,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_118 7 roots_118 ops++addP pm 1 dom_124 5 roots_124 ops++addP pm 2 dom_110 7 roots_110 ops++addP pm 3 dom_94 7 roots_94 ops++addP pm 4 dom_62 5 roots_62 ops++addP pm 5 dom_122 6 roots_122 ops++addP pm 6 dzo_122_4 6 roots_122 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_126 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_122_4_74 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_118 7 s (0,roots_118.map (·&&&dom_118)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_126 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_118 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_126==dom_126)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_126 gM v ys):RunD true dom_126 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_126 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_126 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_126 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_126 roots_126 goal_126 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_126
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=S_126.noCircuit
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=lower_slice_b [(0xcccc000000000000cccc000000000000cccc000000000000cccc,8,10)] (by decide +kernel) lowS_205
def dzo_153_2:=0xc0c0c0c0000000000000000000000000c0c0c0c
def gzo_153_2:=0xc0c0c080000000000000000000000000c080c00
def gsh_153_2:=0x303030200000000000000000000000003020300
theorem lowS_zo_153_2_145:Lower true dzo_153_2 roots_153 gzo_153_2 5:=lower_iso_b (d1:=dom_153) (r1:=roots_153) (T1:=gsh_153_2) [(dom_153,2)] (by decide +kernel) (lower_slice_b (T:=gsh_153_2) [(0x300030000000000000000000000000003000300,0,8)] (by decide +kernel) lowS_145)
def dzo_217_2:=0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c
def gzo_217_2:=0xc0c0c0c000000000c0c0c08000000000c0c0c0c000000000c080c00
def gsh_217_2:=0x3030303000000000303030200000000030303030000000003020300
theorem lowS_zo_217_2_145:Lower true dzo_217_2 roots_217 gzo_217_2 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_2) [(dom_217,2)] (by decide +kernel) (lower_slice_b (T:=gsh_217_2) [(0x3000300000000000300030000000000030003000000000003000300,0,8),(0x3030303000000000000000000000000030303030000000000000000,0,64)] (by decide +kernel) lowS_145)
namespace S_219
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,10),(2,66),(3,11),(3,19),(3,67),(3,131),(8,9),(8,10),(8,72),(8,136),(16,17),(16,80),(16,144),(18,19),(18,26),(18,82),(18,146),(24,25),(24,26),(24,88),(24,152),(64,65),(64,66),(64,72),(64,80),(64,192),(128,129),(128,136),(128,144),(128,192),(130,131),(130,138),(130,146),(130,194)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_219.map (·&&&dom_219)
def gM:=goal_219&&&dom_219
def NN:Nat→Nat
|5=>2
|6=>8
|7=>9
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x9f8fa4bd68
|6,0=>0xc68137409f6d98d6378d4e4d4430af24300017fe
|7,0=>0x5edc45159d50400396cd318202c1d229b351c5671370d
|8,0=>0xdadac488e40af55
|9,0=>0x798d4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x505050500000000050505050000000005050505000000000000000000000000000000000000000000000000e0e0e0e000000000e0e0e0ee0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0ef0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0ac0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0cf0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0af0f0f0f000000000f0f0f0f00000000000000000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000f0f0f0f000000000f0f0f0f000000000e0e0e0e000000000e0e0e0ef0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0af000f00000000000f000f00000000000f000f00000000000f000f00f0f0f0f000000000f0f0f0f000000000c0c0c0c000000000c0c0c0ca0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a0000f0f0000000000000f0f0000000000000f0f0000000000000a0af0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000f0f0f0f0000000000000000000000000f0f0f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x5d30985e30985431085bc310985b631985d310985730985bc30985ba31085b30f985e6095b320985731085d61985b6a15b632095bc3209854c31085761543210
|1=>0x85b30985ba30985b63098
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x65006
|6,0=>0x3863262c62662061971270b7
|7,0=>0x7566f66786075975364c74573e7
|8,0=>0x8878177b6
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 16 220 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xe5036cdd9ecdb9425134250940db3425d96cd6940d9342513c25d9ecd036326940dba64d094c1b34253064d09632695a5034c5b9425306e993425
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0x5cd4344ce32cc921c843
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 10
def pmP:Nat→Nat
|0=>0x1cebe6171aeef74eba35b1ad8807ee3b79daccde66e2bf13ac8d6400034810003c000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x20
|6,0=>0x40cec7088d
|7,0=>0x98ce0b5524f
|8,0=>0x38c9
|9,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_217 8 roots_217 ops++addP pm 1 dom_155 7 roots_155 ops++addP pm 2 dom_216 5 roots_216 ops++addP pm 3 dom_211 8 roots_211 ops++addP pm 4 dom_89 5 roots_89 ops++addP pm 5 dom_91 7 roots_91 ops++addP pm 6 dom_218 7 roots_218 ops++addP pm 7 dom_154 4 roots_154 ops++addP pm 8 dzo_153_2 5 roots_153 ops++addP pm 9 dzo_217_2 6 roots_217 ops++addP pm 10 dom_203 8 roots_203 ops++addP pm 11 dom_90 5 roots_90 ops++addP pm 12 dom_27 4 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_153_2_145 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_217_2_145 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_217 8 s (0,roots_217.map (·&&&dom_217)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_217 h
def symsG:List (List (Nat×Nat)):=[[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_219==dom_219)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_219 gM v ys):RunD true dom_219 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_219 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_219 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_74_4:=0x50500000000000005050
def gzo_74_4:=0x50400000000000004000
def gsh_74_4:=0x5040000000000000400
theorem lowS_zo_74_4_74:Lower true dzo_74_4 roots_74 gzo_74_4 4:=lower_iso_b (d1:=dom_74) (r1:=roots_74) (T1:=gsh_74_4) [(dom_74,4)] (by decide +kernel) (lower_slice_b (T:=gsh_74_4) [] (by decide +kernel) lowS_74)
def dzo_220_2:=0x44444444000000004444444400000000444444440000000044444444
def gzo_220_2:=0x44444444000000004444444000000000444444440000000044404400
def gsh_220_2:=0x11111111000000001111111000000000111111110000000011101100
theorem lowS_zo_220_2_148:Lower true dzo_220_2 roots_220 gzo_220_2 6:=lower_iso_b (d1:=dom_220) (r1:=roots_220) (T1:=gsh_220_2) [(dom_220,2)] (by decide +kernel) (lower_slice_b (T:=gsh_220_2) [(0x11001100000000001100110000000000110011000000000011001100,0,8),(0x11111111000000000000000000000000111111110000000000000000,0,64)] (by decide +kernel) lowS_148)
def dzo_156_2:=0x4444444400000000000000000000000044444444
def gzo_156_2:=0x4444444000000000000000000000000044404400
def gsh_156_2:=0x1111111000000000000000000000000011101100
theorem lowS_zo_156_2_148:Lower true dzo_156_2 roots_156 gzo_156_2 5:=lower_iso_b (d1:=dom_156) (r1:=roots_156) (T1:=gsh_156_2) [(dom_156,2)] (by decide +kernel) (lower_slice_b (T:=gsh_156_2) [(0x1100110000000000000000000000000011001100,0,8)] (by decide +kernel) lowS_148)
def dzo_202_4:=0x5050000000000000505000000000000050500000000000005050
def gzo_202_4:=0x5050000000000000505000000000000050400000000000004000
def gsh_202_4:=0x505000000000000050500000000000005040000000000000400
theorem lowS_zo_202_4_74:Lower true dzo_202_4 roots_202 gzo_202_4 5:=lower_iso_b (d1:=dom_202) (r1:=roots_202) (T1:=gsh_202_4) [(dom_202,4)] (by decide +kernel) (lower_slice_b (T:=gsh_202_4) [(0x505000000000000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_74)
def dzo_148_2:=0x44004400000000000000000000000000440044
def gzo_148_2:=0x44004000000000000000000000000000400000
def gsh_148_2:=0x11001000000000000000000000000000100000
theorem lowS_zo_148_2_148:Lower true dzo_148_2 roots_148 gzo_148_2 4:=lower_iso_b (d1:=dom_148) (r1:=roots_148) (T1:=gsh_148_2) [(dom_148,2)] (by decide +kernel) (lower_slice_b (T:=gsh_148_2) [] (by decide +kernel) lowS_148)
def dzo_218_4:=0x50505050000000005050505000000000505050500000000050505050
def gzo_218_4:=0x50505050000000005050505000000000505050400000000050504000
def gsh_218_4:=0x5050505000000000505050500000000050505040000000005050400
theorem lowS_zo_218_4_74:Lower true dzo_218_4 roots_218 gzo_218_4 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_4) [(dom_218,4)] (by decide +kernel) (lower_slice_b (T:=gsh_218_4) [(0x5050000000000000505000000000000050500000000000005050000,0,16),(0x5050505000000000505050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_74)
def dzo_212_2:=0x440044000000000044004400000000004400440000000000440044
def gzo_212_2:=0x440044000000000044004000000000004400440000000000400000
def gsh_212_2:=0x110011000000000011001000000000001100110000000000100000
theorem lowS_zo_212_2_148:Lower true dzo_212_2 roots_212 gzo_212_2 5:=lower_iso_b (d1:=dom_212) (r1:=roots_212) (T1:=gsh_212_2) [(dom_212,2)] (by decide +kernel) (lower_slice_b (T:=gsh_212_2) [(0x110011000000000000000000000000001100110000000000000000,0,64)] (by decide +kernel) lowS_148)
namespace S_222
def pG:List (Nat×Nat):=[(2,10),(2,66),(4,20),(4,132),(6,14),(6,22),(6,70),(6,134),(8,10),(8,72),(8,136),(12,14),(12,28),(12,76),(12,140),(16,20),(16,80),(16,144),(18,22),(18,26),(18,82),(18,146),(24,26),(24,28),(24,88),(24,152),(64,66),(64,72),(64,80),(64,192),(68,70),(68,76),(68,84),(68,196),(128,132),(128,136),(128,144),(128,192),(130,134),(130,138),(130,146),(130,194)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_222.map (·&&&dom_222)
def gM:=goal_222&&&dom_222
def NN:Nat→Nat
|4=>7
|5=>18
|6=>46
|7=>36
|8=>12
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xa49a78e8f471b496916943da939fa9174b5
|5,0=>0xb9058b1b959d8459c9528dae58cfeb832b87a8d879d456df1a6b6a4555183b33739ca12bb6623a71188c018152
|6,0=>0xf90a4f2106ca7c7c3304c04c0b4c56ab6f0aa398aa128a088a9c89994f0290a6e902798d7688cf4986b8485391825cb7b6ae794b17619673a4271b9a70ea26bbb2678dc66c1963abd604614f9e84bd3545e274489b3d2d5378b4335dc31a882c4452a02f29c0a2817f1e1d417e4a0ad53008d1
|7,0=>0xf5a9ed4f4eac40faa876a511f9ee14862ca8595c7d32177a1e6d38654108500464bc6d4b59a3e10d3c0f73b40730da02db7b2d5d525d1c258ed2494b23a3d218161929d156620ead10e24c0de0e0cc540a813088240765606328
|8,0=>0xbad5eac4b278bdf62fd65a519577e145e2a2b66c2b37d2426a05964050df
|9,0=>0xbad5e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaa00000000aaaa000000000000aa00aa0000000000aa00000155555554000000015555555400000001555555540000000000000002aaaaa80000000002aaaaa80000000002aaaaa80000000002aaaaa8055555555000000005550555000000000555555550000000055505500aaaaaaaa00000000a0a0a0a000000000aaaaaaaa00000000a0a0000155555554000000015555555400000000000000000000000000000002aaa8000000000002aaa8000000000002aaa8000000000002aaa800055005500000000005500550000000000550055000000000055005500aaaaaaaa00000000aaaaaaaa0000000088888888000000008800880014141414000000001414141400000000141400000000000014140002aaaaaaa8000000000000000000000002aaaaaaa800000000000000055555555000000005555555500000000555500000000000055550000aaaaaaaa00000000aa00aa0000000000aaaaaaaa00000000aa00aa0141414140000000014141414000000001414141400000000141414142222222200000000222222220000000022222222000000002222222255555500000000005555550000000000555555000000000000000000
|0,1=>0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaa0000000000000000015555540000000000000000000000000155555402aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002a802a800055005500000000005500000000000000550055000000000055000022222222000000002200220000000000222222220000000022002201555555540000000155555554000000011111111000000001111111100002aaa8000000000002aaa8000000000002aaa800000000000000000550055000000000050005000000000005500550000000000500000aaaaaaaa00000000aaaaaaaa00000000aaaaaa0000000000aaaaaa01555555540000000155555400000000015555555400000001555554000002aaa8000000000002aaa8000000000002a800000000000002a80505050500000000050505050000000005050000000000000505000008888888800000000880088000000000088888888000000008800880155555554000000015554000000000001555555540000000155540002aaaaaaa800000002aaaaaaa800000002a802a80000000002a802a8011111111000000001110111000000000111111110000000011101100
|0,2=>0xaaaaaaaa00000000aaaaaaaa00000000a0a0a0a000000000a0a0a0a155555554000000001414141400000001555555540000000014140002aaaaaaa8000000022222222000000002aaaaaaa800000002222222255555555000000005555555500000000000000000000000055555500aaaa00aa00000000aaaa00aa00000000aaaa00aa00000000aaaa000000000154000000000000015400000000000001540000000000000002aa22aa2000000002aa22aa2000000002aa22aa2000000002aa22aa2555555550000000000005555000000005555555500000000000055000000000000000000000000000000000000aa00aa0000000000aa0000000000000000000000000000000000015555555400000001555554000002aaa8000000000002aaa8000000000002aaa8000000000002a8055555555000000005050505000000000555555550000000050505050000000000000000000000000000000000000000000000000aaaaaa00015401540000000001540154000000000154015400000000000000000000000000000002aaaaaaa8000000000000000000000002a802a8055550000000000005555555500000000555500000000000055555500
|0,3=>0x2aaaa222000000002aaaa222000000002aaaa222000000002aaaa2225454545400000000545454540000000054545454000000005454545400000000000000000000000000000000aaaaaaaa00000000aaaa0001555555540000000155555554000000015555111000000001555511100002aaa8000000000002aaa8000000000002222000000000000222255555050000000005555505000000000555550500000000055555050aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaa00000000000000000000000000000000000111111110000000011111111000000000000000000000000000000002aaaaa80000000002aaaaa8000000000000000005050505000000000000000000000000050505050
|_,_=>0
def sP:Nat→Nat
|0=>0x6c614a48809a3992482c160a3482c114a2483c204e24320b04a5d220204e48808100a58420204e24c20b04a1080811402484c614a3440c204e24308154e34350114a3490871524420402482d028d3c204e3432c128d30b04a2481c61440c2040
|1=>0x22404a34420204e16324808114a2482c114a25108138588424320204e58944204528420204e1593498420452a024808114a24321404529f24808114a24320118529e10808114a34909314a34974204528920205c38a35244204e34f08114a248
|2=>0x24808138524891a38920204500a24808116a29725120268526920118528920206814a2480819c528d48808138a98920204528920206514a2482c128974204588a48920268e24344204e3440c204528974890138a2489013a22890c205514a352
|3=>0x20204e14a25d44808114a24808138588a5c920204529225120204528424808138535220204528d24308114a352442045289201b8529225120204e2483c204528922d04614a25108116229610808114a7894420452ac24808114aac9202045297
|4=>0x2b4243202045289224c852b324808114a34920268529648920204528920204564a24809a38548920204e2922480b214a2512240452b124808114a48420204528921404528d248c0114a24804614a248bc2b4114a48922404a109202b4114a25d
|5=>0x4528d24808114a2480ad0452b924808114a2480b214a248e02045289a4808114a24808138528944808114a248c3214a24891a14a5cd24808114adc920204528d2480813852b624808114a248081d4528920205c14a1090c808114a24809ad45
|6=>0x920204528920204528920268528424808114a248902
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x1e5065414503d40a50154005
|5,0=>0x22188261f187661c186a619185e61618526131846610183a60d182e60a18235
|6,0=>0x6fddb966c9dab7691d9d7659d8f7621d8175e9d7555b9d677581d597549d4b7511d3d74d9d3154a9d2464799177441d097409cfc63d5cee73a18e17369cd37331cc572f9cb772c1ca97289c9c6255c8e7
|7,0=>0xb01aba6aca2ab7a8e29c7a55e8e7a1a27f79de27169a9e63796e2547939a477901e3978c9e2b7895a1e7861a108829a0287ea1f287aa1e3776e1d47735dc67
|8,0=>0xc45b0b6c11efd7bd9eef7ba1ee26b6ded47b35ec67
|9,0=>0x3176
|_,_=>0
def wAt:=mkWire dB 58 223 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x85452920e8a1508542152094915505440824a483a14a4929488491524e8529445c829445c40824a5245102c929345c9210c10825205483914a522324554151020929505440824a5244245482924a481124a4d382094d152485415102092934e092124a49294ca4304209481524a4929
|1=>0x85c40b24a422904542152454929045483914a511520a483a14a494520a491520a492914a482524548252054615102c929491091520a440b24a51153454921345c921345c83a449482914a421504a4d38248452904a4829102c92958ad415102092914a41292854915205452920a4929
|2=>0x4a49290854921045490504ac205201452920a421704ac21504a4d29248522b245492114a440524a496a04a484a245481524a496a04a4909205421504ad229245492104a4849245493a285452904a4a15245412b245421520a4d2b2484929245440824a4825
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11001000000
|5,0=>0x1a31731431311120f20d20a3082000071000061024
|6,0=>0x6430006135f25e15c25a25915815625335030004e24c20000000004b10004834714434134013e23b30003830000003533323213022e22c22b12922812622422131f21d2
|7,0=>0xad2ab2a92a72a52a32a129f29d29b29929729529329128f28d28b28928728528328127f27d27b27927727527327126f26d26b2692672
|8,0=>0xb91b81b71b61b51b41b31b21b11b01af1
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x7870001140000444000110000043700010d0000420000104c0004120001010000401000100000033f40009fd00004000000940000220000084000020000007f00001f400007900001e00000440000108000040000003000000800000100000020000004000000
|1=>0x2001dc05807d0104520041140010410002d9f900a65f4024cfd008b3f4022c9c00833f4020c1c0077bf401d0fd00659f401814c00531f40149fd004b2700128fd00411f401017d002e9f400a07f00239f400487d00100300031dc000c6000021500008240002080
|2=>0x200067f40239f480ce7d12209f44802111010884204062052a3f41420c404a65e4121150042a3f410997904221f4088efd02001fc08007d
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x408000
|5,0=>0x3060a08204061c7002200109
|6,0=>0xca500140bb06550201ecd2004204000287003f787d8113c5c03a1a020082254816401d1860628e95
|7,0=>0x18ce43537093b9449e52e6ea631362d09328ada0a84d2dc4c7af4c4934b63c4
|8,0=>0x16c562f87367aa9d415be
|9,0=>0xb
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 26 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_220 7 roots_220 ops++addP pm 1 dom_208 4 roots_208 ops++addP pm 2 dom_94 7 roots_94 ops++addP pm 3 dom_158 7 roots_158 ops++addP pm 4 dom_206 7 roots_206 ops++addP pm 5 dom_218 7 roots_218 ops++addP pm 6 dom_214 7 roots_214 ops++addP pm 7 dzo_74_4 4 roots_74 ops++addP pm 8 dom_148 4 roots_148 ops++addP pm 9 dzo_220_2 6 roots_220 ops++addP pm 10 dzo_156_2 5 roots_156 ops++addP pm 11 dzo_202_4 5 roots_202 ops++addP pm 12 dzo_148_2 4 roots_148 ops++addP pm 13 dom_74 4 roots_74 ops++addP pm 14 dzo_218_4 6 roots_218 ops++addP pm 15 dzo_212_2 5 roots_212 ops++addP pm 16 dzo_90_4 5 roots_90 ops++addP pm 17 dom_142 4 roots_142 ops++addP pm 18 dom_86 4 roots_86 ops++addP pm 19 dom_200 4 roots_200 ops++addP pm 20 dom_198 4 roots_198 ops++addP pm 21 dom_202 5 roots_202 ops++addP pm 22 dom_156 5 roots_156 ops++addP pm 23 dom_216 5 roots_216 ops++addP pm 24 dom_204 5 roots_204 ops++addP pm 25 dom_212 5 roots_212 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_222 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_74_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_220_2_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_156_2_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_202_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_148_2_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_218_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_212_2_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_90_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_212 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_220 7 s (0,roots_220.map (·&&&dom_220)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_222 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_220 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_222==dom_222)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_222 gM v ys):RunD true dom_222 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_222 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 46 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_222 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_222 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_222 roots_222 goal_222 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_222
theorem lowS_222:Lower true dom_222 roots_222 goal_222 10:=S_222.noCircuit
theorem lowS_235:Lower true dom_235 roots_235 goal_235 9:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c,8,10)] (by decide +kernel) lowS_233
theorem lowS_237:Lower true dom_237 roots_237 goal_237 9:=lower_slice_b [(0x303000003030000030300000303000003030000030300000303000003030,32,36)] (by decide +kernel) lowS_233
def dzo_206_32:=0x555500000000000055550000000000005555000000000000555500000000
def gzo_206_32:=0x555500000000000055540000000000005554000000000000545400000000
def gsh_206_32:=0x5555000000000000555400000000000055540000000000005454
theorem lowS_zo_206_32_200:Lower true dzo_206_32 roots_206 gzo_206_32 6:=lower_iso_b (d1:=dom_206) (r1:=roots_206) (T1:=gsh_206_32) [(dom_206,32)] (by decide +kernel) (lower_slice_b (T:=gsh_206_32) [(0x4444000000000000444400000000000044440000000000004444,0,2),(0x5050000000000000505000000000000050500000000000005050,0,4)] (by decide +kernel) lowS_200)
def dzo_106_4:=0x5050000050500000505000005050
def gzo_106_4:=0x5050000050400000505000004000
def gsh_106_4:=0x505000005040000050500000400
theorem lowS_zo_106_4_74:Lower true dzo_106_4 roots_106 gzo_106_4 5:=lower_iso_b (d1:=dom_106) (r1:=roots_106) (T1:=gsh_106_4) [(dom_106,4)] (by decide +kernel) (lower_slice_b (T:=gsh_106_4) [(0x505000000000000050500000000,0,32)] (by decide +kernel) lowS_74)
def dzo_234_4:=0x505000005050000050500000505000005050000050500000505000005050
def gzo_234_4:=0x505000005050000050500000505000005050000050400000505000004000
def gsh_234_4:=0x50500000505000005050000050500000505000005040000050500000400
theorem lowS_zo_234_4_74:Lower true dzo_234_4 roots_234 gzo_234_4 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_4) [(dom_234,4)] (by decide +kernel) (lower_slice_b (T:=gsh_234_4) [(0x50500000000000005050000000000000505000000000000050500000000,0,32),(0x50500000505000005050000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_74)
def dzo_204_32:=0x111100000000000011110000000000001111000000000000111100000000
def gzo_204_32:=0x111100000000000011100000000000001110000000000000101000000000
def gsh_204_32:=0x1111000000000000111000000000000011100000000000001010
theorem lowS_zo_204_32_200:Lower true dzo_204_32 roots_204 gzo_204_32 5:=lower_iso_b (d1:=dom_204) (r1:=roots_204) (T1:=gsh_204_32) [(dom_204,32)] (by decide +kernel) (lower_slice_b (T:=gsh_204_32) [(0x1010000000000000101000000000000010100000000000001010,0,4)] (by decide +kernel) lowS_200)
namespace S_238
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(4,36),(4,132),(6,14),(6,38),(6,70),(6,134),(8,10),(8,72),(8,136),(12,14),(12,44),(12,76),(12,140),(32,34),(32,36),(40,42),(40,44),(40,104),(40,168),(64,66),(64,72),(64,192),(68,70),(68,76),(68,100),(68,196),(96,98),(96,100),(96,104),(96,224),(128,132),(128,136),(128,192),(130,134),(130,138),(130,162),(130,194),(160,162),(160,164),(160,168),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_238.map (·&&&dom_238)
def gM:=goal_238&&&dom_238
def NN:Nat→Nat
|4=>2
|5=>15
|6=>56
|7=>31
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xbc92226902
|5,0=>0xeda3cda146c41bdb71465b58b536924d6104d3a241d4428160257d0190961292609f10035d8
|6,0=>0xe54facd065c05feac473a73b9a1e7997ce094cd2916818fa0f8645581f3f81b3675172711a56bab3696ce6777961a8e601a65b8e35b58b59e9d589b2533774f9a64b5424afd0485044829b46c393bbc639ebc32b1d2d9f72d06b2983c267ff228c9225532074a200f7182d417dfc17cc41408612a13117f4117ab0feaa0f7930e2eb0e01a050f80291602861
|7,0=>0xe43c8a20fe7df4b7ddba7bac678f37789716c0545d97b4f4564ee404d9eb4cd92417574092434b9e2520a221951c5101c1e7182aa135ca11b4d0ffab0ff9f0a4d007c2d06d42063540301200a86
|8,0=>0x9859a8180380e155ee8935aed1cbbf17c761305b
|9,0=>0x1305b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa0000000a00000202000002020000020a0000020a1555400015554000155540001555400015400000154000001540000015402aaa80002aaa800022220000222200002a8000002a800000220000002200555500005555000000000000000000005555000055550000000000000000aaaa0000aaaa0000aaaa0000aaaa00000000000000000000000000000001540000015400000154000001540000015400000154000001540000015402aaa80002aaa80002aaa80002aaa80002aa200002aa200002aa200002aa2444400004444000044440000444400004444000044440000444400004444aaaa0000aaaa0000aa000000aa000000aaaa0000aaaa0000aa000000aa01555400015554000155540001555400011110000111100001111000011112aa200002aa200002aa200002aa200002aa200002aa20000000000000000555500000000000055550000000000005555000000000000555500000000aa880000aa880000aa880000aa880000aa880000aa880000aa880000aa89414000014140000141400001414000014140000141400001414000014142aaa80002aaa80002a8000002a8000002222000022220000220000002200555500005555000055550000555500005555000055550000000000000000
|0,1=>0xaa220000aa220000aa200000aa200000aa220000aa220000aa200000aa2001540000015400000110000001100000015400000154000001100000011000000000000000000000000000000000888800008888000088000000880555500005555000055550000555500005555000055550000554400005544a8a8000000000000a8a8000000000000a8a8000000000000a8a800000000444400004444000044000000440000004444000044440000440000004402aaa80002aaa80002aaa80002a8000002aaa8000222200002aaa80002200005500000055000000550000005500000044000000440000004400000044aaaa0000aaaa00000000000000000000aa880000aa88000000000000000000000000000000015554000155540000000000000000000155100001551000000000000000000000000000000002aaa80002aaa80002aaa00002aaa55550000555500005554000055540000000000000000000000000000000000000000000000000000000000000000aa880000aa880000aa880000aa8955540001555400011110000111100001555400015554000111100001111222200000000000022220000000000002222000022220000222200002200000000000000000000000000000000005151000051510000515000005150
|0,2=>0xaaaa0000aaaa00000000000000000000aaaa0000aa01555400015554000001540000015400015554000155540000011000000112aaa80002aaa80002aaa80002aaa8000002a8000002a8000002200000022555500005555000055500000555000005555000055550000555000005550aaaa0000aaaa0000aaa00000aaa0000000000000000000000000000000011110000111100001555000015550000111100001111000015550000155500000000000000002aaa80002aaa80000000000000000000222200002222000000000000000000550000005500000000000000000000004400000044a0a00000aaaa0000a0a00000aaa00000a0a00000aaaa0000a0a00000aaa1555400015554000044440000444400015554000155540000440000004402aaa80002aaa80002aaa80002aaa80002aaa80002aaa8000222200002222550000005500000055000000550000005500000055000000440000004400aaa00000aaa00000aaa00000aaa00000aaa00000aaa00000aaa00000aaa0000000000000000044400000444000000000000000000000444000004442aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002a80000000000000000000000000000000005555000055550000555000005550
|0,3=>0x22220000222200002220000022200000222200002222000022200000222151500001515000015150000151500001515000015150000151500001515000000002a2a0000000000002a2a0000000000002a2a0000000000002a2a55550000555500005555000055550000555500005555000055000000550000aa000000aa000000aa000000aa000000aa000000aa0000008800000089414000014140000141400001414000014140000000000001414000000002aaa80002aaa80002aaa80002aaa80002aaa8000000000002aaa80000000000000000000000000000000000000005555000055550000550000005500aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa000000000000aa01540000015554000154000001555400015400000155540001540000015402aaa8000000000002aaa8000000000002aaa80002aaa80002aaa80002a80555000005550000044400000444000005550000055500000444000004440aaaa0000aaaa0000aaaa0000aa000000aaaa0000aaaa0000aaaa0000aa01111000011110000111100001100000011110000111100001111000011002aaa8000000000002aaa80002aaa80002aaa8000000000002aaa80002a80000000000000000000000000000000000000000000000000554400005544
|0,4=>0xaaaa0000aa000000aaaa0000aa0000000000000000015540000155400000000000000000000155400001554000000002aaa8000000000002a800000000000002aaa8000000000002a80555500005555000055440000554400005555000055550000554400005544aaaa0000aaaa0000aaaa000000000000aaaa0000aaaa0000aaaa00000001555400011110000155540001111000015554000111100001555400011112aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80000000000000005555000000000000555500000000000055000000000000005500aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aa000000aaaa0000aa0155540001555400015554000155540001414000014140000141400001414088880000888800008888000088880000888800008888000088000000880050500000505000005000000050000000505000005050000050000000500a0a0000000000000a0aa000000000000a0a0000000000000a0aa0000000014140000141400001410000014100000141400001414000014100000141088880000888800008888000088880000888800008888000000000000000444400004444000044440000444400005555000055550000554400005544
|0,5=>0x1555400015554000141400001414000015554000155540001414000014142aaa8000282800002aaa8000282800002aaa8000282800002aaa80002828555500005500000055550000550000005555000055000000555500005500
|_,_=>0
def sP:Nat→Nat
|0=>0x8281063c30584140841d182c2030420c0c1610e0a042060b146c11a182cc8a042060b081c1080a2c2021060b8b0858502102c215140840c082810818502130e0890b0828111182c20a200840c080c3820c0020a103c60b0838108023020a041868c0824382100020704182840608080
|1=>0x420f0c161150a042060b080c38210005841409288522c20a0420c00181050210a060b0838502105c584149c40c1610502109860b0828106105c584042120c161048a042000c082810844305a10828108182c2071c083081810502103460b080c106303058440281081810f8a042060b
|2=>0x6e305846c28108182c2071c084006a1050210305842628112182c2032c28108161050210d060b0858502102c207140990c1610125109060b081c5024a205b10828108182c2092c28108161180a042060b5e105021030584140842e182c20a042168c1610502103158406281060030223
|3=>0x8c0840c16e4207140840c161048a042060b08281083c305841408401182c20a042228c162a18210305841408442182c2161408308161038a042208b09005021030584401c502103020a0421f8c161c50210f460b08f05020c20604140843b182c20714e840c16e4238140840c0828108
|4=>0x8245020c2060b08281089a3058a360840c161018a042000c1612607140840c161038a044840b080c5020c305b3081c50210305cb083850210305847028108182e5041c28108182e4841408400182c20a0420c0c1610502112060b8e10502103058a0421e8c1610483140840c161038a
|5=>0xe28108182c20a8c0840c16e420a042060b082810610305841548108182e884140840c161018a042060b0828108182c2071408308182e8840e28108182c213140840c161070a042000c9e105021030584782810800305849c28108182c22c140840c16105020c20c0c1611e0a042060b
|6=>0x105021030584
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x154005
|5,0=>0x5e61618526131846610183a60d182e60a18226071816604180a6
|6,0=>0x779dd777459ca770ddbc76d5dae769dda07665d92762dd8475f5d7675c19697589d5b7551d4e651dd4074e5d3274add247475d16743dd096409cfb73d1ced7399cdf7361cd1732d8c472f5cb762c1ca97289c9b7251c8d721d88071e5c7271adc647
|7,0=>0x2c28aea2b37ab1ea57a762967a3de878a01e7889c5e6b698e25b8951e4d791623d88d9e2e889a21f7861e11782da0387ee1f387b1de57
|8,0=>0xbe9ef37bb1ee57b79ed77b41eca6
|9,0=>0x3016
|_,_=>0
def wAt:=mkWire dB 83 239 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xe2d143114317208082d0e2f1431142d182d14311233062d4648182166200e110c31102d1c330c29102d0c2b102d242b1821582c0e091431242b182118a50c330c2b102d3033102d12301c2112300c29102d4a280c31102d0c29102d464b182114312438142d18211621242b1821122b062d0600182d14210e18102d062d1421
|1=>0x188e04290e0914310c2b102d0e2d14310c29102d0e1314317c100421182d14210e21143118211431142116210e111431142d08310e2f1431162908210011182d0c2b102d1c13142d1c11142d7c130421062d14211431042d1431082d0c29102d242b18210e181431102d09130e0b143112330c290023182d582f0e097c130421
|2=>0x1431042d082d102d0431080914211431102d08091431062f14211631142da02f08290029182d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x43000000000000000000000000000022000002
|6,0=>0x4b30004830004624420004220004023e20003b33920000003630000003423220003020002e22d12b20000002922722430002220000002021e21c21a20000001731431221020f10000c30b1000000092000072000
|7,0=>0x8a28828628428228027e27c27a27827627427227026e26c26a26826626426226025e25c25a25825625425225024e2
|8,0=>0x9219119018f18e18d18c1000
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x824300813f00803f00423f00417f00417b00413f00407f0030000010b200093f00083e0006010001160000b20000a600004100003f00002f00002e000020000017000015000013000010000008000006000004000003000002000001000000
|1=>0x8049bf80080a4000833000a22030a41440bf0c093f06083f0470bf0450bf0440bf04093f04019f02080a01853f01840601417f01051601005101004300c207
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x5000000000000002004
|6,0=>0x28030004200200204044b0004800010800800971000041d40060004c40820000c31065c01420001c03c0
|7,0=>0xacdb8ef96ea489a1a9525f81ac507b2c19aaca229d691c
|8,0=>0x76dad9a7460d
|9,0=>0xe
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 24 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_236 7 roots_236 ops++addP pm 1 dom_230 7 roots_230 ops++addP pm 2 dom_174 7 roots_174 ops++addP pm 3 dom_234 7 roots_234 ops++addP pm 4 dom_110 7 roots_110 ops++addP pm 5 dom_206 7 roots_206 ops++addP pm 6 dom_228 4 roots_228 ops++addP pm 7 dzo_206_32 6 roots_206 ops++addP pm 8 dzo_106_4 5 roots_106 ops++addP pm 9 dom_172 4 roots_172 ops++addP pm 10 dom_46 4 roots_46 ops++addP pm 11 dzo_234_4 6 roots_234 ops++addP pm 12 dom_74 4 roots_74 ops++addP pm 13 dzo_74_4 4 roots_74 ops++addP pm 14 dzo_204_32 5 roots_204 ops++addP pm 15 dom_166 4 roots_166 ops++addP pm 16 dom_102 4 roots_102 ops++addP pm 17 dom_106 5 roots_106 ops++addP pm 18 dzo_202_4 5 roots_202 ops++addP pm 19 dom_226 4 roots_226 ops++addP pm 20 dom_198 4 roots_198 ops++addP pm 21 dom_142 4 roots_142 ops++addP pm 22 dom_204 5 roots_204 ops++addP pm 23 dom_202 5 roots_202 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_238 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_206_32_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_106_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_234_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_74_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_204_32_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_202_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_202 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_236 7 s (0,roots_236.map (·&&&dom_236)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_238 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_236 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccccccccccccccccccc,126)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccccccccccccccccccc,126)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_238==dom_238)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_238 gM v ys):RunD true dom_238 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_238 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 56 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 56 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 31 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 31 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_238 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_238 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_238 roots_238 goal_238 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_238
theorem lowS_238:Lower true dom_238 roots_238 goal_238 10:=S_238.noCircuit
theorem lowS_249:Lower true dom_249 roots_249 goal_249 9:=lower_slice_b [(0x300030003000300030003000300030003000300030003000300030003000300,1,9)] (by decide +kernel) lowS_241
def isoMvS_159:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_iso_b isoMvS_159 (by decide +kernel) lowS_95
def isoMvS_175:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_iso_b isoMvS_175 (by decide +kernel) lowS_119
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_125
def isoMvS_189:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 8:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_123
def isoMvS_190:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_126
def isoMvS_215:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_207
def isoMvS_221:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 10:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_219
def isoMvS_231:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_119
def isoMvS_246:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_238
def isoMvS_250:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 9:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_95
def isoMvS_252:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccccccccccccccccccc,126),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_95
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0e00000f0f00000e000
def gsh_107_4:=0xf0f00000f0e00000f0f00000e00
theorem lowS_zo_107_4_75:Lower true dzo_107_4 roots_107 gzo_107_4 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xf0f0000000000000f0f00000000,0,32)] (by decide +kernel) lowS_75)
def dzo_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_123_4:=0xf0f0f0f0f0f0f0e0f0f0f0f0f0f0e000
def gsh_123_4:=0xf0f0f0f0f0f0f0e0f0f0f0f0f0f0e00
theorem lowS_zo_123_4_75:Lower true dzo_123_4 roots_123 gzo_123_4 7:=lower_iso_b (d1:=dom_123) (r1:=roots_123) (T1:=gsh_123_4) [(dom_123,4)] (by decide +kernel) (lower_slice_b (T:=gsh_123_4) [(0xf0f00000f0f00000f0f00000f0f0000,0,16),(0xf0f0f0f000000000f0f0f0f00000000,0,32)] (by decide +kernel) lowS_75)
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,10),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(4,20),(4,36),(5,13),(5,21),(5,37),(5,69),(6,14),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,10),(8,72),(12,13),(12,14),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(18,19),(18,22),(18,26),(18,50),(18,82),(24,25),(24,26),(24,28),(24,88),(32,33),(32,34),(32,36),(40,41),(40,42),(40,44),(40,104),(48,49),(48,50),(48,52),(48,112),(56,57),(56,58),(56,60),(56,120),(64,65),(64,66),(64,72),(64,80),(68,69),(68,70),(68,76),(68,84),(68,100),(96,97),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|8=>1
|9=>5
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xb0a69
|9,0=>0xe6b3fd9c79d7508715435254f
|10,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfffffffffffffffff0f0f0f0f0f0f0f0fffff0f0fffff0f0fffff0f0fffff0f00000ffff0000ffff0000000000000000ffffffffffffffffffff0000ffff0000ffffffff00000000ffffffff000000000f0f0f0f0f0f0f0f0000000000000000ffffffff0f0f0f0fffffffff00000000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8543210854c3210854321078b5432108543210a895432106543210
|_=>0
def sO:Nat→Nat→Nat
|8,0=>7
|9,0=>0x2787e1783e078
|10,0=>0x2f7
|_,_=>0
def wAt:=mkWire dB 13 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc13094d50941874c2
|_=>0
def oO:Nat→Nat→Nat
|8,0=>2
|9,0=>0x61a3058a1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 7
def pmP:Nat→Nat
|0=>0x35f7fcff17c00
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>2
|9,0=>0x3512
|10,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_126 9 roots_126 ops++addP pm 1 dom_125 9 roots_125 ops++addP pm 2 dom_123 8 roots_123 ops++addP pm 3 dom_119 9 roots_119 ops++addP pm 4 dom_111 8 roots_111 ops++addP pm 5 dom_63 7 roots_63 ops++addP pm 6 dom_95 9 roots_95 ops++addP pm 7 dzo_107_4 6 roots_107 ops++addP pm 8 dzo_123_4 7 roots_123 ops++addP pm 9 dom_107 6 roots_107 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_107_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_123_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_107 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_126 9 s (0,roots_126.map (·&&&dom_126)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_126 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 5 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_127 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_149_2:=0xcc00cc00000000000000000000000000cc00cc
def gzo_149_2:=0xcc00c800000000000000000000000000c80000
def gsh_149_2:=0x33003200000000000000000000000000320000
theorem lowS_zo_149_2_149:Lower true dzo_149_2 roots_149 gzo_149_2 5:=lower_iso_b (d1:=dom_149) (r1:=roots_149) (T1:=gsh_149_2) [(dom_149,2)] (by decide +kernel) (lower_slice_b (T:=gsh_149_2) [] (by decide +kernel) lowS_149)
def dzo_213_2:=0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc
def gzo_213_2:=0xcc00cc0000000000cc00c80000000000cc00cc0000000000c80000
def gsh_213_2:=0x330033000000000033003200000000003300330000000000320000
theorem lowS_zo_213_2_149:Lower true dzo_213_2 roots_213 gzo_213_2 6:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_2) [(dom_213,2)] (by decide +kernel) (lower_slice_b (T:=gsh_213_2) [(0x330033000000000000000000000000003300330000000000000000,0,64)] (by decide +kernel) lowS_149)
def dzo_203_4:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0
def gzo_203_4:=0xf0f0000000000000f0f0000000000000f0e0000000000000e000
def gsh_203_4:=0xf0f0000000000000f0f0000000000000f0e0000000000000e00
theorem lowS_zo_203_4_75:Lower true dzo_203_4 roots_203 gzo_203_4 6:=lower_iso_b (d1:=dom_203) (r1:=roots_203) (T1:=gsh_203_4) [(dom_203,4)] (by decide +kernel) (lower_slice_b (T:=gsh_203_4) [(0xf0f0000000000000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_75)
def dzo_221_2:=0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc
def gzo_221_2:=0xcccccccc00000000ccccccc800000000cccccccc00000000ccc8cc00
def gsh_221_2:=0x33333333000000003333333200000000333333330000000033323300
theorem lowS_zo_221_2_149:Lower true dzo_221_2 roots_221 gzo_221_2 7:=lower_iso_b (d1:=dom_221) (r1:=roots_221) (T1:=gsh_221_2) [(dom_221,2)] (by decide +kernel) (lower_slice_b (T:=gsh_221_2) [(0x33003300000000003300330000000000330033000000000033003300,0,8),(0x33333333000000000000000000000000333333330000000000000000,0,64)] (by decide +kernel) lowS_149)
def dzo_157_2:=0xcccccccc000000000000000000000000cccccccc
def gzo_157_2:=0xccccccc8000000000000000000000000ccc8cc00
def gsh_157_2:=0x3333333200000000000000000000000033323300
theorem lowS_zo_157_2_149:Lower true dzo_157_2 roots_157 gzo_157_2 6:=lower_iso_b (d1:=dom_157) (r1:=roots_157) (T1:=gsh_157_2) [(dom_157,2)] (by decide +kernel) (lower_slice_b (T:=gsh_157_2) [(0x3300330000000000000000000000000033003300,0,8)] (by decide +kernel) lowS_149)
def dzo_217_4:=0x30303030000000003030303000000000303030300000000030303030
def gzo_217_4:=0x30303030000000003030303000000000303030200000000030302000
def gsh_217_4:=0x3030303000000000303030300000000030303020000000003030200
theorem lowS_zo_217_4_73:Lower true dzo_217_4 roots_217 gzo_217_4 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_4) [(dom_217,4)] (by decide +kernel) (lower_slice_b (T:=gsh_217_4) [(0x3030000000000000303000000000000030300000000000003030000,0,16),(0x3030303000000000303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_73)
def dzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
def gzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000f0f0e000
def gsh_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000f0f0e00
theorem lowS_zo_219_4_75:Lower true dzo_219_4 roots_219 gzo_219_4 7:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_4) [(dom_219,4)] (by decide +kernel) (lower_slice_b (T:=gsh_219_4) [(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000,0,16),(0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_75)
namespace S_223
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,10),(2,66),(3,11),(3,19),(3,67),(3,131),(4,20),(4,132),(5,13),(5,21),(5,69),(5,133),(6,14),(6,22),(6,70),(6,134),(7,15),(7,23),(7,71),(7,135),(8,9),(8,10),(8,72),(8,136),(12,13),(12,14),(12,28),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,26),(18,82),(18,146),(24,25),(24,26),(24,28),(24,88),(24,152),(64,65),(64,66),(64,72),(64,80),(64,192),(68,69),(68,70),(68,76),(68,84),(68,196),(128,129),(128,132),(128,136),(128,144),(128,192),(130,131),(130,134),(130,138),(130,146),(130,194)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7ffffffffffffffff
def xsM:=roots_223.map (·&&&dom_223)
def gM:=goal_223&&&dom_223
def NN:Nat→Nat
|3=>2
|4=>10
|5=>34
|6=>136
|7=>234
|8=>138
|9=>34
|10=>5
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xe113ebd290
|4,0=>0xa287f833e47e9d16d905647ac4f1bd3deb32588b1c10b01a60
|5,0=>0xc6694c22c0bacbea3688a1a8697c9296e10873db846fb83c237e8f67ada27a3b661d5e61cbf5fd755bd2b5732d4d7744b78246bea42a604093c3a6c439b7438fd6385a02acf9281fa237e320b301c3ba1c384133df
|6,0=>0xcc149c8370c64fac4ddfc4830c2affc281abe0c1bc134b9d0cac47daa08da8c57a5542a2cbfa0c3a9fe519ec519ac079828694bbc912e2910748f1e08c7828c40c8a900899e588851878b58770f84f09833dd81a2e8193c808388072f804d27dc887a7ae795a076cf17656d7569c6b9f767d90675d366e3f659c4631d4631c75f1b65d1d15d1a15c39a59ff358e9b567fc565ec5510053e0d52c4651e7e50c7c4ee5b4be4b49298443fd41b6c4063940336401253e3ca3c9773c4da3a6063908735c08338fc32d393287f2f1592e9522e75c2d8ef2d5f82c0172ab1a289dc27788257ef24ae722a4121fa6211e21ca901b12f1a289188f314fcb14447137951300b1290c10ee710c501058b0f1840ce560bc830afe70ab0a0a9e90a5580a482095d40959e091dd0901508d2208b400836c074470600505a5903ea6032c001863
|6,1=>0xf9b9af89abddb2dd828ed5cecd5cb2d10fdcf133
|7,0=>0x57064565a155fcb5544753f1b528a1515cd51562502a14e3374c80f4c7324bb134bb0a4b42a4a2d549c3b48bff4847a480a046937463a3459e1459bb459b64543e448614456b4429f4369f4313442fe7428634241441aaf40a2b4004a3ee733ec173e2e73d9653d6083d24a3d1a03cf0a3ba7c3adfb36ed734b67349883479a3357b3207b3108d30b75300cb2f7f72eb752ea4c2c2532a3cf2a1b127e7d274e1270292459a2390023471221c6220e4220042190621468208962065b20447200d92009d1fca31eb2d1ea001e86c1e7651de7b1da731d9611d1871d0fd1cb491a9cd194cd17ee117b8c1796216cb2168c515e36156e514a78144bd126de120fd11614115f110c7f0f3600f1130e54f0d67e0caf20c71b0c2720bed30ad970a8f208f3c07e9407c87072b70724c06ed606a1f0518204d6404d530478d0244300881
|7,1=>0xfd808f6f46ea078e6ee9e5abadd90edb30fd6520d5a84d4298d1e7fcad15c9bd4c775cc3371c1b97c1838c0d10c09f4bfa90b9ba1b9277b756db64a7b4ec8b16ddaefedabe04ab2cda8943a5970a438aa4135a3560a1c9d9fe519f3039ba6d9aa0599e9b99a6f9773996ed49610094e0d941aa927b98ece48dd828dbdb8cd5c89e4989e2d8753286eb583e1d82f4c8261a804dc804d27ef227e5957cf3e7cc987c9f47b6067b202794e276ddb76c0876bb175640738fb70c7470aa7701ca6fbbd6f7e76f58f6d65c6ace76a67269b35682c065d7164c986474264465635b862d59621e261eb55fe365fd275f00a5cbcd5c7365c5ed5c5ea5c5225c12f5a91c5a52a59654591af57ab7
|8,0=>0xc4e1dc2d17bf0a2bed56bc413bbf9cba4e2b8ef6ace5ca9f15a92c0a6d71a1e42a0e36a0165a000a97a45975d9920318dd828bf708a6df854128529f8401283447814337fed27fc177e3377ca7c7bf0274129740447217a6fb756732465d78649006156f614476129c610d9600c05e9615e0fd5c6c1580ca5395e53406521fc50360501d4501134f4e44e2044e0c24a32d4840a47ed64682b4633945d64459e14553f4357342d40401c64014b3f06539f9638f2e3881337a90375f63572d34fe733f6831e5f313b530e2c3085d2f1d62eed32eb7c2eace2b32a2a3ac2a19229e3329d0527d6f278c625212237a92372922e4621d3c204431e5af1cecf1c30f1ba7b1b4fe1acb519b2519224184b41816d1752016c001586014c8d14c32131621256311e5610e3b0f1320c4d80b0b80abd80a298099370989908d870590401348
|8,1=>0xfc6d7f7b7deb1bee87feded84dcf72d5400d054bc8532c636d
|9,0=>0xfabead6d3cccff7cb6dfb11779b3958852c7ea407b49b79181613415b6bc58948518fd501d24ce6e4ccaf424353bfef3bc91267b125aeb242cf2275a2253b1c0f51bd4519e441154b1073a0d3a90b10506d07061a1
|10,0=>0x946447474a6375a4e3a91f206
|11,0=>0x1730e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffffffff00000000ffaaffaa00000000eeeeeeee00000000eeaaeeaaffffffff00000000ffffffff00000000ffffffff0000000000000000ffffffff000000000000000000000000ffffffff0000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00ffffffff00000000ffffffff00000000000000000000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0ffffffff00000000ffffffff00000000cccccccc00000000ccccccccffffffaa00000000ffffffaa00000000ffffffaa00000000aaaaaaaaffffffff00000000ffff000000000000ffffffff00000000ffff0000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00ffffffff00000000ffffffff00000000ffff000000000000ffff0000ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00fffffffa00000000fffffffa00000000fffffffa00000000fafafafaffffffee00000000ffffffee00000000ffffffee00000000eeeeeeee
|0,1=>0xffffffff00000000f0f0f0f000000000ffffff0000000000f0f0f000ffffff0000000000ffffff0000000000ffffff000000000000000000000000ff00000000000000ff00000000000000cc00000000cccccccc3333333300000000330033000000000033333333000000003300330000000000000000000000000000000000333333330000000033333300ffffffff00000000f0f0f0f000000000ffff000000000000f0f0000033003333000000003300333300000000330033330000000033003300ffffffff00000000f0f0f0f000000000ffffffff00000000f0f0f0f00f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000ffffffff00000000fafafafa00000000ffffaaaa00000000fafaaaaa33333333000000003333333300000000333333330000000033003300ffffffff00000000ff00ff0000000000cccccccc00000000cc00cc00aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaaffff000000000000ffff000000000000ffff000000000000ffff0000cccccccc00000000cccccccc00000000cccccccc00000000ccccccccffffff0000000000ffffff0000000000ffffff0000000000ffffff00
|0,2=>0xf0f0f0f000000000f0f0f0f000000000f0f0f00000000000f0f0f0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f000000ffff000000000000ff00000000000000ffff000000000000ff00f0f0ffff00000000f0f0fff000000000f0f0ffff00000000f0f0fff0ffffffff00000000ffffffff00000000ffffff0000000000ffffff0000000000000000000f0f0f0f0000000000000000000000000f0f0f0055555555000000005555555500000000555511110000000055551100ffffffff00000000ffffff0000000000ffffffff00000000ffffff000000ffff000000000000ffff000000000000ffff0000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffff005555555500000000555555550000000055555555000000005555550011111111000000001155115500000000111111110000000011551100000000ff00000000000000ff00000000000000ff00000000ff00ff001111111100000000111111110000000011111111000000001111110005050505000000000505050500000000050505050000000005050500
|0,3=>0xffffffff00000000ffffffff000000000000000000000000ffffff00ff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ff00ffffffff00000000ffffffff000000003333333300000000333333000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f00003333333300000000333333330000000033333333000000003333330000000000000000000000000000000000ffffffff00000000ffffff00ffffffff00000000ffffffff000000003333333300000000330033000f0f000f000000000f0f000f000000000f0f000f000000000f0f0000ffff00ff00000000ffff00ff00000000ffff00ff00000000ffff00000000ffff000000000000ffff000000000000ff00000000000000ff000000000000000000ffffffff000000000000000000000000ffffff00ffffffff00000000ffffff0000000000cccccccc00000000cccccc00000000ff00000000000000ff00000000000000ff0000000000000000fffffff000000000fffffff000000000fffffff000000000f0f0f0f00000ffff000000000000ffff000000000000ffff000000000000ff0033333333000000003333330000000000333333330000000033333300
|0,4=>0xff00ff00000000000000000000000000ff0000cccccccc00000000ccffccff00000000cccccccc00000000ccffccccffffffff00000000ff0fff0f00000000ffffffff00000000ff0fff00ffffffff00000000ffff000000000000ff00ff0000000000ff000000ffffffff00000000ff00ff0000000000ffff000000000000ff000000000000000000000000ff00ff000000000000ffff000000000000000000000000000000000000ffff0000000000ff00ff0000000000000000ffffffcc00000000ffffffcc00000000ffffffcc00000000cccccccc333333330000000033033303000000003333333300000000330333000000000000000000ff0fff0f000000000000000000000000ff0fff0000ff00ff0000000000ff00ff0000000000ff00ff000000000000000055555555000000005505550500000000555555550000000055055500ffffffff000000000f0f0f0f00000000ffffffff000000000f0f0000ff00ff0000000000ff00ff0000000000ffffffff00000000ffffff000f0f0f0f000000000f0f0f0f000000000f0fffff000000000f0fff00000000000000000000000000000000000000000000000000ffffff00
|0,5=>0xffff000000000000ffff00000000000033330000000000003300ffffffff00000000ffffffff0000000000ff00ff0000000000ff000000ff00ff0000000000ff00000000000000ff00ff0000000000ff0000ffffffff000000000000000000000000ffffffff00000000ffffff0000000000000000000000000000000000ffffff0000000000ffffff0033333333000000000000000000000000333333330000000033333300ffffffff000000000f0f0f0f00000000ffffffff000000000f0f0f00000000000000000000000000000000000000ffff000000000000ff00ffff000000000000ffff000000000000ffffffff00000000ffffff000000000000000000000000000000000000ff00ff0000000000ff00000000000000000000ffffffff000000000000000000000000ff00ff00ffff000000000000ffffffff00000000ffff000000000000ffffff000f0f0000000000000f0f0f0f000000000f0f0000000000000f0f0f000000ffff0000000000000f0f000000000000ffff000000000000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff0000ccffccff00000000ccffccff00000000ccffcccc00000000ccffcccc
|0,6=>0xffffffff00000000ffffffff000000000000ffff000000000000ff00ffffffff00000000fff0fff000000000ffffffff00000000fff0fff03333333300000000333033300000000033333333000000003330333000000000000000000000000000000000ffffffff00000000ff00ff0000000000000000000f0f0f0f0000000000000000000000000f0f00000000000000000000ffffffff000000000000000000000000ffff00000000000000000000ffffff00000000000000000000000000ffffff00ffffffff00000000ffffffff00000000ffffffff00000000cccccccc0000ffff000000000000ffff000000000000ffff000000000000ccccf0f0f0f000000000f000f00000000000f0f0ffff00000000f000ff00ffffffff0000000000ff00ff00000000ffffffff0000000000ff0000ffff333300000000ffff330000000000ffff333300000000ffff330000000000000000000000000000000000ffff333300000000ffff330000000000000000000000000000000000ffffffff00000000ffff0000ff0fff0f00000000ff0fff0f00000000ff0fff0000000000ff0fff0000ff00ff00000000000f000f0000000000ff00ff00000000000f0000
|0,7=>0xffffffff00000000ffffffff00000000ffccffcc00000000ffccffccffffffff00000000ffffffff00000000ffffffff00000000f0f0f0f0
|_,_=>0
def sP:Nat→Nat
|0=>0x101c99e1e084110c2818b100030c203c4142634782101c99e242cc1d2634904024430c2408406382818b304430d242cc133634909165888d0a2cc133228284024430f166038606080910c0c49822181822218b921658a8d203c40e1a0c581003028b020050512203860a100800608080
|1=>0x265468f16603933c14208221868304449973c48581003051216603a41a0c108221869212203861848588463050508208862488c112628904100030c242d0a01828904304430d1e2c4070c30182104431216603861a40789301c9920420006141420b3e1c990165888d0a244110c28289
|2=>0x2e30f12164d82f1828904161c9a9189c904104cd8c203c5980e4c685242c893522890b107498d1848208221861212203935c3090b229168c144822b224c6aa242c893523490b10a0e0c149c904104ce0d242cc132a98505242c4133634904103860f16608933c2890916203a4184859a
|3=>0xe4dc0d18d4588224d88a062cc112635992122c3935a30792166099514dc904101c98c240841338d8692164caaf1829a92041040726404880e4d88c2048588684c69204208861a28904101c98c66481080e4c69e062d91126346101e10c11263479216609b01414598224d88a062c893
|4=>0x1a4821126e060a74d490b104499216203861a3029216608a41440789101c98c541459126bc6837c2cc1126353920821a1318e890b104de8c242c9bb7830510060841338342921621a131a40298224d70a242cc13763451208449b81a30909304499e144859f224c6ba242c413723090b
|5=>0x164ddad182890b2c446c22410407263090b224e08c14d4908224d70a0a2c40726c469204203935c34902081c9af1848232224c68c544811126bc6902410413363090b641c98d18a8902224cb8d240821126f06c0242cc072634904104430d181459f224c53f242cc112634902161c9bc
|6=>0x263479216603938a48588229060a204840e182894616449c3143c108224cf0a2048208684c61216203a41a3090b1090a8c14dc904304498d242c4246030512164cabc1829a92122c40726dc90b301c98d2410c1126359921604886182890b231218c1449108224c60a242cc072635992
|7=>0x4208933c485980e4c69e06084112635992164e3c3182829216609bd14dc909101c98c242c4244230505082cf91262829216609bb143c90b105098d20142180e4c909101c98c664858726e0645242c9b05a305121645217182938316449971a485938e5c60a0a2441126785101e08407
|8=>0x82cf872631512167c8931a42588224c683162088618e890b304498d10449ae6230505062c4136034284104499e242c411263651016688931a14208224c6b3242c41126364920422413144859126a468a1e4848b301c9a5242cc07263478b104430c1448218224c69e242c8935a30503
|9=>0x149c90b104dc8c1448488224c61e140c588224c61e242cc07263530f0a2cc11269851024208935c305100a2c407263494d1644997182938316209b0182890216449ad182818b104498d18cc284104498d3c42608224c69216603935c3490b26ecb8c140c108224c69e4e14904301c992
|10=>0x224c633144820b3e4498c140df0b104498d189c90b104de8c149c29216603931440904301c98c4a4848b101c98c20484880e4c68c2048488265460a242c4133630527242c413763051216449bc19145100a208935c305100a10411263490b104dd8d182890b113898c1415f0b104498d
|11=>0x224c6c5242e588224c68f242cc07263481216449ad1829392082039318d490b104498d14a890416608931a48588a04c68c2534591270c60a0a2cc112698505242c41148305270a48218224c525242c8935a305270a0c588224c6ba5448588224c6121622413182880f1660893140c588
|12=>0x104498c149c90208208931a40902101c98d242c413323460a4e0c591265c60a242c89378b860a2048591276460aae0c588224c60a80485880e4c68c24105880e4eb0c6a4820b104498d241058826ec60a242cc1126b868a7e48588224c68ca848591274c60a062c893863290a0648598
|13=>0x783052a0a10598224c50516228131829a83242c4112634902082099c1ae8909162089318a8908224d70c144820b0e4d78c242c8937030512162099c62305127c2c41332305121220995191452a242c411483052a0a2c411263490916609951a2828b10449d11a409090820393180df0b
|14=>0x241041126346330a4858826c068a544848b101c98c242c40e1828902101c98d8a0c588224c68c3c0c591265ee8c1448588276860a064810b224cb8d242cc1126c468a4e40904104498d242c407263463320dc588224c60a4e4090b101c98d0a2c4112634f0a242c4342630512122c893
|15=>0x603051208208931879a92042c4112629285242cc112628192122cc11263490b104498c662939208209b01829392162099b182890b104dcdf182951204208931a48588221860a6e485880e4c68c2410588224ef0c1e2c41126c460a204859f224c60a2424588229060a4e48588267068a
|16=>0x304498a6a48104104498a202441126c460a200c591265c68c1e2c8932e3130a4ee890b104498d0a2c893783130a24f8598224d30a0a48588265468a24f85880e4c68c0a2c411263198a242c448263460a241059126a460a2410598224c6a6242e608224c6b50a0c588224c510062c413
|17=>0x1e4820b304498d0a2c40726353102424413383050f242c40726322ba1e48588224c61216608936c3539216449af182880b344498c1495a92162089314dc904104498c157090b104ed0c14d490b224d48c149d51216208931a48591265f00c140c90b104ca8d189c29208208931b6c28b
|18=>0x101c98c4c40902104dc8c141490b104de8c14e82921660893143c598224d30a544859f224c60a0a4858826ec60a212c41126305106a14588224c5100a1040726309091620393623090b304ca8d149c18b104ce0c14a880516608931448593385c60a0a0c58826c060a242459126b460a
|19=>0x16208931a9890b104520c141490b30449ae14d490b224d78c14d42921620893144b08b224e18c144090b224d48c1448588221868c14a890b104dd8c14485880e4c68c3c1418b104498d8a40789104498c14d490b224cb8c149490b104d80c149dd0316208931840909304498d144848b
|20=>0x1442608224c60a0a2c41126c468a240841126b868a54d428b104498a4a48591265c60a1e4859126b460a4a48588224c60a2584111265c60a2188598224c51006088932e305102410413603050f24245880e4c6106a48108224c525242c4072634625242c4132a3051216449d31828182
|21=>0x1620893623050316449971a31310242cc07263539216449bc182890b224cbd81829392082099c182828416208931a9878b104498c662890b224ec8c14a819204208931a4859126b460a0a0c48b104498d242c414263418b10449dd1b08904104498c156c902104ce0c1440904104ca8c
|22=>0x241041126b860a200c41126b860a4a2c41126c460a2014488224c68a242f311265c60a242c413323130a5440902104498d203c108224c68a4e4841126b860a0648593385c60a2408588224f28a4e485880e4c6aa242c8935e3461216208a41a30563242c413383050f7c2c4112630503
|23=>0x143c90b224cb8c14a819216208931a3090b304498d8a2829216449bc1829385242cc11262890916209951a30503242c411276060a2048588229060a4a48588229060a0a2cd11262880304208931a4848b224d78c140c90b104520c14149041660393544820b0e4d78c4e1418b304498a
|24=>0x16208931829d12042c411263051024244112630505242c4072635512082c8935e305121620893ba345121620393ce305121620893ac305120820893583050f2408588224c68a4e4848b104498c14a82841620893182890b30449a6144018b304498c1448588265460a4a4090b104498c
|25=>0x82c4112634626d248208224c60a1e48598224c5250a48588224c60a0648588224d70c144859126bc60a541418b104498c15a490b101c98c159090b104ce0c140c902162099c182938316208931828292082cc11262890b10449b11a305052424588224c68a242420b104ca8c14a9a92
|26=>0x224c60a4aa890b104498c1448488224c64514e88121620893182890916608931a2890216209b918289041620893623053f242c411263052a2408208224c60a242c89386305127c2c411263130a242cc07263490b114098c150090b104498c14a881216208931a3080f16208931a30512
|27=>0x26bc60a242cc11263530a24082080e4c61216449eb182880516208931a2890b104498c662886a1620893182890b104ca8d18295100a2c411263052a0648108224c60a242c411277860a4e3c90b104498c1448588284c60a062c411277460a064810b104498d4e4858826c060a204aa88
|28=>0x2048108224c60a1e48598224c68a4e48208224c60a0a4820b104498d4e485880e4c60aae48588224c60a242c413727060ab648108224c60a2048218224c60a203c18b104498c14949091620893182880316208931a31b9216208931829d05242c4112630510242cc07263052a2048591
|29=>0x224cb8c1448108224c6c5144810b224cb8c1448588224c68c662881216209b0182890b101c9dd182890b304f68c14d490b104498c144820b224d78c140c90b224cb8d184018b224cb8c1440909082089318288120820393190090b104498d182879216449bc18289041620893ac3052a
|30=>0x182890b10449cf182828b104498d4c2b1121660893143c90b104498c8a29392162099c1828909042089319145270a48588224c68a4a48588224c60a8448588224c60a20485880e4c68c200c108224c60a6e48588224c68c140c90b304498d242c4112630f0a2424208224c645141418b
|31=>0x101c98c144820b301c98c1e4848b104498c1448588224d70c149490b104498d1828812162089318cc5120820893191450f0a48598224c50316208931898512172c411263051216208931a30f0a544820b304498c14a890b104498d1848588224e88d1840284104498c144848b10449b1
|32=>0x14a81921620893182890b224cb8c15a490b104498c144820b304498c144848b104498d182890b101c98d18a89041620893182890b10449ac18287921620893182890216208931a985275448588224c60a4a0c90b104498c14485cc104498c1448588224f78c141418b104498d4e4090b
|33=>0x164499718288031620893182896e1660893182896a1620893182890416208931a313921620893182890b10449b6182890be060893182881216608931829510242c41126305121208588224c60a242c411263462614484841620893182890216208931a289041620393180c90b304498c
|34=>0x90b104498c144090b104498c140c90b104498c144820b104498c1448588224c68c14485880e4c60a0a4820b104498c140c9021620893182890b301c98c144090b104498d182890b104498c8a28805162089318289711620393182b1121620893182828316208931828192
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x880004
|4,0=>0x6aa0305015a80994042a01c500ba8049401aa0085
|5,0=>0x1fac0f76078b03ad81cac0df606cb034d819ac0c85061302f1816cc0b0605530295413ec0996049b02358110a082603e301d980e0c06a60323017980b0c0526026301198080c03a6
|6,0=>0x15b38abdc550e2a1714d38a4dc51ac286713fb89e1c4e2e26a7131b8971c4aae24e7123b8901c472e2327115b8891c43ae2167107b88258404e1fb70fa387b5c3cce1df70ec38745c394e1c370de386d5c35ce1a770d038665c324e18b70c2385f5c2ece16f70b438585c2b4e15370a6b0519c27ee1396099384adc248e11d708b384454214e1037
|6,1=>0x236b119d88c0e459722939131888ae43f621c390c5c856c424720eb9059c81ee4087200b8fed87e8e3ed71f338f7dc7b0e3d171e538f0dc778e3b661d7b8ea1c742e39a71c9b8e31c70ae37e71bbb8dc1c6d4c36371ae38d55c69ce34771a038ce5c664e32b719238c75c62ce30f718438c05c5f4e2f5517738b9dc5c0e2d9716938b2dc588e2bd7
|6,2=>0x251b9275892ce48f724439205c8f4e4737
|7,0=>0x34941a2dcd07067b8339c19b1ccc9065c832a419320c89063c831a418b20c49061c830a418320c0905fc82fab97b9cbcd05df72ebc173e0b90e5c082dcb96c60b5305a182ccc16460b14e58372bdc15ce0ad7056382adc1551ca990544829e414d5ca5b0525828ec1459ca1d0507727fc13de09df04e87270b936609a304ca7261412ea096504aa8
|7,1=>0x441c21f1d0e9086c84324217210a9084c8422420f21069082c8412420721029080d7402c1ff60fece7ee83f341f7a0fad07ce83e341efa0f6ee7b073d441e820f31079083c441e020ef1077083b441d898eb6e75383a5c1d11ce790734839641c920e390714838641c15cdfb06f5837739b9a0dbee6d78367c1b21cd82e6b98358c1aa60d43069a7
|7,2=>0x53c3a9c214d10a60852c4294214910a40851cba8c614530a21850cc284614130a0274fd427cdd3d709e384edc274e139709c384ddc26ce135709a384cdc264e1317098384bdc25ce12d7096384ae3a55212990945749ec24d9d25d0927748fc245e1220e9088480423e211e2e8e98470c236611a4e8ca8461ba2ee116708ab8451c226e1127088b8
|7,3=>0x17790bb485d732e9dd73f0b9785c83ae2217010b7885b842da216c10b5885a842d2216810b38859842ca21642eb198588c2c2616030af98578c2ba9d5c50ada856942b2a15850abb7559c2ab1d5490a9e654bbaa3e150f0a7f8
|8,0=>0x6e74371a1b7b2db496d64368e5b38ed9486c6436121af90d7396b5c358a5ab50d5286a4cb5061a712d3176944b4899a36ed1386854b40659f12cf08674bb38259af2cd07663cb2fe196f0cae96534327a192b2c8c9641cb1ea58e32c6986313b16658a30c498620c30e618612c27960f4b05dd81f0c0875ffcafde17dd2be685ef42f5a179b2bc49
|8,1=>0x7ed4bf465f930fc187dcc3ec61f512f9f97cbc3e3e1f0f0f7e97bb43dba1eceef5e97ab43d365e892f3c879a43cb21e490f1b978a3bc321e072efb8779c3bae1dc52eda876943b2ddd870ebb8759c3aae1d452e9b77494ba2a1d032e789738439a21cc10e588728439221c810e388717cb89a5c3d0e168706cb8161bf92df486f6bb799dbbd0dd68
|8,2=>0x205b3024980dcc04e2017100477fdcbfd1dfd72fe38
|9,0=>0x2287313a9899bc4aa6245111a88894442a220510fa8879443aa21c510da88694432a218510ba8858cc2a2613f309698474421de0ff10769837bc19e20bf10569827bc11a607d10368
|10,0=>0x116b88b1c456e22a7114c7
|11,0=>0x11737
|_,_=>0
def wAt:=mkWire dB 114 224 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x62d2429044704491631284d1629041c163122292034103114314a4f12490831162910312034182922292431267916292034242d18291631267920342429242d1829103116351649243518292229344d1829164906602429103124351431242d041c16312229344d066024291635143110311649284d041c1631243518292229
|1=>0x16362034143110311431546020291649103116364a23124916351829243512471635143124261635242d18294e1c222914312031267920341631143122292034164914312034103116292435164914314e4716150a2924312034242d06230449163110311649243518292229267916292034242d1829143110b1044b16291631
|2=>0xa2d062324311649163124351829222916361031243518292229284d242d041c16312229163625152229163618291431344d06602429103108162431542320345423084916292034062d0623242916291e2324351431162926792034182924315460202916491031203716491635164924351829222954232029242d24292425
|3=>0x18294e47242916151431243116292034242d182918291649066024291031182922792034163116491431163510312435182922292035242d10311829222926792034243516492034103116491431163120342429242d18292034242d10311829222918292431546024111031041c163124351829222910312431242d16292229
|4=>0x4a472035242d233d040e242916312436382904470449163120341635242d182920342429242d1829222910312436143110311e4b0a2924314a2f54312029242d14312431242d2229170d2e31062324294e470a2d24314a234e29044916312036242d1829242d0a10182924311629060816312429242d1829267920342429242d
|5=>0x4a2320351649143124291615243114314e2b20312029242d22792034242d18290a2916492431103124ba163e06312429546024111031243660294e47044916312229243110311031242d16292229124908311629222922291635242d1829164912471635182974474e2b044916314e29044916310a2924311829242d24311629
|6=>0x16294a47242508311031163e2435143180292037242d1829aa4908331629250e2e31062324291636182924291031060824291631143110312435182922294a234e2920312031242d162922294a332035164914311031162918292345160e24291829170d2e310623242910311e4b0a2924314a4f163d0a291629161524311031
|7=>0x4491631062d163e0631242954232411162922296e2325151636182916992436143116361247163518294a4f5431062d2429084914311629243112471635143110311431062f243124290831242d16292229143104491629163122291631164914317c47169924360a2d062324315e31542320292561060a1631242954332411
|8=>0x41c16312229163122291636182920342429242d1829b847b631202b242d1631242616351431103114312031164922292036242d182924cd203616491431222914312031164920342431164914314e1c2031242d222916351e232435143124312411162910312345062f243124295433062d242916291431044716314e2b0429
|9=>0x242d18294a334e29044916314e2916152431103124291635143110314e470449163104491631382904471631202916311649143126792034242d18292515222916361829ac2908161629243124352426163518295460103120294a4f1249163518290447044916312036242d18294e471615243114312229241108311629284d
|10=>0x162916152431202b16492431103154330849162924261635242d182906231e4b063124294e2b044916311e231e4b0a29243110311699243614312431124716351829222916992436143124ba163e0a29243122792034242d6a235433241110311629243614310a101829243116295433062d242924294e472031164916292034
|11=>0x1631062324294e470a2d243124294a2312491635182916292435143110312229243124361431164904290447163124352229163618294e2b16150a292431084b182916291031203154232029242d164906602429103154335431062d2429b631202b242d5433062d2429182920312029242d2e31062324291247163524291829
|12=>0x143154330623062d24294e474e29044916314e2b04491631242d1635143110312229163524361431242d38290447163160294e4716154e2b161524311031243510312436143120294a47163d0a2906081631242d24292029242d2431242d16292229124b08311629222912471635143110310447044916311649243110310447
|13=>0x16294e472031164916352435182922292029242d163d2435182922291249124716351829a823aa4908331629163124364a4f2035242d182910310a2924315433062d24294a33163d0a292431165d2e31062324296a235433202926792034242d18294a475431062d242920342229242d18292429243116361829163524351649
|14=>0x24294a2320351649143124311635242918291829041c1631222918290a2f243124291759081616292431202b044716491247242d083116290a10242d24311629242616351829163e243514315433062d242954310623062d24291e2d2435143180352037242d1829165d1631062324290a2b1649243110310623242916491631
|15=>0x242d182920291649143124351631164914311e2f16150a29243106232429044716319e31040e24291631044914311631222954232029242d4a4f2035242dc82b044716314a4b5431062d2429243618290623242d1031182922291e2316150a292431044704491631162924362036243514315e315423062d242916311829062d
|16=>0x1031163618291e230a292431161524311031124716351829060a163124294a4f543120294a4f2035242d1829243106602429103116312429242d182954232411083116294a4f5431062d24292431103116292229542324111629222924291615243110314a2f242508311629242d163e0631242924c5124b1635182924311635
|17=>0x10312426163518292431163518291247083116295433062d24294e2b044916311635242d182914312431222954232411162914311616243125a20e312229081616292431044b162916312435163114310429044916310849162924311031243614311031242d242912471635182954312029242d0631062324291829062d2429
|18=>0x8311629d229203316490849162916312e31062324291699243614311031182922292345062f24292037242d182918292029242d2435164914311629243614311629203316490a2924311031163d0a292431163e063124295423062d2429062d243124292229203316492471044716312429044716310a2d2431242916292431
|19=>0x1031243614312229162916310663242910312431164914312516163618290633242d242912471635182924312029242d1631062d2429ba291616243116150a292431041c163122290a2f243124292429163114314e47044916311649083316295431062d24291715163618294e2b203116491635143110313829044716312426
|20=>0x623242d2429242d08311629242d162922292037242d1e23243514310816243116312029242d2435143110310449162916311829243116292031242d2229d849042b16313829044716311631202b242d1629164910310631242d24291249163518292429242d18292515163618294e2b1615243122291649103154232029242d
|21=>0x1829044704491631122f042916311615243114312035242d1829c42d0a2b24312229242d18291631242d24292515163618291829242910312034242d1829122f083116290623243124291631163618291631062324292036242d18294e4720311649222916162431dc47166110315433062d2429542324111629182906232429
|22=>0x5829044b16311829243124292229203116491031162922292435163518291e2f243514312035242d182920361829122f0831162910310a2924311e4b063124290608163124292034242d18292411162910312029242d1829160e24291829242d24311629124b16351829040e242916312431243614310a2b2431103124351636
|23=>0x2431242906232429242d2429166110310633242916291829044916312412162930291031164910312029242d042916312436143108311629163114311629222924291031062d2429062324292033164916291031163518291829222924111629044b16312435143116312436143120312029242d5431062d24290a1024311629
|24=>0x242d2429162918292229243116291631242910312229242d18291636182924311649161d22290a2b2431
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0xe00000000000
|5,0=>0x2b4000000000000000000000000000256000000000000000000007d800001960000000009b00000000000000000d60000000000000000000000003b0000
|6,0=>0x27044c989540000245046288a20000000000000000000215441180000000000000008110000000040087f10f861dd400007610000000039206e40000000000000000d48199031200000bc817442c285440000144c000000009e41294000000008aa0000000040507c400001d9800000000d9419982f4
|6,1=>0x208a3fd400000001f683d940000f151e02000075a80001cca38546ea0d940000351467a8ce10000000000000001948000062a8c0500000000000000017a600000000b85166a0000572800000000000000000015a200000000000152800000000000000000000000a451444000000000000000284450089d3
|6,2=>0x42540000000000000000000000
|7,0=>0x3be876d0eba00003a6873d0e619c930000718ce12000000006fccde19b8436886c4cd6a1a9434a86850cf199a432c864ccc7a18b430e8610cc0217c42f085d10b8216c42d08594cb2096042ba65650aaa151429a85250a318000288450109e9939427024d1098212c42508491090211c42308454c88a10e3
|7,1=>0x57a6ae515b1ab240000ab91559aa745468a7d14da29745286a44d46a289450c6a0913f227a44ec89c9000026f34da49a8d33226244bc896912b2253349e8930d249a45448288f511ca235400008c51180a2c44526895110a21d44328855108a20d44128818d0121fe43f487d90f9200003de67ad0f3a1e34
|7,2=>0x7408e74dcd1b9737268e40dc6238847088e011be237846ec4dc91b7236a46d04d911b09b5e36b48d591a99b4f46968d1d1a1a33f46768cdd19a1b3046588ca11929b21463a8c7058c9b1546264c3d185a30746086c04d7ea2f945ea8bc5176a2e945ca8b8516ea2d945aa8b4500002ce35966b1d1621ac04
|7,3=>0x2171c2a484c908920f241a482c9049207240a480c90091ff200000000fecdfba3f347de8fad1f3a3e437c26f78c0003da47ae6f4d1e7a00007986f289e39bc3477e8eed1dba3b3475e8ead1d41ba44
|8,0=>0x9dc73ace741ce539c4737ce6e1cd939ac734ce681ccd3994731ce621cc1397c72ece5c1cb5396472bce561ca9394c728ce501c9d3934725ce4a1c91391c722ce441c85390471fce3e1c7938ec71cce381c6d38d4719ce321c6138bc716ce2c1c5538a4713ce261c49388c710ce201c3d387470dce1a1c313
|8,1=>0xb5676a4ad31da33b407674ecd1d973b287644ec71d8b3b107614ec11d7f3af875e4ebb1d733ae075b4eb51d673ac87584eaf1d5b3ab07554ea91d4f3a987524ea31d433a8074f4e9d1d373a6a54c8e98152d3a54749ce921d213a3c746ce8c1d153a24743ce861d093a0c740ce801cfd39f473dce7a1cf13
|8,2=>0x2e49dc63b867700ede9dba3b6e76d0ed89dae3
|9,0=>0x307160c2c145820b0316042c045800aff15fc2bf457e0afb15f42be457c0af715ec2bd457a0af315e42bc45780aef15dc2bb45760aeb15d42ba45740ae715cc2
|10,0=>0x6141c2638487088e101
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 15
def pmP:Nat→Nat
|0=>0x40000000006a0000000198000000064000000018000000004e000000012c000000044000000010400000004000000000f000000002e00000000b000000002b00000000a00000000220000000084000000020000000003c00000000d000000003000000000b00000000280000000090000000020000000007000000001800000000500000000100000000020000000004000000000
|1=>0x85bc0000020e7000000839800000206f00000081b8000002069000000819c0000020650000008190000002060000000813800000204d000000812c00000204a000000811c000002044000000810c000002041000000810000000202e00000080900000020080000008018000002004000000800000000100500000040000000008000000001f8800000020000000004ac000000128
|2=>0x6819c00001800b00000504800000120670000040500000010040000004008800001000b0000040008000010000000002811c00000a02c000002808000000a000000002010000000802b000002002c000008004000002000400000800000000181bc00000602000000180000000041420000010100000004026000001008800000400a000001000000000306f000000c0bc00000300d
|3=>0x1581bc00005002b00001285bc00004a10d00001281bc00004800400001181bc00004216f00001085a000004212c00001081bc00004204f000010808000004200000001005b0000040168000010059000004014d000010053000004010100001001a0000040041000010010000004002e00001000b0000040028000010009000004002000001000300000400000000090000000020040
|4=>0x850598000214124000084010000020616f00008185a80002061620000818518000206144000081841800020606f00008105ac000204166000081059000020414f000081049800020402400008085bc00020206f0000808190000202000000080050000020004b000080010000020002f00008000000001420010000408000000100003000030008000008206f000020000c000080000
|5=>0x88281b000220216f00088081bc00220010100081180b400204206c0008108000002040044000805811800200606f00080180980020060030008010198002004026000801008400200400100080085bc00200206f00080005bc002000041000800001800200000400060000f000040000000009181bc00024400b00009081bc00024206c000090800000021616f0000858518000216000
|6=>0x401085bc01004206f00400681bc01000a06f002000002400600600b001801019800600206b0014000190004200022001050049000404316f00101085bc00404214b001010813400404004d001008c1bc00401606b001000853c00400206f00100081900040020000010000190004000063001000010000400000c00089281b0002248044000890c1bc00224206f00089081b000224202c
|7=>0x8800c0b402200112d008085c1bc02020602f008080c5bc02020306f00802484bc02001216f00800481bc02000606f00800181ac02000206f00800081b402000204900800001000200000000048d0819c0122ca06f00489281bc0120ca02700482081bc0120800670040e085bc0102ca0630040a081bc01020a06f00408005bc0100ca16f004030019c01008216f00402081bc01004304f
|8=>0x60c000c1bcc0008306f228005c1bc82001706f204020c5bc80000316f18012089bc40218206f10002081bc21008206f08400081bc10008006f029000c1bc08600206902104081bc08400306f010810803004200306f00c020c5bc03008306f00c020409402600706f00980180bc02220300d008801c1bc02200702f00880181bc02200606b00880180bc022006002008800c1bc02200302f
|9=>0x282002306f808000e1be02000206d
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x10000000
|5,0=>0xe000000000000000009000000000000240014000002a00000000002000000000000001600
|6,0=>0x3506800000da200041438010c000a1782c2800220708700000000001800200a000000000138000005080007a000000000002180000003080000000000000a954000000000088ac16001582c18000388024000000000000502c00000000062000009843018980043000000e020000000000380c1c000c1580a020012400004001400000f0000001128004e000008c1c07
|6,1=>0x2b00000001880000
|7,0=>0x5cc21121121ac172b1059cdaa182880d92384e8a51e042c19c0052400392a3b230100203039c918530f0f9a02b000c48665518d80cb80e2080e902e16ce84d00be46800039b0049231aece00062b8cd2270000c1e000011c9caa0b80a04d71c42406e80b974be0c89039720a6080473031400c3e2a3d434a020331540e0001af0a22f31214309688ad008ea0409c168c
|7,1=>0x60a872980e10861161e0402804cc000022d560108011d85a0b038000f2542c0e003931c06f2240cce314568102c735e99154896d95c14f17f910a6140b13d083a650c8060207860061c010e46e14302051866631ac1c676d3c01ca50b39426e042a805c2d03ac9908308005fc07210040007010c0061b
|8,0=>0x4500d9b07670f0789e4e1fd7c1325b6200d6779f1803c573854ed98ea38dd0468bcd1ae675c7c78f87abf0eee90b414069b853095eee3dc554afb5b8492ccc524312f10724817acc4b3793294570b104af3cbb51e19692e9a8df0e23934f463479ba8e4c2cd968f830843af750b9e2a6861404de7636a517e788c2455f16571f56a5449c4dfadc06c1d3ecf82b0cda59
|8,1=>0x196353f0f0f6b66246c283c
|9,0=>0x15e798f23998bd8cab96cf64b488963f610fe42fa4e1f598783ab8a38a27a23a34d38ba70f6b6
|10,0=>0x8e258fc7882
|11,0=>0x3c
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 38 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_222 10 roots_222 ops++addP pm 1 dom_219 10 roots_219 ops++addP pm 2 dom_215 9 roots_215 ops++addP pm 3 dom_221 10 roots_221 ops++addP pm 4 dom_74 4 roots_74 ops++addP pm 5 dom_207 9 roots_207 ops++addP pm 6 dom_159 9 roots_159 ops++addP pm 7 dom_148 4 roots_148 ops++addP pm 8 dom_87 6 roots_87 ops++addP pm 9 dom_85 5 roots_85 ops++addP pm 10 dom_158 7 roots_158 ops++addP pm 11 dom_91 7 roots_91 ops++addP pm 12 dom_155 7 roots_155 ops++addP pm 13 dom_95 9 roots_95 ops++addP pm 14 dom_75 5 roots_75 ops++addP pm 15 dzo_149_2 5 roots_149 ops++addP pm 16 dzo_75_4 5 roots_75 ops++addP pm 17 dom_211 8 roots_211 ops++addP pm 18 dom_149 5 roots_149 ops++addP pm 19 dom_93 7 roots_93 ops++addP pm 20 dom_205 8 roots_205 ops++addP pm 21 dom_199 6 roots_199 ops++addP pm 22 dom_213 8 roots_213 ops++addP pm 23 dom_206 7 roots_206 ops++addP pm 24 dom_27 4 roots_27 ops++addP pm 25 dom_143 6 roots_143 ops++addP pm 26 dom_31 5 roots_31 ops++addP pm 27 dom_145 4 roots_145 ops++addP pm 28 dzo_213_2 6 roots_213 ops++addP pm 29 dzo_203_4 6 roots_203 ops++addP pm 30 dom_139 5 roots_139 ops++addP pm 31 dom_203 8 roots_203 ops++addP pm 32 dom_29 4 roots_29 ops++addP pm 33 dzo_221_2 7 roots_221 ops++addP pm 34 dzo_157_2 6 roots_157 ops++addP pm 35 dzo_91_4 6 roots_91 ops++addP pm 36 dzo_217_4 6 roots_217 ops++addP pm 37 dzo_219_4 7 roots_219 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_223 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_149_2_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_75_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_145 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_213_2_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_203_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_221_2_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_157_2_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_91_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_217_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_219_4_75 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_222 10 s (0,roots_222.map (·&&&dom_222)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_223 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_222 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_223==dom_223)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_223 gM v ys):RunD true dom_223 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_223 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 10 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 34 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 34 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 136 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 136 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 234 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 106 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 234 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 138 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 138 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 34 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 34 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 5 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_223 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0
def gzo_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0e00000f0f00000e000
def gsh_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0e00000f0f00000e00
theorem lowS_zo_235_4_75:Lower true dzo_235_4 roots_235 gzo_235_4 7:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_4) [(dom_235,4)] (by decide +kernel) (lower_slice_b (T:=gsh_235_4) [(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f00000000,0,32),(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_75)
def dzo_207_32:=0xffff000000000000ffff000000000000ffff000000000000ffff00000000
def gzo_207_32:=0xffff000000000000fffe000000000000fffe000000000000fefe00000000
def gsh_207_32:=0xffff000000000000fffe000000000000fffe000000000000fefe
theorem lowS_zo_207_32_200:Lower true dzo_207_32 roots_207 gzo_207_32 7:=lower_iso_b (d1:=dom_207) (r1:=roots_207) (T1:=gsh_207_32) [(dom_207,32)] (by decide +kernel) (lower_slice_b (T:=gsh_207_32) [(0xaaaa000000000000aaaa000000000000aaaa000000000000aaaa,0,1),(0xcccc000000000000cccc000000000000cccc000000000000cccc,0,2),(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0,0,4)] (by decide +kernel) lowS_200)
def dzo_203_32:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f00000000
def gzo_203_32:=0xf0f0000000000000f0e0000000000000f0e0000000000000e0e00000000
def gsh_203_32:=0xf0f0000000000000f0e0000000000000f0e0000000000000e0e
theorem lowS_zo_203_32_200:Lower true dzo_203_32 roots_203 gzo_203_32 6:=lower_iso_b (d1:=dom_203) (r1:=roots_203) (T1:=gsh_203_32) [(dom_203,32)] (by decide +kernel) (lower_slice_b (T:=gsh_203_32) [(0xa0a0000000000000a0a0000000000000a0a0000000000000a0a,0,1),(0xc0c0000000000000c0c0000000000000c0c0000000000000c0c,0,2)] (by decide +kernel) lowS_200)
def dzo_205_32:=0x333300000000000033330000000000003333000000000000333300000000
def gzo_205_32:=0x333300000000000033320000000000003332000000000000323200000000
def gsh_205_32:=0x3333000000000000333200000000000033320000000000003232
theorem lowS_zo_205_32_200:Lower true dzo_205_32 roots_205 gzo_205_32 6:=lower_iso_b (d1:=dom_205) (r1:=roots_205) (T1:=gsh_205_32) [(dom_205,32)] (by decide +kernel) (lower_slice_b (T:=gsh_205_32) [(0x2222000000000000222200000000000022220000000000002222,0,1),(0x3030000000000000303000000000000030300000000000003030,0,4)] (by decide +kernel) lowS_200)
namespace S_239
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,10),(2,34),(2,66),(3,11),(3,35),(3,67),(3,131),(4,36),(4,132),(5,13),(5,37),(5,69),(5,133),(6,14),(6,38),(6,70),(6,134),(7,15),(7,39),(7,71),(7,135),(8,9),(8,10),(8,72),(8,136),(12,13),(12,14),(12,44),(12,76),(12,140),(32,33),(32,34),(32,36),(40,41),(40,42),(40,44),(40,104),(40,168),(64,65),(64,66),(64,72),(64,192),(68,69),(68,70),(68,76),(68,100),(68,196),(96,97),(96,98),(96,100),(96,104),(96,224),(128,129),(128,132),(128,136),(128,192),(130,131),(130,134),(130,138),(130,162),(130,194),(160,161),(160,162),(160,164),(160,168),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_239.map (·&&&dom_239)
def gM:=goal_239&&&dom_239
def NN:Nat→Nat
|5=>1
|6=>53
|7=>266
|8=>338
|9=>85
|10=>12
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x1d628
|6,0=>0xedb10e3c05d58fcd47dcd36bbd11cbcd6ccc629fc3461bf536b2429aa7f7a9e1ca2f639dbaa9677d92dee910b27804674d83738ad6fff26deaa6b7e0698c8665dc6517060224538c94d6b1431713553133bb6323172f2bf2dd572ce8f2c11d25a622246f19cb9183fb181da16c23141d012df610404100a90ff76090c308b490600700058
|7,0=>0x553595531d5517354ea854dfa54bc05296d507964ea424d42d4bfee4bd154b8c84a0bf49c5449a7947bda47a2245a3b4556b446a74447743e9b432384227841ba141981418af3f2e53ea173d4603d4013adaf3aa863a4303917037c333764e3754c375423709633241322a931b4331b293077c300cc2e8552cd7f2cc862c25d2bbc92af1a2ad8d29c012925428c9f2893f2868f28320258ac249962493d2400e23b0d23a4e2341d233ce22b6a2282722385220ac213c82110e20c7420967205d32003f1f8b31f5891e9781e69f1d24c1cb051bd0019fed19ea6197071945918fbb18b4a17df2161731592914f8514749141d013174125cd11d8d11a561054e0ffff0e6a20e56a0d03a0b6410ab140a55f09bf8093f60892c0884f07de807a20079650755b071e706e3f0600705a2204e7b04cac0430903fcb03762021c200899
|7,1=>0xe4892e2844e1c8be0986dec3cdd1c4dc686dc5cbdaa3dd8dafd8178d780fd47dcd3933d351ccd565cc5dfcb360c9e49c9a8bc826ec79a0c6f6cc640ec0f63c0c82c062cc0267bfb1ebe4a4bc981ba2b3b9802b9171b7837b3084b23d5b1dc5b0dc1b0828b0735afbd5afa3ba9467a8dd0a8a46a807ca7f61a772da62bda623ba5058a35dca3448a22e79e1839daef9cfbd9b2aa9a2f99868a96b2a966c29637b9623c95a089412b939039385d92b3e927e68e7aa8dfe48c11e8bc0986b0b8415983452831fa82297815737f2a47ed8a7cdf07c9e67bffb7bd297b96679dec7807574bce7438e72abd725ed7239372182715db70eb9706e16d31669e1b698af691236810e673c465ae36546d65170648a76456a63ebb63378624f0623be6221761ab4604bc602925fecc5fe3e5f2155d7485d3505ce4d5bdd45b0db592dd56442
|7,2=>0xfee73fdacefbde7fa891f6695f09dcef5c8ee035eca49e9574
|8,0=>0x419a3408d43fc893fbba3effb3e2e93e0eb3dd333db6b3d21a3ca393c8cc3c4e73bbb13b7533a9e63a26439a60392c63917238e9938aa738a0a387203822e3817837d2437c78377e236fea36cbe36b6a366ae359ab3516e34e95345a5339fe31b4331b0e319b03104a2fe342fd3a2f1822f0452efd92ed002e2c72e1572d9e52ce3e2c8242c1f52c0c02bed52b64e2af212ab2429ba429afb2994b2920d28d2728cbc28cb128bee27d5a27799271d5265cb24cb1236782339f22ad121ec121ad321437212d420c3d1fe571d0dc1ca1f1c21c1bb8a1b91c1b80d1a4c01a30c16c2216ad3145591383e12a9f126ff11cd2119db10581100560fdca0fc840e41e0e0490d8160cc920c77d0c2260be640bd750abd80aa540a55f09b45093de08e8d079650770d0637e060d605fd605797039de0383903469025d002177020b000bca
|8,1=>0x9ed0d9dbae9b7d39b2aa9b2a59aab99a9bd9978c983f99816997daf975bc96b8e966df95f3f942459418a90e229040f8df568d4ec8a30b893cc88df088bf28840a866b8864fd84608827d382356817a98040f7ff1d7fec57fbdb7f96a7f2387ee277e5687e3b87e3677da197d9c17bb587b9667a0877807577e0b777fb772d4761b2757d173b0272f9e71ea96f06a6de5d6d9716d28f6cfb66c5846bc7169bc668e316899267def66c1665240638b563162629a0617696149060bc560bc2602615fd415e73b5d5795ca615c9585a6865a15859ee059eac5996c5967858ef25833457b1257a985701c56c84554d2554a355173542a25424953cde5313752e1f50ae74fe0d4f3ae4f1c74eb4d4e1344d7a44ce094c5484b6ac4b3be4b39e495754936548ab24769b460ab45a564556b453b044a5943c26437c84233141ed541d2e
|8,2=>0xff8e8fdacefb9f6f9ac7f702bf6695f4bd4f4b2af01deee7a5ee035e9dd4e608ee5e71e4a73e3b64e0986dddebdda2edc3f7daa3dd8f31d8858d782cd6473d4e1fd26f1d0e11cbc2ecb458cb0d9c9d3fc9a8bc9557c879fc7d6bc4f89c4e89c3d67c19dec102ac0f63c0ab7bee91be581bddabbcab3bc981bafa8ba8a9b91c2b8e9eb8421b691eb57f6b4b2bb4260b3a87b1a67b152ab11b4b0e1faefaaaec97ae3c9add89ab729ab09faad13aa946a9d35a7f61a6982a6539a5ff9a51e7a3d3fa272ca269da1d12a190b9f888
|9,0=>0xfbfeef6695f341befff4ed4d8eb8d7e90aedff84db623c4d60c1783bbeeabbdf8bb876b897ab53f9b22ceb1df8a7f61a11b19e30a9b28b9a4d694d6293b0b90b0f90a268a8bf89fc08760c8722d839497ad9d796ec6d9d36cf5f6cdc3661c264183620315f83e5d41a5646f53d2451dda513845033d4ce164b9364955946b4544edd428094065c3fbd23ec8d3d13b3a524397a5377e2324593227e2ea252c8862bf1c2b70429ca1299c82866126aab221ca21bbb21ba2210d11ff591bacf18d5f16ed71529512bd70df8e0cdde06f1805ead04c22
|10,0=>0xda982cacf59ebd8806367dfda704995dbf34f9c249772460e01023701464
|11,0=>0x3ce8d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff0000ffff0000fff00000fff000000000000000000000000000000000ffff0000ffff0000fff00000fff00000ffff0000ffff0000fff00000fff0ffff0000ffff0000ff000000ff000000ffff0000ffff0000ff000000ff00ffff0000ffff0000ffff0000ffff00000000000000000000000000000000ffff0000ffff0000fff00000fff00000ff000000ff000000ff000000ff00ff000000ff000000ff0f0000ff0f0000ffff0000ffff0000ff000000ff00ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000ccccaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaaffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000ffff0000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff00f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0ffff0000ffff0000ffaa0000ffaa0000aaaa0000aaaa0000aaaa0000aaaa333300003333000033330000330000003333000033330000333300003300ffff0000ffff00000000000000000000ffff0000ffff0000000000000000
|0,1=>0xff00000000000000ff00000000000000ff0000ffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f000000000000000000000000000f0000000f0000ffff0000ffff00000000000000000000000000000000ffff0000ffff00000000000000000000ffff0000ff0000000000000000000000000000000000ffff0000ffff0000ff000000ff0033330000000000003333000000000000333300003333000033330000330000000000000000000f0f00000f0f000000ff000000ff0000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc333300003333000033330000333300003333000033330000000000000000ffff0000ffff0000ffcc0000ffcc0000cccc0000cccc0000cccc0000cccc00000000000000000000000000000000ffff0000ffff0000ffff0000ff0000000000ffff000000000000ffff000000000000ffff000000000000ff00ffff0000ffff0000ff000000ff0000000000000000000000000000000000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff00ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000
|0,2=>0xffff0000ffff0000ffff0000ff000000ffff000000000000ffff00000000000000000000000000ff00000000000000000000ffff000000ff0000ff0055550000555500005555000055550000555500005555000055550000550000ff000000ff000000ff000000ff000000ff000000ff00000000000000000000000000000000ffff0000ffff00000000000000000000ff000000ff00000000000000000000330000000000003333000033330000333300003300ffff0000ffff0000f0f00000f0f000000000000000000000000000000000ffff0000ffff0000f0f00000f0f00000ffff0000ffff0000f0f00000f0f0ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ff00ffff0000ffff0000fafa0000fafa0000aaaa0000aaaa0000aaaa0000aaaa000000000000000000ff000000ff0000ffff0000ffff0000ffff00000000000f0000000f0000000f0000000f0000ffff0000ffff0000ff000000ff0000ff000000ff000000ff000000ff000000ff000000ff000000ff00000000003300000033000000000000000000000033000000330000ff000000ff00ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff000f0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000
|0,3=>0x333300003333000033000000330000000000000000000000000000ff0000ffff0000ffff0000ff000000ff00000000000000000000ff000000ff0000ffff0000ffff0000ffff0000ff00ffff0000ffff0000ffff0000ff0000000000000000000000000000000000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000ccccffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000000000000000cccc0000cccc0000cccc0000cccc0000ffff0000ffff0000ffcc0000ffccffff0000ffff0000ffff0000ffff00003333000033330000330000003300ffff0000ffff0000fffa0000fffa0000aaaa0000aaaa0000aaaa0000aaaafff00000fff00000fff00000fff00000fff00000fff00000fff00000fff0ffff0000ffff0000fff00000fff00000ffff0000ffff0000000000000000ffff0000ffff0000fff00000fff00000f0f00000f0f00000f0f00000f0f0ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc333300003333000033330000333300003300000033000000330000003300
|0,4=>0x333300003333000033000000330000003333000033330000330000003300333300003333000033330000333300000000000000000000000000000000cccc0000cccc0000cc000000cc000000ffff0000ffff0000ff000000ff00ffff0000ffff0000cccc0000cccc0000ff000000ff000000cc000000cc0000000000000000000000000000000000ffff0000ffff0000ffcc0000ffcc333300003333000033330000333300003333000033330000330000003300000000000000000000ff000000000000ffff0000ffff0000ffff0000ff003333000033330000333300003333000033330000333300003333000033000f0f00000f0f00000f0000000f0000000f0f00000f0f00000f0000000f00ffff00000f0f0000ffff00000f000000ffff00000f0f0000ffff00000f000000000000000000000000000000000000ff000000ff000000ff00000000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff000000000000000000000000ffff0000ffff000000ff000000ff0000ffff0000ff0000000000ffff000000000000ff00000000000000ffff000000000000ff00f0f00000ffff0000f0f00000fff00000f0f00000ffff0000f0f00000fff0ffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc
|0,5=>0xfff00000fff00000fff00000fff00000fff00000fff0000000000000000000000000ffff000000000000ff0000000000000000000000000000000000cccc0000ffff0000cccc0000ffcc0000cccc0000cccc0000cccc0000ccccffff000000000000ffff000000000000ffff0000ffff0000ffff0000ff000f0f00000f0f00000f0000000f0000000000000000000000000000000000ffff00000f0f0000ffff00000f000000ffff000000000000ffff00000000ffff0000ffff0000ffff0000ffff000000000000ffff000000000000ff00ffff0000ffff0000ffff0000ffff0000fff00000fff00000fff00000fff00000000000000000ffff0000ffff00000000000000000000fff00000fff0000000000000000000ff000000ff0000ff000000ff000000ff000000ff00ffff000000000000ffff000000ff00000000000000000000000000000000ffff0000ffff0000ffff000000ff0000ffff0000ffff0000000000000000ffff0000ffff0000ffff0000ffff0000ffcc0000ffcc0000ffcc0000ffccffff0000ffff0000ffcc0000ffcc0000ffff0000ffff0000ffcc0000ffcc000000000000000033330000333300000000000000000000330000003300ffff0000ffff00003333000033330000ffff0000ffff0000330000003300
|0,6=>0xff00000000000000000000000000000000000000000000000000ff000000ff0000000000000000000000ff00000000ffff000000000000ffff000000ff0000ffff000000000000ffff00000000000000000000000000ff000000ff000000000000000000000000000000000f0f0000000000000f0f0000000f00000f0f0000000000000f0f0000000000000000ffff000000000000ffff000000000000ff00000000000000ff000000000000000000ffff0000ffff00000000000000000000000000000000ffff0000ffff00000000000000000000ffff0000ff000000ffff0000ff00aaaa0000ffff0000aaaa0000ffaa0000aaaa0000aaaa0000aaaa0000aaaa0f0f0000000000000f0f00000f0f00000f0f0000000000000f0f00000f00ffff000000000000ffff0000ffff0000ffff000000000000ffff0000ff000000000000000000000f0000000f00000000000000000000000000000000ff000000ff000000ff0f0000ff0f0000ff000000ff000000ff000000ff000000000000000000000000000000000000000000ffff000000000000ff00f0f00000f0f00000f0f00000f0f00000f0f00000ffff0000f0f00000fff0ff000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ff00
|0,7=>0xffff0000ffff00000000000000ff0000ffff0000ffff0000000000000000ffff000000ff0000ffff000000ff0000ffff000000ff0000ffff00000000ffff0000ffff0000ffff0000ffff000000ff000000ff000000ff00000000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff000000ff00000000000000000000000000000000000000000000000000ffff0000ff00ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff00ffff0000ffff0000ffff0000ffff00000000000000000000ffff0000ff000000000000000000000000000000000000ff000000ff000000cc000000ccffff0000ffff0000ffff0000ffff000000ff000000ff000000cc000000ccffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffcc0000ffccffff0000ffff0000f0f00000f0f00000ff000000ff000000f0000000f000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000fff00000fff000ff000000ff000000ff000000ff000000ff000000ff000000f0000000f0000000000000000000ff000000ff0000000000000000000000f0000000f0ffff0000ffff0000ffff0000ffff0000f0f00000f0f00000f0f00000f0f0ff000000ff000000ffff0000ffff0000ff000000ff000000fff00000fff0
|0,8=>0xf0f00000ffff0000f0f00000fff00000f0f00000f0f00000f0f00000f0f0ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff000000ff00ffff0000ffff00000000000000000000ff000000ff000000ff000000ff00ff330000ff330000ff330000ff330000ff330000ff330000ff000000ff00cccc0000cccc0000cccc0000cccc0000ffff0000ffff0000ff000000ff0000000000000000000000000000000000ff000000ffff0000ff000000ff00afaf0000afaf0000afaa0000afaa0000aaaa0000aaaa0000aaaa0000aaaa0f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000003300000033000000330000003300000033000000330000000000000000ccff0000ccff0000ccff0000ccff0000ccff0000ccff0000cccc0000cccc0f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f00ff000000ff000000ff0f0000ff0f0000ff000000ff000000000000000000ff000000ff000000ff000000ff000000ffff0000ffff0000ffcc0000ffcc00000000ffff000000000000ffff000000000000ffff000000000000000000000000ffff000000ff0000ffff000000000000ffff000000000000ff000f0f0000000f00000f0f0000000f00000f0f0000000f00000f0f00000000
|0,9=>0xff0f0000ff0f00000000000000000000ff000000ff00ffff0000ffff0000ffff000000000000ff000000ff000000ff000000000000000000000000000f0f00000f0f0000ffff0000ffff0000000000000000ff000000ff000000ffff0000ffff0000ff000000ff000000ffff0000ff00000000000000000000ff000000ff0000ffff0000ffff0000ff000000ff00000000000000000000000000000000000f0f00000f0f00000f0000000f00ffff000000000000ffff000000000000ffff00000f0f0000ffff00000f0000000000ffff000000000000ffff00000000000000000000000000000000ffff0000ff000000ffff0000ff000000ffff0000ff000000000000000000cfcf0000cfcf0000cfcc0000cfcc0000cccc0000cccc0000cccc0000cccc0f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f0f00000f00f0ff0000f0ff0000f0ff0000f0ff0000f0ff0000f0ff0000f0f00000f0f0ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000f0f00000f0f000000000000000000000000000000000ffff0000ffff0000cccc0000ccccffff0000ffff00000000000000000000ffff0000ffff0000ffff0000ff0000000000ffff000000000000ffff0000ffff0000ffff0000ff000000ff00
|0,10=>0xf0000000f00000f0f00000f0f00000f0f00000f0f0cccc0000cccc0000cccc0000ccff0000cccc0000cccc0000cccc0000ccccff330000ff330000ff330000ff330000ff000000ff000000ff000000ff00ffff0000ffff0000ff0f0000ff0f0000ffff0000ffff0000ff000000ff00ff000000ff000000ff000000ffff0000000000000000000000000000000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000ffcc0000ffcc0000ffcc0000ffff0000cccc0000cccc0000cccc0000ccccffff0000ffff0000ff000000ff000000ffff000000000000ff0000000000f0f00000f0f00000f0ff0000f0ff00000000000000000000000000000000ffff0000ffff0000f0ff0000f0ff0000ffff0000ffff0000000000000000ff000000ffff0000ff000000ffff0000ff000000ff000000ff000000ff0000000000000000000000000000000000ffff0000ffff0000ffff0000000000000000000000000000000000000000ff330000ff330000ff000000ff000000000000000000000000000000000000ff000000ff000000f0000000f0ffff0000ffff0000ffff0000ffff000000ff000000ff000000f0000000f0ff0f0000ff0f0000ff0f0000ff0f0000ff0f0000ff0f0000ff000000ff00
|0,11=>0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000ff000000ff000000ffff0000ffff0000ff000000ff000000ff000000ff0000000000000000000f0f00000f0f00000000000000000000000000000000fffc0000fffc0000fffc0000fffc0000cccc0000cccc0000cccc0000cccc0f0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f000000000000000000ffff0000ffff00000000000000000000ffff0000000000ff000000ff000000ff000000ff00000000000000000000000000000000ffff0000ffff0000ffff000000ff0000ffff0000ffff0000ffff00000000ffff0000ffff000000ff000000ff0000ffff0000ffff000000000000000000000000000000000000000000000000ffcc0000ffcc0000ffcc0000ffcccccc0000cccc0000ffff0000ffff0000cccc0000cccc0000ffcc0000ffccf0f00000f0f00000ffff0000ffff0000f0f00000f0f00000fff00000fff0fff00000fff00000fff00000fff000000000000000000000000000000000ffff0000ffff0000ff330000ff330000ffff0000ffff0000ff000000ff00ffff0000ffff000000000000ffff0000ffff0000ffff000000000000000000ff000000ff00000000000000ff000000ff000000ff0000000000000000
|0,12=>0xff000000ff000000f0000000f0000000ff000000ff000000f0000000f0ffff0000ffff00003333000033330000ffff0000ffff00000000000000000000000000000000fff00000fff000000000000000000000fff00000fff000000000000000000000000000000000ffff0000ff000000ffff0000ff00000f0000000f00000000000000000000ffff0000ffff0000000000000000ffff0000ffff0000ffff00000000000000000000000000000000000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f00000000000000000000cc000000cc0000cccc0000cccc0000cccc0000ccccf0f00000f0f00000f0000000f0000000ffff0000ffff0000ff000000ff00ffff000000ff0000ffff000000ff0000ffff000000000000ffff000000000f0f0000000f00000f0f0000000f00000f0f0000000000000f0f000000000000000000000000ffff0000ffff00000000000000000000f0f00000f0f0ffff0000ffff000000000000ffff0000ffff0000ffff000000000000ff00000000000000000000000000000000000000000000000000fff00000fff0000000000000000000ff000000000000ffff000000000000ffff00000000000000000000000000000000ffff0000000000000000000000000000ff00
|0,13=>0xff000000ff0000000f0000000f000000ff000000ff0000000000000000000000000000000000000000000000000000000000000000ffcc0000ffcccccc0000ccff0000cccc0000ccff0000cccc0000cccc0000cccc0000ccccffff0000ffff0000ffff0000ffff00000f0f00000f0f00000f0000000f00ffff0000fff00000ffff0000fff00000ffff000000000000ffff0000000000ff000000ff000000cc000000cc000000ff000000ff000000cc000000cc00ff000000ff000000ff000000ff000000ff000000ff000000cc000000ccfffa0000fffa0000fffa0000fffa0000aaaa0000aaaa0000aaaa0000aaaaf0f00000f0f00000f0ff0000f0ff0000f0f00000f0f00000f0f00000f0f0cccc0000ffff0000cccc0000ffff0000cccc0000cccc0000cccc0000ccccff0f0000ff0f0000ff0f0000ff0f0000ff000000ff000000ff000000ff00ff000000ff000000ff000000ff000000ffff0000ffff0000ffff0000ff0000000000ff00000000000000ffff000000000000ff00000000000000ff00ffff0000ff0000000000000000000000ffff0000ff000000ffff0000ff00000f0000000f0000000f0000000f0000000f0000000f00000000000000000000000000ff00000000000000ff00000000000000000000000000000000
|0,14=>0xf0ff0000f0ff0000f0ff0000f0ff0000f0f00000f0f00000f0f00000f0f000ff000000ff000000ff000000ff000000ff00000000000000ff00000000000f0000000f0000000f0000000f0000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0000f0f00000f0f00000000000000000ffcc0000ffcc00000000000000000000ffcc0000ffccffff0000ffff0000ff000000ff000000f0f00000f0f00000f0000000f000ffff000000000000ffff0000ffff0000ffff000000000000ffff00000000ffff000000000000ff00000000000000ffff0000ffff0000ff000000ff00ffff0000ffff00000000000000000000ffff0000ffff0000ffcc0000ffcc0000000000000000ffff0000ff0000000000000000000000ffff0000ff00ffff0000ffff00000000000000ff000000000000000000000000000000000000000000000000ff330000ff3300000000000000000000ff000000ff00f0f00000f0f00000f0f00000f0f00000ffff0000ffff0000fff00000fff0ffff000033330000ffff000033330000ffff000000000000ffff00000000ffff0000ff000000ffff0000ffff0000ffff0000ff000000ffff0000ff00ffff0000ffff00000f0f00000f0f0000ffff0000ffff0000000000000000
|0,15=>0xffff0000ff000000ffff0000ff0000000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x308070c110509031507062105040308020011050903080206050d04080720061f09030807000c050d0408071d060509030807061c1b051a090308070509030719000c05090308070618050d040317071605090307010612111009031507001409030807130011100903080200050b03080706050a0903080706050403020100
|1=>0x50d0339073805370903073600050403083500052b030807230c052704030807330509320701000c05310d030730062f09030701000c090308072e000c050903082d000c051a2b0308072c050d04030701061405092b030807050903072a000c0527090308260625050903080706052404030807000308072313000c050d22
|2=>0x7062c050903394c0700054b0903074a000509030201000c491009030807000509030748000c460d04030807064305090308070c0509031507130005090308021300050d044108070605040b03080706050d040340073f053e09030807003d050903080700050d040308073b3a0509031507003a050903080200111009320807
|3=>0x27090308070c050e040308070605570d040308070c050903074806000c3a051a090308070010051a0903080700050d045603080700050d09030807540c05530d030730000c050b03080706055227090339070005520d0403390700050903400807500c05274d0903080700050d040308074f06050d4d04030807000504280308
|4=>0x48000c0509035d07000c05310d033907060509030719000c052709410807000c050d04410807000c3a05090308070012050d1a0403080706050d0403080730065a09030807000c05040b030807000c05370903073f000c055209030736000c055309030750000c050941080759000c050903080713000c050d030807380c0557
|5=>0x308073f0600054b310903390700050d63030807000c05270903082d000c05040903082d000c1b0509030807060c050d090308073f060509610807000c051a030807002c050d09030701060c4410092b0308070c1e6009030807000c05270d0903403907054b0903170807000504030807005f05310d1a0340070c050d090307
|6=>0x8070005040308074706051a09030807006f051a090308076e00050903400736000c051a09080720000c050908076b000c462709030807000c050308076a002c0c460d04030807000c68050409030807000509030867000c0509030807060f050409080766000c3a05092b0308070c10050932080700050d09034007360c0509
|7=>0x9030807003c050d7c030807000c050d090315070605520d0403080706790509030807060005310d0317070c0504090308077700054b0903080706001105030807002c0c1b050d090308070c11050403080700120504090375080706050d0903080206050d03080773000c054b0d090308070605700d030807000c21051a0903
|8=>0x5310903073f000c05310d03073f000c0509080780002c0c050d0403080716050d090308077f0c140509030807060005090339074a0600650509080766000c7a7e030807002c0c2144092b0308070c14050d0903080706051a09030807130005764b0903080700052b0308072c0c050d04031740080705090308077d000c100d
|9=>0xc0509080780000c050d1a030807062c050903080706840c050e0d04030807060527090339070016050b090308070605524b0903390700140509030807000c058304030807000c10050d040308070605580d040308070605092b080720000c051a090308070082050903080781000c490509030807000c0509030807130012
|10=>0x807000c058a09030807000c0509030889000c0553310d0340070c050d0403080706880504090317070016050d09030719000c050b030807000c051a09030701000c050d09034007160c05530d040308070605090317074a000c05092b030807130c050d09030807063c053109038607000c052709080785000c050409080785
|11=>0x82d000c0531270d0340070c050d0908076b000c058c09034007000c053709030807060005278b090308070021050d0403080706058b04090308070010050d0932080700110903080759000c05310d031707060c050d040340074f0c05370d09030807060509030701000c12050d03080723060c05040908071d0600050d0961
|12=>0xd2b0308072c0c05092b030807420c5c0509030719000c6d051a0903080700052709080720000c050d04080720000c05760903074a000c0504030802005c1009030807000c106009030807000c05271a092b0308072105098d0308070005270908071d000c0504090807200600050d04030807470605520903073f000c050903
|13=>0xc05092b030807450c111009030807001210051a0908072000055709030807060c0509030807363f000527090308070629051a09030719000c050d040308070682050d1a0403400807110903080713000c110509031507000c050903082606057609030807000c11101a0903080700058e09030807000c110509030802000c05
|14=>0x9030807000c5c101a09030807001b05040903080706050494030807060010050903080200050d040308074206050403080773060005310d0392070c05310903074a000c050d040317080705310d03074a000c910509030807060c0509080785000c05901a0903080700052709030748000c05098f0807000c1e090308071300
|15=>0x7060509030807069d9c050d030807000c05279b09030807002105030807002c0c9909030807000c051a09030807000c2105040308070012050d0903082d000c0527090308073f00058e1a0903080700052709030701000c1b0527090308070c1e0903080700970c0509039607000c1005090315070005092b080795000c5c05
|16=>0x2709030807000527090339074a0005a30903080706000509030701000c6c050d0903390706162f09030807000c05520903074a000c05270903150700050409030807a100116d09030807000c0509710807000f05270903080200054b27090308070005099f030807060c10099e030807000c0531090307300600050d04710308
|17=>0xc050903a907000c052709030807003c10050d09030802000509030748000c050d09080785000c051a04030807002c058c0903390706001109a8030807000c050d04080795000c050d09030807a60c050903080762000c051aa50903080700050d1aa503080700a405092b0308070c050456030807000509320807000c1405
|18=>0x3ae07000c112f09030807000c052709030807000c1009030807003c059b0903080700050903080759000c05272b0308072c0c053727090308070011050d0403080706050dad0308070605042b030807062c05ac09030807000c10050d0903150700140509030807006c3a0903080713000c100903080713000c3a0509030807
|19=>0x51a0903080700055309030730000c5c051a09030807000c05b20d09030807000c05270d09030807004e050903080700b00c050d09030807160c05765209030807000c050903390807002c050903080742000c6c050d09af0807000c050d09320807000c440504092b0308070c110509320807000c2f0d09030807000c050d09
|20=>0x9030807b7000c650509030807000c3a050903080706000c21050409030807006905b609034007000c05b509030807000c05270d09033908070005040903170807060005b4092b030807000c050d0903080762000c10050d09030807060c050903080713000c05270993030807000c05310d1a030807000c050971080700b310
|21=>0x50903bc07000c050409030807bb06007aba09030807000c05760903400807000c05270903170807000c050e09080747000c05090308075030000c050d0903080736000c058c09030807000c0509080795000c1005090308070012050903080706005f0c05310903174007000c050e0d09030807060c050903080778000cb805
|22=>0xc052709030807bb000cc10d09030807000c05271a0903080700051a040903080700050d1a0403080700050409030807c0000c05ac0d09030807000c0504090308076a0600050dbe030807000c050903080700970c056309030807000c050d030807062c0c050d0903080706880c05040903403907003a050d09030807000c
|23=>0x3080747060c21050903080706000c050d040308076a000c050d09030701000c05090308073f000c05765309030807000c050994030807000c05c709030807000c050903080773000c460903080747000c05090807c5000c05520903403907000c057009030807000c0509030807c36a000c05ad09030807060005c209030807
|24=>0x4092b03080706050dad030807000c057c09030807000c05521a09030807000c0509030807364f000c050d0903080759000c1e050908071d06000c052709030807c9000c050409030807c9000c1b0509030807000c050d030807002c0c0527090308070012050d040308070012050903c807000c0527090308076a000c050d09
|25=>0x100903080706000c050d090308076e000c0534040308070600050971030807002c0c05270d09030807000c050d0903080706160c0509030802000c0552310903074f000c054b09030807000c0509030807cb0c05762709030807000c05760409030807000c11052709030807000c11050d04030807000c05090308077d000c05
|26=>0x1a0903080700980509710807cf000c0527092b0308070c055309034007000c05b209030807ce000c050d09030807064e05b40409030807000ca4050409030807000c050409030807a2000c05cd04030807000c0527090308074a000c0504090308074a000c050d09030807000c6f1e0504090308070600cc4409030807000c7a
|27=>0x30807000c10090308076a000c100903080700ca1e052709030807000c055331090308070600050993030807002c0c050903080700d10c050d090339080706050903080745000c0509030807000c5e051a09030807006c053409c40807000c05090308077f000c0509031507000c0509030807a1000c05090308071306000c05
|28=>0x80700380c050903080742000c5505570409030807000c111009030807000c0553310d030807000c050d0903080713000c05310903080700870cd20509030807000c050932030807000c050941080742000c10050d1a09030807004405092b0308070c058c0903080706000c10051a09030807000c140509030807000c6d0509
|29=>0x4030807000c050903080772000c05271a090308070600d40509030807000c050409030807300600050b030807000c0509030807d3000c05090308070600970c0527090308074f000c050d040308074f000c10050d090308070012110509030807000c6c050d04034008070c7e0509030807002c0c05a009030807000c050903
|30=>0x7000c05270903080730000c052704030807002c0c0509030807000c5505090308d8000c0509030807000c3c050d0903080742060c0509d7030807000c0509a8030807000c050d09031708070c050d0903d607000c0509410807000c1009030807aa000c05acd509030807000c050903400700160c0531270d030807000c050e
|31=>0x409030807000c0509033907da000c050d090308073f000c4609030807000c11050d09030701000c0509030807c0000c0509030807d9000c0504098d030807001005092b030807000c05310d033907000c0509030807061221090308076a000c05271a09030807000c051a0409030807000c050e09710807000c050d1a040308
|32=>0x7002c0c057609030807000c050903dd07000c058e09030807000c050d09030802000c054b0d09030807000c0509030807dc000c050d0971030807060c0509030807c9000c050403080747000c05525309030807000c050409080720000cdb09030807000c053709030807000c050d0903c807000c05742709030807000c0574
|33=>0x6000c0504090308070016e20d09030807000c050d0993030807060ce10509030807000c7b050903080706000c050903080700df0c05090308074a000c050d09031507000c05de0903080706000c05522709030807000c05270409030807004e050d1a09030807009805270d092b0308070c05520d04030807000c1e05090308
|34=>0x52709030807000c10052709030807000c7e050903080706000c05270928030807060c11100d09030807000c050d0903170807060c055209033907000c100504090308070600055804090308070600054d09030807000c2f0509030807000c14050d09030807000c6d050d09030807000c05270409033908070005a009030807
|35=>0x110903080742000c050d09030807000c3c050d09d7030807000c5c0509030807000c050d09a8030807000c050d09410807000c050da5030807000c050e2709030807000c054b3109030807000c050d0903080772000c056009030807000c10050d09080720000c050b09030807000c0509030807000ca705092b030807004e3a
|36=>0x7c3000c05310d0340070c460d09030807000c21440409030807000c9c0509030807000c051a09030807000c050d04030807060504030807002c0c05090308076a06000c05310903170706000c0509e4030807000c05e309030807000c05090308072306000c050e0d09710807000c05090308079a000c050d09030807000c55
|37=>0x807000c64050d09030807dc000c050d09030807c9000c05270903080747000c050dd5030807000c7a1e09030807000c057409030807000c05e709030807000c21050d04030807000c051a0971030807000c050903080777000c05370d09030807000c05310903074f000c05310d03074f000c0509030807000ce50504090308
|38=>0x62905b209030807000c052709030807004e05270903080713000c05090339070600160509af0807000c0509320807000c050d090308074a000c050903750807000c05524b09030807000c7ae909030807000c05760d09030807000c2f09030807000c05b60d030807000c05e809030807000c058e0d09030807000c050d0903
|39=>0x807000c05371a09030807000c0504090317080700050d09030807000ca7058ea509030807000c05520903074f000c050903080736000c050903080751000c050409080795000c05520d09033907000c0527090339080700050d4d09030807000c050903080762000c2f050d09030807000c050928030807062c0c0509030807
|40=>0x2709030807000c05740d09030807000c050409710308070600110509030807000c12050903ea0807000c050903080759000c0509030701000c05270903080742000c11051a09030807000c050d04030807060cc109030807000c05ac09030807000c0509030807000c5b05090308075942000c5c050d09030807000c3a050903
|41=>0x880c10050d09030807000c050903d607000c0509030807000c29050903080700820c0509030807000c6c10050903080706000c05eb09030807000c050903080700160c05520d09030807000c7a1009030807000c05270971030807000c2f0d09030807000c050de809030807000c050d09080720000c05090308076e000c05
|42=>0x807000c0509030807000ced05ad09030807000c0509030807002c0c050903080742000c0504090308076a000c7a4409030807000c05270903080706000c05040903080706000c0509030807000cd005523109030807000c440509030807000cb90509ec030807000c05be09030807000c050e0d09030807000c050903080706
|43=>0x504090308070069050d09030807000c98050993030807000c05533109030807000c053409710807000c0509ef030807000c0509030807ee000c0509033908070600053404030807000ce209030807000ccc0509030807000c050903080706004e050d0903080747000c05090308070600160c050903c40807000c05270d0903
|44=>0xc0509030807aa000c050d0971030807000c05099303080706000c110509030807000c05097103080706000c050d0903080742000c050d09030807060c0509030807bb000c7a050903080706000c053109033907000c050903080706002c0c0509030807000cf0050903170807000c100509080720000c050d09030807000c6c
|45=>0x807000c0509080720000c05d509030807000c0509030807000c1221050409030807000c051a09030807000c05040928030807000c05310d030807000c05a509030807000c05090308074f000c05040903400807000ce90509030807000c050d0903390807000c05090317080706000c050d09030807000c4e1e050903080700
|46=>0x9030807000c98440509030807000c050903080747000c052709030807000c050d09030807000c12053109034007000c053409280807000c0504090308070600050d1a09030807000c050e09030807000c050d090308074f000c055209030807000c050d09030807000cbf11050d09030807000c0509030807cf000c05b60903
|47=>0x509030807000c100509030807000c053409030807000c053109030807000c0509030807000cbf050d09030807000c050903080706000c0509030807000cb9050903390807000c0509030807000c4e050971030807000c05
|_=>0
def sO:Nat→Nat→Nat
|5,0=>6
|6,0=>0x16f70b438585c2b4e15370a638515c27ce1377098384a5c244e11b708a38435c20ce0ff707cb03c9c1d8c0e5706f3835dc1a0e0c97061382edc168e0ad70533827dc130e09170453820dc0f8e07570373819dc0c0e05970293812dc088e03d701b380bdc050e021700d3804dc01ac0067
|7,0=>0x1af40d5a069ee347819fc0cde065f03287190b8c660623030a718140bea05e502ea817140b6a05a502ca8161b8af1c56902ac815240a720529028d7142c09f604ece26f71343898204b102508124409020472e2318114c0886043302118104c0809c3f501f370f5c078e03b701d380e5c070e037701b560d6c0696033b019580c6c061602fb01767
|7,1=>0x2aac15360a8ce53e829b414ba0a4d051e828b4143a0a0d04fe827bb93be09cf04df826bc1341c99104c0825c412c2095104a0824c4124209110480823c411c208d10461722cc114608930441821cc10c608530421820cc1049c815040281fd40fca07d6e3e381edc0f51c79903c481de40ed2075903a481ceb8e56071b038581bec0dd9c6dd03668
|7,2=>0x3a5c1d11ce7907357396c1c960e3ce716838741c1dcdff06f78377c1b9e0dbf06d78367c1b1e0d7f06b78357c1a9e0d42c6998348c1a260d0306798338c19a60cc306598328c19260c86c63b8319c18ae0c47061b8309c182e0c0705fc72fa417b20bc905dc82ea417320b8905bc82da416b20b49059c82ca416320b09057c82ba415b5cacb055d8
|7,3=>0x49ec24d9d25d0926848f4245a121d0906847f423ddd1df08e784703a36211a108c88460422e2116108a88450422621121088974413a1ea10e5086a84314216a10a6e84b84223a0f21069082d74133a07a102d080e840341ffa0feee7ef83f3c1f7e0fb0e7d083e441f020f7107b083d441e820f31079173c539e0a0ef5077283b541d8a0eb6e7538
|7,4=>0x1317098384bdc25ce12d7096474aeba556129b09458
|8,0=>0x5d43ae7e572f0b8e95c342dfa16eb2b6d85b2c2d7616ab0b4c95a1cacea56650b2a859142c6a16232b0985804abe5d5e12ae8856fcab5a559d0ac5955e4aad2155aeaa5854e4aa4e55152a82853cca9c614d12a5f952bc293e148d2a3d951a4a8ae54452a1a8508ca8225402e9f984f8c27a253bf29d694e74271a137b29b584d64a692133909939
|8,1=>0x6e0c36e61b630da986d0c36661b24ed8a86c0cb5e61ae30d6986b0c35625aa10d47969f4b4d65a5b0d24968dcb44a5a132d01867c4b3be59cf0cde966acb332598aecbc965a432b5d9492c9b96494b22659030c798638c31a618c12c5796274b11658792c339615c308e18370c1386063b00e57f52bf195f44af8217b10bcf95e3c2efe176f0baf8
|8,2=>0x7ec4bf421f910fc087dbcbebe1f50efa087cbcbe3a5f0d0f7d97ba4bdae5ec70f5c77aa43d2e5e870f3b8799c3cae1e48ef1c8789cbc2e1e052efa877943ba65dc30ed89768bbb261d812eb797574ba965d392e948745cba0e1cf70e729734cb9861cb12e4f97234b8fa1c6d0e2e8712cb8761c292e0b9701c37ee1be70dec76f1cb76a5ba32dc98
|8,3=>0x8fc447be63cd31de88eacc736238b11bc98d9cc6aa6345119998c8c46262303117898b7cc59a62bb315498a5cc50e227531319894c44862231310f98834c3f661eb10ed88724c37221a730cb8861c42ee216530a998504c25e611d3085983e4c1d220daf065882ec415260991043981dc40ce20553022880dbc04e2017100297fccbfc61fd12fe17
|8,4=>0xa06cd01267f913f399f5c4f8a67b333d189e4c4f06277313b099d444e7e672f138e99c2ccdf9e6ed136e89b2ccd7626acf34f79a34ccfa266b332d89924cc75e62b130d89824cbee65e532e999704cb6225a112c8896044ade655d32a6894ecca56251b1285893e4c9d5e4db1264992e44952249af245891e4c8ce64571223890d4c846641312009
|8,5=>0x2945349a8a48cd226290314798a384d19e68bd34568a274511de87d34359a16c5099e83d14168
|9,0=>0xb5dc5ace2d5536a28b4ccda426d0f367f8b3bc59ba6ccb365d8b2a4d92e6c87163b8b194d8aa2c4336198b08c58262c0135f88af7cd79e2bbd35d68ae74571a2b7d15b68ad7bd69e2b3f15969ac6cd6162af935748ab6455922ab915539aa5c550a6a7335318a944d47e6a2f150f8a834d3f669e934ed7a72c537629ab14cc9a62452f2296734ab8
|9,1=>0x17698bb0c5d626ea117488ba045cde6e5f17269b8f45c566e1937048b7e45bd5eddb16e58b6e4db522d9736c38
|10,0=>0xbe4c5f062f7317b18bd4c5e862f3317918bc4c5e062ef317718
|11,0=>0x17d17
|_,_=>0
def wAt:=mkWire dB 241 240 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x50d41435050c40c490d0c02401080c418c4090842401000c41c3d0e0c0340d000942431090c4d0300309424311108c1435000c41ca5000c4a0300300400310d0c02401090c41c490d0c000250712434300900400311003c1431090c40031090c4780f0506400310d0c04423050d41431081243430050d42401050d4143107124343009004243d0e0c0340d090040031
|1=>0x9004344b0d0c024010412c3430090c40155420c814360900424a5000c4a030030043431090040025005141103090c420010d0c4353b0900400310d08c0025090c4353b080c8000d0609c203104400243108004151d090c4340f000c4ad154404c0012050041c490527834300d0c40031034241436090c400253a12c44310d0c01435003c44430050d41c49110c43430
|2=>0x3094200108094343300094e823052743431085e50830050d82401080c424210900400315c08c14690d0cc2401034241436090c444310d0c014350d0cc2401090c40031000c42012000942431055b51c300d03c24010e040340d083f434e7090042031063102421090040031005880c11000442431000c4340d000942431005880c11090c4e823052742419100d43433
|3=>0x90c485a7050440032075e50830050d824010e0c0340d0900400316503c14ad000499401000482431050c40c490d0c024014a0cc9c230906400313100420250964438320d03400253a07c149d000448403050440031090c434e70900420310362440360900414310609c9c330906400311108c1435000c40012090c43431090054833400c50025080042431063400031
|4=>0x9424317b0c5e81b000c41425000950031080042025780c41102090c42001760cc9c210906400312709c343100094e8030527434310900414350d0c00025090c400310428024310712434300900400317409c9c0d0d0c40025520cc342109005c8250d7180025030c49c33000442431000c4340f000942431100dc14310d0cdb40f056c4343209004151d0d03c0025
|5=>0xc40c110009424311112c343009004149e0d0c034315239c20313100434e7000942031080682431090040031006f44432050d424013a0cc149d090640031090640031052b40012090c4241a000c40012090c44433050d42401520cd48313100420252709c0012000442431400c40021090c44430050d41431093c44430050d40025081243430090040031000c43421
|6=>0x50c41d6d470c0340f09004c431000942025080040025030682431000c57023051a434330e040340d000942431400c40031080440025090c418212708c2419000c40031110c024010887418c7000c420253a03c149d00045f80f052c4241a000c43433000c4340d090c42401000c40031092940031280c00c01310042025780941102090c42001050c42401090c40031
|7=>0xd0cc2401090c4400f000941431084a49c23090640031090c41c490d0c00025050c414690d0cc24011003c1431090c40031090c4340f09004003109004e81f7a064003108004343100095b40f056c43432091650031000941411000c42431050c40c490d0c024010608400310d08c24310d0cc44230d0c01435090047827050640031090c4780f050640031036244036
|8=>0x5094e80f7a0640031050940d79420c01436090041419052782419000c51013000481401050c43430050d424010d0cc400f09005d003270342419000c4fc310d39c2401080c40031280c00c01090c4141a090040031080043433050d4149e0d0c42401081243430050d42401072940031280c00c010d0cc24010d6f44432090041c490d0c01435090049c030d0c41469
|9=>0xd0c00025090c4e81f0527434312739c34310900638330d98424012100c141100044243105065e81805094216d470c0340f0900420490d0c02401050c4344b0d0c024010d0cc24012100c1411090c4241a050c41c490d0c02401090c414360900400319309c0c19000c4202500095003308005d823520c4c401080950031000840025090c4343100095ec017a06c0031
|10=>0x9164201a000c44440050d42401050c49c230d0c434210900420490d0c03431090068831042882431030041435056c434320900438300d0342401030c41c490d0c034310900548330d0c43421090068003098840031440401401050c42431030c42401000c418a7000c4a03003005b825100dc0025050c49c4b0d0c034312709c0011090c416690d71c2401030c41411
|11=>0xd0c8149d052782419000c4149e0d0c42401050c5b435056c434320900422adaa0c9102705004143107124343009004e8237a064003105094e80f0527434312709c9c33000442431091640031100d01435050c424012103c1411090c4029d470c8340f09004409e0d0c4240100094104b0d0c00025090c40d6d470c0340f09004e833052742419000c43431090063033
|12=>0x90042032080c8343109006c427009841432080682401000c4c401080942031090680031050d83432090040c4b0d0c02401031243430090040012090c41401031243430050d42401111001435050c421bd110c814350d0c02401110c014350900414312712c34300d0c42401000c41435000942431000c425390009420320400c0031081243430090041431110cc1435
|13=>0x634000310309500310800420250d0342401000c41102090c4200100b942432052b40012090c4149d090640031050440032090c4c433080942001082b40012090c420310d0c42401080642431000c40012090c44036090041431050c42401000c4149e090640031030642419000c420250d0cc0025030c4d030030943433090041431080442012090c43433090043539
|14=>0xd0cc0025090c51012090c414010dbf42401030c81412000c42431096c4343200095e818000c4142509bd4a03203004241a090040031030682401000c424310800420310527434310900422cd340c00c25030480031090c44003050941431520c50025080642419000c40d1d0d03c24010804824314f0c434230900424590806800312103c4025050c43430090041431
|15=>0x900434300009424310812c34300900424310d03c2401000c41411000c42431050480025090c44423050d424010d39c2401080c4e425080c40cb10906800310dbfc2401030c8264e280c40c0105474340f09007180f05b942432080c500250800427117100c0c31050482431000c42539080c818d2000c40c25090c4144b0d0c024010d0cc3431090049c33000442431
|16=>0x1a0c4343309004201a090040031071243430090054823310042025520ccc4010809402cf340c00c25090640031270840011090c414350d0c42401050d40025090c6a8314409c14010400c2431000c4253900094203209ca51030050043433090043423090050831050d824011e03c1419000c42419000c49c0f0004424312100c4025050c49c270d0c400250d0c03431
|17=>0x81243430090073c312809c0c01052782419000c43433090041432030c4a027030040012000442431310c42025080040139080c82032090040031032b40012090c51033090c4140104288243103004d003090c40c250906400312708c0011090c44432050d42401050642431000c5e833050041425000c41425050c44037090041431030940031090c40c31090680031
|18=>0x900418c7000c5e9a7000c81425031243430090040d09050d82401050c43433090040012090c4140109164201a000c43433090044433440941401056c43432090041431050482431440c01401050c41419090640031310c4003108094241a000c40cb2090680031080c42401000c51013090c41401420c014360900434320d0cc240109035c403030c403417a0c81425
|19=>0x800420250d0c400250d0340025090c435c6090040c31270cc2419000c69025440cc1401000c42012090c424a5280c00c0105be825a5000c9e818000c414250900434230009424310d0c02401050c414350d0c82401000840025090c414b1090680031880940c1a000c418c4000c42025420c81436090040162030442431050d42401050c42401310c42025052783431
|20=>0x469c0032090c41431000482431090042025080c43430090040031056a41412090c49c330004424310d0342401030c43433000942431000442012090c49c27000442431420c81436090041ecd340c00c25110c11025050041436090040031036c43432090044034090041431080642401000c4240108984143203424143609005102705004143109bf40c321708d0031
|21=>0x31004202508d05e8320509436610900414320712434300900548330d0842401470c4340f090040c310900400312703c2419000c4340f000942431310c4c40108094400f090c4143105b34d0300309468210d0cc24010812c3430090042419000c49c0d0004424314009c2001080c434e709004203105474340f090044423050d4240144048243105004245e390042031
|22=>0xc424310d4ec2401080c814490d0c02401110cc14350900415b10d0c82401080c40011090c42621030680031080682431000c42401054e42032030642401000c416f90969400327a06c003105097802700bf40c322708c2419000c420490d0c024010631820250d0c43421090042032090c434330900414322700c343109004342100094243105064241a000c54831
|23=>0x90040db10d0c82401051a434330900440340900414310342414360900426610009414320d03434310900548333100420250d7182401030c426090506800311003c2401050c424a5280c00c01470c8340f090042032000482431052742419000c434310900414b1090680031030042419000c41435090041431080642401000c42031310042025050c42431000c40c11
|24=>0xd0cc24015208cc4010809420250d08c0025e60c9e80305095a80105048243109004200108094151d0d03c240105044243105006e8251000c14310d12c34300900424310900400310609c0031090c41412000c4243106084003108096b403094e420321a03434330900478270506400310d0342401030c435c7090040c31420c81436090041435050d82401110c01435
|25=>0xd0c02401031243430090049c230d0c424010428024310300548333100420250569400320509548310d0842401051243430090042401310cc20250d98c2401050c836610900414320e0c8340d470c4340f090049c0f0d0c424010d03c343109004240109bf40c320506400310509435c5090040c31b6004c4330809414110009424310d0cc2401da0c50027080046821
|26=>0x50d82401051a4343309005e819000c414250d0cc2401080642431000c51c320d03c2401a50042661050c948233100420254f0c434230900420ae0004824312103c1411090c420310d08424010d0c42401080c4353b090042032100d82401050c414490d0c0240103004241a000c40031280c00c010d4e42401080c82032090640031090640031080c4201a000c40c4b
|27=>0xd0c82401000c414313100c20250806800310d08424010509414310d0c424010512434300900436630900414321003c2401050c440370900414310d6c43432090049c0d0d0c42401030c42431000c43430050d424010d7102401030c50831050d824011108d1025050043431090043433090042401090c400310512c343009007540109bf40c32470c0340f090050831
|28=>0x310c42025030c40c2503b9424321009c1431000c42031090c40c25054e420327a0cc1425000c420320d03c24010806800317100c0c310d0c42401340c80c25094e42032090680031050d82401050482431050941401090640031090c400317a0c81425310042025090c81401280cc0c010969400320d0342401030680031090041431089841432280c00c01050680031
|29=>0x9bf40c320d0c024010504424310d0cc2401090c40c010900420250998414320d08c2401090c420010569400320900420310806400310900420321000414314409c1401090040c31030640031440941401000c40c31050d82401090040031030482431000c414250809420310906800317a0c014253900420311003c14310d0c82401000c82431090041432280c40c01
|30=>0x50c40c25080940c32090040031090c82031080c80c31050c814010d03c24010906400310d0c02401080042025030040c25090c400310d0cc2401340040c250d08c2401310042025090040c32050d424012809c0c01310cc20251003c1431
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x5740a68000027a04b4000012840000464086600001fa03a506aa0000182800005a6000000000000000000000002940000000012a000000000000000022303c806900b200000248000000000000000000007980a5000001540028000
|7,0=>0x81a000000003fd07e18f841e883c4c7718ea4000039907210e040000374c6ca0d631a4833906598c92000031c861a0bf417682e0c5a20b04158800005498a63144827904d2098212880000000000000002410462088410a6208c3f987c30f261d5000007140de41b8435206730c6818482f905b4
|7,1=>0x6c0cd620000356269d0d1a000034066710000199332a864c800018f431c26290c41000030886010be2000000000000bc997632e665c0c00016c42d085910b1115f32ba456c8ac180002a885410a69800029465190a1213e427484d9099212e4256649d091a1203238846108a9911421c642900001073
|7,2=>0x4a26935124a245448648fd11da000000008dd119a230345888a4d12a221443c600010d22182428884110620000414481cd01a201200007f8c00000003f487d90f921ee40000000000000003d487990f289e233be6770ced10000000075900001d2400007408e711cd13928718ce121bf300006ed0dba1b34
|7,3=>0x6188c21183100006048bfcd7da2f745e68bbd00002eb45ce8b90d7022de25b66b5d169a2d030000b3c40002cb458e8b0d16092bd4000000015ca2b545628ab5154a2a545428a7514d1a9730000a4d147a28b45106a14d40a00004fa89e8d3b9a74300009c11369a6944ca80001311a6024ba697052c22544
|7,4=>0x190231d36346c6080003144620800000000000
|8,0=>0x7b06f54de91bd0279a6f28de48bc637866f00dde9bba376e6ed0dd89bae37566ea0dd29ba2373e6e70dcc9b9637284e44dc71b8c27126e18dc19b8036fa6de8dbb9b7436e44dbcdb61b6936cc6d8cdb01b5d36b64d60daa9b52369e6d30da49b4636866d0499f1b3b36706cd4d999330365a6ca8d939b243
|8,1=>0x91e7230e449c8639067200e3e9c7a38ee71d0e389c6e38d671a4a331c6338c07174e2d1c5828aa7148e279c4c38927118e219c40387a70e8e1b9c34386270b8e161429384c708ce101c1d3834705ce0a941328207034e059408380a7008dff9bfc37f26fe05fa9bf237de6fb0df49be727c86f84def1bdb3
|8,2=>0xa8c750cea01d3d3a7474dce9a1d31300014b8e959d283a4a7488e8f9d1c3a327458e899d103a1a7428e839d043a0453fce7e1cf939ec73cce781ced39d4739ce721ce319c07374e6d1cd739a87344e671ccb39907314e611cbf397a52e8e5b9cb4396272b8e559ca9294c728ce501c9d3934725ce4a94923
|8,3=>0xc0477fcefe1df93bec77ccef81ded3bd4779cef21de13bbc776ceec1dd53ba65740ee69dca3b8e7710ee09dbe3b7676e0eda9db23b5e76b0ed49da63b467680ece9d9a3b2e7650ec9158f3b1a5628ec39d843b0275f8ebd9d783aea75c8eb79d6c3ad27598eb19d603aba7568eab9d552aa4753cea61d493
|8,4=>0xd7c7aecf5c1eb62d667ac0f569eaa3d4e7a90f509e9e3d367a60f4a9e923d1e7a30f449e863d085a04f3f1e7b3cf079d4f391e6f3cd879a4f331e633cc07978b2d9e583caa7948f279e4c3c927918f2216413c7c78ecf1c1e353c6478bcf161e293c4c788cf101e1d3c34785cf0a1e113c1c782cf041e053
|8,5=>0x37916ef3dd87ba4f731ee33dc07b74f6d1ed73da87b44f6796cd2d947b1cf621ec13
|9,0=>0xee45dc0bb7176c2ed45da0bb317642ec45d80baf175c2eb45d60bab17542ea45d40ba7174c2e945d20ba317442e845d00b9f173c2e745ce0b9b17342e645cc0b97172c2e545ca0b9317242e445c80b8f171c2e345c60b8b17142e245c40b87170c2e145c20b8317042e045c00b7f16fc2df45be0b7b16f42
|9,1=>0x79c2f345e60bcb17942f245e40bc7178c2f145e20bc317842f045e00bbf177c2ef45de0bbb17742
|10,0=>0xf523ea07d38fa61f4a3e907d18fa21f423e807cf8f9e1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x5ce000000b1c00000161000000245000000484000000900000001060000002010000003060000006000000008180000010200000020000000030800000060000000083000000104000000204000000400000000780000000e2000000110000000210000000410000000800000000800000000300000000400000000600000000800000000800000000
|1=>0x440a0000083c4000010610000020820000041000000081180000102200000204200000404400000801800001001800002002000004000000006a8c00000c5100000188200000240400000400800000800000000aa20000011440000022800000044000000082200000104000000200400000321000000640000000c0a00000180800000300000000480
|2=>0xc58e0000187dc000030c000000610000000c1ee000018208000025798000042f70000085e6000010b9c000020fb800004187000008306000010608000020800000040f70000081040000102000000200080000400000000756600000e08800001451000002822000005000000008f8c0000116380000229b0000045060000089cc00001121000002240
|3=>0x1c3ee0000387540000707180000c27b0000184e60000307dc000060c100000c082000018100000030000000054510000088a20000104e20000209080000404180000800000000f5e600001e79c00003979800006bf700000d5e600001a7cc000034f18000063f700000c7e6000018f9c000031f18000062ff00000c5f6000018bdc000031798000062e7
|4=>0x800040001000000001b0810000360d700006c0040000d07dc0001a0c00000341020000681040000d0000000190800000301020000601000000c0004000171fb80002e1d700005c1c60000a020c000130fb8000261d30000483ee000090400000120410000200010000400000000586000000a00000000ebf700001d5e6000038bcc0000717380000e273
|5=>0x2083ee000410208000814c18001022c70002041e600040820c000800610001000c0000200106000400200000800010001000000001483060002804040004b0fb800094187000128304000250600000460c18000861f700010c30000021824c000420fb800084187000108304000210604000400800000800000000885ce000108000000201000000400c2
|6=>0x300206000600000000a0161000112083000220006000440004000874f180010e2f300021c5ce0004383dc0008704380010c0000002143060004281080008500180010a00200021031400042060c0008406000010808300021010000042000800084000000106bf700020c5ee000418bcc000831738001061f700020c1ee00041824c00083043800104bff
|7=>0x50c304000a107dc001420c3800284182000508300000a104080014204080028018200045c3ee0008987dc001130c9800224183000448304000890408001100c10002201030004400040008587dc0010b0eb80021418300041c1ee00083825c0010704980020c18500040c3ae00081824c001020fb80020410300040800400080800000100001000200000
|8=>0x2004786004008908008003210010002c200200050400400081c00800100001000080002000084004000010008000018010000000018051e600300a1c400404010000807af300100d5e6002012bcc00402179800801822001000000001014bcc002025798004018a20008021440010023cc00200450000400820000800100000a50604001440000002861d7
|9=>0x40095e60080123cc010022738020042e70040083ee0080106080100208000200400000400530600800a088010010c18020021000040040840080080880100051100200024200400020000800020c01000040002000044004000084008000008008833738010482c20020805840041003080080717380100864000200d586004018b9c008031670010062c7
|10=>0x10001044020002080030221738060420c600a20c5ce014018b9c028001610050002c00082085ce010110b8c020210610040400c600808018801002090802000341004000287006000088008a18608011420fb8022800d300420d3c600840000c0104206b80208408700406c2040080a020c010074f580200e98300400f3c600801a7ac010034f18020060e3
|11=>0x3180004406001cbcc08600569810806af30210095e604101abcc082025798104028f302000f5e604001cbcc080035798100062f30200095e60400123cc08002179810002af3020004526040004bcc0800045101000080202000000402b012bcc0508104180a0069e301400c7ee02801838c05001041808c008a201180104402200000804003179808002822
|12=>0x8800c5ee110018b9c220021738410400e008200c5ee104018b9c208021238410022c20820005ce1040009082080003104100004208008c5ee100118b9c2002217b8400442e70800805ce1001001082000317b8400062e70800089ce100010bdc20002173840002600080004402100008800200001738400000c208000010410000020020000021020000204
|13=>0x240003579a010060f340200c166800010b8ce08030739840066e730000c1ce60001831cc00024599800040e720000d1ce40001a31c800032738450002c208a00040e11011010822020153844040246
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0xf01000040f0004c00020100004050a800180006800000000000000f000000400000000004120101e00078000000000001a05000141600
|7,0=>0x98087c0080a9d10000393400020080a176452200660001c6e0e000000014020105000a61a83898060d285440049369c2000104688fc083c0060e0380c0a2aa280dc403038c80002000000200000a40419210080f23439386603000081c160080404a10022911062900802b2008025a021e13c02020080000000014c4d12818340e07078d1bc7b28a949ad4278088e54
|7,1=>0xaa39804008b80802081180c0117008081e76010806e21000cc0017218049877001c002016600c7f6f678062202000c0e7156501c0200128089807000041a188f800080a8c0b6421d174089ae44284002000000402020281c1c0101000252a008d8f8008b01c6cb50013000001da49801c000022800078b027804c008980064d656809003be5ae00f27c1e02001115e49
|7,2=>0xa02010100187670000000
|8,0=>0x4628cc135b7180cb0d09116e0db58329d508c1db2f04c278da4f85cc652f105689e4c8f92a95d2cef1cd4d46dc61182733499e704e2bced19a74b2827a63515c558aa9387186f772d3be2158274c261660975a6cb8e6804a6e6030a3890ed8d19c939742a26fab6a39eb5920b6bc6c6e59255ea11d7eafd3af313e5a3c56144eae85f6fcb1a0d040ab52a90111868612
|8,1=>0xd08f4513cc0cf579602edaf139530985821c0d4a2bfa07940239082d982aa414b9d155af864a708822ad041a5c658d294fba9268ccd7a13fee24a2c92d0da6d8cecb75eb139ca5a9d163116bd6eaa109a364aeae03c71adcc063c64c0c3227a11b518c65ba13313369c720be30b17092f9d45c74ec395ccbd8883e315c3826180c38b1c07cf040c4c8b338d0daae086b
|8,2=>0x4f411e6aa4541170c48a6dc4eba334f34961b061c357313387acc99b4c9db134afa4e16b132b3aa09acd5039f8ae6e4dc3cb98c4a1a966606900a6c4817aef1f7354d604ee5a752690605cbfa7da4ad504c4bd503cd8659935fee733
|9,0=>0x173345a1fd733159ae73b7f586bb7b566ad8c68add9ef8a963ceddd9b2f3dcb793c8dfa218a37cf0d175cf2b11e627b6b682c8305f16375bbe6d1b7ad867dd73f3fdda806161a4714c5c51f5b2627f64af8c8b520f346530e34d125549fe9b8d
|10,0=>0xcdde552612c1a0d85e2ddd8c591
|11,0=>0x58
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 35 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_238 10 roots_238 ops++addP pm 1 dom_231 9 roots_231 ops++addP pm 2 dom_205 8 roots_205 ops++addP pm 3 dom_110 7 roots_110 ops++addP pm 4 dom_233 8 roots_233 ops++addP pm 5 dom_235 9 roots_235 ops++addP pm 6 dom_207 9 roots_207 ops++addP pm 7 dom_175 9 roots_175 ops++addP pm 8 dom_109 7 roots_109 ops++addP pm 9 dom_203 8 roots_203 ops++addP pm 10 dzo_75_4 5 roots_75 ops++addP pm 11 dzo_107_4 6 roots_107 ops++addP pm 12 dom_107 6 roots_107 ops++addP pm 13 dom_111 8 roots_111 ops++addP pm 14 dom_237 9 roots_237 ops++addP pm 15 dom_47 5 roots_47 ops++addP pm 16 dom_101 4 roots_101 ops++addP pm 17 dom_45 4 roots_45 ops++addP pm 18 dom_143 6 roots_143 ops++addP pm 19 dom_229 6 roots_229 ops++addP pm 20 dom_103 5 roots_103 ops++addP pm 21 dom_173 6 roots_173 ops++addP pm 22 dom_227 6 roots_227 ops++addP pm 23 dom_171 6 roots_171 ops++addP pm 24 dom_75 5 roots_75 ops++addP pm 25 dom_167 5 roots_167 ops++addP pm 26 dom_199 6 roots_199 ops++addP pm 27 dom_163 4 roots_163 ops++addP pm 28 dzo_235_4 7 roots_235 ops++addP pm 29 dzo_206_32 6 roots_206 ops++addP pm 30 dzo_207_32 7 roots_207 ops++addP pm 31 dzo_203_32 6 roots_203 ops++addP pm 32 dzo_203_4 6 roots_203 ops++addP pm 33 dzo_205_32 6 roots_205 ops++addP pm 34 dom_195 5 roots_195 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_239 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_75_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_107_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_235_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_206_32_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_207_32_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_203_32_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_203_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_205_32_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_195 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_238 10 s (0,roots_238.map (·&&&dom_238)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_239 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_238 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_239==dom_239)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_239 gM v ys):RunD true dom_239 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_239 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 53 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 53 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 266 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 266 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 338 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 82 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 338 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 85 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 85 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 12 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_239 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤11) (h:RunD true dom_239 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_239 roots_239 goal_239 12:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_239
theorem lowS_239:Lower true dom_239 roots_239 goal_239 12:=S_239.noCircuit
theorem lowS_251:Lower true dom_251 roots_251 goal_251 11:=lower_slice_b [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,1,33)] (by decide +kernel) lowS_219
def dzo_188_2:=0x444444444444444400000000000000004444444444444444
def gzo_188_2:=0x444444444444444000000000000000004444444444404400
def gsh_188_2:=0x111111111111111000000000000000001111111111101100
theorem lowS_zo_188_2_148:Lower true dzo_188_2 roots_188 gzo_188_2 6:=lower_iso_b (d1:=dom_188) (r1:=roots_188) (T1:=gsh_188_2) [(dom_188,2)] (by decide +kernel) (lower_slice_b (T:=gsh_188_2) [(0x110011001100110000000000000000001100110011001100,0,8),(0x111111110000000000000000000000001111111100000000,0,32)] (by decide +kernel) lowS_148)
def dzo_220_32:=0x1111111100000000111111110000000011111111000000001111111100000000
def gzo_220_32:=0x1111111100000000111111100000000011111110000000001010101000000000
def gsh_220_32:=0x11111111000000001111111000000000111111100000000010101010
theorem lowS_zo_220_32_216:Lower true dzo_220_32 roots_220 gzo_220_32 6:=lower_iso_b (d1:=dom_220) (r1:=roots_220) (T1:=gsh_220_32) [(dom_220,32)] (by decide +kernel) (lower_slice_b (T:=gsh_220_32) [(0x10101010000000001010101000000000101010100000000010101010,0,4)] (by decide +kernel) lowS_216)
def dzo_250_4:=0x5050505050505050505050505050505050505050505050505050505050505050
def gzo_250_4:=0x5050505050505050505050505050505050505050505050405050505050504000
def gsh_250_4:=0x505050505050505050505050505050505050505050505040505050505050400
theorem lowS_zo_250_4_74:Lower true dzo_250_4 roots_250 gzo_250_4 7:=lower_iso_b (d1:=dom_250) (r1:=roots_250) (T1:=gsh_250_4) [(dom_250,4)] (by decide +kernel) (lower_slice_b (T:=gsh_250_4) [(0x505000005050000050500000505000005050000050500000505000005050000,0,16),(0x505050500000000050505050000000005050505000000000505050500000000,0,32),(0x505050505050505050505050505050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_74)
def dzo_252_2:=0x4444444444444444444444444444444444444444444444444444444444444444
def gzo_252_2:=0x4444444444444444444444444444444044444444444444444444444444404400
def gsh_252_2:=0x1111111111111111111111111111111011111111111111111111111111101100
theorem lowS_zo_252_2_148:Lower true dzo_252_2 roots_252 gzo_252_2 7:=lower_iso_b (d1:=dom_252) (r1:=roots_252) (T1:=gsh_252_2) [(dom_252,2)] (by decide +kernel) (lower_slice_b (T:=gsh_252_2) [(0x1100110011001100110011001100110011001100110011001100110011001100,0,8),(0x1111111100000000111111110000000011111111000000001111111100000000,0,32),(0x1111111111111111000000000000000011111111111111110000000000000000,0,64)] (by decide +kernel) lowS_148)
namespace S_254
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(4,20),(4,36),(4,132),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,72),(8,136),(12,14),(12,28),(12,44),(12,76),(12,140),(16,20),(16,80),(16,144),(18,22),(18,26),(18,50),(18,82),(18,146),(24,26),(24,28),(24,88),(24,152),(32,34),(32,36),(40,42),(40,44),(40,104),(40,168),(48,50),(48,52),(48,112),(48,176),(56,58),(56,60),(56,120),(56,184),(64,66),(64,72),(64,80),(64,192),(68,70),(68,76),(68,84),(68,100),(68,196),(96,98),(96,100),(96,104),(96,112),(96,224),(128,132),(128,136),(128,144),(128,192),(130,134),(130,138),(130,146),(130,162),(130,194),(160,162),(160,164),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|6=>2
|7=>7
|8=>27
|9=>19
|10=>4
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x9c559372ab
|7,0=>0xc9146b9ff56bee161e66337d9314f816afe
|8,0=>0xe4a24d2342b3a76a91899b9cf9933079e356ea066660f5454a5427b535604d72f4a6a248e4c3f27339a3c2376d2151d20cca20af51589b13b9a0876b03fc4009cf0038e
|9,0=>0xfd87fd188d9dd5a977e8827977ae886fe3468c0b560644bb774b88540456258631d9191d1f81bfa91283a11dc905f3b
|10,0=>0xc5d3ea74c91a4340a6d4
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88888888888888895555555555555555555555555555555555555555555555554141414141414140282828282828282828282828282828282828282828282828000000000000000005500550055005500550055005500550055005500550055005400540054005400000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000a8a8a8a95554000155540001555400015554000155540001555400015554000155540002a802a802a802a802a802a802a802a802a802a802a802a802a802a802a802a80555555555555555555555555555555555555555555555555000000000000000000000000000000000a0a0a0a0a0a0a0a222222222222222200000000000000015555555400000001555555540000000155555554000000015555555400000002828282828282828282828282828282828282828282828282828282828282828444444444444444444444444444444444444444444444444444444444444444400aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00880088008800880001555400015554000155540001555400015554000155540001414000014142aaaaaaaaaaaaaaa80000000000000002aaaaaaaaaaaaaaa80000000000000005555555555555555555555555555555500000000000000000000000000000000
|0,1=>0xaaaaaaaaaaaaaaaa8888888888888888a0a0a0a0a0a0a0a080808080808080801414141414141414141414141414141410101010101010101010101010101012aaaaaaaaaaaaaaa8282828282828282aaaaaaaaaaaaaaaa82020202020202021111111111111111111111111111111110101010101010101010101010101010aaaaaaaaaaaaaaaa2222222222222222aaaaaaaaaaaaaaaa202020202020202000000000000000015555555555555554000000000000000111111111111111100000000000000002aaaaaaaaaaaaaaa800000000000000028282828282828284444444444444444555555555555555544444444444444445454545454545454aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a155555555555555551111111111111111555555555555555511111111111111100000000000000000000000000000000028282828282828282020202020202025555555555555555555555555555555544444444444444444444444444444444aaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a08888888888888888808080808080808155555555555555554141414141414141555555555555555541414141414141422a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2222222222222220000000000000000454545454545454500000000000000004444444444444444
|0,2=>0x2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a1111111111111111101010101010101011111111111111111010101010101010aaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8aaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8000000015555555400000001515151500000000155555554000000015151515000000002a2a2a2a000000002a2a2a2a000000002a2a2a2a000000002a2a2a2a1111111111111111111111111111111111111111111111110000000000000000a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8000000000000000000000000000000000000000000000001555555555555555541414141414141400000000000000000000000000000000088888888888888888080808080808080505050505050505040404040404040405050505050505050404040404040404aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a95151515151515151515151515151515151515151515151515151515151515150000000000000000000000000000000000000000000000002a2a2a2a2a2a2a2a1111111111111111111111111111111111111111111111111010101010101010
|_,_=>0
def sP:Nat→Nat
|0=>0x8804018a24511a20018914408100628915110804018a24544404018a25814404018a24e1541080462891445410062891444c818a48510320018a24511020018a38510304018a1440c134018a14430100a24510b04018a2451081c61440c2040
|1=>0x18a24e1440680062891444c10062891442019c018a2451019c018a24512504018a24552404018a2611442010062898c510100628948550420628914480804018a26114404018a24512004018a24511f04018a24511d04018a24511b040189144
|2=>0x4018a24511a04018a2525c404018a24e14420100628938510100628988510804018a25215410100628914420134018a24511c04018a252144b0100628914404d0062898855010062893853c404018a24550420134a24512a040289144a48040
|3=>0x628914404018a24510804018a25714404018a26214404018a24550404028988512904018a25715610100a24512904018a24564404018a26b14404018a24550420118a24511e04018a26d144
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0xee007
|7,0=>0xf1c6902c812407202ae0e7
|8,0=>0x46261f30878043de5df0e696f435a19d0c595ec2d61592a484e425211908483e41d20dae6492e41520972438
|9,0=>0x6da35b3a67cf465a31d1868bf45da2dd1659aec55269734299d44c66531218
|10,0=>0xeb473a38d1be8
|11,0=>0x1de7
|_,_=>0
def wAt:=mkWire dB 46 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x5d6440514041011414401384c52100162231444101384d2011415758101450178145521005c055c4c50128e85210014f07108410128e92011414435148800510d452200159115c1c5011004521001575a101450104052501414401141493e1084101441c435148800524f84211484005
|1=>0x140444914141011004552100620314454071004501141452100152011414511040450510045220015713140444a1414522001451110044211484005100452200146ae11245051a28511040442214840054940505100622014441018880511040449a480c505585c40510062231444101
|2=>0x1011404511100468a1444405140468a1445707
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0xc4084044004000000000
|8,0=>0x5e35b35835535234f34c34934634334033d33a33733433132e32b32832532231f31c3193163133103
|9,0=>0x8528328127f27d27b27927727527327126f26d26b2692672652632612
|10,0=>0x8a1891881871
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x80100242fc0e5fe064bf0317f818afc085fe042480207f8102fc0497e022ff0115f8082fc0317e0183f0035f8012fc008f4002ff00139800978004b4001bf0007f8002fc000fe0005a0002a0000800002800000
|1=>0x1002bf4325f9012fc400d6142bf
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x5043080000
|8,0=>0xb29e41f1d830759859b10c4864968a120948e352
|9,0=>0x1d8d155b5da81748f4996e47144d7
|10,0=>0x195657
|11,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 21 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_246 10 roots_246 ops++addP pm 1 dom_252 9 roots_252 ops++addP pm 2 dom_126 9 roots_126 ops++addP pm 3 dom_190 9 roots_190 ops++addP pm 4 dom_250 9 roots_250 ops++addP pm 5 dom_238 10 roots_238 ops++addP pm 6 dzo_188_2 6 roots_188 ops++addP pm 7 dom_222 10 roots_222 ops++addP pm 8 dzo_234_4 6 roots_234 ops++addP pm 9 dzo_122_4 6 roots_122 ops++addP pm 10 dom_122 6 roots_122 ops++addP pm 11 dzo_220_32 6 roots_220 ops++addP pm 12 dzo_220_2 6 roots_220 ops++addP pm 13 dzo_250_4 7 roots_250 ops++addP pm 14 dzo_252_2 7 roots_252 ops++addP pm 15 dzo_218_4 6 roots_218 ops++addP pm 16 dom_216 5 roots_216 ops++addP pm 17 dom_124 5 roots_124 ops++addP pm 18 dzo_106_4 5 roots_106 ops++addP pm 19 dom_188 6 roots_188 ops++addP pm 20 dom_62 5 roots_62 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_188_2_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_234_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_122_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_220_32_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_220_2_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_250_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_252_2_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_218_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_106_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_62 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_246 10 s (0,roots_246.map (·&&&dom_246)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_246 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 2 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 27 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 27 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 19 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 19 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 4 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_254 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_191:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_iso_b isoMvS_191 (by decide +kernel) lowS_127
def isoMvS_247:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_247:Lower true dom_247 roots_247 goal_247 12:=lower_iso_b isoMvS_247 (by decide +kernel) lowS_239
def isoMvS_253:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 11:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_251
def dzo_189_2:=0xcccccccccccccccc0000000000000000cccccccccccccccc
def gzo_189_2:=0xccccccccccccccc80000000000000000ccccccccccc8cc00
def gsh_189_2:=0x333333333333333200000000000000003333333333323300
theorem lowS_zo_189_2_149:Lower true dzo_189_2 roots_189 gzo_189_2 7:=lower_iso_b (d1:=dom_189) (r1:=roots_189) (T1:=gsh_189_2) [(dom_189,2)] (by decide +kernel) (lower_slice_b (T:=gsh_189_2) [(0x330033003300330000000000000000003300330033003300,0,8),(0x333333330000000000000000000000003333333300000000,0,32)] (by decide +kernel) lowS_149)
def dzo_253_2:=0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def gzo_253_2:=0xccccccccccccccccccccccccccccccc8ccccccccccccccccccccccccccc8cc00
def gsh_253_2:=0x3333333333333333333333333333333233333333333333333333333333323300
theorem lowS_zo_253_2_149:Lower true dzo_253_2 roots_253 gzo_253_2 8:=lower_iso_b (d1:=dom_253) (r1:=roots_253) (T1:=gsh_253_2) [(dom_253,2)] (by decide +kernel) (lower_slice_b (T:=gsh_253_2) [(0x3300330033003300330033003300330033003300330033003300330033003300,0,8),(0x3333333300000000333333330000000033333333000000003333333300000000,0,32),(0x3333333333333333000000000000000033333333333333330000000000000000,0,64)] (by decide +kernel) lowS_149)
def dzo_185_2:=0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c
def gzo_185_2:=0xc0c0c0c0c0c0c0800000000000000000c0c0c0c0c080c00
def gsh_185_2:=0x30303030303030200000000000000000303030303020300
theorem lowS_zo_185_2_145:Lower true dzo_185_2 roots_185 gzo_185_2 6:=lower_iso_b (d1:=dom_185) (r1:=roots_185) (T1:=gsh_185_2) [(dom_185,2)] (by decide +kernel) (lower_slice_b (T:=gsh_185_2) [(0x30003000300030000000000000000000300030003000300,0,8),(0x30303030000000000000000000000000303030300000000,0,32)] (by decide +kernel) lowS_145)
def dzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0f0f0f0e000
def gsh_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0f0f0f0e00
theorem lowS_zo_251_4_75:Lower true dzo_251_4 roots_251 gzo_251_4 8:=lower_iso_b (d1:=dom_251) (r1:=roots_251) (T1:=gsh_251_4) [(dom_251,4)] (by decide +kernel) (lower_slice_b (T:=gsh_251_4) [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,0,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,0,32),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_75)
def dzo_249_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_249_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c0c0c0c0c0c0c0c0c0c0c0c0c080c00
def gsh_249_2:=0x303030303030303030303030303030203030303030303030303030303020300
theorem lowS_zo_249_2_145:Lower true dzo_249_2 roots_249 gzo_249_2 7:=lower_iso_b (d1:=dom_249) (r1:=roots_249) (T1:=gsh_249_2) [(dom_249,2)] (by decide +kernel) (lower_slice_b (T:=gsh_249_2) [(0x300030003000300030003000300030003000300030003000300030003000300,0,8),(0x303030300000000030303030000000003030303000000000303030300000000,0,32),(0x303030303030303000000000000000003030303030303030000000000000000,0,64)] (by decide +kernel) lowS_145)
def dzo_249_4:=0x3030303030303030303030303030303030303030303030303030303030303030
def gzo_249_4:=0x3030303030303030303030303030303030303030303030203030303030302000
def gsh_249_4:=0x303030303030303030303030303030303030303030303020303030303030200
theorem lowS_zo_249_4_73:Lower true dzo_249_4 roots_249 gzo_249_4 7:=lower_iso_b (d1:=dom_249) (r1:=roots_249) (T1:=gsh_249_4) [(dom_249,4)] (by decide +kernel) (lower_slice_b (T:=gsh_249_4) [(0x303000003030000030300000303000003030000030300000303000003030000,0,16),(0x303030300000000030303030000000003030303000000000303030300000000,0,32),(0x303030303030303030303030303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_73)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,10),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,72),(8,136),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,28),(24,88),(24,152),(32,33),(32,34),(32,36),(40,41),(40,42),(40,44),(40,104),(40,168),(48,49),(48,50),(48,52),(48,112),(48,176),(56,57),(56,58),(56,60),(56,120),(56,184),(64,65),(64,66),(64,72),(64,80),(64,192),(68,69),(68,70),(68,76),(68,84),(68,100),(68,196),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,132),(128,136),(128,144),(128,192),(130,131),(130,134),(130,138),(130,146),(130,162),(130,194),(160,161),(160,162),(160,164),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|9=>3
|10=>26
|11=>15
|12=>4
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0xf5136e02a995bef
|10,0=>0xfc66dd3414cb333b8b1eb77c3b2eb09e02384eb3700266d4835d4b95c48f52f204862c426543e3e03bc652c57f2615a2579424fa41d2cc1aea1101170bff406014
|11,0=>0xc2f0daf7e97e18b77637770cd709c564df26224036fe42c649279ab23abe0e20b0d608090fc
|12,0=>0x8e306792e43ec66177bc
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c03030303030303030303030303030303030303030303030300000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000ffffffff03030303ffffffff03030303ffffffff03030303ffffffff00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0ffffffffffffffffffffffffffffffffccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000
|0,1=>0xffffffffffffffffccccccccccccccccf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffffcfcfcfcfcfcfcfc0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cfffffffffffffffffffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfffffffffffffffffffffffffffffffffffffffffffffffffcfcfcfcfcfcfcfc3333333333333333333333333333333330303030303030303030303030303030ffffffffffffffff3333333333333333ffffffffffffffff3030303030303030fffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc000000000000000000000000000000000f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c3333333333333333333333333333333333333333333333330000000000000000fffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfc00000000000000000000000000000000fffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0cfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfccccccccccccccccffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc
|0,2=>0xffffffffffffffffccccccccccccccccf0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0
|_,_=>0
def sP:Nat→Nat
|0=>0x1c614b24158a2071852c20402951c61440c90402071854cb2412881c614b08904028d1c614b4490402881c615224128d2071852c904f00a2071852d12412881c614b40904a3481c614b2413ca20c1852c904028830614b2412881c61440c2040
|1=>0x26004a20718578b2412881c614b08174a20718548b08904028718548b4090402881c61522d02412881c614b24100a3881c614b24128e2071857032412881c615b2c90402881c61440c204a2071852d704a5481c615b2c904a2071852c9059288
|2=>0x4a2071851032412881c614b24100a3481c614b24168a2071854982c904a2071852c904a3481c614b7c904a20718510b24100a2071852c224100a1c614b5c204a2071852d02412881c615c2c904a20718548b24100a2071850cb0890401c614b
|3=>0x71852c904a2071852c22412881c614b24100a2071852d72412881c61442c904a2071850cb08904a20718560b5c904a2071857182c9
|_=>0
def sO:Nat→Nat→Nat
|9,0=>0x424110008
|10,0=>0x2092fb9794ba65bf4d4b65530296f2ae952526e52528994049de4dd26592e494a89143f91ad0b24454199
|11,0=>0x646b0f57daba4daaac3357aa74d16677532994cc8262f30da
|12,0=>0xdb4eb674939b9
|13,0=>0x1bf8
|_,_=>0
def wAt:=mkWire dB 33 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x20a4b292c249214894b0120a4b252ca4921409d72124a4b4108a492168a49622c8585e2c849292408a21248492d20a4b29508c90d2ca4b02288492124d4b0220a522f0c84b2940bc90128849352c088292c089012884b4208a49211ce44022c94a211ce49362c088292c94b292884921
|1=>0x2484a2124a4b252ca49212c849292584b2124b4b292c088292588b2160a4b212c088295c8c9292c94a21288492124a492108a49212c249212c048292ca4a21248585c2c849292df572324a49212d789292c04a2124849012c048292404b0120a44022c94a2124d8b02
|_=>0
def oO:Nat→Nat→Nat
|9,0=>0x21022004
|10,0=>0x2b9d43a2738e59c838a708df9bc3726d8d99b035a6a8d39a4342678cd99832a648c798c3
|11,0=>0x1d8ba1722e05b8b616a2d0598b21622c0578ae15a2
|12,0=>0xf63e87c8f81
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0xa379f0813ff0807bf06079f04039f03bf9f03bc0e029f9f024bff020fff02039f014b9f01439f011bbf010b9f01039f00db9f00afbf00439f003bbf003b9f00339f002bdf00139f000fff000fbf000f9f000b9f0007bf0003bf00039f000000
|1=>0xc3039f86079f414b9f3803bf260bbf
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>0x2047
|10,0=>0x38141161969e2168464cd5503dd6cc2dc24848d
|11,0=>0x59200c85632900845225df
|12,0=>0x101402
|13,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 24 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_253 11 roots_253 ops++addP pm 2 dom_191 11 roots_191 ops++addP pm 3 dom_251 11 roots_251 ops++addP pm 4 dom_127 11 roots_127 ops++addP pm 5 dom_249 9 roots_249 ops++addP pm 6 dzo_189_2 7 roots_189 ops++addP pm 7 dom_247 12 roots_247 ops++addP pm 8 dom_239 12 roots_239 ops++addP pm 9 dom_223 12 roots_223 ops++addP pm 10 dom_187 9 roots_187 ops++addP pm 11 dom_125 9 roots_125 ops++addP pm 12 dom_63 7 roots_63 ops++addP pm 13 dzo_121_4 6 roots_121 ops++addP pm 14 dzo_253_2 8 roots_253 ops++addP pm 15 dzo_185_2 6 roots_185 ops++addP pm 16 dom_189 8 roots_189 ops++addP pm 17 dom_123 8 roots_123 ops++addP pm 18 dzo_251_4 8 roots_251 ops++addP pm 19 dzo_123_4 7 roots_123 ops++addP pm 20 dom_185 6 roots_185 ops++addP pm 21 dom_121 6 roots_121 ops++addP pm 22 dzo_249_2 7 roots_249 ops++addP pm 23 dzo_249_4 7 roots_249 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_189_2_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_121_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_253_2_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_185_2_145 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_251_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_123_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_249_2_145 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_249_4_73 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 3 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 26 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 26 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 15 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 4 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 4 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [4, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.or, inputs := [0, 7] }, { op := GateOp.or, inputs := [10, 8] }, { op := GateOp.or, inputs := [3, 5] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [6, 12] }, { op := GateOp.or, inputs := [5, 9] }, { op := GateOp.and, inputs := [15, 13] }, { op := GateOp.and, inputs := [11, 6] }, { op := GateOp.and, inputs := [14, 1] }, { op := GateOp.and, inputs := [8, 10] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52388_aux

theorem PEqualNP.Outside.L_meta_52388 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52388_aux.main
