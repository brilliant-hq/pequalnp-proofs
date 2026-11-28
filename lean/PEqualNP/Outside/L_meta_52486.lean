import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52486_aux
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

def dom_50 : Nat := 0x5000500050005
def goal_50 : Nat := 0xffffcccccccc0000ffffcccccccc0000ffffcccccccc0000ffffcccccccc0000
def roots_50 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xffffeeeecccc0000ffffeeeecccc0000ffffeeeecccc0000ffffeeeecccc0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xffffaaaaf0f00000ffffaaaaf0f00000ffffaaaaf0f00000ffffaaaaf0f00000
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xffffccccfcfc0000ffffccccfcfc0000ffffccccfcfc0000ffffccccfcfc0000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xffffeeeefcfc0000ffffeeeefcfc0000ffffeeeefcfc0000ffffeeeefcfc0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffffffaaaa00aa00ffffffaaaa00aa00ffffffaaaa00aa00ffffffaaaa00aa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffffffcccccc0000ffffffcccccc0000ffffffcccccc0000ffffffcccccc0000
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffffffeeeeccaa00ffffffeeeeccaa00ffffffeeeeccaa00ffffffeeeeccaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_60 : Nat := 0x1111111111111111
def goal_60 : Nat := 0xffffff00f0f00000ffffff00f0f00000ffffff00f0f00000ffffff00f0f00000
def roots_60 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xffffffaafaf0aa00ffffffaafaf0aa00ffffffaafaf0aa00ffffffaafaf0aa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xffffffccfcfc0000ffffffccfcfc0000ffffffccfcfc0000ffffffccfcfc0000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xffffffeefefcaa00ffffffeefefcaa00ffffffeefefcaa00ffffffeefefcaa00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfffafffafffafffaaa00aa00aa00aa00fffafffafffafffaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfffefffefffefffeaa00aa00aa00aa00fffefffefffefffeaa00aa00aa00aa00
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

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffeeffffffeeeeccaa00eeccaa00ffffffeeffffffeeeeccaa00eeccaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffffafffffffafaf0aa00faf0aa00fffffffafffffffafaf0aa00faf0aa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffffcfffffffcfcfc0000fcfc0000fffffffcfffffffcfcfc0000fcfc0000
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffffefffffffefefcaa00fefcaa00fffffffefffffffefefcaa00fefcaa00
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
def goal_105 : Nat := 0xffaaffaaffaaffaaffaaffaaaa00aa00ffaaffaaffaaffaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeffeeffeeffeeffeeaa00aa00ffeeffeeffeeffeeffeeffeeaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfff0fff0fff0fff0ff00ff0000000000fff0fff0fff0fff0ff00ff0000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffafffafffaffaaffaaaa00aa00fffafffafffafffaffaaffaaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfffcfffcffccffcc00000000fffcfffcfffcfffcffccffcc00000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefffefffeffeeffeeaa00aa00fffefffefffefffeffeeffeeaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffccccffffccccffffcccccccc0000ffffccccffffccccffffcccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffeeeeffffeeeecccc0000ffffeeeeffffeeeeffffeeeecccc0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffff0f0fffff0f0ffff0000f0f00000fffff0f0fffff0f0ffff0000f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafafffffafaffffaaaaf0f00000fffffafafffffafaffffaaaaf0f00000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcfffffcfcffffccccfcfc0000fffffcfcfffffcfcffffccccfcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefefffffefeffffeeeefcfc0000fffffefefffffefeffffeeeefcfc0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffffaaffffffaaaa00aa00ffffffaaffffffaaffffffaaaa00aa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffffccffffffcccccc0000ffffffccffffffccffffffcccccc0000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffffeeffffffeeeeccaa00ffffffeeffffffeeffffffeeeeccaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffffaffffffaafaf0aa00fffffffafffffffaffffffaafaf0aa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcfffffffcffffffccfcfc0000fffffffcfffffffcffffffccfcfc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffffeffffffeefefcaa00fffffffefffffffeffffffeefefcaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaacccc0000cccc0000cccc0000cccc0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_148 : Nat := 0x11001100000000000000000000000000110011
def goal_148 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_148 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fcfc0000fcfc0000fcfc0000fcfc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffafafffffafafffffafafffffafafcfc0000fcfc0000fcfc0000fcfc0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffff00ffffff00ffffff00ffffff00cccc0000cccc0000cccc0000cccc0000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffaaffffffaaffffffaaffffffaaeeccaa00eeccaa00eeccaa00eeccaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffafaf0aa00faf0aa00faf0aa00faf0aa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fcfc0000fcfc0000fcfc0000fcfc0000
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffafffffffafffffffafffffffafefcaa00fefcaa00fefcaa00fefcaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_161 : Nat := 0x30000000300000000000000000000000300000003
def goal_161 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaeeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfffffffffafafafafffffffffafafafaaaaaaaaa00000000aaaaaaaa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0cccccccc00000000cccccccc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffafafafafffffffffafafafaeeeeeeee00000000eeeeeeee00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_168 : Nat := 0x1010000010100000000000000000000010100000101
def goal_168 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_168 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffff00ff00ffffffffff00ff00ffccffcc00000000ffccffcc00000000
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffff0fff0fffffffffff0fff0ffccffcc00000000ffccffcc00000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffafffafffffffffffafffaffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_176 : Nat := 0x100010001000100000000000000000001000100010001
def goal_176 : Nat := 0xffffffffffff0000ffffffffffff0000ffff000000000000ffff000000000000
def roots_176 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffffaaaaffffffffffffaaaaffffaaaa00000000ffffaaaa00000000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffffff0000ffffffffffff0000ffffcccccccc0000ffffcccccccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffaaaaffffffffffffaaaaffffeeeecccc0000ffffeeeecccc0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0ffff0000f0f00000ffff0000f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffffffafafffffffffffffafaffffaaaaf0f00000ffffaaaaf0f00000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffff0f0fffffffffffff0f0ffffccccfcfc0000ffffccccfcfc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffafafffffffffffffafaffffeeeefcfc0000ffffeeeefcfc0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffffaaffffffffffffffaaffffffaaaa00aa00ffffffaaaa00aa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffff00ffffffffffffff00ffffffcccccc0000ffffffcccccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffaaffffffffffffffaaffffffeeeeccaa00ffffffeeeeccaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffffafffffffffffffffaffffffaafaf0aa00ffffffaafaf0aa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffff0fffffffffffffff0ffffffccfcfc0000ffffffccfcfc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffafffffffffffffffaffffffeefefcaa00ffffffeefefcaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfefefefefefefefefafafafafafafafafefefefefefefefe0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffccffccffccffccff00ff00ff00ff00ffccffccffccffcc0000000000000000
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeffaaffaaffaaffaaffeeffeeffeeffeeaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffafffafffafffafffafffafffafffafffaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffcfffcfffcfffcfff0fff0fff0fff0fffcfffcfffcfffc0000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffefffafffafffafffafffefffefffefffeaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffccccffffccccffff0000ffff0000ffffccccffffcccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffaaaaffffaaaaffffeeeeffffeeeecccc0000cccc0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfffff0f0fffff0f0fffffcfcfffffcfcfcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefffffafafffffafafffffefefffffefefcfc0000fcfc0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaaa00aa00aa00aa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffffff00ffffff00ffffffccffffffcccccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffffaaffffffaaffffffeeffffffeeeeccaa00eeccaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcfffffff0fffffff0fffffffcfffffffcfcfc0000fcfc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffffffafffffffafffffffefffffffefefcaa00fefcaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffccccccccffffffff00000000cccccccccccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeffffffffaaaaaaaaeeeeeeeeeeeeeeeeeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f00000000000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffafafafafffffffffafafafafafafafafafafafaaaaaaaaa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfffffffff0f0f0f0fcfcfcfcfcfcfcfccccccccc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefefffffffffafafafafefefefefefefefeeeeeeeee00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffff00ff00ffccffccffccffccffccffcc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffffaaffaaffeeffeeffeeffeeffeeffeeaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffafffffffffffafffafffafffafffafffaffaaffaaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcfffffffffff0fff0fffcfffcfffcfffcffccffcc00000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffffffffffafffafffefffefffefffeffeeffeeaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffaaaaffffffffffffaaaaffffaaaaffffaaaaffffaaaa00000000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffccccffffffffffff0000ffffccccffffccccffffcccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffffffffffaaaaffffeeeeffffeeeeffffeeeecccc0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fffff0f0fffff0f0ffff0000f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffffffffff0f0fffffcfcfffffcfcffffccccfcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffffffffffafafffffefefffffefeffffeeeefcfc0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffff00ffffffffffffff00ffffff00ffffff00ffffff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffffffffffaaffffffaaffffffaaffffffaaaa00aa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffffffffff00ffffffccffffffccffffffcccccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffffffaaffffffeeffffffeeffffffeeeeccaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffffffffffafffffffafffffffaffffffaafaf0aa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffffffffff0fffffffcfffffffcffffffccfcfc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffffffffffafffffffefffffffeffffffeefefcaa00
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
def isoMvS_50:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_50:Lower true dom_50 roots_50 goal_50 4:=lower_iso_b isoMvS_50 (by decide +kernel) lowS_41
def isoMvS_82:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_82:Lower true dom_82 roots_82 goal_82 4:=lower_iso_b isoMvS_82 (by decide +kernel) lowS_41
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_41
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_41
def isoMvS_148:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_148:Lower true dom_148 roots_148 goal_148 4:=lower_iso_b isoMvS_148 (by decide +kernel) lowS_41
def isoMvS_161:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_161:Lower true dom_161 roots_161 goal_161 4:=lower_iso_b isoMvS_161 (by decide +kernel) lowS_41
def isoMvS_168:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_168:Lower true dom_168 roots_168 goal_168 4:=lower_iso_b isoMvS_168 (by decide +kernel) lowS_41
def isoMvS_176:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_176:Lower true dom_176 roots_176 goal_176 4:=lower_iso_b isoMvS_176 (by decide +kernel) lowS_41
theorem lowS_43:Lower true dom_43 roots_43 goal_43 5:=lower_slice_b [(0xc0c00000c0c,32,34)] (by decide +kernel) lowS_41
namespace S_53
def pG:List (Nat×Nat):=[(1,33),(4,20),(5,21),(5,37),(16,20),(16,48),(17,21),(17,49),(32,33),(32,48),(36,37),(36,52)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_53.map (·&&&dom_53)
def gM:=goal_53&&&dom_53
def NN:Nat→Nat
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x3d669
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc00cc000000033000000330000c000c000c000c22002200220022
|_,_=>0
def sP:Nat→Nat
|0=>0xe4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|_,_=>0
def wAt:=mkWire dB 4 54 0x3fffffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_53 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_53 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_53==dom_53)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_53 gM v ys):RunD true dom_53 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_53 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_53 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_53 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_53 roots_53 goal_53 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_53
theorem lowS_53:Lower true dom_53 roots_53 goal_53 4:=S_53.noCircuit
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
def isoMvS_51:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_51:Lower true dom_51 roots_51 goal_51 5:=lower_iso_b isoMvS_51 (by decide +kernel) lowS_43
def isoMvS_54:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 5:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_43
def isoMvS_57:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_43
def isoMvS_58:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 5:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_43
def isoMvS_60:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_60:Lower true dom_60 roots_60 goal_60 4:=lower_iso_b isoMvS_60 (by decide +kernel) lowS_53
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 5:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_43
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_43
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_43
def isoMvS_101:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 4:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_53
def isoMvS_102:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 4:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_53
def isoMvS_105:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_86
def isoMvS_108:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 4:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_53
def isoMvS_114:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_86
def isoMvS_116:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_43
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_43
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 4:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_53
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_43
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_43
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 4:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_53
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_43
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 5:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_43
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 4:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_53
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_43
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_86
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_86
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_86
def isoMvS_195:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 4:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_53
def isoMvS_198:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 4:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_53
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 4:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_53
def isoMvS_210:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_43
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_86
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 5:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_43
def isoMvS_226:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 4:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_53
def isoMvS_228:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 4:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_53
def isoMvS_240:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_240:Lower true dom_240 roots_240 goal_240 5:=lower_iso_b isoMvS_240 (by decide +kernel) lowS_43
theorem lowS_55:Lower true dom_55 roots_55 goal_55 6:=lower_slice_b [(0xaa00aa00aa00aa,32,33)] (by decide +kernel) lowS_54
namespace S_59
def pG:List (Nat×Nat):=[(1,9),(1,33),(2,18),(2,34),(3,11),(3,19),(3,35),(8,9),(8,40),(10,11),(10,26),(10,42),(16,18),(16,48),(17,19),(17,25),(17,49),(24,25),(24,26),(24,56),(32,33),(32,34),(32,40),(32,48)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_59.map (·&&&dom_59)
def gM:=goal_59&&&dom_59
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x2c5d5
|4,0=>0x4f4a113fb00600e036a3
|5,0=>0x721ff4970736c4020d2719bfe0d6260ad3b06e1202aaa00363
|6,0=>0x9abd70e01a0a6f001a42
|7,0=>0x9abd7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x303030302020202f0f0f0f0e0e0e0ea0a0f0f0a0a0a0a00000000f0c0f0cf0f0f0c0c0c0c0cf0f0f0f0f0f0000f0f0f0000000000505050505040504f0f0f0f00000000f000f000f000f00a0a0a0a0a0a0a0a303010103030000f0f0f0f0a0a0a0af0f0f0a0f000f00f0f00000f0f0000c0c0c0c0c0c0c0c
|0,1=>0xf0f00000c0cf0f0a0a0f0f0a0af0f0a0a00000000003000300000000505050505000500f0c0f0c0f0c0f0cf0f0f0f0f000f0000f000f00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1c26014e1300a70c8c02c4e1300a70980581cc02dcf509805384c02d2270981389c3201627080b0384c02bdc709805384c0694e1300ac3ac262a926014e130107098a418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x272c8684cf19b330654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 24 60 0xfffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1939939b3d8897399399181395387
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x610042310000120100
|6,0=>0x918171
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0xffbe625ca246080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x503640210
|6,0=>0x7988
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_58 5 roots_58 ops++addP pm 1 dom_50 4 roots_50 ops++addP pm 2 dom_41 4 roots_41 ops++addP pm 3 dom_51 5 roots_51 ops++addP pm 4 dom_43 5 roots_43 ops++addP pm 5 dom_57 5 roots_57 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_57 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_58 5 s (0,roots_58.map (·&&&dom_58)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_59 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_58 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_59==dom_59)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_59 gM v ys):RunD true dom_59 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_59 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_59 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_59 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_59 roots_59 goal_59 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_59
theorem lowS_59:Lower true dom_59 roots_59 goal_59 8:=S_59.noCircuit
def dzo_57_4:=0x3030303030303030
def gzo_57_4:=0x3030302030302000
def gsh_57_4:=0x303030203030200
theorem lowS_zo_57_4_41:Lower true dzo_57_4 roots_57 gzo_57_4 5:=lower_iso_b (d1:=dom_57) (r1:=roots_57) (T1:=gsh_57_4) [(dom_57,4)] (by decide +kernel) (lower_slice_b (T:=gsh_57_4) [(0x303000003030000,0,16)] (by decide +kernel) lowS_41)
namespace S_61
def pG:List (Nat×Nat):=[(1,9),(1,33),(4,20),(5,13),(5,21),(5,37),(8,9),(8,40),(12,13),(12,28),(12,44),(16,20),(16,48),(17,21),(17,25),(17,49),(24,25),(24,28),(24,56),(32,33),(32,40),(32,48),(36,37),(36,44),(36,52)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_61.map (·&&&dom_61)
def gM:=goal_61&&&dom_61
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x83f2c19fc8
|5,0=>0xa5e0197d244f32e
|6,0=>0xd596d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccccc00cc0332233223322332244444444000000033003300330033004444444444004403333333300000000cccc0000cccc0003300330022002200c0c0c0c0c0c0c0c2222222222222222
|_,_=>0
def sP:Nat→Nat
|0=>0x436109436104386104361074361543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 62 0x3fffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x103
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
addP pm 0 dom_57 5 roots_57 ops++addP pm 1 dom_60 4 roots_60 ops++addP pm 2 dzo_57_4 5 roots_57 ops++addP pm 3 dom_53 4 roots_53 ops++addP pm 4 dom_41 4 roots_41 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_61 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_57_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_41 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_57 5 s (0,roots_57.map (·&&&dom_57)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_61 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_57 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_61==dom_61)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_61 gM v ys):RunD true dom_61 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_61 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
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
theorem lowS_79:Lower true dom_79 roots_79 goal_79 6:=lower_slice_b [(0xcccc000000000000cccc,64,66)] (by decide +kernel) lowS_77
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_slice_b [(0xaa00aa0000000000aa00aa,64,65)] (by decide +kernel) lowS_86
theorem lowS_103:Lower true dom_103 roots_103 goal_103 5:=lower_slice_b [(0xaa000000aa000000aa000000aa,32,33)] (by decide +kernel) lowS_102
theorem lowS_107:Lower true dom_107 roots_107 goal_107 6:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c,32,34)] (by decide +kernel) lowS_105
def dzo_105_4:=0x3030000030300000303000003030
def gzo_105_4:=0x3030000030300000302000002000
def gsh_105_4:=0x303000003030000030200000200
theorem lowS_zo_105_4_41:Lower true dzo_105_4 roots_105 gzo_105_4 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_4) [(dom_105,4)] (by decide +kernel) (lower_slice_b (T:=gsh_105_4) [(0x303000003030000000000000000,0,64)] (by decide +kernel) lowS_41)
namespace S_109
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(4,68),(5,13),(5,37),(5,69),(8,9),(8,40),(8,72),(12,13),(12,44),(12,76),(32,33),(32,40),(36,37),(36,44),(36,100),(64,65),(64,68),(64,72),(96,97),(96,100),(96,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_109.map (·&&&dom_109)
def gM:=goal_109&&&dom_109
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xc6b62
|5,0=>0x1422f
|6,0=>0xf22e7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3333000000000000333300000000cc880000cc880000cc880000cc8b300000033000000330000003300c0c00000c0c00000c0c00000c0c222200002222000022220000222200000000cc88000000000000cc8b333000033330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xd1a1ac684688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 110 0x3fffffffffffffffffffffffffff
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
addP pm 0 dom_105 5 roots_105 ops++addP pm 1 dom_108 4 roots_108 ops++addP pm 2 dzo_105_4 5 roots_105 ops++addP pm 3 dom_77 5 roots_77 ops++addP pm 4 dom_41 4 roots_41 ops++addP pm 5 dom_101 4 roots_101 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_109 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_105_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_101 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_105 5 s (0,roots_105.map (·&&&dom_105)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_109 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_105 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_109==dom_109)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_109 gM v ys):RunD true dom_109 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_109 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_109 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_109 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_109 roots_109 goal_109 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_109
theorem lowS_109:Lower true dom_109 roots_109 goal_109 7:=S_109.noCircuit
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_slice_b [(0x220022002200220022002200220022,32,33)] (by decide +kernel) lowS_116
namespace S_118
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,66),(4,20),(4,68),(6,22),(6,38),(6,70),(16,18),(16,20),(16,48),(16,80),(32,34),(32,48),(36,38),(36,52),(36,100),(64,66),(64,68),(64,80),(96,98),(96,100),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_118.map (·&&&dom_118)
def gM:=goal_118&&&dom_118
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x93d49
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x550055000000000055005500000000aa000000aa000000aa000000aa000140014001400140014001400140014220022002200220022002200220022550055005500550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 119 0x7fffffffffffffffffffffffffffff
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
addP pm 0 dom_116 5 roots_116 ops++addP pm 1 dom_114 5 roots_114 ops++addP pm 2 dom_54 5 roots_54 ops++addP pm 3 dom_86 5 roots_86 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_118 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_86 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_116 5 s (0,roots_116.map (·&&&dom_116)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_118 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_116 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_118==dom_118)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_118 gM v ys):RunD true dom_118 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_118 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_118 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_185:Lower true dom_185 roots_185 goal_185 8:=lower_slice_b [(0x30300000303000000000000000000000303000003030000,32,48)] (by decide +kernel) lowS_169
namespace S_230
def pG:List (Nat×Nat):=[(2,34),(2,66),(4,68),(4,132),(6,38),(6,70),(6,134),(32,34),(32,160),(36,38),(36,100),(36,164),(64,66),(64,68),(96,98),(96,100),(96,224),(128,132),(128,160),(130,134),(130,162),(130,194),(192,194),(192,196),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_230.map (·&&&dom_230)
def gM:=goal_230&&&dom_230
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x390381840c
|5,0=>0x525c803fe000fef
|6,0=>0x3fe0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x5500000055000000550000005500000055000000000000005500000000a0000000a0000000a0000000a0000000a0000000a0000000a0000000a154000001540000015400000154000001540000015400000000000000002800000028000000280000002800000028000000280000000000000005500000000000000550000000000000055000000000000005500000000880000008800000088000000880000008800000088000000880000008954000001540000000000000000000001540000015400000000000000028000000280000002800000028000000280000002800000000000000005500000055000000550000005500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x47320847320473204736204325043210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x156414a6
|6,0=>0x1b5
|_,_=>0
def wAt:=mkWire dB 9 231 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0xf9040
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x21
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_228 4 roots_228 ops++addP pm 1 dom_166 4 roots_166 ops++addP pm 2 dom_198 4 roots_198 ops++addP pm 3 dom_102 4 roots_102 ops++addP pm 4 dom_226 4 roots_226 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_230 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_226 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_228 4 s (0,roots_228.map (·&&&dom_228)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_230 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_228 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124)],[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffffffffffffffff0000000000000000,64),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccccccccccccccccccc,126)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccccccccccccccccccc,126)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_230==dom_230)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_230 gM v ys):RunD true dom_230 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_230 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_230 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_230 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_230 roots_230 goal_230 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_230
theorem lowS_230:Lower true dom_230 roots_230 goal_230 7:=S_230.noCircuit
def isoMvS_62:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 6:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_55
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 8:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_59
def isoMvS_93:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 8:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_59
def isoMvS_94:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 6:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_87
def isoMvS_110:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 5:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_103
def isoMvS_115:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 6:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_107
def isoMvS_121:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 6:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_107
def isoMvS_122:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 6:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_107
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_55
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 7:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_61
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 6:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_55
def isoMvS_167:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_55
def isoMvS_173:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_171
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_55
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_118
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 7:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_118
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 7:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_118
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_118
def isoMvS_199:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 5:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_103
def isoMvS_203:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 7:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_109
def isoMvS_206:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 5:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_103
def isoMvS_211:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 6:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_117
def isoMvS_214:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 7:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_118
def isoMvS_217:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 6:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_107
def isoMvS_218:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 6:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_117
def isoMvS_227:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 6:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_117
def isoMvS_229:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 6:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_117
def isoMvS_233:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_185
def isoMvS_234:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 6:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_117
def isoMvS_241:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 6:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_107
def isoMvS_242:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 7:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_118
def isoMvS_244:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 7:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_118
def isoMvS_248:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 6:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_107
theorem lowS_63:Lower true dom_63 roots_63 goal_63 9:=lower_slice_b [(0xf0f0f0f0f0f0f0f0,16,20)] (by decide +kernel) lowS_59
theorem lowS_95:Lower true dom_95 roots_95 goal_95 9:=lower_slice_b [(0xcccccccc00000000cccccccc,16,18)] (by decide +kernel) lowS_93
theorem lowS_111:Lower true dom_111 roots_111 goal_111 8:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc,32,34)] (by decide +kernel) lowS_109
theorem lowS_119:Lower true dom_119 roots_119 goal_119 8:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa,32,33)] (by decide +kernel) lowS_118
theorem lowS_123:Lower true dom_123 roots_123 goal_123 9:=lower_slice_b [(0xf0f0f0f000000000f0f0f0f00000000,1,33)] (by decide +kernel) lowS_91
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=lower_slice_b [(0x33333333000000003333333300000000,1,33)] (by decide +kernel) lowS_93
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_slice_b [(0xcccc0000cccc00000000000000000000cccc0000cccc,32,34)] (by decide +kernel) lowS_173
namespace S_183
def pG:List (Nat×Nat):=[(1,33),(1,129),(2,18),(2,34),(3,19),(3,35),(3,131),(4,20),(4,132),(5,21),(5,37),(5,133),(6,22),(6,38),(6,134),(7,23),(7,39),(7,135),(16,18),(16,20),(16,48),(16,144),(17,19),(17,21),(17,49),(17,145),(32,33),(32,34),(32,48),(32,160),(36,37),(36,38),(36,52),(36,164),(128,129),(128,132),(128,144),(128,160),(130,131),(130,134),(130,146),(130,162)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_183.map (·&&&dom_183)
def gM:=goal_183&&&dom_183
def NN:Nat→Nat
|3=>1
|4=>6
|5=>13
|6=>9
|7=>2
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xfbe0
|4,0=>0x8d7a63b34e25763223d70a6ac034a8
|5,0=>0x9a26f57684447f73ff5d3e69d391e631efa30d56212551902b1571607f90051d0
|6,0=>0xff647c0fee6e7225317639eb11523211cf402e58008aa
|7,0=>0xa886d4dc49
|8,0=>0x8a6fe
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x330033003300000000000000000000003300330033000000000000000000000000000000000000ff00ff00ff0000550055005500550000000000000000005500550000000000000000ff00ff00000000000000000000000000ff0000ff00ff00000000000000000000000000ff00ff00000000ff00aa00ff00aa000000000000000000ff00aa00000000cc00cc00cc00cc000000000000000000cc00cc00cc00ccff00ff00ff00ff00000000000000000000000000000000ff00ff00ff0000000000000000000000ff00ff00ff0000f000f000f000f0000000000000000000f000f000f000f0ff00ff00ff00ff000000000000000000ff00ff00000000ff000000ff0000000000000000000000ff000000ff0000ff00ff00ff00ff000000000000000000ff00ff00ff0000ff00ff00f000f0000000000000000000ff00ff00f000f0ff00aa00ff00aa000000000000000000ff00aa00ff00aaff00ff00ff00ff000000000000000000cc00cc00cc00cc
|0,1=>0xff00ff00ff00ff000000000000000000ff00aa00ff00aaff005500ff0055000000000000000000ff005500ff00003300330033003300000000000000000033003300330000aa00aa00aa00aa000000000000000000aa00aa00aa00aa000000000f000f000000000000000000000000000f0000ff00ff00ff00ff000000000000000000ff000000ff00000f000f000f000f0000000000000000000f000a000f000a
|_,_=>0
def sP:Nat→Nat
|0=>0x34de85d8243250b890c09896120103590c099cb132662290135d4864a16434e88591339216a219282ac31324ab090c058489820eb099e872c264a045201ab0980c1ac2601d464a0e5098022848018820
|1=>0x164326685c4864cd0b090c940d64326682ac243250b090c041571219333ac869bd0b2193362164
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x1d51851350e5095045
|5,0=>0x6966365d65855264c64664063a63462e6286226
|6,0=>0xa479d79769078978277c67576f6
|7,0=>0xb17ab6
|8,0=>0xb86
|_,_=>0
def wAt:=mkWire dB 23 184 0xffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2219915c52215a19914a19915a12213a722d5c62213a722d0a19914114a15c54115a122159942d4a12845a1
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x391484600000000400000000000
|6,0=>0x192b954a6512793496492
|7,0=>0x383b1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 9
def pmP:Nat→Nat
|0=>0x13f5d9c07e3b0c85c200a040180200
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x321000100000
|6,0=>0x7282456ab
|7,0=>0x9c
|8,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_182 7 roots_182 ops++addP pm 1 dom_167 6 roots_167 ops++addP pm 2 dom_151 6 roots_151 ops++addP pm 3 dom_181 7 roots_181 ops++addP pm 4 dom_179 7 roots_179 ops++addP pm 5 dom_55 6 roots_55 ops++addP pm 6 dom_54 5 roots_54 ops++addP pm 7 dom_53 4 roots_53 ops++addP pm 8 dom_166 4 roots_166 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_183 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_166 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_182 7 s (0,roots_182.map (·&&&dom_182)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_183 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_182 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_183==dom_183)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_183 gM v ys):RunD true dom_183 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_183 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 13 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 13 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_183 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
namespace S_187
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(2,18),(2,34),(3,11),(3,19),(3,35),(3,131),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,138),(16,18),(16,48),(16,144),(17,19),(17,25),(17,49),(17,145),(24,25),(24,26),(24,56),(24,152),(32,33),(32,34),(32,40),(32,48),(32,160),(128,129),(128,136),(128,144),(128,160),(130,131),(130,138),(130,146),(130,162)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_187.map (·&&&dom_187)
def gM:=goal_187&&&dom_187
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xd359c
|7,0=>0x523a54519f2e55a2b4d1064fc
|8,0=>0xd514626f6b
|9,0=>0x3dbb0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000a000a0000000000000000000f000f000a000af0f0f0f0f0a0f0a00000000000000000f0f0f0f0f0a0f0aa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0af0f0f0f0000000000000000000000000f0f0f0f00000000f000f000f000f0000000000000000000f000f000f000f00f0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0f0f0f0a0a0a0a00000000000000000f0f0f0f0a0a0a0af0f00000f0f000000000000000000000f0f00000f0f0000f0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0f0ac0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x7361807326180573618073618a097361809573618047326105436180543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d4835c67
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 188 0xfffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1a17651b785c968561765e1685e1765a1785d9
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
|7,0=>0x38764
|8,0=>0x52
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_185 8 roots_185 ops++addP pm 1 dom_59 8 roots_59 ops++addP pm 2 dom_171 8 roots_171 ops++addP pm 3 dom_179 7 roots_179 ops++addP pm 4 dom_155 7 roots_155 ops++addP pm 5 dom_186 7 roots_186 ops++addP pm 6 dom_147 4 roots_147 ops++addP pm 7 dom_154 4 roots_154 ops++addP pm 8 dom_178 5 roots_178 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_187 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_178 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_185 8 s (0,roots_185.map (·&&&dom_185)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_187 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_185 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_187==dom_187)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_187 gM v ys):RunD true dom_187 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_187 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_187 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
namespace S_231
def pG:List (Nat×Nat):=[(1,33),(1,65),(1,129),(2,34),(2,66),(3,35),(3,67),(3,131),(4,68),(4,132),(5,37),(5,69),(5,133),(6,38),(6,70),(6,134),(7,39),(7,71),(7,135),(32,33),(32,34),(32,160),(36,37),(36,38),(36,100),(36,164),(64,65),(64,66),(64,68),(96,97),(96,98),(96,100),(96,224),(128,129),(128,132),(128,160),(130,131),(130,134),(130,162),(130,194),(192,193),(192,194),(192,196),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_231.map (·&&&dom_231)
def gM:=goal_231&&&dom_231
def NN:Nat→Nat
|4=>5
|5=>16
|6=>36
|7=>9
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xe0ec6a57da68b3766cd41d840
|5,0=>0xf52f4e7592abea69998d821a66fe60661a8523854d554486d43624335b0b3136f23f0c1dc1419f42
|6,0=>0xfb9c0cdf1dcd1f4c083bbd61aa4ca89ea37946cf9087a8fe3b815537ea426ca1364efc609cf5bd925965b58a6958a5155abd5518e45e79408d03d00f3797f34a0627d5d219ff19f42195d90e7190ae4c091c407d99057d504e9c
|7,0=>0xa4ca8905bc8cb8887c1f867c44b9033818b34ab92d269
|8,0=>0x9aff0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00000000000000ff00000000000000000000000000000000000000005500000055000000550000005500000055000000550000005500000000ff00000000000000ff00000000000000ff00000000000000ff00000000ff000000ff000000ff00000000000000ff000000ff0000000000000000ff000000ff000000ff000000ff000000000000000000000000000000000000000000000000ff000000ff0000000000000000000000ff00000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000ff000000f0000000ff000000f0000000f0000000f0000000f0000000f0ff000000ff000000ff000000ff000000ff000000ff000000000000000000000000ff00000000000000ff000000ff000000ff000000ff00000000aa000000aa000000aa000000aa000000aa000000aa000000aa000000aaff000000ff000000ff000000ff000000ff000000ff000000ff00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0cc000000cc000000cc000000cc000000cc000000cc000000cc000000ccff000000aa000000ff000000aa000000aa000000aa000000aa000000aaff000000ff0000000000000000000000ff000000ff0000000000000000
|0,1=>0xff000000ff000000ff000000ff000000cc000000cc000000cc000000ccff000000ff000000ff000000ff0000003300000000000000330000000000000000000000000000000000000000ff000000cc000000ff000000ccff000000ff000000ff000000ff000000ff000000cc000000ff000000cc330000003300000033000000000000003300000033000000330000000000000000ff00000000000000ff00000000000000000000000000000000ff000000ff0000000000000000000000ff000000ff000000ff00000000ff00000000000000ff00000000000000ff0000000000000000000000000f0000000f0000000f0000000f0000000f0000000f0000000f00000000ff000000ff000000ff000000ff000000ff00000000000000ff0000000000000000ff00000000000000ff000000ff00000000000000ff00000000cc000000cc000000cc000000ff000000cc000000cc000000cc000000cc00000000000000000000000000000000ff00000000000000ff0000000000000000ff00000000000000ff00000000000000ff00000000000000000f0000000f000000000000000f0000000f0000000f0000000000000000ff000000cc000000ff000000cc000000cc000000cc000000cc000000cc
|0,2=>0xff000000ff00000000000000ff0000000000000000000000000000000000000000000000000000000000000000ff000000ff000000ff00000000cc00000000000000cc00000000000000ff00000000000000ff0000000000000000cc00000000000000cc000000cc000000cc000000cc000000cc0f000000000000000f000000000000000f000000000000000f00000000ff000000ff0000000f00000000000000ff000000ff0000000f0000000033000000330000003300000033000000330000000000000033000000003300000033000000330000003300000000000000000000000000000000ff000000ff000000ff000000ff0000000f000000000000000f00000000000000000000000000000000ff00000000000000000000000000000000cc000000cc000000cc000000cc000000ff000000cc000000ff000000ccff000000cc000000ff000000cc000000ff000000cc000000ff000000cc00000000ff0000000000000000000000ff000000ff0000000000000000000000000f000000000000000f000000000000000000000000000000000000000000000000ff000000ff00000000000000000000000000000000cc000000cc000000ff000000ff000000cc000000cc000000cc000000cc
|0,3=>0xf0000000f0000000f0000000f00000000000000000000000000000000ff000000ff000000ff000000ff000000f0000000f0000000f0000000f0ff000000f0000000ff000000f0000000ff000000f0000000ff000000f00000000000000000ff000000000000000000000000000000ff00000000ff000000ff000000ff000000ff0000000000000000000000ff00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1a64d0c21402d60c20402430851cf28308500f24308560b34215700b5950c214054308500d0c204700d0d41402d30c214048d0850112c90d01402cd0d01470040c21403cd0c23802cd0c214c2c90c20472830810092021471830850040c2040
|1=>0x2da58d0c2140a0d0c216700b3430851c03cd0c21402e634a0c21402e534308500b90d0df1402cd0c21632cd0c21402e234380500b58d0df08500d0c215e00b34308530b74d0c21402dc34308500b3430850182cd2021402c934315b00b4c3085
|2=>0xb3730c21402cdc4308500bc8d0c21402d60c21403cdc0308500b10d0c21402cd0c21402ef34315b00b58d0c21402ee34308500b36d0c21402c93430851cb343b0500b34308100b343085a8b343085a402cd4c30850213430853002c90c2140
|3=>0x34308500b58d0c21402cd0c21402f43430851c02cd0c21402cf34308500b68d0c216b
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x3929b18ccc6062d315189ea49621b0f586ec31615b09583ec196
|6,0=>0xb1b571eaaf4e7a43505e74f337963c99a40d1a689bc31e0aefe77bbbc1dd2ee276dbb51d9aec76603ae9966eac753327dd30e91745b211cfcc777
|7,0=>0x1a17cd3e4df18f857bf3dddee0f697
|8,0=>0x1a86
|_,_=>0
def wAt:=mkWire dB 53 232 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x34b432e00b4d2c34b83360cb40360cd4d2d34b312d347402d08980352c9a83608fcd2cac043362cdcd2c2c9c03f34b210900b8b3500f4d2c0cf4b34089803534bcd2e2cd963f34b4d2c
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xc0000000000000000000000
|6,0=>0x7c9e170800688006458100162001420000000131000004851100000000f2000d23040028800000002086210831
|7,0=>0x291a0671986519063188611
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xe75e6dd3d6e566d53d4f54ed43d1201000c10c008003002401a01900c009008005004002001000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x10000000200000000000
|6,0=>0x31dc00946b68521000030006c001e400600080004290c
|7,0=>0x11ccef4ae658
|8,0=>0x16
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_230 7 roots_230 ops++addP pm 1 dom_198 4 roots_198 ops++addP pm 2 dom_167 6 roots_167 ops++addP pm 3 dom_199 5 roots_199 ops++addP pm 4 dom_103 5 roots_103 ops++addP pm 5 dom_229 6 roots_229 ops++addP pm 6 dom_163 5 roots_163 ops++addP pm 7 dom_165 5 roots_165 ops++addP pm 8 dom_101 4 roots_101 ops++addP pm 9 dom_225 5 roots_225 ops++addP pm 10 dom_227 6 roots_227 ops++addP pm 11 dom_195 4 roots_195 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_231 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_195 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_230 7 s (0,roots_230.map (·&&&dom_230)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_231 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_230 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_231==dom_231)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_231 gM v ys):RunD true dom_231 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_231 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_231 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_231 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_231 roots_231 goal_231 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_231
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=S_231.noCircuit
theorem lowS_235:Lower true dom_235 roots_235 goal_235 9:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c,32,34)] (by decide +kernel) lowS_233
namespace S_243
def pG:List (Nat×Nat):=[(1,33),(1,65),(1,129),(2,18),(2,34),(2,66),(3,19),(3,35),(3,67),(3,131),(16,18),(16,48),(16,80),(16,144),(17,19),(17,49),(17,81),(17,145),(32,33),(32,34),(32,48),(32,160),(64,65),(64,66),(64,80),(96,97),(96,98),(96,112),(96,224),(128,129),(128,144),(128,160),(130,131),(130,146),(130,162),(130,194),(192,193),(192,194),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_243.map (·&&&dom_243)
def gM:=goal_243&&&dom_243
def NN:Nat→Nat
|5=>3
|6=>5
|7=>4
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x773cf4fa9a0b493
|6,0=>0xc98e7c5edeb8179a75f6461a9
|7,0=>0x712a9655b012792104eb
|8,0=>0x7a9f6
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000f000f000f000f000f000f000c000c000c000c000c000c000c000cf000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000f000f000f000f000f000f000c000c000f000f000f000f000f000f000c000cf000f000f000a000f000f000f000a000f000f000f000a000f000f000f000af000f000c000c000f000f000c000c000f000f000c000c000f000f000c000ca000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a00000000000000000000000000000000f000f000f000a000f000f000f000af0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000f000f000f000f0000000000000000000f000f000f000f0000000000000000f000f000f000f000f000f000f0000000f000f000f000f000f000f000f0000f000f00000000000f000f00000000000f000f00000000000f000f00000000f000f000f0000000f000f000f0000000f000f000f0000000f000f000f0000f000f000f000f000f000f00000000000f000f000f000f000f000f00000000f000a000f000a000f000a000f000a000f000a000f000a000f000a000f000ac000c000c000c000c000c000c000c000c000c000c000c000c000c000c000cf000f000f000f000f000f000f000f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x581a7058f1a704581a705e81a70528170352810d3581a0452170c528170b381a095281763521043210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x2d82b005
|6,0=>0x2b648e798bb916
|7,0=>0x8aef9dbbb16
|8,0=>0x4c6
|_,_=>0
def wAt:=mkWire dB 16 244 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x41586018a55d8a55d8a6158a5455755d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x100
|6,0=>0x7261423112
|7,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xdb5ecad6d65201f5806000c000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>8
|6,0=>0x55a3
|7,0=>0xb6f
|8,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_242 7 roots_242 ops++addP pm 1 dom_225 5 roots_225 ops++addP pm 2 dom_163 5 roots_163 ops++addP pm 3 dom_241 6 roots_241 ops++addP pm 4 dom_177 5 roots_177 ops++addP pm 5 dom_83 5 roots_83 ops++addP pm 6 dom_115 6 roots_115 ops++addP pm 7 dom_147 4 roots_147 ops++addP pm 8 dom_211 6 roots_211 ops++addP pm 9 dom_179 7 roots_179 ops++addP pm 10 dom_210 5 roots_210 ops++addP pm 11 dom_227 6 roots_227 ops++addP pm 12 dom_226 4 roots_226 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_243 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_226 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_242 7 s (0,roots_242.map (·&&&dom_242)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_243 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_242 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccccccccccccccccccccccccccccccc,126),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_243==dom_243)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_243 gM v ys):RunD true dom_243 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_243 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_243 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
namespace S_246
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,66),(4,20),(4,68),(4,132),(6,22),(6,38),(6,70),(6,134),(16,18),(16,20),(16,48),(16,80),(16,144),(32,34),(32,48),(32,160),(36,38),(36,52),(36,100),(36,164),(64,66),(64,68),(64,80),(96,98),(96,100),(96,112),(96,224),(128,132),(128,144),(128,160),(130,134),(130,146),(130,162),(130,194),(192,194),(192,196),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_246.map (·&&&dom_246)
def gM:=goal_246&&&dom_246
def NN:Nat→Nat
|5=>5
|6=>28
|7=>19
|8=>4
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x4cf311a33a09ca00424400fad
|6,0=>0x88c957ce5f7c5097ba5c76edc5bd925318a41ded3a3382a97a29de323982217211fd3116b1414cc614c620f23a0ebd40d9020d7f30d7600c4ae09a7008f7b07769044b903c08
|7,0=>0x9f16e5e0d74dfe742a1a3de6439eee355802d2e121cfd20c1620b4d1e6981912c16a0711b50116770e92d0a03b015af
|8,0=>0x42c423f43d17b541122d
|9,0=>0x3f43d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x2200220022002200220022002200220022002000220020002200200022002000000000000000000000000000000000440040004400400044004000440042a802a802a802a802a802a802a802a802a802a802a802a802200220022002255004400550044005500440055004400550044005500440055004400550044aa00aa00aa00aa00aa000000aa000000aa00aa00aa00aa00aa000000aa000154015401540154015401540154015401100110011001100110011001100112a802a802a802a802a802a802a802a802a802a802a802a800000000000000000000000000000000000000000000000550055000000000055005500550050a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000000001540154000000000154015400000000015401540000000001540112a802a80000000002a802a80000000002a802a80000000002a802a80000000550000005500000055000000550000005500000055000000550000005500008800880088008800880088008800880088008800880088008800880088008814001400140014001400140014001400040004000400040004000000040002a802a802a802a8000000000000000002a802a802a802a800000000000000055005500550055005500550055005500000000000000000000000000000000
|0,1=>0xaa00880000000000aa00880000000000aa00880000000000aa008954015401540154015401540154015400140010001400100014001000140012a802a802a802a802a802a802a802a802a802a802a802a802a8000002a80000500050005000500050005000500050005000500050005000500000005000000000000000000000000000000000000aa008800aa008800aa008800aa00895001500150015001500150015001500150015001500150015001500150015000000002a802a80000000002a802a80000000002a800000000000002a80005500550055005500000000005500550055005500550055000000000055000000000000aa00aa0000000000aa00aa0000000000aa00aa0000000000aa0001540140015401400154014001540140015401400154014001540140015401400000000000000000000000000000000000000002a802a80000000002a8000050005000500000005000500050000000500050005000000050005000500008a008a008a0088008a008a008a0088008a008a008a0088008a008a008a008954015401540000015401540154000001540154015400000154015401540002a802a802a802a802a802a80000000002a802a802a802a802a802a8000000055005500550055005500550055005500550000005500000055000000550000
|0,2=>0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000015401540154015401540154015401540154015400000000015401540000000000000002a802a80000000002a802a80000000002a802200000000002a802255005500550055005500550055005500500050005000500050005000500050aa00aa00aa00aa00aa00aa00aa00aa00a800a800a800a800a800a800a800a844004000440040004400400044004000440040004400400044004000440042a802a802a8022002a802a802a8022002a802a802a8022002a802a802a802255005500550054005500550055005400550055005500540055005500550054aa00aa0000000000aa00aa00aa00a000aa00aa0000000000aa00aa00aa00a000000000000000015401100154011000000000000000000154011001540112a802a802a802a8000000000000000002a802a802a802a802a8022002a802255005500440044005500550044004400550055004400440055005500440044aa00aa00a800a800aa00aa00a800a800aa00aa00a800a800aa00aa00a800a954015401540154015401540154000001540154015401540154015401540000880088008800880088008800880000008800880088008800880088008800055005500500050005500550050005000550055005000500055005500500050
|0,3=>0x154015401540154015401540140014001540154015401540154015401400142a802a002a802a002a802a002a802a002a802a002a802a002a802a002a802a55005500550055005500550055005500550050005500500055005000550050aa00aa00aa00aa00a000a000a000a000aa00aa00aa00aa00a000a000a000a154015401540154011001100110011001540154015401540110011001100110280028002800280028002800280028002800000028000000280000002800011001100110000001100110011000000110011001100000011001100110000aa00aa00aa00aa00aa00a000aa00a000aa00aa00aa00aa00aa00a000aa00a000000001540154000000000154000000000000015401540000000001540002a802a802a8028002a802a802a8028002a802a802a8028002a802a802a802800000000000000000000000000000000550055005500500055005500550050
|_,_=>0
def sP:Nat→Nat
|0=>0x4a31070c10221441e10408041c37c10051070de0401501037010056c46870401441c36010051070d70401564072830451070d50401441d30c10124501c30401441c33c10051070ce04014c2c734014c2c72892051070c11070c60401440c2040
|1=>0x4014c11a1c1005ccb1070c10051070f204014b1072830404911070c9005304ac7040c121441c30451070ef0404ae4070c11070ed04015012b1c30601440ea0408053046810281441c30409c51070c10059841c32401651070c10057441ca0c1
|2=>0x1441c3040144dc70c100511a1c3040150107d830408053041c3040e851070c1005e561070c1005e101070c102014468304015d1070c10291441c30401564070c10052c4dc70c014c107d810051070f50401441c3a810314851070c10051070f4
|3=>0x51070c10055841c3040
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x18609303180cc006
|6,0=>0x6cbb49d96ec475f32e1962eaa751ba71d2ae8e743ba01cf2e72735b991cbae56727b921c82e3a719b8b1c4ae1e7
|7,0=>0x5922b91557a6c51627cf377983ca5e44f1b78a3c35e0b0fe77bbbbe1d0ee08
|8,0=>0xc03de9ae6f6c7
|9,0=>0x1876
|_,_=>0
def wAt:=mkWire dB 59 247 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1d24415483c415103470d2c7440514b840510143011414415680440d1c371031d244011054015b034401007435a107440d0c7691d1245607301c40d6c14c0310941011e444150c5444504545321035d1f4014c0310341651c444010c0435110541151054401281400d10140051034405
|1=>0x41d1c1470d00443051c5440d1774705583441d40744011c5431d1094101124450d100441d10147051034305407c401583c41d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x3300600000000
|6,0=>0x644bcd6900054600139a52464849009e2384688b9952264000890f21c20005980012418c00000
|7,0=>0x160ab1542a4540a714c294520a31442845009f13c2744e09b1342
|8,0=>0xb82002d8da1
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x191080c4000430f1258c202363031258c06416300f088801c3730054fcc007b61001ad8c004163001048c00404b00044840011000003548000a0000008040001c0000040000004400001000000280000088000020000004000000d000000c0000020000004000000
|1=>0x380002260201c902c16740305cca0222122040c88300222030dcc804363
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x3100000
|6,0=>0x2870803c01cb40e14904d0c118008614020018c000
|7,0=>0x1e4579285a676765f9608db722692
|8,0=>0x853615
|9,0=>0x14
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 26 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_244 7 roots_244 ops++addP pm 1 dom_230 7 roots_230 ops++addP pm 2 dom_54 5 roots_54 ops++addP pm 3 dom_116 5 roots_116 ops++addP pm 4 dom_82 4 roots_82 ops++addP pm 5 dom_242 7 roots_242 ops++addP pm 6 dom_118 7 roots_118 ops++addP pm 7 dom_150 5 roots_150 ops++addP pm 8 dom_214 7 roots_214 ops++addP pm 9 dom_176 4 roots_176 ops++addP pm 10 dom_86 5 roots_86 ops++addP pm 11 dom_84 4 roots_84 ops++addP pm 12 dom_210 5 roots_210 ops++addP pm 13 dom_240 5 roots_240 ops++addP pm 14 dom_182 7 roots_182 ops++addP pm 15 dom_50 4 roots_50 ops++addP pm 16 dom_178 5 roots_178 ops++addP pm 17 dom_166 4 roots_166 ops++addP pm 18 dom_148 4 roots_148 ops++addP pm 19 dom_198 4 roots_198 ops++addP pm 20 dom_212 5 roots_212 ops++addP pm 21 dom_228 4 roots_228 ops++addP pm 22 dom_180 5 roots_180 ops++addP pm 23 dom_226 4 roots_226 ops++addP pm 24 dom_102 4 roots_102 ops++addP pm 25 dom_114 5 roots_114 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_246 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_176 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_114 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_244 7 s (0,roots_244.map (·&&&dom_244)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_246 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_244 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124)],[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffffffffffffffff0000000000000000,64),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccccccccccccccccccc,126)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccccccccccccccccccc,126)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_246==dom_246)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_246 gM v ys):RunD true dom_246 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_246 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 28 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 28 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 19 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 19 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 4 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_246 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_249:Lower true dom_249 roots_249 goal_249 9:=lower_slice_b [(0x303000003030000030300000303000003030000030300000303000003030000,32,48)] (by decide +kernel) lowS_233
def isoMvS_126:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_126:Lower true dom_126 roots_126 goal_126 8:=lower_iso_b isoMvS_126 (by decide +kernel) lowS_119
def isoMvS_159:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_iso_b isoMvS_159 (by decide +kernel) lowS_63
def isoMvS_189:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 10:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_187
def isoMvS_190:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_183
def isoMvS_207:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_207:Lower true dom_207 roots_207 goal_207 8:=lower_iso_b isoMvS_207 (by decide +kernel) lowS_111
def isoMvS_215:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 8:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_119
def isoMvS_219:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_219:Lower true dom_219 roots_219 goal_219 9:=lower_iso_b isoMvS_219 (by decide +kernel) lowS_125
def isoMvS_222:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 8:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_119
def isoMvS_237:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 9:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_235
def isoMvS_238:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_231
def isoMvS_250:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 9:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_243
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(4,20),(4,68),(5,13),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,40),(8,72),(10,11),(10,26),(10,42),(10,74),(12,13),(12,28),(12,44),(12,76),(14,15),(14,30),(14,46),(14,78),(16,18),(16,20),(16,48),(16,80),(17,19),(17,21),(17,25),(17,49),(17,81),(24,25),(24,26),(24,28),(24,56),(24,88),(32,33),(32,34),(32,40),(32,48),(36,37),(36,38),(36,44),(36,52),(36,100),(64,65),(64,66),(64,68),(64,72),(64,80),(96,97),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|9=>1
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0xbbe94
|10,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ffffffff00000000ffffaaaaffffaaaaffffaaaaffffaaaaffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ec688fac688
|_=>0
def sO:Nat→Nat→Nat
|9,0=>8
|10,0=>0x87
|_,_=>0
def wAt:=mkWire dB 8 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa5
|_=>0
def oO:Nat→Nat→Nat
|9,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 5
def pmP:Nat→Nat
|0=>0xff00
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>1
|10,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_125 9 roots_125 ops++addP pm 1 dom_63 9 roots_63 ops++addP pm 2 dom_123 9 roots_123 ops++addP pm 3 dom_95 9 roots_95 ops++addP pm 4 dom_126 8 roots_126 ops++addP pm 5 dom_119 8 roots_119 ops++addP pm 6 dom_111 8 roots_111 ops++addP pm 7 dom_118 7 roots_118 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_118 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_125 9 s (0,roots_125.map (·&&&dom_125)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_125 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
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
  · simp [NN] at hi
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
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_slice_b [(0xcccccccccccccccc0000000000000000cccccccccccccccc,16,18)] (by decide +kernel) lowS_189
namespace S_239
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,34),(2,66),(3,11),(3,35),(3,67),(3,131),(4,68),(4,132),(5,13),(5,37),(5,69),(5,133),(6,38),(6,70),(6,134),(7,15),(7,39),(7,71),(7,135),(8,9),(8,40),(8,72),(8,136),(10,11),(10,42),(10,74),(10,138),(12,13),(12,44),(12,76),(12,140),(14,15),(14,46),(14,78),(14,142),(32,33),(32,34),(32,40),(32,160),(36,37),(36,38),(36,44),(36,100),(36,164),(64,65),(64,66),(64,68),(64,72),(96,97),(96,98),(96,100),(96,104),(96,224),(128,129),(128,132),(128,136),(128,160),(130,131),(130,134),(130,138),(130,162),(130,194),(192,193),(192,194),(192,196),(192,200),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffffff
def xsM:=roots_239.map (·&&&dom_239)
def gM:=goal_239&&&dom_239
def NN:Nat→Nat
|9=>1
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0xda982
|10,0=>0x3ce8d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000ffff000000000000ffff000000000000ffff000000000000ffff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000ccccaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaaffff0000ffff00000000000000000000ffff0000ffff0000000000000000ffff0000ffff0000ffff0000ffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ac688fac688
|_=>0
def sO:Nat→Nat→Nat
|9,0=>8
|10,0=>0x87
|_,_=>0
def wAt:=mkWire dB 8 240 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc1
|_=>0
def oO:Nat→Nat→Nat
|9,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 5
def pmP:Nat→Nat
|0=>0x3f80
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>1
|10,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_238 9 roots_238 ops++addP pm 1 dom_175 9 roots_175 ops++addP pm 2 dom_237 9 roots_237 ops++addP pm 3 dom_235 9 roots_235 ops++addP pm 4 dom_231 9 roots_231 ops++addP pm 5 dom_207 8 roots_207 ops++addP pm 6 dom_111 8 roots_111 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_239 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_111 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_238 9 s (0,roots_238.map (·&&&dom_238)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_239 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_238 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_239==dom_239)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_239 gM v ys):RunD true dom_239 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_239 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_239 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,32,33)] (by decide +kernel) lowS_246
def dzo_153_2:=0xc0c0c0c0000000000000000000000000c0c0c0c
def gzo_153_2:=0xc0c0c080000000000000000000000000c0c0800
def gsh_153_2:=0x303030200000000000000000000000003030200
theorem lowS_zo_153_2_137:Lower true dzo_153_2 roots_153 gzo_153_2 5:=lower_iso_b (d1:=dom_153) (r1:=roots_153) (T1:=gsh_153_2) [(dom_153,2)] (by decide +kernel) (lower_slice_b (T:=gsh_153_2) [(0x303000000000000000000000000000003030000,0,16)] (by decide +kernel) lowS_137)
def dzo_233_2:=0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c
def gzo_233_2:=0xc0c00000c0c00000c0c00000c0800000c0c00000c0c00000c0c00000800
def gsh_233_2:=0x30300000303000003030000030200000303000003030000030300000200
theorem lowS_zo_233_2_137:Lower true dzo_233_2 roots_233 gzo_233_2 6:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_2) [(dom_233,2)] (by decide +kernel) (lower_slice_b (T:=gsh_233_2) [(0x30300000000000003030000000000000303000000000000030300000000,0,32),(0x30300000303000000000000000000000303000003030000000000000000,0,64)] (by decide +kernel) lowS_137)
def dzo_249_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_249_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c0c0c0c0c0c0c0c0c0c0c0c0c0c0800
def gsh_249_2:=0x303030303030303030303030303030203030303030303030303030303030200
theorem lowS_zo_249_2_137:Lower true dzo_249_2 roots_249 gzo_249_2 7:=lower_iso_b (d1:=dom_249) (r1:=roots_249) (T1:=gsh_249_2) [(dom_249,2)] (by decide +kernel) (lower_slice_b (T:=gsh_249_2) [(0x303000003030000030300000303000003030000030300000303000003030000,0,16),(0x303030300000000030303030000000003030303000000000303030300000000,0,32),(0x303030303030303000000000000000003030303030303030000000000000000,0,64)] (by decide +kernel) lowS_137)
def dzo_217_2:=0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c
def gzo_217_2:=0xc0c0c0c000000000c0c0c08000000000c0c0c0c000000000c0c0800
def gsh_217_2:=0x3030303000000000303030200000000030303030000000003030200
theorem lowS_zo_217_2_137:Lower true dzo_217_2 roots_217 gzo_217_2 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_2) [(dom_217,2)] (by decide +kernel) (lower_slice_b (T:=gsh_217_2) [(0x3030000000000000303000000000000030300000000000003030000,0,16),(0x3030303000000000000000000000000030303030000000000000000,0,64)] (by decide +kernel) lowS_137)
def dzo_201_2:=0xc0c0000000000000c0c0000000000000c0c0000000000000c0c
def gzo_201_2:=0xc0c0000000000000c080000000000000c0c0000000000000800
def gsh_201_2:=0x303000000000000030200000000000003030000000000000200
theorem lowS_zo_201_2_137:Lower true dzo_201_2 roots_201 gzo_201_2 5:=lower_iso_b (d1:=dom_201) (r1:=roots_201) (T1:=gsh_201_2) [(dom_201,2)] (by decide +kernel) (lower_slice_b (T:=gsh_201_2) [(0x303000000000000000000000000000003030000000000000000,0,64)] (by decide +kernel) lowS_137)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(16,18),(16,48),(16,80),(16,144),(17,19),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,48),(32,160),(64,65),(64,66),(64,72),(64,80),(96,97),(96,98),(96,104),(96,112),(96,224),(128,129),(128,136),(128,144),(128,160),(130,131),(130,138),(130,146),(130,162),(130,194),(192,193),(192,194),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
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
|5,0=>0xa9bd097c867e6d8478b727e3217754
|6,0=>0xf2cfceca4ddd47ddbdf7da2c9bd2f4b60ebb20faad620a57079b2db96cda95029916dd83c2a83889836fe7dd6f7ba7b6ebc164521636b75ec155c3f355c945232b474594725f42e45402ef38b0d37d682c98f2c3d92b8732a30c27b14279e825d9b20e8d1a65617fec165921018c09517
|7,0=>0xfb715ed006e9df0e9d9ce5ea3df8b0d5f99d0886cdb0acd39dcce68cb51cc1d23bdbc4b09e3afaf2aec60ad917ac5f6aad87a7be1a77c09fd4d9f0339e7629876b95900948a493e7e8f8c88ea808c2c78a9ea86b42858f18422a80aa17df9f7b1127a6a3791ae6d1a66c9ac6c1996bf6464fa0644ae6274460a5a5fa485e2275b1e2597965808d575345572f50ee35067f4e39346bb145e0c401e83d12c3c11f3a73d38c8c34dd934bef3374432b403279d320a6320662ff5f2a54d2a21d29a9a2878f234b221e3f212c71e2301d1691c48f1bf871b1ca1a3ca179b016676165f11635e15e2e158d5158ad1490c11b860e7a20ccda0c99e09e6909d4a069a7066ff050ec02a350193a
|8,0=>0xf8ab8f6d4ef048deea1ceaedfea936e5377e0cf6de9b9da921cfb05ccc4ecc83ecc59cc91f9c61d6c2db8bfbfbbb540b6145b4584b320eb1773acf81ac630ab100aa217a27719ec789d3a59c8639c7a19b8179a6459975496869914228fb278e71f8d1c9899aa88f0988c9587c01865547f5627d8747be2c7add7789e574eed716887093e6e77b6de8c6cc9369ff8681b06785f63b3c628205ca735c7525bc585a8e758b2f571d14ec024e1104da224d36f4c83d4c3a64baee4ac724906147e894775844600411963ffcd3f3913c9ea3b6773af3d3a4cf394c238d2a3703a354af33c44325a930b642fee32f4092b27c2865c285e127c2726d8e24402208d1205f01fa7e1d3a61c3ff19ff81932a183181420213a4e13920136fc123f111f850fdb80ec3b0d4850a9dd09d7f09cfb073890719b06c63060f10604f05be901612
|9,0=>0xe7cd9e6665da7e9d77f1d4598c8ab8c4548c27d3bcc66b61feb4c83ad69e9c9be9396b91fa28f85a8e7548b088876ad870078249c79b4d739e0727c6701b66ca956a04365023626475cb505459751f54514c1501ea4e0714d79e4c48247eb847e7f466d540e333dae93649f3163b3019c2f6942aa7524b9f24a752300a1c20b1abc91a49d11d970f6ef05c100547803c5a022db01f7a01666
|10,0=>0xce221c34dfac435a62c296f85840fe6c0fe411753ecf23e1f9
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f0f0f0f000f00f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0af0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f0a0a0f0f0f0f0f000a000f0f0f0f0f0f0a0a0f0f0f0f0f000a00f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f00f0f0a0a0f0f0a0a0f0f0a0a0f000a000f0f0a0a0f0f0a0a0f0f0a0a0f000a00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|0,1=>0xf0f0f000000000000000000000000000f0f0f0000000000000000000000000000000000f0f0f0f0f0f0f0a0f0f0f0f0f0f0f0af0f0f0f000000000f0f0f0f050505000f0f0f0f000000000f0f0f0f05050500505050505000500050505050500050005050505050005000505050505000500f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0af000f000f000f000f000f000f0f0f0a0f000f000f000f000f000f000f0f0f0af0f0f0f000000000f0f0f0f0f0f0f0a0f0f0f0f000000000f0f0f0f0f0f0f0a505050505050505050505050505050005050505050505050505050505050500303030303030303030303030303000003030303030303030303030303030000f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000050500000505000005050000050000000505000005050000050500000500f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0cf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f00303000303030003030300030303000203030003030300030303000303030002f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a
|0,2=>0xf0f000f0f0f000f0f0f000f0f0f000a0f0f000f0f0f000f0f0f000f0f0f000af0f0f0f0f0f0f0a0f0f0f0f0f0f0f0a0f0f0f0f0f0f0f0a0f0f0f0f0f0f0f0a00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a3030303030303030303030303030302030303030303030303030303030303020000f0f00000f0f00000f0f00000f0a00000f0f00000f0f00000f0f00000f0af0f0f000f0f0f000f0f0f000a0a0a000f0f0f000f0f0f000f0f0f000a0a0a00303010103030101030301010303010003030101030301010303010103030100000000f0000000f0000000f0000000a0000000f0000000f0000000f0000000a00f000f000f000f000f000f000a000a000f000f000f000f000f000f000a000a30303030303030303030303030303000303030303030303030303030303030000f000a000f000a000f000a000f000a000f000a000f000a000f000a000f000a505050005050500050505000505050005050500050505000505050005050500f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0af0f0f0f0a0a0a0a0f0f0f0f0f0f0f0a0f0f0f0f0a0a0a0a0f0f0f0f0f0f0f0a303030303030303030303030303020203030303030303030303030303030202f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a
|0,3=>0xf000f000a000a000f000f000a000a000f000f000a000a000f000f000a000af0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00a0f0a0f0a0e0a0e0a0f0a0f0a0e0a0e0a0f0a0f0a0e0a0e0a0f0a0f0a0e0a0ef0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e000000000000000000000000f0f0a0a0000000000000000000000000f0f0a0a505050505050500050505050505050005050505050505000505050505050500e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e00f000f000c000c000f000f000c000c000f000f000c000c000f000f000c000cf0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a50505050505050505050505050505050505050005050500050505000505050000f000f000f000f000f000f000f000f000f000a000f000a000f000a000f000aa0a0f0f0a0a0f0f0a0a0f0f0a0a0f0a0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0a50505050505050505050505050005000505050505050505050505050500050000000000f0f0f0f000000000f0f0f0a000000000f0f0f0f000000000f0f0f0af0f0f0f000000000f0f0f0f0f0f0f000f0f0f0f000000000f0f0f0f0f0f0f00
|0,4=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f000f0f0f00f0f0f0f0f0c0f0c0f0f0f0f0f0c0f0c0f0f0f0f0f0c0f0c0f0f0f0f0f0c0f0c5050505050405040505050505040504050505050504050405050505050405040000f0f00000f0f00000f0f00000f0000000f0f00000f0f00000f0f00000f00a0a0a0a0a0a0a0a0a0a0a0a0f0f0f0a0a0a0a0a0a0a0a0a0a0a0a0a0f0f0f0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0ad0d0d0d0d0c0d0c0d0d0d0d0d0c0d0c0d0d0d0d0d0c0d0c0d0d0d0d0d0c0d0cf0f0f0f0f0f0f0f0f0f0f0f0f0a0f0a0f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0af0f05050f0f05000f0f05050f0f05000f0f05050f0f05000f0f05050f0f050000000000000000000000000000f000a000000000000000000000000000f000a504050405040504050405040504050405040504050405040504050405040504f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0cf0f0f0f050405040f0f0f0f050405040f0f0f0f050405040f0f0f0f05040504f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c
|0,5=>0xf050f050f040f040f050f050f040f040f050f050f040f040f050f050f040f0400000000f0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f0000000000f0f0f0a000000000f0f0f0a000000000f0f0f0a000000000f0f0f0a303030302020202030303030202020203030303020202020303030302020202d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0c0d0c0d0c0d0c0d0c0d0c0d0c0d0c505050505050505050505050505050505000500050005000500050005000500f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0af0f0f0f050505000f0f0f0f050505000f0f0f0f050505000f0f0f0f05050500000000000000000000000000f0f0f0a0000000000000000000000000f0f0f0af0f0f0f0f0f0f0f0f0f0f0f000f000a0f0f0f0f0f0f0f0f0f0f0f0f000f000a00500050004000400050005000400040005000500040004000500050004000400f000f000f000f000f000f000f000a000f000f000f000f000f000f000f000af0f05050f0f05050f0f05050f0f05000f0f05050f0f05050f0f05050f0f0500f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f000000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000ef0f0f0f0f0e0f0e0f0f0f0f0f0e0f0e0f0f0f0f0f0e0f0e0f0f0f0f0f0e0f0e
|0,6=>0xf000f000f000a000f000f000f000a000f000f000f000a000f000f000f000aa0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0a0a0f0a0a0a0f0a0a0a0f0a0aa0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0e0a0e0a0e0a0e0a0e0a0e0a0e0a0ef0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e00000000000000000000000000000000f0f0f000f0f0f000f0f0f000f0f0f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a00f000f000f000f000f000f000f000f000c000c000c000c000c000c000c000cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f050405040504050405040504050405040000f0f00000a0a00000f0f00000a0a00000f0f00000a0a00000f0f00000a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c00f000f000f000f000f000f000f000f000e000e000e000e000e000e000e000ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e00f000f000f000f000f000f000f000f000a000a000a000a000a000a000a000af0f000f0f0f000f0f0f000f0f0f000f0f0f000a0f0f000a0f0f000a0f0f000a00f000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000505050504040404050505050404040405050505040404040505050504040404
|0,7=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a50505050505050505050505050505050404040404040404040404040404040430303030300030003030303030003000303030303000300030303030300030000000000000000000000000000000000f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c00000000f0c0f0c000000000f0c0f0c000000000f0c0f0c000000000f0c0f0c0000f0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00303030303030303030303030303030302020202020202020202020202020202505050505050505050505050505050505050000050500000505000005050000005000500050005000500050005000500040004000400040004000400040004005000500050005000500050005000500050000000500000005000000050000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e000000000000000000000000000000005050500050505000505050005050500f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000a000f000a000f000a000f000a0000000000f000a00000000000f000a00000000000f000a00000000000f000a00000000000000000000000000000000f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0aa0a0a0a0f0f0f0a0a0a0a0a0f0f0f0a0a0a0a0a0f0f0f0a0a0a0a0a0f0f0f0a
|_,_=>0
def sP:Nat→Nat
|0=>0x78d871e380863a1c78e02180071e3831c2e00d8b0e0c086004838f3404300321c78e02180090e3c701300060b0a0c086002438f2638b802c2438a1c040090e3c7012a00585080c801002ca051e4c080241c78622006050438080182c28a02004870608080101c1810c002840608080
|1=>0xcac0120ea87810c003841e38329003038e0219400181c1810c9c00b0a1050f0200607063832600584871c05280182c3810c900230e3c7062e0060704380860048287143c080441c78e02180120e3c70642010120e0c08600305871404300162438320040090e407013e00b07203809c
|2=>0xcc80071e39c867001b872038086004838a063c086001050f0219a0d00107816ad0680181c701661801b0e3c701640038f1c0433100c03901c04300241d78f021802e3c1c78e0219687083c7010c1c22a2038080101c78e021800c161479302003841e3832c00142021e38080181c701
|3=>0x4800a050e3c98e02020071e380867e01707063c7010c00909143c08d0078d841e380861a5848720380807c1c2101c04300241c7810c9c0071e380bd0c009091ef008d004838a203c086001c2031c0433b00b8d871e38086002ca051e38086002438f1c18b800e3c7010ce80140e3c701
|4=>0x6c383203808600302870638086001c78e8e043003c1050f1c0430d182c3830218046281c78e0218007083c7064c0020320380b51a003c51e3808600b838a1e38086001c20f1c043440014384064070100782031e380861a2c284063c086002c4871e4c080821c78e021800c0e38086
|5=>0x1e043341a00384043c7010c00909140c7811a0038f1c0434c0048383200430036583901c04300181c7010d2c00b121c18f02180090e3c7010c7c0160e3c7010c7000b0e1050f021800c0e2818e0218020181c80e0218007083c7019418004143e48190358071e3808600584871e4c701
|6=>0xc98007203c70138003841e380865000384a63c7010c00384063c0864e0020a063e4819034b230e3c7010c00210a4380b51a004871e38086960024f1e380b51a00384063c7064c004871e380d1002438a1e38080121c7bc1c0400b0e107810c9000c161c79302180500e3c7010c0024e
|7=>0x8287010c00909064008d006c5871e38086005038f1c1a1805c7820f1c0430d361c50f1c04300182c28f1c04300181c78e02199000e3c7010d540049c407016a34004203c7016a3403e121c78e0218007083c7010cac040121c7931c04007083c7010d50016241c80e021800b0e1078e
|8=>0x1e4c0800e1078e02cc300b21c20f1c04300b01c78e021801e083c7010c357071e38086008e0071e38086001c20f1c043570010190920640d2c1c20e0219200ac1c20f1c04300191838f1c0430016243901e38080121c78e02940140e3de0e0c003841e4c7062e01007083c7064200b07
|9=>0x1e380861a0020321240861a0038f1c0435c004848f840430d001078eb60430d00502871e3808600101b61c0430d00b9b841e380861a026920e3c7010c0020f1ce40da1a00487063c7010c020841e380861a009071f08086003020e021920d00b82031e380861a006071438086002c284
|10=>0x1c20f1c0431f003020a06380861a00b090e3c7010c02007083c98e021800b121c78e02180049cd878e021868036101901c0430d001078e8e0430d008c38f1c043000e1078e0219200181c7931c04300083c7010d746808c1c20f1c04300084078e0219a0d001228f1c0430d00b820a
|11=>0x21b08d00107df1c0430d005038f1ce43000e105031e380860080384203c7010c009400e3c7010c002361e380866834004140c78e032068008407010d78680241c79302180200a1c20f1c043000a1c2031e38086002c384063c08600105521c0430d00484901e3808d001278f1c0430d
|12=>0x21b000121078e0344680121050f1c046800e1078e021a5800e1078e0219380361c78e0218009083de0e0234004a4380864834004203e48e0320684c43c7010c34050083c7010c34004a43c7010cd0680082880f1c0640d001078e021a60d001078e032128d0048203200430d001080e
|13=>0xd8068009a878e02186807c1c20f1c04300083c7390da4680084078e027068008281d21c0430d00127831e380861a0020f1c043681a0038f1c04367001c78e0219f80121c80f1c040090e3e10e02180041e38086ca340460a1c20f1c04300080db101c0430d00107c21d9030d001c78e
|14=>0x1a0020f1c0436f1a00a041e383431a00484140c78e023400406da90e02186800e101901c04300083c701dc18680083c701da18680361050f1c0430d004848f2604680281c7931c04300083c7010d5468008287c90218680084078e0368680093c50f1c0430d01b038f1c04300083e10e
|15=>0x83c7010dcc680083c7010dc8680083c7660d0c680161c20f2604300093e90f1c0430d001388f1c0430d00135901c0430d0010793920640d083c701e01868012105101e3808d006c3901e3808600127b61e380861a006050e3c7010c00b07080c7010c004841e380a51a00a041ef0706
|16=>0xe1078e021a1800e1078e0c5c00c0e0c7010c0060414380861a0020f1c043771a0020f1c043761a0020fea380861a02c041e380861a0020f1c043741a00d8406380861a01b920e3c7010c00b07083c98e021800414d878e0218680083c7010cd06805c1078e0218680083de0ecc18680
|17=>0xc80430d001078e021bc0d004820f260430d00107c91ce40861a00203a4380861a03609083c7010c340041f087390c34004d63c7010c340160e1078e0218023083c7010c340041f087660c3400c083c98e0218680161c20f1c043000e1050f1c043000e107bc1c04300161420f1c04300
|18=>0x1a0020f78380861a0020ff8380861a0020f1c0433f1a00484203c7011a0020f1c043431a002521e4c7010c34009083e10e0218680083c7010d806800e107c21c04300361078e0218680083c7010dec680093a90f1c0430d001078e021bd0d001078e021bc8d005020f1ce430d001078e
|19=>0x4848f1c0430d001078e021be8d006c2101e380861a009071e38086001078ec8064061a002361e380861a0020f1c043241a00a041e4c7010c34004063e4810c34007083c98e02180041e4c701903406c083c7010c340400e1078e021800c0e3c7010c0020a1e380861a0020f1c04367
|20=>0xc340041ffc7010c34009083c739023400c080c7010c340046c3c701901868008d880f1c0430d005038f1c04300241080f1c0430d00dc9041e380861a0020f1c0437e1a0020f92380c80c3420f1c043631a0020a063c7010c340041e4c766021868008407c91c0430d001078e021af0d
|21=>0x1078e0218680083c7660218680083c98e0218680281078e02186800e1078e02180041f087010c34004a43c7010c34012083c7010c34004063c7010c340041f247010c3400c083c7010c34007080c78e02180040640701
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x1e60186012600c600660006
|6,0=>0x1587151714a7143713c7135712e7127712071197112710b710470fd70f670ef70e870e170da70d370cc70c570be70b770b070a970a2709b7094708d7086707f70787071706a7063705c7055704e7047704070397032702b70247
|7,0=>0x33e8336832e83277320731973118309830272fa82f282ea82e372dc72d482cd72c582bd82b582ad82a5829d8295828e7287727f8277826f8268726082597251824a7242823b7233822b8223821b8213820c720571fe71f681ee81e681df71d781d071c881c171ba71b371ab81a3819b8193818c7185717d8176716f7167815f8
|7,1=>0x483747c7474846c8465745e7457744f84478440743884308428842084197412740a840283fa83f373eb83e473dc83d483cc83c483bd73b583ad83a5839d8395838d8385837d8376736e8366835e8356834e83468
|8,0=>0x68b9683867c7674866c8664865c8655764d8645863d8635862d8624961b9613860b860385fb85f385ec75e395da95d285c995c095b885b175a8959f9597858f8587857f8577856e9566855d9555854c9543953b8534752c8524851c8514850b950384fa94f284eb74e384db84d384cb84c294ba84b284aa84a2849b7493848a9
|8,1=>0x8908888888088788871786a7862885a8852884a8842883a8832882a8821981898108808880087f887f087e887e087d797cf87c787c077b887af97a7879e9796878e8786877e8776876e8765975c9754874c8744873b9734772c8724871c8714870b970476fc86f486ec86e486dc86d396ca96c286bb76b476ad76a5869d86949
|9,0=>0xa858a7d8a758a6d8a658a5c9a539a4c7a439a3a9a328a2a8a228a199a109a0799ff89f789ef89e699df79d699ce89c689bd99b589ad89a5899d8995898e7986897e8976896e8966895e8956894d9944993c8934892c8924891b9913890b890388fb88f388eb88e298da88d198c988c188b988b188a988a098988
|10,0=>0xad48acc8ac48abd7ab58aad8aa58a9d8a958a8d8
|11,0=>0xadc7
|_,_=>0
def wAt:=mkWire dB 128 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x6191e390e39083508190835203b061b1e3916401e190e19203908351e190c7d0e0e1e390a3d0e1908350839083d06191e390e3908351e390e390835241b083508390e3908351e39083d0e2a06191e390e3908351e39083d06191e390e3d083508191e390e39083508050e190e3908350c3916401e19083d06191e390e390835
|1=>0x8350ce1283b080526051c19081908390839083520391e190e4208351e19083536391819083d0e390e19083508052c070e3d083508196e1b080d08351e390805161b0e3908350835283b08050219183908351e19083d083908351e396c3b200120391e190835244108391e19083d0e190e39083516401e190a0c1e390e190835
|2=>0xe39083506011e3908351e71241b08390829083506191e3916420e3908350e1908351e191e395c03120d08191e390e39083508190e3908350c39090d841b083502390835083d061b1e390e19083508051c19123b08190e0508350829083506191e391e4d1c19081908391e190e3d083508190e0d08351e3908390a3b0e190835
|3=>0x163f0e3908350e39083508191e390e0e08351e39241b0e3d0835083906191e390e390835083d08351e390e4108351e190e0e08351e390c0120391e191c01087d0e0e08351e391c190e3d08350819084108351e191e390e1908351e39083d08350271241b08395c0308291e390e3908351e39083d08050e4d08351c197c07163d
|4=>0xc01123908350819a4391e010819163f0e3908359c1b9c191f251c017c070e0d08351e3908351ce60c0508190619083508191e390835081926051c19061b1e390e39083d083546050835084d1c199e3b9c191f251c0116401e190e3908350619083908191e3908359a1b2405083908351e3908391e1908410e3d08351e19083d
|5=>0x1e190841083520391e190e39083d0e190835083d161b0e390835284f083508051c191f251c019e1b21251e191c012c390e3d083508198c3f0e4d08351c1908191c190e050835403b0a3d0e1908351e190e3d083508397c07163d0835241b083508391e190a0f1e390e191ec9161b0e3908351e390a3b0e1908351c0106191e39
|6=>0x835061b1e395c03244108391e19120d083508191e390835084d1c190c011e391e191c010e3d0835061b1e39083d0e4d08351c190e39083508191e1908190835203b1e192605083508051c192c070e3d08351c1940070a3d0e1908351e4d0e3d08351c1908191e3908391e1908411e190e3908350805841b0835023924410839
|7=>0x241b0839082906191e391e391e191c0108351207081908191c0508390369921b1c010e19083508051f211e390c016e191839083d240508350839921b02191c01083508191e39090d841b0239083908350239083d061b1e39120d08191e39061908351e39083d0e190e3908350c390d2d163f0e3908358c3d0e4d08351c190891
|8=>0x83908350c390a3d0e1908351e390e1908351e390e3908351e0106191e39081908391e1921251e191c010e0e08351e39083d06191e390e3d083508191c190e05083508190e390835a419a4391e011e3908411e190271241b08390835084d1c190835061b1e39083d08351c19082a06191e390e4d08351c196c3b20011e191e71
|9=>0x8350a3b0e190835084108351e19081926051c191e01061b1e391e190c011c011f8d903b0c0108f126051c196c3ba4191e010c0120391e199a1b240508390c01203b1e191e3908391e191e19a43b1e011d81281b0805080508350219083506191e390e4108351e1908390e0508356c3b1f210c0106191e390c011e19080e1e39
|10=>0x6191e3908e508350219281b08050239d61906031e39163d0e3908350c05cc3b0201241b08391e191e0106191e3907211e390c018601841b02390835123f08190835123b0819083508191e190819083502391d92cc1902010a390e19083520011e191e39900502390c01281b083508051ce60c050819061908191e39163f0e39
|11=>0x1c010d79080e1e39203908191e19083508411e191f210c01083d0e1908350e3d08351e39203b08191e19080526051c19363b1819083d0d0a08050239061908191e391e39a4191e0108351e191e390d85a43b1e010da5cc3b0201203908411e191c1908190839083508051c19284f08051c1920391e191c011e19921b1c011401
|12=>0x1e39083d083d06191e39279a1c190201a44f1c191e01780126051c190891061b1e3907231e390c01123d08191e390835243d08390e3d08351c19200120391e196c3b1f210c01244108391e19020126051c194a01203b1e19244208391e190201841b02390e3908350c399c19a4391e01140306191e391e1906031e391c190c01
|13=>0x841b02391c191e0102390819281b0805083502391819083d090a0239a4391e011f261c0190070c0108050219cc190201a41b1e0108390c3902191c011e391e01120508190219023906031e390e3d0835084d1c19023902011c19083d0e390835083506191e39083526051c190e190e390835841b083502392c070e3d08350835
|14=>0x1f210c0120011e190835080508391e19243d0839cc1b02010c011c01903b0c0106191e391c1902011e191c01080e1e39081908392407083908411e190835083990050c011f210c01061b1e3908051c191e391c0108351c190c390c01120508190e0508350835083d06191e39123f081926051c1984030239123b081908191e19
|15=>0x2011c190805083502391e0108391e391c01083d08351e391e191e3992191c010c0508191e39083d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x5200140000000000
|6,0=>0x4a40000000000046400004420000404000000000003c400003930dc80000d483140b8c0000a90255088c00007cc000000000006d0000060c000051000003d4000030c075
|7,0=>0x4d913244b912a4499122448091d3465115444510d442510544050fd43e50f633c90ee43acce83394ce143750d943550d143350ca33190c242f90bc22e10b442c4cad42a8ca7328d09f426d097424d08f422d000021d084320107c41e107441c4c6d41a5065418505d41650554148c4e4
|7,1=>0x7351c947151c146f51b946d51b230001ae46a900006991a2467919a4659192463918a461918245fcd7b45dd17345bd16d25a5165458515d45651554548d4e452cd47450d13f44f0d3a2
|8,0=>0xa38e8b3a20e853a08e7f39f0e7939d8e7339c0e6d39a8e673990e613978e5b3960e553948e4f3930e493918e433900e3d38e8e3738d0e3138b8e2b38a0e253888e1f3870e193858e133840e0d3828e073810e0137f8dfb37e0df537c8def37b0de93798de33780ddd3768dd73750dd13
|8,1=>0xd34f4a3d1cf443d04f3e3cecf383cd4f323cbcf2c3ca4f263c8cf203c74f1a3c5cf143c44f0e3c2cf083c14f023bfcefc3be4ef63bd0af13bb8eeb3ba0ee53b88edf3b70ed93b58ed33b40ecd3b28ec73b10ec13af8ebb3ae0eb53ac8eaf3ab0ea93a98ea33a80e9d3a68e973a50e913
|9,0=>0x3c82f18bc42f08bc02ef8bbc2ee8bb82ed8bb42ec8bb02eb8bac2ea8ba82e98ba42e88ba02e78b9c2e68b982e58b942e48b902e38b8c2e28b882e18b842e08b802df8b7c2de8b782dd8b742dc8b702db8b6c2da8b682d98b642d88b602d78b5c2d68b582d58b542d48b502
|10,0=>0xf4c7d21f447d01f3c7ce1f347cc1f2c7ca1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 14
def pmP:Nat→Nat
|0=>0xa2b0000000028040000000044000000000107d000000003210000000008a400000000223000000000884000000001018000000004040000000010040000000028800000000083000000000140000000000420000000001000000000003080000000008400000000014000000000048000000000100000000000200000000000400000000000c00000000002800000000008000000000018000000000050000000000100000000000200000000000400000000000
|1=>0x1510dc00000044040000000101024000000400c600000010011000000028042000000090300000000144290000000310300000000c0000000000210000000000800800000001f3fc00000007cdd00000001f1f400000007c5d00000001e2f40000000787d00000001d1f400000005c7f0000000171f4000000054ff0000000153f40000000547f0000000151f4000000041480000000101f40000000400c0000000100180000000400000000000b23000000002c5e
|2=>0x401d1740000100705e0000040151f40000080907e0000020159fc000008054dd0000020151f40000080545d0000020149fc000008050fd0000020141f40000080125e000002001978000004086be0000010100300000040029f0000010000300000040000800000100001800000400002000000e101f400000380414000000e000600000010547d0000004010300000008c07e0000002101a4000000670560000001971fc0000006547f0000001913100000006004e
|3=>0x400048000000a0010800000220041700000800d67f00001481d174000052054fd0000148151f4000052050ff00001480a07400004a0547d00001081f1740000420747d0000108153fc000042054fd0000108151fc0000420547d0000100301f80000400907e0000100161700000400547d0000100151740000400505c00000e0141780000200107d0000050141fc0000130001800000491d1fc0000124507f00000481d1f40000120547f0000048151f4000010074da
|4=>0x4018158fc001006000040004011171fc0010040567f0004010151fc001004006bf00040001016400084205c7f0002108171f40008408405c00020451d1fc0008110747d00020441d1740008110707f0002044090300008110200c00020101217800080005c7f0002000171f400080005c5d0002000153fc000800054fd0002000151fc0008000547d000200002178000800000470001000001100002380567f00008a0151f40002040120000004001002000010004000
|5=>0x400401f3740100038547d004000e010500100038001400400040103001000007cfd00400001f3b401000007cdd00400001e3f401000006c8800400001a2a00100000547d00400000b230010000028ac0040000000b0010000000050020000040100040880d07f0010020153fc004008054fd0010020151fc0040080547d0010010041f80040000547d0010000041f80020a80547f0008280151fc0020a0014840008068141fc0020000100000060101000000140025c7f
|6=>0x800000000201011000808c040440015af41010040863f0402000351fc1000020023d04000018951c1000002e1440400000358fc0900000547d024000010200090000000240240000000200900000000101808a015bfc060228054fd018008015374060000054d101100e0151f40440320547d01000e8151f4040020056da0100060151740240620547f00881a8159fc0202780545d00808e0151f40202080547d00800a0159fc0200280547d0080020151f40200000547d
|7=>0x4000020153f50000080547d4000000151f4c0000005c7d2a000001d1f4a000000747d28000001c1f4a000000202c2000000171f4800000054fd2000000151f4800000050fd1a000001c0f4680000054fd1a00000151f46800000281d1300820151f44800000787d12000001d1f448000005c7d1200000151f4410000078bd1000000151f44000000507d0a00020151f4280000054fd0a00000000202000000703d0800000161f42000000547d0800000100302000000002c
|8=>0x8000001550fd2c00000547d
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x2028000000
|6,0=>0x2800000002000020001c000000014000b010000407048001805018002400000000600048000600078000613
|7,0=>0x4052408344a1525a8800f01d84100512f14c2c1d1e1dc9e540511c10a15380c0885401f82240271a86a851b0687c034f3487a6930328980e340042e1b2e1b50c991180c4c4d0f0e8062f228e520083700d1e7f1c00cde4a110d00c03280710e1457998640022215b4a9670640c49098fc8c823ea5830b0
|8,0=>0x19b45b8c380a3970fd7a964562b49a6082b113af8ac2d1695534d55a0b9e42b5b255a6db2197cb4482c085f0317abf5767a56aa1d4e86a15cb42b50158d6b272b00c86732a10b2de7c1555cc95fa6dae9267b8de6e22cb856a59721d5e8a82d885b2a56f87c60736c0dd3ab73db5858b3212913e24489b0f02c45ad1bae0362f5dca3633a4f8f95e321d0626031d1866
|9,0=>0x2c18bc9968d7dbe956744bbf9e2e25cbfdda2b3c9d92871803e856ac760a9cccd53225746168310ba6360bd98aaa61a5184fc75b9cb2597a9c9def76620c56423d165149c
|10,0=>0x1fc29550a182f5380add688
|11,0=>0x27
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 46 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_187 10 roots_187 ops++addP pm 1 dom_155 7 roots_155 ops++addP pm 2 dom_250 9 roots_250 ops++addP pm 3 dom_243 9 roots_243 ops++addP pm 4 dom_91 8 roots_91 ops++addP pm 5 dom_123 9 roots_123 ops++addP pm 6 dom_233 8 roots_233 ops++addP pm 7 dom_242 7 roots_242 ops++addP pm 8 dom_170 5 roots_170 ops++addP pm 9 dzo_153_2 5 roots_153 ops++addP pm 10 dom_219 9 roots_219 ops++addP pm 11 dom_227 6 roots_227 ops++addP pm 12 dom_249 9 roots_249 ops++addP pm 13 dom_234 6 roots_234 ops++addP pm 14 dom_235 9 roots_235 ops++addP pm 15 dom_186 7 roots_186 ops++addP pm 16 dzo_233_2 6 roots_233 ops++addP pm 17 dom_137 4 roots_137 ops++addP pm 18 dom_171 8 roots_171 ops++addP pm 19 dom_195 4 roots_195 ops++addP pm 20 dom_202 4 roots_202 ops++addP pm 21 dom_210 5 roots_210 ops++addP pm 22 dom_179 7 roots_179 ops++addP pm 23 dzo_249_2 7 roots_249 ops++addP pm 24 dom_218 6 roots_218 ops++addP pm 25 dzo_217_2 6 roots_217 ops++addP pm 26 dom_211 6 roots_211 ops++addP pm 27 dom_153 5 roots_153 ops++addP pm 28 dom_178 5 roots_178 ops++addP pm 29 dom_240 5 roots_240 ops++addP pm 30 dom_163 5 roots_163 ops++addP pm 31 dom_203 7 roots_203 ops++addP pm 32 dom_147 4 roots_147 ops++addP pm 33 dom_185 8 roots_185 ops++addP pm 34 dom_217 6 roots_217 ops++addP pm 35 dom_177 5 roots_177 ops++addP pm 36 dom_226 4 roots_226 ops++addP pm 37 dom_241 6 roots_241 ops++addP pm 38 dom_248 6 roots_248 ops++addP pm 39 dom_114 5 roots_114 ops++addP pm 40 dom_154 4 roots_154 ops++addP pm 41 dom_122 6 roots_122 ops++addP pm 42 dom_115 6 roots_115 ops++addP pm 43 dom_107 6 roots_107 ops++addP pm 44 dom_121 6 roots_121 ops++addP pm 45 dzo_201_2 5 roots_201 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_153_2_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_233_2_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_249_2_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_217_2_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_zo_201_2_137 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_187 10 s (0,roots_187.map (·&&&dom_187)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_187 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 6 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 45 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 106 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 106 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 61 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 61 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 10 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 10 0 = true)
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
def isoMvS_223:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_iso_b isoMvS_223 (by decide +kernel) lowS_127
def isoMvS_253:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_251
def isoMvS_254:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 11:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_247
def dzo_171_4:=0xf0f00000f0f000000000000000000000f0f00000f0f0
def gzo_171_4:=0xf0f00000f0f000000000000000000000f0e00000a000
def gsh_171_4:=0xf0f00000f0f000000000000000000000f0e00000a00
theorem lowS_zo_171_4_43:Lower true dzo_171_4 roots_171 gzo_171_4 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_4) [(dom_171,4)] (by decide +kernel) (lower_slice_b (T:=gsh_171_4) [(0xf0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_43)
def dzo_205_2:=0xcccc000000000000cccc000000000000cccc000000000000cccc
def gzo_205_2:=0xcccc000000000000ccc8000000000000cccc0000000000008800
def gsh_205_2:=0x3333000000000000333200000000000033330000000000002200
theorem lowS_zo_205_2_141:Lower true dzo_205_2 roots_205 gzo_205_2 6:=lower_iso_b (d1:=dom_205) (r1:=roots_205) (T1:=gsh_205_2) [(dom_205,2)] (by decide +kernel) (lower_slice_b (T:=gsh_205_2) [(0x3333000000000000000000000000000033330000000000000000,0,64)] (by decide +kernel) lowS_141)
def dzo_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0
def gzo_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000a000
def gsh_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000a00
theorem lowS_zo_235_4_43:Lower true dzo_235_4 roots_235 gzo_235_4 7:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_4) [(dom_235,4)] (by decide +kernel) (lower_slice_b (T:=gsh_235_4) [(0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000,0,64),(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_43)
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0f00000f0e00000a000
def gsh_107_4:=0xf0f00000f0f00000f0e00000a00
theorem lowS_zo_107_4_43:Lower true dzo_107_4 roots_107 gzo_107_4 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_43)
def dzo_157_2:=0xcccccccc000000000000000000000000cccccccc
def gzo_157_2:=0xccccccc8000000000000000000000000cccc8800
def gsh_157_2:=0x3333333200000000000000000000000033332200
theorem lowS_zo_157_2_141:Lower true dzo_157_2 roots_157 gzo_157_2 6:=lower_iso_b (d1:=dom_157) (r1:=roots_157) (T1:=gsh_157_2) [(dom_157,2)] (by decide +kernel) (lower_slice_b (T:=gsh_157_2) [(0x3333000000000000000000000000000033330000,0,16)] (by decide +kernel) lowS_141)
def dzo_173_2:=0xcccc0000cccc00000000000000000000cccc0000cccc
def gzo_173_2:=0xcccc0000ccc800000000000000000000cccc00008800
def gsh_173_2:=0x33330000333200000000000000000000333300002200
theorem lowS_zo_173_2_141:Lower true dzo_173_2 roots_173 gzo_173_2 6:=lower_iso_b (d1:=dom_173) (r1:=roots_173) (T1:=gsh_173_2) [(dom_173,2)] (by decide +kernel) (lower_slice_b (T:=gsh_173_2) [(0x33330000000000000000000000000000333300000000,0,32)] (by decide +kernel) lowS_141)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,28),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,18),(16,20),(16,48),(16,80),(16,144),(17,19),(17,21),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,48),(32,160),(36,37),(36,38),(36,44),(36,52),(36,100),(36,164),(64,65),(64,66),(64,68),(64,72),(64,80),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,132),(128,136),(128,144),(128,160),(130,131),(130,134),(130,138),(130,146),(130,162),(130,194),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|7=>71
|8=>437
|9=>439
|10=>176
|11=>41
|12=>7
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xfa7c6d554acdcf4c5692a30c9a0be0a0bc49d4e092f7f8d99f8d54d8bdc889ab07b4e26ef496d3776c80e65510610f25e3345c7df5c22b53b5a4f9184f4b24c75e43947426b438572372de37254338292ee502d7d72d6f028f5227167266d1252a124b7423863230eb1def11ced7193791906a155dc1361d1243011525107c3103ba0ff270fc670f4a00eb830aed009c3508680079ac05ae3050e704e8d04d2c048f4043c603e420371302ed20121a008a2
|8,0=>0x18c871883618588184b0180f017efe17e0e17c9d178d1178c817533173fe173121715516ec81673b1650a15dac15d8c158d6158b81524114c8c14c0d1450314345142f4142cc14282138391312912e9112e7812e3a12d5412a2c129a312931126ee126d012552121c2118a810e47109c51095010737103ee102d00ff700efbd0ebad0eab60e6b50e53f0e3980e0b40e0740e0440db530d7f20d6080d3940d2710d1c60ce170c9f30c7880bc270bb8e0baa20b7430b6920b4cc0b33c0b1bb0afda0ad830a9be0a9660a83f0a58a0a11d09f38095bb093d4091f1082f60815f08037079150779d0769f06eba06c9806aa40683e0658d0600605ae30573c05620054e20504f04f5d04f0e04730044e10444d043c1042920416603e7f03c5203726035ee035aa0355102ff202e9e02d8302895027660260e01b5c01876011cc00971
|8,1=>0x3910c3892238788386e93861b37db937970372fe36905368303657d3634c3609835b0835982358c5352c1349fc3493d342ed33e0233ce63376533694330d532d3b32c2e32a4932a22329e33241931a5b31905314e6311553073c302c0301ce3018f2ff952f8082f7572f30d2f2422eddd2ecf32ecc42e83a2e7f32e3df2e14e2d7ad2d6122d2762d1d02ca4c2c5522bf6a2bd1a2b6322b58e2b4282a7092a5e72a3e32a34b29bf829b4029ace299472958f294e6294df2946828f52287042860c27f2627e24275b826818267b726594259a725907257ec2571f256ae254902501224e58246982459a23d7c23d442327922f6e223be21f5b21ec0212dd20186200a01fe101ec701ebd71e3091ded21dba61d96d1d5a81cf371cb091c5331bd7a1bb441baeb1b1101adfa1ad061abce1a59f1a1df1a0c919f0619e34199f21932a
|8,2=>0x8783786f6c85b22833a380b957f1497e2d47cf737c7d07b7ac7a96578c50781d57495571e0d71720714c270e0470b88702f96ef536e3206db046d08f6b6116b51969d59696f06861066d7f6595d6532d64ed064bcf6467264424641726322b61eec618e661036605ec5df135d9f65cfd65cf9e5bfe45b99e5b3205aece5aa6c5a3e358ecf57a9d5781f563305595d557e155360545835423f5396c538955370352c4d52a705118850d6e50989508e850779506764fe544f88b4ed224e6524e2924e08f4e0714cc1a4c87e4c2214bf9a4adc04a9e84a4d74a49449454492fb48008477ca4733046ee746a9246970454cb449a343e3243d9c438ae42c034261a421e8420df4209a4187240f4840dc940da140ae1408f43f66b3f0c73e42b3e4203e3403cf743cebd3c4ab3c0a43bdf73b66d3b5463b5233b3763b23339cb3396b1
|8,3=>0xeb03de540eda64bd83cfd673ac67fbc6728c546ec2d25c1b98bd31fbb733baff9b9f2fb72a9b20cdae066adeb2ad81bad70eac924ac4f8ac254aaf6baac3ea9e1ca80e1a65dba6100a5c91a2e739c8329c76b9bebc9994398ad1987ec9711c96c81960509565695137905f68c57b8b3f68ad0a8a94389dda88dcc88d3b887d987f9587bdb
|9,0=>0x16aeb1664c1658f164f9161361613415fa6155ca154b2153dd151c814cf614c3e14c0d14a191461e13d7913bfa139c8134b2134711312912a22129e81266012529114a31141010fcf10ab71093610928107df101ef100b20f3d70f0320efc60eefd0ed3d0ec8b0eb8c0de920dbc40d6270d4610d16b0cb790cb630c3d70b9b90b8660b7710b5f60b3ef0b08f0b0540af100aebf0ae960ae3d0aa8d0aa550a12309e9709afa099b00979f09517092f0090b90904308f1f0898008903084cc082d30823e081790814907e1707cc90737606e6106d91069bb0695605f7005dfb0568d056500537a0524604ffd04cad04c3304a6b04998048f8048cb04628045fa0459504520044a1040d0040240383a0366c03253030c40233401f1e01e60017a30144d012ed012aa010cc00f1000a2000971007030059900493003fd003590010b
|9,1=>0x3a9223a5423a5113a1c639b6a398253905838c753853b383a53835937c32369aa3625a35dff35c3235c17353cd35363353253506834cb7346e53455e33a7b32d02329cb3264931e6231a2e317f9306f43036e301ff2f0172efaf2ed192e7b92d8be2d87e2d1da2d0a12cf0c2c6802c2152bd782bc1e2b0ff2b0592ab272a8682a0e929e4a29ab5295c228fa828fa728f8f2862e281dd27baf277752760526b5126675264fa25fcf25d9025b5225899250ec246f8244012406a2379e2365022c5c22ac722642223e621f2621c34219f3212dd212cd20dfb20ce3207ca205552045d1fb811f61d1f6091ed051ecb81ecae1eb5a1e6e31e0ec1df701d95f1d6a31d5411d17e1ce0f1c7271c5681c49c1c2301c1981c0881c0381bc441aad01a7bd1a5ab1a3a81946118cef18a54186ce18218181e717fc417aa3176fa176b416e28
|9,2=>0x807967d00d793f678bc978bb6786d27861b77cf8779be772337539972d67724da71fd17104a7070b7008e6fc2b6f3286efc46eca96e2146daec6d9086d3a16ca8d6ade96a8bd6a3c769873685aa67f7d67eb067dfe677dd67080664ea664a2631d96257b6235e6165d6147d61090602fe5e8355e6a55d6295d3815ce125bc945b5f25b4d05a6345a2445a01e5901058ddf57ffc57b15561515530b550dc5502554cda546475305152faf52e0250fe45066f504014ff494f9aa4e6ec4d0814ce564cdec4cbc74b74a4b2704afdc4a8b54a7e84a2bd49ccf49cbc496524875b481564801846f8c46b9f45fd545eb845cce45c444592c456f1450b644dc344d4944bdb44701445a54433e44037437d5434c54262a425514209241cab4139e40e6840e2b40d3b40b973fc523faed3f81e3ef2c3e9763e79b3da823cd2c3c91d3acd0
|9,3=>0xfe4c3d944bd4232d3833d2f9ad16e6d0d4fcd092c67fbc2cc5bcb86bb274b9221b7596b6448b17cab00e6ad058ac2cda6e28a5e07a4d4ea4747a382ea269da0c959dcc19adcd9a9ad9a717999439976998f46985ce96e5d951a894772936b992df492d10928729221791b25907d6900968edbf8d6508c48c88b23886e9864918643e835438149780d5d
|10,0=>0x511af505f74f12a4e44d4e2ce4dd454b57348a4b4854c47a9646f5b46f45443db43ecd438514323242f31421e14142c4137a3ff7a3fd553ee0a3dd833d5033c8123ab173a1d539f8a39e92397a938d1736f8536dd135e7a34bf7332d632079315d52dbd62cad02bcb82b9712b2b62b1852b0ab2a61b2949d28b342861b282df27aa4261ea2617925c3425adb2554524d0f24a4f244592338d22c19228442260c21fab2003a1fbba1ed741ed461e7fd1e7a91e0261dd601d7151d4201bb571b89d1adbf1aa501a94a1a3ab189d1174ea14eaa14c4413a791363313096114a3110be10a9e0fd780f9100e8920de8a0db5e0d85b0d7a40c3480c2560bfed0b4320afcf0a93f08dac08888085d4067180657d0628305aed0516b04f1d04d8204a8704827043b403ec903a58037ee037a3035bc0319b0118b0112800c3c008fe00878
|10,1=>0xf871beed0ceceafda172cfdd0ccbb2cae57bbe69b5084b0edfad13fac6b1a9aa4a534fa263c9e2688be428bb728b4ab89516870218465e80be77cee879afe78ba676d657528f73fe16da166d957685c167bf1672ca63acf62efe62778611a1607f95eeac5de8e5766754e73540b253a9752b60529bd51f43
|11,0=>0xebd96debebb4dc7b2e77b054ba644ba27fa854996e56e678f262d8661dd3615915365d5361552c7250c194a3c2472873ab61397853936636ac735ccc35a2c3570c3072b2cc2d214fe1bbff1b7741931917aaa131f11308811fae0ef310abfe089aa01c3201913
|12,0=>0xe9668d709b9736a8f4ad7ec6312dcb11ebd
|13,0=>0x4766c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x5500555555005555550055555500555555005555550055555500555555005500ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000ffffffff000000000000000000000000ffffff00ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f03333111133331111333311113333111133331111333311113333111133330000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|0,1=>0xffff5555ffff5555ffff5555ffff5555ffff5555ffff5555ffff5555ffff00005555555555555555555555555555555555555555555555555555555500000000ffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000ffffffffffffff00ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffff00ff00ffffffffff00ff00ffff0000ff000000ffff0000ff000000ffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffffffffffffffffffffffffffffffffffffff00000000ffffffff000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f00ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000
|0,2=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0affffffffaaaaaaaaffffffffaaaaaaaaffff0000aaaa0000ffff0000aaaa0000ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff003333333333333333333333333333330033333333333333333333333333333300ffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaa000000000000000000000000ffffffff000000000000000000000000ffffaaaaffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaa3333333333333333333333333333333333333333333333333333333333333300000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa
|0,3=>0x33333333030303033333333303030303333333330303030333333333030300000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00ffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff00003333333333333333333333333333000033333333333333333333333333330000ffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaffffaaaa333333333333333333333333333322223333333333333333333333333333222200ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aaffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff000f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000033333333333333330000000000000000333333333333333333333333333322223333333333333333333333333333333333333333333333333333333333330000ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffff0f0faaaa3333333333333333333333333333333333333333333333333333333333332222
|0,4=>0x33330033333300333333003333330033333300333333003333330033333300220000000000000000ffffffffffffffff0000000000000000ffffffffffffaaaa0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000000000000000ffffffffffffffff0000000000000000ffffffffffffff0000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffff0000aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00aa5555555555555555555555555555555555115511551155115511551155115500ffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff0000ff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ff0000000000000000000000000000000000ffffffffffffff00ffffffffffffff00ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffff0000aaaa000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000000000000000000000ffffffffffffffffffffffffffffff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff005555555555555555555555555555555555555555555555555555555555555500afafafafafafafafafafafafafafafafafafafafafafafafafafaaaaafafaaaa
|0,5=>0xccccccccccccccccccccccccccccffffccccccccccccccccccccccccccccffcc0f0f05050f0f05050f0f05050f0f05050f0f05050f0f05050f0f05050f0f00000000555500005555000055550000555500005555000055550000555500000000ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0b0b0b0b0b0b0b0b0b0b0b0b0b0b0a0a0000000000ff00ff0000000000ff00ff0000ffff00ffffff0000ffff000000005555555555555555555555555555555555555555555555555555555555550000ffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff000000000000000000000000000000000000ffffffffffffffffffffffffffffaaaa0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f00555555555555555555555555555555555555555555555555555555555500550000000000000000000000000000000000ffffffffffffaaaaffffffffffffaaaa00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffaaaaffffffffffffffffffffffffff00ff00ffff0000ffff0000ffff0000ff0000003333333303030303333333330303030333333333030303033333333303030300
|0,6=>0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaa5555555555555555555555555555555511111111111111111111111111110000ffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00ffffffffffff0000ffffffffffff0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000ffff0000000000000000000000000000aaaaffffffff00000000ffffffff0000ffffffffffff00000000ffffffff0000aaaaffffffffffffffffffffffffffffffff0000ffff0000aaaa0000ffff0000aaaa000000000000000000000000000000000000ffff0000aaaa0000ffff0000aaaaffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000aaaa0000000000000000ffffffffffffffff0000000000000000ffffff00ffffff00ffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffff0000000000ffffffff00000000ffffffff00000000ffffff0000000000ffffff000000000000000000000000000000ffff0000000000000000000000000000ff00
|0,7=>0xff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffffff0000000000000000ffffffffffffff0000000000000000000000000000000000ffffffff00000000ffffffffffffff00ffffffffffffffffffffffffaaaaaaaaffff0000ffff0000ffff0000aaaa00000000000000000000ffffffffffffff000000000000000000ffffffffffffff0000000000ffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaaffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffff0000000000000000000000000000000000000000000000000000ff00ff00ff0000ffffffffffffffff0000000000000000ffffffffffffffff00ff00ff00ff0000ffffffffffff0000ffffffffffff0000ff00ff00ff000000ff00ff00ff000000ffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffff00ffffffffffffffffffffffffffffffffffffffffffffaaaaffffffffffffaaaaffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaccccccccccccccccccccccccccccffffcccccccccccccccccccccccccccceeeeffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa
|0,8=>0xffff0000ffff0000ffff0000aaaaffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000aaaaffffffffffffffff0000000000000000ffffffffffffffffffffffffffffaaaaffffffffffffffff0000000000000000ffffffffffffffffffffffffffffff000000000000000000ffffffffffffaaaa0000000000000000ffffffffffffaaaaff00ff00ff00ff00ffffffffffffff00ff00ff00ff00ff00ffffffffffffff000000000000000000ffffffffffff00000000000000000000ffffffffffff0000ffffffffffffffffffffffffffffffffff00ff00ff00ff00ffffffffffffff0000000000ffffffff00000000ffffffff00000000ff00ff0000000000ffffff0000000000ffffffff00000000ffffffff00000000ffffaaaa00000000ffffaaaa00ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000ffffffffffffffffffffffffffffaaaaffffffffffffffffffffffffffffaaaaffffffffffffffffffffffffffffffff000000000000000000ff00ff00ff0000ffffffffffffffffffffffffffff0000ffffffffffffffffff00ff00ff0000000055005500550055005500550055005500550055005500550055005500000000ffffffffffffffff000000000000ffffffffffffffffffff000000000000aaaa
|0,9=>0xffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00ffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ffffff000f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f00aaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffaaaaaaaaaaaaffffaaaa0f0f0f0f0f0f0f0f0a0a0a0a0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0f0f0a0a0000000000000000000000000000000000000000000000000000ffff0000aaaaffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffffaaaaffff0000ffff0000ffff0000ffff0000ffffffffffffaaaaffffffffffffaaaaffff0000ffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffaaaaff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff00ffff0000ffffffffffff0000ffffffffffff0000ffffaaaaffff0000ffffaaaa0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0a0abbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaabbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaaffffffffffffffffffffffffffffffff33333333333333333333333333330000ffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00aaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaa
|0,10=>0xff00ff00000000000000000000000000ff0000ff00ff00ff00ff00ff00ff00ffffffffff00ff00ff00ff00ff00ff00ffffff0000000000000000000000000000000000ffffffffffff0000ffffffffffff0000ffffffffffffffffff00ff00ff00ff00ffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffff00ffffffffffffff00ffffffffffffffffffffaaaaffffaaaaffffffffffffffffffffaaaaffffaaaa55555555555555555555555555555555555500005555000055550000555500003333003333330033333300333333003333330033333300333333003333330000000000000000ffff000000000000ffff000000000000aaaa000000000000aaaa00000000ffffffff00000000ffffffff00000000ffff000000000000ffff00000000ffff0000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff00ffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0000ffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffffffffffffffffffffff0000000000000000ffffffffffffaaaaffff0000ffffffffffff0000ffffffffffff0000ffffff00ffff0000ffffff00
|0,11=>0xffff0000ffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffff00ffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaaffffaaaa000000000000000000000000000000000000000000000000ffffffffffffaaaaaaaaaaaaaaaaaaaaffffffffffffaaaaaaaaaaaaaaaaaaaaffffffffffffaaaa00000000ffffffff00000000ffffffff00000000aaaaaaaa00000000ffffaaaaffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00aa00000000ff0fff0f00000000ff0fff0f00000000ff0fff0f00000000ff0fff0033333333333333330000000000000000333333333333333333333333333333000000000055555555000000005555555500000000555555550000000055550000ffffffff55555555ffffffff55555555ffffffff55555555ffffffff55550000ffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffaaaa0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0a0affffffffffffffffffffffffffffffff00000000000000000000ffff0000aaaaffffffffffffffff0000000055555555ffffffffffffffff0000000055550000ffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ffffaaaaffffffffffffffffffffffffffff0000aaaaaaaaaaaaaaaaaaaaaaaaaaaa0000
|0,12=>0x3333333333333333333300003333000033333333333333333333333333332222ccccccccccccccccccccccccccccffffcc00cc00cc00cc00cc00cc00cc00ff00ffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffff00ffffff000000000000000000ffffffffffffffff0000000000000000ff00ff00ff00ff00ffffffffffff0000ffffffffffffffffffffffffffff0000ffffffffffffff0000000000000000000000000000000000ffffffffffff0000ffffffffffffff000000555500005555000055550000555500005555000055550000555500005500ffffffff55555555ffffffff55555555ffffffff55550000ffffffff555500000000000055555555000000005555555500000000555500000000000055550000ffffffffffffffffffffffff55555555ffffffffffffffffffffffff5555000000000000ffffffff00000000ffffffff000000000000000000000000ffffff000000000000000000ffffffffffffffff0000000000000000ffffaaaaffffaaaaffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffaaaa00000000000000000000000000000000ffffffff00000000ffffffffffffaaaaffff0000ffff0000ffffffffffffff00ffff0000ffff0000ffffffffffffff0000000000ffffffff00000000ffffffff00000000ffff000000000000ffffff00
|0,13=>0xffff0000ffff00000000000000000000ffff0000aaaa000000000000000000000000ffffffff000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000ffffffffffff00005555555555550000555555555555000055555555555500005555555555550000000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00000000000000000000ffffffffff00ff000000000000000000ffffffffff00ff00ffffffffffffffffffffffffffffffff0000000000000000ffffffffff00ff00ffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff000000ff000000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000ffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff0000000000000000ffff000000000000ffff000000000000ff00000000000000ff00ffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0a0a000000000000ffff000000000000ffff000000000000ffff000000000000ff00ffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffff000000000000000000000000000000000000000000000000005555555555550000ffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffaaaa
|0,14=>0xffffffff00000000ffffffff00000000ffffffff00000000ffff0000ff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffff000000000000000000ffff0000ffffffff0000000000000000ffff0000ffffff000000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff0000ffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff000000000000000000000000000055555555000000000000000000000000555500000000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa0000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff000000000000000000000000000000000000aaaaaaaaaaaaaaaaffffffffffffaaaa0000000000000000ffffffffffffffff0000000000000000ffffffffffff0000ff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffff0000000000000000000000000000000000ffffffffff00ff00ffffffffff00ff00ffff0000ffff0000ffff0000ffff0000ffffffffffffff00ffffffffffffff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ff00ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ff00
|0,15=>0x5555555555550000555555555555000000000000000000000000000000000000ffffffffffffffffffffffffaaaaaaaa00000000000000000000000000000000ffffffffaaaaaaaaffffffffaaaaaaaaffff0000ffff0000ffffffffffffaaaaffff0000ffff0000ffffffffffffaaaa0000000000000000ffffffffaaaaaaaa0000000000000000ffffffffaaaaaaaa5555555555555555555555555555000055555555555555555555555555550000ffffffffffffffffffffffffffffffff55555555555555555555555555550000000000000000000000000000000000000000000000000000ffffffffaaaaaaaa0000000000000000ff00ff00ff00ff000000000000000000ffffffffffffff000000000000000000000000000000000000ff00ff00ff000000ff00ff00ff000000000000000000000000000000000000ffffffffffffffffffffff00ffffff00ffffffffffffffff000000000000ffffffffffffffffffff000000000000ff000000000000000000ffffffffffffffff0000000000000000ffff0000ffff0000000000000000000000000000000000000000ffff0000ff000000ffff0000ff00ffffffffffffffffffffffffffffffff0000ffff0000ff000000ffff0000ff00ffffffffffffffff00000000ffffffffffffffffffffffff00000000ffff0000
|1,0=>0xffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ff00ffffffffffffffff0000000000ff00ffffff0000ffff00000000000000ff0000ffffffffffffffff00000000ffffffffffffffffffffffff00000000aaaaaaaa00000000000000000000000000000000ffffffffffffffffffffffffffff000000000000ffffffff00000000ffffff0000000000ffffffff00000000ffffff00ffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffff00ffffffffffffffff0000ffff0000ffffffffffffffffffff0000aaaa0000aaaa00000000000000000000ffff0000aaaa00000000000000000000ffff0000aaaaf0f0f0f0f0f0f0f0f0f0fffff0f0fafaf0f0f0f0f0f0f0f0f0f0fffff0f0fafa0000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff000000000000000000000000000000000000000000000000000000ffff0000ff00ffffffffffffffffffffffffffffffff0000000000000000ffffffffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffff000000000000000000000000000000000000000000ffffffff00000000ffffff00ff00ff00ffffffffff00ff00ffffffffff00ff00ffffff00ff00ff00ffffff00ffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00ffffff00
|1,1=>0x333333333333333300000000000000003333333333333333333333333333000000000000000000000000000000000000ffff0000ffff0000ffffffffffffff00ffffffffff00ff000000000000000000ffffffffff00ff000000ffff0000ff00ff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff00ff0fff00000000000000000000ff00ff00ff00ff000000000000000000ff000000ff0000ffffffff00000000ffffffff00ff00ffffffffff00000000ffffffff00ff000000000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff000000000000000000ffffffffffffffff0000000000000000aaaaaaaaaaaaaaaaffffffffffff0000ffffffffffffffffffffffffffff0000ffffffffffffaaaa00000000000000000000ffff0000ff0000000000000000000000ffff0000ff00ffffffffffffffffffffffffffffffff00000000000000000000ffff0000ff00ffffffffffffffff0000000000ff00ffffffffffffffffff0000000000ff0000ffffffffffffffff5555555555550000ffffffffffffffff5555555555550000ffffffffff00ff00ffffffffffffffffffffffffff00ff00ffffffffffffff00ff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffff00ffffff00ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ff000000ff00
|1,2=>0xaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaffffaaaaffffaaaaffffffff0000ffffffffffff0000ffffffffffff0000aaaaffffffff0000aaaaffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffaaaaffffaaaaffffffffffffffffffffffffffffffff00ff00ff00ff000000ff00ff00ff0000ffffffff00000000ffffffffffffffffffffffff00000000ffffffffff00ff00000000000000000000000000000000000000000000000000ffffffffff00ff0000000000ffffffff00000000ffffaaaa00000000ffffffff00000000ffffaaaaffffffffffffffff00ff00ff00ff0000ffffffffffffffff00ff00ff00ff000000000000000000000000ffff0000ffff00000000000000000000ff000000ff000000000000000000ffffffffffffffff0000000000000000ffffffffff00ff000000000000000000ffffffffffffffff0000000000000000ffffffffaaaaaaaaffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffaaaa0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff00ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ff0000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff0000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffff0000
|1,3=>0xffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff00000000000000000000000000ffffffff000000000000000000000000ffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000ffff0000aaaaffffffffffffffff00000000ffffffffffffffffffffffff00000000ff00ff00000000000000000000ff00ff00ff0000000000000000000000ff00ff00ff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x800342a17010060b040342c051300c142b0086c52040182c1428040340c051302c14250086c0c0e0182c1420008440a04018284601000340c0e0182c1422008440a0b0508440010001822050200c3a0200070361a07010060b050182e190182c1401068581805058282a010381828040182c26120884008030583c0200068300a03058281208038180a04018080200
|1=>0x800220502100143f00800220502028563e008007a1607010060a1d804661602898060a1d8042205058285e3800800361607010160a1080422051302c14360080022050182872380080022051b82c143600800220502028681500800361107010060a1a804220502028682f00800220502028463200800661607010160a1900422050202c143100800220502028602f
|2=>0xa80400110280c144f1000400070b0a81c04058c8021b0b030080b05054024e08810060b05134004c02810060b0512c00110700c160a2500400110281006491d80400112411c060b05004001102810164119004004608810060b05108021102810143910804001a1511408030580022050200c16410080022030582888420080086110200c160a2100422050200c8234
|3=>0x182c145b08814080a1d9680200230440a03058288801030441c040182c1e0103014080305828b201068144c0305828120802810060b2c14802002b84408030583c02000386854100202c64000304428040182c1e001384408030583c02002b014080305828a4010d814080b05154020008814080b2a0f8020029814080305828a4010885ca203058281011028101450
|4=>0x512c020006858c6051300c160a008f0ce050200c160a00800220e02810060b05190022d08814060b051100200310440a260200c160a040180a260200c160a30804361102810065f05004004e08814080305828020008814080a011780200270440a040182cb0001e8441c04018286a01030441c040182c3a5d08814080b2a09402000381828040182cba000d8181c5c
|5=>0x30440a040584c1425008440a04019c41401001a422040182c1442008007a110200c160a268040033088144c03050ec0200088300a040182c14090409c220401828681200800de1102810160a10804001102810060a1d9b80200368443e050200c16010003422170280c165400800342a0200c166a00800343a02810060b05148001b0b038080b050c8023302810060b
|6=>0x1300c160a0081c0c050200c165800800f01102810060a118040016088300a04058282a01270440a040182c260a040440a370200c160a3b000861102810060a1d804007208814080b050bc02000b05cea0305828021102810060a11804001107014080b0515402001381408030582896010004430050200c160a0480022050200c16132e804000702810060b050a00200
|7=>0x138440a04050d06401001b022050200c164100800223a0280c160a1000400110b838060b0511002001e0442e0401828760800044547b0200c1601000cc2c051b898060b05004f4050200c160a30804003d088380803050ec02000d8580a040182856010006854140200c1679000f42c1007010060b050040c1107010060b05088022d088140803050ac1000068181805
|8=>0x40804001b0d01408030582900003601822170700c160a009f822051300c160a008004e110280c160a1c004001b03038080305874141c088300a040182c1401030440a040182c3a58001f4581102810060b05000581102810060b20804001b088a8080b0509402003e044c6050200c160a008f4a61a02810060b050201a110618c0a0305828107a0d8681c040182c1400
|9=>0x2810060b380290c00088a80a03059c04001000181c040182c14850091822050200c143b00801083d0b01408030584c0211028dc0803058290601271b422050200c160a0001822050202c145e008001a1a06014060b05020ae1102810060a1800400110b840060b0511002000885d040305828020006814080305828e801001cc22050200c1434008001a110280c1654
|10=>0x95c2204018286812008008c6b02810060b05184028c0d8441c040182c14011e06c22290200c160a0422cda1102810060a1c8004e110202c143209004006d088a808030593402000681890050182c14010001c0a040182c2628008005a1b0b038080305828021b0b06018040182c1401440140803058290e010009c1a060b80c160a008002c0e02810060b05148021a
|11=>0x509402000881408030583c0200088144c0405828aa01001b40e11148140803058200e1102810161310804001124014080b050d80200088144c040182c1483008440a04019c0143000800ae050200c160a25804001102810060b480780200088380a040182c148e0081822052e010060a1a0001a050200c160a25804001b02810060b050a00200468441c050200c160a
|12=>0x7010060b05000221831814080b050c800110281006930524802003c0440a04058282a010006c1c040182c1409008009c3c08814080305828000d06014060b051d002003e84522050200c160a0004522050200c1641008009c111d014080305828008d1e8441c040182c1401030440a04058287c01000f0361115010060b09820781102810060a15820003c0885c080b
|13=>0x9c222a0202c142500800360614838080305828026c0885c0a030595002000d0145c040182c1408358440a03058284401000580a040182c260a29004e6110280c160a1c00400114a814080b05250020008814080a1a094020008814080b0505496010004418050200c14340080048110280c162040804007c088380a040182c1401088600803058288401000ccf41a
|14=>0x58280200168440a04018284601000440a370182c142200800e41102810060b2c004001102a58080b05094020003868540e0200c16080b04452050202c1432009300a040182c14610080034110c014080b050c8000d06014060b0512c02003e86c34050200c160a001cc22050202c143200801163c088140803050e4005708814060b050e002001e044080305a401401
|15=>0x2810160a1080400240887c0a040182c02000d81852040182c260a009b40a040182c14860080022050202c141e12804000d03014080b050940200261b022050200c160a000440a0401828764400800660602898060b0500516070d01408030584c001102810169c0526c02004c8440a040182c140100260220e0200c160a04004361123810060b05004003c08a5c0803
|16=>0x1f0220513010060b05004220e02810160a1f00400a11e0440a040182c1400218b022050200c160a040f40c0e0200c160a0090c0c1102810060b050040e06148380a040182c020d0b0140803050ac0200198b022051300c160a040b022050182ca88100800d81102810060a1a00400110c0140803050ac02002984474050200c160a008453c050202c149d008004e11
|17=>0x2810060a1c80058050200c160a25804006c02810060b0512c02000d85852040182ce00a008f0222a0200c263b0080022050202c149b0080022050200c143500800361107010060a158040057088a8080b0509402001384454040182cb001000440a0405828649a0080022050202c142143004001102810060b380285000199f434050200c160a000440a040182c8201
|18=>0x800342a0200c161d530001a060280c160a528049c06088140803058280056088e80a040182c14010d85854040182ce013008f00a040182c1486008007a070d03808030582810a308814080b050c802000d868300c0200c160a000b022170700c160a040cc781607010060b05005441102810060b09820021108014080b050f802001e0440a04019c41401002111611
|19=>0x200c143400800361a14810060b05021184608814080305828100d088155c030582802003904454050182c400100018221423810060b05000341002810060b0514800ac558440a040182c140808aa80803058289a0100130229102810060b050004e1123810060b05004001b0d010060b052a4100d02898060b051841001088140803052a0b601000440a040182876a7
|20=>0x348440a0401828760100130361a02810060b050000e161d01408030584c0224088a808030593402002b8440a04058284201000441c050200c160a59804861148814080305828106b068682e140182c1400088146e04058287c010006c220c0202c1415008000e1a02810060b052c8001a58a540a040182c14000d84408030582884010004454040182d60010006c222a
|21=>0x8008611070140803058280257088a8080305960020013890222a0200c160100211421102810060b05000229131814080b05054001102810060b2a0480200168440a04058284a010001d6c050200c160a00800661b0d0144c030582810070b0a40a040182ce0010d04554050202c14210001c222a07010163200800221f0200c160a09004001102810160a5aad00200
|22=>0x200c1613008440a040582864b900800360e0200c160a29004003c0885c0803050d002002184420050200c160a0083422050182ca85b008007a1b0d038080305828101b0b18c1c040182c14011e0440a04058285e010006c343a07010060b050008c1102810060a5c00400160601408030582896010d0148a040182c140012018222a0a010060b000440a260202c143e
|23=>0x280c160a1c004002d088140803059040200138440803058288401000cc981a02810060b050008c1b0d0140803058281053038680a040182c14081e0440a040182c1480001bc0a040182c145200800781102810143412804001b08810060b0517402000887c0a040182c26010015c22470200c160a00800866b088140803058280253120440a040182c14011381c0c05
|24=>0x88144c03058288801000f02204058284a1200800860d088144c030582802bd08aa80a040182c14005e0140803058297601001ac22170182c144200800361a14810060b3802800115d014060b050800200030a40a040182c14860084474050202c1425008004e110b810060a1d8040011028dc060b0511002000304428040182c14420001c0a040182c26b500800e411
|25=>0x5174002708810060b05174020008814080b051604a01000440a04050d06401000f422050182c142000800222a0200c161326804001b360181c040182c14010d8457e040182c1401001a422050200c165400800481102810060a1c804008408814080b050bc020008814080b5f02936010006c342a0200c167009800f0050200c160a25804002c088155c03058280200
|26=>0x58281201003040a040182c14c00080058110280c16542d804002408814080b050bc0200030440a040182c1e01001b022050182ca85b00800ae110b810060a1d804003c08810060b0508802002b8440803058288401000f40e1a02810060b098200c110711c080305828028c088300a040182c14010386874050200c1613000f022050200c1641008000c110a010060b
|27=>0xd8a40803058285001000b4661102898060b05020ac3d088380803058280206088380a5c0182c145b038581c050202c14320086c1c040182c148604004e41102810160a108040006088500a260182c145b348440a04058287c0100018220502028682500800220528810060b0502022052380c160a1100400110701408030508c020003014080305828d401068300a03
|28=>0x508c020065b2822050200c160a0086874050200c160a4300022050200c16546480400070d0a820040182c007308810060b051340200088380a040182c142804018220e0200c160a21004342a17010060b00800d61124014060b0500400110280c169005128020003b180a040182c1401000cc0a040182c14c500800ae110200c160a2e80400c3610440a040182c1401
|29=>0x200c160a0f004220e0202c142509004001102810060b2a10802003491822050200c160a008f4781107010060b0502078110200c143409004001102810060b0982850080d85854040182876010009022050200c1658008000e1114814080b1080400331e0440a260182c1408088380a04050d04a01001a422050182c1444008000c1102810060b208040011028980803
|30=>0x1991834051300c160a008f0361615010060b0980422050200d9c0a1d804001102810060b0784802001e8440a04058285e010001c0c0e02810060b0f004221f0200c160a2e80400a408814080a1f8c802000386820050202c1432000441c050200c1641008001a160618c0a030582802461e0440a040182c14080d0440a04059c01421000440a040182804010006c0c0e
|31=>0x58287c010003434050182c14a5041c822050182c3c2000800de4e08814080305828000608814080305874ba00088300a0405828aa0100018221402810060b2a0004e1102810060b2a00400110289808030590402002315c0a040182c1461008342c0c08014060b05004e65302810060b05218021102810060a67804001102810143f190040007030140803059740200
|32=>0x88140803059040200360440a030582844010001c0c140200c160a090007a1107010160a19004001b08b480803058280200348440a04058284a010015c361a15010060b0e8001a0602898060b0504802d00881408030582802001e94c340e0200c160a009ac22050182ca88100800220e0200c1434090040007030a828040182c003d088140803059600200138440a04
|33=>0x182c3a0608838b8040182c14121e8440a030582870010001c0c2a07010060b008340c1402898060b051cc22050182c1420008008c2708814080305828023d088140803050d002002709c22050200c160a0006c2c2962010060b050047a1102810060a18004003c08810060b051080200030441c050200c16540084420050200c160a1400022aa02810160a178040069
|34=>0x2810060b0513402006b0440a040182c1401000580a043a80c160a009e022050182c144400800ae110281014341280400460d8180a040182c140113818222a0200c161d0009c220502028682500800d21102810060b050040007030380803058282401030443e050200c161d0035022050202c14210080022aa02810060b2c004004602810060b051840206088a81c04
|35=>0x1b422050182c142000800222902810160a1900400841e0440a040182c1408001b40e110701408030582810271e0440a04058284a01000f4361a02810060b05020001a088a40a040182ce00a001bcda1102810060b05004001a0886122050200c160a0013822050200c160a008004e1102810060a1a004001102810060b09828a401000cc361102898060b050200211
|36=>0x358440a040182ca80100374222a0200c160a00800d2060881408030582802000b0300a040182c1461008f434050200c16130080034050200c160a6e020001148814080b050540200068442e140182c1408000440a040182c14db00800fa0d088140803058280200088600a370202c141500800220522810060b0500400d90885c0a030582802000d8182e040182c1401
|37=>0x80022050200c160a6f804001a02810060b0529c02003c09c22050200c160a008002c11318144c040182c14011e86c220e0200c160a04004661607010060b0500436111d0380803058280200088e9881002810060b0500022bf02810060b05004002d198441c040182c140100068222a02810060b3804c0011070140803058288801001cc361a02810060b05004006c
|38=>0x881408030582802002b844540e0200c161d008000c110a010060b05048001107010060b0537010012984452050200c161305004660d0301408030582802000d858080305829ae01088400a040182c144400800220502208060b05004002708810060b0504802000d0442e051300c160a041b00c1107014080305828021608b101c050200c160a00b8022050200c160a
|39=>0x30440a040182ca8010001822aa02810060b05001c41102810060b050200227088140803058283c010009c1a0602810060b05004006f1e0440a040182c14010006c340c13010060b05004000714814080305a1802003784474050200c160a00800f45708814080305828020039a2c22050200c160a00800d811028dc0803059500200088600a260202c141500801428b
|40=>0x200c160a000440a040182c147f00800581102810060b0539c0200088140803050e40200730440a040182c140100044186302810060b05020664c0881408030582802001e04454040182c1408000f0ae110b810060b050040006088500a040182c141e0039022050200c160a008008c1b0881408030582810013601822050182c145b00800a607088140803058281001
|41=>0x76004007a160440a040182c14001395c222a0200c160a0080022050200c161305344020008814080305829d4010015c22050200c1434008015a1115010060b0e804001a02810060b051a80200088140803098287601001b0220513010060b2a004002708814080b050c80200368440a040182c14e9008000e1602810060b74004781102810060b05354020008860c605
|42=>0x2810060b050040027030442e040182c1401000ccae1a02810060b05004001102810060b051d0c201000440a040182c14d300800663c088380803058280200120440a040182ce01e0080034110c014080305828008d038440a040182c1401001cc22050200c160a0080034110601408030582810a10881408030582802000d84452040182ce00a008000c050200c160a
|43=>0x582802001e81c22050200c1439008008c11060380a040182c140108814f6040182c140100018224802810060b05004001107014080305829e2013c014080305828c201000441c050200c160a43020028b038680a040182c140003b200a040182c14010006828050200c160a3c80022170200c160a78004001b088a80803059c02601000440aee0200c160a0080022ed
|44=>0x4a810060b050040073298441c050200c160a0086822f502810060b050004e0608814080b050940200088a40a04058284201000cc8c1102810060b05020021b08814080305829e8010004452050200c160a14004001b0885c4c030582810013904454140200c161300800ae110200c160a090040006088148e040182c14010001c222a79810060b00800d211070140803
|45=>0x220220513010060b050040007088a40a040182ce001000440a260200c160a3b0040069358440a040182c1401001e8229102810060b05000222a17010060b00800da1115014080305820004c068440a040182c1401000f40e1102810060b098200207088e80a040182c26010004418050200c160a3a004000d0b0146e260182c14013583434170280c160a008003611
|46=>0xd8581c040182c1401368440a040182c3c010028822050200c160a0400422050200c160a4d00400240304454050200c1601000440a040182c260a4302002f8088a80a040182c0200368440a040182c144d00801ee1102810060b05004005708814080b050c8020008814080b0509402001689c22050200c160a00800781115010060a1d804004c2b8440a040182c1401
|47=>0x800de240881408030582802003994c22050200c161305004781b0881408030584c14087e84454050200c16080086c226307010060b0500400990881408030582802003d06c34050200c160a0006c220c0200c160a04004781102810060b05180020008814080305829f201000440a040182c145b09004008d0d8440a040182c14010004418050200c160a25804003c
|48=>0x28980803058280200818440a040182c1401000440a040182c150200800781b0b0a808030582802000881600040182c14010009c221707010060b05004001102810060b053fc1001068442e0e0182c14080084474aa02810160a10804003d0d8440a04018287201003f8222a02810060b0080048110280c160a10004006c358440a0305828b601001ac22050200c1654
|49=>0x9c220e02810160a12804001102810060b052000200169e8581102810060b050000e1a070140803058281006088380803058282401138442e100200c160a008000c1102810060b0510802003681c2c2a02810060b008001a11060380a030582810010d01408030584dd801001cc22050200c16130502002271e0440a04018286801000b0220e02810060b05020d211
|50=>0x8010060b00802081115010060b05004001b08838b8040182c140835834341402810060b05000d81102898060b0516c0200088144c040182ca8010006c2c050200c143b008005a570881408030582802003c0b022050200c160a008000c11070140803058283c01460440a040182c1401001e0d81102810060b05004001a029700803058294c00368440a04018287201
|51=>0x800781102810060a1c80400110701408030582a0a01001ac22170a00c160a008001a0602898060b05004221f02810060b0500400997e0440a040182c14010022ce41102810060b050040007088500a040182c26080d830080305828c201001ac221802810060b0500400111d0140803058290c01001ac220c02810060b0502002271e04408030582824010001c222a
|52=>0x2898060b050200273088e80a040182c140100090222902810060b05004001102810060b0541810001e0440a040184c143b00800580d088144c0305828100608814080305828ba01000342c0c0280c160a0089c22050200c160a2c004002d3d04522050200c160a0001822050200c160a6b8047a3c0881408030582810000d8442e040182876010001c2c2a0a010060b
|53=>0x440a040182c150a00800341102810060b05424000d0d014080305829ce01000440a048382c1401001cc7a050200c160a430040024088a80a040182c26010001c34050200c16e800800361602810060b3804c14010b044742902810060b05004781102810060a1d8200011488140803058289601000443e050200c160a0f00400731e0440a040182c140100034220c
|54=>0x182c141200801f81107010060b050040007088380a0405828640100118220e02810060b05004d6110280c160a2d8040024088140803058780200358440a040182c144200800361102810060a15804010c088a80803058280200120440a040182c144d008006611080380803058280200088e852050202c1421008000e1102810060b052dc0200198180a040182c1401
|55=>0xd04452050200c161305020220e02810060b0523c02001384454040182c140100188220e02810060b0500400070b0a81c040182c02841e8440a040182c1408000f022050202c1425008004806088500a040182c14002b8440a040182c1458008004e24088140803058280200420440a04018287201000b4d81102810060b05004001115014080305c340200088148e04
|56=>0x5004003c0d8442e040182c14080043c22050200c160a00800f0330d01408030582802003c118d61102810060b0500422050200c160a87004000708b100a040182c26010015c361a15010060b050040046358440a040182c14010b044300e02810060b05005481102810160a1900400430d8440a040182c14010009c0c110200c160a090040006088a828040182c1400
|57=>0x88380a04018286801001181a1102898060b050041a160a0144c0305828021a02810060b052180200378f422050200c160a00801b4110b838060b05004001b088380803050ec02000881408030582a26080006c222907010060b05020021102898060b0516c0200088144c040182c14420080022050200c160a2580400c3088a40a040182c140100448231102810060b
|58=>0x50ac02001e8441c040182c14080089c220e0200c160a090040016088600a260200c160a008440b0080810060b05004001b088a408030584c14080086c22171b80c160a00800f43c08814080305828003d038581c040182c14010881408030582a2801001e0981102810060b050040033088144c03058281001230440a260200c160a00938220e02810060b050040027
|59=>0x46822050200c160a008007a530d01408030582802000684418630280c160a0080034110b83808030582810330d8580a260182c1401068440a040182856010004420050200c160a430040011690140803058280200030440a04058284a010045c361102810060b05004001102810060b05454020008814080305a40140100058222a07010060b0e8045a1b088140803
|60=>0x200c160100118361602810060b05004361a080380803058280053038580a040182c14010881408030582850010005822296201408030582802ad088a808030582810010b044521002810060b05004d6110b8146e030582802001e86c2c0e0200c160a00868221807014080305828001102810060b05048ba01000900c110280c160a1000400bd038440a040182c1401
|61=>0x88146e040182c146100801441102810060b0980400bd0d8440a040182c140100034220c08014060b05004003d138440a040182c1401000442e140182c149f00800340517010060b05004001107014080b0509402000d04430051b810060b05000360607010060b05004781102810060a1a00400841e0440a04018287201000f0361115010060b09804006d038445205
|62=>0x2810060b05004001102810060b38028a4010004474050202c14320080022050200c160a2c004006c160442e050182c1401000f40e1602810060b0980434050200c160a76020001a088a81c040182c3a0008ac40a040182c140100068221802898080305828003c08810060b05048020003844742902810060b008007a050200c160a4300400070d0400a040182c1400
|63=>0x11004003c0d8580a040182c260a00b9422170200c160a008000e0602810060b05048020008814080305828ee0100118361107010060b050063c1102810060b05004001107014080305829e408009a44e1102810060b050040006088a80a040182c3a00030440a5c0200c160a0900022050200c160a8e8040007030a80a040182c0200088163804058286401001bc22aa
|64=>0x881408030547c0200068680a260182c14082b86c34052e010060b05001781102810060b09804006c0885c0a030582802003994cae1102810060b05004220e02810060a1a004001b088a588040182c1401001b022050200c160a090040016088300a370200c160a009a4ae1102810060b05004001a07010060b05370020008a7940050200c160a0080022050200c160a
|65=>0x2810060b050040124088140803058280200261ac22050200c160a008004e5708814080b0509402000881408030582a440100210223a02810060b05004001102810060b0548410000381828050200c160a0001c342a0a010060b0004420050200c160a25804001107010060b0504802001e86c0c050200c160a0080036160717008030582802d0088140803058280200
|66=>0x8810060b050480200121c8222a02810060b00800361a07010060b05020361a15010060b0e80022050200c165400800d21102810060b050040007030380a040182c14012315c22050200c160a0081822052e00c160a2d800ae1115010060b0e8040006088380a5c0200c160a030440a040182c1458008005a43088140803058280200930442e050182c1401001bce611
|67=>0x200c160a7b0040078198440a040182c14010004474aa02810060b050040073390440a040182c14010006c22050200c161d05020001608a440a040182c14010015c361115010060b05004001102810060b0549c02003981c220e02810060b05004000d088146e260182c1401000440a040182c141e2e8040006088144c0305828b6011381822052e010060b050004e57
|68=>0x2810060b0521802003d03422050200c160a0080022050200c160a4282002002b86c34050200c160a008002c11080380a040182c14011e06c220e0200c160a0080022170a010060b050200006088500a040182c14002b8441c052e010060b05004001102810060b0542402000881408030587414a6008004e1102810060b050040011148380a040182c1408008440a26
|69=>0x5828020008860180513010060b05004001102810060b054a402001686c22050200c160a008000e1602810060b09804222902810060b0982810010885c0a370182c14010006c34170200c160a0080022050200c160a94004006c160440a040182c1401001c822050200c167005004001b0881408030584c14080081c2c2a02810060b00800d6110b814060b050040011
|70=>0x1481408030584c1401000680a040182c14ec008007a070b01408030582802001e94c22050200c160a008000c1102970080305828001a08aa80a040182c14003c15c22050200c160a00800f00d08814080305828020008814080305829c20100058222902810060b05004e61102810060b050040073088a41c050200c160a008002c1102810060b052a402ab088140803
|71=>0x200c16700982802000d044540e0200c160a008002c111501408030587402003901c34050200c160a008001a110701408030582810010881408030582a3201000680a040182c149f008007a1102810060b0502002004201c22050200c160a008002c11028dc4c040182c14011986c22050200c160a04004000d088300a03058280200168cc22050200c160a00800e611
|72=>0x900e1102810060b05004001115014080305c600200088380a040182c1465008015a1102810060b050200206088380a040182c1401088a828040182c26010006c340e0200c160a0080022170200c160a53004001a0885c0a040182c14080001c0c050200c160a00800e4110a01408030584c140100068221007014080305828000708815e6040182c14010006c2205
|73=>0x182c140100044301002810060b05004006b088500a040182c140100018222a02810060b05004012a088140803058280200138f022050200c160a00800222a08038080305828020003844540e0200c1601000440a040182c14e700800d81102810060b0500400331e0440a040182c14010004540050200c160a008007a1b0b0140803058280200088145c040182c1401
|74=>0x200c160a54804003d038441c040182c14010001c221002810060b05004003c2b8440a040182c14010001c34050200c1613008003411028dc4c040182c14001983422050200c160a04004001196814080305828020008814080305829d60100034221402898060b0500400110c0146e040182c1401001c80e1115014080305804001102810060b054b00200958440a04
|75=>0x54840200930440a040182c1401000442e050182c149f00800661b088144c0305828020008814080305829e00100068222a02810060b098040027030440a040182c1401004b822050200c160a0080022050200c160a7602002000385828050200c160a0080078110b810060b05004001b088a408030582802003d0440a040182c140100044540e0200c161d008003611
|76=>0x224222a0200c160a0080022050202c143200800341102810060b3802800070b0380a040182c14010d8440a370200c160a008008c1b0881408030582802002981c22050200c160a0080022050200c160a0f004001114b100a040182c1401000f4361107010060b050040011978140803058280200198680a040182c140100368220e02810060b05004001102810060b
|77=>0x58293e01001b00c1102810060b05004001102810060b0535c10010d8440a04018287601000440a040182c153100800e611070140803058280200168440a040182c1401001b40e1115014080305804003d038440a040182c2601000ccd61102810060b050040016088380a5c0200c160a0089c220e02810060b050040057088a808030582802000881408030582a6001
|78=>0x182c14080001c342a02810060b008002c110b838080305828021b08838b8040182c1401000f4ae1102810060b05004001102810060b053c80200121c822050200c160a00800220c028dc08030582802001e06c22050200c16130500400160885c28040182c14010004474290701408030582802000881408030582a640100068221402810060b0982800110a0140803
|79=>0x200c160a000f022050200c160a04001ca1102810060b05004005708814b8040182c1401000440a040182c14120080022050200c160a9980400070d0500a040182c140008814080305829de010004420050202c1432008001a110280c160a52804001602810060b053b002000d0441c050200c160a0401822050200c160a0f004001a088a80a040182c3a00038680a04
|80=>0x582802000885c0a260182c14010015c22050200c160a00801121102810060b05004001a088500a040182c14007e8440a040182c1401000440a046600c160a00800661102810060b050040011028dc4c040182c14010006c2c0e0200c160a0081822050200c160a0900401040881408030582802000898c1c050200c160a008004e570881408030582802000d8680a5c
|81=>0x6c34050200c160a00800e41102810060b05004001107014b8040182c14010001c220e02810060b05004001a088a80a040182c14010004522050200c160a00800361115010060b0500400110a01408030584c14010001c34050200c160a00800341102970080305828003c0d8440a040182c1401000440a040182c15340080022050200c1670050040011150500803
|82=>0x582802000b04428050200c160a008000c1102810060b05004003c0881408030582802003583422050200c160a00800ae1107014080305828020008814080305829b8010006c22050200c160a0400400070881408030582810010004454050200c161d0080022050200c160a5300400111481408030584c140100058221702810060b050040011148380a040182c1401
|83=>0x22050200c160a0080022052e010060b0500400110a0140803058280200088380a040182c14010006822050200c160a00800221702810060b050040016088140803058280200068440a040182c14010006822050200c160a04000361107010060b05004001608814b8040182c140100058220e02810060b050040e1602810060b05004000d088144c03
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0x7d201ec8079201dc8075201cc8071201bc806d201ac80692019c80652018c80615c17d805d6016d80596015d80556014d80516013d804d6012d80496011e7045a010e8041a00fe803da00ee8039a00de8035a00ce8031a00be802da00ae8029a009e8025a008e8021a007e801ddc06f8019e005f8015e004f8011e003f800de002f800a1c0208006200108002200008
|7,1=>0x22c80892021c80852020c8081201fc8
|8,0=>0x118a4459911460448910fe4436910b644249106e441291026440090fde43ee90f9643dc90f4e43cb80f0a43b990ec243a790e7e039690e36438490dee437290da6436090d5e434e90d16433c90cd5c32d80c92431b90c4a430990c0242f790bbe02e690b7642d490b2e42c290ae642b090a9e429e90a5a028d90a16027c909ce426a9098642589093e4246908f642349
|8,1=>0x1a7a469591a324683919ea4671919a2465f9195a464d91912463b918ca46299188246179183a4605917f245f4817ae45e29176645d09171e45be916d645ac9168e459a916464588915fe4576915b645649156e4552915264540914de452e91496451c9144e450a9140644f8913be44e78137a44d59133244c3912ea44b2812a644a091262048f9121a447d911d2446b9
|8,2=>0x235a48ce8231a08bd922d248ab9228a4899922424887921fe0876921b648649216e48538212a4841920e2482f9209a481d92052480b9200a47f991fc247e791f7a47d591f3247c391eea47b281ea647a091e5e478e91e16477c91dce476a91d86475891d42074791cfa473591cb2472391c6a471191c2246ff91bda46ed91b9246dc81b4e46ca91b0646b891ac206a79
|8,3=>0x2c420b0792bfa4af592bb24ae392b6a4ad192b224abf92ada4aad92a924a9b92a4a4a8992a024a77929ba4a65929724a539292a4a41928e24a2f9289a4a1d928524a0b9280e09fa927ca09e99278249d79273a49c5926f249b3926aa49a19266609909261e497e925da096e82596495c9254e494a925064938924be49278247a4915924324903923ea48f1923a248df9
|8,4=>0x353a4d45934f24d33934aa4d21934624d0f9341a4cfd933d24ceb9338e0cda933464cc8932fe4cb6932b64ca49326e4c92932264c80931de4c6e931964c5c9314e4c4a931064c38930be4c26930764c149302e4c0292fe64bf092f9e4bde92f564bcc92f0e4bba92ec64ba892e7e4b9692e364b8492dee4b7292da64b6092d5e4b4e92d164b3c92cce4b2a92c864b189
|8,5=>0x3e260f8093dde4f6e93d964f5c93d4e4f4a93d064f3893cbe4f2693c764f1493c2e4f0383bea4ef193ba24edf93b5a4ecd93b124ebb93aca4ea993a824e9793a3a4e85939f24e73939aa4e61939660e509391e4e3e938da0e2d938924e1b9384a4e09938024df7937ba4de5937724dd39372a4dc1936e24daf9369a4d9e836564d8c936120d7b935ca4d69935824d579
|8,6=>0x115e94556514c9450e513a944c651289447e5116944365105843f610f4943ae50e38436e10d29432650c0942de50ae94296509c9424e508a942065078941be50669417650549412e5042940e650309409e501e94056500d840124ffb93fce0fea93f864fd893f3e4fc693ef64fb493eae4fa293e664f918
|9,0=>0x4ef693b494eaa93a0a4e5a938ca4e0a9378a4dba936594d725352a4d22934084cda932d94c92531b94c469307a4bfa52f594bb252e2a4b6292cea4b1a12bca4aca92a994a7e9295a4a2e9281a49de926e94992925b9494a5249949025237948ba5224a486a92119482251ff947da51ed9478e91d9a473e91c5a46ee91b1a469e919e94656518ba46069178945be51678
|9,1=>0x5866560fa581a55fca57ca95e8a577e55d5a573255c3956e695b09569e559e95656558ba560a5579955be9565a556e955295522953ea54d6552ba548a5519954425506a53f654f4953aa94e0a535e54ce9531654bc952ce54a9a52825496a523a1484a51ee5472951a294608515e544e95112943b950c69427a507a5414a502a9400a4fde53ee94f9653dba4f4693c7a
|9,2=>0x61e2986f9619a585ca614e5849a61025837960b69823a606a58119601e97fe95fd297eaa5f8297d795f3697c495eee57b295ea2979f95e56978ba5e06977895dbe576695d765753a5d26974095cda972d95c92571c85c4a970995bfe96f5a5bae96e1a5b5e96ce95b1a16bd95ace96a9a5a7e9695a5a325682a59e6566fa599a565ca594e5649a58fe9635a58b25622a
|9,3=>0x6b6e1ad1a6b1e9abe96ad29aaaa6a865a97a6a369a83a69e69a6fa69969a5c9694a9a49968fe9a37868b69a23a686a5a10a681e59fe967d659eba678a59da8674659c7a66f699b4966ae59a1a665e998da660e997a965c659689657a9954a652e5942964e2992ea6492991b964469908963fe58f5a63b258e2a636658d09631a98bca62ca98a8a627e5895a622e98829
|9,4=>0x74e65d309749e5d1da74525d0b974069cf7a73ba5ce5973725cd2a73265cc0972de5cada72925c9aa72465c87a71f69c73a71aa5c60a715a9c4d9710e9c39a70c25c26a70765c13a70269c0096fda9beca6f8e5bd9a6f461bc7a6efa5bb4a6eaa9ba0a6e5e5b8da6e125b7aa6dc65b67a6d7a5b5596d325b42a6ce65b3096c9a9b1ca6c4a9b08a6bfe5af696bb65ae3a
|9,5=>0x7e565f8c97e0e5f79a7dbe9f6697d765f53a7d2a5f4197ce25f2f97c969f1c97c4a9f0997c025ef6a7bb65ee3a7b669ecfa7b1a5ebd97ad25eaaa7a8a1e9997a3e9e85a79ee9e72979a65e609795e5e4da79125e3aa78c29e27978769e13a78269dffa77da5deca778a9dd9977425dc7976f69db4976ae5da1a76625d8f9761a5d7ca75ce5d69a757e9d55a752e9d429
|9,6=>0x2195a86326182a85e2a16ea859a215e8855a214d98512613b984ca6129984826116a8432a103983e6a0f09839aa0dca834e60c9a830260b7982be20a5a82726092a82266080981e220708819aa05d98152604aa81066037a80b6a023a8066a0109801a9ffd97fce9fea97f829fd797f3a5fc597eee9fb1a7ea25f9ea
|10,0=>0x900ea3f8b8fbaa3e4a8f6aa3d0a8f1e63be98ed2a3aaa8e82a395b8e326382a8ddee36e98d92a35aa8d46634898cfaa334a8cae632298c66630eb8c1662fc98bc6e2e898b7aa2d688b32a2c398aea62b198a9ea29da8a4ea28a98a066278989baa264a896aa250a891aa23d988d26229b88826216a88366203a87e6a1efa8796a1dba8746a1c7a86f6a1b4986a6e19fa
|10,1=>0x9996665c9994aa648a98faa635998aea621a9862660f99816a5fc997ce65ea99782a5d799736a5c3a96ea65b0a969aa59d99652658b9960a6579995bea565a956ea55299522a53db94d2652b99486a517a9436a504993ee64f1a939ea4dda935264caa9302a4b7992ba64a59926ea49299222a47f991d6a46c9918aa459991426447990fa6435990aea4229905ee40da
|10,2=>0xa0ae2821aa062680eaa012a7fb99fca67e999f7ea7d699f3667c499eee67b299ea667a099e5e678da9e12677b99dca676999d7ea755a9d326742a9ce2a72db9c8ea718b9c3e6705a9beea6f1a9ba266df99b5a66cca9b0e66b9a9abea6a5a9a6ea691a9a22667f999da666e8
|11,0=>0x29aa9a6866997aa63a69859a5f26972aa5a669609a55aa94caa50e6939aa4bea9269a4766913aa426a8ffaa3da68ed9a38ea8d9aa33ea8c69a2f668b3aa2aa68a19a25ea88e9a216687c9a1ce686a9a18668589a13e68469a0f66833a
|12,0=>0x29e99a78269d79a73a69c59a6f269b39
|13,0=>0x29f28
|_,_=>0
def wAt:=mkWire dB 309 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 18
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 1000003 zs)
def oP:Nat→Nat
|0=>0x1e02f0d8290d805028450d8111e02f0d805028451d00f08029070050280108801068150800f088110700503838028010282900801008451682f028b106805000450200115001028291380f030150b00500045020010280112013030290d0010084504045008010f82f028790302b0d001050050d81102845028110b005088010683802801020450c00f060050b80102811028050500103017008010701100015
|1=>0x88150700502801088013484716801198050b845028110881106007088011301502001089a1098f308851028050500133005328010383b050451e011138131e0010d015008453184513015020010882108832008011301502001059811e09a0d805020010d0010084504045008010200502801030130d001130150200105045028052382b02049030170d0010800f0882907005088010c00f060050b80102811
|2=>0x88620801104015008010d062071710280102005051361201739005098450500127047398073901503801050011380f0301504045008010290936017088dd040110080112017001b50380503815050451e02f0d8110d805028450b801028111382f138171e0010d015008451d00f1d045029c10402900801028113602b35805068010204500845028290986c0284505001088ea070750280105005008450800f
|3=>0x6815130050880102001020451e02f0d8290d805028451682f1e0110d8050284500045028290280509847050010084515045070050282902801088010305f028110d001008451682f0d97102845020050080100069008450881113015020011382b0301504045008010c00f060050b801028113901509845050013b8050d8df08815040110080102811000451306c02845020013a00f30805088320701108841
|4=>0x8851028050200137813138291e0010d0150084508821028010284505005008013c023060450b801028111382b030150d0010500500845028291380f1e0010d8050284508805008011e803150450282900801060070b8010281100845198070d81100015028451382f0800f0804504015008013482b36015088dd04011008013801512013089c104029008012b805070450280102829071b4000150d02900845
|5=>0x301504045008011d047080290700502801098150500112013089c104029008010b00500045028010d8130284500045050011e8051504502829001dd0d8df08815040110080103805398073901503801050450f80f028790302b008010084507011020450001500801080450401500801028113a8051306c0284502001021523602b3580506801020450986f028450500102801030110d00100845021fd130f2
|6=>0x71b6000150d029008451382f030150d001020050084534847070b106805028010204527047398070986d05001138171382f2b8050b015088013c0473c0030680102045000ce0702900801028010d805028454202f42007029b50d02900845138170800f080450401500801001b50d02900845030131486b008450981505001000451e011028010d80502845088150600507011028010880100229448110d807
|7=>0x6047378071d045029c104029008011e8033480f3601503011008010d80502845008010500102829008011682f1e0110d015008451380f1e0010d015008450511e02049030170d001008453a00f30805088321301503805070290001500801050451d00f0a04d02805050012400f0296d0301304045008013b8010d8df130050284502001348473c0052b8110b0150004505049030170302b0d0010084547801
|8=>0x1380f080450401500801028450b005070290280108801028113602b088dd040110080103838088050504500015008010210a3580506801020451d0470a04d02805050010508212013089c10402900801310030898d0600707011360171b815088dd040110080100845198070b845028110c0070800f080110401500801050ed000ed1e02f0d015008450606b08805070110280137807098f1088510280505001
|9=>0x20450d0010d8110200108815008451e80708805000290381505045072690801e07005028010383b05045029a1098f308851028050500116801028b10d011008450210a088dd04011008013782b398053901503801050451380f08045040150080108829028010282900801008450800f070290700502801088050800f08011040150080108862060050b801028113d0010d81108815420071e0290d01500845
|10=>0x8450882107029050450001500801088011682f0a03502805020450680500801000110681502045021523602b000b10d011008451382f030150d00100845002451682f488450b8050281139803148451500102829500054f8151304702001080451d00f080290401500801028790d00100845028450b00508801098150500139847390150380105045088111380f030150404500801358053c0073581506801
|11=>0x1e8051e80715045028293484736015000b10d011008450c0471b815088dd040110080108815098050981505001050014682f298051e803150451682f1e011028010d805028451380f2b8050b015000451e0010d015008450d0a609805098150500100845001e9198070b84502811310033184506007130153480f138110804507005028b10d01100845000690d8290280108815008453480336015030110d001
|12=>0x70470280105005008450289a0b0050880102001020453780712015030290d00100845378031d045029c104029008010880102829098050284505001398471e8010d82902845000150880500005038150504552029088c90800f040150080106005130150200108815008452e045028110001502005008010d811000150d80502845000450986e0284506841000510280502045098f30885102805050014202f
|13=>0x284502829098f0088510280505001028291382f1e0010d8050284508805070290284500015008012300500005198030b84502811022bd070b3068050280102045120133900503801050450204902805030170d00108805088ea0802904015008015580500801022b50006e0284537817088e95500115005028293480708861488010b805028110284500005008450702b028010883200005130150200102829
|14=>0x880105001050451d00f5500115005028290800f0504502879030170302b0d0010084543005148471500102829138111e02f1e0010d015008451306d0284502001029c10980508801050010504512017089c104029008014d0010801e070050280105045488450b8050281102805088050281106801020450c00f060050b801028110701f02801050454a805088053c815098470500134817138111e0010d805
|15=>0x8815028013780f098f108851028050500108029008450284507005028010c047060050b8010281108805038400005102805050450280502829030290d001008453480f0d8dd130050284534803138110804507005028012b8050b0150880103015030290d001008450c0070c00f488010b805028111380f1e0111e0010d0150084508add03842000510280505045000050d8110200108815008450284d09805
|16=>0x5000f6008450381505045538050d8050986f0284505001089491d047029c104029008011380f1e0010d015008450504a138171e0010d8050284500035168030a035028050204539803390150380105045030150b005088010500105045088ea0802907005028011382f1e0010d0150084534803068410005102805020453602b36013358050680102045088050d829028450001500801088010600707011
|17=>0x2805020450421255045150050282935805068010204508815088050980509815050010288112013089c1040290080100069008451484715001028291380f080290804504015008011e02f1e0010d015008453481336015088dd04011008010280536017030110d00100845148473482b16801028b10d011008453601703015030110d001008453c00708805198010b845028110000508805000ce0d81102845
|18=>0x2805030ab028290d0010084503015030ab0d00100845390050984505001030110d001028010881500845029811e09a0d8050284502001360153602b088dd04011008014202f36815001b5008453780f42001029b50d029008454e005052990883a028010880502845088310c047060050b80102811022bd070b3000150d01100845348130d8dd1300502845020011380f138171e0010d01500845168030a035
|19=>0x30170d001008453482f1381108045070050b005000450986c02845050010606b0b80100845028113602b36013000b10d011008453780f12015001b5008452382b02049030170d00100845360133602b088dd04011008010d8011e02f0d80502845029121e0010d01500845348173c0052b8110b0150880108805008010002903815050450301709851008450002902805050453482b130f1088510280502001
|20=>0x280100845050450282905049030170d0010084564005638450383a028013e847001e90b84502811138172b8050b01508801618036204515001028291486b0981505001008450000502001198050b84502811420031e80515045028290200502801030130d0010800f0882900005088a60702902801030133480f138110804504015008011382f1380f030150080100801070b0000150d01100845020890204a
|21=>0x1e02f0d805000451382b03015030290d001008451d00f14805150010282902001008010d8110d805028451380f1382f080450700502111138131e0010d015008453482b36015030110d0013482f0d8dd13005028456580308b3502b310200114805008451484715001028293602b088dd040110080105045000510282902805008453901512017390050380105045070290280136017030110d001008450701c
|22=>0x28010302b029750504a030170d001008455202f088c90800f0401500801088050005102805050453482b1381108045070050881108801060070b8010281119803008010d8110d805028451d00f029c104029008010f82f028790302b0d0010084508815028010302b0d00100845138171380f08045070050280104119198030b845028110d82900801028010d80502845138171e0010d015008450981505001
|23=>0x804504015008010289a02001020450084500801120131202b390050380105045398053980739015038010504505005030ab028290d00100845028053602b030110d001008453602b03015030110d001008453482b0d8dd13005028453c0473c0030b0150880107011088110700502801088015202f088c90800f04015008010504a030170404500801198030d8110881500845050010d805028290284500045
|24=>0xd01500845030110305f0d00100845028050504503017040450d8290800f028450700502b4d0d8de088150401100801138111380f0804504015008010d80102829088150500500845020010204503017040450080109b450d9c30980505001000f60d8290881500845021523602b358050680102045138171382f080450700502801028290b0050004502805050451382b1e0010d8290d805028453480f13811
|25=>0x302b0d00105005108451d00f029c104029008013782b088e9550011500502829198033c047198010b84504045028290001505005008010301700069028010084505045028290882100801088110280502001198031e0010d811028452b805398072b8290b01508801088150880114807150010282934817130f1088510280502001028013602b030110d00100845070051486b07029028013482b138111e001
|26=>0x500112015001b50d0290084508805488010b80502811398073901503801050451382f1e0010d015008451d0470a04d0280505001008010d811028450200112017089c104029008016c0456b8050701302801000451306c02845020012b811138132b8050b01508801198030b0050d8110284503015028290d00105005008451380f1382f1e0010d015008451e3550d8051306f0284502001050450301702879
|27=>0x84508805008010d82b028450c00f488010b80502811088110281102805008012b9730b01502005088013d0011980706815020450c00f028dd040110080103840000510280505045028110036906807020450b00502811028450004512013001b50d029008450800f0702907005028011e0290a0450280500801038050504500015008011380f1e0010d0150084508805000050d82902845088050980509815
|28=>0x8452b8052b8110b01508801060070880113015020010d8290284500015008010885d028110280108801080290284507005028011d0070802904015008016f0151306b020010084502801198050b8450281100845098050500102829138130804507005028010986d0500108815008453602b358050680102045028290d823028450080136015030110d00100845088320701102801088010d8290500108815
|29=>0x2001458011e80715045028290500507045028010282902805030170d001008450d82b02845000150080139803088a509815050010b00500045068150204508801028450701302801138130804504015008013a8051306c0284502001138171e0010d015008450200102811008010084502801030110d001008451480707029028010880108b85028de0401100801390530280503801050450986f0500108815
|30=>0x2b8070b0150880100801000ce0d8110284503013030110d001008451e8030000503815050453602b030110d00100845028750d0010500500845000057181506803020450302b030150d0010084502045030150404500801098f108851028050500113015020010881500845050451484715001028291d045029c10402900801198070d8110006d0284515045028293602b088dd04011008010c00f0a09902805
|31=>0x986c050010881500845000291e02f0d015008453602b3580513045020010800f0804504015008010284e0880105001050450d8051306f028450200106005060070b80102811130f20885102805020010703702801020454202f029b50d02900845002f2448290d8070284500801060070b801028113c007198010b84502811088510282902805008010d8050d8010284502811028050302b0d0010084572811
|32=>0x28110d8de0881504011008010d811028010d805028451202b089c104029008010717102801020050084529805000f60381505045071950383b02801050450b801028110080100845458011e8071504502829088150980509815050010d001088050381705045198070680506815020452b8050d80102845028290d9c30980502845758052b8130b015088011382f2b8050b0150880105005028290006e02845
|33=>0x3815050453c003088310701102801071b4000150d029008450296d030130d00100845790010683b028010204506045060470b8010281100005088a607029028011e807008450381505045638450383a02801050450280509847050010084553005028110883a02801028290284505001023bd080470401500801500074f815130470200103015028110d00100845088050d8110006d0284530805060470b801
|34=>0x2001020450880502811068010204502a9d0986f028450500139803038390280105045488030297102005008451380f0301504045008011d00f14805150010282900801198030b845028116a8051306f02845020011486b1500100845028290284500801020010281102805028290984505001138172b8050b0150880102049030170d0010084502829070070280105045138110804507005028014202f1e805
|35=>0x7005028011380f0804504015008011e0111e0010d015008451e02f0a04502805028293c0072b8110b01508801132250d8070284502001088290980509815050017b0051306e02845020013c00535815068010204516807488450b805028110282903838028010504500005028290d029008453c007358150680102045008010002903815050450a04d08829028050500130805060470b801028111300508801
|36=>0x88150084507011028450001500801130f30885102805020017d0011e02b0d0150084503017030130d0010084529805000f60d829028450c047060050b80102811000150d80502845000451202b001b50d0290084500801052b50006e028450384300051028050504502829030290d00100845088a60080109815050010401e00005050450282912017001b50d0290084555807022b50006e02845070450800f
|37=>0x883a028012b805070450280102811000050986e0284505001028110204500015008011d00f5500115005028294202f1e8050d82902845001b6028290d0290084512013089c10402900801360133580506801020453602b35805068010204512015089c1040290080139803390150984505001008010d80502845050010282903803050450080106007070110881502801003f102bed0380705045198070d811
|38=>0x28450500116807028b10d0110084508805050450001500801030170b00502801088010281108045040150080136017030110d00100845028290380508801050450701102045000150080105001088050381705045088a50080109815050011382f1e0010d01500845068050204500015008010d8dd130050284502001023750d82302845008010b2460a01102805088010d8050282902845000458080502299
|39=>0xd015008450282900051028050504502829448010d807028450280102845020050080100845000350280502045360133580513045020013602b3580513045020011e02f0d8050284500045198050d8110006d02845000cd068050681502045028010302b0d0010084523005198030b8450281135805358150680102045070470280102005008454202f029b50d029008451380f080450700502801538050986f
|40=>0x280108801008010d8290d805028451e02f0d8050284502811050450004502805028294202f1e0290d0150084508036070050280102045028050281106801020450b005088010200102045028790302b0d00100845003f102bed03807050451e8070381503801050450080108829028050500102845060470b80102811060051301513045020011480514847150010282908899008011301502001138171e001
|41=>0x284505001148050702902801088011e02f0a045028050080108862488010b80502811028790302b0d001008451e8010d8290d805028450000508811130150200114845148051500102829089c109805098150500100005028b20d011008451e02f08851028050500100005068050204502001030ab028290d00100845028990880102001020451382b1e0010d0150084516807488450b80502811070130b005
|42=>0x1202b089c10402900801360173580506801020451682f1e0110d805028451e0030a045028050282912017089c104029008010d8110284507005028011d00f1480515001028290384200051028050b0050d811028450004585801488470b80502811088057400509817050010703708805028010204501c210a01e0280505045398471e801150450282902829390050984505001088050284e050010504508801
|43=>0x845028291e0010d015008450898d06007070110280108829028290280108801008011e80515045028291380f1e0010d0150084502805030290d001008451382b2b8050b0150880103015030290d001008454202f029b50d0290084516015000b10d01100845028293c8050984705001030170d001008450001502bed03807050450800f0700502801050453c00306839028010204536013358050680102045
|44=>0x150010282908c45798110700702801000050d805028450281108c4152805130170200108805198010b845028113c0033581506801020456d03a06807028010204514807088290981505001088050d80102845028293c00335815068010204508011070050280108801088c90800f0401500801168031e0110d8050284503017030150d001008450882102829028050080100005088050981505001071b60d029
|45=>0x680102045000050d81102845020013c003358151304502001398070383902801050451382f080450700502801198030001106815020450280508801020010204508805148471500102829420011e8051504502829000150680702045028111e02f028010d80502845008016e0050d82b028450702902845000150080136013358051304502001360173580513045020010c047028dd040110080108b1114807
|46=>0x88de04011008011380f0301504045008018c06d098070284505001004590a036028050204505049030170d00100845050050282902801088011682f1e0110d805028450381505045000150080113817080450700502801028dd13005000450200180805022990883a028010000509815028450500108815028110401100801198070d8110d8050284508801038150280105045738050683a028010204535815
|47=>0x880114807150010282900005028290006e028450702907005028010880113005028111304502001028010d829028450004507171028010200500845030170d0010084512013030290d001008451e8230000503815050458d845071730200502801088051e803150450282908811060070b8010281102801028110080100845020010d81102845000451682f0a035028050204507005088a6070290280102c65
|48=>0x1e823000050d82902845020450701107005028011e0010d8290d80502845028050889a02001028110701c0880502801050451380f08045070050280108805028dd04011008010d0010280108815008451382f1e0010d015008454202f1e0290d01500845000290d80502845028290981503805050450500108801000ce0d81102845008450284507005028011e80300045038150504543007148471500102829
|49=>0x88e9550011500502829088ea029c104029008010800f0802904015008011382b1e0010d0150084502811000b10d011008450281d00045050450500100801088050381705045028290280105005008454a8053c815098470500106005088051301502001138171e0010d0150084505045148051500102829398471e80115045028290880500051028050504508832130051301502001053fd0986e0284505001
|50=>0xd82b028010881500845500054f81513047020010204a030170d00100845000290d80502845000452b8070d8010284502811050450301704045008010d8df08815040110080102801000ce0d811028450030602b6906807020450683b020450001500801138111e0010d01500845028290d0010500500845030170d001020050084506bcf07007028010204505045028290404500801020c90800f0401500801
|51=>0x84508862080110401500801138170804507005028010b0050d829028450004508801020050881502801002f1448290d8070284505c82568050006e02845020010204500845008010d80108815020050084500029448290d8070284502811088dd0401100801398032b8290b015088011382f08045070050280108815148071500102829030170d00100845088011300513015020013c0052b8110b01508801
|52=>0x8010d801000ce0d81102845030130d0010200500845028290b0150500508801028010d00102005008451382b030150d0010084516803028b10d011008453580702811068010204539805390150380105045928153900703801050453c0073581506801020451380f2b8050b015000459180535817068010204508aa9550011500502829008011e0130d015008450b005000450280505045050450282902805
|53=>0xb845028115500115005028293901503801050450284505005008010a01102805088010d80102845028290a09a02805020010383902801050451300502001020450302b0d0010084502001030130d00100845030150d0010200500845138172b8050b015088013900502829038010504500801028010881500845028290881505005008453602b088dd0401100801138111e0010d01500845088210504500015
|54=>0x28110881500845428050d81302845000b10d01100845098050984505001000050284505001000450504502829028110680102045148471500102829198070681502045008010d813028450d8010881500845070050280108801028010d805028450281102805008010d0010280500845020050883902801740050981705001050050883a028011e0010d015008450702900015008011306e028450200119801
|55=>0x2045198050b84502811088a509815050010880503817050450004503815050451e80315045028290d00102005008450287505005008452b8110b01508801358150680102045028de0401100801070290280108801390150380105045088a507029028010702b0280108801022b50006e028450600513015020015504715005028291e0110d80502845088010500105045008010981505001028110401100801
|56=>0x6e028450b0050280108801028290280505001028010881500845028110883a028010281100801008450504504045008010884d0280505001008450700502801070070280105045098050284505001008450280102829088010500502829088050380105045020450001500801088de04011008011304702001008451504500801028290a01d0280505045130050004502001000050d811028450701102801
|57=>0x88110280502001028dd0401100801028290380105045428010d8130284508b311300702001080110401500801028050680102045028290d001008450682302045008011e0010d015008450700502801028290504502801028290683a0280102045088dd04011008010d8110d805028454f81513047020010d82902845000450383802801050453900503801050450980705001028290383b028010504500005
|58=>0x20450889a02001028110d8110284502001530050883a02801088050500102829030150d001008457404509817050010080103817050450004502805050450a0450280502811150010284502829198070b84502811050050280102829028450702b028010381502801050450005102805050450d8010d8050284500845050450500113005020010084500005068150204502c6109807050012b8130b01508801
|59=>0x5045028290002903815050450681506801020450200502801088010804507005028010d80102845028290d97302005028450d80702845028290800f04015008010e8010500500845088290280108801088150401100801000ce0d81102845000f603815050450302b0d001008451480715001028290d82900015028457982907007028010d81108815008450680702801020451e0130d015008453580706801
|60=>0x282905005008450504500845008010084505045028290281102801088010200508815028010d8290006d028450683b02801020453900503801050451300513015020010d80502845050010880102805028111480507029028013901703801050450500102805008450889a0280502001030110d001008450701300015008011e02f0d805028454f8051304702001038390280105045028b10d0110084503805
|61=>0x280500845038030504513007020010b845028111300502001088150280108801030170d00100845448010d807028450600707011028012b8050b015088010881502005008450a04502805008012b8070b015088010b0150200508801030170d001008450706b02801008450882902805008450804704015008010800f04015008010289a02001020450381708801050450084500015008010302b0d00100845
|62=>0x880105045020010204502805088010d001008450d01500845068010204508839028010d82b028450284500801050450080105005028290883a02801098150500108801028110702902801088150084503801050450200502801028010504500845028290b8050281102845028290280505001088290084502005008450d8050284506817020450402900801028050282902001028110b015088010d80702845
|63=>0x20050280502801008450281108801020450080100845088150280102005088010280108801
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x4e20000000004d10485000000000000000000000000000000000444040400000000000000000000000000000000000000000000000000000000000003c4038400000335000000000000000000000000000002f40000000002a50255023201e501950000017200000125010200a600640024000000020000
|7,1=>0x562000005420504
|8,0=>0x13d51385133512f412a50000000012550000120511c41175112510d510851053000010050fb500000f740f250ed50e850e440df50da50d6400000d240cf30ca5000000000c5500000c140bc50b840b350af40aa500000a550a0509c409a2095509050000000008b50865081507c50775072506d506940645061305c505840000
|8,1=>0x220521c42175213420e520950000205420051ff1000000001fa51f911f541f051eb51e741e251de41da41d551d051cb500001c651c151bc51b751b251ae400001a951a541a4119f519a519551923191118d418851835180317d317941772173416e500001695164515f515b415650000153314e500000000149514631424
|8,2=>0x2ed100002e942e452e042dd3000000002d942d4500002d042cc400002c932c452bf52ba52b552b052ab52a742a2529e429a42955292328d528940000284527f5000027a527550000271426f2000026a52664262425d5259425452504000024b524742443000024040000000023c42375232522d5229422540000000000000000
|8,3=>0x3eb53e653e243dd53da33d6400003d1500003cc53c753c253bd53b943b723b253ae43a953a633a1539d40000398539533905000038c43893384537f537a53755370536b53665362435e43595354534f534a50000345534140000000033c53375332532d53285324431f531a53155310530b53092305430142fc52f752f252ee4
|8,4=>0x4dd54d944d544d054cb54ca100004c554c054bb54b740000000000004b434af54aa54a554a1449c549844962491548c54875482547e447a400004773472546d54685463545f445a545554541000044f544a54455440543b54365431542d4428500000000423541f441a500004164412440d5408540353fe53f953f4500003f04
|8,5=>0x5cd55c945c545c050000000000005be25b955b455b045ac45a755a2559e45995594558f5000058b458655824580257d35785574456f556b45665562455e455a45555551454c554755452541453c5000053845344530452c45284524451f551b45174515251140000510150b5507450254fd54f944f454f0400004eb54e744e25
|8,6=>0x69650000692468d568856835681267d46785673566f466a566910000664565f5000065b4000065656515000064c564756434000063e563a46364632462d56285623561e561a46164611560c5607560255fd55f855f355ee55e9500005e455df55db45d745d2500000000
|9,0=>0x7954791478d478947872783477f477b47774773476f476b47674763475f475b47574753474f474b47474743473f473b47374733472f472b47274723471f471b47174713470f470b4707470346ff46fb46f746f346ef46eb46e746e346df46db46d746d346cf46cb46c746c346bf46bb46b746b346af46ab46a746a3469f469b4
|9,1=>0x88e488a48864882487e487a48764872486e486a48664862485e485a48564853384f484b48474843483f483b48374833482f482b48274823481f481b48174813480f480c38084804480047fc47f847f447f0400007ec47e847e447e047dd37d947d547d147cd47c947c547c147bd47b947b547b147ad47a947a547a1479d47994
|9,2=>0x98e498a49864982497e497a49764972496e496a49664962495e495a49564952494e494a49464942493e493a49364932492e492a49264922491e491a49164912490e490a4906490248fe48fa48f648f248ee48ea48e648e248de48da48d648d248ce48ca48c648c248be48ba48b648b248ae48aa48a648a2489e489a489648924
|9,3=>0xa8d4a894a854a814a7e3a7a4a764a724a6e4a6a4a664a624a5e4a5a4a564a524a4e4a4a4a464a424a3e4a3a4a364a324a2e4a2a4a264a224a1e4a1a4a164a124a0e4a0a4a064a0249fe49fa49f649f249ee49ea49e649e249de49da49d649d249ce49ca49c649c249be49ba49b649b249ae49aa49a649a2499e499a499649924
|9,4=>0xb894b854b814b7e3b7a4b764b724b6e4b6a4b664b624b5e4b5a4b564b524b4e4b4a4b464b424b3e4b3a4b364b324b2e4b2a4b264b224b1e4b1a4b164b124b0e4b0a4b064b024aff3afb4af74af34aef4aeb4ae74ae34adf4adb4ad74ad34ad03acc4ac84ac44ac04abc4ab84ab44ab04aac4aa84aa44aa13a9d4a994a954a914
|9,5=>0xc884c844c804c7c4c784c744c704c6c4c684c644c604c5c4c584c544c504c4c4c484c444c404c3c4c384c344c304c2c4c284c244c204c1c4c184c144c104c0c4c084c044c004bfc4bf84bf44bf04bec4be84be53be14bdd4bd94bd54bd14bcd4bc94bc54bc14bbd4bb94bb54bb14bad4ba94ba54ba14b9d4b994b954b914b8d4
|9,6=>0xd633d5f4d5b4d574d534d4f4d4b4d474d434d3f4d3b4d374d334d2f4d2b4d274d234d1f4d1b4d174d134d0f4d0b4d074d034cff4cfb4cf74cf34cef4ceb4ce74ce34cdf4cdb4cd74cd34ccf4ccb4cc83cc44cc04cbc4cb84cb44cb04cac4ca84ca44ca04c9c4c984c944c904c8c4
|10,0=>0xe233e203e1d3e1a3e173e143e113e0e3e0b3e083e053e023dff3dfc3df93df63df33df03ded3dea3de73de43de13dde3ddb3dd83dd53dd23dcf3dcc3dc93dc63dc33dc03dbd3dba3db73db43db13dae3dab3da83da53da23d9f3d9c3d993d963d933d903d8d3d8a3d873d843d813d7e3d7b3d783d753d723d6f3d6c3d693d663
|10,1=>0xee33ee03edd3eda3ed73ed43ed13ece3ecb3ec83ec53ec23ebf3ebc3eb93eb63eb33eb03ead3eaa3ea73ea43ea13e9e3e9b3e983e953e923e8f3e8c3e893e863e833e803e7d3e7a3e773e743e713e6e3e6b3e683e653e623e5f3e5c3e593e563e533e503e4d3e4a3e473e443e413e3e3e3b3e383e353e323e2f3e2c3e293e263
|10,2=>0xf733f703f6d3f6a3f673f643f613f5e3f5b3f583f553f523f4f3f4c3f493f463f433f403f3d3f3a3f373f343f313f2e3f2b3f283f253f223f1f3f1c3f193f163f133f103f0d3f0a3f073f043f013efe3efb3ef83ef53ef23eef3eec3ee93ee63
|11,0=>0xfc62fc42fc22fc02fbe2fbc2fba2fb82fb62fb42fb22fb02fae2fac2faa2fa82fa62fa42fa22fa02f9e2f9c2f9a2f982f962f942f922f902f8e2f8c2f8a2f882f862f842f822f802f7e2f7c2f7a2f782f762
|12,0=>0xfce1fcd1fcc1fcb1fca1fc91fc81
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 16
def pmP:Nat→Nat
|0=>0x20400000000010040000000008000000000002040000000001000000000000600000000000230000000000108000000000082000000000040400000000020000000000008800000000004200000000002040000000001000000000000490000000000220000000000108000000000080000000000030000000000010000000000004800000000002000000000000c000000000004800000000002000000000000c0000000000050000000000020000000000008000000000002000000000000
|1=>0x20800000000010080000000008010000000004001000000002000000000000f0900000000032000000000018080000000008808000000004200000000001810000000000944000000000496000000000242000000000120000000000089200000000044700000000022300000000011080000000008810000000004400000000002120000000001080000000000824000000000406000000000202000000000100c0000000008010000000004000000000001480000000000a00000000000489
|2=>0xa240800000005111800000002813a00000001358d000000009200800000004300400000002120200000001084d0000000084020000000041404000000020882000000010425000000008204800000004101400000002080200000001020c00000000810200000000408000000000203020000000101040000000080428000000040040000000020016000000010009000000008004000000004001000000002000600000001000100000000800000000000184f000000000b318000000004880
|3=>0x2004c280000010020040000008000020000004000000000001a00468000000a428100000005214000000002902800000001480420000000840a10000000420108000000200080000000100002000000080000000000020102800000010048100000008000a000000040000000000018081c0000000908000000000404460000000200010000000080002000000020084000000010041000000006100000000002dbba000000016d9d00000000b4268000000052200000000028b2a00000001450c
|4=>0x4084c6800000204123400000102081200000081000100000040344f000000201826800000100c03c00000080480e000000400443000000200203800000100100800000080080000000040024c800000200107000000100081000000080008800000040004000000020001200000010000100000008000040000004000008000002000000000000c8910a0000006408810000003200008000001053634000000820a020000004101c500000020802e800000101022400000080810a000000400989
|5=>0x40b6ee800000205b67c00000102db3a000000816c9d00000040b4ce80000020577b400000102bb9a000000814dfd00000040a6ee80000020536f4000001029b3a00000081449d00000040a044800000204b7b4000001025b9a000000812dad0000004096c680000020477b4000001023b9a000000811d8d0000004087f68000002043f34000001021f1a000000810ded0000004086ef8000002043734000001021b5a000000810d9f0000004086ce800000204363400000102191a000000810a0c
|6=>0x820246000000404100400000200100200000100005c0000008000230000004000110000001c80102000000e400010000006086c7800000304363400000180911a000000c002060000006000008000003000000000001520402000000a10d8d000000508102000000245327c000001225b9e000000912d8f0000004886e78000002443734000001221b3e000000910d8f00000048866f8000002202270000001101018000000880014000000440002000000214363c000001061b1a000000830c9d
|7=>0x2000040000000a043e34000005021bda000002810d8d0000010085000000008042010000004020bda0000020009a40000010004120000008002070000004000048000002000004000000cca6ce8000006653634000003309010000001890d8f000000c486c68000006243234000003025b9e000001810d9f000000c086c7800000604363400000302191a000001810455000000c02427000000600211000000300009c00000118409c0000008c04000000004600000000002109000000001080802
|8=>0x240a6ee800001205363c000009029b1a000004813ded0000024096e6800001204b6f4000009025b1a000004812d2500000240924680000120476f4000009023b5a000004810ddd0000024086e680000120436f4000009021b3a000004810d8f0000024086c6800001204327400000902191a00000480488c0000024016460000011002044000008801006000004017db900000200be54800001004329400000802192e0000040059ac000002002cd4000001001621000000800a1000000040011a8
|9=>0x440a66e800002205323c000011025d32000008812dcf0000044096c7800002204b63400001102593e000008810dcf0000044086e6800002204367c000011021b3a000008810d8f0000044086c680000220432740000110209a2000008012c4200000400864b800002004124c000010020882000008000808000002c0a6c6800001605333400000b021b9e000004c10d8d000002608646800001245363400000922993a000004910d9f0000024886c7800001244323400000906191a000004816ddd
|10=>0x64186e780000320c363c00001904111400000c816c8300000640a6c7800003205333c000019025b9e00000c812d8f00000640864f800003201221800001900812800000c804080000006400045000003200002800001800911c00000c00409c0000060020400000030000200000013025b1a000009810d9d000004c0864e800002255327c0000112a1b3e000008940d850000044a044d000002250206000001106191a000008816d9d00000440b66e800002205b274000011029b3a000008814d8d
|11=>0x14ccb6c680000a634b634000053025b3a000029812d8f000014c096c680000a604b62400005302193a0000290c0c0800001480000080000a27426740000511a9b1a000021810d8d000010800404000008234263400004118081c0000208c040c00001046008200000820c3634000041021b1a0000200c0d85000010060280000008030101400004018080200002002008400000800b6a6800004005363400002002081200001000408400000800000080000360c363c000019065b9e00000c832d8f
|12=>0x222020ca8000111002004000088800002000041814c8d000020c086ce800010604363c000083021b1a000041810c9d0000207000428000102e43e3c000081621b3e000040a0020400002048b24f800010205b67400008102d79a000040815dad00002040a7e780001020536b4000081029b3e000040814bdd0000204096d6800010204b634000081021b3a000040810d8f0000204086c68000100052200000080023b1a000040010481000020008200800010004001000008000002a000040000000
|13=>0x804086c6800040200001000020000121800010000020400008000000400004000000000001800041000000c00000a00000404086d68000202043634000100020b1a00008000090c00004000000400001a60080300000d2000008000048e70d8d00002440a7e68000122053a7400009102993a000048812d8d0000244096478000122043f3c000091021b3e000048810d9d000024008340800011305367c000089829b3a000044c10dbd0000226086ce800011300226c00008980103200004441088d
|14=>0x100408ec680008020436b4000401021b3a000200810d8d0001004086c2800080104f62400040002da0a000200014ded00010000a6ee80008000536f4000400024a9a00020001149900010000822e80008000125b00004000012f800020000084c0001000000b6000064205b67400032102d33a000190810d8d0000c84000020000642000004000320000a180001900005050000c80002440000640000430000301021b1a0001808004000000c0000c0600006000010a0000221000800000102010800
|15=>0x1c8409cc68000e420060000007200038020003900005050001820096860000c02043634000581027b1a0002c0811dad000140409ed68000a0204f634000501023b5a000280811d8d000140400ec28000a0000e6a0000500004a1a000240813d8d000120408ec680009020436b4000481021b1a000210810d9d00010840008a000081204f6b4000409021b1a000204015dad00010200a6d6800080a043634000404021a9a00020200014d00010040bece8000802057674000401027bda000200811ded
|16=>0x20240040000010110429040008082000880004040108cd000202000020800100800201000080182d73a000400c10f8d0002006085ee8001003040834000801800418000400830d8d0002004087c680010020436b4000801021b1a00040081048d0002002085428001001040e2400080082061a000400410305000200208140800100104093400080082041a0004004009c100020020019600010010008340008008004020004004001200002000800410001000049534000800001310000400000100
|17=>0x4004000008002000001004001000000002000484812dcd0002400004400001200001624000900000012000444c129dd0002226085ce800111304277400088982133a000444014add00022000246680010a604b634000841021b1a0004208000010002100100408001080000000000819065b9e00040c810dcd000202c0864e800101304af34000809821482000404910dcf000202409ee4800101204b73c000809025b9a0004048129dd0002024086e78001012043734000809021b1a0004048028ca
|18=>0x100000040000080000002800040000001080020000000800009a10085b40004900040e10002281029f9a001102010b0c0008810083c48004400043e340022000214080011000102840008800081060004400040820002200020018001100000b0c0008800001008004100040c00002021821b1a001010400881000808200004800404100001400202000810200101000008d0008004086c680040000436f40020000206080010000102140008000000400004000000010002000000002001000000000
|19=>0x2000c086e7801000604363400800300101c00400180048f002000c000268010002243634008001021b9a004000810d8d00200040840a001000200213800800002102800400000088e002000000403001000000201000800000000c003014c11dad001242408ed68009202047734004808000208002284813dad001102409ed680088000416b4004400020b1a002044c11dbd00102020828e80080120476b4004009021b1a002000811dad0010004086c68008000043674004000020bda0020000105cd
|20=>0x1000040b6ce8080002053734040001025b9a020000812d8d0100004086e68080002043674040001021b1a020000014dcd0100000086ee8080000041004040000000102010000000401008000000002002301200a73401180180171a008044c1099d00402040a7e6802000604373c01000102d33a008000810d8d00400000800400110a600013800885104419c004428810dcd002212c000270011082000004008840000012004400810d8d0020108004040010032081234008003721494004001814dcf
|21=>0x240005407c68100000000010052081021b5a02304001050d01180a6086c68088040001474042601029f1a0211000100cc0108204096d680841020436b4042029021b1a02101000008c010808000004808101204b7340408080042980204000020800101c040aec68080e02053634040609029b1a020304810dad01018140a6f68080c0205b634040601029b5a020300814d9d01018040a6c68080a40057654040321023b3a020010014ddd010008008222008001204b734040009021b9a020004810dbd
|22=>0x1800444c1099d2040004084ee8820002043634210001021b1a10800081098d04022200846e820101204a73410080182171a080044e50d9d04002260868f8200112043674100089021a7a08004441489d04002200944e82001020476341000112a1b3a080000e50d8d0400004086c682000020436301000010213ba048001800dcf
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x800008030000000000024000001b00c000000000000000000000e00c00000000000000000000000000000000000000441100008000000000000000000110000001417024170200002c0000c3b0e80300c0002400
|8,0=>0x16b018019724f23c000300190000000011c803674120542e0546f04c44058000056901c17058060021b6ce4060469814061f00a9225500e041a809019fb000880040100dd30001541800001be08dc2058442f023230000008c0014e3d25d8f48d10c150002f1000004414610620f81273cd20000308c0100000460000180100c142288c0000100411026058f80000008414468cc010cc010180108c0f01800
|8,1=>0x24c6d0540722891002410000122d01314030360510c6608ccf07c0001c116e00000c231b00725c8c3a0240580600c461f801004004c4f5000001c1da010013802353c1e912a32006e10c0121c010046a1f000018132288a0000000c2b00015018000455c010db069647101d10c2310e3f074db08c0006801001071a00000d800000100406004154b40300293908230007d00000228e5234b40181c0000000000
|8,2=>0xa2c0a97909000000000900404138060a03c00c9526410000232047d02402078032080607803054231280669c01025bb4bc000548a97c8a08c0a9247400c0d9c4000ec5100c600780642c0c00163074087281505401541ba00075004052280000000019c901c450740110ce2004010587d90c11000063104836abe0540102072000010042b0d8ff004010048c0000000423858001cc15004375543300475001bc
|8,3=>0x100036350441443b00c040041f1783b001301900008c000042500001020030009c07c1104407a52031080319dc10412e00444751770040500008110158004f8b800
|9,0=>0x871c94e165549e428a0d6d63a9f4c0841982ace32a4fc81e013e9bf1fd6a95997a11d7304c34f6ba8a48a846ce48d0eb09eba44005e82495cd608ec3305e50b5a682099844417210c7359361449838de7467c1483f0edcb938688745d4aa7b402271310f83dd6724966fd6d3a4590cd5647077345dc930e4065737f910151d555d25af59084434948a27d51a5dac03654682d5431855950a2b359440ca284d19
|9,1=>0xb4a2f37d4b3847ab2013120dd748572496634ea626de12724a59cd5b25abb30477e1e3289680f59c3e5829d5b482daa88e986e5fc7b2c7a5429266630d697b14833aa4b4fc63831c651dd05e61f82ea42150f91da23f884434ba1e152309727f5ff14e866853e3e16e989d8004d60607b94235521224cd719d93424263a4a8c136cb0c66d1ac3160ebc4d14a0d1511da58ab9f227a8591a09a390209c3079db1
|9,2=>0x28939b445b022bf289c7561ad31e7a969a01ea826b8f627898140b37b932b4e53482d43619e1c45c8d1179e025478a070d58ae08a5bc982995d3dcb87aac69ddbfa36832b0a2336b356a0a914fb39aac99d59298237a2694b0839a9f02845f2bacf49ce776c1928a728699f7163b8e4a29d2207c651b42b48198d37006860384f089a41702509db10203c0215148e981f35b032ad4d7245861e48a422473b839
|9,3=>0x67660d8797847d2427ca250e0218628196150b1b71696d09a1e6d84b219426a44c16153a8a14b0de2ac12173230b0673089bda5a2b700a242a122690f986630a85633842
|10,0=>0x3cd3cab666578a29fd5f9e5162b4d66d9de9acaa3b2195d1406b1a44a66332e2c585af8e14caa1049fa117beb95f2217d2597e4be2b23763d3c299cc9a1e6581335d4eb4dd1d2fd9a450a82d9446c98c4dcf129ccc5f4b96fddd56db0aa90478270a1da85815ea7d958f26e6fced8c68a2c66596cd0aed4da02a944928a957f4ad3b7de789911d891918d98e64ab13bcca862807a66f65a3249ab7899dca26af
|10,1=>0x46cbb888fd8aaa069611ac8a2299a92a68f7d13a2dcbd325414d8b2a862d2b17eaada162e815b59b7b5cea7aca7ea889354958a6ca76178990f4428c
|11,0=>0xb544e9c2c53a77d8a2f5a37da2543d1d500c829a7f2c27f4457ba6d37292b6441994d69a68cac3c98877a2543d894cddc456a7
|12,0=>0x29961ca628ca52bcac
|13,0=>0xa2
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 10 (j%128);fld (pmP (k/32)) 49 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_253 12 roots_253 ops++addP pm 1 dom_238 9 roots_238 ops++addP pm 2 dom_223 11 roots_223 ops++addP pm 3 dom_239 11 roots_239 ops++addP pm 4 dom_159 9 roots_159 ops++addP pm 5 dom_231 9 roots_231 ops++addP pm 6 dom_111 8 roots_111 ops++addP pm 7 dom_127 11 roots_127 ops++addP pm 8 dom_247 11 roots_247 ops++addP pm 9 dom_43 5 roots_43 ops++addP pm 10 dom_246 10 roots_246 ops++addP pm 11 dom_191 11 roots_191 ops++addP pm 12 dom_215 8 roots_215 ops++addP pm 13 dom_95 9 roots_95 ops++addP pm 14 dom_63 9 roots_63 ops++addP pm 15 dom_85 5 roots_85 ops++addP pm 16 dom_251 12 roots_251 ops++addP pm 17 dom_206 5 roots_206 ops++addP pm 18 dom_158 6 roots_158 ops++addP pm 19 dom_62 6 roots_62 ops++addP pm 20 dom_190 9 roots_190 ops++addP pm 21 dom_174 6 roots_174 ops++addP pm 22 dom_141 5 roots_141 ops++addP pm 23 dom_254 11 roots_254 ops++addP pm 24 dom_126 8 roots_126 ops++addP pm 25 dom_103 5 roots_103 ops++addP pm 26 dom_207 8 roots_207 ops++addP pm 27 dom_222 8 roots_222 ops++addP pm 28 dom_151 6 roots_151 ops++addP pm 29 dom_94 6 roots_94 ops++addP pm 30 dom_175 9 roots_175 ops++addP pm 31 dom_87 6 roots_87 ops++addP pm 32 dom_55 6 roots_55 ops++addP pm 33 dom_119 8 roots_119 ops++addP pm 34 dom_79 6 roots_79 ops++addP pm 35 dom_219 9 roots_219 ops++addP pm 36 dom_167 6 roots_167 ops++addP pm 37 dom_199 5 roots_199 ops++addP pm 38 dom_110 5 roots_110 ops++addP pm 39 dzo_171_4 6 roots_171 ops++addP pm 40 dom_243 9 roots_243 ops++addP pm 41 dom_183 9 roots_183 ops++addP pm 42 dom_250 9 roots_250 ops++addP pm 43 dzo_205_2 6 roots_205 ops++addP pm 44 dzo_235_4 7 roots_235 ops++addP pm 45 dom_218 6 roots_218 ops++addP pm 46 dzo_107_4 6 roots_107 ops++addP pm 47 dzo_157_2 6 roots_157 ops++addP pm 48 dzo_173_2 6 roots_173 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_zo_171_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_zo_205_2_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_zo_235_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_zo_107_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_zo_157_2_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_zo_173_2_141 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_253 12 s (0,roots_253.map (·&&&dom_253)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_253 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 1000003 zs symsG zs (hk 1000003 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 1000003 ys h symsG ys (hk 1000003 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 1000003 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 71 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 71 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 384 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_384 : ∀ i, 384 ≤ i → i < 437 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 53 384 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 437 → Z 8 i = true := (range_split (range_split z8_0 z8_128) (range_split z8_256 z8_384))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 256 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_256 : ∀ i, 256 ≤ i → i < 384 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_384 : ∀ i, 384 ≤ i → i < 439 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 55 384 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 439 → Z 9 i = true := (range_split (range_split z9_0 z9_128) (range_split z9_256 z9_384))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 176 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 48 128 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 176 → Z 10 i = true := (range_split z10_0 z10_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 41 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 41 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 7 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z13 : ∀ i, 0 ≤ i → i < 1 → Z 13 i = true := span_ok (by decide +kernel : span (Z 13) 1 0 = true)
theorem checked (s:Nat) (hs:s≤13):∀ i<NN s,bar dom_255 gM mpG SD SS NN hAt idxH ori 1000003 mkCut s i=true:=by
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 1] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.or, inputs := [3, 10] }, { op := GateOp.or, inputs := [7, 6] }, { op := GateOp.or, inputs := [4, 6] }, { op := GateOp.or, inputs := [2, 11] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.and, inputs := [12, 14] }, { op := GateOp.and, inputs := [5, 15] }, { op := GateOp.and, inputs := [13, 8] }, { op := GateOp.and, inputs := [0, 3] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52486_aux

theorem PEqualNP.Outside.L_meta_52486 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52486_aux.main
