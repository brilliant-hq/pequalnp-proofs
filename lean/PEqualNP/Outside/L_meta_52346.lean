import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52346_aux
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

def dom_82 : Nat := 0x500050000000000050005
def goal_82 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_82 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffccccffffcccceeee0000eeee0000ffffccccffffcccceeee0000eeee0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffffcfcfffffcfccccc0000cccc0000fffffcfcfffffcfccccc0000cccc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffcfcfffffcfceeee0000eeee0000fffffcfcfffffcfceeee0000eeee0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffeeccffffeecceeeeaa00eeeeaa00ffffeeccffffeecceeeeaa00eeeeaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffefcfffffefceeeeaa00eeeeaa00fffffefcfffffefceeeeaa00eeeeaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xffffffffccccccccaaaaaaaa00000000ffffffffccccccccaaaaaaaa00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_100 : Nat := 0x11000000110000001100000011
def goal_100 : Nat := 0xfffffffff0f0f0f0f0f0f0f000000000fffffffff0f0f0f0f0f0f0f000000000
def roots_100 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfffffffff0f0f0f0fafafafa00000000fffffffff0f0f0f0fafafafa00000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfffffffffcfcfcfcfafafafa00000000fffffffffcfcfcfcfafafafa00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffaa00aa00ffaaffaaaa00aa00ffffffffaa00aa00ffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffccccccccff00ff0000000000ffffffffccccccccff00ff0000000000
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffeecceeccffaaffaaaa00aa00ffffffffeecceeccffaaffaaaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfffffffff0f0f0f0fff0fff000000000fffffffff0f0f0f0fff0fff000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffffffffaf0faf0fffafffaaa00aa00fffffffffaf0faf0fffafffaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffffffffcfcfcfcfff0fff000000000fffffffffcfcfcfcfff0fff000000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffffffffefcfefcfffafffaaa00aa00fffffffffefcfefcfffafffaaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffffffcccccccc0000cccc0000ffffffffffffcccccccc0000cccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffffffcccceeeeaaaaeeee0000ffffffffffffcccceeeeaaaaeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffffffcfcfcfcf0f0cccc0000fffffffffffffcfcfcfcf0f0cccc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffffffcfcfefefafaeeee0000fffffffffffffcfcfefefafaeeee0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffffffffff0000ff00ff0000000000ffffffffffff0000ff00ff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffffaa00ffaaffaaaaaaaa00ffffffffffffaa00ffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffffccccffccff00cccc0000ffffffffffffccccffccff00cccc0000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffffeeccffeeffaaeeeeaa00ffffffffffffeeccffeeffaaeeeeaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffffaf0fffafffaaaaaaa00fffffffffffffaf0fffafffaaaaaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffffcfcfffcfff0cccc0000fffffffffffffcfcfffcfff0cccc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffffefcfffefffaeeeeaa00fffffffffffffefcfffefffaeeeeaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffefffefffefffefffefffefffefffeaa00aa00aa00aa00aa00aa00aa00aa00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfafafafafafafafafafafafafafafafaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfccccc0000cccc0000cccc0000cccc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfefefefefefefefefefefefefefefefeeeee0000eeee0000eeee0000eeee0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffccffccffccffccffccffccffccffcccccc0000cccc0000cccc0000cccc0000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffafffafffafffafffafffafffafffaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffccccc0000cccc0000cccc0000cccc0000
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffefffefffefffefffefffefffefffeeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_161 : Nat := 0x30000000300000000000000000000000300000003
def goal_161 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeaaaaaaaa00000000aaaaaaaa00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_164 : Nat := 0x110000001100000000000000000000001100000011
def goal_164 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_164 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfffffffffafafafafffffffffafafafafafafafa00000000fafafafa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcf0f0f0f000000000f0f0f0f000000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffefefefefffffffffefefefefafafafa00000000fafafafa00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_168 : Nat := 0x1010000010100000000000000000000010100000101
def goal_168 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_168 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffffccffccffffffffffccffccff00ff0000000000ff00ff0000000000
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fff0fff000000000fff0fff000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffafffafffaaa00aa00fffafffaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfff0fff000000000fff0fff000000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffefffefffffffffffefffefffafffaaa00aa00fffafffaaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffccccccccffffffffcccccccccccc0000cccc0000cccc0000cccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeaaaaeeee0000eeeeaaaaeeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffafafafafffffffffafafafafafafafaaaaa0000fafafafaaaaa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfcfcf0f0cccc0000fcfcf0f0cccc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffefefefefffffffffefefefefefefafaeeee0000fefefafaeeee0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffccffccffffffffffccffccffccff00cccc0000ffccff00cccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffaaeeeeaa00ffeeffaaeeeeaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffafffafffffffffffafffafffafffaaaaaaa00fffafffaaaaaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfffcfff0cccc0000fffcfff0cccc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffefffefffffffffffefffefffefffaeeeeaa00fffefffaeeeeaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_194 : Nat := 0x5000000000000000500000000000000050000000000000005
def goal_194 : Nat := 0xffffffffffffffffcccccccccccccccccccccccccccccccc0000000000000000
def roots_194 : List Nat := [xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfffffffffffffffffafafafafafafafaf0f0f0f0f0f0f0f00000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffeeffeeffeeffeeeecceecceecceeccaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfffffffffffffffffff0fff0fff0fff0f0f0f0f0f0f0f0f00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffffafffafffafffafaf0faf0faf0faf0aa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffffffffffffffffffcfffcfffcfffcfcfcfcfcfcfcfcfc0000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffefffefffefffefefcfefcfefcfefcaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffccccccccccccccccffffccccffffcccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeffffccccffffcccceeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0fffff0f0fffff0f00000000000000000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfffffcfcfffffcfccccc0000cccc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffefefefefefefefefffffcfcfffffcfceeee0000eeee0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffffffffffffffff00ff00ff00ff00ffff0000ffff00000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffffaa00ffffaa00aaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffccffccffccffccffffccccffffcccccccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffffeeccffffeecceeeeaa00eeeeaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fffff0f0fffff0f00000000000000000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffafffafffafffafffffaf0fffffaf0aaaaaa00aaaaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffcfffcfffcfffcfffffcfcfffffcfccccc0000cccc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffefffefffefffefffffefcfffffefceeeeaa00eeeeaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_224 : Nat := 0x100000001000000010000000100000001000000010000000100000001
def goal_224 : Nat := 0xffffffffffffffffffffffff00000000ffffffff000000000000000000000000
def roots_224 : List Nat := [xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffffffffffaaaaaaaaffffffff00000000aaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffffffffffffffffffccccccccffffffffcccccccc0000000000000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffffffffffeeeeeeeeffffffffccccccccaaaaaaaa00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffffffffffafafafafffffffff0f0f0f0fafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfffffffffcfcfcfcf0f0f0f000000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffffffffffefefefefffffffffcfcfcfcfafafafa00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffffffffffff00ff00ffffffff00000000ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffffaa00aa00ffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffffccffccffffffffccccccccff00ff0000000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffeeffeeffffffffeecceeccffaaffaaaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffffffffffff0fff0fffffffff0f0f0f0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffffffffffafffafffffffffaf0faf0fffafffaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffffffffffcfffcfffffffffcfcfcfcfff0fff000000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffefffefffffffffefcfefcfffafffaaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffffffffffffffff00000000ffffffffffff00000000000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffffffaaaaaaaaffffffffffff0000aaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffccccccccffffffffffffcccccccc0000cccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffeeeeeeeeffffffffffffcccceeeeaaaaeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fffffffffffff0f0f0f0f0f000000000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffafafafafffffffffffff0f0fafafafaaaaa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfffffffffffffcfcfcfcf0f0cccc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffefefefefffffffffffffcfcfefefafaeeee0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffffffffffffffff00ff00ffffffffffff0000ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffffffffaa00ffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffccffccffffffffffffccccffccff00cccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffeeffeeffffffffffffeeccffeeffaaeeeeaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffffffff0fff0fffffffffffff0f0fff0fff000000000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffafffafffffffffffffaf0fffafffaaaaaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffcfffcfffffffffffffcfcfffcfff0cccc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffefffefffffffffffffefcfffefffaeeeeaa00
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
def isoMvS_100:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_100:Lower true dom_100 roots_100 goal_100 4:=lower_iso_b isoMvS_100 (by decide +kernel) lowS_41
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_41
def isoMvS_161:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_161:Lower true dom_161 roots_161 goal_161 4:=lower_iso_b isoMvS_161 (by decide +kernel) lowS_41
def isoMvS_164:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_164:Lower true dom_164 roots_164 goal_164 4:=lower_iso_b isoMvS_164 (by decide +kernel) lowS_41
def isoMvS_168:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_168:Lower true dom_168 roots_168 goal_168 4:=lower_iso_b isoMvS_168 (by decide +kernel) lowS_41
def isoMvS_194:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_194:Lower true dom_194 roots_194 goal_194 4:=lower_iso_b isoMvS_194 (by decide +kernel) lowS_41
def isoMvS_224:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_224:Lower true dom_224 roots_224 goal_224 4:=lower_iso_b isoMvS_224 (by decide +kernel) lowS_41
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
theorem lowS_165:Lower true dom_165 roots_165 goal_165 5:=lower_slice_b [(0x220000002200000000000000000000002200000022,32,33)] (by decide +kernel) lowS_164
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
|0=>0x14815240925545514055248501415
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
def isoMvS_51:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=lower_iso_b isoMvS_51 (by decide +kernel) lowS_27
def isoMvS_53:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_53:Lower true dom_53 roots_53 goal_53 4:=lower_iso_b isoMvS_53 (by decide +kernel) lowS_27
def isoMvS_57:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_45
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_45
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_45
def isoMvS_99:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 4:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_27
def isoMvS_101:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 5:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_45
def isoMvS_105:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_45
def isoMvS_106:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 4:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_27
def isoMvS_108:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 5:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_45
def isoMvS_114:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_45
def isoMvS_120:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 4:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_27
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_45
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 4:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_27
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 4:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_27
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_45
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 4:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_27
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_45
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_45
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_45
def isoMvS_172:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 5:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_165
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_45
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 4:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_27
def isoMvS_197:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 5:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_45
def isoMvS_198:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_165
def isoMvS_201:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_45
def isoMvS_204:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 5:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_45
def isoMvS_210:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_165
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_45
def isoMvS_216:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 4:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_27
def isoMvS_225:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 5:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_165
def isoMvS_226:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_165
def isoMvS_228:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 7:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_169
def isoMvS_232:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 5:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_165
def isoMvS_240:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_240:Lower true dom_240 roots_240 goal_240 5:=lower_iso_b isoMvS_240 (by decide +kernel) lowS_45
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
|0=>0xf9c80
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x25
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_57 5 roots_57 ops++addP pm 1 dzo_57_2 5 roots_57 ops++addP pm 2 dom_51 4 roots_51 ops++addP pm 3 dom_41 4 roots_41 ops++addP pm 4 dom_27 4 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_57_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_51 _ g hchk
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
namespace S_109
def pG:List (Nat×Nat):=[(1,9),(1,33),(4,36),(4,68),(5,13),(5,37),(5,69),(8,9),(8,40),(12,13),(12,44),(12,76),(32,33),(32,36),(32,40),(32,96),(64,68),(64,96),(65,69),(65,73),(65,97),(72,73),(72,76),(72,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_109.map (·&&&dom_109)
def gM:=goal_109&&&dom_109
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x2fc1b
|4,0=>0x1e31b0d6510cdb304b05
|5,0=>0x63bb060aa04afa045a963f75832f042238d223341a1ab00c68
|6,0=>0xf22e738010230dc1ecc0
|7,0=>0xf22e7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc8c80000c8c80000c8c80000c8cb2320000000000003232000000000c0c00000c0c00000c0c000000033300000333000003330000033300c0c00000c0c0000040400000003333000033000000333300003300cccc000000000000cc0000000003332000022220000333200002222cccc0000cccc0000000000000000000000000000000333300003232cccc000000000000cccc00000003030000030300000303000003030cccc0000c0c00000cccc0000c0c3300000033000000330000003300cccc0000cccc0000c8c800000002222000022220000222200002222
|0,1=>0x33330000333300002222000022224444000000000000444400000000000000032320000000000003232cccc0000cccc0000cccc0000cc0333300003333000033330000000000cc000000cc000000cc000000000000000000000001111000000000c0c0000000000000c0c00000003333000033330000111100000000
|_,_=>0
def sP:Nat→Nat
|0=>0x144401ca2200e5113003d0a2200e51101739444058f5288803d0a2034e51101339444048e32881139444040e5138803944069d45610072880b3a92401ca8110e62888018820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682ced9ab2f652c8d8f2986
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 25 110 0x3fffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1d29d283a0929da1329d2832bc289
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x523200000021110001
|6,0=>0x918171
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0x3ff77d543cc286080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x360021504
|6,0=>0x7a89
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_108 5 roots_108 ops++addP pm 1 dom_41 4 roots_41 ops++addP pm 2 dom_105 5 roots_105 ops++addP pm 3 dom_100 4 roots_100 ops++addP pm 4 dom_45 5 roots_45 ops++addP pm 5 dom_101 5 roots_101 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_109 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_100 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_101 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_108 5 s (0,roots_108.map (·&&&dom_108)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_109 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_108 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_109==dom_109)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_109 gM v ys):RunD true dom_109 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_109 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_109 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_109 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_109 roots_109 goal_109 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_109
theorem lowS_109:Lower true dom_109 roots_109 goal_109 8:=S_109.noCircuit
theorem lowS_115:Lower true dom_115 roots_115 goal_115 6:=lower_slice_b [(0xa000a000a000a000a000a000a000a,16,17)] (by decide +kernel) lowS_114
theorem lowS_143:Lower true dom_143 roots_143 goal_143 6:=lower_slice_b [(0xcccc0000000000000000000000000000cccc,128,130)] (by decide +kernel) lowS_141
theorem lowS_151:Lower true dom_151 roots_151 goal_151 5:=lower_slice_b [(0xaa00aa00000000000000000000000000aa00aa,16,17)] (by decide +kernel) lowS_150
theorem lowS_158:Lower true dom_158 roots_158 goal_158 5:=lower_slice_b [(0x5050505000000000000000000000000050505050,128,132)] (by decide +kernel) lowS_154
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_slice_b [(0xaa000000aa0000000000000000000000aa000000aa,32,33)] (by decide +kernel) lowS_166
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_slice_b [(0xc0c00000c0c000000000000000000000c0c00000c0c,128,130)] (by decide +kernel) lowS_169
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_slice_b [(0x30300000303000000000000000000000303000003030,32,36)] (by decide +kernel) lowS_169
def dzo_165_16:=0x3300000033000000000000000000000033000000330000
def gzo_165_16:=0x3300000032000000000000000000000032000000220000
def gsh_165_16:=0x330000003200000000000000000000003200000022
theorem lowS_zo_165_16_164:Lower true dzo_165_16 roots_165 gzo_165_16 5:=lower_iso_b (d1:=dom_165) (r1:=roots_165) (T1:=gsh_165_16) [(dom_165,16)] (by decide +kernel) (lower_slice_b (T:=gsh_165_16) [(0x220000002200000000000000000000002200000022,0,1)] (by decide +kernel) lowS_164)
namespace S_181
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,129),(4,36),(4,132),(5,21),(5,37),(5,133),(16,17),(20,21),(20,52),(20,148),(32,33),(32,36),(32,160),(48,49),(48,52),(48,176),(128,129),(128,132),(128,160),(144,145),(144,148),(144,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_181.map (·&&&dom_181)
def gM:=goal_181&&&dom_181
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xf3aae
|5,0=>0x409f8
|6,0=>0x3afc8
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3300330033003300000000000000000033003300000000c000c000c000c0000000000000000000c000c000c000c3300330000000000000000000000000033003300000000cc000000cc0000000000000000000000cc000000cc00022002200220022000000000000000000220022002200220c000c000c000c0000000000000000000c000c00000003300330033003300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8ea1a3a84688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 182 0x3fffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x81
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
addP pm 0 dom_177 5 roots_177 ops++addP pm 1 dom_149 4 roots_149 ops++addP pm 2 dzo_165_16 5 roots_165 ops++addP pm 3 dom_165 5 roots_165 ops++addP pm 4 dom_164 4 roots_164 ops++addP pm 5 dom_53 4 roots_53 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_181 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_165_16_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_53 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_177 5 s (0,roots_177.map (·&&&dom_177)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_181 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_177 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_181==dom_181)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_181 gM v ys):RunD true dom_181 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_181 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_181 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_181 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_181 roots_181 goal_181 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_181
theorem lowS_181:Lower true dom_181 roots_181 goal_181 7:=S_181.noCircuit
theorem lowS_211:Lower true dom_211 roots_211 goal_211 6:=lower_slice_b [(0xa000a00000000000a000a00000000000a000a00000000000a000a,16,17)] (by decide +kernel) lowS_210
namespace S_214
def pG:List (Nat×Nat):=[(2,18),(2,66),(2,130),(4,68),(4,132),(6,22),(6,70),(6,134),(16,18),(16,80),(20,22),(20,84),(20,148),(64,66),(64,68),(64,80),(64,192),(128,130),(128,132),(128,192),(144,146),(144,148),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_214.map (·&&&dom_214)
def gM:=goal_214&&&dom_214
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xb098e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x550000000000000055000000000000005500000000000000550000a000a00000000000a000a00000000000a000a00000000000a000a1100110000000000110011000000000011001100000000001100112a802a800000000000000000000000002a802a8000000000000000550055000000000055005500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 215 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_212 5 roots_212 ops++addP pm 1 dom_86 5 roots_86 ops++addP pm 2 dom_210 5 roots_210 ops++addP pm 3 dom_198 5 roots_198 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_214 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_198 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_212 5 s (0,roots_212.map (·&&&dom_212)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_214 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_212 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccccccccccccccccccc,126)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_214==dom_214)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_214 gM v ys):RunD true dom_214 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_214 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_214 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_214 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_214 roots_214 goal_214 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_214
theorem lowS_214:Lower true dom_214 roots_214 goal_214 7:=S_214.noCircuit
def isoMvS_87:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_iso_b isoMvS_87 (by decide +kernel) lowS_61
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 7:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_59
def isoMvS_103:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_61
def isoMvS_107:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 7:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_59
def isoMvS_110:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_61
def isoMvS_118:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 8:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_109
def isoMvS_121:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 6:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_115
def isoMvS_122:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_59
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 6:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_115
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 6:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_61
def isoMvS_174:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_167
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 6:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_115
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 7:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_59
def isoMvS_185:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 8:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_171
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_59
def isoMvS_203:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_109
def isoMvS_205:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 8:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_109
def isoMvS_206:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 6:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_167
def isoMvS_217:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 6:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_115
def isoMvS_218:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 7:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_181
def isoMvS_220:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 6:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_61
def isoMvS_227:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 7:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_214
def isoMvS_229:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 8:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_173
def isoMvS_230:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 8:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_173
def isoMvS_233:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_173
def isoMvS_234:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 7:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_214
def isoMvS_236:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 8:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_173
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 6:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_211
def isoMvS_242:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 7:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_214
def isoMvS_244:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 8:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_171
def isoMvS_248:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 7:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_181
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xf0f0f0f0f0f0f0f0,32,36)] (by decide +kernel) lowS_59
theorem lowS_111:Lower true dom_111 roots_111 goal_111 9:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc,64,66)] (by decide +kernel) lowS_109
theorem lowS_119:Lower true dom_119 roots_119 goal_119 9:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_118
def dzo_121_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_121_2:=0xc0c0c0c0c0c0c0c0c0c0c080c0c0800
def gsh_121_2:=0x3030303030303030303030203030200
theorem lowS_zo_121_2_41:Lower true dzo_121_2 roots_121 gzo_121_2 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_2) [(dom_121,2)] (by decide +kernel) (lower_slice_b (T:=gsh_121_2) [(0x3030000030300000303000003030000,0,16),(0x3030303030303030000000000000000,0,64)] (by decide +kernel) lowS_41)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,18),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,40),(10,11),(10,26),(10,42),(10,74),(16,17),(16,18),(16,80),(24,25),(24,26),(24,56),(24,88),(32,33),(32,40),(32,96),(34,35),(34,42),(34,50),(34,98),(48,49),(48,50),(48,56),(48,112),(64,66),(64,80),(64,96),(65,67),(65,73),(65,81),(65,97),(72,73),(72,74),(72,88),(72,104)]
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
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_59 7 roots_59 ops++addP pm 2 dom_107 7 roots_107 ops++addP pm 3 dom_91 7 roots_91 ops++addP pm 4 dom_121 6 roots_121 ops++addP pm 5 dzo_121_2 6 roots_121 ops++addP pm 6 dom_115 6 roots_115 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_121_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_115 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 7 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
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
def dzo_27_4:=0xf0f0f0f0
def gzo_27_4:=0xe0e0a000
def gsh_27_4:=0xe0e0a00
theorem lowS_zo_27_4_27:Lower true dzo_27_4 roots_27 gzo_27_4 4:=lower_iso_b (d1:=dom_27) (r1:=roots_27) (T1:=gsh_27_4) [(dom_27,4)] (by decide +kernel) (lower_slice_b (T:=gsh_27_4) [] (by decide +kernel) lowS_27)
def dzo_155_4:=0xf0f0f0f0000000000000000000000000f0f0f0f0
def gzo_155_4:=0xf0f0f0f0000000000000000000000000e0e0a000
def gsh_155_4:=0xf0f0f0f0000000000000000000000000e0e0a00
theorem lowS_zo_155_4_27:Lower true dzo_155_4 roots_155 gzo_155_4 5:=lower_iso_b (d1:=dom_155) (r1:=roots_155) (T1:=gsh_155_4) [(dom_155,4)] (by decide +kernel) (lower_slice_b (T:=gsh_155_4) [(0xf0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_27)
namespace S_159
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,129),(2,18),(2,130),(3,11),(3,19),(3,131),(4,132),(5,13),(5,21),(5,133),(6,22),(6,134),(7,15),(7,23),(7,135),(8,9),(8,136),(10,11),(10,26),(10,138),(12,13),(12,140),(14,15),(14,30),(14,142),(16,17),(16,18),(20,21),(20,22),(20,148),(24,25),(24,26),(24,152),(28,29),(28,30),(28,156),(128,129),(128,130),(128,132),(128,136),(144,145),(144,146),(144,148),(144,152)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffff
def xsM:=roots_159.map (·&&&dom_159)
def gM:=goal_159&&&dom_159
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>7
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x1941e
|4,0=>0x7524f4d8811bf9e11f93
|5,0=>0xcf1dcc4c87c3fa4a96b28941f2a91523aaf1d3b11d25507893
|6,0=>0xfd1ebf177ee4721cbab5beed87da7f74778
|7,0=>0x932a5
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff0fff0f000000000000000000000000ff00ff0000ff00ff00000000000000000000000000aa00aa0f0f0f0f00000000000000000000000000000000fefefefe000000000000000000000000fefefefeffffffff000000000000000000000000ffff0000eeeeeeee000000000000000000000000eeeeeeeeafafafaf000000000000000000000000aaaaaaaaffff0000000000000000000000000000ffff0000cccccccc000000000000000000000000ccccccccaaaaaaaa000000000000000000000000aaaaaaaa00af00af00000000000000000000000000aa00aaffffffff00000000000000000000000000000000ff00ff00000000000000000000000000ff00ff00f0f0f0f0000000000000000000000000f0f0f0f0eeeeeeee000000000000000000000000eeee0000ffffffff000000000000000000000000aaaaaaaa
|0,1=>0xfafafafa000000000000000000000000fafafafafff0fff0000000000000000000000000fff0fff0ffffffff000000000000000000000000ff00ff000000eeee0000000000000000000000000000eeee3333333300000000000000000000000033330000
|_,_=>0
def sP:Nat→Nat
|0=>0x40e87311033988d44c673110311c06220625188b188e62224311cc4189468916311a0440ce931163128c443c6731102399c440c4a011035188d58c4701903628c458c4a00c413110352488398a418820
|1=>0x10311cc4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x1350e5095045
|5,0=>0x4e64864263c63663062a62461e6186
|6,0=>0x7a67466e66776165b6547
|7,0=>0x806
|_,_=>0
def wAt:=mkWire dB 21 160 0xffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x119112189311399411191129399
|_=>0
def oO:Nat→Nat→Nat
|5,0=>2
|6,0=>0x81716151413121
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0xbf76ae95c306f24c8748b902003001000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1032
|6,0=>0x75b6948
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 11 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_157 6 roots_157 ops++addP pm 1 dom_150 4 roots_150 ops++addP pm 2 dom_153 5 roots_153 ops++addP pm 3 dom_143 6 roots_143 ops++addP pm 4 dzo_27_4 4 roots_27 ops++addP pm 5 dom_155 6 roots_155 ops++addP pm 6 dzo_155_4 5 roots_155 ops++addP pm 7 dom_27 4 roots_27 ops++addP pm 8 dom_158 5 roots_158 ops++addP pm 9 dom_154 4 roots_154 ops++addP pm 10 dom_151 5 roots_151 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_159 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_27_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_155_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_151 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_157 6 s (0,roots_157.map (·&&&dom_157)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_159 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_157 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_159 gM v ys):RunD true dom_159 gM v (ori ys):=h
def Z (s:Nat):=barP dom_159 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_159 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_159 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_159 roots_159 goal_159 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_159
theorem lowS_159:Lower true dom_159 roots_159 goal_159 8:=S_159.noCircuit
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_slice_b [(0xcccc0000cccc00000000000000000000cccc0000cccc,128,130)] (by decide +kernel) lowS_173
def dzo_167_16:=0xff000000ff0000000000000000000000ff000000ff0000
def gzo_167_16:=0xff000000fe0000000000000000000000fe000000ee0000
def gsh_167_16:=0xff000000fe0000000000000000000000fe000000ee
theorem lowS_zo_167_16_164:Lower true dzo_167_16 roots_167 gzo_167_16 6:=lower_iso_b (d1:=dom_167) (r1:=roots_167) (T1:=gsh_167_16) [(dom_167,16)] (by decide +kernel) (lower_slice_b (T:=gsh_167_16) [(0xaa000000aa0000000000000000000000aa000000aa,0,1),(0xcc000000cc0000000000000000000000cc000000cc,0,2)] (by decide +kernel) lowS_164)
namespace S_183
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,129),(2,18),(2,130),(3,19),(3,35),(3,131),(4,36),(4,132),(5,21),(5,37),(5,133),(6,22),(6,38),(6,134),(7,23),(7,39),(7,135),(16,17),(16,18),(20,21),(20,22),(20,52),(20,148),(32,33),(32,36),(32,160),(34,35),(34,38),(34,50),(34,162),(48,49),(48,50),(48,52),(48,176),(128,129),(128,130),(128,132),(128,160),(144,145),(144,146),(144,148),(144,176)]
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
|4,0=>0xd8460a655855b0f3f4dd112a3
|5,0=>0xefc69dde2bdb852cdd59c85bbc47857feb369cf064153624c75a9b440fed28fe714cfc0cb0e
|6,0=>0xfdaa3f928ef79aff39aef1569de6d4d8916d721cbe2f2b4a95b4392b3e259f90a979bb86a307992074bf2718856fe3764bf05f3824683d44f6740fed404403d86b3bf9536c14267a6223b421f3e20c0916b7d14bc210fe00de960ad60
|7,0=>0xfdaa3ede7acf017b3401ad864a4c5d7dc0c490a514b6813292
|8,0=>0x8a6fe
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff00f000f0ff00ff00ff00ff000000000000000000ff000000ff0000f000f000f000f0000000000000000000f000f000000000f000f000f000f0000000000000000000f000f000f000f0ff00ff00ff00ff000000000000000000ff00ff00000000ff00ff00aa00aa000000000000000000aa00aa00aa00aaff00ff00000000000000000000000000ff00ff00000000fe00fe00fe00fe000000000000000000fe00fe00ee00eefa00fa00fa00fa000000000000000000fa00fa00aa00aaff00ff00ff00ff00000000000000000000000000000000000000000f000f0000000000000000000f000f0000000000000000ff00ff000000000000000000ff00ff00000000ff000000ff0000000000000000000000ff000000ff0000cc00cc00cc00cc000000000000000000cc00cc00cc00ccaa00aa00aa00aa000000000000000000aa00aa00aa00aa0f000f000f000f0000000000000000000f000f00000000
|0,1=>0xff000f00ff000f000000000000000000ff000000ff0000ff000000000000000000000000000000ff000000ff000000000000ff0000000000000000000000ff000000ff0000ff00ff00ff0000000000000000000000ff000000ff0000f000f000f000f0000000000000000000ff00ff00f000f0ff00ff00f000f0000000000000000000ff00ff00f000f0ff00ff00ff00ff000000000000000000f000f000f000f0ff00ff00ff00ff0000000000000000000f000f00000000ff00ff00f000f0000000000000000000f000f000f000f0ff00ff000000000000000000000000000000000000000000000000000000000000000000000000ff000000ff00000f000f000f000f0000000000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000ff00ff00000000000000000000000000000000ff00ff000f000f000000000000000000ff00ff000000000f000f000000000000000000000000000f000f00000000
|0,2=>0xf000f0000000000000000000f000f000f000f0000000000000000000000000000000000f000f00000000ff00ff00ff00ff000000000000000000ff00ff00f000f0ff00ff00cc00cc000000000000000000cc00cc00cc00ccf000f000000000000000000000000000ff00ff00000000ff000000ff00ff000000000000000000ff000000ff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x3020462c33020562c90cd08118b0cc08a68b0d90812430816142c40cc0812c35c204b0c204058b2431c218938204018954204018b0c20505040cc0812430810064430814063c938c0812431c218b0c20452c308a0090c81c61030811440c2040
|1=>0x2433020546890d908118980c0811897cc08118978c0811890d708119a2c33020462c33020501890c204019124330204668938c08118938c0814066930cc08118b24e30204625d30204625c3020462c954c0811894ce3020466c90cc0811894d5
|2=>0xcc08119224364c08119a24330204624330205018b2433020462430814065090e508118b24364c0812433020641a32433020462433220464c330205224330205818f2433020462c90c20401898433020462433020401890cd0811890cc08a18b
|3=>0x90cc08118b2433020462530cc0811890cc08119424e302046255302046243302046589
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a94c8c5e62c314d49ac47620b0ed86ac30515309183cc195
|6,0=>0x15e7abbd45a94f4379e3cd9a60d297913c6de28f0d783b4059f4ef3776b39d9c2cdb66a3b35d8ecc075cbac9d56ea474f3261922e8a741b9f1cecc6f7
|7,0=>0x344f9b7ca3e39b10d817bd3dcded8f657
|8,0=>0x1a96
|_,_=>0
def wAt:=mkWire dB 38 184 0xffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x919246cc1a0c6431b246091a306493124ccc5b24609190964918246891b24649532cc0919056491824643492468351306834b2468c5924609192464b3324643190c6491b0d6c9180d64918246491924609190564918246491931649184d2491a246cd052cc0919
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xa324400000630000000000000330000000003
|6,0=>0x2f2b8400002c2a880000291a040098a428c400849f2749b2685915c8005855150400489023c4000000034800
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xf6fd9eef7bde75bc6709c04cc3049022c8218460140421003b0a8120400e00c0200400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x10c010c020000300007
|6,0=>0xe034c0046200156044962a567134020314aa9cd89025e2
|7,0=>0x35abdafbde339
|8,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_182 7 roots_182 ops++addP pm 1 dom_51 4 roots_51 ops++addP pm 2 dom_150 4 roots_150 ops++addP pm 3 dom_181 7 roots_181 ops++addP pm 4 dom_179 6 roots_179 ops++addP pm 5 dom_163 5 roots_163 ops++addP pm 6 dom_55 5 roots_55 ops++addP pm 7 dom_151 5 roots_151 ops++addP pm 8 dzo_167_16 6 roots_167 ops++addP pm 9 dom_167 6 roots_167 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_183 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_167_16_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_167 _ g hchk
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
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_slice_b [(0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c,16,18)] (by decide +kernel) lowS_185
theorem lowS_189:Lower true dom_189 roots_189 goal_189 9:=lower_slice_b [(0x303030303030303000000000000000003030303030303030,32,36)] (by decide +kernel) lowS_185
theorem lowS_190:Lower true dom_190 roots_190 goal_190 8:=lower_slice_b [(0x505050505050505000000000000000005050505050505050,32,36)] (by decide +kernel) lowS_186
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=lower_slice_b [(0xcccc000000000000cccc000000000000cccc000000000000cccc,64,66)] (by decide +kernel) lowS_205
theorem lowS_215:Lower true dom_215 roots_215 goal_215 8:=lower_slice_b [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,16,17)] (by decide +kernel) lowS_214
theorem lowS_219:Lower true dom_219 roots_219 goal_219 9:=lower_slice_b [(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000,1,17)] (by decide +kernel) lowS_203
def dzo_86_8:=0x550055000000000055005500
def gzo_86_8:=0x550054000000000044000000
def gsh_86_8:=0x5500540000000000440000
theorem lowS_zo_86_8_86:Lower true dzo_86_8 roots_86 gzo_86_8 5:=lower_iso_b (d1:=dom_86) (r1:=roots_86) (T1:=gsh_86_8) [(dom_86,8)] (by decide +kernel) (lower_slice_b (T:=gsh_86_8) [] (by decide +kernel) lowS_86)
def dzo_210_8:=0x5000500000000000500050000000000050005000000000005000500
def gzo_210_8:=0x5000500000000000500050000000000050004000000000004000000
def gsh_210_8:=0x50005000000000005000500000000000500040000000000040000
theorem lowS_zo_210_8_82:Lower true dzo_210_8 roots_210 gzo_210_8 5:=lower_iso_b (d1:=dom_210) (r1:=roots_210) (T1:=gsh_210_8) [(dom_210,8)] (by decide +kernel) (lower_slice_b (T:=gsh_210_8) [(0x50005000000000005000500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_214_8:=0x55005500000000005500550000000000550055000000000055005500
def gzo_214_8:=0x55005500000000005500550000000000550054000000000044000000
def gsh_214_8:=0x550055000000000055005500000000005500540000000000440000
theorem lowS_zo_214_8_86:Lower true dzo_214_8 roots_214 gzo_214_8 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_8) [(dom_214,8)] (by decide +kernel) (lower_slice_b (T:=gsh_214_8) [(0x550055000000000055005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_86)
namespace S_222
def pG:List (Nat×Nat):=[(2,18),(2,66),(2,130),(4,68),(4,132),(6,22),(6,70),(6,134),(8,136),(10,26),(10,74),(10,138),(12,76),(12,140),(14,30),(14,78),(14,142),(16,18),(16,80),(20,22),(20,84),(20,148),(24,26),(24,88),(24,152),(28,30),(28,92),(28,156),(64,66),(64,68),(64,80),(64,192),(72,74),(72,76),(72,88),(72,200),(128,130),(128,132),(128,136),(128,192),(144,146),(144,148),(144,152),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_222.map (·&&&dom_222)
def gM:=goal_222&&&dom_222
def NN:Nat→Nat
|3=>1
|4=>30
|5=>85
|6=>62
|7=>14
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xc5874
|4,0=>0xfd34bfabd9ed023dc09fd5b44d56d3d4437cddfcc2441bcc608e5418d34179c4476a416fe496e45c6c78768d265f8df5ee844ac16419292b2f51ee521cef513048114f10dc800d69a058c0
|5,0=>0xfb7abf6075f5055f4a2df37feed20eebe30eb95ce8fa0e72bce297be0636de9bedc9bfd01f1cedd2ce464cb823ca88ac96a3c6ff4c3ba5c3b93bbf97b8a69b22a2afe95ae4a8a6cd2a57f6a2d85a10709d1049b93a971f794be0924f387984861db8197580a2c8074c7d01f7b5107a40b778e971f7c70bfc6e73a6cf14692e168b4c683ae6826667605671c05d12a589da55bcf5513f4dccc47bbe4469b442484298440e85402ae3f4e439eb83726336cd83448933cee2cf3a2a70326ed42353322ed11ed1f1c0eb1571f1448311a6008ee9040d2
|6,0=>0xf7b63f67a7f450fefc94ed420ec54beb67ddea34dbc39d8266d53bbd2756cf4c1ca143c762cc0e65be262bd06bb58d0b022daaaf7aa876a932d9d2f58f5ef8bc5a88fce7c60b772af75d8373d3a71ce16c2a167197579b05678155c8050ee2500464fa484d61748f3548c1e43aa33e10d3bafd3b7f735d6d320f631edc31a942a9f925d1c243e223aec1ffc11ef1a1142b0e4b0088240469e035f0
|7,0=>0xfa83ad9300d5f6dcb937c0492abeb8abba178bdf66b6d577e137962205e80c45705964
|8,0=>0xbad5e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaa000000008888888800000000aaaa888800000000888888894141414000000001414141400000000141414140000000014141414002aaaaa80000000002aa22a8000000000002aaa800000000000222255555555000000005554555400000000000000000000000000000000aaaaaaaa00000000a0a0a0a000000000a8a8a8a800000000a0a0a0a111111110000000011111111000000001111111100000000111111112aaa8000000000002aaa8000000000002aaa8000000000002aaa800054545454000000005454545400000000545454540000000000000000aaaaaaaa00000000aaaaaaaa00000000aaaa000000000000aaaa000155555554000000011111111000000001555555540000000111111112aaaaaaa8000000000000000000000002aaaaaaa800000000000000055555555000000005555555500000000000000000000000000000000aa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa0151515150000000015151515000000001515151500000000151515152aaaaaaa8000000022222222000000002aaa8000000000002222000055555555000000005555555500000000555555550000000000000000
|0,1=>0xa0a0a0a00000000080a080a000000000a0a0a0a000000000808080800000000000000015555555400000000000000000000000111111110000000000000000222aa22a8000000000000000000000002222222255555555000000004455445500000000555555550000000044444444aaaaaaaa00000000aaaa000000000000aaaaaaaa00000000aaaa000000000000000000015555555400000000000155540000000155540000002828280000000000280028000000000000282800000000000000055555555000000000055005500000000555555550000000000000000aaaaaaaa00000000aaaa000000000000aaaa888800000000aaaa000000000000000000015551555000000000000000000000000155515550080808080000000000000000000000000808080800000000000000055555555000000005050505000000000555550500000000050505050aaaaaaaa00000000aaaaaaaa0000000088888888000000008888888955555554000000015555555400000001555555540000000111111110080808080000000000080008000000000808080800000000000000055555555000000005555555500000000555555550000000055550000
|0,2=>0x2222222200000000222222220000000022220000000000002222000115151514000000011111111000000001151515140000000111111112aaaaaaa80000000000000000000000022222222000000000000000011551155000000000055005500000000111111110000000000000000020202020000000002000200000000000202020200000000020002015555555400000000000000000000000155540000000000000000000028282828000000002828282800000000000028280000000000000001111111100000000111111110000000011111111000000000000000000000000000000000000000000000000aaaaaaaa000000008888888800000000000000015555555400000000000000000000000155540000000000000000000000000000000000000002aaa8000000000000000555555550000000055555555000000001111111100000000000000008888888800000000888888880000000088888888000000008888000044444444000000004440444000000000444444440000000044404440082808280000000000280028000000000808080800000000000000045454545000000004445444500000000454545450000000044444444
|0,3=>0xaa00aaaa00000000aa00aa8800000000aa00aaaa00000000aa00aa8951555154000000015155515400000001515151500000000151515152aaaaaaa800000002aaa2aaa000000002aaaaaaa800000002aaa2aaa000044440000000000004444000000000000555500000000000044440000aaaa0000000000000000000000000000aaaa000000000000000001555554000000000154015400000000000155540000000000000002a80aa80800000002a802a80000000002a80aa80800000002a802a80050505050000000005050505000000000505050500000000040404048a8a8a8a000000008a8a8a8a000000008a8a8a8a000000008888888814141414000000000014001400000000141414140000000000000002aaa2aaa000000002aaa2aaa000000002aaa2aaa000000002aaa2aaa5555555500000000554455440000000055555555000000005544554400000000000000000000000000000000aaaaaaaa00000000aaaa0000444444440000000044444444000000004444444400000000444400000002aaa80000000000022220000000000002aaa800000000000222200550055000000000055005500000000000000000000000000000000
|0,4=>0xaaaa000000000000aaaa000000000000aaaa000000000000888844444444000000000044004400000000444444440000000000000002aaaaaaa800000002aaaaaaa8000000000002aaa800000000000222255555555000000005555555500000000000055550000000000000000aaaaaaaa00000000aa00aa0000000000aaaaaaaa00000000aa00aa0155555554000000015555555400000001555400000000000000000000282828280000000028282828000000002828282800000000000000044444444000000004444444400000000555555550000000044444444000000000000000000000000000000000000aaaa00000000000088880001555400000000000151500000000000015554000000000001515000000000000000000000000000000002aaaaaaa800000000000000005050505000000000505050500000000010101010000000000000000020202020000000002020202000000000202020200000000000000000000000000000001111111100000000000011110000000011111111222aa22a80000000222aa22a8000000022222222000000002222222205050505000000000505050500000000050505050000000005050000
|0,5=>0xaa88aa8800000000aa88aa8800000000aa88aa8800000000aa88aa8800000000000000000000000000000001555400000000000155540002a802aaa800000002a802a80000000002a802aaa800000002a802a80555500000000000055550000000000005555555500000000555500002222222200000000220022000000000022222222000000002200220000000000000000000000000000000000444444440000000000000002a88aa88800000002a802a80000000002a88aa88800000002a802a80555555550000000055555555000000005454545400000000545454540000aaaa000000000000aaaa000000000000aaaa000000000000000155555554000000015151515000000001555555540000000151515152aaaaaaa800000002aaaaaaa800000002aaaa222000000002aaaa22211111111000000000000000000000000111111110000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x6387800638501001c1823c14496041820904742841208e05086c18e1e10d031c28209064c288120c70f001c1820c0048a0a642090418c042e0c7060824b0a2a1018e260428706505000e0c1120a2450522108031c3c20e14342841208505182418b14004830c2020304042840608080
|1=>0xe0c71214144831c2802d1238505581048214ac2840e0c70a00a8483044c005120c50552103831c282a8120c11e0a10483049c2844c0c70a4a1048328282840e0c70f0a1018e14042840e0c70a0a904831c189800e0c7230a104824414209141508412805050824194140048a3e14207
|2=>0x42828412f410a0a1018e14f02844c0c70a76103a60638500123850574104b90428284120c5380a104836e28284120830508c048a0ad82096a2829508d070a62142330e0c70a0a2418b14142070608985120c7065a103831cc82841c2988508c038304bc284120c505101048304b8284
|3=>0x6083310a104831c3c2840e0c1060a1048314162041228c056c1048314161840e0c10a001448e382828412085180a103831d0828412383410a10b831c28284120c5400a103831c4d7850e0ca0a0a1048304482847e385310a103831c18500200c70a54104b40418284123830a30104be
|4=>0xc1420706383130a1c18a80142031c2a785086c18e14a8209050428412385059c1018e15342840e0c70a0b304831cc82840e0c70a3c1658e14c42840e0c70a0b284831c2802a123851d0a1038314002c9120c1480a1018e151c28406085460a10483041800412d41060a10483041a284
|5=>0x1c282d0082418e1416604120c70a3c14209074810a0a104831c9c505082470a0aec230361c18e14142031c29885081c18e1415284120c5000b242096a08505081c18214142090638505541038906385000b443831c28284132c70614142070638500a02470a31402092c085050826582
|6=>0xaa020906385055a1048e0c28284601c18e14155040e0c70a0aec21b132c70a0a104831c282a408265821414207063898a0a241821414a84120c70a0140210120c70a0a103831c2978508241d40428284120c7062614209060830508253031c28284120c70a0b4c209063898a0014383
|7=>0x155c284120c748141420906282c9082418e0c28004120c70a0b582090428284602418e0c2a284063830a621420906385054a103831c1850508403831c282840e0c70a001448e1460284662418e14142074c0c70a0a10483044c284120c7121414209aa385050825a0e0c28284120c70a
|8=>0x826d8e141421b120c70a0a104831c4c50508241821414207120c70a0a104cb1c28284120c706141425a0638505081c18e1414209063850576104831c280050824741141420906085000a1048e14168046026c8e1414258120c70a0a104b41c28284120c10a0b1421b123850508c048e
|9=>0x90638505082418e1416284123850508c04831c282d0
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x4aa8905116a219440a87c50eea1c9436a86850c6a17942ca854509ea129422a8405076a0d9418a82c504ea08940ea8185026a039404a8045
|5,0=>0x424c831903320063f4c7d18f731e863c4c7718eb31d06394c7118df31b86364c6b18d331a06334c6518c731886304c5f18bb317062d4c5918af315862a4c5318a331415276c4d5897b1296248a47988c31126218c41988030fa61e8c3b987430e261b8c35986830ca6188c2f985c30b26158c299850309a6
|5,1=>0x28f6512ca0d93eb27764e2c9ad932b26054b4c95192732486484c8f191b32306454c89190f32186
|6,0=>0x218b42a7846f075a0b3c106812f009dfe33f577decfa1df0bbdb67a8ef35de33bbf7770eec99d633a5773cee619c8bb8b6708edf5dbb3b6f76d0ed85dad3b53769acd1d9a03b397664ecadd923b1d762ecc41d84bb0275f6ebd1d76bae675beeb61d68bacb6588eaf5d5bb2b16554ea8dd4e3a957
|7,0=>0x2463c8668fef1e5a393c6b78cad179e2c34517896d115a1f3c377
|8,0=>0x4936
|_,_=>0
def wAt:=mkWire dB 92 223 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x61212161215121a14150e1612111c020a1106091c2912111c290e1412110a110e2912111415061514166a171c290615141506121c291c020a130609141514151c291c290e2b0c111415141506190e1706121c6204161c2914151c291211141126140e2b1c2904000a110416261526140e141c290c130e180a11141526150e18
|1=>0xe161211121114150e15121112110a110ac10612361312150e17121114111c2914010a11074114160619141514020a1126141411141506120e141211121612110615a011141606151c291211141104161c2914160e1512110e2b121104111c29141514151c290e1712110a1112111416761112162617141104151c290c131415
|2=>0xa13061214160629121514111c291211061514151213121112160a1114c106120a111c290612141606ed1216061914150a131c290612962b061515150a131c020a1114150a112616141106121c2914150a13121a1415
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11000000000000000000001
|5,0=>0x2120001f20000000000000001e10000000000000000001d10001b20001a10001910000000000000001810000000000001711611421310000001030f10000000d20b20a1091081000000071061000000000051000000000041000022000
|5,1=>0x2b1000292281271000000000252000000000000000000000000000241231000
|6,0=>0x9b29929729520009329129018e28c28a28828628428228027e27c27a27827627427227026e26c26a26826626426226025f15d25b25925725615425225024f14d24b20004a14824624424224023e23d13b23923723523323123012e22c2
|7,0=>0xaa1a91a81a71a61a51a41a31a21a11a019f19e19d1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x2280113c088804100200008000280012300400018000be005c002c8016000ac005300290014400a00045002000070003000140008000280010000400018000800020000
|1=>0x802c2517d20be845d4227a00408284305f14230811838be181f0abf8517c28b6144f0a000413c209210060802020080abe054f02a38117c08ba045b022c8116008a80451
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x80000000002
|5,0=>0x70160870000060000000000000070800006006c00000001c000000000700300702a01a0000070000000852d70008440006c10821406871c0000080000080280
|6,0=>0xb94af103451be0f48a37021d3543a3b5f8a943ddce56c4d26ceca567a421fc99d20085203793ef14c353ce591c476
|7,0=>0xf30ef5ee6a26fbb9a5efc
|8,0=>0x1e
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 17 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_218 7 roots_218 ops++addP pm 1 dom_204 5 roots_204 ops++addP pm 2 dom_220 6 roots_220 ops++addP pm 3 dom_86 5 roots_86 ops++addP pm 4 dzo_86_8 5 roots_86 ops++addP pm 5 dom_210 5 roots_210 ops++addP pm 6 dom_214 7 roots_214 ops++addP pm 7 dom_198 5 roots_198 ops++addP pm 8 dom_216 4 roots_216 ops++addP pm 9 dzo_210_8 5 roots_210 ops++addP pm 10 dom_206 6 roots_206 ops++addP pm 11 dom_212 5 roots_212 ops++addP pm 12 dzo_214_8 6 roots_214 ops++addP pm 13 dom_150 4 roots_150 ops++addP pm 14 dom_154 4 roots_154 ops++addP pm 15 dom_158 5 roots_158 ops++addP pm 16 dom_82 4 roots_82 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_222 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_86_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_210_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_214_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_82 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_218 7 s (0,roots_218.map (·&&&dom_218)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_222 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_218 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_222 gM v ys):RunD true dom_222 gM v (ori ys):=h
def Z (s:Nat):=barP dom_222 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 30 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 30 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 85 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 85 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 62 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 62 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 14 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_222 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_slice_b [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,32,33)] (by decide +kernel) lowS_230
namespace S_235
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(2,66),(2,130),(3,11),(3,35),(3,67),(3,131),(8,9),(8,40),(8,136),(10,11),(10,42),(10,74),(10,138),(32,33),(32,40),(32,96),(32,160),(34,35),(34,42),(34,98),(34,162),(64,66),(64,96),(64,192),(65,67),(65,73),(65,97),(65,193),(72,73),(72,74),(72,104),(72,200),(128,129),(128,130),(128,136),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_235.map (·&&&dom_235)
def gM:=goal_235&&&dom_235
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x56440
|7,0=>0xa60855aa7e19020168de1439c
|8,0=>0x7ccdc2ff10
|9,0=>0xfffda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x50500000505000005050000050500000500000005000000050000000500f0f00000f0f00000f0f00000f0f00000f0a00000f0a00000f0a00000f0af0000000f0000000f0000000f0000000f0000000f0000000f0000000f00a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0af0f00000f0f00000f0f00000f0f00000000000000000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0af0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0cf0f00000f0f00000f0f00000f0f00000a0a00000a0a00000a0a00000a0af0f00000f0f000000000000000000000f0f00000f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x582706548270653827065382170598270654821065827a0659821706543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d5739c68
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 236 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x21d865d9864dd865e1764df8646176619785d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfff337f3f7f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x5ee6
|8,0=>0x14
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_233 8 roots_233 ops++addP pm 1 dom_171 8 roots_171 ops++addP pm 2 dom_234 7 roots_234 ops++addP pm 3 dom_227 7 roots_227 ops++addP pm 4 dom_107 7 roots_107 ops++addP pm 5 dom_203 8 roots_203 ops++addP pm 6 dom_226 5 roots_226 ops++addP pm 7 dom_106 4 roots_106 ops++addP pm 8 dom_99 4 roots_99 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_235 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_99 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_233 8 s (0,roots_233.map (·&&&dom_233)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_235 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_233 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_235==dom_235)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_235 gM v ys):RunD true dom_235 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_235 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
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
namespace S_237
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(4,36),(4,68),(4,132),(5,13),(5,37),(5,69),(5,133),(8,9),(8,40),(8,136),(12,13),(12,44),(12,76),(12,140),(32,33),(32,36),(32,40),(32,96),(32,160),(64,68),(64,96),(64,192),(65,69),(65,73),(65,97),(65,193),(72,73),(72,76),(72,104),(72,200),(128,129),(128,132),(128,136),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_237.map (·&&&dom_237)
def gM:=goal_237&&&dom_237
def NN:Nat→Nat
|4=>7
|5=>45
|6=>173
|7=>133
|8=>30
|9=>5
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x4ac433271626d430f73708aa401733004d8
|5,0=>0x9a0c988551741005c689550d853774485694647b39fec380c1346143280130f6e30eab2dbda2c30f2bb1b2a4c12921828c5d289a62631f229881d1261cf35153d41324e12191102ba0e3f50c4770c3360b0350ae9a0a23c097000800f073fd072fc05c7e05bef0567803ebc01dd20075d
|6,0=>0x37dd837a5a3615634e1734740346ae33c1b339533362f3332432f9c328723179931189300e02f8c22ee322e6462e0f62d2f42c8fb2bf892bd072babc2b4b92acad2aaf42984728b20272132644425f0025e3b2545f23b3622c6b2237421f6c214da20796205891fe331fd171f8dc1f36a1d8941cecb1cc0c1bebd1bb991aba61a5d21a50e1a23c199d71959e1949d18f8617ded17b27172bc16e12161ee15fa7153961472713d61131ac1303911f86119da116cf1163310c3d103500f8550f5a60e3f30df810d7ed0d71f0c9400c1c10be480be3b0bbfa0ba840ba0f0b3850af080a7870a58d0a2050a03f09c5509bc708e6d08d8f08bf007969077ec07447072210717e070c306db0068680662805c47054b904fe504c9a0485f0455403eca03a97038e903566033c402d8401f300181f013f6011eb00f5d00caa0089d0075d
|6,1=>0xbebfc7e202711586e0d66b66d6aed969360690c3684f0680a8672f15a69555fc655ecf537d95352852eac527b25239f51fd250940508854ee604da8d4c7914b4804a3a149e4f49dfa493dc47bf447a26450e4445c743c3e41ac14017f3fec23ed8b3dbe23d3723cd253c30f3ae9039268
|7,0=>0x8dea081dbe7bf4e748926e60b6d6f96869f66e086473363bd462576622dd5bce0592ac565ec563ae536df52fc2515ef5110b507324e8e24cf4b4be2d4b97348fcd485ca46d2d469cb451d643a8b4116240b1c3f7e63f7523e6163db543b68e3ae243a6233a399395463906437cd635ded336d6336b3331a931cde2f3442f2d42ed422dc5b2d89b2d7e22d5a42c9d42c4be2c26c2a7682a68e293702913328ed2287c827cca27b0b2765e25d8b253d92447d235a2210731f1311eb341e5831d04d1cd561b35c1a9f81a59719f7c19abd17ec417ded15a801557a13b3b13987122c311c7811af4110ff10ee010b581064610636104a10f3780ec480e5050de9b0b3740adfe0ac750a77b08c640892107d260759a06d0d0694005e42049d4041bf03f39035700330702c4a0297b024b402493022e90158600d410030c00186000e5
|7,1=>0xbebfcbb71bb451e98a5096398
|8,0=>0x9867881cde81965790e25aa9b50820506a64c280455fc44db740b3137256362fc3378a318072ec622ea752e8e926db421aa21eef41b67a1574c1445a1399912af60b90a082f302daf014cf
|9,0=>0xf0cad743d35a8794e2f643d29
|10,0=>0xf0cad
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccc000088880000cccc000088880000cccc000088880000cccc0000888b33300003333000033330000333300003333000033330000333300000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc0333300003333000032320000323200003333000030300000323200003030cccc0000cccc0000cccc000000000000cccc0000cccc0000cccc0000000333300003333000033220000332200003333000022220000332200002222cccc0000cccc0000cccc0000cccc0000cc000000cc000000cc000000cc0333300003333000000000000000000003333000033330000000000000000cccc0000cccc0000cccc0000cccc0000cccc000000000000cccc0000000333300003333000022220000222200003333000033330000222200002222cccc0000cccc0000cccc0000cccc0000000000000000000000000000000333300003333000033330000333300003333000022220000333300002222cccc000000000000cccc000000000000cccc000000000000cccc0000000333300003333000033220000332200003333000033000000332200003300c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c333300003333000033330000333300003333000033330000000000000000
|0,1=>0xcccc0000cccc0000ccc00000ccc00000cccc0000c0c00000ccc00000c0c333300003333000033330000333300002222000022220000222200002222cccc0000cccc00008888000088880000cccc000000000000888800000000003000000030000000300000003000000030000303000000003000030300c0c00000c0c0000000c0000000c00000c0c00000c0c0000000c0000000003300000033000000330000003300000033000000330000003300000022cccc0000cccc0000cccc0000cccc0000cccc0000cc000000cccc0000cc0333300003333000033300000333000003333000033330000333000000000ccc00000ccc00000ccc00000ccc00000ccc0000000000000ccc00000000333000003330000033300000333000003330000033300000333000003330cccc0000cccc0000cccc0000cccc0000cccc0000c0c00000cccc0000c0c333300003333000032320000323200003333000033330000323200000000cccc0000cc000000cccc0000cc000000cccc0000cc000000cccc0000cc0333200003332000033320000333200003332000022220000333200002222cccc0000cccc0000cccc0000cccc0000c0c00000c0c00000c0c00000c0c222200002222000022220000222200002222000022220000222200002222
|0,2=>0xc4c40000c4c40000c4c40000c4c40000c4c40000c0c00000c4c40000c0c1111000011110000111100001111000011110000000000001111000000000000000000000000c4c40000c4c400000000000000000000c4c40000c0c00000000000000003033000030330000000000000000000030330000303200cc000000cc000000cc000000cc000000cc00000088000000cc000000880000000000000003333000033330000000000000000000033330000323200cc000000cc000000cc000000cc000000cc000000c8000000cc000000c800300000003000000030000000300000003000000000000000300000000c8c80000c8c80000c8c80000c8c80000c8c80000c8c80000c8c80000c8cb33300003030000033330000303000003333000030300000333300003030c8c80000c8c80000c8c80000c8c80000c8c8000000000000c8c8000000000000000000000003333000033330000000000000000000033330000303044440000444400004444000044440000444400004400000044440000440333200003332000033320000333200003332000033000000333200003300cccc0000cccc0000cc000000cc000000cccc000000000000cc000000000333300003333000033000000330000003333000033330000330000003300
|0,3=>0x8c0000008c0000008c0000008c0000008c000000880000008c000000880220000002200000033000000330000002200000022000000330000003200000000000000000000000000000000cccc0000cccc0000cccc000088880000000000000003333000033330000000000000000000033330000222244440000444400004444000044440000444400004444000044440000440030300000303000003030000030300000303000003030000030300000000000000000c0c0000000000000c0c000000cc00000000000000cc00000000000000000000000000000000000000033330000323200003333000032320c0c00000c0c00000c0c00000c0c00000c0c0000080800000c0c0000080b30300003303000033030000330300003303000033000000330300003300c0cc0000c0cc0000c0cc0000c0cc0000c0cc0000c0c00000c0cc0000c0c0000000000000000000000000000000033330000333000003333000033300c0c00000c0c00000c0c00000c0c00000c0c00000c0000000c0c00000c03300000033000000333300003333000033000000330000003333000033000000000000000000cccc0000cccc00000000000000000000cccc0000000110000001100000011110000111100001100000011000000111100001100
|0,4=>0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0003300000033000000330000003300000033000000000000003300000000cccc0000c8c80000cccc0000c8c80000cccc0000c8c80000cccc0000c8cb33300003333000033330000222200003333000033330000333300002222cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cc000000cc0000000003333000000000000333300000000000033330000000000003300cccc0000cccc0000cccc0000cccc0000c8c80000c8c80000c8c80000c8c800000000000000000000000000000000303000002020000030300000202c0c00000c0c00000c0c00000c0c00000cccc0000c8c80000cccc0000c8cb33300003333000033330000333300003333000033300000333300003330cccc0000ccc00000cccc0000ccc00000cccc0000ccc00000cccc0000ccc00000000333300000000000033330000000000003333000000000000222200000000cccc000000000000cccc000000000000c8c8000000000000c8c911100001111000011110000111100001111000011110000111100000000cccc0000cccc0000cccc000000000000888800008888000088880000000000300000003000000030000000300000003000033000000000300003300
|0,5=>0xcccc0000cccc0000cccc0000cccc0000cccc0000c8c80000cccc0000c8c800300000003000000030000000300000003000000030000000300000000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc00008888000000000000000111100001111000000000000000000001111000000004444000044440000444400004444000044440000444000004444000044400030000000300000003000000030000000300000002000000030000000200cc000000cc000000cc000000cc000000cc000000c0000000cc000000c1111000011110000111100001111000010100000101000001010000010100000000000000000cccc0000cc0000000000000000000000cccc0000cc0000000000000000000000000000000000033000000330000003300000000cccc0000cccc0000cccc0000cccc000000cc000000cc000000cc00000000011000000110000001100000011000000110000000000000011000000000c0c00000c0c00000c0c00000c0c00000c0c0000000000000c0c0000000111100001111000011110000111100001111000010100000111100001010cccc0000cccc0000cccc0000cccc0000ccc00000ccc00000ccc00000ccc333300003333000033330000333300003333000033330000333300003300
|0,6=>0xc0c0000000000000c0c0000000000000808000000000000080b3330000030300003333000003030000333300000202000033330000020244040000440400004404000044040000440400004400000044040000440303300003033000030330000303300003033000030320000303300003032cccc0000cccc000000cc000000cc0000cccc0000cccc000000cc0000000333300003333000033330000333300003333000033330000222200002222cc000000cccc0000cc000000cccc0000cc000000cccc0000cc000000cc00101000001010000010100000101000001010000000000000101000000008888000088880000cccc0000cccc00008888000088880000cccc0000888a3230000232300002323000023230000232300002323000023230000222200cc000000cc000000cc000000cc000000cc000000cc000000cc00000000000000000000000333300003333000000000000000000003333000033308c8c00008c8c00008c8c00008c8c00008c8c0000888800008c8c0000888800000000000000000330000003300000000000000000000003300000000cccc0000cccc0000cccc0000cc000000cccc0000cccc0000cccc0000cc0000000000000000000000000000000003333000033330000333300003300
|0,7=>0xcccc000000000000cccc000000000000cccc0000cccc0000cccc0000cc000000000333300000000000033330000000000003330000000000000333000000000cccc000000000000cccc000000000000cc00000000000000cc0000000000000000000000000000000003232000032320000323200003232cccc000044440000cccc000044440000cccc000040400000cccc0000404000000000000000000000000000000003333000033000000333300003300cccc0000cccc00000000000000000000cccc0000cccc0000cccc0000cc00000000000000000000000000000000000330000003000000033000000300c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c0000080800000000000000030330000303300000000000000000000303300003030cccc0000cccc00004444000044440000cccc0000cccc0000444400000003333000000000000333300000000000033330000333000003333000033300000000000000000cccc0000cccc00000000000000000000cccc0000cc0000000000000000000000000000000000000000033300000000000003330cccc0000cccc0000cccc0000cccc000000000000ccc0000000000000ccc333300002222000033330000222200003030000020200000303000002020
|0,8=>0xc0c00000c0c00000c0c00000c0c00000c0000000c0000000c0000000c00033000000300000003300000030000000330000003000000033000000300000000000000000000000000000000000000000c8c8000000000000c8c8000000000000000000000003333000000000000000000000000000033000000000000000000000000000000000000000000cccc000000000000888b33300003300000033330000330000003030000030000000303000003000c0c00000c0c00000c0c00000c0c00000cccc0000ccc00000cccc0000ccc00000000333300000000000033330000000000003333000000000000000000000000000000000000000000000000cccc0000cccc0000888800008888000000000000000333300003333000000000000000000003300000033000c0c0000080800000c0c0000080800000c0c0000080800000c0c0000080b333000033330000333300003333000003030000020200000303000002020000000000000000cccc0000888800000000000000000000cccc000088891110000101000001111000010100000111100001010000011110000101000000000444400000000000044440000000000004040000000000000404000000000000000000000000000000003333000033330000330000003300
|0,9=>0xcccc0000000000008888000000000000cccc000000000000888800000000000000000000000000000003333000033330000333300000000
|_,_=>0
def sP:Nat→Nat
|0=>0xd01300507030a09010804030d2d0105032c01102b050f220108051324070901102a030110290513071110280826040d25080524030d01230507032211100807031f0d10000e030d011e1d030d101c08050309101b08050301101a0805190318111013151208050f070d141113071211080f0e0d0c050b070a09010403020100
|1=>0x11043080322011e083c030d014205070d0106410b070d011e1d0f02010805260711102b0807030d14011e030110400805070311103f082a0301102b051317111008150322100805130709103a08240301103e051903180110053d3c030d0110030d3b3a0805070d0110390838030d10370803363510080534030d1033080e03
|2=>0x1100805320e030d0110050b030d104f080526070901104e08380f030d011e083d0f070d0110080e0d01104a080526070d49100847030d1110080513170110080546030d10330805450716090110080301101a080519030a0108050e030d0c10050d01424408052607103f08050d1037430805030d141110070309101b08380d
|3=>0x2e05030d06103a0005260701102b080526070d1058085707090110082607170d100805030d111033080503090d011055080403012b5408053c0b070d01100507030d2511100826071609100807090d01104a082407030d011e10030d013b0008054524030d01100526070d1e105308030d011e5208054507510d011008070302
|4=>0x301102908050349011029080513030123540805030d103a5e08053419030d0110083415030d01100824030d0110520526070d491e10080f0d250108051503360d1008050e07030d01061e5d3c030d0110050b030d01105c0513030d015b08050301102b5a08050327011e2b08052607510d10081303011059080524030d0110
|5=>0x805030901234e0805070d011041083d030d0106100015030d1068080567030d010608054c0301102b0805030d66103a0805610301106508050e030d010642056413030d01100546030d0123080507030d116310081503161059080519030d103a080507030d01106200070d0110430805600b030d0110000f070d011d080504
|6=>0xd013b08050407030d27110813074b011008036c01102b080507030901106b080f070d0142080560030d01100008030d11102808050f070d015208051307310d011000030110533f080507030d011e5c08030d27103708053426070d0110082607360d1008054c0f070d011e080f070d016a0008030d01105c08051303690110
|7=>0xd010605030d27700805030d14011005130751110110083c030d0106100515030d251008050f070d490108030110532b08054d0f070d111008266e0d011008052404030d011005030d012333080526070d106808050b03200d103a051507030d271e084d38030d011e08030d016d080545340309011008320301106208055003
|8=>0x190b070d01100015030d63100805030d011e680805130301106208054507160d1110080f070d49011e080e030d01105c0574070d0110080519031701100805030d01064200050b0d01101d05070309011028085f2a030d0110055073030d011005040d01104308050327011029080507030d011071080f070d011e5308040e03
|9=>0x1008070d016a1044086419030d011005340316090110086173030d0110050703120d01080538030d2711100813033501100805030d0106107505030d2d01102e0515030d015b08051903011059080507030d2d01100504030d015c08050b074b0d0110003403090d0110085060030d01100826070d11104e080403012e2b0805
|10=>0x1104a0805030163103f0805070301101a08054534030d11100824030d1110530507030d015b0805320301104e0805030d35760110050f030d017508052604070d270805616003090110084c0b070d01100003180d0110050e03200d103a0513031610330805137303200110054c070d01061e084d2a030d0110053403510d01
|11=>0x103a0805030d011e2e08054c030d01061e080515030d01104e0805030d01631053080579030d0110080546030d01100805260751160d1008040327012b08050f0e070d011e0804030d01520805030d49015208050e0301102b0805030d0110755c05030d0610770805040b070d011000030d35105308055f030d103708051320
|12=>0x1107e08050e030d01061005030d270110680805190b070d011008052407030d0110054d26030d1110080526070d105308050f030d016a08054c0b030d011000050b030d01106508054c030d011e08051503160d100805031601107d08050f030d016a0608050f030d7c0108057b030d0110080519030901104e08050e0b030d
|13=>0x4200080557070d011008054607030d011008053c07030d011008052607160d1008054d030d1110080504030d010608050f030d016a1e080519030d0110330805070301102b08054645030d0110080513070d01100008040e030d0110080526070d01104e08054507160d011008050703090d0110530807030901104e0803090d
|14=>0x54c0b070d0110080503090d0110780805030d11011048080583070d01100805030d01104a000805030d111082080504030d01061e0805070351090d01100803510d01107e08054d15030d01100805030d011081080538030d2701100805030d01105c08051526030d271008057f030d011008055019030d01100805030d0110
|15=>0x310d01106208050e030d0110650805030d0110534e08050e0b03310d011005260351090d100805130320011000050b030d018710056119030d01100805030d01103708054603090d01100805130386011008054d26070d01100805030d0110752e080507030d0110750805070351160d01100861030d01100005030d01108408
|16=>0xd01101d0805030d018a10080507030d01102808050403011e102b0805452603090110080589030d011008050b070d01061005030d011e103708055f04030d011008054603160d011008054d070d0110080519130320011008056113030d01100005040301102b080561034b0d01100805030d010610880526070d2710080503
|17=>0x513030d012308050e0703090d0110081507030d105308056113070d0110080526030d4927100805030d011052080513072001100805130709011008152407030d011005030d01230805030d01108c080561070d011008055d04030d011008055003090d0110080507030d01108b0805070d0110820805040b070d0110080503
|18=>0x50e030d01104e080503360d0110080504030d012e080567030d0110080526070d1110080407030d01060805030d01108d0805030d01104e6208050e07030d01061005500b030d01100805150703160d1008050b030d103a0805380f030d01100805030d01104a08055d0b030d01100805030d011053280805150f070d011008
|19=>0x10080507030d01104e08054c0f030d01100805030d01108f08050f070d0110080507030d110110081303160110080515030d110110080507030d0110000846030d011008050407030d012e080524030d01100519030d0110530805030d016310080507030d01101d080504070301102b080507030d0110370805070d01108e08
|20=>0x1105308057a030d011008052603090d011008054513030d01100805030d01102e08054c030d010610080507030d01061008054526030d01100805030d491101100805034b0d01100805030d011091080519030d01100805040f030d0110080515030d01100805030d010610000590030d01100805030d01108e080526030d11
|21=>0x30d01100805030d011008050b030d0110080503090d0110080503200d0110080507030d0110080507030d01102e08051907030d011008051507030d011008050f030d011e0805030d
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x1e50195014500f500a500550005
|5,0=>0x125611f61196113610d6108510260fc60f750f160ec50e660e150db60d560cf60c960c360be50b860b260ac60a660a0609a6094608e60886082607c60766070606a6065505f60596053604d60476041603b6035602f602960236
|6,0=>0x2dc72d572ce72c772c072b972b272ab72a4729d7296728f72887281727a7273726c7265725e7257725072497243623c7235722e7227722072197212720c620571fe71f771f071ea61e461dd71d671cf71c871c171ba71b461ad71a6719f71987191718a7183717c7175716e7167716071597152714c6145713f61387131712b6
|6,1=>0x495748e7487748074797472746b7464745d7456744f74487441743a7434642d7426741f74187411740a740373fc73f663f063e973e273db73d563ce73c773c073b973b273ab73a4739d7396739063897382737b7374736e6367736073597352734b7344733d7336732f73287321731a7313730c730572fe72f772f162ea72e37
|6,2=>0x5cf75c875c175ba75b375ac75a5759e7597759075897582757b7574756d7566755f75587551754a7543753c7535752e75286521751a7513750c750574fe74f774f074e974e274db74d474cd74c674bf74b874b174aa74a3749c7
|7,0=>0x7b487ad77a5879d8795878d8786777f7777876f87678760775887517749874187398731872a7722871b7713870c770486fc86f576ed86e586de76d776d076c886c086b976b186aa76a2869a8692868a8683767b8674766c8664865d7655864e7647763f8637863076297622761a8613760c760485fc85f575ed85e585dd85d67
|7,1=>0x996898e8986897f7977897079697962795c6954894d7945893d8935892d8926791e8917790f890788ff88f878f088e888e088d888d178ca78c468bc88b668af78a878a08898889088897881887a7873786b8863885b8854784d7845883d8835882e7826881e8817780f8808780177f987f187e987e187d987d277cb77c387bc7
|7,2=>0x9bb79b389ad69a5899e7
|8,0=>0xa998a918a898a827a7b7a747a6c8a648a5d7a558a4d8a458a3d8a367a2f7a287a208a197a127a0b7a0479fd79f589ed89e679df79d879d179c989c27
|9,0=>0xabd6ab67aaf7aa87aa17
|10,0=>0xac36
|_,_=>0
def wAt:=mkWire dB 146 238 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x30544021010541037071040c15071600c15030d404150d2541c9c0305438070d0541c21030545c21071600c153210c34c5030543415102141c800305420be2e0140c150d2541c9c011040c4103054542307014341503054140d072700c05030548405080541c80030544015070600c15170841c5805014140d0d034405d07160140d100341c18050342015070600c15
|1=>0xd0143475070600c151008434c50305540070b0943415070dc040d054d83c051003530170f0840c41030052c0f080549c15100140c05030540521110f8400d010541c580d034140d0d0144c150d0340c15160340435070d44085072000c150d0847405070841c18030544021082541c9c0110414050503440150d2541c9c0305404410b1e01441100840c410d1d41c18
|2=>0x10343445050340415460dc4c4501054340d100843807000342015040dc0c05071040c1505034444305014040d0d0544c23030d40c15030141c58030540435150d4440d560542c270803440ae040dc3c15100341023071040c15010541c9c030544005050341435010352c0f0908434151508c144107014140d5010c004d0d03440150701c1005031e40c1516054580d
|3=>0xe01c1c2103054c4370708c0c155f03c100507104140d6105c2c3508034400d07060140d100857c37040143c15100348c371910c4c150d03438070b054200d4605c4c150d0351417260d41499030147805051041c9c011040c41030554c3503054144107084140d5d08c10210f054400d4208c38430b054200d4610c6405051341037031e44015040dc4005031e44015
|4=>0x5005c004d0d03420151516c04350311404151510c1c05030541c23030d4c4430708c0c155f01d34152703514170d264040d0701c40150f0840c4103054400d1000420150013c20151910c0c251e0b0200d05104140d060344021070154c430701c0c150706c0c150e01c0c01080542c150803438430300420154608c640505134644313054340d0701c543726054040d
|5=>0x110d4340d0105574234c054180d070141c9c03054400510034780505104140d010543c0503105bc0d261e84015010345423070140c15105381c070305420350e01c142d08034144107014140d4d05c0c9d0110440da0d5341c0703055141713014340d0708c0c155010c38350b054200d050141c4105034140d090840c350d0541037031e44015070dc384307084140d
|6=>0x1920c4c150d084580d0d014140d1e0140c41100540c1507084b8230710c0c15037241c5a030540435070d41c58030543405000342015070602041030840c15530dc1c07050357c231510498150103464211908c4c150d0357c0f040143c155f0dd341527035c815071680c15010d41c07031044015030541c21071040c150f1100c41010544005082541c9c030544005
|7=>0x6a03c4001080551823190144c151603434055008c158520034405d071600c15010d49c0d0110421710706c0c154610c5435260551837190144c150d03420be2e0141c430305440b9082e81c4303054140d080340035080551817190140c250d054158105618800d070dc0c05010540c150410c10370f054400d080540c21070d40c15105340c15103781007031e44015
|8=>0x710c0c155d01d3015060341c41080540c21030541c370305404dd0401c3c151003480150d084414d0701c0c155d0dc38410708415161603434051508c440d4610c6405070d41c23030540539070dc0c15010341c4105035841720034203508054402d08034140d081741c580305404350e01c2c1508034203505134340d05134340d05034180d1008458154505c580d
|9=>0xe0dc2c15080343c2105104400d0311404150d0140c260d054043506054400d100849c171003440055803444430105464370309434150e01c2c15080341043031e4401510054180d100841c37030541c0703055e8211305c340d0978498270d054040d160540c15010d44005040dc3c15100344015031041c21030541c05030540c45010541037071040c152e08cb821
|10=>0x30140c15032740415100144021031e440151e0840c41100546407030943415040dc1c41030541515160343405080540c35030541c21071040c15070dc0c05030540c151603404350701c1435050343415070dc0c155103c24050d0542c150803420410727c0c15080341c35050345423070140c15261040c05010541c07030140c1506054400d1008420150b104200d
|11=>0x200343421058543c0710034402d03054200d2609c040d110f8400d030543c23100352c0f000d420152610c0c05010544021031e44015090141435050340d4616054340526104149901034443f1003404154d05c9c0d1001440c60708c0c1510014149901036000d2005c3421190840c250d05438430003420151308c0c35030546405070d40c150408c1c41030540435
|12=>0x31040c1513054340d0d084201513084340d040dc3c1510034801520034342110084000f080544005030140c150708c0c150e0dc2c15080341c370701c0c150e08c2c150803424050d054040d030d420150d084141a08034402113084144d0d03410070f054400d190140c250d0540c350908c341510264040d050341c4303054b8210710c0c15160540c15010d41421
|13=>0x26054040d0d034140d0d0843415030d40c151508c1c050305464430309434150b098341508034342d03054200d040843c15100346421030943415070684021102680c15010340c21071040c15070600c1510084444c0d0340415530dc1c07030541037031e44015260d4341501035e8051305c340d03054200d081041007031e44015040143c15100351415160343c05
|14=>0x70dc0c15530d41c07030541c43071040c15103141c23030540c05010540c15100841c41030541c9e030544005070dc0c15081041c210305438350b054200d010d41c050305438070b054200d4d05c3c05100340d2e2005434210b1e44015080341c07030540c41070140c151910c144d0d0343415070840c150701c1c05030544c21030d40c15010349c15100145443
|15=>0x260d4040d1110404152005434210603c4021030943415050f4400d26054040d0805440210b05c200d260dc040d01054040d070dc0c150f084400d0901c3415031040c15010540c150d0343405110340415050342015150d49815010341c43071040c151508c9815010341c0703054414d0701c0c15070600c15100841037071040c150401c1c4103054349a03054040d
|16=>0x803434150d0840c150710c0c15070d40c15070140c150310440150701c0c1505138340d0d054040d13014340d0710c0c15060344021030544021
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x2900320000000000cc0000003
|5,0=>0x5550a0a00000000000096a00000000465000010cc00003e507480000000000000000d9019982f400000b0c000000000000000000000005260950111800003aa0650000018102a60000000011401c600000000000
|6,0=>0x2244000087990d2214641cc821903120063f4c7d18f641e663bd075a00001ce8390c7098de3000036cc6ba0d521a4633906520c73188630105e20b8400002d105820ac41508291051109f31368260c4a2091311c62290439800010a420c83fa07b40f241d8c3a107130dc61acc33a06340be817482d18000
|6,1=>0x3aa8748ce721ca438c87108e021bd337466d90d921ae435486a08d221a1333a86650cb1993331e862d0c41984430085f4cbd197642e480000b7996b42d060000b2996142bc656ccaba15432a445390a599474288650c4a0193c427084d4c999000026064b4c951929124a8488c000120223c446908c11144
|6,2=>0x25444a26935124a247248a4908d1f223b346e88d4918a22f245868a4d131a242442687c90e180004326858d09220e44148820903120330000800cfe99fa33f047d4cf8a1ef200007b0c0001e933ca87850eea1d94
|7,0=>0x61e6c30d849b0726086c04d7f1afb35f06bd897a12f135dc6bacd741ae535c46b7cd6e1ad935ac6b4cd681acd35946b1cd621ac1357c6aecd5c1ab535646abcd561aa9354c6a8cd501a9d35346a5cd4a1a92251e6a30d449a8635066a00d3e9a7a34ee69d0d389a6e34d669a0d329a6234be697492d92583
|7,1=>0x7926f18de19bc0377c4eecddc1bb537646ebcdd61baa274e6e90dd09b9e37366e60dca9b9327206e34dc51b8737086e04dbf1b7b36f06dd4db91b6f36d86da4db31b6426c26d78dad9b5836aa6d48da79b4c36926d18da19b41267c6cecd9c1b3536646cbcd961b2a264e6c90d909b1e36366c60d8a9b123
|7,2=>0x3d737a86f44de793cc3
|8,0=>0x20a141228205038a06140a28105018a02140228004ff89fe13fa27f04fd89fa13f227e04fb89f613ea27d04f989f213e227c04f789ee13da2
|9,0=>0x832306060b8c161
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x10c000210000410000800000ca000184000300000500000900001180002080004000007c0000c00001600002600004800008800010800020000034000050000090000100000100000180000280000400000600000800000800000
|1=>0x480000858001008001f70003ea0007cc000f00001c7000362000680000c08001780002e0000584000b0000150000260000490000908001200002240004440008800010e000208000408000808001000001c000034800048000087
|2=>0x27e2004e50009c28013600026880047dc008800010050020000037dc006f9800df1001bac003708006c9000d120019a4003048004ff8009f70012a400241800480800810000bfe0017f8002fb800448000880001000001fb800300
|3=>0x142420284440508180a0c3014024028044048fb8091c70103ee020200040110061670093ee0125d8024070045ff008ad00111e0020fb80417f0082c80101200200b00400100620000854c0108300202200400000765800aeb0013f7
|4=>0x4078e0807dc100200180670283ee0507d40a0f88141a002828a0504d00a092014065028048048400084b401093802123c042400080fb8101380202100400800800280c1610180800287dc050f980a1f101438402860c050c080a153
|5=>0x118282230184440f38881671102c22105dc420b08801f710020020010020cfb84199008330c1057dc204c80407d6080da01017d8200fb8400840800800a0fdc141e38283c10507800a0d041416082804004638e08c700108fb8203d7
|6=>0x4000044002e24005c4490fb89214112424c2484844908388c167
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x2040000040002
|5,0=>0x26270000002a000036004000232c000000001304290002000000000000041c0200232900070200000804000000
|6,0=>0x1208337a510419246ac2052c2b01a0171d0a01012c3220bbc68e012ec300870d0200b72989b63917090564b30f573d21186814009d014342a867000848381405030003080508c8630a02ab25ab35120049080c0c0092bd04580525080c198f120015199c622f0c087b761a7159251c0024013135042414b63f08c10d460f4400
|6,1=>0x68b125d0301040501829305240824178a244e1c0075aba8c7120c1ca4000c670214082f14000500040e251db4
|7,0=>0x387e7f72ac3c803c9b82b81c5d4a965fb93c650894545e95afc43cae56983b4cb01f3e24747c9e3c347e6e45a02d1010c052af843079ba080a125b90b29f223c6953be1e5d91b077a5080c78b1748390901b8d883c97ad1f356128816cc086a20e84166120336f334b8c60014f99bf6ba3a630a99b4da2bc8d505c66a7110345
|7,1=>0x3c7d3a0b3c
|8,0=>0x3a559a863c4573703caa9e70c5b59e56859ba1416d9b3aaa4c778d479a5a
|9,0=>0x37414cad3c
|10,0=>0x3c
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_236 8 roots_236 ops++addP pm 1 dom_228 7 roots_228 ops++addP pm 2 dom_169 7 roots_169 ops++addP pm 3 dom_225 5 roots_225 ops++addP pm 4 dom_229 8 roots_229 ops++addP pm 5 dom_233 8 roots_233 ops++addP pm 6 dom_109 8 roots_109 ops++addP pm 7 dom_173 8 roots_173 ops++addP pm 8 dom_205 8 roots_205 ops++addP pm 9 dom_141 5 roots_141 ops++addP pm 10 dom_197 5 roots_197 ops++addP pm 11 dom_101 5 roots_101 ops++addP pm 12 dom_45 5 roots_45 ops++addP pm 13 dom_108 5 roots_108 ops++addP pm 14 dom_201 5 roots_201 ops++addP pm 15 dom_204 5 roots_204 ops++addP pm 16 dom_105 5 roots_105 ops++addP pm 17 dom_172 5 roots_172 ops++addP pm 18 dom_165 5 roots_165 ops++addP pm 19 dom_232 5 roots_232 ops++addP pm 20 dom_168 4 roots_168 ops++addP pm 21 dom_161 4 roots_161 ops++addP pm 22 dom_224 4 roots_224 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_237 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_161 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_224 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_236 8 s (0,roots_236.map (·&&&dom_236)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_237 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_236 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96)],[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff00000000ffffffff00000000,96),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffff00000000ffffffff00000000,96),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_237==dom_237)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_237 gM v ys):RunD true dom_237 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_237 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 45 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 173 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 45 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 173 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 133 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 133 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 30 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 30 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 5 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_237 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_237 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_237 roots_237 goal_237 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_237
theorem lowS_237:Lower true dom_237 roots_237 goal_237 11:=S_237.noCircuit
namespace S_243
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,129),(2,18),(2,66),(2,130),(3,19),(3,35),(3,67),(3,131),(16,17),(16,18),(16,80),(32,33),(32,96),(32,160),(34,35),(34,50),(34,98),(34,162),(48,49),(48,50),(48,112),(48,176),(64,66),(64,80),(64,96),(64,192),(65,67),(65,81),(65,97),(65,193),(128,129),(128,130),(128,160),(128,192),(144,145),(144,146),(144,176),(144,208)]
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
|5,0=>0x853c44d4121ecfe
|6,0=>0xfd23ac2a7133ef72e33a24096
|7,0=>0xf2e8fa83ca712a90fc84
|8,0=>0x7a9f6
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000c000c000f000f000c000c000f000f000c000c000f000f000c000cf000f000f000f000f000f000f000f000f000c000f000c000f000c000f000cf000f000f000f000f000f000f000f000f000f000f000f000a000a000a000af000f000f000f000f000f000f000f000c000c000c000c000c000c000c000ca000a000a000a000a000a000a000a000a000a000a000a000a000a000a000af000f000f000f000f000f000f000f000f000f000f000f0000000000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000f000f000f000f000f000f000f000f000f000f000f000f000f0000000f0000f000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000cf000f000f000f000a000a000a000a000f000f000f000f000a000a000a000a00000000f000f00000000000f000f00000000000f000f00000000000a000af000f000f000f0000000000000000000f000f000f000f0000000000000000f000f000f000f000f000f000f000f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x854a10e854a1085431085b4a10854a910864310864a918d64a10854c31086b4a186439876430543210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x31433006
|6,0=>0x2b64ac79cbb916
|7,0=>0x8aefd9c3b17
|8,0=>0x4c6
|_,_=>0
def wAt:=mkWire dB 15 244 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x211a150110541a154110541a154140541
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x100
|6,0=>0x7252413112
|7,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xdb6aeb56da4401f680e000c000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>8
|6,0=>0x5d13
|7,0=>0xbed
|8,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_242 7 roots_242 ops++addP pm 1 dom_163 5 roots_163 ops++addP pm 2 dom_177 5 roots_177 ops++addP pm 3 dom_115 6 roots_115 ops++addP pm 4 dom_114 5 roots_114 ops++addP pm 5 dom_83 5 roots_83 ops++addP pm 6 dom_241 6 roots_241 ops++addP pm 7 dom_99 4 roots_99 ops++addP pm 8 dom_227 7 roots_227 ops++addP pm 9 dom_211 6 roots_211 ops++addP pm 10 dom_225 5 roots_225 ops++addP pm 11 dom_179 6 roots_179 ops++addP pm 12 dom_178 4 roots_178 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_243 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_178 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_242 7 s (0,roots_242.map (·&&&dom_242)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_243 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_242 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
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
theorem lowS_245:Lower true dom_245 roots_245 goal_245 9:=lower_slice_b [(0x22002200220022002200220022002200220022002200220022002200220022,16,17)] (by decide +kernel) lowS_244
def dzo_168_16:=0x10100000101000000000000000000000101000001010000
def gzo_168_16:=0x10100000100000000000000000000000100000000000000
def gsh_168_16:=0x1010000010000000000000000000000010000000000
theorem lowS_zo_168_16_168:Lower true dzo_168_16 roots_168 gzo_168_16 4:=lower_iso_b (d1:=dom_168) (r1:=roots_168) (T1:=gsh_168_16) [(dom_168,16)] (by decide +kernel) (lower_slice_b (T:=gsh_168_16) [] (by decide +kernel) lowS_168)
def dzo_82_8:=0x50005000000000005000500
def gzo_82_8:=0x50004000000000004000000
def gsh_82_8:=0x500040000000000040000
theorem lowS_zo_82_8_82:Lower true dzo_82_8 roots_82 gzo_82_8 4:=lower_iso_b (d1:=dom_82) (r1:=roots_82) (T1:=gsh_82_8) [(dom_82,8)] (by decide +kernel) (lower_slice_b (T:=gsh_82_8) [] (by decide +kernel) lowS_82)
def dzo_234_16:=0x505000005050000050500000505000005050000050500000505000005050000
def gzo_234_16:=0x505000005050000050500000504000005050000050500000504000004040000
def gsh_234_16:=0x50500000505000005050000050400000505000005050000050400000404
theorem lowS_zo_234_16_168:Lower true dzo_234_16 roots_234 gzo_234_16 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_16) [(dom_234,16)] (by decide +kernel) (lower_slice_b (T:=gsh_234_16) [(0x40400000404000004040000040400000404000004040000040400000404,0,2),(0x50500000505000000000000000000000505000005050000000000000000,0,64)] (by decide +kernel) lowS_168)
def dzo_170_16:=0x50500000505000000000000000000000505000005050000
def gzo_170_16:=0x50500000504000000000000000000000504000004040000
def gsh_170_16:=0x5050000050400000000000000000000050400000404
theorem lowS_zo_170_16_168:Lower true dzo_170_16 roots_170 gzo_170_16 5:=lower_iso_b (d1:=dom_170) (r1:=roots_170) (T1:=gsh_170_16) [(dom_170,16)] (by decide +kernel) (lower_slice_b (T:=gsh_170_16) [(0x4040000040400000000000000000000040400000404,0,2)] (by decide +kernel) lowS_168)
def dzo_242_8:=0x500050005000500050005000500050005000500050005000500050005000500
def gzo_242_8:=0x500050005000500050005000500050005000500050004000500050004000000
def gsh_242_8:=0x5000500050005000500050005000500050005000500040005000500040000
theorem lowS_zo_242_8_82:Lower true dzo_242_8 roots_242 gzo_242_8 6:=lower_iso_b (d1:=dom_242) (r1:=roots_242) (T1:=gsh_242_8) [(dom_242,8)] (by decide +kernel) (lower_slice_b (T:=gsh_242_8) [(0x5000500000000000500050000000000050005000000000005000500000000,0,32),(0x5000500050005000500050005000500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_114_8:=0x5000500050005000500050005000500
def gzo_114_8:=0x5000500050004000500050004000000
def gsh_114_8:=0x50005000500040005000500040000
theorem lowS_zo_114_8_82:Lower true dzo_114_8 roots_114 gzo_114_8 5:=lower_iso_b (d1:=dom_114) (r1:=roots_114) (T1:=gsh_114_8) [(dom_114,8)] (by decide +kernel) (lower_slice_b (T:=gsh_114_8) [(0x50005000000000005000500000000,0,32)] (by decide +kernel) lowS_82)
def dzo_232_16:=0x101000001010000010100000101000001010000010100000101000001010000
def gzo_232_16:=0x101000001010000010100000100000001010000010100000100000000000000
def gsh_232_16:=0x10100000101000001010000010000000101000001010000010000000000
theorem lowS_zo_232_16_168:Lower true dzo_232_16 roots_232 gzo_232_16 5:=lower_iso_b (d1:=dom_232) (r1:=roots_232) (T1:=gsh_232_16) [(dom_232,16)] (by decide +kernel) (lower_slice_b (T:=gsh_232_16) [(0x10100000101000000000000000000000101000001010000000000000000,0,64)] (by decide +kernel) lowS_168)
namespace S_250
def pG:List (Nat×Nat):=[(2,18),(2,66),(2,130),(8,40),(8,136),(10,26),(10,42),(10,74),(10,138),(16,18),(16,80),(24,26),(24,56),(24,88),(24,152),(32,40),(32,96),(32,160),(34,42),(34,50),(34,98),(34,162),(48,50),(48,56),(48,112),(48,176),(64,66),(64,80),(64,96),(64,192),(72,74),(72,88),(72,104),(72,200),(128,130),(128,136),(128,160),(128,192),(144,146),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_250.map (·&&&dom_250)
def gM:=goal_250&&&dom_250
def NN:Nat→Nat
|4=>7
|5=>18
|6=>46
|7=>36
|8=>12
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xdf713d7fa89c4228fd2f8ad8b61f7f27ef4
|5,0=>0xfc551ed770e265ddfb0dc990ca7bc9a2d4e9a3e493bb68f1b783b887f0c4763d26c6346bbaa6b38f36d7c05f3f
|6,0=>0xf7e25e36f3c815fc5751bfdb8bd391b6e15b4042b227eb09f4a7f5ea752f94a9a8bb9a89779889e885109830106d3326b032646746392461c0a5fb115d08059b72571f156ae4566d4562c24b69c446eb4280b39bfe38eff1ddda1bfc5139d711d19117c10c4b20a0d90915806c0605a61011b7
|7,0=>0xcc5ddc7a469a8d1998479723490d5a90a2087e706fca6687b465f28643de637585ef995ed475c585581725746a54bde50b474e21a4d25949fce47e7f4756345d274039d36f22322c11c3ce18e58182210b0840a02c07adf06a3d
|8,0=>0xef2e166ea96234955b5f4679b3912737a3b35617309b61cf321991212b8d
|9,0=>0xef2e1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000000000000000001400140014001400140014001400140014001400140000001400140010000282828282828282828002800280028002828282828282828280028000000000505050505050505050505050505050500000000000000000000000000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000000000a0a0a0a0000000141400001414000014140000141400001414000014140000141400001414000282828282828282820202020202020202828282828282828202020202020202505050504040404050505050404040405050505040404040000000000000000a0a0a0a080808080a0a0a0a080808080a0a0a0a080808080a0a0a0a080808094141414141414141414141414141414141414141414000014141414101000028002800280028002800280028002800280028002800280028002800280028050505050000000005050505000000000505050500000000050505050000000080808080808080808080808080808080808080808080808080808080808080941414141414141414141414141414141414000014140000101000001010000002800280028002800280028002800280028002800000000002800280000000505050505050505000000000000000005050505050505050000000000000000
|0,1=>0xa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a0a0a0a0a080808094141414141414141414141414141414141414141010101014141414101010100000000000000000000000028282828000000000000000000000000202020250505050101010105050505010101010505050501010101050505050000000020202020202020202020202000000000202020202020202020202020000000000000001414141400000000141414140000000014140000000000001010000000000002828282800000000282828280000000020202020000000002020202505050505050505050505050404040405050505050505050505050504040404a0a00000a0a000008080000080800000a0a00000a0a00000808000008080001414141414141414141414141414141414140000141400001414000014140000000000028282828000000002828282800000000282828280000000000000005000500050005000500050005000500050005000000000005000500000000000000a0a00000a0a000008080000080800000a0a00000a0a000008080000080941414141414141414141414000000001414141414141414141414140000000282828282828282828282828282828282020202020202020202020202020202505050505050505050505050000000004040404040404040404040400000000
|0,2=>0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0808080800000000000000000000000000000000000000000000000141414141010101000000000000000000000000000000002828282828282828282828280000000505050505050505000000000505050505050505050505050000000004040404a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000a000a000a000a000a000a000a0141414141414141414141414141414141414141414141414141414140000000080808080808080808080808080808080808080808080808000000000000000404040404040404040404040404040405050505050505050505050504040404a0a0a0a0a0a0a0a000a000a000a000a0a0a0a0a0a0a0a0a000a000a0000000000000000404040400000000040404040000000004040404000000000000000282828282800280028282828280028002828282828002800282828282800280505050505050505050005000500050005050505050505050500050005000500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a080808080808080800000000000000000000000000000001414141410101010141414141010101000000000000000028282828282828280000000000000000282828282020202000000005050505000000000505050500000000050505050000000004040404
|0,3=>0x2828280028282800282828002828280028282800282828002828280028282805040504050405040504050405040504050405040504050405040504050405040000000000000000a0a0a0a0808080800000000000000000a0a0a0a08080809414141414141414141414141414141414141414141400001414141414140000000000028282828000000002828282800000000282800000000000028280005050404050504040505040405050404050504040505040405050404050504040000000000000000a000a000a000a0000000000000000000a000a000a000a0000000000000000000000000000000001414000014140000141400001414000282828282828282828280000282800002828282828282828282800002828000101010101010101010001000100010001010101010101010100010001000100
|_,_=>0
def sP:Nat→Nat
|0=>0x14340f1035c100c1050c26801cb28524f60428544f10a3490cc48a14320c1ca34300c10a14964f1cb15700c60b2850cf18414308010a14920c4961433d51ca3433040c14c03122854481ca1503c40c23801ca34930b2852481c61420040c2040
|1=>0x8c33cc1c415700c10a34300c1161433c056210a14900c8442850c03042890c100c10a14380031f10a14300c1d228544031e48a14300c10a1437403122850c054c48a1433d531210a1510cf7042850c030b2850db00c1d228544f1ca15000c10a
|2=>0x4430041430801ed2850c03182ca14300c2c41435c030710a1493cc48b2850cf10a14364f0042850ec00c10a143008304ac50d300c1ea2850c032248a14300c10a1493e932810a14300c10a0e700c6042850cf3042850c098c9441434c03042a4
|3=>0x30713214300c48428544300ca842850c0304c4aac50c03042a444300c10a143c003042850c0a4c1161510c010a14340032f10a14300c4845850cfb842850c030748a9033072ca14900c1169033c42858c0a4c2c42852433c748a1433cc784585
|4=>0xc4842850cf3072ca14300c2c4c4a14300c10a1433c0a4cdc42850c030b10a1433c06042850c0304ca40c03042a40cf33610a14300c116143d403042940c032d10a14300c10a1630cf00c2c4d0a14300c78428544300c10a143640304cb30c0
|5=>0xc03042850cf00c1312850c03042b814300c10acc300c1c42850c0304d0a14300c2c42850c030458a14300c11690300c2c428524300c48b2850c03181c42850c030710a90300c1c428544032a4842850c030710a1433c0304283040312132143
|6=>0x42850c03042850c031210a14300c1392850c03042a4
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x1e5065414503d40a50154005
|5,0=>0x22188261f187661c186a619185e61618526131846610183a60d182e60a54236
|6,0=>0x6fddb876c99ab769599e7665592762dd8475f5d7855c5d6a758dd5c755994f7521d4174e9d3374b1d257479d186445d0a740dcfc73d98f063a5ce2736dcd47335cc672fdcb872c5caa728dc9c7255c8e7
|7,0=>0xb01ab88ac5ea98a89e9b7a4e28b8a15a7e79dde7079a22608965e52792de4568fda3878c5e2b6891e1c885220c8815dff67e1df087a5de18769dd37731dc66
|8,0=>0xc45b0a7c0defd6bd9eef7ba1ee26b6ded47b35ec67
|9,0=>0x3176
|_,_=>0
def wAt:=mkWire dB 58 251 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x103433e30052330404b1710c49110c0492b0c0450100c49280c443015004b1410c4a3110f8c011ccc311780cb1710c47331cc440d48c443e300433e4910331100573124a030110c520d10044311cf03115004b1410c44311c0440d102573124a03011cf03115004b14103443110c4211
|1=>0x4444331444c33128cc5030c44a330cc44012c0443114c4a010cc45010e485010cf80310cc4a31491033110058310c04c011004a31140440d100443100c4a31140403110c4a310cc573124a030148cc4011c0440d10c49280c044311004c01444c3311cf040d00c492b0c052311004733
|2=>0x401285450100c4a0114345031034a0d10c4a3128c45010c0443110044311c0431110345010c4433148c440110340312c5c4311004a331004c01103443110c4a010cf80311c0c31100c443124443011404a3300c45012ca4431584ca312c5043148cc4010cf40312834431
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11000001000
|5,0=>0x1b30001831711521411220f30000e10c2084062000024000
|6,0=>0x6736526230005f35e15b35a15910005725435225024d30004a34820004534324123f23d23c13933720003523323032d32a32822712520002410002220002111f20001e1000
|7,0=>0xb02ae2ac2aa2a82a62a42a22a029e29c29a29829629429229028e28c28a28828628428228027e27c27a27827627427227026e26c26a2
|8,0=>0xbc1bb1ba1b91b81b71b61b51b41b31b21
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x24680012240007ba0003880001a00000c0400060000025d0001280000924000410000204000100800070400011200008800004000001c4000088000042000020000007400003000001400000800000340000180000080000020000008000002000000
|1=>0x4282a0200d40100480077a7d038c3a81c29f40cd0ea062c7d03043e8146bd409f4ea047875020fba80d69d40635ea02535401243a8086dd40230ea01001400443b80221d400e0b80051540024ba8006bd40031ee00087700043a800219400108e000800
|2=>0x41c61d50e70ea4068772010218b063f450011a241f71120db889063f44830ea2007410a543a844a0802140c00d1ae5042dba82169d410b0ea085354
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x400100
|5,0=>0x100058f0e08181000838c0a00700
|6,0=>0x41c520220f787878436849871811414007501a281882c120101144a8b8332040102a5003d1a00c80
|7,0=>0x784a04d6d31f185a99fcb8a2a5309cc593568ae11f9f219a44a5a1c674edbb8
|8,0=>0x47068b25f1e9279341739
|9,0=>0x23
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_248 7 roots_248 ops++addP pm 1 dom_224 4 roots_224 ops++addP pm 2 dom_186 7 roots_186 ops++addP pm 3 dzo_168_16 4 roots_168 ops++addP pm 4 dom_122 7 roots_122 ops++addP pm 5 dom_234 7 roots_234 ops++addP pm 6 dom_218 7 roots_218 ops++addP pm 7 dom_168 4 roots_168 ops++addP pm 8 dom_82 4 roots_82 ops++addP pm 9 dzo_82_8 4 roots_82 ops++addP pm 10 dom_120 4 roots_120 ops++addP pm 11 dom_242 7 roots_242 ops++addP pm 12 dzo_210_8 5 roots_210 ops++addP pm 13 dzo_234_16 6 roots_234 ops++addP pm 14 dzo_170_16 5 roots_170 ops++addP pm 15 dom_194 4 roots_194 ops++addP pm 16 dzo_242_8 6 roots_242 ops++addP pm 17 dzo_114_8 5 roots_114 ops++addP pm 18 dzo_232_16 5 roots_232 ops++addP pm 19 dom_154 4 roots_154 ops++addP pm 20 dom_170 5 roots_170 ops++addP pm 21 dom_216 4 roots_216 ops++addP pm 22 dom_232 5 roots_232 ops++addP pm 23 dom_226 5 roots_226 ops++addP pm 24 dom_240 5 roots_240 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_250 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_224 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_168_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_82_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_210_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_234_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_170_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_242_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_114_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_232_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_240 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_248 7 s (0,roots_248.map (·&&&dom_248)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_250 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_248 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_250==dom_250)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_250 gM v ys):RunD true dom_250 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_250 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 46 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_250 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_95:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_95:Lower true dom_95 roots_95 goal_95 8:=lower_iso_b isoMvS_95 (by decide +kernel) lowS_63
def isoMvS_125:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=lower_iso_b isoMvS_125 (by decide +kernel) lowS_119
def isoMvS_126:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_iso_b isoMvS_126 (by decide +kernel) lowS_111
def isoMvS_221:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 9:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_119
def isoMvS_238:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_231
def isoMvS_246:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_235
def isoMvS_249:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 9:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_245
def isoMvS_252:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_189
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,18),(2,66),(3,11),(3,19),(3,35),(3,67),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,40),(10,11),(10,26),(10,42),(10,74),(12,13),(12,44),(12,76),(14,15),(14,30),(14,46),(14,78),(16,17),(16,18),(16,80),(20,21),(20,22),(20,52),(20,84),(24,25),(24,26),(24,56),(24,88),(28,29),(28,30),(28,60),(28,92),(32,33),(32,36),(32,40),(32,96),(34,35),(34,38),(34,42),(34,50),(34,98),(48,49),(48,50),(48,52),(48,56),(48,112),(64,66),(64,68),(64,80),(64,96),(65,67),(65,69),(65,73),(65,81),(65,97),(72,73),(72,74),(72,76),(72,88),(72,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|8=>2
|9=>1
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xd61c086515
|9,0=>0x761fa
|10,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffffffffffff00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0f0f0f0f0f0f0f0f0f0f0f0f00000000ffffffffffffffff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x654732086547320865432106543210
|_=>0
def sO:Nat→Nat→Nat
|8,0=>0xf007
|9,0=>0xf8
|10,0=>0x177
|_,_=>0
def wAt:=mkWire dB 9 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x18187d8187d81
|_=>0
def oO:Nat→Nat→Nat
|8,0=>0x1102
|9,0=>0x41
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 7
def pmP:Nat→Nat
|0=>0x1ff780
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>9
|9,0=>2
|10,0=>2
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_126 9 roots_126 ops++addP pm 1 dom_123 9 roots_123 ops++addP pm 2 dom_95 8 roots_95 ops++addP pm 3 dom_119 9 roots_119 ops++addP pm 4 dom_63 8 roots_63 ops++addP pm 5 dom_125 9 roots_125 ops++addP pm 6 dom_111 9 roots_111 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_111 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_126 9 s (0,roots_126.map (·&&&dom_126)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_126 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
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
def dzo_61_2:=0xcccccccccccccccc
def gzo_61_2:=0xccccccc8cccc8800
def gsh_61_2:=0x3333333233332200
theorem lowS_zo_61_2_45:Lower true dzo_61_2 roots_61 gzo_61_2 6:=lower_iso_b (d1:=dom_61) (r1:=roots_61) (T1:=gsh_61_2) [(dom_61,2)] (by decide +kernel) (lower_slice_b (T:=gsh_61_2) [(0x3333000033330000,0,16)] (by decide +kernel) lowS_45)
def dzo_174_16:=0x555500005555000000000000000000005555000055550000
def gzo_174_16:=0x555500005554000000000000000000005554000044440000
def gsh_174_16:=0x55550000555400000000000000000000555400004444
theorem lowS_zo_174_16_172:Lower true dzo_174_16 roots_174 gzo_174_16 6:=lower_iso_b (d1:=dom_174) (r1:=roots_174) (T1:=gsh_174_16) [(dom_174,16)] (by decide +kernel) (lower_slice_b (T:=gsh_174_16) [(0x44440000444400000000000000000000444400004444,0,2)] (by decide +kernel) lowS_172)
def dzo_175_16:=0xffff0000ffff00000000000000000000ffff0000ffff0000
def gzo_175_16:=0xffff0000fffe00000000000000000000fffe0000eeee0000
def gsh_175_16:=0xffff0000fffe00000000000000000000fffe0000eeee
theorem lowS_zo_175_16_172:Lower true dzo_175_16 roots_175 gzo_175_16 7:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_16) [(dom_175,16)] (by decide +kernel) (lower_slice_b (T:=gsh_175_16) [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,0,1),(0xcccc0000cccc00000000000000000000cccc0000cccc,0,2)] (by decide +kernel) lowS_172)
def dzo_189_2:=0xcccccccccccccccc0000000000000000cccccccccccccccc
def gzo_189_2:=0xcccccccccccccccc0000000000000000ccccccc8cccc8800
def gsh_189_2:=0x333333333333333300000000000000003333333233332200
theorem lowS_zo_189_2_45:Lower true dzo_189_2 roots_189 gzo_189_2 7:=lower_iso_b (d1:=dom_189) (r1:=roots_189) (T1:=gsh_189_2) [(dom_189,2)] (by decide +kernel) (lower_slice_b (T:=gsh_189_2) [(0x333300003333000000000000000000003333000033330000,0,16),(0x333333333333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_45)
def dzo_173_2:=0xcccc0000cccc00000000000000000000cccc0000cccc
def gzo_173_2:=0xcccc0000cccc00000000000000000000ccc800008800
def gsh_173_2:=0x33330000333300000000000000000000333200002200
theorem lowS_zo_173_2_45:Lower true dzo_173_2 roots_173 gzo_173_2 6:=lower_iso_b (d1:=dom_173) (r1:=roots_173) (T1:=gsh_173_2) [(dom_173,2)] (by decide +kernel) (lower_slice_b (T:=gsh_173_2) [(0x33330000333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_45)
namespace S_191
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,18),(2,130),(3,11),(3,19),(3,35),(3,131),(4,36),(4,132),(5,13),(5,21),(5,37),(5,133),(6,22),(6,38),(6,134),(7,15),(7,23),(7,39),(7,135),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,138),(12,13),(12,44),(12,140),(14,15),(14,30),(14,46),(14,142),(16,17),(16,18),(20,21),(20,22),(20,52),(20,148),(24,25),(24,26),(24,56),(24,152),(28,29),(28,30),(28,60),(28,156),(32,33),(32,36),(32,40),(32,160),(34,35),(34,38),(34,42),(34,50),(34,162),(48,49),(48,50),(48,52),(48,56),(48,176),(128,129),(128,130),(128,132),(128,136),(128,160),(144,145),(144,146),(144,148),(144,152),(144,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7ffffffffffffffffff
def xsM:=roots_191.map (·&&&dom_191)
def gM:=goal_191&&&dom_191
def NN:Nat→Nat
|4=>2
|5=>5
|6=>26
|7=>42
|8=>24
|9=>6
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xbf9c8b595a
|5,0=>0xcfd75b470297b018da9340daa
|6,0=>0xfa2ebf8a87f70c7eea19dfda6c4aafbed64aeb04907df8c83b8c367682355e1c754985530b2511574a29b40756393553466030cfb3026918ee3120271160c0859a
|7,0=>0xed7c1e9617e341fe275be2611e06d3d93b1cc341c91bbc55b3bf14db20ddaa18ea9acc9fa5e9780e927ab8f5878f49885519804ed7db307cd8679e697826675eca71f1a5cf6f5b1d4451fe3fc9931f1f25e2925a3524fa318947111c40fa8a0ede90e9f707b3b06346
|8,0=>0xe6f22dd6bed8159bdef5b0e07b09ddaa82b9e8068c548798cd78e3b787696f97d648015a1de4a59d4264e41659362a52d22a1f196152461260e0e38a
|9,0=>0xfc5eef269ee03e0c437a4eb9911d8d
|10,0=>0x2bff1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfafafafafafafafa0000000000000000fafafafafafafafaffffffffffffffff0000000000000000ffffffffaaaaaaaaffffffffffffffff0000000000000000ffff0000ffff0000eeeeeeeeeeeeeeee0000000000000000eeeeeeeeeeeeeeeecccccccccccccccc0000000000000000ccccccccccccccccaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaaffff0000ffff00000000000000000000ffff0000ffff0000ffffffffffffffff0000000000000000000000000000000000000000ffffffff000000000000000000000000aaaaaaaaf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f000ff00ff00ff00ff000000000000000000ff00ff00aa00aaffffffff000000000000000000000000ffffffff00000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00eeeeeeeeeeeeeeee0000000000000000eeee0000eeee0000ffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0a0a0a0a
|0,1=>0x3333333333333333000000000000000033330000333300000000eeee0000eeee00000000000000000000eeee0000eeee55555555555555550000000000000000555555550000000005050505050505050000000000000000050505050000000000000000000000000000000000000000ffffffffaaaaaaaa000f000f000f000f0000000000000000000f000f000a000aafafafafafafafaf0000000000000000afafafafaaaaaaaa00af00af00af00af000000000000000000af00af00aa00aa0f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000ffffffffffffffff0000000000000000ffffffff00000000ffffffffaaaaaaaa0000000000000000ffffffffaaaaaaaa
|_,_=>0
def sP:Nat→Nat
|0=>0x8a46b0c8895a8b5411a37ac278a46f584f12256a9a0895d1534112b54a68225eb095044ad522a08d199813c523330278112f5950419841235eb095c419841234cc0948d1b02020cc209c86104a418820
|1=>0x4412332c274106612910234665861148ccb0ba0448deb441237ace8224cc0950e225eb2a0891b020439237ace8711a37ac312246c0ca0d199613912b500a8711a3330244ad53411a6585452346b0a810
|2=>0x22291996a3a0891ae8a4408d1bd6822466604e8724665a8e8845237ad1122466605c468ccb0aa1148d6a922c448deb438891bd68891235d1482246ba2a48711237ac28711235aa482346f584891b152
|3=>0x8a466585472246b55d0468ccc091235a8082246f59d0449961515112246c5490448d615010448deb09d112246f586044996a2a20448d6a022244996a2a2091996a3a1c44996a2a22448d61549c448d6a
|4=>0x5aa4889123331488112332c28224665a8e8811237ad0448ccb0a8e88912332c2a22466605041998aca22448d6a9208d1bd6a4408d1996a4112332d58442291996a4388919981411a332c2a391265a8a8
|5=>0x411237ad488112332d488912332d48224666290468ccb52089199615208d1998a458891996a438891996a43889199615208d19961544891bd6a411a332b48740891996a43a2448ccb520891bd6141123
|6=>0x891996a
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x154005
|5,0=>0x226071816604180a6
|6,0=>0x351ccd7319cbf72e1cb172a9ca37271c95723d8887205c7a71cdc6c7195c5e715dc507125c4270edc3470b5c285
|7,0=>0x83e2078801df887c5deb6791ddd77561cd87161bd86d9dae869a19e865a18e861a17e85da16f75a1d6085621517529d4284ea13374b1d248472114843210663fdcf783c58ea738dcdb8
|8,0=>0xb2dec38aee2b29aadea38a71e939a2a68379f1e7489b22648975e54993224578f9e3688bde27887e2178
|9,0=>0xbe1ef08ba22e17b69ed28
|10,0=>0x2ff7
|_,_=>0
def wAt:=mkWire dB 27 192 0xffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x5218a989b2215213294a15a989b2212065216b04a15a94a122952122122952132982122970f2055212055213294a15a94a12055211d254989b22152189b2215213294a11d254989b5a95214a15216b04a15a96b05a94a12055216b05a95214a1
|1=>0x52152132922170f82171b82170f8a922171382122970f20552152189b22171b2055217138a922154989b2214a12293292065215a92062055212212293292215215a94a120552122989b22182322932982122932954989b22154989b221329205
|2=>0x8a922132952189b2212215a92295212065212293292065212215215215a94b25a989b2213294a12294a18ab2212292212055215a92065214a170f20552120652154a89b2214a15215a971b20552132920652170f2055a989b22171b205206329
|3=>0x3292292215a94a15214a15a98232292055212055215214a13292216af4a1821229
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x45000000004
|6,0=>0x2530000002140000000001d41940000001630001330001030000000000000d3000000094
|7,0=>0x9d39a39739529238f38c38938728438227f37c37a27827537236f36c36936636336035d35a35735435134e34b34834534233f33c33933633423132e32b3283
|8,0=>0xce2cc2ca2c82c62c42c22c02be2bc2ba2b82b62b42b22b02ae2ac2aa2a82a62a42a22a02
|9,0=>0xd51d41d31d21d11d01
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 12
def pmP:Nat→Nat
|0=>0xee0007380037c0019c000c7000604002fe00150000a3000508002800010e00086000400001fe000c100047000200000fe0007d0003a8001c4000a400042000200000480001c0000c000030000100000400000
|1=>0x10287f4323f92a1fc502fe201ce100818401fc200f6100790802402a1fc103f40817b040840203fc101f40807f0403d01f1fc0d8fe0467f0223f8111f8050fe0285f0023c8009fc0041e001ff
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x140001
|6,0=>0x380080394000005280488001001000000040021
|7,0=>0x3c92c6d6a32b1c3548c07543404593df4c886b199462d757cdbbfa8c88a435c
|8,0=>0xa5181e979a5fe2cda744db89667ed9ca5660
|9,0=>0xb11668f0d
|10,0=>0xd
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 21 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_189 9 roots_189 ops++addP pm 1 dom_159 8 roots_159 ops++addP pm 2 dom_187 9 roots_187 ops++addP pm 3 dom_183 9 roots_183 ops++addP pm 4 dom_63 8 roots_63 ops++addP pm 5 dom_175 9 roots_175 ops++addP pm 6 dom_190 8 roots_190 ops++addP pm 7 dom_158 5 roots_158 ops++addP pm 8 dom_27 4 roots_27 ops++addP pm 9 dom_172 5 roots_172 ops++addP pm 10 dzo_61_2 6 roots_61 ops++addP pm 11 dzo_174_16 6 roots_174 ops++addP pm 12 dom_173 8 roots_173 ops++addP pm 13 dzo_175_16 7 roots_175 ops++addP pm 14 dzo_189_2 7 roots_189 ops++addP pm 15 dom_186 7 roots_186 ops++addP pm 16 dzo_155_4 5 roots_155 ops++addP pm 17 dzo_27_4 4 roots_27 ops++addP pm 18 dom_171 8 roots_171 ops++addP pm 19 dzo_173_2 6 roots_173 ops++addP pm 20 dom_45 5 roots_45 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_191 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_61_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_174_16_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_175_16_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_189_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_155_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_27_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_173_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_45 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_189 9 s (0,roots_189.map (·&&&dom_189)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_191 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_189 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_191 gM v ys):RunD true dom_191 gM v (ori ys):=h
def Z (s:Nat):=barP dom_191 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 26 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 26 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 42 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 42 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 24 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 6 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_191 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_191 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_191 roots_191 goal_191 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_191
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=S_191.noCircuit
def dzo_87_8:=0xff00ff0000000000ff00ff00
def gzo_87_8:=0xff00fe0000000000ee00aa00
def gsh_87_8:=0xff00fe0000000000ee00aa
theorem lowS_zo_87_8_86:Lower true dzo_87_8 roots_87 gzo_87_8 6:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_8) [(dom_87,8)] (by decide +kernel) (lower_slice_b (T:=gsh_87_8) [(0xaa00aa0000000000aa00aa,0,1)] (by decide +kernel) lowS_86)
def dzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00
def gzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000ee00aa00
def gsh_215_8:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000ee00aa
theorem lowS_zo_215_8_86:Lower true dzo_215_8 roots_215 gzo_215_8 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_8) [(dom_215,8)] (by decide +kernel) (lower_slice_b (T:=gsh_215_8) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xff00ff0000000000ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_86)
namespace S_223
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,129),(2,18),(2,66),(2,130),(3,11),(3,19),(3,67),(3,131),(4,68),(4,132),(5,13),(5,21),(5,69),(5,133),(6,22),(6,70),(6,134),(7,15),(7,23),(7,71),(7,135),(8,9),(8,136),(10,11),(10,26),(10,74),(10,138),(12,13),(12,76),(12,140),(14,15),(14,30),(14,78),(14,142),(16,17),(16,18),(16,80),(20,21),(20,22),(20,84),(20,148),(24,25),(24,26),(24,88),(24,152),(28,29),(28,30),(28,92),(28,156),(64,66),(64,68),(64,80),(64,192),(65,67),(65,69),(65,73),(65,81),(65,193),(72,73),(72,74),(72,76),(72,88),(72,200),(128,129),(128,130),(128,132),(128,136),(128,192),(144,145),(144,146),(144,148),(144,152),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7ffffffffffffffffff
def xsM:=roots_223.map (·&&&dom_223)
def gM:=goal_223&&&dom_223
def NN:Nat→Nat
|6=>3
|7=>7
|8=>5
|9=>4
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x974147d3b509eda
|7,0=>0xc844787e0c8711c3f1063c3192df992b1ac
|8,0=>0xd2e9ed21ae44642256450d5a7
|9,0=>0xe400b799006375a4e3a9
|10,0=>0x1730e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00ffff000000000000ffff000000000000ffff000000000000ffff00000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f00000000000000000000ffffffff000000000000000000000000ffff0000ffffffff00000000ffffffff00000000ffffffff00000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0ffffffff00000000ffffffff00000000ffffffff00000000ffff0000cccccccc00000000cccccccc00000000cccccccc00000000ccccccccffffffff00000000ffffffff00000000ffff000000000000ffff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa3333333300000000333333330000000033333333000000003333000003030303000000000303030300000000030303030000000003030000ffffffff000000000000000000000000ffffffff0000000000000000ffffffff00000000ffffffff00000000000000000000000000000000
|0,1=>0xffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00
|_,_=>0
def sP:Nat→Nat
|0=>0x39e549c81038a939161020c549c81018a939161714e458540330a939020714e40a80629c8b0a90661527200cc2a4e4598a7234203152418408314e46840831524184062906d080cc29c8b518a418820
|1=>0xe2a4e4080c549c8103a0549c81
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0xe7077007
|7,0=>0x4273a83372c72571d8158
|8,0=>0x678607588508497
|9,0=>0x8777f87786f8
|10,0=>0x8e7
|_,_=>0
def wAt:=mkWire dB 17 224 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x7012852810813057010817014ae0813077014ae0817014ae08130730570130708170142730570141f30570142730570141f30570148e41f
|_=>0
def oO:Nat→Nat→Nat
|6,0=>2
|7,0=>0x14344ce32cc8314c23
|8,0=>0x1f2749b264972
|9,0=>0x9063188611
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0x7bd7fa7fcfe9bd1fa1f41f83505c01c01000
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x7264533
|8,0=>0xa9999
|9,0=>0x9bc9
|10,0=>8
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 11 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_222 9 roots_222 ops++addP pm 1 dom_143 6 roots_143 ops++addP pm 2 dom_159 8 roots_159 ops++addP pm 3 dom_219 9 roots_219 ops++addP pm 4 dom_207 9 roots_207 ops++addP pm 5 dom_221 9 roots_221 ops++addP pm 6 dzo_87_8 6 roots_87 ops++addP pm 7 dom_95 8 roots_95 ops++addP pm 8 dom_215 8 roots_215 ops++addP pm 9 dzo_215_8 7 roots_215 ops++addP pm 10 dom_87 6 roots_87 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_223 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_87_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_215_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_87 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_222 9 s (0,roots_222.map (·&&&dom_222)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_223 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_222 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_223 gM v ys):RunD true dom_223 gM v (ori ys):=h
def Z (s:Nat):=barP dom_223 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 3 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 5 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 4 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_223 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_239:Lower true dom_239 roots_239 goal_239 12:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,64,66)] (by decide +kernel) lowS_237
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_246
def dzo_115_8:=0xf000f000f000f000f000f000f000f00
def gzo_115_8:=0xf000f000f000e000f000f000e000a00
def gsh_115_8:=0xf000f000f000e000f000f000e000a
theorem lowS_zo_115_8_82:Lower true dzo_115_8 roots_115 gzo_115_8 6:=lower_iso_b (d1:=dom_115) (r1:=roots_115) (T1:=gsh_115_8) [(dom_115,8)] (by decide +kernel) (lower_slice_b (T:=gsh_115_8) [(0xa000a000a000a000a000a000a000a,0,1),(0xf000f00000000000f000f00000000,0,32)] (by decide +kernel) lowS_82)
def dzo_243_8:=0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00
def gzo_243_8:=0xf000f000f000f000f000f000f000f000f000f000f000e000f000f000e000a00
def gsh_243_8:=0xf000f000f000f000f000f000f000f000f000f000f000e000f000f000e000a
theorem lowS_zo_243_8_82:Lower true dzo_243_8 roots_243 gzo_243_8 7:=lower_iso_b (d1:=dom_243) (r1:=roots_243) (T1:=gsh_243_8) [(dom_243,8)] (by decide +kernel) (lower_slice_b (T:=gsh_243_8) [(0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a,0,1),(0xf000f00000000000f000f00000000000f000f00000000000f000f00000000,0,32),(0xf000f000f000f000f000f000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_249_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_249_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c0c0800
def gsh_249_2:=0x303030303030303030303030303030303030303030303030303030203030200
theorem lowS_zo_249_2_41:Lower true dzo_249_2 roots_249 gzo_249_2 7:=lower_iso_b (d1:=dom_249) (r1:=roots_249) (T1:=gsh_249_2) [(dom_249,2)] (by decide +kernel) (lower_slice_b (T:=gsh_249_2) [(0x303000003030000030300000303000003030000030300000303000003030000,0,16),(0x303030303030303000000000000000003030303030303030000000000000000,0,64),(0x303030303030303030303030303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_233_16:=0x303000003030000030300000303000003030000030300000303000003030000
def gzo_233_16:=0x303000003030000030300000302000003030000030300000302000002020000
def gsh_233_16:=0x30300000303000003030000030200000303000003030000030200000202
theorem lowS_zo_233_16_168:Lower true dzo_233_16 roots_233 gzo_233_16 6:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_16) [(dom_233,16)] (by decide +kernel) (lower_slice_b (T:=gsh_233_16) [(0x20200000202000002020000020200000202000002020000020200000202,0,1),(0x30300000303000000000000000000000303000003030000000000000000,0,64)] (by decide +kernel) lowS_168)
def dzo_185_2:=0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c
def gzo_185_2:=0xc0c0c0c0c0c0c0c00000000000000000c0c0c080c0c0800
def gsh_185_2:=0x30303030303030300000000000000000303030203030200
theorem lowS_zo_185_2_41:Lower true dzo_185_2 roots_185 gzo_185_2 6:=lower_iso_b (d1:=dom_185) (r1:=roots_185) (T1:=gsh_185_2) [(dom_185,2)] (by decide +kernel) (lower_slice_b (T:=gsh_185_2) [(0x30300000303000000000000000000000303000003030000,0,16),(0x30303030303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_171_16:=0xf0f00000f0f000000000000000000000f0f00000f0f0000
def gzo_171_16:=0xf0f00000f0e000000000000000000000f0e00000e0e0000
def gsh_171_16:=0xf0f00000f0e000000000000000000000f0e00000e0e
theorem lowS_zo_171_16_168:Lower true dzo_171_16 roots_171 gzo_171_16 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_16) [(dom_171,16)] (by decide +kernel) (lower_slice_b (T:=gsh_171_16) [(0xa0a00000a0a000000000000000000000a0a00000a0a,0,1),(0xc0c00000c0c000000000000000000000c0c00000c0c,0,2)] (by decide +kernel) lowS_168)
def dzo_83_8:=0xf000f00000000000f000f00
def gzo_83_8:=0xf000e00000000000e000a00
def gsh_83_8:=0xf000e00000000000e000a
theorem lowS_zo_83_8_82:Lower true dzo_83_8 roots_83 gzo_83_8 5:=lower_iso_b (d1:=dom_83) (r1:=roots_83) (T1:=gsh_83_8) [(dom_83,8)] (by decide +kernel) (lower_slice_b (T:=gsh_83_8) [(0xa000a00000000000a000a,0,1)] (by decide +kernel) lowS_82)
def dzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def gzo_235_16:=0xf0f00000f0f00000f0f00000f0e00000f0f00000f0f00000f0e00000e0e0000
def gsh_235_16:=0xf0f00000f0f00000f0f00000f0e00000f0f00000f0f00000f0e00000e0e
theorem lowS_zo_235_16_168:Lower true dzo_235_16 roots_235 gzo_235_16 7:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_16) [(dom_235,16)] (by decide +kernel) (lower_slice_b (T:=gsh_235_16) [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a,0,1),(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c,0,2),(0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_168)
def dzo_211_8:=0xf000f00000000000f000f00000000000f000f00000000000f000f00
def gzo_211_8:=0xf000f00000000000f000f00000000000f000e00000000000e000a00
def gsh_211_8:=0xf000f00000000000f000f00000000000f000e00000000000e000a
theorem lowS_zo_211_8_82:Lower true dzo_211_8 roots_211 gzo_211_8 6:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_8) [(dom_211,8)] (by decide +kernel) (lower_slice_b (T:=gsh_211_8) [(0xa000a00000000000a000a00000000000a000a00000000000a000a,0,1),(0xf000f00000000000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,18),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(16,17),(16,18),(16,80),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,40),(32,96),(32,160),(34,35),(34,42),(34,50),(34,98),(34,162),(48,49),(48,50),(48,56),(48,112),(48,176),(64,66),(64,80),(64,96),(64,192),(65,67),(65,73),(65,81),(65,97),(65,193),(72,73),(72,74),(72,88),(72,104),(72,200),(128,129),(128,130),(128,136),(128,160),(128,192),(144,145),(144,146),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|6=>1
|7=>3
|8=>15
|9=>55
|10=>10
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x2f379
|7,0=>0x859f829c15247fe
|8,0=>0xf4ed7eeda7d75f096ca7802947ae7d5cae3590d22d7bd2975b19058117b40a387057de05127
|9,0=>0xfc1abfb416f9b0bf6011f0143eb9c9e8b19e04efd5c26c491dc28a5c0e1dbff33b5c01b3ee5ac976a4324a40ab980d597a1e921598bf19876ad8575d84b248464b77bf77168b702ad69ee75fa065c2ca5ab02540114e07145426443213cbc13abc13725536b5f3474031e693163b309062c43623bdb1c096182a81778b16f15138f40e4dd022db0026a
|10,0=>0xfd547eb5f5e3d59d8a86ce221ac43596f856c0fe58b413ecf2
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000000000000000000000000000000f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a303030303030303030303030303030303030303030303030303000003030000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000
|0,1=>0xf0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c00000000000000000000000000000000f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f000000000000f0c0f0c000000000f0c0f0c000000000f0c0f0c000000000f0c0f0c00000000000000000000000000000000f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0000000000000000f0f0f0f0f0f0f0f00000000000000000f000f000f000f0000f000f000f000f000f000f00000000000f000f000f000f000f000f0000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0cf0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
|0,2=>0x30303030303030303030303030303030300030003000300030003000300030000f000f000f000f000f000f000f000f000c000c000c000c000c000c000c000c0000000000000000f0f0f0f0f000f0000000000000000000f0f0f0f0f000f0000000000f0f0f0f000000000f0f0f0f000000000c0c0c0c000000000c0c0c0c00000000f0f0f0f000000000f0f0f0f000000000f000f00000000000f000f0000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c303030303000300030303030300030003030303030003000303030303000300f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f000f0f0f00f0f0f0f0f0c0f0c0f0f0f0f0f0c0f0c0f0f0f0f0f0c0f0c0f0f0f0f0f0c0f0c00f000f000c000c000f000f000c000c000f000f000c000c000f000f000c000c00000000f0f0f0f000000000f000f00000000000f0f0f0f000000000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f00
|_,_=>0
def sP:Nat→Nat
|0=>0xc709200f1440c70922853040c708024a1481031c20092851031c248044e2cd0c70802851034070801444c31c24851030810093ce2c31c24911440d00803ce2cd0c708028e2cd1c200a1440c204024614c1031c20061481031c20061440c2040
|1=>0x1440c708024f1440c70802452c31c268025914b0c70802452c36070802452c31c25c02452d60c708025514b0c708025114b0d00802452d33470802453040c70802452040c70802452d40d008025138b0c70802451140d00801851031c200a38b
|2=>0x1c200914b0c70a200954f14b0c70802451140c708024a14b0c709200914b0c70a100914b8031c20097c52c31c200914b7831c200914b7431c20092851031c20092852d31c20093852cd0c70802852c340708025c14b0c70802452d30c709225b
|3=>0x802452d434708024510340708028e2c31c200914b0c70a80097cf14b0c708024f38b0c708026714b0c708024f14b0c709224f14b3431c20092852cd1c20093c52d30c70899852c31c200914b0c70a50094451031c20091641031c20098c52c3
|4=>0x802452c340708025114b0c70802452d40c708024a14b0c708024f14b0c70802452cd0c708024614b0c708024e14b0c70920052c31c2b002452c31c2ac02451031c24804452cd0c708026a14b0c708025114b5030802452c31c2a402451130c7
|5=>0x52c31c200914b0c709200914b4c31c20093852c31c20091440c7
|_=>0
def sO:Nat→Nat→Nat
|6,0=>7
|7,0=>0x17803e0078
|8,0=>0x8a720dc7b81d1c6b918a45a814a04a810dc3c70d5c2e709a01f7
|9,0=>0x24588f623588b62267876615883620587f61f587b9de6877a1d597361c586f61b496b21a48672194863218485f217485ae563856a552852a14284ea13284aa122846a111942610183e60f183a60e183660d183260c182e60b182a60a182660918
|10,0=>0xa5228c8a1227d79d626d899625d895624d8
|11,0=>0x29c7
|_,_=>0
def wAt:=mkWire dB 45 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc0441d2c944012c947250c7451d1494b251c9431d2c94a27143402514345252c94501009441d1434b2514344012c9450d0094b2514943251474b2514347250c040252c9481f1004b25149450100947251474b2514945010c943251434525143481f1004b25289c50d2c94b25289c50d
|1=>0xc9450d0c945010c04e1d1494a1f143451d2c9440d2c9510d147510f1474f25140431d2c9450d009454e0c053250c0454d0c04d1d0c954270c7450d2c9450d0c04325149450d1c94e0d14940250c045112c945012c945520c751271474d030c94f0f14053270c04e0114947251474325
|2=>0x250c045252c94725147431d14345010c94a2714340251494d1f0c943421c940252c943251474a03143431d14745421c943012c9431d0c947252c9450d14945360c94f0d14045011494f2714045010094501
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x64033003
|8,0=>0x3433132e32b32832532231f31c31931631331030d30a3
|9,0=>0xa32a129f29d29b29929729529329128f28d28b28928728528328127f27d27b27927727527327126f26d26b26926726526326125f25d25b25925725525325124f24d24b24924724524324123f23d23b2392372
|10,0=>0xae1ad1ac1ab1aa1a91a81a71a61a51
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x30026de00242399c00405f3780080126f000f2749e0012449bc00208937800213a6f0004074de0008069bc00085f37800103a6f0001224de000184ebc0001ffb780003536f00003fcde00006e9bc0000a93780000bf6f0000174de000027db400004f37800009a6f0000074de0000079bc000009b780000126f0000001c000000006000000003000000000
|1=>0x1004034de2002469bc40000d37843801f6f086003ede10a0079bc21000f37842001a6f0600226fe0c0001078158109b78200024e601f0026de0280c4dbc038009b780690126f00d0024de0184049bc03000d3780600126f0080024de00a4049bc012ca93780259126f0049626de0090469bc0108093780203176f00402b4de0080549bc0100893780180bf6f
|2=>0x108c087dbd41008937a020b176f4040224de8002449bc900009f78c600926f18c0034de3080069bc42181533884203a6f1010034de201a4e9bc40185d37880303a6f
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x4103
|8,0=>0x9051e66d9a203645e1260ca294
|9,0=>0x25518467e10b2689dbe2055fc85cb17c40f1d48e4f389a66130ec68619f4a181a00f82e9ab19a68bad72c10bd6f250a8
|10,0=>0xe384a146999621596
|11,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 35 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_123 9 roots_123 ops++addP pm 2 dom_243 9 roots_243 ops++addP pm 3 dom_249 9 roots_249 ops++addP pm 4 dom_233 8 roots_233 ops++addP pm 5 dom_187 9 roots_187 ops++addP pm 6 dom_185 8 roots_185 ops++addP pm 7 dom_171 8 roots_171 ops++addP pm 8 dom_107 7 roots_107 ops++addP pm 9 dom_219 9 roots_219 ops++addP pm 10 dzo_115_8 6 roots_115 ops++addP pm 11 dzo_243_8 7 roots_243 ops++addP pm 12 dom_235 10 roots_235 ops++addP pm 13 dom_83 5 roots_83 ops++addP pm 14 dom_121 6 roots_121 ops++addP pm 15 dom_211 6 roots_211 ops++addP pm 16 dzo_249_2 7 roots_249 ops++addP pm 17 dzo_233_16 6 roots_233 ops++addP pm 18 dzo_185_2 6 roots_185 ops++addP pm 19 dzo_121_2 6 roots_121 ops++addP pm 20 dom_91 7 roots_91 ops++addP pm 21 dom_115 6 roots_115 ops++addP pm 22 dom_217 6 roots_217 ops++addP pm 23 dom_59 7 roots_59 ops++addP pm 24 dzo_171_16 6 roots_171 ops++addP pm 25 dzo_83_8 5 roots_83 ops++addP pm 26 dom_155 6 roots_155 ops++addP pm 27 dom_203 8 roots_203 ops++addP pm 28 dom_105 5 roots_105 ops++addP pm 29 dzo_235_16 7 roots_235 ops++addP pm 30 dom_179 6 roots_179 ops++addP pm 31 dzo_211_8 6 roots_211 ops++addP pm 32 dom_41 4 roots_41 ops++addP pm 33 dom_241 6 roots_241 ops++addP pm 34 dom_227 7 roots_227 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_115_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_243_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_249_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_233_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_185_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_121_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_171_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_83_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_235_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_211_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_227 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 15 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 55 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 55 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 10 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 10 0 = true)
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
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_slice_b [(0x3333000033330000333300003333000033330000333300003333000033330000,1,17)] (by decide +kernel) lowS_237
theorem lowS_254:Lower true dom_254 roots_254 goal_254 11:=lower_slice_b [(0x5050505050505050505050505050505050505050505050505050505050505050,32,36)] (by decide +kernel) lowS_250
def dzo_109_2:=0xcccc0000cccc0000cccc0000cccc
def gzo_109_2:=0xcccc0000cccc0000ccc800008800
def gsh_109_2:=0x3333000033330000333200002200
theorem lowS_zo_109_2_45:Lower true dzo_109_2 roots_109 gzo_109_2 6:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_2) [(dom_109,2)] (by decide +kernel) (lower_slice_b (T:=gsh_109_2) [(0x3333000033330000000000000000,0,64)] (by decide +kernel) lowS_45)
def dzo_238_16:=0x5555000055550000555500005555000055550000555500005555000055550000
def gzo_238_16:=0x5555000055550000555500005554000055550000555500005554000044440000
def gsh_238_16:=0x555500005555000055550000555400005555000055550000555400004444
theorem lowS_zo_238_16_172:Lower true dzo_238_16 roots_238 gzo_238_16 7:=lower_iso_b (d1:=dom_238) (r1:=roots_238) (T1:=gsh_238_16) [(dom_238,16)] (by decide +kernel) (lower_slice_b (T:=gsh_238_16) [(0x444400004444000044440000444400004444000044440000444400004444,0,2),(0x555500005555000000000000000000005555000055550000000000000000,0,64)] (by decide +kernel) lowS_172)
def dzo_59_4:=0xf0f0f0f0f0f0f0f0
def gzo_59_4:=0xf0f0f0f0e0e0a000
def gsh_59_4:=0xf0f0f0f0e0e0a00
theorem lowS_zo_59_4_27:Lower true dzo_59_4 roots_59 gzo_59_4 5:=lower_iso_b (d1:=dom_59) (r1:=roots_59) (T1:=gsh_59_4) [(dom_59,4)] (by decide +kernel) (lower_slice_b (T:=gsh_59_4) [(0xf0f0f0f00000000,0,32)] (by decide +kernel) lowS_27)
def dzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def gzo_239_16:=0xffff0000ffff0000ffff0000fffe0000ffff0000ffff0000fffe0000eeee0000
def gsh_239_16:=0xffff0000ffff0000ffff0000fffe0000ffff0000ffff0000fffe0000eeee
theorem lowS_zo_239_16_172:Lower true dzo_239_16 roots_239 gzo_239_16 8:=lower_iso_b (d1:=dom_239) (r1:=roots_239) (T1:=gsh_239_16) [(dom_239,16)] (by decide +kernel) (lower_slice_b (T:=gsh_239_16) [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,0,1),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,0,2),(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,0,64)] (by decide +kernel) lowS_172)
def dzo_237_16:=0x3333000033330000333300003333000033330000333300003333000033330000
def gzo_237_16:=0x3333000033330000333300003332000033330000333300003332000022220000
def gsh_237_16:=0x333300003333000033330000333200003333000033330000333200002222
theorem lowS_zo_237_16_172:Lower true dzo_237_16 roots_237 gzo_237_16 7:=lower_iso_b (d1:=dom_237) (r1:=roots_237) (T1:=gsh_237_16) [(dom_237,16)] (by decide +kernel) (lower_slice_b (T:=gsh_237_16) [(0x222200002222000022220000222200002222000022220000222200002222,0,1),(0x333300003333000000000000000000003333000033330000000000000000,0,64)] (by decide +kernel) lowS_172)
def dzo_231_16:=0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
def gzo_231_16:=0xff000000ff000000ff000000fe000000ff000000ff000000fe000000ee0000
def gsh_231_16:=0xff000000ff000000ff000000fe000000ff000000ff000000fe000000ee
theorem lowS_zo_231_16_164:Lower true dzo_231_16 roots_231 gzo_231_16 7:=lower_iso_b (d1:=dom_231) (r1:=roots_231) (T1:=gsh_231_16) [(dom_231,16)] (by decide +kernel) (lower_slice_b (T:=gsh_231_16) [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,0,1),(0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc,0,2),(0xff000000ff0000000000000000000000ff000000ff0000000000000000,0,64)] (by decide +kernel) lowS_164)
def dzo_119_8:=0xff00ff00ff00ff00ff00ff00ff00ff00
def gzo_119_8:=0xff00ff00ff00fe00ff00ff00ee00aa00
def gsh_119_8:=0xff00ff00ff00fe00ff00ff00ee00aa
theorem lowS_zo_119_8_86:Lower true dzo_119_8 roots_119 gzo_119_8 7:=lower_iso_b (d1:=dom_119) (r1:=roots_119) (T1:=gsh_119_8) [(dom_119,8)] (by decide +kernel) (lower_slice_b (T:=gsh_119_8) [(0xaa00aa00aa00aa00aa00aa00aa00aa,0,1),(0xff00ff0000000000ff00ff00000000,0,32)] (by decide +kernel) lowS_86)
def dzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def gzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fe00ff00ff00ee00aa00
def gsh_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fe00ff00ff00ee00aa
theorem lowS_zo_247_8_86:Lower true dzo_247_8 roots_247 gzo_247_8 8:=lower_iso_b (d1:=dom_247) (r1:=roots_247) (T1:=gsh_247_8) [(dom_247,8)] (by decide +kernel) (lower_slice_b (T:=gsh_247_8) [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,0,1),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000,0,32),(0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_86)
def dzo_246_8:=0x5500550055005500550055005500550055005500550055005500550055005500
def gzo_246_8:=0x5500550055005500550055005500550055005500550054005500550044000000
def gsh_246_8:=0x55005500550055005500550055005500550055005500540055005500440000
theorem lowS_zo_246_8_86:Lower true dzo_246_8 roots_246 gzo_246_8 7:=lower_iso_b (d1:=dom_246) (r1:=roots_246) (T1:=gsh_246_8) [(dom_246,8)] (by decide +kernel) (lower_slice_b (T:=gsh_246_8) [(0x55005500000000005500550000000000550055000000000055005500000000,0,32),(0x55005500550055005500550055005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_86)
def dzo_91_4:=0xf0f0f0f000000000f0f0f0f0
def gzo_91_4:=0xf0f0f0f000000000e0e0a000
def gsh_91_4:=0xf0f0f0f000000000e0e0a00
theorem lowS_zo_91_4_27:Lower true dzo_91_4 roots_91 gzo_91_4 5:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_4) [(dom_91,4)] (by decide +kernel) (lower_slice_b (T:=gsh_91_4) [(0xf0f0f0f0000000000000000,0,64)] (by decide +kernel) lowS_27)
def dzo_118_8:=0x55005500550055005500550055005500
def gzo_118_8:=0x55005500550054005500550044000000
def gsh_118_8:=0x550055005500540055005500440000
theorem lowS_zo_118_8_86:Lower true dzo_118_8 roots_118 gzo_118_8 6:=lower_iso_b (d1:=dom_118) (r1:=roots_118) (T1:=gsh_118_8) [(dom_118,8)] (by decide +kernel) (lower_slice_b (T:=gsh_118_8) [(0x550055000000000055005500000000,0,32)] (by decide +kernel) lowS_86)
def dzo_229_16:=0x33000000330000003300000033000000330000003300000033000000330000
def gzo_229_16:=0x33000000330000003300000032000000330000003300000032000000220000
def gsh_229_16:=0x3300000033000000330000003200000033000000330000003200000022
theorem lowS_zo_229_16_164:Lower true dzo_229_16 roots_229 gzo_229_16 6:=lower_iso_b (d1:=dom_229) (r1:=roots_229) (T1:=gsh_229_16) [(dom_229,16)] (by decide +kernel) (lower_slice_b (T:=gsh_229_16) [(0x2200000022000000220000002200000022000000220000002200000022,0,1),(0x3300000033000000000000000000000033000000330000000000000000,0,64)] (by decide +kernel) lowS_164)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,18),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,17),(16,18),(16,80),(20,21),(20,22),(20,52),(20,84),(20,148),(24,25),(24,26),(24,56),(24,88),(24,152),(28,29),(28,30),(28,60),(28,92),(28,156),(32,33),(32,36),(32,40),(32,96),(32,160),(34,35),(34,38),(34,42),(34,50),(34,98),(34,162),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,68),(64,80),(64,96),(64,192),(65,67),(65,69),(65,73),(65,81),(65,97),(65,193),(72,73),(72,74),(72,76),(72,88),(72,104),(72,200),(128,129),(128,130),(128,132),(128,136),(128,160),(128,192),(144,145),(144,146),(144,148),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|7=>31
|8=>217
|9=>367
|10=>246
|11=>67
|12=>10
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xf844eefc69dd0c9dc21bd6231cf86ccb84ec0adcbc340b72ceb290eafff795bed814b780e6a806637b9d579c806ee775d54759969545584a0b33847a380c01cd3b196fd17d6d0ed8f0c9390b3a8
|8,0=>0x9be719bbb6989a5980b096344949579449493e6c92ac092473920c58f1ca8deb58d3558c7e08b5c58b0fb884f08655f83f9082eb0815f6814b78131e80ac27fd1d7e89f7e6867cfa27ca0a7c8637c41e7c3927b3157aaf479c40795d278c5e784c8782e577d887366370ebd70e11705496eb506ad20693cf6932267480657ca653836444462f3862ab462310620f86177e5eb595e4f35b6bc59a48591e3578a15474452e4e513f250f454fdf94ed854e2434cb6e4c5004aa70495cf446414154f3dcd93d8473d13d3cc1c3c2503b40e3a2b239abc3946938a7d388b93822935e0a31e383124b308d72eede2da292bf572a259280f227af62542524c7522f6820f781d9c01d4ce1d3731c8b81ba4a1a6241957117c2f168751659515b0315ae91564c14c5e13bb1103440ffbc0f4230f1a50d0c30c3b70b9ee09a5706fcd0052c
|8,1=>0xffe9cff916fe017fdabafd655fc5f6fc107fbfb7faa32fa3c4f9a50f8e0bf67d0f34f8f1fbdf1a43f1218f11e4f00cbee9deee6d2ee41ced919eb70beb510eadd7ea114e854de8480e6976e65bce5eaee5003e4591e455ce40cde3f01e3d2ae098cdee18ddd4ed6aafd687ed4fecd3010d2355d1d37cf007cee3ccb237c4b13c490fc47fdc3832c2ff9c1600c0dd2be3d7be2b9bd9e3bb1c7baf87ba752b9ddeb98b2b98a4b8a20b7c8bb74bfb6ad9b47d2b455ab38bab05e1ae122ab165aa4a2a8d2fa7300a694aa5c3da2baaa1f35a1d6aa0f599f6179e1659d4f89cbf6
|9,0=>0x5c6915c52f5c0795aece59eec59b0b5973a5899e580b357df857de85775e57597572c955ea155de85579854f6f54f1b5484754802542f252e4e52bd9520974e8054dbc64c8ae4bfd24b2964b2734ae2e4abe34ab254a83048eee47fa24766e475a9469ab44f04445e442e15428f44285441167405c13dafa3d5603d2033cd043c12a3bf5f390ff38fd4387133866037a2136b9f3645236402353f334a5e33e243311532a413284d2e5ce2ddb42d22d2b6d32b2232aec829fe12881c2845827dbc277db276782671626618262e725de2248ee2430d2425e22e65215c52134a205661f3b91efe11e12f1de001d9c01d36a1c40719d4e199091781e16149151541307812daa1145a0f85a0f6530f29b0e7a20d7100d6340c4bd0c3ce0c03b0be0d0aa880a41407bb10626f04ad60490102f080287801cae00a03003a10035c002c3
|9,1=>0xb196ab12acb0d8bb07bdb00b8af06bae421ad348ac74eac690ac4c5ac460abc4aab840aadfcaa96da9c0ea9346a8139a809aa794da7925a7752a7307a56b8a478fa3c59a36cea2fcaa2c0ea2a73a21cca07d3a038ea01439fdd39e5c79cbce9b7d09ab409a01b9977e995949958d9861096f3b96f0f95a9d959829580895314944b99320d92f6092ac092845922c99174f90e36904048f8c68f8168f3a58edc88db688d9a08cb648ca3b8c91e8c3f38b9628b249887ee8858e87a908518e84989842a5815e48150c80b51802337f0827ec7a7e5397adfa7863577bae777ce77272769017607875f3a75a19745bf745417402073701730af716b6714f5710266fdac6fd256fafc6f3896ef6b6d6296cc876c853696d467cdb66ac066187647fb642da63337630fd62b4d622c761ce86037f601615f84c5ebe95e2225e1775da72
|9,2=>0xffecdff441ff349fe8b1fe601fda70fd8eefd5fafc65ffc5f2fc3b7fc12efb482facf5f9a89f86d8f67e0f5333f3a6df3820f2bdbf211aefa74ef357eebeeed8b5ecc7cea74ce9077e876de7e92e77d2e6f79e6bb8e6ad7e65f5e53aae4209e33bae2df7e2484e1b6ee1953e0ec4df9f0df747df5afde200ddd4eddbb5dc6cbdbc2fdac79daa13d9cd0d67dbd66b5d5cc3d593fd55f4d3fafd1d8cd1d2bd1a9ed14ffd0eadd02d8cda9ecd754ccde0cc3c9cc065cbd5bcb8b0cb3e7cb006c9b1fc8bcfc8460c5decc3ef8c302cc2857c1c1ac12edc0e1fbfbf4bfa1cbf71cbf35cbe8ecbd070bc76ebc329bc0debc020bbb5dbbb58bbaabba11ab902db7f53b7e32b6f5db5a7ab56c1b5660b521bb4cbcb4138b1a5b
|10,0=>0x83fc280f1880d5580c047e6d27de5c7bc857bc127b6f17b5077abf479f6478a7078262769587692576335760007319f7145d70c95707ed703586f1ff6e9d96dbac6d6196b3fd69fa7694ae688d26466a63cc563be3603e45e9c05c5d05bca35aa535a39a5987358ba758a7557fef56ca4557cf544085352752cb551bca4f7dd4ee384e7ed4e3304c81a4be754bba74b00a4aa7448a6b45922451cb41ee04174b3e06e3d76f3d6fe3bd053b6753ae5f37e6d36d1a36a89355463452731e8b2fa462dada2d19c2d0532b09b2ab7a2999d2923828e4f28c55288fc288712777a2708526e78267e8266b22620b22d02217902166a1f8d41d7761c6881bbf41b183194791743615c8a1402d13a76122fc11b36105bf0f4b20eb890e7030d2470ba0e0ae840ac370aa47096b5091940794e0707006d6705bdd04d1304b66041e4025a9
|10,1=>0xfebe9fe2c0fd981fc66afb2fefa31cf73d7f660cf4955f4654f3dcbf2de1f26a8f204cf1e2af1cc7f0d50f0431ef357edf18edc5bedbf2ed2ffed0dceaceaea028e8eb5e17bae0f36e0722e06ebe054fdffe6dea74dd58cdc93cdbf9bd9918d77fcd65f0d5b4bd5b3bd2c6ecf125cefecce670cd746cb895cb376c8a5cc86ffc86c3c81a2c6c41c6965c5838c4852c475fc40bec2e8ac2c57c1723c07bbbf161bea0ebde6fbd0a2baf56baaf3ba3e1ba309b9cb2b8910b8370b54e7b4155b1807b1432b0b95b09abb0295af05dae1ffad45aaca28a9b87a9b5ba8215a2e6ca0e2a9f6fe9d77b9c5a59c1df9ad309abe59a84f99df79954c9917c9890d983709833e97d9f95cd592ce992150903bf903948ebe58dd188d0ef8ba748b9d68b042898a587dab8680c
|11,0=>0xf2f5cf2cdbe76b0e469ae2958df0a7dc52adbc69d9c9dd6a8ed6578cbd95c7aa2c6ccac67a9c4871c3e3fc1b85c13aec00dcbc505b6b15b4102a763da6f8ba30979d9fc9b4f29ae8296f2d902838a7577acdd795637856b77077732c87176a703fb6f8866c4d7668d765e50642dc5862257fb951a4a518e24ea87428f6404e735a8033f6d2f4092bfee2b4a52b1ad2986b24a6b1884614d98130ba11a1d09e08097c70946307de9
|12,0=>0xfff0bdd9d2c6ddca6e4299b3f792e42da102bad80eef70c075
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f000f00000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f000f0000000000000000000000000000000000ffffffffffffffffffffffffaaaaaaaaffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc555555555555555555555555555555555555555555555555555555550000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00ff00ff00aa00aaffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
|0,1=>0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0a050505050505050505050505050505050505050505050505050505050000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff000000aa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f00000a0affffffffffffffffffffffffffffffff0000ffff0000ffff0000aaaa0000aaaaafafafafafafafafafafafafafafafafafafafafafafafafafafafafaaaaaaaa00af00af00af00af00af00af00af00af00af00af00af00af00af00af00aa00aa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0affffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00000000ffffffff00000000ffffffff00000000ffffffff00000000aaaaaaaa0000000000000000ffffffffffffffff0000000000000000ffffaaaaffffaaaaffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa0000000000000000ffffffffffffffff0000000000000000ffff0f0fffff0000
|0,2=>0xffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff0000000000000000000000000000000000ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaaaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00003333333333333333333333333333333333333333333333333333333333330000ffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffff0f0fffff0f0fffff0f0fffff000033333333333333333333333333333333333303033333030333330303333300000000000000000000ffffffffffffffff0000000000000000ffffff00ffffff00ffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaa00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a
|0,3=>0xafafafafafafafafafafafafaaaaaaaa000000000000000000000000ffffffff000000000000000000000000ffffff00000000000000000000000000ffffffff000000000000000000000000ffffaaaaffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff0000000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffeeeeeeeeeeeeeeeeffffffffcccccccceeeeeeeecccccccc00000000000000000000000000000000ff0fff0fff0fff0fff0fff0fff00ff000000000000000000000000000000000000000000ffffffff00000000aaaaaaaaff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff00ff0000000000ff0fff0f00000000ff0fff0f00000000ff0fff0f00000000ff00ff00ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaffffffff00000000aaaaaaaa00000000fffffffffffffffffafafafafafafafafffffffff0f0f0f0fafafafaf0f0f0f0ffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00
|0,4=>0x55555555000000005555555500000000555555550000000055550000ffffffffffffffffffffffff00000000ffffff00ffffff00ffffff000000000000000000ffffffff00000000ffffffff000000000000ffff000000000000aaaaffffffffffffffffffaaffaaffaaffaaffffffffff00ff00ffaaffaaff00ff00000000000000000000000000000000000000ffff0000ffff0000aaaa0000aaaaffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000aaaa00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffffffffff00ff00ffffffffff00ff00ffffffffff00ff000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff00003333333333333333333333333333333333333333333333333333000033330000ffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffaaaaffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffffffffff00000000ffffaaaaffffaaaaffffaaaa00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0000000000afafafaf00000000afafafaf00000000afafafaf00000000aaaaaaaa
|0,5=>0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff000000000000000000000000000000000000ffffffffffffaaaaffffffffffffaaaa00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000000000000000000000000000ffffffffffffffffffffff00ffffff00ffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffff003333333333333333333333333333333333333333333333333333330033333300ffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00ffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffaaaa00000000ffffffff00000000ffffffff00000000ffffaaaa00000000ffffaaaa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000ffffffffffffffffffffffffffffffffffffff00ffffff00ffffff0000000000ffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00aa00aa0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000a000a0000000000000000555555555555555500000000000000005555555500000000ffffffffffffffff5555555555555555ffffffffffffffff55555555000000000f0f0f0f0f0f0f0f05050505050505050f0f0f0f0f0f0f0f0505050500000000
|0,6=>0x5555555555555555555555555555555555555555555555550000000000000000aaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaffffffffaaaaaaaa00000000000000000000000000000000ffffffffffffffffffffffffffff0000aaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffaaaa00000000ffffffff00000000aaaaaaaa00000000ffffffff00000000aaaaaaaaffffffffffffffffffffffffffffffff00000000ffffffff00000000aaaaaaaa5555555555555555555555555555555555555555000000005555555500000000000000000000000000000000000000000000000000000000ffffffffff00ff000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000ff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffff00000000000000000000000000000000000000ffff0000ffff0000ffff00000000ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff000000000000000000000000ffffffffffffffff0000000000000000ffffffffffff0000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffaaaaffffffffffffaaaa
|0,7=>0xffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff000000000f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f00000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000000005555555555555555555555555555555555555555555500005555555555550000ffffffff00000000ffffffff00000000ffffffff0000ffffffffffff0000aaaa00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00ff00ff00ff00aa5555555555555555555555555555555555555555555555555555000055550000ffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffff00555555555555555555555555555555555555555555555500555555555555550055555555555555555555555500000000555555555555555555555555000000003333333333333333333333333333333333333333333333333333222233332222000000000000000000000000000000000000ffff0000ff000000ffff0000ff00ffffffffffffffffffffffffffffffff0000ffff0000ff000000ffff0000ff000000000000000000ffffffffff00ff000000000000000000ffffffffff00ff00ffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaffffaaaa00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffaaaa
|0,8=>0xffffffffffffffffaaaaaaaaaaaaaaaa0000000000000000ffffffffffffffff0000000000000000ffffffffaaaaaaaa0000000000000000000000000000000000ff00ff00ff00ff00ff00ff00000000ffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00000000000000000000000000000000000000005555555555555555555555550000000000000000ffffffff00000000ffffffff00000000ffffffff000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ffffffffffffffffffffffffffffffff0000000000000000ffffffffff00ff000000000000000000ffffffffffffffff0000000000000000ffffffff0000000000aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aa00ff00ff00aa00aa00000000ffffffff00000000ffffffff00000000ffffff0000000000ffffff0000000000000000000000000000000000ffffffffffffffffffffaaaaffffaaaa00000000000000000000000000000000ffffffffffffff00ffffffffffffff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffff0000ff000000ffffffffffffffffffffaaaaffffaaaaffffffffffff0000ffffaaaaffff000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000
|0,9=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000000000000000000000ff00ff00ff00ff000000000000000000ff00ff00000000ffffffffffffffffffffffffffffffff55555555555555555555555500000000ffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff000000000000000055555555000000005555555500000000555555550000000000000000ff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ff00ff00aaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffaaaaaaaaffffffffffffffff0000000000000000ffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffff00ff0000000000000000000000000000000000ffffffffff00ff00ffffffffff00ff000000000000000000ffffffffffffffff0000000000000000ffffffffff00ff00ffffffff55555555ffffffff55555555ffffffff55555555ffffffff0000000000000000000000000000000000000000ffffffffffffffffffffffff0000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff0000
|0,10=>0xff00ff0000000000ff00ff0000000000ff00ff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x21050b030a201f00060f0b0317181e00060f04030a1d1b0007050b0403021500060f030a18160d00060f0b030a1c1b00060f030a0e190d00060f03170a1816000504030201150013060f040317021600050403021615001306140f0b030a0e0d06120f0b03110e0d06100f0b030a0e0d0c050b030a0908000706050403020100
|1=>0x50b030a0e150013060f0b03170218000706050403021600050b030218150013070504030a01150007050b030a0e1500060f0b0a250e0d0006240f0b030a0e0d070504030a16150006230f0b0403110d0f0b040317021500060f030a0e160d000706050b030218000c050b030a201f000605030a1816001307050b030a181500
|2=>0x30a0d2206050403020100132e0c06050b030a0e002d06050b03181e00130706050403170a1600292721050b04031711060504032c111600130c0605030a1816001327060f0b040a2a0d22060f0b030a0e0d000729050b04030a1500220605030a181600130721050b04030a1500060f0b04031702000c0605030a0e19001327
|3=>0xd00220605030a18010013270f0b0403170a15060f040317110a1600270605030a0e190013070c050b04030a150022060504030a1600130c050b030a0e3400132207050b04030a150006230f0b04030a0d00060f0b03170a180006050b31030a0d3321050b03111800132106050b031128180027050b31030a130c06240f0b04
|4=>0x3e0d270f0b0403170a150d060f0b04030a3d0d27050b030a0e340013060504031102160013270f0b04030a150d270f0b04030a3b0d3a210539030a0e0006050b04380a0d06050b031702180013060f0b03170a180d00060f0b030a180d002906050b03181e0013270605030a181600130c0605370b030a0e0007060504030a16
|5=>0xa0e1600130c050b030a41080013072906050b030a1800072106050b030a1800220706050b04030200060503110a1816001321050b030a0e40001306050b030a18200d0006050b033f0a0e0d002206050b03181e00130706050b030a0e0d002d0f0b0403170a1500330f0b040317111500072906050b04030200060f0b04030a
|6=>0x130c06120f0b0403110d2d2921050b04031700070c06050b030a1800220605030a0e1600130c050b030a0e400013220706050b030a1800060f0403170a1600060f440b030a0e0d33210504031116001321060504031128160006430f0b0403111306050b030a180013290c06050b03110e132d050b04030215001321060503
|7=>0xf0b030a0e0d0027060f0b04030a4513330f0b0403171500060504031702160013060f0b03170a0e00060f0403170a160d00060f04030a160d0027050b030a410800130c0f0b0403170a150029050b04030215001321050b030a181f0013220f0b0403170a15000c0605030a0e1600130c06140f0b04030a0d2d050b030a1815
|8=>0x30a0e010013330c21050b03280e0027050b0403283221054404030a4833060f0b042846000c050b030a181f00130c0f0b04030a150d000c060f0b03110a0e0d06050b0311181e001329050b030a1815001327050b030a0e40001321050b030a1815001322050b040302150013220f0b04030a150d000605030a0e1900130612
|9=>0x30a15002d06050b03021800130c050b030a181500130729060504030a16000605030a0e190d00130721060504030a160022050b030a181500130c060f0b030a410d00330f0b040317150d00060f0b040311020d33050b0403320d060503170a18160013060f0b04031128490605030a18160013270605030a0e1600130c0605
|10=>0x30a160033054c0403001306054c040328002207060504030a1600330c21050b03110e130605030a180100132e06050b030a0e0d000c2106050b0311280e27050b030a181f001342060f0b030a0e0d000605030a18160d001322060f0b04031702004a060f0b04030a1b0007050b0403170a1500060504030a16001307050b04
|11=>0xf0b030a0e0d0006050b0317181e0013064e0f0b04030a0d220706050b030a0e000605370b030a0e0d00060f0b04030a1b4d0027050b030a181500132906050b03021800132106050b030a18200007050b04030a150d0022060f0b03170a18002106050b033f0a0e002d0504030a16150013072106050b030a0e00070c060504
|12=>0x2000706050b0403020006050b03110a515013060f0b0403284f000c06050b030a1820000c060f0b030a180d000c06050b033f0a0e00290504030a161500132206050b030218001322060f0b030a180d00210504030a161500132207060504030a01000605031a0a0e190013050b04031102150013070c06050b030a0e000626
|13=>0x30a18001321050b0403112815000605030a0e1600130706050b03170a1800060f0b04031711020006550f0b04030a0d002d060504030216001321050b030a0e1500130c0504030a16150013220504030a1615001306300f0b030a0e0d003a0c210539030a0e00060f0b031a0a0e0d000605030a54015300130706050b040317
|14=>0x6050403021600130c060f440b030a0e0d0706050b030a180d00220504030a0115001322060f0403170a160027060f0b04030a3e0d060f0b0317110a18000c050b030a0e15001327060f0b04030a3d0d27060f0b030a560d0c050b030a0e3b00132d0605030a1816001322050b030a0e1500132d2921050b0403110d2206050b
|15=>0x50b03110218001327210504030a010d0605030a015300130605030a0e010013210605030a0e1900133321050b03280e00060f350b030a0e0d00050b04031702150013270f0b040317110a15050b04030215001306430f0b04030a0d060f0b03110a0e0d0605030a0e160d00130c060f3c0b030a0e00270504030a1615001329
|16=>0xa5a001306050b04030a320d060f0b04030a3d00135906050b030a0e001327050b030a0e3b00130c060f0b03170a0e00060f0b04030a580d000c06050b030a4109000c060f04030a160d00060f0b030a410d00290605030a18160013060f0b040311570d210605030a1816001322060504030216001322060f04030a160d0006
|17=>0xb040311130c0605440b030a0e132d060f0b0403110a0d21060504030a16001306050b040317110200132d06050b030a0e001306050b0403110200133321050b04030200132106050b0403280200592721050b04030a0d060f0b0403170a150d00060f0b04030a150d00060f0b04030a3b0d00060f0b04030a3e0013060f0b04
|18=>0xa1800130c21050b04030a1500130c2106050b03110a0e132229050b04030a1500132221050b04030a1500130605350b030a0e00133a060f4404030a0d0c060f0b030a0e0d0021050b0403170a15000c06300f0b04030a0d0006050b030a0e5d00132d2721050b04030a0d065c0f0b04030a0029060504030a160013290c0605
|19=>0x110a151321050b04030a150d000c06053c0b030a0e001321050b04030a3b0d002906050b030a0e00130c060504030a1600130c0605440b030a0e0d1306050b030a4100132206050403170a1600132d27050b04030a1500132f21053904030a0006050b0317110a18001322060504030a16001306054c04030a001306050b0311
|20=>0x403110a0d060f0b04030a450013220c050b04030a150013060f0b040a2a00133a060f3c04030a0d000605350b030a0e0d0013290605040311010013270605440b030a0e13060f0b04030a1b0027050b040317110a1513292721050b04030a0d06050b03110a0e0d135e060f0b04030a0021050b0403170a150d0027050b0403
|21=>0x31102130c06050b03170a0e00130c060f0b0403110a0d3a21053c04030a003a0c21050b030a0e00130c060504030a160d00132d27060f0b0403280006050b030a410d00133a21054404030a0d3a060f0b040a4600132206050b030a0e00136121050b04030a001322060504030a160d0013222d06050b04030200132d21050b
|22=>0x6050b04032800072706050b04030a0d2d060f0b04030a0d33060f0b0403110d06050b04031702001327060f0b040317110a222d06050b030a1800132d050b0403110a15001327060504030a16001327060f0b040311280c060504030a010013060f0b04030a4f0013330c21050b0403280022060504030a0100130c06050b04
|23=>0x5390b030a0e003a21053c04030a0d00060f0b04030a630062060f0b04030a0d0c27050b04030a1500130c2706050b03110a0e130c27050b04030a3b0013420c06050b030a0e001333050b040332001306050b04032832002206050b030a0e0d00132227050b04030a15001321050b04030a0048222906050b04030200132d07
|24=>0x68060f0b04030a0d00222106050b030a180013060f0b04030a670013060f0b04030a660d060f650b04030a00132706050b04031102132d060f0b040311280006050b03170a18001321050b0403110a15001342060f0b04030a0d0006050b030a1800132f27060f0b04030a0d2e2721050b04030a0006050b030a020e00132106
|25=>0x50b04030a000605040317110a1600136227060f0b04030a13060f0b04030a570d0006050403110a1600130c2106050b030a180013220c060f0b04030a0d000c2706050b030a410013330c21050b04031113222906050b030a1800132e06050b04030a0d000c2106050b040311282d2721050b0403280006050b030a51500013
|26=>0x422706050b030a0e001322050b0403110a1500132d21050b04030a0d3321050b0403110d6d060f0b04030a000706050b0403110a0d2721050b040317110a060f0b04036c0a00132106050b031a0a0e0013060f0b04030a6a002d2706050b030a180013072906050b04030a002721050b0403112827050b0403170a1513072106
|27=>0x403170a150d1327050b04030a150d13220706050b0403170a0027050b04030a3b0d132f06050b030a0e00136e06050b0403110013220706050b04030a003306470f0b040328003321050b030a0e00132106050b03280a0e002d06050b040311020013220c06050b030a18001306050b03170a180d001306050b030a180d0013
|28=>0x504030a54010013064e0f0b04030a001327060f3c0b04030a0d27060f0b0403170a21050b04030a660d0c06050b031a0a0e00132d21050b040311280006470f0b040311282d050b0403170a15001333050b040317111500132f2721050b04030a0d2d050b04030a15001333050b040311150013070c06050b04030a0027050b
|29=>0x2d060f0b0403280021050b04030a150013222706050b030a180013070c06050b04030a0d0006240f0b04030a0d2721053c0b04030a220706050b04030a0d00060f0b030a0e0d0027060f0b04030a6f22060f0b040317110a003a0c21053904030a00222d060504030a1600132706120f0b04030a0d2d06050b03110a18001306
|30=>0xe0d1306050b0403110a5113292106050b0403110d5f330f0b040328005f270f0b04030a0d2d060f0b0403170a00060f0b04030a70001333060f0b0403171100590c06050b030a0e0013060f0b04030a6b0d292721050b040311133306470f0b0403111327060f0b0403170a0d29050b04030a1500130c2706050b030a180013
|31=>0x30a002721050b0403170a2d0c06050b030a0e00132229060504030a1600132221060504030a1600132106050b04030a6a0006054404030a48132106050b03110a18001306053c0b030a0e00132206050b04031102001306050403170a1600132706050b031a0a0e001306050b030a500013060504030a1600130605440b030a
|32=>0x4030200132721050b04030a6f2e2706050b04030a0d060f0b040a7500130c050b0403170a1500130c050b04030a1500130c06050b03110a0e130c050b04030a3b00132d27060504030a16001322050b0403170a15001322050b04030a150013060f0b04030a73000c21060504030a1600132721053c0b04030a0d7221053904
|33=>0x30a0027060f0b04030a3d001327060f0b030a56001306050b03170a0e001306050403170a160d00132f060f0b04030a0d3a21050b030a0e0013060504030a160d0013060f0b04030a5d0d000c060f3c0b04030a002206050b03110a1800132d2921050b04031100130c060f440b04030a0d0c0605350b030a0e00132d06050b
|34=>0x150d0013290c06050b030a0e00132d21050b0403170a003321050b0403171100060f0b0403770013060f0b04030a760d0c06050b030a4100132721050b0403170a0d2d21050b0403280027060f0b04030a3e0013222106050b030a0e0013220c060504030a16001333050b0403171500130706050b04031128002d0721050b04
|35=>0x130c060f0b0403170a002906050b0403020013060f0b0403287900060f0b040317110a150022060f0b0403170a0006300f4404030a0d0c270605440b030a0e13223321050b04031100132d06050b030a1800130c050b04030a150d00130c06050b03110a0e0d1306430f0b04030a0013222106050b040311280022050b04030a
|36=>0x13220c06050b030a0e001333050b040317150d001321060504030a010d00270605350b030a0e0013060f0b0403287c007b060f0b04030a001306050b040311020d132d06050403110a16001327210504030a01001327050b04030a1500132706050b03110a0e1327050b04030a3b00134206050b030a0e0013060f04030a7a00
|37=>0x22060f0b0403170a0d002106050b030a1800130c27060504030a1600132206050b04030200132706300f0b04030a0d22060f0b04030a0d002706050b030a4100132f21050b04030a0d2f2721053904030a002227060504030a16001333060f0b040317000c06050b030a410d00130c06120f0b04030a0d00060f0b0403115700
|38=>0x7f7e0013272105443904030a060f0b0403286b0027060f0b040a2a001306140f0b04030a0d2106050403110a16001306120f0b0403110d06050b030a0e1e00132e0c06050b04030a0021050b04030a760d2b27060f0b04030a0d4206050b030a0e0d001306050b030a0e7d00132906050b030a1800132206050b040317020013
|39=>0xa7e0013060f0b0403280a49000c06050b030a18001306050b31030a001383060f0b04030a002206050b03170a180013060f820b04030a0013292106050b04031711002206050b030a180013222706050b030a0e00130c210605390b030a0e0006810b04030a001333060f0b0403170d0021050b040317110a150006050b030a
|40=>0xb04030a0022072906050b04030a0022072106050b04030a0006050b031a0a0e0013060f0b04030a850d003321050b040317002206050403110a1600132e0c06050b04030a0d00060f0b04030a020d000706050b0403170a002706120f0b04031113060f0b04280a460006840f0b04030a00420c060f0b04030a0d0006050b03
|41=>0xb0403170a0d0033060f0b040a4600130706050b04030a0d0006050b04380a00130c06050b030a180d00132d060504030a160013072721050b04030a002721050b04030a892206050b030a180d00138806050b04030a0d00060f0b0403170a15002206050b04030a0013060504030a8600132d27060f0b04030a0d070c210605
|42=>0xa0d001360060f0b04030a0013060f0b030a560013222d050b04030a150013060f0b0403110a49132f0c06050b030a0e001322070c06050b04030a00330c21050b030a0e00132706050b030a18001306050b031a0a0e0d00133321050b0403170d0027050b04030a32132d0706050b04030a0d0c2106050b03280a0e00070605
|43=>0x5f060f0b0403280a007221050b04030a0013072706050b04030a00132706050b04030a891306050b04030a0200132d060f0b04030a001333060f0b04031100138c06050b04030a00130c2706050b0403110a13420c06050b04030a00132206050b0403170a0d001306050b04030a8b001306050b0403110a8a132206050b0403
|44=>0x30a660013420c06050b04030a0d0013222d06050b0403110a00132f27060f0b04030a0013060f0b04030a900013060f440b04030a0d06050b0403110a5200133306050b0403170d00133306050b04038f001362060f0b04030a00138e06050b04030a001306050b0403286b00135f330f0b04030a001306050b04030a8d0013
|45=>0x220c2706050b04030a001306050b0403170a15001321060504030a01001327060f440b04030a1306050b04030a15001306050b04030a3b00132d2706050b04030a0d133a06470f0b04030a0013422706050b04030a00132106050b030a0e001306050b04030a36001306050b04030a020d00139106050b0403110a13060f0b04
|46=>0x60f0b04030a006f2f06053904030a001306120f0b04030a0d00222106050b0403110a00139206050b04030a0013060f3c0b04030a0d002106050b040317110a00060f0b0403170a002d21050b04030a00133321050b04031100130706050b0403110a00132106050b040311280029060504030a01001306050b04030a510013
|47=>0xa520013272105440b04030a132706120f0b04030a00132d06050b0403110a0d13060f0b0403170a0d009306050b04030a001321050b04030a660013060f0b04030a7c001306050b0403170a150d001306050b04030a150d001306050b04030a3b0d00132f2721050b04030a0013060f0b04030a7900130c06050b030a0e0013
|48=>0x132d0c06050b04030a0013060f0b04030a6b00135906054404030a00132706050b030a0e0013222d06050b04030a00132106053c0b04030a003a06053c04030a0013060f0b04030a85001306240f0b04030a0013210605440b04030a0d3a06054404030a0d130c06050b030a0e0d0013590c06050b04030a001306050b0403
|49=>0x2106053c0b04030a0d003a06053c04030a0d00132106050b0403170a000706050b04030a001306050b04030a0048130c06050b0403110a1306050b04030a7f00135f060f0b04030a0d000c06050b04030a5d00139506050b04030a00139406054404030a00138806050b04030a0013292106050b04031100135f270f0b04030a
|50=>0x31128130c270605440b04030a130c06050b0403110a0d130605440b04030a8a135f06470b04030a00136e06050b04030a00132d2706050b04032800132f060f0b04030a0013290c06050b04030a00132106050b04030a006f06710f0b04030a0013222906050b04030a00132e2706050b04030a0013222106050b04030a0013
|51=>0x1306300f4404030a0013220c06050b04030a001306470f0b040a4600132d06050b04030a0d133306050b0403110d136806050b04030a0013065b0f0b04030a00132706050b040317110a132106050b0403170a0d004206050b04030a0013060f0b04030a7600139606050b04030a00132706050b04030a5d00132706050b04
|52=>0x136806050b04030a0d001306050b04030a660d132d06050b0403112800134206050b04030a0d001333060f0b040328002f2706050b04030a0d1327060f0b04030a0d910605440b04030a1306050b0403990a00139806050b04030a00132106050b04030a0200135f06120b04030a001306300f0b04030a0d009706050b04030a
|53=>0x4030a00132106050b04030a36001306120f0b0403110013222706050b04030a00130c06050b04030a02001306050b04030a6a00130c210605390b04030a00060f0b040a46001321050b04030a7600132b27060f0b04030a0013060f0b04030a490013220c06050b04030a0d00132706300f0b04030a00132f21050b04030a00
|54=>0xa130c2106050b030a0e001306050b04030a009b13060504030a0100133321050b040328002721050b04030a0d060f0b04030a740013060f0b0403110a0d06050b030a0e001333060f0b04030a0d00210605443904030a00272105390b04030a0027060f0b0403280a002706053c0b04030a1306140f0b04030a001306059a0b
|55=>0x1327060f0b0403110a132f0c06050b04030a00132706050b04030a6f132206050b040317110a0013330c21050b04030a00132206050b0403110a00130c2106050b0403280a002706050b04030a0200132d27060f0b04030a0013420c2706050b04030a00132706053c0b04030a0d137206053904030a00132706050b040317
|56=>0x1306050b04030a32001306050b04030a6b0d132706050b0403170a0d133321050b04030a0d002d06050b04032800132706050b04038f0a13060f0b04030a5700132d0706050b04030a001306050b04030a9d001306050b04030a9c00132721050b0403280a002e06050b04030a00132106050b04030a008906050b030a0e0d
|57=>0xb0403280a000c2106050b0403110a132d2721050b04030a00132d060f0b0403110a0013592106050b04030a0d000c060f0b04030a0d006106050b04030a00135f06300b04030a001306050b04030a5d0013592721050b04030a0013060f0b04030a4b00130c0605440b04030a132d06050b0403170a00133306050b04031711
|58=>0xa001306050b04030a760d130c2706050b030a0e00132f06050b04030a0d1306050b04030a5d0d00132106050b0403110a0d0c06053c0b04030a00132f2706053904030a00132906050b04031100130c0605440b04030a0d132721050b0403110a133a060f0b04030a0d003a060f4404030a001306050b04030a9e001306470f
|59=>0x60f0b04031128003a21053904030a0006050b040317110a150013292106050b04030a0d002206050b0403170a001306050b0403110a1500132206050b04030a0013292721050b04030a0013060f0b04030a9f0013270605443904030a132b060f0b04030a00133306470f0b04030a0013060f0b04030a64001372060f0b0403
|60=>0xa00130c06050b04030a0d00133306050b040317001306050b04030a00a0133a21050b04030a0d00222d2706050b04030a00133a21054404030a001378060f0b04030a0013220c2106050b04030a0013060f0b040317110a000c06050b0403170a00132d21050b0403110a001306470f0b0403110a133a0c21050b04030a0013
|61=>0x1306050b04030a76001306050b040317110a00132f06050b04030a001306050b0403112800133321050b04030a00132106050b0403280a0006050b04030a8000130687050b04030a00133a06050b04030a0d0013210605440b04030a001306050b04030a6b0013210605390b04030a0033060f0b04030a00133a0605390403
|62=>0x60f0b0403110a001306050b04030a006f130c2106050b04030a001306053c0b04030a0d001306050b0403170a00133a21050b04030a0013292106050b04030a0013593a06050b04030a001306053c0b04030a001327060f0b04030a00130605440b04030a0d133a060f0b04030a0013060f0b04030a0d00592106050b04030a
|63=>0xb0403110a00130605443904030a00130c2706050b04030a001306050b04030a008a1306120f0b04030a00133a06054404030a00132d06050b0403110a001306470f0b04030a001306050b0403170a0d001306050b04038f0a00132706050b0403110a132106050b04030a0d002721050b04030a00132d2706050b04030a0013
|64=>0x403280a001306050b04030a6900132f3a06050b04030a00132d06050b04030a00133306050b04031100133306050b04032800132706050b04030a0d139406050b04030a00135f060f0b04030a001306050b04030a0089135906050b04030a0013270605390b04030a00139106050b04030a00137206050b04030a0013210605
|65=>0x403110a001306050b0403280a00132706050b04030a00130605390b04030a00130c06050b04030a0013060f0b0403280a0006300f0b04030a0013270605440b04030a1306050b0403110a0d132906050b04030a0013060f440b04030a00133306050b04030a0d001306050b04030a6600132f2706050b04030a00132706050b
|66=>0x6050b04030a00133a06050b04030a00132106050b04030a00133306050b04030a0013060f0b04030a00130605440b04030a001306050b04030a0d001306050b
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xf0803a200e08036200d08032200c0802e200b0802a200a0802620090802220080801e20070801a20060801620050801220040800e20030800a200208006200108002200008
|8,0=>0xc7a031680c36430490bee42f290ba642e090b5e42ce90b1642bc90ace42aa90a86429890a3e4286909fa0275909b602649096e42538092e0243808f1c233908aa42228086642109081e41fe907d641ed8079241db9074a41c99070241b7906ba41a68067dc196906364186705f64174905ae41629056641509051e413e904da012d90492411b9044a410a8040640f89
|8,1=>0x152e4542914e645309149e451e91456450c9141204fc813ce44ea9138644d89133e44c6912f644b4912b204a5712724494812320483911ea4471911a9c4637116e0452911264440910de442e91096441c9104e440a9100a03f990fc243e880f7e43d780f3a43c680ef643b490eae43a290e66439090e1e437e90dd6436c90d8e435a90d46434890d02033880cbe43269
|8,2=>0x1e06477891dbe476691d76475491d2e474291ce6473091ca2071f91c5a470d91c1246fb91bca46ea81b8646d891b3e46c691af646b491aae46a291a66469091a1e467e919da066d91996065c9194e464a919064638918be46269187646149182e4602917e645f0917a205df9175a45cd9171245bb916ca45a99168245979163a4585915f24575715b9c5659157245548
|8,3=>0x859921424847920fa4835920b608249207208139202a480191fe247f081fa207e081f5e47cf81f1a47bd91ed247ac81e92079c81e4e478a9
|9,0=>0x2a864a9892a3a8a84a29ee4a72929a28a608295e4a4da29124a3b928ce0a29a28824a179283e0a05a27f249f3927a689e09275e49ce9271289bc826ca89a8a26820996a26364985825f24972a25a2895ea2552894b9250e093a924c64927a247a4915924360904923ee48f2923a648e09235a88cd9231248bb922ca48a99227e8896922364884921f20874821ae48629
|9,1=>0x339e4cde933564ccba33068cb7a32ba4ca4a326e4c92932264c80931de4c6da31924c5c8314e4c4a931064c38930ba8c25930760c149302e4c0292fe64bf092fa20be082f5a8bcca2f0a8bb8a2ec20ba882e7a8b94a2e320b82a2de64b7092da20b6082d5e4b4e92d128b3aa2cc64b2982c824b1792c3a4b0592bf24af2a2ba64ae182b5e8acda2b124abb92ace0aaa9
|9,2=>0x3cba0f2593c724f1393c2a4f00a3be20eef93b968edba3b4e0ecb83b068eb983ac60ea7a3a7a4e94a3a2e4e81a39e24e6f9399a4e5e8395a0e4ca390e4e3b838c68e27a387a4e15938324e03937e68df09379a8ddd937524dcb9370a4db9936c24da7936768d93a36268d80935da8d6ca35920d5c835520d4b9350a4d39934be8d27834768d14934320d03933ea4cf0a
|9,3=>0x45ca9169945825158845421147944fa5136844b29122a4462910f9441a50fd943ce90ea9438650d7a433e10c6942f650b4942ae50a1a425e908e94212907b941ce106a9418a1058a413e5046940f65033a40a6902094062100ea40164ffd83fd60feba3f868fd7a3f3a4fc683ef28fb393ea68fa093e5a8f8e83e1a0f7d93dd24f6b93d8e0f5b83d4a4f4993d024f36a
|9,4=>0x4ef693b494eaa93a0a4e62138f94e16937c94dd2136c84d8e535b84d46934984d02533794cbe132694c72931394c2a5300a4bda92ed94b8e92da94b4652c894afe52b784aba52a4a4a721292a4a22927f949d6926ba498a5258a49421247948fa5234a48ae52229486652109481e51ff847da51ed9479611dba474a51ca8470291b6a46b651a3a466691909461a917ca
|9,5=>0x156b8558695589553a9544a54ea95319549e951e9545a150d9540e94f9a53c254e79537e14d5a533254c3952ee14b1a52a2549f9525a548e85216547ba51c69467a517a5455951361443a50e694309509e541e9505a140e8501293fc84fce53ea94f8a13da84f4293c79
|10,0=>0x5f1257bb95ec2d7a6a5e729792a5e26578095de2176f95d9a575bb5d4a574995cfe973785cba572595c6e971295c26570095bd6d6eba5b8a56d995b4256c795af696b3a5aa696a095a5e568da5a12567b959c2d665b596e96529592a1640a58da962d95892561b9584a56099580255f7957ba55e4a576e55d29572655c0956de55ada568e9598b563e5586955f295739
|10,1=>0x68669a109681e59fe967d659eba678a59d99674259c7966fa59b4a66aa99a196662598f96616997c965ca9968a657e5956965365943a64ea5930a649e591e96452990aa640298f6a63b298e39636a58d19632258bf962da58aca628e589a962465887a61fa5874a61ae586296166584fa611a583d960d2582b9608a58199603e9805a5ff257f395fa697dfa5f5a57cd9
|10,2=>0x71b25c62a71665c509711e5c3e970d29c2b9708a5c19970425c0796ffa5bf596fae9be296f5edbcda6f0e9bb9a6ebe9ba5a6e6adb90a6e1e5b7e96dd29b6b96d8e1b5b86d4e1b4a96d0a1b3a86cc65b2896c7e5b1696c365b0496bee5af1a6ba25adea6b529acb96b069ab986ac25aa6a6a765a92b6a229a7f969d69a6c9698a9a58a69421a46a68fa1a35968b25a239
|10,3=>0x79aa5e61979625e4db79125e3b978c2de27978769e13a782a5e00a77e21df087796dddba77469dc7a76fa5db4a76ae5da2976665d8fa761a5d7d975d25d6aa75865d57a753a5d44a74ea9d319749e9d1e974565d0c9740e5cfa973c29ce6a73729cd2a73265cc0972de5cae972929c9b9724a5c88a71fa9c759
|11,0=>0x82f260b3982aa60a19825ea08e98212a07aa81c66067a817a6055981326043980ea6031980a2601f98056a00c9800e5ff9a7fc25fe6a7f765fd497f2e5fc1a7ee25faea7e965f9c97e4e5f8a97e029f7797dba5f64a7d6a9f5197d225f3ea7cd29f2b97c8a5f1997c425f0887bfa9ef597bae9ee297b665ed097b1e5ebe97ad65eaba7a869e9897a3e5e86979f65e73a
|11,1=>0x20d69833a20c59
|12,0=>0x84be6126984766115884326103983ea60f1983a260df9
|13,0=>0x21388
|_,_=>0
def wAt:=mkWire dB 161 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 18
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa004882f0c0a49c4d06004004d2b03c9c3d06004144d051343013060d4004d2213c881b2900418a10a1348813220bc9ca106004284d2213c302921004302b051342835060d4004d0b1a828390c04c9c4d06004881b0c0a430132713418012603c3c390c04c30480a0043c2900134144d1813c88130c0a484010b1a8144d0a0e418350013430130a0043c29060d4144d
|1=>0x2206cb44f2d13418450a00430480f0a4183500134144d2204c185d0a0d4004d0513410c921110280106134004d2204c84450613428012204c84450613428010432484440a004184d06004183500134c0030f0b4144d290bc882b2900418a10a13430132f13c9c2d2713418010a188b44d0611428012213c882f06174444d0a0041801111342801210a4184d2d1341845
|2=>0x1113428012204c144d06174004d051348813330d4004d060a428622900418a10a134882f2204c9ca10a134d44f0b0e430132713418012213c882f330d4004d060a4881329004a42f06284284d06178444d06004144d0a004144d220bc185d1113428010b1a828390c04c9c4d06004881b2213c3029271341801220bc84d921118184d0a00418d60b0e43013271341801
|3=>0x60d4004d06114144d06178444d0a004144d06178444d0a004884f220aca40106284284d001349cc20f0b4180105134144d06004185e0a0d4004d27128004d0f0a418010513418d60b0e43013271341801220ac882f2d13418450a004144d06004185e0a0d4004d063c8144d060042c35001343013060b42c4d21004184d001340cc921110184d0a0048813220ac185d
|4=>0xa00488132136484460613428010c04c842921004184d220ac881b061142801220bc30130c0a484010641908130c0b49c4d0600488132213ca40106284284d2204c884f0c0a4840106134882b2d13cb44d061142801220bc88132d1341845061a828390c04c840106134604f2204ccc350013418291a13c28390c04c18350013428622728418010a134884f0c04c3029
|5=>0x2713418011200c3c29060d4004d0513488132206cb44d0611428010a0043c29060d4004d051341845111342801210a4184d2204c884f0c0a49c4d06004882f0c04c3029271341801061a828390c04c9c4d0600488132d13cb44d06114280105134882f06174444d0a004144d0b0043013060d4004d220bc8445061342801220bc8445061342801271203c2906004144d
|6=>0xc04c9c4d0600430130f0a4183500134144d3d0049c4a0f0a4180105134185e28004284d051341829220ac882f06174444d0a0043013051342835060d4004d220bc144d06174004d05134882f330d4004d060a419064204c302d27134180106178144d0a0d4183500134882b2206ca40106284284d0618888130c0a4840106134185506178283500134144d220bc3029
|7=>0x613418290a13484440a004184d06004184d0b004e83400134182d060a4284d4703c3c010513418622204c302927134180105134881b0c0a41835001343013051342801060d4004d0a18888132d13418450a00488132206ca40106284284d061a828390c04c9c4d0600488132206c302921004184d06178882b06174444d0a004185e05134185d0a0d4004d0b1a82839
|8=>0x2206c30292713418012213c882f2900418a10a1342c6a0a0e43013060d4004d220bc884f0c0a484010613488132206c9ca106004284d0513508130c0b4183500134144d06178283500134302b051342801060d4004d060a484440a004184d0013428010a134191e0f004144d2204c882f2728418010a134882f0c0a4301327134a42f210a4840106134301321004284d
|9=>0x613428012d13c882f2d13418450a00430130a004840106134a42f2204ca40106284284d0c04d084f0c0b418350013430130a00484010613418622204c9ca106004284d0c04c183500134144d2204c882f330d4182905134882b06174444d0a004186d4b1343c46051342801220bc84d921118184d0a004881b2d13cb44d061142801220ac88132d13418450a0048813
|10=>0x6004144d2213c30130c0a49c4d06004d44f0b0e43013060d4004d4b1343c460513428012206c88132728418010a1348813220aca40106284284d1813c88130c0a4840106134144d2204c185d1113428011a13c28390c04c840106134881b220bcb44d0611428012213c30130c0a4840106134884f220bc3029271341801060a42cc921110184d0a004284d0b3248444
|11=>0x513418291813c88130c0a49c4d06004144d2204c3029060d4004d1a13c28390c04c9c4d06004882f2206ca40106284284d2204c882b2728418010a134144d2204ccc35001341829220bc881b0c0a4840106134a42f2213ca40106284284d0b1a828390c04c9c4d06004884f0c04c30292713418010f0e4144d0c04c183500134286206174444d0a0049cc0001343c2d
|12=>0x6174444d0a00430c00f0b4183500134144d220ac882f2d13418450a00430132206c302921004184d2206c882f0c0a49c4d06004185e220bc185d1113428010c04c3c2d060d4004d051343013060b42c4d21004184d0513428390c04c183500134115201004a42f06284284d2213c882b111342801220acb44f2d13418450451948012111c184d0a004284d334783c01
|13=>0x2204ccc35001341829290bc881b2900418a10a134144d220bc185d1113428012204c144d06174444d0a0043013060d4185e0a0d4004d00134ac13270f418010513418f20c04c18350b0d4004d2206c30130c0a49c4d0600418450a004842906134004d2204c84d921118184d0a004881b2111428010c04c882f0c0a49c4d06004884f2204c185d111342801220ac144d
|14=>0x290bc84290c04c8401061342c6a0a0e4301321004184d0c04c84010a134184d060a4144d0b0e43013060d4004d05134185e1113428010c0ac1835061782835001349c48001343c2906004144d0c04c144d0a004183500134882f0c04c3029060d4144d0c04c18350b0d4004d220bc881b2728418010a134882b220bca40106284284d0b0043013060d4004d05134884f
|15=>0x4206c302d0c04c9c4d060043013051342835060d4004d4113d08130c0b49c4d06004144d220bc3029060d4004d4204ce83505134004d060b48813220bca40106284284d061283c290a004004d05134882f2204c302921004882b220bc9ca106004284d05134882f330d4004d060a4882b2204cb44d061142801001341801290bc842906134115201004a42f06284284d
|16=>0x6114280100134144d220bc302921004184d220ac185d1113428010c04c9c29271341801220acb44d0611428010c0ac84010613418290c0ac284d21004184d06004004d210b4184d05134185e0a0d4004d05134185e0a0d4004d0513418f20b0d4004d273083c2d06004144d5b03c3d11051342c0121110280106134004d271283c2906004144d210b4301321004184d
|17=>0x2204cb44d0611428012206c302921004184d0c04c280121004184d2206ca40106284284d2206c302921004184d0b0e430132713418010b004144d00134182d0c04c183500134144d06178283506134004d0f0b4183500134144d0c0bc3013271341801001349c290613418015b13c3d11051342c01220bca40106284284d0a004842921004184d0c04c1835001342c01
|18=>0x6013d7c29060f4144d06178283506134004d06004185e11134280106178283506134004d0c04c18350b0d4004d0613418f20b0d4004d210a4301321004184d220bc30292713418010c04c1835001342c014204d6401063942c4d220bc185d1113428012206cb44d270a418010b134e80106134182d2204c185d111342801220bc9ca106004284d0b3248444061342801
|19=>0xc04c3029271341801063648446061342801220bccc35001341829220acb44d06114280106114280106134004d57004184a0f0a4144d2206c30292713418012b03d7c01060f4144d0b0d4144d00134182d0b0e43013060d4004d290bccc4d060a428010c04c2c012713418014b1343c4605134280106178180111134280106004842906134004d0c04c2801060d4004d
|20=>0x220bc9ca106004284d0a1341801051342801290bc842921004184d334783c0105134182921004284d06134182929004a42f06284284d0c0ac18350013428010c04c2835060d4004d051342801060d4004d441342c0106134182d0c04c840106134182d220bc3029060d4004d051349c2906004284d4204ce83500134182d001342c0106134182d060b51c0f0f004144d
|21=>0x4206c302d2713418010c0b430132713418012111028010613418290a13484440613428010c04c3029060d4004d2206c9ca106004284d06134e83400134182d220aca40106284284d2d13c9c2906004284d2d13c9c2900134180106114280100134144d060a4280100134144d0c0ac2835060d4004d1113418010513428012204cb44d0611428012206cb44d061142801
|22=>0xb494191e0f004144d0c0ac280127134180105134284d0611428012204c185d1113428012206c84450613428013a0d4144d00134182d2204c9ca106004284d051349c2d0013418012f13c9c2d0613418010c0ac30132713418010b134301321004184d061342c3500134182d641349c3f06004144d5f00c004d060f4144d2206c30292713418010c04c2801271341801
|23=>0x2b00c9c3d06004144d061283c2900134144d220bcb44d0611428012204c302921004184d051343029060d4004d4204c302d2713418012100428010613418292204ca40106284284d4213ce83500134182d0a134280121004184d0a1349c2906134180104519a401210ac184d05134e83700134182d2204c302921004184d3a478182d0f004144d00134144d270bc1801
|24=>0xc0b430132713418012206cb44d06114280100134cc010613418290013428010613418292b13d7c01060f4144d00134b44f0611428010613418011113428010a494191e0f004144d0a0e4301321004184d05135ac4d0611828012204cb44d270a418012213ca40106284284d0a134280106134180106178a00106004284d2213c302921004184d220bc185d111342801
|25=>0x6178444d060a428012213c302927134180106004185e0a0d4004d06004185e0a0d4004d2213c185d111342801063c818010b0d4004d0c04c9c2d2713418010a52484470613428012d13cb44d0611428010f004284d051341829060a4301321004184d0a134301321004184d220acb44d0611428012204c30292713418012204c185d0a0d4004d2204ccc35001341829
|26=>0x60b42c4d21004184d220bcb44d061142801001343c2906004144d2204cb44d06114280101004a42f06284284d273003c2d06004144d0513418010b0d4004d11134180105134280100134184d270bc18010a0e4301327134180106134284d0611428010a13428010f004144d06178444d06114280106178444d060a42801001349c2d0613418012206cb44d061142801
|27=>0x6118280100134144d060042801210a4184d060a428010f004144d0a0d4180100134144d2206ca40106284284d2204c3029271341801051349c2906004284d2206c302921004184d2204c9ca106004284d2213c3029060d4004d00134c0030f0b4144d441341801061342c012213ccc35001341829051343013060d4004d0513418010a0d8004d05134185d111342801
|28=>0x2204c84450613428010c04c18350b0d4004d220acb44d061142801220bc185d1113428010a0e4301327134180104519a401210ac184d220bc9ca106004284d0b0043013060d4004d5200484470613428010a004842906134004d060f4284d05134182906004004d060f4144d11134144d061142801067191c290f004144d05134444d060a428010c04c8401210b4184d
|29=>0x60d4185e0a0d4004d0c04c1835001342801063c818350b0d4004d220bcb44d270a4180106154185e1113428012206c9ca106004284d74134e83f060b4144d220bc302921004184d0613418010b0d4004d061342c4d3a00c182d06004283506134004d270a43013271341801220bca40106284284d220bc302921004184d3613484460613428010b004e83400134182d
|30=>0xc04c2835060d4004d220bc185d0a0d4004d051341911001342c01060b4301321004184d220bccc350013418290c0bc183500134144d0513418350b0d4004d2204cb44d061142801061142801210a4184d0b004183500134144d0b0e43013271341801220acb44d0611428010613418010a0d8004d2f13c9c2d0013418017103d1c290f004144d061782835060d4004d
|31=>0xc04c842921004184d06134444d061142801111342801061341829780ad7c2d060f4144d05134004d270ac18014204c302d27134180106004283506134004d33004284d061341829273083c2d06004144d0c04c302921004184d220bc302927134180106178444d060a428012d13c284d0611428012d13ccc01061341829271283c2906004144d2b04c9c3d06004144d
|32=>0xc0b43013271341801600bd7c29060f4144d051342835060d4004d0c0ac842921004184d470ac284d0f004144d05134185e11134280106174283500134144d001343c2d051342c010c04c2c012713418012111428010613418292204cb44d0611428012206c3029060d4004d0c04c2801060d4004d271203c2906004144d0a13484450613428012206ccc35001341829
|33=>0x28004284d0513418294204c302d060d4004d0f0a4183500134144d061283c290513428010c04c3029271341801061782835001341829290bc842906134004d0b0e430132713418010a1357c2b060f4144d064b43c460513428010c0ac2801060d4004d220bcb44d06114280106004a42f210a4184d2206c9ca106004284d0c04c28012713418014206c302d271341801
|34=>0x134184d270ac1801001349c3d06004144d0c04c302d060d4004d0b0e830132713418012204ca40106284284d220ac185d11134280105134185d0a0d4004d2204c302921004184d220bc3029271341801220ac9ca106004284d001343c2d06004144d05134cc350013418294204c302d27134180100134e80106134182d0b1349c2d061341801220bc9ca106004284d
|35=>0x111342801210a4184d2204c9ca106004284d0c0a430132713418010c04c2c4d21004184d05324844406134280105134283500134182906134185e111342801047fa0001210bc184d0b1341801061342c0105134284d0611828012b03c9c3d06004144d0013448030f0a4144d220bc84450613428010f0a4280100134144d0a0e830132713418012f13c9c2d271341801
|36=>0x28004284d061341829220bcb44d0611428014213c302d060d4004d0c0ac183500134144d11134b44f0611428010f0a418010513428010a1351c0f0f004144d7113d1c290f004144d0c0b4183500134144d047fa0001210bc184d0a134191e0f004144d2204c30292713418010432484440613428017813d7c2d060f4144d2204c185d1113428013a470182d0f004144d
|37=>0x332484440613428012204c3029060d4004d220bcb44d0611428012d13c9c29061341801061342c360013418012204ccc3500134182968134e83700134182d06178283500134144d2136484460613428016e0be1c292100c184d051349c290013418012213c302921004184d2213ca40106284284d2213c302921004184d0a0e430132713418010013418c20f0b4144d
|38=>0x60a57c29060f4144d2b04d7c01060f4144d2206cb44d0611428010647828010f004144d270b430132713418012213c30292713418010c04c84010613418292204c9ca106004284d0a0e43013060d4004d060a4283506134004d21110280106134180100134b44f0611428010c04c284d21004184d2213c185d0a0d4004d060a51c0f0f004144d2213ccc35001341829
|39=>0x613428010a0d4004d060a4444f060a428015f00c183d05134a40306284284d0a13418460a0041829060f4144d2739c18010b134284d060f4144d3a00c184d060b4b44f270a418010b0d8004d06004302b27134180133004144d060a4144d060a42801068942c360013428012713418010c0b49c4d06004185d0a0d4004d2728c18010a1342801060d8004d330d4004d
|40=>0x290bc18a10a135a401210ac184d0c0a49c4d06004185e111342801290bc8429061341801051342c0106178444d0a00418f2390042c4d270a4004d06004182d0f004144d0c0b49c4d06004301321004184d21118184d0a004302b060d4004d0a0049c4f06004144d270bc18010c0b4183500134b44d061142801270b41801051357c2f060f4144d00134144d0b0048447
|41=>0x51356403063942c4d061349c2f060057c2b060f4144d06178283500134185e0a0d4004d063c82c35001349c2d061341801470ac3c010513430132713418010a0d8004d0513419110b0042c4d0f0a4004d051348445061342801066f4283600134144d0b0d4004d11134184d0a004283500134144d33004184d060a428010613418292d13c18450a004184d0a1342801
|42=>0x3a13c182d72134e803060b42801210a4184d06004183d051349c2927134180106118144d0a0042c01063942c4d0c04c9c4d06004b44d0611428010b0d4184d001342c3500134182d063083c2d05134c0030f0b4144d06134004d0b004182d001342c010c04c1835001348401210b4184d2111c184d0a0041801061342c010f0a4180105134004d0611428010a0d4004d
|43=>0x60d8004d0b0043c01060f4144d870a48403061349c2906004284d06444144d0b004842921004184d0a0d8184d001351c290f004144d2900418a10a134bc4f270b418010c0a48401061342c3506134004d0b0d4004d060b4283506134004d2d13c18450a004e83400134182d060d4004d0a0060001210bc184d00134183d05134302f271341801870b48403061342c01
|44=>0x13644292713c18010c0ac8401061343c29060f4144d0f0b4004d0513650013a13c182d0f0b4144d0b00430292713418014703c3c0105134cc010013418290013418290a004e83700134182d0f444144d0b00418011113428010a0d4184d001356401063942c4d051349c2b06006442d2713c18010c0bc9c4d06004280106004284d0b0049c4d060042801060d4004d
|45=>0x613428010f0a4144d0a0049ca106004284d0c0ac9c4d06005ac4d0611828010b1348401061351c0f0f004144d061349c2b060049c3d06004144d064783c01051343029060d4004d0f0b4180105134e80106134182d3a0dc004d060b4004d270bc18010a13418450a004e83500134182d0a134144d060a49c2d00134180106004004d051342c012713c18010a8a41836
|46=>0xc0ac9c4d06004144d270a418010c0b49c4d0600418010b0d4004d0b134e803060b4a00106004284d0c04c840106134cc36001341829290bc18a10a134284d06134182906004184d00134e83f060b4144d0a004004d05134301327134180100134144d060a42c4d061342c0106004184d0b134144d06004284d06004e4010b13448030f0a4144d0b8a41836001348446
|47=>0xa00484440613428010013418460a004283500134180100134184d060a49c2906004284d1113c18010a004184a0f0a4144d2d13c18450a005d84d270ac1801661349c2f06004184d06004284d2f13c19110b0042c3606134004d0c04c1835001341801051342801270b49c4d0600418010a0d8004d06174444d0a00484010613418292d13418450a004284d21004184d
|48=>0xb0d4004d0b1349c2d06004cc4d060a42801060d4004d0b004280106134180105134004d060b4182d051342c012144c184d0b004284d0f004144d0a0048401061349c290613418010513418450a004004d210b4184d060d4004d051341a3d1113c28010f0b4183d05134302f27134180106004842d061343c46051342801060d4004d0b004444d061142801111341829
|49=>0xa0043c0105134840106134182d0a134144d0a0042c4d06134182d06178444d0a004842906134004d06174444d0a004185e1113428012728418010a1341801210a4184d470bc3c01051342c4d060042c015f004183d051343c01051341829270fc180105134e803060b4144d001349c2b06004301327134180106444004d0b004302f060d4004d0a004184d001341835
|50=>0x134144d210b4184d270ac1801111342801064442c010a134280106134182906134284d210bc184d2100c184d00134182d061342c01061182801061342c4d051341829060b42c4d060d4004d1113418290a004e83600134182d00134184d060b4b44d270a418010b004184d060b57c2d060f4144d0c0a4840106134444d0513428010a0d4183500134184d061142801
|51=>0x60f4144d0b0d8004d063942c4d060042c4d2713c18013a00c182d0613428010b0042c4d271341801060d8004d0f0a4144d060b42c010611428010f004144d0a0d4004d1113c280106004280106134004d061341801270a418010513428010a0d8004d21004184d0b0d4004d11134280106134182d210a4184d3a134182d390042c4d06004144d001342c01060b4144d
|52=>0x60b4184d060a4144d0b004004d0a004284d060042c4d27134180105134284d0f0b4144d060042c0100134280106284284d051342c01001341829270bc1801270b4180106004284d210ac184d3a004182d061142801060a42801060a4284d0013418013a13c182d
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x1330000000000e500000000000000000000000000a4000000000000000000000055000000000000000000000005000000000000
|8,0=>0x13f513a51364132412e41295124511f511a51164111510c5107510340fe50f950f540f050eb50e650e150dc50d750d250cd50c850c350be50ba40b550b140ad40a850a3509e50995094508f508a50855080507b50765071506c50684064405f505a50555050504c40475042503f303b40365032402d502850253020501b50165
|8,1=>0x26b52674262525e425a425552505000024b52465241523c52375232522d52285223521f421a521550000210520b5207420341fe51f951f451ef51ea51e551e051db51d651d151cc51c751c251bd51b851b351ae51a951a451a0419b51965191518c51875182517e41795174516f516a51655160515b51565151514c514841444
|8,2=>0x38b53865381537c537753725000036d536850000363535e500003595354534f534c33475342533d53385333532e53295324531f531a53155310530c4308430352fe52f952f452ef52ea52e552e052db52d652d1500002cc52c752c342be52b952b452b042ab52a652a15000029c52975292528d52885283527e5279527542705
|8,3=>0x3fb53f6500003f153ec53e753e253dd53d943d453cf53ca53c553c053bb53b653b153ac500003a843a3539e5399539543905
|9,0=>0x4fc44f844f444f044ec44e844e444e044dc44d844d444d044cc44c844c444c044bc44b844b444b044ac44a844a444a0449c449844944490448c448844844480447c447844744470446c446844644460445c445844544450444c444844444440443c443844344430442c442844244420441c441844144410440c4408440444004
|9,1=>0x5fc45f845f445f045ec45e845e445e045dc45d845d445d045cc45c845c445c045bc45b845b445b045ac45a845a445a0459c459845944590458c458845844580457c457845744570456c456845644560455c455845544550454c454845444540453c453845344530452c452845244520451c451845144510450c4508450445004
|9,2=>0x6fc46f846f446f046ec46e846e446e046dc46d846d446d046cc46c846c446c046bc46b846b446b046ac46a846a446a0469c469846944690468c468846844680467c467846744670466c466846644660465c465846544650464c464846444640463c463846344630462c462846244620461c461846144610460c4608460446004
|9,3=>0x7fc47f847f447f047ec47e847e447e047dc47d847d447d047cc47c847c447c047bc47b847b447b047ac47a847a447a0479c479847944790478c478847844780477c477847744770476c476847644760475c475847544750474c474847444740473c473847344730472c472847244720471c471847144710470c4708470447004
|9,4=>0x8fc48f848f448f048ec48e848e448e048dc48d848d448d048cc48c848c448c048bc48b848b448b048ac48a848a448a0489c489848944890488c488848844880487c487848744870486c486848644860485c485848544850484c484848444840483c483848344830482c482848244820481c481848144810480c4808480448004
|9,5=>0x9b849b449b049ac49a849a449a0499c499849944990498c498849844980497c497849744970496c496849644960495c495849544950494c494849444940493c493849344930492c492849244920491c491849144910490c4908490449004
|10,0=>0xa793a763a733a703a6d3a6a3a673a643a613a5e3a5b3a583a553a523a4f3a4c3a493a463a433a403a3d3a3a3a373a343a313a2e3a2b3a283a253a223a1f3a1c3a193a163a133a103a0d3a0a3a073a043a0139fe39fb39f839f539f239ef39ec39e939e639e339e039dd39da39d739d439d139ce39cb39c839c539c239bf39bc3
|10,1=>0xb393b363b333b303b2d3b2a3b273b243b213b1e3b1b3b183b153b123b0f3b0c3b093b063b033b003afd3afa3af73af43af13aee3aeb3ae83ae53ae23adf3adc3ad93ad63ad33ad03acd3aca3ac73ac43ac13abe3abb3ab83ab53ab23aaf3aac3aa93aa63aa33aa03a9d3a9a3a973a943a913a8e3a8b3a883a853a823a7f3a7c3
|10,2=>0xbf93bf63bf33bf03bed3bea3be73be43be13bde3bdb3bd83bd53bd23bcf3bcc3bc93bc63bc33bc03bbd3bba3bb73bb43bb13bae3bab3ba83ba53ba23b9f3b9c3b993b963b933b903b8d3b8a3b873b843b813b7e3b7b3b783b753b723b6f3b6c3b693b663b633b603b5d3b5a3b573b543b513b4e3b4b3b483b453b423b3f3b3c3
|10,3=>0xc9b3c983c953c923c8f3c8c3c893c863c833c803c7d3c7a3c773c743c713c6e3c6b3c683c653c623c5f3c5c3c593c563c533c503c4d3c4a3c473c443c413c3e3c3b3c383c353c323c2f3c2c3c293c263c233c203c1d3c1a3c173c143c113c0e3c0b3c083c053c023bff3bfc3
|11,0=>0xd1c2d1a2d182d162d142d122d102d0e2d0c2d0a2d082d062d042d022d002cfe2cfc2cfa2cf82cf62cf42cf22cf02cee2cec2cea2ce82ce62ce42ce22ce02cde2cdc2cda2cd82cd62cd42cd22cd02cce2ccc2cca2cc82cc62cc42cc22cc02cbe2cbc2cba2cb82cb62cb42cb22cb02cae2cac2caa2ca82ca62ca42ca22ca02c9e2
|11,1=>0xd222d202d1e2
|12,0=>0xd2d1d2c1d2b1d2a1d291d281d271d261d251d241
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 16
def pmP:Nat→Nat
|0=>0x103800000000000080c0000000000004020000000000002000000000000000ea00000000000003540000000000001a80000000000000d300000000000006900000000000003400000000000001880000000000000940000000000000490000000000000240000000000000108000000000000054000000000000028000000000000010c0000000000000820000000000000320000000000000130000000000000080000000000000028000000000000012000000000000008000000000000003000000000000000a0000000000000040000000000000018000000000000008000000000000002000000000000000
|1=>0xfeb8000000000007e5c000000000003e2e0000000000017f7000000000000b8b8000000000005b7c000000000002daa000000000001697000000000000b0b80000000000058080000000000029ae000000000001484000000000000a098000000000005000000000000001d6e000000000000c0000000000000057b8000000000002a5c0000000000014060000000000008d20000000000004010000000000001edc000000000000d2e0000000000004d000000000000024300000000000010400000000000008000000000000002f000000000000016b8000000000000b40000000000000508000000000000210
|2=>0x4b7b8000000000025b5c000000000012d6e00000000000969f000000000004b4b8000000000025a1c000000000012c2e00000000000949700000000000494f8000000000022148000000000010d2e000000000008450000000000004138000000000002094000000000001040000000000000815400000000000402a00000000000201480000000000100a00000000000080100000000000040020000000000020008000000000010000000000000005a17000000000002008000000000000de5c000000000004f2e0000000000024100000000000011ea000000000000888000000000000403c000000000002014
|3=>0x10461000000000008071000000000004018000000000001f69700000000000eb4b8000000000074a4c000000000032d6e00000000001969700000000000c25b800000000003da5c00000000001e92e00000000000d697000000000006049800000000002ffdc000000000017d6e00000000000be97000000000005d4b800000000002dadc000000000016d3e00000000000b697000000000004ffb8000000000027edc000000000013f3e000000000009f97000000000004f6b8000000000027adc000000000013d3e000000000009e97000000000004beb8000000000025edc000000000012f3e000000000009797
|4=>0x25b4f800000000012da5c00000000009402c000000000049ff7000000000024bdb8000000000125e5c000000000092d6e00000000004969f000000000024b4b80000000001090c800000000008444c00000000004221600000000002101b0000000000108058000000000084020000000000041e97000000000020d4b8000000000103c9c000000000081de4000000000040e020000000000207000000000000102b4800000000008152e000000000040a0700000000002050100000000001028000000000000804400000000000402020000000000200090000000000100008000000000056d0a000000000028000
|5=>0x10d00a000000000082527c0000000004100200000000002000140000000001000080000000000535a5c000000000296d6e00000000011f6b700000000008fb4b8000000000465adc000000000232d2e0000000001192b7000000000087b5b800000000043da5c00000000021ad2e00000000010b69700000000008594f800000000042ca5c000000000212d6e00000000010969700000000008425b80000000002008100000000000d250600000000006368700000000002eb5b8000000000165a5c00000000009ad2e00000000004d497000000000025ffb800000000012fedc000000000096dee00000000004b6b7
|6=>0x22015b80000000011008dc000000000880464000000000440010000000000214b638000000001080b40000000000816d6e0000000004097d7000000000204b6b8000000001025a5c000000000806d6a00000000040263300000000020111b800000000100889c0000000008040200000000004006120000000002001f90000000001000b500000000008005a200000000040021600000000020010900000000010005140000000008002820000000004000d500000000020006980000000010001040000000008000460000000004000010000000001a52438000000000d20048000000000612d2e00000000024b6b7
|7=>0x1006b4f800000000802da7c000000002001f3c000000000ccb6bf000000000604bef8000000002329e7c00000000119253e000000000849f9f000000000424d6b8000000002125e7c000000001017d3e00000000080ba9f000000000405b4f8000000002028a4c0000000008d6d6e00000000044bff7000000000225f5b800000000112eafc000000000896f6e00000000044b6f7000000000225b5f800000000112dadc000000000896d2600000000044b63f000000000225b1b8000000001125adc000000000884c640000000004426140000000002211fb0000000001108b4000000000088442c000000000440bd2
|8=>0x8007b5b8000000040035adc00000002001ad2e00000001000b6b7000000008005a5a80000000400290cc000000020012d2e00000001000841200000000800401900000000400200580000000200040200000000100000260000000080000008000000030025a7c000000015092d3e0000000080ca69f00000000404111b000000002012026c00000001008053600000000800969f00000000400494f800000002002126c000000010000d36000000008000000000000002404f4f800000001000167c00000000708483e00000000280b69f00000000140494f8000000008824a7c00000000409ad3e00000000201969f
|9=>0x81acb5b8000000040c6dadc000000020612d2e00000001025b4b7000000008125b5b800000004092804000000002041002800000001014f6b70000000080a7b4b8000000040535adc00000002029ad2e00000001014b6b70000000080a525b80000000405242fc00000002021ad6e00000001005f6b700000000802fb4b800000004016dadc00000002009ed7e00000001004f6b7000000008026b5b8000000040131abc00000002009486400000001004a41400000000802500b0000000040125adc00000002009016e000000010048037000000008024019000000004010004000000002003ed6e00000001001d6b7
|10=>0x2000495f8000000100024a5c0000000800100240000000400036970000000200016780000000100008c08000000080003d2e000000040001797000000020000793800000010000380c000000080001804000000040000c000000000200005030000000100002218000000080000b080000000400004840000000200001018000000100000408000000080000124000000040000086000000014024b4f80000000a0025a7c000000040012d3e00000002000000000000000c004b4f8000000048535a7c0000000240bcd3e00000001201f69f000000009007b4f800000004112dadc000000020896c6e00000001035b6b7
|11=>0x20024bcb8000000100125a5c000000080087d6e0000000400437b700000002002114b0000000100105a5c000000080082d26000000040040e0200000002002070000000001001028180000000800814080000000400404020000000200201010000000100080208000000080017fee00000004000bfb7000000020005fcb800000010002fadc000000080017d2e00000004000b797000000020005b4b8000000100027fdc000000080013d6e000000040009e97000000020004dc98000000100026a7c000000080012f6e000000040009797000000020004b5b8000000100025a7c000000080012d2e000000040009395
|12=>0x20424d4f8000000102125e7c000000081092d3e000000040840293000000020405f4f800000010202de7c000000081016d3e00000004080af9f000000020404fcf8000000102027a7c000000081012f3e00000004080969f0000000204047cf8000000102002a5c00000008100052600000004044bfb7000000020225f5b800000010112dadc0000000808845ec000000040440bd6000000020204b6b800000010012fe5c000000080097d6e00000004004be97000000020025bdb8000000100127fdc000000080093f6e000000040049f97000000020024f6b8000000100127adc000000080093d2e0000000400497b7
|13=>0x1000002b2b800000800000fcdc000004000002c3e000001800049292000000208104b43800000104082004000000082029ad0e0000004101196a700000020800fb438000001000c0000800000080042000800000040020000000000010142120f800000080a02d87c00000023001406c00000011204b6bf0000000880040020000000420129a7c0000001800d6d6e0000000c0069e87000000040034357800000020012dadc00000010008350e00000004888b69f000000024400b05800000010212fe7c000000081097d3e00000004084ba9f0000000204253cf8000000102127e7c000000081093d3e000000040849b97
|14=>0x4020424d4f800002002a00d07c000008230016d3e00000410804969f000002030404b4f8000010122325a7c000008091112d3e00000404004a29b000002020004b4f80000100a0225a7c000008040196d3e00000402000969f000002004064b4f800001002022da7c000008010032d3e00000400800979f0000020040000010000010000025a7c00000800000033e000002040049e17000001020005b8b8000008040027cdc000004000096c6e000002000047637000001000020f9b800000800010685c000004000013eee000002000009e97000001000004bcb8000008000025adc000004000012cae000002000009617
|15=>0x10020025fcb800008010012de5c000040080081de40000200400401f2000010020005fdb800008010002fe5c000040080016fae00002004000b7b7000010020005bcb8000080100025bdc000040080004fe4000020040001797000010020000381800008000110bbc8000040000813dae0000200004000d3000010000001bcb8000080000009c0c0000400000046060000200000004d1000010000000168800008000000098400003000000006200001008004b6bf000006084004b4f800003002a025a7c000018010112d3e00000c004809f9f000006002404f4f8000030012025e7c000018009012d3e000008040849e9f
|16=>0x10000102cb4f8000800000865a5c00040000029ad2e00020000005d6b700010000002cb4b800080000007da5c000400000032d6e00020000001969f000100000004b4f8000800000024a7c000298008012d3e00010c00e84b69f000086007424b4f800043003a02da7c00021801d012d3e00010400400b69f000080004004bcf8000400010024a7c000182002013d3e0000c000100979f000060000804b4f8000200010025a7c000100000012d3e000044044809e9f000022022404b4f8000110010027a7c000088008012f3e00004004480979f0000200020047cf800008010112dedc000040080805fa4000020040400ff6
|17=>0x70008c006b4f8003000000535a5c001208024012d3e00080400800000200040000818cb5b800200004007da5c001000010012d3e00080000014d69700040000008fb4b800200000007da5c000c000040bad3e00060000201f69f00030000100eb4f8001800000575a5c000c000002b293e00060000001f69f00030000000fb4b8001000000c65adc0008000002bad6e00040000011f69700020000008eb5b8001000000465adc000800000232d2e00040000005d69700020000000eb4b8001000000025a5c000688000032d3e00020800014d69f0001000090a6b4f8000800040535a5c00040001001253e00020000221969f
|18=>0x8000000810c019024000002a02d87c100000007016c3e040002040009697020001008004f9b80800001001adadc040000080056f0e02000000004b6b7010000000004b4b8040c10000025a7c020388008012d3e01014400400969f008022002004b4f8040110000025e7c020010015094c3e01000400080979f008002000004b4f8040000010027a7c020000008012f3e01000000000969f004402008004b4f802001044012da7c010008210012d3e00800000804969f002000008025b5b801000000018fadc0080000000c6f6e004000000029fe7001000002004b4f800400000002585c001e0002001ad3e000e0011804d69f
|19=>0x100000001034a432400040000806b4f9000000000024a7c400000000432d2e10000001025a036
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x28000000200000000000000000800000000000001c0000000000000180000000
|8,0=>0x1485041b40101804c000c814004010344000c0d0302b3c960001cd0c80201c9459c7a3f40f314dd0240d02403058c90ccaa00d92005a9219bd2f00305426038070300110427004803440d7192a5395469c3208425008bb034030581c11010024070141e0ac154288442409075911ccc36f0012183a01c024880511d9c22c830804c4541602c8f2a54e5508145c0d44c070054c124074147d0544c0082e24403
|8,1=>0x332d482ec0c2f84b760020344d0743d0d832248a82f40020834435ab0104a00c0d48c050344e4208b311086cd13000c6540120c0320042d4500100c01035af27422024020441d4180f030dc0340d0580303451000c47a407438c60240200c0d0200005c83004030043b1200d10832
|9,0=>0x779d57089333c965f0191617d5c05d87d4d85caf4756164d8123a2016d451dcd64ce2d40d11350e5469ba591681f9f01e41a5617a6699e565a50a1ed7119b7224d289bf3a4cc3acba4a0936626129e0b36c38141ec61d493360a8c4bf7152c15d741adad42c8727831458ab911c94a45b139ee2dd7770437174d32541a31d198d4e8225b14656c85a5b28d2c68e5c55a5916c46240b621de08923998d7e529b8
|9,1=>0x3398a615123d0c06056f8f172149590f84573db26b1758c13c70db04c8245452d4e9f4268a48241f354f146d5a03839408932e8b4604d013d5d0e07455db97adcc2285b1652c16d8679214699ce6893957d71811a10f09665c380b0de920ba321e83e88d2e4544415a90947519a42b8e25c20853d551f1ef0f8df5cd5c060756dc5e08e03916467cc225d4636d9ea5b1808389e6264c5ed5e5682f5b9790a577
|9,2=>0x2437b250460cd3906710d855ad5c384888303816c9372c2a2981b161df35c3768cde068c795e4a61053490fc23da88366297c5b948a116a2105c5c5485e1fd27154f82305d2cd669754b55dda95d251be516d5191ac1838161258356b8fb3047c2e0566809343ddb3695371cc241d625855a6f838968586ee0f3b83f9388c3de404a5fc5b0d23950c56cca
|10,0=>0x3a9e5770788fcec9556c5fc789058860a263cc6c4716d4b18e2961517dfa8d0f0269d71ae3662d368c98116c5b2805d84d421747b1e16a84a026522b961f94d61d92e494ae2839d401751f749fe686262c1e15d9818752194cea3e62c74e0025e236159f5b1657dd697145d7c9817294316e267fa254f647584e61c0fe981f55123d40563611647985e5a1e21b1e31e5f72985b6699525d8e4ed8c1b09a361d0
|10,1=>0x6109787201481d1635a163dfb81d2e65a2a5e09c60d8117872958b284205411001c0e786926601388dc6b4b16e87e3317606641f86693f3ad6179d194f9624b1ff6116158d8826d6f5add47dc6c1b071898a66a9994c09a7f4ed7d8ef3659a991372d581504977006a281006745b3d9312ccf58e1d625d63765f13a9614d20b1c25e93ce37761a86cb07ea1e1a52f27c7625c6c
|11,0=>0xa0196491d97e1acff2686c8e8701762f5b1641a09e1e21125e2e2c06c1e1632c4ea25dd689df7951815856b2646e7dd9425d42889818646b8ba3e1b4a5860988ec6c6062f5a0621985d1761b479612b4618a4ea
|12,0=>0x1e05d1805c1d097584641b0ac
|13,0=>0x5b
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 10 (j%128);fld (pmP (k/32)) 61 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_253 12 roots_253 ops++addP pm 1 dom_223 11 roots_223 ops++addP pm 2 dom_191 11 roots_191 ops++addP pm 3 dom_111 9 roots_111 ops++addP pm 4 dom_251 12 roots_251 ops++addP pm 5 dom_95 8 roots_95 ops++addP pm 6 dom_86 5 roots_86 ops++addP pm 7 dom_246 10 roots_246 ops++addP pm 8 dom_222 9 roots_222 ops++addP pm 9 dom_254 11 roots_254 ops++addP pm 10 dom_127 11 roots_127 ops++addP pm 11 dom_126 9 roots_126 ops++addP pm 12 dom_239 12 roots_239 ops++addP pm 13 dom_159 8 roots_159 ops++addP pm 14 dom_183 9 roots_183 ops++addP pm 15 dom_247 11 roots_247 ops++addP pm 16 dom_215 8 roots_215 ops++addP pm 17 dom_250 10 roots_250 ops++addP pm 18 dom_63 8 roots_63 ops++addP pm 19 dom_238 9 roots_238 ops++addP pm 20 dom_119 9 roots_119 ops++addP pm 21 dom_87 6 roots_87 ops++addP pm 22 dom_27 4 roots_27 ops++addP pm 23 dzo_174_16 6 roots_174 ops++addP pm 24 dzo_109_2 6 roots_109 ops++addP pm 25 dzo_167_16 6 roots_167 ops++addP pm 26 dzo_238_16 7 roots_238 ops++addP pm 27 dzo_175_16 7 roots_175 ops++addP pm 28 dzo_87_8 6 roots_87 ops++addP pm 29 dom_110 6 roots_110 ops++addP pm 30 dom_190 8 roots_190 ops++addP pm 31 dzo_59_4 5 roots_59 ops++addP pm 32 dom_231 9 roots_231 ops++addP pm 33 dzo_171_16 6 roots_171 ops++addP pm 34 dom_243 9 roots_243 ops++addP pm 35 dzo_61_2 6 roots_61 ops++addP pm 36 dom_252 9 roots_252 ops++addP pm 37 dzo_214_8 6 roots_214 ops++addP pm 38 dzo_239_16 8 roots_239 ops++addP pm 39 dom_207 9 roots_207 ops++addP pm 40 dom_235 10 roots_235 ops++addP pm 41 dom_158 5 roots_158 ops++addP pm 42 dom_175 9 roots_175 ops++addP pm 43 dzo_237_16 7 roots_237 ops++addP pm 44 dzo_231_16 7 roots_231 ops++addP pm 45 dzo_119_8 7 roots_119 ops++addP pm 46 dzo_247_8 8 roots_247 ops++addP pm 47 dzo_215_8 7 roots_215 ops++addP pm 48 dzo_246_8 7 roots_246 ops++addP pm 49 dzo_235_16 7 roots_235 ops++addP pm 50 dzo_91_4 5 roots_91 ops++addP pm 51 dom_103 6 roots_103 ops++addP pm 52 dom_45 5 roots_45 ops++addP pm 53 dzo_155_4 5 roots_155 ops++addP pm 54 dzo_118_8 6 roots_118 ops++addP pm 55 dom_143 6 roots_143 ops++addP pm 56 dom_55 5 roots_55 ops++addP pm 57 dzo_115_8 6 roots_115 ops++addP pm 58 dom_174 6 roots_174 ops++addP pm 59 dzo_229_16 6 roots_229 ops++addP pm 60 dom_151 5 roots_151 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54|h55|h56|h57|h58|h59|h60
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_174_16_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_109_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_167_16_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_238_16_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_175_16_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_87_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_59_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_171_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_61_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_214_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_239_16_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_zo_237_16_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_zo_231_16_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_zo_119_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_zo_247_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_zo_215_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_zo_246_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_zo_235_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_zo_91_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h52;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h53;exact cpcs (by decide +kernel) lowS_zo_155_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h54;exact cpcs (by decide +kernel) lowS_zo_118_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h55;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h56;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h57;exact cpcs (by decide +kernel) lowS_zo_115_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h58;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h59;exact cpcs (by decide +kernel) lowS_zo_229_16_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h60;exact cpcs (by decide +kernel) lowS_151 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_253 12 s (0,roots_253.map (·&&&dom_253)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_253 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 31 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 31 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 217 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 89 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 217 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 256 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_256 : ∀ i, 256 ≤ i → i < 367 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 111 256 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 367 → Z 9 i = true := (range_split z9_0 (range_split z9_128 z9_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 246 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 118 128 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 246 → Z 10 i = true := (range_split z10_0 z10_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 67 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 67 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 10 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 10 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [2, 1] }, { op := GateOp.or, inputs := [7, 5] }, { op := GateOp.or, inputs := [7, 6] }, { op := GateOp.or, inputs := [5, 8] }, { op := GateOp.or, inputs := [6, 0] }, { op := GateOp.or, inputs := [1, 12] }, { op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [14, 12] }, { op := GateOp.and, inputs := [4, 13] }, { op := GateOp.and, inputs := [11, 10] }, { op := GateOp.and, inputs := [9, 15] }, { op := GateOp.and, inputs := [0, 3] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52346_aux

theorem PEqualNP.Outside.L_meta_52346 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52346_aux.main
