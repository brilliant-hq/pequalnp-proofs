import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52990_aux
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

def dom_41 : Nat := 0x30300000303
def goal_41 : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_41 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_42 : Nat := 0x50500000505
def goal_42 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00
def roots_42 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfffafffaaa00aa00fffafffaaa00aa00fffafffaaa00aa00fffafffaaa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xfffcfffccc00cc00fffcfffccc00cc00fffcfffccc00cc00fffcfffccc00cc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfffefffeee00ee00fffefffeee00ee00fffefffeee00ee00fffefffeee00ee00
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

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffeeeeaaee00ffeeffeeeeaaee00ffeeffeeeeaaee00ffeeffeeeeaaee00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_60 : Nat := 0x1111111111111111
def goal_60 : Nat := 0xfff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000
def roots_60 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafffafafaaa00fffafffafafaaa00fffafffafafaaa00fffafffafafaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcfffcfcf0cc00fffcfffcfcf0cc00fffcfffcfcf0cc00fffcfffcfcf0cc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefffefefaee00fffefffefefaee00fffefffefefaee00fffefffefefaee00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffaaffaaffaaffaaee00ee00ee00ee00ffaaffaaffaaffaaee00ee00ee00ee00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfffafffafffafffaaa00aa00aa00aa00fffafffafffafffaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfffafffafffafffaee00ee00ee00ee00fffafffafffafffaee00ee00ee00ee00
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_81 : Nat := 0x300030000000000030003
def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_84 : Nat := 0x1100110000000000110011
def goal_84 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_84 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffffafafffffafafafa0000fafa0000fffffafafffffafafafa0000fafa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffffaaffffffaaaaaaaa00aaaaaa00ffffffaaffffffaaaaaaaa00aaaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffff00ffffff00cc00cc00cc00cc00ffffff00ffffff00cc00cc00cc00cc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffaaffffffaaeeaaee00eeaaee00ffffffaaffffffaaeeaaee00eeaaee00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfffffff0fffffff0f0f00000f0f00000fffffff0fffffff0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffffafffffffafafaaa00fafaaa00fffffffafffffffafafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffff0fffffff0fcf0cc00fcf0cc00fffffff0fffffff0fcf0cc00fcf0cc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffffafffffffafefaee00fefaee00fffffffafffffffafefaee00fefaee00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_97 : Nat := 0x3000000030000000300000003
def goal_97 : Nat := 0xffffffffaaaaaaaaaaaaaaaa00000000ffffffffaaaaaaaaaaaaaaaa00000000
def roots_97 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xffffffffaaaaaaaaeeeeeeee00000000ffffffffaaaaaaaaeeeeeeee00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_100 : Nat := 0x11000000110000001100000011
def goal_100 : Nat := 0xfffffffff0f0f0f0f0f0f0f000000000fffffffff0f0f0f0f0f0f0f000000000
def roots_100 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfffffffffafafafafafafafa00000000fffffffffafafafafafafafa00000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfffffffff0f0f0f0fcfcfcfc00000000fffffffff0f0f0f0fcfcfcfc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfffffffffafafafafefefefe00000000fffffffffafafafafefefefe00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_104 : Nat := 0x101000001010000010100000101
def goal_104 : Nat := 0xffffffffff00ff00ff00ff0000000000ffffffffff00ff00ff00ff0000000000
def roots_104 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffffaaffaaffaaffaaaa00aa00ffffffffffaaffaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffff00ff00ffccffcccc00cc00ffffffffff00ff00ffccffcccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffffaaffaaffeeffeeee00ee00ffffffffffaaffaaffeeffeeee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfffffffffff0fff0fff0fff000000000fffffffffff0fff0fff0fff000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffffffffffafffafffafffaaa00aa00fffffffffffafffafffafffaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffffffffff0fff0fffcfffccc00cc00fffffffffff0fff0fffcfffccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffffffffffafffafffefffeee00ee00fffffffffffafffafffefffeee00ee00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffffffffffaaaaaaaaaaaaaaaa0000ffffffffffffaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffffff0000cccccccc00000000ffffffffffff0000cccccccc00000000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffffffaaaaeeeeeeeeaaaa0000ffffffffffffaaaaeeeeeeeeaaaa0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffffffffffff0f0f0f0f0f0f0f00000fffffffffffff0f0f0f0f0f0f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffffffafafafafafafafa0000fffffffffffffafafafafafafafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffffff0f0fcfcfcfcf0f00000fffffffffffff0f0fcfcfcfcf0f00000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffffffafafefefefefafa0000fffffffffffffafafefefefefafa0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffffffffffff00ff00ff0000000000ffffffffffffff00ff00ff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffffffaaffaaffaaaaaaaa00ffffffffffffffaaffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffffff00ffccffcccc00cc00ffffffffffffff00ffccffcccc00cc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffffffaaffeeffeeeeaaee00ffffffffffffffaaffeeffeeeeaaee00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffffffffffff0fff0fff0f0f00000fffffffffffffff0fff0fff0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffffffafffafffafafaaa00fffffffffffffffafffafffafafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffffff0fffcfffcfcf0cc00fffffffffffffff0fffcfffcfcf0cc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffffffafffefffefefaee00fffffffffffffffafffefffefefaee00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_138 : Nat := 0x50500000000000000000000000000000505
def goal_138 : Nat := 0xffccffccffccffccffccffccffccffcccc00cc00cc00cc00cc00cc00cc00cc00
def roots_138 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeee00ee00ee00ee00ee00ee00ee00ee00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_142 : Nat := 0x555500000000000000000000000000005555
def goal_142 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffccc00cc00cc00cc00cc00cc00cc00cc00
def roots_142 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffefffefffefffefffefffefffefffeee00ee00ee00ee00ee00ee00ee00ee00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeaaaa0000aaaa0000aaaa0000aaaa0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_148 : Nat := 0x11001100000000000000000000000000110011
def goal_148 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_148 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafafafa0000fafa0000fafa0000fafa0000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcf0f00000f0f00000f0f00000f0f00000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefefafa0000fafa0000fafa0000fafa0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffcccc00cc00cc00cc00cc00cc00cc00cc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeeeaaee00eeaaee00eeaaee00eeaaee00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfffffff0fffffff0fffffff0fffffff0f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffafafaaa00fafaaa00fafaaa00fafaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfcf0cc00fcf0cc00fcf0cc00fcf0cc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffefffffffefffffffefffffffefefaee00fefaee00fefaee00fefaee00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_162 : Nat := 0x50000000500000000000000000000000500000005
def goal_162 : Nat := 0xffffffffccccccccffffffffcccccccccccccccc00000000cccccccc00000000
def roots_162 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfffffffffafafafafffffffffafafafafafafafa00000000fafafafa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfcfcfcfc00000000fcfcfcfc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffefefefefffffffffefefefefefefefe00000000fefefefe00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffffccffccffffffffffccffccffccffcccc00cc00ffccffcccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeee00ee00ffeeffeeee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffafffafffaaa00aa00fffafffaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfffcfffccc00cc00fffcfffccc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffefffefffffffffffefffefffefffeee00ee00fffefffeee00ee00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffeeeeffffffffffffeeeeeeeeeeeeaaaa0000eeeeeeeeaaaa0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f0f0f0f0f00000f0f0f0f0f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffffffafafffffffffffffafafafafafafafa0000fafafafafafa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfcfcfcfcf0f00000fcfcfcfcf0f00000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffefefffffffffffffefefefefefefafa0000fefefefefafa0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffffaaffffffffffffffaaffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffffccffffffffffffffccffccffcccc00cc00ffccffcccc00cc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffeeffffffffffffffeeffeeffeeeeaaee00ffeeffeeeeaaee00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0fff0fff0f0f00000fff0fff0f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffffafffffffffffffffafffafffafafaaa00fffafffafafaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffffcfffffffffffffffcfffcfffcfcf0cc00fffcfffcfcf0cc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffefffffffffffffffefffefffefefaee00fffefffefefaee00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f00000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfffffffffffffffffefefefefefefefefafafafafafafafa0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffffccffccffccffccff00ff00ff00ff00cc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffaaffaaffaaffaaee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffffafffafffafffafffafffafffafffaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffefffefffefffefffafffafffafffaee00ee00ee00ee00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffaaaaffffaaaaaaaa0000aaaa0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffffafafffffafafffffafafffffafafafa0000fafa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffff0f0fffff0f0f0f00000f0f00000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffefefffffefefffffafafffffafafafa0000fafa0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffeeffffffeeffffffaaffffffaaeeaaee00eeaaee00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffffafffffffafffffffafffffffafafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffffcfffffffcfffffff0fffffff0fcf0cc00fcf0cc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffefffffffefffffffafffffffafefaee00fefaee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffffffffffffffffffccccccccffffffff00000000cccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffffffffffeeeeeeeeffffffffaaaaaaaaeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffffffffffff00ff00ffffffffff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffffccffccffffffffff00ff00ffccffcccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffeeffeeffffffffffaaffaaffeeffeeee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffffffffffafffafffffffffffafffafffafffaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffffffffffcfffcfffffffffff0fff0fffcfffccc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffefffefffffffffffafffafffefffeee00ee00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffffffcfcfffffffffffff0f0fcfcfcfcf0f00000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffffffaaffffffffffffffaaffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffffffccffffffffffffff00ffccffcccc00cc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffffeeffffffffffffffaaffeeffeeeeaaee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffffffffffff0fffffffffffffff0fff0fff0f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffffffafffffffffffffffafffafffafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffffffcfffffffffffffff0fffcfffcfcf0cc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffffffefffffffffffffffafffefffefefaee00
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
def isoMvS_42:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_42:Lower true dom_42 roots_42 goal_42 4:=lower_iso_b isoMvS_42 (by decide +kernel) lowS_41
def isoMvS_73:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_73:Lower true dom_73 roots_73 goal_73 4:=lower_iso_b isoMvS_73 (by decide +kernel) lowS_41
def isoMvS_81:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_41
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_41
def isoMvS_97:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_97:Lower true dom_97 roots_97 goal_97 4:=lower_iso_b isoMvS_97 (by decide +kernel) lowS_41
def isoMvS_100:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_100:Lower true dom_100 roots_100 goal_100 4:=lower_iso_b isoMvS_100 (by decide +kernel) lowS_41
def isoMvS_104:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_104:Lower true dom_104 roots_104 goal_104 4:=lower_iso_b isoMvS_104 (by decide +kernel) lowS_41
def isoMvS_138:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_138:Lower true dom_138 roots_138 goal_138 4:=lower_iso_b isoMvS_138 (by decide +kernel) lowS_41
def isoMvS_148:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_148:Lower true dom_148 roots_148 goal_148 4:=lower_iso_b isoMvS_148 (by decide +kernel) lowS_41
def isoMvS_162:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_162:Lower true dom_162 roots_162 goal_162 4:=lower_iso_b isoMvS_162 (by decide +kernel) lowS_41
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
theorem lowS_43:Lower true dom_43 roots_43 goal_43 5:=lower_slice_b [(0xa0a00000a0a,8,9)] (by decide +kernel) lowS_42
theorem lowS_45:Lower true dom_45 roots_45 goal_45 5:=lower_slice_b [(0x303000003030,32,36)] (by decide +kernel) lowS_41
namespace S_105
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(8,9),(8,40),(8,72),(32,33),(32,40),(32,96),(64,65),(64,72),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_105.map (·&&&dom_105)
def gM:=goal_105&&&dom_105
def NN:Nat→Nat
|3=>3
|4=>7
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xa3c7b36bad0b047
|4,0=>0x5ef5a56d164b08941ad53e3192943b0e7df
|5,0=>0x8401343d8911e8a
|6,0=>0x84013
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c0000080800000c0c0000080b03000003030000020200000202c0800000c0800000c0800000c0b03000003030000030300000202404000004000000040400000400030000000300000002000000020000000000000000c0c00000c0101000001010000010100000100c0c00000c0000000c0c00000c0303000003030000030300000000c0c00000c0c00000c0000000c0202000002020000020200000202c0c0000000000000c0c000000030000000300000003000000030080800000808000008080000080303000003030000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x3240324035240632407f240632e473d40c3240324b0324a093240328076543210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x21022004
|4,0=>0xa952aa0536a5948a8c5
|5,0=>0xe51a2af5
|6,0=>0x3d4
|_,_=>0
def wAt:=mkWire dB 16 106 0x3ffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x204c1324d1404c12448d204c1
|_=>0
def oO:Nat→Nat→Nat
|3,0=>0x200
|4,0=>0x62422200000000
|5,0=>0x9181
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xf76530
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>0x18
|4,0=>0x52000
|5,0=>0x12d
|6,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_104 4 roots_104 ops++addP pm 1 dom_97 4 roots_97 ops++addP pm 2 dom_73 4 roots_73 ops++addP pm 3 dom_41 4 roots_41 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_105 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_41 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_104 4 s (0,roots_104.map (·&&&dom_104)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_105 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_104 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_105==dom_105)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_105 gM v ys):RunD true dom_105 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_105 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_105 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_105 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_105 roots_105 goal_105 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_105
theorem lowS_105:Lower true dom_105 roots_105 goal_105 7:=S_105.noCircuit
def isoMvS_29:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_29:Lower true dom_29 roots_29 goal_29 4:=lower_iso_b isoMvS_29 (by decide +kernel) lowS_27
def isoMvS_46:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_46:Lower true dom_46 roots_46 goal_46 5:=lower_iso_b isoMvS_46 (by decide +kernel) lowS_45
def isoMvS_51:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=lower_iso_b isoMvS_51 (by decide +kernel) lowS_27
def isoMvS_54:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 4:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_27
def isoMvS_57:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_45
def isoMvS_60:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_60:Lower true dom_60 roots_60 goal_60 4:=lower_iso_b isoMvS_60 (by decide +kernel) lowS_27
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_45
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 5:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_45
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_43
def isoMvS_89:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_43
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 4:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_27
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 5:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_45
def isoMvS_99:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_45
def isoMvS_101:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 5:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_43
def isoMvS_102:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 5:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_45
def isoMvS_106:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_43
def isoMvS_108:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 5:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_43
def isoMvS_113:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_43
def isoMvS_114:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 4:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_27
def isoMvS_116:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_43
def isoMvS_120:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 5:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_45
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_43
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_45
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 5:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_45
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_45
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_43
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_45
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_45
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_45
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_43
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 5:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_43
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_43
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 7:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_105
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 7:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_105
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_43
def isoMvS_195:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_45
def isoMvS_198:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_45
def isoMvS_201:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 7:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_105
def isoMvS_202:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_43
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 7:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_105
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 7:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_105
def isoMvS_226:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_43
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 7:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_105
theorem lowS_31:Lower true dom_31 roots_31 goal_31 5:=lower_slice_b [(0xcccccccc,8,10)] (by decide +kernel) lowS_29
theorem lowS_47:Lower true dom_47 roots_47 goal_47 6:=lower_slice_b [(0xaaaa0000aaaa,8,9)] (by decide +kernel) lowS_46
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_slice_b [(0xaa00aa00aa00aa,16,17)] (by decide +kernel) lowS_54
def dzo_43_16:=0xf0f00000f0f0000
def gzo_43_16:=0xf0e00000e0a0000
def gsh_43_16:=0xf0e00000e0a
theorem lowS_zo_43_16_42:Lower true dzo_43_16 roots_43 gzo_43_16 5:=lower_iso_b (d1:=dom_43) (r1:=roots_43) (T1:=gsh_43_16) [(dom_43,16)] (by decide +kernel) (lower_slice_b (T:=gsh_43_16) [(0xa0a00000a0a,0,1)] (by decide +kernel) lowS_42)
namespace S_59
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,34),(3,11),(3,19),(3,35),(8,9),(8,10),(8,40),(16,17),(18,19),(18,26),(18,50),(24,25),(24,26),(24,56),(32,33),(32,34),(32,40),(48,49),(48,50),(48,56)]
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
|4,0=>0x116aa
|5,0=>0xa6f0
|6,0=>0x9abd7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f000f00c0c0c0c0c0c0c0cf0f0f0f00000000f0f00000f0f0000f000f000f000f00a0a0a0a0a0a0a0a303030303000300
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
addP pm 0 dom_57 5 roots_57 ops++addP pm 1 dom_51 4 roots_51 ops++addP pm 2 dzo_43_16 5 roots_43 ops++addP pm 3 dom_43 5 roots_43 ops++addP pm 4 dom_42 4 roots_42 ops++addP pm 5 dom_27 4 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_43_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_57 5 s (0,roots_57.map (·&&&dom_57)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_59 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_57 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
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
theorem lowS_61:Lower true dom_61 roots_61 goal_61 6:=lower_slice_b [(0x3030303030303030,16,20)] (by decide +kernel) lowS_57
def dzo_46_16:=0x5555000055550000
def gzo_46_16:=0x5554000054500000
def gsh_46_16:=0x555400005450
theorem lowS_zo_46_16_42:Lower true dzo_46_16 roots_46 gzo_46_16 5:=lower_iso_b (d1:=dom_46) (r1:=roots_46) (T1:=gsh_46_16) [(dom_46,16)] (by decide +kernel) (lower_slice_b (T:=gsh_46_16) [(0x505000005050,0,4)] (by decide +kernel) lowS_42)
namespace S_62
def pG:List (Nat×Nat):=[(2,10),(2,34),(4,20),(4,36),(6,14),(6,22),(6,38),(8,10),(8,40),(12,14),(12,28),(12,44),(16,20),(18,22),(18,26),(18,50),(24,26),(24,28),(24,56),(32,34),(32,36),(32,40),(48,50),(48,52),(48,56)]
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
|4,0=>0xae7d077c2a
|5,0=>0xf6ea34f5852440f
|6,0=>0xaaa4e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x2aa22aa22aa22aa25555555544444444aa00aa00aa00aa00444444440000000002a802a802200225555555500000000aaaa0000aaaa000154015401100110028282828282828284444444444444444
|_,_=>0
def sP:Nat→Nat
|0=>0x437104397108437104371064310543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 63 0x7fffffffffffffff
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
|0=>0xf9c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x16
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_46 5 roots_46 ops++addP pm 1 dom_60 4 roots_60 ops++addP pm 2 dzo_46_16 5 roots_46 ops++addP pm 3 dom_42 4 roots_42 ops++addP pm 4 dom_54 4 roots_54 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_62 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_46_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_54 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_46 5 s (0,roots_46.map (·&&&dom_46)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_62 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_46 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
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
theorem lowS_79:Lower true dom_79 roots_79 goal_79 6:=lower_slice_b [(0xcccc000000000000cccc,8,10)] (by decide +kernel) lowS_77
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
theorem lowS_107:Lower true dom_107 roots_107 goal_107 8:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c,8,10)] (by decide +kernel) lowS_105
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_slice_b [(0x220022002200220022002200220022,16,17)] (by decide +kernel) lowS_116
namespace S_158
def pG:List (Nat×Nat):=[(2,10),(2,130),(4,20),(4,132),(6,14),(6,22),(6,134),(8,10),(8,136),(12,14),(12,28),(12,140),(16,20),(16,144),(18,22),(18,26),(18,146),(24,26),(24,28),(24,152),(128,130),(128,132),(128,136),(128,144)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_158.map (·&&&dom_158)
def gM:=goal_158&&&dom_158
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x124b0
|4,0=>0x3dec70b22607559042bb
|5,0=>0x7ad8671c83439753853529d7a1dd2510db10900506480055d3
|6,0=>0x7fdda4c31a2089208b1f
|7,0=>0x7fdda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaa001414141400000000000000000000000000000002aa82aa80000000000000000000000002aa82aa85555555500000000000000000000000050505050a2a2a2a2000000000000000000000000a0a0a0a044004444000000000000000000000000440044002828282800000000000000000000000028282805555555500000000000000000000000055550000aa00aa00000000000000000000000000aa00aa0155555400000000000000000000000000000000022222222000000000000000000000000222222225555555500000000000000000000000000000000aaaa0000000000000000000000000000aaaa000155515550000000000000000000000001540154028282828000000000000000000000000282828285555555500000000000000000000000044444444
|0,1=>0x15555555400000000000000000000000151515152a2a2a2a0000000000000000000000002a2a2a2a5454545400000000000000000000000000000000000022220000000000000000000000000000000001540154000000000000000000000000011001102828282800000000000000000000000028280000055005500000000000000000000000000500050
|_,_=>0
def sP:Nat→Nat
|0=>0xce12906709483384a470cf50948819c2520cf609483384a4a0ce1292630964440ce5890670960478ce1290676148e1b4ec29067584a419c2a20ce549107094c3104a418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682cf15b330654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 23 159 0x7fffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x92095191615091a90407191091292
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x52410000220000001101
|6,0=>0x918171
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0xff591f6d8506100
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x7800400321
|6,0=>0x5696
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_156 5 roots_156 ops++addP pm 1 dom_150 5 roots_150 ops++addP pm 2 dom_138 4 roots_138 ops++addP pm 3 dom_142 5 roots_142 ops++addP pm 4 dom_154 5 roots_154 ops++addP pm 5 dom_148 4 roots_148 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_158 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_148 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_156 5 s (0,roots_156.map (·&&&dom_156)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_158 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_156 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_158==dom_158)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_158 gM v ys):RunD true dom_158 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_158 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_158 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_158 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_158 roots_158 goal_158 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_158
theorem lowS_158:Lower true dom_158 roots_158 goal_158 8:=S_158.noCircuit
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_slice_b [(0xaa000000aa0000000000000000000000aa000000aa,32,33)] (by decide +kernel) lowS_166
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_slice_b [(0xa0a00000a0a000000000000000000000a0a00000a0a,8,9)] (by decide +kernel) lowS_170
theorem lowS_186:Lower true dom_186 roots_186 goal_186 8:=lower_slice_b [(0x50500000505000000000000000000000505000005050000,128,144)] (by decide +kernel) lowS_170
namespace S_233
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(8,9),(8,40),(8,72),(8,136),(32,33),(32,40),(32,96),(32,160),(64,65),(64,72),(64,96),(64,192),(128,129),(128,136),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffff
def xsM:=roots_233.map (·&&&dom_233)
def gM:=goal_233&&&dom_233
def NN:Nat→Nat
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x80eb7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x30300000000000003030000000000000303000000000000030300000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c020200000202000002020000020200000202000002020000020200000202c0c00000c0c000000000000000000000c0c00000c0c00000000000000030300000303000003030000030300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>5
|_,_=>0
def wAt:=mkWire dB 5 234 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_232 7 roots_232 ops++addP pm 1 dom_169 7 roots_169 ops++addP pm 2 dom_225 7 roots_225 ops++addP pm 3 dom_201 7 roots_201 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_233 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_201 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_232 7 s (0,roots_232.map (·&&&dom_232)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_233 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_232 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xffffffff00000000ffffffff00000000,96)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_233==dom_233)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_233 gM v ys):RunD true dom_233 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_233 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_233 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_233 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_233 roots_233 goal_233 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_233
theorem lowS_233:Lower true dom_233 roots_233 goal_233 9:=S_233.noCircuit
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 7:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_59
def isoMvS_94:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 7:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_62
def isoMvS_103:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_47
def isoMvS_109:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 8:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_107
def isoMvS_110:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 7:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_93
def isoMvS_115:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_59
def isoMvS_118:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_59
def isoMvS_121:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 8:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_107
def isoMvS_122:List (Nat×Nat):=[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_59
def isoMvS_124:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 7:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_93
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 6:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_47
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_47
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 7:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_93
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 7:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_93
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_107
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 8:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_107
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_93
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 6:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_117
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 7:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_93
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 8:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_107
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 7:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_93
def isoMvS_199:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 6:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_47
def isoMvS_203:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_107
def isoMvS_205:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 8:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_107
def isoMvS_211:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 8:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_186
def isoMvS_213:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_171
def isoMvS_214:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 8:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_186
def isoMvS_217:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 8:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_171
def isoMvS_220:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 8:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_107
def isoMvS_227:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 8:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_107
def isoMvS_234:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 8:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_171
def dzo_47_16:=0xffff0000ffff0000
def gzo_47_16:=0xfffe0000fefa0000
def gsh_47_16:=0xfffe0000fefa
theorem lowS_zo_47_16_42:Lower true dzo_47_16 roots_47 gzo_47_16 6:=lower_iso_b (d1:=dom_47) (r1:=roots_47) (T1:=gsh_47_16) [(dom_47,16)] (by decide +kernel) (lower_slice_b (T:=gsh_47_16) [(0xaaaa0000aaaa,0,1),(0xf0f00000f0f0,0,4)] (by decide +kernel) lowS_42)
namespace S_63
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,34),(3,11),(3,19),(3,35),(4,20),(4,36),(5,13),(5,21),(5,37),(6,14),(6,22),(6,38),(7,15),(7,23),(7,39),(8,9),(8,10),(8,40),(12,13),(12,14),(12,28),(12,44),(16,17),(16,20),(18,19),(18,22),(18,26),(18,50),(24,25),(24,26),(24,28),(24,56),(32,33),(32,34),(32,36),(32,40),(48,49),(48,50),(48,52),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_63.map (·&&&dom_63)
def gM:=goal_63&&&dom_63
def NN:Nat→Nat
|4=>5
|5=>15
|6=>37
|7=>10
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xf1020923f59089f6129a2d780
|5,0=>0xe2aafdfcf6d9245cdbbcca973bc4f1b08c8a544199818971348e1da428452133316de40ba3d
|6,0=>0xf47e6e62f6ddd8bdd808cf6b2cf246bad5eb52c4b40d5b30d0b17a7a528aa43039c2ed9ba9c96bec91e73908be8e1da888bc84f7c7c4e3785bc758e072b0e692a4664126324a5ce5b5a9d24d95439e342b5df2b4e3241930779704701
|7,0=>0xf8293dd808d42517adc35f7114f362414e64017b29ed429720
|8,0=>0xc6758
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff33ff33ff00ff0000000000ffff000033333333000000003300330033003300ffffffff00000000ff00ff00ff00ff00fefefefefefafefaeeeeeeeeeeaaeeaaffaaffaaaaaaaaaa333333333300330000ff00ffff00ff00ffffffffff00ff00ffff0000ffff0000f0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaa0033003333003300
|0,1=>0xccccccccffccffccffff3333ffff0000ff000000ffff0000cc00cc00ff00ff000000000033003300ffccffccccccccccffffffff33003300ffffffffccccccccffccffccffccffcc00000000ffccffcccccccccccc00cc0000ff00ff0000000000000000ff00ff00ccccccccccccccccff00ff0000000000ffffffffffff0000
|0,2=>0xfff0fff0f0f0f0f000ff0000ffff0000ffffffffffccffcc00cc00ccccccccccffffff00ffff0000ffff00ffffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x48158b0ca09205b1180ca0920440da08164328204d1180d708140a0920561031c24842c32822040c248114b0ca0880c24811440d108118b0ca0811902ca08118b0cf08130b2820463840c204d30b0ca2481031c21830811400c20461440c2040
|1=>0xca0920464042ca0920430920544cb0ca0811902ca0920532e12824812e028248164b0ca09204b0ca09f4812c368a08160b0d72820442ca09204e2c33ca09204b2824813932c31ca09210328248134b78a09204b29d09204b0ca0927012c3282
|2=>0xca09204d2c35ca09204b0ca0920542c32824813102d728248110b0ca0950502ca09204c10b0ca0920440d109204b0ca0950442c35c24812c394a4812ca0920648cb0ca09204b0d709205310b0ca0811842c309204c2c32820622c328204d30b
|3=>0xb0ca0920582c328248110b0ca09204b0ca09205340b2824812c329109204b28248138b
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a94c8c5e62c314d49ac4762128f546ec31615b09583ec196
|6,0=>0x15e7abbd41e92f4369eb4d9e60d2a691bc71e2af0e7843405df4ef3776b39d9c0eda66a3335d8cec065cbac9d56ea474f325dd22c8b64239f5cece6f7
|7,0=>0x344f9b7ca3e39b0ef816bd3dcded8f657
|8,0=>0x1a96
|_,_=>0
def wAt:=mkWire dB 38 64 0xffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xb492ca4b2a2c34b282c38b4b2924b2b292cb0d2c34b292ca04482ca4b294424b280d1cb282ca8b292ca514a2ca0b2a2cac44b2ca43452ca03512cad1492ca0b294414b282ca43352d2c3532caca372ca51492ca4b282ca4b294414b2854144482ca544d2ca8b2b
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xa30009100063000000cc03000000000000000
|6,0=>0x301002f1002d2acaa1a0a62002519063184800000007c9d2001b26480000172001610000050931448f238400000d1
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xfb7e9ef77dde76dca709c04ca304a02348418051140441003d090200700e0140400400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xc070104228c0000000
|6,0=>0x7119cf41e33018d06000a88533a001112c09936b368007
|7,0=>0x31ad5b77be779
|8,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_62 7 roots_62 ops++addP pm 1 dom_54 4 roots_54 ops++addP pm 2 dom_29 4 roots_29 ops++addP pm 3 dom_59 7 roots_59 ops++addP pm 4 dom_45 5 roots_45 ops++addP pm 5 dom_61 6 roots_61 ops++addP pm 6 dom_31 5 roots_31 ops++addP pm 7 dom_55 5 roots_55 ops++addP pm 8 dzo_47_16 6 roots_47 ops++addP pm 9 dom_47 6 roots_47 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_63 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_47 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_62 7 s (0,roots_62.map (·&&&dom_62)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_63 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_62 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_63 gM v ys):RunD true dom_63 gM v (ori ys):=h
def Z (s:Nat):=barP dom_63 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 37 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 37 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 10 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 0 = true)
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
def dzo_85_2:=0xcc00cc0000000000cc00cc
def gzo_85_2:=0xcc00c80000000000c80000
def gsh_85_2:=0x3300320000000000320000
theorem lowS_zo_85_2_85:Lower true dzo_85_2 roots_85 gzo_85_2 5:=lower_iso_b (d1:=dom_85) (r1:=roots_85) (T1:=gsh_85_2) [(dom_85,2)] (by decide +kernel) (lower_slice_b (T:=gsh_85_2) [] (by decide +kernel) lowS_85)
def dzo_93_2:=0xcccccccc00000000cccccccc
def gzo_93_2:=0xccccccc800000000ccc8cc00
def gsh_93_2:=0x333333320000000033323300
theorem lowS_zo_93_2_85:Lower true dzo_93_2 roots_93 gzo_93_2 6:=lower_iso_b (d1:=dom_93) (r1:=roots_93) (T1:=gsh_93_2) [(dom_93,2)] (by decide +kernel) (lower_slice_b (T:=gsh_93_2) [(0x330033000000000033003300,0,8)] (by decide +kernel) lowS_85)
namespace S_95
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,10),(3,11),(3,19),(3,67),(4,20),(4,68),(5,13),(5,21),(5,69),(6,14),(6,22),(6,70),(7,15),(7,23),(7,71),(8,9),(8,10),(8,72),(12,13),(12,14),(12,28),(12,76),(16,17),(16,20),(16,80),(18,19),(18,22),(18,26),(18,82),(24,25),(24,26),(24,28),(24,88),(64,65),(64,68),(64,72),(64,80),(66,67),(66,70),(66,74),(66,82)]
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
|4,0=>0x44f983d51c01dec
|5,0=>0xdbd85d96cf84b6c814366b55a6667d616d2419c0339792fe2a
|6,0=>0xf8e2df4153d6302c9547c75f0c0be3af52e9323b700976f9fe6f78a654e262b886055f4fe621bd920c6f3
|7,0=>0xfddb0e1246da081bf2a14d1952bb092a996
|8,0=>0xc3264
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f000f000000000f0f00003300ffff0000000033003300ffffffff00000000ccccccccffffff0000000000000000003300330000000000330033000f0f0f0f000000000f0f0000ffffffff0000000000000000ffff000000000000ffff0000ffffffff00000000ff00ff00fffffff000000000f0f0f0f0aaaaaaaa00000000aaaaaaaaffffffff00000000ffff0000ff00ff0000000000ff00ff00f0f0f0f000000000f0f0f0f0cccccccc00000000ccccccccffffffaa00000000aaaaaaaa
|0,1=>0xff00000000000000000000000000000000ffffff00ffffffff000000003300330000ff00ff0000000000ff0000ff00ffff00000000ff00ff0000ff00ff0000000000000000ffff00ff00000000ffff0000ccccffff00000000ccccccccffffffff00000000ffffff000000ffff000000000000ff000000ffff0000000000000000ffffff0000000000ffffff000f0f0f0f000000000f0f0f00555555550000000055555500
|_,_=>0
def sP:Nat→Nat
|0=>0x104a962062b152440c455a6a818825491030954940c412d128188ab4ce48388254a0612c528188304a0e209588184af4a06609528188ae4a06d2a92418825620655a928188204a0e208083304a418820
|1=>0x40c412a5031156940c412a67240c412a503104a9c20e3104a940c4d2a488188254a0612a928188254f788188254c883104a940c45da503104ba4a323104a9220626953740c412a503
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa5055005
|5,0=>0x4563f63963362d62762161b61560f6
|6,0=>0xb96b27ab7a479e69779078978277b77566e76776075975274b7
|7,0=>0xe86e17da7d37cc7c66bf7
|8,0=>0xee6
|_,_=>0
def wAt:=mkWire dB 30 96 0xffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x18742640d1a61a50a542520b42592640d92740d40d4255a518720f4251cd4260a54254611a692440d0cd42618742520d42520b4251874261a540d
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1e2709a26096250922408e2308a2208621080008802
|7,0=>0x261946418c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xffbfbd7d65503f3d2c18160f08060500
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x1227b22639b6460a5
|7,0=>0xcd9eefd
|8,0=>8
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_94 7 roots_94 ops++addP pm 1 dzo_85_2 5 roots_85 ops++addP pm 2 dom_93 7 roots_93 ops++addP pm 3 dom_91 7 roots_91 ops++addP pm 4 dom_79 6 roots_79 ops++addP pm 5 dom_85 5 roots_85 ops++addP pm 6 dzo_93_2 6 roots_93 ops++addP pm 7 dom_31 5 roots_31 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_95 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_85_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_93_2_85 _ g hchk
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
theorem lowS_111:Lower true dom_111 roots_111 goal_111 9:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc,8,10)] (by decide +kernel) lowS_109
theorem lowS_119:Lower true dom_119 roots_119 goal_119 8:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_118
def dzo_81_2:=0xc000c00000000000c000c
def gzo_81_2:=0xc00080000000000080000
def gsh_81_2:=0x300020000000000020000
theorem lowS_zo_81_2_81:Lower true dzo_81_2 roots_81 gzo_81_2 4:=lower_iso_b (d1:=dom_81) (r1:=roots_81) (T1:=gsh_81_2) [(dom_81,2)] (by decide +kernel) (lower_slice_b (T:=gsh_81_2) [] (by decide +kernel) lowS_81)
def dzo_42_16:=0x505000005050000
def gzo_42_16:=0x504000004000000
def gsh_42_16:=0x50400000400
theorem lowS_zo_42_16_42:Lower true dzo_42_16 roots_42 gzo_42_16 4:=lower_iso_b (d1:=dom_42) (r1:=roots_42) (T1:=gsh_42_16) [(dom_42,16)] (by decide +kernel) (lower_slice_b (T:=gsh_42_16) [] (by decide +kernel) lowS_42)
def dzo_89_2:=0xc0c0c0c000000000c0c0c0c
def gzo_89_2:=0xc0c0c08000000000c080c00
def gsh_89_2:=0x30303020000000003020300
theorem lowS_zo_89_2_81:Lower true dzo_89_2 roots_89 gzo_89_2 5:=lower_iso_b (d1:=dom_89) (r1:=roots_89) (T1:=gsh_89_2) [(dom_89,2)] (by decide +kernel) (lower_slice_b (T:=gsh_89_2) [(0x30003000000000003000300,0,8)] (by decide +kernel) lowS_81)
def dzo_121_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_121_2:=0xc0c0c0c0c0c0c080c0c0c0c0c080c00
def gsh_121_2:=0x3030303030303020303030303020300
theorem lowS_zo_121_2_81:Lower true dzo_121_2 roots_121 gzo_121_2 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_2) [(dom_121,2)] (by decide +kernel) (lower_slice_b (T:=gsh_121_2) [(0x3000300030003000300030003000300,0,8),(0x3030303000000000303030300000000,0,32)] (by decide +kernel) lowS_81)
def dzo_107_16:=0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16:=0xf0f00000f0f00000f0e00000e0a0000
def gsh_107_16:=0xf0f00000f0f00000f0e00000e0a
theorem lowS_zo_107_16_42:Lower true dzo_107_16 roots_107 gzo_107_16 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_16) [(dom_107,16)] (by decide +kernel) (lower_slice_b (T:=gsh_107_16) [(0xa0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_113_2:=0xc000c000c000c000c000c000c000c
def gzo_113_2:=0xc000c000c0008000c000c00080000
def gsh_113_2:=0x30003000300020003000300020000
theorem lowS_zo_113_2_81:Lower true dzo_113_2 roots_113 gzo_113_2 5:=lower_iso_b (d1:=dom_113) (r1:=roots_113) (T1:=gsh_113_2) [(dom_113,2)] (by decide +kernel) (lower_slice_b (T:=gsh_113_2) [(0x30003000000000003000300000000,0,32)] (by decide +kernel) lowS_81)
def dzo_106_16:=0x5050000050500000505000005050000
def gzo_106_16:=0x5050000050500000504000004000000
def gsh_106_16:=0x505000005050000050400000400
theorem lowS_zo_106_16_42:Lower true dzo_106_16 roots_106 gzo_106_16 5:=lower_iso_b (d1:=dom_106) (r1:=roots_106) (T1:=gsh_106_16) [(dom_106,16)] (by decide +kernel) (lower_slice_b (T:=gsh_106_16) [(0x505000005050000000000000000,0,64)] (by decide +kernel) lowS_42)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,10),(2,34),(3,11),(3,19),(3,35),(3,67),(8,9),(8,10),(8,40),(8,72),(16,17),(16,80),(18,19),(18,26),(18,50),(18,82),(24,25),(24,26),(24,56),(24,88),(32,33),(32,34),(32,40),(32,96),(48,49),(48,50),(48,56),(48,112),(64,65),(64,72),(64,80),(64,96),(66,67),(66,74),(66,82),(66,98)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|4=>3
|5=>12
|6=>20
|7=>13
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xe219c21e2d114b1
|5,0=>0x5b1e258fcd58e995838c56ce83a7983390d2d74c1d42312494117ce091b3
|6,0=>0x682be5e77543d25436d239f503833437db4274b61ddb31dd37174021667d107f50fa5b0d1770c09c0acad05d3a03dca024bd
|7,0=>0x52ca74f6444643a446b5424f32e1d02cd92224591fafa16fdc1489e0ca2c001c7
|8,0=>0x47c680e7a107721
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f000f000f000f0000000000f0f0f0f000000000f000f00f0f0f0f000000000f0f0f0f00000000f000f000f000f000f000f000f000f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a3030f0f03000f0f03030b0b03000b0af0f0f0f0f0f0f0f0000000000000000f0f0f0f0f000f000f0f0f0f0f000f00f0a0f0a0f0a0f0a0f0a0f0a00000000f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f00000000f0f00000f0f00000f0f00000f0f0000f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0a0a0a0a0f000f000a000a00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
|0,1=>0xf0a0f0a000000000f0a0f0af0f0f0f0f0f0f0f000000000f0a0f0af0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a000000000000000000f000f000a000a5050505050505050500050005000500f0f0f0f0f0f0f000f0f0f0f0f0f0f0050505050505050505050505000000000000000000000000b0b0b0b0b0a0b0af0f0f0f0f0f0f0f0303030303000300f0f0f0f0f000f0f0f0f0f0f0f000f0a30303030300030003030303030003000000f0f00000f0f00000a0a00000a0af0f0f0f0f0a0f0a0f0f0f0f0f0a0f0af0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e
|0,2=>0xe0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0ae0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e00f000f000f000f000f000f000a000af0f0f000f0f0f000f0f0f000f0f0f0000000000f0f0f00000000000f0f0f00
|_,_=>0
def sP:Nat→Nat
|0=>0x70a6cc0c22c02073c308020c0cb00a68810c0cb00a65810b00a2070cb00a5c84440ce00a3032d62883032c529550c2c028830b29348844c0ce0053c40cb40c0c638028f10308e00710308014c0c20053470c600a20c2ca2481c31801440c2040
|1=>0x70a20f1032c028860c2c02883032c02992073030802883cc84b00a20f30338b00594c0cb0052873c32c01483032c100a21d10e2c02a43032c02883032c529320c0cb29520430308e00a6cf3032e320c0cb00a88830200a8083032c029e21d10b
|2=>0x3032c02883032c014a20c0cb8ca2043032c02883032ca4c83cc0ce2c028810c0cb70a1cc0cb0052883032e628844c0c22c028894c0cb00a20c84b
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x283129888c3e61c30c985aa27610b06d82ac0f6
|6,0=>0x6a3b35d8cebf75cb2c9d56ea564f3a5dd20e8a641b9f94eee71635398dcbac567
|7,0=>0x12e6934481a31112685440ddfacf677833a5dc4edb7
|8,0=>0x505e76d347
|9,0=>0x1486
|_,_=>0
def wAt:=mkWire dB 39 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2884b3120a4f3830a4b2120b433120c471530b4a2100788292cc53210078b3100a4f2130a5b2f10a4c2128b61330cb487d08cca2d308433100844293084c2930b4a2d38acb21308431d30b4b3110acc2108c4a2d1ca4c2d20a4a3120c401520a42102ca4c212cc4a21288440820c4a2d
|1=>0x2884029308401e2cc4c292c840213084c2d288632300a423128b442d20c432d0084a3120c431d2cc4e2b2c84c2d28b432d28c4a211c84c2d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x2040000000000034c4a06300010818803
|6,0=>0x842fcde93a36e6d0d89ae3000acd41a534467cce91a3000608a9923
|7,0=>0x5b2b255caa9532a253ca694b29251ca29432
|8,0=>0x17c6f0dd1
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x8047f840235c2001a00e5cdf040c4b82022000d00be04484f01feef80b817c007b3e002897000d6f8006a7c00212c0008df000457800225c0010bc0008080003c50000324000180000068000024000011000008400001800000a0000038000010000000
|1=>0x60020ae00115e8028d323642f911237c40517e2008d7
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1000000042c3008042
|6,0=>0x1cc21058a6911dd25825718f005646
|7,0=>0x1b3557d39a17248e0962
|8,0=>0x1e494
|9,0=>0xe
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 8 roots_121 ops++addP pm 1 dom_91 7 roots_91 ops++addP pm 2 dom_115 7 roots_115 ops++addP pm 3 dzo_81_2 4 roots_81 ops++addP pm 4 dom_59 7 roots_59 ops++addP pm 5 dom_81 4 roots_81 ops++addP pm 6 dzo_42_16 4 roots_42 ops++addP pm 7 dom_107 8 roots_107 ops++addP pm 8 dzo_89_2 5 roots_89 ops++addP pm 9 dom_120 5 roots_120 ops++addP pm 10 dom_57 5 roots_57 ops++addP pm 11 dom_122 7 roots_122 ops++addP pm 12 dzo_121_2 6 roots_121 ops++addP pm 13 dom_27 4 roots_27 ops++addP pm 14 dzo_107_16 6 roots_107 ops++addP pm 15 dom_75 5 roots_75 ops++addP pm 16 dom_105 7 roots_105 ops++addP pm 17 dzo_43_16 5 roots_43 ops++addP pm 18 dom_99 5 roots_99 ops++addP pm 19 dzo_113_2 5 roots_113 ops++addP pm 20 dom_42 4 roots_42 ops++addP pm 21 dom_51 4 roots_51 ops++addP pm 22 dzo_106_16 5 roots_106 ops++addP pm 23 dom_90 4 roots_90 ops++addP pm 24 dom_114 4 roots_114 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_81_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_42_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_89_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_121_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_107_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_43_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_113_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_106_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_114 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 8 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 20 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 20 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 13 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 13 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
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
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(4,20),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(8,9),(8,40),(8,72),(12,13),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,56),(24,88),(32,33),(32,36),(32,40),(32,96),(48,49),(48,52),(48,56),(48,112),(64,65),(64,68),(64,72),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|4=>21
|5=>61
|6=>70
|7=>45
|8=>10
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xd65bdc72d3b9f597f3c27c9be6b11c57cc24df834b2cd434c7301172f7ee2d92d26cc126aac22ff716e0514aad0bfda0802404165
|5,0=>0xd996dd6582d0d5ad0b4cd0b45beb46bc504b82e8b14eb95bb894b3589c548941083d457f8f876c2c711676d49a69644651e9639185e65e5a856544355035b4fa8348f7d48d3645cd445bf844a01441fe40f143db8b3babf3b7d039710372f136148344623108f2c35c29de2262cd1f4791cf031cefd188bb17778151b512009118990f3670cfce0869e056ed04a68042bf02d3a01d5b0046f
|6,0=>0xff7f0f50add2990ccf5ac8b2bbfafdbef0ab837dafd8fae7fa9fdff97b7993bab901958d7ca8cc468aa52862e482cde805157d40b7cfdd77cf573b467345772c746d39d6c8d66939c66b0064cfd641c663c58638dd622a06102a5e5d05df575c88a5b5f459b8959517506274eb424abf140de63fc003a4913786336f1e3584e3545631d073186f312802cfd72c7472a1e328b9c26c6d2524923166211d01a31119e7b17bda16faf0cce00bde803cc3
|7,0=>0xca6a8c6757c19e3bfefebc7afbbfada95cca8aa3984d193a478e6608e098894b287a52874a584d1283a7c78c4a689cc5fceb5e2c95d3c55545f4965848ece3dc6e394822a856274a4268b6255c124ed422f26158a11499b133ac11e8311c1e1099d0bf980bc5c07eb303c220377e01a5b
|8,0=>0xf3b5cf353be22acc6757b324d74b3a642d233280213f10f7ba
|9,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccc000000000000c8c80000000333333330000000033332222cccccccccccccccc888888888888888b3330000333300003333000033330000cccccccc00000000cccccccc000000033333333333333333333333322222222c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c80330033003300330033003300220022cccccccccccc0000cccccccccccc00033333333222222223333333322222222c8c8c8c8c8c8c8c8c8c8c8c8c8c800033333333323232323333333332323232cc00cc00cc00cc00cc00cc00cc00cc0333333333333000032323232323200008888888888888888888888888888888b3333333333333330000000000000000
|0,1=>0xcccccccc8888cccccccccccc8888888b3333333333333333333333333330000ccccccccccccccc0c0c0c0c0c0c0c0c333333323333333233330000333300000000000000000000ccccccccc8c8c8cb3333333333333333232323232323232cccccccccccccccccccccccc000000023232323232323232222222222222222ccccccccccc8ccc8cccccccc000000033333333333333223300330033003300cccccccccccccc00cccccccc000000033333333333333333300330033003300ccccccccccccc8c8cccc0000cccc00033333333333233323300330033003300cccccccccccc8888cccccccc000000030303030303030303030303030303030
|0,2=>0x444444444444444444444444444400022222222222233332222222222222222cc04cc04cc04cc04cc00cc00cc00cc0110011001100110011001100110011000000cccc0000cccc0000ccc80000ccc8101010101010101000000000000000000cc00cc00cc00cc00cc00cc00c800c9111111111111111111111111010101088cc88cc88cc88cc88c888c888c888cb332333233323332222222222222222200cc00cc00cc00cc00cc00cc00cc00000000000330033000000000033003300cccccccccccc8888cccccccccccc888b3333333333322220000000000000000cccccccccccccc88888888888888888a3232323232323232323232322222222
|0,3=>0x888c888c888c888c888888888888888a22222222323232322222222222222220000000000000000cccccccccccc888b3333333333333333333333332323232ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc83030303030303030303030303030000cccccccc0000cccccccccccc000000003030303030301010303030303030000444444444444444444444444444444033333333333333000000000000000000ccccccccc8c8c8c800000000000000001010101010101010101010100000000000000000000cccc000000000000cc033333333000033333333333300003300000000000000cccc00000000000000033333333000033333333333300003232
|0,4=>0xcccccccc44444444cccccccc000000000000000333333330000000033003300444444444444444444004400440044000330033003300330000000000000000c8ccc8ccc8ccc8ccc8c8c8c8c8c8c8c80000000333333330000000000000000c8c8c8c8ccccccccc8c8c8c8c8c8c8c80003333000033330000333300003232ccccccccccccc8c8c0c0c0c0c0c0c0c03030303030300030303030303030000cccccccccccccc00cccccccccccccc00000000033333333000000003333330000000000cc00cccc00000000cc00cc033333333000033333333333300002222040404040404040404040404040400000000000000000003333333333333300
|0,5=>0xcc88cc88cc88cc88cc88cc88cc88cc8b3333333010101013333333300000000cccccccccccccccccc88cc88cc88cc8b333333333333232333333333333323288cc88cc88cc88cc8888888888888888001000100010001000000000000000000000000cccccccc00000000c8c8c8cb3333333333333333333333333003300cc00cc00cc00cccccc00cc00cc00cc011111111111111111111111100000000cccccccccccccccc44004400440044000000000000000003332333233323332cccccccccccccccccccccccccccccc033333333333333333333333333332222cccccccccc00cc00cccccccccc00cc011111111111111110000000000000000
|0,6=>0x444444440000000000000003333333333333333000000003300330000000000cccccccc0000000088888888011001100110011000000000000000088cc88cc88cc88cc00000000000000000220022002200222222222222222222cccccc00cccccc00cccc0000cccc0003333333300330033333333330000000000cc00cc00cc00cc00cc00cc00000003300330033333333330033003300330000cc00cc00cc00cc00c800c800c800cb3003300330033000000000000000000cccccccccc00cc00cccccccc00000000000000000000000330033003300330000cc00cc00cc00cccc00cc00cc00cc000000000010101010000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x80cd01001c8014a90007360c481001cc832005107320c8210e0c4a0001cf831200f0b067408b260cd0116701891a1cd831234b8c0668087320c4982e30a09021c5962034395284008b260c48d16309091a1c8832034303123c00706247000e2c1851a1c509100038606140040608080
|1=>0x2a8f0b06400b6323018902d43831205a00142c609100038606684800ec8190020038606406b1602c189020038606417800e181905c0058c5a25600160c481560038a062400b380c481001c303120150b18240a9002c60312a00071464189002c603129c0230e64189002c6031298007
|2=>0x6400800e2c1818202007320c80116301897e0058c06680b50ee4189020038b064108016301897c0039906684817a1cc832004219180c48d0ef0189020038b06257001631d94123438302e92000ee41901a0439f06400803c1c303203439920044000e2c181700038b0641b800e64189
|3=>0x1ca0320067008a1c5942004007160c80100d858c06406cd002c603962408016301c9120400b06240c8001cc83123458c24240800e641891a0039106400800e2c185020038b071c0800e2c1818c0038b28400b6467858320343860605d000e6419002d838320062000e0c80186003c2
|4=>0x280c48d001c190035800a1630189001858c062402a0e181901a0058c0626a801632a03120400a322c603120058c06266803c1c5832006807720c801001ca100290004163019a0200d8b180c4810144c8c28400d30e2c1900202907160c8010144c8c28400800f3c1900200f07160c481
|5=>0x1630189b60058c0624080b41c5832005980322c610022000b180c481b20038406240800f60c832004019163018902a838b06246800e2eb832004007320c80d022c6031205a00163018958015070c0c4800e641901a0400b18501901b3430b180cd09002c614062468a16301891a0058c
|6=>0x22858c20044001633090022c60312040601631d8312340453c2c190020039906400d03c1c58302e80230e64190020038b0640080441c58302e800b197ca109a02f0b180c481006458c06684811632e83213400b180c48d982c6033425600b81c583120400b1840088008c38b0640680
|7=>0xa08c38b064008017a4190020340b180c801001c583120400b180c801ce0058c280c801a02c65d0640681002c65f28400801633303200400b180c80d033058c280c8019a0058c06246801632e83200400b1853090022c60312072800c646032034319180c80d001c583120402ac630a10
|8=>0x3424080163019003b80061630189006458c0640681002c60320340ca1630189020150616301901a0058c760c481002c60320076801630a10029004f1630190020058cba50190020058c0640080d82c603200406b1630190d40058c0624080981c5940640080c630190020038b0640080
|9=>0x322c603200400b180c801012858c06400ac014458c06400800c2c603200400a1630190020058c280c801006458c280c801146458c0640080163019003340191630a03200400b1988801986458c06240800e0c801480058c0640080df44c8c06400801630a100390c8b180c80d022c603
|10=>0x1630190020058c0640080c82c603200404c16301e2200400b1850190020058c0624080
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x6450bea16942aa8505096a119420a83c506ea0c9416a8285046a07940ca814501ea029402a8005
|5,0=>0x1cf6394a7118df31b86364c6b18d331a06334c6518c731886304c5f18bb317062d4c5918af315862a4c5318a331406274c4d189731286244c47188b31106214c41187f30f861e4c3b187330e061b4c35186730c86184c2f185b30b15156c29584fb0996126c235843b08160f6c1d5837b0696
|6,0=>0x6f0edcd5b63b6576bced619a8bb4a7686ecf599b3b2f7650ec85d8db314761aec1d9803afa65e6ebb1d72bade75b0cb45d653ac4657aeadd9583aa97548aa75d4b3a8f7512ca09d3dba7564dec9a1d31325c64aae939d2432417476c8d59173a277442c869d09ba0c740cc7fdcfc39f173d4e78dcee39d57
|6,1=>0x1cfb3987724ce2ddc23b7f5
|7,0=>0x4d6799ef321e6044b9796312ada523c9e692ef241e45348378f8f1d5e37b46788c0f165e293c4b7888f0f5e1b3c2e884ef081e0d34137818f0199ffbbf877e4cfaddf2b3de77aeef3e1e43bc17774eeca1d633a57
|8,0=>0x28dbd147a1af419e8034f979e4f3ade723cdd7
|9,0=>0x5226
|_,_=>0
def wAt:=mkWire dB 112 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1741020202410e01182d1652182d06010e0d06018a00061d182d020128070601133120050602132920051602182d16013c240e01182d0e010201182d8a001a1f080016311601342d12012005120d06010e020e0116310201080020051601163116cd0e52060116351631120216312005200516010803460032270e0216311601
|1=>0x160516312005182d160102012807060116051201200502012005060102410201020120050601182d32071601163502012005120220051631022d020102415801060776030625200532051601025220050601182d16c50e02182d160e182d060112012005080316251601062d06010e51182d06014601021d182d062d06011631
|2=>0x61d0e01182d02021601182d207a0e01182d1601182d4600021d182d207a0e01182d2807060116a91202120116012005ba07280506012005020106020607120120050e251631140f320516010201033120050602140f3205166a12012005182d162520051601182d1202200516310201200506c50e0202011601182d12022005
|3=>0x2020601be020605580206070393060020050602182d060117910600182d0202021d182d199106001731060216312005320f1601020206011a0d0201060506010729160202010602280706010201200528050601299306010600066a12011601022d02011605020116011202163120050601179106001601c531060306020201
|4=>0x6000602060306012005160116020607062d16053205160107310602160106013205160128070601160106010603060216012005062f182d0c021605160d16010601060002011601120120054801062f16052005020116010201160212022005022d0201062520051a2f0201062f06011741
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x1880840000000000000000000000000000000000000000000000000008000000
|5,0=>0x50400012980000000001118000422000000080400000000007c400000000007840001d10d1800030400000005c428600000000000000000910000222101069800000000000000000000b2000020c00000000000000c400000000000a2041
|6,0=>0x620b04c000c015e9ae8d6e6b52591abcd5a4ab2541a94d4469f34e9268d3229630000001284913471a309144873429208c0008023e99e8cf047533919c08da66a33399948c465f32e9168cae6561299940c9c44c2249918c8664121f18ecc7063621998c0c5a62a3
|6,1=>0x1a66d12671b2cd906c53
|7,0=>0x12d29594a4a4e5252919484a3e51d28d9464a2e5152899444a1e50d2859424a0e50528194049fe4fe17e13e89f04f627a13c89e04ee27613a89d04e627213889c04de26e13689b04d62
|8,0=>0x27033719b0cd46683331990cc466032f1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 13
def pmP:Nat→Nat
|0=>0x1100002000003d3800680000c00000f0c001c18002800004000007bc000f38001af0003420004e00008c0001080002000002c00004400008000008c000108000180000220000400000400000400000400000600000800000800000
|1=>0x100500200804400908601e30c035e1406bc280d18403a708058610078c200de8401ad08034e100600200800400a3080100080708100d38201670402840802101004082000502375e040ebc081818101a5020202020c00038040013ef
|2=>0x8a034314048e200d7c401a788014f1002122001742008482034f040696080d0c10100820151040002001d2c001a580014f00020200014c000084c034698060128190a501a3480706900601100f3a201c2400f0e400200800060c0000
|3=>0xca024794040320092e101a3c0040b4006be300574581a58a074714069e280d2c501a3
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x4080000000000000000000000000010000
|5,0=>0x60002000003000b8000080000014000001800510006800008c0000000001e002050e00000000000b00400001400d800000f17
|6,0=>0x120c6cc8824089004146ddf1c32f670c22a2ccd424cdb0000078e4f487941f1c04c4119792caaed435840d5384ba7c0939c79fbc0c1b166fea224aa4489
|7,0=>0x45c3ae25cd585d5167aeb4b6b40b4a6cd1e665ba59aa677efddc785c1dc981368b762de0b769dad
|8,0=>0x30e2c388a487356b95
|9,0=>0x13
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 8 roots_121 ops++addP pm 1 dom_84 4 roots_84 ops++addP pm 2 dom_116 5 roots_116 ops++addP pm 3 dom_120 5 roots_120 ops++addP pm 4 dom_57 5 roots_57 ops++addP pm 5 dom_109 8 roots_109 ops++addP pm 6 dom_92 5 roots_92 ops++addP pm 7 dom_124 7 roots_124 ops++addP pm 8 dom_93 7 roots_93 ops++addP pm 9 dom_77 5 roots_77 ops++addP pm 10 dom_108 5 roots_108 ops++addP pm 11 dom_89 5 roots_89 ops++addP pm 12 dom_105 7 roots_105 ops++addP pm 13 dom_73 4 roots_73 ops++addP pm 14 dom_104 4 roots_104 ops++addP pm 15 dom_101 5 roots_101 ops++addP pm 16 dom_85 5 roots_85 ops++addP pm 17 dom_60 4 roots_60 ops++addP pm 18 dom_61 6 roots_61 ops++addP pm 19 dom_45 5 roots_45 ops++addP pm 20 dom_113 5 roots_113 ops++addP pm 21 dom_29 4 roots_29 ops++addP pm 22 dom_117 6 roots_117 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_117 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 8 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_125==dom_125)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 21 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 61 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 61 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 70 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 70 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 45 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 45 0 = true)
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
def dzo_84_2:=0x4400440000000000440044
def gzo_84_2:=0x4400400000000000400000
def gsh_84_2:=0x1100100000000000100000
theorem lowS_zo_84_2_84:Lower true dzo_84_2 roots_84 gzo_84_2 4:=lower_iso_b (d1:=dom_84) (r1:=roots_84) (T1:=gsh_84_2) [(dom_84,2)] (by decide +kernel) (lower_slice_b (T:=gsh_84_2) [] (by decide +kernel) lowS_84)
def dzo_116_2:=0x440044004400440044004400440044
def gzo_116_2:=0x440044004400400044004400400000
def gsh_116_2:=0x110011001100100011001100100000
theorem lowS_zo_116_2_84:Lower true dzo_116_2 roots_116 gzo_116_2 5:=lower_iso_b (d1:=dom_116) (r1:=roots_116) (T1:=gsh_116_2) [(dom_116,2)] (by decide +kernel) (lower_slice_b (T:=gsh_116_2) [(0x110011000000000011001100000000,0,32)] (by decide +kernel) lowS_84)
def dzo_124_2:=0x44444444444444444444444444444444
def gzo_124_2:=0x44444444444444404444444444404400
def gsh_124_2:=0x11111111111111101111111111101100
theorem lowS_zo_124_2_84:Lower true dzo_124_2 roots_124 gzo_124_2 6:=lower_iso_b (d1:=dom_124) (r1:=roots_124) (T1:=gsh_124_2) [(dom_124,2)] (by decide +kernel) (lower_slice_b (T:=gsh_124_2) [(0x11001100110011001100110011001100,0,8),(0x11111111000000001111111100000000,0,32)] (by decide +kernel) lowS_84)
def dzo_110_16:=0x55550000555500005555000055550000
def gzo_110_16:=0x55550000555500005554000054500000
def gsh_110_16:=0x5555000055550000555400005450
theorem lowS_zo_110_16_42:Lower true dzo_110_16 roots_110 gzo_110_16 6:=lower_iso_b (d1:=dom_110) (r1:=roots_110) (T1:=gsh_110_16) [(dom_110,16)] (by decide +kernel) (lower_slice_b (T:=gsh_110_16) [(0x5050000050500000505000005050,0,4),(0x5555000055550000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_92_2:=0x444444440000000044444444
def gzo_92_2:=0x444444400000000044404400
def gsh_92_2:=0x111111100000000011101100
theorem lowS_zo_92_2_84:Lower true dzo_92_2 roots_92 gzo_92_2 5:=lower_iso_b (d1:=dom_92) (r1:=roots_92) (T1:=gsh_92_2) [(dom_92,2)] (by decide +kernel) (lower_slice_b (T:=gsh_92_2) [(0x110011000000000011001100,0,8)] (by decide +kernel) lowS_84)
namespace S_126
def pG:List (Nat×Nat):=[(2,10),(2,34),(4,20),(4,36),(4,68),(6,14),(6,22),(6,38),(6,70),(8,10),(8,40),(8,72),(12,14),(12,28),(12,44),(12,76),(16,20),(16,80),(18,22),(18,26),(18,50),(18,82),(24,26),(24,28),(24,56),(24,88),(32,34),(32,36),(32,40),(32,96),(48,50),(48,52),(48,56),(48,112),(64,68),(64,72),(64,80),(64,96),(66,70),(66,74),(66,82),(66,98)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_126.map (·&&&dom_126)
def gM:=goal_126&&&dom_126
def NN:Nat→Nat
|4=>7
|5=>18
|6=>46
|7=>36
|8=>12
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xfbfeae71649af9b7b12b6de3e6b33a40411
|5,0=>0xd3025a1d258e7d287ac3720c4672595c64154c174a3ab43bff355253332b27f6623a7912bb80ec980bcca0a366
|6,0=>0xf00e6cbb4fc4027c182bc0485b3187a609e92e448c3718317b78d60782f6773bf76327752bd719296a65a69d88639b25eafe58382580fb4f24c4ea094e1f6490ff4188e3e2943a0b536bbd330883257731e4d29cba298782730b21756215c4213e61f68e131a30bbf008c000849407c7801427
|7,0=>0xe3f4fd5098c7121bbb66bb86ab4028b20bda11e1a0507974c0912b18bf7389f058110c80d1e79d20764a97627868f2a53fbe4c2f8446174206241a9d41695358d8357e231b6d265581dad31adc20cb1b0c9350a0c308e6e080d4
|8,0=>0xe9649e6db0a14c27e99549279464f44457d38cc63188f25b0e0ef6800935
|9,0=>0x464f4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaa00aa00aaaaaaaaaa00aa0000015554000155540001515000015142aaaaaaaaaaa80002aaaaaaaa8280000505050505050505050505050505050502222222222002200222222222200220155555555555555540000000000000002aaaaaaaa82828282aaaaaaaa828282855505550555055505550555000000000aaaaaaaaaaaaaaaaaa00aa00aa00aa0111111111111111111111111111111112a802a802a802a802a802a802a802a8055555555000000005555555500000000aaaa0000aaaa0000aaaa0000aaaa000155415541554155415541554155415542aaaaaaaaaaaaaaaa82828282828282855555555555555554444444444004400
|0,1=>0xaa00aa00aa00aa00aaaaaaaaaaa0aaa001540154015401540154015400000002aaaaaaaaaaaaaaaaaaaaaaaaaa82aa805050505050505050500050005000500aaaaaaaaaaa0aaa0aaaaaaaaaaa0aaa00154015401400140015401540140014002a802a802a8000002a802a8028000000005555000055550000505000005050aaaaaaaaaaaaaaaa888888888888888814141414141414141414141400000002222222222002200222222222200220055550000555500005050000050500000aaaaaaaaaaaaaaaaaaa0aaa0aaa0aaa155555555555555555555555400000002aaaaaaaa82828282a802a802800280055555555555555555454545454505450
|0,2=>0xa0a0a0a000000000a000a0000000000000000000000000155415542a82aa82aa82aa82aa82aa82aa802a80555555555555555511111111110011000000000000000000aaaaaaaaa0a0a0a155555555555555540000000155415542aaaaaaaaaaaaaaaaaaa80002aaa800055555555555555550055005500500050000a000a000a000a000a000a0000000155554141555541415555414155554142aaaaaaaaaaa80002aaaaaaaaaaa8000555555555555555555555555550055000000000000000000aaaaaaaaaaa0aaa00000000155415540000000015541554002a802a802a802a802a802a8028002855555555555555555555555550505050
|0,3=>0x2aaaaa802aaaaa802aaaaa802aaaaa805555444455554444555544445555444400000000000000008888888888888888141414141414141410101010101010100000000000000002aa82aa82aa82aa80000000055555555000000005500550000000000aaaa000000000000aaaa000001540154015400000154015401540002aaaaaaaaaaaaa802aaaaaaaaaaaaa8055555555444444445555555544444444
|_,_=>0
def sP:Nat→Nat
|0=>0x1413006d20c73062520c21c648314119a34530664a10530b60a4831513062520c55d61031503001032073063c409418a1032050461053142ca10308c00d10214628f4834cc1920c244610309000f0c804610530038d14c2ca2432071840c2040
|1=>0x1cc1a228f4831cc1840c23152840c730678a9644853062a310314c18a1031411a22840c530684a10314c00a1031513062a010314658a7c40c530629210314c5d63d20cc19e29d10314c18a4840c530670f48308c18a10309118a3d20c2046103
|2=>0xc20462ab10308518a10314c1aa28f10531418a9521c53061290c530b2a548531710314c1a82840c504c2ca6c40c73062840c53069ca1260c530b29b10314118a3453062a410308c18a2440c21c62921031cc19e10314119a292103087306103
|3=>0xd308530629b10314c18a1030850462840c530668ac04a4314c18a3c40c730629b2440c530628910308518a3d20c504c1840c5306bca10314c1ae2a52421462894831c53061034c714c5c40ed14c18a4840d314c1840c532c2840c814c18a3c4
|4=>0x2a010314c18a10314c1b62921030853062841c5306cca103d453062840c5306d0a105317cca1031c531794414c1b22921031413069441c53062840c214c5cac440c530629210314c1962a51053172a41031c530628414c1982a04840c5306284
|5=>0x31718a1390c53062840c53062840c504c18a1260c530628910314c18a1380c53062840c53372b010314c18a105337cca3c4a4314c18a3c40c504c18a4840c714c18f1260c53062840c53152840c214cdca10314c1962a54853062891031c5306
|6=>0x40c53062840c214c18a4840c53062840c53172840c5
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x1e5065414503d40a50154005
|5,0=>0x22188261f187661c186a619185e61618526131846610183a60d182f50a58236
|6,0=>0x6fddb876c5dab6691d9d7659d8f762598275edd7475b5d667581959755154d7519d3f74e1d3174a9d255479d177441d097409cfb73d58ef63a1ce17369cd37331cc662fdcb872c5caa728dc9c7255c8e7
|7,0=>0xb01ab88ac22a97a8629b6a51e8d7a1da7f89e1e7179a6262796de547939a486905e3a78cde2c7895e1d885da0f8825a0187e61f277adde477721d577361c67
|8,0=>0xc41f097c0dafc7bd5eef6ba1ee17b69ed37b35ac67
|9,0=>0x3176
|_,_=>0
def wAt:=mkWire dB 58 127 0x7fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x30a52152845217284421314c4a151444a1118f0511305471128443116cac40a14c552918f05112470529304492924ad23310a4629485ca11482473314a4c291444f3114454110c10c292470529304552918f05114820531144520814c4c1554a463c14454110c10c291cc4a151444511
|1=>0x10346291c445290c18c2948c442908a45310844c1530a4531245cc110ca461114445292454c113044c1530a440d3044c15286452948cc50530a4a2d18f8511482042914c4c2924acc11084c10c28c451110a431114a463e1444629284431118f8511084453118f851110245315044304
|2=>0x53110a462918a450d30a4c0d304431918ac611103862b14443291054c2928445291054c0d18f051118ac53148cc429284431114a4c1124a4c11317862910a45310c4c52908ac5311c4c52910386292864529165831130a44290c4452918a45313c3451148cc429
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11000000000000001
|5,0=>0x1c11b11920000001630001330001030e20d10b2000074043022
|6,0=>0x6710000006430006226115f25c35935815625515234f34d24a30004824620004424223f33d20003b20000003923633333213022f12d20002a32732612512232021f11d2000
|7,0=>0xae2ac2aa2a82a62a42a22a029e29c29a29829629429229028e28c28a28828628428228027e27c27a27827627427227026e26c26a2682
|8,0=>0xba1b91b81b71b61000b51b41b31b21b11b01
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0xbb00002c40000a800002900000940000210000082000020400008000001eb00007a40001e10000780000100000032c0000880000210000082000020000006c000013000004200001000000280000090000020000004000000c00000200000040000008000000
|1=>0x100a0003bbed00e47b40345ed00d07a40329e900c51b00301ed008efa40239e9008bfa40211e90072fd40199e900607a4014bf9004bfa40115ed00407ec009bed00262b0004464001111000202800062e00011f90003fa40006fc00018500004d00001110000404
|2=>0x80ea7a50199e920247ac8080c2122060020a101080a7ac14044c0452fe4114bf104437b4110dcd04427a41042d00266fa40801eb02007a4043be90106fa4041ab801062a00402b0
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x800000001
|5,0=>0x5020c0001a00400140c084004c686
|6,0=>0x28000cc021341d4240a3d00e5649f0012640090644d9820001194e51f9c340c04510a4d0b3a8c397
|7,0=>0x2d45141a5196b87a79e3a3e965c36b1193958be38c7d018aa9d36530a10a44c
|8,0=>0x92d1bb6a855753775534f
|9,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 26 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_124 7 roots_124 ops++addP pm 1 dom_104 4 roots_104 ops++addP pm 2 dzo_42_16 4 roots_42 ops++addP pm 3 dom_62 7 roots_62 ops++addP pm 4 dom_84 4 roots_84 ops++addP pm 5 dom_94 7 roots_94 ops++addP pm 6 dom_122 7 roots_122 ops++addP pm 7 dom_118 7 roots_118 ops++addP pm 8 dom_110 7 roots_110 ops++addP pm 9 dzo_84_2 4 roots_84 ops++addP pm 10 dom_42 4 roots_42 ops++addP pm 11 dzo_116_2 5 roots_116 ops++addP pm 12 dzo_46_16 5 roots_46 ops++addP pm 13 dzo_124_2 6 roots_124 ops++addP pm 14 dom_90 4 roots_90 ops++addP pm 15 dzo_110_16 6 roots_110 ops++addP pm 16 dzo_106_16 5 roots_106 ops++addP pm 17 dzo_92_2 5 roots_92 ops++addP pm 18 dom_54 4 roots_54 ops++addP pm 19 dom_100 4 roots_100 ops++addP pm 20 dom_114 4 roots_114 ops++addP pm 21 dom_92 5 roots_92 ops++addP pm 22 dom_46 5 roots_46 ops++addP pm 23 dom_106 5 roots_106 ops++addP pm 24 dom_102 5 roots_102 ops++addP pm 25 dom_108 5 roots_108 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_126 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_42_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_84_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_116_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_46_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_124_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_110_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_106_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_92_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_100 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_108 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_124 7 s (0,roots_124.map (·&&&dom_124)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_126 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_124 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_126==dom_126)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_126 gM v ys):RunD true dom_126 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_126 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 46 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
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
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_slice_b [(0xaaaaaaaa000000000000000000000000aaaaaaaa,8,9)] (by decide +kernel) lowS_158
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_slice_b [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,8,9)] (by decide +kernel) lowS_174
theorem lowS_183:Lower true dom_183 roots_183 goal_183 8:=lower_slice_b [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_182
def dzo_171_16:=0xf0f00000f0f000000000000000000000f0f00000f0f0000
def gzo_171_16:=0xf0f00000f0f000000000000000000000f0e00000e0a0000
def gsh_171_16:=0xf0f00000f0f000000000000000000000f0e00000e0a
theorem lowS_zo_171_16_42:Lower true dzo_171_16 roots_171 gzo_171_16 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_16) [(dom_171,16)] (by decide +kernel) (lower_slice_b (T:=gsh_171_16) [(0xa0a00000a0a000000000000000000000a0a00000a0a,0,1),(0xf0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
namespace S_187
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,10),(2,34),(2,130),(3,11),(3,19),(3,35),(3,131),(8,9),(8,10),(8,40),(8,136),(16,17),(16,144),(18,19),(18,26),(18,50),(18,146),(24,25),(24,26),(24,56),(24,152),(32,33),(32,34),(32,40),(32,160),(48,49),(48,50),(48,56),(48,176),(128,129),(128,130),(128,136),(128,144),(128,160)]
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
|5,0=>0x4b53d0a8d3
|6,0=>0xd38a6ae7e488f275b9765b3ed312203045f09edb
|7,0=>0xc3cc4bf55c8852f6494852dbc3082822f9a0aba606719
|8,0=>0x6a88837c7026f6b
|9,0=>0x3dbb0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f000000000000000000000f0f0f0f0f0f000000f000f000f00000000000000000000000f000f000f000000000000f0f0f000000000000000000000000000f0f0f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00f0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0f00000f0f000000000000000000000f0f00000f0f0000f000f000f000f0000000000000000000f000f000f000f00f0f0f0f0f0f0f0000000000000000000f0f0f0f0f0f0f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0cf0f0f0f0000000000000000000000000f0f0f0f00000000f0f0f000f0f0f0000000000000000000f0f0f000f0f0f00f0f0f0f0f0f0f0f00000000000000000f000f000f000f00a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a30303030303030300000000000000000303030303000300f0f0f0f0f0f0f0f00000000000000000000000000000000
|0,1=>0xf000f000f000f0000000000000000000f000f00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x524c2020a93080520cc2030aa498407946930805524c2801872a9261016550cc201526138072a869309855244102cea1984552441020e9308072906611caa4882028cc26818520cc2020e3308a418820
|1=>0x5524c201543498407952610165
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x65006
|6,0=>0x3773162b62561f61871260b7
|7,0=>0x7566f66876175a75284b74563e7
|8,0=>0x8878267b7
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 17 188 0xfffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x4815152a57a551548152528d48148151549e28149d2812a54817a751528148128d4812812a548161b28d4815a949528152528148161b49d4812175254a928d4814815a9495281
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0x6095348cf330ca21cc43
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0x1d73cb855ce8e6d73639a140ff66f737999dcae64732308fec4f60ff020004001e000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x20
|6,0=>0x13ce430cae
|7,0=>0xb6d1919c152
|8,0=>0x254f
|9,0=>8
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_186 8 roots_186 ops++addP pm 1 dom_59 7 roots_59 ops++addP pm 2 dom_139 5 roots_139 ops++addP pm 3 dom_163 5 roots_163 ops++addP pm 4 dom_185 8 roots_185 ops++addP pm 5 dom_179 7 roots_179 ops++addP pm 6 dom_155 7 roots_155 ops++addP pm 7 dzo_43_16 5 roots_43 ops++addP pm 8 dom_51 4 roots_51 ops++addP pm 9 dzo_171_16 6 roots_171 ops++addP pm 10 dom_171 8 roots_171 ops++addP pm 11 dom_147 5 roots_147 ops++addP pm 12 dom_27 4 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_187 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_43_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_171_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_186 8 s (0,roots_186.map (·&&&dom_186)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_187 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_186 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
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
namespace S_190
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,130),(4,20),(4,36),(4,132),(6,14),(6,22),(6,38),(6,134),(8,10),(8,40),(8,136),(12,14),(12,28),(12,44),(12,140),(16,20),(16,144),(18,22),(18,26),(18,50),(18,146),(24,26),(24,28),(24,56),(24,152),(32,34),(32,36),(32,40),(32,160),(48,50),(48,52),(48,56),(48,176),(128,130),(128,132),(128,136),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_190.map (·&&&dom_190)
def gM:=goal_190&&&dom_190
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xc7549
|7,0=>0xb27668862485897833ba0724b
|8,0=>0xe260976607
|9,0=>0xf79e0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x15401540154015400000000000000000110011001100112aaaaaaaaaaaaaaa80000000000000002aa22aa22aa22aa2444444444444444400000000000000004444444444444444aa00aa00aa00aa000000000000000000aa00aa00aa00aa01555555555555555400000000000000000000000000000002aaaaaaa8000000000000000000000002aaaaaaa80000000555500005555000000000000000000005555000055550000aa88aa88aa88aa880000000000000000aa88aa88aa88aa8955555555555555540000000000000001540154015401540282828282828282800000000000000002828282828282828555555555555555500000000000000004444444444444444
|_,_=>0
def sP:Nat→Nat
|0=>0x5471865437186542718654718a654971865427108543710654927186543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d5739c68
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 191 0x7fffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1e17641f864d97861976619784a1765e1865d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x1ffe36fe7eff5f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x38467
|8,0=>0x52
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_186 8 roots_186 ops++addP pm 1 dom_188 7 roots_188 ops++addP pm 2 dom_182 7 roots_182 ops++addP pm 3 dom_62 7 roots_62 ops++addP pm 4 dom_158 8 roots_158 ops++addP pm 5 dom_174 8 roots_174 ops++addP pm 6 dom_54 4 roots_54 ops++addP pm 7 dom_60 4 roots_60 ops++addP pm 8 dom_180 5 roots_180 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_190 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_180 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_186 8 s (0,roots_186.map (·&&&dom_186)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_190 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_186 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_190==dom_190)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_190 gM v ys):RunD true dom_190 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_190 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_190 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_190 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_190 roots_190 goal_190 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_190
theorem lowS_190:Lower true dom_190 roots_190 goal_190 10:=S_190.noCircuit
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_slice_b [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,16,17)] (by decide +kernel) lowS_214
namespace S_221
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(4,20),(4,68),(4,132),(5,13),(5,21),(5,69),(5,133),(8,9),(8,72),(8,136),(12,13),(12,28),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(24,25),(24,28),(24,88),(24,152),(64,65),(64,68),(64,72),(64,80),(64,192),(128,129),(128,132),(128,136),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffff
def xsM:=roots_221.map (·&&&dom_221)
def gM:=goal_221&&&dom_221
def NN:Nat→Nat
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xf8f3f
|9,0=>0x7369e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x33330000000000003333000000000000333300000000000033330000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc0303030300000000030303030000000003030303000000000303030308888888800000000888888880000000088888888000000008888888b3333333000000003333333300000000333333330000000000000000cccccccc000000000000000000000000cccccccc00000000000000033333333000000003333333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x6b191ac688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>7
|9,0=>0x76
|_,_=>0
def wAt:=mkWire dB 7 222 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x21
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
addP pm 0 dom_220 8 roots_220 ops++addP pm 1 dom_157 7 roots_157 ops++addP pm 2 dom_93 7 roots_93 ops++addP pm 3 dom_217 8 roots_217 ops++addP pm 4 dom_213 8 roots_213 ops++addP pm 5 dom_205 8 roots_205 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_221 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_205 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_220 8 s (0,roots_220.map (·&&&dom_220)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_221 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_220 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_221==dom_221)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_221 gM v ys):RunD true dom_221 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_221 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_221 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
namespace S_235
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,10),(2,34),(2,130),(3,11),(3,35),(3,67),(3,131),(8,9),(8,10),(8,40),(8,72),(8,136),(32,33),(32,34),(32,40),(32,96),(32,160),(64,65),(64,72),(64,96),(64,192),(66,67),(66,74),(66,98),(66,194),(128,129),(128,130),(128,136),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffff
def xsM:=roots_235.map (·&&&dom_235)
def gM:=goal_235&&&dom_235
def NN:Nat→Nat
|4=>3
|5=>71
|6=>160
|7=>87
|8=>20
|9=>4
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x18d2c11c09101b1
|5,0=>0xcee02c740f8fd4a8ea128774a7d1757bc7c70823698936891067fdd623955f0d05c84b577f75000e4f1b84e92f4d01d4c9e749f8648040438bf3b04d370f03471933de431f6830e382ebc32e9492a2ee280bd2529c23bde236192107120f421c0381a3791a2121908b185f91850e167af15b8e15b54159711441712abb1259c111150fb0e0f0750d3fb0c5620c34e0b7e90977f094a608090072a2068fb05680048290351b03387025960184a0161d00112
|6,0=>0x5c3545b8a95af095aa1f59005557945551051fb451eb6516954f9af49a53469ff45790434214213b41b4840beb3dded3c4f33bc873ba6a3b171393723903e38dea38072370443666935b6435a5434ccc3388f3258a319552fc382f2d52d6c52c8282bb5329dab2885227f4b27a942794626eaf26b4522db022af721e1f219f7217982113f1fe441fabf1f42b1e9f81e7b61d6711d23a1be7b1b6ab1b4b51b15c1ac511a4931a3d719508184211782616ac91690e15c4b156511432213ac7135fd11fc3119f01124e10cf8103400f97e0f8e80f5c70dec40d9c80d2070cf840cc870c9350c5590bfc80b7e90b70b0b5dd0b42d0b4240b3a10ac200abfa0a8320a5c4098a108d210760c072a206733066be0642a057a205408053e404849047fa046ae0444c0408a036d302e6b02db702582024fe0221b01fd30156000dfe005a0
|6,1=>0xddf45bcec2b7765b1524abc3a948488b9998774a83fa482a6b7c8cd74e16738f870c7c6ece46eb586e87d6df1c6c9ad6c13a6966d68b7066f8c6602665ccc6530f6512663ffb626d361dba5ec895eb40
|7,0=>0xddf45a16b1962b284b4682708825fa7ef1a70dc06fcce6ccc168390648005d0e95bc1d52d6b4fdb44ef744bbbc4959a4792c462984382d420dd3bdc93a23e3979138de738c9e3842133a50336b733163330ac329a93202e3168e314003086a304a42f8f22ee2f2d2592d1382b7f32a2a729ed0291aa2915a283622717c23a0b2374722e8322c7b21cea1e25a1dae91b3d418d08185fc1688915c4e13e13121a7113360fd140f58c0e3f10e2490de7b0d3e70c7bb0c5ba0b3d208827083e40838407453055be047280443703f0902eb8020a900ffe00e050065a
|8,0=>0xa2b7e77bdf63b5961f5d5de5e5aa7e56565424ee3fd043891e386903033021abc190201439c1342612f3c12e870979903e38
|9,0=>0x7ccdc51d3d0ee3d040d9
|10,0=>0xfffda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0000000000000f0f0000000000000f0a0000000000000f0af0f00000f0000000f0f00000f0000000a0a00000a0000000a0a00000a00f0f00000f0f000000000000000000000f0f00000f0f0000000000000000f0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f00f0f00000f0f00000f0f00000f0f00000a0a00000a0a00000a0a00000a0af0000000f0000000f0000000f0000000f0000000f0000000f0000000f00f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0ac0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0cf0f00000f0f00000f0f00000f0000000f0f00000f0f00000a0a00000a00f0f00000f0f00000c0c00000c0c00000f0f00000f0f00000c0c00000c0ca0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00f0000000f0000000f0000000f0000000f0000000f0000000f0000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f00f0f00000f0f00000f0f00000f0f00000000000000000000000000000000
|0,1=>0xf0f00000a0a00000f0f00000a0a00000f0f00000a0a00000f0f00000a0af0f00000f0f00000f0f00000f0f00000f0f00000f0a00000f0f00000f0a0000000000000000b0b00000b0b000000000000000000000b0b00000b0af0f00000f0f00000f0f00000f0f00000f0f00000f0000000f0f00000f0000000000000000003030000030300000000000000000000030300000300f0f00000f0f00000f0f00000f0f00000f0f00000f0f000000000000000000000000000000000000000000000000f0f00000f0a00000f0f00000f0af0f00000f0f00000f0f00000f0f00000f0a00000f0a00000f0a00000f0af0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f005050000050500000505000005050000050500000505000005050000050030300000303000003030000030300000303000003000000030300000300f0f00000f0f00000f0000000f0000000f0f00000f0f00000f0000000f00f0f00000f0f00000f0f00000f0f00000f0f00000a0a00000f0f00000a0ae0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00f0000000f0000000f0000000f0000000f0000000a0000000f0000000a
|0,2=>0xf0f00000f0a00000f0f00000f0a00000f0f00000f0a00000f0f00000f0af0f00000f0f000003030000030300000f0f00000f0f0000030300000300505000005050000010100000101000005050000050500000101000001001010000010100000101000001010000010100000100000001010000010000000000000000000000000000000000505000005000000050500000500f0f00000f0f00000f0f00000f0f00000505000005000000050500000500f0000000f0000000f0000000f0000000f0f00000f0a00000f0f00000f0af0f0000000000000f0f00000f0f00000f0f0000000000000f0f00000f00f0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f0000000030300000303000003030000030300000303000003020000030300000302b0b00000b0b00000b0b00000b0b00000b0b00000b0a00000b0b00000b0af0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0000000000000000000000000000000000f0f00000f0f00000f0f00000f000000000000000000f0f00000f0f000000000000000000000f0f00000f0a0000000000000000000000000000000000f0000000a0000000f0000000af0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00
|0,3=>0xf0000000f0000000f0000000f0000000f0000000f000000000000000010100000101000001010000010100000101000001010000010100000100f0f00000f0f00000f0f00000a0a00000f0a00000f0a00000f0a00000a0a30300000303000003030000030300000303000003030000030300000300f0f00000f0c00000f0f00000f0c00000e0e00000e0c00000e0e00000e0cf0000000f0000000f0000000f0000000f0f00000f0f00000f0f00000f00f0f0000000f00000f0f0000000f00000f0f0000000a00000f0f0000000a0000000000000000f0f00000f0f000000000000000000000f0f00000f00f0f00000f0f00000f0f0000000000000f0000000f0000000f0000000000f0f00000f0f00000f0a00000f0a00000f0f00000f0f00000f0a00000000f0f00000f0f00000f0f00000f0000000f0f00000f0f00000f0f00000f00f0a00000f0a00000f0a00000f0a00000f0a0000000000000f0a00000000f0e00000f0e00000f0e00000f0e00000f0e00000c0c00000f0e00000c0cf0f00000a0a00000f0f00000a0a00000f0000000a0000000f0000000a00f0f00000f0f00000f0f00000a0a00000f0f00000f0f00000f0000000a0050500000505000005050000050500000505000005000000050500000500
|0,4=>0x500000005000000050000000500000005000000000000000500000000a0f00000a0f00000a0f00000a0f00000a0f00000a0a00000a0f00000a0a0000000000000000f0f00000f0f000000000000000000000f0f00000000f0000000f0000000f0f00000f0f00000f0000000f0000000f0f00000f003000000030000000303000003030000030000000300000003030000030000f0000000f0000000f0000000f0000000f000000000000000f000000000000000000000000000000000000000000000000f0f0000000000000f000000000000000000000000000000000000f0000000f0000000f000000000000000000f000000000000000f000000000000000a000000000000000a00000000000000000000000000000000f0f00000f0000000f0f00000f0000000000f0f0000000000000f0f0000000000000f000000000000000f0000000000f0f0000000000000f0f0000000000000f0f000000000000000000f0000000a0000000f0000000a0000000f0000000a0000000f0000000a00000000000000000000000000000000f0a00000f0a00000f0a00000f0af0f0000000000000f0f0000000000000f0f00000f0a00000f0f00000f0a00000000f0f0000000000000f000000000000000f0f0000000000000f00
|0,5=>0xf0000000f0000000f0000000f0000000a0000000a0000000a0000000a00000000f0a0000000000000f0a0000000000000f0a0000000000000f0a0000000000000000f0f00000f0f000000000000000000000f0000000f0000000000000000000000000000000000f0f00000f0f00000f0f0000000000000000000000000000000000000000f0f00000a0a00000f0f00000a0af0f00000f0000000f0f00000f0000000f0f00000f000000000000000000f0f00000f0f00000f0f00000f0f000000000000000000000f0f00000f000000000000000000f0f00000f00000000000000000000000f0f00000f0030300000303000003030000030300000000000000000000030300000300f0500000f0500000f0500000f0500000f0500000f0000000f0500000f0050500000505000005050000050500000505000000000000050500000000f0f0000000000000f0f0000000000000f0f00000f0f00000f0f00000f0000000000505000000000000050500000000000005000000000000000500f0f0000050500000f0f0000050500000f0f0000050000000f0f0000050050500000505000005050000050500000500000005000000050000000500a0a00000f0f00000a0a00000f0f00000a0a00000f0a00000a0a00000f0a
|0,6=>0xf0f0000000000000f0f0000000000000a0a0000000000000a0af0f00000f0f00000f0f00000f0f0000000000000f0a0000000000000f0a0000000000000000000000000000000000000000f0a0000000000000f0a000000000000000000f0000000f00000000000000000000000f0000000000000000000000000000000000000000f0f00000f0f00000f0000000f00
|_,_=>0
def sP:Nat→Nat
|0=>0x1a2048a16b068914445aa1a205040604029128088d00a138a080c009140d30d002048a3a0c02446245040688498144401e122888d0064e091444689147418038245033668c89302888d2e28203020041614101811228a941a00493080c10018488901a008901e340080e182840608080
|1=>0x1a01a8c1080203442438a2201792128088d387c3941a0040764186b8141818100209b70c0c4b640181892680194343041120340352e250040630ba740101a4122819b00259a00634487621801912283301abcf884044689402968d00785111e3400c4010181002438a583400c248088b
|2=>0x7048a16b069912181901a30f912034019122888b1a2452e5a34009401818518490111a30f872834009142d60d002451578340234e2050406bc608404469c124c194342503b0634e0914b468012292ac1a0040a223c6802e245033601d09401018012585042a01c09140d70018e4511
|3=>0x230c680442438a0c0c00c105830334357880e2888d0030fa02234041122888d009c41626283031280303806979212803031a30407223401f106100a0c3440914101bf24204a014446891455f0d00245145a34019141818f1a79109144402212283030030ba0080c4bd261802f122960d
|4=>0xbcf88141858d12805035c3401e10245111a0048a760c680469c48a080c01c1024986066978c128088d0070409141019a18e45060634009149418d007848a223401c124c3033518487223402f3e250061634e09141019a121c30b8a35c09141819a00d53881410180124d006071040a
|5=>0x102450336340234e20506063440a0c0c78d007048a06b0680443048a0c0c02710283037e2048a06986805e3040a2234009140cd8d007048a0650d0d102450616c069c18243861634f89144480d003049626101808c7c5111a00498144478d00245034c3400812292831a006170c0c10d
|6=>0x122820300d5188141818d38245062a34035125850406006272c4c303007c40a06506805e203a00c0c68c3e610061a0061214446801824503783401c4e205060668e09142c1941a24504072000c401818f1a004a00c0c80d00304060608680389c5060668609304458d0090b891410180
|7=>0x14181811a00e09402888b1a8c496141818d12288d01a01a882628203002438a0d386802e2049340181af18210060634b892680303102450407240171280504073048a072c6804824503283401f144650d008c4a0141818d38e048a0c0cd0914181850024504072402f12281941a01208
|8=>0x1a20493401018c12281ac1a0048a6e1819a38245035c34009402830b60344a00c0c70d6a245037834038122819b1a00e0926803033430fa00c2c68c242100606346080e1858d48e048a0c0c00c10181d11a309200c0c6a3124d00606349090e1880d004848a06506804e24503783401c
|9=>0xc0c02f12605111a006200c0ea8d18210040634f1f122888d00704090e446804e4c506060401f682830d0090496141018038243911a01c171228303015040a0c0c6801280504072001fa4283031a013882c28303187c303203400c2e803031ad4e09141018010283031c34c891418583
|10=>0x1a8c48a080c01c3e605061a01209140de0d00bc48a0cc06807024503283400c247c5111a00e09140d30d00791091418180382450616c0689140eb8d00243d60c0c6804e20503283401e38245111a00f1912283031abd1091418180122888b563402f38245111a00487144678d0031396
|11=>0x242438a0c2c6801228350063402712585060601789144468010249a00c0c6a412283031a0048a06b8a0d002500a080c080122888f1a0120a0c0c08d002450328b068052245111a0110914181803c2438a223401c182451116344a00c0c6da323048a223403546245060668c9f122830b
|12=>0x634012122888d017048a080c01c122830360340271080506063520940283031a0138826283030030f870c34035182450606680094028303903400c2e205060634027124d0060600487141818f1a01389402820300d4e09141818d0030b8a0c0c680383138a0c0c680382500a0c2c18d
|13=>0x141818d702450606340123e2500a0c0c68c4e803031a00496141019a00243a022340081228303be36309261818d011848a080c68012288de1a0060a0c0ea8d0020498141818d1826106063400c12802031a012092c283031a0040915743031a4840914446801824b06063401e1280506
|14=>0x121c5061a01189141818d0078f89141818d0024b1314101802e24b0a0c0c6803e243a00c3401c3e283031a0048a641818d011938a0c0c6803e205061634e08121c3031a0049314181e11a01c0812283031a01389c02830300704870c0c680383048a0650680383048a220c6801024b20
|15=>0xc0c6804e20504060048a0c0f18d0070609141819a1a24506071c680323048a0c0c680182100606349090e2830d002048a06506801848f8a0c0c68012281941a006092c803031a0121c12283031a00498144458d005c40914101805e7048a0c0c680121c506073c6801228303c43405b
|16=>0x1260506160c6801228303aa3400812282031a02309141818d00304a00c0c6801228303c83402412283031a00e09140ca0d005c4a0141819a1a24b0a0c0c08d005d38940283031a2450606ac68024245060640680382048a080c6801228303c23401c12282031a00609144458d013048a
|17=>0x121c506063401f12283031a0048a080c680102450606340090e2888d007c48a223402f1824506063401c1024506063401c12283031a00498141818d00304870c0c6801824506160c680124d00606340092c283031a00609141819a1a01a8c12283031a01388141818d002438a0c2c680
|18=>0x48a0c0c680
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x9500540005
|5,0=>0x17f61796173616d61676161615c51575151614b6145613f61396133612e51286122611c61166110610a610460fe60f860f260ec60e660e150db60d650d150cb60c560bf60b960b360ae50a950a3609d60976091608b6085607f60796073606d60676061605b6055604f60496043603d60385032602c60266020601a6014600e6
|5,1=>0x1a761a1619b6195618f618a51855
|6,0=>0x351734a7344633d7336732f73296322731b7314730e6307730072f972f272eb72e472dd72d762d072c972c362bc72b572ae72a772a0729a6293728d6286727f72787271726a7264625d7256724f72487241723b6235622f62296222721c6216620f7208720261fc61f571ee71e771e161db61d471ce61c771c161ba71b461ad7
|6,1=>0x4fd64f674f064ea64e374dc74d574cf64c874c264bb74b474ad74a674a064997493648c7486647f74796472746c6465745e74586451744a7443743d6436743064297423641d6416740f7408740173fa73f373ec73e663df73d873d173ca73c463bd73b763b073a973a3639c7395738f63896382737b7374736d7366735f73587
|6,2=>0x5d675cf75c875c265bb75b475ae65a865a1759a7594658d7586757f75796572756b7564755d7556754f75487541753b6534752d7526751f75187511750a75037
|7,0=>0x7a6879f7798779087888781777a7773776b8764775c8755774e77477740773a6732872a8722871b7714770c870486fc86f576ed86e676df76d966d276cb76c476be66b776b076a976a2769a8693768c7685767d8677667166698662765a8653764d6645863d8635862e7626861f761786107608860085f885f175ea75e465dd7
|7,1=>0x84e7847783f8837882f8828782088188811780a780377fc77f667ef77e787e077d887d267cb77c477bc87b667ae8
|8,0=>0x8df68d968d188c988c278bb78b478ac88a5789e7896888e8887788078788871786a7863785c78557
|9,0=>0x8f978f278ec68e57
|10,0=>0x9006
|_,_=>0
def wAt:=mkWire dB 101 236 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x140d381b003540250029242b4e014e290c351a254e010c3514011a2548136a014e291a250cd10e2000290025140d140d6435407c1401062514013e2906250c0d06ba2835381b40252c2716250c0d0601122900ad182f12294e8214014a370651381b10294085407e0029120d10291201125a242b0025140d1c35182c14250601
|1=>0xc35002514256e0d409c00291a291a25102912011a39182c1401142506013e010c0d062512290029381b062518011425120100290c0d180d381b102912010c39182c140114250601381b102912010c350025140118353e013e290c0d0625381b10290025140d3e800625120114011435409c002500291a2568350e2000290025
|2=>0x1a014e291a2500250c350029126a1a011a2912013e2b120d0c0d3c37101d120134291a01142500250e250c0d06290c0d06251229002984250e03140d0c0d260100251a290035262714011a293e29007d140106250c0d122912010629400d14010625342b1a0112010c3514010c0d100d12013c375e010c0d3e29062510351401
|3=>0x1a25000d00253e2906252835381b4025380d0c0d102912011c19182c1425060100d64e290c351a25102912011a290c0d1401180d122910291a0112010c358e25182e14250601381b102912015e010c0d3e290625102912011a011a290c0d140d180312293e290029120d0c35180114251a01000d140d40270029483718691425
|4=>0x102912016a034e291a253c27380d10290025381b102912013c37380d1801146a1a0112011a253c1b380d10290c0d1201180d12292837381b10291201381b10291201380f1029120100311425000d0c0d144a3e010625004d0c3514251a29120d0c0d1803122930270c0d162906013c1b182d142506010651381b1029145e4e01
|5=>0x480f383510291201124d260114350c351235260114251a29381b06251029002500250e250629400d1401062512290c0d16250601481b18691a0100351a2510290025381b180112294e830c3514011a253027400d00293c2b407d14010625145e103500251a01402514011a2516290c0d142506012e29103512010c3538130c35
|6=>0x26251a290c0d8a0d4027002926250c3500251a29073d101f1201140d103500251a2900251401180d12291401103512011a290c35104e1a2934251a0114010c35153510371201381b10291201102b062500250c0d4803409d14011a253837180114251c35182c142506010c35104e1201143526210c3512011a2900d626251a29
|7=>0x14011a011a252835381b10291201380f40251401163006010029122938371029120114351a014025140106010625122900291401100d00251425142512010601062938373835102912011229400f140112013e0106251229002900d626251a29144a3e010625481b409d140140252c2740350029000d0c0d40251401004d00d6
|8=>0x10291201125a26011a290e20120d1201140d2c250c3534291a010c0d06291801122910353837102912011325104e12011a29409e12350c35134d407f1401120d1235120126011a29242b3e0106251269140114251a0118350c3518011229163012011229000d3c03182d1425060112011a2900290c3538470c0d18011229409c
|9=>0x180d180112293837102912010c0d14253e010625380d102912013c37182d14250601380f18011229b21b016118371229153d101f00250629381b1a2510290025380d1029120100bd00be3e29062518010c0d180d12292601123514251a29121d0e010c0d0629100f12010029122912010c35002912293e811401062506290c0d
|10=>0x4121409e14011a25381b102912012c270c35403514013027400d14010c0d4827186912291a01381b10291201b6293e030c0d06253c37182d1425060112610e01140d0c0d1801142506011868140114251a010c0d5e03180d122900d6183514255e033e2906256a030c354e291a254025400d14010625481b186914251a01380f
|11=>0x12010c0d4e030c351a25380f10291201002500291235409d14011a2500251a251a29120d14250629183514251a01409e1a25103500251425143514011a2512620e0106290c3514011a25180118351229126912291a011a2518011425060140251401140d162506018a0d40270029403514011a250c0d3e290625002900251a29
|12=>0x381b180112290c0d18011229002540350029383710291201007d140106251a25122900290c3534291a010c0d14010629162b002506011435180312290c35180312290e27140d0c0d1425100f002512010e0106290e03142506290c3500291229125934291a014037140112010c0d100d1201403500291229380d40251401100d
|13=>0x14254035002938351029120116290c0d06010c3510351201180d18011229101f1201101e1201140d007e0625062900d64e291a25407d14010625260114350c35126934291a01140d1401120d402514010625407c14010625123518031229060112010625140d10291201104f0025383710291201004e1a251a29062918011229
|14=>0x1a01381b10291201342500291a01125a34291a01009d00291a25182f1229000d144a3e0106250c3510291201104f00251a290c35102912011229000d0c0d1535103712011a2500250c3501790e270629180114251a01182e142506015e03180d1229120100291229122d06010629381b1029120114253e010625381b10291201
|15=>0x140d06250c351201140d0c0d0c0d0625180d122910291201102912010e010629142506291229000d1401143534291a0114251a011835122912011a250601062916290601100f120112010c3518031229002912291627060118691425
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x18000
|5,0=>0x762000000000000001c546c51a10000000000019106131714000164c0000000000000000000005540000514138c49500004450fd43b40e843640c902e40a542450000204071000006c400005d0000050c000000012200000e4000000002900000000082000000001c40000000061
|5,1=>0x20940001f54785
|6,0=>0x5b4d6a3599163357d15c3561155354514e3529146450913e44ecd3744d0d3134b512a3499122447cd1c3464d15444510d44251054408cff33ed0f833d10f043b10e933950e143750da33590d243390cb331d0c342fd0bb42dd0b342c0cad32a50a5428509e3269096424908f322d0874
|6,1=>0x94524d49252454908e3e48ece3748cd22f48ad2274890e20487121938552114835209481520147f51f947d8df240001ef37ad1e7478d1df476d1d7474d1d03734c000728dc647091be46e91b646c91af36ad1a74690da04674d9a3659192463cd8b461d000060d18035f117845d11704
|6,2=>0xaf12b93ad52b14ab52aa3a992a24a7ce9b4a5d2934a40e8d3a252854a0527d49e8e7649cce6f49b0e6849912604974e59400000009550000
|7,0=>0xde8f773dd0f713dbcb6c3da4f663d8cf603d74f5a3d5cf543d44f4e3d2cf492d18f433d00f3d3ce8f373cd0f313cb8f2b3ca0f253c88f1f3c70f193c58f133c40f0d3c28f073c10f013bf8efb3be0ef53bc8eef3bb0ee93b9cae43b84ede3b6ced83b54ed23b3cecc3b24ec63b0cec03
|7,1=>0x3bf3ef0fb93ed8fb33ec0fad3ea8fa73e90fa13e78f9b3e60f953e48f8f3e30f893e18f833e00f7d3
|8,0=>0xfa0be62f90be22f80bde2f70bda2f60bd62f50bd22f40bce2f30bca2f20bc62f10bc22
|9,0=>0xfb47ec1fac7ea1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 14
def pmP:Nat→Nat
|0=>0x116400448001104004400010300040b001010004010010000028c0009340024500081000100000324000800001a40005500012400045000104000400000f00002800004000009000020000050000100000300000400000
|1=>0xa5340294c00a01402800008130020410081000200c008020020040080040200000602400c7d00313000c3c0030d000c0f00301400c0400300000a800025700088c0020c000820002040008080020100054100141000500
|2=>0x4a9341208c04222010244040220100080400000840901b5b406d4d01b1b406c4d01a57404c14012570041540100b0040280100500400400b5f402d6d00b57402d4d00b1b402c5d00b13402c4c00ab3402a8400a5b00295c
|3=>0x242230900cd2402309000821b1b484c6d2130308400820b5b482ccd20b13482acd20a93480c7d2031548087d201104804002000a0400000cb33430a4c0c213022e4d08b1342200408393420e4c08333020c4c08010020000
|4=>0x6031358040060043122c4d44b1351284944a11506c4d41313502ecd40b1f502c6d40b13502a8440a935028cd4031b500c3c4028010096c402571009544020e1008344020810080028233092ccd24a33492888248230908c9
|5=>0x84a93612a048489161220c8428321024d84001206d5d81b17604c5d8130520481c8111560441c8110520401c80b93602c4d80ab3600c6d8031a60096c80100200204800011a2c4d61014582c4d60a9358284d60803580d48
|6=>0x3a2c4de8803382c4de0b03782805e0a01382049e081178200de0341380c4de020178040de0103380401c1018700c4da88132a0004a0a936828cda0833682000a0241280400a0042272e4d88b93622c4d
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x200
|5,0=>0x35005c330012000000001a501900000009341e000a000000000000160023171f001558360723130b1e330025030010004c001200006c000500000b000060000059000007
|6,0=>0x8024ab670b9d5a320da0010603187ea7bd66cc1885195f35a99f0001d4a5b2cd0b71b3864d000501c301482a18b98eba056a0161aa04c62e6300118d01247f2b876d5103d41764080413d54e0c378606200399058844346e9e4c5d8a4f1d05a88e030f3128c689ca041c3fd68c27cb7035429a29177c278b415bc72c8c7869b0
|6,1=>0xb395e3e011740180bc5a22f2a26621b0b0101520135c43b183c220100002100
|7,0=>0x45d9bc7dbb93b1dbaedc56aec147d75430dab6d9b545823a57c22d174732456f6b3872d24691b7cf03a143d2d1d38145b5a36b7797909c4aac7a8fa60d73b8830e5365cec914ad959203be7479683dbfd8d0b475834bc8
|8,0=>0x4a4995d9da7b949876849b96af557baec093a454
|9,0=>0x474667ae
|10,0=>0x45
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 22 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_233 9 roots_233 ops++addP pm 1 dom_42 4 roots_42 ops++addP pm 2 dom_227 8 roots_227 ops++addP pm 3 dom_203 8 roots_203 ops++addP pm 4 dom_202 5 roots_202 ops++addP pm 5 dom_226 5 roots_226 ops++addP pm 6 dom_170 7 roots_170 ops++addP pm 7 dom_163 5 roots_163 ops++addP pm 8 dom_232 7 roots_232 ops++addP pm 9 dom_139 5 roots_139 ops++addP pm 10 dom_234 8 roots_234 ops++addP pm 11 dom_107 8 roots_107 ops++addP pm 12 dom_138 4 roots_138 ops++addP pm 13 dom_171 8 roots_171 ops++addP pm 14 dom_106 5 roots_106 ops++addP pm 15 dom_162 4 roots_162 ops++addP pm 16 dom_43 5 roots_43 ops++addP pm 17 dom_169 7 roots_169 ops++addP pm 18 dom_201 7 roots_201 ops++addP pm 19 dom_99 5 roots_99 ops++addP pm 20 dom_195 5 roots_195 ops++addP pm 21 dom_75 5 roots_75 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_235 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_75 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_233 9 s (0,roots_233.map (·&&&dom_233)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_235 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_233 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffffffff00000000ffffffff00000000,96),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_235==dom_235)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_235 gM v ys):RunD true dom_235 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_235 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 71 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 71 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 160 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 160 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 87 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 87 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 20 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 20 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 4 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_235 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_235 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_235 roots_235 goal_235 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_235
theorem lowS_235:Lower true dom_235 roots_235 goal_235 11:=S_235.noCircuit
def isoMvS_189:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 10:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_125
def isoMvS_207:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=lower_iso_b isoMvS_207 (by decide +kernel) lowS_111
def isoMvS_219:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_219:Lower true dom_219 roots_219 goal_219 10:=lower_iso_b isoMvS_219 (by decide +kernel) lowS_187
def isoMvS_222:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 10:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_190
def isoMvS_237:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 11:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_235
def isoMvS_238:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 10:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_221
def isoMvS_246:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_187
def isoMvS_249:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 11:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_235
def isoMvS_250:List (Nat×Nat):=[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_187
def isoMvS_252:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 10:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_221
def dzo_117_2:=0xcc00cc00cc00cc00cc00cc00cc00cc
def gzo_117_2:=0xcc00cc00cc00c800cc00cc00c80000
def gsh_117_2:=0x330033003300320033003300320000
theorem lowS_zo_117_2_85:Lower true dzo_117_2 roots_117 gzo_117_2 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_2) [(dom_117,2)] (by decide +kernel) (lower_slice_b (T:=gsh_117_2) [(0x330033000000000033003300000000,0,32)] (by decide +kernel) lowS_85)
def dzo_125_2:=0xcccccccccccccccccccccccccccccccc
def gzo_125_2:=0xccccccccccccccc8ccccccccccc8cc00
def gsh_125_2:=0x33333333333333323333333333323300
theorem lowS_zo_125_2_85:Lower true dzo_125_2 roots_125 gzo_125_2 7:=lower_iso_b (d1:=dom_125) (r1:=roots_125) (T1:=gsh_125_2) [(dom_125,2)] (by decide +kernel) (lower_slice_b (T:=gsh_125_2) [(0x33003300330033003300330033003300,0,8),(0x33333333000000003333333300000000,0,32)] (by decide +kernel) lowS_85)
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000ffff0000fffe0000fefa0000
def gsh_111_16:=0xffff0000ffff0000fffe0000fefa
theorem lowS_zo_111_16_42:Lower true dzo_111_16 roots_111 gzo_111_16 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xaaaa0000aaaa0000aaaa0000aaaa,0,1),(0xf0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff0000000000000000,0,64)] (by decide +kernel) lowS_42)
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,10),(2,34),(3,11),(3,19),(3,35),(3,67),(4,20),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(6,14),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,10),(8,40),(8,72),(12,13),(12,14),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(18,19),(18,22),(18,26),(18,50),(18,82),(24,25),(24,26),(24,28),(24,56),(24,88),(32,33),(32,34),(32,36),(32,40),(32,96),(48,49),(48,50),(48,52),(48,56),(48,112),(64,65),(64,68),(64,72),(64,80),(64,96),(66,67),(66,70),(66,74),(66,82),(66,98)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7ffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|4=>1
|5=>11
|6=>102
|7=>279
|8=>282
|9=>93
|10=>12
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xee4c8
|5,0=>0xf765dbbd38a7a3fa54b884ae24be8048cb54671435a561c3d20ca6e
|6,0=>0xff2b1fdf7afdd79fc326eefcded734eca46e8831e5fc4df2fdde489dcd2eda94cda860da511d9216d8bbad7abad220dcd1aecab4ec6caec6301c1206bf804be9e5be062bde43bcb23bc178b8e02b687bb42d3b3dc9af13aacefda6832a2815a199aa17909e32e9c9b89bc5997eb1974529625295f119400e923ba8e35a8dca28b9c388dbc84f55803eb7f84978cad761db7534b6f80c6e36d69bd3670566639e65e8e6577664cba63e17558da4e5c14c27b4bb9d4843c46d274643642de83ec003e9d13e76736d3936c13331a12edda2d3262c30725ce4214bd20d921d2961afe916bce1620f160fc160b4119eb0b7a80b3df09e4208a2007fe803f11032c6
|7,0=>0x7dc0a7d0d87d05b7c51f7bde57bb957b9f07b79e7b6f77adef797797933b776c1748b472db87266f720fa7187f712d97125570ecb70e7a6f7236ebbe6c17b6b5d96b00b6ac0969855695ea68d766865e67d5166c9d63a6161dad60d665eedd5ed945ead35d97c5d68a5b059591d055fc5556c354f155250451dbc4fc064f1634de0a49c0f49a3d49882496704779d4770447421440ed41fbf40d793ec2d3ec003d6533cc7239b9b39afb39878375ea360893537734e6733b023292c313342f1ef2ec2d2e08b2e0312dfb92d3662c3ac2ab57275992679e2576d2546924797241a92356622dae2293c21dee21a98212201fd1f1c4011c1131b3211b2941b07a18f9c18c5a16b241691414fea142391368611e79100500f33d0e6900e0000d0750936108af506f9b055f00557604a140403e0323002de8026d20219901c9100390
|7,1=>0xe8cf2e6e83e499ae3147e21eee1b26e103ce08a8dfcb0df1fcddc65ddb19dd748dd3f9dced6dcbf6dc571db20bdb1c1da9a2da8b0d8bc1d6b99d0dfbd07fbd0096cd8b5cd6b8ccd0dcb5e9cb0f7ca496c9d17c9b96c92ffc91e9c9175c6e2fc662ec384ac2695c1ac6c0f4ac07ebbfa0bbf060be9e5bdc73bd109b8f3eb890eb8684b84d9b7956b72f0b6cb1b58fbb4d69b2bc0b2022b1161afe3aafc7aae39cadb5fad925ad691ac891ac748ab87bab84caa32ba971aa9274a7caba56ffa53d1a536ea3a67a3591a2777a1ecda12169f8a09e7199daff9ce689c5c09b9099aeca9aaa89a6c898df9967c096318963149542694a85942799383f930ee9124290a81909cb906e0900058fb6f8e8ab8e2848d5268d3e18a9d3872fa8692a863b08632b862fc85a77842a58406e824ab80b0680a7f803eb7fed27fe117e60a7e36c
|7,2=>0xfde09fd7fdfc062faf21f9be6f8e06f8babf866bf6858f5bd2f5b99f51fcf4bc2f2e1df0f6df0896f061cf05c5ef2cbeedf3ecf03eb694e8eac
|8,0=>0x79484789c6781ec77ef076a5075e80756587410e73db373d627260b7195c700846ea176def36c8786c17b6bd256afb36978e66dc5669496518b64c9564c7e6433c6410f63c4e6384662d3a62bbf61871610b8608645df415d5925b69858081575e456c0a5688b55b4652118511835100d50fa450cf24f5924d93b4a6854a3094673a4652f4584844fb044ea743c61437b0431dd4148a3ec2d3cbd7396d4395ed3955338e1938c40383e637d4f368d23623135f7b3513334e9c3421c3243630f1930ea230ea1302332ec2d2e91a2e02c2d7d02c9412c2072adb229f962727f2709126fa4259ad2573c24cd62410823ece230722274f2251c21bd21d5be1ca651a67119e6f19ae319a0c197fc1949818cae1835e16c9e15dd714fea0eef50c51c0a55d0928f084d8077df06f2606be0066030611805a7b04b79042340243200aa2
|8,1=>0xe1bdddf459df1cfde5adde32ddd798dd038dc55cdbfa6da247d8ba6d7144d5444d2f42d2dafd2d5ed07fbd07b1d0562cfc0fcf7e1cdbbacd913cd8c9cd37ecc823cc1e7cb743c9d17c98a9c912fc86b3c8491c6732c612cc5e73c49aec0625c0372bf75fbec4cbeb72bd497bcb2bbc10ebbe26baf10bad17baac9b965ab87e3b71bab4e36b314db2dd7b1b9bb1b2ab1801af855ae22bad598ad213abe6bab343aafefaac99aa008a8bb6a8a8da138fa0cb8a0c99a09e79f4a89f0df9ef069ed069ddb29d08a9cfb39b747972a596b569627695baa94dbc94d1e94279935dd935db935c892610919bf91696902e58e0748dd328d8bb8c35b8b62d8929889213891e488efb88d6a87ec3871e78429683afd82dba8219181f7a81836815fc8132f80b068091e804447ff647f90a7e8d87dcd77dc1e7d2597cb787b5dc7a19379721
|8,2=>0xff2e2fc621fbdb1fbceefb553fab11f9140f7aaaf7843f6b33f5b9df51fcf3853efbbfef94ceed51ec9bdebbdaea111e98a8e927be7882e4a0ee3fd8e3f24e2391
|9,0=>0xfd9f9fb4b0f673bef8a5ee5b6ecff9eaa72e2858e20b7de234dd5bfda8e5d6882d1cb7d07fbd07b1c61f9c35c5c325ac08bbbf24abeff6bdd15ba77aba0a2b8856b7c01b601ab58b4b3cadb273db0ec4b0480affa6afc7daded7a9e0ea8ed5a3c68a28b19dbaa9ba129162390c1a8dc818adab83cf380b067654e733126f7606e2206a3f769d355e22c5dfcc5529e5411b4fdf44f3284d3d5494174789646f5d46698439ee3e1543e0c13d5ff3d36c3b2ce38d69382e53801b3801334048323e42f0e62e31e2988c292942862426df2241f0204a61a4a018bfe1109d0e1b30d6d40a6c7096970398a
|10,0=>0xfd72af69ede0a26c2a1c8d3bf83c7d7de0e761fa581865254f177e0063e4
|11,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x11111111115511551111111111551100ffffffffff00ff00cccccccccc00cc00aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffff00ff00ffffffffff00ff00ffffffffffffffffccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffffff0000000000000000ffffffff00000000ffffffff00000000ffffffffffffffffff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000ffff0000ffff0000ff000000ff00ffffffffffffffffffffffff00000000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffaaffaaeeeeeeeeeeaaeeaa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000
|0,1=>0xfff0fff0fff0fff0fff0fff0f0f0f0f0333333333300330033333333330033000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f000f000f000f000f000f0f0f0000ffffffffffffffff33333333330033000f0f0f0f0f0f0f0f0f0f03030f0f0300ff00ff00ff00ff00ff00ff0000000000ffffffffffffffffffffffffff00ff00ffccffccffccffccffccffccccccccccffaaffaaffaaffaaffaaffaaaaaaaaaaffffffffffffffffffffff00ffffff00ffffffffffff0000ffffffffffff00000000000000000000ffffffffffff000000ff00ff00ff00ff00ff00ffff00ff000f0f000f0f0f000f0f0f000f0f0f0000ffffffffffffffffffffffffffff0000
|0,2=>0xffffffffffffff00ffffffffffff0000000000ff000000ff00000000ff00ff0000ff00ff00ff00ff00ff00ff00ff0000ffffffffff00ff00ffffffffff00000000000000ffffffff00000000ffffff00ffffffffffffffff00000000ff00ff00ffffffffffff000000000000ff00000055555555555555555555111155551100ffffffffffffff00ffffffffffffff00ffffffffffff0000ff00ff00ff000000000000000000ffff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000000000000000000000000000ff00ff0033333333333333333333333333003300ffffffffffffffffffffffffffffff0055555555555555555555555555555500
|0,3=>0xffff3333ffff33000000000000000000333333333333330000ff00ff00ff000000ff00ff00ff0000ff00ff00ff00ffffff00ff00000000000000000000000000ffffffff00ff0000ffffffffffffffffff00ff00ff000000ffffffffffffffffffffffff00ff000000ff00ff000000ff00ff00ff0000000000000000ff00ffff00000000ff00ff003333333333ff33ff3333333333ff33000000000000000000ffffffffffffff00ffffffff00ff00ffffffff0000ff0000ffff0000ffffffffffff0000ffffff0000000000ffffffff00000000ff00ff00ffffffffffffff00cccccccccccccc00ffffff00ffffff00ffffff00ffff0000
|0,4=>0xffffffffff00ff00ffffffffcc00cc00ffffffffffffffffffccffccffccffccffffffffffffffffffff0000ffff0000ffffff00ffffff00ffffff00ffffff00000000000000000000ff00ff00ff0000ffff00ffffff00ffffff00ffffff0000ffffffffffffffffff00ff00ffff000000ff00ff00ff00ff00ff0000ffffff00ff00ff00ff000000ff00ff00ffff000000ff00ff00ff00ff00000000ff00ff00ffccffccffccffffffccffccccccccccffffffffffff00ffffffff00ffff000000ff00ff00ff00ff003300330000000000000000ffffffff0000000033003300ffffffff000000ffff00ff0000000000ffffffffffff0000ffffffffff000000
|0,5=>0xffffff0000000000ffffff00ff00ff00ffffffffff00ff00ffffff00ff00ff00ff000000ff00ff00ff0000000000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff000000000000000000ff00ff0000000000ff0000ccccccccccffccffccccccccccffcccc0000ff000000ff000000ff000000ff00f0f0fff0f0f0fff0f0f0fff0f0f0fff0fff0fff0fff0fff0fcf0fcf0fcf0fcf000ff00ff00ff00ff00ff000000ff0000ffffffff00ff00ffffffffff00ff0000ffffff00ffffff00ffffcc00ffffcc00ff00ffffff00ffffff00ffffff00ff00ffffffffffffffffffff3333ffff3300ff00ff00ff00ff00cc00cc00cc00cc00
|0,6=>0xffaaffaaffaaffaaeeaaeeaaeeaaeeaaff000000ff000000ff000000ff00ff00ffffffffff000000ffffffffff00ff00ffffffffffff0000cccccccccccc00000000ffff0000ffff0000ffffff00ff0000ff000000ff000000ff0000ffff0000ffffffff00ff0000ffffffffffff00003333333333333333333333333333330000ff00ff00ffff0000ff00ff00ffff0000ff00ff00ff000000ff00ffffff00000000ffff0000ffff0000333300003300ff00ff0000000000ff00ff000000ff0000000000ffffffff00000000ffff0000fff0fff0f0f0f0f0fff0fff0f0f0fff000000000ff00ff0000000000ff00ff00ffffffffffffffffffff0000ffffff00
|0,7=>0xffff3333ffff3300ffff3333ffff330000ff00ff00ffffff00ff00ff0000000000ff00ff00ff00ff33cc33cc33cc33ccffff00ffffff00ffffff00ffff000000ffffffffffff0000ffffffff00ff0000ffffffffffffffff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff000000ff000000ffffffffffffffffff000000ff00ff00000000000000000000000000ffffff00ffffffffffffffff00000000ffffff00ffffffff0000ffffffffffff0000ff00ccccccccccffccffcccccccccc00cc00ffffffff0000ff00ffffffff0000ff00ffffff00ffffff00ffffff0000000000ccccccccccffccffcccc0000ccff0000
|0,8=>0xffff0000ffff0000ffffffffffffff0000000000000000000000ff000000ff00ffffffff00000000ffffffff0000ff00ffff00ffffff00ffffff00ff0000000000000000000000003300330033003300ffffffffffffffffffff3300ffff3300ffffffffffffffff3300330033003300ffff0000ffffff00ffff0000ffffff000000ffff0000ff000000ffff0000ff00ffffffff00ff00ffff00ff00000000000000ff000000ffff0000ff000000ff0000ff00ff00ff00ff3300330033003300ffffffff00000000ffffffffff00ff00ffffffffffff0000ffffffffffffff00ffffffffffffffffffffffffff00000000ff00ff00ff00ff00ff00ffffff0000
|0,9=>0xffffffffffffffffffffffff0000ff0000ff00ff0000000033ff33ff00000000ffffffffffffffff0000ffff0000ff00ffffffffff00ff00ffff0000ff000000333333330000000033333333330033000000ffff0000ffff000000000000ff0000000000ffff000000000000ffff000000000000000000000000ffff0000ff00f0f0f0f0f0f0fff0f0f0f0f0f0f0fff0000000ff000000ff000000ff00000000f0f0f0f0f0f0f0f0f0f0fff0f0f0fff00000000000000000ff00ff00ff00ff00ffffffffffff000000ff00ff00ff0000000000000000ff00000000000000ff00ffff0000ffff0000ffff0000ffffff000000000000000000ffffffffff00ff00
|0,10=>0xffffffff00000000cccccccc000000000000000033333333330033000000ffff0000ffff0000ffcc0000ffccffff0000ffff0000ffff3300ffff3300000000000000ffff000000000000ff00ffffffff0000ffffffffffff0000cccc00ff00ff00ff00ff00cc00cc00cc00ccffffffffffffffffffffffffcccccccc0000ffff0000ffff0000ffff0000cccc0000000000000000ffccffccffccffcc0000ffff0000ffff0000cccc0000ccccff00ffffff00ffffff00ffccff00ffccffffffff00ff00ffffff000000ff000000ff000000ff000033ff000033ff000033333333333333003333333333333300ffffffffffffffff0000ff000000ff00
|0,11=>0xffff0000ffff0000ffffff00ffffff00ffffffffffffffffffffccccffffcccc0000000000000000ffffff00ffffff00
|_,_=>0
def sP:Nat→Nat
|0=>0xb201413041602060a04080302060b2014181f0a0d090803020d1e1d0914131819060a0d0803020a0d1c090803020d1b1a09100c0317060d0914131816060a0c03170d00090c03160a0009080316070a000815030706011413060a0d120803070b0d110403020e0d00100403020601080302060f090803070601050403020100
|1=>0x60a0d12090803020a0d11092f0407060a0d080307060a0d2e040302060a0d25180302060b0d2b0c0403060b0d2d2c040307060a0d0c0403070a0d00040302060b0d2b1413041702060d140402060a0d2908030206281b0927040307060d1e14180316060a09140402060a0d251413060a0d24230803020d2200091808030206
|2=>0xb0d37080302060d360914041f070a0d1403060a0d1209180803020b0d00080317020d000935080302060d1b100c031f0a0d0908340307060b0d04330302060b0d080307060e0d051008031f070a0d080316020a000903060d2224320903060b0d24320803070a0d110908030206201e090c0307060b0d2b08030706310d1418
|3=>0xd080307060108030702060d3e080307060b0d2d1404023c060b0d143b0402060a0d0815031607060a0803020d1e1a090c04033a060a0d14390402060b0d141816060a091418031f0a0d09080307060b0d3810040302060e0d040803020b0d111413041f020a0d1404031607060a0803020a0d1d090803020d221d0904030206
|4=>0x20b0d1d14044502060d09180803060b0d2d08440307060b0d0c03060d43420904080302060d3e080302060a20090803020b0d0024080302062022090403023c060b0d08030741060b0d0c03190a0d0009080307190a0d0008030206281e0914400402060b0d080307020b0d1d083f0302060d1b1803060b0d24320403020631
|5=>0x60b0d14041607060a04030206011404031f070a0d100c0316060a0908030702060b201008031607060a14060a0d12090803020b0d112414044902060a0d040803070a0d1108150307060e0d080307060a0d480c0403020b0d0014044702060b0d140407060a0d4603060d1e243209180803020b0d1d14130402060d22040803
|6=>0xa0d04080302060a20094f034e060d090c044c0307060a0d27084d02060d1e0908150302060d22090c040316060a0910080302060b0d24180803060d2224090408031607060a140402060b0d3d180803060b0d24084c0307060d220914040302060a0d2a084a0307060a0d0908030702060b0d4b100c0319060a0d09084a0307
|7=>0xd09180302060b0d320c04150307060a0d0408300307060a0d0c080302060a2009085307060b0d0c040317060d09080302060d1e050918080302060a2009040302060d223209140402060b0d24040302060b0d3208035202060a0d091008031f020a0d09040307060a0d24321808031f0a0d0908510302060d1b091404071906
|8=>0x80302060d225c090833030702060b0d0c040302060b0d5b1413180402060a0d14180319060a0d0908030206590d0914040226060a0d18080307570a0d0914041f020a0d09084c4d02060d1e090803020a0d002309040302060b0d3d180302060d2232091413040219060a0d080307560b0d100c040302060b0d0c540302060a
|9=>0x60b0d08035e02060a0d090803020a0d11091404023a060a0d0c0302060a0d2b091403060a0d242309180302060a0d2b09044c0307060a0d32350c040302060a0d0c0403060a0d2d091404031602060a0918080307060b0d2404080307060a0d2d080302060d1e55090c0307060b0d32040302060a0d2b09080302060a0d5c09
|10=>0x302060e0d080302060d680908060a0d6709140402060a0d6609080302060109080302060d1b650903060a0d2432091418040302060b0d0c0307060a0d2b09080362020a0d09180803060a0d12091404031702060d0908600302060b0d2a04030226060a0d080307060b0d5f040803023a060a0d04084a0302060b0d27040302
|11=>0x60b6c0d080302060d225b09140407060a0d2408340307060a0d0904330302060a0d09080302060a0d6b09080302190a0d0009040803020b0d000408035202060b0d1808150302060b0d690402060a0d09140402060a0d4b04080307570a0d08030702060b0d5c10080302060d220918084c0307060b0d1404070226060a0d04
|12=>0x90403070226060a0d0c08035e060a0d09100c040307060a0d080302060d1b4309040302060a0d6609080307066f0b6d040302060a0d0927080307060d1e09180803020a0d000918040302060b0d320c08150307060b0d0c0403060b0d24140402060d220921080302060a0d0921080302060d220908150307060b0d61140402
|13=>0xd090c040307060a0d5b0803020a0d1d097408030702060b0d4f0307060b0d08030206730d090c04031f0a0d0908710307060a0d0803060a0d2d230914130402060a0d2472040307060a0d0408031f070a0d040302060a0d370904080302060b0d5c14040702060a0d3d140402060a0d2a0408710302060b0d08030206700d1e
|14=>0xa0d46180803060d1e2409040803020a0d110914040702060a0d2414080702060a0d7a084c0307060d1e09084c0307060b0d3208030702060d680918080379060a0d0904080302060b0d7608330302060b0d3218080302060b0d5c2f0802060a0d09080302060a0d38090408030277060a0d04080302060a0d7518080302060a
|15=>0x3d2108030702060b0d18080316060a090803060d7d0914390402060a0d09087c0307060a0d091404030719060a0d147b0402060a0d0904083007060a0d04084a0307060a0d080302060a0d2d0927040307060a0d08150302060d1e09080307060a0d3809080302060d22050914040702060a0d4b08150302060b0d3208030706
|16=>0x32090815030719060a0d0c040307060a0d05087f0302060d1b09141819060a0d0904080302060d680904030702060a0d2b08510302060d1e093508030702060a0d140402060a0d7e09080307060a0d2d091404023c060a0d090c0302060d1b420914040302060b0d241008031602060a09084a0302060b0d2404030702060a0d
|17=>0x80302060b0d08031607060a14060a0d242309080307020a0d1d091008031702060d0914810402060a0d0918080302060d680914041602060a09180302060d1e3209080302060d1e5a0908030702060a0d7a0c03060a0d2432091404031f020a0d09080302060a0d80090c0803060d1b43091408070226060b0d1803060a0d24
|18=>0x60b0d14041702060d0918080302060b0d5b0803020a0d0024093504080302060a0d0403023c060a0d0908030741060a0d09080302060a20090c0307060d1e3209080307060b0d842104080302060b0d82040302060a0d09080302060d1e5c092704030702060a0d35080302060d1e090c0316060a0914400402060a0d091018
|19=>0x927080302060d1b09080302060a0d2409040803020a0d1d090408710307060a0d27040302060d1e090c0803060a0d2d090c0317060d093518080302060a0d0803070226060b0d14180402060a0d09180803060a0d2d09080307570b0d08440307060a0d0914180402060d220914180402060b0d0c040307060d1e2118080302
|20=>0xb0d2d14130402060a0d2304080307060a0d462c040302060a0d09087f4d02060d1e090c0803020a0d1d090c0403020a0d000914044702060a0d090433030702060a0d080307060d22240908030786060b0d350c080307060a0d04080307020a0d00180803020a0d1d09080307060b0d241808030206730d09085e02060a0d85
|21=>0xc040379060a0d09270c040307060a0d0408030779060a0d08030702060a200914040307060a0d240803060a0d12092f0402060a0d09084c0302060d1b090402060a0d66090803020a0d11240918080302060b0d050c040307060a0d2427080307060b0d080302060d1e6509040307060a0d8714080702060b0d4b0408030206
|22=>0xd4b0914040302060a0d230908030702060a0d2409084c0307060b0d1008030719060a0d083f0302060d1e090c0403060d1e240904088c0307060a0d080307060e0d0c080307060b0d05088a0302060b0d8908880307060b0d08030206310d0921080302060d1e0914040302060d2209084a0302060a0d0908030702060b0d2b
|23=>0x90c040319060a0d090803020a0d00090408030719060a0d08035202060a0d0904080302570a0d092708030702060a0d0918080302060d1e090c0803060a0d240910080302060a0d2409080307060b0d58140402060a0d3d090803026e060a0d090c080302060a0d5509180803060a0d24098d080302060a0d0908030702060a
|24=>0xb0d100c040302060a0d09180302060a0d3209080302060a0d5a09140802060a0d9309100408030702060a0d080302066f0b0983040302060a0d0904080302060b0d24080302060d1b090c080307060d1e0908060a0d3d920908910302060a0d09140402060a0d2409040302060a0d32098f080302060a0d09140802060a0d7a
|25=>0xa0d0914080279060a0d090c040302060a0d5b094f0302060b0d09080302060a0d5c090408030702060a0d5b08710302060a0d09140802970a0d0972040302060a0d090408031f020a0d0918080302060a0d2409080302060a0d96090c0302060a0d3209040302060a0d3d09080302950a0d09080302060d2209084c03070206
|26=>0xa0d090c040307060a0d0c084d0302060d1e09080302060a0d7609040802060a0d6a09080302060a0d7a09087f0302060d1e090815030702060b0d18080307060a0d24091402060a0d5f09080307060a0d8709080302060a0d980914080702060b0d2718080302060a0d090c0307060a0d3209080307060b500d083303070206
|27=>0x18084c0302060a0d091418040302060a0d0982080302060a0d09080302970a0d0908600302060a0d2a09080307060a0d5f091404030219060a0d09080702060b0d9904083002060a0d09270c080307060a0d0904084a0302060a0d0927040302060a0d0904084c0302060b0d080302060a0d930927085d060a0d0908035e0206
|28=>0x60a0d3d09080302060d9b090c04030702060a0d0c084c0307060a0d0908030702060a0d5c0918084c0307060a0d09084c5d060a0d09088c0302060a0d09140802060b0d3d0908030702060d2209080302060a0d9a09040803026e060a0d090408030702060a0d0527080394060a0d0974080302060a0d0908030279060a0d09
|29=>0x8150307060a0d6109140402060b0d21080302060a0d0910080302060a0d23091404030702060a0d0408910302060a0d090c08150302060a0d09040803020a0d000908031602060a090408035202060a0d0918080307060a0d580927080302060d1e0908039c02060a0d091808150302060a0d09180c0803060a0d2409084d02
|30=>0x80302060d1b09080302570b0d0908031702060d0908030264060a0d09080302060b0d3d09080302060a0d5b23090c040302060d1e092c080302060a0d0904080302060d2209140802060a0d2d0918040302060a0d32090c08150307060a0d090c0403060a0d2409080302060a0d9d0904080307060a0d24100802060a0d3d09
|31=>0xa0d2a1404025d060a0d09180c0302060a0d32090c080302060a0d5a0908600302060a0d0918080302060a0d09084c0302060a0d3209084c0302060d1e0918080302060d220927084d02060a0d0904080302060a0d5c090408710302060a0d0918080302060b0d140402060a0d230908300302060a0d0914080226060a0d090c
|32=>0x4030702060a0d320c080307060b0d084c0307060a0d32090c080302060a0d5c09350c080302060a0d0904080302060a0d760908330302060a0d320918080302060a0d5c099f080302060a0d09140802060a0d5509080307060b0d611402060a0d63090302060b0d9e0914080278060a0d097408030702060a0d090408030206
|33=>0x80307060a0d5808030226060a0d090c040302060a0d24090803a402060b0d0904084c0307060a0d0803a302060a0d0927080302060b0d090408030702060a0d24080302060a0d2d090802060b0da20908884d02060a0d0908150302060a0d3209040302060a0d8709140802060da1091408023a060a0d0904080302060a0da0
|34=>0x2060a0d091004080302060b0d54080302060a0d09080302060e0d09aa080302060b0d0908880302060b0d09270c040302060a0d090408030279060a0d09084c0302060a0d240914040302060a0d2409084a0302060a0d2409140802570a0d09080307060b0da9080302060b0da7092108030702060a0d090803a602060b0d04
|35=>0xb0d090803060d8ba9090803060a0d2423091018080302060a0d0904080302060b0d5b0408031602060a09080302060a0dab09140802060a0d4b091808030702060d2209080302060da1090803023a060a0d091808030702060b0d1008030219060a0d09080302060b0d321408070226060a0d0918080319060a0d0904088c03
|36=>0xd09084c78060a0d092118080302060a0d0908030719060a0d080302060a0d2b0918080302060a0d5b0908034e06500d0908030702060b0d0514040219060a0d09140802060b6c0d09080302060d1b1e090c044c0302060a0d09147202060a0d091408030702060b0d2104080302060a0d0904084c030702060a0d08ac030206
|37=>0x302060a0d24091804080302060a0d0972080307060a0d091804080302060d220914080702060a0d3d09040815030702060a0d080302060b0d241804080302060b0d0803070226060a0d090408300302060a0d09080307570a0d09085302060b0d0914180402060a0d09210c080302060a0d090408031702060d090c0319060a
|38=>0x5f0908030702060d1e0908030786060a0d0908030702060b0d3208030702060b0da5080302060dae09080307060a0d2409270c084d02060a0d0908031f020a0d09084d0302060d1e09080302060b0dad099f04080302060a0d09084c02060a0d6309080302060b0d89080302060a0d4b0914130402060a0d080302560b0d0908
|39=>0xa0d0009083002060a0d09084a0302060a0d0914040302060b0d080302060a0d750908030702060a0d3d090c080302060a0d0509080302060b0d2a18080302060a0d05090c040302060b0d0802060a0d6a0908060a0d3d580927080307060a0d0914080702060a0d4b0914040702060a0d04080302060a0d2d09084d02060a0d
|40=>0x60a0d09080302060a0d8e09140802060a0d92090c080302060d1e09080307060a0d580908150302060a0d09084c0307060a0d0908330302060a0d0904080302060b0da5040302060b0daf0c080307060a0d050908880307060a0d09080302060b0da00c084c4d02060a0d0908030702060a0d2b09080302060b0d5f09140802
|41=>0x803025d060a0d09080302060b0d610914080702060a0d09270c080302060a0d09080302060a0d230914084d02060a0d0908b20302060a0d09080302060a0d92091408030294060a0d09080302060a0d8709084c030702060a0d0914130802060a0d0908b10302060b0d0904080302060a0d240908b00302060a0d091408025d
|42=>0x2060b0d0908030702060b0d0c084c0302060a0d09080302060b0daf09080302060b0da90904080302060a0d5809080702060a0d990914080302060b0d0913080302060a0d0904084c0302060a0d09080302060b0d8b090c080302060b0d0910140802060a0d0990080302060a0d09080302060a0d5f090815030702060a0d09
|43=>0x294060a0d09140802060a0d3d09084c4d02060a0d09080302060a0d05090c080307060a0d09080302060a0d6309080307060a0d610904080302060a0d230918080302060a0d0908030219060a0d0904080302060b0d140402060a0d09084c0394060a0d09080302060a0d5b09080302060b0da50910080302060a0d09a80803
|44=>0x904080302060a0d5b0983080302060a0d09080302060b0d580908034e02060b0d090c08030702060a0d09080294060a0d99091808030702060a0d09084c0302060b0d09080302060a0d3209080302060d1e090c084d0302060a0d091004080302060a0d09084d0302060a0d6109080302060a0d550908030278060a0d091408
|45=>0x702060a0d3209180c080302060a0d09140802060a0d580927080302060a0d0914084c02060a0d090802060b0d9909080302060a0d24091804080302060a0d090408030219060a0d0972080302060a0d0908030702060a0d0509140802060b0d09080302570a0d091408030702060a0d09080302060a0d3d0927140802060a0d
|46=>0x14080302060a0d090c080302060a0d09080302060a0d610904080302060a0d0908030702060a0d09084d0302060a0d090802060a0d9909140802060a0d09080302060a0da0090c080394060a0d0914040302060a0d09080302060a0d2a0908880302060a0d090c040302060a0d090408030702060a0d080302060b500d090803
|47=>0x80302060a0d09080302060a0d5809084c0302060a0d09080302060b0d0908030294060a0d09
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x1058076c0356017b00a58046c01d600bb00458016c0056
|6,0=>0xfd287cdc3d8e1e570ef3875dc3a0e1c970e1386f1836ae1ae70d3b8681c332e19270c5b8611c2fae17670b8305a5c2c4e15b70aa38535c28ce13f709c384c5c254e123708eb0459c21ee1087081303edc1e8e0ee6073b8381c1b2e0d27065b8311c17ae0b67057b82a1c142e09a7049b8231c10ae07e703bb81c1c0d4c063702e38155c09ce0477
|6,1=>0x5fae2f7617928badc5c8e2dd716b38b418592e2c2715db8ad1c55ae2a6714fb8a61c522e28a7141b89f1c4eae26e7133b8981c4b2e2527125b8911c47ae2367117b88a1c442e21a7109b8831c40ae1ff6
|7,0=>0x273b937e09af04cf8263c12fe096f04af8253c127e092f049072444120208f1047082344118208b1045172253910a0876e4338215c1091c839041482073101a07fd03f771f7c0f9e07bf03d961e938f2a078503ba81d9b8eb1c749039c81ca40e35c70b037e71bb40dc186d1036081ac40d45c6930341819d38ccdc658e324818e40c52061903048
|7,1=>0x36639b120d7906b5735739a9a0d3d06968347b9a1e0cff06778337c199e0cbf06578328b19260c8306398318c18a60c44e61b7309c182e0c0705fc72fa417b5cbcb05dd82eac17360b8ce5be82db416bdcb50e5a172ccc16460b13058182bdb15d1cadcc56682b0315620aa2e54982a0c14e9ca65052a82914146dca28e50c8282413f5c9eb04ee7
|7,2=>0x45f422da115d08a6844f4225a111d0886843f421da10dd0866842fba15e109f0847841fc20de105f0827840fc205e101f080783ffc1fde0fe0e7ea63f141f6a0fa507ca83e1b9eee0f6707ac73d241e720f29078c83c241df5ceeb076d83b2c1d760eab074d83a2c1cf60e6b072d8392c1c79ce2d070e838341bfa0ded06ef7373c1b858db4e6d37
|7,3=>0x555c2a8e1538ea948546baa1614fb0a758536c299614bb0a558526c2916147b0a3585173a89a143d0a168507ba81e13ff09f784f7c279e13bf09d784e7c2725938309b984d8c26a61346c99b84c9c2631d30ae97d84bb3a5ba12cd095e84ab4253a128ee93f849c3a4c212510920848c424421214c902847d423d191dae8e5846ec2356119b08c67
|7,4=>0x2d7216a90b4c85a242cf9966d0b2e8593bac81d6310b10858442c0215f10af0857442b8215b10ad175653ab0a1576eab38
|8,0=>0x6aec35561a9b0d45869e4b4d5da5b0d25868f3b4565a1b0d06767ecb3d619d92ce5766ec335259990cc5765ec32d619592ca4864e43252191aec86763f431d658db0c65862ec3152589aec45861ec30d9d85d0c27760fc305e181f0c0785ffc2fde17e0ebe885f042f62179f2bc785dfc2eda575eeba785cfc2e5a571d0b8685becadd256d72b647
|8,1=>0x7b5bbd8e1eb70f5297a543d0a1e750f328794cbc825e310f10878443c021def2ef16774c3b825db10ecf97634bafa1d6eeeae9752cba761d2b0e8c9741cb9ee1ce8ee6c8731cb96a5ca32e4a7721438ea1c650e2a8710cb8625c210e088700437de5bdd2de686efbb75a5b9d0dc596df3b6da1b5b2da496ce436521b190d8576bec35d9dadb2d658
|8,2=>0x8b9c45ae22c8f15c88aa4452e6285313998984c49e6240f1197888c44226202f0f98878c43a261c110d8886844322217f30b788583c2a2213f309788483c222210110788838bc1a260bf30569826cc112607730338815c4091e03af0167807440165ffb0ff587f64bf8e5fb70fd387e54bf0a1f750fb287d4cbe825f32ef9187c4c3e061ef30f727
|8,3=>0x9bb44dba26cd135e89abbcd3e268d333f799bc4cbe264d331e898bbcc3e2610f301797cc4bc265d112df996b4cb36658cf2be895accab2654af29e794b44a36650b127e793bbc9ba64cef25f892b4c93de48f123f891bc48be244d321f790bc483a640b31fd88fb3c7ba23cb31dd88eac4736238b11bc98dabc6b6234b119c98cabc6326309117b9
|8,4=>0x2889143c8a1abd0b26849141d7a0a4d02e680713fc79fabcfb627ccf3de89eaccf32678af3bc99dabceb9e74ef39f89cb4ce3de70d337e8
|9,0=>0xb26c59126c7916348b16bd8926c3736129b054580a2bf515f28af54578a2bb515d28ae5457066b7315b18ad53d68deb3715938ac5c560e2af715747ab5cd58e2ab715529aa54550a2a7515319a94c54862a3315118a84c540269f114f08a744537e69af14cf8a63c52fe296d34ae8a52cd276292b148c9a42451f228e9146c8a324517228a9144c8
|9,1=>0x173a8b9945caa2e45171a8b8945c2a2e0516f99b784dba22dc116d88b68bdb262d8136b79b57c5a9a6d3ef6987b47cda1e2cff16769b374599a2cbd16559
|10,0=>0xbcbc5e3e2f10f7808bbc45dc22ed117608bac45d422e92f7427
|11,0=>0x179f7
|_,_=>0
def wAt:=mkWire dB 179 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa0946067080341008040242025083040c650402020250209440300209420090403420251006c082508024100d142a0200d04028300d0c0ac200904024643504020200d0426c501c02094843718034201d02094100919064200d040201009080942009190a410080403420250e0d408250c0b020090a09438350403420250c0b020090a09438350c0b02009020942825
|1=>0x2094302c0802428250a09410f71402c643504020202502094401c0209420090809464350803410080402420250403420250c0b020090a094100b02094643504020202519064200d04020202502094200d1819c100804024401b04034100908094200904034100808094302c0802408250a094100d04020202502094600b0a09420c9080780825270b008250c0342009
|2=>0x8094200d0209464350402020250e0d420250c0b020090a094100d080246435040202025040340825190d4100808094606708034100804024202547094509308034100b0402c08250c0b020090a0941c670402008252106c600d0c094200904024f029021b878250c0ac100904020401b0403410081006c100d1802c20c9080780825270b028250c0342009080943835
|3=>0x809408250402c6419040201009080940c6d1e094302b08024200d040202025020948437180341009020b42141020b02825080940c090802408250c034302b080242009190d4100808094100d0a094100b08094602b02244100b080940825190d4100808094500b0a094200d08094282502244100b08094602b03024201d02094100a1407c282502094100808024100d
|4=>0x1402c200d180ac20c90807808250402020251409c200d020941941020b028250a09420090403420250802421554d02c0c250a09420c9080780825080242025030740825020940c65040202025210dc600d0c0942009035040825020b02825190a41008080242025210dc600d0807408251808c602b0402420250402c28250803420250a0946023040242025040341008
|5=>0x3024201e2709c300d08024400b040342025190d4100808094200d0a094600b0807408251002c100d08094201e0209420090a094842318034100908094282503324201e02094100f0809420090a094100908094502708034100904020200d0a5a43136080240c2514070202508034082506584201d0302808250803464190402020250c0ac0c09080240c25080942825
|6=>0xa094200d040242025081580c1d0209590190263c213603094606704020100908094642904020202508034282561094200a08094501c02094200d084c828250302408251007008250403420250324428250402c20250a094300d080242025025a4313608025281b03244100b0809420255d0945008080342009081580c1d02094100a08034100b08158201d030740825
|7=>0x1006c100d080942825025b420250a094201d030740825086a40c6704020202508094501f0803408250809419610302808250a094201d02094602b04034100908094201d0a0940c0902094202514070200d0209420250c0b020090a094842b18034201d020949d7714024500808034506704020200d0809438350c0b020090a09478250c0ac20091808c08910402c2025
|8=>0x8024100d08094506704020200d500d40825020b02825086e4096f0403c20250c034302b08024401b0403410090809428251808c1009080940c1d0209420090a094282508024100b08094200d180ac100908094600d02244100b08094600d180ac201d020942825080280825140b028250803420250803408250402c20251561c200a0307410081006c100d080942825
|9=>0x2094100f08094841b18034201d020942015020942825085040825020b02825181ec30250c0ac20090802464190402020250209411300302420250402c502708034082508094216103028641904020202502094214a025b4100f0809428250402420251402c2025080340825080348c25040282025044c00c090a09420251407008250803409690c4d82009030940825
|10=>0x307808250209428250807808250719c08250402020250c0ac600b0c09420094a06c0c910402c082508034100b0809408253d094500b08034302b03024200902094201e0a0940c0902094842b18034201d0403428250807808250a094600f0807408252c03421e14d0200c257402c201502095b825025bc100f08095d825044c80c090809411b9025bc100f080942009
|11=>0x2109c600d080740825045dc50082102c600d080740825043dc500b080342025081b8782508024282508034100b08094100d190d4100808094282503244100b08094202502094500b08034282518034201d020946435040201009080953943020b4082c0a094082504020202508034508f04028200d080940c6504020202502094100b02094300d0802420257402c2015
|12=>0x807408250803464350402020250c0ac60230c09420093d09408251402c200d1802c60230c094200919064100808094200d1019c1008040342025021b878250c0ac20091407028250803408251808c08910402c20250402020250307408250809420090307808251e0940c790c0ac2009080341008040242025210ac600d0402420560307408254d1e4302b080240c25
|13=>0x1803410090809410f71402c200d075fc213203024843718034201d02094201e02094302b0750c0825020b028250a094600d04024202583034208d04028202502094300d0802420252709c300d0c0ac2009190d4100808024202514180200d0402420250a094100d040242025190d4082504020202504028200d0402c20252106c600d08074642904020100d08094600d
|14=>0xc0ac200904034841b1803410090209411300302420250c034302b08024840b180343025080242009190a41008080949c270c034302508024282514070082508034089108034100b08094400b040341009080940825065840c0a0a094200d0402420250402428250803420250809408250c0ac2009180343025080242825190a410080803420250403c1009080948427
|15=>0xc0ac20090809408250c03c20091002c2825040342025040281c67040200825100c02009040342025031e4302b080240c252106c600d0c09420091006c200904034509308034100b08094201e1802c602b0807408250a0941d870802808252709c300d0802408251006c100d2106c600d0807408250a094600b080740825181ec30250c0ac20090263421361e094300d
|16=>0xc03420090a094313503094302b08024200d180ac1009080940c911802c201d020942825081580c1d02094400808024100d0809408250c034200908094400802094100d08094843718034201d08034100b1819c1008040242025083040c650402020251e094302b08024506704020200d08094201d0307808250a094082508024100b0809408250c03420090a0947825
|17=>0x1802c302508024100d0402c20250a0940c0a02094500b080342025025bc100f0809420094d02c0c2502244100b0809422394d0280c251407c082508034100a08094200d1802c201d0209428250302408250403410080809408257f09c302b08024100b08094302b0458c0c0a02094302c080242825080240c1e0209428258b094082f0a094282503614200a020949c2c
|18=>0x20943136080240c251494c0827080340825040342025500d4082c0a094208d0402820250a094100b0809478250c0ac200902094302b08024500b14028200d03234100a08094200d0402c20251808c100908096400d0c09c20093d094500b0803410080802420251006c5025080341008080940825025b4100f080942025065840c0a0c03420090209430250c0ac2009
|19=>0xc094200908024201e020940825020b0282503324201e02094400814094200d08024100f080942141020b028251803c201d0209408250403c2025044c00c09080941a4914028200d08094216103028641904020202502244100b080940c920402c202508024201e0209420251402c200d068e5340a03094602b0807408250a0940c0902094200904034202508324201e
|20=>0x2094200e0a0940c6504020202502094300d080240c910402c20250c0342009080940c090809428251494c082708034500914020200d02634213603094082508024202503094302b0802411320302420250319c100808094f4251402c200d031e4302b0802428250307408251802c201d02094200d084c80c0902094300f080243137080240c250a094200d02094300d
|21=>0x89440827080942009020940c090802408251803c201d020940c090807408250302450080803411630302820251402c200d0a094602b080740825032a9842508028096f0403c2025080940c1e02094300d080240827080540c1e02094400814094200d080740c0902094200d0402420258303422510209c1a4914028200d61094200a02094213203024100808094200d
|22=>0x80240c1d0209420090402c202587094300f0802408250402c20251402c502508034200a0307408250a094200d08094600d08074082504028100d08094082508094200d03234100a080940c1d0802408251006c100d080946435040202025025b4100f08094201d0302808250c034302b080243134080240c25080740c1d02094600b0c094200903094500b080360c2b
|23=>0x309408910402c202503024201e02094302b080240c09180ac201d02094300d080240c251803c10090809411300302420250c09420090a094100a08034202503194100808094501c0803408251e094302b080241961030282825190a4100808094098f084d80c250a094500b0803420250c0ac200908785340803094602b0402420251002c5025080346023040242025
|24=>0x5d094500808035602503028202508094201e02094082508024282503024201e02094600f0c09420092709c300d0802411320302420250807808251803c201d02095c825085840c0a08035340b030940825080282825084d80c25080342143020b0282508035340803094201503078082523094100a08094202514020200d1808c3025080243136080240c254d614200a
|25=>0x402c202508034100b080940c910402c2025080341961030280825020b82825a803c202d0a094600d0807408254e09c082d0a09420250302808251407008250803420090402c202502a540c2e0a09420250302408254d61c200a03094300d08024282502094100b08094400b14094200d0350c082c0a0940d85080280c250807808250c03c2009080949c2b14024200d
|26=>0x8094100d0402420250a094100f08094643504020202503328201e02094501f080340825180ac201d020949c2b14024200d5d094500808034282508074082504020100d08094282508078082514070200d0209410080402420250458c0c0a08094282504034202508555340b03094302c08024282508a540c2e0a0940d850802828250c0342009080944008040342025
|27=>0x40242025180343025080246429040202025040202009080940c094d0200c2518034201d020940825040202025081580c1d02094100f040242025020b4082c0a0940c1e02094282504020200d08094502c0803428251e094302b080240c0908024202508034216103028282502094200d180341009080942025030240825038b4082f0a094082e020bc282504028100b
|28=>0x19064100808094302b080240c25034e8082d0a0941161030282025030242136030962c25020bc28251407c08250803420251409c200d06504082c0a094600b08074082502244100b080942161030280825180ac100908094500b080340825080940c1d0209428250402c20250a094100908094501c02094200d03194100808094196103028082503504082c0a094200d
|29=>0x8094282508094200d5f09421320302408251402c200d03078200902094282561094200a03078201d0209420250802428250319c1008080940c0a1402c200d0c034200902094501f08034082508094200d02094400b04034202503094213203024302b0802408250761c200a020942825080780825020940c2e0a094302f0802428251802c201d02094300d080240c25
|30=>0x8034082708034300f080240c09020945027080340c2d0a094100b08095302703024500808035340a03094500a08034302b080240c0a020940c1d020940c09020940cc9080780825080940c2e0a0942025080b82825080240c1e020940d85080280825580940c0a0a0940c09080240c25081580c1d020942825084c80c091006c5025080340c6504020202503244100b
|31=>0x8094201d0209410080809420250a094200d08094082703024100f080940c2e0a094502508034202d0a09408250a094200903024202e0a094082e0a0940c0a08094200e020942825080345027080340c0908094082f0a09420090a0945025080343027080242132030240c1d02094500808034200a0a094200d02094300d08024100a080940c25080340e510209c500a
|32=>0x80941009080941008080942161030280c1e02094200d0a094196103028082508034500b08034500908034100f0809422510209c0c0a0a094082d0a094200902094200e0209c201d020940c090a094201e02094302b08024200903094100d08094200a03095340b03095340803094082708034500b080340c09030940c1e02094200902094213603094200a02094100a
|33=>0xc0a0302428250209c200d08024200a08094082503094200e0803560250302820090209c2025080358425080280d8508028200908094202502094082c0a094201e020943025080240c0a080345009080340c0908034200e0a094100b
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xb5000000000000005600000005
|6,0=>0x7c50000000007930000075400000714000006c5000000000675066100000624000000000000000005d5059405540000000005140000000004d4049400000000044500000000000003f503a5000003550000000000000000030502c400000000029300000263022401f30000000001b4000001a1015500000000000000000105
|6,1=>0xba50b5500000b0500000ab50a6500000a240a1109d400000000000009a30000096400000951094100000000091309010000000000000000000008d308a3000000000000000008640815
|7,0=>0x18b418741843180417e217b317831744170416d300001694165400000000161415d415941563152414e414a414641424000013e413a41364132412e412a41264122411e411a411641124000010e410a41064102400000ff30fd20f940f540f140ee30ea40e640e3300000df40db40d740d340cf40cb40c740c6100000c330bf4
|7,1=>0x26640000263325f425b425742543250424c4249300002454241423d4000023a32364232422f322b42274223421f421b421742134210320c40000208420530000000020141fd41fa31f641f241ee41ea41e731e341df41db41d741d341cf41cb41c741c431c041bc41b931b541b141ad41aa31a641a2419e419a41964193318f4
|7,2=>0x33640000332432e432a43264322431e431a43164312430e430a43073304330042fc42fa22f642f242ef32eb42e742e342df42db42d742d34000000002cf42cb42c742c6100002c2400002be400002bd12ba32b642b242af32ab42a742a3429f429c329b1000029832944290428d328942854281427d427942763272426e426a4
|7,3=>0x4094405440143fe33fa400003f643f513f233ee43ea43e643e333df43de13da43d643d333d033cc43c843c443c223be43bd13ba33b643b333af43ab43a743a3439f439b4397400003943390438c4388438443813000037d437a337733734370336c4368436440000360435c435843544350434c4348434533414000033e333a4
|7,4=>0x458445534523450244c444844453441443d443944354431442d442944254421441e341c241844144411340d40000
|8,0=>0x519351635133510350d350a35073504350134fe34fb34f834f534f234ef34ec34e934e634e334e034dd34da34d734d434d134ce34cb34c834c534c234bf34bc34b934b634b334b034ad34aa34a734a434a1349e349b349834953492348f348c3489348634833480347d347a347734743471346e346b346834653462345f345c3
|8,1=>0x5d535d235cf300005cc35c935c635c335c035bd35ba35b735b435b135ae35ab35a835a535a2359f359c3599359635933590358d358a358735843581357e357b357835753572356f356c3569356635633560355d355a355735543551354e354b3548354625433540353d353a353735343531352e352b352835253522351f351c3
|8,2=>0x692368f368c3689368636833680367e267b367836753672366f366c3669366636633660365d365a365736543651364e364b3648364626433640363d363a363736343631362e362b3628362626233620361d361a361736143611360e360b36083605360235ff35fc35f935f635f335f035ed35ea35e735e435e135de35db35d83
|8,3=>0x752374f374c3749374637433740373d373a373737343731372e372b372837253722371f371c3719371637133710370d370a37073704370136fe36fb36f836f536f236ef36ec36e936e636e336e036dd36da36d736d436d136ce36cb36c836c536c236bf36bc36b936b636b336b036ad36aa36a736a436a1369e369b369836953
|8,4=>0x7a0379d379a379737943791378e378b378837853782377f377c3779377637733770376d376a376737643761375e375b375837553
|9,0=>0x821281f281d281b28192817281528132811280f280d280b2809280728052803280127ff27fd27fb27f927f727f527f327f127ef27ed27eb27e927e727e527e327e127df27dd27db27d927d727d527d327d127cf27cd27cb27c927c727c527c327c127bf27bd27bb27b927b727b527b327b127af27ad27ab27a927a727a527a32
|9,1=>0x85b28592857285528532851284f284d284b28492847284528432841283f283d283b28392837283528332831282f282d282b28292827282528232
|10,0=>0x86818671866186518641863186218611860185f185e185d1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 16
def pmP:Nat→Nat
|0=>0x60000000230000001120000008000000032000000150000000a2000000500000002600000012400000090000000470000002200000010800000082000000400000001600000008000000022000000100000000700000003400000018000000090000000400000001c0000000c00000004000000018000000080000000200000000
|1=>0x2080000010340000081800000409000002040000010080000080200000400000001e900000074c000003a2000001b0000000ce000000640000003180000018b000000c38000006180000030600000180000000b98000005700000028200000133000000888000004400000021e0000010c0000008200000040000000198000000c4
|2=>0x2d800000164000000ae200000563000002ae00000154c00000aa00000054f000002a600000152c00000a8e00000545000002a08000014c400000a38000005140000028980000143000000a0800000503000002800000013000000091800000488000002400000011b00000089800000448000002228000011100000088000000411
|3=>0x1098800008110000040180000200000000aa780000553000002a8600001540000008a780000443000002210000010c4000008600000042000000208800001041000008060000040200000200000000800000003f9000001d5c00000e8e00000727000002fb8000017cc00000be2000005d3000002e880000174000000b9a000005cc
|4=>0x42b780002159c00010ac600008557000042a980002153c00010a8e000085430000427080002133000010990000084c00000424c000021130000108800000841000004206000021000000103200000810e0000406600002031000010098000080440000402000002003800004b8e00002563000012a78000094c40000489800002433
|5=>0x53e3800029d9c00014bae0000a5d3000052e780002971c00014b860000a567000052b180002957c00014aae0000a547000052a180002923000014818000095cf00004ae380002570c00012a9e000091cc00004800000021d1c00010bee000085f3000042ef80002175c00010ba6000085cf000042e38000216c400010b2000008577
|6=>0x44a2700022511000110bde000885cf000442b780022153c001100800008154f00040aa38002051380010209c000805df000402c180020153c00100a8e000805000004022200020103c0010081c0008040c000402020002010000010011c0008000800040000000105000000800000003c2560001002200007115c0002880c0000a7d7
|7=>0x2000070010000300061209e0030854700140ae7800a0151c00400bc600200003000c42d780042977c00214bae0010a5c7000852cb80042553c00210bee001085d7000842e780042171c00210b2e00108567000842ab80042154c00210a8e001085270008428980042111c00200bae00100557000802880004001100020008000100000
|8=>0x384ae7801c0113c00d00a9e005085470028420780122153c00900898004804440024020600102575c00812a9e004085d7002042e78010215bc00810a9e004084cc0020420600100577000802b98004015c4002008ee00100453c00800bb80040054f002002858010013300080089a0040044c002002000010004000080018000400044
|9=>0x90142ab84802155c24010a8e10000517060802a382c02151c15200a8e0a408547050042b382802151c104009ae081095470408422382040151c08210bce041001100200123180c40151c04400a8e021085d7010002e780800171c02210a8e011005570080021180342515c01a10b9e00d08447005042b780280973c0100008000800003
|10=>0x1000422008000553c40002a8e2000150b100008a788000412040000b9e20000580100002a788000151c40000a862000050010000227880001130400008902000040810000024068c0171c34600b0e1a1085470c3042e78618216bc30610b8e183085870c1043e3860821e9c30410bae182085c70c1042db86082169c30010b8e18008547
|11=>0x1c0802e788a80573c44402b9e20f0854f103842e7881c2153c40e1081e2048854f102042aa08102153c40810a8e2040155410184ae7880c2513c40610b9e201095cf10084aa788042433c40110aae20088547100402a788020151c40012b9e200095c710004aa788002551c4001219020009040100042ef88002153c40010a8e200084cc
|12=>0x240000a8f00000547500042a7a8002151d30410b8e982085a7400842e7a004216bd00014ba68000a5c7400052b1a0002173500010ade8000856d400042a7a0002151c80000a8c3a1211c71d080ae38e342173c71210b9e381015cf
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x100000000140004
|6,0=>0x69620000400010d80041038100000000e018220001cda00000fc0e00000018a6c1c0400000000004c0a6080000c6000100009000dc380e0281c000400000f8000087c440000008000002008000c0080000001f0c8001400000000009904000008000201f1c00000220001c6a00000000002
|7,0=>0x8280082dac59f813645991000451cb59c04aa322830223fb2d36e416c80098400260200000161f47d26abeb98804808a35a9f950ac7461010523381950be200254ef24566bf40854b38e43e080a9cd56202936400e71c80000cb619d43e43ad97b1887005c81a79c832472288c0f4974a7a80044405ecbc00021c1940cb41dcd60921003000a0d5f5b89e1a63800763a
|7,1=>0x11a463c046701d9e6e20881c24b0804d8e1993c0482224009c09210e0ec2e181cca03b51468231c00193d9d42f77088003c080430a907c8c0400044484d471171a17210011c858bf06800226210015c74f1304c8a135292194030b11c2c78980840405af8bcd72e36871127489320010a0006c006e021301a3b471c1c4450f8700e0411d54088f1e0b0845407d0ca78d
|7,2=>0x4808900acf02e048d985f01a013303d0d0b8402a66520115c00
|8,0=>0x94a66e60075271e16141461375959d9a012b2c21ace496835d54b12f499384e31d99d29c84914b762525c1e09a5911a2357b08c45513c3bfaeca47e44e1cdf8adc6c36268a70a11151d76691d2edd9b9617798137428cd84fd452c206239353e3068583259f24ee92b5456d1b0b5a8ebc5eba5d4ad4cad108b0b32f728b8ab62958e452bfdef674cd50b561a922d2f7c
|8,1=>0x74a76638299adee9867353127619b9eebd9142a89baa1b2c5de6f5a9127134b5b34de89cb08953d6b814da46bac1cca2162b8c1e1f389eae519225fa6abc5979291e25898d6950957ddaa7d7f8e42d2c1e2282f2748991de74dbb125303764cc7d2356a0d84ded4b7da5345c78248af0ca802448a7ab3a2d540b0919676931d62c26783491cb6647d49dabb4cd9dd78f
|8,2=>0x1a580a691622efbbc66f5954c962fd08b01e9d876961555b15ad269bd75
|9,0=>0x9a4e5793d754e266889e5358acf6296ad16aba5327e5786b3d9ace834e3be98a94ca82f69e74db5b16cb62653566b0d89396a4f2e9389995162ed57bfd5a76ee8a53a92a44cdf6bd769b4b2ac9cbac6946e94d4593356bb26acf6388d7a72b4bb5a2c36275b6ef176
|10,0=>0x4cdd4aa99aea7132554cda8aa55
|11,0=>0x55
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 33 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_126 10 roots_126 ops++addP pm 1 dom_123 10 roots_123 ops++addP pm 2 dom_111 9 roots_111 ops++addP pm 3 dzo_47_16 6 roots_47 ops++addP pm 4 dom_85 5 roots_85 ops++addP pm 5 dom_55 5 roots_55 ops++addP pm 6 dom_63 9 roots_63 ops++addP pm 7 dzo_85_2 5 roots_85 ops++addP pm 8 dom_125 10 roots_125 ops++addP pm 9 dom_118 7 roots_118 ops++addP pm 10 dom_95 9 roots_95 ops++addP pm 11 dom_101 5 roots_101 ops++addP pm 12 dom_79 6 roots_79 ops++addP pm 13 dom_31 5 roots_31 ops++addP pm 14 dom_84 4 roots_84 ops++addP pm 15 dom_119 8 roots_119 ops++addP pm 16 dom_94 7 roots_94 ops++addP pm 17 dom_29 4 roots_29 ops++addP pm 18 dom_77 5 roots_77 ops++addP pm 19 dom_47 6 roots_47 ops++addP pm 20 dzo_117_2 6 roots_117 ops++addP pm 21 dom_45 5 roots_45 ops++addP pm 22 dom_103 6 roots_103 ops++addP pm 23 dom_109 8 roots_109 ops++addP pm 24 dom_117 6 roots_117 ops++addP pm 25 dzo_93_2 6 roots_93 ops++addP pm 26 dom_93 7 roots_93 ops++addP pm 27 dzo_125_2 7 roots_125 ops++addP pm 28 dom_61 6 roots_61 ops++addP pm 29 dzo_111_16 7 roots_111 ops++addP pm 30 dzo_46_16 5 roots_46 ops++addP pm 31 dom_115 7 roots_115 ops++addP pm 32 dzo_107_16 6 roots_107 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_85_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_117_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_93_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_125_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_111_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_46_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_107_16_42 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_126 10 s (0,roots_126.map (·&&&dom_126)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_126 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 11 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 102 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 102 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 279 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 23 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 279 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 282 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 26 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 282 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 93 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 93 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 12 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_127 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_175_16:=0xffff0000ffff00000000000000000000ffff0000ffff0000
def gzo_175_16:=0xffff0000ffff00000000000000000000fffe0000fefa0000
def gsh_175_16:=0xffff0000ffff00000000000000000000fffe0000fefa
theorem lowS_zo_175_16_42:Lower true dzo_175_16 roots_175 gzo_175_16 7:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_16) [(dom_175,16)] (by decide +kernel) (lower_slice_b (T:=gsh_175_16) [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0,0,4),(0xffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_174_16:=0x555500005555000000000000000000005555000055550000
def gzo_174_16:=0x555500005555000000000000000000005554000054500000
def gsh_174_16:=0x55550000555500000000000000000000555400005450
theorem lowS_zo_174_16_42:Lower true dzo_174_16 roots_174 gzo_174_16 6:=lower_iso_b (d1:=dom_174) (r1:=roots_174) (T1:=gsh_174_16) [(dom_174,16)] (by decide +kernel) (lower_slice_b (T:=gsh_174_16) [(0x50500000505000000000000000000000505000005050,0,4),(0x55550000555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
namespace S_191
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,10),(2,34),(2,130),(3,11),(3,19),(3,35),(3,131),(4,20),(4,36),(4,132),(5,13),(5,21),(5,37),(5,133),(6,14),(6,22),(6,38),(6,134),(7,15),(7,23),(7,39),(7,135),(8,9),(8,10),(8,40),(8,136),(12,13),(12,14),(12,28),(12,44),(12,140),(16,17),(16,20),(16,144),(18,19),(18,22),(18,26),(18,50),(18,146),(24,25),(24,26),(24,28),(24,56),(24,152),(32,33),(32,34),(32,36),(32,40),(32,160),(48,49),(48,50),(48,52),(48,56),(48,176),(128,129),(128,130),(128,132),(128,136),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffff
def xsM:=roots_191.map (·&&&dom_191)
def gM:=goal_191&&&dom_191
def NN:Nat→Nat
|5=>12
|6=>69
|7=>201
|8=>216
|9=>74
|10=>11
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xbc21ca5cf1916fd8217b71d2865ba15b4c34f2934bf412f96701a4d00fdb
|6,0=>0xfef37fc8e4fc66ffc630fab63f62c6f5838ea416e529bdd565d3b16d0b13cba03c83acc4929bec4fbaf37bae1cbab81b085caf061a9387a09139fe869ee4f9d2c99527686e53850368436a7e9dd7c3ac7a20e74db76d88668bcd649b5643be5d84959f8d533055139550be54fee54852546172435473b31d34c04328a93103f21e221f33c1dca11a9ab17a1c1760516b781610614146128a011b0e0d9230d30d0ae5d09d500799406d4d050e3
|7,0=>0xa44bda2b49a2350a2324a0f3a9fd7e9fac89f3969ea4e9dbd69d2c99c3f89c0599a4ab9a4759a0a79822b97b299747292d159197b8e2028d1678b8fd8b2b18b2888aedc8a4f68665085cc3850368440d8320e81e598199f808b97e9dd7d1e77c3487bfa47bb9c7b6cf7a5bd7872d76ec576e4b75c8e759c074f5e74cc274c2e723f9715d2708a16fe176f32668ede684306822965e1f65125647316426263d8c62dfe61fd75bcd15b46a5b0f85a0b955f9e55e4054ee554a0b52bbe51a08516b850448502204e2334e0434d5364836645d6a454894513d406d63e5cb3e26d39425375cd34864344673356932dcc31d703194028eaf289a5285192706225ecb2398021ad01dca11d42b1a20e18f66184d911e321175b112bf0f3cf0ed450d9120cad10b10d0ae5d0a9930a68709c2809be3092e50929b0821603632033ae026eb
|7,1=>0xffc36ffb8bfe11dfaf95fa3c6f83dbf83a6f80f7f6c2ff5845f4d94f417af3ee5f3ccaf201bf1d82f0ed6f0dceeee21ee1c6ea5d7ea00ee96d1e8151e7945e130ae0f36e04afdf4ccdd4d7dccd6db53ad9576d8bd8d8ae2d6ea5d3c6cd2e2dd29d8d1701d0fe0d0855cba4ecba42cabf6c7bb5c74a1c5030c418cc2fcec0feabf24cbeb5abe4b2bd9ecbd5e1bb7b4baf37b89acb6cf6b3f7ab2928b117ab0a70b0595afd73abf40aaefca9872a9292a85a9a80b9a4aa1
|8,0=>0x935ea9125a8d3468aca18aaeb89d598991288ef68832386e5d854b98404383c4382767814927ed157e9dd7cd877c68a7c3487c1ba7911178d6c772117702976d5676b8773fd97250c724c971d3d6fe9a6fbf16ef4e6c4996b6506b1f06a52d6964f6819567a78653b364e5f62661606115fb045f8745ea715e7865c0095bfbc5bd275bcd1595545927258500582da57af656c635532954ee553f2252419520b5516cf5122b4f59b4dcb74cf8b4c2684a23c49c2747bf2479d94513d40a1a402083f08f3edf33e65a3e2563d6513ba1d3b6213a745339a13374a32dcc305052f2e32e0f52e02d2cc582c77e2aba9291b02612c24a3824512224311fee01d42b1c6a4199fc1876516e2216b03166c513740126fa100c00fb4e0e4a60c82d0c6c90c2a70bba20a9700a08a09fce09e4a092e5092d4076c906855064a404c1a00a6b
|8,1=>0xff388fe268fb1a9fa71ff9fa6f9d0bf9a95f952cf6044f5bb7f5b39f45f7f347ef3472f19a0ee676edb05ece7deb050e9c25e7c18e6d14e618fe241ce1808e0b6dded07db77cdb499db132dab28da693da23bd9414d8daed89e4d4b07d270cd181ace945cd738ccb54cc368cb211ca05bc8cfbc828ac7b2fc1bc3c175abf446be3bdbde71bd6d4bc678b7fa7b6b25b56f2b4ea4b49b2b357eb2401b0a70b07d3af5d6aec5aae836ae272ac878a9f28a95daa85a9a8137a47dea1e4ba0f3a9fc7c9f40f9f3969eeb79c73a9a3fa998c897e7997926961ca9529b93ba3
|9,0=>0xfd834f5794eded9e856ee7a39e1ddbe0b7ddf384da0afd7786d5f94d5cb4d34dfd2f3cd2c0cd22a4d092dcffd7cb2b5c7946bfa90bd6d4b9364b68afb2c59b207eaa6d9a7647a3967a148d9f396978929724c96ce59377392b4a8aec389cd084d1c81b4071c8c7003e6d62b664a76135e6109b5f367541ae53785526dc4f9644eb564c9ff4c4cb4ba964b0d44a160430a140a5d39aea2efb32eb272096a2038f1ff421a2bd16b3f0ff790d9b60d4c40bd9a09a56092e503a23
|10,0=>0xe03e0c84bec4e91af5c96f1d76d589644614f6342eaa62e0371deb5
|11,0=>0x2bff1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffff00ff000000000000000000ffffffffff00ff0000ff00ff00ff00ff000000000000000000ff00ffff00ff0000000000000000000000000000000000ffffffffffff0000ffffffff000000000000000000000000ffffffff00000000ffff0000ffff00000000000000000000ffff0000ffff0000ffffffffffffffff0000000000000000ff00ff00ff00ff00cccccccccccccccc0000000000000000cccccccccccccccc0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0000ffaaffaaffaaffaa0000000000000000ffaaffaaaaaaaaaa333333333333333300000000000000003333333333003300ffffffffffff00000000000000000000ffffffffffff0000ffffffffffffffff0000000000000000ffffffffff00ff00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa003300330033003300000000000000000033003333003300ffffffffffffffff00000000000000000000000000000000
|0,1=>0xffffff00ffffff000000000000000000ffffff00ffff0000ffffffffffffff000000000000000000ffffffffffff0000f0f0fff0f0f0fff00000000000000000f0f0fff0f0f0fff000ff00ff00ff00ff000000000000000000ff00ff000000000000000000000000000000000000000000000000ff00ff000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f00ffffffffffffffff0000000000000000ffffff00ffffff00555555555555555500000000000000005555555555555500003300330033003300000000000000000033003300000000000000003333333300000000000000000000000033003300ffffffffffffffff0000000000000000ffffffffffff0000ff00ff00ff00ff000000000000000000ff00ff0000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ffffffffffffffff0000000000000000ffffffff00000000fff0fff0fff0fff00000000000000000fff0fff0f0f0f0f0ffccffccffccffcc0000000000000000ffccffcccccccccc
|0,2=>0xff00ff00ff0000000000000000000000ff00ff00ffff0000ffffffffffffffff0000000000000000ff00ff00ffff0000ffffffffffff00000000000000000000ff00ff00ff0000000f0f03030f0f030300000000000000000f0f03030f0f0300ffffffffffffffff0000000000000000ff00ff00ff00000000ff00ff00ff00ff000000000000000000000000ff00ff00333333333333333300000000000000003333333333333300ffffffffff00ff000000000000000000ffffffffff000000000000ff000000ff000000000000000000000000ff00ff000f0f000f0f0f000f00000000000000000f0f000f0f0f0000000000000000ffff000000000000000000ff00ff00000000555511115555111100000000000000005555111155551100ffffffffffffffff000000000000000000000000ff00ff00ffffffffffff0000000000000000000000000000ff00000000000000000000000000000000000000ffffffff00ff000000000000ffffffff000000000000000000000000ff00ff00
|0,3=>0xffffffff000000000000000000000000ffffff000000ff000000ff0000000000000000000000ff000000ff00ffffffff0000ff000000000000000000ffffffff0000ff0000000000000000000000000000000000ffffffffffffff00ffffffffffffffff0000000000000000ffffffffffffff00ffffffffffffffff0000000000000000ffff0000ffff0000ffffffffffffff000000000000000000ffffffffffffff000000000000000000000000000000000000ff00ff00ff0000ffffffffffffffff000000000000000000ff00ff00ff0000ffffffffff0000000000000000000000ffffffffff00ff00ff000000ff0000000000000000000000ff000000ff00ff000000ffff0000ffff00000000000000000000ffff000000000000ffff0000ffff00000000000000000000ff000000ff00ff00ff00ff0000000000000000000000ff00ff00ff000000000f000f000f000f0000000000000000000f000f0f0f000000ff00ff00ff00ff000000000000000000ff0000ffffff00
|0,4=>0x3333000033330000000000000000000033330000330000000000ff00ff00000000000000000000000000ff00ff00ffffffff00ff00ff0000000000000000ffffff0000ff00000000000000000000000000000000000000000000ffffff00ffffffffffffffff000000000000000000000000ffffff0000ff00ff00ff00ff000000000000000000ff00ff00ff0000ffffffffffff00ff0000000000000000ffffff00ffff0000ffffff00ffffff000000000000000000ffffff00ffffff00ffff3333ffff33330000000000000000ffff3333ffff3300ffffffffffff00000000000000000000ffffffffff00000000ff00ff00ff0000000000000000000000ff00ffffff00000000ffff0000ff0000000000000000000000ffff0000ff00ffff00ffffff00ff0000000000000000ffff00ffffff0000ff00ff00ff00ff000000000000000000ff00ff00ff000000ffff00ffffff00ff0000000000000000ffff00ff000000000000ffff0000ffff00000000000000000000ffff0000ff00
|0,5=>0xff00ff00ffff00000000000000000000ff00ff00ffff00ffffffff000000000000000000000000ffffffffff00ff00ffffffffffff00000000000000000000ffffffffffffff0000ff000000ff0000000000000000000000ff0000ffff0000ffffffff00ff00000000000000000000ffffffffffff000000000000ffffffff000000000000000000000000ffff00000000ff000000ffff00000000000000000000ff000000ff000000ffff0000ffff00000000000000000000ffffff00ff000000000000ff00ff00000000000000000000000000ff0000ff00ff00ffffffff0000000000000000ff00ff00ffffff00ff00ff00ff00ffff0000000000000000ff00ff000000000000ff00ff00ffffff000000000000000000ff00ff0000000000ff00ff00ff00ff000000000000000000ff000000ff0000ffffffff00ff00ff0000000000000000ffffffff00ff0000ffff0000ffffffff0000000000000000ffff0000ffffff0000ff00ff00ff0000000000000000000000ff00ff00ff0000
|0,6=>0xffffffffffffffff0000000000000000ff000000ff00ff0000000000ff00ffff000000000000000000000000ff00ff00ffffffffffff00000000000000000000ffffffff00ff0000ffffffff0000ffff0000000000000000ffffffff0000ff0000ff00ff000000ff000000000000000000ff00ff0000000000ff00ff00ff00ff000000000000000000ff00ffffff000000000000ffffff00000000000000000000000000ffffff00ffffffff000000ff0000000000000000ff00ff0000000000ff00ff00000000000000000000000000ff00ff000000ff00fff0fff0f0f0f0f00000000000000000fff0fff0f0f0fff0ff00ffffff00ffff0000000000000000ff00ffffff00ff00ffff00ffffff00ff0000000000000000ffff00ffff000000ffffffffffffffff0000000000000000ffffffff00ff0000ffffff00ffffff000000000000000000ffffff0000000000ff00ff00ff00ff000000000000000000ff000000ff000000000000000000ff000000000000000000000000000000ff00
|0,7=>0xffffffff000000000000000000000000ffffffff0000ff00000000000000ffff0000000000000000000000000000ff00ffffffff00ff00ff0000000000000000ffff000000ff0000000000000000000000000000000000000000ff000000ff00f0f0f0f0f0f0f0f00000000000000000f0f0fff0f0f0fff0ffffffffffffffff0000000000000000ffffffff0000ff00000000000000000000000000000000000000ffff0000ff00ffff0000ffffff000000000000000000ffff0000ffffff00ffffffffffffffff0000000000000000ffff0000ffffff000000ffff0000ffff0000000000000000000000000000ff00f0f0f0f0f0f0fff00000000000000000f0f0f0f0f0f0fff0ffffffffff00ff000000000000000000ffff0000ff000000ffffffffffffffff00000000000000000000ffff0000ff0000000000000000000000000000000000ff00ff00ff00ff00ffffffffffff0000000000000000000000ff00ff00ff0000ffffffffffffffff0000000000000000ffffffffff000000
|0,8=>0xffff0000ffff00000000000000000000ffffff00ffffff0000000000000000000000000000000000ffffff00ffffff0000000000ffff0000000000000000000000000000ffff0000ffffffff00ff00ff0000000000000000ff00ff0000000000000000ff000000ff0000000000000000000000ff0000000000000000000000000000000000000000ffffffffff00ff00ffff0000ffff00000000000000000000ffffffffffffff00ffffffffffffffff00000000000000000000ff000000ff00ffff0000ffff00000000000000000000ffff0000ffffff00
|_,_=>0
def sP:Nat→Nat
|0=>0x2050d0309021c1b0c0b1302061a000c190b070a03090c0b13030918000c0b1013020800040b0302171600150c0b100a03020512070a0309050d0309020e0504110206000f0b10020800050d04100302050302060e000c0b100a02080f0b070908000503020e0100050d040703090c0b070a0908050407030600050403020100
|1=>0x120b100a0302051213030902220c0b1302060800050d12071303090c190b100a03020512100a0302050b0309020e00150f0b10030200052112130309020f0b1409020800050309020e000512130302060005120b070a03090b0302061c20001e120a030902040c0b07030600040c0b030201000c0b0a1d020600050d04140309
|2=>0x90205120a0309022a0c0b1303022900120c0b0a0902260c0b0302060e000c0b130902260028120b0a0309020c0b1303020600050d12101303020c0b0a03090227150c0b110a09020f0b030217160005040b110902000c0b0a090226000c0b03020e01000c0b1303180600120b13030902250504110902000c0b130324060005
|3=>0xc0b0a1409020805122e13030902050d1211130902050410030200051213030902250c0b0713090800150c0b070a03090c0b1302062c000504140302060005040b0703090005120b110a09020c0b1309021a00040c0b11020600050d12130302060f120b0a0902080504070309000512110a0902150f0b110902000f120b2b03
|4=>0x120b13030902230c0b13030918000f0b130302062000390f120b0a030902050c0a130309023736120b1303090200040c0b13030902000c0b1303020633000f0b0309021c20000c0b130902081b000512132b030902120b0a132d0309020c0b13090231000c0b0a03090230150f0b0703090005040309020e0005040b10030200
|5=>0x200120c0b0a420309020c190b1303020600120c410b0a030902120b0a130309023f051213030206000c0b130309024000120c0b070a0309150c0b1113090200120c0b132b0309020f0c0b0302061c00040c0b0309020e000f0b0a0309023f003d120b0a0309023c0f120b130309020c0b0a1303091800050d12131403090205
|6=>0x120b07030900050d0412130309023b0c0b130309020012130309024500040c0b0302061700120c1f0b0a030902120c0b1309022600120b0a030902440c430b0a030902000c0b0309020e0005120b1303020600120c0b13030206000c0b1303020634000f0b130309023f00120c0b0a13090208120c1f0a03090228120b130309
|7=>0x120c0b130309024b040c0b0309024a000f120b0a0309021c120b1303090245000c490b0a030902000c430b13030902000f120b13090208000f120b4203090200150f120b0a030902120c0b1303022900120c0b100a03020c480b0a030206000c470b13030206000f0c0b13030918000512111309020005461213030902000f
|8=>0x21c1b0005120a13030902500f120b0a030902330c480b13030206000c0b130302064000120c0b1309021a000c0b130902081c00040c0b110902000c0b130302064f000c0b070a0309120c430b0a0309020c4d0b0a030902003c120c0b130309020c0b0a030206170005120b1113090200120b130302061600040c0b13030206
|9=>0xc0b0a0302063e000c0b0a0309024a000c0b13030206000c0b1303090258000c0b5613030902000f120b10030200120b1303020620000512135503090200040c0b1303022900051213030902540012480b0a030902200f520b1303090200050d12130309021b0504140309020012510b1303090200150c0b0713030900050309
|10=>0x1303020600150c0b0a140309025d120b13030902000f0b070309000f12190b0a0309023c040c0b130309020c0b0309024a1b005b12130309020005040b1403090200040b130302061600050b0309021c1b000c0b0a130309023705120a132d0309020c0b13090226000c0b1303020617000512132d0309020c56130309025900
|11=>0x2061700120b130309023f00390c0b1303020600040b0309021c20000c0b130309024a000c0b0a13030229001e0c13030902000c0b130309021c00040c0b0a1d0902000c0309025f000c0b13030229000f0c0b56030902000c0b100a030205120a0309021c0c0b1314090208000f120b0a03090234040c0b1309021a003b0c0b
|12=>0xb1309021a000c0b0a68030902000c0b6613090200120c0b0a0309022a3c0c0b0a13030902120c0b0a0309024a0c0b6513030902000c640b0a0309020005120b0a0309021c040c0b0302061c00150c0b10130302000563121303090200051207130309000504121303090200120c620b0a030902040b1303020620000f0c0b03
|13=>0xc0b42030902000c0b0a0309026b00040b130309023f0005120a140309020c0b130309026a000f0b1003020039120b0a0309020b0309021c2000040c0b07030900150f0b14030902000f0c0b0309024a00120c0b130309180005120b0713030900120c0b110a09020c0b0a1309021a0005120a130309021c1e1213030902000c
|14=>0x5122f130309020005120b0a14030902120c0b136f0309020f0c0b130302290005121013030200040c0b14030206000f120b0309024a00050d12130309021c05121303090245000f12480b0a030902120b130309026e00056d1213030902000c190b0a14030902040c0b13090208003c0f0c0b0a0309020c0b0a0302061c0004
|15=>0x550309020005120a13030902380512130309022305120b10130302000512130309023812510b0a130309020c620b0a030902120c0b0a1d09020c0b130302061c000c0b130309026b000f0b130302061600120b0a1303090250057012130309020039120b0a130309020f120b11090200150c0b1303020600040c0b1303091800
|16=>0x7130309000f120b0a13030902040c0b1303090200120c430b13030902000c0b130309023700120c190b0a1303090204120b1303090220000c0b1303090273000c0b130309027100120b132d0309020c0b0a0309022a0f0c0b1309021a000504121303020600040c0b100302000c0b130902261c00120b0a0309021c20120b13
|17=>0x90269000c1f13030902000c0b1342030902000c0b7413030902000f0c190b13030902000c410b1303090200120c0b0a130309023404120c0b13030206000c0309025060000c0b0a0309026900280c0b13030902000f120b1403090200040c0b0a0309023e000c483203090200120c0b1303090223150c0b130309021c000c0b
|18=>0x30206000c0b136703090200390c0b0a03090200120c480b0a0309020c1f0b130309020039040c0b13030902000c0b0a140309020c0b130309024b00120b130309022000120c130309025c000c0b130309027600050c130309024a003b040c0b13030902000c0b0a1303090240000c0b1303090240000c0b1375090200051303
|19=>0x3b0c0b0a13030902007a120c0b13030902003b0c0b13030902000f0c480b0a030902000c0b10130302000c0b130309024c000c030902503e000512130309021c000f120b130309023400390c32030902000c0b130309027900150c0b1314030902000c510b1303090220003c0c0b13030902000c770b1303090200120c0b13
|20=>0x30902000c0b130309027e000c0b0a130309025000120c0b130309024a000c430b130309020005120b130309021c00390c0b0a1303090200040b1303090220000c3a130309026900120c480b0a130309020c0b7d1303090200120c0b1335030902000c0b137b090200120c620b130309020005120a130309020c48130309025a
|21=>0x50c131d090200120c0b651303090200120c0b11130902000f0c0b13030902400005120b0a13030902120c0b0a0309023e050c0a130309023800040c0b0a1303020600040c0b0a0309021c00050c1303090238000c510b0a1303090200040c0b1303020600040c0b0309021c000c510b130309020005130309025a000f0b14
|22=>0x1303090250003c0f0c0b130309020015040c0b1303090200390c3a1303090200390f0c0b0a030902000c130309025c00120b13030902500005121314030902006c0c0b0a13030902006c0c0b130309020039120b1303090200050c132b030902000c0b0a132d030902000c780b0a03090200050d12130309020c0b132d030902
|23=>0x309023f0005120b131403090200050c1303090271000f0c483a1303090200053d13030902000c0b0a13030206000c0b0a0309021c000c0b13030206000f12480b1303090200040c0b130309021c000c0b5613030902007f0c0b1303090200050c1309020800050c1361030902003d0c0b0a030902005d0c0b13030902000c3a
|24=>0x1335030902000c620b13030902000f0b0a0309022000120c0b131d090200040f0b130309022000040c0b1303090233007a0c0b13030902000c480b130309021c000f0c0b130309025300050c130309023700040c0b14030902000c0b0309021c1b000c0b0a130309023f00120c800b13030902003b0f0c0b13030902000c0b13
|25=>0x30902000c0b11130902000c783a1303090200120c0b1309020800150c1303090250000504121303090200120b0a1303090220150c0b130309021b000c0b0a130309021c000c0b130309024a00050c13750902000c0b0a03090244000c0b130309021c00040f0c0b1303020600040f0c0b0309021c00050c1342030902000c0b
|26=>0x7130309000504120b130309020004120c0b1303090200040c0b1303090234000f0b1303090220000c0b130309025700390f0c3a13030902000c190b0a0309024e000c190b1303090220003d120b1303090200120c0b13030902810c0b651303090200040c190b1303090200120c0b0a0309021c0c486103090200390f120b13
|27=>0xc800b1303090200120c0b0a130309021c120c0b1303090240005e120b1303090200050c130309025300120c1f1303090200520c0b1303090200120c0b13420309020015120c0b0a13030902390c0b72030902000c430b130309021c00120c410b13030902000f0c0b13030206000c0b0a1d0902000f0c0b0309021c00120c0b
|28=>0x2000f120b0a0309020c0b130309028400120c1f0b13030902000c770b130309022300120c0b0a140309020c480b0a0309022000120b1303090244000c0b0a1303090238000f120b0309021c00040c480b0a03090200820c0b1303090200050c0a1303090250000f0c0b0a03090233000512130309021b000c0b130309023800
|29=>0x57000f0c0b1303090233003b120c0b13030902000f0c190b0a03090200150f120b13030902000c0b1309020800120c0b1013030200120c0b130309024c000512130309025000051213320309020005120b130309021b00050c0a132d030902000c0b13030902341b00050c132d03090200120c0b0a13030902330c0b132b0309
|30=>0x20015050c13030902000c0b130309027c000c0b0a1303090220000c0b0a0309024e000c0b130309022000040c0b0a13030902000c13720309028600040c0b1303090200120c0b130309023e000c480b1303090220000f120b130309021c00040c480b1303090200040c0b1303090240000c0b0a85030902000f0c0b13030902
|31=>0xb133203090200390c0b13030902000f0c0b0a030902000d0c0b1303090200040f0c0b1303090200050c13720309020015120c0b13030902000c0b130309025300830c0b13030902000c483a13030902000c0b130309021b000c0b0a0309023e000c0b1303090269000c480b0a13030902000c0b1303090260000c870b130309
|32=>0xc0b130309023400390f0c0b13030902000f120b13030902000c780b1303090200120c0b1314030902000c0b1303090281000f0c0b0a13030902000c0a1303090286000c0b130309025a000c3a0b130309024e00050c0b1372030902000f0c480b1303090200120c0b0a130309020c0b130309025000120c0b130309021c000c
|33=>0x90200050c0b0a13030902000c0b13030902440004120c0b13030902000c0b0a1303090233000c0b1303090233005e0c0b1303090200050c0a13030902000c880b13030902000f0c3a0b1303090200050c130309026000050c4813030902000c0b130309021c003d0c0b13030902000c480b7203090200150c0b130309020012
|34=>0x21b000f0c0b7203090200050c3a13030902000c0b131d09020005120b13030902000c0b1303090234000c0b130309022300050c1303090250000c190b0a1303090200050c1332030902000c190b130309020039050c1303090200050c130309023e00120c480b13030902000c0b131403090200050d0c130309020005121303
|35=>0xc0b1303090200120c0b13030902000c0b137203090200050c0b1303090200050c13030902000f0c0b13030902000c1303090286000c3a0b13030902000c0b130309023e000c0b0a13030902000c0b130309024e000c480b13030902000c480b0a030902000c0b136103090200120c0b130309
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x21300f1806cc030601530091803cc018600930031800cc0006
|6,0=>0xfcb87c9c3d6e1e560ef3875dc3a0e1c970e1386edc368e1ad70d33867dc330e19260c630615c2fce17770b8385a5c2c4e15b70aa38535c28ce13f709c384c5c254e123708e38455c21ce1086080b83e9c1e6e0ec7072b8379c1b0c0d170653830dc178e0b66057b82a1c142e09b604a38235c10ce07f703c381c5c0d4e063702e38155c09ce0486
|6,1=>0x21c710ab8839c40ee2007
|7,0=>0x207c101e07ff03f781f7c0f9e07bf03d781e7c0f1e077f03b781d7c0ea1c741039881c840e25c703037a71b940daa06c6e35b81a9c0d2e0688e33c819ab8cb6064b031d818ac0c36060ce2fe817b40bba05cd02de816bb8b3e0590e2c0815c40ac2055102a0814cb8a4605130281813cc09c9c4d50262812d4094a04950242811d408ca0456e2238
|7,1=>0x2fe417d20bd905e482ee417520b9ae5c582dec16dd8b60e5a882d13166dcb27058b82c1c15ee0ae7056b82b2b15760aab054d82a3394fa0a6d052e82934147a0a2ee50f82843940209f104f08274b938609b304d272654130a097504b282554128a093504937245c120e08f8e47482364119208b90454822641115c87b04376217c109e083f04178
|7,2=>0x3f639f920fbae7d583e739f1dcf7f07b783d7c1e9e0f3f079783c839e220f01077883b841da20ec1075973a8c1d260e8307398398c1ca60e4307198388c1c260e0306f98378c1ba60dc4e6da836a31b35cd8ce6bf735bc1abe0d4f069f834c39a420d110681733d399ca0cd6e663832dc194e0c970643831dc18ce0c570623830e398520c1906048
|7,3=>0x83174153a08a103508137405c200e0ff707f38
|8,0=>0x51c428be544f0a1e950bba83a540ee9ff84fb4a7b653cb09dc94eaba736138ce9be84daca6b9d34d099d94ca4a6321309097c84ba425b212c9095c84a9ca531d289093c849a424b21249091b94894a42a1206e8fc747aba3b611cb08dc946a4232e518528bb7459c22ae1147089a9449ba22e1105287b7439c21ae10c5285a8428ca122508108388
|8,1=>0x624430fe586d2c2e86134307a182b2c0c9601cafee17e52bea85f0caf69d7a50bca85e1baeea57632ba985d0c2e69d7250b8a85c142dea16e32b6895b042d5e56a0eb4885a042cde565f0b27858fc2c5a561d0b07757fc2be1d5df2ae7856f4ab5a159d0ac5955e4aace55570aa2954d42a4a15150a83753e3a9d214d72a62952d4294654912a408
|8,2=>0x72ecb9561c992e44871dcb8ce1c552e22870ccb8425c110e0086fc437be5bcd2dde86eb4373a1b8d0dbd96da4b6b21b472d9a96c94362ddb070d7b86b94b5a65ac12d5886a84351e5a7d2d359696c34961a3b0d14968643415d9f92cf57676c339619bb0cd58666c331259772cb386563b29219390c9396454b20a18f50c7286354318a18b32c509
|8,3=>0x7954bc865e312f0f9783c3bfa5deb2eec9771cbb6a5da6eecb87614baea1d650ea997504ba5e5d1f0e86973f439dddcdf0e669
|9,0=>0x89ecc4d6225b1125888ec445262191104887ebc3d261d910e3986d4c34a219510c2885d442c6615310a1884cc424621131081883c4c1be60cf105f882b4c13a208b303d881ac40b26047301a98094402a20032ff987f8c3fa61fc30fd897e843f1e5f7f0fb787d7c3e9e1f3f0f9787c74be1a1efd0f7687b743d965ebb0f5587a64bd121e790f339
|9,1=>0x231d118688becc5d622db116678af4455a229d11468
|10,0=>0x479223b911d488e6bc716237cf1b688d74469a233d11968
|11,0=>0x11ec7
|_,_=>0
def wAt:=mkWire dB 137 192 0xffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x14094484c13004300105230302d121385025121304c010c004302d14094484c1300430010414c484c12134302d120b450251213030010c134540f120b4484c0414c484d0c0b4484c0c0045009121304c010c004307d0b144484c1300430010409c484d14024484c0410c484d14094484c14024484c130043001130045025120b4484c0c004500912130302d130043001
|1=>0xc00448b7050a04c01120b44c0114024484c0c004302d12134500912130304d1503c482d13004500912134302d1213030010c0b4500d121304c010c004482d1213030010c134304d150a04c010c0042853121304c011213c105312130102712134543c13004482d0c004304d120b4484c1300430011306810270f004243a1c1b4484e1213c500d12134302d121303001
|2=>0x500c302d12138ec0b0f3a42c010c1341027040cc3c010c1343c2d0c1344c010c004e001050ac302d1300430d51334c482f0c00448d51334c482f0c004104f040cc3c010c134300132004144c0c0b4142813004302d0c0045009120b4484c0c004304d0414c484d0c0b4484c0c004302d12134502512130484c1503c482d2f00414730c0b4484f0c0b4484d14094484c
|3=>0x131c4484f0c198e84d0b004304d1503c482d130042c51121304c010c004543c120b430010c134544c120b44c010c00448fb0b13830660b0a44c010409c302d121343001130045009121303001120b4484c0c0045428120b44c010c00410270413c3c010c134105312130484d0c00430660b0a44c011300430010c3e42c4e3900c3c2d0c134ec0b040b43029121303001
|4=>0x121345025121304c010c00410270c0a44c010b1342c190409c3c010c134ec0b0f3a42c0114034302d12130300105040302d12134300114024484c0c004304d1213430010500c302d040b4486d1213830010514c302d1213030011306810270f004304d0b144484c1300430014303c2c711213c3001130043c2f0c134706d12138484f0c004102712134302d0c0041027
|5=>0x14034484c0c00410270f004304d14024484c1300430011213c653b0c1382c293b00c102d1213430011306810270c0a44c0114034484c0c0b430010c0681027121343001121b4484e0c00530011248830010b134544f120b4484d0c004484f0c1344c010c004145312130302d0b1c448531213030011503c482d0c134544c0c004304d13004482d0c004304d3b09c102d
|6=>0xc0044d690c3a8ec4f040b43029130041027121b4484e0c0044d5d0f3a8304d14094484c0c004304d040cc10271213430011250c144f0c0b4102d0f004304d1232c144c0c0a82c4d0c134314d3a13c2c0112138484d0c0b4484c0c004482d14024484c0c004484e0c0b4484f0c0044c010c004144f0c0b430010b0a84c010c13410270f004304d3b03c102d12134484d
|7=>0x120b4484c0c004304d120bc4c010c004ec0f040b43c010c1341027040b43c010c134482d121304c010c005782d0c1b4484e0c00450091213030010c134304d0b0a44c010c004e4030f0043c2d0c13431710b14c484c0c004484c12134302d0c06810270f004304d12138484f0c0b540010513c302d1300414280c0b44c010c0050c0f0b1c4484f0c00414280c0b44c01
|8=>0x14094482d1213030010c0b45009121303001131c4302d1213c3001124802c4d1300430010409c30290c0a84c011306810270f004304d3b0cc102d121343001040cc484f1213430013b09c102d0c0a4a02d0c614e84c0b0043029033e42c4e13005418105138144f0c0b4ec270f3a42c010c1344d5d0f3a82c010c1344c0114094484c0c004484f0c0b44c010c004540f
|9=>0x1213c484d0c004484d14024484c0c004482d1213030010c134ec4f0f3a42c010c134ec0b040b4484d0c0b4500912130300114034484c1300430013b03c102d0c0a4484f0c0b44c010c004307d0b144484c0c004ec0f0f3a42c010c13429a70c4882c4d670344d6b0c3a82c010a14c484c13004e403130043c2d0c134544f120b430011213c302d0409c484f121343001
|10=>0x409c484d1513c482d0c00414030c0b4484f0514c302d1213030010b134304d1300430010c6584cd1120bc3001051bc302d121383001121302c291300430011503c482d1213430013900c3c2d0c13410270413c302913005b04f0c3342c2a1300430290c1982c2913004484c0c0b44c010c0045453120b4484c0c00450251213030010c1343c2d0c1344c010c0041033
|11=>0xc004302d14094484c0c004142b0c0b44c010c004302a124802c4d130043001130040cf90b13830016c13c30cd13004301a0f004304d0c004144f0c0b44c010f0b4304d13004300114034484c0c004304d0409c482d1213430013b02c102d0f004304d051cc302d1213c3001121304c010c0b43001350044cd3120bc30013b09c3ce90b004302d14094484c0c004484c
|12=>0x5130302d0b1346c01121383001120b4484f0c00450091213030010c1344c010c004486d1213830010b1c4484f0c00540010513c302d0b0a44c010c0041033121343001440043c2f0c13415cb0c0b44c03050a04c010c0b430010a14c484c1300430013b03c3ce90b004302d0409c484d0c004484d14094484c0c004484f1300449430513c302d13004302d1b004484e
|13=>0xb13410331213430010b14c484c0c0042c8e4e004304e1513c14010c0b4102d0f004304d040bc302913004102f0f004304d03604144e0c0b431220c0b42c4d0b144484c0c004544c0c3a42c010f3a02c010c134e84d0b004304d123ec2c4e0c004482f1300430010409c484d0c004144e0513c302d0c4884c010b13431853a1302c011213030010c13430290b1384c01
|14=>0x123e42c4e0c0043ce90b004304d130042c4d0c13450251213030011248830010b1342c4e0513c302d0c0b4484f0c004482f0c004304d05134144c0c0b43ceb0b004304d120b4484c0c004302a13004e4030f0b4304d780042d390c1381027121343001135ac30ea0b0044c010f0b4304d0b1344c010c0042c511213030010f0043c2d0c134484c130043001690043122
|15=>0x1300410270f004304d1213c484d0c0042c810c0a84c010c0b430ea0b004484c0c004304d0b208302a13004144f0c0b44c011513c482d0c0042c711213c30011213c302d0c0044c010f0b4304d0c0a4302a1300431220b1342c010b1344c010c004e93b0c1382c011334c482f0c0040df13a1382c011248030010b134302d1300430010b13430ea0b004102d0c0a44c01
|16=>0x1213030010513c302d0c004302d1213030010c3342c2a1300430cd0b0a84c010f0b430010c134c80105130302d050a0302d130044c010b4e4304e0c00414030c0b414280c0b44c010c0b40cf90b1384cd1120bc300114034484c0c004102f0f004304d13004302d0c0042c4e130043001050ac302d1300410270c0a44c010413c302913004142b0c0b44c010b204302a
|17=>0xc198e84d0b004484c0c0b430010572c302d1300c304d0b1342c010c0b430f90b13810270c0a44c010413c30291300410270f004304d0b13430010c134484f121343001135a430ea0b00431f13a1382c011503c14010c0b4302d3a1302c010c3e42c4e13005782d0c7244c030b004144f0c0b4e4030f0b4304d120b4484d0c0043c2d0b004304d130043c2d0c1342c53
|18=>0xc3a42c0103604144e0c0b44c010f0bc304d1214c484c0c00410270f004304d0413c3c010c134544c05004302d1334c482f0c00449200c0042c4d0c134302a130040cf90b1383001040cc3c010c1342c2a0c0a44c013d00430f90b138484f0c004304d3a13c2c0150004144f0c0b4484c12134300112138484f0c00430660b0a44c010b1b4484e0c0043ce90b004304d
|19=>0xc004482f1213430010c134302a130043cea0b004304d0f0b42c010c134304e0b0a44c010c0a84c010c00430f90b138f8010b138300113344482f0c00430290b0a44c011213c4c010c004e84c0b1342c010f0b430010c134500d1213030010b0042d390c138540f120b430010513c14010c0b4302d1213430010c0a84c010c004482d1213830010413c302913004544f
|20=>0x513c302d0b0a84c010c134302d121383001050ac302d130042c6d1213830011213c4c010c004102f1213430010c1b4484e0c004302d3a13c2c010b144484c0c004314d3a13c2c0115130482d0c004482d1300430011300c3c2d0c1342c711213c3001123ec2c4e0c00410270f004304d033e42c4e13004104f0f004304d14024484c0c004484d0c0b43001131c4484f
|21=>0xc134540f0c3a42c0114094484c0c00449220c0042c4d0c004144f0c0b4300105130302d12138302d0c00414280c0b44c01050a0302d130042c2a13004300132004144c0c0b4304d1300430010b1c8484f0c0042c511213030014e004304e121304c010c0042c4d0c0a84c010f0bc30010c134142b0c0b44c011213c30010c1343029130042c4d830b43c030c1344c01
|22=>0xb0043c030c1342c4d0b004484e0c0042c4e1300431220b1344c010b134144e0c0b520030b13414010c0b4e84e0b004302a13004304e13004302a13004302913004302e1300c3c010c1342c4e0c0042c4d0c0a84c011213c30010c134484d0c0042c4d040bc3c010c134293b0c1384c010f3a82c010c134304d0b0a84c01040b4484d0c0042c2913004304d120b43001
|23=>0x1300c302d130042dc91300c2c010c134144e0c0b4302d0b134484f0c00430f90b1382c4d1300c30e90b004482f0c0043c2d0c13430010c1342d390c138484c0c004f8010b1384c010c134302e1300430ea0b004304e0b004302d1300c2c4d0c1344c010c004144f0c0b4484f0c004144c0c0b43c2d0c1344c010c13414030c0b43c010c134302d1300c482d0c004e84f
|24=>0xc0044c030c0b4302d0c134302e0b0042c4e13004304e0b1344c010b134e84c0b004484e0c004304d1300c302d0b0040cf90b138302d0c004482f0c00538010c138144f0c0b42c2913004144c0c0b4e84d0b004144d0c0b42c4e0c0b430010b134484c0c00414030c0b4302d0c004302d130043c2f0c134484d0c0042c2a130042c2a1300431c9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1106211000007f50f8600003ba800000001cd000000000000000037a06a50caa18502ea05a3000016442aa00000a0a000000000000988124c000000008a80000000040500000f101c9800000000d5018282c404ea000012181f5000006d000001650248039000000000000000005200000000000002a8005
|6,1=>0x251447a88b4
|7,0=>0x2cc85890af995b42ae854d0a8180002988524ca31942427e64ed09ba133426064b109421244240847108c211442208434c84a000020a840507f180001f483dcc79a0ef41d6800007490e631c4800006f20db31ae834d067a0cc31908314c6118be417a22e505aa0b1415a82a5052a0000142800004ea0994
|7,1=>0x4508891000022040000874d0ca000042a8845106a209440a88050fea1f943ea87c50f6a1e943ca87850eea00003b28758ce921cf3396871d0e1a000037e86f480001b9436a80000d919ae4354869ccd219a2234046710cd89974000064d0c7a18b430e8610c000181300005f50bd197642ea25c8cb7216a4
|7,2=>0x5fe8bed17ba2f615e48bb900002eb35d06b9100002e045b88b6116a22d045988b211629ac1457c6aecd5c1ab445608ab115422a445408a74d4ca000052a8a45146a289450a8a0513ea27944ea89c51371a6a44cc898cd2fa25b44ae8950d28224d34928918c0000000488490111e2000047088d1118222c4
|7,3=>0x31846288c44d86a30940000c1c9821b031
|8,0=>0x7b06f54de91bcf37986f24de31bc337806ef4ddd1bb737686ec4dd71bab37506e94dd11b9f373a4e68dcb9b9437226e38dc59b88370a6e08dbf9b7c36f26dd8db99b7036da6da8db39b6436c26d78dad9b5836aa6d48da79b4c36926d18da19b40367a6ce8d9b9b3436626cb8d959b28364a6c88d8f9b1c3
|8,1=>0x92e7254a491c8f39187224e431c83390071f4e3d1c7738e871c4e371c6b38d07194e311c5f38b87164e2b1c5338a07134e251c4738887104e1f1c3b387070d4e191c2f385870a4e131c2338407074e0d1c1738287044e071c0b38107014e011bff37f86fe4dfb1bf337e06fb4df51be737c86f84def1bdb3
|8,2=>0xaac554cea81d4d3a94751cea21d413a7c74ece9c1d353a6474bce961d293a4c748ce901d1d3a34745ce8a1d113a1c742ce841d053a0473fce7e1cf939ec73cce781cee29d673a0e729ce239be7370e6c9cd639a67340e669cca398e7310e609cbe397672e0e5a9cb2395e72b0e549ca639467280e4e9c9a3
|8,3=>0xb34765ceca1d913b1c762cec41d853b0475fcebe1d793aec75cceb81d6d3ad460002b39d643ac27578ead9d583
|9,0=>0xc365864b0b96152c265844b07960d2c165824b0396052c065804aff95fd2bf657e4afb95f52be657c4af795ed2bd657a4af395e52bc65784aef95dd2bb65764aeb95d52ba65744ae795cd2b965724ae395c52b865704adf95bd2b7656e4adb95b52b6656c4ad795ad2b5656a4ad395a52b465684acf959d2
|9,1=>0x317962d2c5658a4b1396252c465884b0f961d2
|10,0=>0x18ec71d0e391c7038dc71b0e351c6838cc7190e311
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x4c000024800012000008a000041800020400010000003f00001d80000cc00006200002d00001400000940000480000220000100000048000022000010000007800003800001800000a000004800002000000e0000040000018000008000002000000
|1=>0x41d800203000093c00049c00024700010fc000876000435000212000107800082c0004140002070001030000812000408000203000101000080600040200020080010000005720001f80000df80004fc00017e0000bb00005c800026c000134000099
|2=>0xc5d800624c00307e00183b000c0580052fc00290400143f000a1a000509000281c00140c000a05000501800227e0010bf00085d800424800212000103f00081d80040300020140010020006070002aec0013f400093700045c800226c001124000890
|3=>0x2e1f80152fc00a87e00540600285f801423800887e004433002212001107c00881c0044040020470010040008018004008002001000d2fc00687e00340e00185f800c0fc00601400243f001207000900800417e00203f001015800800800387e0018bf
|4=>0x40c1f82060ec10297e08143f040a030204afc10247e0811ff0408bf82042fc10217608103f04081d820224c10107608043f040207020003008687e04303f020e1f810707c08287e04141f02081f808004003207e018a3700c05f801d0fc00e11c00703f
|5=>0x81a1f840d02020607e10300808121f84090f420486610240808101f84050fc20281810103f08081d840400020092010043f08021e840105020080810040008004604000ec20001810000a08000484000202000000c183b06085d83040fc10347e08193f
|6=>0x28021f94010b8a0085850003f202a1f901103880880c40400e20185f900c0fc80407e401cbf200e1f90042fc80201040043f20020010002fc80016e40003f2000199000008800000200036083a5f841823820a97e1050bf08225e841023820811810400e
|7=>0x100203f80001fa000084a0285c50100e
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0xf1d060608002902000f000006000000000828010f2e02002a0200090000000f0200000200002000040600000418060f00022300040014020200000000040000000f26
|7,0=>0xe03001d000663001e390503844b3a0a0ce2130927d82b00b4061d0607b80b00ba0400310300049a03a80c023003ac4f000f93bc3304002c00420444cf062d1f091f0c2d2b4908000f062ede2ca1091202a2ab98b115b31d2f2ccd001709020003087f09320030ca2500a00f331b416fd2a606aac9c81bc2a74a0c001c00bf33
|7,1=>0x6816021d46000206ac9309b9c9768a00048669194aa30f0c095452029902b208a9738ea9090c7007003e2b941183c30d4510032c09a40648580506050831d10000301a0fa5974d321a
|8,0=>0x5a2e62bd5f93da2fcbd5586a816e509e4c7a40cc6ae46ad47bbdc057bdc218bf944768c5bf677dbb6d8d9ba233bfd3b82142bbda2524d0d550586ce03a33b543807c4c9b8c67586aaf596473857db6948e6d6a3a2eb76a504cc5824c365d79914c586a38333a89824c6a50ca588f4eb68250961e6d9377515094e1b7d992656a
|8,1=>0x754934345c623b78d8dde39966bfbf54b800bf4758503a2f749f55ce674f3d50be339cb04c495295647dd555de7e3753508b4f973c5e7224ccc671ad50586435936ac1876adcbd9d3f565b648dd29421226a4c7d4f8822ae
|9,0=>0x824c94506487bb685dbddbbdd6bf6d824cbb3abf6b96616d505882d76d6d9450826490c450809458604cd5d6bf7b4cbd944cc750bb5058dfd6506a4cd3807d5882646a5d5d5d604c5058
|10,0=>0x184cb7185018d54c4c4c80
|11,0=>0x18
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_190 10 roots_190 ops++addP pm 1 dom_159 9 roots_159 ops++addP pm 2 dom_175 9 roots_175 ops++addP pm 3 dom_63 9 roots_63 ops++addP pm 4 dom_189 10 roots_189 ops++addP pm 5 dom_187 10 roots_187 ops++addP pm 6 dom_158 8 roots_158 ops++addP pm 7 dom_151 6 roots_151 ops++addP pm 8 dom_182 7 roots_182 ops++addP pm 9 dom_149 5 roots_149 ops++addP pm 10 dzo_47_16 6 roots_47 ops++addP pm 11 dom_55 5 roots_55 ops++addP pm 12 dom_183 8 roots_183 ops++addP pm 13 dzo_175_16 7 roots_175 ops++addP pm 14 dom_167 6 roots_167 ops++addP pm 15 dom_165 5 roots_165 ops++addP pm 16 dom_181 6 roots_181 ops++addP pm 17 dom_157 7 roots_157 ops++addP pm 18 dom_179 7 roots_179 ops++addP pm 19 dom_31 5 roots_31 ops++addP pm 20 dom_143 6 roots_143 ops++addP pm 21 dzo_174_16 6 roots_174 ops++addP pm 22 dom_47 6 roots_47 ops++addP pm 23 dom_173 8 roots_173 ops++addP pm 24 dzo_171_16 6 roots_171 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_191 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_175_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_174_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_171_16_42 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_190 10 s (0,roots_190.map (·&&&dom_190)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_191 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_190 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_191 gM v ys):RunD true dom_191 gM v (ori ys):=h
def Z (s:Nat):=barP dom_191 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 69 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 69 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 201 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 73 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 201 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 216 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 88 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 216 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 74 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 74 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 11 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 11 0 = true)
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
def dzo_213_2:=0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc
def gzo_213_2:=0xcc00cc0000000000cc00cc0000000000cc00c80000000000c80000
def gsh_213_2:=0x330033000000000033003300000000003300320000000000320000
theorem lowS_zo_213_2_85:Lower true dzo_213_2 roots_213 gzo_213_2 6:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_2) [(dom_213,2)] (by decide +kernel) (lower_slice_b (T:=gsh_213_2) [(0x330033000000000033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
def dzo_221_2:=0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc
def gzo_221_2:=0xcccccccc00000000cccccccc00000000ccccccc800000000ccc8cc00
def gsh_221_2:=0x33333333000000003333333300000000333333320000000033323300
theorem lowS_zo_221_2_85:Lower true dzo_221_2 roots_221 gzo_221_2 7:=lower_iso_b (d1:=dom_221) (r1:=roots_221) (T1:=gsh_221_2) [(dom_221,2)] (by decide +kernel) (lower_slice_b (T:=gsh_221_2) [(0x33003300000000003300330000000000330033000000000033003300,0,8),(0x33333333000000003333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
namespace S_223
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,10),(2,130),(3,11),(3,19),(3,67),(3,131),(4,20),(4,68),(4,132),(5,13),(5,21),(5,69),(5,133),(6,14),(6,22),(6,70),(6,134),(7,15),(7,23),(7,71),(7,135),(8,9),(8,10),(8,72),(8,136),(12,13),(12,14),(12,28),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,26),(18,82),(18,146),(24,25),(24,26),(24,28),(24,88),(24,152),(64,65),(64,68),(64,72),(64,80),(64,192),(66,67),(66,70),(66,74),(66,82),(66,194),(128,129),(128,130),(128,132),(128,136),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffff
def xsM:=roots_223.map (·&&&dom_223)
def gM:=goal_223&&&dom_223
def NN:Nat→Nat
|4=>7
|5=>36
|6=>149
|7=>330
|8=>209
|9=>53
|10=>7
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xe564ed4e03c7527b56b0a7f7e2eb221e2d7
|5,0=>0xfca88ec23de24a1b8a7eb35b4acf30a2d69a18d29ab5b9a27c95d848e74b8997484c776f5aa683f663a5c636f959fda583fe552dd53c7c508ea4df144c8b0419c3404a03b7a33831e2b92727ad32241a216e110b060be0908380
|6,0=>0xda65bd9d6fd9a03d75b1d37c0d1b61ceac3ccd8acb7fcca930ca3fcc94efc9141c8a15c2d8ec227abc614bb216b672cb4217b0407b0103af51aaf2edad346ab0cea8649a694ca61f1a5dc3a4229a39cca325ea2ef0a20139f5809d3169c5ba9bb7d9aa62968179583a948d4931708e4f88e4738ba538a50789c05869e4864608506a84eea8427984061838b6824697fc6d7ddc47c1257ae96776176fe90696c364040637d661b7b5ead95e3975d5445d4a959889551c0531f85118a506b24dba04b5884897d485a546a7a438fa4021c4015a3f1d03f0a43e9213d51038faf3635c344a133afd32b32319c23165f2f6c82efef2e0242cd172919b2856e27f40235952324322b7d2251d1e8501e56e1cf681987118b9f186a714a25147be138d0126830fcb00f1410c8010c03106a620628405d9004ce403e900358801d5c0029c
|6,1=>0xfd09af5a39f564ff2cf1f2352eff75ee361ee1a4ed82bed577eb0faeb078eaab4e90f0e3f36e1f71e141bdea6cddfbedcce0db1a6
|7,0=>0x5fe555efd85d3145c8e55bcb85aef65846d58409583bc580af57f465757b56d0f551c0538fb534b351866506b24e9914dd644d9f34ca284c98f4adac46570461b845c98458d945536454754439d4398b429ef4275e41f933fb463e1733dd0d3b94137bc0372a236f923654433dd732ec33213d3173c2ffc82f9d22eaca2e6b42e3942d97a2d07f2ca3f2c2fd2bf6f2ac3e29698294dc28c7d2895228645284ee27edf27be1277ef273d42737526fc726c0f265ee24c9524831233522284520a14200f61f0f01eff71e8441e53c1e3ca1db481d4581d0cc1bb061addc19c0e194ee16a13168e314dc3149e01443a137de12dc411048103c10f2590eeb60e5630e0c00d9380bb130b72d0b38a0a36c089940862907e4b07c8f07c220765e075c4074c40721e06f1506b8b05f5e051d302407019360176d0158a0127d00c3900147
|7,1=>0xc3a09c332ac2ddcc1b75c1746c0ec5c0c0bc042ac02b8bf76dbeecdbeb40baa1fba2d6b8d34b7b2ab75f8b6c73b5d1db4e73b497ab353ab2aeab2424b1fa0b1e9cb17f7b114cb0866ae8ecadfbbadfabadce3abe77aa2e6a96dba943aa84caa846fa6afaa6452a61f1a38fea33d2a1bdfa1bdea1ab0a1726a11f0a051ea0372a03289f36d9ca299c5f79c5df9c5489c36899c8f973889521594ee99454a93a7e9312d9131e901e08fe248f2a68c76e8bfb68a0fb897398819087b8e8783985968846928308082f1e82e968217d816cc808d0805c37f9e77f5ab7d4807d32e7b4447b2ac7abde7828d7796177160765af74a4b743837360a72c6472b307193270e5670ce3701de6ff796f5b16f5b06dc706d0ee6c8fe6c82c6b3776b27c6a51f69724689c867b2f66c3c65dde653316477d63a62637a0632c9622d1613f3607c6
|7,2=>0xfc9c2fc593fbc18fbb10fb1d4fa958f9aa9f7eb4f71a5f4d73f4a06f1a62f14fbee1fded732ecfabec9cfec90eec4d4eb9a3eb5f7ea274ea1a4e9f18e92ebe92eae8fb2e79b9e77d7e6b05e5d16e5541e42b5e4000e33d3e16aee1208e05e9de481dd79cdc9b1da9d2d9d50d8bbfd7dced7dcdd6586d5decd49c8d4555d447ed3e0cd3cf6d3cd4d32b6d32b4d293dd2689d14eed14a6d02fccfdddce809ce202cd856cd0dcccc98caafdca502c8b35c8aeac7083c5affc3abd
|8,0=>0xa5226a4724a43a1a3875a1c3aa072a9eb219a79198c8f9826f95b9c94db993371930e5930cd924b88f65c8ee2b8dd158cd528ca4588b1f8773986eb283c83827e07ff067fbd27e5997d3cf7c8527c3637ab4e7a02977641771f77643074d51743b8722ff718806cb836c4f76a5456a4ae6a22469554691f168ebf6598a6567d6547e62e4f61277611e46064a6063e5f6e65e3da5da1f5b6535a6f25a3845a07757fc857dfe5769f56f7b560f6550445445e53c7953786534b3502384fb684e8364e5294da194bbcb481804625f461f3458c7450c644fe040bca406913d2483960a37c3f368893332a319543122f2e0b82ddbb2cf352ba0c2a9eb2a60d27d2425b7223ec7211e71e77c1a8f515e6e1383f0fef90e7aa0e5550db7d0dadb0cdf20c0d90b0d70994307f450742f05b260520804ef80324502577018bd0169600e29
|8,1=>0xfd938fd4cbfb8e0fa5e3f9ed5f8aacf82baf7e7ff7e7ef6be3f5b47f52dbefd3aefab0edaa6ed0cdecf5dec879ec330ea711e7270e6f63e47cfe0d2ae0cbde065fdebbbd9a79d8be5d7a95d7561d6d30d6103d5788d1f2ed1cfcd1720d14efd14eed0ef2d0a8bd0709d043ecaafdca653c9282c9112c84e5c7a0fc5956c58ecc46dbc1201c04a0be5dcbcedfbc9abbbe15bb698baf11b9374b78d6b75c9b244ab21eeb1f66b1d3db1339b02c7af614af2d2ad630ac9f7ab888aad54aa970aa917aa5b8a8938a6217a5d33
|9,0=>0xfaf80fa353ee819e9b84e3dd4dba41d903dd37dacf823bdc7cbcaa0b7722b6bd8b05fcafd53ab6a3aa863a36eea1c79a1a84a104c9e9f1971e895a468c3aa8add8899098583c8552f7f8a37f36f7cf987b2e96f0b6686f766f0a62d1f5c6ba507464853838fd3352f2333e42f5472d3872a91a29ced29cec2659c1e19e1dace03b4a03552
|10,0=>0xfa282eed4dd3ae7d2eba8bbe2796095840a
|11,0=>0xc78b4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff000000000000ffff000000000000ffff000000000000ffff0000cccccccc00000000cccccccc00000000cccccccc00000000ccccccccffffffff000000000000000000000000ffffffff0000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00ffffffff00000000ffffffff00000000000000000000000000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffff00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0ffffffff00000000eeeeeeee00000000ffaaffaa00000000eeaaeeaaffffffff00000000ffffffff00000000ffffffff0000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00ffffffff00000000ffffffff00000000ffff000000000000ffff0000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00fffffff000000000fffffff000000000fffffff000000000f0f0f0f0ffffffff00000000cccccccc00000000ffffffff00000000ccccccccaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa
|0,1=>0xff00ff0000000000ffffffff00000000ff00ff0000000000ffffff00ffffffff00000000ffffffff00000000ffffff0000000000ffffff0033333333000000003333333300000000333333000000000033333300000000ff00000000000000ff00000000000000ff0000000000000000000000ff00000000000000ff00000000000000ff00000000ffff000011111111000000001111111100000000111111110000000011111100050505050000000005050505000000000505050500000000050505000f0f000f000000000f0f000f000000000f0f000f000000000f0f000011111111000000001111111100000000115511550000000011551100ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00ffffff0000000000ffffff0000000000ffffff0000000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0000ffffffff00000000ffff000000000000ffffffff00000000ffff0000ffffffaa00000000ffffffaa00000000ffffffaa00000000aaaaaaaa33333333000000003333333300000000330033000000000033003300ffffffff00000000cccccccc00000000ff00ff0000000000cc00cc00
|0,2=>0x3300333300000000330033330000000033003333000000003300330033333333000000003333333300000000333333330000000033333300333333330000000033333333000000003333333300000000330033000000000000000000ffff3333000000000000000000000000ffff3300ffffffff000000003333333300000000ffffffff0000000033003300ffffffff00000000cccccccc00000000ffffff0000000000cccccc00000000000000000033333333000000000000000000000000333333000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f000f0f0f0f000000000f0f0303000000000f0f0f0f000000000f0f0300000000ff00000000000000ff00000000000000ff00000000ff00ff0000000000000000000000000000000000ffffffff00000000ffffff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000ffff00ff00000000ffff00ff00000000ffff00ff00000000ffff00000000ffff000000000000ffff000000000000ffff000000000000ff0055555555000000005555555500000000555555550000000055555500ffffffff00000000ff00ff0000000000ffff000000000000ff000000
|0,3=>0xff00ff0000000000ff00000000000000ff00ff0000000000ff0000ccffccff00000000ccffcccc00000000ccffccff00000000ccffccccffffffff00000000ffffff0000000000ffffffff00000000ffffff0055555555000000005555111100000000555555550000000055551100000000ff00000000000000cc00000000000000ff00000000ccccccccffffffff00000000ffffffff000000000000000000000000ffffff0000000000000000000000ffff0000000000ff00ff000000000000000055055505000000005505550500000000550555050000000055055500ffffffff00000000ffff000000000000ff00ff0000000000ff0000000000ffff000000000000ff00000000000000ffff000000000000ff00ffffffff00000000ffffffff00000000ffffffff00000000ffffff00ff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000000000ffffffcc00000000ffffffcc00000000ffffffcc00000000cccccccc0000000000000000ffffffff000000000000000000000000ffffff00ffffffff000000003333333300000000ffffffff0000000033333300
|0,4=>0xf0f0000000000000f0f0000000000000f0f0000000000000000000000000000000000000000000000000000000000000000ffffff00ffffffff000000000000000000000000ffffffff00000000ffffff00ffffffff00000000ffff333300000000ffffffff00000000ffff330000ff00ff00000000003300330000000000ff00ff0000000000000000000000000000000000ff00ff00000000000000000000000000ff000000000000000000000000ffff0000000000000000000000000000ff00ffffffff000000000000ffff00000000ffffffff000000000000ff0000ff00ff0000000000ff00ff0000000000ff00000000000000ff00000000ffff0000000000003333000000000000ffff0000000000003300000000000000000000000000000000000000ffff000000000000ff00ffffffff00000000ffffffff000000000000ffff000000000000ff000000ffff000000000000ffff000000000000ffff00000000000000003333333300000000333333330000000033ff33ff0000000033ff330033033303000000003303330300000000330333030000000033033300000000000000000000ff00ff000000000000ffff0000000000000000
|0,5=>0x33003300000000003333333300000000330033000000000033333300ffffffff00000000ffffffff0000000000ff00ff0000000000ff00000000ffff000000000000ffff000000000000ff00000000000000ff00ffff333300000000ffff333300000000ffff330000000000ffff3300ffff000000000000ffffffff00000000ffff000000000000ffffff00cccccccc00000000cccc000000000000ccffccff00000000ccff0000ff0fff0f00000000ff0fff0f00000000ff0fff0f00000000ff0fff00ffffffff0000000000ff00ff00000000ffffffff0000000000ff0000cccccccc00000000cccccccc00000000ccffccff00000000ccffccccffff000000000000ffff000000000000ffffffff00000000ffffff000000000000000000ffffff00000000000000000000000000ffffff003333333300000000333333330000000000000000000000003333330000000000000000000000000000000000ffffffff00000000ff00ff00000f000f00000000000f000f00000000000f000f00000000000f00000000000000000000000000000000000000ff00ff0000000000ff0000ff00ff0000000000ff00ff0000000000ffffffff00000000ffffff00
|0,6=>0xffffffff00000000ffffcccc00000000ffffffff00000000ffffccccffffffff00000000ffccffcc00000000ffffffff00000000ffccffcc00000000000000000000000000000000ffffffff00000000ffff000000000000000000003333333300000000000000000000000033003300ffffffff00000000ffffffff00000000ffffffff00000000cccccccc0000ffff000000000000ffff000000000000ffff000000000000cccc0000000000000000ffffffff000000000000000000000000ff00ff0000000000000000000000000000000000ffffff0000000000ffffff000000000000000000ffffffff000000000000000000000000ffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x40400b1e1449222347960200c0b1e304971a2c21612389071e30800281c9851238907260c48e242c30512040150c3c609101c20312040151418490001c50f122038f0a240920e3c18902485930a240112a182890248203120490f1820a0726144922228309101c30504040040608080
|1=>0xe10609020039c0c1410e0034203043800d3630481002c30c040400b0c1448e243420c0404007080c48e2434316043800b085848e243c61a32345842c087000e4c2891c489850438007260c10e002c30c120490b1e14080301c20c12049071e0c080302c78504040070c5848e242c783
|2=>0x18255000e8c783120400b140c48100885931824712161078c12014871e304a13a3459318087000e2d28f2c14481003c6003aa068b1e300114e3458f4c247001a2d28f12380241a8c796120400b0c1448e0034a8a2c24080442c78c1284d0d16290091c0039f1e58481002cf13182401d
|3=>0xe3478c0201407163c60942b868b1e304a15a3458418247120e347831c00c0d16946091c0110d1e3002e503458f18016a81a2c785123890d143c60954003841e304aa001c78504380071a9478c12040071e0c10e003459e1e58480221d60f182402b163cb0e006068b463c289020038f
|4=>0x1804028163c6091c8468b1e3072128345846830481001c78c1c0140d163c601005198b1e5860902845a51e0c609020020c12c80071a3cb0c020140b1e144b2003588f1824030161060902011072610609007438f18015a71a2c20c120178d16186091c4868b1e30481421c58f0a38018
|5=>0x283458a2614480221c48e009110d163cb091c4838b1e5860900a458418247121a29b891c0038f18250911a2c20c04380071a3c60022a068b1e30480521c59e2630480221d88f182402b163c2890200395263010e002c7831204015163c18c120508b261060900b438f0a240116c1c783
|6=>0xe3c2890201207085848e001ca8f0624080482cf0f2c240291628789200038f18240920e2c78c0200c33163cb090200e0b1e3048e001dc930a247000e54796122059306247002a2c78c1c84c8d163cb09020120b08304805e1c68618087001a2c78c1ce0a0d169588f18247001e3001d
|7=>0x5458f2c14700281cf0f2c2401d0e1060902003951418289020039b18247001a2cf0f2c255001628303120400b1e304bb001c58f0a240800e703161238015163c1890200e0b1e144802234a8f182402e1a2c30f18248000e3c6005c5068b1410189020038f18016941a2dd0f1824080
|8=>0x1c4838d1e3072150345930a247000e707961c00c071628796120148b1e0c48e24345b11e24700482cf0f18240290e3c28c0200a071e5848e242c7831804014163cb021c0038b143c4881a2c20c12f8007263048e241c58f1824407083010e0035e8f0a240110e3c609784468b0c30481
|9=>0x1c78c043800d16c46091c0110b080c48e0034a8f0a259000e3478c12f158d163c601006038b1e30480843458f18020941a2c50f2c255001610b091c00a841e584aa002cf0f18255000e3c28e006068b1e3048e001e0042c247000e7078c0404007163cb0954005930a247002a3c289
|10=>0x12380073c3c609004438d263c28c12008870c3c60900b468b1e1448022d868b143c28900ac68b3c1079612380071e3048e421c68b143c60900c068b083c60900c068b083c6091c0220d1e30700501c68b1e304be001c58f18dc48e001c50418380141a2c20c1c00a0d862de8a083048e
|11=>0x1a2c78c12008c61a2cf1318240111a2cf0f18240800e4c28c123800786d588f182470016106091c01f871e304805e3458f18380181a2c20c12380220e3529e1e3048e003430f18040140e2c796120168d662d18f18380181a2c51306247000e2c796124000b0c3c60900b868b3c28796
|12=>0x382c23418247000e34f0a1e30481001cf0f18380281a2c783120168d662cf041e30481001c50f06240111a2c21618247000f0c98c12380072a2c78c1c00a0d662c78c120178d862c30c12380221a2c79618247211a2dea5083048e003528f063048e003479612380240e2c7961838028
|13=>0x1c00a0d164c60e00506c3169450f0a247001a29b891c0068b1e30481011c38f063070050345bd26106091c003841e0c609020038a0c5848e001c58a0c24700483459e623c6091c0038f0a24700483458f2c247002a2cf0f18247211a2c50f0a240110e3430f2c1448e001c7961238007
|14=>0x624c6091c0058f0a247000e34a8f0a247001a7058f2c3048101285a5263c6091c003bd1e304803a3458a2614480223458a1e14481001c98f1824700902c783123800d2a2c78318247211a2c78c12040240e2c33418247001a2c5311e5848e002d88f18240111a2c50f0624080162898c
|15=>0x1b3c5cd1e3048e001c58f182402b8c3458f18248000ed528f18247001a7898c12380077a3cb05120400b624c78c123800b1418609020038b983c609004468b7a3c48e009068b0c3c28c12040071e30481001ce0b1e0cb09020198b1e1448e00d838f0a2402b1b2c5861e0c609020059e
|16=>0x80c6091c0038f18247211a2da8f18380281a2c78c123800d382e80f0a247001a2c78c1c0140d167851318247000e7898418247000ef478c120170d16f478c120168d168c78c1204033169420f18247001a3cb0c1c00a07163c60e005120d1628789200068b1410b0902005841838014
|17=>0x1a7058a1f4c481002cf0f12380241a2c50f18247211a2c20f18247211a2c796120403316f46091c0110d16289851238007143c60e00a068b083c60e00a068b1e30700294868b1e5848e009068b6a3c6091c8468b141860e005068b0c30700283618b1e304805c1c68b263048e011c393
|18=>0x1824700173078c120158d16f478c1c00a0d164c60e00506cf163c289004438d664c6091c00a8b1e0c48e009068b1e5860900b868b1410b091c0038f18247120e3458f06240111acc59318247000e705bd1e582891c0039e1e584803a3458f18380181acc5b1083c6091c0038f2c24700
|19=>0x1a7078c12008d11a2de8f0630481002c7851204007663c6090201107163c1891c0069c16106097c0068b3c3c60900b868b1e304881a2c783120403316f4785120088d162820312380071ae878c12380071a3c60900b510d16298931824700163c2891c012071ac4984182470016c430f
|20=>0x18247211a2c78c40247000e786091c0110d16106091c0038d2a4c78c1c0140d16106091c0069c164c7851238007662830512380071a7878c120148d162820c12040070830481001e18f0a247001a5478c12c80071a2c50606247001a2c783182402e1a2d28a083048e00347851238007
|21=>0x83048e00345b51e24700483459e1e304aa00345bd085860902005931e304805a1c59e1e3070028345bd3c3c6091c003a31e5848e001c58618247001a545d51e1448022345841e5848e001d99e1e582891c0038f18240541a2da8f182401d1a2c7961824080442c7b418240800e2c98f
|22=>0x16f528f18247000e287961200e8d169498418247001a9430f18247001af478512380071e1460e005038d463c2891c0068b141448e008868b143c48e009068b3c3c609007438d1e586091c02c0b1e0c60e005068b1e304d700345a51e58609020058f0630481008858618380141b3c5d6
|23=>0x1c68b083c60900b868b1e304805a3618b1f6460e005068b6a3c609020038b623cb05123800b148048e00345bd143c2891c0039e26304803a3459318247001a7058f18040140e2da8f182402e1a2d18f18240800e2da8f182402d1a2c98c12380220e2c20f18240800ecc78c120170d
|24=>0x18240291a2d88f18247000e2c20f18240291a2da8c12380221a2c78c12008a21a2de842c3048e001c9b418247000e2c30f18247211a2c78c123890d173878c1204007163c609b40088d16f588f1824700163c60900a468b0c3c60e00a068b143c60900b868b0c3c609020198b1e3010e
|25=>0x1e3048e003458f2c1448e001e1b51e30700283459e1e30480603458f18255001a2ee0f182402b1a2dea51e1448e003450c12380221a2ed9318247001a2c20c12380221a2d88f182401d1a2c50f2c2402d1a2da8f2c30481002c78c12017871a2d28f2c3048e001c78c1c00c071a2c50f
|26=>0x1c23418247001a2c51612380221a2da8f0630481002c50f18255001a2cf130a3048e001c20c123800d2a1078c12a800d167c796123800d16c47961824700169478518247001a282091c0120d163c28c123805e1a106091c0038d383c609640068b1e5848e017439e1e5848022345b5
|27=>0x120400b1e1460902003c31e1460e00a068b4a3cb05123800d1e30480be345841e304803a1c68f0630481010c58a1e0c481001c58618247001a705931e304805c3459f1e30480be3459e1e58481002c79612380072a2c98418247000ecd18f2c247001a2c50f062402d1a2de931e1448e
|28=>0x12380071a3da0c120178d167988f2c2470016e878c1202a0d164c6091c0110d162898c1200e8d164c20c1200e8d161878c1200e8d16c478518247000eb078c120088d168c783123800d16281891c0110d163c28c123908d163cb051200887623c18c123800b3c28796120400b3c10796
|29=>0x16787961238007083c60900b438d26d06091c0068b1e3048060345e11e58481002de8f18380281a2c51312380241a2c52318247001a2de8418247000ed478c120088d169478c12380071ac478c120148d163c609020039516287832c24080177098c120088d167878c120158d168c785
|30=>0x1c003b3162830c12380071a2c7d31824080163c6091c0069516287e2123800d1628985123800d161878518247000e3478c12380071a7058f065848e003598b083048e003618b623c6091c0068b1e30481001d98b263048e011c68b0c3c18c123800d16f478c123908d16287b4123800d
|31=>0x162820c120400d164c6091c006c3161878c1c00a0d16e878c123800d163c28c12380221a2c98f18240111a2c78c120158d168c78c123800d662c50f2c240801628216123800d16f47960a247001a2c5311e3048e00345e1263048e00345b1083c6091c0068b0c3c609020038b263c609
|32=>0x1acc78c12380220e3458f1825f001a2c783123800d662c7832c304805a345bd3c3c6091c0068b1e3048e012868b7a2878c123800716787960a247001a2c3041e30700283458f188048e003458a1f4c48e003458f06304805a1c68b1e5848e003598b6a1878c123800d16f478c1238007
|33=>0x683048e001c68b3c3c609007468b1e586091c003c3163c6091c0288d161078c12380241a2c78c123800d382c20f18240800e3c609020198b14106091c0038d083048e001c6c37a9478c123800d16f4785123800d163c6091c0120d163c6091c01f8716f478318247001a2c7851238007
|34=>0x143c609007468b1e30480564468b3c1078c1200e8d163c6091c0220d162878c123800d382de931e3048e001c58ac03048e00345b51e146091c0068b0c4c78c1c00a0d162830c123800d16186091c006c3163c609020318d16f450f0a247001a2c7961824700443458f182402d0e3458f
|35=>0x1e3048e001c6b36af478c123800d167878518247000e34f0f063048e00345db1e3048e00345a51e586091c0068b1e0c6091c0110d175878c123800d163cb0c120168d163c609019468baa3c2891c0068b141820c123800d161820c123800d862de8f2c30481002de842c3048e003459e
|36=>0x1a2c78c1200e8d173878c12380071a2c78318240800e2c30f18247001acc593083048e001de931e1448e003459e26146091c0068b6a3c6091c0038d163c18c120168d164c78c12380241a2c78c12380491a2c78c1c00a071a2c796123805d1a2d18f18247000e345d01e3048e0034584
|37=>0x2005b53c3c6091c0068b1e3048e011468bb83c609004468b1e0cb0c120400b1e3048e008868b143c609007468b623c28c123800d161078c1200e8d163cb05120088d16d479618247001a2c98f063048e001c58a0c4c6091c0068b0c4c6091c006c3173478c123800d16287830a24700
|38=>0x6e247001a2de8a083048e00345861e586091c0038b1e0c6091c006c3161878c12380241a2c50f06247000e345a51e3048e003459e1e5848e003458f182402d1a2c78c123805e1a2c7b418247001a2c20f18247008a345b51e0c6091c0068b143cb091c0038b7a106091c0068b1e58289
|39=>0x1c0038d2a2c50f065848e003458418247007e3458a1e30481001c58f18240800f0c5a5143c6091c0068b1e3048e017438d3c28796123800d164c78518240111a2cf041e5848e003458f683048e003618b1e146091c0038d863c28c120158d162b30c123800d164c78c12380491a2c78c
|40=>0x1c02c0d16d478c123800d163c28c12008871a107961824080167850f18240801a2cf041e3048100345e11e5848e003458f0630480223458f18380141a2d18f18247001a2cf8f18247001a2c78c12380360e2c7960a247000e7878c120400d167878c120088d175420c123800d163c609
|41=>0x1e30700281c68b4a4c78c123800d1628785120400d1628785120088d16d450f18247001a2da841e3048e003458f0a30481001e70f18247001a2c78c12040471a2c7830a247001acc5bd26106091c0068b7a1878c123800d161078c1c00a0d163c18c120400b3cc478c123800d163c609
|42=>0x1c0038d7a3cb0c1238007163c6091c0240d163c609200068b083cb0c12380073c2878c12380071a7898c123800d167820f18247000e347961238007662c51318247000e2c98c1238007862c7851824700a23459e1e3048e001c6931e146091c0038f0a247006c345e11e304810034586
|43=>0x12380071a3c6091c006b3163c6091c01b0d162820c123800d163cb0c123804a1a2da931e3048e003458a1e1448e001c68f0a247001acc58f1824700481c68b3c2898c123800d164c78c1c00a0d167898418247001a2cf061e3048e003458a1e0c48e003458f18247008e1c6841e0c609
|44=>0xa247001a2c78c123805d1a2c7832c3048e0034586263c6091c0068b1e0c6091c0038d163cb0c1238007163f38c120400d161820f18247001a2de8f2c3048e003458f06146091c0068b1f806091c0068b144c6091c0068b26106091c0068b0c3c6091c0068b3c3c28c123800d161078c
|45=>0x263c6091c0068b3c1078c123800d163c18c123800d161079618247001a2cf0f18247001a2ea8f18247001a2c98f0a3048e003458f18247007e3458a1e3048e001c68b1e3048e001c6c3163c28c120400d163c28c120088d179878c123800d16f450f18247001a2de8f18247001a2c796
|46=>0x18240801a2c50f2c247001a2c30f18247000e3458fa63048e003458f18247001b0c58f18247000e3598b1e58609020058f182720100345e11e3048e00345931e3048e001c58a1e1448e003458f198848e003458f18240800e2c78c12380471a2c78518247000e34f0a1e3048e00345bd
|47=>0x3c6091c0068b263c6091c0068b1e30481003458a1e3048e00345841e3048e003458f2c3048e003458f18247000e3458f0a3048e003458a1e3048100345841e30481003458f18240111a2f40f
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x794032a0145007a8029400aa0005
|5,0=>0x79303b181ccc0e0606d30351819cc0c86061a82f5816ec0b25056302998140c09a604a302398110c082603e301d980e0c06a60323017980b0c0526026301198080c03a601aa80bd8052c0236
|6,0=>0x155b8a91c53cc297714838a25c504e27b713a389b5c4cce25f712c38945c494e243711e388d9845ee2287110b8869c426e20c7102b87f9c3eee1f070f4b8789c3b6e1d470e6b8719c380c1b970d9386adc348e19d70cb3863dc310e18170bdb05d1c2dae16760b038565c2a4e14b70a2384f5c26ce12f709438485c234e1137086b0419c1fee0f87
|6,1=>0x23039165c8a4e44b7222390f9886ee430721531091883ae41852093102dc808e3fd71fb38fbdc7d0e3e171ed38f4dc798e3c571df38eddc760e3a971d138e6dc728e38d71c338dfdc6f0e37171b538d8dc6bac35671a7b8d21c682e33a719aa8cb9c64ee320718cb8c49c616e304717eb8bd9c5dee2e87170b8b6d85aac2ce7163b8b01c572e2b27
|6,2=>0x4f07274b9389c9b6e4d47266b9319c97ee4b96259392adc948e49d724b3923dc912c483623e391d5c8dce4677
|7,0=>0x37239b75cdab06cd8362c1af60d6b06ad8352c1a79cd2d068e8343419fa0ced066e83334197a0cad064e8323418fa0c6d062e83134187a0c2d060e8303417fa0bed05ee82f3b977e0baf05d072e4b9709cb7505b282d54168a0b35059282c6316120af9057482b6415920ab9055482a6415120a7905348296414920a3ae51672874141a09fd04f77
|7,1=>0x46bba33e1190e8c0845c422c2115108a0844c4224211110881743cc21c9d0d50862842d4214dd0970843841dc20ce10570823840dc204e1018e80573fec1fd60fdb07e763efc1f61cfa107c883e041ee20f6107a883d041e620f22e78983c0c1de60ee3076983b0c1d660ea3074983a139cea0e65072a839141c6a0e25070a8381b9bee0de706eb8
|7,2=>0x564c2b0615730ab18554c2a861534ea92854542a0a14f50a737535c298e14b70a538525c290e14770a347516ba899d43d0a1685074281a13fd09f684f74279dd3bf09d784e83a7221384c9bb74d9c26ae1347099b84c9c262e1307097b84b9c25ae12c7095b84aa3a5321289093d749ac24b6124b091d848ac2436120b08fd847b3a3ba11cd08de8
|7,3=>0x661432ea19650caa86514326a19250c8a8641431ea18e50c6a86314316a18a50c4a8621430edd8670c2b8611c3071d8290c0c860242ff217e90bec85f242f7217a90bcd75e2c2ef6176b0bae75d342e7a172d0b8e85c342dfdd6ef0b6f85b3c2d7e16b0eb5085a442d0216710b30859442c821632eb118584c2c0615f30af18574c2b8615b30ad18
|7,4=>0x75dbbace1d570ea3874dc3a4e1d170e83873dc39ce1cd70e63872dc394e1c970e43871dc38ce1c570e23870dc3851dc190e0486fe437d21bd90de486eebb7561b9b0dc586dec36d61b5b0da676cf4365a1b1d0d8686bf435da1add0d6686af4355a1a9eed47869fc34de1a5f0d27868fc345e1a20ed097680c33e619e30ce98670c3369d9a50cca8
|7,5=>0x1e0f0eff877c3bbc21dd10ee1776d3bb4a1d950ec28
|8,0=>0x88dc444a62133101887c4c3c221cf30df886b4c33a218ef0c0785c442c2214f309f884bc423e210d307e883acc1b9e0cd105d982a4c1322087303a9818cc0a62043101898084401e5fff0ff787f7c3f9e1fbf0fd697e743f1ddf7d2fb777d7c3e9a5f3b2f9587c64be121ef72f7297b5bbd8e1eb70f5387a54bd065e712f30879443c821e310f0f9
|8,1=>0x99b3ccba264d131d998a4cc32260912fd797a4cbb225c912dc896a44b32258732bb8959c4aaa654332989947cca1e24fd327779374c99a24bb32567926cc9126477323389154c88a243512128904cc80623f131ef98f34c77663ab11cc98e1cc6ee236711ac78d24466e6325318a88c0cc5e262e1116798afc455a629b3145889e4c4ce625711238
|8,2=>0xaa5c550a6a7515328a95454866a3315118a84c540629f134ef9a73c537e29ad34cd9a633d2fa296d14ad9a524d26e6927148c7a41cd1ee28e7146b8a31c516a68a334498a20c50e9e865142a8a114506de827140b8a01c4fea67e333e989f0c4f6627a133c889dfcceda675b33a499cdcce4e2717138299bd44dc666d1335f99ab4cd36668b133d8
|8,3=>0x15da9ae8cd7262b8315b89ad7cd69e2b3d35959ac6c56162af935739ab5c5591eab915539
|9,0=>0x17918bc4c5e09eef517728bb4cdd862eb317509ba4bdd062e7317318b94c5c862e34f7128b8545c066df136ef9b73c5b7a6dad16ce8b62cdaf62d6936ab9b51c5a6e2d27168a9b41459ea2ce516699b304d95e6c9f16478b1f4d8d66c5936248b0e458522c1916039afdc57ce2bd715e38
|10,0=>0x5f222f82f7b98bd8c5ea62f4317998
|11,0=>0x17d07
|_,_=>0
def wAt:=mkWire dB 105 224 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 1000003 zs)
def oP:Nat→Nat
|0=>0x3c0408311c351e2d1e0e181d1e311a2d1e350055141c1e311a2d1e351255141c1a2d08581e311e2d1a2d1835085b1e2d3c3b142d1e311e2d18350055141c1e311a2d1e35182d0055141c1e311a2d1e1d1a2d20010a041c35182d0a041e311e1d1a2d1c35182d20010a04182d1a2d1e311c3520010a041e311e1d1a2d1c35182d
|1=>0x1a2d1e2d1255141c1a2d0a3b1e15182d141c1a2d1e311c351e351255141c1e311a2d1c35141c1a2d6a031e0d2c2d18351e2d063b181d1a2d6a271e0d2c2d18351e1e141c1c55182d141c1e311a2d1a2d3c3b08311e2d1e1d0055141c1e311e2d0055141c1a2d182d0055141c1e311a2d3c041c351a2d142d1e150a3b182d1a2d
|2=>0x1a2d3c3b142d1e31141c1a2d1e311c351e311e1d1a2d1c35182d1c351e31181d1e1d1a2d0a3b141c1e310a041e1d1a2d1c35182d181d1a2d1e311c351e2d141f1e31142d1e310a04182d1a2d1e311c35183520010a041c35182d1e1e1e1d1255141c1e311e3500551835141c1a2d1e2d0055141c1e311a2d1e312614182d1e35
|3=>0x1a2d18353c0408311c351e2d1e35182d141c1e311a2d182d0055141c1a2d1a2d0055181d141c1e31142d1e3118350055141c1e311a2d181d0c271e1d1a2d20011e310a041c35182d1cfd1a2d1e2d26331e351e350055141c1a2d1a2d20010a041c35182d1e2d1255141c1e311a2d1e590a3b1835141c1a2d1c35182d0c271e1d
|4=>0x1e150a3b182d1e35063b181d1e1d1a2d1e3122350a3b182d08311e2d18356a030c311e1d3a353c3b142d3a353c3b08318a2d085a1e2d18356a270c311e1d1a2d1cfd26331e352614182d1e351a2d0c2708351e311e2d0c270c3f08351e2d1a2d14351e311255141c1e311a2d141c141c1e311e2d1a2d18353c04183508311c35
|5=>0x6a277a2d1e5922350a3b182d0a3b1e15182d08311a2d1c351e2d182d1e1e62353c371e15182d1a2d1e2d26331e35683b190d1e1e1a2d46271ecd181e1a2d1e0e181d1a2d142d7a2f14351e311c350c271e1d1a2d0633063b2c2d18351ecd181e1a2d1e311e35181d1a2d0a0418351c35182d6a3b0c311e1d1a2d1a2d142d1e31
|6=>0x142d1e316a331e0d0a35182d1835141c1e311a2d6a033c351e15182d1e1d182d1a2d1835141e1e311a2d1e1e1c351a2d142d1e316a273c351e15182d063b18cd181e1a2d1a2d1c351e2d0a351e310a3b182d1e1e18351e35141c1e311a2d6a3f0c311e1d1a2d6a037a2d1e597a2f1e5918357a2f2c2d1e5918350c331e1d1a2d
|7=>0x26161e35182d181d141c1e311a2d6a031e0d2c2d18350c331c351e1d1a2d142d1e313c371e150a3b182d1c35181d1e311a2d0c27262d1e311e350c270c3f262d1e3514351e312614182d1e311e351c351a2d08331e2d6a271e0d2c2d18351a2d26311e351e2d181d1a2d1c351e2d1e1d18351e311a2d0c33262d1e311e353c37
|8=>0x1e5918356a370c31262d1e351e1d1a2d1e311c351ead22350a3b182d26310c33262d1e351e1d1a2d1c35182d141e1a2d1e311c3506332c2d1c3518351e5a182d1a2d183518ae22350a3b182d1c35181d1e1d1a2d3c37142d1e31182d141c1e311a2d188a1e0e0a35182d7a2f26311e351e311e35182d182d1a2d1e311c359235
|9=>0x6a27141d1e311a2d194526171e35182d6a27141d1e311a2d1a2d142d1e311a2d1e3508311e2d1c351ecd181e1a2d6a2f3c3508311e2d18350c271e1d1a2d1e310a041c35182d18351e311c351e2d1e520c2708351e2d9c35141f1e311a2d22350a3b182d1a2d0a041c35182d7a2d7a2f1e5918351e35142d1e311a2d182d1c35
|10=>0x1e311c350c33083508311e2d6a033c35142d6a033c3508311c3506332c2d18356a3f7a2d1e5918351a2d182d1e311e356a273c35142d6a273c3508310c271e1d1a2d6a337a2d1e5918356a03141d1e311a2d1e310c271e1d1a2d0c271e1e1e1d1a2d6a3b0c311e1d1e351a2d08331e2d1e2d1e35181d1a2d6a03141d1e311a2d
|11=>0x1e310c331e1d1a2d3c3708311e2d08353c3708311e2d1ead22350a3b182d1e520c27262d1e35181e0a3b1a2d1e35141c1e311a2d0c33181d1e1d1a2d6a3b7a2d1e591e311e2d1a2d18350055141c1e311a2d0a3b06330a35182d141e1e311a2d1e59182d1a2d18353c3b142d1e313c3708311e2d188a1e0e2c2d18352c2f1835
|12=>0x1a2d1c351e2d182d141c1e311a2d1c55141c1e311e31181d1e1d1a2d1e0d2c2d183514351e31141e1e311a2d2c2d1c351e591835182d1c35181e1a2d1c351e0e181d1a2d140e181d1a2d1cfd1e2d26331e353c351e15182d20010a041c35182d06330a351c35182d0a3b1e591835181d1a2d1e311e2d9c2d141f1e311a2d142d
|13=>0x1e1d141c1e311a2d14371e310a3b181e1e2d1a2d1e15182d1835743baa2d14371e313c3b3c351e15182d1e0e2c2d1c3518351c35190d1e1e1a2d6a030c31262d08581e2d1a2d18351e151e0e0a35182d1e2d141c1e311a2d6a270c31262d141a08351e311e2d1e35181e1e1d182d1e311a2d1e15182d1a2d1e311c351e2d1e1e
|14=>0xc271e1d1a2d1e311e0e0a35182d6a333c35142d1e313c3b142d1e319435085b1e2d18350c27181d1e1d1a2d1d4526171e35182d7a2f1c351e5918351e0e0a351c35182d1e520c271e1d1a2d1f15085a1e2d18350c330c311e1d1a2d1e2d1e2d1c351e591835063b1e35181d1a2d0c27083508311e2d14351a2d142d1e31181e
|15=>0x1c353c371e15182d1e3108581e2d18351a2d14351e313c3b142d1e311e920c33262d1e351c350c271e1d1a2d6a3b141d1e311a2d1c351ecd181e1a2d1e0d063b2c2d18351e0e181d1a2d181e1a2d1c351e2d6a3b141d1e311a2d7a2f1e59183518353c3b142d1e317a2f26311e356a2f0c311e1d1a2d1a2d182d1e591835182d
|16=>0x1e59183546271ecd181e1a2d623b3c37142d6a370c311e1d1a2d623b3c3708311e891e0e2c2d18351e591e2d18351e1e6a030c311e1d1a2d0055141c1e311a2d6a377a2d1e591835623b3c371e15182d0c311e1d1a2d6a3b3c35142d1c35181e1e1d1a2d1255141c1e311a2d6a3b3c35083118510c271e1d1a2d141d1a2d1e31
|17=>0x141c1e311a2d1a2d18351e16182d0a3b1e15182d9c1d141f1e311a2d1e1e182d1a2d18350c310c271e1d1a2d3a353c3b1e15182d3c0408311c351e2d1e4522350a3b182d7a2f1e5918356a3f3c35142d1e311f2526161e35182d6a3f3c3508311e2d3c371e15182d1e31063b2c2d18357a2d1c351e591835683b190d1e1e7a2f
|18=>0xc03108371e2d142d18351e311c351835141c1e311a2d1e2d1e35181e1a2d063b181d1e311a2d182d26311e352c2d18351e0d0a351c35182d3c041c35142d1e351e15182d1a2d1e2d141c1e311a2d3c0408311c351929085b1e2d18356a377a2d1e5918356a2f1e0d0a35182d08351e2da22d26171e35182d141e1e311a2d1c55
|19=>0x8311e2d3c371e15182db8370a3b182d1e0e181d1e311a2d6a031e0d0a35182d0a3b182d1a2d18353c371e150a35182d18351e311c35183508311c351e2d1e1e1a2d1c35182d6a271e0d0a35182d7a2f1e5918353e3bc03108371e2d1a2d3c3b08311e2d1c351e1e181d1a2d181d1a2d1e311c351e1d141e1a2d6a3b0c31262d
|20=>0x1835142f1e31262d1e351e71141e1e311a2d1e591e2d1a2d18350a3b1e0d0a35182d6a2f0c311e1d1a2d3c371e15182d1c35141c1e311a2d2c2d18351e311c351e451e350a3b182d1e1522350a3b182d181e190d1e1e1a2d3c37142d1e31aa2d14371e316a3f0c31262d1e351e353c3b142d1e313c3b1e3508311e2d3c3b0835
|21=>0x8311e2d1c351e1d1a2d1e35181e1a2d1e311e1d1a2d2c2f1c351835141c1e311a2d1e310a37182d182d1e311e35182d1e1d1a2d141e1e311a2d06332c2d18350c3f08351e2d3c371e15182d1c35181e1a2d1e3508331e2d181d1e1d1a2d1871141e1e311a2d1e15182d1a2d18351e2d063b181d1a2d3a353c3b1e15182d1c35
|22=>0x1e15182d18350c2708351e2d08581e2d18352c2f1e311835063b181d1a2d06332c2d18350c311e1d1a2d26311e351a2d1e311c351e2d0c3f262d1e350c271e1d1a2daa2d14371e311e0e0a35182d1e350a3b182d22350a3b182d1ecd181e1a2d18351e311c3518351e311e2d182d1e5918353c37142d1e311e35142f1e313c37
|23=>0x182d1e1e1a2d183526171e35182d0c3308351e2d1ece181e1a2d1a2d1c351e2d1c35181e1a2d1a2d1e311e2d1e2d1e1e1a2d7a2f1e591835182d1e5918350c331e1d1a2d1a2d26331e352c2d1e591835182d181e1a2d1e0e181d1a2d1cfd26331e3518cd181e1a2d063b2c2d18351435142d1e31085b1e2d18351a2d14351e31
|24=>0x182d14371e3108351e311e2d0c3f08351e2d1c351e5918351e2d1e5918353c3b142d1e3122350a3b182d3c3b08311e2d6c2d1e5a1835141e1a2d26311e351a2d08371e311e2d1e0d0a35182d0c27262d1e35262d1e311e351e1e1e1d1a2d1f92022d1c35182d14351e311e0e2c2d1835063b181d1a2d190d1e1e1a2d3c3b1e15
|25=>0x1a2d1e2d1e351a2d26311e35182d1e151e35182d0c311e1d1a2d063b2c2d18350c33262d1e3526161e35182d0c271e1d1a2d18351e16182d1ecd181e1a2dcc31262f1e351e2d181e1a2d7a2d1e5918351e15182d1a2d1e150a35182d1f890a37182d7a2f1e5918351e0e2c2d18351f4d2c2f1835063b2c2d1835c43b0a37182d
|26=>0x18351e311a2d26311e351e2d18351c35182d3c351e15182d085a1e2d18351e450a3b182d2c2d1c3518351e0e2c2d18353c3b142d1e313c371e15182d3c3b08311e2d18350a3b182d7a2d1e5918351e35181d1a2d262d1e311e350c3f262d1e35c235142f1e311e310a35182d3c3b1e15182d141f1e311c35181d1a2d181e1e1d
|27=>0x1a2d1e16182d1835142d1e311e350a3b182d183508311e2d190d1e1e1a2d1e1e182d1a2d22350a3b182d1e31262f1e352616182d26141e35182d1e2d14351e3118351e1d1a2d1e1e181d1a2d0c331e1d1a2d1e31181d1a2d7a2f1e591835142d1e311835063b2c2d18357e2d26331e35190d1e1e1a2d085a18351e0d2c2d1835
|28=>0x1e2d141d1e311a2d0a3b182d1a2d18351c351e2d1c35142d1e3108311c351e2d1835142f1e310a3b0a35182d0c271e1d1a2d1ecd181e1a2dc03108371e2d1a2d1e5a1835182d1a2d183508311c351e2d1e150a3b182d1e2d14371e31141c1e311a2d2c2d1e3118351e2d26331e351a2d1e311c351c351e1e1a2d7a2f14351e31
|29=>0x1e351a2d26171e35182d142d1e311a2d182d1e351a2d182d1e5a18351c35142f1e310c271e1d1a2d7a2f26311e35182d1e311c351e310a3b182d3c35142d1e313c3508311e2d1a2d1c35182d141f1e311a2d08331c351e2d06330a35182d26311e351e2d2631262d1e350c2708351e2d0a351c35182d3c371e15182d8e350833
|30=>0x1e2d085b1e2d0c31262d1e35182d1e311a2d06330a35182d0c331e1d1a2d1e35142d1e310c27262d1e351e3508311e2d083508311e2d181d1e311a2d1a2d08331e2d1e2d181d1a2d1a2d1e591835ba351e16182d0a041c35182d1e2d1a2d18351a2d142d1e31142d1e311e351a2d08311e2d1835181e1a2d1a2d1e311e351e1e
|31=>0x1e2d2c2d18351e2d18351e15182d14371e311e35182d26331e351e311a2d1e1e1a2d1c35182d0a3b182d262f1e3514351e311e591835182d18351e16182d2c2d1835262d1e35181d1a2d1a2d183518051c3508351e2d1e5918350a35182d08371e2d1e311e351e351e2d1e1d1a2d1e15182d1e2d1a2d181e1a2d1e5a18351e31
|32=>0x1e351c351e311e2d18351a2d182d1e311c351c351e2d0a3b182d1e051c351e3118351e1d1a2d2c2f18351e1e1a2d181e1a2d1c351835022d1c35142f1e311e351a2d1e31182d0a37182d1c351a2d08331e2d182d1a2d142d1e3126311e350831
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x700000000
|5,0=>0x1f6000000000196000000000000000000000000000000000000000000000000000000000000000000000136000000d60076000000000000
|6,0=>0x74406f506c306840644000006040000000005f1000000000000000005e1000005950000000005540000000005140000000000000000000004d40000000000000000048504440000000000000000041300000000000003c50000038403350000000002f400000000000000000000000000000000000002a5028202530000
|6,1=>0xec400000ea200000e550e1400000dc50d750d340ce50c950c6300000c330bf40bc30b840b35000000000ae500000000000000000ab300000a6500000a15000009f200000000000009d20985000000000000000000000935000000000000092108e400000000000008d1000008940000084507f5000007b4000000000783
|6,2=>0x109100000000000000000000104510040000000000000ff100000fa50f550f1400000f010000
|7,0=>0x1d941d541d141cd41c941c541c141be31ba41b641b2400001ae41ab31aa11a641a2419e419b31974195219140000000018d418a318731834180317d317a317731734171216d416941654161415e315a41564152414f314b414741434140313d313c1138400001344131312e312b312831244121311d411941154111410e310a4
|7,1=>0x2b042ac42a842a532a2329f329b42974293428f428c328842844280427c4000027842744271326d400000000269426542614000025d425942554251424e324a42464242423e423a42364232422e422a42264222421e421a42164213320f420b4000020830000205320141fd41f941f541f1400001ef21eb41e741e341df41dd2
|7,2=>0x3814380137c437933772373436f436b436743634360335c435843544351334d434b234743452341433d433943363332432f332d232a300003264322431e431b331743143310430c430933054301400002ff22fc32f932f542f1400002ed42ea32e642e242df32db42d742d342d032cc42c9300002c632c242be42ba42b732b43
|7,3=>0x4574453444f444c344844444441343e343a443734334430342c4000042934281424442040000000041c441844153412340e440a44073000040343ff43fc33f843f533f233ee43ea43e643e243de43db33d743d343d033cc43c933c543c143bd400003b943b543b233ae43aa43a643a2439e439a439643924391138d438943854
|7,4=>0x533452f452b452835244520451c4518451715143511350e350a4506450244fe44fb34f8300004f444f044ec44e844e534e144dd44d944d634d244ce44ca44c644c334c034bd34b944b544b1400004ad44aa300004a824a444a1349d449944963492448e448a448824844481347d447944763472446e446a44664462445e445b3
|7,5=>0x54d4549454540000541453d4000053b25374
|8,0=>0x60e360b36083605360235ff35fc35f935f635f335f035ed35ea35e735e435e135de35db35d835d535d235cf35cc35c935c635c335c035bd35ba35b735b435b135ae35ab35a835a535a2359f359c3599359635933590358d358a358735843581357e357b357835753572356f356c3569356635633560355d355a3557355435513
|8,1=>0x6cb36c836c536c326c036bd36ba36b736b436b136ae36ab36a836a536a2369f369c3699369636933690368d368a368736852682367f367c3679367636733670366d366a366736643661365e365b365836553652364f364c3649364636433640363d363a363736343631362e362b3628362536232620361d361a3617361436113
|8,2=>0x78a378737843781377e377b377837753772376f376c3769376637633760375d375a375737543751374e374b374837453742373f373c3739373637333730372d372a372737243721371e371b371837153712370f370c370937063703370036fd36fa36f736f436f136ee36eb36e836e626e336e036dd36da36d736d436d136ce3
|8,3=>0x7bd27ba37b737b437b137ae37ab37a837a537a2379f379c3799379637933790378d3
|9,0=>0x827282528232821281f281d281b28192817281528132811280f280d280b2809280728052803280127ff27fd27fb27f927f727f527f327f127ef27ed27eb27e927e727e527e327e127df27dd27db27d927d727d527d327d127cf27cd27cb27c927c727c527c327c127bf2
|10,0=>0x82f182e182d182c182b182a18291
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 16
def pmP:Nat→Nat
|0=>0x420000008100000100800002000000020000000214000004180000080000000c400000158000002a00000053000000a2000001400000023800000440000008600000100000000f0000001400000026000000480000008800000100000000e000000180000002800000040000000600000008000000080000000
|1=>0x1ca800003940000070a00000c540000182200003004000050200000a00000011080000215000004238000084400001080000020100000400000006010000088e00001110000020a0000040400000800000009c8000013300000256000004a8000009440000121800002420000048200000900000010a00000211
|2=>0x3088000060400000c00000016570000280000004b5c000096a80001276000024ae000049540000928800012500000243c0000485c000090a800012140000242200004840000090280001200000021ae000041c8000083300001054000020880000410c000080b000010140000202200004040000080200001000
|3=>0xa000000129500002500000048140000848600010800000202b8000400000007cae0000f9100001d2b8000321100005ca200008950000110200002200000040a00000811c0001021800020400000402000008004000100000001e5700003c88000071500000e2880001c5000003888000071040000d2b80001a53
|4=>0x1002c2802005000040096380801257010020040200400004001008080001601000028020000480400008008000060100000a020000000350b07004016d700201402004008000080001800f001e0010243e0010435c0004000000078000000c4000001695c0002b2b800056550000ac2800015000000292b80005214
|5=>0x2002cae0400515c080092b81000a40020014000400195c0800101010000530200002404000040080000281000000018028080201695c0402b6b808056570100ac88020158500402b08008056040100a8a60201511c0402a0a008052570100a4aa02014850040280000804843010074ae0200814c0400e0b80801a57
|6=>0x300200c0600295c0c0010b018002140300040e060008180c00001018000010200f4ae0401e9100803c0801006a540200d028040189500802d2b81005a500200b488040168400802c28010056570200a4ae04012950080252981004a47020094280401215008022018100420002005020040088000800d2a01001810
|7=>0x700042c0c00491c1800123828012470500240e08404b5c108060a0204021404012c2608024b5c100202802004006040054a60800795c1000f2182001c43040034a60800614c1000b2982001257040024280800401c100080002000e540400042808000800100002802000006030024ae060048480c0080b01801007
|8=>0x820adae1001eb5c2003d43840072570800b0ae1001525c2002a2b840052d708007dae1000c95c2000f6b84001e5708003ca61000735c2000e2b84001c40080034ae1000694c2000d0b8400189708002dae1000535c2000a4b840012d7080024ae1000485c200010084000200080000000e004b5c1c0092b83801243
|9=>0x641012d7c08125af1002eb5e2001d6bc11012d7820025af00004b5d20009eba40012d7480024ae40000104600092b880012171000000618024b5c3000f6b85105a170a00f5ae1401e95c280296b850032570a00552e14004b5c280084b85000497
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x80000
|5,0=>0xb8000017000000000000000000000000000000000000000180002068000000
|6,0=>0x700018001241c0029804108c1310000040f870820a000002c0000000005d0001800100006c0000000609600000000000488000000188700000000c40004000a9320004000001c00108860807078000e0000062000000000690023c00000f000001c0000000000002000000000052080000000000e00000000d0001c4a000001000000000000000000000182243800
|6,1=>0x1a400000000000790200000003c000347902000f000
|7,0=>0x7b805480802020120f05360e0be1f8901e000488d88ca000000c0521000b5194d874088a00b2566054b00c02980f18975100b1e888410016c0033860143e0e4a800388e8887d264053c801cae1e25814bb04a141c316e9e862c0070e9863774884000000820fe014a820088e91b9802de2695464014a0ec042e48008fa3818808005f5d8701004028725852212d54a56
|7,1=>0x48140a0e1c9b4709a0f8203a04008013c2b011600000009d00408030840800099b50e84410703e9d07a611a2c7388d3c713f805541f000401270048383a970ab640a0181a78820e272483c40733504019063e4085200910084274adc312175218e01636100fe0023bb85a042903916f0200d03a000e2d8f40103801725e54004d6c5108e8f4ae38000701e848041004
|7,2=>0x13640e401058d000100b55cac3a0e2918e088e5a038f40e0287c980261010001009180d4883e3e0247f279c5ca2e040101d1d1094000344f000086e042f19604048241208049fca2a11c03ca12e111643c7f
|8,0=>0x8b271d80408a156117129725f152bc71a52489ae0cce270204ed160e4a5e8e354b28f71422185c6777fa71d6466a1c8eaa60a972290d43389b6b154b365ec62e02152cb5137dc700982bc890f74499d69c10bb2692a65bf95cb02ba8090ef1ecb5e2642a2f55ad66d15d0a3e7685161257e38d02278341dc91f662b182a83f409d6dd852050cb26ea00cafd2bbd97e16
|8,1=>0x81aa19e6dc6838da028342fc7ea93a9697ece68b29daa87d9bda2a05fc61b4838f46c282f9b206447356915c712652f4af0e85b55a6858a95dd8bd5f9a24f286595ccee3843e93ea3678d98ee575c5150042bab5c2f5050fcaed1
|9,0=>0x11899c1e708580971d8ec85cc5029c4318664bd30b4560d1342fda2815027102ec9ac3d38b0581a0ea6871bc8b93771ac0eebd5438dc6d75ebb0b8cb
|10,0=>0x270b4815e970ae61
|11,0=>0x57
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 31 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_222 10 roots_222 ops++addP pm 1 dom_219 10 roots_219 ops++addP pm 2 dom_207 9 roots_207 ops++addP pm 3 dom_148 4 roots_148 ops++addP pm 4 dom_215 9 roots_215 ops++addP pm 5 dom_198 5 roots_198 ops++addP pm 6 dom_221 10 roots_221 ops++addP pm 7 dom_157 7 roots_157 ops++addP pm 8 dom_93 7 roots_93 ops++addP pm 9 dom_159 9 roots_159 ops++addP pm 10 dom_151 6 roots_151 ops++addP pm 11 dom_85 5 roots_85 ops++addP pm 12 dom_95 9 roots_95 ops++addP pm 13 dzo_85_2 5 roots_85 ops++addP pm 14 dom_199 6 roots_199 ops++addP pm 15 dom_213 8 roots_213 ops++addP pm 16 dom_214 8 roots_214 ops++addP pm 17 dom_220 8 roots_220 ops++addP pm 18 dom_29 4 roots_29 ops++addP pm 19 dom_156 5 roots_156 ops++addP pm 20 dom_205 8 roots_205 ops++addP pm 21 dom_212 7 roots_212 ops++addP pm 22 dom_149 5 roots_149 ops++addP pm 23 dom_143 6 roots_143 ops++addP pm 24 dom_79 6 roots_79 ops++addP pm 25 dom_31 5 roots_31 ops++addP pm 26 dzo_213_2 6 roots_213 ops++addP pm 27 dom_141 5 roots_141 ops++addP pm 28 dom_211 8 roots_211 ops++addP pm 29 dzo_221_2 7 roots_221 ops++addP pm 30 dzo_93_2 6 roots_93 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_223 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_85_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_213_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_221_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_93_2_85 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_222 10 s (0,roots_222.map (·&&&dom_222)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_223 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_222 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_223 gM v ys):RunD true dom_223 gM v (ori ys):=h
def Z (s:Nat):=barP dom_223 gM mpG SD SS NN hAt idxH ori 1000003 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 36 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 149 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 21 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 149 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 330 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 74 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 330 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 209 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 81 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 209 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 53 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 53 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 7 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_223 gM mpG SD SS NN hAt idxH ori 1000003 mkCut s i=true:=by
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
theorem lowS_239:Lower true dom_239 roots_239 goal_239 12:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,8,10)] (by decide +kernel) lowS_237
theorem lowS_251:Lower true dom_251 roots_251 goal_251 12:=lower_slice_b [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,8,10)] (by decide +kernel) lowS_249
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_slice_b [(0x3030303030303030303030303030303030303030303030303030303030303030,16,20)] (by decide +kernel) lowS_249
namespace S_254
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,130),(4,20),(4,36),(4,68),(4,132),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(8,136),(12,14),(12,28),(12,44),(12,76),(12,140),(16,20),(16,80),(16,144),(18,22),(18,26),(18,50),(18,82),(18,146),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,36),(32,40),(32,96),(32,160),(48,50),(48,52),(48,56),(48,112),(48,176),(64,68),(64,72),(64,80),(64,96),(64,192),(66,70),(66,74),(66,82),(66,98),(66,194),(128,130),(128,132),(128,136),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x15555555400000001555555540000000155555554000000015555555400000002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80005500550055005500550055005500550055005500550055005500550055005500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a11111111111111111111111111111111111111111111111111111111111111112aaaaaaaaaaaaaaa80000000000000002aaaaaaaaaaaaaaa80000000000000005555555555555555555555555555555500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ac688
|_=>0
def sO:Nat→Nat→Nat
|11,0=>7
|_,_=>0
def wAt:=mkWire dB 7 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_190 10 roots_190 ops++addP pm 2 dom_250 10 roots_250 ops++addP pm 3 dom_246 10 roots_246 ops++addP pm 4 dom_238 10 roots_238 ops++addP pm 5 dom_222 10 roots_222 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_222 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
  · simp [NN] at hi
  · simp [NN] at hi
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
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,10),(2,34),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,40),(8,72),(8,136),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,36),(32,40),(32,96),(32,160),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,72),(64,80),(64,96),(64,192),(66,67),(66,70),(66,74),(66,82),(66,98),(66,194),(128,129),(128,130),(128,132),(128,136),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xfac688
|_=>0
def sO:Nat→Nat→Nat
|13,0=>8
|_,_=>0
def wAt:=mkWire dB 8 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0x3f80
|_=>0
def pmB:Nat→Nat→Nat
|13,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_191 12 roots_191 ops++addP pm 2 dom_253 12 roots_253 ops++addP pm 3 dom_251 12 roots_251 ops++addP pm 4 dom_127 12 roots_127 ops++addP pm 5 dom_239 12 roots_239 ops++addP pm 6 dom_223 12 roots_223 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_223 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
  · simp [NN] at hi
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [7, 5] }, { op := GateOp.or, inputs := [6, 8] }, { op := GateOp.or, inputs := [9, 3] }, { op := GateOp.or, inputs := [6, 0] }, { op := GateOp.or, inputs := [9, 6] }, { op := GateOp.or, inputs := [8, 3] }, { op := GateOp.or, inputs := [1, 12] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.or, inputs := [7, 10] }, { op := GateOp.and, inputs := [16, 17] }, { op := GateOp.and, inputs := [15, 11] }, { op := GateOp.and, inputs := [14, 13] }, { op := GateOp.or, inputs := [18, 19] }, { op := GateOp.or, inputs := [21, 20] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52990_aux

theorem PEqualNP.Outside.L_meta_52990 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52990_aux.main
