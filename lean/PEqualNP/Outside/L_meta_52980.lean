import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52980_aux
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

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfefeaa00fefeaa00fefeaa00fefeaa00fefeaa00fefeaa00fefeaa00fefeaa00
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

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
def goal_51 : Nat := 0xffffeeeeeeee0000ffffeeeeeeee0000ffffeeeeeeee0000ffffeeeeeeee0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xffffaaaafafa0000ffffaaaafafa0000ffffaaaafafa0000ffffaaaafafa0000
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xffffccccfcfc0000ffffccccfcfc0000ffffccccfcfc0000ffffccccfcfc0000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xffffeeeefefe0000ffffeeeefefe0000ffffeeeefefe0000ffffeeeefefe0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffffffaaaaaaaa00ffffffaaaaaaaa00ffffffaaaaaaaa00ffffffaaaaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffffffcccccc0000ffffffcccccc0000ffffffcccccc0000ffffffcccccc0000
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffffffeeeeeeaa00ffffffeeeeeeaa00ffffffeeeeeeaa00ffffffeeeeeeaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_60 : Nat := 0x1111111111111111
def goal_60 : Nat := 0xffffff00f0f00000ffffff00f0f00000ffffff00f0f00000ffffff00f0f00000
def roots_60 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xffffffaafafaaa00ffffffaafafaaa00ffffffaafafaaa00ffffffaafafaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xffffffccfcfc0000ffffffccfcfc0000ffffffccfcfc0000ffffffccfcfc0000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xffffffeefefeaa00ffffffeefefeaa00ffffffeefefeaa00ffffffeefefeaa00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfffafffafffafffaaa00aa00aa00aa00fffafffafffafffaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffaaaaffffaaaaeeee0000eeee0000ffffaaaaffffaaaaeeee0000eeee0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffff0f0fffff0f0fcfc0000fcfc0000fffff0f0fffff0f0fcfc0000fcfc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffafafffffafafefe0000fefe0000fffffafafffffafafefe0000fefe0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffffaaffffffaaaaaaaa00aaaaaa00ffffffaaffffffaaaaaaaa00aaaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffff00ffffff00cccc0000cccc0000ffffff00ffffff00cccc0000cccc0000
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffaaffffffaaeeeeaa00eeeeaa00ffffffaaffffffaaeeeeaa00eeeeaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfffffff0fffffff0f0f00000f0f00000fffffff0fffffff0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffffafffffffafafaaa00fafaaa00fffffffafffffffafafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffff0fffffff0fcfc0000fcfc0000fffffff0fffffff0fcfc0000fcfc0000
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffffafffffffafefeaa00fefeaa00fffffffafffffffafefeaa00fefeaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_97 : Nat := 0x3000000030000000300000003
def goal_97 : Nat := 0xffffffffaaaaaaaaaaaaaaaa00000000ffffffffaaaaaaaaaaaaaaaa00000000
def roots_97 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xffffffffaaaaaaaaeeeeeeee00000000ffffffffaaaaaaaaeeeeeeee00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfffffffff0f0f0f0cccccccc00000000fffffffff0f0f0f0cccccccc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfffffffffafafafaeeeeeeee00000000fffffffffafafafaeeeeeeee00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_104 : Nat := 0x101000001010000010100000101
def goal_104 : Nat := 0xffffffffff00ff00ff00ff0000000000ffffffffff00ff00ff00ff0000000000
def roots_104 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffffaaffaaffaaffaaaa00aa00ffffffffffaaffaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffff00ff00ffccffcc00000000ffffffffff00ff00ffccffcc00000000
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffffaaffaaffeeffeeaa00aa00ffffffffffaaffaaffeeffeeaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfffffffffff0fff0ff00ff0000000000fffffffffff0fff0ff00ff0000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffffffffffafffaffaaffaaaa00aa00fffffffffffafffaffaaffaaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffffffffff0fff0ffccffcc00000000fffffffffff0fff0ffccffcc00000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffffffffffafffaffeeffeeaa00aa00fffffffffffafffaffeeffeeaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffffffffffaaaaffffaaaaaaaa0000ffffffffffffaaaaffffaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffffff0000ffffcccccccc0000ffffffffffff0000ffffcccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffffffaaaaffffeeeeeeee0000ffffffffffffaaaaffffeeeeeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffffffffffff0f0ffff0000f0f00000fffffffffffff0f0ffff0000f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffffffafaffffaaaafafa0000fffffffffffffafaffffaaaafafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffffff0f0ffffccccfcfc0000fffffffffffff0f0ffffccccfcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffffffafaffffeeeefefe0000fffffffffffffafaffffeeeefefe0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffffffffffff00ffffff0000000000ffffffffffffff00ffffff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffffffaaffffffaaaaaaaa00ffffffffffffffaaffffffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffffff00ffffffcccccc0000ffffffffffffff00ffffffcccccc0000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffffffaaffffffeeeeeeaa00ffffffffffffffaaffffffeeeeeeaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffffffffffff0ffffff00f0f00000fffffffffffffff0ffffff00f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffffffaffffffaafafaaa00fffffffffffffffaffffffaafafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffffff0ffffffccfcfc0000fffffffffffffff0ffffffccfcfc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffffffaffffffeefefeaa00fffffffffffffffaffffffeefefeaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffefffefffefffefffefffefffefffeaa00aa00aa00aa00aa00aa00aa00aa00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_146 : Nat := 0x5000500000000000000000000000000050005
def goal_146 : Nat := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000eeee0000eeee0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcfc0000fcfc0000fcfc0000fcfc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefefefe0000fefe0000fefe0000fefe0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffcccccc0000cccc0000cccc0000cccc0000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfffffff0fffffff0fffffff0fffffff0f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffafafaaa00fafaaa00fafaaa00fafaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfcfc0000fcfc0000fcfc0000fcfc0000
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffefffffffefffffffefffffffefefeaa00fefeaa00fefeaa00fefeaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_162 : Nat := 0x50000000500000000000000000000000500000005
def goal_162 : Nat := 0xffffffffccccccccffffffffcccccccccccccccc00000000cccccccc00000000
def roots_162 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfccccccccc00000000cccccccc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffefefefefffffffffefefefeeeeeeeee00000000eeeeeeee00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

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
def goal_172 : Nat := 0xfffffffffff0fff0fffffffffff0fff0ff00ff0000000000ff00ff0000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffffcfffcfffffffffffcfffcffccffcc00000000ffccffcc00000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffefffefffffffffffefffeffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffffaaaaffffffffffffaaaaffffaaaaaaaa0000ffffaaaaaaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffffffccccffffffffffffccccffffcccccccc0000ffffcccccccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffeeeeffffffffffffeeeeffffeeeeeeee0000ffffeeeeeeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0ffff0000f0f00000ffff0000f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffffcfcfffffffffffffcfcffffccccfcfc0000ffffccccfcfc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffefefffffffffffffefeffffeeeefefe0000ffffeeeefefe0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffffffffffff00ffffffffffffff00ffffff0000000000ffffff0000000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffffaaffffffffffffffaaffffffaaaaaaaa00ffffffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffffccffffffffffffffccffffffcccccc0000ffffffcccccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffeeffffffffffffffeeffffffeeeeeeaa00ffffffeeeeeeaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0ffffff00f0f00000ffffff00f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffffafffffffffffffffaffffffaafafaaa00ffffffaafafaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffffcfffffffffffffffcffffffccfcfc0000ffffffccfcfc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffefffffffffffffffeffffffeefefeaa00ffffffeefefeaa00
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
def goal_202 : Nat := 0xffffffffffffffffffccffccffccffccff00ff00ff00ff000000000000000000
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffffafffafffafffafffafffafffafffaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffffffffffffffffffcfffcfffcfffcfff0fff0fff0fff00000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffefffefffefffefffafffafffafffaaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffffffccccffffccccffff0000ffff0000cccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffaaaaffffaaaaeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffff0f0fffff0f0fcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffefefffffefefffffafafffffafafefe0000fefe0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffffccffffffccffffff00ffffff00cccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffeeffffffeeffffffaaffffffaaeeeeaa00eeeeaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffffafffffffafffffffafffffffafafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffffcfffffffcfffffff0fffffff0fcfc0000fcfc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffefffffffefffffffafffffffafefeaa00fefeaa00
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

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f00000000000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfffffffff0f0f0f0cccccccc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffffffffffefefefefffffffffafafafaeeeeeeee00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffffffffffff00ff00ffffffffff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffffccffccffffffffff00ff00ffccffcc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffeeffeeffffffffffaaffaaffeeffeeaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffffffffffff0fff0fffffffffff0fff0ff00ff0000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffffffffffafffafffffffffffafffaffaaffaaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffffffffffcfffcfffffffffff0fff0ffccffcc00000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffefffefffffffffffafffaffeeffeeaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffffffffffffffffffff0000ffffffffffff0000ffff000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffffffffffaaaaffffffffffffaaaaffffaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffffffccccffffffffffff0000ffffcccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffffffeeeeffffffffffffaaaaffffeeeeeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffffffafafffffffffffffafaffffaaaafafa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffffffcfcfffffffffffff0f0ffffccccfcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffffffefefffffffffffffafaffffeeeefefe0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffffffffffffffffffff00ffffffffffffff00ffffff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffffffaaffffffffffffffaaffffffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffffffccffffffffffffff00ffffffcccccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffffeeffffffffffffffaaffffffeeeeeeaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffffffffffff0fffffffffffffff0ffffff00f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffffffafffffffffffffffaffffffaafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffffffcfffffffffffffff0ffffffccfcfc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffffffefffffffffffffffaffffffeefefeaa00
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
def isoMvS_73:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_73:Lower true dom_73 roots_73 goal_73 4:=lower_iso_b isoMvS_73 (by decide +kernel) lowS_41
def isoMvS_97:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_97:Lower true dom_97 roots_97 goal_97 4:=lower_iso_b isoMvS_97 (by decide +kernel) lowS_41
def isoMvS_104:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_104:Lower true dom_104 roots_104 goal_104 4:=lower_iso_b isoMvS_104 (by decide +kernel) lowS_41
def isoMvS_146:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_146:Lower true dom_146 roots_146 goal_146 4:=lower_iso_b isoMvS_146 (by decide +kernel) lowS_41
def isoMvS_162:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_162:Lower true dom_162 roots_162 goal_162 4:=lower_iso_b isoMvS_162 (by decide +kernel) lowS_41
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
theorem lowS_43:Lower true dom_43 roots_43 goal_43 5:=lower_slice_b [(0xc0c00000c0c,32,34)] (by decide +kernel) lowS_41
theorem lowS_51:Lower true dom_51 roots_51 goal_51 5:=lower_slice_b [(0xa000a000a000a,16,17)] (by decide +kernel) lowS_50
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
|0=>0x204c1324d1404c1424c930409
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
def isoMvS_29:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_29:Lower true dom_29 roots_29 goal_29 4:=lower_iso_b isoMvS_29 (by decide +kernel) lowS_27
def isoMvS_53:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_53:Lower true dom_53 roots_53 goal_53 5:=lower_iso_b isoMvS_53 (by decide +kernel) lowS_43
def isoMvS_54:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 5:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_43
def isoMvS_57:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_51
def isoMvS_58:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 5:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_43
def isoMvS_60:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_60:Lower true dom_60 roots_60 goal_60 4:=lower_iso_b isoMvS_60 (by decide +kernel) lowS_27
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 5:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_43
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_43
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_43
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 4:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_27
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 5:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_43
def isoMvS_99:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_43
def isoMvS_102:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 4:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_27
def isoMvS_106:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_43
def isoMvS_108:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 5:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_43
def isoMvS_113:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 7:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_105
def isoMvS_114:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_51
def isoMvS_116:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_51
def isoMvS_120:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 5:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_51
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_43
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_51
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_51
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_43
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_43
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_51
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_43
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 7:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_105
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_51
def isoMvS_172:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 5:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_43
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 7:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_105
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 7:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_105
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_51
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 5:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_51
def isoMvS_195:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_43
def isoMvS_198:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_43
def isoMvS_201:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 7:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_105
def isoMvS_202:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_43
def isoMvS_204:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 5:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_51
def isoMvS_209:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 7:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_105
def isoMvS_210:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_51
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 7:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_105
def isoMvS_216:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 5:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_51
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 7:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_105
def isoMvS_226:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_51
def isoMvS_228:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 5:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_51
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 7:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_105
def isoMvS_240:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_240:Lower true dom_240 roots_240 goal_240 7:=lower_iso_b isoMvS_240 (by decide +kernel) lowS_105
theorem lowS_31:Lower true dom_31 roots_31 goal_31 5:=lower_slice_b [(0xcccccccc,16,18)] (by decide +kernel) lowS_29
theorem lowS_55:Lower true dom_55 roots_55 goal_55 6:=lower_slice_b [(0xaa00aa00aa00aa,16,17)] (by decide +kernel) lowS_54
namespace S_59
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,18),(2,34),(3,11),(3,19),(3,35),(8,9),(8,40),(10,11),(10,26),(10,42),(16,17),(16,18),(16,48),(24,25),(24,26),(24,56),(32,33),(32,34),(32,40),(32,48)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_59.map (·&&&dom_59)
def gM:=goal_59&&&dom_59
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x9abd7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f00000000f0f00000f0f0000f000f000f000f00c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 60 0xfffffffffffffff
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
addP pm 0 dom_58 5 roots_58 ops++addP pm 1 dom_57 5 roots_57 ops++addP pm 2 dom_51 5 roots_51 ops++addP pm 3 dom_43 5 roots_43 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_43 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_58 5 s (0,roots_58.map (·&&&dom_58)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_59 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_58 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_59==dom_59)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_59 gM v ys):RunD true dom_59 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_59 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_59 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_57_4:=0x3030303030303030
def gzo_57_4:=0x3030302030302000
def gsh_57_4:=0x303030203030200
theorem lowS_zo_57_4_41:Lower true dzo_57_4 roots_57 gzo_57_4 5:=lower_iso_b (d1:=dom_57) (r1:=roots_57) (T1:=gsh_57_4) [(dom_57,4)] (by decide +kernel) (lower_slice_b (T:=gsh_57_4) [(0x303000003030000,0,16)] (by decide +kernel) lowS_41)
namespace S_61
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(4,20),(5,13),(5,21),(5,37),(8,9),(8,40),(12,13),(12,28),(12,44),(16,17),(16,20),(16,48),(24,25),(24,28),(24,56),(32,33),(32,40),(32,48),(36,37),(36,44),(36,52)]
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
|4,0=>0xb6d8e
|5,0=>0xd9213
|6,0=>0xd596d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3333333322222222cc00cc00cc00cc03333333300000000cccc0000cccc00030303030303030308888888888888888033003300220022
|_,_=>0
def sP:Nat→Nat
|0=>0x8ea3a3a8c688
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
|0=>0x85
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
addP pm 0 dom_57 5 roots_57 ops++addP pm 1 dom_60 4 roots_60 ops++addP pm 2 dzo_57_4 5 roots_57 ops++addP pm 3 dom_53 5 roots_53 ops++addP pm 4 dom_41 4 roots_41 ops++addP pm 5 dom_29 4 roots_29 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_61 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_57_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_29 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_57 5 s (0,roots_57.map (·&&&dom_57)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_61 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_57 h
def symsG:List (List (Nat×Nat)):=[[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
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
theorem lowS_62:Lower true dom_62 roots_62 goal_62 6:=lower_slice_b [(0x5050505050505050,16,20)] (by decide +kernel) lowS_58
theorem lowS_107:Lower true dom_107 roots_107 goal_107 8:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c,32,34)] (by decide +kernel) lowS_105
theorem lowS_115:Lower true dom_115 roots_115 goal_115 8:=lower_slice_b [(0xc000c000c000c000c000c000c000c,16,18)] (by decide +kernel) lowS_113
theorem lowS_121:Lower true dom_121 roots_121 goal_121 8:=lower_slice_b [(0x3000300030003000300030003000300,1,9)] (by decide +kernel) lowS_113
theorem lowS_143:Lower true dom_143 roots_143 goal_143 6:=lower_slice_b [(0xcccc0000000000000000000000000000cccc,128,130)] (by decide +kernel) lowS_141
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_slice_b [(0xaa00aa00000000000000000000000000aa00aa,16,17)] (by decide +kernel) lowS_150
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
def isoMvS_87:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_iso_b isoMvS_87 (by decide +kernel) lowS_55
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 7:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_61
def isoMvS_94:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 6:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_62
def isoMvS_103:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_62
def isoMvS_109:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 8:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_107
def isoMvS_110:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_62
def isoMvS_117:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 8:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_115
def isoMvS_118:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_59
def isoMvS_122:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_59
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 7:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_59
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 7:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_59
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 7:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_59
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 6:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_55
def isoMvS_167:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_55
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_115
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_107
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_55
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 8:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_121
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 8:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_115
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 8:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_121
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 8:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_115
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 7:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_59
def isoMvS_199:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 6:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_55
def isoMvS_206:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 6:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_55
def isoMvS_211:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 8:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_115
def isoMvS_214:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 8:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_115
def isoMvS_218:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 7:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_59
def isoMvS_220:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 8:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_115
def isoMvS_227:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 8:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_115
def isoMvS_230:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 7:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_59
def isoMvS_234:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 8:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_115
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 8:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_115
def isoMvS_241:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 9:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_233
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 8:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_121
def isoMvS_248:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 8:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_121
def dzo_43_4:=0xf0f00000f0f0
def gzo_43_4:=0xf0e00000a000
def gsh_43_4:=0xf0e00000a00
theorem lowS_zo_43_4_43:Lower true dzo_43_4 roots_43 gzo_43_4 5:=lower_iso_b (d1:=dom_43) (r1:=roots_43) (T1:=gsh_43_4) [(dom_43,4)] (by decide +kernel) (lower_slice_b (T:=gsh_43_4) [] (by decide +kernel) lowS_43)
def dzo_59_4:=0xf0f0f0f0f0f0f0f0
def gzo_59_4:=0xf0f0f0e0f0f0a000
def gsh_59_4:=0xf0f0f0e0f0f0a00
theorem lowS_zo_59_4_43:Lower true dzo_59_4 roots_59 gzo_59_4 6:=lower_iso_b (d1:=dom_59) (r1:=roots_59) (T1:=gsh_59_4) [(dom_59,4)] (by decide +kernel) (lower_slice_b (T:=gsh_59_4) [(0xf0f00000f0f0000,0,16)] (by decide +kernel) lowS_43)
namespace S_63
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,18),(2,34),(3,11),(3,19),(3,35),(4,20),(5,13),(5,21),(5,37),(6,22),(6,38),(7,15),(7,23),(7,39),(8,9),(8,40),(10,11),(10,26),(10,42),(12,13),(12,28),(12,44),(14,15),(14,30),(14,46),(16,17),(16,18),(16,20),(16,48),(24,25),(24,26),(24,28),(24,56),(32,33),(32,34),(32,40),(32,48),(36,37),(36,38),(36,44),(36,52)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_63.map (·&&&dom_63)
def gM:=goal_63&&&dom_63
def NN:Nat→Nat
|3=>1
|4=>30
|5=>85
|6=>62
|7=>14
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x954d0
|4,0=>0xff9b5fece0fc946ef0a8ebaa7e06bfdbc2ada30ecd85cbce5eb51d49bbc188c3b839647e81f75dd8749995a6705550d54cda4f1b34b8d4404313fab335f242e3a31d71a16bf40fac20caea
|5,0=>0xfdf56fdd14fd208f98eef8e11f6d49f389def874ea6aae4133df212dd263dcdc5dca00dc671daeffdaca3d4c62d3f67cf2cccc3afcc0d1cbea5c9a00c7ac7c3a32c3719c1865c0093b858bb7e91b1fb7af7e5adff8abdbfa6102a542da45319ed5a9be19982839697895e639267f8f9147f8597988a792d278ab977b4e72ad46d1cb695f966099629cd623fe623916013d5fa735b921595e6552b75490053c5f52c914dbfa4584c36c9634849277af268ea2571323e3322f5a1de9a135ff09e5e086b90774f06922053d10199b00dbd0060e00257
|6,0=>0xfd833f9e4bf23f0f0dc2e9efae8886e53e3e3bebd97f6d6184d3bd8d2847cf8a9ce108cb3fbc81ecc68d6c4659c06dec029ab9d4ca9467a6d5ba521ba4233a0edc9bce9985608dbf18d95f819587ed2f7ce537ac007a84976d1d7314b6ed1469e66635d25630f55a76540964be3949e744877e464973b2093a8653528c32b7d324833127a2e1d725b8c2250b1ffd719cf01934c12cff1287502396
|7,0=>0xe79ace7166dd808d4175ba6a9b57fbaa9129933e814b077e2567c7f29ed41e1dc14dd9
|8,0=>0xc6758
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffaaaaaaaaaaffffffffaaaaaaaaffffffaaff00ff00000000ffffffff000fff00ff0faf00aaffffeeeeccccccccccccccccccccccccffffffff00000000ffff0000ffff0000ff00ff00ff00ff00aaaaaaaaaaaaaaaa3333333323232222ffffffffffff0000ffffff00aaaaaa00f0f0f0f0f0f0f0f0eeeeeeeeeeeeeeee
|0,1=>0xffffffffafafaaaa131311110303000000000000fefefefeffffaaaaffffaaaaffffffffffffaaaa00000000afafaaaaffffffcccccccccc1111111101010000ffffffff0f0f0000bbbbbbbbababaaaaffffff00ffffff0000000000ffffaaaaffffffffff00ff005555555554545454ffff0000fefe0000ffffffffffffff00
|0,2=>0x1111111111110000333333333333330000ff00ff00ff00aa555555550505000033330033333300005f5f55550f0f0000000000aaaaaaaaaa55555555555555005555555500000000f1f1f1f1f0f0f0f0fefefefefefefefe0000ffff00000000aaaaffffaaaaaaaa03330033030300001111111100000000eeeeeeeeeeee0000
|0,3=>0xff00ff0000000000000000ffffff00bbbbbbbbbbbbaaaaffff5555ffff0000fffffffffafafafaffffaaaa00000000ffff00ffffff00aa00ff00ff00ee00eefffffffffefefefeaaaaaaaaaaaaaa003333333333330000bbbbbbbbaaaaaaaa00ff00ff00aa00aa3333111133330000ffffff00000000005555550055555500
|0,4=>0xff000000000fff00ff0f0f00001111111110101010ffffff00ffff000000aa00ff00aa00aaffff00ffffff0000f0fff0fff0faf0fa0000ffff0000aaaa0000ffff0000ff003333333333332222fffffffff0f0f0f055555555555500003333333303030000efefeeeeefefeeee0f0f00000f0f0000afafaaaaafafaaaa
|0,5=>0xfafafafafafafafa0000ff000000ff00ffffffaaffffffaa5555555550505050ffffffffeeeeeeeeff00ffffff00ff00f0fff0fff0f0f0f0f5f5f5f5f0f0f0f0ffffeeeeffffeeee00ff00ff00ff00000000555500000000000000ff000000aa
|_,_=>0
def sP:Nat→Nat
|0=>0x1e540891070301407c4070c001992a042880e1829e1c1c3003a2011c022418f0c0449b1054080101c300340cc8602144070c14c0e2e1c300101c3160a20a81005098f0e044880e1801210443000a40787022470d0e04487022428c101c485160c506021418202242880e182840608080
|1=>0x1220a8702157080e044855a20a9c02004070c242ac1064a8702144070c042ab101c3090aa818e0e18080105438112a44070c044a82e1c3090a9c4070c980051c20a9c02244070c942a12e2038600147070c04024101c301008c7070c050031c54080101c305441c30542744020e04003
|2=>0xc044831c540890a21c8702242880e0400570dc4070c00288141c3010a203860200a08041c0890a20a870225b0310540856a4d88702242882a1c08950203860201a080e180053a38407020198e1054381007c4070c242880e18085644188702242882a1c080602038602157881e54381
|3=>0x101c48582cc18e381808910540890b1c4070c042c68a384070c004070c020082a04485885c4070c161880e1a1000a0ca8112153880e180a00a0c41502002bb101c48566384070c0208362180890a6c4070c0400e101c309801c0890afdf080e180bd0a20abc02242bb1c203860039d07
|4=>0xb3df080e18485342038612167032ac40890a0c41c0c040080e182c3101c3000b3440f0e180898a203890acc4070c042ae1056601121440d0e04485101c0890b2c19502242be1c5c3861214415940448510540890a504190e18085101e4890acc4070c0404806e830112147080e19280
|5=>0x101c3011216408381c301002038600160931054381121628e101c3090a2038613002882a1c0890af8b880e184852020a8702242880e044856621d070c044851c20e070c0448e101c3090b044070c04005426c4070c044851054381121539b10540890a20a9c02258080e04485a01c089
|6=>0x8a20386121418e0e180890a2038602242cf10543811215f93101c3090b044530e180800a3838602242a4101c301128c283101c3010ad44070c04485a40c4150c044850620e0602242880e192800a203860215a880e180890b462880e18005101c3090a9e0882ac43811215d880e18485
|7=>0xe180890af84070c044858e3840702242b30620a8112147082a1c0890a404070c04485101c3090b05f882a1c0890ac04070c0448588203861216c030e180890a9eb880e180800a0c4070c04005101eb0602242880e180800a904070d5448510f038602242882a700890a20386a824293
|8=>0xa2038602242a410543860224288381c30112144070c044854e2038602002c5101c3090a384070c04485101c3090b044070c044857e20a8702242880e04485b4384070c0403b1c2038612144310e180890a20a870200288b254381121444a0e180890a20a8702242cf101c3011214a08
|9=>0x80e180890a20386b624283101c30112149880e18089
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x4aa8905116a219440a87c50eea1c9436a86850c6a17942ca854509ea129422a8405076a0d9418a82c504ea08940ea8185026a039404a8045
|5,0=>0x424c831903320063f4c7d18f731e863c4c7754ebb1d16396c7158dfb1b96366c6b58d3b1a16336c6558c7b1896306c5f58bbb17162d6c5958afb15962a6c5358a3b1416276c4d5897b1296246c47588bb1116216c41587fb0f961e6c3b947430e261b8c35986830ca6188c2f985c30b26158c299850309a6
|5,1=>0x28f6512ca0d93eb27764e2c9ad932b26054b4c95192732486484c8f191b32306454c89190f32186
|6,0=>0x218b42a7846f075a0b3c0f7810f005dfd3bf377d8ef999efbbd877a2ef29de1bbbd676ceebddd43ba17734ee519c6bb876702cde9db9bb6c76caed79dabbb507692ed09d9dbb34765aec9d990b31a7628cc35d833b0065f2ebcd976b2e675beeb659693acc658aeafd95c3ab17554ea8dd4e3a957
|7,0=>0x246b48678fef1e1e38bc6a78c6f175a2bb4507894d10de1eb4376
|8,0=>0x4936
|_,_=>0
def wAt:=mkWire dB 92 64 0xffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xe0710560e1911050e0710550e191c1b101510700e15101510150e07100312150615101d0e191017101d2a17105412152e2710561c1f107010150201101d1015100512150e0710170600101d121510150e070615101d1c05107010151c540627100310961215121510152a1712150e190e151215101510031215101f1c541c1d
|1=>0x101b2a170e190617101d8a171005101710011215101d12151215101f02fd101b0e9d10170e150e19029d101710051015101d10570e190e19101b0e070e0112151015101f0a91101f0627101d101d101d020112150627101d10730e15100512150e07101710540e191c0510151c1f10150e1512150e0712151019101510050b05
|2=>0x215101d1019101f0e190e1510171215100510150e07101b0e190e1a101512151c05101510540e190e1912152a150e190efd101b10570e1910720e1510560e19261f10191c1b1015101d0e1910150e1910550e190e07
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11000000000000000000000000001000000000000000000000000000000000000000000000000
|5,0=>0x2512412220002020000001f11d20000000001c11a21911811710001520000000000001411311210000000000000001110001010000000f10d20b2000000000000092000000000000063000000000000000000000000000051032000000021
|5,1=>0x2b12a1000000000000291281271000000000000000000000261000000000000
|6,0=>0x9b29929729529329128f28d28b28928728528328127f27d27b27927817627420007227026e26c26a26916726526326216025e25c25a20005915815625425225024e24c24a24824624424314123f23d23b23923723523413223022e22c2
|7,0=>0xaa1a91a81a71a61a51a41a31a21a11a019f19e19d1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x10e008580422020c0102008000306011000480017c00ba005c002a801500088004000110007400380017000b00054002800100006000280010000400018000800020000
|1=>0x4024924be921f412ea096c8038321f11190884827be127f092f8496c245e121b09010480020be1040080c82000080002df016d80b4c04be025d012d8095004a0021f
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x80000000000002000000000000000000000000
|5,0=>0x2100000004105a8000000000400000000215901c000086000a84044a420030000003da100000000080100002610000000400000022000000000000004200002
|6,0=>0x9b75a47932493528557ccb222b81fe7c07ed2a4f10709350e5b2ce0116f5349cee3b12e8c85db052b29d807bd731f
|7,0=>0xd3bebb965ea7f7acba925
|8,0=>0x23
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 17 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_61 7 roots_61 ops++addP pm 1 dom_54 5 roots_54 ops++addP pm 2 dzo_43_4 5 roots_43 ops++addP pm 3 dom_43 5 roots_43 ops++addP pm 4 dom_59 7 roots_59 ops++addP pm 5 dom_58 5 roots_58 ops++addP pm 6 dom_55 6 roots_55 ops++addP pm 7 dom_60 4 roots_60 ops++addP pm 8 dom_57 5 roots_57 ops++addP pm 9 dom_62 6 roots_62 ops++addP pm 10 dom_51 5 roots_51 ops++addP pm 11 dzo_57_4 5 roots_57 ops++addP pm 12 dzo_59_4 6 roots_59 ops++addP pm 13 dom_27 4 roots_27 ops++addP pm 14 dom_41 4 roots_41 ops++addP pm 15 dom_31 5 roots_31 ops++addP pm 16 dom_29 4 roots_29 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_63 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_43_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_57_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_59_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_29 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_61 7 s (0,roots_61.map (·&&&dom_61)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_63 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_61 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_63 gM v ys):RunD true dom_63 gM v (ori ys):=h
def Z (s:Nat):=barP dom_63 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 30 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 30 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 85 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 85 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 62 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 62 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 14 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_63 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_111:Lower true dom_111 roots_111 goal_111 9:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc,32,34)] (by decide +kernel) lowS_109
theorem lowS_119:Lower true dom_119 roots_119 goal_119 9:=lower_slice_b [(0xcc00cc00cc00cc00cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_117
def dzo_89_2:=0xc0c0c0c000000000c0c0c0c
def gzo_89_2:=0xc0c0c08000000000c0c0800
def gsh_89_2:=0x30303020000000003030200
theorem lowS_zo_89_2_73:Lower true dzo_89_2 roots_89 gzo_89_2 5:=lower_iso_b (d1:=dom_89) (r1:=roots_89) (T1:=gsh_89_2) [(dom_89,2)] (by decide +kernel) (lower_slice_b (T:=gsh_89_2) [(0x30300000000000003030000,0,16)] (by decide +kernel) lowS_73)
def dzo_121_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_121_2:=0xc0c0c0c0c0c0c080c0c0c0c0c0c0800
def gsh_121_2:=0x3030303030303020303030303030200
theorem lowS_zo_121_2_73:Lower true dzo_121_2 roots_121 gzo_121_2 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_2) [(dom_121,2)] (by decide +kernel) (lower_slice_b (T:=gsh_121_2) [(0x3030000030300000303000003030000,0,16),(0x3030303000000000303030300000000,0,32)] (by decide +kernel) lowS_73)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,18),(2,34),(3,11),(3,19),(3,35),(3,67),(8,9),(8,40),(8,72),(10,11),(10,26),(10,42),(10,74),(16,17),(16,18),(16,48),(16,80),(24,25),(24,26),(24,56),(24,88),(32,33),(32,34),(32,40),(32,48),(32,96),(64,65),(64,72),(64,80),(64,96),(66,67),(66,74),(66,82),(66,98)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|5=>2
|6=>8
|7=>9
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x3cf2e3390d
|6,0=>0xb1f30b179d5e8135964f387743429d298001dd37
|7,0=>0xbaca95f86f4643a42e01424f33c00a391042514f1fafa
|8,0=>0x47c680e7a107721
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0a0a0a0a5050505050505050404040404040404f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0ae0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c00f000f000f000f000f000f000a000ac0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0aa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f000000000f0f0f0f00000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f00000000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f00f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e
|0,1=>0xe0e0e0e0e0e0e0e
|_,_=>0
def sP:Nat→Nat
|0=>0x105272b4c20a4e568cc20a4e51984159cc2080e530830395e61052728cc20a5072184159ca41882939466104ee698493a8a41882b398493a8a41882940cc2080e430927515a43082c28cc259d4418820
|1=>0x610527298414a0e53082c39466
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x56005
|6,0=>0x3863172b62561f61961270b7
|7,0=>0x7476c86666065a65374c74573e7
|8,0=>0x8878267b7
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 17 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x39549d31532139519d3154953154a139561749d21731d31539549531d31d31531559f49532139531d49531568732139539531d3154a131539568721521549d31d4a139531d315
|_=>0
def oO:Nat→Nat→Nat
|5,0=>4
|6,0=>0x5cd5248cf330c931c843
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0x1cf3e5153ce1e6cf3479a180ff67fa2798ffc7f62fa17b87f81e60d104000f8040000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>2
|6,0=>0x405847986e
|7,0=>0x149b5478c132
|8,0=>0x3ceb
|9,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 8 roots_121 ops++addP pm 1 dom_91 7 roots_91 ops++addP pm 2 dom_120 5 roots_120 ops++addP pm 3 dom_57 5 roots_57 ops++addP pm 4 dom_107 8 roots_107 ops++addP pm 5 dom_115 8 roots_115 ops++addP pm 6 dom_59 7 roots_59 ops++addP pm 7 dom_122 7 roots_122 ops++addP pm 8 dzo_89_2 5 roots_89 ops++addP pm 9 dzo_121_2 6 roots_121 ops++addP pm 10 dom_27 4 roots_27 ops++addP pm 11 dom_58 5 roots_58 ops++addP pm 12 dom_90 4 roots_90 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_89_2_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_121_2_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_90 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 8 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_123 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
namespace S_126
def pG:List (Nat×Nat):=[(2,18),(2,34),(4,20),(4,68),(6,22),(6,38),(6,70),(8,40),(8,72),(10,26),(10,42),(10,74),(12,28),(12,44),(12,76),(14,30),(14,46),(14,78),(16,18),(16,20),(16,48),(16,80),(24,26),(24,28),(24,56),(24,88),(32,34),(32,40),(32,48),(32,96),(36,38),(36,44),(36,52),(36,100),(64,68),(64,72),(64,80),(64,96),(66,70),(66,74),(66,82),(66,98)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_126.map (·&&&dom_126)
def gM:=goal_126&&&dom_126
def NN:Nat→Nat
|3=>1
|4=>6
|5=>13
|6=>9
|7=>2
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xc159f
|4,0=>0x895905c5ec487d9241621903d01d38
|5,0=>0xe8f129e0cc7f3ce5fb7936c2b2a6d61f8141b68c1b5db194e11361b077b90015f
|6,0=>0xe14d2700a461f35430fe418a93600c201e11ee571c647
|7,0=>0x524f424673
|8,0=>0x464f4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaa00000000aaaa000000000000000000015555555555540002222222222222222222222222222222255555555555555550000000000000000aaaaaaaaaaaa0000aaaaaaaaaaaa000155555555555555555555555400000000282828282828282828280000282800055555555000000005555555500000000aaaaaaaaaaaaaaaaaaaa0000aaaa000154015401540154015401540154015402828282828282828282828282828282855555555555500004444444444440000aaaaaaaaaaaaaaaaaaaaaaaaaaaa000155555555414141415555555541414142aaaaa802aaaaa802aaaaa802aaaaa8055555555555555554444444444444444
|0,1=>0x55555555555555005555555555555500222222222222000022222222222200015555540155555401555554000000000088888888888888888888888888880000055005500550055005500550000000000aa00aa00aa00aa00aa00aa00a000a155555554141414155555555414140000000002a8000002a8000002a8000000055550000555500005555000055550000
|_,_=>0
def sP:Nat→Nat
|0=>0x815ac5a2062dd883c0c500950300480c00c45a056b110316ac5220505162399ac5a0250316a398ad1220d9b062819ac922066b1102b62c440c503c680940e105ac5a825020270244809c08398a418820
|1=>0x110315ac41e062b5880c0ad60d10315ac440cd4b1483c0c5689018358b440c503110315af66101
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x1d51851350e5095045
|5,0=>0x6a56465e65865264c64664063a63462e6286226
|6,0=>0xa479e69779168a78377c77576f6
|7,0=>0xb17ab6
|8,0=>0xb86
|_,_=>0
def wAt:=mkWire dB 25 127 0x7fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x83134141d8313978314318312a134163582141e8310a13415b78216b18314156b143150462143183162d821
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x63001080000000004400010000000
|6,0=>0x192b954a6512793496492
|7,0=>0x383b1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 9
def pmP:Nat→Nat
|0=>0x15f6d97c96421287c3210040180600
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x3030000204000
|6,0=>0x59268471b
|7,0=>0xac
|8,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_124 7 roots_124 ops++addP pm 1 dom_110 6 roots_110 ops++addP pm 2 dom_94 6 roots_94 ops++addP pm 3 dom_118 7 roots_118 ops++addP pm 4 dom_122 7 roots_122 ops++addP pm 5 dom_86 5 roots_86 ops++addP pm 6 dom_62 6 roots_62 ops++addP pm 7 dom_60 4 roots_60 ops++addP pm 8 dom_102 4 roots_102 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_126 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_102 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_124 7 s (0,roots_124.map (·&&&dom_124)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_126 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_124 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_126==dom_126)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_126 gM v ys):RunD true dom_126 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_126 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 13 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 13 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_126 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_159:Lower true dom_159 roots_159 goal_159 8:=lower_slice_b [(0xcccccccc000000000000000000000000cccccccc,16,18)] (by decide +kernel) lowS_157
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_slice_b [(0xcccc0000cccc00000000000000000000cccc0000cccc,32,34)] (by decide +kernel) lowS_173
theorem lowS_183:Lower true dom_183 roots_183 goal_183 9:=lower_slice_b [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_182
namespace S_187
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,18),(2,34),(2,130),(3,11),(3,19),(3,35),(3,131),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,138),(16,17),(16,18),(16,48),(16,144),(24,25),(24,26),(24,56),(24,152),(32,33),(32,34),(32,40),(32,48),(32,160),(128,129),(128,130),(128,136),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffff
def xsM:=roots_187.map (·&&&dom_187)
def gM:=goal_187&&&dom_187
def NN:Nat→Nat
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xe5ea9
|9,0=>0x3dbb0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000f0f0f0f0000000000000000000000000f0f0f0f00000000f0f00000f0f000000000000000000000f0f00000f0f0000f000f000f000f0000000000000000000f000f000f000f00c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x58d11ac688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>7
|9,0=>0x76
|_,_=>0
def wAt:=mkWire dB 7 188 0xfffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa1
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
addP pm 0 dom_186 8 roots_186 ops++addP pm 1 dom_185 8 roots_185 ops++addP pm 2 dom_179 8 roots_179 ops++addP pm 3 dom_171 8 roots_171 ops++addP pm 4 dom_155 7 roots_155 ops++addP pm 5 dom_59 7 roots_59 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_187 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_59 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_186 8 s (0,roots_186.map (·&&&dom_186)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_187 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_186 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffff00000000ffffffff00000000,96),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_187==dom_187)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_187 gM v ys):RunD true dom_187 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_187 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_187 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_235:Lower true dom_235 roots_235 goal_235 10:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c,32,34)] (by decide +kernel) lowS_233
namespace S_243
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(1,129),(2,18),(2,34),(2,130),(3,19),(3,35),(3,67),(3,131),(16,17),(16,18),(16,48),(16,80),(16,144),(32,33),(32,34),(32,48),(32,96),(32,160),(64,65),(64,80),(64,96),(64,192),(66,67),(66,82),(66,98),(66,194),(128,129),(128,130),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffff
def xsM:=roots_243.map (·&&&dom_243)
def gM:=goal_243&&&dom_243
def NN:Nat→Nat
|4=>3
|5=>65
|6=>145
|7=>85
|8=>20
|9=>4
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x5aee324d7f0e772
|5,0=>0xb58d298dbd8494181f3e7b9bb6d9b769c0161fe05c4fa57862560cd5398351fa54e7144d2454bda149289486ee4690446130450c442c7e42aa1421d43e90f3b36e3a78d375af36b1f3452133a563386733723323b930aec2ed562cc612bad62948d2584722e26211ce20ea820ab31ebd01e4b91e1d31e1851ac141aa1518cb216d6e13a680e5db0d53e0ceb20c8f50b9910807a0654805457027ea01fb9013100070b
|6,0=>0x688b966f0c6627b63b5f6359e61de561c66616ab5d3f65b92a5961f58c5e5871654ff95330e52fb952ed04dc444b6ff49849494894647644f4c44eb543d8e434d241dc43fe613f7c63e94d3e8b33dd323d54a3cb3c3c5633b1c637d19379c533b6f3386732083316cb303e52fced2d1df2cd152bac72835628171278202713526c672678525faa23fe621cfa21a7e20fe620fe520acf1fa4e1f7a41e9851e7291e4211da0d1d6eb1d1b0184d516ea816b26153e31462f13e231353b1340d131591309012f1012f0d12d2b12c3212af312361115af1146e0ff0c0fa4d0efc70dc780d9bb0d8eb0ca0f0c5d20c47e0c0b80c0aa0c0a90c0220bb9f0bac80b8e60b6890b5ab0b2cf0b1000af140ad0b0a9f2090220892c07ffe06be505036041e7041550372602b0d027ea01fb901dcd01535014b30138500b6e00ae1009450023c
|6,1=>0xc990fbbf53ac592ac040993a398b7295ffb8be84886e687a557a14179b2e794b0700396fbe96f6646c44b
|7,0=>0xcde28ab9e5880db84755842037a98378cda74a9472b6b6e5176e1be6dce265bc4656e8647f0605385e8e159fff58db257f07550955407052f0e527795152b509474efe04df094db5849449477594378140a7c3ffe33e55b369b835a2c34c34340033125e30c182e2cd2d87f292d827c55275912301e2268821d53200ba1fe771f78c1eb7f1daa61d8221caf61ba141b84a1ae461abf6190f218508170d416ffb1617a1570d15487146da1271f1257e115af106e20fdcb0fa9e0df680cf230bc220bb400993a065fb0569c03dee01d2e018df00041
|8,0=>0xed64aa05469facb853e65fb415e52b5ca6059c5137d4735c4f32ee831f3c2f81c2e68f1a9c911b010d96f0c0150599d02810
|9,0=>0x17c56127920fc8407d2f
|10,0=>0x7a9f6
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000f000f000f000f000f000f000f000f000f000f0000000000000000f000f000f000f000f000f00000000000f000f000f000f000f000f00000000f000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000f000f000f000a000f000f000f000a000f000f000f000a000a000a000a000af000f000f0000000f000f000f0000000a000a000a0000000a000a000a0000f000f000f000f0000000000000000000f000f000f000f0000000000000000f000f000f0000000f000f000f0000000f000f000f0000000f000f000f0000f000f000f000f000f000f000f000f000a000a000a000a000a000a000a000af000f00000000000f000f00000000000f000f00000000000f000f00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000f000f000f000f000f000f000f000f00000000000000000000000000000000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000af000f000f000f000f000f000f000f000f000f00000000000f000f00000000f000a000f000a000f000a000f000a000f000a000f000a000f000a000f000ac000c000c000c000c000c000c000c000c000c000c000c000c000c000c000cf000f000f000f000f000f000f0000000f000f000f000f000a000a000a0000
|0,1=>0xf000f000f000a000f000f000f000af000f000a000a000f000f000a000a000f000f000a000a000f000f000a000a1000100010001000100010001000100010001000100000001000100010000f000f000f000f0003000300030003000f000f000f000f00030003000300003000300030003000300030003000300030003000300000003000300030000f000f000f000f000f000f000f000f000f000f000f0000000f000f000f00005000500050005000100010001000100050005000500050001000100010000300030003000300030003000300030003000300030003000300030003000050005000500050005000500050005000500050005000500050005000500001000100010001000100010001000100010001000100010001000100010000f000f000f000f000c000c000c000c000f000f000f000f000c000c000c000cf000f000f000f000f000f000f000f0000000f0000000f0000000f00000000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e0000f0000000f0000000f0000000f0000000f0000000a0000000f0000000a00000000f000f00000000000f000f00000000000f000a00000000000f000af000f000f0000000f000f000f0000000f000f000f00000000000000000000
|0,2=>0xf000f000f000f0000000000000000000f000f000f000ab000b000b000b000b000b000b000b000b000b000b000a000b000b000b000af000f000f000f000f000f000f000f000f000f000f000f000f000f00000000f000f000f000a000f000f000f000a000f000f000f000a000f000f000f000af000f000f000f000f000f000f000f000f000a000f000a000f000a000f000af000f000f000f000f000f00000000000f0000000f0000000f000000000000f000f000f000f000f000f000c000c000f000c000f000c000f000c000c000cf000f000f000f000f000f000f0000000f000f000f000f000f000f000f000000000000000000000000000000000000f000f000f000f000f000f000f00005000500050005000500050005000500050005000500000005000500050000f000f000f000f000f000f000f000f000f000f000a000a000f000f000a000af000f000f000f000f0000000f0000000f000f000f000f000f0000000f0000f000f000f000c000f000f000f000c000e000e000e000c000e000e000e000cf000a000f000a000f000a000f000a000f000a00000000000f000a00000000f000f000f000f000f000a000f000a000f000f000f000f000f000a000000000000000000000000300030003000300000000000000000003000300030000
|0,3=>0xf000f000f0000000f000f000f0000f000f000f000f0000000000000000000f000f000f000f000f000f000f00000000000000000000f000f000f000f0000000000000000000f000f000f0000f000f000e000e000f000f000e000e000f000c000e000c000f000c000e000cf000f000f000f000f000f000a000a000f000a000f000a000f000a000a000af000f00000000000f000f000f000f000f000f00000000000f000f000f0000f000f000f000f000f000f000f000f000f000f000f000f000f0000000f00000000f0000000f0000000f0000000f0000000f0000000f0000000f000000003000300030003000300030003000300030003000300020003000300030002f000f000f000f000f000f000f000f00000000000f000a00000000000f000af000f000a000a000f000f000a000a000f0000000a0000000f0000000a0000f000f000f000f000f000f000f000f000f000f000f000a000f000f000f000a00000000000000000000f0000000f00000000000000000000000f00000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0000f000f000f000f000f0000000f0000000f000f00000000000f000000000000f000f000f000f000f000a000f000a000f000f000a000a000f000a000a000a
|0,4=>0xf000000000000000f000000000000000f0000000000000000000000000000f000000000000000f000000000000000a000000000000000a000000000000000000000000f000f000000000000000000000000000f000000000000f000f00000000000f000f00000000000f000f00000000000000000000f0000000a0000000f0000000a0000000f0000000a0000000f0000000a0000000000000000f000f000f000f0000000000000000000f0000000f000000000000f000a00000000000f000a00000000000f000a00000000000f000a0000000000000000000000000000000000000000f000f00000000000f0000000000000000000000000000000000000000f0000000f0000000f0000000000000000f000f00000000000f000f00000000000f000000000000000f000000000000f000f00000000000f000f00000000000f000f00000000000f0000000000000000000000000000000000000000000000000000f000f000f000000000000f000f00000000000f000000000000000f000f00000000000f00000000f0000000f0000000f000000000000000f0000000f0000000f000000000000f0000000f0000000f0000000f0000000f000000000000000f00000000f000f000f000f0000000f0000000f000f000f000f000f0000000f00000000
|0,5=>0x50000000500000005000000050000000500000000000000050000000000000000000000000000000000000000f000f000f000f000f000f000000000000f0000000f0000000f0000000f0000000a0000000a0000000a0000000a0000000050005000000000005000500000000000500000000000000050000a000f000a000f000a000f000a000f000a000f000a000a000a000f000a000a0000000000000000000000000000000000000000f000a00000000000f000a500050005000500050005000500050005000500000000000500050000000000000000000000000000000000000000f000f000a000a000f000f000a000af0000000f0000000f000f000f000f000f0000000f0000000f000f000f00000000000000000000f000f000f000f0000000000000000000f000f0000000030000000300000003000300030003000300000003000000030003000300005000500050005000500050005000500050000000500000005000000050000f000f00050005000f000f00050005000f000f00050000000f000f000500003000300010001000300030001000100030003000100000003000300010000000000000000000000000000000000000000f0000000a0000000f0000000af0000000f0000000f0000000f0000000f000f000f000a000f000f000f000a
|0,6=>0xa000a000f000f000a000a000f000f000a000a000f000a000a000a000f000a0000000000000000f000f000f00000000000000000000000f000f000f0000f000f000f000f000f000f000f000f0000000000000000000f000f000f0000
|_,_=>0
def sP:Nat→Nat
|0=>0x4a3498a580d58626287030c10d8f12a420a0a7cf030c4c5284e1c695081c0a624282830e3499214683a4086c79f0e18988141c6a308283a10c044070c10e200a7c38d0c4c51a3c18e8a0a0c38632282870c10c0a0a1c3012e282870c5cb0a0a1c6862a10a1324445051c3408c0608080
|1=>0xc4db0a0e343083a297a50e189854e2438d2a101826a045345e1c3130ad0393242829f0e0421214c83862a10287483421b1e6870608802ac4a1c69314241ab26284b0022829f0e180a614b4386088028e0e182200a9d6870c5422f0eac3130a1c32e4c282895a38695081d5932428289
|2=>0x3664505681c31d14147030c110053418991141539a0e18a845e1c3043614d1e0c20d8a12840840a25d811414f030c74505743831508144837234a84580c10d262838638645054e1c0847029a1f0e1898a1c1c3152e141a402108090e4c90a0abc38608dc2870c64505581c31d1414187
|3=>0x86c505129431310282870c1131d141438d0c4c88a0a1c31509002871a182201415f070c54205500d2062a1029a0e18a841e1c30430282870c04b8a0a2418d2a105070c042000a68703480420512c408414153ad0e1808414f47030c042051238681083c3bc0c10505341c3191414386
|4=>0x2205030ee4315083d61f0e18088141c31509187890eac69314143862a1228f0af838602107850e1898822282895a0c3150815609063408414b438d0211c0a341d20d02107a8121c681083c487040530a0a1c681090c7871a0420b14f438d0c0420f0e1821b3a282870c542140a1c10d
|5=>0x728084147c3820c0440a120c084242828e063431508243ab044c505586838626282871a4e48a0aa04830c0420f1c180848a2829a12781011414f070c0530a0a38331021029f0e1898a0ac83860210505581808422282871a18a848e14483040440a341c686262051a0e90a840a1d106
|6=>0xa68f030c4c505342438202205071a18a84980c301112c5070c4db0a0aa03b90c54205580c68108294071a0420f0e1821c362829a3c180a6141542d0e34084146848e0c0420f64243862a1029a4a1c1011414187043498a5e7838602102a7121c6810829f9e0c4c50564f43860210289
|7=>0xa0c3010844505341c30438282bd0ee43010814186022021114696870c542053438301083d9070c542050ee431509142ba1c180841415a1e0e1898a0a241b91a0420a120dc81083c5094a3408808296874834084500c301083cd1e0404505341c3043a282a71c1c301083c7070c10c0a
|8=>0xad03010844505500c68108283862a11c050e9031508cc2a7341c30108284ad0c542050e18a849e14d0e0c10d8a0aa07071a0420f0e080888c284870c4e70a0ab04871a0440a5e6838602102a50e080921414d07021090a0a381b90c0420f506838602107a50e0868110296870c10d8a
|9=>0xc4c5053478304362829a0e0869314159270e18084141c30440282870c1131b14157871a180840ab17870c04205581d586262829a0e182371414d090e189881424f2b02205050e3430438282894aac084141592d0e18a840a9c7030c0420aa01c68108282c40e18a841e15a1a0e1898a
|10=>0xa0c3a40c0420f581c10d0210505a01c30108282871a1808415304870212a0a0a24386086c5050e1821c14144830212a0a581c30436282b20e1821b14159070c10c0a0ac8386025c5051c0c30436282870c12a8a0a1c68608dc505581c3046e282b40e3431314169870c1290a0ad1607
|11=>0x1414f030c0440a681d5860210505680c386021050534b438602105050e1821b14144d60c0420a0a6838d0c5420a0a1c301b610505641c30108282a5061c686021050772180848a282870c04212141568748180841e1560304180841414d030e0808414141870c0425a14144860212c8a
|12=>0xe34315083c4ad0c0420a0b60386262829f0e08301082829e0e180dd1414f0756180881414d071a1821b1414386021288a0a243b9480420a0a2418202105051c0c31508144870c5420f0a1d10602105054a1d58602105053c0c686021051e0eac6860228289b0180841414f070c0425c
|13=>0xc5420a0a9438d0c0420a1238301083c29a0e0808414144871a5420a0a6870d0c0420a0a68386021130a0b803860210505682438602105050e18084be282b21c1c30108282a53c1c3131414d090e0808414141874834084141c30108e05050e18a849815f870c5420a0b783a40c04205
|14=>0x1414f890e180841414d0e061808414154070c0420f0a1c686021130a0a9c4870c0420a0a1d58d0c4c5050e086811029f8e0c0420a0ab43862a10785582418602105050ee431508147070c042381414386038820a0a1c10109185053c1c686022052c121c68108282a8121c3150814483
|15=>0xe18a841e14386021248a0aa04870c0420a0a941870c0420a0ab038602105050e3430110105070c0420a981438d0c0420f1424386022020a0a1c30108985053438301082829a0e1821b141561a0e18084141591a0e180841414d070c5420a0ab43a40c04205120c6810828487720420f
|16=>0x70c0420a0a1c30110105050e3430108282870c0420f14143862a10505341c30108282bf0e18084141438d0c5420a0a6838d0c0420a0ab0f070c0420a0a783820c045053c1c30110282870c0425414156870c0420f14143b90c0420a0a0c38d0c0420a
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x8500440004
|5,0=>0x17c61766170616a6164615e61586153514e51486142613c61366130612a6124611e61195113610d6108510260fc60f660f060ea60e550df60d960d360cd60c760c160bb60b650b150ab60a5609f60996093608d60876081607c50766070606b5065605f60596053604d60476042503d50376031602b6025601f60196013600d6
|5,1=>0x1826
|6,0=>0x3297322731c6315730e7308630172fb62f472ed72e762e072d972d362cc72c572be72b772b162ab62a4729d7296729062897283627d6276726f72696262725b7254724d7246723f72387231722a7223721d621762107209720361fc71f571ee71e771e161da71d461cd71c761c161bb61b561af61a871a2619b7194718e61886
|6,1=>0x4da74d374cc74c574be74b774b074a974a2749b7494748d7486747f74787472646c6465745e74586452644b7444743e6437743074297422741b7414740d740673ff73f873f173ea73e373dc73d663d063c973c273bb73b473ad73a673a0639a6394638d7386737f73787371736b6365635f63587352634c6345733e733773307
|6,2=>0x54e65486541753a7533752c7525751f65187511750a750374fc74f574ee74e774e16
|7,0=>0x71f771877117709870276fb76f476ed76e676df76d786cf86c876c086b976b186aa76a2869b7694768e66877680767a6673766d6665865e7656864e8647763f86387632662b7624761c8615760d860675fe85f865f085e885e085da65d375cb85c475bd75b585ad85a6759e8596858e8586857f7578757085697562755b75547
|7,1=>0x7b877b177aa77a2879a8793778c7786677e8776876e8767775f87578750774a6743773c7734872e67268
|8,0=>0x8497842783b7833882b8824781d7816780e8807780077fa67f377eb87e387dc77d577ce77c777bf8
|9,0=>0x864785d785678506
|10,0=>0x86b6
|_,_=>0
def wAt:=mkWire dB 99 244 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa1d62110c1d06900a1d0c291c15141d02290a190c15061102110c1d0a1d041d0a0902110c11141534070c0d0a1d54050e191a380a190e2950174a1b34070a250e19022d10240a110a190e19442906080c110e150a1134070e350c150a250c1d0872362934070c0d141d20111e240a290a190e1908190e15162912200e190a11
|1=>0xe116e13680712210e190a1134070c0d0a1d0e19442906080e150c1154111c340e290e190a191a3b0c1502291a290c1d0c150e150a1d0e0902110c11123c0e150a290e190c2950171a78081d0c110e150c150211682b12210e190a1148cd06930e150c29141534070e350c150c0d0a1d02110a790c790e111019081502110c1d
|2=>0x34130e350c150211561f1a110c15022982290c0e0a1d362b34070e350c157e290a260c1d022902290e150e910c29121502290e190a296407123d0e190a296413123d0e190a290e1502290e190a19162912200e190a1106190c290a1d0c1d06900a1d0c290aa20c390a390e29342b0c0d0a1d0c150a290c1d0e296a051a780c15
|3=>0x22902110c1d1a110c150229721f0c3d0a291511123f0e190a290211561f0c210a11022906290a1d0c1d0e1512110e190a195a1b0e3d0a290e350c290c150a2912290e190a2934130a250c1d0c150a290e920c2910240a110a190e19342b0e350c1534070e350c150b090c3a02290e290c1134070e350c150c1d0e2102110a11
|4=>0xc150e0a02110c1112290a290c1d641f1a390a190e2912150e110e190c1168131a790a190e1106900c290a1d0e29021158170c790e11072106920e150c29041d561f0a090c111a3a02290e2908150c110a1d0c1d08150e350c15021102290e350a190c2906080c110e150a111e1914150e15022958170c790e110a290e360a19
|5=>0xe290c150a2934070e350c1534130a250c1d0a390c150c390e290a250c1d0a290229501512290c1d0c11061906110a1d02110c110e150c15682b1a790a19501712290c1d02110a260c1d0e113429342b0e350c150e151a2b0e190a1958170e090c114a1b06110a1d141d02290c150e150c1d0a0902110c11021112110a250c1d
|6=>0xa190e294a190a790e111a290c1d0c150e150c1d0c3d0a290e210c1d0a1106290c290e150c1512290a290a1d0c1d06190c110a1d0e11029a0e350c1550170c390e2964071a390a190619081d0a1d021108150a250e190c150e3e02290a290a1d0c7a0a110e1192150e0a02110c110a910e9102290c29041d0c110e150c150c39
|7=>0xc150a11021112220a110a1112110e19682b34110e350c154a1b3c15081d4a1b061906110a1d0e290e150c3d0a2912290a290a250c1d0c150e210c110a11681f4a1906110e15362934070e350c15342b1a1d1a290a19561f0c210a110229061906290a1d12150a290c1d0e290229123d0e190a290229721f0c3d0a290f351a3b
|8=>0xc1134110e350c150a110a250c1d02110c210e190a11362934070e3510190e210c1d0a110cb506290e15022950170c390e29a2191a7a0a190e1134110e350c15681f1a790a190e110a1912290a1d0c1d02290cb60e3d14151215501712290c1d062902290c1d0a1d123e02290e190a2934070a250c1d0c150c390e290c110e36
|9=>0x34070e350c150e151a130a190e1934070e350c156407123d0e190a296413123d0e190a290e2934070c0d0a1dae070d59062b0a1d6807561d1a1102111a790c150e110f511a130c15021158150c790e1134070c0d0a1d0c110e350c150211641706910e150c2902f6342b0e350c1534130e350c15682b561d1a11041d0a090211
|10=>0xc210a1106090e150c11061906290a1d34070e350c15062b0c1d0a1d0e350c15022982110c0e0a1d123d0e190a2906110e150c15721f0c3d0a294a1b0a790e110c290e3d0a290e090a1d0c1106190e150c11060a0c1106130a1d0c1d0c290e150a290e090a190c11b0190a7a0e110e3e0c150a291a130e190a1934070a250c1d
|11=>0xa290a260c1d02290c290a3a0e2902290c150a2906290c1d0a1d0a7a02110e1158170e090c110c220e110a110c210e110a1134070e350c151a7a0a190e110e190a910c290c110a1d0c1d141d0a1d022902290e190a2906080e150c110c210e210a110e110e150c151a110a190e110e190a7a0e111a7b0a190e110e150a11561d
|12=>0xa390e298c110e360c150e360a190c110a110c150e110c1512110c1d12290c1d022902290a1d0c1d06110c150e150a290c1d0e290e350a190c1102290e190a190e290e350c1534130e350c150b85122b0c1d581512110c1d060b0e150c111a390a190e290a7902110e110a250e190c110e150a190c290cb60e3d14150e3e0229
|13=>0xa290e190a1134130e350c150a250c1d0e2934070e350c1512110a250c1d34290e350c150e350c1502291c150c29141d0e190e150c150c1d0c3d0a29581712110e190c0d0a1d0e2912290e190a2934130e350c15501712290c1d02111a110c150c110c150a110a260c1d0e290e3d02290a2912110a1d0c1d1a290c1502295a1b
|14=>0xa110c15141502290e350c150a260c1d0c1502290e350c150c790e110c11081d0e110a111a130c150e3d0a290c3d14150e150c1502290a290e0a0c1112290c1d06110e150c790e110c150a110e3e0a290c15
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x198006
|5,0=>0x7a5000000000000001dcc7251b540001ac86651890000000000000005d500000000000000000000000005c115d4525000000013904a412084440fd43a50000000000000000000000d900000c542d40a502450000231000022107cc0000694155048c00004080c400000000000000
|5,1=>0
|6,0=>0x5b116845911613578d5a4559152453cd4c3521144450113c44e4d3544c512d44a5125448511d4468d16444910e4429106440ccff43ed0f743cd0ef43ad0e74390ce04374cda33590d2433cccc33210c443010bd32e50b542c50ad42a50a5428509d42650954248c8e4229087320d07f4
|6,1=>0x918e43300023f48f0e3848d4e3238b922a489ce23400022038712184851000084120c48212053808dfe47ecdf837d11f137b51e947951e140001dd47651d54748dce47291c647091be46ecdb746d0db136b51a946951a2367cd9c3661195364518d4625185460517d45e8d7735cd1703
|6,2=>0x27d39e500009d8e7249b926a4999263300025f4970e584954e5149352494
|7,0=>0xcecf383cd4f323cbcf2c3ca4f263c8cf203c74f1a3c5cf143c44f0e3c2cf083c14f023bfcefc3be4ef63bccef03bb4eea3b9cee43b84ede3b6ced83b54ed23b3cecc3b24ec63b10ac13af8ebb3ae0eb53ac8eaf3ab0ea93a98ea33a80e9d3a68e973a54a923a3ce8c3a24e863a0ce803
|7,1=>0x37a3ddcf743dc4f6e3dacf683d94f623d7cf5c3d64f563d4cf503d34f4a3d1cf443d04f3e3
|8,0=>0xe8cba12e7cb9d2e6cb992e5cb952e4cb912e3cb8d2e2cb892e1cb852e0cb812dfcb7d2
|9,0=>0xea07a71e987a51
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 14
def pmP:Nat→Nat
|0=>0x308000420000800000ec00018a000300000588000a1000128000230000440000810001000001a000030800060000098000120000220000410000800000a4000128000210000400000600000600000500000800000c00000800000
|1=>0x49da0092f40124c002494004120008094010000014210028080050000087e0010ec00217800400000604800885001092001bb40027e8004ed0009d80012b4002560004a000091e00121000206800408000802001000001c2000225
|2=>0x409da080bb4100f682010804014a0801001000c020008020092021eb4043768086ec0109da020ab00406200802001000001d3b4038120064ed00c95a01801002a768044fd0089da0112840224e004025008030010020020020030b0
|3=>0x2009da4012f4801f690028c200408400100502f68a02ed1403da2806a4500b48a012d1401da280020443768882ac1003da20073040084080004090dda1000001427682502c0489fa0912b41224e0244980489180910e41220e0224ed
|4=>0x4041308042f1003f6a006ed4009da8012f5002002003c8400788800e11001402000a14001006213b4c40561806ed3005da600a94c014618020c2509da4880c4908021204bd24090a4810009007692004020c9da4192b483242102004
|5=>0x6401dac80315900623200856400cac80135840723044ad602100c0403180276b001ed6003caa8088550036a880a44509da8a03a1108402204ad4408008213b503256a064a540895a8110b50205ea034fd4049fa8093b50124a20209c
|6=>0x304376ce85ed9009590012b194276b280c46409dac8133590256b20489640908c810a590206b20401
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x202
|5,0=>0x800000000223157006a2106000000005b000000000000001d460c0000080d4f05402f0000000000006c004d151a12001d00390b0028300700321300000000
|6,0=>0x103001501b63b032609580400380175ca000170540b6da50359014a01970f8100140c019351bb2a2114089795808e74c2361e1389ab52a8351562761086168420269e221e6808b14241913d37337214c1236f340801038ab7ae3e2143b09f1f0c178c657bbe5c99b3ac7a22cb244a013c2a0d2c6db9110c5327845d015ab229
|6,1=>0x10a6005008230e1c030044010a22ad012b
|7,0=>0x2cbfc62511c98fc79745ba77876ea4a3737161567c9b9aa964cc8b8278c5afbdc05f3a7f944ec4b42c6b696fcd8f49634ba0bc47988892552d26b8a166228318191b2c85c87f2c81962c8d64c3137e7d64475ea7c6
|8,0=>0xc75faac667484c9b909db5552d798367a22e9c60
|9,0=>0x3f9b2e53
|10,0=>0x2c
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_241 9 roots_241 ops++addP pm 1 dom_50 4 roots_50 ops++addP pm 2 dom_227 8 roots_227 ops++addP pm 3 dom_115 8 roots_115 ops++addP pm 4 dom_226 5 roots_226 ops++addP pm 5 dom_178 7 roots_178 ops++addP pm 6 dom_179 8 roots_179 ops++addP pm 7 dom_211 8 roots_211 ops++addP pm 8 dom_163 5 roots_163 ops++addP pm 9 dom_51 5 roots_51 ops++addP pm 10 dom_242 8 roots_242 ops++addP pm 11 dom_162 4 roots_162 ops++addP pm 12 dom_240 7 roots_240 ops++addP pm 13 dom_114 5 roots_114 ops++addP pm 14 dom_210 5 roots_210 ops++addP pm 15 dom_177 7 roots_177 ops++addP pm 16 dom_146 4 roots_146 ops++addP pm 17 dom_195 5 roots_195 ops++addP pm 18 dom_209 7 roots_209 ops++addP pm 19 dom_147 5 roots_147 ops++addP pm 20 dom_83 5 roots_83 ops++addP pm 21 dom_99 5 roots_99 ops++addP pm 22 dom_225 7 roots_225 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_243 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_225 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_241 9 s (0,roots_241.map (·&&&dom_241)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_243 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_241 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xffffffff00000000ffffffff00000000,96),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_243==dom_243)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_243 gM v ys):RunD true dom_243 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_243 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 65 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 65 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 145 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 145 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 85 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 85 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 20 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 20 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 4 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_243 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_243 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_243 roots_243 goal_243 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_243
theorem lowS_243:Lower true dom_243 roots_243 goal_243 11:=S_243.noCircuit
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_slice_b [(0x300030003000300030003000300030003000300030003000300030003000300,1,9)] (by decide +kernel) lowS_241
def isoMvS_95:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_95:Lower true dom_95 roots_95 goal_95 9:=lower_iso_b isoMvS_95 (by decide +kernel) lowS_63
def isoMvS_125:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_125:Lower true dom_125 roots_125 goal_125 10:=lower_iso_b isoMvS_125 (by decide +kernel) lowS_123
def isoMvS_189:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 10:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_123
def isoMvS_190:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_119
def isoMvS_207:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=lower_iso_b isoMvS_207 (by decide +kernel) lowS_175
def isoMvS_215:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_183
def isoMvS_219:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_219:Lower true dom_219 roots_219 goal_219 10:=lower_iso_b isoMvS_219 (by decide +kernel) lowS_123
def isoMvS_221:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 10:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_187
def isoMvS_222:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_119
def isoMvS_231:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_119
def isoMvS_237:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 10:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_235
def isoMvS_238:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_119
def isoMvS_245:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 11:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_243
def isoMvS_246:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_187
def isoMvS_250:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_187
def isoMvS_252:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 10:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_187
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xcccccccccccccccccccccccccccccccc,16,18)] (by decide +kernel) lowS_125
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_slice_b [(0xcccccccccccccccc0000000000000000cccccccccccccccc,16,18)] (by decide +kernel) lowS_189
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,32,34)] (by decide +kernel) lowS_237
theorem lowS_247:Lower true dom_247 roots_247 goal_247 12:=lower_slice_b [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_245
theorem lowS_251:Lower true dom_251 roots_251 goal_251 12:=lower_slice_b [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00,1,9)] (by decide +kernel) lowS_243
namespace S_254
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,130),(4,20),(4,68),(4,132),(6,22),(6,38),(6,70),(6,134),(8,40),(8,72),(8,136),(10,26),(10,42),(10,74),(10,138),(12,28),(12,44),(12,76),(12,140),(14,30),(14,46),(14,78),(14,142),(16,18),(16,20),(16,48),(16,80),(16,144),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,40),(32,48),(32,96),(32,160),(36,38),(36,44),(36,52),(36,100),(36,164),(64,68),(64,72),(64,80),(64,96),(64,192),(66,70),(66,74),(66,82),(66,98),(66,194),(128,130),(128,132),(128,136),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1fffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|4=>15
|5=>111
|6=>289
|7=>257
|8=>94
|9=>19
|10=>3
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xfbbeafb887b77667456b631815471f45ab23dc1539a9438d0836e402b1f92a19b0c33f0ae24
|5,0=>0xfb887a68bd8c8b27ca5b7c8c37b18276aaa745806f1e36eea96cdd16c13a678fd67432673d2670cf65bbd64a665efc65a60c59a1257e1d5658e551d45159b5131a4ec97447bd43c0c4296d3f6de3c8e73c4d03b7443af103987c3869537f0436f7736cfe35dc035b4834eb634a7c31a09311023059a2fae12f7a52ebb42debe2dbbc2cb922aaa32a979292492917628ebf2870d2707c26e5d24ea72376b235a222b2b2249a21ed42165320ede20ebe20609201fd1fa4c1dabe1b95a1af8a1a8341a64c1a123199bf19426190c417e071730a169761636a152771526514793132f81290d115a10ed7b0ebb70ea220e29c0de540d8600cfc60c8770b9440b4840940e0876406ef006cb6065fe0642a046f5043eb00db8
|6,0=>0x20e8220cdf20b6d20364202c72027d1fb741ef3a1eee81e92d1e7331e5ff1e2591dcd51d2701cf201c3fb1c35d1ba9f1a8431a7031a39318da618d2818912188901884c18380180d417ca117b65169d6168aa1558f15349147ab13ca1136e413445130a212bfb1273112105115f311525113d9112d910b7b10b71109fc10890106c3106001055a105551027b0ff850fbf60e5d30dec00dcae0d4330d37a0cf4d0ce1a0ca4c0c5180c3630be4a0ba4e0b7d70b7040b2420b1c10b1a00a8af0a5990a5220a3e20a184096870903a08fd008c8c084e2081f1077ee074240714a071310651c0628c05e08055810553d0530b049ca046c40410603ffc03fba03e4003c2c03b4e0392f038ef037f4037da02f2102af602a01027920274b0251302447023e80235001e9b01c5c0198a0172d01182010e100cf300a710052f0050200283
|6,1=>0x66bce6654f65e7763bb062b705ff1d5fb265e99f5e8265e2ab5cdff57f3557c3855cb8556bd54ac95376c522ef51376503d95027c4e8ce4c93f4c89e4c0264b8094b671492614763a46b3144c3e4445c438cb422794211a4202841c0241589410783f4493f3233e52f3d94c3cf9f3cf3b3c4833bc133ba483b7f23b0d13ac4b3a8d53a7ff3a17439fe039ce339c11399a13934d3874c37a96369263655834fb334a3a34a2d349d63424d3361132f9832e3c32dfd3251d323433136f30d2330b43306432fe602fdfa2f31c2ee3e2ec132e5a92dcfd2d1532d12d2d08a2bc852b8fb2b1492aa262a31729c012964c2925628e7c28c2127925278e32776827762276c026769261ed261a725e5525e4e2554d24e8a249bf2456823e3323623233c02323f231152304522f9422c9722c3922a462227021ac921829217f4212b120ffb
|6,2=>0xd29d8cff68b788bab2bd9d3f09c76c9bcd79bcb4949bb8e3fc8154e8093c803107f40a7f3f97d9d57d0867ce297add37a5587891976ccc7512873b26732476fe9a6f80d6d4896afc76ace969e6e69b0b670cf
|7,0=>0x2aa612a36129a48295e4290142869d2804b27a4b26b1a2691025a94259d0257be2568323ac422ee622da0229c7225b020c9520711202eb1f95c1f6ed1e7bc1e5431e3c01d47b1d3101d2481c9f11b85b1b2cc1af961a5a11a3f7199c619674192e618a5c18a04181231801517824177cc16b051696e1613015bce15bc114fda14ee614c9414b41149061435b13ce212f9112d9212807126cf12472121db11887117401100f1072e0fc160fb310f5810f4880f3290f12f0ef9f0eddf0e71f0e54b0e48a0e2130df440dd800d2eb0d1890cf920c5ba0afa90ac160abce0a22a09ea709682094f90938508d2a08c4b089d30857d0857a0851b07d4a07d20072be071000709806b1e067b70658a05ef105c3e05a6d0505f04f4f0469804437041f602f6b02c660271e0262b0252d0236601a3a0194b011a0009f40092800438000df
|7,1=>0xe43a3b3be5968009469193ee3925398b2ff8608b819c980db4806a08038e7f8657e8947d38e7cdc07c0d87ae1f7a761776927701975de1759e674f3a712a3703dd6fd166fb526e8d06d5da6d5846a7626a6a66a1a969b0b696f9679cf6609864b1a640b3622ac61f8a5f6d35ea0e5d1185cfca57fc857f3557f1e5705c56dfa55cb855c405521952eb152994523a1504fa4f5af4f2da4e5b44e50e4d4d44bd6a4bc9d4b6244a9354a8f64a1164963b482ae47158462f244a6444a58445c5444bc4421d41e8540c18400843f9db3f93e3f68e3f5e53eebf3d5973cfe23cb4d3b7b03b52a396b439621392bd3913538e2a38b51388fd388993877c385703803c37d0137a6c34f0a34d7f33d9a33bc233a7d3375f33509333443333a32d5a329f031bec31aa031415313b23106d30f8430d902fb8f2f9ed2d99a2d4622c63d2c254
|7,2=>0xe4706
|8,0=>0xe5feee43a3e2267b3eb99c6aa949a58f3d98f3808cd0a753ce7507571b646514f640cd62f095ee965b02658afb558ed52c994fbd04d3324d2384cef04c0774bce148efe475f446c594434e42ac03ac723aa783798d36810356e43429d33dee33aa93015e2f8112f40e2f2db2ce252ad1e2a6ba2a5db2a42a29ccd281fa2810825aa725403241f523a2c20dfc20d2b1f42d1e6f81ded81c0b01b1ed1b1ad185fd18169173421617f15eaa158281510b11d65119db1109810980106000fbc50d9e50bf3509e96093240931f0867a084a906b0e05d7c04f690481303200024cf01dde0193000cc200ae600923
|9,0=>0x8472e7ad1e6dd17659455acf656d6954eb64b93a4b4a63545b30a152ab4427cf124fe31c55613ad41018f0fb8d05515
|10,0=>0x8a42580a152224d
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000014141414000000001414141400000000141414140000000014140002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaa800000005555555555555555555555555555555500000000555555550000000055550000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000015555555555555555555555555555555555540001555400015554000155540002aaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaaaaaaaaaaaaaaaaaaaaaaaaaa80005555550055555500555555005555550055555500555555005555550000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00015555555541414141555555554141414155555555414141415555555541414142aaaaaaaaaaaaaaaa2222222222222222aaaaaaaaaaa800022222222222200005555555505050505555555550505050555555555050505055555555505050000aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa01555555555555555511111111111111115555555555555555111111111111111000000002aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002aaa80005555555555555555555555555555555500000000000000000000000000000000
|0,1=>0xaaaaaaaaaaaaaaaaaaaaaaaa88888888aaaaaaaaaaaaaaaaaaaaaaaa888888895555555555555555555511115555111155555555555555555555111155551112aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002aaaaaaa800000000505050505050505050505050505050505050505050505050505050505050000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa015555555555540001555555555554000155555555555400011111111111100002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaaaaaaaaaa80001111111111111111111111111111111111111111111100001111111111110000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000015555555555555554000000000000000155555555555555540000000000000002aaaaaaaaaaaaaaaaaaa80002aaa80002aaaaaaaaaaaaaaaaaaa80002aaa80005555555555555500555555555555550055555555555555005544554455445500aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaa000155555555555555555555555400000001555555555555555555555554000000028282828282828282828282828282828282828282828282828282828282828280000005500000055000000550000005500000055000000550000005500000000
|0,2=>0x22222222222222222222222222222222222222222222222222222222222200015555555555555555555555554141414155555555555555555555555541414142aaaaaaaaaaaaaaaaaaa80002aaa80002aaaaaaaa82828282aaa8000282800005555550055555500555555005555550055555500555555005555550044444400000000aa000000aa000000aa000000aa000000aa000000aa000000aa000000895555555555555554000155540001555555555555555555540001555400000002aaaaaaaaaaa80002aaaaaaaaaaa80002aaaaaaaaaaa80002aaaaaaaaaaa8000111111110101010111111111010101011111111101010101111111110101000000aa00aa000a000a00aa00aa000a000a00aa00aa000a000a00aa00aa000a0000000000000000000000015554000155540000000000000000000155100001551000000000000000000000000000000002aaaaaaaaaaaaaaaaaaaaaaa800000005555000055550000555500005555000055555555555555555555555555550000aaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0000aaaaaaaa0a0a000000000000000000015555555555555554000000000000000155555555555400022222222222222222222222222222222222222222222222222222222222222225555000055550000555500005555000055550000555500005555000055550000
|0,3=>0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00000000000000000000000155540001555400000000000000000001555400000002aaaaaaaa82828282aaaaaaaa82828282aaaaaaaa82828282aaa80002828000055555555555555551111111111111111555555555555555511110000111100000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000a0a00000aaaa0000a0a00001555400015554000155540001555400015554000155540001555400015152aaaaaaaaaaaaaaaaaaaaa802aaaaa802aaaaaaaaaa82aa82aaaaa802aa82a805555555555555555555555555555555555555555555555554444444444444444aaaaaaaaaaaaaaaa8888888888888888aaaaaaaaaaaaaa00888888888888880155555555555555555555555555555555555555554141414155555555414141400002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa800000000000000000000000111111111111111100000000000000001111111111110000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00aaaaaa00aaaaaa00aaaaaa015555555555555555555555555554000155555555555555551111111111100002aaa802aaaaa802aaaaa802aaaaa802aaaaa802aaaaa802aaaaa802aaaaa80001111111100000000111111111111111111111111000000001111111111111100
|0,4=>0xaaaaaaaaaaaaaaaaaaaaaa00aaaaaa00aaaaaaaaaaaaaaaaaaaaaa00aaaaaa000000000155555554000000015555555400000001555554000000000155555402aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000000000000002aaaaaaaaaaa8000000000000000000011111111111111110000000000005555111111111111000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa0000000000000000000000000000000000000001555555555555554155555555555555402828282828282828282828282828282828282828282828282828282028282825555555550505050555555555050505055555555505050505555550050505000aaaaaaaaaaaaaaaaaaaa2222aaaa2222aaaaaaaaaaaaaaaaaaaa2222aaaa00015555555555555554444444444444000155555555555555544444444444440002aaaaaaaaaaaa8282aaaaaaaaaaaa8282aaaaaaaaaaaa8282aaaaaaaaaaaa82855555555555555550000000055555555555555555555555500000000555500000a0a0a0a0a0a0a0a000000000a0a0a0a0a0a0a0a0a0a0a0a000000000a0a000155555555555555555555111155551111555555555151515155551111515111102828282828282828282828282828282828282828282828282828000028280000000000000000000000000000000000000000000555555550000000055550000
|0,5=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a0a0a00000000000000000000155540001555400000000000000000001555400014142aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002aaaaaa2000000000000000000000000000000000000000055555555555555555555000055550000aaaa00aaaaaa00aaaaaa00aaaaaa0000aaaa00aaaaaa00aaaaaa00aaaaaa00015555555555555555555555555555555555555555555555555555555511111110000002a8000002a8000002a8000002a8000002a800000280000002a80000028111111001111110011111111111111111111110011111100111111111111110000000000aaaaaaaa00000000aaaaaaaa00000000aaaa000000000000aaaa00015555555555555554444444444444444555555555555555544444444444440000282828282828282808080808080808082828282828282828080808080808000555555555555555555555555555555550000555500005555000055550000000000aa00aa00aa00aa00aa00aa00aa00aa000000aa000000aa000000aa000000015555555555555554000000000000000155555555555555400000000000000002aaaaaaa800000002aaaaaaa800000002aaaaaaaaaaaaaaaaaaaaaaaaaaa80001111111111111111111111111111111100000000000000001111111111110000
|0,6=>0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00a000a155540155555401555554015555540155555401555554015555540155555401400002aaa80002aaa80002aaa80002aaa80002aaa80002aa800002aaa80002aa8555555555555550055555555555555005555555555555500555555555555550000aa00aa00aa00aa000000aa000000aa00aa00aa00aa00aa000000aa00000001555555555555555555555555555555540000000000000000444444444444000000000000282828280000000028282828000000002828282800000000000000055555555555555505555555555555550555555555555555055555555555555500000000000000000aaaaaaaaaaaaaaa00000000000000000aaaaaaaaaaaaaaa00000000014141414000000001414141400000000141400000000000014140002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8282aaaaaaaaaaaa8285555555555555555000000550000005555555555555555550000005500000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00aaaaaa00aaaaaa00aaaaaa00015555555555555554000000000000000155555555555555555555555555540002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa802aaaaaaaaaaaaa801111111111111111111111111111111111111111111111001111111111111100
|0,7=>0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa008800000154000001540000015400000000000001540000015400000154000000000002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002222000022220000000055555555000000005555555500000000555555550000000044444444aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa000000000000000000000000000000000000000000000000000155555555555400015555555555540002aaaaaaa80002aaaaaaaaaaa80002aaaaaaaaaaa80002aaaaaaaaaaa800000000055005500000055005500550000005500550055000000550055005500000000aaaaaaaaaaaaaaaaaaaaaaaaa0a0a0a0aaaaaaa0aaaaaaa0aaaaaaa0a0a0a0a00000000000000001555555555555555400000000000000015554000155540002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2222aaaa2225555555555555555000000000000000055555555555555551111111111110000000000aa000000aa000000aa000000aa000000aa000000aa000000000000000155540155555401555554015555540155555401555554015555540001555400000000000000000000888888888888888800000000000000008888888800000005555555555555555555555555454545455555555555555555555555554545454
|0,8=>0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000000000015554000155555555555400015555555555540001555555555554000155540002aaaaaaaaaaa802aaaaaaaaaaaaa802aaaaaaaaaaaaa802aaaaaaaaaaaaa800000000000000000005555555555555555000000000000000055555500555555000000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaa0a15555555400001415555555540000141555555554000014155555555400000002aaaaaaaaaaaaaaa800000002aaaaaaaaaaaaaaaaaaaaaaa800000002aaaaa8055550000555505055555000055550505555500005555050555550000555500000000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaa0000000044444444444444444444444444444444444444444444444044444444444444400000000000000000888888888888888800000000000000008888888888888085555555555555500555555555555550055555555555555005500550055005500aaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00a0aaaa00aaaaaa00a0000000000000000000000001555555540000000000000000000000015554000000000000000000000000000000000002aaaaaaaaaaaaaaa88888888888880000000555500005555000055550000555500005555000000000000555500000000
|0,9=>0xaaaaaaaa000000002222222200000000aaaaaaaa00000000222200000000000000000000000000000000000155555555555555555555555551515152aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa22aaaaaa25555555555555555555555555555550055555555555555555555555555555500aaaaaaaaaaaaaaaaaaaaaaaaaaaa8888aaaaaaaaaaaaaaaaaaaaaaaaaaaa88880000000000000000000000000000000155555555555555555555555555554140000000000000000000000000000000000000000000000002aaaaaaaaaaa80005555555555555555555555550000000055550000555500005555000000000000aaaaaaaaaaaaaaaaaaaaaaaa88888888aaaa8888aaaa8888aaaa8888888888881414001414140014141400141414001414140014141400141414000014140002aaaaaaaaaaaaaaaaaaaaaa22aaaaaa22aaaaaaaaaaaaaaaaaaaaaa22aaaaaa200000000050505050000000005050000000000000505050500000000050500000a0a000a0a0a000a0a0a000a0a0a000a0a0a000a0a0a000a0a0a000a0a0a00015555555555555555555400015554000155555554000000015554000000000002aaaaaaaaaaaaaaaaaaaa8282aaaa8282aaaaaaaa82828282aaaa828282828285555555555555555555555555555505055555555555555555555555555555050
|0,10=>0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaa00000000000000000155555555555400000000000000000001555555555554000000000002aaaaaaa800000002aaaaaa2000000002aaaaaaa800000002aaaaaa2555555550000000055555555555555555555555500000000555555555555000022222222000000002222222222222222222222220000000022222222222200015555555400015555555555540001555555555554000155555555555400011112aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa802aaaaa8000000000000000000000000000000000000000000000000011111111111100000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa00000000000000015555555541414141555555555555555555555555414141415555555555554142aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8000005555000055550000555500000000000055550000555500005555000000000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aa0155555555555555555555555555540001555554015555540155555401555400000002aaa80002aaa80002aaa80002a2a00002aaa80002aaa80002aaa80002a2a0505050505050505050505050505050505050505050505050505040405050404
|0,11=>0x5555000055550000555500000000000000aa000000aa000000aa000000aa000000aa00000000000000aa000000001414141414141414141414141414141414141414141414141414140014141402aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8000000002828282800000000282800000000000555555550000000055550000000000005555555500000000555500000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000000000a0a0a0a000000000a0a00015555555541414141555555554141414155555555555555555555555555554142aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa82aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000000000000000000000550000005500000000000000000000005500000000aaaaaaaaaaaaaaaaaaaaaaaaaa00aa00aaaaaa00aaaaaa00aaaaaa00aa00aa000000000000015554000000000001555400000000000155540000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa82aaaaaaaaaaaaaa81111111111111111111111111111111111111111111110101111111111111010
|_,_=>0
def sP:Nat→Nat
|0=>0x60b0313020024060302000623151b0200070603021700220603132100191f1e1b1117071d03021c00120a1b11021a190603181716070f06030207060302000703020e000d151411020f060313020612080a020f03110201060b0a02100f060d03020903020e00060d03020c060b080a02090608020007060305000403020100
|1=>0x2000d201b110232090f06030200060b312002001d03151130002906032f16002e1d0a2d1b211203110201001d2c15110200060b1e0a1b02041d031502001d1511022b000706201b0500060315212a002906151b05001d0a1102101709060313020004201b0201001d15110210001d20282716001d0311022600070603150200
|2=>0x3152117071d110210001d03153d0200070603181600090f060a1b02290d1b11023c060b082002001b110235010029061b023b1706121b023a00061d39202117092206032100191203113802191f151b113819061e1b3816060d0a1b02351d0320113717360612030a02290b081102000f1d1b110235191d0311341709063303
|3=>0xd0a1b1102460b201b020e0045122d1b210009203d1b0200060b200210001d15141102001d03024443000b203d1b0200060d08152100060d0313022906421b160009060b0a1b021d0302410100090620023f0009060a1b38021d0315020e00060d201b023c060d03024000060b20023f00060315023e00120313210e000f06
|4=>0x201b02290b0a11024b1d030a110517060b0a1b02354a19060321160f0603211716291211021000191d031105171d0315024900220603341600060a1b023500120348202100091d030241004536120a1b02060d031315020f06120302000f060d201b0209201b020e00060d03130217060d201b020c2e060d0313211d03471102
|5=>0x3416001d201b56551600091d03211c1600290d131b2141161d2011025453000706030200070906030200070603130200290603215200510d031102000f060b201b02060b330320024d0603501600070311020100294f11214e170f060302004d06032117161d201b114c00070f1d0311020d15203d1b02071d031102000f0613
|6=>0x201b215e001906201b1817165d032011021600292e065c1b21001d2011024b35000f06150a1b21161d035b11211700290b1e1b110200295a03110216001d0a1b11021a16290a1b11020100290603215916001d2021414b1600191d03112f160045060d151b02001d032011581600290d4f031121171d1e1b110257172906201b
|7=>0x61d151b21661707060313211600071d201b021c0065061d201b02171d20211c3f16001d0320110264001d201b181c16001d201102101700061d1e0a1b02171d036311211600621d03112117001d150a1b110500290b131b110200121d0815112100060d0320601600290311214e1716060b030a211716295f06151b21000612
|8=>0x1b02001d030a112f16001f0d0315110200061d03216d16006c0d4f20112117061d33031502002406201b020007221d03112100060b1e201b02000620212a6b16001d201b11026a1745361d151b02000f29060a1b2116220613201b2100060d4f032021171d13112110160029060a1b21166967061d03152100071d030a110200
|9=>0x613201b02000612202d1b2100682e1d03152100290603181600091d0311181600091d0811211600290620216f1600290d0a1b214116041d0313211600070615201b0200295a0a1b1102166c1d33151102002e1d201b213b17061203130a2100061d6e20211600071906032116002e1d202d1b210068190603211600060b1320
|10=>0x10001912031102001d201b11027400041d15201b020068061203152100290620213f16001912151b1118000612201b214400060d0320211673060d201b023500121d037211210007091d031102000615201b212a000612201b213b1729151b110271000b1d080a112116041d201b02170070061d0315020019060d0302160009
|11=>0x13112101163606120a201b020d1d0311210c16191d201b11341706792021781600293606151b2117090f06201b02001d151b113802571d7703202116002906201b2f16006c0d037611211629124f3311210036061d030a02161f0d03201138161d0a1121101600061275201b020012201b11020100120d03131121121d151121
|12=>0x1b11381d031511027c0029201b210e1600192206151b2100652e1d151b2100291f1e1b111700120a1b11217b452e1d131b21001d03133d2116007a1203110200292e360a1b21160d201b110201170f0d1d03112116061d1b023a1600293d1b211600061d150a1b38021906150a1b020022060b201b2100191d03113802160d03
|13=>0xa201b1134170706201b18160009060b201b02002906151b1816001213203d1b2100450612131b21001f201b113880161d2011027f16000906201b38020045061d5c1b02001d030a11217e1709060a1b02001d203d1b021700092206201b2100120d0313112117091d11211016001912201b113802060d201b027d16121d1e0a
|14=>0x4000192912031102000612201b028200060d201b0240000615201b023e001213201b210e001d0321010e1600293d1b211716001d031302410009191d03112117703612201b02006c0d03131121160d1d201b1105170d0311210116001d15203d1b02004a060d03202116120d03131511211d201b110281001d0313210e16001d
|15=>0x290d1e1b110217121d03132141002906881b2116000906150a1b020029123303110200060d13201b021f1d030a110217068733032021161906030a1816001d311121351600291d1b11023500061d0320861600061d201b851600091d330311211707203d1b211600122084112100061d0383211600090f1d031121171d031102
|16=>0x1b115634002e060d13201b21061233032002001d038e110200121d080a112116295f060a1b211629221203112100060a1b213517168d1d0311211600061d038c1521005106201b02000687030a21168b0612201b2100060b1220024b00068a201b211600060b0d150a1b2107201b210e1600290311218916000623201b021600
|17=>0x1600060b12032002001d0320113016002e361d13201b211d2c2011021600060d1315201b020612030a02000b1d201b0241002912151b2141001d910a1b211690061d031502000f0612201b020019061e1b021600060d13201b021709120d031121171d0a2011024b17290311027116006c1d8c151121000d1d03130a11021d20
|18=>0x161d201b211c1600990603211716001d201b11341600060d15201b3802060d150a1b021906032117161d1511211017000d97201b1116060b120a201b020d1d037211211670060d201b0217090612030200192206032116001d0372219616000f1d201b1102171d9533201102170f1d0313112116061d0a1b2194171d2021934b
|19=>0x200061d030a02170f06201b0200090d03112117061d035c02001d080a112116070f1d201b1102071d201b110200071d031102001d9d03151102001d201b110256002e361d150a1b21611d4f201121179c1d030a112117290603211673004d1d201b1102179b1d0a1b1138160f0b1d03112116060d4f332021169a060d201b21
|20=>0x19203d1b211600452e1d5c1b21000f1d1b112135161d03a21121160007060321171600061d0302a1160090061d0a1b21170f0615201b02001d132011023f001d150a1b02a000090d031511211709060302000612201b023500190b1d03110200290d0311380216071d0315110200060b032002001d201b11029f009e0612201b
|21=>0x2100a51d032011211600061d1315201b02001f1d030a110216007a06151b2116000d1d0a1b11213516061d201b215e16001d3303201121168f06124f032021000f2906201b21160007191d201b11020019291d151b110200090d031511020006201b0254001d031121a3160006201b0235001f1d1e0a1b11171b112135011600
|22=>0x612201b21a70009060315211600621d201b112117000612201b21661600292e06151b21001912150a1b112100060b0a201b211716a6061d201b2116001d030a111816000d1d03761121162906131b21171600295a201b11021600191d201b112f1600290d1e1b110216001d1e130a1b110200091d201b211c16006c124f2011
|23=>0x1b1121000d20981b112116061d03130a211600aa1d201b11021600061220214b1600071d0a201b1102000b1d151b11213500090f1d0a1b112116090b1d03112116001d0a2011213f16001da903151121170009121d0a1b1121170b121d150a1b11211d030a1121168f0b1d0820112116001d201b1102a816001d032011601600
|24=>0x30a11210036061d0320021600061d201b213b1716071906201b2116000d1d031121401600192906151b2116001d031511213e160070061d201b021700061d202d1b2116000b1d201b111816001d0a201b112f16001f0d15201b11020009290603211600291d151b1138020007221d201b11210009120d031121160029221d15
|25=>0xac1d201b11ab1600090b1d0a1b11211607091d201b110200191d03110216000b1d201b112f16000d1d0a2011214b16091d201b1118160045061d761b21160068061d031521160019291d03111816000d1d0320110217120d201b111816001d97201b111600191d151b11181600041d13201b211600121d031121821600121d4f
|26=>0x101600120d13201b11211d1e201b11028f001d031511214e1600290d03112117161912201b110200ae06032116001d03201102ad160012201b11217b001d038c15112100061d0a1b21941600360612201b02001d201b11023500291d4f3311211600061d75201b021600061d15201b3802000d1d0313112116061d150a1b0200
|27=>0x1d03112116000f0d1d201b112116191d201b113802160d13201b1121011622060d201b2116000d1d201b11210c166c1d952011021600061d4f33202116001f0d201b1138167a1d0311021600061d9503200216009a061d201b2116001d0a201b11561600511d03112116001d9533201102160036061d0a201b02160b1d201121
|28=>0x2116000d201b1121011600b1061d03202116001f1d032011021700290603021600061d201b210e16001d030a11380216121d201b211c1600791d201b110200121d312011211600061d0a201bb01600120d13201b1121170d1d0313151121161d131b11213516001d03201121af160045061d131b2116007a12201b1102000f12
|29=>0x2a0029870a1b1121169c1d030a112116006c1d0315112117001d0a201b11051600121d082011211600295f06201b211600120d03151121001f1d031511020006201b21351716000d1d3303151121161d201b1102400006870320211600091d03112117001d201b21010e16001d13201b024100060b0d15201b21002979201b11
|30=>0x1d0311380216000b1d0315112117005f061d201b0217001d0a201b210e1600121d2011213f16006c0d030a11211629221d03112116001d035b112116001d13201b02411700061d201b216617161f1d0a201b110217611d4f20112116001db320112116000b121d030a11211619060a201b1816001d201b115016001d201b1102
|31=>0x201b02001d031121821600061d030a02160009120d201b112117071d201b21411600091d1b1121351600291d151b2141160029201b1102711600091d031511211700251d4f0320112100120d150a1b11211d201b11025400b5061d03202116001d03201121b4160007121d201b1102001f0d032011021600091d0a1b11211729
|32=>0xa110217060d130a201b2116060d15201b02000f1d13201b112116991d201b11021700060b12201b020019060d03211600041d201b214116001d035c1102000b0d1d0320110200191d201b110217700612201b020006120a201b02001f0d0a201b110216291d0a1b11380216121d20112110160009291d031121170090061d15
|33=>0x1b210012201b1121011700b6061d201b2116001d201b211c1600121d030a1121170d1d1e201b1138161d3120112116001d201b113416009b1d201b113816000f121d201b1121170f1d03112116000b1d0a2011214b165f061d20216f160090061d0a1b2116001d032011027c1600192206201b211600060d201b219416001d03
|34=>0x21000623201b2116001f1d1e0a1b111600093606201b211600061d201b21b916001d201b11ab1600ae0d0a1b112116071d201b1102006c1d8c2011211600191d13201b1102001912151b1121001d201b210cb7160019120a201b1121171d201b21410e16001d082011211600191d030a11211716ae0d03112116002e361d1520
|35=>0x7291d201b1102000906201b0200290b131b112116001d2011214b3516001d33032021ba1600091d13201b110200060b201b0200290d0a1b1102160b1d13201b110200291213151b1121000b1d1e201b110200061d032021591600071d201b110217009e061d201b021600061d032021166900290b201b1102007a12151b11
|36=>0x213e160009291d201b1102006c1d4f2011211600060b201b21171600090f1d201b11211600070f1d201b112116071d201b112116005106201b2116002912031102001f1d1e201b1117001d33031511211712201b1121011600291d130a1b110200090f1d201b110200071d201b211c160065061d201b2117161d032011216416
|37=>0x160065061d201b21160009120d201b11211600061d130a201b211600090b1d201b11211600121d032011020029060a1b211600091d0a1b112116001d0a201b111816000d1d20761b1121161d032011214e1600061d201b2116a7001f1d0a201b11021600191d150a1b112116001d03201121bb160006201b21a416001d201b11
|38=>0x16001d030a110216000d1d330320112116290d201b112117165f36061d201b2116006c1d0320110216000d1d13201b1121160d1d201b110217191d201b110216001d201b1121167b001d201b2141160036061d201b02160019291d201b111816000d1d201b11214016001d15201b11213e160029120311211600092906201b21
|39=>0x1b110217001d201b1121bc16000b121d032011211600ae1d0a1b112116002987201b11211600251d15201b112100291d1e1b110216000d1d1315201b112116121d030a112116001d15201b214116000f121d201b11211600221d201b112116000d1d13201b112117167a1d201b11021600121d33032011211600511d201b1121
|40=>0x1d130a201b2141160009291d201b1121170070061d201b021600061d0a201b021600291d0a1b1102160029221d201b112116000b1d201b11213516001da9032011211716000687201b21160019120a201b11211600120d15201b1121001f1d15201b1102000b1d15201b1121006c0d0320112116000d1d0315112116001f1d20
|41=>0x160045361d201b211600ac1d201b112116001d33031511211600091d03112116009c121d0320112116001d201b1121011716001d031315112116000f1d201b112116001d201b11210c16001d032011217e160019060d201b2116001d03151102000b1d2011214b16001d5c201b110200070d1d201b112116001d031311211600
|42=>0xd1d0320112116002912201b112116001d1e201b11021600121d201b1102001d201b1121168f002912151b112100071d201b11211600191d13201b1121160007121d201b11211600061d0320021600120d201b11211707091d201b112116009c1d0320112116000d1d032011211716071d13201b11211600291d13151b1121
|43=>0x1d201b110216000d1d201b11211600121d0320112116001d0320110216001d201b1121a41600091d201b112116007a1d201b112116001d13201b1121171600121d201b112117001d13201b112116001d201b1102170009121d201b112116000b121d201b11211600121d0a201b112116000d1d0a201b1121161d201b11380216
|44=>0x1d201b11211600121d201b11211600
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x1194082a03c501ba80c9405aa0285011a80794032a0145007a8029400aa0005
|5,0=>0xe2286f98370c1b260d6306998340c19a60ca306398310c18260be305d982e0c16a60b23057982b0c15260a6305198280c13a609a304b98250c122608e304598220c10a6082303f981f0c0f260763039981c0c0da606a303398190c0c2605e302d98160c0aa6052302798130c0926046302198100c07a603aa81bd80d2c063602eb015d80a2c04b6
|5,1=>0xb7145acc2d0616530b11857cc2b8615930ab1854cc2a1514db0a55851ec2896141b09f584eec2716135b099584bec2596129b0935848ec241611db08d5845ec2296111b0875842ec2116105b081583fec1f960f9b07b583cec1e160edb0755839ec1c96
|6,0=>0x24cb9249c916e484723eb91d9c8dee4687230b9169c8a8c44d7223390fdc870e43172153908dc838e41572073901dc800e3f971f938fadc7c8e3dd71eb38f3dc790e3c171dd38ecdc758e3a571cf38e5dc720e38971c138dedc6e8e36d71b338d7dc6b0e35171a538d0dc678e335719738c9dc640e319718938c2dc608e2fd717b38bbdc5d0e2e17
|6,1=>0x32a31935cc8ce640631cb98c9cc56e624730f3185dcc20e6097301397edcbe8e5ed72f33977dcbb0e5d172e53970dcb78e5b572d73969dcb40e59972c93962dcb0ac57e72bc315c5cad4e56372ae39555ca9ce54772a0394e5ca64e52b729239475ca2ce50f728439405c9f4e4f372763939989bee4d87268b9329c986e4bc725ab92b9c94ee4a07
|6,2=>0x4073a01dd000e7f973f939fadcfc8e7dd73ebb1f41cf92e7c273ddb9ed1cf5ae7a673cfb9e61cf24c78b73c239df98eeee77073b4b9d89ceb6e75473a6b9d1d8e80e739739939cadce48e71d738b39c3dce10e701737d39bcdcdd8e6e5736f39b5dcda0e6c9736139aedcd68e6ae6353b9a81cd32e6927345b9a11ccfae6767337b99a1ccc2e65a7
|6,3=>0x4e2ba6f9d36ee9b074d4ba689d336e99474c6ba619d2fee97874b8ba5a9d2c6e95d64abb2541d294c943749e3a4d5d25ec9287490ba469d226e90c7482ba3f9d1eee8f07474ba389d1b6e8d564673a31dd182c8ba7459ba2b1d14ae89e744bba241d112e882743dba1d1d0dae86764303a165d0a4e84b74223a0f5d06ec83164153a08dd038e8157
|6,4=>0xaa1754db2a51d51cca8775403a9e5d4e4ea6b75323a975d4acea4f75243a905d474ea3375172a89dd440ea1975093a831940ae9fe74fc327c993d8c9e664f032765d3a4e9cc6
|7,0=>0x649c322e19070c7b8639c31ae18c70c5b8629c312e18870c3b8619c30ae18470c1c760a4303218090bfc85fabafb617cb0bde75eb42f3a178d0bbe85db42eba174d0b9e85cbbae3e170f0b8075bcbadc9d6d50b6285adbad4e16970b43859e3acd5d65b0b25858ec2c56161b0b05857f3abda15dd0ae6856fbab5e159f0ac785603aae215610aa88
|7,1=>0x73ec39d61cdb0e65872fb395e1ca0ee488720bb8e61c630e298710c38661c230e0987013b7ea1be50dea86f14376a1ba50dca86e1436eddb68edac86d2436721b2aed8d86c2c35f61aeced6e86b34357ddab0ed5266a54350dda78ed348696bb499da3d0d1686874341dda00ecf88678433a219c2ecd98668c332619830cb98658c32a9d9450c9b7
|7,2=>0x832c417620acf04f7823c4105a07310327815bc091e03910148806440121ff90ff577f73bf9a1fbd0fd687e743f1a1f7d0fb687d7bbea1df410f9887c843e221f02ef7987b8c3da61ec30f5987a93bd2a1e86ef3b8799c3cae1e470f1c778a43c321e0aeefe777bbbbbe1dcf0edf876bc3b3e1d90eec1775cc3ac61d54eea3774e3ba521d1aee858
|7,3=>0x925c4911e47cd2368917bc89e243f12178907c481e23ff11f788f8b47a623c311d988e8c472da388f1bc88da446b22349119c88ca44632230af17e78bbbc5be22cf115f88ac3c545e294f142889d444cde2571123888dc4451e2191105787ec43d621db10e6786fbc35e21a0f0c97860c42e62164f0aa88514426a2125108a8841441f1a0e9106d7
|7,4=>0x12538
|8,0=>0xa2f4515a289b34449a1dcd0d1e85734238a0dc504e2817140389fdc4fce27d533e289ed44f4a279513c199dcc4ec6275133a089cbcce3e270d337e89bbbcdbe26cf135e99ab44d3a268ef33f899bc4cc1e651131f998b4cc36660cf2fe897b44bb665c932db996a3cb35e58b12bd895ac4ab6254b129c9949cca2e2508f27c893a449b224c9125b9
|8,1=>0x2aa2f5498aa04d4de6a60f5297a904d4622a2115079a7f4d3da29dd14e68a6fbd35a699b34c58a5ec52d6295b14a58a4fb525e2920f4879a403d1de68dd34668
|9,0=>0x57a62bc4f5da8ae94572a2b8335b98ad8c56a9eb4335989ac7cd61e2aff15778ab7c559e2ac0f5588
|10,0=>0x58022bf2f5f18
|11,0=>0x16087
|_,_=>0
def wAt:=mkWire dB 189 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1d11484591d1645885200641801111d45875201b458850900c4881111d458751536080591220448011d11484591d164806d0613054012116480590b03034591d11484591d004a4011d20474551621474451b2045881201b480491d11484591d1645401201b484592016424012116454751b2045881162144475171d45801201b480951d11458851200c58751d0a48001
|1=>0x200041c471916434811d004588520004800916214447516214745d1720458011d11584870d0347401201b4b8011606444751500c58810900c48011d1646c81293800801201d484591d13880591d00484591d0042877200044c471500458811d114806d1916428752000484591d11424011d154806d211648059131d42859201b48459200043459162147445201b48049
|2=>0xa16480012116454351d00480591f00408752116458851d0340c011b2045881111d4806d1619428752000444751536080590600444751d0a40c19201b48001111d4744516214745d16004806d1620474091d00484591d00458011621474451b2045881202547445162144803161d4745d162145801111d474451d005a05b06034806d120a480011d164806d131d42859
|3=>0x20048459201b474011500474592016480351b20474592116474590603474451b20458811921ca4011d204482a2000458850b20c58351d0044475090047455201b484592016480da1b20418091d11484592016434811d1146c811d00484591500484592016454d8201641801111d418590603474451b20464872900474451b2047481122042c0c201b448011d0044c47
|4=>0x203887445200240801211647459161982819200044475160047409200248459200045ca4160048075161d45c81160044c18201b42859200047459162146c811d20480011d2044c18172045801111d40801111d480012116484591d0a4806d1d1388459200041801111d458750d20474010900c80491d11484591d164742a20004740d160a8806d16214806d1b2047409
|5=>0xa1648001061307481172044475201b484591311c540120164a401291646c811d20474590602418011621444751500480590613054012116480596800c7401150046c811620464591921ca401201d448811200474452116474591500480592916480751d11484591621454031d154447520164800121164184c162145c81160047401201b4805d160047459290048075
|6=>0x61745801111d4802e211657075111d454031620444750d16c806d1d00480010b1bc48011d11484591d16474450d1647401201644c1b131d45c811600474011d15444752016480012116474811d16458851b2047401162145c81160044475200045885160046c81160d874451921c6ded172905801201d458750900c806d2116454371d00480591d16458851b2047481
|7=>0x300458851b204806d1200474452116474590a16480011d1147459201b484592000444751d1644c47150045881200044649150d0740116204806d2116454192016458850900c4881111d45875111d474011d0045885160044475122047401160046c81160a45885201b474012000428592000474451d16458851b204806d8f204745e160048459200042c0c201b44801
|8=>0x21164cc09211640c011b204588120005b001031d46c814f1d4580d201b45c0f1b20458012917c80751e1d480092116444751b204a45f1d20480591d1147401111d47401201648001211648035201b474451600474011d0048661120a08001161d480011200474452116474590602474451621474011600484591b2044881111d45875201b458660a1d48001111d4080d
|9=>0x201b480491d11484591d1642c83120047445211647459201b48459200d434591d00474811b204806d2116454351d00480590d16474452116474011b20474597000c18091d114845916004806d2116480010900c80491d11484591d164a4591600474811d0046c8116214806d111d454032016480010b03034591d0046c810d40454371d0048059201b464590a1d48001
|10=>0x2900c7481200b834591d00454da201641801171dc5801161d4580d1d1146c810900ca459111d480751916434811d0045885162047481162147401151d46c811620474452116690011220c74591d114802e0d16474012116480010a1d4184c0a16444750b2044475171d458011b204806d7020c1809150648059111d444750900c5475211648059151d47401162046c81
|11=>0x16994a45f1600480750a06c4475200045875162045819111d480751d1647429200048001171d45801111d419d90a16c8001111d464871d0a480011b204582a201b47401200047481172045801111d434091d004845916194a401201d474010220428592000484591d164740d160346c810b03434591d0046c81150047445211648059201b408752000484591d1148059
|12=>0x2900474811d0044828200045875201b428592000444757d1d480e2020048459111d42c6f1200458751619428752000484590b20c48011d1642403291647481201b44801122047459071bc48291d16480591703458011b20480011220474592000448011d1645c77201b45801200042c0c0d16474016121c340d1d0046c811720c5875160044475111d454751b2045881
|13=>0x1d4144c47150048059120a8806d200040c59201b480011d1645885201b44475203681801111d458650a1d48001111d46c81150dc5881111d4a4011620474810206458851600444751536080590600444751921c80350d16474010721c48291d16458811d024740121164806d291644475201d47481020048459201641c5b120a480011d16448811d16474011b2045866
|14=>0x30046c811d20444751d1140801211648059160a4806d1d0048001111d480592000484591d764285b2000480011200448811d16484590900448811d164806d0a1d48001211641c87200b448011d16480010b1bc34591d004285b20004180d1d1146c8116204806d1921ca401201d4806d162147401160046487200d47401161d48661120a08001161d46487290047481
|15=>0xa1d47571201b45403201640c090300458851b2041801111d48001211642c0f0d16474011d00454011d164805902204745e1600484591d3380c011b20458811600474811d0046c811d16428752000484591b204a45b111d48075951dc0c09201b48459172905801201d458753316c0c011b20458811506c7445162048459060044475161d4802e0d164740121164580d
|16=>0x1d00454011b20458810b20c745d172045801a91dc5c0d160046c811720458011621474592900c80750900c806d1220474590700c54351d00480590d20474011d138285920004645b200d47401111d50001150dc7401201640c091d03458851b2044475160340c011b20474011d024080121164806d21164a403201d40c091d114806d211664003150648059181646487
|17=>0x150dc74012016458361d11474011b20454751620458011b204744e150048059211644c471500480590d16474451d0048059b21d4a45e160048075071dc54351d0048059360341801201b444751d0245885160046c81201d45885201b4447502004806d2000484590711c4829200069c7520178580121164812d0b1bc48016521c28192000444751d004805d160047459
|18=>0x331d40c011b2046e61120a080011d1644801201b480011d16464870a1d48001111d48536ae004a45b201d458851680434831d00480750d16c740120004480d201b480011d1640c751620458011b20408640a1d48001211642c0c201b448011d16458d9060044475201d4806d1d00480591d16458811d024806d211642c83171d45801111d47401030046c81162048459
|19=>0x1200c74592000474012016474592116690011220c74594f0648459120a480011d16474092116474011b20458011220480011d164748102004806d211646c81160048059211645c19160044475061382859200044475071bc482920004740d201b47401200045866290046c811d20481f91203c806d1d1644c4720174580121164182a111d480011d0245885200045801
|20=>0x201b458851500c58812116434591d0046c811600434811d00484590602474452116474591d1648459200044475200048075204b82c6f12004745916004a4591b204748121164541920164482a201b480011d164806d211648001111d458011d0044881161d44c751311c5401201642c831200448811d1644c4715004748116204340b1d00484591600454751b2045881
|21=>0x1d164640b0d20474012116478752002484590900c48811d1646c810900ca4591d2042c6f0d16474015f1bc5c191600444752e2041859111d46c811d38808012116458660a1d48001111d474011506c744520164806d1621480011600474452000474012016474451d00484590900c5401151d480591200474452116474590d20474451d0046c811d4144c47150048059
|22=>0x161d650011506c744520166b0871d764285b20004740120004a45b1d20464590d204740121164cc5b030046c812116474290a16480011d164a401162047481b800454772016428752000458751311c5401201642c0c0d16474011b2047429201b4580120004a45b1d20474011b2044c772017458010711c4829200045875161d4806d1600480011d004812d0b1bc4801
|23=>0x1d20480491d11484591d16474811d1745c81160042c83120047459a911c58cd1b2048459150045475201648459171d45801111d47401201d480012116458851d1745c811600474591500474811620434591d004845916214a45d1600480757000c18091d11484591706c4475160045885120048075161d4745920164a4031d20475990a06c8001111d48001201244475
|24=>0x1d004805916214a4591d204740d160346c81171d45801111d424031220474590f00424031220474590d40454371d00480595c1d444751500c58811d204806d211647459160047409200248459160040c011b2045881071dc48292000458751621458292000474812116424031220474590711c4829200045875450041881111d6ec590d03c74011b2045885291745801
|25=>0x150048059060045885111d46487290047481150dc8059150d874011b2045875201d4a459111d480750a0648001111d474011220458750a1648001111d44801122047459201b484591d16480752000444751220480011d16464870a1d480010a16c80011d00474ce030046c811720c5801111d408752000484591d0a4800116204340f1d0046c811220c4475161d45436
|26=>0x201d4345b1d00458811200c74590220458851d20454011d0048059201b480011d1644c471500480590900c48811d16458662900480751720458011d00484592900c74811d1640c011b20570751500c5881201b48001211640c011d0046c811d20474011600458d90600444751d03458851b20428592000474011621474011600434811d00484592917058011d2044c47
|27=>0x1620454351d00480591720458011b2044c470a16480012916458011d20418091d1148459211648001111d480752000484591916ca4011d204802e1200474591703458011b20458361d00444750a1d48001161d474012016474591d02484592016448012016474591d03474011b2046c811d00458811d024580121164482b200047459201b448011d16480012916c7481
|28=>0x2000474591d114806d2116474591600474010900448811d164480d201b474591b20458011d004744d1500480591500474811620480190600444751d764285b200040c011b2045881291646c811d204480d201b474591d1385c811600454011b20458810900c48811d166e001151dc80591203c806d1d16480351d0044475201b48459201642c6f120047459162145403
|29=>0x7459211647401201b47459201b484591220c74591220474592900c74811720458011600474591500480591600484591220474591200474592000474592000474010200484591d0046c81201d45875200248459211647459171dc5801201648075161d448292000474591d0a42859200044829
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x15a80000000000000000000000000000000000000000013280000000000010a8000000000000000000000007c80000000000000000000000000006940000155000000000000000000000000000000000000000000000000004500000000000000000628084004c00000000000000400000000000
|5,1=>0x141825304550000000000004230000000000003d5000000000000000000000000000000000000000000000000000000000000000000001c28000064c0000000000000000000000000000000c080000000000000000000000
|6,0=>0x2b145420a3513e800004d280001304251047a8000116800000000000000000004490000000021c841a00000fe81ed03d0800000000000000076400000000000072400001b9000006d10d46000000000000d04000033880000ca4190430205f10000000000005c3000016c42c90000000000002b18000
|6,1=>0x25aa4ac893a123424420000000000023aa46508c0800022c44544882800021c40000000109520e400000001043000040887f20000000000007ca80001ea800000000f0500003b4c75900001cca000070a80001c02000000000001b6a35946998cf4196831940000c2400002f900000ba416e62c940000b11
|6,2=>0x34a800000001a4100000000cfa99b432ca6490c8118f100000000000000000000000c52800031226114c02000000000000bf100002f485d54b8a16c52d44000000016642ca25850000000000005750ac280000000558800000002a48540800014b528e80000a12800028044f889d2000000004e449b19324
|6,3=>0x474a00011c8a36346668c0d17122b300000000000000044e80001121a1f5434a00010aaa105000082d5032a01500000000fea000000000000fc280003ec40000fa89f0500007b10f3a9e343bca7708ec21d44000000000001cf500007348e4a1c4538086f4c0001bc100000000dba9b2500006b540001a94
|6,4=>0x2a3553ca00014caa9810000a51000000000000a3d5461a893508a000000028044f6a9d9538aa6f24d4a995400026054b8895d5292a4d5490a000122223f5
|7,0=>0x7006df11bc9b7546e46dbcdb5a36836c880001b0235c46b08d54da8a34d46928d151a0a33e36748cd9199232e46548c9cd921b20463a6c6518b1b13361e8c30c00030846088c0117e22f845e88bc4d76a2e945ca8b8516ea2da35ae6b585692000059c8b2916322c2457c8aecd5c1ab625648ab91559aa83
|7,1=>0x8cc918922f245a48ac8000229244f38969120e222440487890e121a2432285c90a921324242842707520ca41548229035204a40548046ffcdfda3f747e68fc0df623e847c88f811ee23d847a88f411e623c9378a8f051dea3bc17708ed11d823ad37528e951d0a39d473280001cb9393471e8e2d1c3a3834
|7,2=>0xa9880002a425444a8094f129c25344a6094b12958d2a1a4c948928f9d1b4a2e944d287a50b4a0e9410e8024fe29f493d927a880009e293b5274a4e549c4737926d24d739a6933d265a4c74988730125e9cb9496a92c5256a4a9494a928524ea499492a9245246a489490a920523ea47948ea91c8e37246a4
|7,3=>0xc549899311261e4c349859309260e4c14981cf01a5ff4bf697dd2fa1df13bda97a52f2a5e14bba9768c0005d64ba4973cee5a5c74b8697086df9dbb4b6e96cd2d7a5ac3b5096912d09d9e3b36765d2c9a58f40001630c0005884b08960c6bfa57b4af075d4eb8a56e3ad4959ceb1a55f4ab6955d2aa1d504
|7,4=>0x62e4
|8,0=>0xdda7ba8f739ee43dc27b78f6d9ed83daa7b48f679ecc3d927b18f619ec03d7a7ae8f5b9eb43d627ab8f559ea83d4a7a88f4f9e9c3d327a58f499e903d1a7a28f439e843d0279f8f3d9e783cec59d0b389e6e3cd679a0f329e623cbe7970f2c9e563ca67940f269e4a3c8e7910f209e3e3c7678e0f1a9e323
|8,1=>0x3a39f443e827cf8f9d9f383e6a7cc8f979f2c3e527c98f919f203e3a7c68f8b9f143e227c38f859f083e0a7c08f7f9efc3df27bd8f799ef03
|9,0=>0x1db8bb6176a2ed05d98bb217622ec05d78bae175a2eb05d58baa17522ea05d38ba6174a2
|10,0=>0x1dc87b88f701
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x5c0000000000005b000000000000560000000000004e0000000000004c0000000000004a0000000000004800000000000046000000000000440000000000004200000000000041000000000000400000000000002600000000000022000000000000200000000000001f0000000000001d0000000000001b0000000000001900000000000016000000000000140000000000001200000000000011000000000000100000000000000d00000000000008000000000000060000000000000500000000000004000000000000020000000000000100000000000000
|1=>0x107f0000000000105f0000000000105e0000000000105d0000000000105c0000000000105700000000001055000000000010480000000000104400000000001041000000000010400000000000101d0000000000101900000000001010000000000010050000000000100400000000001002000000000010010000000000100000000000000802000000000004400000000000040000000000000264000000000002000000000000010200000000000100000000000000c00000000000008900000000000080000000000000600000000000005f0000000000005e
|2=>0x2147a0000000002145f0000000002144100000000021417000000000214070000000002107f0000000002105f00000000021041000000000210030000000002100100000000021000000000000204440000000002005d0000000002000300000000020002000000000200000000000001024400000000010042000000000100000000000000d0ff0000000000d0040000000000c0a20000000000c0820000000000204800000000002040000000000020000000000000145f00000000001401000000000010ff000000000010cf0000000000109b00000000001080
|3=>0x1200020000000011007f0000000010107e0000000010105f0000000010007e0000000010001d0000000010001600000000100012000000001000040000000010000200000000100000000000000a105f000000000a007a0000000008149f0000000008145f000000000814440000000008107f0000000008105f0000000008104200000000080440000000000800ea0000000008004a0000000008004200000000080041000000000800400000000008000a000000000800060000000004006200000000040020000000000400060000000004000400000000040000
|4=>0x22044300000000220003000000002200020000000020147c0000000020145f00000000201447000000002014000000000020105f0000000020101700000000201005000000002010000000000020001d00000000200000000000001a10df000000001a105f000000001a1046000000001a1042000000001a1002000000001a005f000000001a001f0000000018145f0000000018105f000000001810170000000018100200000000180046000000001800020000000012141f0000000012104600000000121017000000001210040000000012004600000000120013
|5=>0x401146000000004010ff0000000040107f0000000040105f0000000040101d000000004010170000000040100000000000400104000000004001000000000040004a0000000040004000000000380419000000003010540000000030104000000000301017000000003010040000000030004400000000300015000000003000040000000028105f000000002214df0000000022147f0000000022145f0000000022145d000000002214440000000022141b00000000221407000000002210df0000000022105f000000002210450000000022101f00000000221000
|6=>0x1080448000000010804460000000108005e00000001080040000000010800040000000102145f000000010210cb0000000100145f000000010010df0000000100107f0000000100107e0000000100105f000000010004060000000100004800000001000041000000010000400000000100000000000000c214df00000000800008000000008000000000000062005f0000000060107f0000000060105f00000000601057000000005a105f0000000050107f0000000050105f000000005010170000000048107f0000000048105f000000004210570000000040145f
|7=>0x300005e00000002641073000000021000230000000208005e0000000201107f000000020100000000000200005e00000002000040000000020000000000000170105f0000000170101f000000014210150000000130105f000000013010540000000130105000000001301044000000013010160000000130005d0000000130005600000001300046000000013000060000000120101700000001201000000000012000040000000110005b00000001100050000000011000060000000108145f000000010814400000000108105f00000001081044000000010804fb
|8=>0x80000000000000610000090000004010814df000004000014df0000040000144f0000040000000000000200000090000002000000040000020000000200000200000000000001c05a00bb000001004210ff000000401a00fb0000004000c0c00000004000c00000000040001aff000000200010000000002000000100000020000000000000180810df000000140010fa00000010000000000000085210df000000080000800000000800005400000008000000000000040010ff00000004001000000000040000c0000000040000040000000400000200000004000000
|9=>0x80000000200000800000000220008000000000600050800c0105d00050800c010550005000000000000048d004210c700040000c0107f00040000c0045f00040000c0041f00040000400006000400000210170002000000001000010800c810cd000108004000040001000140111b00010000511076000100004001100001000000100200010000000000000084101010d9000080080000800000800002104b00006100401000000060004010000000410000000000002000000000000010004000020000080360107f000008024a107f000008004a105f00000800400000
|10=>0x400080202010df4000800c0000df30010801401058200000000000501001000040115f1001000040110010000000c0055f1000000040115f100000004010530c00010000000002050800c8004c0205000048105f02000000400002010000000000420080000000000000400410000098004000000000c8004000000000080030008040000400300080000044001000800000240010000000002200080080410277000800021a107f0008000203107d0008000100147f0008000004123e0008000001127f0008000000127f000800000012660008000000022600080000000222
|11=>0x8000000004107f4040001500100a
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x381c08000000026000000002000000000000000000000000000000000000000002c000b00000000000000000008c0000000000000000002c00000000000000000000000001000000000c000000000000004400000000000000000800020000000000000000000000000000000c00000000010140b0000000088000000
|6,0=>0x2988c105185000000020888a0003024c4a00088000069088000002004000a00000015c00288000127000b63400338001c008500000008915406405c94800030005c0008238140075000cc81240a00024009d008d4000a0000000000023e00004980200040061a0000000001200000001700334002a0a000000011800a0007b9182c7500000012a004b02200000000600
|6,1=>0x99802142d0100cc00200000000016800c6062b800706700125845600000240000000d200118019eb60005c63190b3dda0820000000af0008c4e1d01850002a00000384400198002b04000004d0000110026900c4c50000000000000002c003a9e4a200000004600169e05e12660000008929dc00000002034000008c000001418006a040016000089809c00001405a4f
|6,2=>0x763500034280005000000015623173280000768a8642e60069a8002c0586900795d8000210
|7,0=>0xa81003418a001fc037f80e0ef256806b90839a04086374160094b17d15834d8c051894a81ad5dd52ad170bf39a61d2ae0285be65b51322c4fa010c03942060b80211284f3545e3d1682c073180c1066032d8009442030528091098051c9538ac0907234370fe170a4b90cdc7a06400206cc245c3295a81c70e65a5d644700be9fa009d825cb3d94b4204b7991b45c9d
|7,1=>0x68fa444f98011d68706c3c6ad1898dc0c27063807c1f76be0000d25851ba8d0f0a202051eaa042031ba98109901af14534001de2c3c75134723d011d97414a745cc25d0548dd24300801c8ce03cbdc29c881ae7e600b9fe3cc85e24048011805103205a3f2ac0006cf918626dd402e039b25868e6168a45a3a69950762142d4e6a360dd3d1349382e0f71b41821ce6c
|7,2=>1
|8,0=>0x1223e1ca517ce407551b00f77d79315b63d5566f61f1f184ab63390fc7a7abc51e4c21a8d34dfaec714e8ba23926ec5a19b9bca32f22a8eec64bcd083e791697e7c65565b5609c3ce8caa2c8fa0a9f018524292afa3de01c61a9122a956561af4252b021845a44f23a90
|9,0=>0x3097a6e48965e6e279b5922e45626ec2c03a3ecded4
|10,0=>0x1b87e45
|11,0=>0x3e
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 56 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_126 9 roots_126 ops++addP pm 2 dom_222 9 roots_222 ops++addP pm 3 dom_246 10 roots_246 ops++addP pm 4 dom_250 10 roots_250 ops++addP pm 5 dom_188 7 roots_188 ops++addP pm 6 dom_238 9 roots_238 ops++addP pm 7 dom_218 7 roots_218 ops++addP pm 8 dom_118 7 roots_118 ops++addP pm 9 dom_156 5 roots_156 ops++addP pm 10 dom_94 6 roots_94 ops++addP pm 11 dom_248 8 roots_248 ops++addP pm 12 dom_190 9 roots_190 ops++addP pm 13 dom_92 5 roots_92 ops++addP pm 14 dom_216 5 roots_216 ops++addP pm 15 dom_184 5 roots_184 ops++addP pm 16 dom_172 5 roots_172 ops++addP pm 17 dom_206 6 roots_206 ops++addP pm 18 dom_124 7 roots_124 ops++addP pm 19 dom_158 6 roots_158 ops++addP pm 20 dom_174 6 roots_174 ops++addP pm 21 dom_110 6 roots_110 ops++addP pm 22 dom_230 7 roots_230 ops++addP pm 23 dom_214 8 roots_214 ops++addP pm 24 dom_62 6 roots_62 ops++addP pm 25 dom_236 8 roots_236 ops++addP pm 26 dom_122 7 roots_122 ops++addP pm 27 dom_234 8 roots_234 ops++addP pm 28 dom_154 5 roots_154 ops++addP pm 29 dom_106 5 roots_106 ops++addP pm 30 dom_232 7 roots_232 ops++addP pm 31 dom_212 7 roots_212 ops++addP pm 32 dom_178 7 roots_178 ops++addP pm 33 dom_170 5 roots_170 ops++addP pm 34 dom_186 8 roots_186 ops++addP pm 35 dom_182 8 roots_182 ops++addP pm 36 dom_242 8 roots_242 ops++addP pm 37 dom_210 5 roots_210 ops++addP pm 38 dom_226 5 roots_226 ops++addP pm 39 dom_202 5 roots_202 ops++addP pm 40 dom_166 5 roots_166 ops++addP pm 41 dom_116 5 roots_116 ops++addP pm 42 dom_198 5 roots_198 ops++addP pm 43 dom_220 8 roots_220 ops++addP pm 44 dom_228 5 roots_228 ops++addP pm 45 dom_180 5 roots_180 ops++addP pm 46 dom_58 5 roots_58 ops++addP pm 47 dom_108 5 roots_108 ops++addP pm 48 dom_204 5 roots_204 ops++addP pm 49 dom_150 5 roots_150 ops++addP pm 50 dom_146 4 roots_146 ops++addP pm 51 dom_162 4 roots_162 ops++addP pm 52 dom_102 4 roots_102 ops++addP pm 53 dom_54 5 roots_54 ops++addP pm 54 dom_90 4 roots_90 ops++addP pm 55 dom_60 4 roots_60 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54|h55
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h52;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h53;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h54;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h55;exact cpcs (by decide +kernel) lowS_60 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 15 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 111 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 111 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 256 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_256 : ∀ i, 256 ≤ i → i < 289 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 33 256 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 289 → Z 6 i = true := (range_split z6_0 (range_split z6_128 z6_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 257 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 257 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 94 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 94 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 19 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 19 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 3 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_254 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_223:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_iso_b isoMvS_223 (by decide +kernel) lowS_191
def isoMvS_253:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_251
def dzo_171_4:=0xf0f00000f0f000000000000000000000f0f00000f0f0
def gzo_171_4:=0xf0f00000f0f000000000000000000000f0e00000a000
def gsh_171_4:=0xf0f00000f0f000000000000000000000f0e00000a00
theorem lowS_zo_171_4_43:Lower true dzo_171_4 roots_171 gzo_171_4 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_4) [(dom_171,4)] (by decide +kernel) (lower_slice_b (T:=gsh_171_4) [(0xf0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_43)
def dzo_205_2:=0xcccc000000000000cccc000000000000cccc000000000000cccc
def gzo_205_2:=0xcccc000000000000cccc000000000000ccc80000000000008800
def gsh_205_2:=0x3333000000000000333300000000000033320000000000002200
theorem lowS_zo_205_2_77:Lower true dzo_205_2 roots_205 gzo_205_2 6:=lower_iso_b (d1:=dom_205) (r1:=roots_205) (T1:=gsh_205_2) [(dom_205,2)] (by decide +kernel) (lower_slice_b (T:=gsh_205_2) [(0x3333000000000000333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_77)
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0f00000f0e00000a000
def gsh_107_4:=0xf0f00000f0f00000f0e00000a00
theorem lowS_zo_107_4_43:Lower true dzo_107_4 roots_107 gzo_107_4 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_43)
def dzo_237_2:=0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc
def gzo_237_2:=0xcccc0000cccc0000cccc0000cccc0000cccc0000ccc80000cccc00008800
def gsh_237_2:=0x333300003333000033330000333300003333000033320000333300002200
theorem lowS_zo_237_2_77:Lower true dzo_237_2 roots_237 gzo_237_2 7:=lower_iso_b (d1:=dom_237) (r1:=roots_237) (T1:=gsh_237_2) [(dom_237,2)] (by decide +kernel) (lower_slice_b (T:=gsh_237_2) [(0x333300000000000033330000000000003333000000000000333300000000,0,32),(0x333300003333000033330000333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_77)
def dzo_93_2:=0xcccccccc00000000cccccccc
def gzo_93_2:=0xccccccc800000000cccc8800
def gsh_93_2:=0x333333320000000033332200
theorem lowS_zo_93_2_77:Lower true dzo_93_2 roots_93 gzo_93_2 6:=lower_iso_b (d1:=dom_93) (r1:=roots_93) (T1:=gsh_93_2) [(dom_93,2)] (by decide +kernel) (lower_slice_b (T:=gsh_93_2) [(0x333300000000000033330000,0,16)] (by decide +kernel) lowS_77)
def dzo_109_2:=0xcccc0000cccc0000cccc0000cccc
def gzo_109_2:=0xcccc0000ccc80000cccc00008800
def gsh_109_2:=0x3333000033320000333300002200
theorem lowS_zo_109_2_77:Lower true dzo_109_2 roots_109 gzo_109_2 6:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_2) [(dom_109,2)] (by decide +kernel) (lower_slice_b (T:=gsh_109_2) [(0x3333000000000000333300000000,0,32)] (by decide +kernel) lowS_77)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,18),(2,34),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,28),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,17),(16,18),(16,20),(16,48),(16,80),(16,144),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,48),(32,96),(32,160),(36,37),(36,38),(36,44),(36,52),(36,100),(36,164),(64,65),(64,68),(64,72),(64,80),(64,96),(64,192),(66,67),(66,70),(66,74),(66,82),(66,98),(66,194),(128,129),(128,130),(128,132),(128,136),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|4=>2
|5=>17
|6=>66
|7=>284
|8=>448
|9=>273
|10=>105
|11=>30
|12=>6
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x3113509eb8
|5,0=>0xec16bcfb899320e6bf9158ca4513bc4f95836a76286db23b40202f51fe771df0c17d1914d7d133e810a71
|6,0=>0xf7619e8699e79c3e3b77e06e2c7bdcbed5bb6731b0597ad836aa1c5a45239e4c49a31689ca088588817807fc367e3357de737cb3d774c770ffa6f8806ea856e5c36e3616d28d6b6a0687d363c9b574e8569f65024a4eeb04e5074cacc4a926489e6472ff415563faf23af5730b312e9982e98b295812492122ed5229b71c48c17ddb17326152ca14ba413cda13acf1371d1310711b37104eb0f8d10ab9e08986064da0272b
|7,0=>0x48ac24860047c954766c472ca46d9d46b754583544e00448c44467643f4743e7a419483faea3f86a3eb333e38c3d4313d2db3d06f3cdb73c1593b6493acaf3a86d3a00d39c5b39aa73921238d5038aee3877137a1a37894377ae36910363f933b8f31cb231258301f82f9552e4282e24e2df202da762c96c2c8d82c8542bfbb2bb222b2272912128a1e27fac2797f273372689b25a15259432510c2473723de723ae722bec22aec2292a21c5e21b82214961f9cd1f0901da241d58c1c0861bc0d1b65c1b3791ab491963d18c9418c4b1832817b09172591616514a0a142fa13c2f137da1354912c7211f850fe800fa160f3890f2860dbfc0ca1b0c8200c4510bb290b9e40b6140b4c90b0910af510a0f509e5409d7109c33099a8098b5090d208af7084000620805d4605d16055d90532f028b702778026d5022650206601be5
|7,1=>0xd0edacfffccd3c5ca1b6c94fdc8b32c23d9c1da6c0e4cc08f8c0436bbc92b900cb808db6c70b2150ae304ad6a8ad1b0aae6fa73c0a6d1ea6174a4e079f9959dc799d3749cf679ce299c9329c7b19c223994a79790c969ac9610393a91937a4929e8929659236990531901238fe238d3418bcb48a3378a1d9894e888d8b872df8569b84f87840d883ede83730836e382ab780ebe7f6b07cdf77cdbc7ad247a98f788f477fc377e657686675bf17504f749527144170baf6f8586f8176f0116eb2d6e4056d36e6b3986b13a6aed669ba068c51683766779567661667de6540a644d663aac63715618386151d608ee5df615c6f95c5bb5b2d95a95c59f565985f5880c56b88558b3555395488c540fa5178050e794fcdb4f8a74f50a4f4e24dc054bf2c4bf0d4bc6f4ba444a9394a8434a3c349d3249af249a114998b4984d4925e
|7,2=>0xfeb9afd864fb873f670ff5590f53d9f4592f3731ef52eed662e6633e2d2ce2568e18c9dff4fde25cde223dceebdcd1edc2c4dbfabdb6c5d943ed44a0d3014d2c0bd2b93d227a
|8,0=>0x29be8290ee283702817127caf27795273f9273a826d48263b225efd25928251d824be02432523868235b22313522f9922e5b22bec22a2b220ee21315207c02038f1ff711fb311f86f1ed7f1e6ba1e6701e3d71d46a1d36a1cba11cb271c69b1bf751bc4f1b41e1a8e91a5951a2b71a03419aba195bb1947d1771916f2616838166ce1657b163fc160f115dad15d93156ee150c6150c114fd0148bb1427f13fda138ad131ed12fe812b5b12699122e411b3c1167a1101210c9d106bf0f87e0f5ac0e6070e5270e0ef0dedf0d1530ce3f0cd6f0cc910c7d20c22c0c0d50b8860b69a0b4b60b45e0b2b30adf10a34009c6d098150926608da408b870863707a68079160754406e4e068e6068c205e84059c2053070503104f8f0423403e6703b7b0390f0363702efe02e2902dee02d0f028d8020d301f1401ee3019070131d0011b
|8,1=>0x6676b658046521363e9c636c96345a6305162a5761d32619486145560da2608a25efe75e9025e3ec5e3505cfb45c9a359f6458b9b5807b57ea357bb956c815686c5630355d3b557a354fad54ac454548529e352521520c6515eb511eb5070b4eaa04e66b4e09d4debd4d9794d5dd4ca5d4bb204b70b4b65e4b46f4a87d4a32849f83496ac495034797047835476de4766c45c12455404511c43cc2439294380043697435c94311242c51428c8425f242175418c340e52404773fa823f7dc3e88e3d8b63c58a3c2703bdae3b7b83b4ed3b1fe3aa783a9a13a5803a3163a0153995d398fd39774394a538b2f38ac63880337997375f737317365d03587735250342b632ec1323d031f223119c3105c30f6b300842f8b22f6322f50c2e6772e2392e2142ddbc2d9972d5812cb6b2c6e82be212bcaa2bc972bb032b00a2a78a2a279
|8,2=>0xb733cb713fb51aeb4372b419ab33cdb212eb1362b0e1bb0dc0b02b1b0085adecdade4caddc3adad9ad39cabdbeaba02a7f43a7a81a753aa65faa4ff7a3cd3a3bcba2913a1205a0f279f3399ebde9eab59ea269dd459d7a19d3989ca079ad409940997b529689c9662a953c7944ad944a6931819247d922399216b9027a8fade8e83f8e5c08cef78cb578c5468b5d98a8218a1c6896a6894538931588eff87fe587eda87d8087bc986fd4868d88556684a6c83f1c83bd78379982e0f8281a8205b813fd8135e802f37fe1a7fbe97e92d7e1247db167d34e7cc447b0217ab847a6397a2eb79af678255777ff7746e7687576473760c675378742df7421473f4873d5272ce0728a471b8b71b4d71aed715ff7136d711af70c996f8176f5946deb56c6326c1706bcaf6bc2e6b3d469fc069db169bab694d86829067f03675b666872
|8,3=>0xfe31cfcc99f8658f7e73f68f7f5f31f3397f2ed5f210cf1ac7efe1cec363eb87de79e2e3d9fe33f2e1275df001de45fdd129dab14da345da2d9d6fadd6737d666ad62b6d6171d5043d3629d2cebd2bd2d0581d03c8cf972cf5a7cf039ce949ce404cd4c8ccebccac48c9f9ec8d62c7af6c676ac65e0c6000c4e04c335bc0e9cc0c8ac0a3ebfb66bed1fbe64dbe29dbc4d0bb229ba79cba3d9b9cbbb85f8b75e4
|9,0=>0x451d34508944f4b44b354414543bee42aa1429e24283a3f9f93f6c63f2043eceb3e7bf3d9c53d0313c95b3c44a3bbeb3a1c6395803819337ad43696f363bb35f1f35103341fa3371732ed232a10326903256a324cb3121630e74305df3044b2ff912f9f22e6292e2142c4bf2c14c2bcd22ad592a73c29f7229ab028f5328e1a28a912842925771231ea228cd226ca2220821ddd213eb204c81ff9e1f3471e5be1e0131d10c1d0111adf81a2641a12619f8419af61972c1945a1812418106172dd16bf315e98151ce1500a13cfb13cb51371d132fd1260a1111d10a501039f0fb770f8300f28a0e8e40e3110df780de4f0d3de0d2a00bd230bbe50b5df0aac60aa450a5a209944093e20937e0836507e3607a070729206d1706bd905f5c05eab05d6d0512e04965047a20437b03f010399f02da401fc601d8400e72008b5000d7
|9,1=>0xcd49ccc14dcbcddc9de7c905ec7199c655fc3efac2bc4c2672c1e22c1d7dc1693bd4e2bcd19b5eccb579fb3e1eb216fae52cae43fadb7fada41ac522aba02ab8c4a988ca9650a8e92a8beca78b6a6c29a52a1a4f6da4f37a33b4a1a24a0a07a07ffa03f69ddb69ad0e9abb099d34997c699688990d697af79770a976499750b96e219529793409924a48e6378dae88c07a8b46f8b31e8b1cb8a66388b5d86776858788445b81d718198b7fb187e2337d9df7c5fd7b3f1785d975be275b9974bab73aa972571722a2704e36ea826e3c36b6b46aa3b691b3691a067f826499963a586307661829610d660aac5f2215b2435a00a58fcc58d4d572e455ca554fae548cd53aa2538ca5368c52356516c950b68508bc4fcf34fbb54f1f94da194c6aa4bfe74b4964aff84a47749cde49b2c4981c492614817a4729345bbd45a8e45650
|9,2=>0xf744af5956eab7eea9dee9ebee9175e8e47e6917e087edd913d8cb4d7d99d5b05d39f3d3531d2ed8d0211
|10,0=>0xfccf7e70c5e60a6e3eb9df81dd9fbdd6372d2485b557cb51cdb158ab10a4b0bddaea60aca28abc4aaa914a8b3ba82ffa14839f4339cd929c1349b5469ab559a99e94f849457490b468e50c8e2298cdff8987784dcf82619805e97fae27b9657b63777ae874019734e17012c6b1946b0566ac40693dc67845615ae5c02a5a3425749a56e10566ea55afd553b4532ea5225750f034c51a480e746c4c45a4042a574170c4036f402314008f3eb6a3ddfa3ccfe3ab323941932fef32b8e32a502f51d2db552bfb62be78287cf259d02313a223a51d2c2182891822c1806816c2c1610c142b91417b133fd1057e100bc0f6d80ded10de520dbe10bec70629904de203ed002d3001d53
|11,0=>0xfd1ddf2f5cecb32c0345b4102aeb579d9fc975d277077732c87318a6e1f266f2358f0a58c9958b5b47d6c433cd3cccd31fd230bb32e0e528a2e277740be990bd5b092f70613d05d8e03fc0
|12,0=>0xc37529892d8fd7c792e4765a30eef7
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc5555555555555555555555555555555555555555555555555555555555555500ffffffffffffffffffffffffffffffff00000000000000000000000000000000fffffffffffffffffffffffffafafafafffffffafffffffafffffffafafafafaccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffffffffffffffeeeeeeeeffffffeeffffffeeffffffeeeeeeeeeeffffffffffffffffffffffffffffaaaaffffffaaffffffaaffffffaaffffaaaaf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000
|0,1=>0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffffffffffffff00000000ffffffffffffffffffffffff000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff00ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff00000000000000000000333333333333333300000000000000003333333333333300ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000000000000000000000000000000000000000ffff0000ffff0000ffff0000ff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f00ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffaaaaaaaaffffffaaffffffaaffffffaaaaaaaaaa00000000000000000000000000000000ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000
|0,2=>0xffff000000000000ffff0000ffff0000ffff000000000000ffff0000ff00000000000000ffff000000000000ffff000000000000ffff000000000000ff00ffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff00003333333333333333333333333333333333333333333300003333333333330000fffffffffffffffffffffffff0f0f0f0fffffff0fffffff0fffffff0f0f0f0f00000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00ffffffffffffffffffffffff00000000ffffff00ffffff00ffffff0000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffff001111111111111111111111111111111111111111111111111111111111111100000055550000555500005555000055550000555500005555000055550000550000000000000000000000ffff0000ffff00000000000000000000ffff0000ff00
|0,3=>0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff000000000000000000000000000000000000ffffffffffffff00ffffffffffffff00ffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffff0000000000ffffffff00000000ffffffff00000000ffffff0000000000ffffff003333003333330033333300333333003333330033333300333333003333330000ffffffffffffffffffffffffccccccccffffffccffffffccffffffccccccccccffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffff00ffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f000000000f0f0f00000000000000000000000000ffffffff000000000000000000000000ffffff00ffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffff0033333333333333333333333333333333333333333333333333333333333333000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ff00
|0,4=>0xffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffff000000000000000000000000000000000000ffffffffffffffffffffffffffff0000ffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff00ffffffffffffffff3333333333333333ffffffffffffffff33333333333300000f0f0f0f0f0f0f0f03030303030303030f0f0f0f0f0f0f0f0303030303030000ffffffffffffffffffffffffffff0000ffffff00ffffff00ffffff00ffff000033333333333333333333333333333333333333333333333333333333333300000f0f0f0f0f0f0f0f03030303030303030f0f0f0f0f0f0f0f030303030303030000000000000000000000000000000000ffffffffffffffffffffff00ffffff00ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ff00ffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffff003333333300000000333333333333333333333333000000003333333333333300ffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffff003333333333333333333333333333333333333333333333003333333333333300
|0,5=>0xffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffffff000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000ffff00ffffff00ffffff00ffffff0000ffff00ffffff00ffffff00ffffff00000000ffff0000ffff0000ffff0000ffff000000000000ffff000000000000ff003333333303030303333333330303030333333333030303033333333303030300ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ff000f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f00ffffffffffffffff3333333333333333ffffffffffffffff33333333333333000000ffff0000ffff00003333000033330000ffff0000ffff000033330000000000000000ffffffff00000000ffffff0000000000ffffffff00000000ffffff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000ffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f000f0f0f00000000000000000000ffffffffffffffff0000000000000000ffffff00ffffff0000000000000000000000000000000000ffffffffffffffffffffffff00000000
|0,6=>0xffff0000ffff000000000000ffff0000ffff0000ffff000000000000ff00ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffff000000ffff0000ffff00000000000000000000ffff0000ffff0000ffff0000ff00ffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f000033333333030303033333333303030303333333330303030333333333030300000000000000000000ffffffffffffffff0000000000000000ffffffffffff00000000ffff000000000000ffff000000000000ffff0000ffff0000ffff0000ff000000000000000000000000000000000000000000ffffffff00000000ffffff003333333333333333333333333333333300000000000000003333333333333300ffffff00ffffff00ffffff00ffffff00ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffffff0000000000000000ffffffffffffff000000ffff0000ffff0000ffff0000ffff00000000000000000000ffff0000ff00ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ff0000000000000000000000000000000000000000ff000000ff000000ff00000000ffff0000ffff0000ffff0000ffff0000ffff00ffffff00ffffff00ffffff00000000000000000000ffffffffffffff000000000000000000ffffffffffffff00
|0,7=>0xffffffff00000000ffffffff00000000ffffffff00000000ffff0000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0000000000000000000000000000000000000000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff00000000000000000000000000000000000000000000000000000000ffffffffffffff00
|_,_=>0
def sP:Nat→Nat
|0=>0x101c70a023cd9d00785011e6ce871c0c10d021c5961454488301890d0a1cc03243408708189190a009862428e05261810a0a6860b143cd87260c10a02689862434c85301890a0a0059614247972c28a891e509822434085224058a123c7060434287182c509101c20604140040608080
|1=>0x2c28c8f361c60a0a3ca1a0e2cf0a32244072c38501123cb8b2c94e051e902123204280224070a022479e147028f281c80b2c352851e4c90a380428e0648699021c60e14044880e101120214d074c2cb2538147842c540891e9118c162828f0e385014484d0716785051e8038b2c28c89
|2=>0x1ebc3a6202c5091e1c9822428085343831214702873058501122038c16586a50a3cc121a04287260c90a3204d111658519123cb0a02247ae0e2cf0a123d50716785191e6c3ad163450f5800c2b14147801c0c90a380438e0608501341c7062434c850e2cb0a123d5072c38515123d48b
|3=>0x2a0448f664459e145448f2260b0a022478b3c28e0f641c80b2c945091e2cb0a2a1441a30585011e6c38b2c28e0f641c8ad3c280891e60f0a02244071659299123d20b2c28a891e9080b14247a40e4c312146429a3c4c5051ec580c1c2848f521d30b2c94c891e98596145448f3c28089
|4=>0xe39c8a380478716785190a3dc073c28c81123d9871c28c8f64a4d071c2808f3680d074c60b0a022478708a0e010a3c3842694e01123cc0a0a3dbb6341cf8c162848f0e585150a3ca1a182c5091ed438b3c29a091e1c60b2c945091e2cb0a6824787182c5091e9039f1658515123cb0a
|5=>0x2247872c3851902244074c7898a7c0428f3e2cf0a32247875a2ce271eb00043c700851e903a616792990a3c03d3c28a81123cc0d1414794341d30b3c28a851e00c1614047b2341c20c3cf00851e1cc0d02147bb0038534023dd1a0e8c596146428f0e9859e4a6448f0e9859e145448f
|6=>0x1c94e010a3c9b9146408f3504f0a02147b00e386a5021479d002cf2514147b00e8c60e140428f0f0c70a38047c20e60b0a02247a40e786a5021479d0e1061e4a0428f00385010a2181a0eb458d143d61a0e7870a02147a00f04f0a32047c000b45a7123df87304d28a0a3d89a0830f25
|7=>0x2c28c851e50d074c2cf0a7c14787202d38f58fcd071c345010a3cb801c9451c023cd87202df27123df8730586a5021478c16585091e1d68b14147a4341c70a323e046341c88b2c28c851e68b0a02147ae341c20c3d140851e1c8161c352810a3d18e140428f881c59e14147aa341d316
|8=>0x46385010a3d507202cb0a1f1cd073c3851902244071c28c8510a4d0782386810a3ce802c3929c02147a430785011ec8d070879e190a3d88716f938f8efcd07084c6810a3d81a0830b0d02147871c28c811ec8d0782786810a3ce87307868a0a3d8871c2828f62a8d07203058a1f1cd07
|9=>0x1c280851e5c0161c280891ea838e7c9c48f98fc39016287ac341e08e147008f361c20e4a0428f9600c161404288341c80b14f848f0e60f0a02247a40e2cb0d32147a40e4c6a8320428f0858f25380428f5a2c68a0a3c00e2428e010a1d68e143e549341c70a900428f00605280214780
|10=>0x140428f400278b14247879c2c5091e1c98e14147b16068992146408535345190a3d99a0e3070a0a3d49a0e4470a02147aa342cb154e247bf4c2cb25321479a4c2cb0a2a1479a3c280851ebcd07202d3891efc3a6202c5051e6839e140428f60cc38c1c287c7986838e14047c096683a6
|11=>0xe4058a0a3d21a0e4518e14640851e385530a3e91a0e44c1e140428f00109a532147b134605051ec599a0e8c70a02147b00e4059e143e39a0e3853e123e6072260f0a02247871c2828f6274d07164c551381478418592810a3cd1126280851f2cd1e146428f286839816945091e00725
|12=>0xf04f0a02147a00e4569e140428f342cb0a2a247ad1c345011eb0010162848f0e7cc16140448f0e60f0a021441a0e785011f00e9a0e2cb25146448f16786990a3d2073c4c53e0a3ea131c29f091f5021e8a540851e2cb2532147a4342cb0a2a147a434b4f0d14047ac0e38519021441a
|13=>0xa3d8875a3938f9358d07164de0a0a3d81a320428f48ccd073c280891e743983c280891ed43911c280851ec0d0e1404288426839814147b6341c2161a540851e385051ec571a0e1098a02147cb010470a02147a00060b1e4a280891e38519022111a0e385051ea551a0e405961a2828f
|14=>0x3c345051e1c80b2c945051e6968b4e3e556341cb0e146448f521c7032428c81341cf983c280891e1d3183c940851e009bc146428f286861e2694501123d1982c280851e1c61e26f05010a3d3183c940891e1cc1e140428f701d3134a0428f9668f0a021479d0038501123ce800878699
|15=>0x182cf251424787302828f6650d07182cf3c1414787182cb154e2479130585010a3cd0a02147cb66683843c340851ec038e14147b0286838e140428f546838e14047b296683ad16287ca341c70a3204440341c70a0a3d49d341c5963c352990a3c70a0a3d4b0341c5963c345150a3c80b
|16=>0x481c80b4e3e3bf341c70a023e044341c60b3d145051e1cc39140479a0e405963c2848f0e7870a32247a90f0470d32047c00038112140429a0e7c596145428f348cc1e140428f0e3928a320479b004058a7c3e39a0e5851502147b334305a7123df872c38515023d91a222cf0a2a1479a
|17=>0x1f64d2626280851ec0d0e1a940851f2c00e1404288966839814147d8341c70a7c3e3cc341cf1378280851ec059614d028f341c70a023eb9d341c5931a2828f606860b2c345051e1c80e143d64c341e09e146408f361c80e14f848f981cc1614147a9341c60b14147a4341cc161a0428f
|18=>0x2147cb0104f0a38047c00e305964a2828f3498596146448f0e2cf3c14147b00e60f0a0a3d49a0e60b25140448f304de0a0a3d89a9a385191f68d072c38515021441a3c945010a3ce801c94501123ce801c28c8f80c4d0782385010a3e58008785010a3d007202c50f8e683911c28085
|19=>0xa3ea804c4c5010a3e580182d28a123c38e14647c0526838c169c7c77e6839e26345010a3d8111c640851e90d1f182c5051e68390182d3891efc38b2c352990a3c5961a28a851e385051edad9a0e309a5140448f5a2c5091e00596146448f481c60b14147b5341c59e14d028f341c98a
|20=>0x341c8901c280851e682102c340851e1d18e140428f3a0060e1404288341d18a320428f661c59e1a2828f601c70a380479b0e10b1502147a43410f0a320479b0e3058a1f1cd07202cb0a123c39315700851e0080c162848f0e2cf0a32247a40e385011f0979a0e44f1314640891e61281
|21=>0x486838e140428f60ccd07302de0a0a3cd075a2cca71f28d07821070d320428f0010b1e1a540851e1081e1a0428f0e2cf0a32247b50e2cb1e145448f203850f8f30d07202cf0a123c38b2c7928a322478e1404288546839f1658519123c3961c280851e5cd111678519123c3842464085
|22=>0x1c28a810a3c02d16287ac341c20e780428f606838e329c7ca5924d071658aa70a3df9ac03929c0214787302d28a123cd071c945010a3d01a0e8c70a32047c0341c80b4e147bf341c70a320479b341ef8e14540851e6859338553891e38553021479a0e1070a02147c4341c70d320428f
|23=>0x1e685931a28a851e6969e389c08f581e0a31c28e010a3c398140428faa003a63c3929902247874c7870a2a0448f0e2c98a32247803c3851902147b80e605a51414780350470a023e01d341e78b141479a0e3928a32047d7341e70b141479a0e38534021479a0e9820e4a640851e01304
|24=>0xe7cf0e14640891e1d68e389c08f5800f8e146428f52683a63c3929902147804c38519023e01a0e38561021479a0e98f0e14540851e0060b3c553891e1c60b14147800e44c1e140428f341cc0b78345051e683844a640851eccd073c4de2514640851e8cb0e14640851e1c5931a94c85
|25=>0x146428f344c70a7c147d434107452a0428f3430f131a280851e1c20e140428f54683e02694c810a3cd602628a810a3cd2d1c345011eb0d074c4d299021479a4c4c515021479a084c6990214780302e28a0a3cd07182cf154e147805a39381123df87202df194e3e39a0e3853e0a3e61a
|26=>0x1c94e01123c38426280851f2cd071658e270a3df873c3928a02147b00e405963c653891e1e08e140428f406838b2c28a851e6821614640891e1c70a02147b35c68398140428f7068398a0345010a3c390162828f341c216320428f486839f30585010a3cd074c4498a320428f342cb25
|27=>0x48683905a2d3851efcd07083929c0214780ca385010a3f21a0e4073e329c48f981c8961c28c810a3cd231c28c811e6cd07207870a0a3e61a0e39e0a3204288341d30e320428f48683e31c945010a3cd073c385010a3d51a0e60b1e4a280851e6a08e146408fae683843c94e010a3c384
|28=>0xe785010a3ce9a0e38501123ce9a0e38519023d91a0e98f0e14f80851e1c80e4e047ac7e683983c280851ed4d07cc39299021479a0f04f3c14640851e1c88e140428f2e683901c6538f5930d071679e25146428f0e2cb1e329c7c7341c6161c280891e1d3183c280891e1d68e140428f
|29=>0x2694c81123cd042628a81123cd0e7c9c08f8efcd07467870a320428f0e9821314640851e0070a021479d006a08e4a28c81123c00426f0c810a3cd041c34c851ec4d071cf8ca71f1e61a0e4060e14047c7341c70a38047c0341cc0e4a2828f62683843c28c811f00d07ca38519023f39a
|30=>0x304de25140428f350420e14700851e005963c70aa70a3c70d146408f6468384463869902147871ce4519023cd074c60f25021479a0e405994e3e39a0eb4f0d140428f0e40b0e14047c7341d31e2628c81123c38e14540851fa0d41087851c0214787165851c0a3c38450640851e68384
|31=>0x840b0a021479a0e4070a023d61a0e2cf1c4e147bf0e38519023ebc0341cb0e146428f52683ad166538f5800d043c640851e90d073e60f0a021479a0e385010a3f49a0eb470d140428f004168b141479a0e2cb1e146448f0e98f1314640851e0061e26945010a3cd1f1c28c810a3cd07
|32=>0x380448f0e38ca71eb249a0e60f3c140428f0e3851902247bb003853e023e39a0fa858a0a3cd073058aa7022479314540851f74d0b269451c0a3cd0e14d00851e90d071c94c810a3d21a0e10b1e1a640851e1c60b3c2848f0e386a532047c0341c70aa60428fbc6838e146428f7160d07
|33=>0x16f128a0a3cd071c6538f8f30d072038ca7123ea07307928a02147800830f0d0214787182cb154e1479a084c51c02147801c2828f62c0d07307928a02247874c58725320428f3498b0e14540851e6b60e7c6538fd66838e146428fb0683841c340851ec0d074c4070a021479a0e1098a
|34=>0x1c345051ec581a0e4c73c146428f626870a3204288341c5d0146448f0e9870a32047b2341c60b4e147bf341cf131a94c810a3cf3c14640851ecc39e2634515021478e4a28c811e6cd071cf05010a3d51a0f0461e140428f341de9e14640891e1c98e1544e010a3c60b3c945051e68398
|35=>0xe1280d320428f0e7870a32147a9341c6132a9c0891e3928ac20428f341c88e1a28c810a3c0161c94c810a3d21a3039f27123ea072c3851502147a4350471902147a4341d68b329c48f004070a02147a4341e08e1a6408f80683983d145010a3c38e329c7c7a8683a614640851eccd07
|36=>0x320428f010470a320479b341c82d1c9c0891efc3911c280851f2cd073e38519023e01a0e4070a7c147cc341cc161a280851e1c2163c94c810a3cd042c78515021479a1c485190214d071c34519021441a0e1081e140428f341d18e7828c810a3c3a62c3851c0214787202cb1e141479a
|37=>0xa3ce9a0e7870a7c147d40fb870a02147ed341c80e4e147cc7e6838e140428f88683ad1c9c08f8efcd072c3851c02147a40e4c73c140428f606870d4a0428f9668384463851c02147878278699021478716786a53214787d838ca71facd07167868a2a1478716385513814787463928a
|38=>0x21478008385010a3e5800e4168e140448f0e3928a021479d006820e140428f406838426f1299021479a20305994e247870858f0a380428f0e6098a02247801c94501123ce9a0e3928a32047b2341e08e140428f966839f1c640851e90d07182caa7123c3911cf0519021479a1cf0501
|39=>0xa3c38b1cf05051ec0d0720385051f30d0708385010a3ec9a0e385010a3d51a0e60b25140428f34305994e3e39a0e9870d4a640851e0130e1a28a810a3c0102c3928a021479a202cb194e247875a393811f2ab1a0e9870a3204288341c20e146408fae683ad3c653811eb00414638519
|40=>0x341c20c2c280851e68398140428f6a683c13c280851e74d078238519023d91a0e9872502147cb341c596329c7c7341c8841c94c810a3cd13140428f96683910838515021479a4d0470a320428f002cb194e247bf0eb470a023e51a0e98596146428f341c20e4a0428f606838e14a0e01
|41=>0x341c98a50640851e6880e14f808f8e6838b1d145150a3cd2d162848f341c72514147b160683841c280851e5cd07164c68a32147800879e0d320428f0e44f0e14540851e68c1e78945010a3c39f1c280851f2cd073c3851c02147a40e7868a320428f661cc0b14247800f0470a38047c0
|42=>0x140428f0e3928a3204288341c80e329c7c798683901678ca7123c38e140428fde683a31c3451902147878210f0a320448f0e2cb0a32247873e5870a2a0428f349898a320428f00309a5140428f34385010a3ed9a0eb458a0a3c01a087a299021478716585190a3d21a0e385010a3dc6f
|43=>0x4c385010a3d51a0e2cf194e3e39a0e7c51902147b3341c59e329c48f7e1c20e14f80891e1c2161a640851e1c60b142478718385010a3d21a0e4060b4e147bf341cc163c280891e1e08e14700851e0058e4a28e051e020843c28c810a3c041083851902247801658f15329c48f1878745
|44=>0xe98c1e140428f001c80c162828f341c59e146428f48683913c4c519021479a262ae010a3cd0782786a5320428f0e305a5141479a0e9898a02147cb341c593145448f345870a680428f341c5934a28c891e68f0e7828c851ec43931c345010a3d81a30280851eccd07164de0a321479a
|45=>0x1a2828f0e4c51902147dd0010b25320428f3410b0a2a0428f342c70d14147b0341c20e146408f36683f01c28e010a3c38b2c7868a3214787202cb0a0a3cd07187898a021478018393851f31f9a0e6280a02247871c280851eb8d0708f0c810a3d99a0e1098d2a0428f3430f13140448f
|46=>0x1ed4d0720305994e3e39a0e4c725146428f626860e14147cc341cf8e1464085106839e1c29a010a3cd071c34c810a3dd80222cf0a321479a0e2c98a7c1479a1c945010a3d51a0e30b0e4a280851e6860b2c653891e1d30e140428f60683e31cf05010a3cd071c345190a3d49a0e3059e
|47=>0x346098aa20428f34405be329c48f0e4059e141479a0e2cb1e4a28c851e6870a2a0428fbc6873c146408f806838e4a28c810a3ef1a5a785010a3c0101658ca71f1cd07174068a32147873e2cb0a321479a0e7874514540851e2cca7123f8875a78501123c3981c352810a3c00c1c28085
|48=>0x329c48f0e7898a2a0448f9c2cca7123c3911c94519021479a1c280851f64d073c4d28a320448f3c4de0a320428f1838ca71f1e61a0e605010a3db9a0e1070a38047c0341c21e140428f3a6838e146408fae6838b3c28c851ed4d073e3070a021479a0e9859e146448f0e2cb1e145428f
|49=>0x1e1c5994e247f30e385010a3cb9a0e7c70a02147aa341d68b4e147bf341c80b3c6538f8e6838e7c653891f3038418792810a3cd072c38519021441a0e6058aa21479a0e609be4e0448f30945010a3d99a0e38519023f39a0e4470a2a0428f34587194e3e3cc341cc0d02147bb341e78b
|50=>0x82385190a3d49a0e7c70a02147b0341d3111c94c810a3cd262238515021479a3c38519021441a0e38548021479a0e9870a02147d9341cf0e329c7c798683843c34a810a3c39816f93891e1c5994e247bf0e2cf0a2a24787167928a32247871679e0a32147871658a994e247901665389
|51=>0x1cf05010a3cd071c28c810a3dd8034b47194e047ca341cc162a9c0851e6880e329c28f98683ad1c653811f1cd073e39e0a320428f341c60b3c2828f341c593145428f343851902247bb341cf0e14f80851e1cb0e140428f54683a61c280851e5cd073e4470a320428f343098a0214780
|52=>0x329c48f001e78e140428f341e70e140428f341e18e14640851e683911c28c810a3cd075a385011eb0d073c4c51902247871c9451902147e2341cb0e2a9c0851efcd183c945010a3cd07303928a022479a0e4072702147bf341cf1338553810a3c98e3855381123c21314700851e68398
|53=>0x1e6838ba028c851e6838e140428f966838c3c38aa7022478718385010a3c0073039e0d140428f341c98e1a94c810a3cd0e7828c810a3d99a0e4c70d14540851e69e9e14640851e683bd1c28c81123cd073c4c5190214780263851902247802038ca70a3ea1a0e60725140428f0068c0b
|54=>0xe5870a2a0428f344070a021479a0e309954e0428f345872514640851e68c16389c0851e1cc0e7c9c28fa86838b3c345190a3c3ad16653851e00d181d145010a3cd07ca38519021479a0e30f0e2a9c0851e0088e1a28c810a3cd072039f194e047c7341d68b329c48f341c20ea264085
|55=>0x4e047c7341e08e4a280851e74d0720b472702147bf341c58e146448f001c60b329c48f0e3851902147b5341c58e38553851e0118e4a28c810a3cd073058f194e0448f0e38ca70a3fa1a0e2cf1c2a9c28f0e2c71c2a9c48f0e5871c4e0428f7e1c70d140428f96683902c787194e0448f
|56=>0x4c4470a320428f341c725146408f806839826280891e683e01c94c810a3cd07c038515021479a0e98725320428f341c5932a653891e6930e14540851e683841c34c810a3c0071658ca7123c3c11c34c810a3cd073c39e2514640851e1c58e1a94c851e6838b1c345150a3cd072c78719
|57=>0x320428f341d30e1a28a810a3cd0720b470a021479a0e58f0e14640891e1d30e140428f966838c3c4cca7022478708385010a3ce9a0e58f0e38553810a3d69e329c08f5868390182cca70a3cd07302ce27123c39826280851e00d1f1c28c810a3cd07182caa70a3cd072c3851c0214787
|58=>0x2c653851efcd07d4385010a3cd074c3868a02147cb341ef8e14640851e6838e14640851eccd074d0470a320428f341cf8e1a28c810a3cd07302c68a0a3cd071c2ae010a3cd07202cb194e1479a0e7871c4e0428f7e1c61e26653810a3c02d1c653811eb001a3140ca702247874c386a5
|59=>0x78945010a3cd07167851c0a3c38b1c28e091e1c70aa2700851e1c70d14640851eccd07164c68a321479a0e2c9be329c28f346058a0a3c01a0e30b0e2a9c0851e6859338653851e0021e4a640851e683843c28a810a3cd077a38515021479a4c1070a320428f001e08e146408f806838b
|60=>0x1d14c810a3cd072c38ca70a3e61a0f8098a320428f341c7194e047ca58683a62628c810a3cd071c3529902147805a78ca702247871c34515021478020b47194e047c7341c60e4e0428f7e683841cf0699021479a0e307194e147cc341d31e1c28c810a3c0071878725140428f341cc0e
|61=>0x14700851e003982c785010a3cd0730280851f54d07821070a320428f006873c1a28c851ec4d071658f15329c28f344059e329c28f341c8163c385010a3cd073e9870a320428f341c70a2a0428fba683c10878519021479a0f0420e14640891e6838b2c28c851e683ad3c653810a3c004
|62=>0x21479a0e39e0d140428f606839e1c653851f30d07084c5190214780350470d4a640851e6838e14640851fa0d073c4ca994e0448fd838ca70a3cd07084c519022479a0e39e0a02147b0341c5994e247f20e609a5140428f342cf194e147bf341c20e14f80851e6838c162828f341c20e
|63=>0xa3cd073c4c68a320428f0e60f0a02147800e30596329c28f341c59e2a653891e1c70a32147b1341d3161c28c810a3cd07164c51c0a3cd073058ca702247872628c810a3ee9a0e60f0d140428f0e7c72514640851e6839816945051e68398a0280851e683a63c3851c0214787187898a
|64=>0x4c2cf0a321479a0e4060e329c28f986838e140428f60683842c78519021479a0e405be329c28f341c613329c0851e007194e0448fea1c613329c0891e1d68e140428f0068b0e14640851e90d0716653851fc4d075a38501123cd071c345190a3d89a0f04725146408f80683981c35281
|65=>0x389c0851e0060e4a280851e683cf16653851e6839e2628a810a3cd131c28a81123cd4e16653851e683ad166538f586838e14a0c810a3cd073c4d28a320428f344c72514640891e68c13389c0891e1c98e7828c810a3cd0418785010a3cd0720587194e147cc341c80c1c9c0851efcd07
|66=>0x329c48f002c73c146428f341c21e1a640851e1c5962a653851e6880b329c28f341c8161c280851e6838b329c28fe6683a61c3451902147800e3851c02147bb341c73e4e0428f7e68384a028c810a3cd071678519123c39018385010a3cd073c3851902147a4341cc137c9c0851e68c13
|67=>0xa3cd182c78e2702147871c653851f30d073e5870a320428f341c20e1a540851e683ad16713851e683913c38519021479a0e605be4e1479a0e2cca70a3df9a0e40f0e329c28f986838b3c28a851e6838b1c28a891e683c13c28c810a3cd07167928a321479a0e2c725146448f341c593
|68=>0x3c38515021479a0e3928a320448f002cb1e329c48f0e2c99c2a9c28f3439f194e047c7341c725140428f606838c1678ca7123c39e1c28c810a3da9a0e3851902147e2341c9994e0428fe400b1e1c28a810a3cd103c385010a3cd072665381123f90720b45994e1479a0e58f0e4a28c81
|69=>0x1e6870a320428fbc6838e14640851e90d073079f2702147878239e0a320428f341c58e78945190a3cd075a2c5051e6838c2c385010a3cd071740ca7123c3842c28c810a3cd07cc38519021479a0e7cf0e14640851e68398a0713810a3c3931cf128a320428f3498f0e4a640851e683a6
|70=>0x5a78ca7021479a0eb47194e0448f341e80e14640851e6838e1a94c810a3cd071c34515021479a0e2c70a381479a0e3851902147dd341c70a320448f001cc1e329c0851e0038e38553810a3c00b2670ca70a3cd07187870a021479a0e4c70a2a0428f34605954e1479a0e4c7251464085
|71=>0x3038e2702247871838aa7021479a0e6058a0a3cd073c4ca994e0428f344c715329c0891e68b0e329c0891e1c5994e147f2341cf0e14640851e0038c1c65381123c39e1c70aa7021478716385150a3cd073c3868a320428f0eb47194e0428f006a08e14640851e6838b1c945190a3cd07
|72=>0xe4c70d14640851e683981c280851e00d072638e194e0428f002cf194e247871678a994e1479a0e2c715329c48f341cb0e329c0851efcd072638e194e0448f0e3928a380428f341cc16329c0851e683981c345010a3cd0720587194e0428f341c80c1c653810a3cd073078e270214787
|73=>0x1e1c715329c0891e00c13389c0851e6839e1c653810a3df9a0e3070a021479a0f0472514640851e6838b1c70ca70a3c0072c78715329c0851e68c0b329c48f341c81e1c653810a3cd071c653810a3fa9a0e5870a320428f341c613329c0851e6838c3c38ca702147800e7870a380428f
|74=>0x1c28c810a3cd071c653810a3f89a0e3868a320428f001c7194e047ac341e80e38653810a3c3ad16653851e6838c2c38ca7021479a0ef470a320428f341c593329c28f006820e1a640851e6838b26653891e6838b3c28c851e6838b1c28c891e6838e1544c810a3cd072c7871c329c085
|75=>0x329c0851fccd071cf068a320428f341cc0e2a9c0851e00d4f1c653810a3cd079c38ca7021479a0e607154e0448f341d68e329c08f586838b2c78ca70a3cd07304c5010a3cd07182cf194e1479a0e98f0e14640851e683983c65381123c3901cf8ca7021479a0e4cca702147f2341d304
|76=>0x1e6838b1c345190a3cd0718787154e0428f341c98e14640851e00d131c28c81123cd071c29f010a3cd073039f27021479a0e38ca702147bf341c5d0329c28f341cf0e14540851e6839e1c94519021479a0e789994e0428f0058715329c0851e6880e329c0851e6839e2665381123c38e
|77=>0x214780346070a021479a0e38a994e0448f341c7194e0428fe46839826653810a3cd071678ca70a3cd071638ca7123cd072638e194e0428f341c70a2a0428f341cc0e2a9c0851e6838e4a28c810a3cd072c7870a320428f341f00e14640851e683a61c28c810a3cd072058f0e329c085
|78=>0x2247800e58f0e329c0851e6838c3c38ca7021479a0e4c7194e0428f0068f13329c0851e683931c65381123cd073c38519021479a0e1070a320428f341c70a320448f341cc1e329c0851e683981c65381123cd071cf8ca7021479a0e78715329c0851e683931c28c810a3cd071c54ca7
|79=>0x38ca7021479a0e38519021479a0e38a994e0428f341c71c329c0851e6838e329c0851e00d071638ca70a3cd073c38ca7021479a0e6071c4e0428f341cb0e329c0851e6838c1c653810a3cd07302cca70a3cd07a038ca7021479a0e38ca7
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x1540005
|5,0=>0x6a60191805e60161805260131804660101803a600d1802e600a1802260071801660041800a6
|6,0=>0x895c21e7085dc21070825c202707edc1f4707b5c1e67077dc1d870745c1ca7070dc1bc706d5c1ae7069dc1a070665c1927062dc184705f5c176705bdc16870585c15a70551814d70519c13f704e1c131704a9c12460475c1167043dc10870405c0fa703cdc0ec70395c0de7036180d170329c0c3702f580b6702bdc0a870285c09a7024dc08c70215c07e701ddc0707
|6,1=>0x8cdc22c7
|7,0=>0x10a2042081062041081022040080fe203f080fa203e080f6203d080f25c3c270eea03b280eaa03a280e6a039280e2a038280dea037370dae036380d6e035380d2e034380cee033380cae032380c6e031380c31c30480bf202f480bb202e480b75c2d580b3602c670afa02b680aba02a680a7dc29780a3e0287809fe0278709c2026880982025880942024970909c23a8
|7,1=>0x185e060f8181e05ff817de05ef8179e05df8175e05cf8171e05bf816e1c5b0816a205a1716660591816260582715ea0574615b985668157dc5578153e054781501c538814c2052881485c5198144605098140604f9813c604e981389c4da8134a04ca8130dc4bb812ce04ac71292049d71259c48e8121dc480711e20470811a20460811620450811220440810e204308
|7,2=>0x2022080081fe207f081fa207e171f6607d181f2607c181ee607b181ea9c7a281e6a079281e2a078281dea077281daa076281d6a075281d2a074281cea073281caa072281c6a071281c2dc70471bf206f481bb206e481b75c6d581b3606c581af9c6b771abe06a781a7e069781a3e0687819fe0677819be066961986065b6194e064b8190e063c718d2062d71899c61f7
|7,3=>0x27f1c9f4827b5c9e58277609d58273609c5826f609b6726bdc9a782681c99a6264a098a8260a097b725ce096b8258e095b8254e094c72512093c824d2092c82492091c82452090c82415c8fd823d608ed8239608de7235a08ce8231a08be822da08ae8229a089e8225a088e8221a087e821da086e8219a085f7215e084f8211e083f820de082f8209e081f8205e08107
|7,4=>0x2b4e0acb82b0e0abc72ad20aad72a960a9d82a560a8d82a160a7e729da0a6e8299a0a5e8295a0a4e8291dca3f828de0a30728a5ca227286dca138282e0a038
|8,0=>0x33ae0ce2933664cd1833260cc0932e20cb0832a20ca0832620c908321e4c7f831da4c6e831964c5c9314e4c4b8310a4c3a830cdcc2a930864c189303e4c0692ffa0bf682fba0be592f760bd492f2e4bc472eee4bb382eaa4ba372e6a4b9372e2e0b8292de64b7272da64b6092d620b5082d220b3f92cda4b2e82c9a0b1e82c5dcb0f82c1a4afd92bd24aec82b920adb9
|8,1=>0x3c424f0973c060ef983bc60ee893b7e4ed693b3a0ec593af60eb493aae4ea293a6a0e9193a224e7f939de0e6f8399e0e5e939564e4c9390e4e3a938c64e289387e4e169383a0e06837f64df4937b20de39376a4dd1937224dbf936da4dad936924d9b9364a4d89936060d79835c24d688357e4d56935364d46734fa0d35934b60d2583479cd15934324d03933ee0cf38
|8,2=>0x44b251239446a51128442a1101943e250f0843a210e08436210d08432210c0842e210af9429a509d94256108c9420e507b841ce106b8418e105b84151d04d74116103d840d2502b9408a501b7404a5009940024ff793fbe0fe783f7a4fd593f360fc493eee4fb383eae0fa383e6e0f9293e264f8093dde4f6e93d9a0f5d93d524f4c83d0e4f3b83cce0f2a93c864f198
|8,3=>0x4d42534884cfe533874cbe532694c76531494c35d30494bee52f384baa52e194b6612d094b1e52be94ad652ac94a92129c84a52128c84a12127b949ca52699498252579493a5246848f65234948b212239486a52119482251ff947de11ee9479dd1de9475651cc9471211bb946ca51ab7468a5199946461189846025177945ba51668457dd1569453a1146844f651358
|8,4=>0x55ca556995586155985542554795501d537954be15278547e1518754421507953fa54f6853b654e585379d4d59533254c4852ee54b2952a654a09525e548e9521dd47e951d6546d85192545b9514a544a851065439850c254279507e14178503a540594ff613f494fb213e394f6e13d384f2e13c294ee653b094ea2139f94e5a538d94e16137c94dce536b84d8a53599
|8,5=>0x5e35d78585df2577395daa576285d66575095d22173f95ce1d72f95c9a571e85c56570c95c0e56fb85bce16eb85b8e16da95b4656c985b0256b885ac216a795a81d69885a3e5687859fe1676959ba16659597256548592e5643858ea5633758aa5622858665610958221600857de55ef8579a55de8575a15ce8572195bf956da55ae8569a159e85656558c95612157b9
|8,6=>0x666659909661e5980765de596e96596595c9654e594b8650a5939964c6192a7648dd91c76452190c86415d8fe763ddd8ef8639a58de8635658cd8631258bb962ce18ac7628e589b8624e188a9620a187b761d1d86d76192585c86152184c8610e583b860ca58299608618189603e580785ffe17f785fbe17e785f7a57d685f3657c495ef5d7b495eb217a395e6e17947
|9,0=>0x6f1a1bbca6ece5bab86e8e1b9b86e4a5b8996dfe9b7786dbe1b6786d7a5b5686d365b4586cf61b3496cae5b2296c629b0ea6c1a1afd96bd61aed86b925adc86b4a9ac996afe9ab696ab65aa496a721a9486a2e5a82969ea1a72869aa1a61969625a50869221a3ea68d65a2c9688e5a1a9684a1a0a8680659f8967be59e69677a19d59673259c2a66ea19b3766aa59a28
|9,1=>0x77e29df1777a9dde2877629dcf9771e1dbf876da5dae876965d9c976521d8aa76065d78975c21d66a75765d549752a9d40a74e21d308749e5d1e974565d0c974121cfaa73c29ce79737a5cd5973325cc3972ea5cb1972a25ca1772661c90972221c80871da9c6d971961c5c9714e5c4a9710a1c39970c25c29770825c16a70365c0496fea9bf0a6f9a9bde86f5ddbce9
|9,2=>0x80ca2028a808220188803e6005a7ff25ff397fae1fe297f6a1fd287f229fc087ee21faf97e9e1f9da7e561f8d87e125f7b97dc69f6897d7e5f55a7d325f4487cf21f3397caa5f2377c6e1f1297c265f0277be65ef097ba21edea7b529ecb97b0a5eb8a7aba9ea597a6e9e91a7a261e81879e25e6f9799a5e5d979525e4c879121e3c878ca9e299787e9e16978329e02a
|9,3=>0x897e2256989366245888eea232988aa22219886262108881e61fda87d261ec8878aa1d99874621c7a86fe21b7886b6a1a58867621949862e6182985ede172985aa21628856a215198526213fa84da612d98492611d78452610aa840a20fa883c660e98838620d98834620c98830260b7982ba60a68827660949822aa080a81de606da8196205ba814a604a8810a203a8
|9,4=>0x22f598bb262e488b6aa2d0a8b25e2c098ae5e2b098a9e629da8a56228ba8a06a277a89be22678
|10,0=>0x94a665218946625118942264fea93da24ed9938ea4db89346a4c8992faa4b6892b2a4a39926a64919921ea47f891d6a46c9918e645c7914e644a99102a437990ba6425990726412a9022a40088fe223ef98fa1e3df98f5a63ce88f1a23bd98ed623ac98e92239b98e4a638998e02637798dba636598d72635398d2e234298cea233198ca6232098c5e630f88c1e22fe9
|10,1=>0x269aa9a466688999f6e674999aaa6619996266508991e663e998da262d9988ea61b8984a66099980625f8997baa5e59977265d39972a65c1996e265b08969e659da9656258ba960a6578a95be65669957a2555995362543a94ea65328
|11,0=>0x9e9a679d99e52678c89e0e677b89dc6a767a9d7a675599d32674399cea673289ca6672099c5e670da9c1266fb99bce26ea99b8666d899b4226c889afaa6b689ab666a49
|12,0=>0x9f6e27d299f2667c099ee227af9
|13,0=>0x27e38
|_,_=>0
def wAt:=mkWire dB 118 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 18
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3c55321d02393c29329d34393c1d1c690239141d329d32391469503d3c941c69141d329d4c1f5005341d32393c943439141d329d46173e6b02392c293c1d3439341d1439503d3c943439141d329d1c0514692c653c1d1c69141d503d1c1d32693c941c69141d329d32693c1d3c291c690239329d1c053e3f0a692c293c1d1c69
|1=>0x3269329d0a693c953c651c690239141d329d0a69023932912c2b3c1d34393c1d0a691c690239141d329d0a6932912c2b0039341d02392c2b329d3c651c690a6902390a69321d02392c29329d3c1d34390a69141d2c650039341d02390a690039341d02393c1d0a6902393c29329d3439321d3c1d0a6902393c29329d34390a69
|2=>0x623b1c6578071a1d329d3c293439321d329d341d02394a69141d3c65329d341d1c963429141d3239329d3e6b02392c293c1d3439141d0a6902393c29329d3439321d0a6902393c29329d3439501532693c941c69141d329d6a693c96141d329d3c293c1d34390a693239329d1c2932693c941c69141d329d143934151c1d141d
|3=>0x34391439141d3c65329d1c05329d5a17324d1c1d8217081d1439329d0a690239206734b5324d1c1d78071c1d4a69141d329d141d329d3e3f0a692c293c1d1c691c1d381d3c29329d32691c694c1d0a6902393c29329d3439341d023932695a17324d1c1d3c1d1c693c29341d1c690239141d329d321d081f34390a691439329d
|4=>0x341d14691c01341d141d3239329d3c1d329d3c651c690a6902391c05202b34b5324d1c1d3e1f02392c293c1d34393c651a1f1c293439146914692c653c1d1c69141d32693c293c1d1c69329d1c1d50153c941c69141d329d78671c95141d329d146982674a39141d329d34391c0578674a69329d32392c2b2669329d1c1d0a69
|5=>0x329d20178267081d1439329d2c2b3c1d1c69329d78071a1d1469329d78671469329d3c653c1d1c2934391469329d826726291c1d329d343978071a1d1469329d329d02392017181d3c651c693e2f02392c293c1d34391c05381d3c29329d32691c695a174c571c351469329d13064a390a693269329d3415023920671cf93201
|6=>0x5a17023934b5324d1c1d4a39141d329d4c671439329d3415329d1c051cf93201341d2c2b3c1d34390a693239329d2c2b329d3c94141d1c691c1d1469329d3c1d3439141d329d301d341d14691c053239329d503d32693c941c69141d329d032a5869329d5a17324d1c1d341d50653c941c69141d329d341d32393c943439141d
|7=>0x341d02390a693239329d39064a39141d329d0a690239a0653c1f329d3439181f1c710a6902393269329d1c1d503d3c943439141d329d321d0a6902392c673c1d34393c1d3c291c690239329d02393c293c1d329d321d343920672c653c1d1c690a6902393c55321d02393c29329d3439783b20172007226708691439329d329d
|8=>0x1c1d329d7c073201341d0a691c1d329d7c073201341d321d1a1f1c2934391469329d2c2b329d321d2c2b0039329d341d02391469329d5a174c1f3239143978074a69141d329d3239783b1a1d1469329d329d20070a691cf93201341d32394c1f0a693c29329d1c6934651c1d4a6b0239141d329d141d3c1d329d34394c1f141d
|9=>0x329d02deaa1d32391a3b1469329d321d3c1d1c2934391469329d4c67341d1439329d8273144d329d1c1d3c1d34390a69141d329d14692c650039341d0239328e081d1439329d4c1f321d329d3c1d1c690a6902391469329d5a173001341d02390a693239329d32390a692c29329d3c1d1c69141d329d3c1d1c690a6902391c69
|10=>0x3c29329d323934391a1d1469329d1c1d3c6534390a69141d329d14013c65329d341d3c29323934390a69141d329d6a693c96141d329d4c671a391469329d8267081d3439341d1439329d0a69341d8267081d1439329d143978071a1d1469329d032a332a58695a17324d1c1d78670029329d341d02391c6934158267081d1439
|11=>0xa6902394a693c65141d329d0a693c653c1d0239321d3439143978671a1d1469329d1c055869329d5a17324d1c1d023914693c1d1c69141d329d321d3c1d1c6902391469329d2c653c1d1c6902391469329d141d2c650039341d02391c05332a58695a17324d1c1d3e070a692c293c1d1c693c95323934390a69141d329d141d
|12=>0x1439329d329d341520071cf93201341d2c2b02393c65329d34392c2b1c01341d329d20173c651a1f1c6902391469501532393c943439141d329d0a6902392c653c1d329d34398217081d1439329d321d02392c29329d3c1d3439806b82174a39329d20171cf93201341d0a692c673c6502393c1d34394c1f141d329d3c651c69
|13=>0x1401329d341d1c690a69341d82674a39141d329d081d4c671439329d328e081d1439329d0239329d20171cf93201341d1c3578671469329d141d4c671a391469329d02e234ed4a3b141d3239329d200778671a1d1c691c1d1469329d32912c2b0039341d02391c1d78671a1d0239329d3c653c1d1c690239146920075a17081d
|14=>0x141d329d3c1d321d1c6902391469329d141d329d34611c651c1d0a69301d341d02390a693239329d0a692c2b0039329d341d0239023932912c2b3c1d34394c670869341d1c1d1439329d8217081d1439329d0239141d3c1d329d34393c1d0a6902393c29329d343978670029329d341d02393c1d323934390a69141d329d7807
|15=>0x341d0239341d1c1d33753c2b329d3439329d181d3c651c690a6902390a6902392c2b3c1d329d34391c1d4c1f0a693c291c69341d1c363429141d3239329d4c670869341d1c1d1439329d3c650a691c690239141d329d20171c1d78671469329d3c953c651c690239141d329d0a6902392067181d3c6534393c1d14691c690239
|16=>0x329d3c651c690a6902393c1d0a691c690239141d329d0a6902392c29329d3c1d34394c1f0a6902393c29329d34391439503d3c943439141d329d2c653c1d1c29343914693506786702391c691a1d1469329d0a8e3465826b081d1439329d2c2b344d1c1d329d82270a69081d329d02392017181d3c651c690a692c650039329d
|17=>0x239321d1c1d3379ba1d3c2b329d1c693a698267081d1439329d3e2b26351c1d1469329d7867783b1a1d1469329d4a690239141d3239329d58691c055a17324d1c1d341d3429081d1439329d321d3c1d1c2934391469329d14691439181d3c65329d34393c960a691c690239141d329d0a693c1d0239321d343920172007181d
|18=>0x341d1439329d3411321d341d1439329d1c05329d5a17324d1c1d78673495141d329d032a58695a17324d1c1d321d02392c673c1d343934121c29141d3269329d141d02390a693239329d39061c95141d3269329d826b8217081d1439329d2c6502392c673c1d343935028217081d1439329d8a391a1f321d1469329d0a693465
|19=>0x5a17324d1c1d3465826b081d1439329d3239341d1a3b1469329d3c2934390a69141d329d321d0a693c29329d1c691c05341d329d1c1d0a696a693c961c69141d329d1c05341d141d3239329d82678217081d1439329d0239a0653c1f329d3439806982174a39329d329d0239181f3c65343932912c2b329d3c1d1c69141d3411
|20=>0x4c1d1a391469329d3c29341d1c69141d329d33893c971c69141d329d3c29341d329d321d1c69321d3c651c690a690239329d1c713465341d02394c1f3c29329d323934391a1d14691c053239329d783b3495141d329d4a693439141d329d3e6b2c29329d3c1d1c6934291c1d0239141d329d1c05321d1c1d1469329d34393269
|21=>0x1c1d086b1439329d321d1c1d086b1439329d1469329d5a17324d1c1d3c291c1d3439141d329d1c35321d1c1d1469329d1469341d1c1d1439329d1a1f14691c053239329d341d3c650239321d34393415206734b5324d1c1d20171cf93201341d2007329d1cf93201341d3c9534390a69141d329d341d32695a17324d1c1d3e07
|22=>0x14392669329d1c1d0a6932ce783b1a1d1469329d34ed4a3b141d3239329d323914693c1f329d1c692c650039329d341d02392c2b344d1c1d329d32392c29329d3c1d34394c1f1a391469329d3c1d1c690239141d329d1c1d329d7c073201341d1a1f1c29321d1469329d3c651c691c1d1469329d3e670011341d1439329d141d
|23=>0x3c292c2b3c1d329d1c691cc178674a69141d329d3e673c951c69141d329d3c1d3439141d329d80698217081d1439329d34391c29141d3269329d14390a69141d3269329d1c1d4c6708691439329d326902392c673c1d34391c6978674a69141d329d2c650a6902393c1d3439328e826b081d1439329d02393c1d329d321d3439
|24=>0x1c1d4a691c690239141d329d1c0520172c651c690a693c1d3c65329d1c693c2934390a693239329d202b34b5324d1c1d1c05206734b5324d1c1d341d1c29141d3269329dca67c01d086b1439329d341520071cf93201341d3e1f2c29329d3c1d1c690a8e826b081d1439329d329d20073c55321d34393e3f78391a1d1469329d
|25=>0x3c651c6934658217081d1439329d323978074a69141d329d82173439081d1439329dca17c01d086b1439329d34398267081d1439329d34158267081d1439329d3e174c1d08691439329d381d3c29329d32691c695a17206734b5324d1c1d15893c971c69141d329d1c954a691c69141d329d4c1f0869143920075a1734b5324d
|26=>0x1439329d3c1d1c6902393269329d14393c943439141d329d141d1c29329d1c1d0a691c29321d329d1c1d0a69201720671cf93201341d3e6b3c951c69141d329d0869341d1439329d341d8267081d1439329d1c95341d0a69141d329d1401341d1c1d1439329d78071c291a1d1469329d201720071cf93201341d329d2017181d
|27=>0x3cd53c961c69141d329d1c651c1d4a69141d329d3269081d341d1439329d32693c1d0239321d34393e1726351c1d329d3506081d1439329d50153c941c69141d329d3c293439141d3239329d023920171cf93201341d26651c691c1d1469329d20173c1d1c691c1d0a693c29329d1c69321d26361c1d1469329d32693439081d
|28=>0x34395a69329d5a17324d1c1d1c0532692c673c1d1c6935018217081d1439329d3e072c293c1d34395a17341d0239324d1c1d2c2b3c1d329d34393c953439141d3239329dbe678a391a1f1469329d324d1c1d341d1469329d329d023934b5324d1c1d1c05329d0a693c1d1c693c29329d341d1c1d34391c1d141d3c65329d3439
|29=>0xa69141d329d329d20171cf93201341d1c05329d34b6324d1c1d3c1d32390a69321d1c693c2b1c1d329d321d343902391c1d141d3269329d32912c2b329d3c1d1c693e2b3c951c69141d329d3c1d1c2934391469329d329d3c651c690a690239146982174a39141d329dba1d3c2b1c69700734ed4a3b141d329d14392c653c1d
|30=>0x321d34393269341d1c1d1439329d786778071a1d1469329d323934390a69141d329d3c293c1d1c69141d329d3c293c1d329d321d1c690bb2a8397c073201341d700734ed4a3b141d329d78671c291a1d1469329d2c653c293c1d329d1c691c1d143934153269329d032a58695a17324d1c1d4a693439141d3239329d341d4a3b
|31=>0x1a1d1469329d321d1c691c1d1469329d806b82174a39329d3e6778391a1d1469329d4a39141d3c65329d081f34390a691439329d34961c1d141d3269329d3c651c690239141d329d4a690239141d3239329d2017200734b5324d1c1d7c070a691cf93201341d1c69341d141d3239329d3c651c2934391469329d3c653c1d0239
|32=>0x1c693e2b8269081d1439329d02390a69341d324d1c1d202b3c55321d1c698217081d1439329d323934391a1f1469329d20177c071cf93201341d1c351cf21a1d1469329d786778071a1d1469329d78071a1d1469329d3e3f4c1d08691439329d3c1f1c69329d0a6902392c673c6502393c1d3439141d1c691c1d1469329d783b
|33=>0x1c69141d329d3e3f26351c1d329d1439181d3c65329d34393e6b78391a1d1469329d3c293c1d329d32691c6902392c653c1d329d3439146914393c1f329d34393e073c953439141d329d1c1d3c650a69321d1c6933893c971c69141d329d4c1f1a391469329d2c2b3c1d1c69329d0a6932397c073201341d2c2b3c1d329d321d
|34=>0x14691c690239141d329dd817a8397c073201341d321d1c6902391469329d34654a6b0239141d329d35064a39141d329d081d1439329d0a69206734b5324d1c1d4c674c1f08691439329d82698217081d1439329d329d20071cf93201341d3429329d3c1d3239343914393c1d3439141d329d14393c1d329d321d3439503d3c94
|35=>0x1c690a693c650239321d34393e1f78391a1d1469329d349582674a39141d329d3439329d7c073201341d7a69081f14392067200734b5324d1c1d34758267081d1439329d2067201734b5324d1c1d2c2b329d3c1d32691c6978671a1d1c1d1469329d141d4c671a391469329d34653506081d1439329d26291c691c1d1469329d
|36=>0x32393439826b081d1439329d341d4c6708691439329d329d341534b5324d1c1d341d82674a39141d329d328e3506081d1439329d1c291c1d4a69141d329d181d3c651c690a69023914393c1d329d32691c691c65341d329d1c1d0a69341582674a39141d329d3e173c951c69329d081d4c6708691439329d2c2b2c29329d3c1d
|37=>0x1c69141d329d78670029329d341d0239329d200734b5324d1c1d961d4c6708691439329d3e674c1d08691439329d1c01341d141d3239329d02392017181d3c651c691c35341d141d1469329d1c35321d341d1469329d2c653c1d1c69141d2c653c1d1c690a690239332a58695a17324d1c1d35018217081d329d5a17301d341d
|38=>0x32393c963439141d329d82674a393439141d329d8269081d1439329d4c6708691439329d023920172c653c1d1c694c1f34111439329d1c1d4c671a391469329d4c1f3411321d1439329d081d3411341d1439329d0a6902392c673c1d34395869329d5a17324d1c1d3c1d02393c29329d34391c2978674a69141d329d32693c94
|39=>0x301d02390a693239329d786778074a69141d329d4c573411321d1439329d02391c1d341d1469329d1c691c291a1d1469329d321d4c1f3c29329d1c691c654a691c69141d329d4c1d4c6708691439329d32692c2b3c1d329d1c69783b1a1d1469329d341d02390a693239329d32698217081d1439329d14393c1d3c65329d3439
|40=>0x3439081d1439329d329d3c1d1c690a690239321d2c29329d3c1d1c690869341d1c1d1439329d38391c1d141d3269329d6e67aa1d1a3b1469329d2a39321d329d341d02391a1f1c2934391469329d2c2b0039329d341d0239706734ed4a3b141d329d1c1d3c943439141d329d329d20171cf93201341d02391a1f321d1469329d
|41=>0x2392067181d3c6534393c1d34390a693239329d144d329d341d34651c1d341d141d02393269329d081d341d1439329d081d3415341d1439329d0a693c1d0239321d34393c6534391a1f1469329d3e3f3c951c69329d2017200734b5324d1c1d181d3c651c690a690239706734ed4a3b141d329d3e6b26351c1d1469329d0a69
|42=>0x1c1d141d329d02390a6978071a1d1469329d1c1d78671a1d1469329d1c65783b1a1d1469329d00291c1d329d341d02393e674c1d08691439329d023920173c55321d1c691cf1783b1a1d1469329d2c670a6902393c1d34390a690065341d1439329d3c1d1c2934391469329d1c710a6902393269329d2c2b3c1d3c65329d1c69
|43=>0x329d783b1a1d1469329d1c29321d1c1d1469329d1c1d0a693c65329d1c69341d3c29329d323934390239181d329d3c65343902392c2b3c1d329d34391c1d4c1f3c29329d34391c1d33753c2b329d343934294a393439141d329d3c651c690239141d329d1c1d4c671a391469329d1c1d321d329d02390a6932912c2b3c1d1c69
|44=>0x329d146902393c65329d34393c2b329d341d1c1d343914393c1d3439141d329d14393c1d329d321d343978671a1d02391469329d0a8e3506081d329d34650012341d1439329d3c1d1c6902391469329d2c650039329d341d02393c65329d341d1c1d343920072067181d3c653439329d32393c1f0a691c6932ce783b1a1d1469
|45=>0x1c691c1d78074a69141d329d329d2007181d3c6534393e3f4c1d08691439329d32912c2b3c1d329d1c69341d1c96141d1469329d4c1f02393c29329d34390239329d1c1d3201341d3e673c951c69141d329d141d3c1d3c65329d1c693c1d3c651c690a69023978671a1d1a391469329d1cc178671a1d1469329d3e0726351c1d
|46=>0x321dba1d3c2b329d1c694a6982174a39141d329dc41d3c971c69141d329d329d301d341d32393439201702392c653c1d3439023914693c1f329d1c6902392c29329d3c1d3439321d34391a1f1469329de41d3c671c690a690239329d2a390a69321d1c691469341d141d3239329d3c653c961c69141d329d02392017181d3c65
|47=>0x1c1d1469329d20172007aa1d32391a3b1469329d34658217081d1439329d82673439081d1439329d35018217081d1439329d02393c963439141d2c293c1d3c65329d1c690a6902393c29329d3439329d3c1d0239321d34394a6b1c1d141d3239329d0a691c051cf93201341d181d02393c65329d34393c1d1c690239141d329d
|48=>0x32394a6b0239141d329d0a691c1d1c653201341d1cf23495141d3239329dca17c01d086b1439329d4c1f3c29329d321d1c69201720071c963429141d3239329da0653c1f1c690a6902391c69321d329d1c1d0a69181f3c651c690a6902393e1f3c951c69141d329d961d4c6708691439329d1c1d34390a69141d329d1a1d1c69
|49=>0x1c690a6902391c69321d329d0a6902390a691c690239141d329d4a691c690239141d329d0a693c1d0239321d34392c653c1d1c690a6902393c570a690239321d34394c573c29329d321d1c693e674c1d08691439329d0239206734b5324d1c1d023920173c55321d1c6920070a691cf93201341d141d329d3e3f2c293c1d1c69
|50=>0x1c69226708691439329d4c1d4c1f08691439329d3c65329d341d1c1d34393e078269081d1439329d786778391a1d1469329d4c1f08691439329d4c1f08691439329d3e3f3c951c69141d329d50653c941c69141d329d961d4c6708691439329d201720073c55321d321d1c2934391469329d0a691c051c653201341d2c673c1d
|51=>0x329d20671cf93201341d321d1c1d32691c691c1d34153269321d34651c1d1439329d3495141d3239329d4a3b341d141d329d58695a17324d1c1d321d3c1d32393439200734b5324d1c1d201734b5324d1c1d78391a1d1469329d02393c65329d34391c1d0239321d329d4a3b0a69141d329d2a69329d321d1c693e672c293c1d
|52=>0x1439329d081f0a691439329d329d341d1c1d3439341d329d1c1d0a697c071cf93201341d341d141d3239329d341d323902390a69a0653c1f329d1c69329d181f3c651c691d454a6b141d329d4c1f08691439329d329d5a17324d1c1d1c69329d1c1d0a693c971c69329d2c673c1d321d1c693439141d3239329d141d0a693239
|53=>0x324d1c1d32391a1f1469329dc01d086b1439329d321d3c65341d1c694c1f1a391469329d20171cf93201341d0a690239324d1c1d3496141d1439329d02393c1f329d34394c6708691439329d3c650a69321d1c693839341d3269329d1c651a1d1469329d1c1d141d1469329d783b1a1d1469329d321d1c1d1469329d1c69081f
|54=>0x341d0239826b4a39141d329d32390a693c1d1c697c2f1c053201341d32690239321d3439321d32690a6902392c673c1d32691c694c671a391469329d2c650a693c1d1c693c1d329d321d1c693c55329d321d1c691c1d3c65321d34393c1d1c69141d329d32693c1d3239343932397c073201341d1c6902391469329d341d0239
|55=>0x1439329d1c35141d1469329d34150239321d1c1d3c29329d321d1c691c29341d1469329d3c1d1c690a6902391c95141d1469329d4a691c69141d329d1c05141d1469329d14690239321d329d20172c653c1d1c6982674a39141d329d206734b5324d1c1d341d329d0a6902393c651c690a6902393c961c69141d329d321d3465
|56=>0x3c1d1c694c6708691439329d34153c651c1d34398267081d1439329d32693c1d321d1c691c695a17324d1c1d181d02393c6534391c05326932390a69329d1c1d1c65341d4c1d08691439329d3c650239321d3439329d3c1d32691c694c1f08691439329d82174a39141d329d1c1d0a693239329d3412141d1439329d321d086b
|57=>0x324d1c1d4c671a391469329d8a391a1f1469329d783b1a1d1469329d081d08691439329d26351c1d1469329d14691c053239329d33753c2b329d1c6902392c653c1d343932692c673c1d1c691c1d3c65341d1c69341d5a17324d1c1d32393c1f0a691c691c35141d1469329d1c35321d1469329d329d34b5324d1c1d329d0a69
|58=>0x3239329d1c6902393269329d0a6902393269329d4a6b141d3269329d1cf21a1d1469329d1c051c1d1469329d02391c1d3201341d341d1c053239329d3c1d3c65321d1c691c1d3465341d02393439141d1439329d1439329d321d3439081f321d1439329d3411341d1439329d8217081d1439329d02392c673c1d3439329d34b6
|59=>0x341d0239301d341d3239343914391a1f1469329d20072c653c1d34391c1d086b1439329d58695a17324d1c1d1c1d1a391469329d341d141d1469329d2a390a69321d1c69321d341d1469329d201734b5324d1c1d3c652c673c1d1c691c291a1d1469329d2007181d3c6534393c29329d341d1c69141d3c65329d1c693495141d
|60=>0x3239329d2c6702393c1d34390065341d1439329d1c7102393269329d1439341d3269329d3c1d329d3239343932391a3b1469329d081d341d1439329d78071a1d1469329d3c1d0239321d34393c550239321d34392c653c1d329d1c694c1d08691439329d321d3c2b329d1c693439081d1439329d081d0a691439329d0039329d
|61=>0x323934393c951c69141d329d0239141d3239329d32393c1f329d34393c29329d32691c691c1d3c65329d343978671a1d1469329d20073c55321d3439341d1c1d1439329d1c95141d1469329d26361c1d1469329d1c1d0a69321d1c69a8397c073201341d1c29329d1c1d0a6978671a1d1469329d3c671c690a6902391c1d141d
|62=>0x324d1c1d2c2b329d3c1d1c690239e41d3c673439301d0a693239329d78071a1d1469329d82174a39141d329d3429141d3239329d1c691c1d1469329d341d329d323934393c6502393c1d34390a690239321d343978071a1d1469329d3c293c1d329d1c691c1d02393269329d344d1c651c1d0a691c1d3c2b329d34393429329d
|63=>0x141d329d1c1d3439141d329d141d329d1c1d0a6934651c651c1d0a691a1d1c1d1469329d14393c65329d343920072c653c1d34392067181d3c651c6902393c29329d34392007181d3c65343978671a1d1469329d14393c1d329d34391c051cf93201341d1c71341d34651c1d7c3b0a693201341d34611c651c1d0a69329d341d
|64=>0x321d34391c35341d1469329d1c96141d3269329d20671cf93201341d14393c1f329d34391c69329d0a690239181d329d3c651c692c2b3c1d329d1c691c1d1c653201341d1c65341d34651c1d1c71141d3269329da0653c1f023934391c1d329d321d3439321d329d1c1d0a690239181f3c6534391c055a17324d1c1d3c941c69
|65=>0x324d1c1d4c1f3c29329d1c691c051c653201341d02392c673c1d343920073c55321d3439329d0239321d3439321d329d0a6902394a393439141d329d1c690239141d329d141d329d0a690239341d1c1d02390a690029329d341d02391c2934391469329d3c1d0239321d34393c550239321d3439329d2c653c1d1c693c570239
|66=>0x321d1c1d20171cf93201341d78674a69141d329d3c651c690a6902393c961c69141d329d3c971c69141d329d3c67341d1c1d34393c1d329d321d1c69181d3c65329d1c693c671c691c1d0a69023934b5324d1c1d3c1d1c69141d329d3c1d326932393439200734b5324d1c1d2c29329d3c1d1c691c29321d1469329d02393465
|67=>0x3c1d1c691c691c653201341d4a694a39141d329d4a690239141d329d329d0239324d1c1d3c1d3c65329d1c693c1f1c690a690239344d1c1d1439329da0293c1f329d1c693c951c69141d329d1c653c1f32691c691c1d4a69141d329d3c291c69141d329d3c29329d321d1c69341d0a69141d329d0a6902393c1d343934650239
|68=>0x329d34391469329d341d324d1c1d081d1439329d0239141d329d301d323934393415324d1c1d3c1f329d1c69141d1469329d321d1469329d02393269329d3c2b329d1c69341d0a69329d341d323934393269321d341d1c0534651c1d3c65329d1c69329d321d1c1d1c053239321d1c1d141d329dba1d3c2b329d1c692c2b329d
|69=>0xa6902390239321d3439321d0a6902392c673c1d1c690a6934651c1d141d3269329d3c1d3239343932391469329d2c653c1d1c69181d3c651c69326932393439326932390a693c65321d1c691c053239329d1c1d321d3439321d1c1d0a6926691c1d0a6902393c673439329d341d1c690a693c651c69321d32691c690239321d
|70=>0x34390239329d329d0a6902394a6b141d329d3c1d32691c690a69321d341d1c6534651c1d2c673c1d1c69329d3c651c694a39141d329d3465341d02393c1d321d1c69323902390a693c55321d1c691cfa3201341d329d3c1d1c691c7134651c1d3c65341d1c69329d32691c691c1d1469329d329d1c65341d341d34651c1d1c69
|71=>0x1c69181f3c651c690a693239321d5a17324d1c1d02393c1d34391c1d3239329d02393c6534393c29329d1c690a69323934391cf93201341d3c671c1d343908691439329de41d3c671c69341d1469329d5a17324d1c1d3c1f32691c690239324d1c1d3c1d3c651c69081f1439329d1c1d341d023914691439329d1c1d02390a69
|72=>0x329d1c69086b1439329d08691439329d2c653c1d1c6902391469329d3c65321d1c69341d1c1d329d329d1c1d0a69329d3201341d1c653201341d2c673c1d1c693c1f02393439329d321d1c691c69141d329d341d1c1d34393c1d321d1c691cf93201341d1c691c1d0a693c57321d1c691a1d1469329d321d1c65341da0653c1f
|73=>0x341d02391c691c6532693c1d1c693c651c691c6502393c1f1c69341d0a693c1d1c693c651c691c1d341d1c1d34391c1d0a69329d1c691439329d0a69329d3239343932390a693201341d321d1c691c1d329d321d341d3239329d321d0a693c671c6932391c1d023934390a69023934651c1d321d329d3239321d141d329d3c1d
|74=>0x329d321d3269
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1c580d6c065602fb0161c000000000000000000a4c00000000000000000000000000139000000000000000000090c0417000000e9c00000000000000d5405ce00000168800000000000000000099c00000000000000000000002060000000000000000000cb8000000000136006380000000000000033000000000000000000001800000000
|6,1=>0xeee0000
|7,0=>0xb4b000002ca816050000056982aaa14f60a708529028aa13f609cb04cd825ca0000094a80000248a11f5000000000234a11460882042d420ca00000000040181fe20fb4000003d9400000f240763039d41ca40e0506d30351819cc0cc2063303018176a0b56000002c50156c0000053282818134c0946048200000000000000453021180fcc0000
|7,1=>0x1169089d8448600000000000000000222210ea88614000000001093083180000206610120804400001fb60fba07c583d6c00000f2b00000000000000efb076943a8c00000e730721838e21c52000007050000000000ddb06e0c36a600000d7b06a5834e41a160cea065d8322c18b60c2b05fd8000017e10000000002f481764000005c90000016f3
|7,2=>0xc1045fcc000017d20bd1800000000177a8000000000000174b0000000002e3600000b7585aec2d2516630b1d400002c1615e28ae4c566c0000157a0aa5854a82a1414db0a558520a28a6142a800004fec00000000000004f2c2736000009bd04d6826650000000004c2a25d412e0895984a6624d6123b0000000002416000008ed846ac22f6
|7,3=>0x1f0b0f6d87aac00001ea08f41000003ca61e230ef98770c00001d930eb1874cc00001d0a8e6d872e839251c630e1d4000038161bea00000000037c11bb3000006e4836e41b43000006c8835f500000d6586b0235261a6a80000690a34351a090cf8c670c0000199a8cbd065c20000194a8c8d863ac000018ca00000626c000018818c2d400003056
|7,4=>0x22a311398892a4436220910ed886ac0000217b00000852c423600001079483a200000000105d8822c40d42051901187fcc3f861f930fb1800003e75
|8,0=>0x2c5a96194b02a57c52bba95c94adaa56852b1a95794ab2a55452a82152d4a8ca541529e294dd400005325296a94a14a46a51e528ca94550a22850c5283a940949faa4f85279a93b949d2a4e4526fa936949aaa4d052662131d4984a4bd525c292cd495e84aa5252a92814936a4965248a9231490ea482523ea91e148e6a46e5234a919148bea45a5
|8,1=>0x35f29ae54d68a6af535529a954d40a69c434ba9a494d1aa6885341a99f94cf2a6745337a99a94ccaa660532da99594ca2a00003262991d4c88663f531d298d90c62a62c53142188d4c3ca619530a2983d4c14a6055300297ed4beca5f152f6a17a14bc6a5de52eca97514b9ea5ca52e2a97014b76a5b652d8a96b14b4ea5a342cf296690b2aa5905
|8,2=>0x3fa21fbd4fd687e653f0a9f714faea7d253e6a9f214f86a7be53dca9ed14f5ea7aa53d2a9e814f36a79653c8a9e314f0ea78253bea9de14ee6a76e53b4a9d914ebea75a53aaa9d414e96a74833a1a9cfd0e74a735539829cb10e4ea723438f29c654e28a70f538529c154e00a6fb537b29bc54dd8a6e8437221b7d4db4a6d5536829b34cd90a6c35
|8,3=>0x490aa471522ea9125486aa4251208a8ff547d2a3d551e0a8eb54741a38d51bca8d9546a2a33d5194a8c554602a2ed516ca8b154562a2a1114a68a0544daa2595122a88c5443aa20950faa879443a2a1bd50d4a86554302a16d50aca8515426a21251088a83f541d2a0d55062882d44142a08d503ca819540aa20415016a00004032a0054ffa87f85
|8,4=>0x52aa29415496aa465520aa8f1546eaa325516aa8a15446aa1e550caa851541eaa0a5502aa80153f6a9f654f8aa7b153cea9e254eeaa76153a6a9cf44e52a7155380a9bb54db2a6c9135c89a954d2a26815336a99654c8aa631530ea98254beaa5e152e6a96e54b4aa59152bea95a54aaaa5451298a94750000250d127ca93a449aaa4c15256a9265
|8,5=>0x5c72ae255708ab7f55bd2add556e0ab6b55b32ad8556b8ab5755a92ad355690ab43559fa2ce9566aab305595aac9956448b1d558c2ac4d561cab0955822abfd55f68af65578aabb155ceaae2556eaab6155a6aace5564aab1155808abb555ba2ac9555aaaa85551aaa795532aa945547aaa29550aaa80553daa9d954e2aa6c55342298d54bcaa595
|8,6=>0x65fa32ed196cacb156562b29d59468c9f464d2b2555920ac8c4643ab20958faac785639ab1b958d2ac64562fab16958aaac505625ab11958884c40461dab0d95862ac2c5613ab0949840ac1b560b2b0455818ac0756012aff557f64bf655f8aafb157ceabe345ef2af6557a8abcf55e52af155780abbb55db2aec55758aba755d12ae755730ab935
|9,0=>0x6df236e91b6c8db246d7236a91b4c8da246cf236691b2c8d9246c7236291b0c8d8246bf235e91aec8d7246b7235a91acc8d6246af235691aac8d5246a7235291a8c8d42469f234e91a6c8d324697234a91a4c8d22468f234691a2c8d1246872342cda0e8d03467fa33ed19ee8cf34677a33ad19ce8ce3466fa336d19ae8cd34667a332d198e8cc34
|9,1=>0x75f23ae91d6c8eb2475723aa91d4c8ea2474f23a691d2c8e92474723a291d0c8e82473f239e91cec8e724737239a91ccc8e62472f239691cac8e524727239291c8c8e42471f238e91c6c8e324717238a91c4c8e22470f238691c2c8e124707238291c0c8e0246ff237e91bec8df246f7237a91bcc8de246ef237691bac8dd246e7237291b8c8dc24
|9,2=>0x7df23ee91f6c8fb247d723ea91f4c8fa247cf23e691f2c8f9247c723e291f0c8f8247bf23de91eec8f7247b723da91ecc8f6247af23d691eac8f5247a723d291e8c8f42479f23ce91e6c8f32479723ca91e4c8f22478f23c691e2c8f12478723c291e0c8f02477f23be91dec8ef2477723ba91dcc8ee2476f23b691dac8ed2476723b291d8c8ec24
|9,3=>0x85f242e9216c90b24857242a9214c90a2484f24269212c9092484724229210c9082483f241e920ec90724837241a920cc9062482f2416920ac9052482724129208c9042481f240e9206c90324817240a9204c9022480f24069202c9012480724029200c900247ff23fe91fec8ff247f723fa91fcc8fe247ef23f691fac8fd247e723f291f8c8fc24
|9,4=>0x1102487f243e921ec90f24877243a921cc90e2486f2436921ac90d2486724329218c90c24
|10,0=>0x8e19c700e37a71ba38db9c6d0e36271ae38d59c6a0e34a71a238cf9c670e332719638c99c640e31a718a38c39c610e302717e38bd9c5e0e2ea717238b79c5b0e2d2716638b19c580e2ba715a38ab9c550e2a2714e38a59c520e28a7142389f9c4f0e272713638999c4c0e25a712a38939c490e242711e388d9c460e22a711238879c430e21271063
|10,1=>0x123e391d9c8e0e46a723239179c8b0e452722639119c880e43a721a390b9c850e422720e39059c820e40a720238ff9c7f0e3f271f638f99c7c0e3da71ea38f39c790e3c271de38ed9c760e3aa71d238e79c730e39271c63
|11,0=>0x24f65279293b949d4a4e652712937949b4a4d65269293394994a4c65261292f94974a4b65259292b94954a4a65251292794934a4965249292394914a48652412
|12,0=>0x2504328119400c9fc64fc327d1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 17
def pmP:Nat→Nat
|0=>0x400000000004a00000000084000000000b00000000015000000000280000000004c000000000970000000012000000000200000000003800000000067000000000900000000010000000000180000000002f0000000005000000000080000000000c000000000170000000002c0000000004400000000080000000000f0000000001c000000000240000000004000000000070000000000800000000008000000000080000000000
|1=>0x60500000000c01800000018010000000300100000006000000000084a00000001084000000021000000000405000000008020000000100200000002001000000040000000000440400000008140000000100000000001c0c000000020c000000004000000000051900000000a0000000001280000000022c0000000042f00000000822000000010400000000204000000004040000000080400000001000000000014000000000220
|2=>0xe2080000001c00000000024000000000469f000000088e0000000110140000002202000000044010000000880000000010ac000000021180000000412800000008140000000101c0000000201f000000040300000000805000000010080000000200a800000040100000000801a0000001001c00000020008000000400000000006a100000000d4180000001a800000000311f0000000622e0000000c458000000188100000003101
|3=>0x1881e000000306dc000000609f8000000c13b0000001823e0000003017c00000060100000000c01f0000001802c0000003004800000060080000000c0080000001800800000030000000000588f8000000b1070000001620c000000280a0000000460f0000000882000000010560000000204a000000040110000000801900000010026000000200480000004008000000080030000001000400000020004000000400000000007106
|4=>0x30140000000600c0000000c010000000180070000002c52000000048240000000825000000010227000000204400000004028c000000805000000010020000000200000000003d47c000000788f8000000d41f00000018d7e0000003187c00000062d78000000c51f000000189fe000000312fc000000624f8000000c47f000000188e60000003115c000000621f8000000c43e0000001883e00000031074000000620d8000000c417
|5=>0x5086e000000a1044000001400800000028000000000488220000009101c0000012200000000240100000004080800000080000000000fbdf8000001e03700000039d7e00000071afc000000e3580000001c6af00000038d3e000000718fc000000e3180000001c61f00000038c1e000000712fc000000e24f8000001c43f0000003845e00000070880000000e05b80000018eb00000003085c00000061024000000c05f800000180b0
|6=>0x216a3e0000042c47c000008428f800001081b70000020e208000004100000000081883800001031040000020000600000400000000003a4080000005c4bf000000b893e000001710fc000002e20f800000541bd00000098d7e000001318fc000002630f8000004c43f00000089d7a00000111a7c0000021883800000430040000008017a000001000140000020000000000380000000005887e000000b02dc000001600b8000002c000
|7=>0x2b883e000005318fc00000a62df8000014c59f0000029897e000005312e400000a624f8000014c4990000029887e0000053107c00000a1adf8000014359f00000286a3e0000050c67c00000a02df8000014059f00000280a32000005013fc00000a025f8000014049f00000280932000004f18ac00000900000000011c61f00000236b7e000004680dc000008c25f8000011802b00000218b5e000004312fc000008624f8000010c41f
|8=>0x8000b0000010000400000200000000003cc43f0000068ee3e00000d1cc7c000018e21f8000031c41f00000618c3e00000c310fc000018620b8000025c835000004b8b7e0000097107c00001263df8000024c59f0000048947a0000091167c000011621f800002240370000043883e000008506a0000010635f8000020c61f0000041897e0000083127c000010620f8000020c0bf0000040822a000008100a000000e00df800001c01b1
|9=>0x889c7a000010f2840000021e21f8000043c2100000087805e000010e20c8000021450000000428002000008488360000108000c000020e71f8000041cc3f0000083947e00001062800000020671f8000040ccbf0000081987e00001032080000020621f80000408470000008108b000001020000000020221b800004042370000080842000001002a4000002002010000040040000000800400000010002c0000020004800000400070
|10=>0x105997e000020b18fc000041625f8000082c43f00001048400000020900c0000040e35f80000818ea70000103000000002051ac000004082500000080440000001008040000020012800000400200000008000b80000100012e000020000440000400008000008000070000100000000001b720f4000033641a8000062c8b700000c3987e000018338fc000030605b8000050c4ff000008e9020000011730fc00002284080000044cc3f
|11=>0x2008400000040002400000800008000010000000000187887e000030f0048000061a00900000c2ccbf0000185946e000030a0000000060e71380000c1c41200001819c7e00002cf10ec000058611f80000a2c43f000012b8876000025310fc00004a025c800009401b90000125887e000024612ec000048625f8000087c43f000010e8000000021b18fc000043621f8000086463d000010b986e000021512f4000041e25f8000083c43f
|12=>0x40100200000801080000010020080000200400000004001060000080012600001000208000020000f800004000130000080001c00001000008000020000000000327087600006091adc0000c082518000143c43f0000287082e000050312400000a04018000014000b00000223887e000044618ec000088c01d800011084bb00002058c280000407121c000080c003800010180000000202896000004043adc000080400080001008000
|13=>0x48089700000900284000012000780000240005000004800020000088332dc000109631f8000212821000004240002000084118ec00010800000000203ce0700004078c7e000080d18bc00010161080000202841d00004048c0800008091010000101211f80002024004000040480000000807009c000100e00000002010000000040188fe000080310fc00010062138000200c0bf0000401802e00008030040000100600000002008411
|14=>0x60504280000c0730fc000180e25f8000301c43f0000603817e0000c0630dc000180631f8000300c4bf0000601887e0000b06125c000160625f80002928210000052104200000a0b08d000014161120000282c21400005058420000090712fc000120835f8000240ccbf00004819520000090313fc000120627c0000240c4bf00004818920000090311fc000120623c0000240c4090000481880000009030a40000120405f800024044f8
|15=>0x8018d3e000100318fc000200628d8000400c4bf0000801893e000100310fc000200615f8000400a41b00008010000000100002a000020000400000392c43f000072109760000e0f10fc0001c182418000382c6370000705887e0000d0720dc0001a087038000340ce3f0000681996e0000d03325c0001a0661f8000340cc37000068181600000d0302400001a020580000310c4bf0000621887e0000c0b18fc000181611a0000302c214
|16=>0x841837e0001056907c00020a630f8000414c41f00008236a3e0001046c47c000208d20f8000411a23f0000823407e0001046127c00020862df8000410c59f0000821883e0001042d67c00020858cf800041083bf0000821037e000101710fc000202c0058000404c4b70000809883e00010111a7c000202205e800040420110000805897e000100b0afc000200e34f8000401c63f0000803896e000100710fc000200e20f8000400c6bf
|17=>0xc01006e000141002dc000280e05f80004a2c1bf00009418970000124206ec000243621f8000483c43f0000907837e000120e00fc000241631f800048080b800008818b5e00010d1507c000218e30f8000431a41f00008438f7e00010871afc000210e34f8000421c61f00008438b7e0001087107c000210e15f8000420f59f0000841e33e00010831e7c00021062df8000420c59f00008418a3e0001083127c000210620f8000420c3bf
|18=>0x20018c3e000400312fc000800624f8001000c48f0002001887e0004003107c0008003804000100070060002000e00000040001640000709611d8000e10c43f0001c210076000305688fc00060ad00f8000c14c63f00018298472000305300ec000609621f8000c12c23b00018250076000304318fc000608621f8000814311f000102304760001e0b18dc0003c1621b8000701803f0000e01897e0001c0310fc000301631f8000600c43f
|19=>0x2041a57e000408348fc000810651f8001020c61f0002041893e0004053167c00080a625f8001014c4b70002029893e000405310fc00080a620f8001014059f0002028093e000405010fc000808e24f8001011849f0002023087e0004043d6fc000808625f8001010c49f0002021887e0004043105c000802e41f8001005c43f000200b883e0004013107c000800e34f8001001c63f0002003887e0004005de4000080092c80001000f5bf
|20=>0x2681986e0004c4312ec000988621f8001301c43f00026018c7e0004c0310fc000920625f800124040f0000248080600004803009c000880e11f8001041c82f0002081997e000410330fc000820621f8001034c41f0002063a47e00040c3dc7c0008186b0f8001030c61f0002060800e000409712fc000812e24f8001024c59f0002049883e0004091127c000810e34f8001021c4bf0002043893e0004083dc7c0008106b0f8001020d41f
|21=>0x4001ea3e0008003c47c001000621f8002000c41f0004001883600050c3507c000a10e35b8001420d61f00028418d3e0005083187c000a1062cf8001420c49f0002823896e0005043127c000a08620f8001410859f000280be23e0005017907c000a02f05f8001405c00f000280b081e0005016007c000a02620f800140460150002803e23e0005007907c000a00f11f8001401c69f0002803883e00050070afc000a00630f8001400c41f
|22=>0xa80bc83e0015007d47c002a00f20f8005400f11f000a041ec3e0014083c07c00220ad20d8004411b51f000882162260011002927c00220050098004010e41f0008009e23e0010012c45c002000d24f8004000c43d0008001883e001000310740020005a8f8004000b117000800100080010000c4080018186b0f8003030d0170006001a83e0009083527c001210680f8002034561d0004068a02a0008043d47c0010083a8f8002001d69f
|23=>0x60028083200c0050103c010818e20f8021030c49f004202b887e0084057107c010808e21f8020034c41f0040061897e00800c212fc010008c2078020010c49f0040021883e0080042127c010008420f8020010049f00228088d3e0044013187c008802624e8010404c49f0020809893a004101302f4004101621f800820240040010005887e0020008001c004000621f8008000c01f001000108360020000009c00400000038005409e03f
|24=>0x202002ef2c0404003d47c0808001bcb0101000359602008438f3e0401047167c080202634f8100021c69f0200029893e0400050d67c08000a02cf8100011c49f02000236b3e0400007de7c080000e34f8080434c41f0100849883e0201091187c040202e31f8080015c63f010002b8c3e020001718fc0400022a0f804004280020080081887e010010210c002000162100040000c437008000188660100003105c01800a624c80300140499
|25=>0x18005007147c802000620f8804419a03f1008823483e1004083047c100010238f8130014c49f0260028093e0480047127c090008c24f8101421c69f0202823893e0404053d47c08080a624f8101010f51f
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x1000000050681d02414000000000003c0000000000000000e0000000000044150000d000000001a02c0004800000000000100000000000000500000000000bc000000f01c000000004400000000000500000
|7,0=>0x24c9d24c00000000017c130030003340d7d000d70691d0024f184eb4000028c0000000bf811054001100d6503b0000900030b48c507c00468110598606a471444112df900038000002f020000480cc93150004a84e000420142e0e009024d9258f1014000140003c3100000044a2184bd024000001c2d82100061000618204e0580566c088340e064c6185200004806000014190544d35800000000454545000
|7,1=>0x271bb5b0000e1a80000410d913900034252070000d8011841a055b5000c712000000b62e40018461b30000259f000670cdac0e4001841e0ecc5180000241a0e00003c6895800184000500052cd80002c0011d54000368ec000006840000000b5c000002a0005313c37b2805002e105cd606c00120171211e0045a1c83d3a40009c000000019098001231841a00000078614767224e48b88000016d0028bb0c9c
|7,2=>0x1e474546780ee6054800040000a46d0001e2d80000199134940b6d53d4013c81100013
|8,0=>0x4eaf64c1639a43c12526c11676d0720d442b415a1b023c0c8320d9b1000002875088c874c9a4463e014705dd251800608e5700c010995425463521494b2f02e31c18e6f32c24305a437895b89215aac86a90a16175a5184759c17b653acaa836f2a012ac0119a000836f67a8418d6e19c56c0664d89aa9388fd9765b0c1264c4d8e1534dc1e1be70b2c6aecbbd5289387508c71b39a3be07b15c626ba55b6139
|8,1=>0x740f41af0d2ed4d198019d0011cec849040c083415ae867cc063df3af29e45557314c970cc6180a12649f211801b801046617a857a18275f897b10a60061e014619107f005a0120833e8007f5f1679db5345a7dd3f432346e07fb0606236164cee3824501485f205a10354a20dad592da39aef295720040a2c4fd1942b0903ab4ef1b2c25b6494b9883a561a3edc97d8047453c9c5802f08248acd8f445661a5
|8,2=>0xab64615c4254ec5012596492ba3c2714f1513059600e32c15829da01752960ce78b832baae46adee44d8c8449e47c7c5da3a6f2fb11d6f121a9200ea09ed40072843d824040d10e0c4ed714c8d5c85025343ec8883605413b4147363720e18768a02dcaa1826a944be1d58a782976c40c1557f940691a8bfc20026eed16548768875c9edc054b8411b7af85720ca1b59e67943fc5aca0005daacc449eafc1475
|8,3=>0x1409006290084a6edbb15c780985ea7e32bfe795b5b69ccf33e07a011f80fb297d42592f0e674822003b308eba28ef53886589b20eda34bb06b3951530eeace3646e6e5548000d4ea884662010a5b00
|9,0=>0x74af74710d61d8ba364a8b6315e293a45cb4f7252d1c4698851d9859507dc4d0888adfbade679ea733dc644307a16df84b1081085ac10971d6083973a49d5bea997b0ec641cf7d29d26d371c0fe3c15ca3174c66bbbf290171a7c7664246b45662db25e4866424b6b7638608795f38888a2220785f26be9c4c5402cb0ab0a35874891f8c3216e03514d2ae078e491a0e8751e4157adea92bfcb84a856f95967f
|9,1=>0xbf6dbb9cfc5508a972b9982ed86d568b4830a1e88c1c5aeaf39626d9d93d5a56ec2db97ae7037cb5385e55c2804c0fb89cadada2c8f0e1a12683772b229615a30f6ce331184351042b94a4a3a22c250ea94b1bcaae76579915dd8031a9debd16d19828aa90d4f935fc6ea2b6c2c74d57a75e89af142ba7018e3269f60f51a039013e77f23c82620325e4e943396a377ac04d32d739f0aba9b1be23782c67023b
|9,2=>0x8a216b61ddd485e2f3e0b322cba889d16fe9859b17
|10,0=>0xb24bdc8c7de3ad4ae34a7eae0833865e574af9949234c8978aa12248caa6ddc5202851cabb282975cc225d9b3d068671b4bce87a4ff388f757318bba2ac461f5ed17c921cc78902ca2489907771fe8b0f99b275c45125c20590b128a222c3eb59268399ccabd08f43a7b9add8a993d5aea6ab88a7be9a4588a339ff9f11889663ac560
|11,0=>0x884af89213224cdc46242b0a93448a4bccc7ee0ba065d2a25f7ea6622601384f642e5ba815c
|12,0=>0x2165a4148e38089
|13,0=>0x83
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 10 (j%128);fld (pmP (k/32)) 43 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_253 12 roots_253 ops++addP pm 2 dom_251 12 roots_251 ops++addP pm 3 dom_247 12 roots_247 ops++addP pm 4 dom_127 11 roots_127 ops++addP pm 5 dom_231 9 roots_231 ops++addP pm 6 dom_151 6 roots_151 ops++addP pm 7 dom_159 8 roots_159 ops++addP pm 8 dom_143 6 roots_143 ops++addP pm 9 dom_63 9 roots_63 ops++addP pm 10 dom_239 11 roots_239 ops++addP pm 11 dom_215 9 roots_215 ops++addP pm 12 dom_43 5 roots_43 ops++addP pm 13 dom_77 5 roots_77 ops++addP pm 14 dom_223 11 roots_223 ops++addP pm 15 dom_191 11 roots_191 ops++addP pm 16 dom_95 9 roots_95 ops++addP pm 17 dom_103 6 roots_103 ops++addP pm 18 dom_189 10 roots_189 ops++addP pm 19 dom_245 11 roots_245 ops++addP pm 20 dom_219 10 roots_219 ops++addP pm 21 dom_175 9 roots_175 ops++addP pm 22 dom_199 6 roots_199 ops++addP pm 23 dom_119 9 roots_119 ops++addP pm 24 dom_183 9 roots_183 ops++addP pm 25 dom_167 6 roots_167 ops++addP pm 26 dom_207 9 roots_207 ops++addP pm 27 dom_243 11 roots_243 ops++addP pm 28 dom_111 9 roots_111 ops++addP pm 29 dzo_171_4 6 roots_171 ops++addP pm 30 dzo_205_2 6 roots_205 ops++addP pm 31 dom_55 6 roots_55 ops++addP pm 32 dom_237 10 roots_237 ops++addP pm 33 dom_235 10 roots_235 ops++addP pm 34 dom_87 6 roots_87 ops++addP pm 35 dom_221 10 roots_221 ops++addP pm 36 dom_31 5 roots_31 ops++addP pm 37 dzo_59_4 6 roots_59 ops++addP pm 38 dzo_107_4 6 roots_107 ops++addP pm 39 dom_249 10 roots_249 ops++addP pm 40 dzo_237_2 7 roots_237 ops++addP pm 41 dzo_93_2 6 roots_93 ops++addP pm 42 dzo_109_2 6 roots_109 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_171_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_205_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_59_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_107_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_237_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_zo_93_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_zo_109_2_77 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 17 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 66 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 66 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 284 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 28 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 284 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 384 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_384 : ∀ i, 384 ≤ i → i < 448 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 384 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 448 → Z 8 i = true := (range_split (range_split z8_0 z8_128) (range_split z8_256 z8_384))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 256 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_256 : ∀ i, 256 ≤ i → i < 273 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 17 256 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 273 → Z 9 i = true := (range_split z9_0 (range_split z9_128 z9_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 105 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 105 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 30 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 30 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 6 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z13 : ∀ i, 0 ≤ i → i < 1 → Z 13 i = true := span_ok (by decide +kernel : span (Z 13) 1 0 = true)
theorem checked (s:Nat) (hs:s≤13):∀ i<NN s,bar dom_255 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [7, 4] }, { op := GateOp.or, inputs := [1, 6] }, { op := GateOp.or, inputs := [7, 6] }, { op := GateOp.or, inputs := [3, 4] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.or, inputs := [10, 12] }, { op := GateOp.or, inputs := [0, 9] }, { op := GateOp.or, inputs := [5, 8] }, { op := GateOp.or, inputs := [12, 2] }, { op := GateOp.or, inputs := [4, 10] }, { op := GateOp.and, inputs := [13, 11] }, { op := GateOp.and, inputs := [14, 15] }, { op := GateOp.and, inputs := [17, 16] }, { op := GateOp.or, inputs := [18, 19] }, { op := GateOp.or, inputs := [21, 20] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52980_aux

theorem PEqualNP.Outside.L_meta_52980 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52980_aux.main
