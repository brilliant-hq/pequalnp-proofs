import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52318_aux
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

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeaa00aa00aa00aa00aa00aa00aa00aa00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_146 : Nat := 0x5000500000000000000000000000000050005
def goal_146 : Nat := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeecccc0000cccc0000cccc0000cccc0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_148 : Nat := 0x11001100000000000000000000000000110011
def goal_148 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_148 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcfc0000fcfc0000fcfc0000fcfc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefefcfc0000fcfc0000fcfc0000fcfc0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeeeccaa00eeccaa00eeccaa00eeccaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffafaf0aa00faf0aa00faf0aa00faf0aa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffefffffffefffffffefffffffefefcaa00fefcaa00fefcaa00fefcaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_161 : Nat := 0x30000000300000000000000000000000300000003
def goal_161 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_162 : Nat := 0x50000000500000000000000000000000500000005
def goal_162 : Nat := 0xffffffffccccccccffffffffcccccccccccccccc00000000cccccccc00000000
def roots_162 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfffffffffafafafafffffffffafafafaaaaaaaaa00000000aaaaaaaa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfccccccccc00000000cccccccc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffefefefefffffffffefefefeeeeeeeee00000000eeeeeeee00000000
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

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffefffefffffffffffefffeffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffffaaaaffffffffffffaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffffffccccffffffffffffcccccccccccccccc0000cccccccccccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffeeeeffffffffffffeeeeeeeeeeeecccc0000eeeeeeeecccc0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffffffafafffffffffffffafafafaaaaaf0f00000fafaaaaaf0f00000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfcfcccccfcfc0000fcfcccccfcfc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffefefffffffffffffefefefeeeeefcfc0000fefeeeeefcfc0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffffaaffffffffffffffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffffccffffffffffffffccffccffcccccc0000ffccffcccccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffeeffffffffffffffeeffeeffeeeeccaa00ffeeffeeeeccaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0fff0ff00f0f00000fff0ff00f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffffafffffffffffffffafffaffaafaf0aa00fffaffaafaf0aa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffefffffffffffffffefffeffeefefcaa00fffeffeefefcaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f00000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfefefefefefefefefefefefefefefefefafafafafafafafa0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffccffccffccffccffccffccffccffccff00ff00ff00ff000000000000000000
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeffaaffaaffaaffaaaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffafffafffafffafffafffafffafffafffaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffefffefffefffefffefffafffafffafffaaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffccccffffccccffffccccffffccccffff0000ffff0000cccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeffffaaaaffffaaaacccc0000cccc0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffafafffffafafffffafafffffafafffffafafffffafaf0f00000f0f00000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfffff0f0fffff0f0fcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefffffefefffffefefffffafafffffafafcfc0000fcfc0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffffffaaffffffaaeeccaa00eeccaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fffffff0fffffff0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffafffffffafffffffafffffffafffffffafffffffafaf0aa00faf0aa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfffffff0fffffff0fcfc0000fcfc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffffffefffffffefffffffafffffffafefcaa00fefcaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeeeaaaaaaaaeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f00000000000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffafafafafffffffffafafafafafafafafafafafaaaaaaaaa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfcfcfcfcf0f0f0f0cccccccc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefefffffffffefefefefefefefefafafafaeeeeeeee00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffffccffccffccffccff00ff00ffccffcc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeffaaffaaffeeffeeaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffafffffffffffafffafffafffafffafffaffaaffaaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffffffffffefffefffefffefffafffaffeeffeeaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffff0000ffffffffffff0000ffff0000ffff00000000000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffaaaaffffffffffffaaaaffffaaaaffffaaaaaaaaaaaa00000000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffccccffffffffffffccccffffccccffff0000cccccccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffffffffffeeeeffffeeeeffffaaaaeeeeeeeecccc0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fffff0f0fffff0f0f0f00000f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffafafffffffffffffafafffffafafffffafafafaaaaaf0f00000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfffffcfcfffff0f0fcfcccccfcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffffffffffefefffffefefffffafafefeeeeefcfc0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffffffffffaaffffffaaffffffaaffaaffaaaa00aa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffffffffffccffffffccffffff00ffccffcccccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffffffeeffffffeeffffffaaffeeffeeeeccaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffff0fffffffffffffff0fffffff0fffffff0fff0ff00f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffffffffffafffffffafffffffafffaffaafaf0aa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffffffffffcfffffffcfffffff0fffcffccfcfc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffffffffffefffffffefffffffafffeffeefefcaa00
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
def isoMvS_161:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_161:Lower true dom_161 roots_161 goal_161 4:=lower_iso_b isoMvS_161 (by decide +kernel) lowS_41
def isoMvS_162:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_162:Lower true dom_162 roots_162 goal_162 4:=lower_iso_b isoMvS_162 (by decide +kernel) lowS_41
def isoMvS_168:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_168:Lower true dom_168 roots_168 goal_168 4:=lower_iso_b isoMvS_168 (by decide +kernel) lowS_41
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
|0=>0xfb9630
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>0x40
|4,0=>0x98011
|5,0=>0x12d
|6,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_168 4 roots_168 ops++addP pm 1 dom_137 4 roots_137 ops++addP pm 2 dom_41 4 roots_41 ops++addP pm 3 dom_161 4 roots_161 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_169 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_161 _ g hchk
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
def isoMvS_113:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 4:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_51
def isoMvS_114:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 4:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_51
def isoMvS_120:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 4:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_51
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_43
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_43
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_105
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_105
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 5:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_43
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_43
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_43
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_105
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_43
def isoMvS_195:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 4:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_51
def isoMvS_198:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 4:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_51
def isoMvS_201:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_105
def isoMvS_202:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 4:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_51
def isoMvS_210:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_43
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_105
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 5:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_43
def isoMvS_228:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 4:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_51
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 5:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_43
def isoMvS_240:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_240:Lower true dom_240 roots_240 goal_240 4:=lower_iso_b isoMvS_240 (by decide +kernel) lowS_51
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
|0=>0x1f69040
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x53
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_43 5 roots_43 ops++addP pm 1 dom_58 4 roots_58 ops++addP pm 2 dom_51 4 roots_51 ops++addP pm 3 dzo_43_16 5 roots_43 ops++addP pm 4 dom_41 4 roots_41 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_51 _ g hchk
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
|0=>0x481011112306491711112491690
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x42310000000000211101
|6,0=>0x81007161
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0xffbae8754486100
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x6403000125
|6,0=>0x9788
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_92 5 roots_92 ops++addP pm 1 dom_85 5 roots_85 ops++addP pm 2 dom_73 4 roots_73 ops++addP pm 3 dom_89 5 roots_89 ops++addP pm 4 dom_84 4 roots_84 ops++addP pm 5 dom_77 5 roots_77 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_93 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_84 _ g hchk
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
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_slice_b [(0xc0c00000c0c000000000000000000000c0c00000c0c,32,34)] (by decide +kernel) lowS_169
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_slice_b [(0x30300000303000000000000000000000303000003030,128,132)] (by decide +kernel) lowS_169
namespace S_179
def pG:List (Nat×Nat):=[(1,33),(1,129),(2,18),(2,34),(2,130),(3,19),(3,35),(3,131),(16,18),(16,144),(17,19),(17,49),(17,145),(32,33),(32,34),(32,160),(48,49),(48,50),(48,176),(128,129),(128,130),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_179.map (·&&&dom_179)
def gM:=goal_179&&&dom_179
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xc94e1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000000000000000000000000000f000f00000000f0000000f00000000000000000000000f0000000f0000c000c000c000c0000000000000000000c000c000c000ca000a000a000a0000000000000000000a000a000a000af000f000f000f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 180 0xfffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_178 5 roots_178 ops++addP pm 1 dom_177 5 roots_177 ops++addP pm 2 dom_163 5 roots_163 ops++addP pm 3 dom_147 5 roots_147 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_179 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_147 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_178 5 s (0,roots_178.map (·&&&dom_178)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_179 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_178 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_179==dom_179)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_179 gM v ys):RunD true dom_179 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_179 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_179 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_179 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_179 roots_179 goal_179 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_179
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=S_179.noCircuit
theorem lowS_199:Lower true dom_199 roots_199 goal_199 5:=lower_slice_b [(0xaa00000000000000aa00000000000000aa00000000000000aa,64,65)] (by decide +kernel) lowS_198
theorem lowS_205:Lower true dom_205 roots_205 goal_205 6:=lower_slice_b [(0x3030000000000000303000000000000030300000000000003030,64,68)] (by decide +kernel) lowS_201
theorem lowS_211:Lower true dom_211 roots_211 goal_211 6:=lower_slice_b [(0xa000a00000000000a000a00000000000a000a00000000000a000a,64,65)] (by decide +kernel) lowS_210
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
def isoMvS_167:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_151
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 8:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_93
def isoMvS_182:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 7:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_179
def isoMvS_185:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 8:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_173
def isoMvS_186:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_179
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 8:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_93
def isoMvS_203:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 7:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_107
def isoMvS_213:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 6:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_205
def isoMvS_214:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 7:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_179
def isoMvS_220:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 6:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_205
def isoMvS_227:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 7:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_107
def isoMvS_229:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 6:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_211
def isoMvS_230:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 7:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_59
def isoMvS_233:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_171
def isoMvS_234:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 7:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_107
def isoMvS_241:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 6:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_211
def isoMvS_242:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 7:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_107
def isoMvS_244:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 7:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_107
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
|0,0=>0xff00cc00ff00cc00cc00cc00cc00ccff00ff00ff000000ff00ff00000000ff00f000ff00f000f000f000f000f00000000000000000ff000000ff00000000ff000000ff0000000000000000ff000000ff000000ff000000ff0000ff00ff00ff00ff0000000000000000f000f000f000f000f000f000f000f0ff000000ff00000000000000000000ff00ff00ff00ff00ff000000ff000000000f0000000f000f0000000f0000ff00ff0000000000ff00ff000000000000ff000000ff00ff000000ff0000cc00cc00cc00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa0f000f000f000f000f0000000f0000
|0,1=>0xff0000000000ff00ff00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8a40829229020a5645204149c86520414914d10530520414914208124521e14918810564329020a48640827729020a48650820490cd104834082450820490c340824308203906209486104a418820
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
|0=>0x52652452552d52652452552552452562d52752631f524525
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x62198000600
|6,0=>0x592480081
|7,0=>0x3c5c2d1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 9
def pmP:Nat→Nat
|0=>0xffccd8c1420100
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1208
|6,0=>0x4014741
|7,0=>0x1ff
|8,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_118 7 roots_118 ops++addP pm 1 dom_115 7 roots_115 ops++addP pm 2 dom_55 5 roots_55 ops++addP pm 3 dom_103 5 roots_103 ops++addP pm 4 dom_117 7 roots_117 ops++addP pm 5 dom_87 6 roots_87 ops++addP pm 6 dzo_87_32 6 roots_87 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_119 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_103 _ g hchk
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
def dzo_121_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_121_2:=0xc0c0c0c0c0c0c080c0c0c0c0c0c0800
def gsh_121_2:=0x3030303030303020303030303030200
theorem lowS_zo_121_2_73:Lower true dzo_121_2 roots_121 gzo_121_2 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_2) [(dom_121,2)] (by decide +kernel) (lower_slice_b (T:=gsh_121_2) [(0x3030000030300000303000003030000,0,16),(0x3030303000000000303030300000000,0,32)] (by decide +kernel) lowS_73)
def dzo_73_2:=0xc0c0000000000000c0c
def gzo_73_2:=0xc080000000000000800
def gsh_73_2:=0x3020000000000000200
theorem lowS_zo_73_2_73:Lower true dzo_73_2 roots_73 gzo_73_2 4:=lower_iso_b (d1:=dom_73) (r1:=roots_73) (T1:=gsh_73_2) [(dom_73,2)] (by decide +kernel) (lower_slice_b (T:=gsh_73_2) [] (by decide +kernel) lowS_73)
def dzo_89_2:=0xc0c0c0c000000000c0c0c0c
def gzo_89_2:=0xc0c0c08000000000c0c0800
def gsh_89_2:=0x30303020000000003030200
theorem lowS_zo_89_2_73:Lower true dzo_89_2 roots_89 gzo_89_2 5:=lower_iso_b (d1:=dom_89) (r1:=roots_89) (T1:=gsh_89_2) [(dom_89,2)] (by decide +kernel) (lower_slice_b (T:=gsh_89_2) [(0x30300000000000003030000,0,16)] (by decide +kernel) lowS_73)
def dzo_107_16:=0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16:=0xf0f00000f0f00000f0e00000e0c0000
def gsh_107_16:=0xf0f00000f0f00000f0e00000e0c
theorem lowS_zo_107_16_41:Lower true dzo_107_16 roots_107 gzo_107_16 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_16) [(dom_107,16)] (by decide +kernel) (lower_slice_b (T:=gsh_107_16) [(0xc0c00000c0c00000c0c00000c0c,0,2),(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_41_16:=0x303000003030000
def gzo_41_16:=0x302000002000000
def gsh_41_16:=0x30200000200
theorem lowS_zo_41_16_41:Lower true dzo_41_16 roots_41 gzo_41_16 4:=lower_iso_b (d1:=dom_41) (r1:=roots_41) (T1:=gsh_41_16) [(dom_41,16)] (by decide +kernel) (lower_slice_b (T:=gsh_41_16) [] (by decide +kernel) lowS_41)
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
|0,1=>0xf0f0f0f0f0f0f0f0f0f0f0f0f000f000000000000000000505050505000500f0f0f0f0f0f0f0f0f000f000f000f0050505050505050505000500050005005050505050505050505050500000000004000400040004000400040c0c0c0cf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0a0a0a0af0f00000f0f0f0a00000000000000000000000000000000f0a0f0a0f0a0f0af0f00000f0f00000c0c00000c0c000000f000f000f000f000f000f000a000a00000000c0c0c0c000000000f0e0f0ef0e0f0e0f0e0f0e0f0e0f0e0c0c0c0c0000000000000000f0f0f0f0f0f0f0a00000000f0f0f0f000000000f000f00
|0,2=>0xf0a00000f0a00000f0a00000f0ac0c00040c0c00040c0c00040c0c0004c0c0f0e0c0c0f0e0c0c0f0e0c0c0f0ef0f0f0f0f0f0f0a0f0f0f0f0f0f0f0a0000f0f00000f0a00000f0f00000f0af0f000f0f0f000a0f0f000f0f0f000a5050505050505050505050505000500f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0ef0e0f0e000000000f0e0f0e00000000e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e000000000000000000e000e000e000ef0f0f0f0f0f0f0f0504050405040504f0f0f0f0f0f0f0f000000000f0a0f0af0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0f0f00000f0a0f0f0f0f00000f0a00000000f0f0f0f000000000a0a0a0a
|0,3=>0x5050505050005000505050505000500f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a005000500050005000500050000000000f000f000f000a000f000f000f000af0f0f000f0f0f000f0f0f000f0f0f00f0f0f000a0a0a000f0f0f000a0a0a00f030f030f030f030f020f020f020f0200000000f0e0f0e000000000f0e0f0e0000f0f00000f0f00000c0c00000c0cf000f000f000f000f000f000a000a00f000f000f0f0f0a0f000f000f0f0f0af0f0f0f0f0f0f0f050505050500050000000000f0f0f0a000000000f0f0f0aa0a0a0a0a0a0a0a0f0f0f0f0f0a0f0a00000000f0f0f0f000000000f0a0f0af0f0f0f0f0f0f0f0f0f0f0f0f0a0f0a
|0,4=>0xf0f0f0f0a0a0a0a0000f0f00000a0a00000f0f00000a0a30303030303000003030303030300005050500050505000505050005050500f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0000000000000000e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0f0c0f0c0f0c0f0cf0f0f0a0f0f0f0a0f0f0f0a0f0f0f0af0f0f0f0f0f0a0a0f0f0f0f0f0f0a0af0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cf0f00000f0f0f0a0f0f00000f0f0f0af0f0f0f0f0f00000f0f0f0f0f0f000000000000f0a0f0a000000000f0a0f0aa0f0a0f0a0f0a0f0a0f0a0f0a0a0a0a000000000000000000000000f0a0f0af0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a
|0,5=>0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0cf0f0f0f0f0f0f0f0f0f00000f0f00003020302030203020302030203020302
|_,_=>0
def sP:Nat→Nat
|0=>0x160ce8d002840b063400c3c2020b063400c381c18d0030d88160c68c34203980608008080c68100305831a0061716586802a305830030a08063400c26205832434608222c18d00303840608005160c1000a405830400788063868018203830c00608160c00a12203830c002840608080
|1=>0x1ab8608160c6ad182160b063400c102c18d0031588302c19d1a0060b067468018805aa063400c1010583047400c160ce8d00a44034e0868018205831a00625102c18d0030a08160c680189040b063400c46205821a00a8c10605830434008422c18d003040b060868040203990608008
|2=>0x30c8b063401b102c18d0031e88160c68018f0419080c68036205ba063400c102c180185040b06e4680182018d0031c08160868018dc418160db0018205836a3400c107c5830030488160c68018d040b063408018205831a0063310c85831a00608160c68018c4430160c6801820583
|3=>0x1a0060817181821a00608160d4021a006080e2c182003040b063400a102e2831a006080e2c1820014403043400c7020c0b0600614111018d0032188069c68018205831a0210c10105831a01488160c6801904404160c68014205c0063403f102c1861a006080e1018d0014604160df0d
|4=>0x106020b063400c102c18d00328080e2c18d00146089e2c18d003040b063400c12205831a0064e102c18d193440b063400c982258b06086801820f8b063400c102c18d94006083e1c5831a00608321018d003040b072468018205831a0061c102c19d1a9800c102e4031a006088e64583
|5=>0x60868018205c6063400c11485831a0060816ec18d003040b063400c10645831a00608882c18d0030404160c68018205831a00643102c6802a30444160c10d003040b06f8680182290b06340051820399063400c1010583043400c102c1be1a0028c102e883043400c10105831a0061b
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
|0=>0x83716213e3308353e30083516210e331a2d08081a3116210a3518213221080b1621102d32ec182d440f002116210e331a2d32741a21182d00bf040f1a3132353221182d32373e333a2d16a004013a9a1a21440c1a310021083116210a2f1821163118351a2d3e303a2d3a331a210833102d322116310e1418211a2d0808102d
|1=>0x18211635182d1a3116210a35182106211a31083316210831162104031a3118211a2d3223182d08371621320f182d8803062d76330635042d1a3108351621109a00310e211a2d182d102d3a011a213a331a2100311a21040d1a31320d182d1a31060104011a3118351a2d0835162116a2040108311621160a1a31502c04011a31
|2=>0x1a310601002d0635182d062d1621042f1a31440c00211a31062d0a351821002d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x52000000000000000000000000000023000002000
|6,0=>0x4920000004724524324033e23c20003933723430003223112f20002e12c20000000002a20000002912722430000000000002130002010001e20001d10001b21921720000000001431220001020d30b2000092072
|7,0=>0x8728528328127f27d27b27927727527327126f26d26b26926726526326125f25d25b25925725525325124f24d24b2
|8,0=>0x8f18e18d18c10008b18a1891
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x104fe001031400192f800325d0005cbe000a17c00112f800160700024be00040040006050000c0200004fe000081c0000c0000007700000be000015c00002000000390000066000004c000008000000f000001a00000200000030000004000000600000080000008000000
|1=>0x800c4ff00000c50020e0900404118104fe08201fc100018818003102104fe018a17c0304018041005004280a008181c01012f802005f003c0be003837c00702f800a07f
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x800000000000000c0080
|6,0=>0x4000108d40110014d2001160400420000010005060c000000a01100201100204900000c080092080102
|7,0=>0x254deaad608a701e87c87598608e76eb55cbda2e1c72b26
|8,0=>0x933ba1397899
|9,0=>0xf
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 27 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_115 7 roots_115 ops++addP pm 2 dom_91 7 roots_91 ops++addP pm 3 dom_59 7 roots_59 ops++addP pm 4 dom_121 7 roots_121 ops++addP pm 5 dzo_121_2 6 roots_121 ops++addP pm 6 dom_107 7 roots_107 ops++addP pm 7 dom_73 4 roots_73 ops++addP pm 8 dzo_73_2 4 roots_73 ops++addP pm 9 dzo_89_2 5 roots_89 ops++addP pm 10 dom_83 4 roots_83 ops++addP pm 11 dom_51 4 roots_51 ops++addP pm 12 dom_90 4 roots_90 ops++addP pm 13 dzo_43_16 5 roots_43 ops++addP pm 14 dzo_107_16 6 roots_107 ops++addP pm 15 dzo_105_2 5 roots_105 ops++addP pm 16 dom_99 4 roots_99 ops++addP pm 17 dom_114 4 roots_114 ops++addP pm 18 dom_58 4 roots_58 ops++addP pm 19 dom_113 4 roots_113 ops++addP pm 20 dom_120 4 roots_120 ops++addP pm 21 dom_89 5 roots_89 ops++addP pm 22 dom_41 4 roots_41 ops++addP pm 23 dzo_41_16 4 roots_41 ops++addP pm 24 dom_43 5 roots_43 ops++addP pm 25 dom_106 4 roots_106 ops++addP pm 26 dom_105 5 roots_105 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_121_2_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_73_2_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_89_2_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_43_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_107_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_105_2_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_41_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_106 _ g hchk
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
def dzo_92_32:=0x11111111000000001111111100000000
def gzo_92_32:=0x11111110000000001110110000000000
def gsh_92_32:=0x111111100000000011101100
theorem lowS_zo_92_32_84:Lower true dzo_92_32 roots_92 gzo_92_32 5:=lower_iso_b (d1:=dom_92) (r1:=roots_92) (T1:=gsh_92_32) [(dom_92,32)] (by decide +kernel) (lower_slice_b (T:=gsh_92_32) [(0x110011000000000011001100,0,8)] (by decide +kernel) lowS_84)
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
def dzo_105_4:=0x3030000030300000303000003030
def gzo_105_4:=0x3030000030300000302000002000
def gsh_105_4:=0x303000003030000030200000200
theorem lowS_zo_105_4_41:Lower true dzo_105_4 roots_105 gzo_105_4 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_4) [(dom_105,4)] (by decide +kernel) (lower_slice_b (T:=gsh_105_4) [(0x303000003030000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_85_32:=0x330033000000000033003300000000
def gzo_85_32:=0x330032000000000032002200000000
def gsh_85_32:=0x3300320000000000320022
theorem lowS_zo_85_32_84:Lower true dzo_85_32 roots_85 gzo_85_32 5:=lower_iso_b (d1:=dom_85) (r1:=roots_85) (T1:=gsh_85_32) [(dom_85,32)] (by decide +kernel) (lower_slice_b (T:=gsh_85_32) [(0x2200220000000000220022,0,1)] (by decide +kernel) lowS_84)
def dzo_109_16:=0x33330000333300003333000033330000
def gzo_109_16:=0x33330000333300003332000032300000
def gsh_109_16:=0x3333000033330000333200003230
theorem lowS_zo_109_16_41:Lower true dzo_109_16 roots_109 gzo_109_16 6:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_16) [(dom_109,16)] (by decide +kernel) (lower_slice_b (T:=gsh_109_16) [(0x3030000030300000303000003030,0,4),(0x3333000033330000000000000000,0,64)] (by decide +kernel) lowS_41)
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
|0=>0x14344810808e021024a010808a011004e0d102433e1405e0b144443108042111004402080423610042450c084310804a010804a3a102440928e840915704090c0420108444011024401080551308d4401114424d1408c130804a3a1024302304c20111143020cf84091404d0b1004201
|1=>0xa010808301080450d10243110c08401080440108044090c04a3a102455c0c04a7110084320804a450c084091408409
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x849009e2366000c19532463cc690a310418819803
|7,0=>0xa253ca694b29251ca29432824fc9e93b2724dc9a9332624bc9692b25249c929232
|8,0=>0xb43646c0d71ac3546a0d31
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0xd2d2183a424f48476b089c6111ac21ff843eb087d210dac203e8406903852020a403f1807e1008c60100c01f0800e3001c4003000031000230004200080000c00008000080000c000100000
|1=>0x2a4b4c0829487fe589a4707f8c3ff187d61e7a434f48696b
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0x40c448040c3822852461c8
|7,0=>0x34c4d57595a56e86189e382198f4512de719
|8,0=>0x917897a5a7de
|9,0=>0x14
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_93 8 roots_93 ops++addP pm 1 dzo_84_32 4 roots_84 ops++addP pm 2 dzo_93_32 6 roots_93 ops++addP pm 3 dom_121 7 roots_121 ops++addP pm 4 dzo_92_32 5 roots_92 ops++addP pm 5 dom_124 7 roots_124 ops++addP pm 6 dom_117 7 roots_117 ops++addP pm 7 dom_61 6 roots_61 ops++addP pm 8 dzo_57_4 5 roots_57 ops++addP pm 9 dzo_45_16 5 roots_45 ops++addP pm 10 dom_84 4 roots_84 ops++addP pm 11 dzo_121_4 6 roots_121 ops++addP pm 12 dom_41 4 roots_41 ops++addP pm 13 dzo_105_4 5 roots_105 ops++addP pm 14 dom_109 7 roots_109 ops++addP pm 15 dzo_85_32 5 roots_85 ops++addP pm 16 dzo_109_16 6 roots_109 ops++addP pm 17 dom_92 5 roots_92 ops++addP pm 18 dom_105 5 roots_105 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_84_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_93_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_92_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_57_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_45_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_121_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_105_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_85_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_109_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_105 _ g hchk
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
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_slice_b [(0xcccccccc000000000000000000000000cccccccc,16,18)] (by decide +kernel) lowS_157
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_slice_b [(0xcccc0000cccc00000000000000000000cccc0000cccc,32,34)] (by decide +kernel) lowS_173
theorem lowS_183:Lower true dom_183 roots_183 goal_183 9:=lower_slice_b [(0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_181
namespace S_187
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(2,18),(2,34),(2,130),(3,11),(3,19),(3,35),(3,131),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,138),(16,18),(16,144),(17,19),(17,25),(17,49),(17,145),(24,25),(24,26),(24,56),(24,152),(32,33),(32,34),(32,40),(32,160),(48,49),(48,50),(48,56),(48,176),(128,129),(128,130),(128,136),(128,144),(128,160)]
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
|6,0=>0xdd446
|7,0=>0xe0bc4d1175bf963718e9103a6
|8,0=>0xd51466a888
|9,0=>0x3dbb0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x50505050505050500000000000000000500050005000500f0f0f0f0f0f0f0f00000000000000000f0a0f0a0f0a0f0aa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0af000f000f000f0000000000000000000f000f000f000f00f0f0f0f0f0f0f0f00000000000000000000000000000000f0f0f0f0000000000000000000000000f0f0f0f00000000f0f00000f0f000000000000000000000f0f00000f0f0000f0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0f0af0f0f0f0f0f0f0f00000000000000000f000f000f000f00c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0a
|_,_=>0
def sP:Nat→Nat
|0=>0x5471865437186542718654718a654321865497186549710865427108543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d5736067
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
|0=>0x1e1764a3765e1764a17641d8661976619785d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfff1b7eff5f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x39f5
|8,0=>0x13
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_185 8 roots_185 ops++addP pm 1 dom_186 7 roots_186 ops++addP pm 2 dom_179 7 roots_179 ops++addP pm 3 dom_59 7 roots_59 ops++addP pm 4 dom_155 8 roots_155 ops++addP pm 5 dom_171 8 roots_171 ops++addP pm 6 dom_178 5 roots_178 ops++addP pm 7 dom_51 4 roots_51 ops++addP pm 8 dom_58 4 roots_58 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_187 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_58 _ g hchk
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
namespace S_189
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(4,20),(4,132),(5,13),(5,21),(5,37),(5,133),(8,9),(8,40),(8,136),(12,13),(12,28),(12,44),(12,140),(16,20),(16,144),(17,21),(17,25),(17,49),(17,145),(24,25),(24,28),(24,56),(24,152),(32,33),(32,40),(32,160),(36,37),(36,44),(36,52),(36,164),(48,49),(48,52),(48,56),(48,176),(128,129),(128,132),(128,136),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_189.map (·&&&dom_189)
def gM:=goal_189&&&dom_189
def NN:Nat→Nat
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0x3abd3
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccc000000000000000000000000cccccccc0000000333300003333000000000000000000003333000033330000cc00cc00cc00cc000000000000000000cc00cc00cc00cc030303030303030300000000000000000303030303030303088888888888888880000000000000000888888888888888b33333333333333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c688
|_=>0
def sO:Nat→Nat→Nat
|9,0=>6
|_,_=>0
def wAt:=mkWire dB 6 190 0x3fffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_188 8 roots_188 ops++addP pm 1 dom_185 8 roots_185 ops++addP pm 2 dom_181 8 roots_181 ops++addP pm 3 dom_173 8 roots_173 ops++addP pm 4 dom_157 8 roots_157 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_189 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_157 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_188 8 s (0,roots_188.map (·&&&dom_188)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_189 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_188 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_189==dom_189)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_189 gM v ys):RunD true dom_189 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_189 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_189 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_207:Lower true dom_207 roots_207 goal_207 8:=lower_slice_b [(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0,64,68)] (by decide +kernel) lowS_203
theorem lowS_215:Lower true dom_215 roots_215 goal_215 8:=lower_slice_b [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,64,65)] (by decide +kernel) lowS_214
theorem lowS_219:Lower true dom_219 roots_219 goal_219 9:=lower_slice_b [(0xf0f0f0f0000000000000000000000000f0f0f0f0000000000000000,1,65)] (by decide +kernel) lowS_155
theorem lowS_221:Lower true dom_221 roots_221 goal_221 9:=lower_slice_b [(0x33333333000000000000000000000000333333330000000000000000,1,65)] (by decide +kernel) lowS_157
def dzo_167_64:=0xff000000ff0000000000000000000000ff000000ff0000000000000000
def gzo_167_64:=0xff000000fe0000000000000000000000fe000000fa0000000000000000
def gsh_167_64:=0xff000000fe0000000000000000000000fe000000fa
theorem lowS_zo_167_64_162:Lower true dzo_167_64 roots_167 gzo_167_64 6:=lower_iso_b (d1:=dom_167) (r1:=roots_167) (T1:=gsh_167_64) [(dom_167,64)] (by decide +kernel) (lower_slice_b (T:=gsh_167_64) [(0xaa000000aa0000000000000000000000aa000000aa,0,1),(0xf0000000f00000000000000000000000f0000000f0,0,4)] (by decide +kernel) lowS_162)
namespace S_231
def pG:List (Nat×Nat):=[(1,33),(1,65),(1,129),(2,34),(2,130),(3,35),(3,67),(3,131),(4,68),(4,132),(5,37),(5,69),(5,133),(6,38),(6,70),(6,134),(7,39),(7,71),(7,135),(32,33),(32,34),(32,160),(36,37),(36,38),(36,100),(36,164),(64,65),(64,68),(66,67),(66,70),(66,98),(66,194),(96,97),(96,98),(96,100),(96,224),(128,129),(128,130),(128,132),(128,160),(192,193),(192,194),(192,196),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_231.map (·&&&dom_231)
def gM:=goal_231&&&dom_231
def NN:Nat→Nat
|4=>5
|5=>15
|6=>37
|7=>10
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xfd9a4c2ed2911326babb01fe6
|5,0=>0xfe73cf52f4e1f39de6bfd42deb4671a397ea07cd977fe75c8f6fe606bfd7661a847b8036e2e
|6,0=>0xfb9c0ec1afc2b1ca4ca8946cf909d58fe3b815537d7a57782675ef5724116ca136c5b66a91e671a16053d5f8f15b0235965b4fdb3468ee45e7940ae6408d03d00f3cc903cc3636e2e27d5d219ff1ce6d19f42195d90e719091c4057d5
|7,0=>0xd269acadeaaff18a4ca887c1f867c470709628fe460fb3ee0b
|8,0=>0x9aff0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00000000000000ff0000000000000000000000000000000000000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000ccff00000033000000ff00000033000000ff00000000000000ff000000003300000000000000330000000000000033000000000000003300000000ff00000000000000ff00000000000000ff00000000000000ff00000000fe000000fe000000fe000000fe000000fe000000fa000000fe000000faee000000ee000000ee000000ee000000ee000000aa000000ee000000aaff000000ff000000ff000000ff00000000000000000000000000000000ff000000aa000000ff000000aa000000aa000000aa000000aa000000aaff000000ff000000ff000000ff000000ff00000000000000ff00000000000000003300000000000000330000003300000000000000330000000000000000ff00000000000000ff000000ff00000000000000ff00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0aa000000aa000000aa000000aa000000aa000000aa000000aa000000aa3300000033000000330000003300000033000000000000003300000000ff000000ff0000000000000000000000ff000000ff0000000000000000
|0,1=>0x33000000000000003300000000ff000000ff00000000000000ff000000ff000000ff0000000000000000ff000000ff000000ff00000000000000ff000000ff0000000000000000ff000000ff000000ff000000ff000000ff000000cc000000ff000000ccff000000f0000000ff000000f0000000f0000000f0000000f0000000f000000000000000000000000000000000ff00000000000000ff0000000000000000ff00000000000000ff0000000000000000000000000000000000000000000000000000000000000000ff000000ff0000000000000000ff000000cc000000ff000000cc000000cc000000cc000000cc000000ccff000000cc000000ff000000cc000000ff000000cc000000ff000000ccff000000ff000000ff000000ff000000cc000000cc000000cc000000cc00000000000000000000000000000000ff000000cc000000ff000000ccff000000ff000000ff000000ff000000ff000000ff0000000000000000ff000000ff000000ff000000ff000000330000000000000033000000003300000033000000330000003300000000000000000000000000000000cc000000cc000000cc000000cc000000cc00000000000000cc00000000
|0,2=>0xff000000ff0000003300000033000000ff000000ff0000000000000000cc00000000000000cc00000000000000ff00000000000000ff00000000ff000000000000000000000000000000ff000000ff000000000000000000000000cc00000000000000cc000000cc000000cc000000cc000000cccc000000cc000000cc000000cc000000ff000000cc000000ff000000cc00000000ff0000000000000000000000ff000000ff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xce08020b6ce08021a0ce08064b0c20582060ce1c02c30814c818308c0111835c20161835420142c33824cb0c24804460c20403c62c324020610338200b0c900810338200d0c230020b0c204020b2890081030850060c70401830850040c2040
|1=>0x1833820082c35c200818338230020b6833824c818b0ce0804462c33824c818b0d00802212c338200818b0c20402162c35420082c33828082c33827c020b0d008020b0c20402062c354e0802c338248020b0ce09e20b0ce09d2142c338200870b
|2=>0x64b0ce0802112c33826082c33824c82c354e0802060ce0803cb0ce0a520d2c338200818b0ce08020b9033820082c33828c82c38820082c338700858b0ce09320b6833826082c33823132166833820082c33820402062c33826082c308c008456
|3=>0xb0ce0802162c33820082c338230020b68338200818b0ce08020b0ce08020f2c3382008
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a58c8a5e62c314d49ac47620b0ed86ac2f615289543ec196
|6,0=>0x15f6acb549e96f4479f34e1a64d2b7923c75e2cf0f7843c05df4ef4676bb99dbeed8768bb29d86ebc75b32bdd52ca364e3a55d1ec8964139edceac6f6
|7,0=>0x344f9b7ca3e35f0cf7f7bc3dc9ad8d657
|8,0=>0x1a96
|_,_=>0
def wAt:=mkWire dB 38 232 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xb392cecb232c84b202c88e22008c0213884b212c800453888b47019cb2238fcb2008f4b2000840212c8cb212c84e3d2c80b212c84b2100fcb2018e0b2118ecb212c840652c8803d2c8033d2c80b222c8c23d2c84b2038f4b212c80b2140246382c8463f2c84b20
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x28c00000731840000000000000cc0300000
|6,0=>0x2f2b4800002c1a8a8298a51002418c40088400845f2784007440000000704006880060962544004c912000003c8d2
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xfafe9ebfadeae58906208160480a007bda9625811804b1082f088200680e00c0200400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xa000ce00004220c00
|6,0=>0xa7013464ec7818c0900f55c291100c260101381ac002b5
|7,0=>0x1efd6b7bc62f9
|8,0=>0xe
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_230 7 roots_230 ops++addP pm 1 dom_101 4 roots_101 ops++addP pm 2 dom_165 5 roots_165 ops++addP pm 3 dom_227 7 roots_227 ops++addP pm 4 dom_198 4 roots_198 ops++addP pm 5 dom_229 6 roots_229 ops++addP pm 6 dom_199 5 roots_199 ops++addP pm 7 dzo_167_64 6 roots_167 ops++addP pm 8 dom_167 6 roots_167 ops++addP pm 9 dom_103 5 roots_103 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_231 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_167_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_103 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_230 7 s (0,roots_230.map (·&&&dom_230)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_231 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_230 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_231 gM v ys):RunD true dom_231 gM v (ori ys):=h
def Z (s:Nat):=barP dom_231 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 37 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 37 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 10 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 0 = true)
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
def dzo_201_2:=0xc0c0000000000000c0c0000000000000c0c0000000000000c0c
def gzo_201_2:=0xc0c0000000000000c0c0000000000000c080000000000000800
def gsh_201_2:=0x303000000000000030300000000000003020000000000000200
theorem lowS_zo_201_2_73:Lower true dzo_201_2 roots_201 gzo_201_2 5:=lower_iso_b (d1:=dom_201) (r1:=roots_201) (T1:=gsh_201_2) [(dom_201,2)] (by decide +kernel) (lower_slice_b (T:=gsh_201_2) [(0x303000000000000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_73)
def dzo_162_64:=0x500000005000000000000000000000005000000050000000000000000
def gzo_162_64:=0x500000004000000000000000000000004000000000000000000000000
def gsh_162_64:=0x50000000400000000000000000000000400000000
theorem lowS_zo_162_64_162:Lower true dzo_162_64 roots_162 gzo_162_64 4:=lower_iso_b (d1:=dom_162) (r1:=roots_162) (T1:=gsh_162_64) [(dom_162,64)] (by decide +kernel) (lower_slice_b (T:=gsh_162_64) [] (by decide +kernel) lowS_162)
def dzo_171_64:=0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000
def gzo_171_64:=0xf0f00000f0e000000000000000000000f0e00000f0a0000000000000000
def gsh_171_64:=0xf0f00000f0e000000000000000000000f0e00000f0a
theorem lowS_zo_171_64_162:Lower true dzo_171_64 roots_171 gzo_171_64 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_64) [(dom_171,64)] (by decide +kernel) (lower_slice_b (T:=gsh_171_64) [(0xa0a00000a0a000000000000000000000a0a00000a0a,0,1),(0xf0000000f00000000000000000000000f0000000f00,0,8)] (by decide +kernel) lowS_162)
def dzo_233_2:=0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c
def gzo_233_2:=0xc0c00000c0c00000c0c00000c0c00000c0c00000c0800000c0c00000800
def gsh_233_2:=0x30300000303000003030000030300000303000003020000030300000200
theorem lowS_zo_233_2_73:Lower true dzo_233_2 roots_233 gzo_233_2 6:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_2) [(dom_233,2)] (by decide +kernel) (lower_slice_b (T:=gsh_233_2) [(0x30300000000000003030000000000000303000000000000030300000000,0,32),(0x30300000303000003030000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_73)
def dzo_163_64:=0xf0000000f00000000000000000000000f0000000f0000000000000000
def gzo_163_64:=0xf0000000e00000000000000000000000e0000000a0000000000000000
def gsh_163_64:=0xf0000000e00000000000000000000000e0000000a
theorem lowS_zo_163_64_162:Lower true dzo_163_64 roots_163 gzo_163_64 5:=lower_iso_b (d1:=dom_163) (r1:=roots_163) (T1:=gsh_163_64) [(dom_163,64)] (by decide +kernel) (lower_slice_b (T:=gsh_163_64) [(0xa0000000a00000000000000000000000a0000000a,0,1)] (by decide +kernel) lowS_162)
def dzo_170_64:=0x50500000505000000000000000000000505000005050000000000000000
def gzo_170_64:=0x50500000504000000000000000000000504000005000000000000000000
def gsh_170_64:=0x5050000050400000000000000000000050400000500
theorem lowS_zo_170_64_162:Lower true dzo_170_64 roots_170 gzo_170_64 5:=lower_iso_b (d1:=dom_170) (r1:=roots_170) (T1:=gsh_170_64) [(dom_170,64)] (by decide +kernel) (lower_slice_b (T:=gsh_170_64) [(0x5000000050000000000000000000000050000000500,0,8)] (by decide +kernel) lowS_162)
namespace S_235
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,34),(2,130),(3,11),(3,35),(3,67),(3,131),(8,9),(8,40),(8,72),(8,136),(10,11),(10,42),(10,74),(10,138),(32,33),(32,34),(32,40),(32,160),(64,65),(64,72),(66,67),(66,74),(66,98),(66,194),(96,97),(96,98),(96,104),(96,224),(128,129),(128,130),(128,136),(128,160),(192,193),(192,194),(192,200),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_235.map (·&&&dom_235)
def gM:=goal_235&&&dom_235
def NN:Nat→Nat
|4=>3
|5=>12
|6=>20
|7=>13
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xe52f1b9de923bde
|5,0=>0x7672a568503dded3ace838dea35b6434ccc319552df1029db721fe205408
|6,0=>0xe14008b6827f90e4fdb4489493822e37540370313202e3168e314002687522e831b3d41426812fbc0c7bb0adec05337020a9
|7,0=>0x80ddb5aa7e56375523d9424ee2dfc72682f1439c0e79c0bb360979903e3800729
|8,0=>0x434562ff10040d9
|9,0=>0xfffda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0e00000f0e00000f0e00000f0e00000f0e00000f0e00000f0e00000f0e0000000000000000f0a00000f0a000000000000000000000f0a00000f0a3030000030300000303000003030000030300000000000003030000000000000000f0f0000000000000f0f0000000000000f000000000000000f00f0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f00f0f00000f0f00000f0f00000f0f00000a0a00000a0a00000a0a00000a0af0f0000000000000f0f0000000000000f0f0000000000000f0f000000003030000030300000f0b00000f0b000003030000000000000f0b00000f0af0000000f0000000f0000000f0000000f0000000f0000000f0000000f00a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0af0f00000f0f00000f0f00000f0f00000000000000000000000000000000f0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0af0f00000a0a00000f0f00000a0a00000f0000000a0000000f0000000a00c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0cf0f00000f0f000000000000000000000f0f00000f0f0000000000000000
|0,1=>0xf0000000f0000000f0000000f0000000a0000000a0000000a0000000af0f0000000000000f0f00000f0a00000f0f0000000000000f0f00000f0af0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000000f0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f0000000000000000000000000000000000000000f0f00000f0f00000f0f00000000f0c00000f0c00000f0c00000f0c00000f0c00000f0c00000f0c00000f0cf0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000a0a00000f0f00000a0a00000f0f00000a0a00000f0a00000a0a00000f0af0f00000f0f00000f0f00000f0f00000f0a00000f0a00000f0a00000f0af0300000f0300000f0300000f0300000f0300000f0000000f0300000f00f0b00000f0b00000f0b00000f0b00000f0b00000f0a00000f0b00000f0af0f00000f0000000f0f00000f0000000a0a00000a0000000a0a00000a00f0f00000f0f00000f0f00000f0f00000f0f00000a0a00000f0f00000a0af0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f0000000000f0f0000000000000f0f00000000000000000000000000000f0af0f00000a0a00000f0f00000a0a00000f0f00000a0a00000f0f00000a0a
|0,2=>0xe0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000000f0f0000000000000f0f0000000000000a0a0000000000000a0af0f00000f0f00000f0f00000f0f00000f0f00000f0a00000f0f00000f0a00000000f0f0000000000000f0f0000000000000f0a0000000000000f0a0000000000f000000000000000f000000000000000a000000000000000a50500000500000005050000050000000505000005000000050500000500f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f0f00000f00
|_,_=>0
def sP:Nat→Nat
|0=>0x2571c11807891c11857494870462d00c10052db1c118525a4866491c16060052c45c11802435860051070465002551c60052520465002d04812802c40c12802d34811802470464452d03c014938718d1490c128c00b0812802481c61440c2040
|1=>0x2860052c41c118015c24798614b25204600524704694015b2470461642470460052470468c014b25204a1802470468801490c718d00541c1c12852520468401501031c10054090d20401604070460052470811801602521c11991091c119f004
|2=>0x2470460052479860052521c11801442470460051090c70460052571c11801493870461491c128664b24704a1801502470466457491c11852571c1
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x283129888c3e61c30c9858c26610306d42ac0f6
|6,0=>0x6a3b35d8cebf75c3ac9956ea474eba59d1ee88740b9e9ce8c6e63431898baa567
|7,0=>0x12c892bc7da32d118853c119f90f5777b3a1dc2edb6
|8,0=>0x509a76f347
|9,0=>0x1486
|_,_=>0
def wAt:=mkWire dB 39 236 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x25792191c54407149461d14640251894b1b1c9461d1494719489451d49009191c5494900547152454a1f18549154864715389430318744012454715246461d2474572009472504740151c54631489c51d2454a1d1854a2c1c946152ca05191c945251c64a2514647250c147192464719
|1=>0x464715245471924552191c54303187401518545191c9450118944012454a1d18545251c94025046491d1474a271464572009495d4864715
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1e6000618001260003905200005000001
|6,0=>0x806f4c00000746dcda9332642c0969aa34e690d099e336660ca9923
|7,0=>0x5b2b255caa9532a253ca694b29251ca29432
|8,0=>0x17c6f0dd1
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x149ec98a2777c407b2e201c950807cb840325c200026092593040ecb820564c0ffb6e020c9500466b8007044001e2a000d970006c900032540010180008020002400001008000604000180000088000041c00020800010200004900001f8000004000000
|1=>0x440125e04092ea03d954107caa083c1100192e681993
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1c00c02c024a002001
|6,0=>0x18510036020910c4191c7498456545
|7,0=>0x1b8dc90f75f8a67a5857
|8,0=>0x1351a
|9,0=>0xe
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_233 8 roots_233 ops++addP pm 1 dzo_73_2 4 roots_73 ops++addP pm 2 dom_171 8 roots_171 ops++addP pm 3 dzo_201_2 5 roots_201 ops++addP pm 4 dom_203 7 roots_203 ops++addP pm 5 dom_225 5 roots_225 ops++addP pm 6 dom_232 5 roots_232 ops++addP pm 7 dom_107 7 roots_107 ops++addP pm 8 dzo_162_64 4 roots_162 ops++addP pm 9 dom_162 4 roots_162 ops++addP pm 10 dom_227 7 roots_227 ops++addP pm 11 dom_234 7 roots_234 ops++addP pm 12 dzo_171_64 6 roots_171 ops++addP pm 13 dom_43 5 roots_43 ops++addP pm 14 dom_169 7 roots_169 ops++addP pm 15 dzo_233_2 6 roots_233 ops++addP pm 16 dzo_163_64 5 roots_163 ops++addP pm 17 dom_99 4 roots_99 ops++addP pm 18 dzo_105_2 5 roots_105 ops++addP pm 19 dom_139 5 roots_139 ops++addP pm 20 dom_73 4 roots_73 ops++addP pm 21 dzo_170_64 5 roots_170 ops++addP pm 22 dom_202 4 roots_202 ops++addP pm 23 dom_106 4 roots_106 ops++addP pm 24 dom_195 4 roots_195 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_235 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_73_2_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_201_2_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_162_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_171_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_233_2_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_163_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_105_2_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_170_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_195 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_233 8 s (0,roots_233.map (·&&&dom_233)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_235 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_233 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff00000000ffffffff00000000,96),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_235==dom_235)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_235 gM v ys):RunD true dom_235 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_235 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 20 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 20 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 13 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 13 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
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
theorem lowS_237:Lower true dom_237 roots_237 goal_237 9:=lower_slice_b [(0x303000003030000030300000303000003030000030300000303000003030,64,68)] (by decide +kernel) lowS_233
def dzo_178_64:=0x5000500050005000000000000000000050005000500050000000000000000
def gzo_178_64:=0x5000500050004000000000000000000050004000500000000000000000000
def gsh_178_64:=0x500050005000400000000000000000005000400050000
theorem lowS_zo_178_64_162:Lower true dzo_178_64 roots_178 gzo_178_64 5:=lower_iso_b (d1:=dom_178) (r1:=roots_178) (T1:=gsh_178_64) [(dom_178,64)] (by decide +kernel) (lower_slice_b (T:=gsh_178_64) [(0x500000005000000000000000000000005000000050000,0,16)] (by decide +kernel) lowS_162)
def dzo_179_64:=0xf000f000f000f0000000000000000000f000f000f000f0000000000000000
def gzo_179_64:=0xf000f000f000e0000000000000000000f000e000f000a0000000000000000
def gsh_179_64:=0xf000f000f000e0000000000000000000f000e000f000a
theorem lowS_zo_179_64_162:Lower true dzo_179_64 roots_179 gzo_179_64 6:=lower_iso_b (d1:=dom_179) (r1:=roots_179) (T1:=gsh_179_64) [(dom_179,64)] (by decide +kernel) (lower_slice_b (T:=gsh_179_64) [(0xa000a000a000a0000000000000000000a000a000a000a,0,1),(0xf0000000f00000000000000000000000f0000000f0000,0,16)] (by decide +kernel) lowS_162)
namespace S_243
def pG:List (Nat×Nat):=[(1,33),(1,65),(1,129),(2,18),(2,34),(2,130),(3,19),(3,35),(3,67),(3,131),(16,18),(16,80),(16,144),(17,19),(17,49),(17,81),(17,145),(32,33),(32,34),(32,160),(48,49),(48,50),(48,112),(48,176),(64,65),(64,80),(66,67),(66,82),(66,98),(66,194),(96,97),(96,98),(96,112),(96,224),(128,129),(128,130),(128,144),(128,160),(192,193),(192,194),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_243.map (·&&&dom_243)
def gM:=goal_243&&&dom_243
def NN:Nat→Nat
|4=>11
|5=>96
|6=>287
|7=>130
|8=>18
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xee552be2d4b42d79a3eb98c5b8710d66771655503a4a034f890b267
|5,0=>0xff7f0f190fe8708e78d7e4af9e3797cdb44c8f77c820fc5042c37b2c201dbe55bb7a5db5206ad8fcad7f4ac033a38ffa1801a074e97443956c0928528ec5c877df864e6830dd7c2e67b0eb72fd1723697219d6f49a6e8a269da8698c765b7e659596216a603dd6019f5fd4c5d5d25928855a8b549614ee494d9c24a87148c3d43cc4430334139c3f1783e5513d2253d0e93b74037c8b3614a353ad32b1a32110315f3304042f3c32c14d27caf26d45258cd1f5a01ec041d4dd1ceb31a61b18fad17cff17ba615487143ae13a93129871031f0fa4d0c5e50c2110a25708d8c0836104ced042a70245701b5901269001f3
|6,0=>0x46ab3469c645b0944e0d44976448cb4413a43a0842ddd425aa4245941e7a40ded3fb9b3f9de3d5173ceb83ccf53b7403a6c5398b938e9c380ae377e3375bc36ab7369f436416363d135eb3359ff3517b34dae3421a3304530ad62e0942a47d29a0129690295dc28d8128c4d28522271dc250cd24a072477e23dad2251621aec213c62122b205be1fa1a1f1a31eaf31e1a01dccc1daa61d70f1d09c1cf701c7f41c0221c0181a9a21a9571a17019c8a196771928b18f2518d7918b8317cff1735817354170d416cc716ae7164ef164d71618a15b0815af2157b615487152a114d3114c061449713d51134d01331c12db51257e122551151e0fae70fa9e0f5a10ed980ec500e6660e5b20df6e0de850d5700c8aa0be110b46109b6109237086cb083be079b20754d070cc068c9055f7049e704434034ae024d8018df0169700041
|6,1=>0xad223ac2e1a5b2ba1e92a1b749f89a9ec049dbab991ad9789e95d8a95353952cd94d29947d593f149251d90bce902ef8ff2a8f4478de228d5608c4e08b72b8b5898afa18ae218a86c88cb2883b28810287ea987962870fb86d15866d98395d827b2820ed80c027f2c47ea247e08e7d5da7d3647ce067ccc07c6e47c4a07c46e7a63279fa97995d78bc0788c5780697719d7518374cf3739ef71fd871066700e26ffec6e6ea6e3aa6e1f86cdd26c4136b7526a7516a2c8687ea678cd667736419062ff96103e60d54601d3601635fa805e94e5e4fd5db045d6c75d5d25d5325c3c35c0845ad2f5ab725946a591f75916158ef25831356ef156b275666a55a81553d9550b954d7f5410a54070532c852f0e528c25229951c5e51b9d50e6f4fbe34f5724e7ea4e3024dced4c53a4b93f4a7754944948c8b48b9348674479ec47176
|6,2=>0xff655f0668e8708e4d8ee4378e072fd79ead6d00d4e81d2d66cc43cc9f07c7702c501dc2e6ac2dc1c1931bf914be55bbe121bce84baea9bab81b53e1b4f5fb2b6cb2ae4b219ab02f9ae3a5ae194
|7,0=>0xeb5a9e4459d82cbd79ead5decd211acc556c767cc430ec07edc0431ba2cfba0e2b9706b8898b5668b4ca9b2ae4afe23ae86aa894ca2ab9a04db9d19a9c5c89a91c9a7c691bba919ff8f7bd8ca7c8ac2b8811d85bb684f7b84e62833a88329b7e4717caf07bf0078d6c783907796776e2376d92752bd74c4a72c93715fd6e5916860666773652926523a637d361d085e1f75dc9c5ca605bf8e5be635b5cb59edc59e2359c515932458274581f0564335551652a25501e94fd9c4e1bd4b1894afe2496384727c461773e0503d6c03b12c395f238aa7383ac363d136222322cd31e4b31508311a03025f300542e0942c7612c3b62af7d2acd227d89271cc2512d2232d21bbc1ff261ec8d1d09c1b1591a9c915a3e158e11352e12ae811b0110819106ed0ffd40dba90d94a0cee70cae20c015093b508f3a08ee3068c90281000cff
|7,1=>0xf4399f2e8f
|8,0=>0xf2e8fb1600a4c039ee737a9f6762ce655b03d1cf2b3091d06f1972114e15127920fc840af0f06f930358a021a9
|9,0=>0x7a9f6
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000c000c000f000f000c000c000a000a00080008000a000a00080008c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000cf000f000f0000000f000f000f0000000a000a000a0000000a000a000a0000f000f000c000c000f000f000c000c000f000f000c000c000f000f000c000cf000a000f000a000f000a000f000a000f000a000f000a000f000a000f000ae000e000e0000000e000e000e0000000e000e000e0000000e000e000e0000f000f000f000f000f000f000f000f00000000000000000000000000000000f000f000f000f000f000f000f000f000f000f00000000000f000f00000000f000c000f000c000f000c000f000c000f000c000f000c000f000c000f000cf000f000f0000000f000f000f0000000c000c000c0000000c000c000c0000f000f000f000f0000000000000000000f000f000f000f000000000000000000000000000000000000000000000000f000f000c000c000f000f000c000cf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a30003000c000c00030003000c000c00030003000c000c00030003000c000cf000f000f000f000f000f000f000f000f000f000f000f0000000000000000
|0,1=>0xf000f000a000a000f000f000a000a000e000e000a000a000e000e000a000af000f000f000f000f000f000f000f000a000a000a000a000a000a000a000a0000f000000000000000f000000000000000f000000000000000f00000000f000f000a000a000f000f000a000a000f000f000a000a000f000f000a000ac000c000c000c000c000c000c000c000c000c00080008000c000c00080008f000f000f000f000e000e000e000e000f000f000f000f000e000e00000000f000f000f000f000c000c00000000000f000f000f000f000c000f00000000f000f000f000f000f000f000f000f000c000c00000000000c000c000c000c00000000000000000000000000000000f000f0000000c000f000f0000000cf000f000f000f000f000f000f000f000f000f000f000f000c000c000000000000000000000000000000000000000030003000c000c00030003000c000cf000e000f000e000f000e000f000e000f000e000f0000000f000e000f0000f000f000f000f000f000f000f000f000c000c000c000c000c000c000c000cf000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000f000f00000000000f000f00000000000f000f00000000000f000f00000000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e
|0,2=>0xe000e000a000a000e000e000a000a000e000e000a000a000e000e000e000e0000c0000000c0000000c0000000c0000000c0000000c0000000c0000000cf000f0000000c000f000f0000000c000f000f0000000c000f000f0000000cf000f000c000c000f000f000c000c000f0000000c0000000f0000000c0000f000f000f000e000f000f000f000e0000000000000000000000000000000000000000000000000000000000000000f000f000f000c000f000f000f000ca000a000a000a000a000a000a000a000e000e000e000e000e000e000e000e000000000000000000000000000000000000f0000000c0000000f0000000cf000f000f000f000f000f000f000f000c000c00000000000c000c00000000f000f00000000000f000f00000000000e000e00000000000e000e000000003000300030003000300030003000300030003000300000003000300030000f000f000f000f0000000000050005000f000f000f000f000000000004000400000000e000e00000000000e000e00000000000e000e00000000000e000ef000f000f000c000f000f000f000c000f000f000f000c000f000f000f000cf000f000f0000000f000f000f0000000f000f000f0000000f000f000f0000c000c000c000c000c000c000c000c000c000c000c0008000c000c000c0008
|0,3=>0xf0000000f0000000f0000000f0000000f000000000000000f00000000f000f000f000f000f000f000f000f0000000f000000000000000f0000000000000000f000f00000000000f000f00000000000f000000000000000f0000f000f000f000f000f000f000f000f000f000f000c000c000f000f000c000c30003000f000f00030003000f000f00030003000c000c00030003000c000c00000000f000f00000000000f000f00000000000f000e00000000000f000ef000f000f000f000f000f000f000f000f000f000f0000000f000f000f0000a000a000a000a000a000a000a000a000f000f000e000e000f000f000e000ee000e000e000e000e000e000e000e000e000e00000000000e000e00000000e000e000e000e000e000e000e000e000e000e000a000a000e000e000a000a5000500050005000100010001000100050005000500050001000100000000f000f000f000f000f000f000f000f000f000f000f000f0000000300000000f000f000f000f000f000f000f000f000b000b000b000b0000000000000000e000e000e000e000e000e000e000e000e0000000e0000000e0000000e0000c000c00000000000c000c00000000000c000c00000000000c000c000000003000300030000000300030003000000030003000300000003000300030000
|0,4=>0xf000f000b000b000f000f000b000b000f000f000b000b00000000000000000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000cf000f000e000e000f000f000e000e000f000f000e000e000f000f000e000ea000a000f000f000a000a000f000f000a0000000f0000000a0000000f000000000000000000000000000000000000f000f000f000e000f000f000f000e0000f0000000c0000000f0000000c0000000f0000000c0000000f0000000cf000f000f000f0000000000000000000f000f000f000f000000030000000000000000000000000000000000000000c000f000c000c000c000f000c000cc0004000c0004000c0004000c0004000c0004000c0000000c0004000c0000f000f000f000f000f000f000f000f000f000f000f000f0004000400040004c000c000c000c000c000c000c000c000c0004000c0000000c0004000c0000f000f000f000a000f000f000f000a000f000f000f000a000f000f000f000af000f000c000c000f000f000c000c000f000c000c000c000f000c000c000c3000300030003000300030003000300030001000300000003000100030000f000f000f000f000f000f000f000f00000000000300030000000000000000f000f000f000f000f000f000f000f000e000e000e000e000e000e000e000e
|0,5=>0x40004000400040004000400040004f000f000f000f0000000000000000000b000b000b000b000000000000000050005000500050005000500050005000500000005000000050000000500005000500040004000500050004000400050005000400040005000500040004f000f00030003000f000f00030003000f000f00030000000f000f00030000c000f000c000c000c000f000c000c000c000f000c000c000c000f000c000cf0003000f0000000f0003000f0000000f0003000f0000000f0003000f0000a000a000e000e000a000a000e000e000a000a000e000e000a000a000e000e300030000000000030003000000000003000300000000000300030000000000000000c000c00000000000c000c00000000000c000c00000000000c000c00000000f000f00000000000f000f00000000000a000a00000000000a000a5000d0000000c0005000d0000000c0005000d0000000c0005000d0000000cf000f000f000f000f000f000f000f00030003000c000c00030003000c000c00000000a000f00000000000a000f00000000000a000e00000000000a000e000000000000a000000000000000a000200020002000a000200020002000a00000000c000c00000000000c000c00030003000c000c00030003000c000c
|0,6=>0xf0000000f0000000f0000000f0000000f000f000f000c000f000f000f000c300030003000300030003000300030003000300030003000300030000000000000000000000000000000000000000e000e000e000e000e000e000e000ec000c000f000f000c000c000f000f000c000c000f000f000c000c000c000c4000400040004000400040004000400040004000400040004000400040004f000f000f000f0004000400040004000f000f000f000f00040004000400040000f0000000f0000000f0000000f0000000f0000000c0000000f0000000c0000e0000000e0000000e0000000e0000000e0000000e0000000e0000000ef000e000f000e000f000e000f000e000f000e000f000e000f000e000f000ef000f000f000f0000000000000000000f000f000f000f000f000f000c000cf000f000f000f000f000f000f000f000000000004000400000000000400040000000000000000f000a000f000a0000000000000000000f000a000f000a3000300030003000300030003000300020002000200020002000200020002f000c000f0000000f000c000f0000000f000c000f0000000f000c000f00003000300030003000300030003000300030000000300000003000000030000c000c00000000000c000c00000000000c000f00000000000c000f00000000
|0,7=>0xb000b000b000b000b000b000b000b000b000b00000000000b000b00000000f000f00040004000f000f00040004000f000f00040004000f000f00040004f0000000f0000000f0000000f0000000f0003000f0000000f0003000f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f00000000500050005000500050005000500050005000500050005000500050000000020002000a000a00020002000a000a00020002000a000a00020002000a000a50005000500000005000500050000000500050005000000050005000500000000000000000000f000f000000000000000000000000000f000f00000000c000c000c000c000f000f000c000c000c000c000c000c000f000f000c000c0000000000000000000000000000000000000000e000e00000000000e000e30003000f000f00030003000f000f00030003000f000f0000000000000000a000f000a000f000a000f000a000f000a000f000a000a000a000f000a000a5000500000000000500050000000000050005000000000005000500000000d000d000c000c000d000d000c000c000d000d000c000c000d000d000c000cf000f000f000f000f000f000f000f0000000000000000000f000a000f000a0000f0000000f0000000f0000000f0000000f0000000a0000000f0000000a
|0,8=>0xf000f000f000f0000000000000000000f000f000f000f0004000400040004f0000000f000f000f0000000f000f000f0000000f000c000f0000000f000c0000000000000000000000000000000080008000c000c00080008000c000cf0003000f0003000f0003000f0003000f0003000f0000000f0003000f0000d000d000d000c000d000d000d000c000d000d000d000c000d000d000d000c5000500050005000500050005000500050005000000000005000500000000a000a000f000f000a000a000f000f00080008000c000c00080008000c000cf000f000f000f000f000f000f000f0003000300000000000300030000000000000000f000f00000000000f000f00000000000f000f0000000000000000c000c00000000000c000c00000000000c000c00000000000c000c000c000c500050005000500050005000500050004000400040004000400040004000400000000f000f00000000000f000f00000000000e000e00000000000e000ef0000000f000f000f0000000f000f000f0000000f000a000f0000000f000af000f000f000f000f000f000f000f000f000f000f000f000c000c000c000c0000f0000000f0000000f0000000f0000000f0000000f0000000c0000000cf000f000f000f000f000f000f000f00040004000400040004000400040004
|0,9=>0xf000000000000000f000000000000000c000000000000000cf000f000f000f0003000300030003000f000f0000000000030003000000000000000000000000f000f000c000c0000000000000000000f000f000c000cf000f000f000f000f000f000f000f0000000000000000000f000f000c000cb000b000b000b0000000000000000000b000b000b000b0000000000000000f000d000f000c000f000d000f000c000f000d000f000c000f000d000f000c00000000300030000000000030003000000000003000000000000000300000000500000005000000050000000500000004000000040000000400000004f000f000f000f000f000f000f000f000f000e000f000e000f000e000f000ef000f000f000f000f000f000f000f000f000f000e000e000f000f000e000ef000f00000000000f000f00000000000f000000000000000f00000000000000000000000000000000000000000000c000c000c000c000c000c000c000cf000f00000000000f000f00000000000f000f000000000000000000000000f000f000c000c000f000f000c000c000f000f000c000c000c000c000c000c0000c0000000c0000000c0000000c0000000f0000000c0000000f0000000cf000f00000000000f000f00000000000f000c00000000000f000c00000000
|0,10=>0xf000f00000000000f000f00000000c000c000c000c000c000c000c000c000f000f000c000c000f000f000c000cf000f000f000f000f000f000f000f000f0003000f0000000f0003000f0000c000c000c000c000c000c000c000c000c000f000c000c000c000f000c000cf000f00030003000f000f00030003000a000a00020002000a000a00020002f000f000a000a000f000f000a000a000f000f000e000e000f000f000e000ec000c000c000c000c000c000c000c000c000c000c0000000c000c000c0000000000000000000000000000000000000000000000000000f000f000c000c0000500000004000000050000000400000005000000040000000500000004f0000000f00000000000000000000000f0000000f000f0000000000000000f000f000f000f000f000f000f000f0000000000000000000c000c000c000c0000000000000000c000c000c000c0000000000000000000c000c000c000cf000f000f000f000f000f000f000f000f000f00000000000f000f000c000cf000f000f000f000f000f000f000f0000000c0000000c0000000c0000000cc000c000c000c000c000c000c000c000c000c00000000000c000c00000000b000b000b000b000b000b000b000b000b000b000b000b0000000000000000
|0,11=>0xf000f000f000f0005000500050005000f000f000f000f00040004000400040000d0000000c0000000d0000000c0000000d0000000c0000000d0000000cf000f000f000f00000000000f000f000f000f000f000f00000000000c000cf000f000f000f000f000f000f000f000f000f000f000f000f000f000c000c00000000000000000000000000000000f000f00040004000f000f0004000400000000000000000000000000000000f000f000f0000000f000f000f00008000800080008000800080008000800080008000c000c00080008000c000c00000000f000f00000000000f000f00000000000c000c00000000000c000cf0000000f0000000f0000000f0000000f000f000f0000000f000f000f0000a000a000f000f000a000a000f000f000a000a000f000a000a000a000f000af0005000f0004000f0005000f0004000f0005000f0004000f0005000f0004f000f000f000f000f000f000f000f00000000000c000c00000000000c000cf000f00000000000f000f00000000000c000c00000000000c000c00000000000000000000000000000000000000000000e0000000e0000000e0000000ec000f000c000f000c000f000c000f000c000e000c000e000c000e000c000e300030000000000030003000000000003000300000000000f000f00000000
|0,12=>0xf000f00050005000f000f00050005000f000f00040004000f000f00040004a000a000a000a000e000e000e000e000a000a000a000a000e000e000e000ef000f000f000f000f000f000f000f00050005000500000005000500050000f0000000f0000000f0000000f0000000f000e000f000e000f000e000f000ef0005000f0000000f0005000f0000000f0005000f0000000f0005000f0000f000f000f000f000f000f000f000f000c000f000c000c000c000f000c000cf000f00000000000f000f00000000000f000f000c000c000f000f000c000c000000000000000000000000000000000000f000000000000000f00000000f000f000f000f0000000000000000000f000f000f000f0000000f000000000000f0000000f0000000f0000000f0000000a0000000a0000000a0000000af000f0000000f000f000f0000000f000f000f0000000a000f000f0000000af000f00000000000f000f00000000000f000f000e000e000f000f000e000e30003000f000f000000000000000000030003000f000f0000000000000000f000f000f000f000f000f000f000f00030003000f000f00000000000000000000000000000000000000000000000050005000400040005000500040004f000f000f000f000c000c000c000c000f000f000f000f000c000c00000000
|0,13=>0xf000f000f000f000f000f000f000f000f0005000f0000000f0005000f000000000000000000000000000000000000f000f000f000a000f000f000f000af000a000f000a0000000000000000000f000a000f000a0000000000000000f000f000f000f000f000f000f000f000f000a000f000a0000000000000000f000f000f000e000f000f000f000e000f000f000f000e000f000f000f000ef000f000f000f000f000f000f000f000f000f000a000a000f000f000a000a3000300030003000300030003000300030002000300020003000200030002000000000000e000000000000000e000000000000000e000000000000000e00000000000000000000000000000000f000f00000000000f000f000c000cf0005000f0005000f0005000f0005000f0005000f0000000f0005000f00000000000040004000000000004000400000000000400040000000000040004c000c000f000f000c000c000f000f000c000c000f000c000c000c000f000c50005000500040005000500050004000500050005000400050005000500040000300000003000000030000000300000003000000000000000300000000f000f000f000f000f000f000c000c000f000f000f000f000f000f000c000c00000000000000000000000000000000f000f000f000f000f000f000c000c
|0,14=>0x50005000000000005000500000000000d000d000c000c000d000d000c000c0000000030003000000000003000300000000000300030000000000000000f0000000f000e000f0000000f000e000f0000000f000e000f0000000f000e3000000030000000300000003000000030000000f000000030000000f0000f000300000000000f000300000000000f000300000000000f000300000000f000f000f000f000f000f000f000f0000000000000000000f000f00000000f000f000f000f000f000f000f000f000d000d000c000c000d000d000c000c00000000f000000000000000f000000030000000f000000030000000f0000f000f000f000f0000000000000000000f0000000f000f0000000000000000f000f000f000f0000000300000000000f000f000f000f00000003000000003000300030003000300030003000300030003000200020003000300020002f000f00030003000f000f00030003000f000f000300030000000000000000f000f000f000f000f000f000f000f000f000a000f000a000f000a000f000a30003000300020003000300030002000300030003000200030003000300023000300030003000000000000000000030003000f000f0000000000000000f000f000f000f000f000f000f000f000f000c000f000c000f000c000f000c
|0,15=>0xe000e000a000a000e000e000a000a000e000e000a000a000e000e000a000af0000000f0000000f000f000f0000000f0000000f0000000f000f000f0000f000f000f000f000f000f00000000000f000f000f000f000f000f000000000000000000000000000000000000000000003000000000000000300000000f000f00000000000f000f000f000f000f000f00000000000f000f000c000c0000000000000000000000000000000000000000c000c00000000000c000cf000f000f000f000f000f000f000f000f000300000000000f000300000000f000f000c000c000f000f000c000c000f000f000c000c0000000000000000f000f0000000f000f000f0000000f000f000f0000000c000f000f0000000c0000000000000000f000f000f000f0000000000000000000f000f000c000c0000f0000000f0000000f0000000f0000000e0000000e0000000e0000000e1000100010001000100010001000100010000000100000001000000010000a000e000a000e000a000e000a000e000a000e000a000e000a000e000a000ef000f000f000f000f000f000f000f00030003000300000003000300030000f000f000f000f000f000f000f000f000500050004000400050005000400040000300000003000000030000000300000002000000020000000200000002
|1,0=>0xf000f000f000f000a000a000a000a000f000f000f000f000a000a000a000af000f00000000000f000f0000000000030003000000000003000300000000f000f000f000f000c000c000c000c000f000f000f000f000c000c000c000cc000c000c000c000c000c000c000c000c000c000c000c0000000000000000f000f000f000f000f0000000f0000000f000f000f000f000f0000000f00000000000000000000f000f000f000f0000000000000000000c000c000c000cf000f00000000000f000f000c000c000f000f00000000000f000f000c000c000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000f000f000f000f0000000000000000f0000000f000000000000000f0000000f0000000f000000000000000f000030003000f000f00030003000f000f00000000000000000000000000000000f000f000f000f000c000c00000000000f000f000f000f000c000c00000000c000c000c000c000c000c000c000c00080008000800080008000800080008f000f000f000f000f000f000f000f00050005000000000005000500000000
|_,_=>0
def sP:Nat→Nat
|0=>0x10144208058383c050880c40020282410030f8380a0801838040f02810060e01074001c0400c20130284406100d8141211018681c0204844061907008121101838300200044280e0101412170880c1c02000300616010541803010540003010042a00088502602028200610078141812030080a11018401e000402c1c0d02830160a028241007030080a04018080200
|1=>0x70d40a090880c1c021a0242203070780433088481c0601014220b190380a090180802150282406021808c0a090880c5e0e000245a080184c0405108b01c02028242203070080a2b15044060e010002203148383c000880c1c021400018040189c0405018981c020282444080184c04050880c04250282422030700848090880c1c1e118001003070081a05110442413
|2=>0x49101003070780a21218380405048300627010142203011080a090880c1c0200104420c090380400060200640010141803098087e050600c26021f0142207098087a050600c043b02824420401838040001838043a0282472110384c04051c044060e0100038031b8380a09018981c1e0100022031b0380a090400c1c06010141803010540a09088480602128002203
|3=>0x18c40400018380452028242203071440a091e0300627010141803011400a090880c1c02278241803138080011070089c0504810060200814124d0880c1c1e00044160e26014124b0880c1c02028200613011280a110183804490484406480700800110191c0405048300602008001211018383c0223044062c07008002106048260202884180b080141211019140405
|4=>0x604406102e01412210880c0425028247803010040a09018080200048301003098080a0c0182804050496c06022b8141211058281c0504820065a098080a112c8481c020000c1c582a81412210903804570000c20562a814120c0189c041502810220307008000c018584e020600c6e020282418030114c0a090580c4c0e02824220b071500a0901808a601028241804
|5=>0x19b41c05048e422120183804000880cd80e0101412080880c1c02350244211058401c0504844060e011a40a090880c20023081412110184c0468028242267018383c05049982203070080a090880c1c023281412113200c260e0102422030709c04050e044060e318141211310380400048440660070080a090880c1c022f02422032d038040004884220e011740a09
|6=>0x2824ee110184c040504844060e0f008be000400c260e0115c0a110183804760282422032d04c040504844060e01000ea0906044240307008001101838e80202824420307008ae00048440672070080009089c4060e01024220307008e005048841803080080a0937844060e01014122108848260e0101406022b958000901898260e01014121101838046e02824220b
|7=>0x28241804018c4040504884220e011840a090880c1c8601000120c0880c04850282406130700908050480c4c0e0101412114180c1c02028242213070090205048701003070780a0c0880c0480028242203071fc0405049f82203098080a09108200613070080a112c80c1c0200024227d01838040504844060e3d814121101838f400048440602128141211090380479
|8=>0x10c00a090880c1c0248814120c0882c061002824229001838040504844060e0f0091e090604406100f01412112180c1c0202824228e01838040504884100b070080a092d844060e01014120c0880c1c02000242203070091a05048702203200380a0910844ce0e0101412114600c1c02028242203458380405048441603072280a090880c1c02448141221018380488
|9=>0x4844060e012640a090880c1c024c0141211018384e02000302203098080a0908a5c060e0101412960880c1c020282410110184c046b02810220307008000510a541c0202824100307008600504844060e011300a090880ce49401014121101a481c0200024220307008b80004884220e011280a09060442403098080a11019c8260202824220307008460004844240e
|10=>0x880c1c020282410110183804a202884240e0115c0a090e0440610070001211018d81c05048440694011700a090880c1c02500242203070093e0504844060e012780a094e044060e0101412211e00c1c020282422033603804000483008110183804000880c1c02198240811018380405048453403070080a090880c26022e014120c0880cda0202824060e01158aa05
|11=>0x70080a0908ab4060e0101412082c80c1c020282418040880c26020284406ac070080a090880c1c025581412aa0880c1c02028243811018a41c05048842203548080a090880c6c0e0101412a80880c1c02028242203070094e05048200672070080a090880c1c025302442110903804000880c1c1e0115800390880c260e0101422590903804050483006020081412a3
|12=>0x4adc1803070080a090880c1cb6010141211038481c0200044160e010f40a0908ad4060e0101412215781c1c020282410110183804b402844061f0701412110183804b2028242203070081e050484406b1070080a09060202203098080a115800c1c020002438110184026050488822030700800090880c260e010f40a3c0880c046b028247211058380405048855c03
|13=>0x880c1cc0010241803138080a220880c2602028242203070097e090880c1c025f01412110183804bd02825781101838040504844060e011500a095d844060e0101412210881c260202825741103838040504844060e010340a090400c1c022e014120404044060e0101444af01838040504844060e012e40a0910844160e0f0141211018383c0240014f003070097005
|14=>0x400c1c0202824101101b381c0504844060e013340a0908b30060e010141211658481c0202824220365038040504830060e013200a090600c1c020e80012c90880c1c0202824220308008600504844060e0131c12c50880c1c02028242203070584e0262044060e0101412110183804c204820060e598080a110183804c10282422031b8380405048202203098085c05
|15=>0x42815ae1101838040504845ac03070080a0904044060e012000a110183804d50002438080184c1c0202844160e012880a090600c26020e81412170880c1c020282444110903804050484406d4070080a09019004c0e0101412110183804d30282410cb01838040504844060e013480a091c80c1c022b81412d00880c1c02028242203070088c0967844060e010141244
|16=>0x4844060e012100a0908b8c061007014120c018c4040004844060e013880a090880c1c0270824421170038040504845be03070080a096f044060e0101412110183804dc04b6c2203070080a090200c1c020e814120320038048402824440801838040504844060e011d412da0880c1c1e01000220307009b205048441603390380a090880c1c026c01412080880c1c02
|17=>0x880c1c02028242203778380405048440629070780a090604406400101412110183804057702422ed01838040504844060a070080a090882c060e2e014121107009d80504845d60307008000908ba80613070080a1101ba41c0202824220e013a00a0908848060e0139c12110183804e6048440613013540a090880c1c027281412110183804007202418113200c1c02
|18=>0x28240626070780405048841803098080a091e044060e0101412f60880c1c0202824220307009ea0504844060e013d00a090882c240e3981412110900c042502824381101839e605049102203070780a090600d420202824420c01838040004844060e013c80a090880c1c0278814121105838e62e02824220b098085c0504844060e013c00a091e030063101014122a
|19=>0x7e01412110183804dc0880c800e01014124d0880c1c5c0282422030705804090880c20027d014123c02044060e0101422030800970050480c040102825f61101838040504b241003070080a090882c2413070080a087580c1c020282422f9018380405048102203070080011018380400770244208018383c02028840803070080a090880c1c0202be012f70880c1c02
|20=>0x8990060e0102422af0380c1c0202824220b0184c1c020282422030825004050484406ff07014122210844060e0101412d10880c1c02028242203070080a8704bf8220e0101412110184c046b0282422030804c040504844060e138080a210880c1c1e010141211018a41c02028241803138080a097e80c1c025c014120c0400c260202844060e01001f0090880c1c02
|21=>0x10b800091e0302203070080a090880c8010070080a09108202203070080a09062bc060e01014121c0400c1c02028244411018380405048440613070083a0504820060e011cc0a090880c1c0280814120c0880c1c020002422030700a000504b68101101838040504844060e0126c12116580c1c02028242207018383c02028243811018401c05049102203070080a09
|22=>0x7008ac0004830220308038040504845c603070080a090600c1c020e81412110183804fa0282422ea01838040504820220701838040504820220307078040502044060e01014121101838040043824220307009700504820220307290040504844060e012d00a090880c1c310100012110183804c3048b42203070080a090604406130101412110183a040204844060e
|23=>0x70090a0504884220309838040504844240307008e60504844060e012000a090880c260e0115c0a090880c1c022e81412110580c1c7302824220309808ac0504b682203070080a090880c1c0264014121101838041d00024220e014100a090e044060e010b80a090880c1c026a814121101838040581844060e508080a090880c1c02398b80a090880c1c02350242203
|24=>0x2824420c01838040504845c01201838040504c1c2203070080a091e0202203070080a090880c800e0f0080a0906044060e011700a090880c1c02308141211058481c02028242203098380506028259211018380405049f0101101838040504845d603070080a090882c0610070141211018401c1e02824220308038050504830063101014121c0880c1c1e028242203
|25=>0x7008002206044060e01014120c0882c060e0101412080880c260e01014421101838040004844060e0f008be0504830221201838040504830220307008000504820220385838040504b44181101838040504844060e012280a0906044060e0141412110183804008502410118480c1c0202824220307008940504a742203070080a090880c1d08010141211019b41c02
|26=>0x380c1c0202824220307008c60504844060e011e40a090880c1c1e011580a090880c260e011cc0a090880c1c580101412210880c200e01014120c04044060e010141211018400456028247811018380405048e4101101838040504830081101838040504844060e138080a093e044060e0101412110380c1c020002422030700a1805048455e03070085c05048442403
|27=>0x48441603070080a0908abc060e0101412110900c1c0202824220307008000504844060e01414121101838620202824227801838040504844060e010b80a09062742203070080a0906044060e01014121101838f4050480c04572b0141211019681c0202824220320038040504845c61201838040504844060e013741211018380430028242267018401c02028243811
|28=>0x11018380405048302203070080a090880c1d0d01014121101838040004bf42203070080a090880c1c02028242207018380405048842203070080a0904044060e01014121101838041d02824220307008ac05
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32502d50285023501e50195014500f500a500550005
|5,0=>0x1af61a961a3619d61976191618b6185617f61796173616e51686162615c61566150614a6144613e61386132612c61266120611a6114610e6108610260fc60f660f060ea60e460de60d860d260cc60c660c060ba60b460ae60a860a2609c60966090608a6084607e60786072606d50676061605b6055604f60496043603d60376
|5,1=>0x26c62675261625b6255624f62496243623d62376231622b62256220521a6214620e6208620261fc61f661f061ea61e461de61d951d361cd61c761c161bb61b56
|6,0=>0x421741a7413740c740573fe73f773f073e973e273db73d563ce73c773c163ba73b373ac73a5739e73977391638b6385637e7377737073697362735b7354734d7346733f73387332632b7324731d731673106309730272fb72f472ed72e672df72d872d172ca72c372bc72b572ae72a862a1729b6294728e62877280727972727
|6,1=>0x5d975d275cb75c475bd75b675af75a875a2659c6595758e75877581657a7573756c7565755f65587552654b7544753d7536752f75287522651b7514750d750674ff74f874f174eb64e474dd74d674cf74c874c264bb74b474ad74a6749f74987491748a7483747c7475746e7467746074597452744b7444743d7436742f74287
|6,2=>0x78e77886781777a7773776c7765775e7757775077497742773b7735672e77286721771b6715670e7707770076fa66f556ee76e866e176da76d376cc76c576be76b776b076a976a2769b7694768d7686767f76787671766b6664765d7656764f76496642763b7634762d7626761f76187611760a760375fc75f575ee75e775e07
|6,3=>0x946793f79387932692b7924791d7916790f7908790178fa78f378ec78e578de78d778d078c978c368bc78b578ae78a868a1789b6894788d7886787f78787871786b6864785e6857785078497843683c7835782e78277821681a7813780c780577fe77f777f077e977e277db77d477cd77c677bf77b877b177aa77a3779c77957
|6,4=>0xa186a117a0b6a0479fd79f859f179ea79e469dd79d679cf79ca59c379bc79b579ae79a779a1699a7993798c7985797e7977797079697962795b7954794d7
|7,0=>0xbdc8bd57bce7bc77bc07bb97bb27bac6ba48b9d7b976b907b888b826b7b7b738b6c7b657b5e7b577b4f8b487b417b3a7b337b2b8b247b1d7b176b107b097b036afc7af48aec8ae48add7ad67acf7ac78ac07ab97ab27aab7aa38a9d6a967a8e8a877a807a7a6a728a6a8a637a5d6a558a4e7a477a416a3a7a337a2d6a258a1e7
|7,1=>0xdb36dad6da67d9f7d978d916d8a7d828d7a8d737d6c7d648d5c8d557d4d8d458d3e7d377d2f8d278d207d197d127d0b7d038cfd6cf58ced8ce67cdf7cd78ccf8cc78cbf8cb78cb07ca97ca27c9a8c937c8c7c857c7e7c777c6f8c687c608c588c508c497c427c3a8c337c2b8c247c1d7c167c0f7c096c027bfb7bf38beb8be47
|7,2=>0xdc08db97
|8,0=>0xe3c7e357e2f6e287e226e1b7e147e0d7e067dff7df87df17dea7de37ddd6dd67dcf7dc87
|9,0=>0xe436
|_,_=>0
def wAt:=mkWire dB 270 244 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x70460609f08839088380883913815188250883808020060c70883908838060c708839088380883908838028251882508839088380884107009060c708839088380604808839088390880d07009010850880d0882508825070251e0c7088390883808825080201084c0880d060c708839088381084c0880d060c70883908838088b90700f0384501839108780880d070850880d088250880d060780883907025
|1=>0x71e108817070250707b0882507046070750880f18802088380883902825010fd088250282507046071cd0880b058170180908839070090880d0883b028250883a20044098090802707009358150700b0903b0182501842070090702d01025018090880905817018090403808825028251880d07044089870903b2f8160707b01025070750880f0182508839070e6108252b9590883b028250883a088250715d
|2=>0x704607025060270883908848018250880d070860880d0724d088000600b0883910839071cd0880b070860880d07009088392f8150707b0880d0882508959028250883a070250700d0403b08825071e50880d0400b088252b8250704608839088380721f0880220047098090890009809070250f0474100f09815088090102508825041af088253e00b0401508825028251880a08838070e60400d018250880d
|3=>0x6078088390702507045070250881d0700d0884a0400d08825072bd088270195d070460602708839010250880907027070e41082508839071cd0880b1f8160400f088250880d01825028250704702825088250195d07046060c708839088385284552025088250182502825508090403808825358020700b028254e825088390702108825088394d825358160700b08027070250282518825088380715d07025
|4=>0x700b010850880d08825520090701708027019cd0880b1083b0880d640150884b08b190f00f1381518825088386182518816088380984407025080200700908825088255081504038188250883908838108390880d428150980b07025098470602510827108780880d0600b07045070452f8250707b01025088270183901825028250884a0182501971088390700d088250883a012cd09844070250804b01825
|5=>0x1083b0880d08839088380707b0102507025060020883908047108400600b0883901a8704038070253c0255980e09844640160884b0881f0700d0581701049028250883908838508160403808825220276e82505814018090e01d070250881d0183918802028250883802825071cd0880b108420880d0702535825088250707307025170250700f070850880d019cd0880b088250882568827088394001535825
|6=>0x700b0702507009070251882508838010250880d4a0090702718825088390883809847070250882507025088390600008839700466e825058140883913815088380702308825088390884e07025060c7088390883808be90403a0882507025088bb0700f060270883906002088390880d088250602707045060000883908900070790880b070e608849088090700f108090880d0883904038088250282507045
|7=>0x883a02825088381881608838088b90700f07025088391881508838028250700f0883908025070090880d08825088270704508809088250600d070450880f07025088250880b07078010250282508839398250880b0400908825358160700b019cd0880b010250700d0700908809058450100d05817018090183908827070250180907009070271880908838108390880d060150883908802028253c00d08817
|8=>0x883801025088090980b070250880d07025018250880b358250700b07025070460900b018250100d0880b070250883a04009088250884b018250880f028253c00e08817088090700f0707308809188260883804038088250880b0700f358150700b028250883a070090883905825018090880f070450403a088253c025088170183908825010250882506027088390880202825098470702507017088252b025
|9=>0x88270700f0182502825070450883907025088250880d028250707b0102507045088390701508825088390400b088250282708839070000282508825018150600f070450601708839098170702508027070090880d0704509039018255204507017040390882507079010250600b088390903b01825018250100d09846070254a045070270401508825088bb0700f07009018090102507009028270700908839
|10=>0x700d0880d088250880f0883a018090882701825028250282708838088170700f08839089590883a1880a088380883b0883a070750880f0980907025090090182505814018091083b0880d0800d07009088090700d0707a010251080b0880d010250883a070250880b011590883a070090880d0882507045070090883a06025088390400d088250602708839188250883804015088250700d028254a04607027
|11=>0x8839010150282508815
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x2630000242000021300001e300001d1000000000001c1000000000001930000000060400005c40000000152048c0000000000000010200000d3000000002c80000000000000000000000000248000000000001c805200c800000000120000001000000000000000000000
|5,1=>0x4240fcc00000000000000000000000000003c300003840dc434300000000c4c00000000000bc800000002b400000000a480000000000
|6,0=>0x28c4a1227c89d200009b2264800025c8000254892324448f2230c000228800000000000000873210c82220087d31f047a200007821d887421c887021b886c200006930000000198c64200006220000000180800000005e2170859300005811588542000051313c84c312884911204462
|6,1=>0x3bc40003b48eb200000003a84e82394ce233808df13748da33608d713584d51348c00033cc0000000cd232c80003284c7300000000000c6100000003144c232fccbe100000002f08b932dc80000000b522cc8b210000b020000ae20000ac20000aa200000000000a820000a530000a41
|6,2=>0x50893f300013c34e880004e45372000000000000004d493324c492e300012b34a48000498d25148c920347891b300011a146440000000000460516245091310000000000110300010f100010c3428908241c5052408d0023f880003f080003ec4f923e040003d88f420000f223c08000
|6,3=>0x6249872614982360097e2000000000000005f0800000017a25e457725d857515cc971200016f200016d25ac9692000000000016810001671590c000584c0000001601574d5c100015b15649563554400054c9512540400000014e253454c152880000001482000000000014625145441
|6,4=>0x1b336c49ae36b09ab16a480006a05a626909a3168499e300019b366859820001962650992264098e200018c20000000000000000018b1
|7,0=>0x8cca3128bca2d28aca29289ca25288ca21287ca1d286ca19285ca15284ca11283ca0d282ca09281ca05280ca0127fc9fd27ec9f927dc9f527cc9f217c09ee27b09ea27a09e627909e227809de27709da27609d627509d227409ce27309ca27209c627109c227009be26f09ba26e09b62
|7,1=>0xab8aac2aa8aa82a98aa42a88aa02a78a9c2a68a982a58a942a48a902a38a8c2a28a882a18a842a08a8029f8a7c29ec67a19e0a7629d0a7319c867029bc66d29aca69299ca65298ca61297ca5d296ca59295ca55294ca51293ca4d292ca49291ca45290ca4128fca3d28eca3928dca352
|7,2=>0xac86b02
|8,0=>0xb0c6c21b046c010002bf1af86bd1af06bb1ae86b91ae06b71ad86b51ad06b31
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0x500000123000045400010100004000000c4000020000007700001d8000066000018c00004c000011000004000000cc0000320000088000020000005400001400000480000110000040000009000001c0000060000014000004000000c0000020000004000000
|1=>0x35dc000d3f000279c0009c500025dc0009000002200000809000201c0007770001dcc000767000180000057700015cc00056700014cc000446000110c00040200010000003330000990000210000072c0001c9000063400018900006080001480000514000142
|2=>0x205dc00814200204cc008112002044400807600201d000801200200140080030020008008000001c7f40061490014ccc00512700115dc0045730010014002141000842000210500084080020480008020002006000801000200200080040013270004004001000
|3=>0xc000002900700a15cc02821200a0048028006008449c0205120080c8c020212008080802000400800080131670040d4001000000364d400c575003005400a101002401c008777002184000857700215cc0085370021000008252002085800821200208080081c2
|4=>0x40449c1010000401d4c10001103a149c0d316303485080d2123032858c0c8527032059c0c312303085cc0c2133024c52c09016302207cc08316f02007cc048577012079c04817701205cc04813301055dc041173010451c04042201010800400730100080040002
|5=>0x10004003080030b2748c2c95330b2549c2c15230a00000241173090108022892708a048c20a10908237dc208db308205dc2081670820554208127082000c200dab08020c820012204a401c121127048001c11316f04484241090070414c9c1051330410844104203
|6=>0x830349d04010229020888c9523232448c8010021a2059c60a16312207c44801f3120078c43010210a040840b16f102040840316f1000540400140
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x160b000000000000000002002904020000020000000200001000000200000000000002000200240003003300000004000000020000120004000002020000000002000200000200000000000000020000000202080000060004000000000000
|6,0=>0x9000c1b00004702aa98051202320e2854047800820000811b0002180000000400004759554700000ec30200002c02bf000200020025004100000038000b0004141b013a001b0270cc00020747026b0001000000000f150243559e0b00020f1f1b1b0280001c00005a02001b7f00021a00010249002b0269001723110245011b
|6,1=>0x1b0c460b1f02000000000200000a040f47131b02006500021bb900000012004817000f0000473d470004021674001b010400000c400401000002000000021912812d000302004744000000000102015900167a00370902340203001939000000120602730000450a001200990101540bad010600550004021200011b00020b00
|6,2=>0x360e7c0f193c004d2e01750130000b2202000e02011b02000100000000004b
|7,0=>0x6768b1a3a53dc852219fc20d564f217b6e77c6586abd93685c9ac0267c979c1f8484b779b286d08fbcba50c971b876a15790916131cf6653a23e32a442206c366272b464a8b0958b1d3f5f7d5b87896da6af319b20a95dcd2aab358a5f2f628c9275a0c5637ec760be3288b5a73bca4c6fc4855e274e68c1bace969d51684a4f
|7,1=>0x8368
|8,0=>0xb3d194bb5d8dcbb6b0688eae90baac68962f
|9,0=>0x1e
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 26 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_242 7 roots_242 ops++addP pm 1 dom_115 7 roots_115 ops++addP pm 2 dom_210 5 roots_210 ops++addP pm 3 dom_162 4 roots_162 ops++addP pm 4 dom_241 6 roots_241 ops++addP pm 5 dom_179 7 roots_179 ops++addP pm 6 dom_225 5 roots_225 ops++addP pm 7 dom_161 4 roots_161 ops++addP pm 8 dom_227 7 roots_227 ops++addP pm 9 dom_113 4 roots_113 ops++addP pm 10 dom_177 5 roots_177 ops++addP pm 11 dom_146 4 roots_146 ops++addP pm 12 dzo_178_64 5 roots_178 ops++addP pm 13 dzo_162_64 4 roots_162 ops++addP pm 14 dom_240 4 roots_240 ops++addP pm 15 dom_211 6 roots_211 ops++addP pm 16 dom_99 4 roots_99 ops++addP pm 17 dom_83 4 roots_83 ops++addP pm 18 dzo_179_64 6 roots_179 ops++addP pm 19 dzo_163_64 5 roots_163 ops++addP pm 20 dom_114 4 roots_114 ops++addP pm 21 dom_147 5 roots_147 ops++addP pm 22 dom_195 4 roots_195 ops++addP pm 23 dom_51 4 roots_51 ops++addP pm 24 dom_163 5 roots_163 ops++addP pm 25 dom_178 5 roots_178 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_243 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_161 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_178_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_162_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_179_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_163_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_178 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_242 7 s (0,roots_242.map (·&&&dom_242)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_243 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_242 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_243==dom_243)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_243 gM v ys):RunD true dom_243 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_243 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 11 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 96 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 96 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 256 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_256 : ∀ i, 256 ≤ i → i < 287 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 31 256 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 287 → Z 6 i = true := (range_split z6_0 (range_split z6_128 z6_256))
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
def dzo_166_64:=0x5500000055000000000000000000000055000000550000000000000000
def gzo_166_64:=0x5500000054000000000000000000000054000000500000000000000000
def gsh_166_64:=0x550000005400000000000000000000005400000050
theorem lowS_zo_166_64_162:Lower true dzo_166_64 roots_166 gzo_166_64 5:=lower_iso_b (d1:=dom_166) (r1:=roots_166) (T1:=gsh_166_64) [(dom_166,64)] (by decide +kernel) (lower_slice_b (T:=gsh_166_64) [(0x500000005000000000000000000000005000000050,0,4)] (by decide +kernel) lowS_162)
def dzo_212_32:=0x11001100000000001100110000000000110011000000000011001100000000
def gzo_212_32:=0x11001100000000001100110000000000110010000000000010000000000000
def gsh_212_32:=0x110011000000000011001100000000001100100000000000100000
theorem lowS_zo_212_32_84:Lower true dzo_212_32 roots_212 gzo_212_32 5:=lower_iso_b (d1:=dom_212) (r1:=roots_212) (T1:=gsh_212_32) [(dom_212,32)] (by decide +kernel) (lower_slice_b (T:=gsh_212_32) [(0x110011000000000011001100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_182_64:=0x55005500550055000000000000000000550055005500550000000000000000
def gzo_182_64:=0x55005500550054000000000000000000550054005500500000000000000000
def gsh_182_64:=0x5500550055005400000000000000000055005400550050
theorem lowS_zo_182_64_162:Lower true dzo_182_64 roots_182 gzo_182_64 6:=lower_iso_b (d1:=dom_182) (r1:=roots_182) (T1:=gsh_182_64) [(dom_182,64)] (by decide +kernel) (lower_slice_b (T:=gsh_182_64) [(0x5000500050005000000000000000000050005000500050,0,4),(0x5500000055000000000000000000000055000000550000,0,16)] (by decide +kernel) lowS_162)
def dzo_214_32:=0x55005500000000005500550000000000550055000000000055005500000000
def gzo_214_32:=0x55005500000000005500550000000000550054000000000054004400000000
def gsh_214_32:=0x550055000000000055005500000000005500540000000000540044
theorem lowS_zo_214_32_84:Lower true dzo_214_32 roots_214 gzo_214_32 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_32) [(dom_214,32)] (by decide +kernel) (lower_slice_b (T:=gsh_214_32) [(0x440044000000000044004400000000004400440000000000440044,0,2),(0x550055000000000055005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_86_32:=0x550055000000000055005500000000
def gzo_86_32:=0x550054000000000054004400000000
def gsh_86_32:=0x5500540000000000540044
theorem lowS_zo_86_32_84:Lower true dzo_86_32 roots_86 gzo_86_32 5:=lower_iso_b (d1:=dom_86) (r1:=roots_86) (T1:=gsh_86_32) [(dom_86,32)] (by decide +kernel) (lower_slice_b (T:=gsh_86_32) [(0x4400440000000000440044,0,2)] (by decide +kernel) lowS_84)
namespace S_246
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,130),(4,20),(4,68),(4,132),(6,22),(6,38),(6,70),(6,134),(16,18),(16,20),(16,80),(16,144),(32,34),(32,160),(36,38),(36,52),(36,100),(36,164),(48,50),(48,52),(48,112),(48,176),(64,68),(64,80),(66,70),(66,82),(66,98),(66,194),(96,98),(96,100),(96,112),(96,224),(128,130),(128,132),(128,144),(128,160),(192,194),(192,196),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_246.map (·&&&dom_246)
def gM:=goal_246&&&dom_246
def NN:Nat→Nat
|4=>7
|5=>18
|6=>46
|7=>36
|8=>12
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xd4bfabdfb5b0f97618185beb42242c15cf9
|5,0=>0xe870fdae0bc4aacb3c249a076973e7966b57fc5359184504fd39a98367fc31c39250ef180bf128d50b0fd0147a
|6,0=>0xe884be7008d4e16c92d0bd2ebbb186b194aaefa8aea80ae559a98f1a72d5a40469ad088dce78a51f829877ce5f7c1837928f76acf7302672dec7147d6401263ec65f43158caf503dd4a65249a2d48e8e39f7f3903f2bbd4292321e2d01de650f23a0f0d00d9020c4ae090f30763b048a9044b9
|7,0=>0xd56e9c3644bf2b2b43cab1a86aa5fbaa1f48fc988f26a84e7876199718146d2d5584ba527994edd84cb194c5b84bbc24a17744b7c3f2153de643bcb739d3a37a5b2fb6421cfd1e6981da7111677110050ef5c03c4b03982015af
|8,0=>0xc602dbdea89fa247c5106eb086d4fd65c6b42c423f43d2070317b541122d
|9,0=>0x3f43d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa800a800a800a800a800a800a800a800a8000000a8000000a8000000a8000154015401540154015401540154015401400140014001400140014001400142a8000002a8000002a8000002a8000002a8000002a8000002a8000002a800000000000550055000000000055005500000000005500540000000000440044aa00aa00aa00aa00aa00aa00aa00aa00aa00a000aa00a0000000000000000154015400000000015401540000000001540154000000000154015400000002a802a802a802a802a802a802a802a802a8000002a8000002a8000002a8000550044005500440055004400550044005000400050004000500040005000400000000000000000aa00a000aa00a0000000000000000000aa00a000aa00a110011001100110011001100110011001100110011001100110011001100112800280028002800280028002800280028002800280028002800280028002855005500550050005500550055005000550054005500500055005400550050aa00aa00aa000000aa00aa00aa000000aa008800aa000000aa008800aa000150015001500150015001500150015001500150015001500150015001500152a802a802a802a8000000000000000002a802a802a802a800000000000000055005500550055005500550055005500000000000000000000000000000000
|0,1=>0xaa00aa00aa00aa00aa00aa00aa00aa000a0008000a0008000a0008000a000800000000000000000000000000000001540110015401100154011001540110000000000000000000000000000000000002a0000002a0000002a0000002a11001100110011001100110011001100110010001100100011001000110010aa00a800aa00a800aa00a800aa00a800aa00a800aa00a800aa00a800aa00a95401540154015401540154015401540150015001500150015001500150015000000002a802a80000000002a802a8000000000220022000000000022002211001100110011001100110011001100110000001100000011000000110000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa000000000000000154015400000000015401540000000001100110000000000110011000000000280028002800000028002800280000002800200028000000280020002800011001100110011001100110011001100100010001000100010001000100010aa00a000aa00a0000000000000000000aa00a000aa00a0000000000000000154014001540140015401400154014001540140015401400154014001540142a802a802a802a802a802a802a802a8022002200220022002200220022002255004400550044005500440055004400550044005500440055004400550044
|0,2=>0x8a008a008a008a008a008a008a008a008a0088008a0088008a0088008a00880001500000015000000150000001500000015000000150000001500000015000000000000000000000000000000002a002a002a002a002a002a002a002a55005500550055005500550055005500550055000000000055005500000000aa00aa00aa00aa00aa00aa00aa00aa00aa008800aa008800aa008800aa008800000000000000000000000000000000140010001400100014001000140010080008000800080008000800080008000800000008000000080000000800050005000500050005000500050005000550054005500540055005400550054aa00aa00aa00aa00a000a000a000a000aa00aa00aa00aa00a000a000a000a154000001540154015400000154015401540000015401100154000001540112a802a802a802a802a802a802a802a802a8028002a8028002a8028002a802855000000550000005500000055000000550054005500540055005400550054aa00aa00aa00aa00aa00aa00aa00aa00aa00a800aa00a800aa00a800aa00a814001400140014001400140014001400140000001400000014000000140000280020002800200028002000280020002800200028002000280020002800255005500550000005500550055000000550055005500000055005500550000
|0,3=>0x2a802a802a802a802a802a80000000002a802a802a802a802a802a8000000055005500550055004400440044004400550055005500550044004400440044aa00aa00aa00a000aa00aa00aa00a000aa00aa00aa00a000aa00aa00aa00a01400140014000000140014001400000014001400140000001400140014000000000000000000000000000000000002a802a802a802a8000000000000000000055000000000000005500000000000000550000000000000055000000000000aa000000aa000000aa000000aa000000a0000000a0000000a0000000a044004400440044004400440044004400440044004400440000000000000002a802a802a802a802a8000002a8000002a802a802a802a802a8000002a800000000000000000000000000000000000550054005500540055005400550054
|_,_=>0
def sP:Nat→Nat
|0=>0x24238129025a1411cd14664048d0960403451994c028914818128d0862ca34f3860440c518100a4091585c314654100a34220100a48f1810120c518100a48919404a34218b00a48f44128d0912ca40f38134518c2ca2422011c31460040c2040
|1=>0x82524518100a90d14604028d14818100a8cd14604029224688100a48908604028914684100a6c914604081008504028d1467c100314604029e34214100a48915118129024544128d14674100a4091465ca34519c04029224244129b245441290
|2=>0x2451a2040b0a1cd14600a6cd15104028d38688100a40d08e04048d14664102024519729035a14100a34f14604028d68e1465caacd15804028d146a8100a3451a904028934e1a204a24d08e1812a834518100d9c519904028d0864c098d146040
|3=>0x14688100a24d14660100a40d08504029b34214604028d146cc100a345197c802a534e1460402b134544604029024e14604ac0d14604028d16f18100a94d08604028d151b8101234519604029234244100a3454610400cd14604029036d141020
|4=>0x1b604028934519728d08519700a6d034518100a3451ae04028734518028d1464c029234218100a40914604080d1465c028d14684100aacd14604029b34518100a94934518100a34e1465e03451b500d0851b404080d38518100a48914604028d
|5=>0x1460402b134518100a40d1460403451b404029234518100a34518100a345e0604028d9c518100a342146040292345446040b0ac4d14604029234e18100d146d3500a40d38518100a36715118100d3851b4040289342146040dca34518100a345
|6=>0xa34518100a34519704028934518100a34519703928d
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x1e5065414503d40a50154005
|5,0=>0x22188261f187661c186a619185e61654536135847610583b60d582f60a58236
|6,0=>0x6fddb876c5daa768dd9c7655d8e762198175e9d7375b1d657579d57754954b7511d3d74d9d2f74a1d217469d137431d0664018f973c9ceb7391cdd7359ccf7321cc262edcb652bdca8728989b725588e7
|7,0=>0xafa2b68abdea96a862998a49e8a8a0de7c79d9a6f799e2607969a546935e467901a3978c9e2b788e21d685da107825e0277eddf387b1de48775dd6773a1c68
|8,0=>0xc41f097c0dafc7bd5eee7ba1ae17b6dad47b35ec67
|9,0=>0x3176
|_,_=>0
def wAt:=mkWire dB 58 247 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x146520414d593544ac60128d4035080d0381404635242491700d501718d501518d4a35146463558d5128180500318d4601180463500d40350404635180501518d4545180453540e050118d46154c0520414d4908146431558d5128180563544a060124206153455301481053514d4315
|1=>0x40c51928dca35140453500d491700d491b340451918d42351854e37140465e0404e3514041351805b03245ce351404237185512814d4601180563544a0601080c519245ca3500d414a14d501518d4e3544ac6013404a35040420114649081464d0104045013404917340500344ac601
|2=>0x404d010404a0504d463528dc5351814505146460114d4a0104d450114d410328dc50118d4115180450128dc5193404a4914d458228d41013404519040501518d4237185520714d520414d451914d463500d4a35040501718d4919340521914d491500d41011404a35
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11000000000000001
|5,0=>0x1d11b20001920001810001531140f20b4000083000062051000023
|6,0=>0x6816716526326035f10005c35a25735525325210005024d34b24834624510000004320004214023d33a33823713433313120002f22d22a30002732522412130001e3000
|7,0=>0xaf2ad2ab2a92a72a52a32a129f29d29b29929729529329128f28d28b28928728528328127f27d27b27927727527327126f26d26b2692
|8,0=>0xbb1ba1b91b81b71b61b51b41000b31b21b11
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x928000480400240000103d00081480040540020200010080008020004000001a7200072900012280002340001000000540000288000140000080000030000014000009000004000001c00000c00000400000100000060000020000008000002000000
|1=>0x2002e010005006fb7a0370bd01b27e80d92b40669da0269bd0134d680982f40482f80221ad00fa6680400a001c9fa00b7ad0052d68024804010a52007ebd0036d68018bb400c57a0061fd0024568008eb40041da0020af001056800823400404e00127d
|2=>0x200db5a836cad3014d7900201c40415e10e4fd08726e84201642100aa1064fd08326e84192b41211100868af041405819a2f40cc17a06407c
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x1000000002
|5,0=>0x6890014002002c90908001800e08001
|6,0=>0xe3a3c4841a0121810444be320de9840797000028b0e06899101c2cf880c306330084b8d2800a80
|7,0=>0x2716025353949c76e9c2c93213cd8eb5eb16131fc272a9e356c6e5ca82adfc3
|8,0=>0x6ed1c5088bd32847467c6
|9,0=>0x23
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_244 7 roots_244 ops++addP pm 1 dom_148 4 roots_148 ops++addP pm 2 dom_242 7 roots_242 ops++addP pm 3 dom_230 7 roots_230 ops++addP pm 4 dzo_162_64 4 roots_162 ops++addP pm 5 dom_118 7 roots_118 ops++addP pm 6 dom_162 4 roots_162 ops++addP pm 7 dom_214 7 roots_214 ops++addP pm 8 dzo_166_64 5 roots_166 ops++addP pm 9 dom_84 4 roots_84 ops++addP pm 10 dzo_212_32 5 roots_212 ops++addP pm 11 dzo_182_64 6 roots_182 ops++addP pm 12 dzo_84_32 4 roots_84 ops++addP pm 13 dom_182 7 roots_182 ops++addP pm 14 dzo_178_64 5 roots_178 ops++addP pm 15 dom_228 4 roots_228 ops++addP pm 16 dzo_214_32 6 roots_214 ops++addP pm 17 dzo_86_32 5 roots_86 ops++addP pm 18 dom_114 4 roots_114 ops++addP pm 19 dom_166 5 roots_166 ops++addP pm 20 dom_240 4 roots_240 ops++addP pm 21 dom_146 4 roots_146 ops++addP pm 22 dom_178 5 roots_178 ops++addP pm 23 dom_150 5 roots_150 ops++addP pm 24 dom_180 5 roots_180 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_246 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_162_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_166_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_212_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_182_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_84_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_178_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_214_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_86_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_180 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_244 7 s (0,roots_244.map (·&&&dom_244)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_246 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_244 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_246==dom_246)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_246 gM v ys):RunD true dom_246 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_246 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 46 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_246 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_126:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_iso_b isoMvS_126 (by decide +kernel) lowS_119
def isoMvS_222:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 8:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_215
def isoMvS_245:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 9:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_219
def isoMvS_249:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 9:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_237
def isoMvS_250:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_243
def isoMvS_252:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_219
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000ffff0000fffe0000fefc0000
def gsh_111_16:=0xffff0000ffff0000fffe0000fefc
theorem lowS_zo_111_16_41:Lower true dzo_111_16 roots_111 gzo_111_16 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xcccc0000cccc0000cccc0000cccc,0,2),(0xf0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff0000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_47_16:=0xffff0000ffff0000
def gzo_47_16:=0xfffe0000fefc0000
def gsh_47_16:=0xfffe0000fefc
theorem lowS_zo_47_16_41:Lower true dzo_47_16 roots_47 gzo_47_16 6:=lower_iso_b (d1:=dom_47) (r1:=roots_47) (T1:=gsh_47_16) [(dom_47,16)] (by decide +kernel) (lower_slice_b (T:=gsh_47_16) [(0xcccc0000cccc,0,2),(0xf0f00000f0f0,0,4)] (by decide +kernel) lowS_41)
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0f00000f0e00000a000
def gsh_107_4:=0xf0f00000f0f00000f0e00000a00
theorem lowS_zo_107_4_43:Lower true dzo_107_4 roots_107 gzo_107_4 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_43)
def dzo_94_32:=0x55555555000000005555555500000000
def gzo_94_32:=0x55555554000000005554554400000000
def gsh_94_32:=0x555555540000000055545544
theorem lowS_zo_94_32_84:Lower true dzo_94_32 roots_94 gzo_94_32 6:=lower_iso_b (d1:=dom_94) (r1:=roots_94) (T1:=gsh_94_32) [(dom_94,32)] (by decide +kernel) (lower_slice_b (T:=gsh_94_32) [(0x444444440000000044444444,0,2),(0x550055000000000055005500,0,8)] (by decide +kernel) lowS_84)
def dzo_95_32:=0xffffffff00000000ffffffff00000000
def gzo_95_32:=0xfffffffe00000000fffeffee00000000
def gsh_95_32:=0xfffffffe00000000fffeffee
theorem lowS_zo_95_32_84:Lower true dzo_95_32 roots_95 gzo_95_32 7:=lower_iso_b (d1:=dom_95) (r1:=roots_95) (T1:=gsh_95_32) [(dom_95,32)] (by decide +kernel) (lower_slice_b (T:=gsh_95_32) [(0xaaaaaaaa00000000aaaaaaaa,0,1),(0xcccccccc00000000cccccccc,0,2),(0xff00ff0000000000ff00ff00,0,8)] (by decide +kernel) lowS_84)
def dzo_43_4:=0xf0f00000f0f0
def gzo_43_4:=0xf0e00000a000
def gsh_43_4:=0xf0e00000a00
theorem lowS_zo_43_4_43:Lower true dzo_43_4 roots_43 gzo_43_4 5:=lower_iso_b (d1:=dom_43) (r1:=roots_43) (T1:=gsh_43_4) [(dom_43,4)] (by decide +kernel) (lower_slice_b (T:=gsh_43_4) [] (by decide +kernel) lowS_43)
def dzo_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0e0f0f0a000
def gsh_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0e0f0f0a00
theorem lowS_zo_123_4_43:Lower true dzo_123_4 roots_123 gzo_123_4 7:=lower_iso_b (d1:=dom_123) (r1:=roots_123) (T1:=gsh_123_4) [(dom_123,4)] (by decide +kernel) (lower_slice_b (T:=gsh_123_4) [(0xf0f00000f0f00000f0f00000f0f0000,0,16),(0xf0f0f0f0f0f0f0f0000000000000000,0,64)] (by decide +kernel) lowS_43)
def dzo_109_2:=0xcccc0000cccc0000cccc0000cccc
def gzo_109_2:=0xcccc0000ccc80000cccc00008800
def gsh_109_2:=0x3333000033320000333300002200
theorem lowS_zo_109_2_77:Lower true dzo_109_2 roots_109 gzo_109_2 6:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_2) [(dom_109,2)] (by decide +kernel) (lower_slice_b (T:=gsh_109_2) [(0x3333000000000000333300000000,0,32)] (by decide +kernel) lowS_77)
def dzo_59_4:=0xf0f0f0f0f0f0f0f0
def gzo_59_4:=0xf0f0f0e0f0f0a000
def gsh_59_4:=0xf0f0f0e0f0f0a00
theorem lowS_zo_59_4_43:Lower true dzo_59_4 roots_59 gzo_59_4 6:=lower_iso_b (d1:=dom_59) (r1:=roots_59) (T1:=gsh_59_4) [(dom_59,4)] (by decide +kernel) (lower_slice_b (T:=gsh_59_4) [(0xf0f00000f0f0000,0,16)] (by decide +kernel) lowS_43)
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
|6=>49
|7=>194
|8=>308
|9=>125
|10=>14
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xe7292b8221948e35410a1ac2f
|6,0=>0xf8c83e53d5ddb31d05bbb69f3aeac0a5c809add296da695682954689512d942e5850f283fc47a9ad7a49c7912d74295724936d2096c4a46abe469613660bc5b67d4e5384a2634804546d36457344002c3e7673d5433bb733a28c399c1351da27ed722e511ac2f13cc00b66b0a7df0547703fa5022980120300f85
|7,0=>0x6c2dc6ae506ab346a1276a0636990a68dde68d32651b961c31619e15f8385f6145f3365e9315bc5e5b8375b64959ba5583c65725a552f153f0d53c9f516f94f3fb4e99e4d2e84d27f4c7f14b8c74b5d44af0b4ae9c49fba49c2748124479d2476ce45a57459384588a44dd742180417ae3e2b63e1a43d6a43d5d53b7bd3b1eb380e737b173753736e8a3672e3543234de7343333423b32f8d320c22ff3c2c3c82c19b2c05a2bebd2b77e2b34828dc7288482863f2826727dd52706026817267ef25bd1259ef259d7252db241c722fad22944227d722130211442032e1fcdb1fcb81fa3b1f42b1f0f21eef31c0f01b0391ac2f1abb61951417fb617d7217c371619c15dc413f8213e7b13d6d13807135331315b11daf1137f1100310b0a0febb0ef9d0cefd0c4bb08a44051c6027c501f0a017e00162b01281012510107e005a9
|7,1=>0xfdf4ff7be7f5de5f5394efc39e9781e5634e3debdc293d6d27d4e28d3ad8d302cd055fcd287caf3cc6e5ac4460c022abd92ab86c5b7c64b68bab5506ac840aa4caaa1bda92f9a9020a850fa24c8a09f39d4ac9b6509a9939855a95694944e79422a8f29b8d68b8d4998c62f8bf7f8b5db8ab848842586f4386cba865d4855a380d87803eb7e4567b9917a3637635c75c27740d4736877306172f70723d8713946febf6cfd5
|8,0=>0x3edd73ec2d3e3fd3d3b33b9dd3b9aa3b5263a7a13a4ca3a3293a2ea395ed394e2364263627135f7b3521334b5533639331ae32f5032d1432a733208a31f2830f192f6db2ece92eac02e9862e6352e02c2deff2ad392abd229f96292f127956266cd265ae255cf24af32370e22d7022c1a22be922a3a217b62171e21414212e82122d20c892064e201071fe1c1fd931fad61fa241f42b1ec0c1dff01c8231c6031c4411c2761ac511aaf41a88b1a1771949818ff918f3218c34184f91731a16f7d16c9e16b1716a72167341624b1606715dd515c2d15bf6154b31549614fb614dfe1487d1443a1417913d8513c89132ef12819114a210fdd0ff810febb0f7620ee700e69c0d1df0c7fb0c3000be5c0ad6a0aa520a535080550721d0719b065f30517b04b9204b79047060407c03c1c0353d0304402e9b02db201b1b0120300e28
|8,1=>0xa640fa24eaa2180a1c1b9fd879f6d79c5eb9c0ef993f1990d89627695baa956829555b94279935c89342f90bbb8f9708e87f8c8068a8f38946a872e28609285ca7842a583f2a8360682ece82df782dba7f0c27e1c37e0317d5537cf637cbc37ba127ad617938178a1c776fa77487769f3733ec72d2071de97195c711e0711376febf6f2c86ee166e9426daa06d33f6cb696c7ac6bea36baf26b8ad6b3026a3166a063691f468f9168ae7682ee681e267c336763f64b8b64aca642da6410f63c4e62b7b625e16237b618246125d5e8545e4615db0c5c9a65b6d75939c5854f57a4957833565ee5635755b46552ed551b854a42539db535f752a9f528c0524f35197c5153a511834fbe84f4354f40d4e4dc4de7a4d9914d48b4d1654cf704ceea4b5324b42b4a86e488fb475c046afc44987440f643fbf43b8742de04178a4127d
|8,2=>0xfeacafa280f2e0bf2cd8f226df1a77f006fefc2eef3a8edd33ec4f9e7224e5d68e4755e14a9e0396dbed3dbda2d88fed6c2ad641ed4e28d3b51d1d76d0c3ad055fce9c0ce2f9cb260ca6a7c9c81c73a5c5102c21f8c0b77c0638bd488bcbe4bcac7b9634b948eb935ab70e6b588fb4eb2b3c51afc7daf005ae8e3ab8ddaa1bda7ad8
|9,0=>0xfcb54fb74afa280f80d3f6f03f673be259de20b7d5822d1b83cec71cdf47c6e0bbdd15bb383ba879ba0a2b38c7b0480afed3afc7daf7f2ad125acea9aab24a8a85a8201a79fea576da4c3aa36faa24cba21faa125c9fc329bd299b7a09b2b79954c98d89956828dc818c1808b3068a35989ecd7cf22794fc77b19776fa707586fc266d2926a3f76a35a69a566765b64aca60eb95f6e15ef435e22c5d2755839a56d99559705254f4b3f949cb64816946fad46f5d44531426593eb213e2c43d5ff3d36c3c2ee3bea03b2ce3a6793a623395c7375e83733034b53348ea3254f2bc42292d4291b828ef024f8b2479722dec2258c224dc2150d1b4fc1ab8a195c21927417b87156f1155f214af80eebe0d80a0d12b0c8070c0cf0bb3f0baf90a10409fe00969706d14068b8065f80570f053570398a037ed0272a
|10,0=>0xce280bbe949e7bb928f2918968d3bf83c7d761fa715435254f43a533b65b2676305c14
|11,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffff00ff00ffffffffff00ff00ffffffffaaaaaaaaffffffffaaaaaaaaffaaffaaffaaffaaffaaffaaffaaffaafffff0f0fffff0f0f0f0f0f0f0f0f0f000000055000000555555555555005500ffffffffffffffffffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00fffffafafffffafaf0f0f0f0f0f0f0f055555555550055005555555555005500ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccffffffaaffffffaaaaaaaaaaaaaaaaaa
|0,1=>0xffffffaaffffffaaffffffaaffffffaafffffffafffffffaf0f0f0f0f0f0f0f000000000000000005555000055550000ffffffffffffffffff55ff00ff55ff000f0f0f0f0f0f0f0f0f0f00000f0f0000ffffaaaaffffaaaaffffaaaaffffaaaaffffffffffffffaaffffffffff00ff00ffffffaaffffffaaff00ff00ff00ff0000ff00ff00aa00aa00ff00ff00aa00aaffffffffffffffffaaaaaaaaaaaaaaaaffffaaaaffffaaaa0000000000000000ffffaaaaffffaaaaaaaaaaaaaaaaaaaa00ff00ff00ff00ff00ff00ff00aa00aa0000ffff0000ffffffff0000ffff0000ffff0000ffff00000000000000000000ffffffffffffffff0000000000000000
|0,2=>0xffffffffffffffffffffffffaaaaaaaa0f0f05050f0f05050f0f00000f0f0000ffffffffffffffffffffaaaaffffaaaa00ff00ff00ff00aa00ff00ff00aa00aa000000ff000000ff00000000ff00ff00ffff0000ffff0000aaaa0000aaaa0000ffffffffffaaffaaffffffffffaaffaaffffff00ffffff00ff00ff00ff00ff00ffffffaaffffffaaffaaffaaffaaffaa0000000000000000ffff0000ffff00000000ffff0000ffff000000000000000000000f0f00000f0f0f0f00000f0f0000ff00ff00ff00ff00ff00ff00aa00aa000f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f000f0f0f000f0f0f000a0f0f000affffffaaffffffaa0000000000000000
|0,3=>0xffffffff00000000ff00ff00555555555555555555005500550055000f0f05050f0f05050f0f05000f0f050000ff00ff00ff00ff00ff00aa00ff00aaffffffffffffffff5555000055550000000000ff000000ffffffffffff00ff00ffffccccffffccccccccccccccccccccffffffffffffaaaaffffffffaaaaaaaaffffff00ffffff000000000000000000ffffff00ffffff00ffffff00ffffff00fffffff0fffffff0f0f0f0f0f0f0f0f0ffffffffffffffffffffffff000000000000ffff0000ffff5555aaaa5555aaaa55555555555555555555550055555500ffffffffffffffffffffff00ffffff0000000000000000005555550055555500
|0,4=>0xff00ff00aa00ff00ff00ff00aa00aa55555555555555555555555555005500ffffffff00000000ffffffff005500000f0f0f0f0f0f0f0f0f0f0f0a0f0f0f0a0000000000000000ffffff00ffffff00ffff0000ffff00ff0000000000000000ffffccccffffccffcccccccccccccccc00000000000000000055000000550000ffffffffffffffffffaaffaaffaaffaaffffffffffffffff0055000000550000ffff0000ffffffffffff0000ffffff000000000000000000ffff0000ffffff00ffffffff0000ffffaaaaaaaa0000aaaa0000ffff0000ffff0000ffff0000aaaaffffff00ffffff00ff00ff00ff55ff00ffff0000ffff0000ffff0000aaaa0000
|0,5=>0x55555555555555005555555555005500ffffff00ffffff00ffffff00ff00ff00000000ff000000ff0000000000000000ffffffffaaaaffffffffffffaaaaaaaa55555555000055555555555500000000000000000000000000ff000000ff0000aaaaaaaaaaaaaaaaaaffaaaaaaffaaaa0000ffff0000ffff5555ffff0000aaaaffffffff00000000ffaaffff0000000000ff00ff00ff00ff00aa00aa00aa00aa00ff00ff00ff00ff55ff00aa55ff00aa00ff00aa00ff00aa00aa00aa00aa00aaaaaaaaaaaaaaaaaaaaffaa00aaffaa00ffffffffffffffffffffffffff00ff0055555555555555555555555500000000aaaaffffaaaaffffaaaaaaaaaaaaaaaa
|0,6=>0xffffffffffffffaaffffffff00000000ffffff00ffffff00aaaaaa00aaaaaa00555555555555555555550000555500000000000000000000ffffffaaffffffaaaaaa0000aaaa0000aaff0000aaff0000ffffffffffffffffaaff0000aaff0000000000ff000000aa00ff00ff00aa00aa00005555000055550000555500000000ffffff00ffffff00ffaaff00ffaaff00ff00ffffff00ffffff00ff00ff00ff000f0f0f0f0f0f0f0f0f0f0f000f0f0f00ffff00ffffff00ffffff0000ffff0000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000ffffffffaaaaaaaaffffffffffffffffffffffaaffffffaaff00ff00ff00ff00ff55ff00ff55ff00
|0,7=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f00ffffffffffff0000ffffffffaaaa00000000555500005555aaaaaaaaaaaaaaaaffffaaaaffffaaaaffffaaaa0000000000000000ffffffff00ff0000ffffff00ffffffffffffff00ffffffffff00ff00ffffffffffffffaaffffffffffaaffaaffff0000ffff0000ff000000ff00000000ff00ff00ff00ff00000000000000000f0f000f0f0f000f0f0f00000f0f000033333333333333333333333333332222ffffffffffffffff00ff000000ff0000aaaaaaaaaaaaaaaaffffaaaaffffaaaaffffffffffffffff55555500555555000000ffff0000ffff0000aaaa0000aaaaffffffff00ff00aaffffffff00aa00aa
|0,8=>0xffff00ffffff00ffffff00aaffff00aa0000ffff0000ffff0000ff000000ff0000ff00ff00ff00ff00ff00ff00ff00aaffffffccffffffccccccccccccccccccffff000000000000ffff000000ff0000ffffffffffffffffffff000000ff00005555550055555500555555005555550000ff00aa00ff00aa00ff00aa00ff00aaffff5555ffff5555ffff5500ffff5500ffffffffff00ffffffffffffff00ff00ffffffff0000ffffffffffff00000000aaaaaaaaaa00aaaaaaaaaaaaaa00aa00aaffaaaaaaffaaaaaaaaaaaaaaaaaaaaffffffff0000ffffffffffff0000aaaa0000005500000000ffffffff00000000aaaaaaaaaaaaaaaaaaaaaaaaaa00aa00
|0,9=>0xffffffffffff0000ffffffff00000000ffffffff00000000ffffffff00ff00000000555500000000ffffffff00000000ffffffffffff0000ffffffffffff0000000000000000000000ff00ff00ff000000ff000000ff000000ff000000ff0000ffffffff0000ffff000000000000000000000000ffff000000000000ffff0000ffffffffaaaaffffaaaaaaaaaaaaaaaaffffffeeffffffeeccccccccccccccccffff0055ffff0055ffff0000ffff0000005500550055005500000000000000000f0f00050f0f00050f0f00000f0f00000000000000000000ffff5500ffff5500ffffffffffffffffffffffff00ff0000f0f0f0f0f0f0f0f0f0f0fffff0f0fafa
|0,10=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000555500000000000055550000ff00ff00ff55ff00ff00ff00ff55ff0000000000555555550000000055550000ffffffffffffff00ffffffff00000000ff00ffffff00ffff0000000000000000ffaaffffffaaffffaaaaaaaaaaaaaaaaffffffffffff00000000000000000000ffffffffffffff00ff00ff00ff00ff00ffffffffffffffffffffffffffff0000333333333333333333333333333300000000ffff0000ffff0000ffff00000000aaaaffffaaaaffffaaaaffffaaaaaaaa00000000ff00ffff00000000ff00ff0000000000ffffffff00000000aaaaaaaa33333333333300003333333333330000
|0,11=>0x5555555555550000ffaaffffffaaffffffaaffaaffaaffaaffff0000aaaa0000ffffffffaaaaaaaa00ff00ff00ff00ff00ff000000ff0000ffffffffaaaaaaaaffffffffffffaaaaff00ffffff00ffffff00ffff0000000055555500555555005500550055005500ffff0000ffff0000ffaa0000ffaa0000ffffffffffffffffff00ff00ffffff00ff55ff55ff55ff55ff55ff00ff55ff0000000000ffffaaaa00000000aaaaaaaa0000ff000000ff00ff00ff00ff00ff000000000000000000ffffffffff00ff00ffff0000ffff0000ffffffffffffff00ffffffffff00ffffffffffff00000000ffff0000ffff0000ffff000000000000
|0,12=>0xffffff00ffffffffff00ff000000000000000000ffffffffffffff00ffff0000ffff0000ffffffffffff0000aaaaaaaaaaaa000000000000000000000000ffff0000ff0000000000ffffff0000000000ff00ff0055550000555500005555000055550000ff55ff00ff55ff00ff55ff00ff55ff000000555500005555000055000000550000ff000000ff000000ff000000000000000000000000000000ff00aa00ff00aaffffff00ffffff00ffffff0000000000ffffffffffffff00ffffffffffffff000000000000000000ffffffffffffff0000ff00ff00ff00ff00ff00ff00000000000000ff000000ff000000ff00000000
|0,13=>0xaaaaaaaaffffaaaaaaaaaaaaffffaaaaffffffffffffffffaaaaaaaaffffaaaaffffffff0000ffffffffffff0000ff00ffff0000ffff0000ffff0000ff000000ff00ffffff00ffffff00ffaaff00ffaa0000000000000000ffffaaaaffffaaaaffffffffffffff000000000000000000ffffffff55555555ffffffff55550000ffffffff000000ffffffffff00000000ff000000ff000000ff550000ff550000ffff5555ffff5555ffff0000ffff00005555555555555555000000000000000000000000ffffffff00000000ffff0000ff00ff00ffffffffff00ff00ffffff005500555555005555550055005500550000000000ffffffff00000000ffffaaaa
|0,14=>0xffffffffaaaaffff0000000000000000ffffaaaaffffaaaaffaaaaaaffaaaaaa000000000000ffff0000000000000000ccccccccccccffffccccccccccccccccffffffffff00ff00ffff0000ff000000ffffffffff00ff000000ffff0000ff00ffffffffffffaaaaffffffff000000000000550000005500ff00ff00ff00ff00ffff0000ff000000ffff0000ff0000000000ffff00ffffff0000000000000000ffffffffffffffffffffffffffffaaaa0000ffff0000ffff0000ffaa0000ffaaffaa0000ffaa0000ffff0000ffff0000ffffffffffffffff00ff00aa00ff00aaffffffffffffaaaaffffffffffffaaaa33333333333322223333333333332222
|0,15=>0xccccccccccffccffcccccccccccccccc00000000aaaaaaaa00000000ffffaaaaffffffffffffffffffff0000ff0000000000ffff0000ff000000ffff0000ff00ffffffffffffffff0000ffff0000ff00ffff0000ffff55550000000000000000ffffffffffffffffaaffaaaaaaffaaaaaaffaaaaaaffaaaaaaffaaaaaaffaaaaffffffffffff0000ffffffffff0000000000ffff0000aaaa0000ffff0000aaaaff000000ff000000ffff0000ffff0000ff00ff00ff00ff00ffffff00ffffff0055005500550055005555550055555500ff00ff00ffffff00ff00ff00ffffff000000000000ff00ff0000000000000000ffff0000ffff00ffffff0000ffff0000
|1,0=>0x333333330000000033333333333300000055000000550000005500000055000000000000ffffaaaa00000000ffffaaaaffffffffffffffff00000000ffffaaaa0000000000ff00000000000000ff0000aaaaaaaaaa00aaaaaaaaaaaaaa00aaaaffaaffaaffaaffaaffffffaaffffffaa00ff00ff00ff00ff00ff00ff00ff000000550055005500550055000000550000aaaaffffaaaaffffaa00ff00aa00ff000000ffff0000ff00ffffffffff00ff0000005555000055550000000000000000ff00ff55ff00ff55ff00ff00ff00ff0000ff00ff000000ff00ff00ff0000000055550000555500005500000055000000ffffffffffffffff0000000055550000
|1,1=>0xaaaa0000aaaa0000ffff0000ffff000000000000ffffff0000000000ffffff000000ffff00000000ffffffff00000000000000550000005500000000000000000000000000ff0000ffff0000ffff0000ffaaffff00000000ffaaffff00000000ffffffff00550000ffffffff00550000ffff0000ffff000000000000555500000000000000000000aaffaaaaaaffaaaaffaaffffffaaffff0000000000000000ffff0000ffffffffffff0000ffffaaaa00000000555555550000000000000000ffff0000aaaa0000ffff0000ffff0000ffffffffffffffff00000000ffff0000ffffaaaaffffaaaaff00aa00ff00aa00ffffffff00000000ffffffffffff0000
|1,2=>0xff00ff00ff000000ff00ff00ff0000ffffffff55555555ffffffff00000000ccccccccffffffffccccccccccccccccffffffff00ff0000ffffffff00ff0000ffff000000000000ffff0000ffff0000ffff0000ffffffffffff0000ffff00000000000000000000ffffffffffff00000000aaaa0000aaaaaaaaaaaaaaaaaaaaffff0000aaaa0000ffff0000aaaa0000ff55ff55ff55ff55ff00ff00ff00ff00000000000000000000000000ffff0000ffffffffaaaaaaaa000000000000000000000000ffffffff0000000000000000ff00ff00ffffffffff00ff00ff00ff00
|_,_=>0
def sP:Nat→Nat
|0=>0x83c1c0d0209c0401080380a12040041e240281046010788820050200c0216078840a0904078020f028100602008000a090400802060a814080c0e0080216028101803008583619028103002008580a04010042c130a8142408010041e17028101002008582a05020080214098401c0d09030040107034120c058040a0401808020a028241007008180a04018080200
|1=>0x786c261002810300200818200e068241802008441c0d02030021b080340a09040d4020f0281010070081820290284810020083c680504008020f198340a090602016010701412080083c4805020300602008c05e050206004010b0140808008185c10028101803008584405020080200160400a090402c020f030140803010041e2b0286804011504c202902824100b
|2=>0x40042c0f0d8146c08010042c0f1d81408230083c36100284818080083c360e0684810020083c1c0d020301601080140801078882610070341208058041e05048301001078901c0509020020f0d8e80a0401808020f0281050020083c200d028100602008001a05090301002008381a2606008022507034080c010e42005090301001078901c380209c0401080140801
|3=>0x258101803010041e0e028101001078882005020200449078400a04238200401079181a05020a00401078400a440200c10020083c0a0404008720f030400a1a040080216218405205020200439078400a08010041e1d210400a0420808020f08014081c0400802160781434400400802160801408080083c363f0801408080083c7c3d08014080c010042c3c080140803
|4=>0x1004a8100289810020083c0c250281010020094c1e10028100602008001c0504820160107814620404008024e0801408080083ca21b080140802009401e4f080a40a2604008020f12934084704008020f080140847040041e4c08014080801004281708014082611808020f080a40a0414008020f080146c0401808024e081340808010041e10028101001079302005
|5=>0x1808020f0801408020083c2e102e81408260600c04010b014080801004a05b0801408030400802590b0140808010042c0f23010ae4704008020f080140823010041e1d080340a09060200401088140808010041e58080340a0406020021b08010ae08010041e10070140827010041e100281010020083caa100281018080083c36101a0140808008581e1b068140808
|6=>0x219c0401078401c380202004010a0400a040600c020f0d8401a0502030cc02008400a0404008020608054a40502020020f328400a6402008020f0b8400a04040080263081880a04040041e1b080e00a04138200401081340808010042c0f080140808008581e4c080380a09040041e1b088640a040c008020f08014086001808020f080140828010041e5f08014bc04
|7=>0x80340a04060a00401080386804040041e1b0801424080083c36050200c10010b03c4405020200401031b42005020203c01078400a040618004010b0400a6c0211c10020083c0a04040041e3e328400a040182004013503c5e050d0200401150400a0414008020f348400857040080216078400a040600c04010b0740a04040080216340401a050203010021c8401c05
|8=>0x600c0401079d01a05048200401078dc0a73020200401030400a04040080216079c80a04010041e13388400a090401c020f029b00808010042c0f070142408010041e700281010020085020051b0100602008587c050200c04010b03c786f020200401078400a0401808020f370340a0404008020008014080304008020f180340a260602004011281408080083c3656
|9=>0x1c014080801004a810068146c78010041e10070140808010042c150681408080083cec10028101001079947e101a0140808008581e221a014080314008020f02810100b0083c0c100681408271400802100282408020083c2610148140808058041e10028101002079d420050200c0401078800a36018080216078740a0404008024e2d0401c0d048101802008400a04
|10=>0x400802160282418080083c3611028b4080c0180802160281030020083c20053e0101002008581c0d020300401080940a0404008020f3d8401c0d048200401078440a1a04820040103040f405020a00401078400a04010041e4f080d00a2d04008020f150381a04040041e1b08014120c0402c020f028108e080100464103c8140808010042810028b40823010041e10
|11=>0x689810020083c4a051690010020083c20051b010060200a00200e0681050020083c200502030060107994200d0281010350083c20050202004010a018200502020020f3f8401a0502030100b008401c0d020200439078400a0423820020f0d840fc050d02004010b0401c050484810020083c0a04040080216190405e0502020020f0d8400a040400802163e8140818
|12=>0x19e004010781408020083c541308014088a01820040107814080200a251010028108e0801004b210028101001078f42005020200401420400a04040080283080140826010041e13081480a0401808020f1b814240c04008020f0282410020083c2e110703408260600802100281010010786c2e1007034080c01004201102810100200858b6104081010020083c200e
|13=>0x801408080083d26100281010020083c60100281006080083c7a1002a48080304008020f070340808058041e1048814080304008020f02824240c04008020f0281010900083c2005478100602008581e0502008023e2b0400a0423820020f11040680504008020f2d2380a04010041e8d08014342604008020608014081c04008020f080340a0404009180f080d00a36
|14=>0x70140808010041e2a08014080c040080250080140808010041e10100140808010042c15070141204040041e1b0801412080083c48290282410020083c22290281010010786c20050f810060200858a405020a00401078400a0904008020f1001412040600c04010b0140808012581e10028481001078900a08010041e33080380a04040041e1b08014120411808020f
|15=>0x470400a04040d4020f080141208010041e15028100608010041e32082780a04018200401078400a090203006020083c209d020200401078400a360211c06020083c20050202004010b03c9010068140808010e41e10028100608010041e9b080340a0904008020f4d0400a0404008029707840c4050481010020083c20050200c1001079942034028100608010041e5a
|16=>0x1004b20f080340a2604008020f12814080801005460f080140808010042c14080140808010041ea2080140808010041e42080a40a0413020040107840520502020040107840220d0281050020083c20050481010020083d421002810180200858ac100289810020083d12100281010020b03d40104f8101808010041e10028c4084704008020f080340a0404008020f
|17=>0x10041e1002810100107abc2005022b40401078406805048100608010041e051b00cf0020083c200d028d81208010041e100281010020083d58105581010020083c200516820040107a6820050202004015483c20050211c1002008f820050209810020083c0c10028114e08010041e1002810100207a9420050d01010020085942100281010020083c0c10088140808
|18=>0x4008020f2a0400a04130200401078fc20050481010020083cac10028c41078010041e10028104c030400802160781408080100428b5080340a045a008020f081480a04041e00401078401a05020301002008404ab20281010020083c200e1a0240808010041e10588140808010041e10029780808010041e10028242408010041e054381010020083c7c100287c0803
|19=>0x83c200d02810cc08010041e10028b4080c0400802160801434040400802162b0410c05020200401078401c0d02030040108014120c04008020f08814088b04008020f0801408ba04008020f08014c20404008020f080140828010041eb90801408b804008020f0801408b701820040107840709f020200401078400a0406020020f0d8400a045b0200401078400a04
|20=>0x1820040107b1420056201010020083c20c20281010020083c20051682004010b03d3410028100608010042c0f0e8140808010041ec00801408020083c2610028101002008587c100281010020083d7e10028101002008581e420801408be04008020f082f40a0404008020f080340a0404008020f5e0400a610211c10020083c200504008020f2d23820bb028101002
|21=>0x281010020083d9610029840808010042c0f080340a04140200401078400a0404008020f650400a0413020040107944200e02810100b0083c200e02824080c010041e101c014080801004280f08014080c04008720f0801408c801808020f080148a04018200401078400a0404008020f638400a0404008020f630400a0404009180f080140860040080216078400a04
|22=>0x60200401078940a04040041e2e0801408d204008020f080140802008581e1308014080c14008020f080380a2d020200401078400a0404008020f688401a050209818080100420050d0200401150401a0502030100200840220502020040107b402034028104c08010042c0f0281010020083d9e1002b340808010041e100281010020083d98100281006020083d1210
|23=>0x40080216078a80ada04008020f4d0400a0404008020f083640a0404008021607b3020050481018080083c36106c0140808010041e10028681002008593010028104c0c01808020f0835c0a0404008020f08014080801004000f080bc0a0404008020f38840c4050209810020083c200e068240808010041e1002811ac08010041e5608014084704008020f2d0400a26
|24=>0x7aa00a8f020200401078405e050d01010020085820050238c10020083c20050222c0608010041e100281010020083dc41002810100207b8020050202004016f03c20dd0281010020083c20910281010020083c20050202004010b03da01002811b808010041e1017814120404008020f0801408db04008020f080152a0404008020f080143408010041e5a080d00a04
|25=>0x20200401078400a0474008020f080140808010041e1d508400a0404008020f083980a041302004010795820051b0100602008581e0e1a0104c08010041e10728140808010041e100281010020083dc810028101002009ac1e10068146c2604008020f08014082714008020f080d00a0401820040107a380a04018080216079580a090211c10020083c2034020200401
|26=>0x7781408ee04008020f080151e04040080216078400a090202004010785c200502020040107b891010028b40803040080216078140808013b01e10068140808010041e101ba7c0808010041e100286810020083ce81002811d608010041e1029014620404008020f080381a0404008020f080940a04040080216288400a0404008020f218400a0404008020f75041d205
|27=>0x1005f2f8078400a040c008020f08014620404008020f1f040b8050202004012803c203402020040107b39ee05020200401078400ada0202004010b03c680404008020f7b0400a042002004010b03c200d02811ea08010041e100281010020083de61002811e403010041e100281010020083c3a5608015e00404008020f081e80a0414008020f080140808010041e10
|28=>0x83e0210028101808058041e10068140808010041e10550146c03010041ec9080146c08010041e6d080140808010041f00080140808013fc1e100681408080100428100281010010786c20050202004010b03c8610028101803010042c100281010020083dfc1007015b40404008020f0801408fd04008020f080140808010041efb080140808010041e107d0140808
|29=>0x10041e100281010010b03c3610828140808010041e1002810060801004d60f080140808010041e17080940a04818200401078406805168101002008581e0502020040107c08200e068104c08010041e10072140808010041e10070340808010041e1008814120801005f00f083740a04018200401078400a1a01820040107968200d028d80803010041e10028101002
|30=>0x7014e60404008020f083dc0a04018200401078400a1a04008020f698400a0404008030a08016120404008020f081480a0404008020f2d04068051b01006020083d4c0504008020f4d0400a0414008020f080140826238200401078400a0404008020f840400a31020200401078fc20050f810100200a24200502020040107c1c200502020040107c18202f028104c08
|31=>0x286810020083e2410068140808010041e5a080140808010042c0f1d814080888808020f080340a64020200401078400a04040041e22080380a09020200401078400a1f048200401078400a04040081f0f080141208010041f0e08014081c04008020f080140823010041e104e2c010020083c200e02810180200858200e0281010020083c21040281010020083e1810
|32=>0x8b0a40a09020200401078400a0404008020f180400a040400802f90b03c200504820040107a24200502020040107918200504820020f0d8440b1502020040107840680502020020f0d8400a1a020200401030401c9f020200401078400a04898200401078400a04040080206083500a090402c020f028104602008581e10070140808010041e3b08014080c018080216
|33=>0x78404a050f89810020083c20050246c10020083c200509020040107814082704008020f080123408010041e10028101808010042c1d080e00a0404008020f084640808010041e10028240803040080216078140808010041f18080140808010041e32080380a0904008020f08a780a0404008020f080380a04040041e1b080140808010062e0f080140808010041e10
|34=>0x20300401078400a0404008020f87041380504008020f648400a040400802160795820051b06810020083c20051b01006020083c200502020040107bd8200502020040107841551d0203010020083c2005048101808010041e10028240808010041e5108014084704008020f240400a6c020200401078400a0404008020f084700a0404008020f240405205020200401
|35=>0x203010020083c2025070340808010041e10028124008010041e1002b680808010041e10070140808010041e106a014091f04008020f080146c0404008020f8f0401a050209810020083c20850281010020083c200d0281010020083c20111a014340404008020f080146c04040080216078401a34020200401078400a1f020200401078400a31020200401078401c05
|36=>0x4008020f4d0400a0404008020f081740a0404008020f368400a0401820040107b500a0404008020f448400a04238200401078400a04928200401078400a04640200401078400a04920200401078400a0404008020f080540a0404008020f083c45e0502020040107841c205020200401078400a0404008020f918400a0404008020f084881c050d01010020083c2005
|37=>0x849c0a0404008020f080140808010041e1076814e60404008020f080140808010041e5a080140847040080216078416605020200401078400a0404008020f8f0400a0404008020f0b8400a040400802df078400a310200c10020083c20053201010020083c2005020981808010041e10028101808010041e10088bc0a04040080216078400a04040080326080d00a04
|38=>0x20301002008582005048101002008581e104f81010020083c20050d02410020083c200d0281010020083d34104e01408080103d4010530140808010041e10028101002008581e7108014080304008020f648423a0404008020f080140808010041e7408014120404008020f0827c0a0404008020f080d00a0404008020f6a0140808010041e7108016500404008020f
|39=>0x28101002008581e100281050020083c200502020040107b4c2005020200401078f82034028101002008581e100281010021c83c200504820040107a68212a0281010020083c2005048200401078440a04040080214078400a04040041e1b08014080304008020f2d0400a3604008020f648400a040182004010b03c200502020040107a902005024a410020083c2005
|40=>0x4008020f080140808010041f12080140808010041e1054014086604008020f080140826040080216078400a0404008020f150405205020200401078400a0902020020f0d84138050202004010b03c2034028240808010041e10028684c08010041e10880140808010041e104e0143408010041e10028101002008581f210281010020083c20940289810020083c4a0e
|41=>0x80140808058041e10028680808010041e88080380a0404008020f0809468050202004010b03c0a0404008020f288400a0404008020f968425805020200401078400a04040080216078a820340281010020083d4810028101002008581e98080140808010041e3f080140803040080216078380a09020200401078400a040400a560f080143408010041e980801408b0
|42=>0x20200401078406805020200401078400a0404008020f080940a09020200401078400a0404008020f084840a04040080216078400a0404008020f648400a0404008020f081dc6805022c010020083c200502020040107ab82005048101808010041e1002810100207a80200502020040107841329c1a01010020083c2034028104c08010041e10028100608010041e3f
|43=>0x5020200401078400a04060200401078400a1a020200401078400a0404008020f4c0400a04130200401078400a0404008020f080453805020200401078401c05
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x18600930031800cc0006
|6,0=>0x16c70b2b8579c2aee15070a4b8509c276e1347096b8499c23ee1187088b8429c206e0fc707ab83b9c1cee0e0706cb8349c196e0c4705eb82d9c15ee0a87050b8269c126e08c7042b81f9c0eee0707034b8189c0b8c0566027b8121c082e03a7019b80b1c04ae01e7
|7,0=>0x1b140d6a06a5034a81a1b8cee0667032b8191c0c6e0627030b8181c0bee05e702eb8171c0b6e05a702cb8161c0aee056702ab815238a720529028c8142409f204e9026c81333097dc4af024f8123c08fe046f022f8113c087e042f020f810438805c3f301f180f53878a03b501d280e54070a037501b280d5b868e0337019380c5c060e02f701738
|7,1=>0x2ab4153a0a8d053e829b414bdca4f051f828c394420a110500827c413c209d104e0826c41342099104c0825c412c2095104a1724d3924a09150482823d411ca08d50462822d4115188990445721ec10d6085b0426720fb905e081f040781ffc0fde07df03e961f0c0f6607a4e3ca81e140eea076503aa81d140e6a0725038a81c140dea06e5036a8
|7,2=>0x3a0c1ce9ce65072b7391c1c71ce2cc70f7383c1bfe0df0e6f0837441b820db106d0836441b05cd7306b2735541a8a0d36e6938345c1a0e0cf706738335c1991ccb9065573273991dcc7f06378318398a20c4106188308418220c02e5f982f8c17a60bc305d982e8c17260b84e5ba82d9416aa0b45059a82c94162a0b06e57c72ba415b20acae55e7
|7,3=>0xea2c7498
|8,0=>0x4b04255e529f0947849f4a4d6525b0924948e42452121ae904947e423d5d1dce8e5946ec2352519908c5745ec22d6115b08a4944e42255d1192883943dc21ce10d70863842dc214e10952841941cc20c250510820840c42042100f27fe93fbb9fc1cfcf27de93eac9f39cf8b27bc93da41eae4f45279a83c8c9e260f01277793b7c1d9e0ec0e7579
|8,1=>0x5b9badae16c70b5b85a94ad2a16832b3a7598caca616412b18858842c2216010af88577cab9a55bd0ad59566c2b1255772ab38555c2a8a55350a928545baa0a54f32a718534c298254af2a4f85243a90214710a2f9513c287e142d2a0d9502c27f613e929eb94f14a76a13a6e9cb84e1c26ee136709ab84d1c266a5325098a84c1425ea12e329689
|8,2=>0x6c3c35fe1aef0d6e96b2cb5725aa72d4c76a1cb4f1da690d2c8691cb46a5a250d0a8681433ea19e6ecea96714336659a30cc89660432e219610ca7964fc325a591d0c85963f3b1da18db2c65862e4b152189aec45861ec30d618592c24860dcb04e18170c0385fd4afca17d50be195ec4af4217910bbf95dbc2ebe174d2b9d95ca4ae2e57052b7a8
|8,3=>0x7ccbbe461f112f8087bbcbdba5ecd0f5f77abc3d3a5e8d0f3e879bbbcba5e4d0f1d978ac3c361e0b0efc977a43bb21dc72eda976943b265d830eb8975843a9e5d3f0e969746cba125cf90e748735cb98e1cb70e5387263b9121c7aee349716438921c372e138705c380e1bf52df376f54b7865bb4edd286e54370a1b732db096d4436821b2f2d8f8
|8,4=>0x89cc44c2624f311e988b4443a220d10fd987ac43b621ced0df886c3c33e618f10c0785bcc2be214f109f884bc423e210f107f883b4c1ba20cb305d882ac4139e08d103e881b440ba204d101e880c34042200f300077fc43fbe5fcf0fdf87eb4bf3ddf8d2fbe87dbbbebe1f4f0fa07
|9,0=>0x9a444cfe666d332f7993c4c7e262f130f8983c4bfe25ef12ef8973c4b7e25ad32ce896344afa256d12ad9952c4a726527328a9941bc9ea64e5126a89314496a24a5124a8921448ea2465122a89114486a2425120a8900cc7e263e111e888f04475e639f11c698decc6d6235931a398cd4c64a2315118288bd445ca22d5116198acc4546229311418
|9,1=>0x15399a98c54a26a42f5198a88c542269ff34f87a77cd39a69bd14d68a674531a297b34b49a55cd28e293714929a45bd20e28f714738a35c518e28b534528a254510a287334309a1445082283114108a0445005e7f133f179f4c4f8627b133d179e4c4f062774f3b289d5bce8a6735139199c4c4e0626f3137099b4bcd8626b133508
|10,0=>0x2b5515a28acd4564a2b1515828abd455ca2ad515628aad4554a2a9515428
|11,0=>0x15b27
|_,_=>0
def wAt:=mkWire dB 302 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x283d02041010dd1b04002021168ab020580205902841020410283d010450403d020400900b048470204102040190431883f0200d0404107841040550d0400203d1680b0404102059078411403d0282104045020400900b13095020420204302041010810f840020310403d01875040410205b040410480b078410204107841040550d0400203d048470283d020410282102040010450204102821020400283d
|1=>0x178100203d078410205907841040410480b0784102041048470480b0204102040048470283d020410282102040028210283d0104502040020410283d0104502821020400d8470480b020410204004847020400480b02041130950283d020430403d02042028210283d02043020420084502821020400283d0900b130950204202043028510a02107845020400204102821020400283d028210480b020410283d
|2=>0x480b02041078210283d0a0210784502821020400e9590205b0405a078410480b02095020420480b020410284107841040520784502040188fb0200d0404104041078dd1b04002021010450204102821020400200d2903f0280d0404117820028590283107821188430200d1680b0483d02041009290701302821240410211f04059078411b00c040410202122843020fd0280e068430283d040ed0e8410205b
|3=>0x40a902058078410285107845020400480b04041078210204102042028210d040070250282102041028510a0210784502040029210211f040593080b0211d040590480b020410204002861040550d0400203d041210211f0780d04041290d8020210280d040411b042020430403d04041078412e03f029410789502042079690200f04041240410211f0405907841178200205b0784107821020410283d02040
|4=>0x168230205907841028810f84002031040411b0580202107841078dd0283d1b04002021190431883f0200d040410283d020430403d020420283d0782104045020400480b02821028410204104847020400480b020411680b02059040410784102041010810f840020310403d0205b07841308430211d040590784135841020fb0780e04041029230211f0405904041078210205b078410283d008450403d02040
|5=>0x2859078410a02307845020400200c04041020210d040078410203d3200b0283d021dd040421680b020590284107841028411b00c02021040411403d0404502040178231a03d02841020410f8400404102031078210283d020410403d028212d0410200f020410283d1b040020210703f02821180411b05b020210784102041010550d0400203d308430211d0405907841048470204102821020400183f02021
|6=>0x203d0205807841048470204102821020403083f0211d04059078410b057078410d0400203d07841040550d0400203d0480b0204102040040410782102059078410f80c0404102031078211a0680203d02841078410403d020420283d028210283d0204102821020400204102821040dd1b040020210205802059028410283d028210480b0204101045020410403d020400183d1883f0200d040410205917820
|7=>0x28410404145841020ff0280e040410403d079210211f04059078414380b020f90780e040414303c428210289502042021580405a07841178230283d1b040020210404113095020430403d0204202821020430283d0282102040078210283d4103f0205a02043020420283d028210282104045020401880b0200d04041010dd0283d1b040020210703f028210283d010450403d0204000845028210283d02040
|8=>0x2040078410404102031078210f840020310403d020410784104041078210204100881020310403d0900b130950204202043168ab0205902058078410480b1304102043020411782002859078414a80b02251060420403d4380b020f90780e43843020f90780e040410283d010450282102040029d12d0410200f04847020410403d020400405a0200f0200e028410703f02821008dd1b04002021020210200c
|9=>0x283d0200e04041010dd1b04002021020410d0400203d1883f0200d04041029690200f04041040410782102041028570d0400203d0183d02021040410211f04059008450283d020404e00f0281104041020230204107a654c04202812068430283d020411880b0200d040410200f0284104041028210205807841078950403d020420f840020310403d078410d0400203d028210480b020410482f0204101045
|10=>0x20232383f04059078410703f0282102043042a14e040028115300702825020410285a0203d078410703f0282102040079690200f040410283d020420204307a911a013028410d0580203d078410299a0409502042178130285907841068210283d02043068210283d020400283d04045020400285a07841020410403d0405a078411b03f02021020434e00702811078410403d02845020400200d0780d04041
|11=>0x405a078410200d0200c04041040410204307841028520784502040040470283d020400283d0403d0204259811070430282102821028410204102aa94d04202023580211a01002841048470204002041020f90780e040410404102031078215300b0282502041042b9068120283d0204102841040410200c020210404102041020210283d068260283d02041028dd1b040020210483d020230204107aa94d042
|12=>0x283d020420283d04823020410211d04059078410200e0200f04041068990283d0204304095020420782102059078410203d0405a078414282102895020420283d0403d02821020410403d02040020ff0280e040411a26b02841020230211d04059078411403f04045020400211c040590784101a6102812040414f83d02845020400480b0403d02041041b50483f020410405207845020400280e0204302041
|13=>0x10450282102040020410403d02821028510784502040008450403d0204004041043250203f020fd0280e04041020fa0780e04041023041a02302841008dd1b04002021040750205b078410d00f0203d040411a0d802021028416184307011028210205902023078410205b0404107841023061a02302841178230285907841078410780e040414e05b0281107841178130285907841060950403d0204206897
|14=>0x4041020430403d020426a80b02351078420434d02826020411782302859078410782104045020400d0410203d028213303f040950204202043078210283d0203d020580784102040078210283d028b60483d020410204302841078410292e1b043020210233907040028214e0580281107841040411b03f020210702702821020410211d0405907841040450283d02040028a20404502040020431a03f02841
|15=>0x200e04041029d14d04102023028b60205907841290100280d040411a03d0284102041041c50205a0784102251060420403d0203d0200f04041020580284107841020230d0430203d6184007011028214e05802811078410480b0403d02041029b50483f02041028120203d07841040410782102043029751b04202021078dd1b0400202107841068430283d02043020410283d028210405a078410183d0200f
|16=>0x40570d0400203d738420701002821020430405a07841020210784104041028410282102043068250283d020410211e0405907841020fb0780e0404102043020210283d1403d04045020400200e02841040410b0230784104041020410405907841028414e04002811021590405a078410203d028590784102253060420403d020ff0280e04041440410d0230203d70807068110283d6f84107a610281202a39
|17=>0x13021020430404104261028120405a07841023c50704202821028a1040450204057042068120283d079e10200c04041021590405a07841068230283d02041440410d0230203d02059040410784100bb54e042028110283d1b0400202102aa14e040028110203d4d041020230702402821020410200d0280d04041020420283d028211783f02859078410b26302812078410709b0282102043028550d0400203d
|18=>0x483f0204157041068120283d00bc50704202821078450283d020400480b13041020430b26302812078410403d0404107841029ce1303d020430d0430203d028217384107010028217e04107013028217b042068130283d07a6902023040550d0400203d0200d0780e040410789502042070400284102821029e10200c0404116843020590784102841068130283d1781002859078410283d021df040427a03f
|19=>0x48330403d0204101b270203f04041068410283d020430480b0784102041070470282102040020fb0780e04041068230283d02042044110d0420203d020590284107841428230289502042028210283d02043028210289502042028210283d0204007a69020230204102a390200e040410203d0200f0404104041020210283d020f80780e04041010450403d020400283d4d042020230203f020210404102021
|20=>0x2041880070289902043020330403d0204164041043250203f1782002859078411a0100281102841078410403d028210d0420203d02821868410286a0203d1303d0282102043029e10200c040410203d028260204107c2f0701202821130310403d020430200f0280d04041020210284104041028250202302041040dd1b040020210204304059078415302302825020410200d0280e040410f83f020310403d
|21=>0xb2690202307841020411b03f0202187041020330403d020400480b02041022850285a078410480b02841020410703f0203d0282102845028210204002453068420283d0703f0784202821020410104502040178200285907841648410203f0403d04041078414c0410203d028120283d0200f040410e8410205b078410d00c0203d040410283d021dd040421680b0483d02041028211304102043020310403d
|22=>0x403d0f842020310403d0211f0405907841028310403d0204202043020310403d0233b070400282113095020420204304051078450204002c3b020330403d078210205b07841068450283d0204002c39020330403d04041078410204131012068430283d1883f0482102041020410282102040029690200f04041028210480b020417c04307a690202387042020330403d028310403d02041448431b03f02021
|23=>0x2841068400283d0203d028210403d020420283d0282104485028420d0430203d07842028210235307842028da020210283d0204302895020420283d020400203d028410202107841028410283d020310403d04821020410403d02821020330403d028110203f0405a07841020210203d0202104041068130283d4d04202023028470403d02040020950403d020421a03f028410204104059078410f84302031
|24=>0x204007842028410205a0784102485028424e043028114e042028111303d020430200f0404104059078410704302821028da02021068230283d07a61028120200d04041021dd040420403d020430403d020400285907841078470204002841020231b042020210483f0204107842040411b03f020210405907841068100283d043250203f04351078420d0400203d07042028210285907841068110283d1a012
|25=>0x203d0784102842060420403d02042020430282107841040450204002826020410780e0404102841078410084502040020230204102a6902023020400204107845020400480b020410200f04041020210203f04041078411a0130284102487028420403d07841078410204102845020400203d020410283d020234e0070281102825020410205a078410203f0404102847020404d04102023130410204302845
|26=>0x28114c04202812028110284102841020430280e0404101045020400d0230203d028210204202841078411a03f028414e0230281102b510784202058078411a0130284102812078410280e040410404107841028210204100c85028420203d028121a010028414c041028124e040028110409502042020430784102058078410703d028210480b02041028110784102841020410203d02043028990204302811
|27=>0x403d0203d028120204302040028110282102841020420204102842078410203f040421a01002841068120283d0403d020414e007
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x55000a00000000000
|6,0=>0xe681b9435200000caa18502ea0000000000002c285440a08131024200000000111020203b5000000001ba032505c80a901320000044800000000000000000000f201a4000000000aa80000000048c07200a4000000000000000
|7,0=>0x1ea23cc800000001e0600007620e931cc638cc6fa0db4000035d06b08d2419c832cc63a0000188630100000bc400002e105a20b1315a82a8c0000a73146827d04da0000000000000000000000026484b90000000000004a9092311e622d044188530000000000000001064200c3e9800000001ec83ba0000
|7,1=>0x33480000cb2194232260000c7198a430c8609000017e42f665e0cba9971400005b50b4a00002cc6589000000002bc8000000015a42b045510a9114e400005290a321424000050089e993a326c84c9097212a40000499091211e4234846448aa113221e8000085a00000000420c822000020083f4c7d18f64
|7,2=>0x8ed0000237446688c0d162228444a688510ea00004346859109220f3416800010508000000081cc00020520000808cff200003f487e44faa1f143da87a8cf411e533c280000ef180003b4876080001d4400000000e899ce3394872080001c4438080000de99b9436a80000d8a1ad435466990d1219e4
|7,3=>0x11fa0000
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
|0=>0x80800000003bc00000001ce00000000e60000000060000000002fc000000016a00000000af00000000500000000021800000001080000000082000000004000000000180000000005e000000002c00000000130000000009400000000480000000020000000000c000000000480000000020000000000c000000000500000000020000000000c000000000500000000020000000000c00000000040000000000
|1=>0x8b78000000450800000022140000001046000000080500000004010000000200000000009e500000004e0000000025000000000e86000000060000000001c200000000c50000000062400000003060000000102000000008000000000368000000018a00000000c10000000060000000002ac000000015200000000a1000000004580000000220000000010c00000000840000000041800000002080000000102
|2=>0x2098000000104500000008220000000410c00000020830000001041000000081de00000040bd0000002057800000102100000008100000000402f0000002003000000100080000008002000000400000000018950000000a2000000004748000000232f000000119300000008990000000446400000021af00000010b7800000084d8000000425e00000021260000001031000000080d800000040040000002000
|3=>0x3132000000187bc000000c35e00000060ef0000003057800000181bc000000c0c4000000602f000000300300000018000000000a250000000510a0000002884000000142bc000000a05e0000004966000000245f800000122bc000000897e00000044af000000225680000010e0000000085fe00000042af00000020f780000010798000000836400000041af00000020c40000001061000000082de0000004134
|4=>0x22006000001086a0000008405800000401af00000200a2000001004000000080030000004000c0000020004000001000100000080002000004000000000130f7800000986bc000004a21400000242ff00000120ff8000009048000000482140000024106000001207f8000008048000000283de00000140af000000a037800000404bc00000100de0000007002000000340a0000001a010000000c740000000626f
|5=>0x420f78000021079c000010835e000008416f00000420b580000210598000010824e00000840ef0000042057800002100bc000010635e00000821af0000041037800002045bc00001021de000008096f00000402fb00000200ed8000010076000000803af000004015f800002008bc00001003ec00000801af00000400b7800002004bc00001001de00000800bf0000023857800001143bc000008835e000004416f
|6=>0x438578000021a0bc000010c95e000008642f00000431b380000218c9c000010c5de00000862af00000430f7800002182fc000010c15e00000860a7000004301f800002180bc000010aade00000850ef0000042857800002132bc00001092de00000848af00000423b780000211abc0000108ade000008452f00000421f780000210f9c000010875e000008436f000004219b80000210bbc000010855e00000841ff
|7=>0xc005780000600000000028021800001061ef00000830930000041829400002083fe00001041bf0000082080000004103fc00002081f600001040bf000008201a80000410000000020434800001001860000063017800003145bc00001883de00000c416d0000062097800003103bc000018435e00000c016f0000060017800002902bc000014475e00000a21af00000508578000028086c00001401de00000a00af
|8=>0x1200440000090018800004800400000240002000010305780000814238000040a00800002041af00001020b7800008103bc000040815e000020402f000010091580000804498000040221800002011040000100857800008040380000402018000020100a000010080300000804000000040035e000020016f000010000200000690bbc000034435e00001802e600000c015f8000060081c000030035e00001800b7
|9=>0x2620f7800013086bc000098215e00004c00af0000243857800012180bc00009083de000048306f00002408f5800012043bc00009002de000048014c00002400978000111c6bc000088a3de00004450ef00002220f7800011103bc000088815e00004401a700002200758000101c3bc000080a15e00004041af00002020c000001008288000080215e00004001820000122005000009004180000480204000024008e
|10=>0x22008d6800110040bc00084081de00041821af0002060057800102184b400081092de00040841ef0002042096800102042bc000810015e00040041800002000845000100040880008000210000201006f0000802147800040102bc000200811e000100226f0000801037800020000880000c0805e000060400000003001178000180089c0000c0005e000060002700003000030000131c3bc000098a2de00004c50ef
|11=>0x2000a067800903105bc004098e05e00204c50af00102420d7800803107bc00401882de00200c206f00100428b7800802140bc00401083de00200452a7001002201780080100030004000815e00200000a4001000001000080000040003088a2de00180841ef000c0420f7000602105bc003000a2de00080841af0002302817800118105bc000898435e00044c00af00022420d780011018680000880a2de00044040af
|12=>0x1004022077820000303bc0c0002819e02000140ef0090002857804019105bc0200c8045e010064020e00803200d7804019002bc0200c0835e01006000af0080222017804010183bc02008081de010040002f0080103077804008106bc020040815e01000860af00800428f7804001100bc020008800801000400ae0040002157002000102bc010000815c00400941ef002000b0f780100050b3c00800283de00400140ef
|13=>0x102000140cf40002028d7980200103bc600010435e30000401af
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x5028000000
|6,0=>0x18140a000280c0200000000e050280c0e00000140a050000006070081416000280000000000010010000024000000c0a06000000000
|7,0=>0xa18000a96030000605a607c000c0300c0205000200e000585c00000c894000f17014a004002140845000a882051481c0a0700430288602a5038010f800a6090000c4c00038181415852580000018000e030180410020008c72304a88408004b81c00070002294030401800034852c18000000000000004ca0000000068010d94406200000000003b00c0c00000040a09
|7,1=>0x2a000002b4121d2586d0c2d0085c2c00008880a012500080fe0000400500000c7600290d8a22107154260b260000a00a32680005000260e2f029400007028012e4302001e6f5019082b34
|8,0=>0xce4e2aaca8f3840e6789ba048d18c5e95f0806c399e63a6842e5876ea4550dfd10884f395020c4ca8ab406f25c83576165f32e8e1a49784ba8e80694e94c6c6c212538259b3056f132888de5704c332b2667e308e8e57610e24f478f254d05d2ddc589685b1fb8a6915eb0f458d8e91492c5c20466b5dd0c111cf078ee3d269646403c28f874b7b12247b2382309ec43
|8,1=>0x97e624135910f5d854629ce6ebb369a9656f1ab61a727cee35195352a766c0595d11aa7414441cd4f8d30db671d01b91056563ae43148bc589c6945266599b1c57cb85a6437de4a1359c9b0fba90dc8d9f87cb5b58f3ad0dceb6c73a8b2008a98953241fb15a45b368b200819829aa26446ac2d2efc5dd93ed5b131cfab94c1c25c9b255e2ae3358b0add5407bdcbc68
|8,2=>0x2b9fd3c5d62295a51f331908ace2a0c653732246d4e7abb5fdbcb78eb2504be6921e67a4c9cb4c988a586a38abad465f4c089604f2c6b4351b818
|9,0=>0x13238b66d4b798ca1c74e66e46793cbbcf9f1316acf54992d0d65aad55c22cc87ba3e0dda7e33ded795c5a15f2c57a1381d3863e5f4f46fc024997059caf556fcb899ecf6d5fbe5ac573d9f2f96533b5eeaa2321ee0794a0d79de933f305835b2bcecb27c72b2557146e390b29cb25854709cd30a8ab533e5cc8d1b0502c13f604958867ccb4afcff5e19ecc57
|10,0=>0x154616915caeeec84f4b27c5a060f048
|11,0=>0x11
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 41 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_125 10 roots_125 ops++addP pm 1 dom_119 9 roots_119 ops++addP pm 2 dom_126 9 roots_126 ops++addP pm 3 dom_95 9 roots_95 ops++addP pm 4 dom_54 4 roots_54 ops++addP pm 5 dom_123 10 roots_123 ops++addP pm 6 dzo_111_16 7 roots_111 ops++addP pm 7 dom_63 8 roots_63 ops++addP pm 8 dzo_47_16 6 roots_47 ops++addP pm 9 dom_118 7 roots_118 ops++addP pm 10 dom_103 5 roots_103 ops++addP pm 11 dom_110 5 roots_110 ops++addP pm 12 dzo_87_32 6 roots_87 ops++addP pm 13 dom_43 5 roots_43 ops++addP pm 14 dom_111 8 roots_111 ops++addP pm 15 dom_59 7 roots_59 ops++addP pm 16 dzo_107_4 6 roots_107 ops++addP pm 17 dom_55 5 roots_55 ops++addP pm 18 dzo_94_32 6 roots_94 ops++addP pm 19 dzo_86_32 5 roots_86 ops++addP pm 20 dom_62 5 roots_62 ops++addP pm 21 dom_86 5 roots_86 ops++addP pm 22 dzo_95_32 7 roots_95 ops++addP pm 23 dzo_43_4 5 roots_43 ops++addP pm 24 dom_107 7 roots_107 ops++addP pm 25 dzo_123_4 7 roots_123 ops++addP pm 26 dom_94 6 roots_94 ops++addP pm 27 dzo_109_2 6 roots_109 ops++addP pm 28 dzo_109_16 6 roots_109 ops++addP pm 29 dom_77 5 roots_77 ops++addP pm 30 dzo_107_16 6 roots_107 ops++addP pm 31 dom_109 7 roots_109 ops++addP pm 32 dom_87 6 roots_87 ops++addP pm 33 dzo_59_4 6 roots_59 ops++addP pm 34 dom_122 7 roots_122 ops++addP pm 35 dom_115 7 roots_115 ops++addP pm 36 dzo_93_2 6 roots_93 ops++addP pm 37 dom_61 6 roots_61 ops++addP pm 38 dom_117 7 roots_117 ops++addP pm 39 dzo_77_2 5 roots_77 ops++addP pm 40 dom_91 7 roots_91 ops
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
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_111_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_47_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_87_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_107_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_94_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_86_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_95_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_43_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_123_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_109_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_109_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_107_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_59_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_93_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_117 _ g hchk
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 49 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 49 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 194 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 66 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 194 → Z 7 i = true := (range_split z7_0 z7_128)
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
namespace S_223
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(2,18),(2,130),(3,11),(3,19),(3,67),(3,131),(4,20),(4,68),(4,132),(5,13),(5,21),(5,69),(5,133),(6,22),(6,70),(6,134),(7,15),(7,23),(7,71),(7,135),(8,9),(8,72),(8,136),(10,11),(10,26),(10,74),(10,138),(12,13),(12,28),(12,76),(12,140),(14,15),(14,30),(14,78),(14,142),(16,18),(16,20),(16,80),(16,144),(17,19),(17,21),(17,25),(17,81),(17,145),(24,25),(24,26),(24,28),(24,88),(24,152),(64,65),(64,68),(64,72),(64,80),(66,67),(66,70),(66,74),(66,82),(66,194),(128,129),(128,130),(128,132),(128,136),(128,144),(192,193),(192,194),(192,196),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffffff
def xsM:=roots_223.map (·&&&dom_223)
def gM:=goal_223&&&dom_223
def NN:Nat→Nat
|9=>1
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0x94644
|10,0=>0x1730e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffff0000000000ffffff0000000000ffffff0000000000ffffff00ffff000000000000ffff000000000000ffff000000000000ffff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0cccccccc00000000cccccccc00000000cccccccc00000000ccccccccaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaaffffffff000000000000000000000000ffffffff0000000000000000ffffffff00000000ffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ac688fac688
|_=>0
def sO:Nat→Nat→Nat
|9,0=>8
|10,0=>0x87
|_,_=>0
def wAt:=mkWire dB 8 224 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xd5
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
addP pm 0 dom_221 9 roots_221 ops++addP pm 1 dom_159 9 roots_159 ops++addP pm 2 dom_95 9 roots_95 ops++addP pm 3 dom_219 9 roots_219 ops++addP pm 4 dom_222 8 roots_222 ops++addP pm 5 dom_215 8 roots_215 ops++addP pm 6 dom_214 7 roots_214 ops++addP pm 7 dom_207 8 roots_207 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_223 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_207 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_221 9 s (0,roots_221.map (·&&&dom_221)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_223 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_221 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_223==dom_223)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_223 gM v ys):RunD true dom_223 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_223 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_223 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,64,68)] (by decide +kernel) lowS_235
def dzo_183_64:=0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000
def gzo_183_64:=0xff00ff00ff00fe000000000000000000ff00fe00ff00fa0000000000000000
def gsh_183_64:=0xff00ff00ff00fe000000000000000000ff00fe00ff00fa
theorem lowS_zo_183_64_162:Lower true dzo_183_64 roots_183 gzo_183_64 7:=lower_iso_b (d1:=dom_183) (r1:=roots_183) (T1:=gsh_183_64) [(dom_183,64)] (by decide +kernel) (lower_slice_b (T:=gsh_183_64) [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa,0,1),(0xf000f000f000f0000000000000000000f000f000f000f0,0,4),(0xff000000ff0000000000000000000000ff000000ff0000,0,16)] (by decide +kernel) lowS_162)
def dzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
def gzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00ee00000000
def gsh_215_32:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00ee
theorem lowS_zo_215_32_84:Lower true dzo_215_32 roots_215 gzo_215_32 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_32) [(dom_215,32)] (by decide +kernel) (lower_slice_b (T:=gsh_215_32) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,0,2),(0xff00ff0000000000ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_213_32:=0x33003300000000003300330000000000330033000000000033003300000000
def gzo_213_32:=0x33003300000000003300330000000000330032000000000032002200000000
def gsh_213_32:=0x330033000000000033003300000000003300320000000000320022
theorem lowS_zo_213_32_84:Lower true dzo_213_32 roots_213 gzo_213_32 6:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_32) [(dom_213,32)] (by decide +kernel) (lower_slice_b (T:=gsh_213_32) [(0x220022000000000022002200000000002200220000000000220022,0,1),(0x330033000000000033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
namespace S_247
def pG:List (Nat×Nat):=[(1,33),(1,65),(1,129),(2,18),(2,34),(2,130),(3,19),(3,35),(3,67),(3,131),(4,20),(4,68),(4,132),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,23),(7,39),(7,71),(7,135),(16,18),(16,20),(16,80),(16,144),(17,19),(17,21),(17,49),(17,81),(17,145),(32,33),(32,34),(32,160),(36,37),(36,38),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,112),(48,176),(64,65),(64,68),(64,80),(66,67),(66,70),(66,82),(66,98),(66,194),(96,97),(96,98),(96,100),(96,112),(96,224),(128,129),(128,130),(128,132),(128,144),(128,160),(192,193),(192,194),(192,196),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_247.map (·&&&dom_247)
def gM:=goal_247&&&dom_247
def NN:Nat→Nat
|5=>4
|6=>16
|7=>68
|8=>139
|9=>108
|10=>15
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x9e54c5fa2546a2a241f2
|6,0=>0xf7936f5d4dbf07eba9dbab2289dd7998996917f583bd97d2d86dad65efd94e5921da190a445060e3
|7,0=>0xfe62efd3d2fbeaafb9f3f4206f37e6f2193ee9a5eded7ede84ec16ce59d6e3c40e2b20df7f8d7072d45b2ccb60cb3f1c7583aff6faa678aa3aba763aa2356a099ca076d9fae09e11d99a6f93aca90dbd8d6d6857dd80dd57671c7377c7356a6beb769a9e67a6f56363552a8549b451ebf48bea4711044437438a33fc5c3f30c3ac5739d0e35c8a34356340a133ea22b7ce28ff1285ba2587a24b541c90115a7611bdd0e5a307cde034f2
|8,0=>0xeb970eb62feaf20ea6c4e832ce2a08e1e3de06c8dfa1ddecf0ddd3bdd595dad1cd5793d4dc0d3ce7d317ed2bc3d2887d26d6d0438ced18cd6e0c32ebc2535c095cbed5cbe2d1b9924b52abb3ec6afcb9aedd9ae138ad481abcc0aa20ba9ec7a9da3a6413a5dc39e3929c33b9acbe9a1eb997699687695c9f8ddcd8c91d8b8f48b51187d9a8674083459808fd7fcee7dfb07c5de76f2c75a44752d17412a734ea7201471fa371a956feb66e51b6df7c6d65069adb6725c5f9ba5e6d15cc095c2435ba22580ce57d5d56f8f5681555da650a874ef734c0c649c844977a4800b45f3e429c43f9863dcbe3d4f03c8fc3c85b3c2c839d472fecb2f14c2e0de2c7802b8812a7fa2a24f216a120c96202511b75919c2819b3319094168d713e8313bb113a38133ea1248f116881024f0b47b0aeb40a3630989209745058d702e4d001d7
|8,1=>0xfbf8ffa86ff911bf638af3fe2f3e3eef09cee0d1edfdced53dec112
|9,0=>0xfb60ff5a42f110fec291e9390e9229e39e1e06a5e031adf8dcdef36db0c8d9b20d8de6d8a46d6743ccf5dc962fc839fc6820c1903c0bf1b44e1b33dfb2322b18edaf571ac1a4a8078a63bba447aa4107a3d7ca36e7a26f99deff95974952e394dfa93ea091cb290afe8d96e8c05f896fc88c438823787cd4872b485d96848828251a8218f7f9fc7e7be7b5b477f43766277534f6ff236fc786fc066f2da6ed776cf3a6cdd06713a64520638b15d0ec5bb105635655a5c53ea5537a14fa5d4e0194930648c35403353cdfd3c4e63c04734a6b30b15303da27c4a27127231a122d5921f94200ce1f9931e888194df1819116dea15a1d151771327b106ad0fdb30f9160f5380d37d08ac5056eb019af
|10,0=>0xff591f9dd7ba86bb4b4eb47c3b412eb1f769ac028898a8064d7fd216aad42e5361950c17a11
|11,0=>0x3ef7d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff0000000000ff00ff0000000000ff00000000000000ff000000000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc000000cc00cc00cc0000ff00ff00ff00cc00ff00ff00ff00cc00ff00cc00ff00cc00cc00cc00cc00cc00000000ff00ff0000000000ff00ff000000ff00ff0000000000ff00ff00000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0ff00ff00ff00aa00ff00ff00ff00aa00ff00aa00ff00aa00aa00aa00aa00aaff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000ff00ff00ff00f000ff00ff00ff00f000ff00f000ff00f000f000f000f000f0cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000
|0,1=>0xff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00000000ff000000ff00000000000000ff000000ff000000ff0000000000000000000000000000000000000000000000000000ff00000000000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000ff00ff00ff000000ff00ff00ff000000ff000000ff00000000000000000000000000000000ff00000000000000ff000000ff000000ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff000000000000000000000000000000000000000000000000ff00ff00cc00cc00ff00ff00cc00cc330033003300330033003300330033003300330033000000330033003300000f000f000f000f000f000f000f000f000f000f000f000f000f0000000f0000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000000000000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000000000000000ff00000000000000ff000000000000000000ff000000ff000000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff0000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff0000
|0,2=>0xff00ff0000000000ff00ff0000000000ff00ff000000000000000000000000330033003300330033003300330033003300000033000000330000003300003300330033003300330033003300330033003300330033000000000000000033003300000000003300330000000000330033000000000033003300000000ff003300ff003300ff003300ff003300ff003300ff003300ff000000ff0000ff00ff00ff00ff0000000000ff00ff00ff000000ff00000000000000ff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff000000000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff000000ff000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00003300000033000000330000003300000033000000330000000000000000ff00ff00000000000000000000000000ff00ff00000000000000ff000000000000000000000000ff00ff00ff00ff000000000000000000ff000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000ff00ff00cc00cc00ff00ff00cc00cc00ff00ff00cc00cc00ff00ff00cc00cc
|0,3=>0xff00ff0000000000ff00ff0000000000ff000000ff000000ff0000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff000000000000000000000000ff00000000000000ff00000000000000ff00000000000000000000000000000000ff00ff00ff00ff000000ff0000000000ff00ff00ff0000ff00ff0000000000ff00ff000000000000000000000000000000ff0000000000000000000000000000000000000000ff00ff00ff00ff00ff000000ff0000ff00ff00f000f000ff00ff00f000f000f000f000f000f000f000ff00f000f000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff000000ff0000ff00ff0000000000ff00ff0000000000ff00ff000000ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff000033003300330033003300330033003300330033003300330033003300330000ff00ff00ff00ff00ff00ff00ff00ff000000ff00000000000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00000000
|0,4=>0xf000f000f000f000f000ff00f000f000f000f000f000f000f000ff00f000f00000ff000000ff000000ff000000ff000000ff00000000000000ff00000000ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff000000005500550055005500550055005500550055005500550055005500550055000033003300330033003300330033003300330033003300330033000000330000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ff00ff0000000000ff00ff0000000000ff00ff00ff00ff0000000000000000ff00ff0000000000ff00ff000000ff00ff00ff000000000000000000000000ff00ff0000000000ff00ff000000ff00ff00ff0000000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff000000ff0000ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff000000000000000000000000000000000000ff00ff0000000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00ff00cc00ff00cc00ff00cc0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0000ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc0000000000000000
|0,5=>0xff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff00ff00ff0000000000000000000000000000000000000000ff000000ff000000ff0000000000000000000000000000000000000000ff00ff00ff000000ff00ff00ff00000000000000000000000000000000000000000000ff00ff0000000000ff0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff000000ff000000000000ff00000000000000ff00000000000000ff00000000000000ff0000000055005500550055005500550055005500550055005500550055005500000000ff00ff00ff00ff00ff00ff0000000000ff000000ff000000ff0000000000000000000000000000ff00ff00ff0000000000000000000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00ff00ff0000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc00cc00cc00cc00cc0000000000000000ff00ff00000000000000000000000000ff00ff00000000ff000000ff000000ff00ff00ff000000ff000000ff000000ff00ff00ff000000000000000000000000ff000000000000000000000000000000ff00000000
|0,6=>0xff00ff00ff00ff000000000000000000ff00ff00ff0000ff00ff00ff00ff00ff000000ff00000000000000ff00ff0000000000ff0000ff00ff00ff00ff00ff000000ff000000ff00ff0000000000ff000000000000ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff0000000000ff00000000ff00000000000000ff00000000000000ff000000000000000000000000ff000000ff00ff00ff000000ff00ff00ff000000ff00ff000000000000000000000000ff00ff0000000000ff00000000000000ff00ff0000000000ff0000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00ff00000000ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff0000ff000000ff000000ff000000ff000000ff00ff00ff000000ff00ff00ff000000000000000000000000000000000000ff00ff0000000000ff00ff000000000000000000000000ff000000ff0000000000000000000000ff00ff00ff0000ff00cc0000000000ff00cc0000000000ff00cc0000000000ff00cc000000000000000000000000ff00ff00ff00ff000000000000000000ff00ff00000000ff000000ff000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff0000
|0,7=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00ff00ff00cc00cc00000000ff00cc0000000000ff00cc0000000000ff00cc0000000000ff00cc33003300330033003300330033003300330033000000000033003300000000ff00ff00ff00ff00ff00ff00ff00ff00330033000000000033003300000000cc00cc00cc00cc00cc00cc00cc00cc00ff00ff00cc00cc00ff00ff00cc00cc00000000000000000000ff000000ff0000000000000000000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff0000000000000000000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff000000000000000000000000000000000000000000000000000000000000ff00ff00ff0000ff00ff0000000000ff00000000000000ff00ff0000000000ff000000000000ff00ff0000000000ff00ff0000000000ff00ff00ff00ff00ff00ff00ff0000000000000000000000000000000000000000000000000000ff00ff00000000ff00ff00ff00cc00ff00ff00ff00cc00ff00ff00ff00cc00ff00ff00ff00cc3300330033000000330033003300000033003300330000003300330033000000003300000000000000330000000000000033000000000000003300000000cc00ff00cc00cc00cc00ff00cc00cc00cc00ff00cc00cc00cc00ff00cc00cc
|0,8=>0xff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff00000000ff000000ff000000ff00000000000000ff000000ff000000ff000000000000ff000000cc000000ff000000cc000000ff000000cc000000ff000000ccff003300ff000000ff003300ff000000ff003300ff000000ff003300ff0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ff00ff0000000000000000000000000000000000000000330033000000000033003300000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc00000000000000000000000000000000ff00ff00ff00ff0000000000000000ff00ff00ff00ff000000ff0000000000ff00ff00ff00ff000000ff0000000000000000000000000000000000000000ff00cc00ff00cc00ff00cc00ff00cc
|_,_=>0
def sP:Nat→Nat
|0=>0x5040701170008100f070201000805040702011c080504070201001b0d07020109000504070201001a0504070201190818050d02011600140f0201160c0e050d0117160c0e0504130702010c05041307020100051104070201000d07020109000c0504070b0100080504070a0100070201090008050407020600050403020100
|1=>0x2012d080d0702011d120014210f0702010c0e05040d07011700050d02012c16000e05040d07020100191404290702010c0e052b07020100250e14040702012a0c0e05210d0701170c0e0528040702010c0e0d0702011d270c0e0504070201002505040d070201220c20050d020116000e05040702010c1e0e0702011d120008
|2=>0x100050d020116120c0e0d070201090c0e05040702011d0008100d0f070201000c05040f070201000805262b070201000e05040d070201003605040d070201001c050d0701320c0e05040d070201300c0528040702010005040d070b010014040f0702010005040702012e000810050d0201160c0e1805210d07020100050407
|3=>0x100504070201000814040f070201000c050d0201410c0e0504070201004005040d3f070201000d0702011d12000c200504070201000805040d070117000c05040d07012c2e0005040702010c1514043e0702010c0e0504070201003d3c050d0702010c0e050407020100151405040201160c0e050d3902010c0e05040d370702
|4=>0x170c0e0504070201120008050d07012c4b000e054a040d07020100480d0702010e05040d0702010047050d070201460c0e0545040d07020100052604070201002518050d0702010008050d0201161d0c0e100d290702010c0e050d0f0201160c0e4305040d0702010c05260407012e0005040702012c00080542040702010008
|5=>0x230702010c0e54050d0702010005040d0753012e0c05040d0f070201000c5105040702010c0e05280d070201000e0d0702011d120c0e05040d0702012c00050d4f02010c0e05040d0701170c0e0542040d070201001005040d07020100050d0702012d080e050d0702014d0c0e050d07024c0c0e100d0f07020100050d230701
|6=>0x15b0c0e05040d0702010038490d0702015a0c0e05040702010c080e050d070259000e05210d070201120c0e050d580702010c0e56050d0702010c0e05280d0702010c0e1405040702010020340d0753010c05040d070b010c0e05040d070201270c0e14040f0702010c0e05040d0702011d000c05040d0702011f0c0e140504
|7=>0xd580702010c0e5f050d0702010c0e050d29070201000e550d0702012f0e1452040702010c0e050d07012c2e0c0e05420d07012e0c0e44050d0702010c0e050d0702015e0c0e05260407020100490d0702012f0e5d05040d0702010c050d0702015c0c0e140521040702010c0e050d0702590c0e05040d0702011200050d0702
|8=>0x702010c0e05660d070201000e05040d0702015e0c0e63050d0702010c0e050d0702010c3d0e20050d07020100080e050d0702010c150e050d290702010c0e14620702010c0e050d070201003d0e050d0702012a0c0e05040d0702015b0c0e05210d0702012d0e60050d0702010c0e05040702010008050d07020100150e0504
|9=>0xd290702010c0e05040d0702012a0c0e05040d070201002f050d07020169000e05660d0702010c0e14610d0702010c0e05040d0702012e005f05040d0702010c0e68050d0702010c0e14670d0702010c0e05040d07012c2e0c0e2005040d0753010c050d07020100400e050d230702011d0c0e1005040d070201000c4405040d
|10=>0xe05040d0702011d00050d0702016c0c0e05260407012e0c0e05040d07020112000c05040d0f07020100050d070201006b0e050d0702010c6a0e05210d0702011d0c0e35050d0702010c0e3405260d0753010c05210d0f0702010c0e050d0702012c00080e050d070201240c0e140504070201000c050d070201006a0e0504
|11=>0xe050d3e0702010c0e050d0201160c0e10050d230702010c0e05260d0701720c0e05260d0770010c0e520d070201380e2005210d070201000e050d020116000e05040d070201240c0e05260d07020100250e6f050d0702010c0e050d0702016e0c0e050d0702010c6b0e05260d07012e0c0e050d6d0702010c0e052b0d070201
|12=>0x1002d0e050d0702011f0c0e740d070201380e050d070201300c0e050d76070201000e6f05040d0702010c0e2005040d07020100050d0701170c0e050d07020127000e050d07020100250e050d0702013b0c0e0526040753010c05040d070201002d75050d0702010c0e100d0f0702010c0e05670d07020100050d0702014b00
|13=>0x2010c0e05040d070201000c05040d3e0702010c0e05040d0201160c0e050d0702017a0c0e1005210d0702010c0e050d070201790c0e18050d07020100050d780702010c0e050d070b010c0e050d070201270c0e140f0702010c0e053a0d0702010077050d0702010c0e05040d070201310c05210d0702012c000e052b0d0702
|14=>0xc0e050d07020100080e050d070201002f0e7f050d0702010c0e050d0702017e0c0e050d0702017d0c0e20640d0702010c0e51050d0702010c0e0526040702010c0e34050d075302010c200d0702015a0c0e050d0702015a000c0e050d0702017c0c0e05040d070201120c0e20050d0753010c0e05260d070201000e7b050d07
|15=>0xf0702010c0e14520d0702010c0e05260d070201710c0e050d0702014e0c0e3405330d0702010c0e050d070201720c0e550d0702015a0c0e050d077002010c0e050d070201000c380e050d0702010c080e050d0702010c2f0e050d0702012e0c0e050d0702015a820e050d070201810c0e05800d0702010c0e1457050d070201
|16=>0x2010c0e85050d0702010c0e05520d070201000e05330d070201000e050d070201710c0e050d070201002d0e14050d070201820e57050d0702010c0e050d070201840c0e050d07830201000e050d230702010c0e20340d0702010c0e14200d0702010c0e14050d070201000c0e050d0702011d0c0e05040d0702012e0c0e050d
|17=>0xe050d070201880c0e05040d230702010c0e14640d0702010c0e340d0702012c0c0e340d0702015a0c0e05210d0702010c0e050d070201310c0e140d0702012c0c0e14550d0702010c0e05040d0702011d0c0e05040d075302010c05040d0f0702010c0e20050d070201000e050d070201870c0e05210d070201000e05860d07
|18=>0x670d0702010c0e49050d0702010c0e1405260702010c0e050d0702012c000e55050d070201000e050d0702015a000e05740d0702010c0e05260d0753010c0e49050d070201000e05040d070201000564260d0702010c0e050d070201690c0e05740d070201000e89050d0702010c0e0542260d0702010c0e050d070201000c2f
|19=>0x10c0e050d0702010c380e050d070201500c0e5d050d0702010c0e14340d0702010c0e18050d0702010c0e050d07020100380e7305260d0702010c0e053a0d0702010c0e05620d0702010c0e2005040d0702010c0e05420d0702010c0e05610d0702010c0e0521040d0702010c0e10050d0702010c0e0552040d0702010c0e05
|20=>0x70201000e05260d0702010c0e050d075302010c0e0564330d0702010c0e1405040702010c0e050d760702010c0e73050d0702010c0e14050d070201000e54050d0702010c0e050d070201120c0e05040d0702012c0c0e5505040d0702010c0e65050d0702010c0e0542040d0702010c0e1005040d0702010c0e3405260d0702
|21=>0x50d0702010c0e34050d0702010c0e14050d0702010c0e05640d0702010c0e050d0702012c0c0e55050d0702010c0e050d0702015a0c0e050d070201820e050d070201000c0e20050d0702010c0e05520d0702010c0e05330d0702010c0e05040d0702010c0e050d
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x12600c600660006
|6,0=>0x8070797072706b7064705e6057705070497042703b7034702d7026701f70187
|7,0=>0x26d8265825f6257824f8247823f8237822f8227821f821782107208820081f881f081e971e271da81d281ca81c281ba81b371ab81a4719c8195718d8186717e8176816f7167815f8157814f8147813f8138713081297122711b7113810b810380fc70f570ed80e670de80d680ce80c680be80b680ae80a6809f7097808f80878
|7,1=>0x28c7285727d82758
|8,0=>0x48d9484947b9473846a9462845a845194498441843a7432842a842194198411840a740283f993f183e983e273da83d283ca83c283ba83b373ac73a4839c8393938c7384837c8374836c8364835d7354934c8344833c8335732e7326831d9315830c930392fa92f372eb82e292da82d282ca82c282bb72b382ab82a3829b82938
|8,1=>0x696868e8685967c9674866d7665865d8654964c8645763d8635862d8626761e8616860e860775ff85f785f075e795df85d785d075c795c075b795ae95a6859e8596858e8586857e8576856e8566855d9555854d8545853c9534852c8523951a9512850a850284f994f094e884e084d884d084c884bf94b784af84a6949e84968
|8,2=>0x6eb96e386db86d296ca86c376bb86b476ac86a5769e7
|9,0=>0x8f788ee98e688de88d688ce88c688be88b688ad98a5889c9894888c8884887c8874886c8864885c8854884c8844883c8834882c8824881c8813980b880297fa87f287e997e187d897d087c887c087b797af87a7879f8797878f8787877e9776876e8766875e8756874e8746873e8736872e8725971d8714970c870486fc86f48
|9,1=>0xa629a5a8a528a4a8a428a3a8a328a299a209a188a0f9a0699fd99f589ed89e589dd89d589cd89c499bc89b489ab99a3899b8992998a898199798971896989618959895189498941893989327929992189198911890898ff9
|10,0=>0xad98ad18ac98ac18ab98ab18aaa7aa28a9a8a928a8a8a828a7b7a738a6b8
|11,0=>0xae17
|_,_=>0
def wAt:=mkWire dB 138 248 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x40c414100d0e414350c0e4400b0504434392107c34010c0e474020504c30390d0e414350521010310d0e434952600830390d02410311002c14110d0e434a50521010310d0e434392600830390d02490390523c10330d0e4841f0d004303905024347e120c414120415050000c0e43039100fc14100504434390415c5000050d44802050483039100fc3039050401411
|1=>0x50083039100fc14100504434390d00814130c0e414100504434020504030390d25498020c0e434091200814120c0e434391000030390504434393502cd0cd0d0c41439310c474390504c34bd0500030390d0e430391002014110d0e43039050403439050d4100b0d00830390d0e4841f050443439200ec34010c0e414090d00808020c0e434390504c14120c0e43439
|2=>0x440ec148d040cc30390402c34390d02434390d00830390502c34020c0e434390504434020c0e414100d0e414353507cd0cd0d0c414392600030390d0e43409042fc14000c0e414120504c30390d00830390d0e430391002c14110d0e450000c0e43439050d414100d0e414350508834020c0e434390d0e450000c0e414352107c1031050d41ced053accc3b0d0c410e3
|3=>0x402c3439020e414100d0e43039520d43439050cc34bd0500030390504814130d0e434390c0e4140b0750414cf0d0c4400b0504434390402430390d0e430390504434390d00808020c0e53831340dc14393501cd0cd0d0c414390504414100c0e434390504830390502c3401492fc14010500030390f00814100c0e434390c0e4803b0d008303905024841f050401031
|4=>0x50e410310d0e414354901d5439050c414120c0e434391d0c414130d0e414020c0e43439340c41439050dc8437040c434394901c14010c0e41412040c43439550403439050c55c39140cc14350d2f414000c0e430390d0e41435020e41409050e440080504434390521810310d0e414100d0e414350504c34390c0e44831050483439040cc3439050d5543b0c0e41431
|5=>0xd00430390526014350d02414220d0083039520483439050cc74310504c34390200834010c0e58435340cc14390d00830390d0e450000c0e41435550403439050c548110d0e414330521034010c0e41431050003039050cc3439050d4100b0d0e4140b4202c354d020e4148d040cc34395504c3439050c430390d0e434090500414000c0e4403b050443439343383431
|6=>0x521010310d0e548120d0e414330500030390d0e414ce0d0c430390d38414020c0e41435340cc14390402c30390d0e548110d0e41433643343431050ec1435520e414330402c34390502c14090d0e408392600030390d02414110d0e430390523410330d0e434e10500830395504c3439050c59433640d4143b0508834020c0e434020c0e41409140003039050d41484
|7=>0xd0244033140e41435643383431050ec14200d00830394202c98390d024d0cc0d0c414390d2d408020c0e414130c0e43439690e414ce0d0c4100b0d0e434090504834390c0e414100c0e434390508034020c0e56802050dc30390504c10310d0e4d0cd0d0c414390d0241439020e41410040c434390d00830390502c148f040cc34390c0e43439050d568020c0e41437
|8=>0x100cc14110d0e430390502434391002c5039050d414860d00430392600830390d02414eb330ec34310d0243439020e408020c0e43439053a4cc3b0d0c41410050443439740e414030c0e4840b0d00430390f0c414100d0e4841f0d00430390504434397302c14990d02409c50526c3409050083039050cc34010c0e414092107c34010c0e4148f040cc3439260083039
|9=>0x20e430390d0259009050ec34390c0e43c310504034392107c10310d0e4d0cf0d0c414390504410310d0e540390533c3431200ec303905025d839053303431100205039050d414860d0043039050403439050d4cc3b0d0c430395d0cc503b050d474390504c34390d00430390502c34b5020083039120c414120d0e414020500c3039310c56839050dc14cc0d0c43039
|10=>0x50d414130d0e4100b0d0e414100d0e41435050cc149b0d024d037050e43431050e4500b050d41437050c40969050dc14020c0e434020c0e414000c0e4100b0d0e4303b050dd6831050dc983b0d0245033050d434020c0e414000c0e4154d020e4149a0d024d00b050e41409050ed4835050cc34390d0241439020e41409050dc14370c0e4b0390502c14120d0e41409
|11=>0xc0e55435050c498390d02414000c0e55437050c410330d0e4143b050d414390502c1439050dc34010c0e56839050dc14350502c1435050c414130d0e43439020e414100d0e430390502480370502434010c0e434b10502d9031050ec3039050cc34310c0e4149b0d02408020c0e4303b050d45033050d4154f020e408010c0e410330d0e41409050e41409050d43039
|12=>0x50c59035050ec10090d0e414110d0e414390d02414020c0e414cf0d0c4503b050d41439050d4803b0502414020c0e414990d024cc3b0d0c414980d02414090d0e4354d020e4d033050e410310d0e45039050d43439050cd4839050cd5439050c414350d02430390502c3039050c43039050dc14030c0e43409020e414010c0e430390d0e4143b0d02414ce0d0c41403
|13=>0x50e41435050ec140b050c414370c0ec30390502414330d0c434390c0e43409020e43431050ec3439050d414cc0d0c414990d0243039050d5543b050c414120d0e434390502c3439
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x3cc0a500000000000000000000001cc0430010000
|7,0=>0x34080003310c84000000031c4c340000000300cbd32e50b542c8cb022b10a842910a13278c9b325d000024d09032310000221085320507e300007a41e087531c8c6e41a9066418905f316d057414d04f4130c48411104040f103840d4c3140b502940000254085000007501940550123
|7,1=>0x3610d440000d22
|8,0=>0x196364cd903634d8a361cd843604d7e35ecd7835d4d7235bcd6c35a4d66358cd603574d5a355cd543544d4e352cd483514d4234fcd3c34e4d3634ccd3034b4d2a349cd243484d1e346cd183454d12343cd0c3424d06340cd0033f4cfa33dccf433c4cee33acce83394ce2337ccdc3
|8,1=>0x954e52393ce4c3924e46390ce4038f4e3a38dce3438c4e2e38ace283894e22387ce1c3864e163850a113838e0b3820e053808dff37f0df937d8df337c0ded37a8de73790de13778ddb3760dd53748dcf3730dc93718dc33700dbd36e8db736d0db136b8dab36a0da53688d9f3670d993
|8,2=>0x27639cce7039b4e6a399ce643984e5e396ce583
|9,0=>0xbdcaf52bccaf12bbcaed2bacae92b9cae52b8cae12b7cadd2b6cad92b5cad52b4cad12b3cacd2b2cac92b1cac52b0cac12afcabd2aecab92adcab52accab12abcaad2aacaa92a9caa52a8caa12a7ca9d2a6ca992a5ca952a4ca912a3ca8d2a2ca892a1ca852a0ca8129fca7d29eca792
|9,1=>0xd3cb4d2d2cb492d1cb452d0cb412cfcb3d2cecb392cdcb352cccb312cbcb2d2cacb292c9cb252c8cb212c7cb1d2c6cb192c5cb152c4cb112c3cb0d2c2cb092c1cb052c0cb012bfcafd2becaf92
|10,0=>0x35f1d7875d1d7075b1d687591d607571d587551d507531d487511
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x2366000044cc000084000001037000020440000408000008030000100200001be20000300000004e00000058000000800000006ec00000a08000012000000204000004000000060800000c0000001400000021000000400000003f000000600000008800000100000001f0000002000000010000000100000000
|1=>0x2a266000542180008edd800119b300023266000457ec0008abd80011173000222660004400800082bd8001014000020000000342880004289800060120000a35400014288000284100005002000082000001020000020010000400000003fa6000077ec0000eb980001d3b000033660000664c0000c99800015fb
|2=>0x8b076001142400022841000450020008807e001100ec0020cdd800419b700083276001056cc0020ac10004153300082376001044cc00208510004108200080a660010140800200510004008600080004000c77ec0018859800309d20004bb66000932c40010edd800219b300041204000654ec000c8d980018573
|3=>0x183366002560c80048cd980091933001222660021704c004204100057133000ab366001554cc002a89980055090000a62760014856c0028cd980051933000a2ae6001454cc00288db800511b3000a227e001444ec002889b80051133000a2166001356dc00268dd8004d13b0009a104001200fc0022e99800459bb
|4=>0x222af6004454ec00842998010047b001ae2760035c4cc006acd9800d5933001aaa66003546cc006a899800d317b001a62760034c4cc0068cd9800d1937001a3266003446cc006889f800d113b001a226e003444cc0068819800cd5370019aa66003344ec00638dd800c713b0018bb66003174cc006289d800c1db3
|5=>0x9aaa66013544ec0269ab9804d1573009a2a66013445fc026889c804d1137009a2266013156cc02628d9804c153700982266011454cc02288bd80451137005ab26600b546cc016a899802d11b3005a2266009564cc0128cd980251137004200000080004000eb89d801d7133003a2276006184ec008cabd8011177b
|6=>0x1020444cd02482b9a008443330183366403444cc20206890400493a060a3266040444cc0800c9980ad11b3011aa366023542cc0468c9b808d1933010aa166021464cc040a89980811933010223660204244c0402819005d313f00ba227e017444dc02c00bf804e5db3
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x10400000000000005010100
|7,0=>0x1a5b00011602121800280c36000005293114340a501a2706012b18137e1d46007a06060600082a01061118191a015f52810f3330485a031c0e2c180d09031b00174b100b
|8,0=>0x9662d5437bb5a8705085b36126689f4ac95b582468d2a7d97295d4d163157b6868356845657b402e6459705e7bc107556899595c4d603b7b89424c70ce4ea226003e638079753f2f9868b9476c2d257c2282796d578fcb4f9c3bac3a7fd87bc5d68768838949d7a6967d68b6a38a5c865d5d32af9d5167605a56d3b4a166448b
|8,1=>0x2dda7074709a68683bbec6
|9,0=>0xcabf68bdb6adbf6eae76a188ba987097b79ac0bdc86a9b9f90c7b76c698ebc5499536c9f831f6fcc5998a077ac41bfc28d3b6bbc95649e64849321b2aa713b6a4568916e3d3c8c95996a426acfb18dcdbbd073993c684268a939952360c4bcb8a46c39c39471b087a520783c
|10,0=>0x8bbf6868ab6a373c9268c8371e389e
|11,0=>0x37
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 31 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_246 10 roots_246 ops++addP pm 1 dom_231 9 roots_231 ops++addP pm 2 dom_87 6 roots_87 ops++addP pm 3 dom_85 5 roots_85 ops++addP pm 4 dom_243 10 roots_243 ops++addP pm 5 dom_119 9 roots_119 ops++addP pm 6 dom_229 6 roots_229 ops++addP pm 7 dzo_167_64 6 roots_167 ops++addP pm 8 dom_245 9 roots_245 ops++addP pm 9 dom_101 4 roots_101 ops++addP pm 10 dzo_85_32 5 roots_85 ops++addP pm 11 dzo_183_64 7 roots_183 ops++addP pm 12 dom_183 9 roots_183 ops++addP pm 13 dom_213 6 roots_213 ops++addP pm 14 dzo_87_32 6 roots_87 ops++addP pm 15 dom_103 5 roots_103 ops++addP pm 16 dom_181 8 roots_181 ops++addP pm 17 dom_55 5 roots_55 ops++addP pm 18 dom_215 8 roots_215 ops++addP pm 19 dzo_215_32 7 roots_215 ops++addP pm 20 dom_117 7 roots_117 ops++addP pm 21 dom_151 6 roots_151 ops++addP pm 22 dzo_213_32 6 roots_213 ops++addP pm 23 dom_167 6 roots_167 ops++addP pm 24 dzo_179_64 6 roots_179 ops++addP pm 25 dom_211 6 roots_211 ops++addP pm 26 dom_165 5 roots_165 ops++addP pm 27 dzo_182_64 6 roots_182 ops++addP pm 28 dzo_214_32 6 roots_214 ops++addP pm 29 dom_199 5 roots_199 ops++addP pm 30 dzo_163_64 5 roots_163 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_247 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_167_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_85_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_183_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_87_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_215_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_213_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_179_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_182_64_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_214_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_163_64_162 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_246 10 s (0,roots_246.map (·&&&dom_246)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_247 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_246 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_247 gM v ys):RunD true dom_247 gM v (ori ys):=h
def Z (s:Nat):=barP dom_247 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 68 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 68 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 139 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 11 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 139 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 108 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 108 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 15 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 15 0 = true)
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
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,18),(2,34),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(16,18),(16,80),(16,144),(17,19),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,160),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,72),(64,80),(66,67),(66,74),(66,82),(66,98),(66,194),(96,97),(96,98),(96,104),(96,112),(96,224),(128,129),(128,130),(128,136),(128,144),(128,160),(192,193),(192,194),(192,200),(192,208),(192,224)]
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
|10,0=>0xac435
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0cf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ac688fac688
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
|0=>0xcd
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
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_187 10 roots_187 ops++addP pm 2 dom_123 10 roots_123 ops++addP pm 3 dom_243 10 roots_243 ops++addP pm 4 dom_235 10 roots_235 ops++addP pm 5 dom_249 9 roots_249 ops++addP pm 6 dom_219 9 roots_219 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_219 _ g hchk
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
def dzo_221_32:=0x3333333300000000333333330000000033333333000000003333333300000000
def gzo_221_32:=0x3333333300000000333333330000000033333332000000003332332200000000
def gsh_221_32:=0x33333333000000003333333300000000333333320000000033323322
theorem lowS_zo_221_32_84:Lower true dzo_221_32 roots_221 gzo_221_32 7:=lower_iso_b (d1:=dom_221) (r1:=roots_221) (T1:=gsh_221_32) [(dom_221,32)] (by decide +kernel) (lower_slice_b (T:=gsh_221_32) [(0x22222222000000002222222200000000222222220000000022222222,0,1),(0x33003300000000003300330000000000330033000000000033003300,0,8),(0x33333333000000003333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_249_4:=0x3030303030303030303030303030303030303030303030303030303030303030
def gzo_249_4:=0x3030303030303030303030303030303030303030303030303030302030302000
def gsh_249_4:=0x303030303030303030303030303030303030303030303030303030203030200
theorem lowS_zo_249_4_41:Lower true dzo_249_4 roots_249 gzo_249_4 7:=lower_iso_b (d1:=dom_249) (r1:=roots_249) (T1:=gsh_249_4) [(dom_249,4)] (by decide +kernel) (lower_slice_b (T:=gsh_249_4) [(0x303000003030000030300000303000003030000030300000303000003030000,0,16),(0x303030303030303000000000000000003030303030303030000000000000000,0,64),(0x303030303030303030303030303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_237_16:=0x3333000033330000333300003333000033330000333300003333000033330000
def gzo_237_16:=0x3333000033330000333300003333000033330000333300003332000032300000
def gsh_237_16:=0x333300003333000033330000333300003333000033330000333200003230
theorem lowS_zo_237_16_41:Lower true dzo_237_16 roots_237 gzo_237_16 7:=lower_iso_b (d1:=dom_237) (r1:=roots_237) (T1:=gsh_237_16) [(dom_237,16)] (by decide +kernel) (lower_slice_b (T:=gsh_237_16) [(0x303000003030000030300000303000003030000030300000303000003030,0,4),(0x333300003333000000000000000000003333000033330000000000000000,0,64),(0x333300003333000033330000333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_220_32:=0x1111111100000000111111110000000011111111000000001111111100000000
def gzo_220_32:=0x1111111100000000111111110000000011111110000000001110110000000000
def gsh_220_32:=0x11111111000000001111111100000000111111100000000011101100
theorem lowS_zo_220_32_84:Lower true dzo_220_32 roots_220 gzo_220_32 6:=lower_iso_b (d1:=dom_220) (r1:=roots_220) (T1:=gsh_220_32) [(dom_220,32)] (by decide +kernel) (lower_slice_b (T:=gsh_220_32) [(0x11001100000000001100110000000000110011000000000011001100,0,8),(0x11111111000000001111111100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
namespace S_253
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(4,20),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,40),(8,72),(8,136),(12,13),(12,28),(12,44),(12,76),(12,140),(16,20),(16,80),(16,144),(17,21),(17,25),(17,49),(17,81),(17,145),(24,25),(24,28),(24,56),(24,88),(24,152),(32,33),(32,40),(32,160),(36,37),(36,44),(36,52),(36,100),(36,164),(48,49),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,72),(64,80),(96,97),(96,100),(96,104),(96,112),(96,224),(128,129),(128,132),(128,136),(128,144),(128,160),(192,193),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
def xsM:=roots_253.map (·&&&dom_253)
def gM:=goal_253&&&dom_253
def NN:Nat→Nat
|8=>2
|9=>13
|10=>4
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xc6e030c01f
|9,0=>0x7fdfe7dad07c3e966fce6323855a7a4be4f4a3413b1b01c19b1c147185d700776
|10,0=>0xdfc1b3343a2609120610
|11,0=>0x1e31b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccccccc8888cccccccccccc8888cccccccccccc8888cccccccccccc8888303030302020202030303030202020203030303020202020303030302020202cccccc00cccccc00cccccc00cccccc00cccccc00cccccc00cccccc00cccccc03333332233333322333333223333332233333322333333223333332233333322cccccccc88888888cccccccc88888888cccccccc88888888cccccccc8888888b322332233223322332233223322332233223322332233223322332233223322cccccccccc00cc00cccccccccc00cc00cccccccccc00cc00cccccccccc00cc02222222222222222222222222222222222222222222222222222222222222222cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000003333000033330000333300003333000033330000333300003333000033330000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc03232323232323232323232323232323232323232323232323232323232323232c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c1111111111001100111111111100110011111111110011001111111111001100cccccccccccccccc0000000000000000cccccccccccccccc0000000000000003333333333333333333333333333333300000000000000000000000000000000
|0,1=>0x3333333330303030333333333030303033333333303030303333333330303030cccccccccc88cc88cccccccccc88cc88cccccccccc88cc88cccccccccc88cc89110111011101110111011101110111011101110111011101110111011101110ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc000000003330333000000000333033300000000033303330000000003330333000cc00cc00cc000000cc00cc00cc000000cc00cc00cc000000cc00cc00cc0003333333333330000333333333333000033333333333300003333333333330000
|_,_=>0
def sP:Nat→Nat
|0=>0x81cc51a020398a3408204acc51a020b1cc522020a9cc51a020398a34502039a652202049cca1a020398a34482059da628d0101cc51a22103ce628d0101cc51a1c101d8628d010256650c20398a418820
|1=>0x1cc51a020399451a02059cc51a0203b4c51a020
|_=>0
def sO:Nat→Nat→Nat
|8,0=>0x87008
|9,0=>0x7086886085885084884083882f92781f81780f8
|10,0=>0x908888808788
|11,0=>0x987
|_,_=>0
def wAt:=mkWire dB 23 254 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2a13a13153994a33953953a11a138d3a92a19a31951a11953954153ce1953a131581739982139958f3a16a13152a13953a14a33951a1
|_=>0
def oO:Nat→Nat→Nat
|8,0=>0xcc03
|9,0=>0x1e2709a26096250922408e2308a220862
|10,0=>0x8c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0x8a3ffc00ffd917cec0be73e1fb980f9c907ce40fe70b1fb810fdc077ee03be7015f3803f9c00ffe007f7001ff800fdc007ce00000
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>0x83
|9,0=>0x1211e683952f8b56c
|10,0=>0x329d0
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 21 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_189 10 roots_189 ops++addP pm 1 dom_125 10 roots_125 ops++addP pm 2 dom_249 9 roots_249 ops++addP pm 3 dom_213 6 roots_213 ops++addP pm 4 dzo_221_32 7 roots_221 ops++addP pm 5 dom_233 8 roots_233 ops++addP pm 6 dom_252 9 roots_252 ops++addP pm 7 dom_245 9 roots_245 ops++addP pm 8 dom_237 9 roots_237 ops++addP pm 9 dom_221 9 roots_221 ops++addP pm 10 dom_244 7 roots_244 ops++addP pm 11 dzo_212_32 5 roots_212 ops++addP pm 12 dom_241 6 roots_241 ops++addP pm 13 dzo_249_4 7 roots_249 ops++addP pm 14 dom_220 6 roots_220 ops++addP pm 15 dzo_213_32 6 roots_213 ops++addP pm 16 dom_212 5 roots_212 ops++addP pm 17 dom_229 6 roots_229 ops++addP pm 18 dzo_237_16 7 roots_237 ops++addP pm 19 dom_205 6 roots_205 ops++addP pm 20 dzo_220_32 6 roots_220 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_221_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_212_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_249_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_213_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_237_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_220_32_84 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_189 10 s (0,roots_189.map (·&&&dom_189)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_189 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_253==dom_253)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_253 gM v ys):RunD true dom_253 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_253 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 13 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 13 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 4 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 4 0 = true)
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
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
  · exact z10 i (Nat.zero_le i) hi
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
def isoMvS_254:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_247
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,18),(2,34),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,28),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,18),(16,20),(16,80),(16,144),(17,19),(17,21),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,160),(36,37),(36,38),(36,44),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,72),(64,80),(66,67),(66,70),(66,74),(66,82),(66,98),(66,194),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,130),(128,132),(128,136),(128,144),(128,160),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|11=>4
|12=>3
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|11,0=>0xfd2f7ecb3258c994ba7e
|12,0=>0xc33a38fd7c0eef7
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffff00000000000000000000ffffffffffff0000ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x765432108765432107b6543210a76543210c765432109765432108a65432109876543210
|_=>0
def sO:Nat→Nat→Nat
|11,0=>0x3924e45480a
|12,0=>0xde574a59
|13,0=>0x408
|_,_=>0
def wAt:=mkWire dB 13 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1d9615c581dd97b585765c5815d9
|_=>0
def oO:Nat→Nat→Nat
|11,0=>0x62422202
|12,0=>0xa19181
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x1ffe7fbff5fe7fc7f800
|_=>0
def pmB:Nat→Nat→Nat
|11,0=>0x5a6
|12,0=>0xab
|13,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 11 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_127 12 roots_127 ops++addP pm 2 dom_253 12 roots_253 ops++addP pm 3 dom_251 12 roots_251 ops++addP pm 4 dom_247 12 roots_247 ops++addP pm 5 dom_239 11 roots_239 ops++addP pm 6 dom_223 11 roots_223 ops++addP pm 7 dom_191 11 roots_191 ops++addP pm 8 dom_207 8 roots_207 ops++addP pm 9 dom_159 9 roots_159 ops++addP pm 10 dom_175 9 roots_175 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_175 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 4 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 3 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 3 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [7, 6] }, { op := GateOp.or, inputs := [0, 3] }, { op := GateOp.or, inputs := [4, 7] }, { op := GateOp.or, inputs := [4, 9] }, { op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [2, 11] }, { op := GateOp.or, inputs := [7, 1] }, { op := GateOp.or, inputs := [14, 9] }, { op := GateOp.and, inputs := [13, 8] }, { op := GateOp.and, inputs := [10, 12] }, { op := GateOp.and, inputs := [0, 3] }, { op := GateOp.and, inputs := [5, 15] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52318_aux

theorem PEqualNP.Outside.L_meta_52318 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52318_aux.main
