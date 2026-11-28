import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_51542_aux
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

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffeffeefefcaa00fffeffeefefcaa00fffeffeefefcaa00fffeffeefefcaa00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_82 : Nat := 0x500050000000000050005
def goal_82 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_82 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_84 : Nat := 0x1100110000000000110011
def goal_84 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_84 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffffcfcfffffcfcfcfc0000fcfc0000fffffcfcfffffcfcfcfc0000fcfc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffcfcfffffcfcfcfc0000fcfc0000fffffcfcfffffcfcfcfc0000fcfc0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffeeccffffeecceeccaa00eeccaa00ffffeeccffffeecceeccaa00eeccaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffaf0fffffaf0faf0aa00faf0aa00fffffaf0fffffaf0faf0aa00faf0aa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffcfcfffffcfcfcfc0000fcfc0000fffffcfcfffffcfcfcfc0000fcfc0000
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffefcfffffefcfefcaa00fefcaa00fffffefcfffffefcfefcaa00fefcaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_98 : Nat := 0x5000000050000000500000005
def goal_98 : Nat := 0xffffffffcccccccccccccccc00000000ffffffffcccccccccccccccc00000000
def roots_98 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xffffffffcccccccceeeeeeee00000000ffffffffcccccccceeeeeeee00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfffffffff0f0f0f0aaaaaaaa00000000fffffffff0f0f0f0aaaaaaaa00000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfffffffffcfcfcfccccccccc00000000fffffffffcfcfcfccccccccc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfffffffffcfcfcfceeeeeeee00000000fffffffffcfcfcfceeeeeeee00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffaa00aa00ffaaffaaaa00aa00ffffffffaa00aa00ffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffccccccccffccffcc00000000ffffffffccccccccffccffcc00000000
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffeecceeccffeeffeeaa00aa00ffffffffeecceeccffeeffeeaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffffffffaf0faf0ffaaffaaaa00aa00fffffffffaf0faf0ffaaffaaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffffffffcfcfcfcffccffcc00000000fffffffffcfcfcfcffccffcc00000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffffffffefcfefcffeeffeeaa00aa00fffffffffefcfefcffeeffeeaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffffffffff0000aaaaaaaa00000000ffffffffffff0000aaaaaaaa00000000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffffffcccccccccccccccc0000ffffffffffffcccccccccccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffffffcccceeeeeeeecccc0000ffffffffffffcccceeeeeeeecccc0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffffffffffff0f0f0f00000f0f00000fffffffffffff0f0f0f00000f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffffff0f0fafaaaaaf0f00000fffffffffffff0f0fafaaaaaf0f00000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffffffcfcfcfcccccfcfc0000fffffffffffffcfcfcfcccccfcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffffffcfcfefeeeeefcfc0000fffffffffffffcfcfefeeeeefcfc0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffffaa00ffaaffaaaa00aa00ffffffffffffaa00ffaaffaaaa00aa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffffccccffccffcccccc0000ffffffffffffccccffccffcccccc0000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffffeeccffeeffeeeeccaa00ffffffffffffeeccffeeffeeeeccaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffffffffff0f0fff0ff00f0f00000fffffffffffff0f0fff0ff00f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffffaf0fffaffaafaf0aa00fffffffffffffaf0fffaffaafaf0aa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffffcfcfffcffccfcfc0000fffffffffffffcfcfffcffccfcfc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffffefcfffeffeefefcaa00fffffffffffffefcfffeffeefefcaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaacccc0000cccc0000cccc0000cccc0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fcfc0000fcfc0000fcfc0000fcfc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffafafffffafafffffafafffffafafcfc0000fcfc0000fcfc0000fcfc0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffafaf0aa00faf0aa00faf0aa00faf0aa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_161 : Nat := 0x30000000300000000000000000000000300000003
def goal_161 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]

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

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffffaaaaffffffffffffaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffaaaaffffffffffffaaaaeeeeeeeecccc0000eeeeeeeecccc0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffffffafafffffffffffffafafafaaaaaf0f00000fafaaaaaf0f00000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fcfcccccfcfc0000fcfcccccfcfc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffafafffffffffffffafafefeeeeefcfc0000fefeeeeefcfc0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffffaaffffffffffffffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffff00ffffffffffffff00ffccffcccccc0000ffccffcccccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffaaffffffffffffffaaffeeffeeeeccaa00ffeeffeeeeccaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0fff0ff00f0f00000fff0ff00f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffffafffffffffffffffafffaffaafaf0aa00fffaffaafaf0aa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffafffffffffffffffafffeffeefefcaa00fffeffeefefcaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfafafafafafafafafafafafafafafafaf0f0f0f0f0f0f0f00000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfefefefefefefefefafafafafafafafafcfcfcfcfcfcfcfc0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaffff0000ffff00000000000000000000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffccccffffccccffff0000ffff0000ffffccccffffcccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffaaaaffffaaaaffffccccffffcccccccc0000cccc0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffafafffffafafffffafafffffafafffff0f0fffff0f0f0f00000f0f00000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfffff0f0fffff0f0fffffcfcfffffcfcfcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefffffafafffffafafffffcfcfffffcfcfcfc0000fcfc0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffffaaffffffaaffffeeccffffeecceeccaa00eeccaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffffffafffffffafffffefcfffffefcfefcaa00fefcaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffccccccccffffffff00000000ffffffffcccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeffffffffaaaaaaaaffffffffcccccccceeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffafafafafffffffffafafafafffffffff0f0f0f0aaaaaaaa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfffffffff0f0f0f0fffffffffcfcfcfccccccccc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefefffffffffafafafafffffffffcfcfcfceeeeeeee00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffffaaffaaffffffffeecceeccffeeffeeaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffffffffffafffafffffffffefcfefcffeeffeeaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffaaaaffffffffffffaaaaffffffffffff0000aaaaaaaa00000000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffccccffffffffffff0000ffffffffffffcccccccccccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffffffffffaaaaffffffffffffcccceeeeeeeecccc0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fffffffffffff0f0f0f00000f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffafafffffffffffffafafffffffffffff0f0fafaaaaaf0f00000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffffffffff0f0fffffffffffffcfcfcfcccccfcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffffffffffafafffffffffffffcfcfefeeeeefcfc0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffffffffffaaffffffffffffaa00ffaaffaaaa00aa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffffffffff00ffffffffffffccccffccffcccccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffffffaaffffffffffffeeccffeeffeeeeccaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffffffffffafffffffffffffaf0fffaffaafaf0aa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffffffffff0fffffffffffffcfcfffcffccfcfc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffffffffffafffffffffffffefcfffeffeefefcaa00
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
def isoMvS_98:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_98:Lower true dom_98 roots_98 goal_98 4:=lower_iso_b isoMvS_98 (by decide +kernel) lowS_41
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_41
def isoMvS_161:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_161:Lower true dom_161 roots_161 goal_161 4:=lower_iso_b isoMvS_161 (by decide +kernel) lowS_41
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
|0=>0x14815240915495514052149550405
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
def isoMvS_99:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_43
def isoMvS_101:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 4:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_51
def isoMvS_102:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 5:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_43
def isoMvS_105:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_43
def isoMvS_106:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_43
def isoMvS_113:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 4:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_51
def isoMvS_114:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_86
def isoMvS_116:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_43
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 4:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_51
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_43
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 4:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_51
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_43
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_43
def isoMvS_197:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 4:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_51
def isoMvS_198:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 4:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_51
def isoMvS_209:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 4:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_51
def isoMvS_210:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_43
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_86
def isoMvS_226:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_43
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
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_slice_b [(0xaa000000aa000000aa000000aa,32,33)] (by decide +kernel) lowS_102
namespace S_107
def pG:List (Nat×Nat):=[(1,9),(1,33),(2,34),(2,66),(3,11),(3,35),(3,67),(8,9),(8,40),(10,11),(10,42),(10,74),(32,33),(32,34),(32,40),(32,96),(64,66),(64,96),(65,67),(65,73),(65,97),(72,73),(72,74),(72,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_107.map (·&&&dom_107)
def gM:=goal_107&&&dom_107
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xe2d1
|4,0=>0x4eba71f4b81033305105
|5,0=>0x7c22774f80492ce3856a23a040da900ca210c32408ad601d56
|6,0=>0xb40cf7ad9f734c404510
|7,0=>0xb40cf
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0c00000f0c00000f0c00000f0c000000000000000050500000000f0f00000f0f0000000f00000000e0e00000e0e00000e0e00000e0ef0f00000e0e00000f0f00000e0ef0f00000f0000000f0f00000f00f0c0000000000000f0c0000000000f0000000f0000000f0000000af0f0000000000000f0f00000000f0000000f0000000f0000000f000000000000000000d0d00000c0ca0a00000a0a00000a0a00000a0af0f00000a0a00000f0f00000a0af0f00000f0000000f0a00000f00c0c00000c0c00000c0c00000c0cf0f00000f0f0000000000000000
|0,1=>0xf0f00000000f0f00000f0f00000f0000000f00f0f0000000000000f000000000000f0000000a0000000f0000000a00000000f0c0000000000000f0c505000000000000050500000000303000002020000030300000202f0f00000c0c00000f0f00000c0c
|_,_=>0
def sP:Nat→Nat
|0=>0x1cc1200e6090103982401ee6090077982401cd5090070928019c24a00e60926019cc1900e60922081de6200e6091c03982468167304803882402921200e1220073142418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b48584cf19b330654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 24 108 0xfffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3853830993d819b39138539b3b1
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x51003200000021001101
|6,0=>0x817161
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0xffde5e3091840c0
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x6040105023
|6,0=>0x7889
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_106 5 roots_106 ops++addP pm 1 dom_98 4 roots_98 ops++addP pm 2 dom_41 4 roots_41 ops++addP pm 3 dom_99 5 roots_99 ops++addP pm 4 dom_43 5 roots_43 ops++addP pm 5 dom_105 5 roots_105 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_107 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_105 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_106 5 s (0,roots_106.map (·&&&dom_106)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_107 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_106 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_107==dom_107)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_107 gM v ys):RunD true dom_107 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_107 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_107 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_107 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_107 roots_107 goal_107 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_107
theorem lowS_107:Lower true dom_107 roots_107 goal_107 8:=S_107.noCircuit
def dzo_114_1:=0xa000a000a000a000a000a000a000a
def gzo_114_1:=0xa000a000a0008000a000a00080000
def gsh_114_1:=0x50005000500040005000500040000
theorem lowS_zo_114_1_82:Lower true dzo_114_1 roots_114 gzo_114_1 5:=lower_iso_b (d1:=dom_114) (r1:=roots_114) (T1:=gsh_114_1) [(dom_114,1)] (by decide +kernel) (lower_slice_b (T:=gsh_114_1) [(0x50005000000000005000500000000,0,32)] (by decide +kernel) lowS_82)
namespace S_115
def pG:List (Nat×Nat):=[(1,33),(2,18),(2,34),(2,66),(3,19),(3,35),(3,67),(16,18),(16,80),(17,19),(17,49),(17,81),(32,33),(32,34),(32,96),(48,49),(48,50),(48,112),(64,66),(64,80),(64,96),(65,67),(65,81),(65,97)]
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
|4,0=>0xc3387
|5,0=>0xf31a
|6,0=>0x88c8c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0000000f0000000f0000000f0000f000f000f000f000c000c000c000cf000f00000000000f000f00000000c000c000c000c000c000c000c000ca000a000a000a000a000a000a000a0000f0000000f0000000c0000000cf000f000f000f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x99a135684688
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
addP pm 0 dom_114 5 roots_114 ops++addP pm 1 dom_113 4 roots_113 ops++addP pm 2 dzo_114_1 5 roots_114 ops++addP pm 3 dom_99 5 roots_99 ops++addP pm 4 dom_51 4 roots_51 ops++addP pm 5 dom_82 4 roots_82 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_115 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_114_1_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_82 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_114 5 s (0,roots_114.map (·&&&dom_114)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_115 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_114 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]]
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
namespace S_118
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,66),(4,20),(4,68),(6,22),(6,38),(6,70),(16,18),(16,20),(16,80),(32,34),(32,96),(36,38),(36,52),(36,100),(48,50),(48,52),(48,112),(64,66),(64,68),(64,80),(64,96)]
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
addP pm 0 dom_116 5 roots_116 ops++addP pm 1 dom_114 5 roots_114 ops++addP pm 2 dom_102 5 roots_102 ops++addP pm 3 dom_86 5 roots_86 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_118 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_86 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_116 5 s (0,roots_116.map (·&&&dom_116)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_118 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_116 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
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
theorem lowS_179:Lower true dom_179 roots_179 goal_179 6:=lower_slice_b [(0xc000c000c000c0000000000000000000c000c000c000c,16,18)] (by decide +kernel) lowS_177
theorem lowS_242:Lower true dom_242 roots_242 goal_242 6:=lower_slice_b [(0x5000000050000000500000005000000050000000500000005000000050000,2,18)] (by decide +kernel) lowS_226
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 6:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_61
def isoMvS_93:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 6:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_61
def isoMvS_109:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 7:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_59
def isoMvS_110:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_103
def isoMvS_117:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 7:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_59
def isoMvS_121:List (Nat×Nat):=[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 7:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_59
def isoMvS_122:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_115
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 7:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_59
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_103
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 8:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_107
def isoMvS_167:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_103
def isoMvS_173:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_171
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 8:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_107
def isoMvS_182:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 6:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_179
def isoMvS_185:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 8:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_171
def isoMvS_186:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 6:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_179
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 8:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_107
def isoMvS_199:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 5:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_55
def isoMvS_211:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 7:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_59
def isoMvS_213:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 7:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_115
def isoMvS_214:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 7:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_118
def isoMvS_227:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 8:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_107
def isoMvS_229:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 6:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_179
def isoMvS_230:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 6:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_179
def isoMvS_241:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 6:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_179
def isoMvS_244:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 6:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_242
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xf0f0f0f0f0f0f0f0,16,20)] (by decide +kernel) lowS_59
theorem lowS_95:Lower true dom_95 roots_95 goal_95 7:=lower_slice_b [(0xaaaaaaaa00000000aaaaaaaa,8,9),(0xff00ff0000000000ff00ff00,1,9)] (by decide +kernel) lowS_86
theorem lowS_111:Lower true dom_111 roots_111 goal_111 9:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f0,64,68)] (by decide +kernel) lowS_107
def dzo_86_1:=0xaa00aa0000000000aa00aa
def gzo_86_1:=0xaa00a80000000000a80000
def gsh_86_1:=0x5500540000000000540000
theorem lowS_zo_86_1_86:Lower true dzo_86_1 roots_86 gzo_86_1 5:=lower_iso_b (d1:=dom_86) (r1:=roots_86) (T1:=gsh_86_1) [(dom_86,1)] (by decide +kernel) (lower_slice_b (T:=gsh_86_1) [] (by decide +kernel) lowS_86)
def dzo_118_1:=0xaa00aa00aa00aa00aa00aa00aa00aa
def gzo_118_1:=0xaa00aa00aa00a800aa00aa00a80000
def gsh_118_1:=0x550055005500540055005500540000
theorem lowS_zo_118_1_86:Lower true dzo_118_1 roots_118 gzo_118_1 6:=lower_iso_b (d1:=dom_118) (r1:=roots_118) (T1:=gsh_118_1) [(dom_118,1)] (by decide +kernel) (lower_slice_b (T:=gsh_118_1) [(0x550055000000000055005500000000,0,32)] (by decide +kernel) lowS_86)
namespace S_119
def pG:List (Nat×Nat):=[(1,33),(2,18),(2,34),(2,66),(3,19),(3,35),(3,67),(4,20),(4,68),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,23),(7,39),(7,71),(16,18),(16,20),(16,80),(17,19),(17,21),(17,49),(17,81),(32,33),(32,34),(32,96),(36,37),(36,38),(36,52),(36,100),(48,49),(48,50),(48,52),(48,112),(64,66),(64,68),(64,80),(64,96),(65,67),(65,69),(65,81),(65,97)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_119.map (·&&&dom_119)
def gM:=goal_119&&&dom_119
def NN:Nat→Nat
|4=>3
|5=>10
|6=>17
|7=>7
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x9991e69d932ef8d
|5,0=>0xac77f9f53794c388dd538542b81527572904a62530a9716b96
|6,0=>0xec6d6de44bd8383c23d5b1c91a8e48a4e71a0b88873f760cc153a794872e3875a361f73222e2b7ce0b8f3
|7,0=>0xe8d9fde33bd6a41d10f384cb0721ca5d38a
|8,0=>0xdaa04
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000f000f000f0000000f00005500ff000000ff00550055000000003300330033003300330033003300000f000f000f000f000f000f000f00000f0000000f000f000f0000000f0000ff00ff00ff00ff0000000000000000ff00ff00ff00000000000000000000ff00ff00ff00ff00ff00ff00000000ff000000ff000000ff000000ff0000ff00ff00ff00f000f000f000f000f0cc00cc00cc00cc00cc00cc00cc00ccff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff000000ff0000f000f000f000f000f000f000f000f0ff00ff00ff00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa
|0,1=>0xff000000ff000000ff0000000000000000ff00ff0000000000ff0000aa00ff00aa00ff00aa00aa00aa00aa00000000ff00ff0000000000000000ff000000ff00ff00ff000000ff0000ff00ff00ff00ff00550055000000000000000000000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00000000ff000000ff0000000000000000ff00ff000000ff00ff00ff00000000ff00ff00ff000000ff00ff00ff0000000000000000ff0000000000000000550055000000000055005500000000ff00ff00ff00ff00aa00aa00aa00aa
|_,_=>0
def sP:Nat→Nat
|0=>0x1162a20ce22c15621c4502a84388a054c831140a21c450292419ca07a8871140a910e58bd443960f510e22b9443880d510e628148388a0490e50314438820510e502d44188a04a0e2080833140418820
|1=>0x21c45028871140aa90e22c544388a0568871160a410e22815321c4502883388a0510e22c55521c4507544388a0e28871176a264e2281443940f510e22e15341c4502ae4388a051067
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa5055005
|5,0=>0x4563f63963362d62762161b61560f6
|6,0=>0xb87b17aa7a469d79769168a78377c77576e76776075975274b7
|7,0=>0xe77e16da7d46cd7c67bf7
|8,0=>0xee6
|_,_=>0
def wAt:=mkWire dB 30 120 0xffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3aa20322a02922921d3a92033aa20e3a90553aa3e922a18b3a98a920322921d9ab21d3a92030293a99a921d2553aa3a921d9a821d18b3a99aa21d
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1e2001c2689825894248902388c2288821884208802
|7,0=>0x261946418c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xffbfb77760553f3729221b1109070200
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0xb03a14a7366532963
|7,0=>0xdcefe9d
|8,0=>8
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_118 7 roots_118 ops++addP pm 1 dom_115 7 roots_115 ops++addP pm 2 dom_86 5 roots_86 ops++addP pm 3 dzo_86_1 5 roots_86 ops++addP pm 4 dom_117 7 roots_117 ops++addP pm 5 dom_103 6 roots_103 ops++addP pm 6 dzo_118_1 6 roots_118 ops++addP pm 7 dom_55 5 roots_55 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_119 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_86_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_118_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_55 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_118 7 s (0,roots_118.map (·&&&dom_118)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_119 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_118 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_119 gM v ys):RunD true dom_119 gM v (ori ys):=h
def Z (s:Nat):=barP dom_119 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
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
def dzo_41_16:=0x303000003030000
def gzo_41_16:=0x302000002000000
def gsh_41_16:=0x30200000200
theorem lowS_zo_41_16_41:Lower true dzo_41_16 roots_41 gzo_41_16 4:=lower_iso_b (d1:=dom_41) (r1:=roots_41) (T1:=gsh_41_16) [(dom_41,16)] (by decide +kernel) (lower_slice_b (T:=gsh_41_16) [] (by decide +kernel) lowS_41)
def dzo_105_16:=0x3030000030300000303000003030000
def gzo_105_16:=0x3030000030300000302000002000000
def gsh_105_16:=0x303000003030000030200000200
theorem lowS_zo_105_16_41:Lower true dzo_105_16 roots_105 gzo_105_16 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_16) [(dom_105,16)] (by decide +kernel) (lower_slice_b (T:=gsh_105_16) [(0x303000003030000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_90_1:=0xa0a0a0a000000000a0a0a0a
def gzo_90_1:=0xa0a0a08000000000a080a00
def gsh_90_1:=0x50505040000000005040500
theorem lowS_zo_90_1_82:Lower true dzo_90_1 roots_90 gzo_90_1 5:=lower_iso_b (d1:=dom_90) (r1:=roots_90) (T1:=gsh_90_1) [(dom_90,1)] (by decide +kernel) (lower_slice_b (T:=gsh_90_1) [(0x50005000000000005000500,0,8)] (by decide +kernel) lowS_82)
def dzo_83_8:=0xf000f00000000000f000f00
def gzo_83_8:=0xf000e00000000000e000a00
def gsh_83_8:=0xf000e00000000000e000a
theorem lowS_zo_83_8_82:Lower true dzo_83_8 roots_83 gzo_83_8 5:=lower_iso_b (d1:=dom_83) (r1:=roots_83) (T1:=gsh_83_8) [(dom_83,8)] (by decide +kernel) (lower_slice_b (T:=gsh_83_8) [(0xa000a00000000000a000a,0,1)] (by decide +kernel) lowS_82)
def dzo_122_1:=0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def gzo_122_1:=0xa0a0a0a0a0a0a080a0a0a0a0a080a00
def gsh_122_1:=0x5050505050505040505050505040500
theorem lowS_zo_122_1_82:Lower true dzo_122_1 roots_122 gzo_122_1 6:=lower_iso_b (d1:=dom_122) (r1:=roots_122) (T1:=gsh_122_1) [(dom_122,1)] (by decide +kernel) (lower_slice_b (T:=gsh_122_1) [(0x5000500050005000500050005000500,0,8),(0x5050505000000000505050500000000,0,32)] (by decide +kernel) lowS_82)
def dzo_107_16:=0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16:=0xf0f00000f0f00000f0e00000e0c0000
def gsh_107_16:=0xf0f00000f0f00000f0e00000e0c
theorem lowS_zo_107_16_41:Lower true dzo_107_16 roots_107 gzo_107_16 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_16) [(dom_107,16)] (by decide +kernel) (lower_slice_b (T:=gsh_107_16) [(0xc0c00000c0c00000c0c00000c0c,0,2),(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_115_8:=0xf000f000f000f000f000f000f000f00
def gzo_115_8:=0xf000f000f000e000f000f000e000a00
def gsh_115_8:=0xf000f000f000e000f000f000e000a
theorem lowS_zo_115_8_82:Lower true dzo_115_8 roots_115 gzo_115_8 6:=lower_iso_b (d1:=dom_115) (r1:=roots_115) (T1:=gsh_115_8) [(dom_115,8)] (by decide +kernel) (lower_slice_b (T:=gsh_115_8) [(0xa000a000a000a000a000a000a000a,0,1),(0xf000f00000000000f000f00000000,0,32)] (by decide +kernel) lowS_82)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,33),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,40),(10,11),(10,26),(10,42),(10,74),(16,18),(16,80),(17,19),(17,25),(17,49),(17,81),(24,25),(24,26),(24,56),(24,88),(32,33),(32,34),(32,40),(32,96),(48,49),(48,50),(48,56),(48,112),(64,66),(64,80),(64,96),(65,67),(65,73),(65,81),(65,97),(72,73),(72,74),(72,88),(72,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|5=>4
|6=>15
|7=>24
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x4edfa43e2138fd11f4ee
|6,0=>0xbf80ab81618e642823cf775e273010531e74f5bf4ea6b499173543a352da33abc0fc1d0d0a1
|7,0=>0xe7fb0a7d1b872ff80af17b99d768f3756366b8185d3245b4b1599c34f929449a9388c92e5222df802a039205631d0481ac5e1861b150fc0cc9507550
|8,0=>0xe3f54cdd92ad2d25459947c683cae432d0c07721
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f0f0f0f0f0000000000f000f00000000000f000f00000000c0f0c0f0c0c0c0c0c0f0c0f0c0c0c0cf0f0f0f0f0f0f0f0c0c0c0c0c0c0c0ca0a0a0a0a000a000a0a0a0a0a000a0000f000f000a000a000f000f000a000a0000f0f00000f0f00000c0c00000c0c0000000000000000f0f0f0f0c0c0c0cf0f00000f0f00000f0f00000f0f00003030303030303030303030300000000f0f0f0f000000000f0f0f0f00000000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00f0f0f00000f0f000f0c0f00000c0cf0f0f0f0f0f0f0f0000000000000000
|0,1=>0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0000000000000000e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0f0c0f0c0f0c0f0cf0f0f0f0f0f00000f0f0f0f0f0f000000000000000000003030303000000005050505000000000505050500000000f0f0f0f0f0f0f0f0d0d0d0d0c0c0c0cf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0f000f000f0f0f0f0f000f005050505050005000505050505000500f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0cf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af000f000a000a000f000f000a000a000000000000000000c0f0c0f0c0c0c0cf0f0f0f00000f0f0f0f0f0f00000c0cf0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c
|0,2=>0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f05050f0f00000f0f05050f0f0000f0f0f0f0f0f0f0f03030303000000000000000000000000f0f0f0f000000003030303000000000303030300000000f0f03030f0f00000f0f03030f0f0000
|_,_=>0
def sP:Nat→Nat
|0=>0x153c710c0941440c224054814710c08510308e24054f14710c0851c46430801581030890051c430358054f1c40860101471021801474cc0c20051c448308044510308020f1471030851c434c0801440cb24014308a2402051c40861440c2040
|1=>0x8401471035801471030a301c5440c20051d30c201588710308054814710308016010308054f14710308014710c0c26803c51c43030851c478308040f1471030801477440c20051c434308014710308601c5451030805051c430308014710309b
|2=>0x51c40c201c1440c20051d81030801471030a10051c40c26801471039420051c43030805051c40c200f1471030801440c224014760430308016410308054f1c40c20101471030807040c2
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x9303180cc006
|6,0=>0x1e58e4e6b7323975cace4f7243905c74e33716389983ee187
|7,0=>0x903462224d0b7823bf99f0cf1775b3959bced686833221810b97593aaa146e9c74aba39d0d07f7
|8,0=>0xabb541e92f4279dbcd1e5af267
|9,0=>0x15d6
|_,_=>0
def wAt:=mkWire dB 38 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x142450d140d5031434785143c50d1404301142c301140407e0834f0d1404c110c04e0d144cf0f140451d143430114245330c0450d0c045011cc8301540c50d1cc8301144c50d0c0450131a4301142c7320c0570b0c045113c3c5013c34f0f14054100c045090c050033c345013834513
|1=>0x51d102450f142c2010c0450914047320c043011024769142c50d1404f0d140451d143d70b1446101143c51d1435410
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x80cf11c232658c999121c63084986300014411802
|7,0=>0xa253ca694b29251ca29432824fc9e93b2724dc9a9332624bc9692b25249c929232
|8,0=>0xb43646c0d71ac3546a0d31
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x5a6a09c540bbf8151d0200003cd406808078700efe01ddc03ba805f700b2e015dc028a80400007ce00f9401b2803070060c00c0000c380106002020020c000c00007000080000c000100000
|1=>0x4371f82efec34d512ab90d0112efe1bcd4268082f35
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40
|6,0=>0xe40814c0901ca19901b103
|7,0=>0x724a0d52381675a3cb74c60f7c995e497856
|8,0=>0x9e655e7d3895
|9,0=>0x11
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_107 8 roots_107 ops++addP pm 1 dzo_41_16 4 roots_41 ops++addP pm 2 dom_59 7 roots_59 ops++addP pm 3 dzo_105_16 5 roots_105 ops++addP pm 4 dom_115 7 roots_115 ops++addP pm 5 dzo_90_1 5 roots_90 ops++addP pm 6 dzo_83_8 5 roots_83 ops++addP pm 7 dom_41 4 roots_41 ops++addP pm 8 dom_121 7 roots_121 ops++addP pm 9 dom_91 6 roots_91 ops++addP pm 10 dom_122 7 roots_122 ops++addP pm 11 dzo_122_1 6 roots_122 ops++addP pm 12 dzo_107_16 6 roots_107 ops++addP pm 13 dzo_114_1 5 roots_114 ops++addP pm 14 dom_82 4 roots_82 ops++addP pm 15 dom_105 5 roots_105 ops++addP pm 16 dom_114 5 roots_114 ops++addP pm 17 dzo_115_8 6 roots_115 ops++addP pm 18 dzo_43_16 5 roots_43 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_41_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_105_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_90_1_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_83_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_122_1_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_107_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_114_1_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_115_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_43_16_41 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_107 8 s (0,roots_107.map (·&&&dom_107)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_107 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 15 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
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
def dzo_124_1:=0x22222222222222222222222222222222
def gzo_124_1:=0x22222222222222202222222222202200
def gsh_124_1:=0x11111111111111101111111111101100
theorem lowS_zo_124_1_84:Lower true dzo_124_1 roots_124 gzo_124_1 6:=lower_iso_b (d1:=dom_124) (r1:=roots_124) (T1:=gsh_124_1) [(dom_124,1)] (by decide +kernel) (lower_slice_b (T:=gsh_124_1) [(0x11001100110011001100110011001100,0,8),(0x11111111000000001111111100000000,0,32)] (by decide +kernel) lowS_84)
def dzo_92_1:=0x222222220000000022222222
def gzo_92_1:=0x222222200000000022202200
def gsh_92_1:=0x111111100000000011101100
theorem lowS_zo_92_1_84:Lower true dzo_92_1 roots_92 gzo_92_1 5:=lower_iso_b (d1:=dom_92) (r1:=roots_92) (T1:=gsh_92_1) [(dom_92,1)] (by decide +kernel) (lower_slice_b (T:=gsh_92_1) [(0x110011000000000011001100,0,8)] (by decide +kernel) lowS_84)
def dzo_57_4:=0x3030303030303030
def gzo_57_4:=0x3030302030302000
def gsh_57_4:=0x303030203030200
theorem lowS_zo_57_4_41:Lower true dzo_57_4 roots_57 gzo_57_4 5:=lower_iso_b (d1:=dom_57) (r1:=roots_57) (T1:=gsh_57_4) [(dom_57,4)] (by decide +kernel) (lower_slice_b (T:=gsh_57_4) [(0x303000003030000,0,16)] (by decide +kernel) lowS_41)
def dzo_85_8:=0x330033000000000033003300
def gzo_85_8:=0x330032000000000032002200
def gsh_85_8:=0x3300320000000000320022
theorem lowS_zo_85_8_84:Lower true dzo_85_8 roots_85 gzo_85_8 5:=lower_iso_b (d1:=dom_85) (r1:=roots_85) (T1:=gsh_85_8) [(dom_85,8)] (by decide +kernel) (lower_slice_b (T:=gsh_85_8) [(0x2200220000000000220022,0,1)] (by decide +kernel) lowS_84)
def dzo_45_16:=0x3333000033330000
def gzo_45_16:=0x3332000032300000
def gsh_45_16:=0x333200003230
theorem lowS_zo_45_16_41:Lower true dzo_45_16 roots_45 gzo_45_16 5:=lower_iso_b (d1:=dom_45) (r1:=roots_45) (T1:=gsh_45_16) [(dom_45,16)] (by decide +kernel) (lower_slice_b (T:=gsh_45_16) [(0x303000003030,0,4)] (by decide +kernel) lowS_41)
def dzo_121_4:=0x30303030303030303030303030303030
def gzo_121_4:=0x30303030303030303030302030302000
def gsh_121_4:=0x3030303030303030303030203030200
theorem lowS_zo_121_4_41:Lower true dzo_121_4 roots_121 gzo_121_4 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_4) [(dom_121,4)] (by decide +kernel) (lower_slice_b (T:=gsh_121_4) [(0x3030000030300000303000003030000,0,16),(0x3030303030303030000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_116_1:=0x220022002200220022002200220022
def gzo_116_1:=0x220022002200200022002200200000
def gsh_116_1:=0x110011001100100011001100100000
theorem lowS_zo_116_1_84:Lower true dzo_116_1 roots_116 gzo_116_1 5:=lower_iso_b (d1:=dom_116) (r1:=roots_116) (T1:=gsh_116_1) [(dom_116,1)] (by decide +kernel) (lower_slice_b (T:=gsh_116_1) [(0x110011000000000011001100000000,0,32)] (by decide +kernel) lowS_84)
def dzo_105_4:=0x3030000030300000303000003030
def gzo_105_4:=0x3030000030300000302000002000
def gsh_105_4:=0x303000003030000030200000200
theorem lowS_zo_105_4_41:Lower true dzo_105_4 roots_105 gzo_105_4 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_4) [(dom_105,4)] (by decide +kernel) (lower_slice_b (T:=gsh_105_4) [(0x303000003030000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_109_16:=0x33330000333300003333000033330000
def gzo_109_16:=0x33330000333300003332000032300000
def gsh_109_16:=0x3333000033330000333200003230
theorem lowS_zo_109_16_41:Lower true dzo_109_16 roots_109 gzo_109_16 6:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_16) [(dom_109,16)] (by decide +kernel) (lower_slice_b (T:=gsh_109_16) [(0x3030000030300000303000003030,0,4),(0x3333000033330000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_117_8:=0x33003300330033003300330033003300
def gzo_117_8:=0x33003300330032003300330032002200
def gsh_117_8:=0x330033003300320033003300320022
theorem lowS_zo_117_8_84:Lower true dzo_117_8 roots_117 gzo_117_8 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_8) [(dom_117,8)] (by decide +kernel) (lower_slice_b (T:=gsh_117_8) [(0x220022002200220022002200220022,0,1),(0x330033000000000033003300000000,0,32)] (by decide +kernel) lowS_84)
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,33),(4,20),(4,68),(5,13),(5,21),(5,37),(5,69),(8,9),(8,40),(12,13),(12,28),(12,44),(12,76),(16,20),(16,80),(17,21),(17,25),(17,49),(17,81),(24,25),(24,28),(24,56),(24,88),(32,33),(32,40),(32,96),(36,37),(36,44),(36,52),(36,100),(48,49),(48,52),(48,56),(48,112),(64,68),(64,80),(64,96),(65,69),(65,73),(65,81),(65,97),(72,73),(72,76),(72,88),(72,104)]
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
|5,0=>0x5fe035d09911ca6
|6,0=>0xe5c58db4ae4cdbb446b93cbb937d1f30f8917350016f9
|7,0=>0x74b3a70b7d5cbc75c4af43d003efe83e9c23e6342bd652a6d01f1a212a730dd3f0bc0f08ea508a8d02f71002ab
|8,0=>0x95de87f2e47749274b3a6951e642d24624f1d4c00f7ba067c2
|9,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccc88888888cccccccc8888888b3223322332233223322332233223322cccccccccc00cc00cccccccccc00cc033333333333333333333000033330000cc00cc0088008800cc00cc008800880333300003333000030300000303000000c0c0c0c0c0c0c0c0c0c00000c0c00033330000333300003333000033330000cc00cc00cc00cc00cc00cc00cc00cc030303030303030303030000030300000444444444400440044444444440044033333333000000003333333300000000cccccc00cccc8800ccc0cc00c8c0880303030303030303030303030303030308888888888888888888888888888888b3333333333333330000000000000000
|0,1=>0xcc00cc0000000000cc00cc00000001111111100000000111111110000000088888888cccccccc0000000000000003333333303030303333333330000000000000000cccc0000cccc0000cccc000232323232323232322222222222222220000cccc000000000000cccc000000030300000303030303030000030303030cccccccc000000000000000000000003333333333333333333333330000000000000000cccccccccccccccc0000000111133330000333311111111000000000c0c0c0c0c0c0c0c00000000000000000003333000033330000000000000000ccccc0c0ccccc0c0ccccc0c0ccccc0c33333333333333333030303030303030
|0,2=>0x33333333333300003333333333330000ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc333333332222222222222222222222220000000000000000cccccccc0000000000000003333333300000000000000000c0c0c0c000000000c0c0c0c000000033330303333300003333030333330000
|_,_=>0
def sP:Nat→Nat
|0=>0x1c20403c420708101211b1c20403c44481c20405881c20571081c26810042076010152070815952070811081c20540042070850131082c20404844482c20403c41c228100420e1c124010c2070850042c22810042071490042071850040c2040
|1=>0x5842070810261081c20401081c20408842251c20401081c205900f1081c20401081c20404d61081c204011120e1c20401081c29008c81c20623c42074020401112070817801201c20401082c20401081c205f0131081c204074420704901c108
|2=>0x1081c20401081c20405c420708100420e1c2040
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x45816c056
|6,0=>0x4e5243105c74e337163895c3ce177
|7,0=>0x190ec085d32d19590a484f3261921089741b1f1ce906e63341818b2e536
|8,0=>0x21af076803be5de4eeb7723b75dacecf7
|9,0=>0x1146
|_,_=>0
def wAt:=mkWire dB 39 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x10007051004811100821d2048111080848910088091c1415d10004031008201044480904488850848f1c044441f080807b0448c0b200444d0808802044485f00408090444400100414d0808267204965f1000401597c4001004d071c448023c701113c701112100201302c80104d8711
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1031a6000590830c410811002
|7,0=>0x1a9332624bc9692b25249c9292324247c8e91b23245c8a9132
|8,0=>0x1f88007c2f45e0bb1742e45c0b71
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0xa00bf1c3d521eea427d220262484448098645f0a8ea11b74232e84455087ba0a97c13ba826ff030260301c03fe806fd00caa0194001fe802dd004be007f4002a800100000e00010000080000
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x64808320422
|7,0=>0x1bb831fae1d51bd9d5ca708
|8,0=>0x1abfb7adf4e54
|9,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_124 7 roots_124 ops++addP pm 1 dzo_124_1 6 roots_124 ops++addP pm 2 dom_109 7 roots_109 ops++addP pm 3 dzo_92_1 5 roots_92 ops++addP pm 4 dom_121 7 roots_121 ops++addP pm 5 dzo_57_4 5 roots_57 ops++addP pm 6 dom_117 7 roots_117 ops++addP pm 7 dzo_85_8 5 roots_85 ops++addP pm 8 dzo_45_16 5 roots_45 ops++addP pm 9 dom_93 6 roots_93 ops++addP pm 10 dom_61 6 roots_61 ops++addP pm 11 dom_84 4 roots_84 ops++addP pm 12 dzo_121_4 6 roots_121 ops++addP pm 13 dzo_116_1 5 roots_116 ops++addP pm 14 dzo_105_4 5 roots_105 ops++addP pm 15 dom_105 5 roots_105 ops++addP pm 16 dom_116 5 roots_116 ops++addP pm 17 dzo_109_16 6 roots_109 ops++addP pm 18 dzo_117_8 6 roots_117 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_124_1_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_92_1_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_57_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_85_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_45_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_121_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_116_1_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_105_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_109_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_117_8_84 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_124 7 s (0,roots_124.map (·&&&dom_124)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_124 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
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
theorem lowS_183:Lower true dom_183 roots_183 goal_183 9:=lower_slice_b [(0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_181
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_slice_b [(0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c,16,18)] (by decide +kernel) lowS_185
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
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=lower_slice_b [(0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000,2,18)] (by decide +kernel) lowS_227
namespace S_246
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,66),(4,20),(4,68),(4,132),(6,22),(6,38),(6,70),(6,134),(16,18),(16,20),(16,80),(16,144),(32,34),(32,96),(32,160),(36,38),(36,52),(36,100),(36,164),(48,50),(48,52),(48,112),(48,176),(64,66),(64,68),(64,80),(64,96),(128,132),(128,144),(128,160),(130,134),(130,146),(130,162),(130,194),(192,194),(192,196),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_246.map (·&&&dom_246)
def gM:=goal_246&&&dom_246
def NN:Nat→Nat
|5=>3
|6=>5
|7=>4
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x6ea63335e720668
|6,0=>0xc9ed579ceb26df9145b004fd7
|7,0=>0x6eb081dd3717b541122d
|8,0=>0x3f43d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaa00aa00aa00aa00a000a000a000a000aa00aa00aa00aa00a000a000a000a150015001500150015001500150015001500150015001500150015001500152a8022002a8022002a8022002a8022002a8022002a8022002a8022002a802255005500550055005500550055005500550055005500550050005000500050aa00aa00aa00aa00aa00aa00aa000000aa00aa00aa00aa00aa00aa00aa000154015400000000015401540000000001540154000000000154015400000002a8000002a8000002a8000002a8000002a8000002a8000002a8000002a800005000500050005000500050005000500050005000500050005000000050000aa00aa00aa00aa00aa000000aa000000aa00aa00aa00aa00aa000000aa000154015401540154015401540154015400000000000000000000000000000002a802a802a8000002a802a802a8000002a802a802a8000002a802a802a800055005500550055005500550055005500550055005500550055000000550000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a110011001100110011001100110011001100110011001100110011001100112a802a802a802a802a802a802a802a802a802a802a802a800000000000000055005500550055000000000000000000550055005500550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xa93206a793206a93210a9f3206a9e32065932105d3206a79321a9c3210b593206a9281057321543210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x2d832806
|6,0=>0x2b64ac7d8c3917
|7,0=>0x8aefd9c3b17
|8,0=>0x4c6
|_,_=>0
def wAt:=mkWire dB 16 247 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x241064c1326a50666929419904199a581
|_=>0
def oO:Nat→Nat→Nat
|5,0=>1
|6,0=>0x7252322111
|7,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xc0435f58fa97d18007f400c000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>1
|6,0=>0x455f
|7,0=>0x9a4
|8,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_214 7 roots_214 ops++addP pm 1 dom_102 5 roots_102 ops++addP pm 2 dom_226 5 roots_226 ops++addP pm 3 dom_180 5 roots_180 ops++addP pm 4 dom_118 7 roots_118 ops++addP pm 5 dom_244 6 roots_244 ops++addP pm 6 dom_230 6 roots_230 ops++addP pm 7 dom_198 4 roots_198 ops++addP pm 8 dom_242 6 roots_242 ops++addP pm 9 dom_114 5 roots_114 ops++addP pm 10 dom_54 4 roots_54 ops++addP pm 11 dom_182 6 roots_182 ops++addP pm 12 dom_150 5 roots_150 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_246 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_150 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_214 7 s (0,roots_214.map (·&&&dom_214)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_246 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_214 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_246==dom_246)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_246 gM v ys):RunD true dom_246 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_246 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_246 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_246 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_246 roots_246 goal_246 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_246
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=S_246.noCircuit
def isoMvS_126:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_iso_b isoMvS_126 (by decide +kernel) lowS_119
def isoMvS_215:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_119
def isoMvS_219:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_219:Lower true dom_219 roots_219 goal_219 10:=lower_iso_b isoMvS_219 (by decide +kernel) lowS_125
def isoMvS_231:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_183
def isoMvS_235:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_235:Lower true dom_235 roots_235 goal_235 10:=lower_iso_b isoMvS_235 (by decide +kernel) lowS_189
def isoMvS_245:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 9:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_243
def isoMvS_249:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 9:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_187
def isoMvS_250:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 9:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_243
def dzo_126_1:=0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def gzo_126_1:=0xaaaaaaaaaaaaaaa8aaaaaaaaaaa8aa00
def gsh_126_1:=0x55555555555555545555555555545500
theorem lowS_zo_126_1_86:Lower true dzo_126_1 roots_126 gzo_126_1 7:=lower_iso_b (d1:=dom_126) (r1:=roots_126) (T1:=gsh_126_1) [(dom_126,1)] (by decide +kernel) (lower_slice_b (T:=gsh_126_1) [(0x55005500550055005500550055005500,0,8),(0x55555555000000005555555500000000,0,32)] (by decide +kernel) lowS_86)
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000ffff0000fffe0000fefc0000
def gsh_111_16:=0xffff0000ffff0000fffe0000fefc
theorem lowS_zo_111_16_41:Lower true dzo_111_16 roots_111 gzo_111_16 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xcccc0000cccc0000cccc0000cccc,0,2),(0xf0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff0000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_94_1:=0xaaaaaaaa00000000aaaaaaaa
def gzo_94_1:=0xaaaaaaa800000000aaa8aa00
def gsh_94_1:=0x555555540000000055545500
theorem lowS_zo_94_1_86:Lower true dzo_94_1 roots_94 gzo_94_1 6:=lower_iso_b (d1:=dom_94) (r1:=roots_94) (T1:=gsh_94_1) [(dom_94,1)] (by decide +kernel) (lower_slice_b (T:=gsh_94_1) [(0x550055000000000055005500,0,8)] (by decide +kernel) lowS_86)
def dzo_87_8:=0xff00ff0000000000ff00ff00
def gzo_87_8:=0xff00fe0000000000fe00aa00
def gsh_87_8:=0xff00fe0000000000fe00aa
theorem lowS_zo_87_8_86:Lower true dzo_87_8 roots_87 gzo_87_8 6:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_8) [(dom_87,8)] (by decide +kernel) (lower_slice_b (T:=gsh_87_8) [(0xaa00aa0000000000aa00aa,0,1)] (by decide +kernel) lowS_86)
def dzo_47_16:=0xffff0000ffff0000
def gzo_47_16:=0xfffe0000fefc0000
def gsh_47_16:=0xfffe0000fefc
theorem lowS_zo_47_16_41:Lower true dzo_47_16 roots_47 gzo_47_16 6:=lower_iso_b (d1:=dom_47) (r1:=roots_47) (T1:=gsh_47_16) [(dom_47,16)] (by decide +kernel) (lower_slice_b (T:=gsh_47_16) [(0xcccc0000cccc,0,2),(0xf0f00000f0f0,0,4)] (by decide +kernel) lowS_41)
def dzo_59_4:=0xf0f0f0f0f0f0f0f0
def gzo_59_4:=0xf0f0f0e0f0f0a000
def gsh_59_4:=0xf0f0f0e0f0f0a00
theorem lowS_zo_59_4_43:Lower true dzo_59_4 roots_59 gzo_59_4 6:=lower_iso_b (d1:=dom_59) (r1:=roots_59) (T1:=gsh_59_4) [(dom_59,4)] (by decide +kernel) (lower_slice_b (T:=gsh_59_4) [(0xf0f00000f0f0000,0,16)] (by decide +kernel) lowS_43)
def dzo_43_4:=0xf0f00000f0f0
def gzo_43_4:=0xf0e00000a000
def gsh_43_4:=0xf0e00000a00
theorem lowS_zo_43_4_43:Lower true dzo_43_4 roots_43 gzo_43_4 5:=lower_iso_b (d1:=dom_43) (r1:=roots_43) (T1:=gsh_43_4) [(dom_43,4)] (by decide +kernel) (lower_slice_b (T:=gsh_43_4) [] (by decide +kernel) lowS_43)
def dzo_119_8:=0xff00ff00ff00ff00ff00ff00ff00ff00
def gzo_119_8:=0xff00ff00ff00fe00ff00ff00fe00aa00
def gsh_119_8:=0xff00ff00ff00fe00ff00ff00fe00aa
theorem lowS_zo_119_8_86:Lower true dzo_119_8 roots_119 gzo_119_8 7:=lower_iso_b (d1:=dom_119) (r1:=roots_119) (T1:=gsh_119_8) [(dom_119,8)] (by decide +kernel) (lower_slice_b (T:=gsh_119_8) [(0xaa00aa00aa00aa00aa00aa00aa00aa,0,1),(0xff00ff0000000000ff00ff00000000,0,32)] (by decide +kernel) lowS_86)
def dzo_118_8:=0x55005500550055005500550055005500
def gzo_118_8:=0x55005500550054005500550054000000
def gsh_118_8:=0x550055005500540055005500540000
theorem lowS_zo_118_8_86:Lower true dzo_118_8 roots_118 gzo_118_8 6:=lower_iso_b (d1:=dom_118) (r1:=roots_118) (T1:=gsh_118_8) [(dom_118,8)] (by decide +kernel) (lower_slice_b (T:=gsh_118_8) [(0x550055000000000055005500000000,0,32)] (by decide +kernel) lowS_86)
def dzo_86_8:=0x550055000000000055005500
def gzo_86_8:=0x550054000000000054000000
def gsh_86_8:=0x5500540000000000540000
theorem lowS_zo_86_8_86:Lower true dzo_86_8 roots_86 gzo_86_8 5:=lower_iso_b (d1:=dom_86) (r1:=roots_86) (T1:=gsh_86_8) [(dom_86,8)] (by decide +kernel) (lower_slice_b (T:=gsh_86_8) [] (by decide +kernel) lowS_86)
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0f00000f0e00000a000
def gsh_107_4:=0xf0f00000f0f00000f0e00000a00
theorem lowS_zo_107_4_43:Lower true dzo_107_4 roots_107 gzo_107_4 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_43)
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,33),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(4,20),(4,68),(5,13),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,40),(10,11),(10,26),(10,42),(10,74),(12,13),(12,28),(12,44),(12,76),(14,15),(14,30),(14,46),(14,78),(16,18),(16,20),(16,80),(17,19),(17,21),(17,25),(17,49),(17,81),(24,25),(24,26),(24,28),(24,56),(24,88),(32,33),(32,34),(32,40),(32,96),(36,37),(36,38),(36,44),(36,52),(36,100),(48,49),(48,50),(48,52),(48,56),(48,112),(64,66),(64,68),(64,80),(64,96),(65,67),(65,69),(65,73),(65,81),(65,97),(72,73),(72,74),(72,76),(72,88),(72,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1fffffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|5=>16
|6=>72
|7=>187
|8=>272
|9=>138
|10=>14
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xf7412b1540993368411a82d1f813805d68d456d73c7ff2f93f1cda31932811f9c0bdff0593301118
|6,0=>0xf955df8c83ecdf1e9750e656bde900d5fcbcff54cf0c7b290ab16d0af53eae69aaa8c2a71f8a344d9f9ad9bf689b0b99971a98227963878e71388b8285951854dc817f07e47f7a49c75a47724937179a6f8fa687ff680f065fdf602bf5e15e5d148577e45755a574165610b556ba47cd945b4743db9405243f33c38abe36d393409b3350b316c22f61c2b676252b619a40194b217ba012e251161a0f7ac0ec9f0e11207da305f0304c9903c95027cf020be01f7a
|7,0=>0x8d4998cee086ef285cf382c088248980c4b803eb7ed867e1b07da587ca937bdfa7bb957a36377cc4743cc736877252c7200b6d1996c2dc6b29f6a0a86990a68d3268889687ff67a586730366b4262ffe629526264861b3960fce5fd7a5d8a95b8b45b4fc59b99598b058479552f153c9f515a451237509cf4fbc24f3314eb994e9f64d2e84ca2f49758488214770445fd54386743654417ae40e343e83a3d6503b6f03b4be399a53918538fb33841c380b2380623563632f282fdf52e9482ba7c2b9802b6202b3482b1bf2aa6b29aa628dc728c7e282232703926d0426208251e1234e92112120b822032e1f0f21ec0e1c4711a9a91a62d1a1911a03d17fb615a7514c28145241315b12c2b10d8b1071f0f5d10e3600dc050c8070bff90bfd90b6a80af240a98b0a8bc096cf07d0a07c73065b80358102b910162b0107e00f8e
|7,1=>0xfe905fc773f5de5f52fef3135ee18deb980eb0a8e94c0e8ba2e82eee7840e6dc9df7b5de096dd624db258d43b2d3ad8d21f6d19d7c8babc4ef3c0df1be9cfbe696bd92abcb2fbc7f6b8d28b7d47b755ab56bab54abb4302b41ccb232cb2170af17dae1b8ac840a9a08a6aada1aa9a1a599f02d9dceb9a99399b8a9811996916947ff937bf927e39258c906ec8ed1f8dde18d709
|8,0=>0x4a45a490be4883f481cb47ab0468784537244ea744ca8447d843fbe43b87436544301342003405bd400103ec2d3c9ce3c1153b9aa3b3713ae0c3a32939c0e395ed394e2386fe3740a36709364263623135f7b359b234b5833e1632d143254f311912fdf52e02c2deff2da292d9d92d8be2d0152c7672afad2984b292f128932282b627884266cd258c5255cf24af324373241ca22546217e121414212e820e2a201071f8081f42b1efe81ec0c1ce3c1c8211c6b61c6031bb9d1acb91a4621a177197fc1949818e6018537179041765416c9e16a721606714fb614e3414dfe13c891281912563123e41212811def114a2111d80f9e60f7620cfb30c8070c23b0ade60acb30a8bc0956f0889d084d8084ba07925076cc068d1068220656f061b305f5d05e0905c2405b6c04db804c680402a03c1c01abc01a3b017350120300e28
|8,1=>0xdbed3da115d9849d88fed7edfd58bad4e28d1b90d0cf6d0c3acdf8acc03fc7b25c7929c73a5c3f6bc1f1ebc515bc4a0bb95ab98e2b8eebb586db51c4b4538b3c51b1624b0dcfad04bab49eaa9d4a991ca83b2a7ad8a70b9a46dba468ba2675a1c5f9e54f9e46c9945f98a2496ff7942799189790bbb906eb8fe558fb128dd078c80689b5889298880f5872e2842a5835778233c80d3b80c5d7fd637e4c47dcd77981b78f9c781357744c761fa73f9072e4b720297200b7195c711e06a55d6a31669f356855e682ee675af672ff66e0b669496638464aa96410f640ac63934630a362b7b6295262648623a361d476125d6114d5fda25e1765d5b95c5975bc9a5a1b9585745854f57a495735f56bd4551b854a4253e695118350e7350cf2507b64f2f44ef404ee2f4e4dc4e4884dede4de7a4d9914ceea4c7834b42b4b2c24a86e
|8,2=>0xfe233fcf9afb75af7783f2e0befc2eefa7deecdeeec8eee191ecf7eec262eb597eb261e65a3ddfc2
|9,0=>0xd89b2d3928cec71cdf47cdd70cb389cae58c7760c6e0bc3a7dbf087bdd15bb383ba0a2b6ac8b51c4b16d2b0480afed3afc7daded7aa9a7a991ca8a85a8201a6636a4c3aa36faa24cba21faa1f8aa11819bd299b7a09b2b798001934af912d68dc818ceeb8c1808b3068104b80e3c7e3a47a7e379dde776fa761fa721876d2926a3f7688a56765b64cd36309f5e22c5d2755d1915cc7658cab57fbf4c7834a45a49cb6489a04816946fad46f5d46aaa4454a445313fd7a3d5ff3d36c3c55e3c2ee3a6793933b38fcb363a335d47350f0348ea33f6c3254f323e43119130ed6308f72d79b2bc422a4cf292d4291b824b852479722dec2258c224dc2150d1df2b1ab8a1927417b871765416ab6156f1155f210c780dece0c8070c6fe0bb3f0baf90a7090a4e309fe00973f0969708cad07bf806d14053570398a037ed016a400f9b
|9,1=>0xfd84bfa280f7decf673bf4ebdf1cfbeb784de17cdd06ad8c87
|10,0=>0xe74f2ce280bbe948d3bf83c7d761fa715435254f43a533b65b31191150280cfcb05c14
|11,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfffffffffffff0f0f0f0f0f0f0f0f0f0cccccccccccccccccccccccccccccccc00ff00ff00aa00aa00ff00ff00aa00aaffffffffcccccccceeeeeeeecccccccc0f0f0f0f0f0f0f0f0f0f00000f0f000055555555550055005555555555005500ffffffffffffffffffffffff00000000ffff0000ffff0000ffff0000ffff0000ffffffffffffcccccccccccccccccccc00ff00ff00ff00ff00ff00ff00aa00aaffffffff00000000ffffffff00000000ffffffffffffffffffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffccddffffccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
|0,1=>0xffff0000ffff0000ffff00000000ffffffff00000000ff00ff0000000000ffffffffffffffffffffffffffff0000ffffffffccccccccffccffccccccccccffffffffffffffffff00ff00ff00ff00aaaaaaaaaa00aa00aaaaaaaaaa00aa0055005500550055005555555555005500fffff0f5fffff0f0f0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0000ff00ff00ff00ff00ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00ffffffffffffaa00ff00ff00aa00aa0000000000333333330033003333330000ffffffffaaaaaaaaffffffffaaaaaaaaffffffffff00ff00ffaaffaaff00ff00ffffffffffffffff0000000000000000
|0,2=>0xf0f0f0f0f0f0f0f0f0f00050f0f0000ffff5555ffff00000000000000000000ffff5555ffff0000ffff5555ffff0000ffffddddffffccccccccccccccccccccffffffffffffffff5555555500000000ffff00ffffff00000000000000000000ffff00ffffff0000ffff00ffffff000000ff00ff0000000000ff00ff00000000ffffccffffffcccccccccccccccccccc000000000000ffffffffffffff00ff00ffffffffffff0000ffffffffffff000055555555000000005555555500000000ffffffffffff0000000000000000000033333333333333333333333333330000ffffffff00000000aaaaaaaa00000000ffffffffffffffffaaaaaaaaaaaaaaaa
|0,3=>0xffffff0000ffff00ff00ff00000000ffffffffccccccccccccccccccccccccffffffff000000000000000000000000fffffffffcfcfcfcfcfcfcfcfcfcfcfc00000000333333333333333300000000fffff0fffffff0f0f0f0f0f0f0f0f0f0ffaaffaaffaaffaaffaaffaaffaaffaaffffffffffffffff00ff00ff00000000ffffffffffffffffffffffffff00ff0000000000ffffffff00ff00ffffff000000000000aaaaaaaa00aa00aaaaaaaaaaffffffffff00ff00ffffffffff00ff00ffffffffaaaaaaaaffaaffaaaaaaaaaa0f0f00000f0f0f0f0f0f00000f0f0000000000000000ffff00ff00ff0000000000330033333333330033003333330000
|0,4=>0xaaaaaaaaffffffffaaaaaaaaffff0000ff55ff55ff00ff00ff55ff55ff00ff005555555555555555555555555500550000000000ffffffff00000000ff00ff00ff00ffffff00ffffff00ff00ff00ff00aa00aa00aa00aa00aaaaaaaaaa00aa000f0f0f000f0f0f0f0f0f0f000f0f000033333333333333333333001133330000aaaaffff00000000aaaaaaaa00000000aaaaffffaaaaffffaaaaaaaaaaaaaaaa0000ffff0000ffff0000000000000000ffaaffffff00ff00ffaaffaaff00ff000f0f0f0a0f0f0f0f0f0f00000f0f0000fffff5f5fffff0f0f0f0f0f0f0f0f0f055555555555555555555555500000000ffff0055ffff00000000000000000000
|0,5=>0xffffffff00ff00ff00000000ffffff55ffffff00ff00ff00ff00ff00aaaaaaaaaaaaaaaaffffffffaaaaaaaa00aa00aa00aa00aa00ff00ff00aa00aa0000000000000000ffffffff00000000ffffffffffffffffffffffaaffffffaa0f0f0f0f0f0f0f0f0f0f0f0a0f0f0f0affffffffffffffffffffffffaaaaaaaaff00ff00ffffffffff00ff0000000000ffffff00ffffffffffffff00ffff0000ffffffff0000ffffffffffff0000000000000000ffffffff00000000ffff0000ffff0055ffff0000ffff0055ffff000000550055000000000055005500000000ffffffffffffffffffff0055ffff0000ffff5555ffff0000ffff0000ffff0000
|0,6=>0x555555550000000055550000ff00ff00aa00aa00ff00ff00aa00ff00ffffffffffffffffffffffffffffff00aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000f0f0f0f0f0f0f0f0f0f000f0f0f0000ffffffffffffffffffff00ffffff0000333333333333333333330033333300000000000000000000ffffffffaaaaaaaaffffaaaaaaaaaaaaffffffffaaaaaaaaffff000000000000ffffffff00000000ff00aa00aa00aa00ff00ff00aa00aa00ffffff00ffffffffffff0000ffff0000ff00ff00ffffffff00000000000000000f0f0f000f0f0f0f0f0f00000f0f0000ff00ffff00000000ff00ff0000000000ffccffffccccccccffccffcccccccccc
|0,7=>0x55555555000000000000000000000000ffff00ffffff0000ffffffffffffffffffffffffffffaaaa33333333333333333333333333332222fffffffff0f0f0f0fff0fff0f0f0f0f000ff00ff00aa00ff00ff00ff00aa00aaffaaffaaffffffffffaa0000ffff000000ff00aa00aa00aa00ff00ff00aa00aaffffffffffff0000ff00ff00ff000000ffffffffffaaffaaffffffffffaaffaa00ff00ff00ff00ff00aa00aa00aa00aa00000000ffffffff0000000000000000ffff0000ffffffffffff0000ffff00000000000000000000ffffffffffff0000000000000000ffff00000000000000000000aa000000ff00ff00ff00ff00ff00
|0,8=>0xffffffffffff0000ffffaaaaffff00000055ffff0000ffff0055005500000000ffffffffffff00005555555500000000ffffffffaaaaffffffffffffaaaaaaaaffaaffaaffffffff0000000000000000ffffffaaffffffffffff0000ffff0000ffffffff00000000ffff00000000000000000000ffff00000000ffffffff0000ffffffffffff0000ffffff00ffff0000ffffffffffffaaaaaaaaaaaaaaaaaaaa0000000000000000000000ff00000000f0f0f0f0f0f0f0f0f0f0f0fff0f0f0f0ffffaaaaffffffffffff0000ffff0000aaaaaaaaffffffff00000000000000000f0f0a0a0f0f0f0f0f0f00000f0f0000ff00ff00ff00ff00ffffffffff00ff00
|0,9=>0xff00ff00ff00ff00ff00ff00ff00aa00ff00ffffffffff00ff00ffffff0000ff00ff00ff55ff55ff00ff00ff55ff00ffff5555ffff5555ffff5555ffff00000000000000000000ffff5555ffff0000ffaaffffaaaaaaaaffaaffaaaaaaaaaa0000ffff0000ffff0000005500000000ffffffffffffff00ff00ff00ff00ff000000ffaa0000ffff0000000000000000ffffffffff00ffffffffffffff00ff00aaaaaaaaaa00aaaaaaaaaaaaaa00aa000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0055000000ff00ff0055005500ff00ff00ff00ffffff00ffffff00ffffff00ff0000000000ff00ffff00000000ff00ff00ffffffffffffffffffaaffaaffaaffaa
|0,10=>0xffff0000000000000000000000000000ffff000000000000ffff00000000f0f0fffff0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffff5555ffff000055555555555500005555555555550000ffffffffffffffff55555555555500000000aaaa0000ffff0000000000000000ffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa0000000000000000fafafffff0f0f0f0fafafafaf0f0f0f00000000000000000ffff0055ffff0000000000000000ffffffffffff0000000000ff00ff0000ffff00ff00ff0000000000000000000000000000ffff0000aaaaf0f0f0f0f0f0f0f0f0f0fffff0f0fafa00000000ffffffff5555555500000000
|0,11=>0xffffffffff00ff0000000000000000000000ffff0000ffff0000ffff0000aaaa5555555555555555555555555555000055555555555555555555000055550000aaaaaaaa00000000aaaaffff0000000000000000ffffffff00000000aaaaaaaa0000000000ff00ff0000000000000000aaaaaaaaaa00aa00aaaaaaaaaaaaaaaa55555555000000000000000000000000ffffffffaaaaaaaaffffaaaaaaaaaaaa00ff00ff00ff00ff00ff00ff00000000aaaaaaaaffffffffaaaa0000ffff0000ffffffffffffaaaaffffffffffffaaaa00ff00ff00ff00aa00ff00ff00ff00aa00005555000000000000555500000000f0f0f5f5f0f0f0f0f0f0f5f5f0f0f0f0
|0,12=>0x5555555555550000ffaaffffffaaffffffaaffaaffaaffaaffff0000aaaa0000ffffffffaaaaaaaaccccffffccccccccccccccccccccccccff55ff55ff55ff55ff55ff00ff55ff00ff00ff00ffffffffff000000ffff000000000000555555550000000000000000ff00ff00ff55ff55ff00ff00ff00ff00aaffaaffaaaaaaaaaaffaaffaaaaaaaa00000000000000000000ffff00000000aaaaaaaaaaaaaaaaaaaaffffaaaaaaaa0000000000000000ffffffffff00ff00ffff0000ffff0000ffffffffffffff00aa00aa00ff00ff00ff00ff00ff00ff0000000000ffffffffffffffff00000000aaaaffffaaaaffffaaaaffffaaaaaaaa
|0,13=>0xff00ff00000000ffff0000ffff0000ffff00ffffff0000000000000000000000000000ffffff00ffffffffffffff00ffff0000ffff0000ff00ff00ff00ffffff00ff00ff00ff00ffffffffffff0000aaaaaaaaaaaa00000000ffff0000ff000000ffff0000ff0000000000000000000000ffff0000ff00ff55ff55ff00ff00ff00ff00ff00ff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff0000000000ffffffffffffff00ffffffffffffff000000000000000000ffffffffffffff00aaaa0000ffff0000ffff0000ffff00000000ffff0000ffff000000ff00000000f0f0fffff0f0f0f0f0f0fffff0f0f0f0
|0,14=>0xffffffffaaaaaaaaaaaaaaaaaaaaaaaaffffffff55555555ffffffff55550000ffffff0000000000ffffff0000000000ffffffffffffffffffffff000000000000ff00ff00ff00ff0000000000000000aaffaaffaaffaaffaaaaaaaaaaaaaaaaaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaffff00ffffff00ffffff00ffffff0000ddddddddccccccccccccccccccccccccffffaaaa00000000ffffaaaa00000000ff00ff00ffffffffff00ff00ffffff0000005555000055550000000000000000ff00aa00ff00aa00ff00ff00ff00ff0055005555550055555500550055005500ffffffffffffffffffffaaaaffffaaaa00000000ffffffff00000000ffffaaaa
|0,15=>0xffffffffffffaaaaffffffff0000000055555555000000005555000000000000000000ff000000ff0000000000000000aaaaaaffaaaaaaffaaaaaaaaaaaaaaaa0000ffff0000ffff0000ffaa0000ffaa0000ffff0000ffff0000ff000000ff00ffffffff0000ffffffffffff0000ff00f5f5f5f5f0f0f0f0f0f0f0f0f0f0f0f00000ffff0000ffff0000555500000000aaaaaaaaffffffffaaaaaaaa000000000000ffff0000ffff0000aaaa0000aaaaff00ffffff00ffffff00ffaaff00ffaa00550055005500550000000000000000ffff0055ffff0055ffff0000ffff0000ffffffffffffff000000000000000000ffffffffaaaaaaaa0000000000000000
|1,0=>0x550055005500550055000000550000ffffffffffffffff0000555500000000ff00ff00ff00aa00ff00ff00ff00aa0000ff00ffffffffff00ff00ff00000000fffffffff0f0f0f0fafafafaf0f0f0f0f0f0f0f0f0f0f0f0f0f0fffff0f0f0f000ff00000000000000ff00ff00000000ffffffffff00ff00ff00ff00ff00ff00ffff0000ffffffff0000000000000000000000000000ffff000000000000aaaaffffffffffffffff0000ffff0000ff000000ffff0000aaaa0000ffff0000aaaaffff0000ffff5555000000000000000000ff00ff000000ff00ff00ff00000000ffff0000ffff00ffffff0000ffff0000ffffffffff00ff00ffff0000ff000000
|1,1=>0xaa00aa00aa00aa00ff00ff00ff00ff00ffffffaaffffffaaffffffaaffffffaa000000000000aaaaaaaaaaaaaaaaaaaa55555555555555555555550055555500ffffffffffffffffffffff00ffffff00ffffffff00000000ffffff000000000000000000ffff000000ff0000ffff0000ffffaaaaffffffff0000000000000000ffffffffffffffff0055005500000000000000000000000000005555000000000f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a00000000ff00ff0055005500ff00ff00ffffffffffff0000ffff0000ffff00005555ffff0000ffff5555555500000000ff000000ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff0000
|1,2=>0xffff0000ffff0000ffffffffffff000000000000ffff0000ffff0000ffff0000ffffffff55555555ffffffff000000005555555555555555550055005500550000000000ff00ff00ff00ff00ff00ff00ffffffffffffffff0000ffff00000000aaaaffffaaaaaaaaaaaaffffaaaaaaaa00000000ffffff0000000000ffffff00ffff00ffffff00ffffff0000ffff0000ff00ff0000000000ffffffff000000005555550055555500555555005555550000ff00ff00ff000000ff00ff00ff0000ff55ff55ff55ff55ff00ff00ff00ff00ff00ff00ffffffffff00ff00ff00ff000000000000000000ffffaaaaffffaaaa55555555555555550000000000000000
|1,3=>0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0
|_,_=>0
def sP:Nat→Nat
|0=>0x1030001f0e824101c018080005040441c00058400a080d838340b080141003070641610028100618070001208018300017028102a020380012080b0080e00028102a0f070000a040a0081c00048202a020380012080a0081c000482006020004c0a040101c000d09020220e058400a0407838000d04820060c0002c1208018080e0a048200407000180a04018080200
|1=>0x28202a0e000c820090400c040e000c40a0801808003008024100307000420b028201e0e0003420050400c1c00178400a080180858001581408030101c0024028201c000b81820050400c0401000400a080100044060801408030109c0026048200602070000a08018601c00080140803078380024028100602070684605040380017068400a0801000440d080241003
|2=>0x58400a080a8380017080141015010004410028201c000583420050400c0407000e00a0801830000b080d01208018080e001a0203c0e0002c20370482006020380012080103800061182410030f0380017048141003010b000090400c040e000d81208018780400110141002038001a1004820040e0003446050400c1c0b1a8406804040cc040e080141015070901610
|3=>0x400c1c002184012081c80c04070001408032103800240482006020380082050200c040e0010068050200c0407000141015078380010028202802070002005040581c000b8400a080b00800220801408030109c002802820040e0d0fc203402810060f070001208018f0003b02810040e0003446090400c0407000a00a080700016060801408031d038003409020720e
|4=>0x4820060207134200504054040e0004046090400c040700014100307000164c08014101b01838400005814104b01038341002820060e2502c2005040581c000584012040400c040c0001410030700092100281072030101c00050400c04002404012080b0081c001181408390183c1c00028201c0019034201204110040e0801410150101c0010048202a02070004605
|5=>0x2c0141003070002e102c014100301000441002958100301038001002820060207000562304810100301038002102820060207000562e2a814100301038001002820061e07000161002810060207000502302820060207068a8100901408030103800230294410030103800100294006020700020050400c740e000a020050400c040e27800200504138060e0002c2025
|6=>0x3000c0400080940a0401038000d08014080801838340b08024100301038005f09014103901838161004814100307080000b028101003010386a100294c080301038001002820bc0207000200502020040e001702005020202a0207090201d0482006020700042050400c1c002082c20550282006020702820090296c1003070001634040cc040e08014100307000b210
|7=>0x40081c0006840e2050200c040e000a054050400c040e000fc2005041c0040e00040680504038000b140400a08370081c00080141015010385610028200602071b020050400c0427000400a0801838006b140400a0801808006914040d0050400c1c00058400a08328081c000801408030783800050400c1e0e0009020050400c1c00310401208018081c001087c0a08
|8=>0x708020090400cee02070000a0801838000b1c0406808308081c0008014080801038000d0801410030700016750801408080180818000801408030101c00050400c040700090203402820060e000c820090400c040e000904609028200602070005c0504054040e120408a34020203c02070002005020e4060207000460539820040e00034207202820040e000342005
|9=>0x1038000d0f8400a7e0400c040e000e00a0801838003214040e4050400c040e000e00a04040081c00030400a0801808007c08024107b0183800101282410150103800102c02410030103800232a814100207000f4100e8141002070001a1002820f20301038001002820060e0002ca4101a04808081c8081c1009014101507000161002820040e001e02005020202a02
|10=>0x70011c10028200602070011a1002820040e001e8203409020060e0002c203402820040e000fc200504038000b068400a8a0400c040e00040aa0504054040e000400a03010380088080250e03010380010028200602072182005040081c00068408a050400d080e000403a05040081c00030400a080183800244084100050400c1c00058400a0801838007f058400a08
|11=>0x2a8141003010392a1002820060e002502005040081c000695020090400c040c000400a0801838006b1c0400a080180800691c0400a0801038009308024100301038009108014109001838000b0809412080b0081c00080d00a08018380017081600a0801838000b080d00a08018080022080151e0301038001002820040e000183e101a0481039010382045028200602
|12=>0x70001a1011814109d010380010048153608018081c0002810100e0002c1a100282134030103820050400c040e0026420050400c1c000b8a020050400c0400110a020050200c040e000b80a08018e81c00080480a0801838400b08014100307000160d080940a040a8081c00080481003070001628080141039018380032080240a084c0081c00028200602070002097
|13=>0x801410030100082220802410030103800a0080d00a08018080e00080240a5b0400c1c000b8240a5b0400c0400110d01208018081c0011814100307000d610028200602001a42005040081c004f8400a08018081c004f0400a08018084e00140400a7304054040e00040e40504054040e000400a080a8081c00081c468050400c1e0e000400a08018081c95080141002
|14=>0x88081c00080154a08018081c00080140808018081c4a0801408080b0081c00080141015070001610048154808018081c00028200602070014610028202a02070003e10048200602060000a081c80c1c000b84012050400c1c200005c0a0801a841c00080141039018080022080240a08018084000110740a080a8081c00080141003010380010200141003070008217
|15=>0x1029c680502020060e0002c2005040e40602038002009040e4060207000467602820060e0002c20090400c040e001044608018380024058a020090400c043e000ec0a080b0081c000f84012a40400c040e000240a08018080e000282006a6070002005040e4060f07000202504820040e0003420090400c783e000740a080b0081c00080d00a0801838140b080140808
|16=>0x1a01408080103800280801410030103800b40801410020700164101a0141003010380010118740a081c80c040e000400a0801ac01c000807412050400c040e100000a0801ab41c00080155808018081c00158401208018087c0002a6c1003010380010340140808018081c0008014104e018081c00081140a08018081c00550400a08018081c001204152050400c040e
|17=>0x2f82009028200602070017a10028200602072ec00100281010030103800ba080d0101e0103800102a8141003010380010028200602072e020250282006020706820050400c040e001043e100294006020700020050400c040e000a0a81002ad810030103800100e81410030103800b5080480a08018081c002a04012052d8200602070003e962a8141003010380010
|18=>0x281006020700048100282184020700020c10400c040e000141002070001a1002820060e0005c200902810101b018081c0002820060207000de100282130030103800100282006020600020050400c0400110400a08018081cc0000400a08018081c00488400a080d8081c005f8940a030103800bc080141039018081c000f84012050400c040e100003e050400c040e
|19=>0x70007010029681003010380010028a408030103800100282072030700016100281010030700016280801410cb018081c00080141003650081c00140400a080a8081c200801410c8010380010028101003010380075080140808018081cc7000400a08018081c00082a40a08018081cc5000402405040e40602070408a090400c040e0013020c3028200602070002025
|20=>0x81c40a040400c040e001482005040081c000304012050400da00e000401205168200602070002012028101015010380010028200602070019e101a01410020700050102281410ce018081c00083340a08018081c000801410030103800280808c120801878040e00041825b0400c040e0001410030133000104b01410030103800101a0481039010382005020200602
|21=>0x18081c006c0400a081c80c040e001502005040081c0006840e8050435c040e0004068050202072020700020050400cae020700020052d82006020700020050400c040e000fc20056a82006020700020d3028200602070002005398200602070004810390141003010380024080d00a0801038003808015a4030103800100282006020700050d1080141003010380024
|22=>0x7300c040e000400a087280c040e00040ce050400c040e000400a08718081c000801410030103800e2080240a08018081c001181410031e0f8001002820060207001c01002b78100301038001002820060207001ba1002b701003010380010400140808018081c000801410db018081c00080140808018081c003f8400a08018081c006d0400a080d8081c006c8400a08
|23=>0x1038002b080145208018081c001c0400a08018081c00290408a05760200602070002009028200602073a8240504054040e000408a050400c040e74840120574020060207000201d0282006020700048100282006027380020250496c1003010380034090101003010380010028101002070001a1002a0c100301038002408024100368038001002820060f070002025
|24=>0x80946e090400c040e000400a081c80c040e0004046050400df00e000400a08018081c007b84012050400c040e003d82058028101003010380010128241003010384000048158208018081c0002821e80301038001002bc810030103800100282006020700020f1028200602073bc2005020207203070001610028200602070005010153b80a08018081c00080141003
|25=>0x400c040e003f820050400c1c001202c20050400c040e0004116054182006020700020250282006020700070100e9600a08018081c0008014100301039f8103e814100301038001002820060207001f610029a810030103800100282006020380020050202120030103800100482006020700046251a02410030103800107c814100301038001002820060207000481f
|26=>0x6840120801878040e000240a08018380017081600a08018081c000f84012050400c0400110400a088000c040e000400a2d0200c040e000902009028200602073000010028200602070008e101a0481003010380010228141003010390c1002820040e000342045028101003010380021080480808018081c0014041fe050400c040e0004012050400c040e002f82005
|27=>0x28221002070000a530400c040e0004012050400c040e000400a08018081c00830400a08018081c0015bdc202504820060207000501002a3c06020700020050400c040e0041420050400c040e00042065502820060207002041002c0410030103800101a1540a08018081c00080480a040400c040e100400a040400c040e000342009608200602070001205040081c00
|28=>0x1038001002820060e1000016100282006020700218100481410030103800dd081540a08018081c00140400a08018081c00068408a050400c040e0040820050400e160e000400a5b0400c1c00058402408018081c00140408a054382006020700020050400e140e000404a05040081c000684012056a82006020700020050400c040e00424200902820040e000182009
|29=>0x1a014e608018081c00081c868050400c040e000400a08018081c00890902034028200602070002071028202a02070002074128241039018081c00080153808018081c0008014111101038001012824100301038004108014100301038011008014a008018081c0008014100301038010f080140803010380023028200602070021c10128d00a04018081c0008014110d
|30=>0x18081c00084603a340282006020700020050400c040e0045c2034028101003010381410028200602070022c10028200602073a8205502820720301038001002820060e00454200504044040e000400a08018081c190801408080a8081c000816c100301038010702820040e0045020058980c040e000400a08018081c4a08014101601038001002820060207000202e
|31=>0x14100301038011c080d00a08018081c0a0811424050400c040e2304068050400c1c00058404a054480c040e00040120504054040e00040ec050202006020700020040400c040e000905010028202a020700020451a014100301038001f080155808018081c001204012050400c1c00058400a7e0400c040e000a020058d0200602070002005018081c008c8400a08
|32=>0xb0081c00080140808018081c0020840ec050400c040e000408a090296c0808018081c00029cc1039018081c00081c80a081c80c040e000400a080a8081c24080200602070004828081140a081c80c040e00040e2090282006021f0004a89018081c000801410030103a3a1002820060e000c82005020203603010384000128140839018081c00081c812050400c040e
|33=>0x7000fe1002822100301038001002c7810030103800100282006020700020b702c6c10030103800101281410030103800280809424050400c040e000406805040e4040e000400ad65400c040e000400ad60406c040e000400a08018081c008204068050400c040e0d0400a08018081c00588400ac10400c040e0016c10036803800100e8240a5b0400c040e000240a08
|34=>0x82cc0a08018081c00080240a081c80c040e000400a08018081c00083c00a081c80c040e000408a34090200602070002005040081c000684012050400c040e0010420050448806020700020059082006020700020050447c040e0004024050400c040e12040aa050400c040e0004100050400c040e0004012055402006020700020056b0200602070800010028200602
|35=>0x18081c00630400a08018081c005e0404a050200c040e000400a5b0400c040e000400a08018081c001589020058982006020700020059302006020700020050406c06020700240050400c040e000902074028200602070024a10028212003010380010128141003010380124080141123018081c000801410030103800105381410030103800105c9600a08018081c00
|36=>0x1038001002b981003010380010028200602070002107028200602070002071028200602074a40010620141003010380010028200602070025010090141003010384010028200602070001a1002c9c10030103800102d8200602070015c10028101003010380024080141003010380021080481003010380028080940a081c80c040e000400a08018081c00083f40a08
|37=>0x202006020708000100481410030103800ae0801410030103800280818c3a050400c040e000400a08018081c20003d420052d8101003010380010048141003010380024080141003010f8001002820060207000481022814100301039de1002820060207000561004814100301038012002820060207002541002820060207001ea10029cc1003010380010390141003
|38=>0x400c040e001d00a08018081c002a04068050400c040e050400a08018081c009604012050400c040e10000200504054040e0004012052d82006020700020090400c040e002b82005148200602070002009028200602070007a050400c1c000584012050400c040e00040b0090282006020700020050406c0602070800010028200602070003e10028225602070002005
|39=>0x1038007402c4c06020700020050400c040e0004046050412c06020700020050400c040e00041047602820060207000200502020060e0002c2025028200602070800010048140808018081c00080200602070004828080d00a08018081c00081d04a055400c040e000400a08018081c20001d00a08018081c00083cc4a052d82006020700020090400c040e000f40a5b
|40=>0x415e059700c040e000400a0801b401c00570400a08018081c002084012052d8200602070000a2d0400c040e0009020050400c040e00490212d028200602070002009028200602070003e10028209c03010380010028200602073a820252d82006020700020050400c040e0013020050406c06020708000340281010030103800100e8240a08018081c000816c1003
|41=>0x400c040e001482005020207203010380010029981003010380010128241003010380010128140602070015c100282112030103800100282072030103800103a0141003980380010128240a08018081c0008014100368038001097814b608018081c00080d012050400c040e0004068050400c040e000408a0902820060207080012f0282006020700020050400c040e
|42=>0x282006020700020050400c040e000407a05040e406020700020055402006020700020250282006020700020340282006020700020090282006020700020050400c040e000408a050202006020700020050400c040e00040e8050400c040e1000020052d82006020700020050400c040e002b820050400c040e0009020050400c040e00041d605
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x2d30151809cc0486021300f1806cc030601530091803cc018600930031800cc0006
|6,0=>0x10ab883d8410e20170fd387cdc3d8e1e570ef3875dc3a0e1c970e1386edc368e1ad70d3386818332e19270c5b861582fce17770b8385a5c2c4e15b70aa38535c28ce13f709c384c5c254e123708e38455c21ce1077080383e5c1e4e0eb707238375c1ace0cf706438305c174e0b37056b0299c13ee0987048b8229c106e07c703ab81b9c0cee0607
|6,1=>0x126b8919c47ee2387118b88a9c446e21c7
|7,0=>0x21cc10c608530421820cc10460813040181fcc0fc607d303e271ed40f4dc798e3c571df38eda075d03a681cfb8e658723038a71c140dedc6e7036b81b238d7206a9034c81a240cf5c66b032d8192c0c76062b030d8183b0c01c5f102f0817440b8205b102d0816440b02057102b0815440a820532e2918144c0a0604f302718135b098e04b702547
|7,1=>0x313c187e0c2f060f8304398020bf105f172f4c1789cbb505d282e5b970e0b7705b382d5c168e0b37059472c6416120af9057482b6b95960abb055672a74151a0a7ee5387298b94a60a44e51a82894142a0a0504fa8279413aa09c504da8269b9331c98904bc825a412b20949049c824a41232090ae47d823b391ba08cee45f822bc113e0892c4418
|7,2=>0x1fb60fcb07dd83eac1f360f8ce7be83dbb9ec1cf52e7a183ccc1e4d8f17078383bdc1dce0ed7076383ae39d520e990744839f31cda0e5d0727738fc1c5e0e1f0707837fc1bde0ddf06e7836fc1b5e0d9f06c87360b9ae9cd6506aa835141a6a0d25068a8341b99ee0ce8e66c833241975ccab064d8322c18f9cc6ee62f8
|8,0=>0x4fa427b213c909db94e9c272a5386e9bc74d9ca6aa5345099a84c8ca6261303097894b8ba5ad92c8e95d74aa4a5321289093d749b3a4ba124d091f748bc243a520b28fd847a4a3b211c728dc746a42335d18b08bc945aba2b25149089b94494a226510128779437c21a1d0bf28569427ba11a507ee8369418320a2103f28169407420164ffce7f59
|8,1=>0x5fdc2fca57d32be185ed3af465794ebc195dc4aec5d7530ba095cc42e3e5710eb8175bd3adca16d50b6375adc2d4e1698eb44859e42cd216590b23958dc2c4a56150b02857d42bc655d30ae2756ccab4615930ac1855cc2ac615512a9f954bc2a41d50f2a7e953aca9b9d4cd0a5d952a4a93214872a3b8519c28aa54450a1b750a3a832140ae9fc9
|8,2=>0x704c38061bf4edf286f54378a1bb32dd096e4bb7061b730db096d44367e5b2d2d8d96c33b5fa1aeeed6f86b34b57a1aad0d4d96a24b4f21a672d2c76924346e5a252d0a8680cb3e619e30ce98670c3362599f2cc87660432e219610ca976504b265d9212c88863fcb1da58db2c66762f4315658992c44861e430d218590c24860ebb05258172c038
|8,3=>0x8084c01e5fff0ff787f74bf9a1fbd0fd687e743f165f792fb487d5cbe8a5f350f9197c4c3e09def50f7197b4c3d825eb10f5177a44bd05de74ef337795c3c91de3aef167787bbc21de010ef797774bb965db92ed48765cbb0e1d78eeb39755c3a8e1d370e94774643a0e5cf8ee7487364398e5cb52e519724c3909dc750e319714c3889dc350e119
|8,4=>0x849bc231e107307b88394c1a660c1305798274c11de07d303598173c09de040f0197
|9,0=>0x94e44a5225191284893e449d224d91264892e4495224991244891e448d224591223990dc484e2415320288fd447ca23d511e288eccc746239311c188dc4c6c22351119f98cbc463e230f117f88bbc45ba62cd115d98aac4539e28b313d889ac44b9e24d111e888b44436620930fc887a443b221c910dc8869cc32a618510ba8859442aa2145109a8
|9,1=>0xa53cd27a692b348d8a42c51f628ecf46e8a334517a28ab344d8a22c50f26869142d7a12c5076282b140c9a01ccff1e7eaf3ed89f2c4f7627ab13cd89e24ceee676713aa99d144e6a2725138999c13cdea26e5136a89b144d6666a4f34999a0c4ce62663132a799144c66662133088980bcbe265df32e6996f44b56659932c3995e3cace6558f2a48
|9,2=>0x29f314f09a744538229b114d08a63cd301e96f34b07
|10,0=>0x2ad315618aacc55462a9315418a9cc54c62a5315218a8cc54462a1315018
|11,0=>0x15717
|_,_=>0
def wAt:=mkWire dB 305 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x708d128400282104041070a914840040a1040410108d1284002821048fb010f9070f5028410284004041010a914840040a10280f0200b04041028010280d0708d1284014041028210708d1284002841028210f001040410280d0286c0184112041070b91684004091040410708d128400282104041070a914840040a10280f040410108d12840028210708502880028410004107079048210286c0284101841
|1=>0x2984104149018920280316810040910280304041010a914840040a10200b02803040411b8030480d028410900c1284002821028010708d1284002841028210200b040410184100041019151a000040420280d0284104041070850288000041040410708d12840028210108d040411284002821028010191d0291800115040420708d02841128400282104041010b916840040910708d12840028410282104041
|2=>0x4041040410007b0286c0184104041041490189202803018b9168400409102803040412e80f2d80102843040410900c0280302801048210288002841000410200b2d84102843040410f0010280d0286c018412d00b020e501801040410415d048a3028410280f128401204102821040410284102880000411204116840040910286c0200b0184104041128400282104041028121a00004041128400404102821
|3=>0x200b0280d04041019bf0901202801040410900c120410280302801368001a0110280d04041070a914840040a10280f3500b020a1040413503b020a1040413380c330010291704042040410108d12840028210108d12840028213200b0418d140420280f028800284100041071850292c019150404204041028210900f028010200b1a0000280d040410487b0286c02841018410200b0280104041028410200b
|4=>0x40413380f330010291704042040410900c00041028011286c0184102841028210280d0292c0191504042040413b00f0900d028010200b000410404104041070850288000041040410708d1284002821028030708d12840028213980b041d1028421284016840040420900c0280302801040410280d0286c018410404112840028210900f02801041d1028420404114840040a1018bb1684004091028030280f
|5=>0x28410286c01841000b91684004091028033b00f0900d0280101215020a20280f040412c00f0480104821028414180b042091204214843040a1140410280f3980b041d102842140410280f12843028212c00f0904102801040413e83b0901102801040410f009028410286c01841028210900c028410280112840028410282112841028210900f02801028e70200b040410404102801018010280d0900c0200b
|6=>0x4041108390284102880000410191f02918001150404202a4a0187d04823028411c8410200b040412c00c0480102841028210e80b12841028210e83b02811040410411d0291800115040420404202801018010280d291150189204042128ac12041028214600f2a8010291504042028010200b0280d040410900f0200b02801040410422d2904201892028030900c029150404212a2702810028210404104079
|7=>0x108d12840028214b0002a80d029150404212840028210900f02801019bd0901202801040414e0430410504803028410200b040410900f02801001850292c01915040420e80b02811040410e83b028110404116840040910280304041010a914840040a10280f0200b02801028210900c02801040410280f0200b02801040413980b041d102842028410188d12840028214b00002915040423680b1a0110280d
|8=>0x2801040410e83b02811040410e83b0482102841028110900c028010404129840041490189202803048870284102880000410708d12840028210e80b028430482102841028430e83b04821028410280d12840028413500b020a10280f040413503b020a10280f040413e80f09011028010404114151028120280f04041070a914840040a10280f0900c02801041d1028420900c12843028210900c1284202821
|9=>0x2841028400488f128400284102821028410708d12840028210111d0291800115040420108d1284002821028410900f02801010f9070f502841028402c00c0480104821028411a0030200b0280d040410404101885028800004104041400002d80d028432c00c0904102801040410900c0200b02801040410488f128400284102821028410708502880000410e80b04821028410e80b04821028410128909013
|10=>0x280f0280d0209302803040415980f090210280112840028210280d048210180102841012c50409202803048210284100041012bd5704002823040ad1204102803070f5028410284016843040910280304041090430280104042018910280355841128030282116842040910004154040040010200b0280d040410708d12840028210284112840028211284002841028210280f0200b0280304041048fb070f5
|11=>0x7d04823028410292e0191504042018411a0400280d02821020030404104823028410482302841000412c02309041028010e803048210284102af302003040410404102882000410280d0286c01841029c51284202821002e71a0420280d1a000028210280d048230480302841042dd120400280302812040414480102810040410480f0482102841028120280104041048232d84102843029150404204041
|12=>0x404101af10200304041020a30280f040410900c000410280101b250904202801018820004104041000a10280f04041168420409102803003190281304041040420000d02801028410286e01841620211a0430280d02821028030404101adf1204002803048f702841028403b00f0900d028010e80b02811040410284101841040410901202801040410188d12840028210708502880000410e83b0281104041
|13=>0x40e2140410280f12842028210189202803040412c00f0904102801012b902841028230284104091028030900c0280104041390031284302821040420280f0280d25801019150404209117040420280112840028210280f028410286c018412d9d10284302842072bd57040028232a80d029150404202801018010280d140410280f04041020e50180104041040a10280f04041018010200b040410200b0280f
|14=>0x140430280f04b5a028410400d042fd1a0400280d040412d80d02843019c51284202821040411204302803128800004102821018411a0230280d1a0130280d040410281204041028420900f0280101add1204002803018010280d04041048a3028410280f0288f128400282114115040420280f04b58028410400d6a0431a0210280d02803041d102842028031284302821140410280f0280d042df1204002803
|15=>0x7684102b580400d003ad02841018420900c0404202801002bd5704002823042d50480f02841028110280304041072dd1204002803028430284102821028010280d04041040410900f02801042091204202803012b902841028230108d128400282102aa0040010282101951028120404133001029170404201b935404204001258030191504042128400284102821010f9070f50284002b8602001040410437d
|16=>0x28210280d028410282102be90406e018410280304823028410480d0284102821018011284002821012dd1204002803040ae1204102803048930284102803090410280104041000410284102821048f7028410284001bd50408200041043cd1c842018016a0401a0210280d003c109040028010200b018010404114840040a10280f02af102003040413f8411204302803040a1140410280f018920404202803
|17=>0x48230284102918001150404202801040420280d0008d1284002821040420900f02801040410288000041028010280f0404102a9d54040040012c02304801028410209002803040410200b028030404129042018920280304209120420280314041028210280f048010482102841003f56b0420400d090110280104041042420188100041020a10280f040410708d12840028210188100041040411284002841
|18=>0x480102841018f5028410284004149018920280302c1d5704202823042ea028820004112041028030280f028410408502880000416c8411a0230280d8204209023028010291504042042e51a0420280d0280d02915040420004102801040410900f0280104041048f70284102840028410900f028010286c02841018410e80b0482102841028410e83b04821028411a0100280d040410409102803040410007d
|19=>0x57040028230480302841028210e80f0281104041042dd1204002803020e7018010404112840028210404158841040920280304041028210280d5980c09021028010200b0004104041141d1028420280f028410291504042040420900f028012a80f02915040420108502880000410200b0284304041040420280f02801040790286c01841013190281304041028210900f02801028410292f01915040422c00f
|20=>0x189202803040411a0030280d020920280304041003cd1c8420180102915040427080b0200104041018850288000041400032d80d028430900c0280104041028435704202823018870288000041128100282104041400002d80d028432c00c09041028011684004091028030280d041d10284212843028210280d12115040420280312842028210900c028420280101801028410282104105048030284101abf
|21=>0x3980b041d1028420404101841000410180102821040411284302841028218d8030200d04041040421a0030280d0280100115040420200b0280d040410281002821040410900c02841028011a0010280d040410280f02803040410900c040420280104823028410280d020910280304041028410200b0404114843040a10280f02c6c0200d040410407b0286c0184158842040920280312841028210280d29041
|22=>0x12040028030200d04041028210280f0282102801018010280d0400d04001018410400d09023028011a0000280d04092028032d9d1028430284202843012b9028230284304821028412c00c0480102841040410480302841040421a0010280d2d841028430404101801041d10284212843028210900c0280302801040420280f02803018011284202821070f502841028400281002821040410008f1284002821
|23=>0x282104041028f7028401204102803040f50284002baf01842000420184102842028036b0030400d01881000411280f0282101c810004254040040011a0420280d09041028010902102801018010284109040028010180104042028010280d0900f028010480302841019d102842540430400101c8300042028030280102915040422d80d028430284104001000410400d1204302803018f5028405400d04001
|24=>0x284102823140420280f0281104041040820004102843040410284102803070f5028400404202803000f5028401204102803028410004257041028230408200041041d102842128430282102aa00400157042028231284202821002b9028231a0430280d02b5a0400d00041028010900f02801043ad018420282302843028030404102880000410280f0280101801028216b0420400d02813040410200304041
|25=>0x40f5028401284002821019150404212042028031a0010280d0200b04041000410282102841040410280f02803028420280d040010282100041028421c8420180102843028210284102840028430284202812040411a0030280d0006e0184102841000410900c028012d841028430284102823040a10280f02841028400200b04041029d102842048010284101841000410482302841018f7028400004104041
|26=>0x189202803018010404102917040420284102821028230282102810040410180102842010f5028400284102821012b9028232d82102843028410280d040420280d02841000412d821028435704002823040f702840012b90282304803028412d8410284304091028031280f0282102c810004204823028410189102803003ad0184202843028210286e0184101841000410280d0404104821028410284302842
|27=>0x28400180104001028210280d028410404204041028420004102843028230280301842
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x135400000000000125022a041400000f500000000000000001ca000006a80c14000000000000ad413a00000000000011a0000000000000fa00000000000000000000000000000001a500000000000000000000000000016402480000000000001aa00000000094000000000000054000a00000000000
|6,1=>0x2d280000ac800000000524
|7,0=>0x232646048b8913421e8430c84200000000414c00010141fa83e507aa0f141da83a8c73980001c6837d06e18d841aa6345066a0c9418a8308c5f98bb416e82cd057a0ab414e800000000a3413e826d0000000012e8250c48208d300002250431883310061f103c2075300001c8c37986b40ce8000031a05f4
|7,1=>0x7450e6a1ca338c80000e199bf400006ed0000000036e86cd0d819ac435260000d319a2400006790cd999833288641000018c43108614cc0a17d42f285d8cb9216e42d66000000000002ce8590cb0215c42b085510a8214d300005250000146328484fcc9da13742668000097a12b42506491090211c4
|7,2=>0xa30d449800050c6a0913f200004f489d9139226f34d869a1132226044b8800012c225444a08931000000004908914d211a3e447668e0d1a2230400000001162229344a888510f1a1a442c8849107220a440c880cd0019fd33f287d50f8a1ed43d2879500001e233be676d0eba1d52
|8,0=>0x6906d14da11b3f36786ce4d9b1b3336606cb4d951b2736486c84d8f1b1b36306c54d891b0f36186c24d831b0336006bf4d7d1af735e86bc89779aec35d26b98d719ae035ba6b68d6b9ad435a26b3c9661ac9358c6b0cd6092be35766ae0d5a9ab2355e6ab0d549aa635466a80d4e9a9a352e6a549491a8f3
|8,1=>0x80c700ce001bfd37f46fdcdfa1bf137dc6facdf41be537c46f7cdee1bd937ac6f4cde81bcd37946f1cde21bc1377c6eecddc1bb537646ebcdd61ba9374c6e909d09b9e37366e60dca9b92371e6e30dc49b8637066e00dbe9b7b26f06dd4db91b6f36d86da4db31b6336c06d74dad1b5736a86d44da71b4b3
|8,2=>0x98272f8e5d9cb8396a72c8e5814ae295672a0e529ca329407274e4d1c9739287244e471c8b3914321ce421c8138fc71ece3c1c7538e471bce361c6938cc718ce301c5d38b4715ce2a1c51389c712ce241c45388470fce1e1c39386c70cce181c2d3854709ce121c21383c706ce0c1c153824703ce061c093
|8,3=>0xaf475dceba1d713adc75aceb41d653ac4757ceae1d593aac754cea81d4d3a94751cea21d413a7c74ece9c1d353a6654c0e969d2a3a4e7490e909d1e3a367460e8a9d123a1e7430e8515073a087404e7f1cfb39f073d4e791cef39d873a4e731ce339c0737c66e94da39ae7350e689cce39967320e629cc41
|8,4=>0xb527698ed19da03b3a7668ecb9d943b24563cec61d893b0c760cec01d7d3
|9,0=>0xc5458a0b1316242c445880b0f161c2c345860b0b16142c245840b07160c2c145820b0316042c045800aff15fc2bf457e0afb15f42be457c0af715ec2bd457a0af315e42bc45780aef15dc2bb45760aeb15d42ba45740ae715cc2b945720ae315c42b845700adf15bc2b7456e0adb15b42b6456c0ad715ac2
|9,1=>0xd545aa0b5316a42d445a80b4f169c2d345a60b4b16942d245a40b47168c2d145a20b4316842d045a00b3f167c2cf459e0b3b16742ce459c0b37166c2cd459a0b3316642cc45980b2f165c2cb45960b2b16542ca45940b27164c2c945920b2316442c845900b1f163c2c7458e0b1b16342c6458c0b17162c2
|9,2=>0x35f16bc2d745ae0b5b16b42d645ac0b5716ac2
|10,0=>0x3668ecc1d963b287648ec81d8e3b187628ec41d863b087608ec01
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 15
def pmP:Nat→Nat
|0=>0xdf000000000db000000000c8000000000a80000000009900000000098000000000900000000008b000000000880000000005b0000000005a0000000005300000000051000000000500000000004a000000000480000000004000000000031000000000220000000001f0000000001900000000011000000000100000000000b0000000000a00000000009000000000080000000000500000000003000000000020000000000100000000000
|1=>0x800200000008001000000080000000000385b00000000830000000008180000000081300000000791000000003db00000000342000000002ff000000002d9000000002d8000000002c8000000002880000000027b0000000025800000000254000000002510000000025000000000248000000002400000000020100000000188000000001800000000014b00000000140000000001130000000010c000000001030000000010200000000100
|2=>0x102db0000001027b000000101d90000001017b000000100df000000100400000000f87b0000000f85b00000008850000000083db000000083d1000000082db000000082c80000000827b0000000825b0000000824200000008241000000081db0000000817b0000000815b0000000810200000008101000000080df000000080db000000080810000000807b000000080790000000805b00000008051000000080410000000804000000008008
|3=>0x100008000000481db000000480df000000480db00000048088000000402ff000000402df00000040258000000400fb000000400db000000400c8000000400b8000000400990000004009800000040088000000400580000004004e0000004004600000040002000000207db000000203db00000018313000000182ff000000182df000000182db0000001815b000000180df000000180db000000102ff000000102fb000000102f9000000102df
|4=>0x1283db000001280db000001083fb000001083db0000010835b000001082db00000108293000001081fb000001081db0000010815b000001080f3000001080db0000010805b000001080480000010801b000001003fb000001003db0000010037b000001002fb000001002db0000010025000000100248000001001fb000001001db0000010015b0000010005b0000010005800000100043000001000400000010001b0000010001000000100009
|5=>0xc0815b00000c000db000009083db0000090008b000008400db0000084005f0000081815b0000081037b000008003000000080011b000005400df0000052805b0000050825b000005080df000005080db0000050805b0000050025b0000050015b0000050005f0000050005b000004182df000004180df000004082df000004080df000004080db000004002df0000040004a00000200010000001888830000014805b0000014005b000001287db
|6=>0x1c4805b000019083db000019081db000018400df0000181815b0000180815b0000180804a000018080400000180015b0000180005a00001800050000015003df000014080df000011083db000011081df000011081db000011081d3000011003db000010182db000010180db00001010153000010082db000010080df0000100805b0000100804c0000100037b00001000342000010002ff0000100027b00001000242000010001320000100005c
|7=>0x381015b000031480db00002d0015b00002c182db00002c180df00002c0805b00002c001df00002c000df000029081db000029080d3000028582db0000281835b0000281037b0000280815b00002808113000025080d9000025000d9000024183db000024083db0000240835b000024080d90000240805b00002408042000024000db0000240005a00002400058000024000520000240004a0000210005f000020500fb0000200815b000020080db
|8=>0x40280815b004024100df0040180837b0040180835b0040100835b004001083db00400108242004001002db0040001817b0040001815b0040000830200400000350004000003120040000005a004000000110030000807b0030000805b0010050805b001001083db001001080db0008280815b0008100805b0008000835b000800081510004000811a000301281db0003010815b0001002015b000080086430000400825b0000400001000003c001db
|9=>0x10004180ff010001083fb010001083db010001083d10100010835b01000108251010001081fb0100010817b010000480fb010000400780100000925b01000008a59010000082db0100000827b0100000825b0100000807b010000080540100000805101000000352010000002fb010000000d9010000000720100000001900c02c183df00c0080835b00c0080035b00c0000015b00802c002ff008000080db0048080837b00402c102df00402c0007b
|10=>0x20000000002122001081db120001083db120001003db102001083db1000050005b100001081db100001003db088001003df088000082df080004000df080004000db08000108208080001081db0800010033b08000100018080000182df080000102df080000002d0080000000000700000827b0600004804b0600000825b0600000805b0600000804b0200000845b0200000844b0200000825b0108000837b0100181817b0100100807b010010008df
|11=>0x8a0000182db50000108ddb4200000804b2000080815b200001080db20000000102
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x1200028000005000100000000140a05000080000000000400010e00000000380e000000004000000004000000000000000000120000000000000000050280000001d800000500000000f098000000
|7,0=>0x680e05840004201004140000008940a1001000043e001bc0a050081c00010485c86992383c020a0280000001480852125228c3a050002800050a814021213001e21201048b240010804e830901412000000800010183104012b808040048c400a0107c1c32120c1b40a1240928241209800003e6f8040000048a074230040c0421028280202000081e1e1e0000eb6
|7,1=>0x140a000281cd600099607c05079b03607090002412041040000820140a010281436e300000fe021f0f8b40180804723f0485c2e0203174023109088000201114843d
|8,0=>0x59941249c76b1d283605ad27815758bebd0fa8c5d2e447d25d414f464963714330b0d0f2631c5e0b0385852e4893c7c5f535e24ca00542a9eb28a6017d08bf6433d388f4f199748b1aa56952a8f03492a7893989889371aa3950498dd7d4996aa22d068118ac4f2309c4a6a60ed0066f7271310e325800aa5110e13ec01426d519673ad4ae182d35a385ce92d815512a
|8,1=>0x739d0ab206caa28e9d4a3542a488aca68a508ea5d6024513595e4938d95fcb12425128984b1212d131b10042943a981261d2e2c09246583043f634d2debee9335928aa58d575deb77938138a14b99c54834e30e14217092e5ee51bbc11144a64d6828519325c86475cd02b23192c28ea29dc6468ea531e658583c1118a5e15b08fd0e4da0058694e38890f2594d9ec5b
|8,2=>0x4e56e5c48a6b62747238a18227b4fce59146
|9,0=>0x4e341b6aa4ea5d2f585525d5ef333945faec9f2e5f74298a71384485a6db94b34cc90cde31aac913d2b27261007d9a03c9c9ea3539484e331dc524d4ce7a9a992a67c964fa59389666a70d3322955d2e446a36a4ca87cd0d393868ad4eee19f4fca49c58275a4f54dc84fab87e48dc2d3aa9f1947c7c3a0caf4ab1515a446ed3e50b05e9e961228c339772479311aeac
|9,1=>0x143374b94921393e435395c
|10,0=>0x13876a70c1fe44224c0a2aa4ba3d5d09
|11,0=>0x16
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 44 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_125 10 roots_125 ops++addP pm 1 dom_119 9 roots_119 ops++addP pm 2 dzo_126_1 7 roots_126 ops++addP pm 3 dom_126 9 roots_126 ops++addP pm 4 dom_123 10 roots_123 ops++addP pm 5 dzo_111_16 7 roots_111 ops++addP pm 6 dom_111 9 roots_111 ops++addP pm 7 dzo_94_1 6 roots_94 ops++addP pm 8 dzo_87_8 6 roots_87 ops++addP pm 9 dzo_47_16 6 roots_47 ops++addP pm 10 dzo_59_4 6 roots_59 ops++addP pm 11 dzo_43_4 5 roots_43 ops++addP pm 12 dzo_45_16 5 roots_45 ops++addP pm 13 dom_61 6 roots_61 ops++addP pm 14 dom_109 7 roots_109 ops++addP pm 15 dom_63 8 roots_63 ops++addP pm 16 dzo_86_1 5 roots_86 ops++addP pm 17 dom_93 6 roots_93 ops++addP pm 18 dom_118 7 roots_118 ops++addP pm 19 dom_115 7 roots_115 ops++addP pm 20 dom_95 7 roots_95 ops++addP pm 21 dzo_124_1 6 roots_124 ops++addP pm 22 dzo_118_1 6 roots_118 ops++addP pm 23 dzo_119_8 7 roots_119 ops++addP pm 24 dom_86 5 roots_86 ops++addP pm 25 dzo_118_8 6 roots_118 ops++addP pm 26 dzo_109_16 6 roots_109 ops++addP pm 27 dzo_43_16 5 roots_43 ops++addP pm 28 dzo_92_1 5 roots_92 ops++addP pm 29 dom_124 7 roots_124 ops++addP pm 30 dzo_85_8 5 roots_85 ops++addP pm 31 dzo_86_8 5 roots_86 ops++addP pm 32 dom_59 7 roots_59 ops++addP pm 33 dom_107 8 roots_107 ops++addP pm 34 dom_103 6 roots_103 ops++addP pm 35 dom_102 5 roots_102 ops++addP pm 36 dom_43 5 roots_43 ops++addP pm 37 dzo_107_4 6 roots_107 ops++addP pm 38 dzo_107_16 6 roots_107 ops++addP pm 39 dom_110 6 roots_110 ops++addP pm 40 dom_91 6 roots_91 ops++addP pm 41 dom_55 5 roots_55 ops++addP pm 42 dom_122 7 roots_122 ops++addP pm 43 dzo_122_1 6 roots_122 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_126_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_111_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_94_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_87_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_47_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_59_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_43_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_45_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_86_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_124_1_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_118_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_119_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_118_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_109_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_43_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_92_1_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_85_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_86_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_107_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_107_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_zo_122_1_82 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_125 10 s (0,roots_125.map (·&&&dom_125)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_125 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 72 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 72 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 187 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 59 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 187 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 272 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 272 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 138 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 10 128 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 138 → Z 9 i = true := (range_split z9_0 z9_128)
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
def dzo_212_1:=0x220022000000000022002200000000002200220000000000220022
def gzo_212_1:=0x220022000000000022002200000000002200200000000000200000
def gsh_212_1:=0x110011000000000011001100000000001100100000000000100000
theorem lowS_zo_212_1_84:Lower true dzo_212_1 roots_212 gzo_212_1 5:=lower_iso_b (d1:=dom_212) (r1:=roots_212) (T1:=gsh_212_1) [(dom_212,1)] (by decide +kernel) (lower_slice_b (T:=gsh_212_1) [(0x110011000000000011001100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_214_1:=0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa
def gzo_214_1:=0xaa00aa0000000000aa00aa0000000000aa00a80000000000a80000
def gsh_214_1:=0x550055000000000055005500000000005500540000000000540000
theorem lowS_zo_214_1_86:Lower true dzo_214_1 roots_214 gzo_214_1 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_1) [(dom_214,1)] (by decide +kernel) (lower_slice_b (T:=gsh_214_1) [(0x550055000000000055005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_86)
def dzo_210_1:=0xa000a00000000000a000a00000000000a000a00000000000a000a
def gzo_210_1:=0xa000a00000000000a000a00000000000a00080000000000080000
def gsh_210_1:=0x50005000000000005000500000000000500040000000000040000
theorem lowS_zo_210_1_82:Lower true dzo_210_1 roots_210 gzo_210_1 5:=lower_iso_b (d1:=dom_210) (r1:=roots_210) (T1:=gsh_210_1) [(dom_210,1)] (by decide +kernel) (lower_slice_b (T:=gsh_210_1) [(0x50005000000000005000500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_246_1:=0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa
def gzo_246_1:=0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00a800aa00aa00a80000
def gsh_246_1:=0x55005500550055005500550055005500550055005500540055005500540000
theorem lowS_zo_246_1_86:Lower true dzo_246_1 roots_246 gzo_246_1 7:=lower_iso_b (d1:=dom_246) (r1:=roots_246) (T1:=gsh_246_1) [(dom_246,1)] (by decide +kernel) (lower_slice_b (T:=gsh_246_1) [(0x55005500000000005500550000000000550055000000000055005500000000,0,32),(0x55005500550055005500550055005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_86)
def dzo_242_1:=0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a
def gzo_242_1:=0xa000a000a000a000a000a000a000a000a000a000a0008000a000a00080000
def gsh_242_1:=0x5000500050005000500050005000500050005000500040005000500040000
theorem lowS_zo_242_1_82:Lower true dzo_242_1 roots_242 gzo_242_1 6:=lower_iso_b (d1:=dom_242) (r1:=roots_242) (T1:=gsh_242_1) [(dom_242,1)] (by decide +kernel) (lower_slice_b (T:=gsh_242_1) [(0x5000500000000000500050000000000050005000000000005000500000000,0,32),(0x5000500050005000500050005000500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_244_1:=0x22002200220022002200220022002200220022002200220022002200220022
def gzo_244_1:=0x22002200220022002200220022002200220022002200200022002200200000
def gsh_244_1:=0x11001100110011001100110011001100110011001100100011001100100000
theorem lowS_zo_244_1_84:Lower true dzo_244_1 roots_244 gzo_244_1 6:=lower_iso_b (d1:=dom_244) (r1:=roots_244) (T1:=gsh_244_1) [(dom_244,1)] (by decide +kernel) (lower_slice_b (T:=gsh_244_1) [(0x11001100000000001100110000000000110011000000000011001100000000,0,32),(0x11001100110011001100110011001100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
namespace S_247
def pG:List (Nat×Nat):=[(1,33),(1,129),(2,18),(2,34),(2,66),(3,19),(3,35),(3,67),(3,131),(4,20),(4,68),(4,132),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,23),(7,39),(7,71),(7,135),(16,18),(16,20),(16,80),(16,144),(17,19),(17,21),(17,49),(17,81),(17,145),(32,33),(32,34),(32,96),(32,160),(36,37),(36,38),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,112),(48,176),(64,66),(64,68),(64,80),(64,96),(65,67),(65,69),(65,81),(65,97),(65,193),(128,129),(128,132),(128,144),(128,160),(130,131),(130,134),(130,146),(130,162),(130,194),(192,193),(192,194),(192,196),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_247.map (·&&&dom_247)
def gM:=goal_247&&&dom_247
def NN:Nat→Nat
|4=>10
|5=>35
|6=>103
|7=>258
|8=>246
|9=>105
|10=>12
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xe88eee337db5ca2952ec92a918d52088c158336228bfa18769
|5,0=>0xfd732f0b00ec204e8d34e8990e4429e341fe2046da512d4fa1d48e2c783dbd8c3b9e09acd6492e8d8f272834047a839755965097b4c4a1420613ed3d3eb91348fd31d5b2b1ee248ee242642093d1b29f19e2415f7f0cf0e
|6,0=>0xfe62ef253eee6a1ebf32da5b4d9117d604dd5043c7664c1079bd5bab9e09b8e45acd64ab185a9acea2fc49f5989da219d87598ef7901118e3c98df308748d86a02859f8852eb850e9843c3835d282f488168d7fee97f7fa7e2fe76ab375aa97577075638755967183e69945671ba652045c4295b7615b5aa5aaed59a565939258f465773e5485451ebf50a1d4f9f74f20a4c54349b1247b2947a183ec333dd0035f79357cd355543540134c1433c8532fd632c6d3273531c6e307b530742303f026521242642397f23866236e123051212271fea11e5f91c3751be8219e24180cd15a8e13917115700cec30ba48093cb089e9085780768d04b6202e6601f4201d42
|7,0=>0x53a835271d5219d51ebf512c5508165024c502075019d500e14fbc04f33b4ecc94e4524d9364d5184ccfc4c7474c7114b07a4afb64af6149a49492ed47786477464544744f3b43b824371f4316b42ee4407d63f3d23f30c3f1303e84b3e23d3dda23b63739eba398eb38dda385ca3724936aca366a4364223615635f2e34ee53415e33b1733aab32cc632a843204e308573067730492300552f2ea2ed162de602d0012cf2f2c7f02b9012a81b2a18529f8629d5a2903728ad92877c286622839326add2675526397262072359922014213df213cc208992020a1febe1f4cc1d57c1c88d1c4ce1ac6c19bcc198cd1983b1825a1751f16f81148b013a541350c133aa1325412aa612919124d311c0a11ab60c89d0be230ba480b86b0a22c092ea08cb5087c70862408578082a606b56068cd062fd058e60553b04dd303cc700196
|7,1=>0xe4ededf559dd68bdcea1d95e5d46b7d3990d3294ce2f6cd415c7705bf4b5bb149b9338b8fc0b5965b4ba6b34d8b2f4bafacaaec38aabc1a8609a8511a5731a3a40a347fa19f2a01f59ece99df2e9ce969ce079c5039a1eb98cd8975c197536971ba95cda92c638f4998e6138de498c7948b04f88928880ae857dd8457d83c91830e182f488203981d3580ce77fcc77f0e47e5087dd777daf97ba9679e2278a0378021758fc75638754c0743b1741f8739db738fc721a771dd2710d2701586e4cc6d6506cdec6a7386a4b1692bb68c1568c0068b81686d7685ad67c26676cd6725c671ba66b6c65a6c6594d654d2646a1641fd6362f62b1f6299f61d50606545f7175e4e95dfe75d98e5d7305c5785acc45a5df5a2b359a565989c5920a58f77584f15803d57abf56e7e569c55620f5590854d6054a9f54a8f54a5e5461a544e2
|7,2=>0xfe62efbda0
|8,0=>0x51aa8507574f6b54eec14e2594d44d4c8714b0a84ab064a00e49c614985e47a42475c34644c45f3e44860442a44332a42e47429c441ece416883f88f3f2f73f0cb3e34d3dc803d4f03c9f73c8fc3c85b3c6f63c2c83b8123b6493af1139ebf39a35390563900a38b893895e378c9350c034df53491231f7f31ddc3179530f8630d542fcab2ed802e2782df022de8e2c7802bade2b6fa2a99d2a24f2979228e6d284aa2771226ff824799244ba23c432288b220b6216a11fe371fbff1fae31f6891f4241eade1dbff1d1d21d08f1b4be1a7661a62b19b33199551984318b36188dc181b91763e169af1602d15e2a15b3114a6e137d3133aa12598118101119d10d040fabc0fa310f4d50f02a0cf400c9860b5600b3a40ab2909b7b0992c0972c094330914308a03081c00802106a60059e20279201629012a6010f2001d700135
|8,1=>0xfcf10fa248f9ecaf911bf8d8af86e9f638af34b3e4a25e1004dfa1ddaf8fd9c48d7917d485dd10cacd25bc80bac7502c694ac6259c2cc5b939eb1dd1adcc7adae4ad481ad10facca7abf6caabb1a9ec7a9191a8254a6fd4a67caa5fa5a3706a23d0a00f59efd89e92a9a1eb99c5a986319840f97f5397d0696e2d96652925759242c90b29904598f3ec8d7208d2738d1ff89cc9887e688004871f986c15833ef808fd7fcee7e0b57bed97b2837a8bc79d7a794ca78cb57850175e6475c49758a97412a7359971fa3717487118170871708236ed206d6506c6006bdf46bdc16b2be6ab4468ded6818f67f036725c66ba566b6665fd5650b863e386362f63518623785fc3d5ddf45dc015d9335c0d55a7ff57a15568d55504554c6d5470253c6a52d96529b351fc1
|9,0=>0xf033de39e1e2e9fe031adaa90d9b20d6743c6b3ac6820c5b6dc4747bc0d6b9126b7fe6b282da9ef4a63bba6193a3d7ca0be3989e19646c9572993ea093ab9912f08da728d96e8827687ac385d968157c7c6427c050785fa75c5f72a5471a346e6486a68e669cf631946229a608ac5d0ec5764d5635655a5c5294f4b95848c35453594503341b30403353e8553cdfd3b0dd37b9a367153557034a6b326fe30b15303192fe902fde62b78e27c4a273eb2488a22d592288b21f94217f21fe9c1bc011b362194df176941705916d2e16736164291327b10d6d0fad30f4940dd410d37d0b6c90b4670b1d90acbe0ac8f0903106344054eb02d7f02bf60280602040019af01756014e7
|10,0=>0xff5919ac029233b8898a7fd216aad44dd5f3ef7d346ae1950c17a110428f
|11,0=>0x3ef7d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000000000000000ff000000000000000000000000000000ff00ff00ff00000000ff00ff00ff00aa00ff00ff00ff00aa00ff00ff00ff000000aa00aa00000000000000000000ff000000000000000000000000000000ff00ff000000ff0000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc000000000000ff00000000000000ff000000000000000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000ff00ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000ff00ff00ff00f000ff00ff00ff00f000ff00ff00ff00f000f000f000f000f0ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000000000000000ff00000000000000ff000000000000000000ff000000ff0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0ff00ff00ff00cc00ff00ff00ff00cc00ff00ff00ff00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa
|0,1=>0xff000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00000f000f000f000f000f000f000f000f000f000f000f000f000f0000000f000055005500550055005500550055005500550055000000000055005500000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa0000000000aa00aa00000000000000000000aa00000000000000aa00000000000000aa00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff0000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000000000000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
|0,2=>0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa000000aa00aa00aa00005500550055005500550055005500550000000000000000005500550055000055005500000055005500550000005500550055000000550055005500000000000000000000ff00000000000000ff000000000000000000ff00ff00ff00000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0000330033003300330033003300330000003300330033003300330033003300000f000f000f000f000f000f000f000f00030003000300030003000300030000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00ff00ff00aa00aa00ff0000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00000000000000000000ff00000000000000ff00000000000000ff00000000000000000f0000000f000f000f0000000f000f000f0000000f000f000f0000000f000055005500550055005500550055005500550055005500550055005500550000330033003300330033003300330033003300330033003300330033003300000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff000033003300330033000000000000000000330033003300330033003300330000000000000000000000000000ff0000000000ff00000000000000ff00ff0000
|0,3=>0xff00ff00ff00ff00ff00ff00ff00ff00f000f000f000f000f000f000f000f055005500050005005500550005000500550055000500050055005500000000000000000000ff00000000000000ff00000000000000ff00ff000000ff000055005500550055005500550055005500550055005500550055005500ff0000ff00ff00ff00ff00ff000000ff000000ff00ff0000000000ff0000000000000f000f000f000f000f0005000f0005000f000f000f000f000f0005000f000055005500550055005500550055005500550055005500000055005500550000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00ff00ff000000000000000000000000ff000000000000000000ff0000000000ff00ff0000000000000000000000000000000000000000000000000000ff00ff00ff00005500550055005500550055005500550055005500ff00ff0055005500ff0000aa00aa000a000a00aa00aa000a000a00aa00aa000a000a00aa00aa000a0000aa00aa000000aa00aa00aa000000aa00aa00aa000000aa00aa00aa000000005500550055005500550055005500550011001100110011001100110011000055005500550055005500550055005500550055005500550055005500000000
|0,4=>0x55005500550055005500550055005500550055005500550055005500500050ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00ff00ff00ff00ccff00ff00cc00cc00ff00ff00cc00cc00ff00ff00cc00cc00ff00ff00cc00ccff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc00cc00cc00cc00cc0f000f000f000f000f000f000f000f000f000f000f000f000000000000000000000000000000000000000000000000ff00ff00ff000000ff00ff00ff0000ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aaff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000000000ff00ff00ff00cc00ff00ff00ff00cc00ff00ff00ff00cc00ff00ff00ff00cc55005500550055005500550055005500550055005500440055005500550044ff00ff00ff00ff00ff00ff0000000000ff000000ff000000ff000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff0000
|0,5=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa0000ff000000ff000000ff000000ff000000ff000000ff0000000000000000ff00ff00ff00ff00f000f000f000f000ff00ff00ff00ff00f000f000f000f0ff00ff00f000f000ff00ff00f000f000ff00ff00f000f000ff00ff00f000f00f000f000f000f000f000f000f000f000f000f000f000f000f000f00000000ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc33003300330000003300330033000000330033003300000033003300330000110011001100110011001100110000001100110011001100110011001100000000000000000000000000000000000000000000ff00ff0000000000ff0000ff00ff00ff00ff00ff00ff00ff00ff0033003300330000003300330033000033003300330033003300330033003300330033003300000033003300330000ff00ff000f000f00ff00ff000f000f00ff00ff000f000f00ff00ff000000000f000f000f000f000f000f000f000f000f000f000f000f000f000a000f000a0000000000000000ff00ff00ff0000000000000000000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000f000ff00ff00f000f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000f0
|0,6=>0xff00ff00ff00ff00ff00aa00ff00aa00ff00ff00ff00ff00ff00aa00ff00aaff00ff00ff00ff00ff00ff00ff00ff00ff00cc00ff00cc00ff00cc00ff00cc55005500550055005500550055000000550055005500550055005500550000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00ff00ff00aa00aa00ff00aaaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00fe00fe00aa00aa00fe00feaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00ff00ee00aa00aa00ff00eeff005500ff005500ff005500ff005500ff005500ff000000ff005500ff0000ff00ff00ff00ff005500550055005500ff00ff00ff00ff005500550000000055005500550055005500550055005500550055005400540055005500540054ff000000ff000000ff000000ff000000ff000000ff000000ff00ff000000005500550055005500550055005500550055005500ff00000055005500ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000f000f000f0ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000000055005500550055005500550055005500110011001100000011001100110000ff00ff00ff00ff00aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aa0000000000000000ff005500ff0055000000000000000000ff005500ff0000
|0,7=>0xff00ff00000000000000000000000000ff0000ff000000ff000000ff000000ff000000ff00ff00ff00ff00ff00ff00ff0000af00af00af00af00af00af00af00af00af00af00af00af00af00aa00af00aaaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00a000a000aa00aa00a000a0fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fcff000000ff000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff000000000000000000003300330033000000000000000000000033003300330000ff00ff00ff00ff00ff00ff00ff000000000000000000ff0000000000000000ff00ff00ff00ff00ff005500ff005500ff00ff00ff00ff00ff005500ff0000ff00ff00ff00ff00ff00ff00f000f000ff00ff00ff00ff00ff00ff00f000f0ff00ff00ff00ff00ff00ff00ff00aa00ff00ff00ff00ff00ff00ff00ff00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00ff00aaaa00aa00aa00aa00aa000000aa000000aa00aa00ff00ff00aa000000ff0000ff00ff000f000f00ff00ff000f000f00ff00ff000f000f00ff00ff000f00005500550055005500550055005500550055005500550055000000000000000000000000000000000000000000000000330033003300330033003300330000
|0,8=>0xff00ff0000000000ff00ff0000000000ff00ff00ff00cc00ff00ff00ff00cc00000000550055000000000055000000000000005500550000000000550000550055005500000055005500550000005500550055000000550055005500000000000000000000ff00aa00ff00aa000000000000000000ff00aa00ff00aaff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aaff00ff0000000000ff00ff00ff00aa00ff00ff0000000000ff00ff00ff00aa00000000000000000000000000000000ff00ff00ff00ff00f000f000f000f0ff00ff0000000000ff00ff0000000000ff00ff00ff00ff00ff00ff00f000f00000ff000000ff000000ff000000ff000000ff00000000000000ff00000000ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff00000000aa00aa00aa00aa00aa00aa00aa00aa000000000000000000aa00aa00aa0000ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff0000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa0000000000aa00aa000000aaff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff0000000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00fc00fc00fc00fc00fc00fc00fc00fcff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fc00fc00ff00ff00fc00fc
|0,9=>0xff000000ff000000ff0000000000000000000000000000ff000000ff0000000000000000000000ff0000000000000000000000005500550055000000000000000000000055005500550000ff00ff00fc00fc00ff00ff00fc00fc00ff00ff00fc00fc00ff00ff00fc00fc550055005500550055005500550055005500550055005500550000005500000000ff000000ff000000aa000000aa000000ff000000ff000000aa000000aa00000000000000000000000000000000ff00ff00ff00ff00ff00ff00000000f000f000f000f000f000f000f000f000ff00ff00ff00ff00ff00ff00f000f0fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00faaa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00aa00aa00aa55005500550055005500000055000000550055005500550055000000550000ff00ff00ff00ff00ff00ff00ff00ff00550055005500550055000000550000000000000000000000000000000000000f000f000f000f000f000f00000000000000000000000000000000000000000000ff000000ff000000aa000000aaff00ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa00000000000000000000000000000000ff00cc00ff00cc00ff00cc00ff00cc
|0,10=>0xff00ff0000000000ff00ff0000000000ff00cc0000000000ff00cc00000000ff00ff0000000000ff00ff0000000000fc00fc0000000000fc00fc00000000000000000000000000000000fc00fc00fc00fc00fc00fc00fc00fcff00ff0000000000ff00ff0000000000ff00ff00fc00fc00ff00ff00fc00fc0000000000000000000000000000000000000000ff00ff0000000000f000f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00ff00ff00aa00aa00000000ff00ff0000000000ff00aa0000000000ff00ff0000000000ff00aaff00ff00ff00ff00ff00ff00ff00ff000f000f000f000f000f000f00000000aa00aa00aa00aa00aa00aa00aa00aa00ff00ff00ff00ff00ff00aa00ff00aa0000000000000000ff00ff00ff00aa000000000000000000ff00ff00ff00aa0f000f000f000f000f000f00000000000f000f000f000f000f000f000000000000000000000000000000000000000000000000fc00fc0000000000fc00fc00000000000000000000000000000000ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff005500550055000000ff00ff00ff00ff0055005500550000ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee0000000000000000ff00ff00ff00ff000000000000000000ff000000ff0000
|0,11=>0x33003300330033003300330033003300330033000000000033003300000000ff003300ff003300ff003300ff003300ff003300ff000000ff003300ff000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000f000f000000000ff00ff0000000000ff00000000000000ff00ff0000000000ff000000000000ee00ee0000000000ee00ee0000000000ee00ee0000000000ee00ee55005500550055005500550000000000550055005500550055005500000000ff005500ff005500ff005500ff000000ff005500ff005500ff005500ff00000f000f000f000f000f000f000f000f000f000f00000000000f000f0000000000000000000000000000000000000000330033003300000033003300330000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00ff00ff00cc00cc5500550055005500550055005500550055005500440044005500550044004400000000fc00fc0000000000fc00fc0000000000fc00fc0000000000fc00fc0000000000000000ff00ff00ff00ff000000000000000000ff00ff0000000000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff00000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000ff005500ff005500ff005500ff005500ff005500ff005500ff000000ff0000
|0,12=>0xff00ff00ff00ff00ff00ff00aa00aa00ff00ff00ff00ff00ff00ff00aa00aa00000000000000000000000000000000fa00fa00fa00fa00fa00fa00fa00faff00ff00fa00fa00ff00ff00fa00fa00ff00ff00fa00fa00ff00ff00fa00fa33003300330033003300330033003300330000003300000033000000330000ff00ee00ff00ee00ff00ee00ff00ee00ff00ee00ff00ee00ff00ee00ff00ee00000000ff00cc0000000000ff00cc0000000000ff00cc0000000000ff00cc55005500550055005000500050005000550055005500550050005000500050330022003300220033002200330022003300220033002200330022003300225400540054005400540054005400540054005400540054005400540054005400000000fa00fa0000000000fa00fa0000000000fa00fa0000000000fa00fafe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe0000ee000000ee000000ee000000ee000000ee000000ee000000ee000000ee00000000000000000000000000000000ff00ff00ff00ff00aa00aa00aa00aa00000000ff00ff0000000000aa00aa0000000000ff00ff0000000000aa00aaaa00aa00aa00aa00aa00aa00aa00aa00aa00aa0088008800aa00aa00880088cc00cc00cc00cc00cc00cc00cc00cc00ff00ff00ff00cc00ff00ff00ff00cc
|0,13=>0xff00ff00ff00ff00fa00fa00fa00fa00ff00ff00ff00ff00fa00fa00fa00faff00ff00ee00ee00ff00ff00ee00ee00ff00ff00ee00ee00ff00ff00ee00ee32003200320032003200320032003200320032003200320032003200320032
|_,_=>0
def sP:Nat→Nat
|0=>0x908020b071204150201191409150201070f0908020b19120918050b000f1708050b00141610060201000415020100140e06020b00120908050b00130908020b001211040602010010060501000f090c020b0709080201070e03020b000908020b0d0a0c020b000a080201000908050100040602010704060501000403020100
|1=>0x1b120915020b0d0f0a08020b00120a150201000f090c020b001209150501000f0908020100120406020b0712100c020b07141008020107140406020b19121008020119141706050b000f0406020b00121008020100140908020b1a120e15050b00140406020100121008050100140915020b070f0415050b0714041502010714
|2=>0x15020b280f1410150227230f140406020b0013260908020b00121706020b000f120406020b00131209150b0025130f10150224230f141008050b0013141008020b0012142215020b001e141008020100131410150201000f140910150200210f11020b00200f14020b001f1e0f1410150b1d1c0f14161115020b1a130908020b
|3=>0xf141015022f2a0f14101502302a0f141008020b071214111008020b2f13110415020b2e141006020b2d0f1404150b00250f1410150201070f142c1015020b000f110915020b070f1008020b1912140415020100141018050b000f1417150b00250f1410150b1a2b0f1410150201190f1404150b002513141015002a290f1410
|4=>0x20b00121015020b190f1411350908020b000915020b1b0f12221015020b1a131015020b340f1410150200230f140415050b0012141015022f230f1410150230230f14041502010012142210020b001f1410150b331c0f140a15020b000f1209150201000f12110415020b07141115020b320f141015021b230f141015022a31
|5=>0x14161006020b00120415020b001214110908020b1a130415020100131410150239230f141115021a2a0f140915050b00130f0908020b001312113b020b00130915020b000f120915020b070f10150b1b3a0f141106020b27130f1015020b070f14101502392a0f1438371015020b001003020b000f1211020b00360f14160915
|6=>0x20b0012161015020b2f131008020100140415020b0712144015020b001e0f1015002a2b0f141006050b00130f0415020b1912140915020b070f1210153f0b3e130f0915020b190f1210150b241c0f1410150b003a0f14103d020b000f141715050b000f141708020b0012141015020b3c0f141015021d230f140415050b0013
|7=>0x130f10150b002b130f144710150b002b0f1410150b0025130f14441015020b430f141006020b001f130f1006020b00130f261015020b240f141142020b00130915020b1a0f12110908020b1b13100c020b00121411020b271f0f1410150501000f14100802010012141015002a1c0f141108020b1a13101500232b0f140406
|8=>0x111015020b430f140910150200230f14114d06024c000f1710150b002b0f141015020b3e0f4b1410150200210f141008020b001214111046020b000f1422100615020b001337351015020b000f044615020b000f14111008020b2f0f14110908020b001310150201000f1449090815020b480f16371015020b0014111706020b
|9=>0xf14100615024c00550f1115020b1a130f44411015024c000f4110150b002b0f14441015020b390f145410153f0b00130f10150b00530f1440100815020b0013090815020b001345111015020b2e0f14111015020b190f1440100615020b000f11221008020b0014501015020b4f0f14471015020b1a0f14411015020b000f12
|10=>0xb001310155d020b30131410150b5f001c0f141015020b2d0f5e1410155d0b005b13145c1715020b300f140915020b1b130f455c17150b005b0f140910150b001c130f100815020b1a13111015020b070f1411095a0200590f14101502002a580f141610150b001c0f141015020b1b570f140410150b002b0f14441015020056
|11=>0xb430f1410150201000f1214541015020b3e0f14110915020b000f12115a020b1a0f14100615020b39130f40101815020b000f1015020b300f5e14111015020b1d0f14221015020b1a0f14091008020b00135e16411015020b001337041015020b0014100615020b240f144710150b001c0f14411015020b1b130f1640101502
|12=>0x110915024c000f11520406020b001410155d0b005b0f14111008020b390f1411095a024c000f1015020b2d0f141715020b1b0f45141015020b620f141710150b001c0f1410150b61001c13145c0415020b300f145210081502002a140410150b001c1314106015020b1b0f14441115020b1a0f141115020b27130f14105a1502
|13=>0x106615020b000f14110915020b1b130f101815020b240f141652101502002a14401015020b00130f10150b00250f451447401015020b000f1015020b650f140915020b000f2614100815020b240f144110150b001c0f14110908020b48000f371015020b2e0f14111715020b270f14110415020b0012141015020b271f0f1444
|14=>0xb6c0f14106015020b000f141715020b300f45141015020b6b0f1440171015020b000f41221015020b001309100815020b1b131015020b6a0f14106915020b680f1440041015020b0013105a150200560f14161015020b0012145c17153f0b00130f11351008020b0014113b020b000f141015020b670f1416110915020b0013
|15=>0x411015020b000f7210150b001c0f1410150b001c0f7114501015020b300f14101502002a700f141015020b1b1f0f14101542020b00135010150b005b0f14106f150b001c0f14094615020b000f1435100615020b000f106e150200550f1410150200230f14101502006d2a0f14114a0406020b000f101815020b270f14101502
|16=>0x140415020b300f45141015020b000f781410150248002a0f14107715020b1b0f14761015020b4f0f1475101502002a0f141008150b00530f141015020b24130f141015020b190f14471015020b240f141015020b731b0f14111006020b000f1240411015020b000f0915020b001e130f1015020b430f14110908020b1a0f1438
|17=>0xf1410081502002a13141008020b001312141015020b000f12141015020b070f14631006020b00130f171015020b240f140415020b001e13141110150b002b0f14471015020b270f141015020100130f14100815020b1b0f1410081502002a791444111006024c000f171015020b4f0f141018150b00530f141015020b39550f
|18=>0x20b7c130f16101502002a79141015020b1d0f1416111006020b0013111715020b300f14041015020b4f0f141015020b301f0f141015020b000f26141006020b001f0f141015020b39590f145c09157b4c000f1006020b000f26147a1008020b000f145204101502002a1410150b001c0f45141015050b00130f141015020b32
|19=>0x15020b190f121411371008020b0014110415020b2f0f141046020b000f26141008020b000f261410150b001c1e0f14471015020b1b0f1410150b7d001c0f14107715020b000f1416101502002a13143810150200210f141015020b00730f140915020b000f1210150b0053130f1438110915020b000f111708020b0013141015
|20=>0x41351015020b000f101815020b1a130f1008150200230f141015020b070f121422101815020b0014161015020b300f147e1006020b000f144410150200550f1410153f0b005b130f1018020b001f0f141110060b001c0f141018020b000f2614114d15020b390f14101815020b300f140415020b0012141008020b001f0f1410
|21=>0x14110406020b001340091015020b000f091015020b00820f1610150200230f14221015020b001314116315020b000f14101581020b670f1422091015020b0013761015020b300f1438111006020b000f10157b020b670f144710020b001f0f14471015020b000f141018150200230f1404101502002a7914471015020b300f14
|22=>0x4c000f1015020b2f130f1015020b3e130f14840415020b000f14471015020b1d0f140410150200230f14411015020b1a130f1015020b830f145410155d0b001314101815020b1d0f141015020b1a570f1411350915020b000f411015020b650f14100815020b1d0f14110415020b390f1422171015020b0014801015020b670f
|23=>0x91015020b00130f76041015020b001314881015020b000f1447171015020b000f1441111015020b00130f16411015020b000f141015020b00860f14114d150200590f141015020b240f14114d060200590f14631008020b000f14371015020b850f1411351006020b000f110915020b1a130f171015020b1d0f144111105a02
|24=>0xf14091015020b1a130f8f1015020b000f14100615020b610013101815020b000f7114106f1815020b000f1410157b020b1a0f1404100615020b00131015020b008e0f14110415020b008d0f14111006024c0b000f1015020b270f14100815020b0013451441100615020b390f148a1015020b000f1476171015020b000f1441
|25=>0xf1449090815020b000f141015020b00930f1441171015020b000f141015020b00920f1491110415020b000f141018150b001c0f144111105a020b000f14111015020b006d0f14170915020b000f45140910157b024c000f1015020b681b0f141611108b020b000f14111018020b000f141008150b001c0f1447041015020b00
|26=>0x451410155d020b1b0f14981015020b000f14171015020b1a0f1416110915020b000f1411521006020b000f1475111015020b000f145c1015645d0b000f145c0415970b000f14104615020b000f45141015020b96000f14100615020b001e0f14114a0415020b000f145c0915020b00130f1015020b00940f1411106e5a020b00
|27=>0xb00130f4b10150b001c130f14101542020b000f145c1715020b000f1411105a024c000f14111015020b000f2614111015020b390f140910155d020b001391161015020b000f1441221015020b000f1409100815020b1b0f141015020b1b0f14111015020b000f1214371015020b000f145c1015640b000f14101815020b000f
|28=>0x9b0f14101815020b001e0f141015020b009a131409101564020b00130f1015020b00550f14091015020b001f0f141008020b00135e14111008020b48000f14631015020b00130f14100815020b001e0f14110915020b48000f1015020b00680f145c1015817b0b000f141006020b000f5e1444111015024c000f1409101502
|29=>0x20b000f141015020b00570f1411101806020b000f1476101564020b000f141015020b300f1452100815020b0014171015020b000f4b1416111015020b001314100815020b009e0f141015020b009d0f1410740815020b000f14041015020b00134b144e411015020b000f149c101581020b000f14101502002a0f141015020b
|30=>0x20b00130f841015020b000f141015640b000f4b141611101502002a0f14809c1015020b000f140915020b00130f451015020b009f0f1417101564020b000f14101806150b001c0f1404101564020b001314041015020b007f0f1410741815020b000f1411106e020b000f1411520415020b00144a100615020b000f4e106e15
|31=>0x114d06020b000f1411101808020b000f140415020b0013451411106f020b000f141015020b1a130f11105a0200590f141015020b00a40f141110a3020b000f1449101815020b000f14111015020b00a20f14114d1502a1000f141015020b001e130f1437521015020b000f141018020b000f5e1416111006020b000f14411015
|32=>0xf14751015020b000f1410a715020b000f14a61015020b000f141015020b00951314100615020b00550f145c10157b4c000f1447091015020b000f14501015020b000f14101808150b001c0f1447111015020b000f145010155d020b000f145c09155d0b000f14541015020b00130f141715020b000f45141015020b00a51314
|33=>0x15020b000f141015020b00ae0f14ac1015020b000f141015020b00ab0f1409100815020b001317100615020b00130faa100815020b000f1441111015020b2f0f141015020b000f12149c1015024c000f141015020b00a90f1438111015020b000f141015020b27130f14110915020b00130f100815020b1b0f141015020b00a8
|34=>0xf5c1015890b000f141015020b00b1131410b015020b000f14100815020b009b0f1410157b020b1b0f144e441015020b000f144d100615024c000f101806020b000f5e1441100615020b00130f110415020b0013141015020b001f0f14171015020b270f141015020b00af0f1411221015020b000f141015020b000f26145c99
|35=>0x541015020b000f4b14521015020b48000f14171015020b1b0f14101808020b000f5e14091015020b00130f5e1015024c00b40f144910a315020b000f144e111015020b000f14104615020b000f1411b315020b000f1441111015024c0b000f101815020b009b0f1441111008020b000f141015020b00b2130f091015020b1b13
|36=>0xb000f1491111008020b000f14471015020b000f14511015020b00130f1015020b00b8130f100615020b390f14171015020b000f5e1441111015020b390f141015020b00b70f145c0915024c0b000f105a15020b1a0f14111008020b008d0f147e1015020b000f1411106f08020b000f141015020bb50f14110415020b610014
|37=>0x4a100615020b000f10153b020b000f1404101502002a0f14401015020b000f140915020b000f45141015020b00bd0f141015020b00820f141115020b00bb0f14110415020b48000f1410b915020b000f1411351015020b000f1410155d0b000f4b14171015020b300f14411015020b00550f14801015020b000f145c17041502
|38=>0x1422100615020b000f1447100815020b000f141015020bc10f1416101815020b000f14100815020b001b0f145c10153f0b00130f50041015020b000f14c01015020b000f14490915020b480f41114d15020b000f141015020b00560f141015020b005b130f1409100815020b1a0f1410be15020b000f14111090020b000f1441
|39=>0x480f141015020b00b40f14171015020b00130f14100615020b00130f1015020b00b80f144910155d020b000f14091015020b00570f14111008020b00131449100815020b480f141015020b009e0f14100815020b1a0f1410157b97a10f1441101815020b000f148010157b020b000f141115020b00c20f1447101815020b000f
|40=>0x1015024c0b000f1015020b00c70f141015020b00c60f141015c57b020b000f141015020b00c40f144d1015024c000f14101502a14c000f145c1015020b00130f14108b1502a10b0f14491015020b610f14111008020b000f141015020bc3000f1416041015020b000f14106f0815020b000f14511015020b000f14101597020b
|41=>0xcc0f14aa1015020b000f1410159702a10b0f14109015020b000f141015020b1b0f1411521015020b000f141015020b00130f7114111015020b48000f1417041015020b000f1410cb15020b000f141015020b00ca0f141015020b00c90f141015020b00c20f1410157b024c000f141015020b00c80f1476041015020b000f1409
|42=>0xb000f1409100815020b000f144d10153f020b000f141015020b00590f14108b15020b610f145c0415020b000f14101564020b00130f149c10157b020b000f141015020b00130f4514cd1015020b000f141015020b000f5e14108b06020b000f141015020b00130f4b1449100615020b000f1410155d020b0013141015020b00
|43=>0x950f140410153f020b000f1417091015020b000f141015ce020b000f1410155d020b48000f14091015020b48000f1015a0020b000f144910157b020b000f14114d15020b000f14111015020b00130f140910157b020b000f1416111015020b000f141015020b00870f141015020b009a0f1449100815020b000f1411101502a1
|44=>0x15020b00bc0f141015020b001b0f14d11015020b000f1491111015020b000f14106e5a15020b000f145c1015024c0b000f141015020b00d00f14101815020b000f145c10155d0b000f144d101502a1000f141015020b00ba0f14091015020b1a0f1410157b970b000f14cf1015020b000f14111015020b61000f141015020b00
|45=>0x20b000f1444105a15020b000f141015020b000f7114106f15020b000f141015c5020b000f14491015020b480f141015020b1a0f1410061502a10b000f1404108b15020b000f14171015020b000f141015020b61001314041015020b001314761015020b000f141015020b5f000f14091015020b00130f101581020b000f1410
|46=>0xf14100815020b000f14100615020b000f14101597020b000f141015020b000f14108b15020b000f14105a15020b000f141015024c0b000f14491015020b000f141015d25d020b000f141015020b00b20f14091015020b1b0f1404100615020b000f14101564020b000f1409105a15020b000f144a1015020b000f1410180815
|47=>0x1015020b000f14091015020b000f141015020b00130f1410157b020b000f144d1015020b00
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x5aa0285011a80794032a0145007a8029400aa0005
|5,0=>0x3f981f0c0f260763039981c0c0da606a303398190c0c2605e302d98160c0aa6052302798130c0926046302198100c07a603a301b980d0c062602e3015980a0c04a6022300f98070c0326
|6,0=>0x15d38ad1855ae2a6714fb8a61c522e28a7141b89f1c4eae26e7133b8981c4b2e2527125b8911c47ae2367117b88a1c442e21a7109b8831c40ae1fe70fbb87c1c3d2e1e270edb8751c39ae1c670dfb86e1c362e1ab60d238675c32ce18f70c438605c2f4e17370b63859982bee15870a8b8529c286e13c709ab84b9c24ee120708cb8449c216e1047
|6,1=>0xf19c780c3b971d938eadc748e39d71cb38e3dc712c38271be30dd5c6dec36871b0b8d69c6a6e34c71a2b8cf9c66ee3307194b8c89c636e3147186b8c19c5fee2f87178b8ba9c5c6e2dc716ab8b39c58ee2c16
|7,0=>0x2dec16d60b5b05a582cec16560b1b058582bec15d60adb056582aec15560a9b0545829ec14d9ca5d0526828f4145a0a1d0506827f413da09dee4e7826fc135e099f04c87260412e2096104a8825041262092104888240411e208e104697230c116608a4e44b7221c10ee0867042b8211c1071c82ae40d8202c0ff607eb03ed81f2c0f7607ab03cd8
|7,1=>0x3d941eaa0f45079b73c9c1e2e0f07077c73ba41db20ecae75d83aac1d360e8ce73e839b41cba0e4d071e838b41c3dce10e700837c41bc20dd106e0836c41b420d9106c1735cc1ac60d5306a1834cc1a460d130681833cc19c60cd30661832d3994dcc970644731e418d20c590624830e418520c19060482fe417d20bd905e482eeb97560b9b05c58
|7,2=>0x4d4c26861334e99284c54260a12f6e97384b63a59212b9095484a642512127909348496ba496123b09158486c241611fce8f684774239a11bee8d78467c231e117f08b78457c229e113f08978447c221e10ff08778437c219e10bf08578427c211e107f08387418420a210410818840842025d00307f983f8c1fa60fc307d983e8c1f29cf8507ba8
|7,3=>0x5d2c2e76172b0b8d85c2c2df616eceb6e85b342d7a16ad0b4e85a3bacfe166f0b2f8593c2c7e162f0b0f8583c2bfe15f0eaf0857442b8215b10ad0856442b0215710ab0855442a8215310a90854442a0214f10a7085344298214b10a5085244290214710a3085144288214310a108504ba80613f309f184f4c278613b309d184e4c2706137309b18
|7,4=>0x176aebad8
|8,0=>0x6e94b72a1b850db996d84b69e5b40ed9796c7c361e1afd2d7686b74359a1abb2d5496a5cb50a5a750d319694c34825a2f2d0f8683c33fa59eb2ced86724b37219a72ccb86614b2e659612ca886504325e591f0c87863f4b1da18dd0c66862ecb15258990c44861e430ce58570c24760dcb04a58150c0195fc4afbe57cf0bde95eacaf3257890bbc8
|8,1=>0x7f7cbf9e1fbf0fd877e843f221f810fb797d74be9a1f3b2f9497c643e0e5ef70f7387b5c3d8a5eb32f5187a4c3d025e6f2f2e9792cbc725e290f0c878243bee5de70eea9770cbb69dda50ec997604bade5d5f0ea6974ecba525d172e84773e439ce5cd70e62972d439465c930e40971bcb8ba5c4d0e1e870acb8361c092dfb96f9c37ae1bc70ddb8
|8,2=>0x9043c80223ef31ee98f34477663a931cc88e1cc6ea636511aa88d0cc662631f318788bfc45de22df116788af4c55a229b3145889e4c4ce62571123888dc444e22153102887d443ca21d510e2886d44346619130bf985bc42be214f109e984b4423a210d107e883b441ba20cd105e882acc1362089303c8819cc0aa6043301988084c02220010ff88
|8,3=>0x279533c289dcccec6275313a279cccce426711137f99bb4cdb666ccf35d99aa4cd322687333b899a3ccae6647131a9988ccc26260312f8997844ba225c112d8896844b22258112b79957c4a9a653d12968946cca1624f932739935c498e24b7125389254c906647312318914c48826431120f9
|9,0=>0xaf1c576a6ba515ca8ae0cd6e62b6135a79acf4d65a2b1d15859abe4d5ce6ad535628aad4554a2a9335409a9bcd4be2a4f151f8a8b4d4366a0b14fd8a7ac53b629cb14de7a6acd332698734ba9a59452aa2945149a8a494522a290334798a38c51a628c134588a2845122287f34378a17c509e283f14169a06cd01627fb13f589f64cf9227b913d39
|9,1=>0x17369b9745c9a2e3b37158b864dc122df736f29b7545b8a2db516d28b65bdb0a6d7336b18b54c5a862d3316918b44c5a062cf316718b34c59826caf364e9b23458fa2c6d162e8b134587a2c2d160e8b02cd7f62be935eb9
|10,0=>0xbcb45e3a2f0d177e8bbb45dba2ecd175f7babc5d3e2e8f173f8
|11,0=>0x179e7
|_,_=>0
def wAt:=mkWire dB 211 248 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x140f45441021245055111303c510012440511113040550f144444c0f154444c11130084913110503d151042c490f1044c44140f454410b124444c101543c5100124444c101543c510b1243c4113110503d021244c5511130405510144543d1113040550f14408490f154444c0f14440550900040510b124543d111303c510f1042c49111303c51001244051111303c51
|1=>0xf14440191514450d513118503d0f1550400141145441101443c51151043c550b124444c101543c51001443c55001045041101343c514702c444d101551c0b13114503d15105180b15454404e0f144404d0f1444055141043c51150f42c49150f4444c101543c51150f440550f1444051151443c4113110503d1510504001114440550b124543d111303c51001244c44
|2=>0xf1444051001244c44140f4582f081043c5510084600b081451c0b1715450111006454511015424000f1444051111442c45151042041150f4dc03521443c460012c4c44140f51c53410f44019111445441510f42409141042421090004051111444c44140f454414e00c51110b1151c2f09084543d0b14454510b1045441380bd283d14118543d1113040550f144444e
|3=>0x1113040550f1452c41021383c51101444c44151042c55090005441141050403140f44019151451c53101842051470004c45140f42455090005041110f44451101551c03410f4401910184600b08144543d09154240314104505a08104543d1700c083d101343c511802c544d0f144404d0f1445c03090f440510900c3c51090f4405110144600b151343c51150f42400
|4=>0x8144600b15104543d1014451490f118544117000243d10144403d13110544117000243d101442c45151059041145d504031114454410f1542c551410454416300c4179151383c51090f424030056964510b11854411802c3c01151343c51021045c03140443c41160fc582f08104403d1802c544d0f1442400151045041170004c41140f454414e00d1051105a42c49
|5=>0x100644019151445c00131043c511700c243d1416850110f10444511015450410f144543d151b46c3d0900c4051041543c41110f44c44140f45441131043c51090804051151043c55110f44051101545d7b131043c511014440550f1451c03101842051160fc582f081051c531113440550f1450051141682041411ac24550900050411711c4055090f440514700c4061
|6=>0xf2a8582f081042c4515105400317024243d10145d00b180042051150f45c0314044592b0f1145441160bc20410f15455a11b0f42403101443c557402c6001081451c031113440554700c444d101543c51151444c441510450451614c3c45151343c510f15470411802c2051150f4600b151343c51090f4582f081043c550f1441018100f45451090f440514113c503d
|7=>0x13104503d151054003761441009410f440191014440090b144082d151e86043060f454510908c5041160bc583f041543c4102124444c101543c51630004179151383c51160bc20410f144543d0f154444c0f14444d713118503d1510400491113040550f1451c0317154243d10144544d0f1451c0b13114503d171545c00090f440510b124444c10154246b090004051
|8=>0x111442c41151045c03131043c510f1044c44140f454411416420410012c444c101543c514100050450f1045441111383c51111882051151043c5517154243d0900c40511802c2051150f455a11b0f4240310144582f081043c51150f5283d141185441150f440511113040550f145d00b18004544d13104503d51000fc41021443c51160bc20410f1145451101545c03
|9=>0xf1551c3f1113440550f1444099111383c510915450418000c25ed10144243d1014411fd04068403d151451c2f1018420512a0fc582f041545c551700c243d101444451131185441090003c51101451c2f10184205100124444c101543c51410fc183d100645c03041545011060483c41141145441101343c51131043c5115104600b060f454511118820510f1550403
|10=>0x101445c55090f44051141145441410004451101543c515400c412d0213841fd04068403d151451c001113440550f1451c2f17154501109154240010144015f090884051150f51c00101842051091545041470004061081450403141143c4115105043f090f4405110815ec51020b454510f104503d151051c53090844051150f55c51090884051150f51c2f141642041
|11=>0x1300c544d0f144200108144543d09000082d10144403d151443c514908800410f1543c410011854411510454510b1445c00090f440511310c3c51150f504031006454518c1062c3f001541051040243c41140f42455141043c51040243c41891045176020f45c55090f440511114440550f14444510f1145441870f4245714104442f0b10454410f11840550f1442400
|12=>0x151044051100243c51951442003150f45169101542c550f15400411410410ff0f104085109154243d10144198614154003d100f4004515104600b08144543d0b15450451510458030f11454411710c243d1014440510b144082d1b0f424031014454010f11454410814454410f154600b08144543d1715450110f1043c510900040511090568530b154003d151443c51
|13=>0x111383c514100c5045151044051140f4083d110043c4515104245514104543d0900c4051091ac2400101444c44140f45441145243c4615105745102104083d1310c3c510900c083d101440a65140483c41090f424001014440510f1145441151443c461510458010f11454415d1440841020f408010f1040841101383c51005e4544e0f1446043060f45451141183c41
|14=>0xb024582f081043c551800c2051150f4406208144543d0f1458457000f44051021343c51410bc2455141045c57090f440511315c3c51150f40051151043c555e104544e0f144406208144543d101540051101446c3d0900c4051147b408410b0246057060f45451140b42c45151044051021383c511802c544d0f1441018100f45451041443c410210454410b1442c55
|15=>0x101441812141543c4110134084d0f144600b060f45451100f4084d0f144101a15144600108144543d060b4505515104403d0f11854414114c40191514568510b154242210144543d060f45055151057441145d4083d1700c243d10144583f081043c55021383c51110f440550f144242310144014a0f1185441180042051150f4403d021383c510915450417b145ec41
|16=>0xf144100b100f43c51151442c41151042051151043c5510138403d0f1442001151043c55090003c51101442c550b1185441097b8082d101442053151043c55060f44001151443e350011854410b0042c41151046043151343c510f118544113154544e0f14454510f11454411114440550f1444281060fc5451024b4084e0f144582f0f11454417b1042c09101383c51
|17=>0x101543c51140b5ec410b025bc43080043c550f4a45046151045c00101343c511014440550f144240310144543d14a54100b0f1045801081043c5500a342053150f43e46108b400550800c3c51150f5042f100645451100242c51020b4242110144543d510f4240914104600b08144543d13114503d151059041145d4083d101440841020f4412d021383c5110138404d
|18=>0xf10455c5001383c511800c2051150f42403020b44051105a42c550b10454510b1446057060f45451140f44019151443c41140f454411715c243d101445c00090f440516e10d68510b155043f1411454411113840550f14410530f104084110819ec51020b6b4417b14c082d095d8083d1014450410f144543d1013454510f144543d09004405141000504515104444c
|19=>0x141044403151043c559915450120f1042001151043c55b600c242d10144403d15104003d021383c51110fc5441090f4240310144605708144543d14104544e0f14441ee0b144082d001042053150f451110b114544145154404e0f1445441090fc4051140b4504515104600308144543d1114454410f154401a151443c510f144240310145745302104083d140f41057
|20=>0xf1545c43090f44051106485175020f6f0510810c3c5510a1854410b0045441140043c4115ba410030f1044c46140f454416402c5175020f45c03090f4405109154504110815ec51020b410510f10408411100454410f154444d101543c513f10408510f1443c510902c50414100c401915144544e0f14504031411454415914c2c46151044051100242c51090002c55
|21=>0x20b44051106185441000f4406108144543d410fc401915144406108144543db6000242d10144402108144543d0900c4051150f40841021443c517614410090f105282d1411854411014400510010444510b1045441591442c46151045c0b101343c51150f4240010146fc55090bc4051145a840550b1550453100645451090804051150f4582f041543c41141682041
|22=>0xf1042c5110145ec03020b4425e02005ec01020b684570b004402d0b144502d0b00440090f14400550b0040041000f454410f1545186000f410550f1042001150f4240914104005102005ec430b024404d0f14454510f144240b141040041020f42422150f43c51151043c55150f4005100104242310144543d090004051150f4082d0b0040801060f440191514425ed
|23=>0xf400410f15454410b0044051150f408510b1042c4615104003d001543c4102104084d0f145ec410b024404e0f144425d02004544e0f144545100154084e0f144400115144503d020f4182f151442401101442c010200568530b1542403101443c4615104004e0f14450011510450110f10684550b004416a0b1557403020f58443000f42c51020b62c2f001541009
|24=>0x20f45185000f43c5110145ec51020b420430f15424031014684410b00400451510568510b15440090b1465c2f020042051150f40841020f42c410b00410030f104240010144082d020058441000f45441000f42003150f43c4102144243d101465c53020045001020f4005110144183f1514400410b0242c411510440550f144082d101443c45151042457141058457
|25=>0x101443c51020b42c41150f454510200400550b1542c51001057401020f4401a15144240310144403d151445175020f42c55141045046151042051150f441690b154004e0f1442001150f65c2d0200400510010424001014450550b004403d00154243d10144503d000f4403d0f1457441
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x84000000000000000000000000000000000000000220000000000000000004000000000000000000000000000000000000000000000
|6,0=>0xc84000000000000000000000000000000000000006220000000000005a8000000002850000000000002440000000000000000000000010200000000000000000000000000000001c4030800000000000000000000000000000004d400000000000000007a00000000000000000000000000000000c3
|6,1=>0xae8000000000000a4a00002720000092a118c21203e4000000001d2000006aa00001a0800000000000000000000000000000000000000cc40000000000000000000000
|7,0=>0x1d26398c0000e330000380c6e20d931ac63490679800019a4328c6410c6218482f905d9800017062d4c0000b2300002c085620a9300000000000000014e400005218a1313c627084c98963124823cc46188840000000042988140fe41f483d180000ec81c9037206a400001a0832986140ba800002d90000
|7,1=>0x5fccbe9000000000000bd1800000005e0800017532e645c0c00016c42d440000b3216420000581000015d32b4655ccaa1951329a80000a51946428484fcc9f093b327064d4c99192f325a400009591274248648108f111a40000459089210f321680000841904420263f507d18f731e683bd07618000
|7,2=>0x428684c507a20c30000828903220420000804cfea1fa300000000fc100003e887c10f711ea400007990f121de43b6675d0e9a000039e87348e519c643866700cde99bb236e86cd00001b1235c66accd3a000034c268ccd01800033880000cc9996332840000c98800031e8630cc58988300006110c110000
|7,3=>0xb0c40002bf45786ae895b22b3355e8aad1541aa53542800014f180000000a7094c9a9545246a3cd45a287450689fd13da278300009d8800000004e669c4936a26a34ce698d1301a5d34b469591299a50349c4930925124824888904d1ea23a346c88d09182000045888a891320000444887cd0da2174
|7,4=>0
|8,0=>0x6fc4decdbc1b7536e64dc0db69b6a36ce6d90db1135f36b86d64dab1b5336a06d34da51b48268a6d08d9f9b3c36726cd8d999b30365a6ca8d939b2436426c78d8d9b18362a6c48d879b0c36126c18d819b0035fa6be8d7b9af435e26bb8d759ae835ca6b88d6f9adc35b26b58d699ad0359a6b28d639ac43
|8,1=>0x86c70cce181c2d3854709ce121c21383c706ce0c1c1628267040e069c0a380e7010e0113ff37f86fe4dfb1bf337e24fb8df59be837ca6f8c9f01bdd37b46f5cdea1bd2279e6f349e51bc737886f089df9bbc37726ed8dd99bb0375a6ea8dd39ba437426e78dcd9b98372a6e48dc79b8c37126e18dc19b803
|8,2=>0x9e673c0e7714ec29d27398e719ce039ba7368e6b9cd439a27338e659cc8398a7308e5f9cbc397272d8e5a14b1395c72ace541ca53944727ce4e1c99392c724ce481c8d3914721ce421c8138fc71ece3c1c7538e471bce361c6938cc718ce301c5d38b4715ce2a1c51389c712ce241c45388470fce1e1c393
|8,3=>0x2c995903b1a7628ec39d843b0275f8ebd9d783aea75c8eb79d6c3ad27598eb19d603aba7568eab9d543aa27538ea59d483a8a7508e9f9d3c3a7274d8e999d303a5a74a8e939d243a44547ce8e1d193a2c744ce881d0d3a165420e829d0239fe73f0e7c9cf63
|9,0=>0xc265844b07960d2c165824b0396052c065804aff95fd2bf657e4afb95f52be657c4af795ed2bd657a4af395e52bc65784aef95dd2bb65764aeb95d52ba65744ae795cd2b965724ae395c52b865704adf95bd2b7656e4adb95b52b6656c4ad795ad2b5656a4ad395a52b465684acf959d2b365664acb95952
|9,1=>0x6652cc65984b2f965d2cb65964b2b96552ca65944b27964d2c965924b2396452c865904b1f963d2c7658e4b1b96352c6658c4b17962d2c5658a4b1396252c465884b0f961d2c365864b0b96152
|10,0=>0xce239c07378e6e1cda39b073588000cd439a47340e671
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x100000000000001c80000000000027000000000000470000000000008c0000000000010c00000000000210000000000004100000000000080000000000000d8000000000001a0000000000003200000000000062000000000000c0000000000001300000000000022000000000000400000000000005000000000000080000000000000e0000000000001a0000000000003000000000000058000000000000a000000000000100000000000001c0000000000003000000000000040000000000000600000000000008000000000000080000000000000
|1=>0x848000000000010080000000000200000000000002fe0000000000057c00000000000938000000000012200000000000230000000000004020000000000080000000000000df000000000001900000000000029c000000000005100000000000088000000000001060000000000020800000000000408000000000005f800000000000be0000000000016c000000000002b8000000000004f000000000000980000000000012000000000000238000000000004400000000000086000000000001080000000000020c000000000004100000000000081
|2=>0x84e20000000001067000000000020cd0000000000411000000000008204000000000102f800000000020480000000000400400000000008004000000000080c0000000000101700000000002008000000000040000000000000400000000000007ff80000000000eff00000000001d7e000000000033fc000000000065f80000000000caf0000000000195a0000000000303c00000000005df8000000000094c000000000011000000000000204000000000004040000000000080100000000001000000000000012bc000000000025700000000000480
|3=>0x1957e0000000003220800000000064050000000000c0ac00000000018144000000000300a800000000060070000000000acbf00000000014b7e00000000028138000000000502300000000008fbf00000000010f7e00000000021bfc0000000004127000000000081300000000001019c000000000203300000000004065000000000080c30000000001008e00000000020088000000000277f80000000004ebf000000000099fe000000000132fc000000000257f800000000048ff00000000008dfe00000000011428000000000215f80000000004274
|4=>0x40819fe0000000810110000000010007ef80000002000eff0000000400108000000002180008000000040865f80000000800400000000008a197e000000010432fc00000002026df8000000040419e0000000080807c00000001003afc0000000200047000000004000000000000040197e000000008012fc00000001001a6000000001f0cf400000000361968000000004c32f0000000008065f800000000808400000000010002000000000121310000000002426100000000040cff00000000050800000000000432fc000000000665f8000000000cc9f
|5=>0x10000004400000200000000000002020065f8000004040093e0000008080010000000101000000000002000416100000040000cb7000000480013900000008400221000000100404df000000200085bf00000040010068000000800136fc00000100026d780000020000fbf00000040001bbe000000800036fc0000010000018000000100000000000001082186c00000020080200000000400865f800000080004000000000e00100000000018002010000000280044200000002200fdf00000004401bbe0000000880337c000000110064f80000002040eff
|6=>0x400070d7e000008000a13080000100000203000002000004000000020107196e000004020a1210000008020021b80000100020080000002000219ee000004000432fc000008000065f800000842006dc000001084007b800000210003a7c00000420001ce800000820800040000010400129800000208000370000004100000200000080200cbf000001004011180000020080053800000401000470000008020000400000100400000000002000302e8000004000505d000000800040bb00000100001fbe00000200003afc00000400004460000008000008e
|7=>0x180000000200002000808088000040000235d8000044000001900000844001bbc000010081033fc000020100026e8000040040010b0000080001195e00001000010474000020000075f80000400000eaf00000800001bbe000010000032f8000020000008580000400000042000008000000600000100000000c0000200000000000003080204820000061002197e00000c001c0140000018001825b8000020802803000000410031d6e000008200432fc0000100420200000002008400800000040108000800000801028298000010020075f80000200040400
|8=>0x1880000193e00025080003efc000420000075f80008000004ebf00010000001d7e000180082023f8000300100065f80006001080dbf0000c00010197e000180002022f8000300000065f80004c00010cff0000880002197e00011000003afc00020100406df80004007000cbf0000800c0017fc000100100032fc00020000a865f80004000110cbf000080001e19fc000100002c32fc000104000045d00002021080dbf00004002101308000080000033f4000080000165f800010000000210000180002195e0000300004239c000060000000680000c0000000b
|9=>0x4d0000015d7e008210004032fc010420000065f80208000000ebf0041000000197e00800000013afc010000000075f802000000000830040000000004200405100043abc0080a200000058010104000000d0020000000997e002180100022f8004200104077f80084002080efd00108000001f7e002082000022e800410020004420008200400080c001040080001180020009800001000400100006de80068400000c37000d000000397e000b1020007afc0014204000f5b80028400001ebf0003180000197e0005a0000032fc000a00000065f0000c400000fbf
|10=>0x201000022197e040100085433fc080008041465f81000100050cff0200020000197e040000200e12f8080000401865f81000000170cfc020000000e1dfe040000000832fc060080000265f80c0100000400d0180004000002402825000013afc050401000065f80a0000020a6bb01018800001d7e02021080003afc04042100005df80808400000a3f01010040010976020200800032fc0400a0000251f8080040000000f0100004000197e01800000808084030000000005180318020000cbf0063001000397e00c600000032fc018000000200080300000000021
|11=>0x2003880002197e400400000432f8800480000965f90008c00000cbf2000000002197e320580000032fc584000009065f89100000000cbf1200000024197e22830000803afc413600001075f8821c400000ebf10400100001d3e204480000032fc404200204065e08082084000cbf1010400800197e200380000032fc400300300067e88004006080efe10008008101d7e200080100032fc400004000065f85208010000cbf0a010000021d7e100010c0202cfc104000009024202004000010cbf0260000001595e0482400006bafc084200400865f81009000010ebf
|12=>0x2200420000865fa2004002050cbf440000040801008800000000121100020040c865fa00000081b0cbc2a04000022197e540200004432fca00400800065f91110000100cbf2061002010197e404730000433fc808c40000067f90118800000cbf
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x4000000000000000000000000400000000002000000000000000000000000000
|6,0=>0xc00000001500002000b034080a000000800158006c000000000000000000000005c00000000000000005c00000000000000000000000b800000005000002a000000023000000000000001000000000000000000002038000000000000000000580000000000800000000000000000031
|7,0=>0x93000002401e00000c800020386000080f8001088000a40034010041e5b04000041a10808a601008084a0255240860a75084643f000808a571180150081e90402255c02004000101d8e28000090e541391c02002190c08430523804ba008340004000f49a400000000000faf804020101c02121080808e8000000a5a0801c04000517c1806000640e46050000400
|7,1=>0xd8001d1ba0c8407028e00807048001e0000060040801004e0050290010020001c00001e8095a0f2c1580e6a010b4040d013708602118107c0f1a808760004008140009005de401ebb47807000b8965c0016406040000004004608c0430000300621028b04800018100412038085cd822110002f0f8042400290080e00098004a02020002e0007005581f000454e00
|7,2=>0x90
|8,0=>0x3e346928f6cc34cb407c494f2bb63178e4789718b16d457298fb2d02519b6bc7138cd07c52c4926d02e809eafe60b97144c9c846972c41031890165092051fb2b15d8cb402ba1ee9013d2dafc03872fe2c494c97f215728cba91a9caeccbf9c831236c9e36844ae1d51e6a80433c51b588fbd8fe8059a89ad50825149a739dd21be4d601ae0ab638c1e2a14368a09cab
|8,1=>0x7261121389b3e2aa7a9815060789a2b775c65496c0a152e480d939ae7533ac49ece871a251008d89a12f3706316f3427cc20cf7641b12d0b2682d5d54bdd359aff7d9ed928aa0a6984646f4dcdc777cc59691b9c5f9c95a3d1d8924f52264de4f5ad921919318cde0b927e223a9450941e4ae7acea76fd6ea2cc1103f051371a67b4e52e7
|9,0=>0x17a3c3e8e96fae38502ebba54a7b8026cfe3c51bb2c231234e5e4cd7fa1cdabb0ac2a062f269027f0d44a74725e9db448a2878c23989f5e4aa129533921a6c2969ec46e1896960d9962b4d8ed478c14f6b7135edce06af9eb5add4fbbdf61157afe370f27acdd6d73da119aa2b2aacc6f90c619e10972
|10,0=>0x5013512a9331e2ce4ab0356ad78
|11,0=>0x4d
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 55 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_246 9 roots_246 ops++addP pm 1 dom_231 9 roots_231 ops++addP pm 2 dom_215 9 roots_215 ops++addP pm 3 dom_183 9 roots_183 ops++addP pm 4 dom_181 8 roots_181 ops++addP pm 5 dom_227 8 roots_227 ops++addP pm 6 dom_86 5 roots_86 ops++addP pm 7 dom_119 9 roots_119 ops++addP pm 8 dom_151 6 roots_151 ops++addP pm 9 dzo_86_1 5 roots_86 ops++addP pm 10 dom_245 9 roots_245 ops++addP pm 11 dom_243 9 roots_243 ops++addP pm 12 dom_212 5 roots_212 ops++addP pm 13 dom_102 5 roots_102 ops++addP pm 14 dom_167 6 roots_167 ops++addP pm 15 dom_103 6 roots_103 ops++addP pm 16 dzo_212_1 5 roots_212 ops++addP pm 17 dom_117 7 roots_117 ops++addP pm 18 dom_84 4 roots_84 ops++addP pm 19 dom_211 7 roots_211 ops++addP pm 20 dom_241 6 roots_241 ops++addP pm 21 dom_54 4 roots_54 ops++addP pm 22 dom_199 5 roots_199 ops++addP pm 23 dom_101 4 roots_101 ops++addP pm 24 dom_147 4 roots_147 ops++addP pm 25 dom_82 4 roots_82 ops++addP pm 26 dom_51 4 roots_51 ops++addP pm 27 dom_213 7 roots_213 ops++addP pm 28 dom_210 5 roots_210 ops++addP pm 29 dom_150 5 roots_150 ops++addP pm 30 dom_198 4 roots_198 ops++addP pm 31 dom_55 5 roots_55 ops++addP pm 32 dom_229 6 roots_229 ops++addP pm 33 dom_197 4 roots_197 ops++addP pm 34 dzo_214_1 6 roots_214 ops++addP pm 35 dom_118 7 roots_118 ops++addP pm 36 dom_230 6 roots_230 ops++addP pm 37 dom_179 6 roots_179 ops++addP pm 38 dzo_210_1 5 roots_210 ops++addP pm 39 dzo_246_1 7 roots_246 ops++addP pm 40 dzo_242_1 6 roots_242 ops++addP pm 41 dom_244 6 roots_244 ops++addP pm 42 dom_116 5 roots_116 ops++addP pm 43 dom_115 7 roots_115 ops++addP pm 44 dom_214 7 roots_214 ops++addP pm 45 dzo_118_1 6 roots_118 ops++addP pm 46 dom_166 4 roots_166 ops++addP pm 47 dom_182 6 roots_182 ops++addP pm 48 dzo_116_1 5 roots_116 ops++addP pm 49 dom_113 4 roots_113 ops++addP pm 50 dom_242 6 roots_242 ops++addP pm 51 dzo_114_1 5 roots_114 ops++addP pm 52 dzo_244_1 6 roots_244 ops++addP pm 53 dom_209 4 roots_209 ops++addP pm 54 dom_114 5 roots_114 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_247 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_86_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_212_1_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_214_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_210_1_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_zo_246_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_242_1_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_zo_118_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_zo_116_1_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_zo_114_1_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h52;exact cpcs (by decide +kernel) lowS_zo_244_1_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h53;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h54;exact cpcs (by decide +kernel) lowS_114 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_246 9 s (0,roots_246.map (·&&&dom_246)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_247 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_246 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_247==dom_247)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_247 gM v ys):RunD true dom_247 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_247 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 10 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 35 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 103 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 103 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 258 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 258 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 246 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 118 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 246 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 105 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 105 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 12 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_247 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_250_1:=0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def gzo_250_1:=0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a080a0a0a0a0a080a00
def gsh_250_1:=0x505050505050505050505050505050505050505050505040505050505040500
theorem lowS_zo_250_1_82:Lower true dzo_250_1 roots_250 gzo_250_1 7:=lower_iso_b (d1:=dom_250) (r1:=roots_250) (T1:=gsh_250_1) [(dom_250,1)] (by decide +kernel) (lower_slice_b (T:=gsh_250_1) [(0x500050005000500050005000500050005000500050005000500050005000500,0,8),(0x505050500000000050505050000000005050505000000000505050500000000,0,32),(0x505050505050505050505050505050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_249_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_249_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c0c0c0c0c0c0c0c0c0c0c0c0c0c0800
def gsh_249_2:=0x303030303030303030303030303030203030303030303030303030303030200
theorem lowS_zo_249_2_137:Lower true dzo_249_2 roots_249 gzo_249_2 7:=lower_iso_b (d1:=dom_249) (r1:=roots_249) (T1:=gsh_249_2) [(dom_249,2)] (by decide +kernel) (lower_slice_b (T:=gsh_249_2) [(0x303000003030000030300000303000003030000030300000303000003030000,0,16),(0x303030300000000030303030000000003030303000000000303030300000000,0,32),(0x303030303030303000000000000000003030303030303030000000000000000,0,64)] (by decide +kernel) lowS_137)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(16,18),(16,80),(16,144),(17,19),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,96),(32,160),(48,49),(48,50),(48,56),(48,112),(48,176),(64,66),(64,80),(64,96),(65,67),(65,73),(65,81),(65,97),(65,193),(72,73),(72,74),(72,88),(72,104),(72,200),(128,129),(128,136),(128,144),(128,160),(130,131),(130,138),(130,146),(130,162),(130,194),(192,193),(192,194),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1fffffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|9=>4
|10=>2
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0x501ea363680f6ef05b9c
|10,0=>0xc34df1497e
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0ef0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a00f000f000f000f000a000a000a000a000f000f000f000f000a000a000a000af0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0ce0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ef0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a302030203020302030203020302030203020302030203020302030203020302f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x7654310768543107654c31076d5431076543b1076a5931076543210
|_=>0
def sO:Nat→Nat→Nat
|9,0=>0x6210822008
|10,0=>0xa2208
|11,0=>0x307
|_,_=>0
def wAt:=mkWire dB 14 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x534c5594d15c8c5544d184d4d
|_=>0
def oO:Nat→Nat→Nat
|9,0=>0x62422202
|10,0=>0x9181
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x9ff5ff2ff1ff0ff000
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>0x49a
|10,0=>0x2c
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_235 10 roots_235 ops++addP pm 1 dom_123 10 roots_123 ops++addP pm 2 dom_219 10 roots_219 ops++addP pm 3 dom_250 9 roots_250 ops++addP pm 4 dom_243 9 roots_243 ops++addP pm 5 dom_249 9 roots_249 ops++addP pm 6 dom_187 9 roots_187 ops++addP pm 7 dom_185 8 roots_185 ops++addP pm 8 dzo_250_1 7 roots_250 ops++addP pm 9 dzo_249_2 7 roots_249 ops++addP pm 10 dom_186 6 roots_186 ops++addP pm 11 dom_242 6 roots_242 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_250_1_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_249_2_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_242 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_235 10 s (0,roots_235.map (·&&&dom_235)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_235 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 4 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 0 = true)
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
def isoMvS_223:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_223:Lower true dom_223 roots_223 goal_223 12:=lower_iso_b isoMvS_223 (by decide +kernel) lowS_127
def isoMvS_239:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_iso_b isoMvS_239 (by decide +kernel) lowS_191
def isoMvS_253:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_251
def isoMvS_254:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_247
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,28),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,18),(16,20),(16,80),(16,144),(17,19),(17,21),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,96),(32,160),(36,37),(36,38),(36,44),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,68),(64,80),(64,96),(65,67),(65,69),(65,73),(65,81),(65,97),(65,193),(72,73),(72,74),(72,76),(72,88),(72,104),(72,200),(128,129),(128,132),(128,136),(128,144),(128,160),(130,131),(130,134),(130,138),(130,146),(130,162),(130,194),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|12=>1
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|12,0=>0x8fd7c
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x86543210876543210
|_=>0
def sO:Nat→Nat→Nat
|12,0=>9
|13,0=>0x98
|_,_=>0
def wAt:=mkWire dB 9 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x185
|_=>0
def oO:Nat→Nat→Nat
|12,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0xff00
|_=>0
def pmB:Nat→Nat→Nat
|12,0=>1
|13,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_127 12 roots_127 ops++addP pm 2 dom_253 12 roots_253 ops++addP pm 3 dom_251 12 roots_251 ops++addP pm 4 dom_247 12 roots_247 ops++addP pm 5 dom_223 12 roots_223 ops++addP pm 6 dom_239 11 roots_239 ops++addP pm 7 dom_191 11 roots_191 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_191 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 1 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 1 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [7, 5] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.or, inputs := [8, 3] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.or, inputs := [9, 2] }, { op := GateOp.or, inputs := [9, 6] }, { op := GateOp.and, inputs := [2, 4] }, { op := GateOp.and, inputs := [11, 12] }, { op := GateOp.and, inputs := [0, 10] }, { op := GateOp.and, inputs := [8, 3] }, { op := GateOp.and, inputs := [13, 1] }, { op := GateOp.or, inputs := [14, 15] }, { op := GateOp.or, inputs := [19, 16] }, { op := GateOp.or, inputs := [20, 17] }, { op := GateOp.or, inputs := [21, 18] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_51542_aux

theorem PEqualNP.Outside.L_meta_51542 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_51542_aux.main
