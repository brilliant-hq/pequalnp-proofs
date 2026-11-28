import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_51648_aux
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
def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfefefafaeeccaa00fefefafaeeccaa00fefefafaeeccaa00fefefafaeeccaa00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffeeffeeffeeffeeaa00aa00aa00aa00ffeeffeeffeeffeeaa00aa00aa00aa00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_82 : Nat := 0x500050000000000050005
def goal_82 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_82 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffeeeeffffeeeecccc0000cccc0000ffffeeeeffffeeeecccc0000cccc0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xffffeeeeffffeeeecccc0000cccc0000ffffeeeeffffeeeecccc0000cccc0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffffaaffffffaaaa00aa00aa00aa00ffffffaaffffffaaaa00aa00aa00aa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffffccffffffcccccc0000cccc0000ffffffccffffffcccccc0000cccc0000
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffeeffffffeeeeccaa00eeccaa00ffffffeeffffffeeeeccaa00eeccaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xffffffccffffffcccccc0000cccc0000ffffffccffffffcccccc0000cccc0000
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xffffffeeffffffeeeeccaa00eeccaa00ffffffeeffffffeeeeccaa00eeccaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xeeeeeeeeeeeeeeeeaaaaaaaa00000000eeeeeeeeeeeeeeeeaaaaaaaa00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfafafafaaaaaaaaafafafafa00000000fafafafaaaaaaaaafafafafa00000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefeeeeeeeeefafafafa00000000fefefefeeeeeeeeefafafafa00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffaaffaaffaaffaaaaaaaaaaaa00aa00ffaaffaaffaaffaaaaaaaaaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeffeeffeeaaaaaaaaaa00aa00ffeeffeeffeeffeeaaaaaaaaaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffaffaaffaafafafafaaa00aa00fffafffaffaaffaafafafafaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffeffeeffeefafafafaaa00aa00fffefffeffeeffeefafafafaaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffeeeeeeeeaaaacccc0000ffffeeeeffffeeeeeeeeaaaacccc0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafaffffaaaafafafafa00000000fffffafaffffaaaafafafafa00000000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcffffccccfcfcf0f0cccc0000fffffcfcffffccccfcfcf0f0cccc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefeffffeeeefefefafacccc0000fffffefeffffeeeefefefafacccc0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffffaaaaaaaaaaaa00aa00ffffffaaffffffaaaaaaaaaaaa00aa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffffeeeeeeaaaaeeccaa00ffffffeeffffffeeeeeeaaaaeeccaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffaffffffaafafafafaaa00aa00fffffffaffffffaafafafafaaa00aa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcffffffccfcfcf0f0cccc0000fffffffcffffffccfcfcf0f0cccc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffeffffffeefefefafaeeccaa00fffffffeffffffeefefefafaeeccaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaa00aa00aa00aa00aa00aa00aa00aa00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfafafafafafafafafafafafafafafafaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfefefefefefefefefefefefefefefefeaa00aa00aa00aa00aa00aa00aa00aa00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_146 : Nat := 0x5000500000000000000000000000000050005
def goal_146 : Nat := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfccccc0000cccc0000cccc0000cccc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefecccc0000cccc0000cccc0000cccc0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeccaa00eeccaa00eeccaa00eeccaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffafafffffafafffffafafffffafaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffefefffffefefffffefefffffefeeeccaa00eeccaa00eeccaa00eeccaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

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

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaa00aa00aaaaaaaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeaaaaaaaaaa00aa00aaaaaaaaaa00aa00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffafafafafffffffffafafafafafafafaaa00aa00fafafafaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcf0f0f0f000000000f0f0f0f000000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffefefefefffffffffefefefefafafafaaa00aa00fafafafaaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffffaaaaffffffffffffaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffffffccccffffffffffffcccccccc0000cccc0000cccc0000cccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffeeeeffffffffffffeeeeeeeeaaaacccc0000eeeeaaaacccc0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f0f0f000000000f0f0f0f000000000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfcfcf0f0cccc0000fcfcf0f0cccc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffefefffffffffffffefefefefafacccc0000fefefafacccc0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffaaaaffffffffffffaaaaaaaaaaaaaa00aa00aaaaaaaaaa00aa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffeeeeffffffffffffeeeeeeeeaaaaeeccaa00eeeeaaaaeeccaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f0f0f000000000f0f0f0f000000000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffafafffffffffffffafafafafafaaa00aa00fafafafaaa00aa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfcfcf0f0cccc0000fcfcf0f0cccc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffefefffffffffffffefefefefafaeeccaa00fefefafaeeccaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfccccccccccccccccc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfefefefefefefefefefefefefefefefeeeeeeeeeeeeeeeee0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffaaffaaffaaffaaaaaaaaaaaaaaaaaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffccffccffccffccccccccccccccccccffccffccffccffcc0000000000000000
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeeeeeeeeeeeeeeeeeffeeffeeffeeffeeaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffafafafafafafafafaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffcfffcfffcfffcfcfcfcfcfcfcfcfcffccffccffccffcc0000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffefefefefefefefefeffeeffeeffeeffeeaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffccccffffccccffffccccffffccccffffccccffffcccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeecccc0000cccc0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcffffccccffffcccccccc0000cccc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefffffefefffffefeffffeeeeffffeeeecccc0000cccc0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffff00ffffff00ffff0000ffff0000ffffff00ffffff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffffaaaaffffaaaaffffffaaffffffaaaa00aa00aa00aa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffffccccffffccccffffffccffffffcccccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffeeeeffffeeeeffffffeeffffffeeeeccaa00eeccaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffff0fffffff0fffff0f0fffff0f0ffffff00ffffff000000000000000000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffafffffffafffffafafffffafaffffffaaffffffaaaa00aa00aa00aa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcfffffcfcfffffcfcffffffccffffffcccccc0000cccc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffffefefffffefeffffffeeffffffeeeeccaa00eeccaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffccccccccffffffffcccccccccccccccccccccccc0000000000000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaa00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffafafafafffffffffafafafafafafafaaaaaaaaafafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfcfcfcfcccccccccf0f0f0f000000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefefffffffffefefefefefefefeeeeeeeeefafafafa00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffaaaaaaaaffaaffaaffaaffaaaaaaaaaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffccccccccffccffccffccffcc0000000000000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffeeeeeeeeffeeffeeffeeffeeaaaaaaaaaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffff0fff0fffffffff0f0f0f0fff0fff0ff00ff00f0f0f0f000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffafffffffffafafafafffafffaffaaffaafafafafaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcfffffffffcfcfcfcfffcfffcffccffccf0f0f0f000000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffffffffefefefefffefffeffeeffeefafafafaaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffff0000ffffffffffff0000ffff0000ffff00000000000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffaaaaffffffffffffaaaaffffaaaaffffaaaaaaaaaaaa00000000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffccccffffffffffffccccffffccccffffcccccccc0000cccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffffffffffeeeeffffeeeeffffeeeeeeeeaaaacccc0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffafafffffffffffffafafffffafaffffaaaafafafafa00000000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfffffcfcffffccccfcfcf0f0cccc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffffffffffefefffffefeffffeeeefefefafacccc0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffff00ffffffffffff0000ffffff00ffffff000000000000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffffffffaaaaffffffaaffffffaaaaaaaaaaaa00aa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffffffffccccffffffccffffffcccccc0000cccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffffeeeeffffffeeffffffeeeeeeaaaaeeccaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffff0fffffffffffff0f0fffffff0ffffff00f0f0f0f000000000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffffffffafafffffffaffffffaafafafafaaa00aa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffffffffcfcfffffffcffffffccfcfcf0f0cccc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffffffffefefffffffeffffffeefefefafaeeccaa00
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
def isoMvS_82:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_82:Lower true dom_82 roots_82 goal_82 4:=lower_iso_b isoMvS_82 (by decide +kernel) lowS_73
def isoMvS_146:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_146:Lower true dom_146 roots_146 goal_146 4:=lower_iso_b isoMvS_146 (by decide +kernel) lowS_73
def isoMvS_164:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_164:Lower true dom_164 roots_164 goal_164 4:=lower_iso_b isoMvS_164 (by decide +kernel) lowS_73
namespace S_45
def pG:List (Nat×Nat):=[(1,9),(1,33),(4,36),(5,13),(5,37),(8,9),(12,13),(12,44),(32,33),(32,36),(40,41),(40,44)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_45.map (·&&&dom_45)
def gM:=goal_45&&&dom_45
def NN:Nat→Nat
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x9bf42
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccc0000000330000003300c0c00000c0c222200002222
|_,_=>0
def sP:Nat→Nat
|0=>0xe4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|_,_=>0
def wAt:=mkWire dB 4 46 0x3fffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_45 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_45 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_45==dom_45)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_45 gM v ys):RunD true dom_45 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_45 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_45 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_45 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_45 roots_45 goal_45 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_45
theorem lowS_45:Lower true dom_45 roots_45 goal_45 4:=S_45.noCircuit
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_slice_b [(0xc0c0000000000000c0c,64,66)] (by decide +kernel) lowS_73
theorem lowS_165:Lower true dom_165 roots_165 goal_165 5:=lower_slice_b [(0x220000002200000000000000000000002200000022,32,33)] (by decide +kernel) lowS_164
def isoMvS_83:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_75
def isoMvS_89:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_75
def isoMvS_90:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_75
def isoMvS_99:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 4:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_45
def isoMvS_101:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 4:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_45
def isoMvS_105:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_75
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 4:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_45
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 4:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_45
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_75
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_75
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_75
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 5:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_75
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_75
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_75
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_75
def isoMvS_198:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 4:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_45
def isoMvS_201:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_75
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 4:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_45
def isoMvS_210:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_165
def isoMvS_216:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 4:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_45
def isoMvS_226:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 4:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_45
def isoMvS_240:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_240:Lower true dom_240 roots_240 goal_240 4:=lower_iso_b isoMvS_240 (by decide +kernel) lowS_45
namespace S_91
def pG:List (Nat×Nat):=[(1,9),(1,65),(2,18),(2,66),(3,11),(3,19),(3,67),(8,9),(8,72),(10,11),(10,26),(10,74),(16,18),(16,80),(17,19),(17,25),(17,81),(24,25),(24,26),(24,88),(64,65),(64,66),(64,72),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_91.map (·&&&dom_91)
def gM:=goal_91&&&dom_91
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x9ec7
|4,0=>0x225e11f29a1d8c01a82f
|5,0=>0x9160d3a2c03767c32bd81653a146d30d1b70a87705038023d8
|6,0=>0x9f8ac8c6bd1b01319c44
|7,0=>0x9f8ac
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x505050500000000040404040000000000000000f0c0f0cf0c0f0c000000000f0c0f0cf0f0f0f000000000c0c0c0c30303030000000003030202f0f0f0f000000000f000f00c0c0c0c000000000c0c0c0cf0f0f00000000000000000030300030000000003030000f0f0000000000000f0f0000f0f0f0c000000000c0c0c0cf0f0f0f0000000000000000f0f0f0f000000000f0f0000f000f00000000000f000f00f0f0e0e000000000c0c0c0ca0a0a0a000000000a0a0a0a
|0,1=>0x505000000000000000030303030000000003030000e0e0e0e000000000e0e0e0ee0e0e0e000000000000000000f000f0000000000000000b0b0b0b000000000a0a0a0a0000f0f0000000000000c0cf0f0f0f000000000e0e0e0e
|_,_=>0
def sP:Nat→Nat
|0=>0x1849010c248086689202184c480861240499849012e6102c430920250ca48093309320104c4822430a09010c2481e433849010cd130043080b21949020c201c861140418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b48584cf19b330654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 24 92 0xfffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x489491112a90492332491601491491
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x6100513212000001
|6,0=>0x918171
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0x3ff7be705cc286080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x53162004
|6,0=>0x7a98
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_90 5 roots_90 ops++addP pm 1 dom_82 4 roots_82 ops++addP pm 2 dom_73 4 roots_73 ops++addP pm 3 dom_83 5 roots_83 ops++addP pm 4 dom_89 5 roots_89 ops++addP pm 5 dom_75 5 roots_75 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_91 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_75 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_90 5 s (0,roots_90.map (·&&&dom_90)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_91 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_90 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_91==dom_91)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_91 gM v ys):RunD true dom_91 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_91 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_91 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_91 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_91 roots_91 goal_91 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_91
theorem lowS_91:Lower true dom_91 roots_91 goal_91 8:=S_91.noCircuit
theorem lowS_103:Lower true dom_103 roots_103 goal_103 5:=lower_slice_b [(0xcc000000cc000000cc000000cc,64,66)] (by decide +kernel) lowS_101
theorem lowS_107:Lower true dom_107 roots_107 goal_107 6:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c,64,66)] (by decide +kernel) lowS_105
def dzo_105_4:=0x3030000030300000303000003030
def gzo_105_4:=0x3030000030200000303000002000
def gsh_105_4:=0x303000003020000030300000200
theorem lowS_zo_105_4_73:Lower true dzo_105_4 roots_105 gzo_105_4 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_4) [(dom_105,4)] (by decide +kernel) (lower_slice_b (T:=gsh_105_4) [(0x303000000000000030300000000,0,32)] (by decide +kernel) lowS_73)
namespace S_109
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(4,36),(5,13),(5,37),(5,69),(8,9),(8,72),(12,13),(12,44),(12,76),(32,33),(32,36),(40,41),(40,44),(40,104),(64,65),(64,72),(68,69),(68,76),(68,100),(96,97),(96,100),(96,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_109.map (·&&&dom_109)
def gM:=goal_109&&&dom_109
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x7cc9d448ee
|5,0=>0xdff7e1422f12cde
|6,0=>0xf22e7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccc0000cccc0000cc000000cc03322000033220000332200003322cc000000cc000000cc000000cc0002200000022000000220000002200cc000000cc000000880000008b333000000000000333300000000c0c00000c0c00000c0c00000c0c2222000022220000222200002222cc000000cc000000880000008803333000033330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x473204973204873204732604325043210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 110 0x3fffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x9f
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
addP pm 0 dom_105 5 roots_105 ops++addP pm 1 dom_101 4 roots_101 ops++addP pm 2 dzo_105_4 5 roots_105 ops++addP pm 3 dom_45 4 roots_45 ops++addP pm 4 dom_73 4 roots_73 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_109 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_105_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_73 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_105 5 s (0,roots_105.map (·&&&dom_105)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_109 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_105 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_109==dom_109)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_109 gM v ys):RunD true dom_109 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_109 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
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
theorem lowS_118:Lower true dom_118 roots_118 goal_118 6:=lower_slice_b [(0x500050005000500050005000500050,32,36),(0x550055000000000055005500000000,4,36)] (by decide +kernel) lowS_82
theorem lowS_143:Lower true dom_143 roots_143 goal_143 5:=lower_slice_b [(0xcccc0000000000000000000000000000cccc,128,130)] (by decide +kernel) lowS_141
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_slice_b [(0xaa00aa00000000000000000000000000aa00aa,128,129)] (by decide +kernel) lowS_150
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_slice_b [(0xaa000000aa0000000000000000000000aa000000aa,32,33)] (by decide +kernel) lowS_166
def dzo_165_8:=0x33000000330000000000000000000000330000003300
def gzo_165_8:=0x33000000320000000000000000000000320000002200
def gsh_165_8:=0x330000003200000000000000000000003200000022
theorem lowS_zo_165_8_164:Lower true dzo_165_8 roots_165 gzo_165_8 5:=lower_iso_b (d1:=dom_165) (r1:=roots_165) (T1:=gsh_165_8) [(dom_165,8)] (by decide +kernel) (lower_slice_b (T:=gsh_165_8) [(0x220000002200000000000000000000002200000022,0,1)] (by decide +kernel) lowS_164)
namespace S_173
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(4,36),(4,132),(5,13),(5,37),(5,133),(8,9),(12,13),(12,44),(12,140),(32,33),(32,36),(32,160),(40,41),(40,44),(40,168),(128,129),(128,132),(128,160),(136,137),(136,140),(136,168)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_173.map (·&&&dom_173)
def gM:=goal_173&&&dom_173
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x6986e
|5,0=>0xe5356
|6,0=>0x4866c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x33330000333300000000000000000000333300000000c0c00000c0c000000000000000000000c0c00000c0c33330000000000000000000000000000333300000000cc000000cc0000000000000000000000cc000000cc0222200002222000000000000000000002222000022220c0c00000c0c000000000000000000000c0c000000033330000333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8ea1a3a84688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 174 0x3fffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_169 5 roots_169 ops++addP pm 1 dom_141 4 roots_141 ops++addP pm 2 dzo_165_8 5 roots_165 ops++addP pm 3 dom_165 5 roots_165 ops++addP pm 4 dom_164 4 roots_164 ops++addP pm 5 dom_45 4 roots_45 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_173 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_165_8_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_45 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_169 5 s (0,roots_169.map (·&&&dom_169)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_173 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_169 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_173==dom_173)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_173 gM v ys):RunD true dom_173 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_173 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_173 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_173 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_173 roots_173 goal_173 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_173
theorem lowS_173:Lower true dom_173 roots_173 goal_173 7:=S_173.noCircuit
theorem lowS_199:Lower true dom_199 roots_199 goal_199 5:=lower_slice_b [(0xaa00000000000000aa00000000000000aa00000000000000aa,64,65)] (by decide +kernel) lowS_198
theorem lowS_203:Lower true dom_203 roots_203 goal_203 6:=lower_slice_b [(0xc0c0000000000000c0c0000000000000c0c0000000000000c0c,64,66)] (by decide +kernel) lowS_201
theorem lowS_211:Lower true dom_211 roots_211 goal_211 6:=lower_slice_b [(0xa000a00000000000a000a00000000000a000a00000000000a000a,64,65)] (by decide +kernel) lowS_210
def isoMvS_115:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_109
def isoMvS_117:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 5:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_103
def isoMvS_121:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 6:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_107
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 7:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_109
def isoMvS_157:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 5:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_143
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 6:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_107
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 8:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_91
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 8:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_91
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 6:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_107
def isoMvS_205:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 7:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_109
def isoMvS_206:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 5:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_103
def isoMvS_214:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 7:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_173
def isoMvS_217:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 6:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_203
def isoMvS_218:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 7:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_173
def isoMvS_220:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 5:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_103
def isoMvS_227:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 6:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_203
def isoMvS_229:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 7:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_173
def isoMvS_230:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 7:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_109
def isoMvS_233:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_91
def isoMvS_234:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 5:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_103
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 6:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_118
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 6:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_203
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 7:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_173
def isoMvS_248:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 5:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_103
theorem lowS_63:Lower true dom_63 roots_63 goal_63 6:=lower_slice_b [(0xcccccccccccccccc,16,18),(0xffff0000ffff0000,2,18)] (by decide +kernel) lowS_45
theorem lowS_111:Lower true dom_111 roots_111 goal_111 8:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc,64,66)] (by decide +kernel) lowS_109
theorem lowS_119:Lower true dom_119 roots_119 goal_119 8:=lower_slice_b [(0xf000f000f000f000f000f000f000f0,32,36)] (by decide +kernel) lowS_115
theorem lowS_123:Lower true dom_123 roots_123 goal_123 9:=lower_slice_b [(0xf0f0f0f000000000f0f0f0f00000000,1,33)] (by decide +kernel) lowS_91
theorem lowS_126:Lower true dom_126 roots_126 goal_126 7:=lower_slice_b [(0x50505050505050505050505050505050,32,36),(0x55555555000000005555555500000000,4,36)] (by decide +kernel) lowS_90
theorem lowS_159:Lower true dom_159 roots_159 goal_159 8:=lower_slice_b [(0xf0f0f0f0000000000000000000000000f0f0f0f0,128,132)] (by decide +kernel) lowS_155
theorem lowS_175:Lower true dom_175 roots_175 goal_175 8:=lower_slice_b [(0xcccc0000cccc00000000000000000000cccc0000cccc,128,130)] (by decide +kernel) lowS_173
theorem lowS_183:Lower true dom_183 roots_183 goal_183 9:=lower_slice_b [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa,32,33)] (by decide +kernel) lowS_182
theorem lowS_207:Lower true dom_207 roots_207 goal_207 8:=lower_slice_b [(0xcccc000000000000cccc000000000000cccc000000000000cccc,64,66)] (by decide +kernel) lowS_205
theorem lowS_215:Lower true dom_215 roots_215 goal_215 8:=lower_slice_b [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,64,65)] (by decide +kernel) lowS_214
theorem lowS_219:Lower true dom_219 roots_219 goal_219 9:=lower_slice_b [(0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000,1,129)] (by decide +kernel) lowS_91
theorem lowS_222:Lower true dom_222 roots_222 goal_222 8:=lower_slice_b [(0x50505050000000005050505000000000505050500000000050505050,128,132)] (by decide +kernel) lowS_218
def dzo_167_64:=0xff000000ff0000000000000000000000ff000000ff0000000000000000
def gzo_167_64:=0xff000000fe0000000000000000000000fe000000ee0000000000000000
def gsh_167_64:=0xff000000fe0000000000000000000000fe000000ee
theorem lowS_zo_167_64_164:Lower true dzo_167_64 roots_167 gzo_167_64 6:=lower_iso_b (d1:=dom_167) (r1:=roots_167) (T1:=gsh_167_64) [(dom_167,64)] (by decide +kernel) (lower_slice_b (T:=gsh_167_64) [(0xaa000000aa0000000000000000000000aa000000aa,0,1),(0xcc000000cc0000000000000000000000cc000000cc,0,2)] (by decide +kernel) lowS_164)
namespace S_231
def pG:List (Nat×Nat):=[(1,33),(1,65),(1,129),(2,66),(2,130),(3,35),(3,67),(3,131),(4,36),(4,132),(5,37),(5,69),(5,133),(6,38),(6,70),(6,134),(7,39),(7,71),(7,135),(32,33),(32,36),(32,160),(34,35),(34,38),(34,98),(34,162),(64,65),(64,66),(68,69),(68,70),(68,100),(68,196),(96,97),(96,98),(96,100),(96,224),(128,129),(128,130),(128,132),(128,160),(192,193),(192,194),(192,196),(192,224)]
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
|4,0=>0xcc53fbebcf751284dd1b0c8e2
|5,0=>0xf52f4f3a17e5c04d445bca7a3bb3259eb229b8ee7cf656fe606f139661a85e263543e73995e
|6,0=>0xfd6cffc45ffb9c0fb398f6a0ef3a17e040ad8374ccfe0c2a83c1d70b623eb0457af5b9a4ca8972b1909d5815537950e7782676a2d71e636c5b66053d5b02358a694fdb34a1f83d00f2f1f825645210dd1ce6d19f42091c406117057d5
|7,0=>0xaff18a4ca8905bc87c1f867c4628fe4b903460fb3818b2d269
|8,0=>0x9aff0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000ff000000f0000000ff000000f0f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0ff000000ff000000ff000000ff000000ff000000ff000000000000000000000000ff00000000000000ff000000ff00000000000000ff00000000aa000000aa000000aa000000aa000000aa000000aa000000aa000000aa000000000f000000000000000f0000000f000000000000000f00000000ff000000ff000000ff000000ff000000ff00000000000000ff00000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000ccff000000aa000000ff000000aa000000aa000000aa000000aa000000aa0f0000000f0000000f0000000f0000000f000000000000000f00000000ff00000000000000ff00000000000000ff00000000000000ff00000000fe000000fe000000fe000000fe000000fe000000ee000000fe000000eefa000000fa000000fa000000fa000000fa000000aa000000fa000000aaff000000ff0000000000000000000000ff000000ff0000000000000000ff000000ff000000ff000000ff00000000000000000000000000000000
|0,1=>0xff000000ff000000ff000000ff000000ff000000f0000000ff000000f000000000ff0000000000000000000000ff000000ff0000000000000000f0000000f0000000f0000000f0000000ff000000f0000000ff000000f0ff000000ff00000000000000ff000000ff000000ff0000000000000000ff000000ff000000ff00000000000000ff000000ff0000000000000000f0000000f0000000f0000000f0000000f000000000000000f00000000000000000000000000000000000000000ff000000ff0000000000000000ff0000000f000000ff0000000f000000ff00000000000000ff000000000f000000000000000f000000000000000f000000000000000f00000000ff000000f0000000ff000000f0000000f0000000f0000000f0000000f0ff000000f0000000ff000000f0000000ff000000f0000000ff000000f0ff000000ff000000ff000000ff000000f0000000f0000000f0000000f000000000000000000000000000000000ff00000000000000ff0000000000000000ff00000000000000ff00000000000000000000000000000000ff000000ff000000ff000000ff0000000f000000000000000f000000000f0000000f0000000f0000000f00000000000000000000000000000000
|0,2=>0xf000000000000000f0000000f0000000f0000000f0000000f0f000000000000000f000000000000000ff00000000000000ff00000000ff000000ff0000000f0000000f000000ff000000ff0000000000000000ff000000000000000000000000000000ff000000ff0000000000000000000000000000000000000000000000000f000000000000000f00000000ff000000cc000000ff000000cc000000cc000000cc000000cc000000cc
|_,_=>0
def sP:Nat→Nat
|0=>0x1ca0402046872810133472814883471811072850402072970502040870401021c10041ca1590041ca14c0181ca5c100858728120b3472815485072812cd1ca0441ca4414081ca1413ce10d1ca30b1ca2412c72850481ca2412071850440c2040
|1=>0x10d1ca8c010d1ca88010d1c60402043472814044cd1ca64010d1ca8410041ca5c10102043472990043602810044cd1ca30010d1ca44100810d1ca3007c434728100434729e01810d1ca04074434728100811434728110d1ca70010d1ca6c0116
|2=>0x10d1ca5c100434728c00450d1ca04054434728100810728504011a1ca04020d1ca04f54450728100434729730010728504020d1ca5c101510d1ca30055334728100434728504054834728100494728100490d1ca04038434728100810d1ca040
|3=>0x43472810044cd1ca04020434728100434728101010d1ca0403c434728101210d1ca640
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a94c8c5e62c314d49ac47620b0f146cc30615a89583ec196
|6,0=>0x15e7ac3549a96f4479f34dde60f297913c6de2ad0e783bc01df4cf4677339ddc0ed97693b2dd8acbe75bbac1d52ea364e3a55d1ce8864131f18eae6f6
|7,0=>0x344f9b7ca3e35f0cf806bcbdcdad8f657
|8,0=>0x1a96
|_,_=>0
def wAt:=mkWire dB 38 232 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x4031004d021000402040c4370404d0110d440120d040110004010404837100440104044031004d3f10004430504d02052c40228f440010044011cf440004fc4001004149100813d1000d3d1000402100ca3d100040168a4834100440134f440010053491008403
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xa3000000007300000000430003100c0000000
|6,0=>0x301b8ac2002b1a4a819c661002518ca2100000809e2709b100000001a16080000000001620000054532448f2000d2
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xfafe9eef7bde76bca709c04cc304a022c8218051140421003b088200680e00c0200400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x10001140000c4718000
|6,0=>0x643c460c0e601d8d03ab39352002e2902813000f49c451
|7,0=>0x35abef77cdb19
|8,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_230 7 roots_230 ops++addP pm 1 dom_99 4 roots_99 ops++addP pm 2 dom_198 4 roots_198 ops++addP pm 3 dom_229 7 roots_229 ops++addP pm 4 dom_163 5 roots_163 ops++addP pm 5 dom_227 6 roots_227 ops++addP pm 6 dom_103 5 roots_103 ops++addP pm 7 dom_199 5 roots_199 ops++addP pm 8 dzo_167_64 6 roots_167 ops++addP pm 9 dom_167 6 roots_167 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_231 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_167_64_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_167 _ g hchk
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
theorem lowS_235:Lower true dom_235 roots_235 goal_235 9:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c,64,66)] (by decide +kernel) lowS_233
def dzo_73_4:=0x30300000000000003030
def gzo_73_4:=0x30200000000000002000
def gsh_73_4:=0x3020000000000000200
theorem lowS_zo_73_4_73:Lower true dzo_73_4 roots_73 gzo_73_4 4:=lower_iso_b (d1:=dom_73) (r1:=roots_73) (T1:=gsh_73_4) [(dom_73,4)] (by decide +kernel) (lower_slice_b (T:=gsh_73_4) [] (by decide +kernel) lowS_73)
def dzo_229_8:=0x330000003300000033000000330000003300000033000000330000003300
def gzo_229_8:=0x330000003300000033000000320000003300000033000000320000002200
def gsh_229_8:=0x3300000033000000330000003200000033000000330000003200000022
theorem lowS_zo_229_8_164:Lower true dzo_229_8 roots_229 gzo_229_8 6:=lower_iso_b (d1:=dom_229) (r1:=roots_229) (T1:=gsh_229_8) [(dom_229,8)] (by decide +kernel) (lower_slice_b (T:=gsh_229_8) [(0x2200000022000000220000002200000022000000220000002200000022,0,1),(0x3300000033000000000000000000000033000000330000000000000000,0,64)] (by decide +kernel) lowS_164)
def dzo_233_4:=0x303000003030000030300000303000003030000030300000303000003030
def gzo_233_4:=0x303000003030000030300000303000003030000030200000303000002000
def gsh_233_4:=0x30300000303000003030000030300000303000003020000030300000200
theorem lowS_zo_233_4_73:Lower true dzo_233_4 roots_233 gzo_233_4 6:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_4) [(dom_233,4)] (by decide +kernel) (lower_slice_b (T:=gsh_233_4) [(0x30300000000000003030000000000000303000000000000030300000000,0,32),(0x30300000303000003030000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_73)
def dzo_172_64:=0x111100001111000000000000000000001111000011110000000000000000
def gzo_172_64:=0x111100001110000000000000000000001110000011000000000000000000
def gsh_172_64:=0x11110000111000000000000000000000111000001100
theorem lowS_zo_172_64_164:Lower true dzo_172_64 roots_172 gzo_172_64 5:=lower_iso_b (d1:=dom_172) (r1:=roots_172) (T1:=gsh_172_64) [(dom_172,64)] (by decide +kernel) (lower_slice_b (T:=gsh_172_64) [(0x11000000110000000000000000000000110000001100,0,8)] (by decide +kernel) lowS_164)
def dzo_228_8:=0x110000001100000011000000110000001100000011000000110000001100
def gzo_228_8:=0x110000001100000011000000100000001100000011000000100000000000
def gsh_228_8:=0x1100000011000000110000001000000011000000110000001000000000
theorem lowS_zo_228_8_164:Lower true dzo_228_8 roots_228 gzo_228_8 5:=lower_iso_b (d1:=dom_228) (r1:=roots_228) (T1:=gsh_228_8) [(dom_228,8)] (by decide +kernel) (lower_slice_b (T:=gsh_228_8) [(0x1100000011000000000000000000000011000000110000000000000000,0,64)] (by decide +kernel) lowS_164)
def dzo_201_4:=0x3030000000000000303000000000000030300000000000003030
def gzo_201_4:=0x3030000000000000303000000000000030200000000000002000
def gsh_201_4:=0x303000000000000030300000000000003020000000000000200
theorem lowS_zo_201_4_73:Lower true dzo_201_4 roots_201 gzo_201_4 5:=lower_iso_b (d1:=dom_201) (r1:=roots_201) (T1:=gsh_201_4) [(dom_201,4)] (by decide +kernel) (lower_slice_b (T:=gsh_201_4) [(0x303000000000000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_73)
def dzo_173_64:=0x333300003333000000000000000000003333000033330000000000000000
def gzo_173_64:=0x333300003332000000000000000000003332000033220000000000000000
def gsh_173_64:=0x33330000333200000000000000000000333200003322
theorem lowS_zo_173_64_164:Lower true dzo_173_64 roots_173 gzo_173_64 6:=lower_iso_b (d1:=dom_173) (r1:=roots_173) (T1:=gsh_173_64) [(dom_173,64)] (by decide +kernel) (lower_slice_b (T:=gsh_173_64) [(0x22220000222200000000000000000000222200002222,0,1),(0x33000000330000000000000000000000330000003300,0,8)] (by decide +kernel) lowS_164)
namespace S_237
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(4,36),(4,132),(5,13),(5,37),(5,69),(5,133),(8,9),(8,72),(12,13),(12,44),(12,76),(12,140),(32,33),(32,36),(32,160),(40,41),(40,44),(40,104),(40,168),(64,65),(64,72),(68,69),(68,76),(68,100),(68,196),(96,97),(96,100),(96,104),(96,224),(128,129),(128,132),(128,160),(136,137),(136,140),(136,168),(136,200),(192,193),(192,196),(192,200),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_237.map (·&&&dom_237)
def gM:=goal_237&&&dom_237
def NN:Nat→Nat
|5=>4
|6=>15
|7=>24
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x7a4e16a2106013d3d1b9
|6,0=>0xf6a72d8713c219ba63818d5c383eaf70a9e387402ca28187be15f1010a150927c0309502031
|7,0=>0xc795cbb175b78d7ae4c2a1cd1a13728f65a790e2625ca5fc484e86d441ad36d6e30e332ef352ec622ea75239d921aa21617712af6122ea11eaf0c29b
|8,0=>0xe2017c30fbbd1589427e5a8794e2f643d29087fd
|9,0=>0xf0cad
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccc0000cccc0000cccc0000cccc0000008800000088000000880000008b32200003322000033220000332200003322000033220000332200003322cccc0000cccc0000cccc0000cccc0000cccc000000000000cccc0000000000000003333000000000000333300000000000000220000000000000022cc880000cc8800000000000000000000cc880000cc88000000000000000000000000000000000000000000000003333000022220000333300002222c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c0000000033330000000000003333000000000000222200000000000022220c0c00000c0c00000c0c00000c0c00000c0c0000000000000c0c0000000003300000033000000220000002200000033000000330000002200000022cccc000000000000cccc000000000000cccc000000000000cccc00000003300000033000000330000003300000033000000330000003300000033000c0c00000c0c00008c8c00008c8c00000c0c0000000000008c8c0000888a22200002222000022220000222200002222000022220000222200002222cccc0000cccc00000000000000000000cccc0000cccc000000000000000333300003333000033330000333300000000000000000000000000000000
|0,1=>0xcccc000000000000cccc000000000000cccc000088880000cccc0000888b3330000333300003333000000000000333300003333000033330000000000000000000000000000000000000000cccc0000cccc0000cccc0000000333300003333000022220000222200003333000033330000222200002222cc000000cc0000008800000088000000cc000000cc0000008800000088000000000000000000000000000000000222200002222000022220000222200000000000000008888000088880000000000000000000088880000888b333000000000000333300002222000033330000000000003333000022228c8c00008c8c00008c8c00008c8c00008c8c0000888800008c8c0000888800000000000000033220000332200000000000000000000332200003322cccc0000cccc0000cccc0000cccc0000cccc000000880000cccc0000008b33300003333000033000000330000003333000033330000330000003300cccc0000cccc0000cccc0000cccc0000cccc000088880000cccc0000888b33300002222000033330000222200003333000022220000333300002222cccc0000cccc0000cccc0000cccc0000888800008888000088880000888802200000022000000220000002200000022000000220000002200000022
|0,2=>0x333300003333000033330000333300003300000033000000330000003300c0c80000c0c80000c0c80000c0c80000c0c80000c0c80000c0c80000c0c80000000000000000000000000000000000000002222000000000000222200000000888800000000000088880000000000008888000000000000888b03000003232000030300000323200003030000032320000303000003232c8c80000c8c80000c8c80000c8c80000c8c80000c8c80000c8c80000c8cb33300003333000033330000333300003333000033000000333300003300
|_,_=>0
def sP:Nat→Nat
|0=>0x511708101228d10908148d1094411440874010053840870403455842420121090880405451090810121094480401541021c101310908804048d10944204d1442423c134510908b00510908c0401440872c02842422011421c60401440c2040
|1=>0x24204048a14424204048510944101314424204048512104014424290100512208100512168100558424200d1442424010201442420404d21442420407c510908101d14424204034538424204048d1090810052426c101214425a040605109081
|2=>0x510908100512108100538424204048510908100510909a040166109081005504242040345109081005109099040485109442040144087040144942040485121081005109088040345504
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x9303180cc006
|6,0=>0x1e58e4e6c632b979caee50724b909c76e34716b899c3ee187
|7,0=>0x8f4461a24d0b7823bf21e90ed7733b819b2ed3666b31d97f0b875842a5d44e9a849ba3590ce7f7
|8,0=>0xabb541e92f4279dbcd1e5af267
|9,0=>0x15d6
|_,_=>0
def wAt:=mkWire dB 39 238 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x854d0a140498d085c909080ce070844501084cd1114052010854569080c07a045421114045010855c1008142030855915081c501480c21514042010854d271404213349c5011404e07084511708542013504501084d1170804d271405115445c20114042010855001084c5013810211
|1=>0x9090844215080c4011014501081c2010854d271404941084c909085511708045011015203085420108552010854909
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x885011d3346608a99231e6348590830a60c801800
|7,0=>0xa253ca694b29251ca29432824fc9e93b2724dc9a9332624bc9692b25249c929232
|8,0=>0xb43646c0d71ac3546a0d31
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x68be0d1740efb81d77031aa05d5c0abb8157502aae051d4092b810550102001d9c03b280565004ee0091c010180080000ce001980023000240003a00040000380005000080000c000100000
|1=>0x21a3ec001d4a8ba80074cefb8b8f713bee1d1d438aa85175
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0xc2514c610508818d2c31c0
|7,0=>0x2db91c5e629069d65d9623df3998684a0496
|8,0=>0x8e96187a7556
|9,0=>0x14
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_233 8 roots_233 ops++addP pm 1 dzo_73_4 4 roots_73 ops++addP pm 2 dom_205 7 roots_205 ops++addP pm 3 dzo_229_8 6 roots_229 ops++addP pm 4 dom_229 7 roots_229 ops++addP pm 5 dom_236 6 roots_236 ops++addP pm 6 dom_109 7 roots_109 ops++addP pm 7 dzo_233_4 6 roots_233 ops++addP pm 8 dzo_172_64 5 roots_172 ops++addP pm 9 dom_73 4 roots_73 ops++addP pm 10 dzo_228_8 5 roots_228 ops++addP pm 11 dzo_201_4 5 roots_201 ops++addP pm 12 dom_173 7 roots_173 ops++addP pm 13 dzo_165_8 5 roots_165 ops++addP pm 14 dzo_173_64 6 roots_173 ops++addP pm 15 dzo_105_4 5 roots_105 ops++addP pm 16 dom_105 5 roots_105 ops++addP pm 17 dom_165 5 roots_165 ops++addP pm 18 dom_164 4 roots_164 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_237 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_73_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_229_8_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_233_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_172_64_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_228_8_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_201_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_165_8_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_173_64_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_105_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_164 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_233 8 s (0,roots_233.map (·&&&dom_233)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_237 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_233 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_237==dom_237)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_237 gM v ys):RunD true dom_237 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_237 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 15 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_237 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_237 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_237 roots_237 goal_237 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_237
theorem lowS_237:Lower true dom_237 roots_237 goal_237 10:=S_237.noCircuit
def isoMvS_125:List (Nat×Nat):=[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_125:Lower true dom_125 roots_125 goal_125 8:=lower_iso_b isoMvS_125 (by decide +kernel) lowS_111
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_123
def isoMvS_189:List (Nat×Nat):=[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 8:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_175
def isoMvS_221:List (Nat×Nat):=[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 8:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_207
def isoMvS_238:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 8:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_119
def isoMvS_243:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_219
def isoMvS_245:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 9:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_231
def isoMvS_246:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_237
def isoMvS_249:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 9:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_235
def isoMvS_250:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 8:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_222
def isoMvS_252:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccccccccccccccccccc,126),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 8:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_119
def dzo_47_16:=0xffff0000ffff0000
def gzo_47_16:=0xfefe0000eecc0000
def gsh_47_16:=0xfefe0000eecc
theorem lowS_zo_47_16_45:Lower true dzo_47_16 roots_47 gzo_47_16 5:=lower_iso_b (d1:=dom_47) (r1:=roots_47) (T1:=gsh_47_16) [(dom_47,16)] (by decide +kernel) (lower_slice_b (T:=gsh_47_16) [(0xcccc0000cccc,0,2)] (by decide +kernel) lowS_45)
def dzo_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_123_4:=0xf0f0f0f0f0f0f0e0f0f0f0f0e0c0a000
def gsh_123_4:=0xf0f0f0f0f0f0f0e0f0f0f0f0e0c0a00
theorem lowS_zo_123_4_91:Lower true dzo_123_4 roots_123 gzo_123_4 9:=lower_iso_b (d1:=dom_123) (r1:=roots_123) (T1:=gsh_123_4) [(dom_123,4)] (by decide +kernel) (lower_slice_b (T:=gsh_123_4) [(0xf0f0f0f000000000f0f0f0f00000000,0,32)] (by decide +kernel) lowS_91)
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000ffff0000fefe0000eecc0000
def gsh_111_16:=0xffff0000ffff0000fefe0000eecc
theorem lowS_zo_111_16_45:Lower true dzo_111_16 roots_111 gzo_111_16 6:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xcccc0000cccc0000cccc0000cccc,0,2),(0xffff0000ffff0000000000000000,0,64)] (by decide +kernel) lowS_45)
def dzo_125_2:=0xcccccccccccccccccccccccccccccccc
def gzo_125_2:=0xccccccccccccccccccccc8c8cccc8800
def gsh_125_2:=0x33333333333333333333323233332200
theorem lowS_zo_125_2_45:Lower true dzo_125_2 roots_125 gzo_125_2 6:=lower_iso_b (d1:=dom_125) (r1:=roots_125) (T1:=gsh_125_2) [(dom_125,2)] (by decide +kernel) (lower_slice_b (T:=gsh_125_2) [(0x33330000333300003333000033330000,0,16),(0x33333333333333330000000000000000,0,64)] (by decide +kernel) lowS_45)
def dzo_61_2:=0xcccccccccccccccc
def gzo_61_2:=0xccccc8c8cccc8800
def gsh_61_2:=0x3333323233332200
theorem lowS_zo_61_2_45:Lower true dzo_61_2 roots_61 gzo_61_2 5:=lower_iso_b (d1:=dom_61) (r1:=roots_61) (T1:=gsh_61_2) [(dom_61,2)] (by decide +kernel) (lower_slice_b (T:=gsh_61_2) [(0x3333000033330000,0,16)] (by decide +kernel) lowS_45)
def dzo_94_32:=0x55555555000000005555555500000000
def gzo_94_32:=0x55555554000000005454505000000000
def gsh_94_32:=0x555555540000000054545050
theorem lowS_zo_94_32_90:Lower true dzo_94_32 roots_94 gzo_94_32 6:=lower_iso_b (d1:=dom_94) (r1:=roots_94) (T1:=gsh_94_32) [(dom_94,32)] (by decide +kernel) (lower_slice_b (T:=gsh_94_32) [(0x505050500000000050505050,0,4)] (by decide +kernel) lowS_90)
def dzo_109_16:=0x33330000333300003333000033330000
def gzo_109_16:=0x33330000333300003232000022000000
def gsh_109_16:=0x3333000033330000323200002200
theorem lowS_zo_109_16_45:Lower true dzo_109_16 roots_109 gzo_109_16 5:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_16) [(dom_109,16)] (by decide +kernel) (lower_slice_b (T:=gsh_109_16) [(0x3333000033330000000000000000,0,64)] (by decide +kernel) lowS_45)
def dzo_109_2:=0xcccc0000cccc0000cccc0000cccc
def gzo_109_2:=0xcccc0000cccc0000c8c800008800
def gsh_109_2:=0x3333000033330000323200002200
theorem lowS_zo_109_2_45:Lower true dzo_109_2 roots_109 gzo_109_2 5:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_2) [(dom_109,2)] (by decide +kernel) (lower_slice_b (T:=gsh_109_2) [(0x3333000033330000000000000000,0,64)] (by decide +kernel) lowS_45)
def dzo_95_32:=0xffffffff00000000ffffffff00000000
def gzo_95_32:=0xfffffffe00000000fefefafa00000000
def gsh_95_32:=0xfffffffe00000000fefefafa
theorem lowS_zo_95_32_90:Lower true dzo_95_32 roots_95 gzo_95_32 7:=lower_iso_b (d1:=dom_95) (r1:=roots_95) (T1:=gsh_95_32) [(dom_95,32)] (by decide +kernel) (lower_slice_b (T:=gsh_95_32) [(0xaaaaaaaa00000000aaaaaaaa,0,1),(0xf0f0f0f000000000f0f0f0f0,0,4)] (by decide +kernel) lowS_90)
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,18),(2,66),(3,11),(3,19),(3,35),(3,67),(4,36),(5,13),(5,37),(5,69),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,72),(10,11),(10,26),(10,74),(12,13),(12,44),(12,76),(14,15),(14,30),(14,46),(14,78),(16,18),(16,80),(17,19),(17,25),(17,49),(17,81),(20,22),(20,52),(20,84),(21,23),(21,29),(21,53),(21,85),(24,25),(24,26),(24,88),(28,29),(28,30),(28,60),(28,92),(32,33),(32,36),(34,35),(34,38),(34,50),(34,98),(40,41),(40,44),(40,104),(42,43),(42,46),(42,58),(42,106),(48,49),(48,50),(48,52),(48,112),(56,57),(56,58),(56,60),(56,120),(64,65),(64,66),(64,72),(64,80),(68,69),(68,70),(68,76),(68,84),(68,100),(96,97),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|5=>7
|6=>69
|7=>169
|8=>104
|9=>13
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xc545189e1e7fdfe7e152641d44e2d615416
|6,0=>0xf61adf32f3f00b9cdc9dcb969c928ac7c0cc5838c5243b7c64b0e27af3e1adabb96ac9964ec93ca6929d18ed4c8c5cf8b6f9897a78666b857ec835817e0af792fa78d9a765ed745637434a7306172f706febf6f0636e6a46d0be64c2661c705f23e5ca8552e5d516f950b414fd904e2d6471cd408953415c339ac3314132f2a2ad1b2743a2668e1e9a61c73f1c5fd1672615416130230d4ba0cf740cc510af960729f03fc4038cd036ee02ea3
|7,0=>0x9be0794b5993cfd93c7f92d568e5928dd278d2338cef48c65186092859018416f82d158168080f9780987806b17f9e37f9a47e6237ce977ab39799dc797a8781e17754f769f375a5b74b657465b7435773329729a4722a07148a6ff3e6febf6fc7b6f0636dc096b0b36b0a06a8fe66fde651e46406263eef63b146204e617ad612ae5e6c95e3165c7e45b6d75b0e95a4ba5989457a49564b3552ed526a4524f3501154fc114e52a4e0234da814c1724a73d4a2b3494d14920a47b7143b7c435b44308140eee406d13f16e3e5da3d98f3ba973b9aa3b65b3ab0439f3036a8d3627134a46339a332d9f2f6db2eac02ea462de0c2b5822b298295c4286d82795625d7c25b50255cf254b6233c72188e201071f0d31ec0c1e49b1c4761ae2716f7d1695d1658115dd5154b30f8f10f5690ee700aa5207c3f02db202d7b02a3e01203
|7,1=>0xfd5a0fc9fef7fbaf502bea12be62dfe4ed9e0a75dbea7db144da8abd785cd3f14d2755d11d3d05b4cf292ce5d2cb969ca998c7518c7418c5838c32f2bff6dbda35b9ca0b9634b588fb0451adabbab02eaaec8a90bda8254a369ea3469a2a199e6e49e4f69c1ce
|8,0=>0xf0603ea12be9001e7237e3487e301be0a75db21dd96d0d457dd1b83cdf0fcd8adcc4d6cb969c5c86c3bffbddb7b73cab5612b493fafed3aeaf3aeadda78aba2628a0e0d9f5f99b2b79654e956ea94e51944e88c1808ac6c807367e3b772b63719006f66a6dcf16d9c26d29269a5661f9f60eb95da4e5d9615cdc65c5695adef5766a52ba052b3f527504a59d4668f462b444f0844a523e2c43c23e3b65b3a67935c2535491348ea3254f2eafa2d77a2d1272bc422b6312ad1329e78292d4291b8288832690c25f142479722dec1ae271ad201a4a01927416568153f114c7b12bb1112d50ea430e1e80e1bf0baf90afac09fe0096970570f053570398a03297027e101b47
|9,0=>0xf9f14e4f60ce280b73ca73727581865456c5254f4ba613da333b65b20b1905c14
|10,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffeeffffffeeffff0000ffff0000ffffffffffffffffccccccccccccccccffeeffeeffeeffeeaa00aa00aa00aa00ffffffffffffffffffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ffffcceeffffcceeccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa001100110011001100aa00aa00aa00aaffffffaaffffffaaff00ff00ff00ff00ffffffffffffffffaaaaaaaaaaaaaaaaffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccffeeffeeffeeffeeaaaaaaaaaaaaaaaa
|0,1=>0x33333333333333333333222233332222ffff00aaffff00aa000000000000000033333333333333333333002233330022ffccffccffccffccaa88aa88aa88aa8800ff00ff00ff00ff00aa00aa00aa00aaeeeeeeeeeeeeeeee0000000000000000aaaaaaffaaaaaaffaaaaaaaaaaaaaaaaaaffaaffaaffaaffaaffaaaaaaffaaaacceecceecceeccee0000000000000000ffffff00ffffff00ffffff00ffffff0055555500555555005555550055555500ffffffccffffffccffff0000ffff0000ffffffccffffffcccccccccccccccccc00aa00aa00aa00aa00aa00aa00aa00aaffeeffeeffeeffeeffeeffeeffeeffeeffffffffffffffff0000000000000000
|0,2=>0xffffaaaaffffaaaa0000000000000000ffffaaaaffffaaaaffffaaaaffffaaaa00ee00ee00ee00ee00aa00aa00aa00aaffffffaaffffffaa00aa00aa00aa00aaffeeffeeffeeffee0000000000000000cccceeeecccceeeecccceeeecccceeeeaabbaabbaabbaabbaa00aa00aa00aa00eeeeeeeeeeeeeeeeccccccccccccccccff00ff00ff00ff00ee44ee44ee44ee44ff55ff55ff55ff55aa00aa00aa00aa0000ff00ff00ff00ff00000000000000005555555555555555aaaaaaaaaaaaaaaa005500550055005500aa00aa00aa00aaffffff00ffffff000000000000000000ffccffccffccffcc0000000000000000ffccffccffccffccffccffccffccffcc
|0,3=>0xaa55aa55aa55aa55aa00aa00aa00aa00333333113333331133330000333300000000555500005555aaaaaaaaaaaaaaaa00ff00ff00ff00ff00ee00ee00ee00ee33330033333300333333002233330022333300333333003333330000333300000000dddd0000dddd0000ddcc0000ddccaaaaffffaaaaffffaaaaaaaaaaaaaaaa0000ffff0000ffff000000000000000000aa00ff00aa00ff00aa00aa00aa00aa0000000000000000aaaaaaaaaaaaaaaa55555555555555550000000000000000aaaaaaaaaaaaaaaa0000000000000000ffffffaaffffffaa0000000000000000cceecceecceecceecceecceecceeccee00ff00ff00ff00ff00cc00cc00cc00cc
|0,4=>0x33331111333311113333000033330000000000ff000000ff00aa00aa00aa00aa000000ff000000ffff00ff00ff00ff00555555555555555555005500550055000000ffff0000ffff0000cccc0000cccc00bb00bb00bb00bb00aa00aa00aa00aaff55ff55ff55ff55ff550000ff550000ffffaaaaffffaaaaff00aa00ff00aa0000ff00ff00ff00ff44ee44ee44ee44eeff00ff00ff00ff00aa00aa00aa00aa00ffaaffaaffaaffaaffaaffaaffaaffaa005500550055005500000000000000000000ffff0000ffff0000ffee0000ffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeffffeeeeffffeeeeffff0000ffff0000aaffaaffaaffaaffaaaaaaaaaaaaaaaa
|0,5=>0x2222222222222222ffff0000ffff0000ffff2222ffff2222ffffffffffffffffffffffaaffffffaaff55ff55ff55ff55ff55ff00ff55ff001100110011001100ff00ff00ff00ff00ff33ff33ff33ff33ff00ff00ff00ff00bbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaaffffffaaffffffaaffffffaaffffffaa2222222222222222000000000000000033333333333333330000000000000000dd00dd00dd00dd00ff00ff00ff00ff00ffffffffffffff00ffffffff00000000ffffffffffffffffffaaffaaffaaffaaaaffaaffaaffaaffaaeeaaeeaaeeaaeeffffffffffffffff5544554455445544ffff5555ffff5555ffff0000ffff0000
|0,6=>0x33333333333333333333330033333300ff55ff55ff55ff5500000000000000000055005500550055004400440044004455005555550055555500550055005500ffffffffeeeeeeeeffffffff000000000033003300330033002200220022002200005555000055550000550000005500aa00ff00aa00ff00aa00aa00aa00aa00aaaaaaaaaaaaaaaaaaaa0000aaaa0000ff00ffffff00ffffff00ff00ff00ff000000aaaa0000aaaa0000000000000000cccceeeecccceeeeccccccccccccccccff33ff33ff33ff33ff22ff22ff22ff223333333333333333333300003333000022222222222222222222222222222222ffaaffffffaaffffffaaffaaffaaffaa
|0,7=>0xffff0000ffff0000ff000000ff00aaaaffffaaaaffffaaaaffaaaaaaffaa0000000000000000eeeeeeeeeeeeeeee0000ffff0000ffff0000ffaa0000ffaaffffffffffffffff00ff00aa00ff00aaccffccffccffccffcceecceecceecceeccccccccccccccccaaaaaaaaaaaaaaaaffffffffffffffffffccffccffccffcc55555555555555555544554455445544ccffccffccffccffcccccccccccccccc0000ccff0000ccff0000cccc0000ccccffaaffaaffaaffaaff00ff00ff00ff0000330033003300330000000000000000ffffffffffffffffeeeeeeeeeeeeeeeeff00ff00ff00ff00ee00ee00ee00ee00ffffffffffffffffffffff00ffffff00
|0,8=>0xff00ff55ff00ff55ff00ff00ff00ff00ffddffddffddffddcccccccccccccccc00ee00ee00ee00ee00ee00ee00ee00ee55445544554455445544554455445544ff22ff22ff22ff22ff00ff00ff00ff000000000000000000cceecceecceecceeffffffff0000aaaaffffffff0000000055555555555555554444444444444444000000000000000055445544554455443333333333333333aaaaaaaaaaaaaaaaffffffffffffffffffffaaaaffffaaaaffffffffffffffff00aa00aa00aa00aa0022002200220022aaaaaaaaaaaaaaaa0000ffff0000ffff000000aa000000aa33bb33bb33bb33bb00aa00aa00aa00aaaabbaabbaabbaabbaaaaaaaaaaaaaaaa
|0,9=>0x55555555555555555555000055550000ffffffffffffffff222222222222222200000000000000000000aaaa0000aaaaaaaa0000aaaa0000aaaaaaaaaaaaaaaa0000000000000000ffffff00ffffff00ffff2222ffff2222ffff2222ffff2222000000000000000000ff00aa00ff00aa00110011001100110000000000000000ff55ff55ff55ff55ff00ff00ff00ff0033333333333333332222222222222222ffff00aaffff00aaffff00aaffff00aa0000ff550000ff550000000000000000ddddddddddddddddddccddccddccddcc000000ff000000ff000000aa000000aa0000aaaa0000aaaa0000aaaa0000aaaaffffffffffffffffcceecceecceeccee
|0,10=>0x5500550055005500ff00ff00ff00ff005555000055550000ffff0000ffff0000ffffffffaaaaaaaaffffffff0000000033333333333333333300330033003300ffff5555ffff55550000000000000000cccccccccccccccceeeeeeeeeeeeeeee0000555500005555000000000000000000ff00aa00ff00aa00ff00aa00ff00aaffff00ffffff00ffffff0000ffff0000000000ff000000ff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1242310050c0b021309050403020100050402091f1b10050c0b0201091e05040b02091d10050402011c121005040201061b1a050402011912100504020118121005040b02010617050c020115121005140201091210050c02130912050f0b020e0905040201060d050c0b020a09050402010608050407020106050403020100
|1=>0x1005040201242305040201061b2305040b020e092b05040302010932050402310930100504020106231005040702010605040201002d1005040201092c1005040b0201062b05040201241b100504022a061b100504020109291005040228061b100504030201091c050402270109100504020e09122105040201062625050402
|2=>0x20106241b0504020106462f05040302010644050b02010943100504110302010605410b020e0905040201403f1005040b02093e1005040201241b050402010012100504020106242305040b0201063d0504070b0201060504070201091005040201093c10050402093b1b10050402093a1210050b0201093910050c02010936
|3=>0x1005040201094e1005040201242334050201091b4b1005040201091b1005040b02093b100504070201060905040b020100100504034d020109050402014c1b1005020109464b1005040201261b1005040201094a100516490201091005040b020a091005040b4802010605040201062305040302010009050402010947100504
|4=>0x45a0b020e091005040b0201590910055804030201091005040201091b10370504550201091054040b020109100504530b02014c1005040b020152091005040b02010951100504450201061b10050c0b0201092f05040201093610370504450b020138100504020106091b2505040b02094f1005040b0201062f05040209461f
|5=>0x3812100504020138096810052e0b02016710050445660201091005040b026409100504630b0201091005040b0201064c1005040b02096212100504020106611b100504600b0201091005040b0201091017055e0b020109100504020109121021055d040b0201091005040b020106261005045c0b0201091005045b0201091005
|6=>0x201091b104405040b020100091005040b0201096d10050b020106094b10050403020140091005040b0201096c1005040b020106091005040201061b12100504030201092205040b020106104405040302010915106b040b020109100504110b0201061005040b0201096a1005040b020109691005040b0213091005040b0201
|7=>0x91005040b0201097b10050402010612102505040b027a01091005040b020179091005040b02010977100504030b02420106050b020109751005160c02010912100504740201061005040201091210730504027101091005040b02096f100504020109301210050402014012102505040b020106106e05160402010612100504
|8=>0x2010981100504020140121005040b020180091005040b020124340504024201064610052e040201091b1005040201151210050402710106091005040201091b1034051604030201060905040b02017e091005030b0201094b1005040b027d01060905040b0201097c100504027201094610050403020106091b0504110b020e
|9=>0x91005040276010912100504200b020988100504027201091b1005040b02010987100504490b02010910051604020109841005040b02010986100504070201091005040b020e092105040201093c1005040b02091f1005040201380936100504020109841b10050403020106092505040b0201831005040b020109821005040b
|10=>0xb0206091f100504020e0109461005410b0201091005040b028e010910050402010984102505040b0201068d10050402010968100504024201061b1005040b020e098c1005040b020106092f050c0b02013809100504030b02096f1005048b0201091005040b028a0109100504450302010610050b020109354b1089040b0201
|11=>0x91b921005040b020e098d100504020e01091b100504030b0201064c0516040201091b100504070b0201091005040b0201093c1005040b02420930100504020106122505040b0201241005040b022a061005040b029001091005047402010605040201061b103305048f0b0201091005040b022806100504020106093c100504
|12=>0x504030b0201063405040b02010010050402010984250504970b02010610050402010946961005950c0b020109100504450302010605040b48020109100595040b0201061005040201094a1005040201091b102505040b02010910940504020109461056050403020109104405040b020106241005040b029301091005040201
|13=>0xb0228091005040b0201062405040b02010910980504020106091b1005040201061b104405040201064610340504020109961b1005040b0201091c100504020140091b1005040b0201094a1005040b02012405450b0201094b1005040201061b330504530201091b1005040201091b1005040201096810370504450302014c10
|14=>0x106091005040b0201400910250516040b0201060910059a0b020109100558040b020109100570040b0201091005040b020106091b1005162e0b020109100516040302010910050420020109121005040b022801091005040b027d0109100504030201091b1005040b020109991005040201061b10340504027a01091b100504
|15=>0x50b0201094b1005040b0201099c10050c040b02010912100504970b0201091005040b020109102f05040b020159091005040b020106091025059b040b020109100504450b0201091037050c0b020109103705040b0201590910560595040b02010910050403020109102505040b02420135100504200b020e091005040b020e
|16=>0xb020109a21005040b020106091005a1040b0201091005040b02010609105605040b020109961005040b02010910a005040b0201099f1005040b0201400910050478030b0201091005040b0201099e100504030b0201093405040b0201099d100504030b020e01091005040b0201063305040b02010915100504530b02010910
|17=>0xb020109106505040b020106092505040b02010910a505045a0b0201091056050453030b02010910052e040b0201061005040b020106103405040b0242010609100504030b020109105605040b02010609961005040b02a401091005040b020e0109351005040b02010912103705040b02010910a30504530b02010609100504
|18=>0x121005040b02010930100550040b0201091005040b0201094c1005040b020135103405040b0201066110050c040b0209621005040b020109102105040b0201099c10370504030b024201091005040b02010935105605040b020109a6100504030b02010609100504450b0201061005045a0b02010910052e0c0b020109100504
|19=>0x1005040b020109841005040201060946100504030b0201094c1005040b02010910340504970b020109103405040201091210250504030b02010609050402010946100504740201091005040b020109106ea7040b020109100504450b020e0109100504030b020109a61005040b020109104405040b020109671005040b020106
|20=>0x105605040b020109102505040b0201091b1005040b022809100504030b020109103405040b02010610330504a90201091005040b0272010609100504020106091b10050445030201091005040b020109342505a80b02010910052e040b020109a21005040b027201091005040b0201353405040b02010609103405040201091b
|21=>0x5040b0201091005040b020109121005040b02010961100504450b0201091005040b020109103405040b02010935100504030b020109100504200b02010910050c040b0201091005040b020109103305040b024201091005040b020106091005040b020109
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x24601e60186012600c600660006
|6,0=>0x1dc71d571ce71c771c071b971b271ab71a4719d7196719061897182717b7174716d7166715f71596152714b7145613e7137713071297122711b7114710d710670ff70f960f270eb70e470dd70d670d060c970c270bb70b470ad70a6709f70987091708a7083707c7076607060697062705b7054704d7046703f70387031702a7
|6,1=>0x1ff71f871f171ea71e37
|7,0=>0x3ee83e683de83d683ce83c773bf83b873b083a973a2739a8392838a8382837a8372836a8362835a8352834a8342833b7333832b8324731c8314830c830572fd82f582ee72e682df72d782cf82c782bf82b782af82a872a082988290828882817279827182698261825a7253724b8243823b8233822c7224821c8214820d72067
|7,1=>0x5dc85d485cc85c485bd75b675af75a785a165998591858a7582857a8572856b7563855b8553854c7544853c8534852c8524851d7515850d850584fe74f684ee84e684de84d684ce84c684bf74b874b174aa74a2849a8492848b7483847b8474746c8465745d8455844e7446843e8436842e8426841e8416840e840683fe83f68
|7,2=>0x71a8712870a870286fb76f476ec86e486dc86d486cc86c486bc86b486ae66a6869f769786907688868086788671766a7662865a8652864b7643863b8634762c8624861c8614860c860485fc85f485ec85e48
|8,0=>0x92b9923891a9912890a890288fa88f288ea88e198d898d088c888bf98b698ad98a5889c9893988b8882987a8872886a886198598851884988418838983088288820881798107808880087f977f187e897e087d887d087c797bf87b697ae87a5979d8795878d8785877c9773976a9763775b8753874a9742873a8732872a87228
|8,1=>0xa6e8a677a5e9a568a4f7a469a3e8a368a2e8a277a1e9a168a0f7a0699ff79f789ef89e699de89d599cd89c589be79b779af89a8799f9996998e8986897e8976896e8966895e8956894e8946893d99349
|9,0=>0xad68ace8ac68abe8ab68aae8aa68a9e8a968a8e8a868a7e8a768
|10,0=>0xade7
|_,_=>0
def wAt:=mkWire dB 170 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x937410420b06824415001c10d10910824412e10010250b2f4b8400910410251b33c24400b06824410b1042485201002c050633c24400b0682441451082441041a404414210004250633c24400b06824410b38824dd0b248d4d10910c24421b33c24400910444400b0942cbd09104b840040942c92041040489161002c110b1042485201002c051609c2c26111002c25
|1=>0x6609c2cdd0410810420b06824410b10458400b04514420910414694210004250122458400b04424dd0410830240410410250410805950937010420309c24410b1042c260c01c10413110004490b098117d0e09804412010114410b0942c6b4210004250b56404d20b06824410b57c2558011081489161002c110309c0c250b1042c1a0910410412e10010250b38824dd
|2=>0x1210424410921c80400b01424950b1082c26353442443091082c18091042c1a0910458270b0442c260b7200419091042c1a0910425fd0304c103a0110508430910404250b06024410910404410b0942c1a09104195b0910404427809c80410b015d813012542c420b09810410b3342441091002dc84210404257001c58410b04424951210824410921480400b0142495
|3=>0xb09824410b3342440013342441091002dca0106424410b0602441041a508400109448420b0982ce00937410420b06824412009cb8400910410250937405c2030442d5d0956004420910424430e04c04410565424dc041083827011042c1a09104801b0910448410b098d5590910c04420b2f4b840040940441201002c050b72908410109406162e1041025093741042
|4=>0xb01424953534424430910838130110424400b0682441530bd14410b0942c1a0934424420b38024dd0309c2c410921480400b0142c42121042c260b34410410b09824410b1042c25032e02d66095640442091065442041242c180910418cf0910424400309c2c410b06824410b4282c1a091042c410b06824410b10824410b098d4d10910c244201914244104098c441
|5=>0x110824411610c2c11041082c25043741042095640442041242c260b1082c410910c0425011042c05091040441092542c42091041185010982cb90409458410b0442c1a091042c11040942c410b0442c050b09804cd091010843010954c2f030942c410b06824d1091082c1a0910404694210004250633c2441091002c1a0934424420b0682c18093442442200602441
|6=>0xb5640442030942c410910410250934424420910404250b10404420910404d50910c24430110410420b09810d20910824410b2e81025093442442042542c4209104041a091042cde0410830270410424950b1080c050b1058441010982c41091083026041042c410110424410910058270b04514410b09438130110424df0410810410b0982cd109108b840040942559
|7=>0x309c2c411033c24400b34424420b1082c26091042c410b06024410b3342440121082c26053342440011042c250301c2c410b34824420c0901041091042c260e0bc04410434424420309c2c410910c24420910404260c01c1041201002c050937c10420b10404250910c04420301c2c41091042c41091042c250b56404420410410250937010420b1082441911081026
|8=>0x2c26010982c250910824430b1042c05041042440010942441011082c420b0682441013342440091082441091002ccf0910024410b06824410b1042c250b10824420433c24400b2e810254210404250910c24420934424420b0682441121042c260b0602441
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x800000000000000000
|6,0=>0x324000000000000000000000000000000002e40a90000099000009080000000204000000007100000000000000000000000000000000068816404cc112000000000000d40000000000000000000000000000000000000000c1021004400000000000000000000000000000088000
|6,1=>0
|7,0=>0x9b2260c953000092324088d300008a321cc00021848420000000204c00000008011f4c7c11e887731d480001c8c00000000001bcc6d200006a31a446630000633180c00000005d3168c59115c8000000054314c45210000502134c4a311cc0000000452108c4020f883c20e4c363
|7,1=>0x4288000000000041cd043404cff23f0c0000000f933d8c0003d08f133bc80000000ec33a88e91398ce5138c8e030000df1370cd930000d723548d320000d12338ccb3320cc53308cc022fc4be12ecc0000000b830000b532cc8b122b8cab32a84a9129c8a52288c00028089f12748000
|7,2=>0x1543000151353c94c3524c000518d451508c0004fcd3e100013b34e493634ccd3034b892c20001293498d2510001232480d1f100011c346c519245c8000450d12244090f143490c1
|8,0=>0x7409ce27309ca27209c627109c227009be26f09ba26e09b626d09b316c49af26b49ab26a85a826989a4268c5a1267c99d266c999265c995264c991263c98d262c989261c985260c98125fc97e15f097a25e097625d097225c096e25b096a25a45672594963258495f257495b25649572
|8,1=>0x878a1c286c619285ca161850a122840a0e2830a0a2820a062810a0228009fe27f09fa27e09f627d09f227c09ee27b09ea27a09e627909e227809de27709da27609d627509d22
|9,0=>0x22c18ac62a18a4628189c6261894624188c62218846201
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x20000090c003a600179000b88005a4000f00007100034800184000a200049000208001000007000030000148000a00004400021000100000700003200018000080000300001400009000040000100000400000
|1=>0xaad80556402aa60154700a228051040238e01155008708042c0020e6010710080e0040600202401000006348031440188200c1000600002544010c20084100410802000008a2004410020d0010400081000402
|2=>0x282081158c08082035ff01aef80d76c06abe0355301a3080800003ef601f7300fa98075fc03afa01d7b00eb98075ac03abe01d5d00ead80754402bfe015f700af380577c02afe0157b00abc8055cc02ae201567
|3=>0x106090830083082011f5b08ab9841d4c13afe09d7d04ebd8275dc13abe09d5d04abd8255cc12ab60955304a61824184112fa08965044ae8215b4108c20842004208021000102f2080610401c0200801003008008
|4=>0x4375fd83af2c1d51186090a55dc52abe21f5310bad8857cc42bae215d110abf8835ac418c620c22
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x10000000000
|6,0=>0x1300000000000000000214130010000800001e000018000300000000000000011508010000002400000000000000260000030b1d3a00000000000000000100
|7,0=>0x3000000017781a014d00006a2c02202d010326151f205f01076400082813000701220030213b7a13130707611300001600741f3057210b0a070727000108050203202412262a3178002513000710000315002661120e105808565d000000380700370364000c1500005e1307010b00130103003013130400001139300711283c
|7,1=>0x9000c20294c00100e0c002e07004d071b04133010604a1462000d1c06003a07071f030f013001200b
|8,0=>0x43786178767e411c6544368879174241431978631b1c4479418e232c78831b878a437882847c6e2c694b111c7147736d456711406c2f7d2b5081347008465189664f7186788b446d457f525c3e8c7335784872615b326f68426b4e538063338d495a1149597b7754
|9,0=>0x42444479443f7c857955447075
|10,0=>0x3d
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 21 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_123 9 roots_123 ops++addP pm 1 dom_109 7 roots_109 ops++addP pm 2 dzo_47_16 5 roots_47 ops++addP pm 3 dom_118 6 roots_118 ops++addP pm 4 dom_119 8 roots_119 ops++addP pm 5 dom_126 7 roots_126 ops++addP pm 6 dzo_123_4 9 roots_123 ops++addP pm 7 dzo_111_16 6 roots_111 ops++addP pm 8 dom_91 8 roots_91 ops++addP pm 9 dzo_125_2 6 roots_125 ops++addP pm 10 dom_125 8 roots_125 ops++addP pm 11 dzo_61_2 5 roots_61 ops++addP pm 12 dom_111 8 roots_111 ops++addP pm 13 dom_103 5 roots_103 ops++addP pm 14 dzo_94_32 6 roots_94 ops++addP pm 15 dom_63 6 roots_63 ops++addP pm 16 dom_117 5 roots_117 ops++addP pm 17 dom_45 4 roots_45 ops++addP pm 18 dzo_109_16 5 roots_109 ops++addP pm 19 dzo_109_2 5 roots_109 ops++addP pm 20 dzo_95_32 7 roots_95 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_47_16_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_123_4_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_111_16_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_125_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_61_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_94_32_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_109_16_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_109_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_95_32_90 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_123 9 s (0,roots_123.map (·&&&dom_123)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_123 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 7 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 69 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 69 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 169 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 41 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 169 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 104 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 104 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 13 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 13 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_127 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_183_8:=0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00
def gzo_183_8:=0xff00ff00ff00fe000000000000000000fe00fa00ee00aa00
def gsh_183_8:=0xff00ff00ff00fe000000000000000000fe00fa00ee00aa
theorem lowS_zo_183_8_182:Lower true dzo_183_8 roots_183 gzo_183_8 9:=lower_iso_b (d1:=dom_183) (r1:=roots_183) (T1:=gsh_183_8) [(dom_183,8)] (by decide +kernel) (lower_slice_b (T:=gsh_183_8) [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa,0,1)] (by decide +kernel) lowS_182)
def dzo_175_16:=0xffff0000ffff00000000000000000000ffff0000ffff0000
def gzo_175_16:=0xffff0000ffff00000000000000000000fefe0000eecc0000
def gsh_175_16:=0xffff0000ffff00000000000000000000fefe0000eecc
theorem lowS_zo_175_16_45:Lower true dzo_175_16 roots_175 gzo_175_16 6:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_16) [(dom_175,16)] (by decide +kernel) (lower_slice_b (T:=gsh_175_16) [(0xcccc0000cccc00000000000000000000cccc0000cccc,0,2),(0xffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_45)
def dzo_189_2:=0xcccccccccccccccc0000000000000000cccccccccccccccc
def gzo_189_2:=0xcccccccccccccccc0000000000000000ccccc8c8cccc8800
def gsh_189_2:=0x333333333333333300000000000000003333323233332200
theorem lowS_zo_189_2_45:Lower true dzo_189_2 roots_189 gzo_189_2 6:=lower_iso_b (d1:=dom_189) (r1:=roots_189) (T1:=gsh_189_2) [(dom_189,2)] (by decide +kernel) (lower_slice_b (T:=gsh_189_2) [(0x333300003333000000000000000000003333000033330000,0,16),(0x333333333333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_45)
def dzo_173_16:=0x333300003333000000000000000000003333000033330000
def gzo_173_16:=0x333300003333000000000000000000003232000022000000
def gsh_173_16:=0x33330000333300000000000000000000323200002200
theorem lowS_zo_173_16_45:Lower true dzo_173_16 roots_173 gzo_173_16 5:=lower_iso_b (d1:=dom_173) (r1:=roots_173) (T1:=gsh_173_16) [(dom_173,16)] (by decide +kernel) (lower_slice_b (T:=gsh_173_16) [(0x33330000333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_45)
def dzo_173_2:=0xcccc0000cccc00000000000000000000cccc0000cccc
def gzo_173_2:=0xcccc0000cccc00000000000000000000c8c800008800
def gsh_173_2:=0x33330000333300000000000000000000323200002200
theorem lowS_zo_173_2_45:Lower true dzo_173_2 roots_173 gzo_173_2 5:=lower_iso_b (d1:=dom_173) (r1:=roots_173) (T1:=gsh_173_2) [(dom_173,2)] (by decide +kernel) (lower_slice_b (T:=gsh_173_2) [(0x33330000333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_45)
namespace S_191
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(2,18),(2,130),(3,11),(3,19),(3,35),(3,131),(4,36),(4,132),(5,13),(5,37),(5,133),(6,22),(6,38),(6,134),(7,15),(7,23),(7,39),(7,135),(8,9),(10,11),(10,26),(10,138),(12,13),(12,44),(12,140),(14,15),(14,30),(14,46),(14,142),(16,18),(16,144),(17,19),(17,25),(17,49),(17,145),(20,22),(20,52),(20,148),(21,23),(21,29),(21,53),(21,149),(24,25),(24,26),(24,152),(28,29),(28,30),(28,60),(28,156),(32,33),(32,36),(32,160),(34,35),(34,38),(34,50),(34,162),(40,41),(40,44),(40,168),(42,43),(42,46),(42,58),(42,170),(48,49),(48,50),(48,52),(48,176),(56,57),(56,58),(56,60),(56,184),(128,129),(128,130),(128,132),(128,144),(128,160),(136,137),(136,138),(136,140),(136,152),(136,168)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffffffffff
def xsM:=roots_191.map (·&&&dom_191)
def gM:=goal_191&&&dom_191
def NN:Nat→Nat
|5=>3
|6=>10
|7=>24
|8=>21
|9=>5
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x7aba37859a1aa91
|6,0=>0xd4acdbe021b0b02a8a058807d5799e3ce73376b92dd592d671
|7,0=>0xefd6ddb0c5d9a7bb12aba415c94306921b5824a773e3863cb8414c23c0723b2332db612d9c72babf250da2317d1ef071e0fb1523c14e4c0d5090bd60
|8,0=>0xe86a8e0d17cbafac9d61c06bfc00f3b8713a89189879887c8378e3b74aae73305522224c9ff4b0d43565d2d22a18850168ad0c5cd
|9,0=>0xe03e0c502bbef167caac64461
|10,0=>0x2bff1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfffffffffefefefe0000000000000000fafafafafafafafaffffffffeeeeeeee0000000000000000aaaaaaaaaaaaaaaa0f0f0f0f0f0f0f0f00000000000000000f0f0f0f000000000000000000000f0f00000000000000000f0f0f0f00000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaaffffffffffff000000000000000000000000000000000000ffffffffffff00000000000000000000ffffffffffff0000ffffffffffffffff00000000000000000000000000000000ffffffff000000000000000000000000ffffffff00000000ffffffffffffffff0000000000000000ffffffff00000000ffff0000ffff00000000000000000000ffff0000ffff0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00fffffffffffffafa0000000000000000fafafafafafafafacccccccccccccccc0000000000000000ccccccccccccccccffffffffffffaaaa0000000000000000aaaaaaaaaaaaaaaa
|0,1=>0x333333333333333300000000000000003333333333330000fffffffffffff0f00000000000000000f0f0f0f0f0f0f0f0333333333333333300000000000000003333333300000000333333333333333300000000000000003333000033330000ffffffff333333330000000000000000ffffffff00000000333333333333333300000000000000000000000000000000ffffffffffffffff0000000000000000cccccccccccccccc0f0f0f0f0303030300000000000000000f0f0f0f0000000000000000333333330000000000000000ffffffff000000000000ffff0000ffff00000000000000000000ffff0000cccc0000cfcf0000cfcf00000000000000000000cfcf0000ccccfffffffffcfcfcfc0000000000000000f0f0f0f0f0f0f0f0ffffffffffffffff0000000000000000ffff0000ffff0000ffffffffffffcccc0000000000000000ccccccccccccccccffffffffcccccccc00000000000000000000000000000000ffffffffcccccccc0000000000000000ffffffffcccccccc
|0,2=>0xffffffffffff000000000000ffffffff000000000000000000000000cccccccc000000003333333300000000000000000000000000000000030303030303030300000000000000000303030300000000ffff0f0fffff0f0f0000000000000000ffff0f0fffff00000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0c0c0c0cffffffffffffcccc0000000000000000ffff0000ffff0000000000000f0f0f0f00000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffcccccccc0000ffff0000ffff00000000000000000000000000000000ffffffff0000ffff0000000000000000ffffffff000000000f0f0f0f00000f0f00000000000000000f0f0f0f00000000ffff0000ffffffff0000000000000000ffff0000ffff000000000000ffffffff00000000000000000000000000000000333300003333333300000000000000003333000033330000ffffffffffffffff0000000000000000ffffffffffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0xcb29f1db1840cb64a1c61032c10071840de04a1c610304a74d1c610304a34768610329c3471840d92981c510304a3511571032c12860c128d58718304a3551c51035012864c32d22851032c13861033c13871440c138d1440c128c1440c2040
|1=>0x36c1c6ac40c128d1c64c40c128d1c51840c12aa1c6a432c12871840c12981e71840c128d1c61032d92911440cb04a44510304a347a051840cb29c1c60cb04a5871440c128d1e220510304a34794610304a9071840c12981da1840cb2a11c5184
|2=>0x1d01840cb64a1d01440cb04a1c61032ca7071840c128d1c51840cb04a7471461032c12876a51840cb04a1e6bc61032c12878051840cb04a1e71840cb04a1c51840c128d1c51931032c12871840cb04ab871840cb04a1ed1840c12aa1c610304a
|3=>0x1840cb04a1c51840cb04a1c61032c12878861032c12876901840cb04a1c64c40cb04a1c64c32c12879851032c12878861032c12874468c40cb04a1c61032c129d1c64c40cb29c1e51840cb04a
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x3180cc006
|6,0=>0x9ce4772038e5c64e2b712b07d832c127
|7,0=>0x82bbf61eb0ed872c379daeecf8643b05d730b18553a8a135092845420dcf70738363995cbb0558
|8,0=>0x1af8d3c67e32f18f8c3c5fe2ef16f8b43d85eb134f9a34cfa26b32d892c47262910c8
|9,0=>0x1d78e7c71e37f1b78
|10,0=>0x1df7
|_,_=>0
def wAt:=mkWire dB 48 192 0xffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x407060518d852f1875307187441d9c4c665047452f187861d14bc61d94bc6991079b2f19a411e8c1c489187a007144461d19a4a2520706112c9481c184452f141c61d14bc61d0479b2f19a461d2d1501c181412520706111074a45187501c1814b39291501c181461d2c04a252070611
|1=>0x187501c18144891878507187530710746991078605047461d1815307107452f1874507187461d0478699107881f18445111874665047452f187461d1074666047501e181672f199411d04d852f187452f187452f187672f141461d111501c1815b2f19a411e14bc61d4070605047461d
|2=>0x187461e0478605107441e107461e
|_=>0
def oO:Nat→Nat→Nat
|5,0=>5
|6,0=>0x1520000000000001140d4094054
|7,0=>0x5635335124f24c34934634424133e33b33833533233022d32a32732432312031d31a3173
|8,0=>0x8127f27d27b27927727527327126f26d26b26926726526326125f25d25b2592
|9,0=>0x871861851841831
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x2401014da014d300fdf00edf00ddf00cdf00c5b00c5300c1b007df0075f005df004ff004df004db0041300401000db000da000d30008400080000520003f0001b0001a0001300012000040000200000
|1=>0x8949760cdb11cdf11c1b114df10553104df10493100ff094ff09497086df084fb04004
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>1
|6,0=>0x20000003472c1
|7,0=>0x14828a3d83205137cf18e2442163c275e0c8
|8,0=>0x25a9ca598676dab115e8992b5542389c
|9,0=>0x11ae7564
|10,0=>0x11
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 20 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_187 9 roots_187 ops++addP pm 1 dom_183 9 roots_183 ops++addP pm 2 dom_173 7 roots_173 ops++addP pm 3 dom_182 8 roots_182 ops++addP pm 4 dzo_183_8 9 roots_183 ops++addP pm 5 dzo_175_16 6 roots_175 ops++addP pm 6 dom_189 8 roots_189 ops++addP pm 7 dom_175 8 roots_175 ops++addP pm 8 dom_157 5 roots_157 ops++addP pm 9 dzo_189_2 6 roots_189 ops++addP pm 10 dom_159 8 roots_159 ops++addP pm 11 dzo_61_2 5 roots_61 ops++addP pm 12 dzo_47_16 5 roots_47 ops++addP pm 13 dom_155 7 roots_155 ops++addP pm 14 dom_185 6 roots_185 ops++addP pm 15 dom_45 4 roots_45 ops++addP pm 16 dom_63 6 roots_63 ops++addP pm 17 dzo_173_16 5 roots_173 ops++addP pm 18 dzo_173_2 5 roots_173 ops++addP pm 19 dom_143 5 roots_143 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_191 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_183_8_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_175_16_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_189_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_61_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_47_16_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_173_16_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_173_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_143 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_187 9 s (0,roots_187.map (·&&&dom_187)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_191 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_187 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_191==dom_191)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_191 gM v ys):RunD true dom_191 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_191 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 10 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 21 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 5 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_191 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
def gzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000e0c0a000
def gsh_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000e0c0a00
theorem lowS_zo_219_4_91:Lower true dzo_219_4 roots_219 gzo_219_4 9:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_4) [(dom_219,4)] (by decide +kernel) (lower_slice_b (T:=gsh_219_4) [(0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_91)
def dzo_214_8:=0x55005500000000005500550000000000550055000000000055005500
def gzo_214_8:=0x55005500000000005500540000000000550055000000000044000000
def gsh_214_8:=0x550055000000000055005400000000005500550000000000440000
theorem lowS_zo_214_8_150:Lower true dzo_214_8 roots_214 gzo_214_8 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_8) [(dom_214,8)] (by decide +kernel) (lower_slice_b (T:=gsh_214_8) [(0x550055000000000000000000000000005500550000000000000000,0,64)] (by decide +kernel) lowS_150)
def dzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00
def gzo_215_8:=0xff00ff0000000000ff00fe0000000000ff00ff0000000000ee00aa00
def gsh_215_8:=0xff00ff0000000000ff00fe0000000000ff00ff0000000000ee00aa
theorem lowS_zo_215_8_150:Lower true dzo_215_8 roots_215 gzo_215_8 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_8) [(dom_215,8)] (by decide +kernel) (lower_slice_b (T:=gsh_215_8) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xff00ff00000000000000000000000000ff00ff0000000000000000,0,64)] (by decide +kernel) lowS_150)
def dzo_150_8:=0x5500550000000000000000000000000055005500
def gzo_150_8:=0x5500540000000000000000000000000044000000
def gsh_150_8:=0x55005400000000000000000000000000440000
theorem lowS_zo_150_8_150:Lower true dzo_150_8 roots_150 gzo_150_8 5:=lower_iso_b (d1:=dom_150) (r1:=roots_150) (T1:=gsh_150_8) [(dom_150,8)] (by decide +kernel) (lower_slice_b (T:=gsh_150_8) [] (by decide +kernel) lowS_150)
def dzo_151_8:=0xff00ff00000000000000000000000000ff00ff00
def gzo_151_8:=0xff00fe00000000000000000000000000ee00aa00
def gsh_151_8:=0xff00fe00000000000000000000000000ee00aa
theorem lowS_zo_151_8_150:Lower true dzo_151_8 roots_151 gzo_151_8 6:=lower_iso_b (d1:=dom_151) (r1:=roots_151) (T1:=gsh_151_8) [(dom_151,8)] (by decide +kernel) (lower_slice_b (T:=gsh_151_8) [(0xaa00aa00000000000000000000000000aa00aa,0,1)] (by decide +kernel) lowS_150)
namespace S_223
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(2,18),(2,66),(2,130),(3,11),(3,19),(3,67),(3,131),(4,132),(5,13),(5,69),(5,133),(6,22),(6,70),(6,134),(7,15),(7,23),(7,71),(7,135),(8,9),(8,72),(10,11),(10,26),(10,74),(10,138),(12,13),(12,76),(12,140),(14,15),(14,30),(14,78),(14,142),(16,18),(16,80),(16,144),(17,19),(17,25),(17,81),(17,145),(20,22),(20,84),(20,148),(21,23),(21,29),(21,85),(21,149),(24,25),(24,26),(24,88),(24,152),(28,29),(28,30),(28,92),(28,156),(64,65),(64,66),(64,72),(64,80),(68,69),(68,70),(68,76),(68,84),(68,196),(128,129),(128,130),(128,132),(128,144),(136,137),(136,138),(136,140),(136,152),(136,200),(192,193),(192,194),(192,196),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffffffff
def xsM:=roots_223.map (·&&&dom_223)
def gM:=goal_223&&&dom_223
def NN:Nat→Nat
|8=>8
|9=>5
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xb75a0b0ec99139574de45f48c4758d1ca420c274
|9,0=>0xc48d4ae79e7990045147259c1
|10,0=>0x1730e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xeeeeeeee00000000eeeeeeee00000000eeeeeeee00000000eeeeeeeeffffffff00000000cccccccc00000000ffffffff00000000cccccccc00ff00ff0000000000aa00aa0000000000ff00ff0000000000aa00aaffffffff00000000aaaaaaaa00000000ffffffff00000000aaaaaaaa0000000000000000ffffaaaa000000000000000000000000ffffaaaaffffaaaa00000000ffffaaaa00000000ffffaaaa00000000ffffaaaa55555555000000005555000000000000555555550000000055550000ffffffff00000000ffffaaaa00000000ffffffff00000000ffffaaaaffffffff00000000ffff000000000000ffffffff00000000ffff0000ffff000000000000ffff000000000000ffff000000000000ffff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0cccccccc00000000cccccccc00000000cccccccc00000000ccccccccaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaaffffffff000000000000000000000000ffffffff0000000000000000ffffffff00000000ffffffff00000000000000000000000000000000
|0,1=>0xffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00ffccffcc00000000ffccffcc00000000ffccffcc00000000ffccffcc
|_,_=>0
def sP:Nat→Nat
|0=>0x31483104062906c10407314831040689483104068148310406291e310406291ee1040620c4d081462906c081062906208166290620810a31483104062906248408398a418820
|_=>0
def sO:Nat→Nat→Nat
|8,0=>0x730c9d542283504644c009
|9,0=>0x618b314624c418
|10,0=>0x697
|_,_=>0
def wAt:=mkWire dB 18 224 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x10530528528d1891891852b210530910538930550730950530938b305389305
|_=>0
def oO:Nat→Nat→Nat
|8,0=>0x713094482311084402
|9,0=>0x14198c862301
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 9
def pmP:Nat→Nat
|0=>0x82ebf48ebf42ebf3cebf3cc083c41d24ebf20ebf08ebf04ebf03abf00fff00eff00ebf00000
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>0x348b596a
|9,0=>0x7dec2
|10,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 20 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_219 9 roots_219 ops++addP pm 1 dom_91 8 roots_91 ops++addP pm 2 dom_159 8 roots_159 ops++addP pm 3 dom_222 8 roots_222 ops++addP pm 4 dzo_219_4 9 roots_219 ops++addP pm 5 dom_221 8 roots_221 ops++addP pm 6 dom_220 5 roots_220 ops++addP pm 7 dom_205 7 roots_205 ops++addP pm 8 dom_157 5 roots_157 ops++addP pm 9 dom_215 8 roots_215 ops++addP pm 10 dom_214 7 roots_214 ops++addP pm 11 dom_207 8 roots_207 ops++addP pm 12 dzo_214_8 6 roots_214 ops++addP pm 13 dzo_215_8 7 roots_215 ops++addP pm 14 dom_206 5 roots_206 ops++addP pm 15 dom_143 5 roots_143 ops++addP pm 16 dzo_150_8 5 roots_150 ops++addP pm 17 dom_150 5 roots_150 ops++addP pm 18 dzo_151_8 6 roots_151 ops++addP pm 19 dom_151 6 roots_151 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_223 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_219_4_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_214_8_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_215_8_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_150_8_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_151_8_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_151 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_219 9 s (0,roots_219.map (·&&&dom_219)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_223 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_219 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_223==dom_223)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_223 gM v ys):RunD true dom_223 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_223 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 5 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 5 0 = true)
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
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,64,66)] (by decide +kernel) lowS_237
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,32,33)] (by decide +kernel) lowS_246
def dzo_178_8:=0x50005000500050000000000000000000500050005000500
def gzo_178_8:=0x50005000500040000000000000000000400000004000000
def gsh_178_8:=0x500050005000400000000000000000004000000040000
theorem lowS_zo_178_8_178:Lower true dzo_178_8 roots_178 gzo_178_8 5:=lower_iso_b (d1:=dom_178) (r1:=roots_178) (T1:=gsh_178_8) [(dom_178,8)] (by decide +kernel) (lower_slice_b (T:=gsh_178_8) [] (by decide +kernel) lowS_178)
def dzo_90_32:=0x5050505000000000505050500000000
def gzo_90_32:=0x5050504000000000404000000000000
def gsh_90_32:=0x50505040000000004040000
theorem lowS_zo_90_32_90:Lower true dzo_90_32 roots_90 gzo_90_32 5:=lower_iso_b (d1:=dom_90) (r1:=roots_90) (T1:=gsh_90_32) [(dom_90,32)] (by decide +kernel) (lower_slice_b (T:=gsh_90_32) [] (by decide +kernel) lowS_90)
def dzo_242_8:=0x500050005000500050005000500050005000500050005000500050005000500
def gzo_242_8:=0x500050005000500050005000500040005000500050005000400000004000000
def gsh_242_8:=0x5000500050005000500050005000400050005000500050004000000040000
theorem lowS_zo_242_8_178:Lower true dzo_242_8 roots_242 gzo_242_8 6:=lower_iso_b (d1:=dom_242) (r1:=roots_242) (T1:=gsh_242_8) [(dom_242,8)] (by decide +kernel) (lower_slice_b (T:=gsh_242_8) [(0x5000500050005000000000000000000050005000500050000000000000000,0,64)] (by decide +kernel) lowS_178)
def dzo_218_32:=0x505050500000000050505050000000005050505000000000505050500000000
def gzo_218_32:=0x505050500000000050505050000000005050504000000000404000000000000
def gsh_218_32:=0x5050505000000000505050500000000050505040000000004040000
theorem lowS_zo_218_32_90:Lower true dzo_218_32 roots_218 gzo_218_32 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_32) [(dom_218,32)] (by decide +kernel) (lower_slice_b (T:=gsh_218_32) [(0x5050505000000000505050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_90)
def dzo_243_8:=0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00
def gzo_243_8:=0xf000f000f000f000f000f000f000e000f000f000f000f000e000a000e000a00
def gsh_243_8:=0xf000f000f000f000f000f000f000e000f000f000f000f000e000a000e000a
theorem lowS_zo_243_8_178:Lower true dzo_243_8 roots_243 gzo_243_8 7:=lower_iso_b (d1:=dom_243) (r1:=roots_243) (T1:=gsh_243_8) [(dom_243,8)] (by decide +kernel) (lower_slice_b (T:=gsh_243_8) [(0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a,0,1),(0xf000f000f000f0000000000000000000f000f000f000f0000000000000000,0,64)] (by decide +kernel) lowS_178)
def dzo_211_32:=0xf000f00000000000f000f00000000000f000f00000000000f000f00000000
def gzo_211_32:=0xf000f00000000000f000f00000000000f000e00000000000e000a00000000
def gsh_211_32:=0xf000f00000000000f000f00000000000f000e00000000000e000a
theorem lowS_zo_211_32_82:Lower true dzo_211_32 roots_211 gzo_211_32 6:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_32) [(dom_211,32)] (by decide +kernel) (lower_slice_b (T:=gsh_211_32) [(0xa000a00000000000a000a00000000000a000a00000000000a000a,0,1),(0xf000f00000000000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000
def gzo_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000e0e0a0a00000000
def gsh_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000e0e0a0a
theorem lowS_zo_219_32_90:Lower true dzo_219_32 roots_219 gzo_219_32 7:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_32) [(dom_219,32)] (by decide +kernel) (lower_slice_b (T:=gsh_219_32) [(0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a,0,1),(0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_90)
def dzo_210_8:=0x5000500000000000500050000000000050005000000000005000500
def gzo_210_8:=0x5000500000000000500040000000000050005000000000004000000
def gsh_210_8:=0x50005000000000005000400000000000500050000000000040000
theorem lowS_zo_210_8_146:Lower true dzo_210_8 roots_210 gzo_210_8 5:=lower_iso_b (d1:=dom_210) (r1:=roots_210) (T1:=gsh_210_8) [(dom_210,8)] (by decide +kernel) (lower_slice_b (T:=gsh_210_8) [(0x50005000000000000000000000000000500050000000000000000,0,64)] (by decide +kernel) lowS_146)
def dzo_210_32:=0x5000500000000000500050000000000050005000000000005000500000000
def gzo_210_32:=0x5000500000000000500050000000000050004000000000004000000000000
def gsh_210_32:=0x50005000000000005000500000000000500040000000000040000
theorem lowS_zo_210_32_82:Lower true dzo_210_32 roots_210 gzo_210_32 5:=lower_iso_b (d1:=dom_210) (r1:=roots_210) (T1:=gsh_210_32) [(dom_210,32)] (by decide +kernel) (lower_slice_b (T:=gsh_210_32) [(0x50005000000000005000500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_211_8:=0xf000f00000000000f000f00000000000f000f00000000000f000f00
def gzo_211_8:=0xf000f00000000000f000e00000000000f000f00000000000e000a00
def gsh_211_8:=0xf000f00000000000f000e00000000000f000f00000000000e000a
theorem lowS_zo_211_8_146:Lower true dzo_211_8 roots_211 gzo_211_8 6:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_8) [(dom_211,8)] (by decide +kernel) (lower_slice_b (T:=gsh_211_8) [(0xa000a00000000000a000a00000000000a000a00000000000a000a,0,1),(0xf000f000000000000000000000000000f000f0000000000000000,0,64)] (by decide +kernel) lowS_146)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,18),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,72),(10,11),(10,26),(10,74),(10,138),(16,18),(16,80),(16,144),(17,19),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,88),(24,152),(32,33),(32,160),(34,35),(34,50),(34,98),(34,162),(40,41),(40,104),(40,168),(42,43),(42,58),(42,106),(42,170),(48,49),(48,50),(48,112),(48,176),(56,57),(56,58),(56,120),(56,184),(64,65),(64,66),(64,72),(64,80),(96,97),(96,98),(96,104),(96,112),(96,224),(128,129),(128,130),(128,144),(128,160),(136,137),(136,138),(136,152),(136,168),(136,200),(192,193),(192,194),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|4=>6
|5=>27
|6=>131
|7=>359
|8=>262
|9=>75
|10=>12
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x9e0bc5f83e1ff28145ad101c70ad42
|5,0=>0xa67528572770f0a60eaa4830b453d8408953a895342aa32b8a329b7317b72ff312ca4c272eb2703c22c56201731d7d118d0218003155ab147e2102e805b9105ac200a35
|6,0=>0xb21b8b0f23b0c35a7f479fc97868e085c4985508824c281b29813f578ee57472872786724477129470f0a6ec9f6dcd46cf746ca6b6c3ae6b2c16b05d6a58b69ea066f1a6583d60eaa5fc985d6df5b6d058b845685f55f7153a275076e4f9854f8994ec644e77b4e6b14a2ea4a12647fd4471fd4584d4580b449bb43f9d422854109d40cbe3ec043cb223c2463a544387eb3734135faf3568c335d032c02328aa321e5319ee305db2fb5b2e8d42dea52d8bf2ce1e2a0ab283852803a2727125d4a2551a24be024110218fd1f6321ef751df9c1df511cc1e19e441973218d021872418620185e61855117926170b616e79168d11444b128501193b10f4710c9c0ec840e7dc0e3850cab30bf200be030a45b09f720980508ff1086020797907560073d70646f063d9062a505d0d05bb2046ba03998029f40261b01b6900b4400392
|6,1=>0xf47c1e1223cca07
|7,0=>0x229db2248a2218021a702136220f2520dcf20a652060a205ff2034d2009b1fa451f7c71f4c11f4a01ec3e1e88e1e3d41df9c1df051d4021d2e71cfa31c8a71c6481c6471c5e71b7211b1181af581a88019fe519b8c1988e1943f192681901a1887f1879c1864117d6c177c41774c16f9f16ea21645715e5615d9415cb4157af151a014ba914b6c14b1f145f81382e134581316412fa61218111e8b11822108f1100db0ff640fdfa0f2930f1920e7020e6d80e3850ddf80dc840d4150ce0b0cdda0cd660c8d80c4cb0c45d0b8d20b8970b4bb0b0fb0aa6d0a45b09f7208d1208c67088fb083ee07e05077f90726906b1a06745065ab0641c0635f062c1061d70551104ff104fc904b9304b0f045df0453403d5a039ab035530321e0309002f7a02e60029f4029c30238901f0901edf0167d0164800e6100cc00092c0076d00359
|7,1=>0x59d845938e58b2a5894958278580e257d835787f57749572f456dd456c7456bb156a0b565ec55f7155db855cd25516c550cb543a353b655314a51ef04fe7c4f7d84f2c54e3344debc4d95d4d41a4ccdc4c5304c4cb4c3994bce34b3e74ab484aaeb4a65c4a37d4a18849dd0496444902f48b8e47bfa471fd470ad4628a4613945b084507e44c74448eb4396142f884299d424924226d41e0341b0f4192a4136340e3740ce840a69409ad405393f6dd3e8ed3d7543cb3a3c7c13c4f43c49b3be6f3b53c3a8713a0dc39316388fb3863d384d63766f36cc936bb736536362923581635148346eb33ccb338f6334633343d2ffec2fc752f9eb2f0002eac12e4382dbfa2d74e2d1fa2ccb52c08a2bcc42bb2d2b6832b5332a80e2a0ab2962728e71285da2819525fbb258f125506251c324fa224f5924c62247c72478123cc6231c2
|7,2=>0xedcc0ea87fe7690e66c6dcb82d9067d54e7d06d7cc0e8c9079c887ac5572c4420c276abb68eba8dcb9eedb96ddb8143b5501b0ce2ab87ea754ea5e87a55e3a39c2a03ce9f9e89bbdc9b64e9ae2598fc596c10969cb94b9a938129275591fd88f6e98b7e38b3c08a0a589ec9895f3875d286f8384774846b983eaf834de812be80c2c7fcbd7f87d7d4a37b49f7ab7a79fce79e87799047964978d9c783c877e6576bcd761b4754a07496a739eb728f4726eb7221171c7e718837156b70ae36ef3c6d12e6b9f66b6136b4f36a77f6a27c69ea06842067ec867c5d677b3677a466f1a655226373d62df961b5c5f7d95f4775e35c5e0a15d4745d0b75c5455bef25b785
|8,0=>0x33485332e832df83185e317ef316c7314a5313b23091b2ffec2ffe52f0cd2e07a2dbfa2c4182b57c2b1c22a4c42a31b2a23e29f8429690285da274d3270702702b26f2b26a6f25961242962427c23f9323cf22370822e8122b0d22a842237a21a7021362211912071f1f9101f8691ed2e1e7d61e3d41dc211d6e31d3531ce8a1b92e1b7211b2df1abf21a894195a919584192191903a18e2a18cf11887f180e117f4a17d42173f516e55158ef153a414f0714d58145f91443b141df135a712fa6120be11c74111df10bae108f11015b0ff960f6820ea370e4390e1a10d4370cff90cbe60b9540b0ab0a69e0a29609ee70938f091c90915d090ed08a590861f083f0081fc073dd0717b063340609705f1605e9505b92058670564b04eec04c850485003f3f03c58030e4030cc029f4026f101e5a015eb0109f009700067700103
|8,1=>0xc74f2c5a50c53eac2d4db989eb5d3fb5b38b55feb4f09b1146adad1acb00a9e42a65d4a2273a00e69a7e398328982d18d5538cb1d8baa18b82b8b4ef8a512882d58540a850527fcb97f87d7de407c8bd7bfe17b49f7ad47775f9751427257771a4f6f61e6f0446bf3e6b2ad6a4cc6a30e692d765d85657986422e63e036358561ed661ba86164d60d315f9cf5ef6a5e35c5e0a15d5d75b78b591f958aa15807f57a7057790574cc5729a56c7454f03548d05407d52e9c5282e4f1de4dd624d97c4d02f4c4cb4c3294c0534b5ce4ac184a57349ee0499d54931647031465a34632845f984597a451d644a724474a446314247a41b0f414b8412df40ec740dbe40a7c401dd3f9023e6f83d98e3d4253d1073d0ce3cb3a3c0b63bd243a9cb3a82a3903137d7137c52375f537274355853512d349ce3495f33fd233f1a33bbd33878
|8,2=>0xf1ce1f0d00e7690df18fcc0e8c887a
|9,0=>0xf0d00cd08ccc0e8bba9ab8e69b7ce7b237ba9e42a2d8f96bc3915588fbe18b8ce880617b194761bc712796e2626baee6a6cf67f0863b685eebb59ab84e8924e14d4c5374c32944f50446074339a422bb400083f0e03dc513c4d33c2073b38637c7637b6a322ea31f80313c52ed782dd6e2d2482b7cf29c69278ca25e6d256d72360f2334522caa220191fb091f13f1ad0e18f50158c213dab12fa6108230c6f40bac80b80d0b73a0a8f906641056ea03f2403da403bc700756001fd
|10,0=>0x954888b2e56ff49643255fef759c845957243aac379de2dac11f24c0b983
|11,0=>0x59c84
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x50500000505000005050000050500000000000000000a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000000050500000505000000000000000000000505000005050a0a0a0a0a0a0a0af0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0f0f0f0f00000000f0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00101010101010101000000000000000001010101010101010c0c0c0c0c0c0c0cf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f00000f0f0000f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f000f000f000f00f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
|0,1=>0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f000000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000c0c00000c0cf0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f000f000f000f00f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f00000f0f0000000050500000505000005050000050500000000000000000f0f00000f0f0000f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0ae0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ee0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0000000000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000000050500000505000000000000000000000505000005050f0f00000f0f0000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
|0,2=>0x30303030303030303030303030303030303030303030303030302020303020200000000f0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0a00000000a0a0f0f000000000a0a0f0f000000000a0a0f0f000000000a0a0e0e505050505050505040404040404040407070707070707070606060606060606f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0c0c0e0e0c0c0e0e0f0f0f0f0f0f0f0f0c0c0e0e0c0c0e0ec0c0e0e0c0c0e0e0c0c0e0e0c0c0e0e0c0c0e0e0c0c0e0e0000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0e0e0c0c0e0e0c0c0e0e0c0c0e0e00f000f000f000f000a000a000a000a000f000f000f000f000a000a000a000af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a05050a0a05050a0a05050a0a05050a0a05050a0a05050a0a06060a0a0606f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0c0c0c0c0c0c0c0c
|0,3=>0xf0f0f0f000000000f0f0f0f000000000f0f0f0f050505050f0f0a0a05050000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f050500000505000005050a0a05050a0af0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f000f000f000f0030303030303030303030303030303030303030303030303000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e505050505050505050505050505050505050505050505050404040404040404f000f0a0f000f0a0f000f0a0f000f0a0f000f0a0f000f0a0f000f000f000f0000f000f000f000f000f000f000f000f000f000f000f000f000f000a000f000a303010103030101030301010303010103030101030301010303000003030000c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0e0e0e0e0c0c0c0c0e0e0e0e00f000f000f000f00000000000f000f000f000f000f000f00000000000a000ac0c0e0e0c0c0e0e0c0c0e0e0c0c0e0e0c0c0e0e0c0c0e0e0c0c0c0c0c0c0c0ca0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0a0a0a0a0a0ae0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0c0c0c0c0c0c0c0c404040404040404040404040404040404040404040404040606060606060606303030303030303030301010303010103030303030303030303000003030000
|0,4=>0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000e0e02020e0e02020000d0d00000d0d00000d0d00000d0d00000d0d00000d0d00000c0c00000c0c5050505050505050505050505050505050505050505050506060606060606061010101010101010101010101010101010101010101010100000000000000000000f0f00000f0f00000c0c00000f0f00000f0f00000f0f00000c0c00000e0ec0c0e0e0c0c0e0e0c0c0e0e0c0c0e0e0c0c0e0e0c0c0e0e0c0c0e0e0c0c0e0e0000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000e0e00000e0ea0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a0000f0f05050f0f05050f0f05050f0f05050f0f05050f0f05050f0f00000f0f0000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0000000000000000101010101010101010101010101010101010101010101010a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a909090909090909090909090909090909090909090909090a0a0a0a0a0a0a0a505050505050505050505050505050505050505050505050000000000000000505050505050505050505050505050505050505050505050a0a0a0a0a0a0a0a303030303030303030303030303030303030303030303030303000003030000
|0,5=>0xb0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0a0a0b0b0a0a202020202020202020202020202020202020202020202020202000002020000f0f0f0f0f0f0f0f0f0f02020f0f02020f0f0f0f0f0f0f0f0f0f02020f0f0202f0f02020f0f02020f0f02020f0f02020f0f02020f0f02020f0f02020f0f020230303030303030303030303030303030303030303030303020202020202020200b000b000b000b000b000b000b000b000b000b000b000b000a000a000a000a00000000b0b0b0b000000000b0b0b0b000000000b0b0b0b000000000a0a0a0a101010101010101010101010101010100000000000000000c0c0c0c0c0c0c0c00f000f000f000f000f000f000f000f000f000f000f000f000a000a000a000af0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f0f0f0f0f0f0f0f0f00000f0f000000000000f0f0f0f000000000f0f0f0f0000000000000000000000000e0e0e0e00f000f000f000f000e000e000e000e000f000f000f000f000e000e000e000e00000000f0f0f0f000000000f0f0f0f000000000e0e0e0e000000000e0e0e0e00f000f000f000f000f000f000f000f000f000f000f000f000e000e000e000e00000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0a0000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000c0c00000c0c
|0,6=>0xf0f0f0f000000000f0f0f0f000000000f0f0a0a000000000f0f0a0a101010101010101010101010101010101010101010101010c0c0c0c0c0c0c0c0000f0f00000f0f00000f0f00000f0f00000f0f00000f0f02020e0e02020e0ef0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a00000a0a0000c0c0c0c0c0c0c0c0c0c0e0e0c0c0e0e0c0c0c0c0c0c0c0c0c0c0e0e0c0c0e0e00000000000000000000a0a00000a0a000000000000000000000a0a00000a0af0f0c0c0f0f0c0c0f0f0e0e0f0f0e0e0f0f0c0c0f0f0c0c0f0f0e0e0f0f0e0e00000000a0a0f0f000000000a0a0f0f000000000a0a0f0f000000000a0a0a0a00f000f000f000f050f050f050f050f000f000f000f000f040e040e040e040e303030303030303030303030303030303030b0b03030b0b03030a0a03030a0a00f000f000f000f000c000c000f000f000f000f000f000f000c000c000e000e000000000000000050500000505000000000a0a00000a0a05050a0a05050a0a000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a101010101010101000000000000000001010101010101010e0e0e0e0e0e0e0ea0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a02020a0a0202000050500000505000005050000050500000505000005050000040400000404
|0,7=>0xf000f000f000f0000000000000000000f000f000f000f000e000e000e000e000000000000000020202020202020200000000000000000202020202020202f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000202020202020202f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a101010101010101010101010101010101010101010101010303000003030000f0f02020f0f02020f0f02020f0f02020f0f02020f0f02020f0f00000f0f000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0a0a0f0f0a0ad0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f00000f0f00000a0a00000a0a000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000e0e0e0ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000f0f0a0a0f0f0a0a00000000000000000000f0f00000f0f05050505050505050000000000000000
|0,8=>0xb0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0a0a0a0a0a0a0a0a000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e505050505050505050505050505050504040404040404040c0c0c0c0c0c0c0c000000000000000000000000000000005050505050505050505000005050000f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e01010101010101010000000000000000f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0c0c0f0f0c0c0000000000000000f0f00000f0f0f0f00000000000000000f0f00000f0f0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f02020202020202020000000000000000000000000000000000000000000000000000a0a00000a0ac0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0e0e0c0c0e0e0000505000005050000050500000505000005050000050500000000000000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0f0f00000f0f0000f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e00000000000000000000000000000000e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e
|0,9=>0xf000f000f000f000f000f000e000e000f000f000f000f000f000f000e000ef0f00000f0f00000f0f02020f0f02020f0f00000f0f00000f0f02020f0f0202f0f0f0f000000000f0f0f0f000000000f0f0f0f050405040f0f0f0f05040504303030303030303000000000303030303030303030303030000000002020202202020202020202020202020202020202020202020202020000000000000000505050505050505050505050505050505050505050505050505000005050000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000a0a00000a0a000000000000000000000000000000000000f0f00000f0f00000a0a00000a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000a0a00000a0a00a000f000a000f000a000f000a000f000a000f000a000f000a000a000a000a00000000e0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0ef0f0f0f0f0f0f0f000000000e0e0e0e0f0f0f0f0f0f0f0f000000000e0e0e0e00f000f000f000f00000000000e000e000f000f000f000f00000000000e000e202020202020202020202020202020202020202020202020202020202020202
|0,10=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000a000a000a000a00000000f0f0f0f000000000f0f0f0f00000000000f000f00000000000a000aa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0000000000000000020202020202020200000000000000000000000000000000f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f00000f0f00000f0f02020f0f020200000000000000000000000000000000505050505050505040404040404040400000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0a0a0000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f02020f0f02020f0f02020f0f0202f0f0f0f0f0f0f0f000000000a0a0a0a0f0f0f0f0f0f0f0f000000000a0a0a0a00000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c00f000f000f000f00000000000a000a000f000f000f000f00000000000a000ad0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e
|0,11=>0xf0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0a0a00000000000000000000000000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a05050505050505050505000005050000f0f00000f0f00000f0f00000f0f00000f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0aa0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0a0a0f0f0a0a000000000000000000000000000000002020202020202020202020202020202f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f02020202020202020202020202020202f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000a0a0a0aa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a000030300000303000003030000030300000303000003030000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f0a0a0f0f0a0a0000000000000000e0e0e0e0e0e0e0e00000000000000000e0e0e0e0e0e0e0e0000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0ad0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0000000000000000f0f05050f0f05050f0f05050f0f05050f0f05050f0f05050000000000000000f0f0f0f0f0f0f0f0f0f0e0e0f0f0e0e0f0f0f0f0f0f0f0f0f0f0e0e0f0f0e0e
|0,12=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f05050505050505050404040404040404f000f000f000f000f050f050f050f050f000f000f000f000f050f000f050f00000000000000000000000000000000000000a0a00000a0a00000a0a00000a0af0f00000f0f00000f0f00000f0f00000f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a00000000000000000000000000000000f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f02020f0f0202c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0e0e0e0e0e0e0e0ec0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e505050505050505050505050505050504040404040404040404040404040404f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0cf0f0f0f0f0f0f0f0a0a00000a0a00000f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f020202020202020200f000f000f000f000f000a000f000a000f000f000f000f000f000a000f000a505050505050505050500000505000005050505050505050505000005050000f0f0f0f0f0f0f0f0f0f00000f0f00000a0a0a0a0a0a0a0a0a0a00000a0a0000000000000000000000000000000000000000000000000000202020202020202
|0,13=>0xc0c0e0e0c0c0e0e50505050505050504040404040404040505050505050505040404040404040400000000000000000000000000000000f0f02020f0f02020f0f02020f0f0202f0f0f0f000000000c0c0c0c000000000f0f0f0f050505050c0c0c0c0404040400000000000000000000000000000000f0f00000f0f00000f0f02020f0f0202f0f0f0f0f0f0f0f000000000f0f0a0a0f0f0f0f0f0f0f0f000000000f0f0a0a00000000f0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0a00f000f000f000f00000000000f000a000f000f000f000f00000000000f000aa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a08080808080808080808080808080808404040404040404040404040404040406060606060606060606060606060606a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0808080808080808f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0505000005050000a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0e0e0a0a0e0ef0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0808080808080808c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0af0f0f0f020202020f0f0f0f020202020f0f0f0f020202020f0f0f0f00000000
|0,14=>0xa0a0a0a0a0a0a0a08080808080808080a0a0a0a0a0a0a0a0808080808080808f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0808080808080808f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0f0f02020f0f020200f000f000f000f000f000f000f000f000e000e000e000e000e000e000e000e303030303030303030303030303030303030303030303030a0a0a0a0a0a0a0a00f000f000f000f0000000000000000000f000f000f000f000f000a000f000a505050505050505050505050505050505050505050505050f0f00000f0f00000000a0a00000a0a00000a0a00000a0a00000a0a00000a0a0000080800000808f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0000000000000000f0f0a0a0f0f0a0a00000000000000000f0f0a0a0f0f0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0af0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a00f000f000f000f000f000f000f000a000f000f000f000f000f000f000f000af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000a0a00000a0ad0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0808080808080808f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0a0a0f0f0a0a
|0,15=>0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c00000000000000000000000000000000f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f00000f0f0000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000000000000000000000a0a00000a0a505050504040404050505050404040405050505040404040505050504040404a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a00000a0a00000a0a00000000000000000000a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0e0e0e0e0e0e0e0ec0c0c0c0c0c0c0c0e0e0e0e0e0e0e0e0c0c0c0c0c0c0c0c0e0e0e0e0e0e0e0ef0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f02020f0f0202f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a00000000f0f0f0f000000000f0f0f0f000000000f0f0f0a000000000f0f0f0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0e0e0c0c0e0ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0c0c0e0e0c0c0e0e0000d0d00000d0d00000d0d00000d0d00000d0d00000d0d0000000000000000
|1,0=>0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000ac0e0c0e0c0e0c0e0c0e0c0e0c0e0c0e0c0e0c0e0c0e0c0e0c0e0c0e0c0e0c0ef0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a00000000f0f0f0f000000000f0f0a0a000000000f0f0f0f000000000f0f0a0a000000000000000000000000000000003030303030303030202020202020202404040404040404040404040404040404040404040404040c0c0c0c0c0c0c0c00f000f000f000f000f000f000f000f000c000c000c000c000c000c000c000ca0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0e0a0e0a0e0a0e0a0e0a0e0a0e0a0e000000000000000030303030303030300000000000000000202020202020202a0a0a0a0a0a0a0a0a0a00000a0a00000a0a0a0a0a0a0a0a0a0a00000a0a0000f0f0f0f0f0f0f0f05050505050505050c0c0c0c0c0c0c0c0404040404040404808080808080808080808080808080808080808080808080a0a0a0a0a0a0a0a00000000000000000000000000000000f0f0f000f0f0f000f0f0f000f0f0f00f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f05050505050505050505000005050000
|1,1=>0xf0f0f0f0f0f0f0f0f0f00000f0f0a0a0f0f0f0f0f0f0f0f0f0f00000f0f0a0af0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a00000000000000000000000000000000c0c0c0c0c0c0c0c0e0e0e0e0e0e0e0ef0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e00f000f000f000f000f000f000f000f000a000a000a000a000a000a000a000af0f000f0f0f000f0f0f000f0f0f000f0f0f000a0f0f000a0f0f000a0f0f000af0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000000f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0a0000000000000000f0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0a303030303030303020202020202020203030303030303030202020202020202f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f000f0f0f000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f00000f0f0000f0f00000f0f00000f0f0a0a0f0f0a0a0f0f00000f0f00000f0f0a0a0f0f0a0a00f000a000f000a000f000a000f000a000f000a000f000a000f000a000f000af050f050f050f050f050f050f050f050f040f040f040f040f040f040f040f04
|1,2=>0xf0f0f0f000000000f0f0f0f00000000000a000a00000000000a000af0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f0000000000f000f000f000f000f000f000a000a000f000f000f000f000f000f000a000a0000000000000000000000000000000050405040504050405040504050405040000000000000000f0f0f0f0f0f0f0f00000000000000000c0c0c0c0c0c0c0c00000000000000000000000000000000c0e0c0e0c0e0c0e0c0e0c0e0c0e0c0e00f000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0e0c0e0c0e0c0e0c0e0c0e0c0e0c0ef050f050f050f050f050f050f050f050c040c040c040c040c040c040c040c04f0f0f0f0f0f0f0f00000a0a00000a0a0f0f0f0f0f0f0f0f00000a0a00000a0a000000000000000000000000e0e0e0e0000000000000000000000000e0e0e0e00000000000000000000000000000000c0c0e0e0c0c0e0e0c0c0e0e0c0c0e0ef000f000f000f000f000f000f000f000f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a00f000f000f000f0000000000000000000f000f000f000f000a000a000a000a
|1,3=>0x303030303000300030303030300030003030303030003000303030303000300f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a00000000f0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0af0f00000f0f0a0a0f0f00000f0f0a0a0f0f00000f0f0a0a0f0f00000f0f0a0a505050505050000050505050505000005050505050500000505050505050000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f0000f000f000f0000000f000f000f0000000f000f000f0000000f000f000f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f000f00f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f005050505050005000505050505000500050505050500050005050505050005000000000050505050000000005050000000000000505050500000000050500000000f0f00000f0f00000f0f00000f0f00000a0a00000a0a00000a0a00000a0af0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000a0a00000a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000a000a000a000a000a000a000a000a
|_,_=>0
def sP:Nat→Nat
|0=>0xb85408030308846140401c0c220d06008060808428150201c0c200d0600803030242e150401c0c050b85408070e82800140200c04010b854080b030282e150f81820000f05018070e8400014020700c0a00050081b0304034130200c0c0100060180b0304000130200c0c01000480811030401e0407018140d0602c0c0a000100606048001007030140004018080200
|1=>0xa8100e1d0800028130202c3806080002408038183210000500807030ac02170c01038060805c2815020380c0a0b84828040b01c3a10000500807030a82e290a8100e06080a02615020380c101404c1807030280014020380c100d04c18070304000140201c0c0a07850080e030401a130200c0c270b850080e080684c130202c0c0a1285408240302834150602c0c0a
|2=>0xb8502a040b018203e0a054080e030403417098100e3d0806878150201c3a100b8502a040381876101d05008071c84034120a81c20171c0b82815020380c100b8502604038182e370a0540e360805c6a140a8100e061a0cc2815020380e061906824040381832310a05408070305c60140a8100e061108c2818038182e2f170502a060805c3c2d0a0540807030645814
|3=>0xb02c0c0a0b854081c030404a140a8102c062410028150201c0c340d0482a040581820250985408470304066140a81016060505c2a0412018201a098540803030042e180a87c0e060084000120602c0c100b84c2a040381820450a05408070306444280901088070304034130201c0c10218502a040b038201a1304808070300420410a8100e3d0b90028151f81c0c10
|4=>0xc0100606080002414020189e100b8502a040181894170a0540806080009c140a8100e060806800180201c0c100785026041201c7a100d0540807030409a140a8100e060800028180200c0c10118502a0c0387420170a054081c030282e140a8100e0611068244c0201c0c251b8502a0403040001e0a118180e030402e14098182017258b82815020189417248502a04
|5=>0xd0482a042e9700c10000480807030ec2e5b0a01c20172d16428150201c0c580b85030040805cae490a0540c100b924a6140a810ac060805c26150601c0c1000048280703064201a2a8540e100b950a6140a81c2017291442815020700c17200502a040181820000a06008060505ca0140a8103806080687815020700c10198502a040387414170a0540807030640200
|6=>0x805cca2e0a05418070304000140201c0c3a2d8502a0403040464e0a054081603040c8140a8104807030c8001402058c60b030400004030402e490a05408070318820170a8100e06190002818020182061300502a040805cae1e0a054080e030403412098100e060d0dc2415030402e1e298502a0403818be5e0a054081c0300420250a810ac1c030400012020700c10
|7=>0xa0540803031cc2e140a8100e010b9682415021c8e207030402e040385c5e380a0540807030402e123801c20171c1bc28150201c0c6e0b8502a0407018201a098100c100b9b42815020580c10360482a040384034260c05408690581854170a8380c100b9a028150601c0c10000502604038402e670a05408070305ccc140a8100e100b8e028150200c0c100b8502a07
|8=>0x38183201118482a0703064200017048280403818e6100b9f428070308820173a0502a043182c0e060805c2a040581820330b8502a042e01820330a05408070305cf4140a810f2060b9002815021e40c10128502a040381864330a05408783b81c0c100b8100e06081d828150201c2e401c0502a0405874201709054081603040ea12038402e523a0502a04018182025
|9=>0x205816060805c2615021ec0e100b8982415020900e064305c28154481c0c100b8b8281503818f8100b94c28150201c0c220805d10120201c0c010b96c2415020380e064305c28150201c0c10118510a150201c0c10000508c84020700c100b8502a0403a0c0c100b8502a0403818201a1d0502a04030ac20170f0502a04038182e400a1082a040386420173f8502a04
|10=>0xa8100e100ba4922140a810b8060806824150201c0c100004828180381820173405108150201c0c10478508c150201c0c194704000140201c0c104685c2414020900e060800028460201c0c220b96c28150201c0c19008e82815021dc4807030402e15038182017460b82815021e01607030402e120201c0c100b85116150222838060805c28150201cf8100b95c2815
|11=>0x80a024150201c0c10478513615020700c100b85026150201c0c100004828850201c32220b8982815020700c010805c24150b01c0c100d1bc28150f8900e060805c2815021100e060826828150201c0c104c8508415022600c100ba5c2815020380e060805d2a140201c20174a0502a040701820170a04c08070305c6e140a87c0e060805c28840a8102c1c030402e14
|12=>0xaa8c0e100ba8828150201c0ca10800028150201c0c101285c28150201c20172b85078150201c0c810c8882e140201c0c220d05c243c0201c0c100d0488415020580c100ba5c28150201d04100ba7c2815022780c010805c24150201820250b92428154e81c0c100b8502a1f0381820000a0100c100b93828420a8100e1d0805c28150381820171727028150201c0c19
|13=>0xa82c0e060805d52140a810e4070304000170a0100e060809428a80a8100e100b95126140a8100e0640a3820170a8100e065380420170a8100e3b0805c4c140a8100e065384000170901088070805c4c140a8114c5c030402e120a0100e060c9cc74140a81088630381820170a0100c7c0805c92140a810d29e030042e140a8102c070e8402e140a8100e1908000ae14
|14=>0xf0502a044c1dc0e060805c2a04038189425090502a0403818201a092c82a040381820170a2c42a07030ac20172984828045801c0c6b0b8502a044c01c0c104d0502a040b038201a130502a070805d5e26570502a040581820170a2142a045581820170a0540807032182e140a8100e06100402e120a0100e063e0402e140a8100e1d0805c28130a810161c030402e12
|15=>0x110402e120a0100e100b96c4c140a8100e3d080682415038186c100bae028150201c04100b84828150201c0c10118e82815022dc0e06080002815020580e060826828150201844170f0516c150201d04b40805c4c15022d40e060805c2815020700c10128502a0403ad002100b9502a16038182025170502a040381904100005c2404038400017290502a04030404a17
|16=>0x8400012232fc0e060805c5c140a8102c07030417a140a81130070805c4c140a811780e030402e140a8108816058182017090100e061105c24140c0100e101285c70140a8100e060ca3844170a0100e061904034120a8100c7c0805c3c140a8117607030402e140a8102c070304046140a810f0070304000170a01c0c730805ca2140a8100e06398402eb90a0100e3d
|17=>0x21ece207030402e15021c80e060805c2415020900e100bb0c28150201c0c100005d84120201c0c100bb0424040b01820254b8502a07080942e26288502a04038402e910a05408070304000140c0100e060800074120a28008070805ca8140a8100e06080cc2e140a8100e06008402e880a810ba9e0300420170a8100e190805ca4140a8100e060808c28130a8100e06
|18=>0xa81c0c101294428420a8100e064088820170a0100e06158402e140c0100e06082690e140a8100c100b92424140a8100e06648882e120a01088070805d86140a8100e06640882e120a0100e06158402e120a0104807031ac2e140a8102c070304034000931808070805ca8140a8100e06083142e120a810f616038182000090100e060805d88140a8100e060c8040012
|19=>0x1e0540807030402e140c0540807030400017678500807408402e7f0a0540807670402e140a8119824030402e140a8100c010b878283c0a8100e191105ca8140a8100e800805cfe140a81c0c10000b82414210100e060809490140a81088070805cae140a859960703040002e0a0100c100b87828460a8100e060809428b10a811945c030402e140a8108e070305c6e14
|20=>0x2a0502a04038402e5b2b8502a1f0701c0c100b848280403818203a3f0502a043c0581c060805c28040b01c0c106a0502a040381820170a2142a0403041a6170f0502a0403818201a0b8602a04038182017690482a04038194210118502a07030411e172c8502a0403818201a092a02a040381820d10b8502a040381840320b84828040381894250a055a007030402e14
|21=>0x805d2e140a8100c730b878283c0a81c0c106e05c5c140a81006060805c28180a8101c07080682e26090113cdb030402e140a8102c070805db0140a8100e100b8e024140a81038060806824150201c0c196b0502a040381832016a8502a04038182028091082a040304034170f0482a04221dc0e060805c2404018182017090502a040381904a70805c2a04038ec2017
|22=>0xbb785c140a8100e010805cae120a81048070305c5e140ab400e060805c24140a8101c070305c5e140a81c20250b95ca2140a810b8dd0304034140a8100e0641065ae140a8100c191105c3c140a8100e061905c283c0a8100e061d8402e140a8100e825a0402e540a8100e100015c28420a810ba5c0304000140a8100e065084000120a0100e060cad0441a0a810f606
|23=>0x381820000a04c0807031cc2e140c0540807030402ee20905008e00701820170a0540807030402e5b0a0540844038182e2f0a054080b038402ec3090540807030404ae10a05408060805c92140a8116a07030402e120a0100e062537c2e140a81048070805c70140a8100e060c9cdaa140a8101c0703040341221010c6070304000170a0100e060b92080140a81c0c10
|24=>0x30402e1e740502a040381876101285c28040381820171d0502a04038186417090502a070805c4cae0a0540807030404a14428540844038402e380a05408070306542170a0540807030640225090540807030042017620540ee7030402e530a054080703040821421055cc07030402e2e0a05408e01201820170a0540807030404a140c054080b038402ee30a0540816
|25=>0xa05408070304000142605408240381864170a0540898038402e380a0540816038182e2f0a05408070805dd4140a8100e100b8e028150201dd2060805c28150201c0c320b85108150201820171d0782815020580e101295c2815020380e100b95c24140200c0c100b8502a04030402e1e300502a040b02c0c100005c24043c81820170a0f02a0403818201a240482a04
|26=>0x304000120a0100e100ba7c28150202c38060805c28150381820177614c2815020900c101985c28150201c0c01080948c15021e40c100b84828150201c0c3b0c8400014038402e572884828150201c0c10198510a15038402e26288502a042201c0c10240502a0403818e6172d8502ad00381820170a0540807030402eeb0a05408161201820230a054080703064208f
|27=>0x38182017090102c07030282e140a8100e060085c244c0a8100e061d8402e120a0100e820805ca4140a8100e060826428850a81130070304090140a810e4160381820000a0100e06508402e140a8100e0600a3c2e120a8102c07030404a140a8100c100bae83c140a8100c100b93824140a811da5c030402e140a8100e060809474140a8100e061909424140a8102c24
|28=>0x210100c100bb003c140a8100e06508404a140a8100e06789ac2e140a810f2060805c28150201c0c195a0040015038402e57288502a042e01820170a3c02a04030402e610f0502a040381894170a0a42a041201820170a2142a040b01820750a054080703065dc140a8100c730b87828b60a81196070805d86140a81c0c10128b828420a8100c100005c92140a810f644
|29=>0xa8100c100b88c3c140a8103807030404a140a8100e060cb5424140abd408160805d86140a8100e060084046420a8100c193985c3c140a8101c07030405017090580e060805de6140a8100e06791282e140a81c0c100b96424140a8580e06080685c140a8100e060823c28420a8102c06080012e140a8100e065085c284c0a8100e060809482140a8100e06080680012
|30=>0xa05408070309c94170a0540807033e1ee100b8502a040381820170a0f136150209038060805c2815020700c100b8510a150201c0c101285084150201c0c10208502a040381832d50a05408f6030402e120a0540807030c82e500a0540847030402e14420540807030402e142105408161201820250a05408630381820170a0540e100b8985c140a8100e06081042414
|31=>0xa8120207030402e140a8100e100d05c4c120a8100e060805e00140a8108807030404a170a054080b038182e400a0540807030404ab3090502a041202c0c100b85108150201dfc060c85c28150201c0c100bbf028150201c0c195a0042e150381820fb520502a040e01820170a0540807030402e6c0a0542c07030402e2e0a05408070c84034260a0540807031282e12
|32=>0xa8100e06398402ec00a0540816030420c140a8102ce60701820170a0540807030402eaa0a0540807030402f050a0540807030882017440502a040381902190805c2815020900e060805c90140a8100e06080682e121e05408b50701c0c100b8502a04038182017820502a040701c0c100b92028150201c0c101985c24140a8100e060c8402e1421054089e030402e14
|33=>0xa8100e068505c24140a8100e06110402e120a10808070304034122105408070304066170a2102a040381820250b96c28150201c0c108405c28150201c0c010805e0e140a8100e064004034170a05408160701820f90a054080e038402e260a0540807030882e120a0f008077381856100b8502a04038182017620482815021e01607030402e140a811c007030402e14
|34=>0x201c0c19398042e140a8100f10030402e140a81c0c360805c5c140a8100e06870882e140a8100e060805c28464205408f40701c0c100b8502a040381820174c8482815021ec0e060805e18140a8113007030404a170a0540807030402f0b0a0558c040381832170a055ea043d8580c100b8502a040381820250b8502a040381832100b85098150201c0c100b848289b
|35=>0x201c0c100b92028150201c0c01080942e120a8100e065384000170a0540807030402e14588540807030400014230102c070304034d90a0540807030402e120a0602a0403818328e0805c28150202c0c100b8510815020580e06080942e140a8104807030402e14230540807030403490090540807030404a000a1082a0403818f8100b8502a040b0380c100bc442815
|36=>0x201c0c82080002e140a8100e060805e2a120a81228160701820170a054087b0b01c0c105f0502a045d81c0c100b8502a040b01c0c10118502a1f0381820170a05408446581c0c100005c2804038182017710502a04038182017090510a150201c0c100ba6428840a8100e063985c24141e05408b50381820170a05408f42201c0c100b8502a07030ac32100b94c2815
|37=>0xa05632043d81c0c100b8502a043881c0c100b8502a040381820170a2110a150201c0c101985c2815020900e06080682e120a8100e060809424142305408078c01820170a0540807030404ab30a0540807032d002100b8540807031f044100b8502a040381832108b8502a040381832a70805c2815020580e060845828150201c20172b848281502059cc07030403415
|38=>0xa05408f40b01c0c100b8502a04038182017608502b1c0201c0c190085c28150201c0c730805c46140a8100e10128002e570a0540807030ac201709050091a0381820170a054087b7302c0e060805c2a046581c0c100005c2804038182017620502a040581c0c100ba682815023d00e060805c2815020580e060800024140201c0cc90805c24140a8108816058182017
|39=>0xa8100e06008402e122305408441201c0c100b8502a048f82c0e060805c2815020580e060806800140a8100e06080002e120a1080807030402e5b090502a048f0580e06080002815021ec2c070304000140a8100e060805c289b0abd408070805c4c140a8100e068e8402e140a8100e068505c28150201c0c190080028150201c0c190808c24140a8100e06080002ec2
|40=>0xbb0c28150201c0c730b85078150201c0c190085c24150381820250b94424140a9101c07030402e6f0a0540e06080682e2e0a05409210381820170a0540807030402ec7090500807030ac44100b84828040381820170a0602a040381820171d04828150201c2017900502a04660380c100b8502a040381820000baa82815022600e060805c24140a8100e060805d2414
|41=>0x201c0c10128508c15020580e100bb0c2815022604807030402e140a8100e06084942e140a8100e100b95c28150201c0c100bc90241502018e6010805c3c140a8100e060805e46140a8100e06254882e140a8100e06398402e1421054081603818201a0b8482a040381820170a2142a040381902800805c28150201820170f0482815021ec2c07030402e120a8100e10
|42=>0x31cc20173f0502a040381820174384828150201c0c7c0c8402e140a8101c07080682e260a05408070349820170a05408982201c0c100b8502a040b32c0e060806828150201c0c3b0805c2815021100e060805c28150701c0c100b9bc2815024082c0608000281502110ee07030402e140a8100e060805c2842260540807031f020000b8502a040581c0c100bc302815
|43=>0xa8101c07030402e870a0540807030402e3a0a0540807030c82e120a0540807032842017090502a040381a4d0e0805c2815020580e060809424140a81048070305c80120a05408070332002170a0540816030402f280a05408160381820176d0502a042e01820000a05408070349c20170a0540807030402e5b0a05408070320968100b8548807030402e6f0a0540807
|44=>0x38182017988502a07030402f2f0a05408070304046120a1082a04038402f2c0a05408160381820170a04c2a040b02c0c100005c28150201c0c100bcac28150201c0c199505c28150201c0c82400402e140a810f6070805c4c140a8100c100b87828150201c0d290805c28150381820250b94428150201c0c2b080002e120a3d40e060805d4a140a8100e06080002842
|45=>0xa05408070304000172d8502a040381820250b85084150201c0c100b88c283c0a8101c07030403417090100e06508402e140a8103807030402e120a0540807030402f330a0540807030402ed5090502a040b01c0c10128502a041201c0c17200502a040384000172b8502a04038182017438502a0403818201a091182a040381820280b8482a044f01802100b8502a04
|46=>0xa05408161201820170a0540816038182025000502a040381820170905084150218c0e060805c24140a8104807030402e9a0a054081c0381820170a0565a040b01c0c100d0540e060805d702e0a0540807030402e14210f02a040381820230a1082a043d9100e060805c28150201c0c100bbb028150205848060805c24140a8100e06398404a170a0540816038182134
|47=>0x210540807030404a17090502a040381820250a1082a040381820250b85078150201c0c100b85084150218c0e060805c28150201c0c100d0002e120201c0c190805dd8140a8100e06080942414210540807030042017118482a04038f42017090502a040381844100bae824140201c0c100b84828b20a8100e06110402eb90a01c0c101285c5c140a810f607030402ed9
|48=>0xa0540807030404a170a0566a0403c3420170a0554607030402ea40a0540807030402e120a1182b380201c0c100b8502a040381820179b8502ae40202c0e060805c28150201c0c19400402e140a8100e061588820170a054081603818201a0a05408079b01832100b8502a040381820170905078150202c0e06080002e140a8100e060805d84140a8100e06508402e14
|49=>0x30400017170502a040381904190805c28150201c0c2b080002e140a8100efe030402e140a8100e060805c283c0ac7008070306420170a05408070805c4c140a8100e062505c2815020900e060805c24140a8100e060805e68140a8100e060805d26140a8127407030402e140a8101607030402e6a0a0540807030402f390a05408070306420be0a0566aa3038182017
|50=>0xb8502a040701c0c100bbe428150201c0c100ba9428159e0100e060805c28150201c0c100bc182815020580e060805c24140a811fa07030402e140a8100e06080682e120a8100e067b8402e140a8102c0b030402e140ab180807030402e140acb408070304034170a8100e060805e76140aa8c08070304034170a05408240701c0c100b8502a040381820170a1182a07
|51=>0x30402f3d0a0566a040b01c0c100b8502a040381820175d0502a0403b9c0c100b8502a04038182017990502a0403c366c100b8502a04038182000480502a040381802100b8482b190202c0e060805c28150201c0c190805d26140a8100e060805d72140a8101c07030402f0f0a055eb2d0381820170a05408440381820170a05408240381820170a0540807030404a00
|52=>0x201c0c100bacc28150201c0c101285c24140a8100e060806800170a0540807030402e14210540807030402f160a0540807030402e230a05409020b01820170a0540807030402e90090502a040381820170905084150232c0e060805c28150201c0c100b88c24140a8102c070304000170a0565c040381820170a0540807030402f090a0540807030402f170a0540807
|53=>0x807030402e140ab900807030402e140a8100e06080002e140acd40807030402e140a8100e060805e1e140a8102c07030402e140a8100e060805c28150201c0c100bbe42815020380e060805c28150201c0c100b8482815968100e060805c28150201dfe060805c2815
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32a0145007a8029400aa0005
|5,0=>0x2e98168c0ae6054302898138c0966048302298108c07e603c301c980d8c06660303016980a8c04e6024301098078c0366018300a98048c01e6
|6,0=>0x13c389c5c4d4e263712e38955c49ce2477120388e5c464e22b711238875c42ce20f710438805c3f4e1f370f638795c3bce1d770e8b0729c386e1bc70dab86b9c34ee1a070ccb8649c316e18470beb85d9c2dee16870b0b8569c2a6e14c70a2b84f9c26ee1307094b8489c236e1147086b8419c1fee0f87078b83a9c1c6e0dc706ab8339c18ee0c07
|6,1=>0x21ab90b9c84ee420720cb9049c818c40571ff38fddc7e0e3e971f138f6dc7a8e3cd71e3b0f01c772e3b271d5b8e91c73ae39671c7b8e21c702e37a71ba30db5c6cce35f71ac38d45c694e343719e38cd5c65ce327719038c65c624e30b718238bf5c5ece2ef717438b85c5b4e2d3716638b15c57ce2b7715838aa5c544e29b714a38a35c50ce27f7
|6,2=>0x1129c886e43c7
|7,0=>0x320418e20c6106288310b986d8c27060c7302417f20be905ec82f2417720ba905cc82e2416f20b6905ac82d241675cb2ce58f72c3c15fe0aef057072b4415820ab1055082a4415020a7105308294414820a31051082844140209f104f082744138209b104d0826441302097104b08254b9286093304918244c120608f304718234c118608b304518
|7,1=>0x41dc20ce10570823840dc204e1017080383fdc1fce0fd8e7e483ee41f520f9907c483de41ed20f5907a573cec1e560f1b078583bec1dd60edb076583aec1d560e9b0745839ec1cd60e5b0726738fb9c5e0e1f0707837fc1bde0ddf06e7836fc1b5e0d9f06c7835fc1ade0d5f06a7834fc1a5e0d1f0687833fc19e1cce106688330419620ca106488
|7,2=>0x51ac28b6144b0a1d850ac2836140ce9fe84fb427ba13cd09df74ebc273e138f09bf84dbc26be134f099f84cbc263e130f097f84bbc25be12cf095f84abc253e128f093f849bc24be124f091f848bc243e120f0900747c423c211d108e0846cba346119308c2745dba2ce115708a3844dc224e11170883843dc21ce10d70863842dc214e109708438
|7,3=>0x619430aa18450c1a86094302a18050bfa85f942faa17c50bda85e942f2a17850bbb75d9c2eae17470b9b85c9c2e2e17070b7b85b9c2dae16c70b5b85a9c2d2e16870b3b8599c2cae16470b1b8589c2c2e16070afb8579c2bae15c70adb8569c2b2e15870abc755abaab6154b0a9d854ac2a36150b0a7d853ac29b614cb0a5d852ac2936148b0a3d8
|7,4=>0x7153b88ddc370e138705c380e1bf70df386f5c378e1bb70dd386e5c370e1b770db386d5c368e1b370d9386c5c360e1af70d7476b6435921ab90d5486a6435121a790d348696bb4961a3b0d1676874341a19fd0cf686774339a19bd0cd776683b32219810cb88658432a21942ec998648c322619030c798638c31a618c30c5a76294312a18850c3a8
|7,5=>0x3d721ea90f4c87a2bbcf9de6d0f2e879343c7a1e2d0f0e8783bbbfe1def0eef8773c3b7e1daf0ecf8763c3afe1d6f0eaf8753c3a7e1d2f0e8f8743c39fe1cef0e6f8733c3981dcb10e517724c39061c730e318
|8,0=>0x8bbcc5be22cf115f88ab4c5366289313b98994c4aa224511199888c442261ff30f788774c39a21bb30d498664430e617530b288554428a213330909843cc1fe20ed306f78334c17a20ad104d98224c0ee606530299810c4062601f300697ffbbfde1fdf0fe787ef4bf5a1f9b2fc497de43ed21f590fa577cf3be5a1f1d0f8687bf43dda1edb2f649
|8,1=>0x9cc3ce42270f337e99baccdb626c9335b99a94cd2a268513399998c4ca626413318898844c1e65fd32f59976c4b9265b912d399654cb0a257512b28954cca8625313290894444a0224ef326f89334c97664ab124d89233c8f6646b122c9911cc86a6425120999004c7e223df31e698ef4475de39d31c598de4c6d2235731a298cd44646631311809
|8,2=>0xad9456a66b44f59a8ac94562a2b0515799ab84d59e6abd35568aa6cd5126a7915348a96454922a3735129a84cd40269f114f08a73cd37e29b0f4d08a63cd2fe296f14ae9a52cd2762929348c8a41cd1f1e8e9146c8a31cd16a68a5144a8a21450e6686314289a10bd0662821340799ffc4fda67db33e499edccf4a679333c099dbccebe274f139f8
|8,3=>0xbe645f0e6f7537b19bd4c5e826f2f378f8bc3c5dfa6eed176d9bb24dd6e6ea5374a8ba145cea2e6337298b904dc622e1f37069b7f45bd66dd936e39b6dc5b4e2d9536c28b5ccdac62d5316a18b4cc5a462d1316818b3cc59c9ecd336627b2ccd9426c9116408b1bcd8be2c50f6208b0c4583e6c0f15ff8afb4d7ba2bcd15dd9aea4d72e6b8535ba8
|8,4=>0x2ffd37f59bf6c5f926fb917d48
|9,0=>0xd094682a340519fa8cf8ce7a633c319d98ce8c6726338319b89cd7ce69e333d39968cc74661a32fb39749cb64659232b919539ca5c650e327719338c95c648e323719129c84ce40631f318f09c73ce37e31af18ce9c63be301f16f38af8c53c627e312d388e8c43461fa30ed186e8c334617670ab184d8c224e0ee7065382a8c10ce062701f38078
|9,1=>0x69be74cd3a5e8d2b4693a348d1a3d9d1a4e8b234473a1a9
|10,0=>0xd67c6b1e357f1ab78d57c6aa1f5411a988d4846a2235011a788
|11,0=>0x1ad77
|_,_=>0
def wAt:=mkWire dB 318 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 1000003 zs)
def oP:Nat→Nat
|0=>0xb8550b8480a055080610c8480805d0e051039190b848038610c8480805d0c848031190b8480b8510a8510204d0b0480385d0a851038510804d0b0480385d0b8510b0480a85108051038610c8480805d0a8510b855021190b8480a8510204d0b0480385d0a8510b84b03855119090b84b0b84a080510304d0b0480385d0b8550b8480a8510b8510b0480a85108051038610c8480805d0b8550204d0b0480a851
|1=>0xb8550b048038510385d0306a038690b8511205e038490a05515851020ae080010b8551105e080550b8490a8510821d1205e070510384d0b0480385d3e05f41055080690b8513981f110511105d03206400510c857008553f0550085e08051021f2158511105d3d84b0585d0a85103861080490c8480805d0a0550b0480b851038550385d0a0550c84835851081a90585e0204d0b8550b0480385d0a0550b048
|2=>0xb8480a851220130b8510b0550385d021190b8480a8510705d1205f07051000510b8554b0550706a0b851030ce0ba110384a0a055038550b0480385d0a0550811e039090b84a0b0900a055498510c8130805d0b8510a85103a410805e0b8550c8480a0551111b0b848080550b8480b8550a055158511105d008550805122053070510705d0585d03851412030c8510805d039190b8480a055030960809500051
|3=>0x3985f080490a0553b857038010b855039f20c8490805d0a0554f041039f90085e080510304d0b0480a05503096000510805d0b8550204103296520510205e4c8490ba130384a080550804a0911b0b8483d8550b0510328241011080690b8510a055039f90085e080513e01f08095000510b8550b855021190b8480a8510304d0b0480385d0a0550384d0b0480385d0a0550306a0805d080550b8510805103919
|4=>0xb855082cd0385e0b8490a055092a30ba100a0550a055020ae080010b8553582d081a90585e1205f1205d0a05503855022be130550306a0b8510b092058550385d03ab55605e0805119055081190b8480a055002a900803080510b8550304d0b0480385d0a05503851039190b8480a851022623d8550585d0b057470510c84b0a8513e053410550085d15853080010b8550306a0705d0b8512e05503a410805e
|5=>0xa0554c05722051038010b855020960b8490a851110515d0551105e0805508055031190b8480a0550b851031190b8480a055080b917051020020b855030610c8480805d0ba3105803038510b8554c05f3d8550b0510807a3981f11051080550306a410530b8510721d1205e07051039190b8480b849410530320a0085d00051020020b855080690b8550b851031f21585108001039ce0b849080492205122053
|6=>0x306a020960d0550b8510324a498510c8130805d0b8550c8480805d0a055080490a055080694ca110ba130384a600513985e008554f051039f90085e031f2410550c8510b84f0b0480a0550b8550b8480a85103ae117051020020b8553dafb0b8570b0510306a3d855038690b8510706a0b851038510b0550385d0c8480a0554c01b03895000510b8550b851081190b8480a8513981f3985d080490b84f0b048
|7=>0x30960005103801020020385d0b8483981f080490a0555984a0b8490a055039090b84a0a0550b84a020960b8490c8480a8510c8550805d3e01f3985d080490b84b0a055031ee0b0510385d1105e0bb1d1105f080550585e0385d0b8510b8554c8510ba130384a0a8510b8550b0510385d0b855080510805d0a851318510b04b0385d0a85105855031ee0585d0585f038510a05505800038510b8550b8490a055
|8=>0xb855038610c8480805d0a055158530c8510c85503855021190b8480a8510b0510385d0b08f0b84b0a0550b8793981f080490b8510c8480805d0a851398680b851080490a8510223e0b8f10804a0a851128f30b8490a05519055081190b8480b849082cd0385e091330c84a0805d0a0555505500803080510b855400510c8570805d0705103b350705e038553981f008550320a080550c8510805d020020a055
|9=>0xb8510b85103a410805e0805d1105c08055039ce110510805d0804a0b8480a0550320a0c8530c8511285f03096000510b8550b85503a410805e0d0550b8510804a3981f080490a055038610c8480805d0a0550b851038550a055039f90085e080510336a6c8510b0130385d4c01b1205d038490b851039190b8480a8510cb5f0805d1105c0805d3985c080510b84b0b84a0a8513981f0b851080492205303801
|10=>0xa8513e8513f0550085e119090b84b0b84a1205e038490a0550b8490c8480805d033967202d0205d0b8550b0480385d080490c8480805d0a055438551205e038490a0551205e070514c04322051038010a851031ee0585d03851700550388d0b84b0a0554c01b1205d0a0553985c0a0552204b038010b855030960b849080510a8511205d038490a0550226d0b8f00804a08262220510705d03096020960d055
|11=>0xa0550810a1285f000510b8550b8480a055032620b0490385d0a055082623d8550b051031ca658510b0570385d1211b0b8480a0550384a0a055030960b8490a055030960b849038550a055038610c8480805d0a0550385d038510804a0a0551205c0b8510a8510b8783981f0a055410570d0550b851080610c8480805d0a055022be130550306a0b8510b8490b04a0a0554c01b22051038010c84a0a0550b849
|12=>0x80490a055031f241055080690b8511285f000510b8550b9090b84a0a0551105e3981f0805503a86081090b84a3985f0b8490a0550b849081190b8480a0550b8550a055039211205c058550ba110a055080510b8480b84903a6d0b8f00804a0a0550c8510805d03096020960b8491985f0ba110a0550705d1205c070510b8490a0550226d0b8f00804a118f10b84b0804a0a0550b84b038490a0550b9310c84a
|13=>0x82cd0223e0b8f10804a0b8510385d020020b8550b9310810a0b84a0a055000510b8550b84a0a0551291b0b8480b8490b84a0a0550b8510b855081a90585e0385103a6d0b8f00804a2e04a0a05503a41250480a055082cd0385e0b04a0a0550385d07068038550b851778550805d0085c080510807a3981f080490a055020021285f0b855039f215851080010b0550b0510385d0804d0b0480a0553e0573985d
|14=>0x38550385d020020b8550306a0805d0b8510a055082cd0385e25055082cd0385e083e50b8530b8f00804a0a0550b8480a055118490b84b0b84a1291b0b8480b8490a0550805d3985c080490a05503b013985e08049081190b8480a0550b84a0a0550b8490a055119090b84b0b84a3985c0805d080490a0553d81b0b0510385d0b84b0b84a08051080490805d0a0550b84b03855023d2031110b055250490a055
|15=>0x8055400510c8570805d1205c038490a0550b8510804a0a851073e50b853038550b8f30804a0a0551205c07051038550ba110384a0a0550b84a0a055039f90085e080518185d810570301d0306a0a8510b851610550585f0385100051038010b8551204305855038510385e0b8490a0551201f05855038510805d7f857030417e85e05857038510c8530805d0205e5185f02041039190b8480a0557d0510705c
|16=>0xb8f00804a0a0550811b0b8480a0550b84a080550a0550b8510b84a0a8510ba110384a0a05508096000510b8550bc251101b08055008020b8550b8510c8570805d038550b8530385d038550306a0b8510804a080550a055030650c8550805d480490805e0a0553d8570585d038510388d0b84b0a0553985e080490a0550385d0585c03851038550b0530385d00803080510b855113e70b853080555d0511105e
|17=>0x805d0a0551201f05855038510b8490385d0a0550b848038490a0550a8510805e0b8511285f000510b8550c8490805d0a055038550b01b0385d008550805d080510331d1105f08055080b9020020b855080550843d0305e0b8480384a0a05586839038550305d0ba130384a0a0553d813038690b85103895000510b8551106a080550b851020050805d080510201d0b0510385d0b9090b84a0a0550c84a0a055
|18=>0xb8550a8510806a0b8510385d07019038550b8570b0510385d8985d07053038550b84b0385d0a055021190b8480a85122057038010b855350550585e038510b04a0385d0a0550384a0a0550804a080490a0558905503be50b85322019038010b855020ae0c8550805d1205c038490a0550b849080510a85115853080010b8555984a0385e0a0550b8550b8480a0550b8510b0130385d0c8480805d0a0550c84b
|19=>0xb8555c851480550805e1205f058550385186839038550305d0b8550385d0a0550808d0b84b0a055038510b0550385d0202d0585d03851730550b0530385d0384a0a0550ba110384a0a0550b851038490a8510b8480b8490a05573857868410305d000510385e0b855410530085d158511105d080557c8550b8530805d158530c8550805d0385d000530b855030960b8490a0550b8510b0530385d0085d08051
|20=>0x385505a910205e038510385d0b8510b8550b8550b84a0a055080960b8490a055030590385d0b8550b8550b0510385d0b8f00804a0a0550201d0306a0b8517b857083e50b8530811b0b8480a055080510805d0b8550b84b0805d0a0550585f03851031110b0550385d05800038510b855080510c8110805d0b84b080490a05503096000510b8550c8550805d0a05503c6d030020b8553d8530585d2205703801
|21=>0xa8510390a0b84a0a0550c8570805d3981f080490a0550a0550b0510385d031ee038690b8510804a080490a055080510805d0a851020960b8490a851021120705d038550b851020020b855658190b0570385d1105f080550a0551105d080550a0550c8480805d0a0553985f080490a055030a25f0510b85703b350705e0385500803080511205d038490a055498510c8130805d0b848080510a851070510705d
|22=>0xb851870550843d0305e22051038010b8550b8510b0570385d41057080690b851073350705e03855021120705d038550301d0385d0b85522053038010b8550b84a0a05515851080010b855021ee0585d038510b8480b8490a055031ee0b0510385d1205d038490a0551143f0305e0805503096000510b8550a851598510385e3981f00855080515a0130c8530805d25057082cd0385e0b84a0a0550b8510385d
|23=>0xb8510a055080010b8550201d520510205e1285f000510b8551205e070513985f080490a055081190b8480a055081090b84a0a0550843d0305e0b8490385d0a05512043038490a05508051082f90b8570385d0701b038556c8510b0130385d0b85503a410805e08459000530b85508096000510b8550c8530c8510805d02112038010b855008550085e080511205e038490a055410550c8510805d0306a03855
|24=>0x7202e038510205d3985c080490a0550b8490385d0a05512043038490a05503096000510b8551205e038490a0550b8510b8480a851118510b84b0a851039f90085e0805199051038020b855024c2878550305e0b84b0b84a0a0559701b9685d020510b0480385d0a0550385d038510b8557f803030410b8550805d11053080550c8570805d0306a038690b8513981f080490a055870570843d0305e020960d055
|25=>0x510b8550205a0385d038490385d0a055000510385d0b8551285f0b8490a0550b04b0385d1205f038490a055039190b8480a055020510385d0b85117051020020b8550804a0b84a0a0550b84b0b84a0a0550b0550b0510385d1581b080010b8550385d038490a0550b849080490a0559a85f0385d0201908096000510b8550b9090b84a0804a0a0550b851038550a055081090b84a0a055039190b8480a055
|26=>0x20410205e0b8480a0559a81d02019033d60201d038510205d0c8570805d1105d080550385d0b8510805d030550804a0a055038510b8550585f038510b84a0a0550b9090b84a0a0550b9090b84a0b8490804a1285f000510b8550b04b0385d0a0550a0550b8510b855030ae0c8550805d0b9090b84a0a0550b84b080510a851031190b8480a0551105e080550a0554804a0805e0a0555d0551105e0805502002
|27=>0x520510205e720190205d0585c038510385d0a05505857038510a8510b851083e50b8530385d0385196841020510b851020510206a0b851020410b85107051038550b8480a055020020b8550c8510805d080010b8557f857030410804a0a0550c8110805d0306a0b851082cd0385e038490a0559a85f020190c8130805d03a910205e0585e038517a85f0201d0b8570805d0204103011000510b855030110305d
|28=>0x30410385e0b8490a0550b8510b8550b84a0a055000530b8550b84b0a055038190385d0805e0a0550b84a0a0550b0570385d0b84b0a0550385d0b8559685d020511101b080557c8550b8539a843020190385d020191105e08055868410305d038020b8550305d030550805e0b855080510a85105811038510c8130805d480550805e0305e038550201d02051038010b855038490a055000510b8550b85303855
|29=>0x205d0b855020190305e0385d0b853038550a05502051
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x418000000000000000000000000000000000000000000000000000001100020000
|6,0=>0x662000017a00000000000000000000000000000002b400000000000000000000000000000004e8090c0fa81b402e800000b080000000054408a00000000000000000000000000000000000000000000000000000000000000000000000000000e3016600000000000000000000000000
|6,1=>0x13d40000000000000000000000094a0000000049108c6000020a800000000000000000008020000000000007a60000000000007460000000000000000000000000006e600000000000000000000000000000000000000000000000001a18000000000000000000
|6,2=>0
|7,0=>0x1bc436906b20d24000033900000ca4000000000000c64000030905f20ba416e62d0c0000b2215e62ad053a0a43000028884f989b413060000000000012a6248c48108e211660000449086310661fd03e187930ec6000039207020dc41acc00000000d06000032206130000178c00000000b4815cc2a18000
|7,1=>0x6150c1180002fe65ed0bc197442e080000b6216842ca60000b0a15e32b4855ccaa1951329c652cca41945328464fcc9da000027064d1098992e325a24a509319233000047d08da11742268440c87880000000430c849800020c640cc8018fd31f463d907920ef31d6839d00000e43000000007110e02
|7,2=>0x44880001102000043a6868d0b98000426883d1061800041088189012000040040000fe99fb23ee87d0c0001f133dc60000f5200003ce67948f119e113bc67744ed180003ac874cc0001cf4000072d0e419c6238487008de21b8436886c88d889ae335666a0cd299a2333e666d0cc19944324463ccc691894
|7,3=>0x578600015c9800056c6accd581aad35528a95151900005406a7100000000530800014a9a9320000a40c00000005188a24d431a8334fe89f0d3c9a7634e660001381a6c44d26000000026724c6800012fa25c34b269551291a4e44966920d229a42347e68ed11c1800000008d10000232245e60001161a284
|7,4=>0x6ac8d491a7200006966d20da29b4230000cf919d20000000000019b980006686cc4d97180006566c9d192900006446000190131d36328c5c98a1b1130000c38d861309360a8c08d7f9afb45f24bd51791aee40000bacd74900005cc6b8916f200005b84b6896b9ad435a26000166a2c9458c6b0cd6092bf2
|7,5=>0xeb080003a9374a8e851cf1b9b373240001cb900000000e50c00000007208e34dc51b87370a4e08dbf9b7c36f08dd11b9137026da6da5000000006cc6d8cc00000006c060001ae235a2
|8,0=>0x8cc718ce301c5d38b4715ce2a1c51389c712ce241c4538847100a1e9c3a386e70d0e189c2e385670a4a131c2338407074e0d1c1738287044e071c0b38107014e011bff37f86fe4dfb1bf337e06fb4df51be827ca6f88def9bdc37b26f58de99bd0379a6f28de413c537846efcdde1bb9376c6eccdd893ae3
|8,1=>0xa427478e8d9d192a2c744ce881d0d3a14741ce821d0229fe73f0e7c9cf639e673c0e769cea39ce7394a711cdf39b87364e6b1cd429a27338e659cc8398a7308e5f9cbc397272d8e599cb0395a72a8e539ca43944527ce4e1c99392c724ce481c8d3914721ce421c8138fc71ece3c1c7538e471bce361c693
|8,2=>0xbba7768eeb9dd43ba27738ee59dc83b8a7708edf9dbc3b7276d8ed99db03b5a76a8ed39da52b44767cece1d993b2c764cec81d8d3b14761cec21d822afe75f0ebd15773ae875c4eb71d6b3ad07594eb11d5f3ab87564eab1d533aa07534ea595483a8a7508e9f9d3c3a7274d8e999d303a5a74a8e939d243
|8,3=>0xd2c7a4cf481e8d3d147a1cf421e813cfc79f0b3c9e763ce679c4b371e6b3cd07994f311e5f3cb87964f2b1e533ca07934f2596492c8c790cf201e3d3c7478dcf1a1e313c5c78acf141e253c44787cf0e1e193c2c784cf081e0d3c165820f029e023bfe77f0efc9df63be857c4ef71deb3bd25798ef19de03
|8,4=>0x35316a33d425a7cb4e1e993
|9,0=>0xe4c5c90b9117202e3c5c70b8d17182e2c5c50b8917102e1c5c30b8517082e0c5c10b8117002dfc5bf0b7d16f82dec5bd0b7916f02ddc5bb0b7516e82dcc5b90b7116e02dbc5b70b6d16d82dac5b50b6916d02d9c5b30b6516c82d8c5b10b6116c02d7c5af0b5d16b82d6c5ad0b5916b02d5c5ab0b5516a82
|9,1=>0x1cf0b9d17382e6c5cd0b9917302e5c5cb0b9517282
|10,0=>0xe903d1c7a30f451e8820003a18f421e823d0079f8f3e1
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 15
def pmP:Nat→Nat
|0=>0x6200000000001830000000000538000000000112000000000041000000000010200000000004000000000000e300000000002a800000000008a000000000022000000000008500000000002100000000000830000000000208000000000081000000000020000000000006200000000001800000000000220000000000080000000000011000000000004000000000000c00000000000280000000000080000000000014000000000004000000000000c0000000000020000000000004000000000000
|1=>0x104400000000040a00000000010040000000004000000000000f2800000000038e0000000000e3000000000038b0000000000e1c0000000003840000000000e0c0000000003820000000000d840000000003600000000000d100000000003150000000000c300000000003080000000000c140000000003020000000000c040000000003000000000000a200000000002830000000000a000000000002420000000000900000000000204000000000080800000000020000000000006e00000000001a0
|2=>0xc03800000000300c000000000aa08000000002a4a0000000008e38000000002280000000000801000000000119a000000000463c0000000011180000000004400000000000e040000000002fc8000000000bf00000000002f68000000000bd20000000002e68000000000b920000000002e3c000000000b700000000002c4c000000000a0000000000022400000000008820000000002200000000000818000000000204400000000081000000000020380000000008000000000001d18000000000722
|3=>0x122400000000043ee0000000010e3c00000000438e0000000010e180000000043820000000010da00000000043050000000010c100000000043000000000010a30000000004282000000001066800000000410a000000001022800000000408800000000102100000000040830000000010208000000004080000000001003000000000400a000000001002000000000400600000000100140000000040040000000010008000000004001000000001000000000000310e000000000c230000000003089
|4=>0x5081c0000000107870000000040400000000010080000000004000800000000c487000000003120c00000000c39f0000000022b04000000008a81000000002220c00000000848f0000000021218000000008485000000002103000000000840b0000000021024000000008085000000002000800000000738f0000000018220000000005b8f0000000013e3c000000004bfe0000000012fc0000000004b9f0000000012e60000000004b820000000012a080000000048980000000012248000000004891
|5=>0x150e0800000005418f000000014ce3c00000005338b0000000148e7800000005238f0000000144e3c000000050bf20000000142e3c00000005078f0000000140e3c00000005038b000000014022c0000000500000000000120a1c000000044b8f0000000102b480000000402ae00000001008200000000402040000000100260000000040010000000010000800000004000000000000c0000000000018803000000005a0200000000149d00000000051e5c00000001439a0000000050e4c000000014392
|6=>0x213e3c00000008438f0000000210e18000000080a42000000020164c0000000805850000000201454000000080207000000020064c000000080180000000020000000000005ca8f0000000162e3c000000058b870000000161e2c0000000583970000000158e3c000000055b8f0000000152fec000000054bf20000000152f6c000000054b9f0000000152e6c000000054b920000000152e3c00000005439f0000000150e7800000005439b0000000150e4800000005438f0000000150e2c00000005438a
|7=>0x1005002000000401010000000100400200000020000000000004940e3c0000010d438f0000004154e3c00000105518f000000415163c00000105438f0000004150e2c00000105418f0000004142e34000001010007000000404000000000080000200000010004800000002001040000000800400000000154a8b0000000550ebc0000001543ab0000000550a4800000015428f00000005502bc000000140080000000050000c00000011428f0000000352f3c0000000d459f0000000350e3c0000000c430f
|8=>0x100010228000020000000000004000081000000c05408f0000024150e3c00000905438b00000205d0e3c00000815438f0000020540e3c0000080dc38f0000020350a2c00000805cb8f0000020160e3c000008056b8f0000020158b3c000008054b8f0000020150e6c00000805438f0000020150e2c00000804630f000002011000800000800ca07000002001883c00000505438f000001404460000000424419b000001090266c00000405628f000001015063c00000405288f000001014276c000004014088
|9=>0x110b0550e3c00442805038f0011020550e3c00440805038f0011000150c3400242905438f0009030140e3c00200805438f0008014940e3c00200505438f0008010150e2c00200105038f0008000050e7800104000419d0002004550e3c00040c05438f0001020540e3c00040807438f0001020160e3c00040805038f0000c2018800800010805038f0000214050420000048054a8f0000120150e3c0000440101980000104150e3c000040054bcf0000100148e3c00004000738f0000100012920000040004138
|10=>0x1001020140e3c400408044b0f1000020140e3c20200405c28f0428014150e7c10200125438f0400014950e7c10000421439f040000244427c10000014409d0400000150e7c09800505428f02200040402000602001402000180400512c3c060008000208010080008082004000c05498f0100020152e3c04000005cacf00c1420550e3c02010814000a0080120150e3c020040000a0e0048034150e3c01000905438f0040014450a3c0100050d428f0040004554ebc01000115428f0020020110e3c00800521478d
|11=>0x200040805438f404b020140e3d00200d05438f4000204944e3c8000001402022000000350a3c41040805038f
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x800000000000000000000000000000000080c00
|6,0=>0x4c00000000000001c8000009030003a00000000000210000000020000000070000000000000000010000000000000000000000000000000400000000000000000000068000800000000000000000007000000000000000000010106a010a800780000024040000000000000000000000000000000000000000000000c030000000000000000
|6,1=>0
|7,0=>0xc54000301c086c080021e10078000e061f0fc4a531e818582315018fe0003271de0604a6c1e020004062ae038181600000040200138941e66078b82a0601a7c003200000320f032c8062a003cc001700000007e00194061502018000803054b6110001950a100800000007810026303000040200c7422f002801dc0f008180000088002022000040000320040c00
|7,1=>0x80022003583c0c110a0540c001101c88001480008040011c0000018141e0659008408d320007e4807801aa064780070aa013f41ea26c008d81a138400200000540002348005418018013a000083ca6001b80d5000378f41800318004a021b918000124800060007804443c13bf09c003907000540007c0823218194ef22698e3c320080402690086c0c240316802ad
|7,2=>0x1000115c1b41e062f0001000000440000083c404062a8180c0f0a9140c05291e8000001045aa0000800fc040b37522002488c68060004152000000008000303c1e00009fcb200078000802360081e06000180a02199ac0203022b00c0c00020c6000305424002518c0c0100800d8e6030880a0a
|8,0=>0x5f2242023a7b1ea66757b4a5856a4328d52c58040bb299198d6a6240cb110da1837d2a8a754c880d095885747d7a171841631a4a49525330896286131e00373715cf23a519416b0b49c4eb8e03e540e0fe17b1a810766804f6c209280ec2b96005af22722c6c47f38b08cd258fad984106d9ac3d216122d0a017aca9d2b91daf0fe5faf309b54160b0a395660455b87b
|8,1=>0x64394fe0386a38dd0a82bb518513683cd6c2ac4d4c8bf1a45cc2789d8a098635dad4e3343721978ec6131186f75bc0cdb311d20eba986b55d68e180a5e6684042d5829a6e208c0de8649a28d35ab660468098b556e31b47d6d11825444e0120bfd98e73bb09d6c5484222a0539ad5acd12c50d289e522960d18682598499744244c369a0dceb20279d1014a2c30a8ae1
|8,2=>0xa87270a968c2
|9,0=>0x32592c263b0a96c260d258328ad4b58f3e9fc3acd4d974516d63a24419f37892f596cf634e9ecc25cb19f4f99bd666d5b5eb0a9ce2a657d6b54a14697b3da3c9df1648b4e595309c3065f657cd85a9558cad59cf9
|10,0=>0xa353678f68dacdecba5abeec11b
|11,0=>0xb5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 50 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_249 9 roots_249 ops++addP pm 1 dom_123 9 roots_123 ops++addP pm 2 dom_233 8 roots_233 ops++addP pm 3 dom_235 9 roots_235 ops++addP pm 4 dom_178 5 roots_178 ops++addP pm 5 dzo_178_8 5 roots_178 ops++addP pm 6 dzo_90_32 5 roots_90 ops++addP pm 7 dom_187 9 roots_187 ops++addP pm 8 dom_179 8 roots_179 ops++addP pm 9 dom_91 8 roots_91 ops++addP pm 10 dom_185 6 roots_185 ops++addP pm 11 dom_90 5 roots_90 ops++addP pm 12 dom_171 6 roots_171 ops++addP pm 13 dom_107 6 roots_107 ops++addP pm 14 dom_250 8 roots_250 ops++addP pm 15 dom_121 6 roots_121 ops++addP pm 16 dom_219 9 roots_219 ops++addP pm 17 dom_115 7 roots_115 ops++addP pm 18 dom_243 9 roots_243 ops++addP pm 19 dom_248 5 roots_248 ops++addP pm 20 dzo_242_8 6 roots_242 ops++addP pm 21 dom_155 7 roots_155 ops++addP pm 22 dom_169 5 roots_169 ops++addP pm 23 dom_163 5 roots_163 ops++addP pm 24 dom_218 7 roots_218 ops++addP pm 25 dom_105 5 roots_105 ops++addP pm 26 dzo_218_32 6 roots_218 ops++addP pm 27 dom_242 7 roots_242 ops++addP pm 28 dom_177 5 roots_177 ops++addP pm 29 dom_210 5 roots_210 ops++addP pm 30 dom_234 5 roots_234 ops++addP pm 31 dom_139 4 roots_139 ops++addP pm 32 dom_227 6 roots_227 ops++addP pm 33 dom_99 4 roots_99 ops++addP pm 34 dzo_243_8 7 roots_243 ops++addP pm 35 dzo_211_32 6 roots_211 ops++addP pm 36 dom_202 4 roots_202 ops++addP pm 37 dzo_219_32 7 roots_219 ops++addP pm 38 dom_211 6 roots_211 ops++addP pm 39 dom_217 6 roots_217 ops++addP pm 40 dzo_210_8 5 roots_210 ops++addP pm 41 dom_226 4 roots_226 ops++addP pm 42 dom_82 4 roots_82 ops++addP pm 43 dom_216 4 roots_216 ops++addP pm 44 dom_146 4 roots_146 ops++addP pm 45 dzo_210_32 5 roots_210 ops++addP pm 46 dom_241 6 roots_241 ops++addP pm 47 dom_240 4 roots_240 ops++addP pm 48 dom_203 6 roots_203 ops++addP pm 49 dzo_211_8 6 roots_211 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_178_8_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_90_32_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_242_8_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_218_32_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_243_8_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_211_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_219_32_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_210_8_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_zo_210_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_zo_211_8_146 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_249 9 s (0,roots_249.map (·&&&dom_249)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_249 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 1000003 zs symsG zs (hk 1000003 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 1000003 ys h symsG ys (hk 1000003 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 1000003 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 27 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 27 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 131 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 131 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 359 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 103 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 359 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 262 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 6 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 262 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 75 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 75 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 12 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_251 gM mpG SD SS NN hAt idxH ori 1000003 mkCut s i=true:=by
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
theorem lowS_254:Lower true dom_254 roots_254 goal_254 11:=lower_slice_b [(0x5500550055005500550055005500550055005500550055005500550055005500,64,72)] (by decide +kernel) lowS_246
def isoMvS_253:List (Nat×Nat):=[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 11:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_239
def dzo_91_4:=0xf0f0f0f000000000f0f0f0f0
def gzo_91_4:=0xf0f0f0e000000000e0c0a000
def gsh_91_4:=0xf0f0f0e000000000e0c0a00
theorem lowS_zo_91_4_91:Lower true dzo_91_4 roots_91 gzo_91_4 8:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_4) [(dom_91,4)] (by decide +kernel) (lower_slice_b (T:=gsh_91_4) [] (by decide +kernel) lowS_91)
def dzo_191_64:=0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def gzo_191_64:=0xfffffffffffffffe0000000000000000fffffffeffffffee0000000000000000
def gsh_191_64:=0xfffffffffffffffe0000000000000000fffffffeffffffee
theorem lowS_zo_191_64_164:Lower true dzo_191_64 roots_191 gzo_191_64 8:=lower_iso_b (d1:=dom_191) (r1:=roots_191) (T1:=gsh_191_64) [(dom_191,64)] (by decide +kernel) (lower_slice_b (T:=gsh_191_64) [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc0000000000000000cccccccccccccccc,0,2),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,0,8),(0xffff0000ffff00000000000000000000ffff0000ffff0000,0,16)] (by decide +kernel) lowS_164)
def dzo_190_64:=0x5555555555555555000000000000000055555555555555550000000000000000
def gzo_190_64:=0x5555555555555554000000000000000055555554555555440000000000000000
def gsh_190_64:=0x555555555555555400000000000000005555555455555544
theorem lowS_zo_190_64_164:Lower true dzo_190_64 roots_190 gzo_190_64 7:=lower_iso_b (d1:=dom_190) (r1:=roots_190) (T1:=gsh_190_64) [(dom_190,64)] (by decide +kernel) (lower_slice_b (T:=gsh_190_64) [(0x444444444444444400000000000000004444444444444444,0,2),(0x550055005500550000000000000000005500550055005500,0,8),(0x555500005555000000000000000000005555000055550000,0,16)] (by decide +kernel) lowS_164)
def dzo_223_32:=0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def gzo_223_32:=0xffffffff00000000ffffffff00000000fffffffe00000000fefefafa00000000
def gsh_223_32:=0xffffffff00000000ffffffff00000000fffffffe00000000fefefafa
theorem lowS_zo_223_32_90:Lower true dzo_223_32 roots_223 gzo_223_32 8:=lower_iso_b (d1:=dom_223) (r1:=roots_223) (T1:=gsh_223_32) [(dom_223,32)] (by decide +kernel) (lower_slice_b (T:=gsh_223_32) [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,0,1),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,0,4),(0xffffffff00000000ffffffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_90)
def dzo_222_32:=0x5555555500000000555555550000000055555555000000005555555500000000
def gzo_222_32:=0x5555555500000000555555550000000055555554000000005454505000000000
def gsh_222_32:=0x55555555000000005555555500000000555555540000000054545050
theorem lowS_zo_222_32_90:Lower true dzo_222_32 roots_222 gzo_222_32 7:=lower_iso_b (d1:=dom_222) (r1:=roots_222) (T1:=gsh_222_32) [(dom_222,32)] (by decide +kernel) (lower_slice_b (T:=gsh_222_32) [(0x50505050000000005050505000000000505050500000000050505050,0,4),(0x55555555000000005555555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_90)
def dzo_175_64:=0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000
def gzo_175_64:=0xffff0000fffe00000000000000000000fffe0000ffee0000000000000000
def gsh_175_64:=0xffff0000fffe00000000000000000000fffe0000ffee
theorem lowS_zo_175_64_164:Lower true dzo_175_64 roots_175 gzo_175_64 7:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_64) [(dom_175,64)] (by decide +kernel) (lower_slice_b (T:=gsh_175_64) [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,0,1),(0xcccc0000cccc00000000000000000000cccc0000cccc,0,2),(0xff000000ff0000000000000000000000ff000000ff00,0,8)] (by decide +kernel) lowS_164)
def dzo_188_64:=0x1111111111111111000000000000000011111111111111110000000000000000
def gzo_188_64:=0x1111111111111110000000000000000011111110111111000000000000000000
def gsh_188_64:=0x111111111111111000000000000000001111111011111100
theorem lowS_zo_188_64_164:Lower true dzo_188_64 roots_188 gzo_188_64 6:=lower_iso_b (d1:=dom_188) (r1:=roots_188) (T1:=gsh_188_64) [(dom_188,64)] (by decide +kernel) (lower_slice_b (T:=gsh_188_64) [(0x110011001100110000000000000000001100110011001100,0,8),(0x111100001111000000000000000000001111000011110000,0,16)] (by decide +kernel) lowS_164)
def dzo_174_64:=0x555500005555000000000000000000005555000055550000000000000000
def gzo_174_64:=0x555500005554000000000000000000005554000055440000000000000000
def gsh_174_64:=0x55550000555400000000000000000000555400005544
theorem lowS_zo_174_64_164:Lower true dzo_174_64 roots_174 gzo_174_64 6:=lower_iso_b (d1:=dom_174) (r1:=roots_174) (T1:=gsh_174_64) [(dom_174,64)] (by decide +kernel) (lower_slice_b (T:=gsh_174_64) [(0x44440000444400000000000000000000444400004444,0,2),(0x55000000550000000000000000000000550000005500,0,8)] (by decide +kernel) lowS_164)
def dzo_182_8:=0x550055005500550000000000000000005500550055005500
def gzo_182_8:=0x550055005500540000000000000000005400500044000000
def gsh_182_8:=0x5500550055005400000000000000000054005000440000
theorem lowS_zo_182_8_182:Lower true dzo_182_8 roots_182 gzo_182_8 8:=lower_iso_b (d1:=dom_182) (r1:=roots_182) (T1:=gsh_182_8) [(dom_182,8)] (by decide +kernel) (lower_slice_b (T:=gsh_182_8) [] (by decide +kernel) lowS_182)
def dzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def gzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00fe00ff00ff00ff00ff00fe00fa00ee00aa00
def gsh_247_8:=0xff00ff00ff00ff00ff00ff00ff00fe00ff00ff00ff00ff00fe00fa00ee00aa
theorem lowS_zo_247_8_182:Lower true dzo_247_8 roots_247 gzo_247_8 10:=lower_iso_b (d1:=dom_247) (r1:=roots_247) (T1:=gsh_247_8) [(dom_247,8)] (by decide +kernel) (lower_slice_b (T:=gsh_247_8) [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,0,1),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000,0,64)] (by decide +kernel) lowS_182)
def dzo_246_8:=0x5500550055005500550055005500550055005500550055005500550055005500
def gzo_246_8:=0x5500550055005500550055005500540055005500550055005400500044000000
def gsh_246_8:=0x55005500550055005500550055005400550055005500550054005000440000
theorem lowS_zo_246_8_182:Lower true dzo_246_8 roots_246 gzo_246_8 9:=lower_iso_b (d1:=dom_246) (r1:=roots_246) (T1:=gsh_246_8) [(dom_246,8)] (by decide +kernel) (lower_slice_b (T:=gsh_246_8) [(0x55005500550055000000000000000000550055005500550000000000000000,0,64)] (by decide +kernel) lowS_182)
def dzo_237_16:=0x3333000033330000333300003333000033330000333300003333000033330000
def gzo_237_16:=0x3333000033330000333300003333000033330000333300003232000022000000
def gsh_237_16:=0x333300003333000033330000333300003333000033330000323200002200
theorem lowS_zo_237_16_45:Lower true dzo_237_16 roots_237 gzo_237_16 6:=lower_iso_b (d1:=dom_237) (r1:=roots_237) (T1:=gsh_237_16) [(dom_237,16)] (by decide +kernel) (lower_slice_b (T:=gsh_237_16) [(0x333300003333000000000000000000003333000033330000000000000000,0,64),(0x333300003333000033330000333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_45)
def dzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def gzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000fefe0000eecc0000
def gsh_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000fefe0000eecc
theorem lowS_zo_239_16_45:Lower true dzo_239_16 roots_239 gzo_239_16 7:=lower_iso_b (d1:=dom_239) (r1:=roots_239) (T1:=gsh_239_16) [(dom_239,16)] (by decide +kernel) (lower_slice_b (T:=gsh_239_16) [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,0,2),(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,0,64),(0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_45)
def dzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0f0e0c0a000
def gsh_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0f0e0c0a00
theorem lowS_zo_251_4_91:Lower true dzo_251_4 roots_251 gzo_251_4 10:=lower_iso_b (d1:=dom_251) (r1:=roots_251) (T1:=gsh_251_4) [(dom_251,4)] (by decide +kernel) (lower_slice_b (T:=gsh_251_4) [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,0,32),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_91)
def dzo_189_64:=0x3333333333333333000000000000000033333333333333330000000000000000
def gzo_189_64:=0x3333333333333332000000000000000033333332333333220000000000000000
def gsh_189_64:=0x333333333333333200000000000000003333333233333322
theorem lowS_zo_189_64_164:Lower true dzo_189_64 roots_189 gzo_189_64 7:=lower_iso_b (d1:=dom_189) (r1:=roots_189) (T1:=gsh_189_64) [(dom_189,64)] (by decide +kernel) (lower_slice_b (T:=gsh_189_64) [(0x222222222222222200000000000000002222222222222222,0,1),(0x330033003300330000000000000000003300330033003300,0,8),(0x333300003333000000000000000000003333000033330000,0,16)] (by decide +kernel) lowS_164)
def dzo_253_2:=0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def gzo_253_2:=0xccccccccccccccccccccccccccccccccccccccccccccccccccccc8c8cccc8800
def gsh_253_2:=0x3333333333333333333333333333333333333333333333333333323233332200
theorem lowS_zo_253_2_45:Lower true dzo_253_2 roots_253 gzo_253_2 7:=lower_iso_b (d1:=dom_253) (r1:=roots_253) (T1:=gsh_253_2) [(dom_253,2)] (by decide +kernel) (lower_slice_b (T:=gsh_253_2) [(0x3333000033330000333300003333000033330000333300003333000033330000,0,16),(0x3333333333333333000000000000000033333333333333330000000000000000,0,64),(0x3333333333333333333333333333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_45)
def dzo_237_2:=0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc
def gzo_237_2:=0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000c8c800008800
def gsh_237_2:=0x333300003333000033330000333300003333000033330000323200002200
theorem lowS_zo_237_2_45:Lower true dzo_237_2 roots_237 gzo_237_2 6:=lower_iso_b (d1:=dom_237) (r1:=roots_237) (T1:=gsh_237_2) [(dom_237,2)] (by decide +kernel) (lower_slice_b (T:=gsh_237_2) [(0x333300003333000000000000000000003333000033330000000000000000,0,64),(0x333300003333000033330000333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_45)
def dzo_218_4:=0x50505050000000005050505000000000505050500000000050505050
def gzo_218_4:=0x50505050000000005050505000000000505050400000000040400000
def gsh_218_4:=0x5050505000000000505050500000000050505040000000004040000
theorem lowS_zo_218_4_90:Lower true dzo_218_4 roots_218 gzo_218_4 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_4) [(dom_218,4)] (by decide +kernel) (lower_slice_b (T:=gsh_218_4) [(0x5050505000000000505050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_90)
def dzo_87_32:=0xff00ff0000000000ff00ff00000000
def gzo_87_32:=0xff00fe0000000000fe00fa00000000
def gsh_87_32:=0xff00fe0000000000fe00fa
theorem lowS_zo_87_32_82:Lower true dzo_87_32 roots_87 gzo_87_32 6:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_32) [(dom_87,32)] (by decide +kernel) (lower_slice_b (T:=gsh_87_32) [(0xaa00aa0000000000aa00aa,0,1),(0xf000f00000000000f000f0,0,4)] (by decide +kernel) lowS_82)
def dzo_245_8:=0x3300330033003300330033003300330033003300330033003300330033003300
def gzo_245_8:=0x3300330033003300330033003300320033003300330033003200320022002200
def gsh_245_8:=0x33003300330033003300330033003200330033003300330032003200220022
theorem lowS_zo_245_8_180:Lower true dzo_245_8 roots_245 gzo_245_8 7:=lower_iso_b (d1:=dom_245) (r1:=roots_245) (T1:=gsh_245_8) [(dom_245,8)] (by decide +kernel) (lower_slice_b (T:=gsh_245_8) [(0x22002200220022002200220022002200220022002200220022002200220022,0,1),(0x33003300330033000000000000000000330033003300330000000000000000,0,64)] (by decide +kernel) lowS_180)
def dzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
def gzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00fa00000000
def gsh_215_32:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00fa
theorem lowS_zo_215_32_82:Lower true dzo_215_32 roots_215 gzo_215_32 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_32) [(dom_215,32)] (by decide +kernel) (lower_slice_b (T:=gsh_215_32) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xf000f00000000000f000f00000000000f000f00000000000f000f0,0,4),(0xff00ff0000000000ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,18),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,36),(4,132),(5,13),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,72),(10,11),(10,26),(10,74),(10,138),(12,13),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,18),(16,80),(16,144),(17,19),(17,25),(17,49),(17,81),(17,145),(20,22),(20,52),(20,84),(20,148),(21,23),(21,29),(21,53),(21,85),(21,149),(24,25),(24,26),(24,88),(24,152),(28,29),(28,30),(28,60),(28,92),(28,156),(32,33),(32,36),(32,160),(34,35),(34,38),(34,50),(34,98),(34,162),(40,41),(40,44),(40,104),(40,168),(42,43),(42,46),(42,58),(42,106),(42,170),(48,49),(48,50),(48,52),(48,112),(48,176),(56,57),(56,58),(56,60),(56,120),(56,184),(64,65),(64,66),(64,72),(64,80),(68,69),(68,70),(68,76),(68,84),(68,100),(68,196),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,130),(128,132),(128,144),(128,160),(136,137),(136,138),(136,140),(136,152),(136,168),(136,200),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|7=>6
|8=>83
|9=>391
|10=>436
|11=>125
|12=>15
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xa908ba32ff598861a118169860d41d
|8,0=>0xdacd8d5548d3f5acbb4ec1f64c1b92c04a2b945ab7506b57ffb4e7ab10ecaeb14addbca8ee8a556ca220e98cc59624e9568e908da8e1b08aa39897608685e864cd8558c849d182ef472928714367112c70cf46e4b26ac8a68e666858a5cfee5c3565a9d85a85a57922573dd558314fb5f4d075402233c3f537ecb340bf330403020e2e2532cc9f2c29c267b32549c24a9824013233cf2034e1f9461f43f17fe517c58174a016c521697b1630814d5d13f7f1380111fba11b041030b0f6cd0d2120d1ee0b16d0ab5c094130424d03738
|9,0=>0x2dc152d4fa2d1f12c40a2beac2be072bb9e2baf12b7a62b1272af2f2a536298f62914b28ec028bce289bb281c527f902792d27709275632693e26348260ed25d0425c15253a42500a24abe2408823b7e222e321ee620ba620943207731f8dc1f8d61f72d1f4a51f0fd1ed181ec081eb731eb3f1ead31e8e01e8981e02e1db1b1d2111cd0e1ccc31c0d11b7491a8a2199ad19521190b218cc9188ef18636183261810317548173a516d8215c8a15a82153f214df714817127b911ff011c2111aa9117921141910ca7107f0106c9106b00ff790fdd50fafe0f9ee0f6d70f6220f2700ec970db840d13d0c9010c3500b8ce0b7ad0b7040b67c0b6620a7b50a6230a2900908308aa708a670888a0862a07dc607af907840064ba0607b05f5c05d7f057e4056f004f4503eca03a2002b4f01f9601499010cd00d0b00a420045f002b9
|9,1=>0x6b0ae692a069033679c866f5166e1c66b1a65ae1650c464ed464d6763ff863fca63db4631f76221f606a9600885f2e25f1425ef9d5ebd85d8465d3015c9be5c9895bcd0586ac582bd5717a569f05617155a4d54e2254d9054c3854a50540c853f6f53d5453c98534ea512d9507e05041b5036b501f7500764fa294f4304f3aa4e68e4e3e14e01a4dfc64d9414d2e64d25d4ce2b4bcff4ab974a69e4a68049ec949aa5499c5497944945448b3848ad24889f485c84809547c3447b484743a4732a47015463a9461974600f45d10454f144a5a448f24479b42ba7428f941ddc4177640e6b40c9440ba040a6d408283ff773fcb73f99b3e6623db193ce523cc6b3ca013c5ab3b7ac3aee53a134392e038ce8386d137f3535ffd3586b34e1334ad833be733b463365d31b6e3152a30e7f301722fd152f9cc2f2332f0832e0692dd92
|9,2=>0xe352be2339e055bda2bdd8a9ad0cd7d0871ce5b5ce37dcd0ddcd0a9cc10ccba2acb97ccadc8c9b93c95eec8f75c6a28c69d1c627ec5ad9c29e4c0670bfcc7b9907b830ab5d2fb5c1eb42eeb3265b2aa7b25ddb1e46b1480b0d81aee53ae78eadacead9a3ac52babfa6ab1d5a9b42a91f6a8226a7e65a7ad7a6deca4e66a485ea4828a43cea42eca3917a14409ff319eedb9e1409dde49cc689bde89a07699be29965d98cfc973f896db994eb29475e9455e938c792d8c917539171890a74907869005d8fd0d8ec3b8d2368ca208c5b38b9cd8b3b389fe3899bc89553887768853387c698638a846d7845fd838c3838808344d826b681610809657ffc87ff3d7f9fa7f24a7e8c57e7777cf3d7cee67bf997a65b799797937f7823177e7576e7575e5a7583c7538074405736a370d7870d03708b4708836fef16e2d16caa76bbd8
|9,3=>0xf7a4af5631ee304ecc6deb371e709be6f57
|10,0=>0x2adc22ac492a4b62a037299ae2995828f9c28a12288712835a2803927e81276a92711626f4926e78259e2259242570e2552e254eb252cd2480f245542419b240c92344222cfa224c5222d82224720ea120e75200ed1fe931f1931e7dc1e49e1dba31d7761d3401d30d1ca521c8f31c23b1c0f01aaff1a1c119fe019f0419c59199f3187ed1785f1776916cbb1636a15ff315b2414eb514e4d1467b143a71413313feb13e3111a891161a1129c1065e105d0105bf105ac1049d103050fcd80fb510f71d0f48d0f3540ee6c0e7c00e3760dbe10ca540c5490be170be020b9980aa470a9cc0a5b50a3230a30608a2507e6807d9607cd7074c407368069c006564060fc0609e05d8205cc305ad0059bc04d1304b660483e0437b0407a03f4903bd5038700339102f37023e101e5901bb2018dd0180e0169c00eda009af00773003c2
|10,1=>0x6dac36d7086d61d6d31b6c09c6afc26a81269e6c694aa68612681776789d66c9066b5c64d586385f622d860fba60cdc603e45f9c85f59c5f4155ecbc5ea465df165de1c5d0805cee85c5d05bf195a16759cad58bfa5801057962576b856e555653355985549b3532ea532e052f20528fc525d8516ec508fb4f63a4ed134e8324e4d54d8c14d6724d1904cc954ca774c3744c0274c0104b6d84afd44a600495d24775e475f8474d8465fc455c245550452a6450d144f1d4461b443174407043d6243009419e8418a4416f540bcd40737402d8402193ffd83fdcd3fc823fa4f3fa473f98e3edf53de9a3d5c23d27f3ccfe3c85f3bdac3bd953bd053bc653b94c3b84b3b70a3b4763ad60395393929a3829f37ad836bff3697b35c92354cb34c9e3469533760334aa30de83082830413300e02fa462f9142f2142d71f2ce062b264
|10,2=>0xb3c41b3995b32ecb1905b12a9b0ff9b09abb082faf05dad93bad591ad45aac348ab110a9a7ba93aea8e84a8b89a7fd6a79b2a7693a6921a5d30a5068a4154a3e40a25c0a241aa1118a041aa034f9f4339f0809ceeb9cc679cc389c1349b9959b6849aa3f9a6f99a5329996997f1b96a8596a1c9689594ff99488094217939dd92d6592394920e691d8691639915799101f90c288fb678f81b8df388ddb38c7418c3798bef68bd528adaa8a33089e5b89d9289a6a897bb8927a891b188e658850887fc087dab877c08730b8680c8658185dc685a5884e6584a3b83b5c824998213281781810b180f3780efb80dec80ceb806b78049f800dd7f1fb7ec0f7e00c7debf7c7ab7c5937c4707bc207bc127b6d579a9879114775217651a7648d74bd2744df74489726d87250671fd7719fa71687714f070b90704576ff386ef856ed14
|10,3=>0xff13bfc218f2530f0b79ef357ebca7ea284e8eb5e738be5d30e532ee3a8fe0fb8e0aa0df0abdefa3de807dc52adb550d71d7d3f7fd32bfd300ed2ad5d1f67d01abceafece739cd6dccbb89cb82fcaf5bc95a7c87b4c7fc5c626ac3eeac34a5c2f68c234dc1f2dc1723c0ca3be1e0bca7ebc20cba48cba3e1b6f69b579bb4ce3b459f
|11,0=>0xf2f5cf0c8beb396e2958df0a7dec90dea95dbc69db393d6578d45f4d3078d29f7cf308cb2c7c6ccac517dc4871c3e3fc39eec1b85bd9d5bc505b4f12b4102b08a3b037fac8f0a911fa8178a6f8ba6728a65dda4cc5a15eb9d9fc9c8c79b4f297a638791d85a0b84713833577db187b93b7acdd7acda7aa8e7856b76c607405473cc6736917176a6f886672c3662fa65e505c6d25b3ea5a180578bf535e850e3a50bdf4f6fb4ef024d52b4cdb14ba7e4a1f3498bc44cc441a2c418e13dbf53d9ee3ceeb3c0493a11138da6380ba36fe436c00362c533f6d32e063264b2d4d12b1ad2ab042a8c529dba2986b2964f28a2e279ab2777426abf23d15230981f2b11e1d61d9861b8c11aefa1a6ae1845718260180be130ba120bc118740fc360e20b0a6ee092f70838607de907c2807b3607a94062e705d8e04b76
|12,0=>0xfff0bdd9d2c6ddca8b4899b3f8e306792e472a9061e185146d3ec662da102bad80eef70c075
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff000000000000ffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa0000000000000000ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000dddd0000dddd0000cccc0000dddd0000dddd0000dddd0000cccc0000ccccffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000033333333000000003333333311111111333333331111000033332222ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|0,1=>0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff000000000000aaaaffff00000000aaaaffff00000000aaaaffff00000000aaaaaaaa5555555555555555555555555555555555555555555555554444444444444444ffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffffffffffffffffffffffffffffffffffffffffffccccccccccccccccffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeccccccccccccccccffffffffffffffffffffffffffffffffccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa3333333333333333333333333333333333333333333333333333222233332222ffffffffffffffffffffffffffffffffffffffff00000000ffffffff000000000000dddd0000dddd0000dddd0000dddd0000dddd0000dddd0000cccc0000cccceeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccceeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000000000000000
|0,2=>0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000eeee0000eeee00000000ffffffff00000000ffffffff00000000eeeeeeee00000000eeeeeeeeffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa00000000ffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa000055550000555500005555000055550000000000000000aaaaaaaaaaaaaaaaffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffff0000ffffffffffff0000ffffffffffff000000000000000000000000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaaffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffaaaaaaaaaaaaaaaaffff0000ffff5555ffff0000ffff5555ffff0000ffff55550000000000000000aaaaaaaaaaaaffffaaaaaaaaaaaaffffaaaaaaaaaaaaffffaaaaaaaaaaaaeeee0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc33333333333333333333333333333333333333333333333300000000000000000000000011111111000000001111111100000000111111110000000000000000
|0,3=>0xffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeddddddddddddddddccccccccddddddddddddddddddddddddccccccccccccccccffffffffaaaaaaaaffffffffaaaaaaaa00000000000000000000ffff0000aaaa00000000000000000000000000000000ffffffffffffffffffff0000ffff0000ffffffffeeeeeeeeffffffffeeeeeeeeccccccccccccccccccccffffcccceeeeffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa3333333333333333333333333333333333333333333333332222222222222222ffffffffffffffffffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeee3333333333333333000000003333333333333333333333330000000022222222ffffffffffffffff00000000ffffffffffffffffffffffff00000000aaaaaaaaffffaaaaffffaaaa00000000ffffaaaaffffaaaaffffaaaa00000000aaaaaaaaffff0000ffffffffffff0000ffffffffffff0000ffffaaaaffff0000ffffaaaa3333333333333333333300003333333333333333333333333333000033332222fafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafaffffffffffffffffccccccccccccccccaaaaaaaaaaaaaaaa888888888888888800000000ffffffff00000000cccccccc00000000ffffffff00000000cccccccc
|0,4=>0xffffffffffffffffccccccccffffffffffffffffffffffffcccccccceeeeeeeeccccccccffffffffccccccccffffffffcccccccceeeeeeeecccccccceeeeeeee0000ffff0000ffff0000cccc0000ffff0000ffff0000ffff0000cccc0000eeeeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffaaaaffffaaaaffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffff00000000ffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ffffaaaaffffffffffffffffffffffffffffffffffffffffffffffffffffffffcccccccc00000000000000000000000000000000ffffffffffffffffffffffffcccccccc3333333333333333333333333333333333333333333333333333333300000000eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee00000000ffffffff00000000ffff000000000000ffffffff55555555ffff000055550000ffffffffaaaaaaaaffffaaaaaaaaaaaaffffffffffffffffffffaaaaffffaaaaffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeccccccccccccccccffffffffffffffffffffffffffffffff333333332222222233333333222222220000000000000000000000000000000033333333222222223333333322222222ffffffffffffffffffffffffffffffffffffffffffffffff3333333322222222
|0,5=>0xffffffffffffffffffffffffffff0000aaaaaaaaaaaaaaaaaaaaaaaaaaaa00001111111111111111000000001111111111111111111111110000000000000000aaaaaaaabbbbbbbbaaaaaaaabbbbbbbbaaaaaaaabbbbbbbbaaaaaaaaaaaaaaaa0000ffff0000ffff000000000000ffff0000ffff0000ffff000000000000aaaa0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaaffffffffffffffffffffffff00000000aaaaaaaaaaaaaaaaaaaaaaaa00000000ffffffffffffaaaaffffffffffffaaaaffffffffffffaaaa0000000000000000ccccccccffffffffccccccccffffffffcccccccceeeeeeee00000000000000000000000000000000ffffffffffffffff0000000000000000eeeeeeeeeeeeeeee000000000000000000000000000000005555555555555555555500005555000000000000ffffffff00000000ffffffff55555555ffffffff55550000ffffaaaaffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaa3333333333333333333333333333333333333333333333333333000033330000ffffffffffff0000ffffffffffff0000ffffffffffff0000aaaaaaaaaaaa0000ffffffffffffffffffff0000ffff0000aaaaaaaaaaaaaaaaaaaa0000aaaa0000
|0,6=>0xeeeeeeeeeeeeeeeeeeeeeeee00000000eeeeeeeeeeeeeeeeeeeeeeee00000000ffffffffffffffffffffffffffffffffffffffffffffaaaaffffffffffffaaaaffffffffffffffffffffffffffffffffffffffffffffffffffffffffeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeee0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000eeeeddddddddddddddddddddddddddddddddddddddddddddddddcccccccccccccccc5555555555555555555555555555555555555555555555550000000000000000ffffffffccccccccffffffffccccccccaaaaaaaa88888888aaaaaaaa88888888ffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaffffffff00000000ffffffff00000000ffffffff55555555eeeeeeee44444444ffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffffffffffffffffffff00000000cccccccccccccccccccccccc00000000000055550000555500005555000055550000555500005555000000000000000000000000ffffffff00000000ffffffff00000000ffffffff00000000cccccccc0000333300003333000033330000333300003333000033330000000000000000ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000
|0,7=>0x55555555555555550000000055555555555555555555555500000000000000000000000000000000000000000000ffff0000000000000000000000000000aaaa00000000000000000000000000000000ffffffffffffffffeeeeeeeeeeeeeeeeffffffff00000000ffffffff00000000ffffffffffffffffffffffffeeeeeeee0000000000000000ccccccccffffffff0000000000000000cccccccceeeeeeee0000000000000000ffffffffffff00000000000000000000ffffffffffff0000ffffffffffffffffffffffffffffffff0000000000000000ffffffffffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000ffffffffffffffffffffffffffffffffffffffffeeeeeeeeffffffffeeeeeeee00ff00ff00ff00ff00aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aa00000000000000000000000000000000ffffffffeeeeeeeeffffffffeeeeeeee5555555555555555555500005555555555555555555555555555000055550000ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa0000000000000000ffffffffffff0000ffffffffffff0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000ffffffffffffffffffffffffffff0000ffffffffffffffffaaaaaaaaaaaa0000
|0,8=>0xffff0000aaaa0000ffff0000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffeeeeeeeeffffffffeeeeeeee00000000000000000000000000000000ffffffffccccccccffffffffcccccccc0000000000000000aaaaaaaaaaaaaaaa0000000000000000ffffffffeeeeeeee00000000ffffffff00000000ffffffff00000000ffffaaaa00000000ffffaaaa3333333322222222333333332222222233333333222222223333333322222222ffffffffffffffffffffffffffffffff55555555555555554444444444444444555555555555555544444444444444445555555555555555444444444444444400000000ffffffff00000000ffffffff000000005555555500000000444444440000000000000000ffff0000ffffffff0000000000000000ffff0000ffffaaaa00000000ffffffff00000000ffffffff00000000ffffffff00000000aaaaaaaaffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffaaaa555555555555555555555555555555555555000055550000555500005555000000000000ffffffff00000000ffffffff00000000ffffffff0000000000000000ffffffffffffffffffff0000ffff0000ffffffffaaaaaaaaffff0000aaaa00000000000000000000ffffffffffffaaaa0000000000000000ffffffffffffaaaa
|0,9=>0x5555555544444444555555554444444455555555444444445555555544444444ffffffffffffffffffffffffccccccccffffffffffffffffaaaaaaaa8888888800000000ffffffff00000000ffff000000000000ffffffff00000000ffff0000ffffffffffffffffffffffffffffffff00000000ffffffff00000000ffff0000ffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaacccccccccccccccccccccccc88888888ffffffffffffffff5555555555555555ffffffffffffffff4444444444444444555555555555555555555555555555554444444444444444444444444444444400000000ffffffff000000005555555500000000ffffffff0000000044444444ccccccccffffffffccccccccffffffffccccccccffffffffcccccccccccccccc00000000ffffffff00000000ffffffff00000000ffff000000000000ffff0000ffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff000055555555555555555555555555555555555555555555555555550000555500000000000000000000ffffffffcccccccc0000000000000000ffffffffccccccccffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaffffffffeeeeeeee0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc
|0,10=>0x555555555555000000000000000000005555555555550000ffffffffffffffffffffffffffffffff000000000000000055555555555500000000000000000000000000000000000000000000ffffffff00000000ffff000000000000000000000000000000000000ffffffffffff0000ffffffffffff0000ffffffff00000000ffffffff33333333aaaaaaaa00000000aaaaaaaa222222220000000000000000ffffffffffffffff0000000000000000ffffaaaaffffaaaa000000000000ffff000000000000ffff000000000000ffff0000000000000000aaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaeeeeeeeeffffffffffffffffffffffff00000000eeeeeeeeeeeeeeeeeeeeeeee0000000000000000000000000000000000000000ffffffffffffaaaaffffffffffffaaaa0000000000000000000000000000000055555555555555554444444444444444ffffffffffffffffffffaaaaffffaaaaffffffffffffffffffffaaaaffffaaaa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000ffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc0000000000000000ffffffffffffffff0000000000000000ffffffffcccccccc0000000000000000ffffffffffffffff0000000000000000ffffffffffffaaaa
|0,11=>0xffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffffaaaa00000000ffffffff00000000ffff000000000000aaaaaaaa00000000aaaa000000000000ffffffff00000000ffffffff00000000ffffffff00000000eeeeeeeeffffffff00000000ffffffff00000000ffffffff55555555ffffffff5555000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000aaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffaaaa0000000000000000eeeeeeeeeeeeeeee0000000000000000eeeeeeeeeeeeeeeeffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffaaaaffffffffccccccccffffffffccccccccffffffffcccccccc0000000000000000ffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeaaaaaaaaaaaaaaaa00000000555555550000000055550000000000005555555500000000555500000000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaaffffffffffffffff00000000ffffffffffffffffffffffff00000000ffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff000000003333333333333333333333333333333333333333333333333333333333330000
|0,12=>0xffffffffffffffffffffffffffffffff00000000ffffffff00000000eeeeeeee0000000000000000ffffffffffffffff0000000000000000aaaaaaaaaaaaaaaafefefefefefefefefefefefefefefefefefefefefefefefef0f0f0f0f0f0f0f0ffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffff0000ffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffaaaaffffffffffffffffffffffff00000000ffff0000ffff0000ffff000000000000ffffffffffffffffffffffffaaaaaaaaffffaaaaffffaaaaffffaaaaaaaaaaaa00000000ffffffff00000000ffffffff00000000cccccccc00000000ccccccccffff0000ffff0000ffffffffffffaaaaffff0000ffff0000ffffffffffffaaaaffffffffffffffff0000000055555555cccccccccccccccc00000000444444445555555555555555111111111111111155555555555555550000000000000000ffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffaaaa3333333333333333333333333333333322222222222222222222222222222222ffffffffffffffff3333333333333333ffffffffffffffff222222222222222200000000000000000000ffff0000ffff00000000000000000000aaaa0000aaaa0000000000000000ffffffffaaaaaaaa0000000000000000ffffffffaaaaaaaa
|0,13=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaaffffaaaa111111110000000011111111000000001111111100000000ffffffff0000000000005555000055550000555500005555000055550000555500005555000000000000000055555555000000005555555500000000555555550000000044444444ffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffff0000ffff0000ffffffffffffffffffffffffffffffffffffffff00000000ffffffffeeeeeeeeffffffffffffffffffffffffffffffff0000000000000000eeeeeeeeeeeeeeee00000000ffffffff00000000ffffffff000000000000000000000000eeeeeeee444444445555555544444444555555554444444455555555444444444444444400000000555555550000000055555555000000005555555500000000555500000000000000000000ffffffffffffffff0000000000000000ffffffffaaaaaaaaffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffaaaaffffffffaaaaaaaaffffffffaaaaaaaaffff0000aaaa0000ffff0000aaaa0000ffffffffffffffffffffffffaaaaaaaaffffffffffffffffffff0000aaaa000000000000ffffffff00000000eeeeeeee00000000ffffffff00000000eeeeeeee
|0,14=>0xffffffffffffffffffffffffcccccccceeeeeeeeeeeeeeeeeeeeeeeecccccccc5555555555555555555500005555000055555555555555555555000055550000ffffffffffffffffffffffffffffffffffffffff55555555ffffffff555500000000000000000000ffffffffffffffff0000000000000000ffff0000ffff0000ffffffff00000000ffffffffffffffffffffffff00000000ffffffffffff0000000000000000ffff000000000000ffff000000000000ffff000000000000aaaa00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffaaaa00000000000000000000000000000000ffffffffffffffffffffffff000000000000000000000000ffffffffffffffff0000000000000000ffffffffffff0000aaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffaaaaffffaaaaffffaaaaffffaaaa00000000ffffaaaaffffaaaaffffaaaa00000000ffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaa000000000000000000000000ffffffffffffffff0000000000000000ffffffffeeeeeeeeffffffffffffffff0000000000000000ffffffffffffffff3333333322222222ffffffffffffffffffffffffeeeeeeeeffffffffffffffffffffffffeeeeeeee0000000000000000000000000000000033333333333333333333333300000000
|0,15=>0xffffffffffccffccffffffffffccffccffffffff00000000ffffffffffffaaaaffffffff00000000ffffffffffffaaaa0000000000000000ffffaaaaffffaaaa0000000000000000ffffaaaaffffaaaa00000000000000000000000000000000ffffffff00000000ffffffffffffaaaaffffffffffffffffffffffffffffffffccccccccccccccccffffffffeeeeeeeeffff0000ffff5555ffff0000ffff5555ffff0000ffff5555ffff0000ffff0000000000000000000000000000000000000000ffff0000ffff0000ffff0000aaaa0000000000000000000000000000000011111111111111111111111100000000ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaacccccccc88888888000000000000000000000000ffffaaaa000000000000000000000000ffffaaaaf0f0f0f0f0f0f0f0f0f0f0f0fffffafaf0f0f0f0f0f0f0f0f0f0f0f0fffffafa0000000000000000555555555555555500000000000000005555555544444444ffffffffffffffff0000ffff0000ffffffffffffffffffff0000aaaa0000aaaaaaaaaaaaffffffffaaaaaaaaffffaaaaaaaaaaaaffffffffaaaaaaaaffffaaaaffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaffffaaaa0000000055555555000000005555555500000000555555550000000000000000
|1,0=>0xffffffffffffffffccccccccccccccccffffffffaaaaaaaaffffffffaaaaaaaaffffffffffffffffffffffffeeeeeeee0000000000000000555555555555555500000000000000004444444444444444ffffffff00000000ffffffff55555555ffffffff00000000ffffffff444444445555555555555555555555555555555555555555555555555555555544444444ffffffffffffffffffffffffffff0000ffffffffaaaaaaaaffffffffaaaa00000000000000000000323232323232323200000000000000003232323232323232ffff0000ffff0000ffff3232ffff3232ffff0000ffff0000ffff3232ffff3232000000000000ffff000000000000ffff000000000000aaaa000000000000aaaaffffffffffffffff000000000000ffffffffffffffffffff000000000000aaaaffffffff00000000ffffffff00000000ffffffffffffffffffffffffffff000000000000000000000000000000000000ffffffffffffffffffffffffffff00000000000000000000333333332222222200000000000000003333333322222222ffffffffffffffffffffffffffffffff000000000000000033333333222222220000000000000000000000000000000000000000555555550000000055550000ffffffffffffffffffffffffffffffffffffffffffccffccffffffffffccffcc
|1,1=>0x55555555000000005555555500000000444444440000000044444444ffffffffffffffff0000000055555555ffffffffffffffff0000000044444444ffffffffaaaaaaaa0000000000000000ffffffffaaaaaaaa0000ffff0000aaaaccccccccccccccccffffffffffffffffcccccccccccccccceeeeeeeeeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeee0000000000000000000000000000000033333333333333330000000000000000333333332222222200000000000000000000000000000000ffffffffaaaaaaaaffffffffaaaaaaaaffffffffffffffffffff0000ffff0000000000005555555500000000555500000000000000000000000000000000000000000000ffffffff00000000ffffaaaa00000000ffffffff00000000ffffaaaa00000000ffffffff00000000ffffaaaaffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc00000000000000000000000000000000555555555555555555555555444444440000000000000000000000000000000000000000eeeeeeee00000000eeeeeeeeffffffffffffffff0000000000000000ffffffffffffffff00000000eeeeeeeeaaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaffffaaaaffffaaaaffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffcccccccc
|1,2=>0xffffffffffffffffffffffffffffffff00000000555555550000000044444444aaaaaaaaaaaaaaaaffffffffeeeeeeeeaaaaaaaaaaaaaaaaffffffffeeeeeeee00000000dddddddd00000000dddddddd00000000dddddddd00000000cccccccc5555555555555555000000005555555555555555555555550000000055550000ffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaaeeeeeeeeffffffffffffffff00000000ffffffffffffffffffffffff00000000eeeeeeee1111111111111111111111111111111111111111111111111111000011110000000000000000000000000000000000000000000000000000ffffffffeeeeeeeeaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa000000000000ffff000000000000ffff000000000000ffff000000000000ccccffffffff55555555ffffffff55550000ffffffff55555555ffffffff5555000000000000000000000000000000000000ffffffff55555555ffffffff55550000ccccccccddddddddccccccccddddddddccccccccdddddddd0000000000000000ffff0000ffff0000ffff0000ffff0000ffffffffffffaaaaffffffffffffaaaa0000000000000000ffff0000ffff00000000000000000000ffffffffffffaaaaffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaaffffffffffffaaaa
|1,3=>0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffff0000aaaa000055555555000000005555555500000000555555555555555555555555555500005555555555550000555555555555000055555555555500000000000000000000ffff0000ffff0000ffff3333ffff2222ffff0000ffff0000ffff3333ffff2222000000000000000000000000000000000000000000000000ffffaaaaffffaaaaffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffaaaaafafafafafafafafafafafafafafafafafafafafaaaaaaaaafafafafaaaaaaaaffffffff00000000cccccccc00000000ffffffff55555555cccccccc44444444aaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffaaaaffffffffffffffffffffffffffffaaaa5555555555555555555555555555000055555555555555555555555555550000ffffffffffffffffffffffffffffffff0000000000000000ffffaaaaffffaaaa00000000ffffffff00000000ffffffff000000000000000000000000ffffaaaa11111111111111111111111111111111111111111111111100000000000000000000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa00000000000000000000000055555555000000004444444400000000555555550000000044444444
|1,4=>0x333333333333333333333333000000003333333333333333333333330000000000000000333333330000000033333333000000002222222200000000222222225555555555555555555555550000000055555555555555555555555500000000ddddddddddddddddddddddddccccccccddddddddddddddddddddddddccccccccffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff000000000000000000ffffffffeeeeeeee0000000000000000ffffffffeeeeeeeeffffffffffffffffffffffffffffffff0000000000000000ffffffffeeeeeeeeffffffffffffffffffffffffffffffff00000000ffffffff00000000cccccccc5555555555555555555555555555555500000000555555550000000044444444ffffffffaaaaaaaaffffffffaaaaaaaa000000000000000033333333222222220000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000ffff0000aaaaffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000aaaaffffffffffffffffffff0000ffff0000ffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffaaaaffffffffccccccccffffffffccccccccffffffffccccccccaaaaaaaa88888888ffffffffaaaaaaaaffff0000aaaa0000ffffffffaaaaaaaaffff0000aaaa0000
|1,5=>0xffff0000ffff0000ffff0000aaaa0000ffff0000ffff0000ffff0000aaaaaaaaaaaaffffffffaaaaaaaaeeeeeeeeaaaaaaaaffffffffaaaaaaaaeeeeeeeeffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff0000000000ffffffff00000000ffffffff00000000ffffff0000000000ffffff005555555555555555555555555555555555555555555555555555555500000000ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000000000033333333000000003333333300000000330033000000000033003300ffffffffffffffff0000ffff0000aaaaffffffffffffffff0000ffff0000aaaaffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00000000000000000000000000000000003333333333003300333333333300330000000000000000000000000000000000ffffaaaaffffaaaaffffaaaaffffaaaaffffffff00000000ffffffff00000000ffffffffffffaaaaffffffffffffaaaa0000000000000000ffffffffffffffff0000000000000000ccccccccccccccccaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee00000000000000000000000000000000555555555555555555555555000000000000000000000000000000000000000055555555555500005555555555550000
|1,6=>0xffffffffffffffffffffffffffffffff0000000000000000ffffffffcccccccc00000000ffffaaaa00000000ffffaaaa00000000ffffaaaa00000000ffffaaaaf0f0f0f0fffffafaf0f0f0f0fffffafaf0f0f0f0fffffafaf0f0f0f0fffffafa0000000055555555000000005555555500000000555500000000000055550000ffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff000000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff00ffffffffffff0000ffffffffffff0000ff00ff00ff000000ff00ff00ff000000ffffffff55555555ffffffff55555555ffffffff55550000ffffffff55550000ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff0000000000000000000000000000000000ffffffffffffff00ffffffffffffff000000555500005555000055550000000000005555000055550000555500000000000000000000000000000000000000000000000000000000ffffffffaaaaaaaa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafaffffffffffffffff0000fafa0000fafaffffffffffffffff0000fafa0000fafa5555555555550000555555555555000055555555555500005555555555550000000000000000000000000000eeeeeeee000000000000000000000000eeeeeeee
|1,7=>0xffffffff000000000000000000000000cccccccc00ff00ff00cc00cc00ff00ff00cc00cc00ff00ff00cc00cc00ff00ff00cc00ccffffffffffffffffffffffffffffffff00ff00ff00cc00cc00ff00ff00cc00ccffffffffffffffffffffffffffffffff5555555544444444555555554444444400000000000000000000000000000000eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeffffffff55555555ffffffff44444444ffffffff55555555ffffffff4444444400ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00ff00ff00cc00cc0000000033333333000000003333333300000000333333330000000000000000000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeeefafafafafafafafafafa0000fafa0000fafafafafafafafafafa0000fafa0000ffffffffffffffff00000000ffffaaaaffffffffffffffff00000000ffffaaaaffffffff55555555ffffffff55555555ffffffff55555555ffffffff00000000ffffffffffffffffffffffffffffffff33333333333333333333333300000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffffffff00000000ffffaaaa00000000ffffaaaaff00ff00ffffffffff00ff00ffffffffff00ff00ffccffccff00ff00ffccffcc
|1,8=>0xffff0000aaaa00000000000000000000ffff0000aaaa3333333333333333333333333333333333003300330033003300330033003300ffffffff33333333ffffffff33333333ffffffff33003300ffffffff33003300ffffffff0000ffffffffffff0000ffffffffffff0000aaaaffffffff0000aaaaffffffffffffffff00000000ffffffffffffffffffffffff00000000ccccccccffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffffffffffffff5555555555550000ffffffffffffffff5555555555550000ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffccffccffffffffffccffcc00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc00cc00cc00cc00ccffffffff00ff00ffffffffff00ff00ffffffffff00cc00ccffffffff00cc00cc00000000000000000000000000000000ffffffffffffffffffffffffaaaaaaaaffffffff00000000ffffffffffffffffffffffff00000000ffffffffaaaaaaaa000000000000000033333333333333330000000000000000222222222222222200000000eeeeeeee00000000eeeeeeee00000000eeeeeeee00000000eeeeeeee0000000000000000fafafafafafafafa0000000000000000fafafafafafafafaccccccccccccccccfefefefefefefefeccccccccccccccccfefefefefefefefe
|1,9=>0xffffffffffffffff0000000000000000ffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffffffffff55555555555555555555555500000000ffffffff00000000ffffffffffffffffffffffff00000000ffffffffccccccccffffffffffffffff5555555555555555ffffffffffffffff555500005555000000000000000000000000fafa0000fafa00000000000000000000fafa0000fafaffffffffff00ff00ffffffffff00ff00cccccccccc00cc00cccccccccc00cc0000000000000000000000000000000000ffffffffff00ff00ffffffffff00ff00ccccccccccccccccccccccccccccccccffffffffffccffccffffffffffccffccffffffff33333333ffffffff33333333ffffffff33333333ffffffff00000000000000000000000000000000ffffffff000000000000000000000000aaaaaaaaffffffffffffffffffffffffffffffffffccffccffccffccffccffccffccffcc00000000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00ccccccccffffffffccccccccffffffffccccccccffccffccccccccccffccffccccccccccccccccccccccccccccccccccffffffffffffffffffffffffccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffaaaaaaaa000000000000000000000000000000000000000000000000ffffffffffff0000
|1,10=>0xffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff00ffffffffffccffccffffffffffccffccffffffffffccffccffffffffffccffcc0000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff0000000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000ffff0000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff005555555555555555555555555555555555555555444444445555555544444444ffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaa0000000000000000555555555555555500000000000000005555000055550000aaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffaaaaaaaaaaaaffffaaaaccccccccccccccccffffffffeeeeeeeeccccccccccccccccffffffffeeeeeeeebbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaabbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaa3333333333003300333333333300330033333333330033003333333333003300ffffffffffffffffffffffffffffffff33333333330033003333333333003300ffffffffffffffffffffffffffffffff0000000000000000ffffffffaaaaaaaaffffffffffffffff0000000000000000ffffffffffffffffeeeeeeeeeeeeeeee
|_,_=>0
def sP:Nat→Nat
|0=>0x170040007160180a04050ac000703014080a048a802280f814080a0189c0e06028101425008900007028101423018880200038180a040c80c02200001c3e0502028061e008002a0703014080a04874020703014081a0c80c02000b8540c05020242c010a81c0a040502428010901c0c05020441210038340a0405024180b03814080a048200200038180a04018080200
|1=>0x801c0a040500c8222008000e1f0281086030081c0c050200c2c0c008000e0602810320a01900020703014083f018dc0200038180a041f02812010001c0c05020ec06010005c2a060281014091c8042e15030140838050240207030140813048dc0200038180a04050246a010001c6806028100633008000e06028c81409188380e06028102609180380e0502028062f
|2=>0x202812500701c0a040500c9a0c00800960703014080a048040e06028101409060041615039300c05020281201258180a04050240207030140803198040007068140843018000e0602810322b080b40c05020281226009200e060281006470081c0a040500c442e008000e06028108c0a048042a07030140809018580207220180a040502402000901c0c05020281201
|3=>0x8828120c0701c0c050202812012f0002a07030140813048e402070301408192e80c0200038d00a040500cb8010001c680502028065b008002e0602810145a0701c0c050202812012c81c0c05020281203009602e1503014085705024020703014080a0195402002981c3e050200ca4010001c1a0502028120b03814080a0480c9a010001c1e0502028a2010001c1e05
|4=>0x81c3e050202806012c81c0a040500cd6010001c0a040502428010001c0c05190242c01000540c050204cd0010399c0c05190242c010001c0c05021981403008002407078340a04050241c0707814080a28038ca0602810c803070540e060281014090098c0c050200c8e62008000e0519064062200984000707814080a2f8040015078340a040502418010b8180a04
|5=>0x38180a040500cbe01001d00e0602810260a0480424070301408030b0040007078340a0405024180e0b8540c05020fc143a0081c0c05020281273008005006028101409391200c050202806620085c0e06028101216008002e1503014080a04958020703014643f048e402000383c0a04051c00200328180a04378ac006e038180a040194802000a81c0c05021a81409
|6=>0xe80400790383c0a040500c02003c01c0a040500cee010001c0c05020641403210040e0f028101471008000e06028102203238040017038180a040c80c0221000480e0602810260a1d00400070281014031118802002981c3e0502028060e009d00e06028107e0a018040e051906414031100400650a8180a040982402290a818080a019d40200038180a04378285600
|7=>0x500c02001481c0a040500d060e0081c1a06028c814090701c0c050204c140900a080e0640814080a0180400800b81c0c05190280200038180a040500ca00e1481c3e050202856030701c0c05020281236009fc000703014080a019f802000b8180a0405024180e009f00e06028101403008000e06028109c7b0500c02000383c0c05020281236008000e06028101409
|8=>0x4a804000703014640a048e40200038180a321c0281201002500e06028101403498040091038180a040500c02000381408110500d20010001c3e0602810140347838028c038180a040500c02000399c0c0502028068b07004a61503014080a04804500602810140945004000703014080a01a1c020003a180c05020280601000480e0d03014080a0480c1c07420180a04
|9=>0x204c0601001940c05021bc0601002800e1f03014080a01804001703014080a048d80200038180a040c80d3e0e0081c0c0502028069e008000e0f0281014034e004000703014640a049400200038180a040526806010001c9406028101403008000e060281026190e804000703014080a01a5c0200038180a044b00c02210001c0c0502028128a070040e0f02810142b
|10=>0x480c2c010001c1e050202806ad00801580707814080a15804000703014080a01aac020003aa80c0502028060c008002a06028101409130040e1f028101403070055207030140819052a006010001c0c05020fd4e0a0180400a60387c0c050202806010901c0c050202806a5008000ea403014140351804001703014080a018d802000383c1a0502028120e5081c0c05
|11=>0x1ad01c010387c0c050202806b8008002a07550180a04050240601038180a04052d806010001c3e05190280601590000e060281014035a838000703014081a0500c0200038180a3205025680e009240e05020280690008000e0f0281014035980400b10387c0a040500c02000387c0c050200d60010001c0c050202806ae008000e0f028101409280040007338180a04
|12=>0x1ca8060281014034780400bf0387c0c050202806010001c0c050202806be008000ea403014080a01a2c02000901c0c05020287401348000e0602810320a01af402005e01c0c05020280601001b40e06028101403008000e0f0f814080a158380e060281014ba018040007338180a040524c02000b81c0a040c8280622008000e0602ae414035180400070f814080a
|13=>0x8000e0f0281014095a038020703014080a04804d282038180a040500d8c010001c0c05020281201628000e0602810260a15a08000703014d8110500d46010001c0c0502024061600801880703014080a018040065140180a040c80c1ca203818080a019d402000a81c0c05021b0260a048040e0602810140300880000703014640a04b080200038180a32050258201
|14=>0x1c02812010001c3e060281014036a80400d3038180a040500c020003819a2050202806010001c0c05190fc1409070040e06028101403678040007030140819018056e070301408a70500c0200038180a0405338d200038180acd0500c020003b2c0c050202806010001d9206028101403008000e0602810d81301b2002000b81c1a060281014090731c0e1f028101403
|15=>0x1c0c050202806d7008000e06028101409018c01c76038180a040d82806010001c0c050213814031b00400280383c3e050202856000b8180a040516802003281c0c040c80cea010001c0c0502028060c1b804000703014080a0195818010001c1e050202812c1008000e06028109c0a0480c1c01038180a040500dac010005c0e060281014091c8040017038180a04
|16=>0x801c217038180a3205004000703014080a6f80c0200038180a041f8240639008000e060281014de0180400dd03014080a01804000703014080a01b700200038180a6c0982806a300800c00707814080a04804000703014080a01b6c020003b680a040500c0200038180a0405024063700801b20703014080a018040015038180a040502406560081c0a040500d2001
|17=>0x801d60707814080a01804000703014643f2b82812010001c0a040c80c4401308000e06028101403750040007338180a040500dd2010001c0c0502064060e00addd007030140813050ac00e6038180a040500c020003b900c050202806010038c0e06028101403008005006028101403390000e060281014032d8300200039300c050202812010001c0c050202806e2
|18=>0x1c1e0502028129d008000e060281014f101804001c038180a040d8640601000a4500f02810142b0001cce060281014035d8040017038180a32052d40200038180a04050acd2820001c0c0502028120e00bc05006028101403138000e3403014080a1d00c02000a81c0c050202812032d8040e1803014080a01a2c0200038180a04778280601003b40e06028101403
|19=>0x281014037480400170301408110500c1801000541e06028101409060042e0703014083f050241c01038180af50500c02001481c1e05020287401001e80e0f028101409008000e670301408032900400170301408110502418010001c0c050202806f4008000e0602810260a1d03002000383c0a0405025e601000480e060281014031c8040012038180a041c0280601
|20=>0x5024060c070540e06028107e0a1d00c02a20381808190500cea01000700e06028101409070042e0703014080a7900400492401c0c05020280601038180a040500df201000540e0602810260a1d024020703014080a01be002000387c0c0502028068b070040e060281014f70180400530a83c0c050202812013b01c0c05020641403070040e060500d4675008000e06
|21=>0x7814080a018040007030146457050240200038180a045386414030080208070f8180a040500c02070301408190191c0200038180a040500e04010001c1e0502028a0010001cce06028100616008000e060281014038080400ff038180a040c82806017e01c0c05020280601003ec0e0602810140300800ca0602810c803008000efa03014080a018040007068180a04
|22=>0x81c0c050982856a3008000e06028100616008000e06028101403858040007033280a040500c1c290399c0a040500c1c0103860ce06028c8140900802140703014080a01804000703014087b0500c18010001e10051902806010001c0c050204406100001c0c05020fc06c30700528060281014035d804000703014080a01c1802000901c1e0d028101409008020a07
|23=>0x8880c0200038180a040c82806e2008000e0602810143a06004d2005301c1e1f0281014030081c0c050206414df01804010e038180a040500c0200038180a043d828120300800240703014083f0500c1c010381408130c80c4401004300e0602810140300800240602810220a018300200039500c0502028068b008002407030140813050241c011681c0c050204c1409
|24=>0x500d16010001c0c05020fc0639008002e07030140857050240200038180a040982472010001c0c05020280640008000e060281014038a004000703014080a018dc0200038b00c05020280601002500e06028100652008000e06028101403890040015038180a04050e812013481c0c0502029e403070002a0703014080a04804d21503014080a019c4020703014080a
|25=>0x982856000387c0a040500c02a90001c0c0502028071d008002a06028109c0a0480c0207030140813019880200038180a328e02812010001c0c050202806018d8000e060281014038d00400a2038180a040c82856030701c0c05020280718008000e060281014038b8040007030140819053dc06010001c0c0502028071607000521507814080a158040007550180a04
|26=>0x500c0200038180a040500c03230005c2a0602810220a04804ca07028103203110040121038180a040500c02003c0180a040500d76010001c0c050500ddca3008000e1f03014080a01be402009001c0c050202806010001c0c040500ceac800800240703014080a048380269038180a0405024020b038180a0409844062e008000e060281014038f004002d038180a04
|27=>0x2702806010001c0c05020fc1403950040007030140819018042007030140803294a40200038180a040980c600e000480e0602810ae0a0180400070301408380500c18010001c0c050200ca401410000e06028101409009c80e060281014090098c0128038180a040500c02000387c0a040549c0601001200e06028102603008000e05020280622930040124038180a04
|28=>0x1cb402000383c1a0502028120c008000e06028c80652008002e1503014083f05024020703014080a01cb00200038180a040502406310701c0c051902874c30080052070f814080a01a4c0200038180a04054ac06010001c0c05190fc143a0480400070f8180a040185802000b8a00c0502028120e0a81c0c05020e01409018040e0f02810142b5a004000703014084f
|29=>0x9828120c070040e05020280614008000e0602810261901988020003cd00c050202807330080158070301014033a8040007030140819018066400038180a0409a5806010001c0c0502028072a008000e06028101409009fc000703014080a048380272038180a040500c03310001c0c0502028072f008000e0602810142b058025c0703014080a04804000703014080a
|30=>0x495802009d01c0c050202806010001c0c05190fc14ce008000e0602810d40a0480400170a8180a04050e812010a8180a04088281203060040e060284415390180400fe0a8180a040500c0200038180a04054e0060c008005a06028101403130040007030140813054dc0200038180a041f828060c07004520707814080a048380217038180a04054d40200038180a04
|31=>0x2028061e00800520707814080a15838000703014080a048301c013481c0c051902812ce0705c5a060281014090081c1e0602810142b45804000703014080a018067a0003cf00a040500c02000b81c0c050200ca4010001c0c05020fc14031b004004b03014080a01804000703014080a9c0240601001940c05020640662008000e060281032031c804000703014640a
|32=>0x20281203008000e4a03014080a0183002000b81c0c0502028125600802860703014080a018040142038180a040500c0200038180a321f8287401002500e0f02810142b008000e06028101403a08040007034fc0a040500c02000387c0a040194802b20012c0e06028101403008000e0f02810143a5a004000703014080a9b804d200038180a040500e7c010001c0c05
|33=>0x500c0200038180a041f95c140300800dc07078180a040500c0200a481c0c05020280601001240e06028102603008000e0f06814140351804000703014080a9c00c02000b81c0c05020fc143a008000e060281014032d0380e6703014080a04a4c0200038180a040500e8e010001c0c05020280746008000e06028101403a200400150383c1a05020281201039280c05
|34=>0x38180a040882812030094c2e0703014640a008000e3403014080a0183002008001c0c050202806010001c0c0502028074e008005007338180a040500c0200038180a048e0281203008000e06028c814030088400940383c3e050202806010005dd006028101403008000e0602812980a018040065038180a040d86406010001c0c050202807300080158070352c0a04
|35=>0x28101403ac804000703014080a01d600200038180a04050241c013481c0c050202807560080052073383c0a040500c02000b81c0c050202aa603008000e0602810260a158380154038180a040500c0200038180a04a902806010005c2a0602810220a01804000703014080a01d440200038180a04050ac06820001c0c05020280750008000e06028c81403a78040015
|36=>0x180400650a81a96050202806010001c0c05021f41403008000e06028101403ae00400071a0180a040502406010001c0c0502028075b008002407068180a040500c02008c81c1a060281014030080038150301408130500c0200038180a040500c02720001c0c0502028061d008000e06028102203070840015038180a040500d1001004140e06028101403008000e06
|37=>0x3500e06028101403008000e0f0281014034a804000703014083f0500c1801002880e0602810320a018380228038180a0405024060e1481c1e050202812010001c0c05021b0261901804000703014080a01cd40200038180a040500ec001000a00c0502028068a008000e0602810260a048300200038180a040500ebe01000a45006028101403070000e0602810155e
|38=>0x1f828120300d900e06028101403008000e67550180a04050240601000b40c05020280601410000e06028c81403b1004001ca501c0c050202806010001c0c05020fc320a0183802070301408570500c0200038180a041f86414031700400290383c0a04050ac02000b8a00c0502028060e0001c0c0502258140307004000703014080a018044e00140180a040500ec201
|39=>0x301408110500c02000b81c0c051904414010014c0e6703014080a018040065038180a041f80c02005601c1e05020280601005a00e06028101403008000e06028107e0a1d02406010001c0c05020285603072080166038180a040500c0200038180a040500eca01004540e06028c81403008000e0d03014080a0480c1801002880e0602810142b018040015038180a04
|40=>0x38180a040c8ac06010001d5406028101409018040017038180a040500c02210001c0c0502028076a008000e0602810140307004e400038180a040c8280641008000e0602da4080a0180400150383c0c05020285601003a00e0602810142b018002407078180a040502402000e0540c050202806010001c306703014080a01804000703014080a1d00d8601000482e07
|41=>0x500c0200038180a04050e8060c00800500703014083f0c82806010001c0c0502028060e0089c00070301408d80500c0200304100e0602810140300800a60703014080a04804000703014080a15838d2001481c0c05020281203070040e0602db4140300800ca1503014080a0480c020703014081b018044200038180a040500ed801005282e0703014080a018040065
|42=>0x9101c0c050202806010001c3e0602810140349804000703014080a01bb81c00038600c050202806010001c0c0502028740342804000703014086c0982812010001c0c050202807480080092070301408110500c0200038180a040c828062e008000e060281014030084000290383c0a040500c1c010001c0c05020280685008000e0665014080a01804016f038180a04
|43=>0x20280601410000e060281014035780400070301408190500eac010001c0c0502028122600802e80703014080a01804000703014080a01dcc0200b901c0c05020280601004000e0602810320a018040080038180a040500c02000a81c0c05020287409018040e06028101403b880400070301408110500c1c820001c0d70028101403008000e0602810d83f0500c0200
|44=>0x1c0c0502470140300801440703014083f0500c0200039500c050200ca4010001c0c05190441403070000e06028101409019580200039500c050202806bb008000e06028107e0a01b380200038180a040986456010001c0c05020280775008000e0602810260a04b380200038180a0405026dc01000b40e0f03014080a0180400070301408960500c0282000a00c05
|45=>0x202812030081c0c050215c320a01804000703014083f0982856010001c0c05050ac06a300800522d03014080a01804000703014080a0180552000399ca806028101403008000e0f03014080a04838020703014080a01a141c010001c0c0502064060e00884a60703014080a0183802003001c1e05020280601000700e060281026110180400290387e9605020280601
|46=>0x10de0007a038180a320500c02001481c0c05020285603070000e06028101403478040007260180a040500c02000b8b40c050202806010001c3e06028101403ae00400a2038180a040c8285603008000e06028c814034e8040012038180a0405024060e0081c0c0519028120e0081c0c05025dc1403008000e0602810220a0480c1c070301465760500c02001681c0c05
|47=>0x3014080a0480cb6010001c0c050202a4e03008000e060281014031303802001481eba1f028101403008000e670281014035a004000703014080a01df40200038180a040d8280601410000e06028101403be0040065038180a04bd80c0200bd01c0c050202806010001c680602810140300800ca0703014083f0c80c0200038180a040500ef2010001c0c05020280601
|48=>0x140180a040500c0200038180a110500d46010001c0c0502028069807004920703014080a0180400280383c0c05020281201000540e0602810260a04804ca2803014640a01804000703014081b0c80c0221001940e0602028067500800f40707814080a018040007030140813a980c0200038180a040502406ce0701c1e0502028069d00801fc0703014080a018040007
|49=>0x500c84010001c0c05c00c81403008002e070301408110500c1c00038180a040194802006001c0c05020641403008000e060281014035d804008e038180a040500c0200038180a040880c02210001c0c051906c1403008000e06028107e0a1d00c0200038180a040500c1c01548000e0602810260a1d0240200038340c0502028060c008000e06028101403bf804001c
|50=>0xa00e060281014034c00400070301408190500c1c014105c0e06028101409070040e0602810320a01d340200038180a320502586010001c301f03014080a01804002d038180a04050ac0600c201c0c050202806010005c5006028101409008000e0602810140370004000703014080a0480f0601000540e0f06814080a01804000703014081901e080200038180a04
|51=>0x202806010001c0c050202806bb07004000703010320a019d402002981c1e0602810142b008000e050206c320a0188802002981c1e06028101409008002e0703014080a01cc002004a01ca806028101403008000e0602810de0a01804000703014260a01a8c0200c281c0c05020280601003840e06028101403008000e06028101409018c402005301c0c05020280601
|52=>0x206c1403008000e060281014032b004000703014080a0191c02000b8180a040502418010001c0c05020287409009a400a1038180a040500c02000381408110500c44010001c0c050204c14ce008000e06028101409009a400070301464190500c1c01038180a040500f12010001c0c050200ca40e00803100703014080a0180400530387c0a040500c0200c301c0c05
|53=>0x8000e060281032034f8040049038180a040c8280601001d80e06028107e0a0180400290a83c0a040500c0200038180a040500e9e0e0001cce06028101403458040065038180a04050e806010001c0c05020285603640040028038180a040c828060e1481c0a040500d060100194500602810142b018000f8a03014140351804001703014080a0183002000b81c0c05
|54=>0x20280671008000e0602810140345804000703014080a0196c0200c601c0c050202806010001c1a060281014035d8040074038180a04098280601001940e06028101403009a4000703014641b0c8280601002480e0602810140901804000703014080a01e2c0200038180a040502406c307005360703014080a01838000703014650f0500c02000399c3e050202806b4
|55=>0x3383c0a040500d68010001c3e050202806b400803200703014080a01804000703014080a0480c180e0081c0c050206414037000400a20381a96050202806010001c0c0502028078f008000e0602810703f050240601000540ea403014080a018040012038180a04088281203008031a0703014080a0180400070301464110502402000383c3e0502028060e0081c0c05
|56=>0x194802003b01c0c05020280601006480e06028101403008002406028101403060040007030140813050e802000a81c0c05022e41403008000e060281014031b0300200038180a04098280601410022a0703014080a01838000703014080a9b80c02000387c0c050202806bb008000e0602810140901d3c0200c881c0c050202806010005c500602810320a018040007
|57=>0x38180a040500f06010001c0c0502064142b018380e06028101409018d80200038180a040500ec20e008000e0f0281014095a004000703014080a01804c6005101c0d95028101403008000e0602813260a01804000703014640a04b380200038180a040500d120100200520703014080a01804001c038180a040986406010005c0e0602810320a0183802070f8180a04
|58=>0x8782806010001c0c05020280631008000e0f2a014080a01804001503014080a018980200038180a040500e26010001c0c05020e014090180400ac038180a04050ac06010001d9806028101403008000e0f06814080a01838000703014643f0502402000e01c0c05021b014030080050070787c0a040500c02000383c0a040500d6801000540e0602810d8110500c0200
|59=>0x3014080a1580c02009701c0c05020280601000a40e1f028101403070042e07030140811050240200038180a04050e80601410000e06028101403cb004000703014080a9b80c1c01004100e06028101403008005007030140813050ac00291407c0a040500c02000b81c0c050206c320a018040115038180a040502406010001c0c050202806c2618040017038180a04
|60=>0x1a8c0200cc01c0c050202806010001c0cd2028101403008000e06028c8143a0480400291403c0a040500c0200038180a04050e802690001c0c0502028060134a080197038180a040500c02000381a80050202806010026c2e0703014640a008002a0703014086c0982806010001c0c05020640601108005007030140819050ac06007401c0c050204c140300800ca15
|61=>0x8000e0602810d40a01804000703014083f05024060e0081c0c0519028079b008002e0703014083f0502402001401c0c050202874030001c0c0502028069d070000e0602810140300bc0000703014080a01968020032ba00c050202806010005c2a0602810140900a880e06a581408190500c0200038180a040502406c2008000e0602810159a0180400070352c0a0a
|62=>0x20280716008000e06028101403cf0040007078180a040500d1601006740e06028101403008000ea403014080a018380048038180a040882806010001c0c0502028060134bc00028038180a040500cd2000a81c0c040500cea01000a40ea407814080a0180400073383c0c0502028068b008000e06028101403618380276038180a040c82806010001c0c0502028079c
|63=>0x410000e06028101403d100400940383c0a040500c0200038180a040500d5a01000480e06028107e0a018040007079503e050202806010001c0c0502028063600803420703014080a0180400070301409a00500c02000b81c0c05020287409008000e0602810140307005e000cf81c0c050202806010001c0c050202812034e80400e10b81c0c050202806010001c0c05
|64=>0x800240703014080a1d00c02000a8180a040500ec2010001c0c050204e1e03008000e06a5814080a01b2002000383c1a050202812010001c0c050202b4c03008002e2803014640a008002a0602810140901830020703014153901804000703014080a01d1402000399c1e0d028101403008034a0703014080a01804000703014080ad200c0200038180a040500c02b2
|65=>0x8000e0602810140341804000703014080a01b381c00038180a0405024060e00a080e06028101403d4804009b038180a040c8280601006a00e06028101403008000e0602810143a01b38000703014083f0500c1c01038180a040500e9a0e0001c0c0502028120300a08500602810140307208000703014080a01e9c0200038180a040500d84010001c0cec028c81403
|66=>0x352c0a040500c02001481c1e050202806010001c0c050202812036700400070301408b90500c0200038180a040d82806010001c0c050202812035a0040015038340c05020280601001945006028101403008005a0703014080a018380200b381c0c050202806010001d480602810140300800520703014640a018040007030140811050240601000a40e1f028101403
|67=>0x7004521503014080a018040053038180a040500c0200038180a040500c18010001c0c050206c140307004000703014080a01eac02000a81c1e06028101403008000e06028101403d5004001c0b81c0c050202806010001c0c050202806c300800ca07035680a040500c02003001c1a06028101403008000e06028107e0a0480c0200038180a04360441403008002a07
|68=>0x38180a040500edc010001c0c050204c3203008000e06028101403a6804000703014080a018c00200038180a040500c4c010001c0c050202874090180400170a8180a040500c02006001c0c050202806010001c0c05021b0260a018040157038180a040c8280601000540e06028101409018053617038180a040500c0200038180a040500f58010001c0c05020641403
|69=>0x3014080a01804000703014080a01b380200038180a320500ec6010001c1a06028101403070002417038180a040500c02000b81c0c05190280200038180a041f84c1403008000e06020280675008000e06028101403c38040065038180a04050ac0601001940e06028101409018040028038180a040c82806010001c0c050206c320a01804000703014090f0500c0200
|70=>0x180400070301408130500c1c010001c0c05020287403008002e2803014080a0180400a23281c0c050202806010001c0c050202807ae008000e0602810320a1580c02001401c0c051902806010001c0c050204c142b008000e06028107e0a0180400280383c0c050202806010001c0c050204c1409008035a65038180a040500c02005101c0c05020280601001805207
|71=>0x301464110500c02008a8a00e06028101403008000e0602812f60a01804000703014080a1d00c1c010001c0c05020280761008000e06028107e190500c02001401c0c05020285603002880e0602810320a01804000703014080a01bb80200038180a0a01a8c0200039501a06028101403008013628038180a040500c0200038180a040500c02690014c0e0f03014080a
|72=>0x6400400650381a9605020280601000540e0602810142b018040012038180a040502406010001c0c051902812010001eba06028101403008002e070301408110500c0200168a00e06028101403008000e0676014080a01804000703014080a018050400038180a040500c02b2001940e060281014030700400531481c0c050202806010001c0c0502028060e009a40007
|73=>0x801360703014080a01804000703014080a0480c1c010b81c0c05020281201000a00e06028101403070000e06a581408190500c0200cc81c0c050202806010001c0c0519028060e00802d60703014080a018040092038180a040500c02007401c0c050202806010001c0c05020280794008000e06028101403070050400038180a040500c1c01590000e06028101403
|74=>0x301408190500c0200038180a0405024060c008000e0602810142b018380012038180a040500c02008c81c0c050202806010001c1e0d028101403008002e0703014080a0183802000a81f140602810140300800500703014080a0480c0200038180a32c08280601004540e06028101403008000e06028c8320a018040007036540a040c8280601002b00e06028101403
|75=>0x5c0e06028101403008000e06028c81403008000e06a5814080a0180400070301408190500c0200038180a040500c1c01001940e06028101403008000f8a03014080a0180400070301408130500c0200038180a040882806010001c0c05020285603008000e06028101409018040028038180a040500c02000381ab405020280601000b40e06028101403008002e07
|76=>0x703014080a018040157038180a040500c02000a81c0c05020280601
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xa200208006200108002200008
|8,0=>0x91a423d908d9c22f7089a421e80856420d8081241fb907ca41e99078241d79073a41c7706fe01b6906b641a49066e41947062e4183805ee0172905aa0161905624151705260142704edc133804ae01229046a01119042240ff903da40ef7039a40dd9035240cb9030e00ba902c640a89027e40969023a0086801f64075801b600667017640549012e4042900e640309
|8,1=>0x2e590b7242d390b2a42c370aee02b290aa642a090a62029170a22427f909de026f8099e025f80961c24f9
|9,0=>0x14a2451ea1456450c9141204fb913ce04e9a138244d79133a44c5912f244b3912aa44a191262448f9121a447d911d2446b9118684589113e4445a10f24432a10aa042191062440f9101683fc90fce43eb80f8a43d990f4243c880efe43b5a0eb243a390e6a4390a0e1a837d90dd2436b90d8a435a80d464347a0cf6833490cae432290c66431180c22430080bde42ee9
|9,1=>0x1dc6876891d7e475691d36474581cf2473481cb2072391c6a4710a1c1e46fe91bd646ec91b8e46da91b4646c7a1afa46b591ab606a491a6a869191a22467f919d6866ba198a4658a193a8644a18ee4632918aa062191862460ea181645fc917ca85e8a177e45d69173645c4916ee45b2916a645a09165e458e91616457ba15ca4569915824556a153a0545914ee8531a
|9,2=>0x270a49b9926be89a692672899392626897fa25da496d9258e895b825468948924fe4936924ba0924a246a8910a241e48fe923d648eba238a48d99233e88c6922f648b4922ae48a29226a0890a221e487e921d6486c9218a8859921460848920fa8835920b248248206a88119201e87ff81fda47ed91f8e87d9a1f4247c881efe47b5a1eae87a291e62878f91e16877ba
|9,3=>0x30364c0582ff24bf2a2fa28bdf92f568bcc92f0a8bb8a2ebe4ba692e728b92a2e228b7f92dda4b6e82d964b5d82d524b4aa2d064b37a2cbe0b2782c7a4b1592c324b02a2be64af092b9a8add92b524acb92b0e0aba92ac64aa892a7e4a9692a3a0a85929ee8a71a299e8a5e929564a4c9290e4a39a28c24a26a28764a149282a8a02827e649efa279a49dca275209cb9
|9,4=>0x39624e4f9391a4e3ca38ce4e29a38824e188383a8e05937ee8df1a37a60de09375e4dcda370e8dba936ca0da9936824d979363a4d85935f24d73935aa4d61935624d4f9351a4d3ca34ce4d2a934828d188343a8d05933f24cf3933aa4ce1933624ccf9331a4cbd932ce8caa932864c97a323a4c85931ee8c72931a28c5f9315a4c4d931124c3b930ca4c299307e8c169
|9,5=>0x427e5096942365084941ea9070a419a905d94152504b9410a5039940c250279407a501594032500393fea4ff193f9e8fdf83f5e0fcda3f124fbc83ece4fa9a3e860f97a3e3a4f8593df24f7393daa4f6193d624f4ea3d164f3c93cca8f2993c824f16a3c364f0493bea8ef283ba28edea3b564ecc93b0e4eba93ac64ea893a7e4e9693a3a0e85939f24e72a39aa0e619
|9,6=>0x10df9435a50cd9431250baa42ca10a8a
|10,0=>0x4ce2532db4c92531b94c46930894bfe52f694bb652e3a4b6692d094b1e52bda4ad252ab94a8a5298a4a3e5286949f65273a49aa52619495e924e94912923aa48c292279487a52159482e9202947e651f09479e51de9475291caa470651b8946be51a5a467251939462a5181945de916e94592915b9454a5148a44fa9135944ae912294466510fa441a50fca43ca90e8a
|10,1=>0x56765593a562a5580a55de556da5592555b955469547a54fa5534a54aa95219545e950e9541654fc953ca94e7b537694d49532a94c1952e254aea529a149d95252548b952069477a51b69463a516a5450a511a943d950ce942a950829417950369403a4fe2d3ef94f9693dc94f4e53ca94efed3b5a4eb253a394e6a538fb4e16937ba4dca5367b4d7a535594d2e9341a
|10,2=>0x5fde97ee95f9297daa5f4657c895efa97b595eb257a395e6a5790a5e1e577da5dd2576aa5d86575895d3e5745a5cead73195c9e971f85c5a570d95c1256fb95bc696e7a5b7a56d595b3256c2a5ae656afa5a9a569ca5a4e5689a59fe9676959b296639596a5650a591a963ca58ce562a958829617958369603a57ea55f19579e95de9575655cc9570e55b9a56c255a6a
|10,3=>0x69325a43968ea5a31968a25a1f9685a5a0d9681259fb967c699e89677a99d4a672a99c0a66da99ad96692599b9664a5988a65fe5975a65ae996296562994f96516993c964ce592a964865917a64369904963ee58f2963a298e08635a98cd9631258bb962ca58a8a627a9894a622a9881961e2586f9619a585d9614e984a961065837a60ba58259607258139602a58019
|10,4=>0x72b25ca3972669c8fa72169c7c971ce5c6a971865c589713a9c44a70ea9c31970a25c1ea70529c0b970069bf7a6fba5be596f6e9bd1a6f1e9bbe96ecedba9a6e7adb9596e325b8396dea5b7196da25b5f96d569b4ba6d069b37a6cb69b2496c6a9b1196c225afea6bd65aeba6b869ad896b3e5ac5a6aee9ab1a6aa25a9f96a5a5a8d96a125a7aa69c65a689697e5a55a
|10,5=>0x7c1e9efe97bd65eeba7b8a5ed8a7b3e5ec697af65eb497aae5ea387a62de8ea7a165e7c979ce5e6a979865e589793e5e45a78f25e33978aa5e1fb785a5e0ca780a9df8a77be5de6977729dd2a77265dbfa76da5dad976925d99b763e9d85a75ee9d72975a65d609755e5d4da750e9d3a974c65d289747a9d14a742e5d00b73de5cee973929cdaa73465cc8972fa9cb59
|10,6=>0x83b260e2a836660cfa831a60bd982d260ab9828a6099982426087981fa6074a81ae606298162a04f9811a603e880d6602d88092601aa8046600897ffa9ff597fb25fe397f669fcfa7f1a5fbd97ed25faaa7e829f9797e369f83a7dea5f7197d9e9f5e97d565f4ba7d069f3897cbe5f25a7c6adf119
|11,0=>0x8d12a33b98cca632998c7ea31698c32a30398be6a2f098b9e62de98b52a2cc88b0aa2ba88ac662a7a8a76a293a8a26a280989de626e98996625c9894e6249a89026237988b6a223a886a6210a881e61fe987d661ec9878e61d9a874261c6a86f661b3a86aa61a0a865aa18ca860aa178a85be6165a8572615398526a13fa84da612ca848e611a984466107a83fa60f59
|11,1=>0x2582995e2a56ea9596655c9954e654a99502a536a94b2a5239946a65119941ea4fe993d664ec9938e64da99342a4c7992fa64b5992b264a39926a6490a921aa47d991cea469a917ea4578913a6444a90eaa431990a2641f99056a40ba9006a3f898fbaa3e598f6ea3d298f22a3bf98ed6a3ac98e92239aa8e42a38798df6a373a8daa636198d5ea34e9
|12,0=>0x2608997fe65f6997ba25e59977265d39972a65c1996e265af9969a659d99652658b9
|13,0=>0x26118
|_,_=>0
def wAt:=mkWire dB 431 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 18
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x88250180103801050050600501801078d80300d06005038260882400801050050200d01801008010384605005018010500d1683c0a80503801018050300d0482f01801078380080103001038051483803819008011303a0b81b008010b8860380d0d82b0c80508825050050e06c0b8290380d0c80505001050620682501801038010300505005098380080103825018010500d078380180100801030050300d
|1=>0x8010300d018050500109838008010500d018010a805038010b81b0380d248032482b0a84503801050051684c018010a805038010500d05062068250180103801030052280d06833030050382601801098380080103825018010500d0502d0300107838008010300d05062030e90480521005208010b8670380d05025050da060050382601801050f50b8f30380d068030300503801050ea04805018010380d
|2=>0x270380503100801038261f8070502501801038012b031038260682701801030050b8190380d051520f805078380180100801030050300d2781b050d90600503826148e8018390300d0381900801008010682403005018010300d2781b2700505031018010384109838008010500d07838008010300d03826018010682703005018010384109838008010500d2502b1a005030310382601801030050502d07838
|3=>0x38010500d0c02b0200d3380501801030050080103825018010300d008010682403005018010300d0080114064050010382903805078ea048050300d2481f2482b0a84503801050050200d0508a0306e0c805050010300d30024018010383503005018de050da0600503826050ea2501b1a005030310382601801030ea030310480503826018010380d008011402401801038052983801801008010383d0300d
|4=>0x180103805018010b838008010380d2481f248030a8450380105005050620682501801030050380d038010682701801030051c02b0200d1f8050502501801388050300d1482403819018011404c018050500d03829038050b87d0380d051520f80503001051a5298380b8190380d00801030013681b0a9b10880d0380105005031aa051a51d00f04805018010506206825030050200d01801328240180103829
|5=>0x3801050050380d0d82b0c805050010480503825018010500d0d81b0386e0c805050010b8190380d00801030013b003038fd0c80d050010200d0306e0c805050010180103829038010500d03801028ae0381901805018051404c038050500d30024018010383503005018010e0030384d0500d0506206825030050382501801008010300d0300501801048050380d0502501801038012500f030d90600503826
|6=>0x18010383a00801090340a80d0380103005298070200d0b8190380d0682403005018010080103819018050080103001018da060050382601801068320300503826018010382601801008010380d039f536003098050500d0503103826018010300d0600503826018011c00f050e904805018010300d3d00114807038193c01b0a8350380103005208010b8670380d050010300d1482403819018012482b0a845
|7=>0x48050200d0180108825050050200d018012a00f0387d0f80503001490253280703829018012481b0a84503801050050b87f0380d0080103001470074680d3280303829008010399e0f80d0300101801038010383d0300d0b82b01801038050380d03a26440010880f050051a0070303103826018010080103005038250180103215038ea158010180500801038190f80f0300100801030050200d018010500d
|8=>0x801030050300d51007038650500d05001038291404c038050500d370070b87d0380d030010380d060050382601801050013280f0382900801340053282403829018014e8010300d038360300506824030050200d018014d864038ad01805050011a0050303103826018010d80f0c8050500d0500103a664c0050c80f05001052090383a0503a00801018010b82b008010380d0300d0387e0180503001050ea
|9=>0xf805030013c02b039510f8050300157801148af03819018050682403005018010300d050623380503025018010300d0a83603801030050300d018051480303819048c3018010384605005038263380703025018010b81b0380d01801038010320a0383a0080103001019890386e0c8050500105001370030b87d0380d0300108827050050382501801030ad0a8130380101805060050901f0b8010380d01801
|10=>0x3801050050300d01805008010300101aed039520f805030010c00f338050f80d030010380d0306e0c805050010a81303801098070500d3381b0f80d0080103001458050399e0f80d030013380703025018010380101add3283803829008010200d2a01b0f80503001008010b836030050380d051c90b838008010380d00801030260200d018012481b0a84503801050050300d4a8050387e0300103ac92a01b
|11=>0x38010500505062030e9048050180103aa9338070f80d030010080105001038290380532801028ae03829018050380109805018010500d0b8860503a008010380d61805050260200d0180106826030050200d018010f8050b87f0380d030016007d0b8070380d03001068300300503826018010399e07801078050300d038251d00f0480501801038e20d80d0c80505001039590682701801030050a9b10880d
|12=>0x18010080168001039b2098050500d05001328380382900801140fc038050c80d05001048071d00f04805018010204109838008010500d6600d032090383a008016500d1407c038050300109805038660500d050010380d030050180100801600190b8070380d030010300d0302601801008010383a018010183a00801600660b8070380d0500101b0a618050502601801018050500d0383a008010880d0a813
|13=>0x18010080103846050050c8050b8650380d05001060050503103826018010300d0300103805018051402401801038050380d05001028ae0382901805050da06005038260180106827030050300d068260180103005050310080103826018014b00f052090383a00801050ea0380d04805018010882501801050050380d0b9520380d0f805030016a019090070b8010380d690050b87c0380d030010200d05025
|14=>0x208050b8670380d050010200d0b845050050380d01b811406703805050011c02b1f805050250180101ab50a83603801030050384309838008010500d1683f0a805038010300d0a81303801098050500d0300d0180103835030050b86e05039008010380d0304109838008010500d050da06005038260180103b615c801098070500d068270180103801030052481b0a845038010500503b625c801098070500d
|15=>0x338050399e0f80d03001051691402401801038050abb90680f03801030050300d03bb10f807030010200d1f80705025018010508a0306e0c805050010396e030ea158010180503862338050f80d0300105001328380382900801140030500d03805018057380d4a0070387d03001728011403c038050300d3b0070e0010384d0500d038050b838008010380d030ea04805038260180101959068270180103005
|16=>0x510af0386501805050010500d0480503826018010300d5a0050302601801050ea038250480501801088250500503825018010383603005018010300d7900101a7503836030050b8290380d0c80505001018050300d03819038050f80d039520f805030010200d0b836030050380d0383a018050183a00801039a6018010183a008010380514838038190080103031048050382601801030ea048050180103801
|17=>0x380104805018010500d140ff038050c80d05001008010399e0f80d030010b86c05039008010380d01801038010383d0300d0b8650380d0080105001028ae0a8130380101805038620f8ad0180503001050050901f0b8010380d0300d0380103826018010080105025018010380d023d91403e038050300d018390300d03819008010300d1480703819018010f80d051520f805030010382601801050050380d
|18=>0x818010b847050050380d0682403005018010300d0c02b338050f80d03001090360a80d0380103005800035101503865050017f00303bf5078070300d600650b8070380d0500114064050010382903805033c10b83a008010380d0382603005018010080104805050250180103801028ae03865018050500101801008010384d0500d01ad50b836030050380d248030a84503801050054d87f038ad0180503001
|19=>0x1407c038050080103001038190f80d00801030010200d338050302501801039410682401801030052700705031038260180103425190470200d050050983800801050050500d1f82b0c80d00801050010387d039520f805030018380503ad203026018010300d0300503825018010300d038f106803030050200d1f8070502501801140fc038050c80d050013c003039510f805030012482b0386d0c80505001
|20=>0x208050b8670380d050011d00f048050382601801298030383d0300d0300101b811406703805050018800d03c3d088030500527007050310382601801050250080103825018010500d0306e0c8050500103c350c8af0180505001038260500503825018010f8050399e0f80d030010080103825018010500d018010a805038010500d0500d0a81303801018050c02b0f8ad01805030012480f0a8450380105005
|21=>0x180503819038010300d338070399e0f80d03001050ea0502504805018011f80705025018010380d050ea04805018010500d21005450010b82b0380d8a827018010384505005050da0600503826018011683c0a805038010300d0387d051520f80503001898050a84e038010500d038011d00f048050180101a75008010383603005038011d00f0480501801038011482403819018011420f038050f80f03001
|22=>0x180107838008010300d038fe09801050050500d8f8050b8660380d050010a80503801018050500d03aca2a01b0f805030010bbb30f8070380d03001050310380103826018010386e0c8050500d050010200d0533904807018010e038008010384d0500d090470a80d0380105005038650180500801050018c836030050b8030380d0aa920680d03801030050b86c0380d0c805050010080103a92078050300d
|23=>0x78ea04805018010300d3a0070e0030384d0500d01ac92a01b0f805030010500d8a80303845050050388a0306e0c805050019280303bb90680f030054503a0b82b008010380d0380d0180103801050050306e038290c80505001910078c8190b8030380d3c01f0a83503801030050a8130680f03801030054d87f038ad01805030010bbb10f8070380d03001028ae03866018050500103825018010183a00801
|24=>0x2a00f038190f8050300115b2103866018050500105025048050200d018010c02b2a00d0f805030010180100801038050380d088250180103801050053381b07801018050300d2700505031038260180117005038fe0c80d050010500109838008010500d0194a051520f805030010500d008010384605005038251f8070502501801050e904805038260180105152030390383a00801018010b838008010380d
|25=>0x18860d82b0c805050010500d052090383a0080117005038fe0c80d05001018da060050382601801018010b838008010380d0bac80303a008010380d980010b846050050380d0180507838008010300d4900d328070382901801039aa051a50183a008010300d0300503826018010200d051520f805030010380d05025018010380101ace4a8050387e030010882405005018010080104805050260200d01801
|26=>0x200d01801051a51d00f04805018010380d0480501801038010382601801038010500501a8d0a813038010500503bf503801078070300d0883305005038260a805038010b81b0380d01a090500d0383a0080103826050250180100801018010300d03819008019b00f0b835030050380d008010500d0382601801031aa051a50183a008010500d0386e0c805050017e801078070300d14803028ae0381901805
|27=>0x303a00801018050300d038190080103826018010183a008010200d008010480701801018010380d14001038050399e07801018050300d149a40183a03819008010340d0b847050050380d0515203039008010380d050250600503826018010384109838008010500d088330500503826018010386e038290c805050011c02b0d80d0c8050500106827030050200d0180103ced0783b008010300d0502504807
|28=>0xb8010380d0300d018010380103005030d90600503826018011a0050303103826018010380d0682701801030058c835030050b8030380d8200d3000303835030050200d050250480501801018050387d0300d03001328e8048050382901801a00010b834030050380d2a01b051520f805030010384109838008010500d0302604805018010300d01a090383a0183a008018280f038f1068030300503c9e01ac9
|29=>0x200d008010387d0300d0300114003038050380d055351400f03805038290c805050010b846050050380d0280514803038191f8070c80d05001298010383d0300da50010e0070384d0500d0a8450500d03801050050300d0a8130380103005088330500503826018010380d050250480501801008011402401801038050c00f33805030250180101d221800103846050050bc3f0380d0880305005a28050901b
|30=>0x32d6a0382902801130050b81b0380d018010183a00801ab867038150500103819078010300d0c8070380d0500100801018050500d03d55078030300da980d0c807050010380d0380105005140270180103805018050383a008011482703819018011402b0200d038050180103801050050200d0b8190380d03031038260180151015038650500103b0e0502601801038050f80d030010533904807018010503a
|31=>0x1801098050500d050013000f03835030051404e038050500d0b82b038050380d0500d03826018014d81b038ad01805038050381900801018c1038460500503829038010280536003098050500d03d760287d030010303103826018011680f14001038050a80d0380103005030050b8030380d038010384d0500d0b838008010380d0d80f0c80505001050050503a008010880f0380105005038f10680303005
|32=>0x3826018010386501805050010502501801038010b83b008010380d3380703025018011681f1400103805b18051901b0200d0e0070384d0500d0c80d00801050011f8070c80d05001038fe0c80d0500103819018050300d00801038050380d052090383a008011483803819008011480f0381903805090070b8010380d0387e0300d030010502503826018010386500801050010380501801008010300d03819
|33=>0xb581b0a815038010b838008010380d0b8670380d0500114d68038190280103801018050300d14003038050180503825018010300d038010384d0500d338050f80d030010502604805018010b801050050380d0200d050050380d078010383d0300d0502503829018010300d148030381903a0d0f80f030010502504805018010383a0080101805b380314815038191403f038050300d0200d038450500503005
|34=>0x500109838008010500d0300d0381900801038ea15801018051407c0380503001490013280703829048050382601801038050c80d050011483803819008015c801098070500d300030383503005018010383d0300d018050183a00801008010381901801025b90383e0300d038010382901801050390503a008010b87e0380d030010e0070b8290380d0382901805050013380703025018010503a008010380d
|35=>0x381901805ab8670381505001018010b81b0380d039a50183a00801a78011402b03805560051480303819510150386505001298070383d0300d048050180103801b70010383e0300d050050383a0080102b21038660500109801098050500d8c8190b8030380d2a00f0f80503001008010680f030050f8ad0180503001038ea158010180509805018010500d1800103846050050a8450380105005038fe0c80d
|36=>0x801018010300d038ea01839008010503a0080105001008010383d0300d0300d0383503005050050384d0500d038190280503001053390480701801038650c80d05001051520f80503001050050200d00801068270180103005039520f80503001050250480701801018050500d05001b70050383e0300d0500d04807018010383e018010300d0a805038010300d052090383a008011681f1400103805148af
|37=>0x5001038860503a008010200d14807038190180503819008010b87f0380d030011e00d06803030050380d140010380503d760287d030010386501805050010200d0383603005008010382501801018010200d008010983b008010500d050050180100801190340200d030050180114001038051f8070c80d0500109801018050500d0a81303801018050381914001038050320a0383a008010f80d0f80503001
|38=>0x18010500d0200d03829038050d82b0c80505001028ae03829018050300d14807038190c8070500d050010080104807018010300d038360300503bf5078070300d030ea048050180101ac90303a008010b81b008010380d038190287d03001032d10302601801bf0013281703829050390383a008014f8013280f0382903829098030500d03a210880f05005030310382601801038290c80d050015101703865
|39=>0x300d03801030050384e0500d05001450010b82b0380dc0829190070200d05005008010380d051520f805030010b8070380d05001039520f805030014680d32803038290d82b0880105005050390200d0080105025048050180103aca0303a0080104805018010500d030050382601801140660380505001038050384d0500d0a81303801050050c80f00801050010a845038010500503805018010300d03801
|40=>0x300d0306e0c805050010383d018010300d0b846050050380d0387d0f805030011404c038050500d0500d0a813038014d803038ad018050e0050384d0500d088240180105005298030383d0300d038050c80f050010383a008010500101801008010380d050011400f03805050260200d018012a00d0f8050300114001038050180503b39048070180101801038050380d140670380505001088260180105005
|41=>0xf80f030010382903805018050a81303801028190901f0b8010380d05039008010380d0682701801030051682b14001038050380d03826018011d00f04805018015100703865050010d81b08801050050500d04807018011d00f0480501801050010200d00801b08051480f03819051520303900801468153280303829030010383d0300d03e1d0286605001039520303900801028ae01805050010383d01805
|42=>0x30ea158010180503ad103026018010395206801030050e0030384d0500d0183a03829008010200d0c805050013280703829018016400503866050010502601801008010b805008010380d0200d08803050053381b0f80d03001050013280f038290386d0c80505001038fd0c80d0500103819038010300d008011402b038050399e0f80d0300104805038290180103866018050500103805008010500103819
|43=>0x80100801038450500501a090383a00801039520f80503001018011402b038057400d140030380505001038050380d3381b078010300d3381b0f80d030011483b03819008010080103826018011406703805050010386502805050010b837030050380d1f80505025018010680d038010300505005038250180103e39ad02b02801050050200d018010300d00801030011482403819018010399e0f80d03001
|44=>0x3801050050533a04807018010180500801050010600503826018011480f038190080103026018010300d031a60183a008010386502865050010565103d6a02801048070200d01801440010880f05005298071480d038190384d0500d050010380d0080105001051520f805030010e0010384d0500d74029140030380503825038260180104805018010500d03801098070500d0600503826018010500d0383a
|45=>0x3b3a048070180101a090383a008013000303835030050500d03805018050300103819038050380d0c805050010180103845050056180505026018010380d08803050050882401801050050f8050300d03001038010b81b0380d0a84e038010500d050e90480501801018051480303819032090383a0080100801030050300d050250200d018010384d098050500d038050300d030013381b078010300d0880d
|46=>0x5001618050502601801ab86403815050010a8130380102805cc829ab803038150b87c0380d03001048050200d018010300d03819038050183a01839008010383a0183a00801038850503a008010b834030050380d0b8050200d0380d03801098050500d0d82b0c8050500105001038050180514003038050500d0382903801018054900d328070382903819008010300101801050050380d0383a0183900801
|47=>0xc80705001030ad00801018058a8030384505005039a60183a00801038050183a00801028ae038010180503819078050300d0399e078010300d0080105026018010b8650380d05001418050f80f03001051a50183a00801050250180100801190370200d0300505025018010380d1580103805018050080103836030050b83a008010380d1402401801038051400303829038050380d01801038010386502805
|48=>0x901b0b8010380d07801030050300d600290b8070380d01d3d1402b038050383a0303a00801d1801ab82b038150387d0300d030010a83603801030050502503825018010f8050300d03001060050382601801600010b8070380dbd805098030500d0380d04805018010b83a008010380d8c8050b8030380d0180103836030050b845050050380d03a92078050300da68011400f038050399e078010300d03d4d
|49=>0x8010383a01801008015100f0386505001038ad01805050011680d14001038056700504807018010c80d0080105001008011400f03805018010383a00801038050383a008010f8af01805030016180505026018010f8070200d03001038250480501801038011480f038190500d088030500503866028050500103005018010300d01a550387e030010200d038050380d03801038260180101a8d0a81303801
|50=>0xb8050380d1401b03805008010500103819038010383d0300d038260180105039008011481703819038010300dad01b028010b8290380d05026018010382902801038350300505025018010880d050050380102805038190300d0480701801098070500d0c8050500103026018010380103005038290380503839008011481503819078050300d038190200d018010500503819030010f80f030011d00701839
|51=>0x200d03805018050500d0c80d05001038050300d018010500d32815038290386505001148050381904807018011901b0200d00801030050b8010380d0200d0380d098010500d028ae0180502866050010382901805038290180103805050010c8050500108803050050383e0300d0500d050011400f0380503846050050b81b0380d0480501801038010380d0b8070380d098050500d03815050010180103801
|52=>0x38010180503825018010200d018010287d03001050050380d14001038050f807030010383a008010303a0080103829008011480d038190183a008010200d050051402903805098030500d01839008011480f038190c80d05001038050180503865050010680f030050a8130380106801030051400d038050183a008010383d0300d008010500d1580101805038050380d3280103829ab81b038150180505001
|53=>0x180501801038050280114001038050380d05001038260180100801018050b8010380d0b8030380d030050300d008010380d03801028190180103805190070200d03845050050200d0500102865050011480303819038ad018050180100801018010380d00801038050280505001ab803038150200d008010a815038013280703829140030380503d6a028010383a008010303a0080103866050010382902805
|54=>0x3815038010380d0200d02805050010080103829028190500d05005
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0xb500000056000500000000
|8,0=>0xf550f050eb50e830e350de50d95000000000d540d4100000cf50ca50c550c050bc40b840b350af40aa50a640a1509c50993094508f508d20885083507e50795074506f5000006a50655060505b500000565053304f404a500000455041403c503a203640000031502c500000275023401e501b300000174000001520105
|8,1=>0x14d51494144513f513a51355130512c41275122511d511851171112510d5108510350fe50fa4
|9,0=>0x24d424942454241423d423942354231422d422942254221421d421942154211420d42094205420141fd41f941f541f141ed41e941e541e141dd41d941d541d141cd41c941c541c141bd41b941b541b141ad41a941a541a1419d419a31964192418e418a41864182417e417a41764172416e416a41664162415e415a415641524
|9,1=>0x34a43464342433e433a43364332432e432a43264322431e431a43164312430e430a4306430242fe42fa42f642f242ee42ea42e642e242de42da42d642d242ce42ca42c642c242be42ba42b642b242ae42aa42a642a2429e429a42964292428e428a42864282427e427a42764272426e426a42664262425e425a4256425242511
|9,2=>0x44844444440443c443844344430442c442844244420441c441844144410440c44084404440043fc43f843f443f043ec43e843e443e043dc43d843d443d043cc43c843c443c043bc43b843b443b043ac43a843a443a0439c439843944390438c438843844380437c437843744370436c436843644362235e435a43564352434e4
|9,3=>0x54845444540453c453845344530452c452845244520451c451845144510450c45084504450044fc44f844f444f044ec44e844e444e044dc44d844d444d044cc44c844c444c044bc44b844b444b044ac44a844a444a0449c449844944490448c448844844480447c447844744470446c446844644460445c445844544450444c4
|9,4=>0x64846444640463c463846344630462c462846244620461c461846144610460c46084604460045fc45f845f445f045ec45e845e445e045dc45d845d445d045cc45c845c445c045bc45b845b445b045ac45a845a445a0459c459845944590458c458845844580457c457845744570456c456845644560455c455845544550454c4
|9,5=>0x7464742473e473a47364732472e472a47264722471e471a47164712470e470a4706470246fe46fa46f646f246ee46ea46e646e246de46da46d646d246ce46ca46c646c246be46ba46b646b246ae46aa46a736a3469f469b46974693468f468b468746843680467c467846744670466c466846644660465c465846544650464c4
|9,6=>0x762475e475a47564752474e474a4
|10,0=>0x8233820381d381a381738143811380e380b38083805380237ff37fc37f937f637f337f037ed37ea37e737e437e137de37db37d837d537d237cf37cc37c937c637c337c037bd37ba37b737b437b137ae37ab37a837a537a2379f379c3799379637933790378d378a378737843781377e377b377837753772376f376c376937663
|10,1=>0x8e338e038dd38da38d738d438d138ce38cb38c838c538c238bf38bc38b938b638b338b038ad38aa38a738a438a1389e389b389838953892388f388c3889388638833880387d387a387738743871386e386b386838653862385f385c3859385638533850384d384a384738443841383e383b383838353832382f382c382938263
|10,2=>0x9a339a0399d399a399739943991398e398b398839853982397f397c3979397639733970396d396a396739643961395e395b395839553952394f394c3949394639433940393d393a393739343931392e392b392839253922391f391c3919391639133910390d390a39073904390138fe38fb38f838f538f238ef38ec38e938e63
|10,3=>0xa633a603a5d3a5a3a573a543a513a4e3a4b3a483a453a423a3f3a3c3a393a363a333a303a2d3a2a3a273a243a213a1e3a1b3a183a153a123a0f3a0c3a093a063a033a0039fd39fa39f739f439f139ee39eb39e839e539e239df39dc39d939d639d339d039cd39ca39c739c439c139be39bb39b839b539b239af39ac39a939a63
|10,4=>0xb233b203b1d3b1a3b173b143b113b0e3b0b3b083b053b023aff3afc3af93af63af33af03aed3aea3ae73ae43ae13ade3adb3ad83ad53ad23acf3acc3ac93ac63ac33ac03abd3aba3ab73ab43ab13aae3aab3aa83aa53aa23a9f3a9c3a993a963a933a903a8d3a8a3a873a843a813a7e3a7b3a783a753a723a6f3a6c3a693a663
|10,5=>0xbe33be03bdd3bda3bd73bd43bd13bce3bcb3bc83bc53bc23bbf3bbc3bb93bb63bb33bb03bad3baa3ba73ba43ba13b9e3b9b3b983b953b923b8f3b8c3b893b863b833b803b7d3b7a3b773b743b713b6e3b6b3b683b653b623b5f3b5c3b593b563b533b503b4d3b4a3b473b443b413b3e3b3b3b383b353b323b2f3b2c3b293b263
|10,6=>0xc7f3c7c3c793c763c733c703c6d3c6a3c673c643c613c5e3c5b3c583c553c523c4f3c4c3c493c463c433c403c3d3c3a3c373c343c313c2e3c2b3c283c253c223c1f3c1c3c193c163c133c103c0d3c0a3c073c043c013bfe3bfb3bf83bf53bf23bef3bec3be93be63
|11,0=>0xd002cfe2cfc2cfa2cf82cf62cf42cf22cf02cee2cec2cea2ce82ce62ce42ce22ce02cde2cdc2cda2cd82cd62cd42cd22cd02cce2ccc2cca2cc82cc62cc42cc22cc02cbe2cbc2cba2cb82cb62cb42cb22cb02cae2cac2caa2ca82ca62ca42ca22ca02c9e2c9c2c9a2c982c962c942c922c902c8e2c8c2c8a2c882c862c842c822
|11,1=>0xd7a2d782d762d742d722d702d6e2d6c2d6a2d682d662d642d622d602d5e2d5c2d5a2d582d562d542d522d502d4e2d4c2d4a2d482d462d442d422d402d3e2d3c2d3a2d382d362d342d322d302d2e2d2c2d2a2d282d262d242d222d202d1e2d1c2d1a2d182d162d142d122d102d0e2d0c2d0a2d082d062d042d022
|12,0=>0xd8a1d891d881d871d861d851d841d831d821d811d801d7f1d7e1d7d1d7c1
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 16
def pmP:Nat→Nat
|0=>0x30014000000000000000059ca40000000000000000901700000000000000001080000000000000000002011c0000000000000000402280000000000000000804380000000000000001000e00000000000000002000000000000000000001ffe40000000000000000200c00000000000000000400700000000000000000511e0000000000000000080a80000000000000000101200000000000000000082d0000000000000000008280000000000000000002380000000000000000004400000000000000000008400000000000000000006a0000000000000000000a80000000000000000001000000000000000000000e0000000000000000000180000000000000000000280000000000000000000480000000000000000000700000000000000000000a00000000000000000001000000000000000000001000000000000000000000
|1=>0x6dff60000000000000000d9cec0000000000000001b3958000000000000000366a900000000000000006c5520000000000000000c80880000000000000001804100000000000000002f72b00000000000000005de560000000000000000b00ac00000000000000013f9d800000000000000027f2f00000000000000004ee5e00000000000000009dcac00000000000000013797800000000000000026f2b00000000000000004cf56000000000000000099dac0000000000000001339d80000000000000002672b00000000000000004ce52000000000000000089cac0000000000000001110480000000000000002200000000000000000004004c00000000000000008002c0000000000000001000200000000000000002000200000000000000004000000000000000000006201c0000000000000000c043800000000000000018027
|2=>0x44ce96000000000000000899cbc0000000000000010c41780000000000000021808700000000000000042000000000000000000081f034000000000000001004128000000000000001e572900000000000000036ee560000000000000004d9cbc000000000000000933958000000000000001262ab000000000000000204058000000000000000408014000000000000000800000000000000000000f6e6a0000000000000001ecc74000000000000000399cac0000000000000005b39d8000000000000000b672b00000000000000016cc52000000000000000299cbc000000000000000533958000000000000000967230000000000000000ecef60000000000000001d9cec000000000000000333bd80000000000000006672b0000000000000000abe760000000000000001400880000000000000001f795800000000000000038002
|3=>0x206ce5e00000000000000409bebc000000000000008133f580000000000000102678b00000000000000204ce5e000000000000004099cac000000000000008023f5800000000000000c2600b00000000000000134fe56000000000000002499cac00000000000000453f95800000000000000837f3b00000000000000106de560000000000000020d9f2c00000000000000413b95800000000000000826f2b00000000000000104ce5600000000000000200b0000000000000000031379580000000000000061ef2b00000000000000087de56000000000000001099cac0000000000000015b3958000000000000002a672b000000000000000500014000000000000000999cac0000000000000011bf9580000000000000023672f00000000000000045fe5e0000000000000008a60b400000000000000113f97800000000000000227c1d
|4=>0x604cf5e0000000000000090d9cac0000000000000111d79780000000000000222772f00000000000000444ac56000000000000008299cac0000000000000102104380000000000000204200100000000000000406cfd60000000000000080d9eac0000000000000101b3b580000000000000203672b00000000000000406c45200000000000000809fcac00000000000001013b9780000000000000202672f00000000000000404ce5600000000000000808ec2c0000000000000101139f80000000000000202220b000000000000004044054000000000000008081038000000000000010100070000000000000020144000000000000000040040480000000000000080080800000000000000100100500000000000000200000a0000000000000040000040000000000000048bfebc000000000000009133858000000000000010367ab
|5=>0x1006ced60000000000000200d9cfc0000000000000401b39580000000000000803240200000000000001004ee5e000000000000020099fac0000000000000401339780000000000000802672b00000000000001004cc5e0000000000000200998a80000000000000400001280000000000000703672b00000000000000e06cd50000000000000019099cbc0000000000000311f79780000000000000603662800000000000000c020004000000000000014111dac0000000000000281b3150000000000000050267ab00000000000000a04cc560000000000000111998a80000000000000221339580000000000000442662b00000000000000844ce560000000000000108000380000000000000201b39580000000000000402672b00000000000000804411400000000000001000100000000000000001a1b28480000000000000303676b
|6=>0x2004cfd6000000000000040099eac000000000000080133958000000000000100241ed0000000000000200408000000000000000400500080000000000000611320580000000000000c03672b00000000000001447de5e00000000000002889fcbc0000000000000501f39780000000000000a03e72b00000000000001126ce5e0000000000000222098a80000000000000441b7d780000000000000883672b00000000000001104ce5600000000000002201c82c00000000000004401b0580000000000000843672b00000000000001086cb16000000000000020e9fcac000000000000041b3b9580000000000000833772f00000000000001056ec5e0000000000000206dfcec000000000000040db39580000000000000816672b0000000000000101cec7e0000000000000202dbaac0000000000000403b7b58000000000000080367bb
|7=>0x10006cf560000000000002000d9cac0000000000004001339780000000000008002672b0000000000000a014ce56000000000000120eddcac000000000000201c33858000000000000400a666b00000000000008004ce560000000000000a1199d2c000000000000140333b580000000000002802672b000000000000048044004000000000000082099cac0000000000001040022000000000000002003672b00000000000004004d856000000000000080099dac00000000000010013395800000000000020008c0000000000000003004cf560000000000000480d9fac0000000000000901b3d5800000000000010827fab00000000000002104de5e000000000000042099fbc000000000000084130000000000000000102363af00000000000002044ce560000000000000404d9ffc000000000000080533b5800000000000010026fab
|8=>0x20106ce5e000000000000401099cac000000000000802132f780000000000010013773b00000000000020024ee7e000000000000400499cac00000000000080083bfe80000000000010002673f00000000000020004ce76000000000000400099cac0000000000008001325380000000000010002432300000000000014186ca8e00000000000023099982c0000000000004611bf9580000000000008c036f2b00000000000011804ce560000000000002210dbcac0000000000004411339580000000000008807773b00000000000011006ce560000000000002140d9aa800000000000042413f9580000000000008482772b0000000000001080ccc540000000000002100d98a800000000000042013101000000000000080c2672f00000000000010044ee5e000000000000200899cbc0000000000004011320580000000000008007672b
|9=>0x400024804000000000000800049000000000000001000000010000000000001a08377ff00000000000031304ee7600000000000062089dcfc000000000000c0c13aff8000000000001810267fb00000000000030106ce5e0000000000006000ddcfc000000000000c00133978000000000001800265ef00000000000026044cbde0000000000004820d9cbc0000000000008c493bbd80000000000011083672f00000000000022024cffe000000000000440499fec000000000000880932f780000000000011002672b00000000000021106ee5e00000000000042008d4bc00000000000080c1b3978000000000001014267eb00000000000020244cfde000000000000404899cbc000000000000808133f580000000000010102672f00000000000020204cbde0000000000004024ddcfc0000000000008041b3b780000000000010083673f
|10=>0x100104de5e00000000000200209bcac000000000004001800138000000000008001361ab00000000000100024c056000000000002000299cac00000000000400033395800000000000800026f2b00000000000100004ce5e000000000002000099cac0000000000040000101000000000000080000002c0000000000008110000500000000000010206dfcac000000000002004133958000000000004000a672b00000000000080004ce5e000000000001000099cac000000000001c061bb9f80000000000038040573f0000000000005580eee76000000000000a301ddcec0000000000014603339580000000000028446662f00000000000050804ce56000000000000a100998ac0000000000014021220580000000000022446676b0000000000004480cccd40000000000008110998ac0000000000010203333500000000000020001240a
|11=>0x200006f4560000000000040000d9cfc0000000000080001b39580000000000100002673b00000000000200004ce5600000000000400002809c0000000000080000501280000000000100000680500000000000200000404800000000000400000800000000000000800000001000000000000d0012672f0000000000018102ece560000000000030082d842400000000000600073395800000000000c000c472b00000000000180014ce560000000000024c0089fac000000000004880932f78000000000009100267eb00000000000120104ce7e0000000000024000d9cbc000000000004084137f780000000000080837672f00000000000100457de5e000000000002008ad9cbc0000000000040115b39580000000000080222502f00000000000100434ce5e0000000000020082dbcac0000000000040105b39580000000000080082ef2f
|12=>0x301006ce760000000000060082d9cac00000000000c010410160000000000018008267af00000000000300016c852000000000006000299cbc00000000000c0004d0110000000000018000800290000000000030000ccf560000000000060000daeac00000000000c0001b39d80000000000180000002d000000000002810000000000000000005000499eac00000000000a000133d580000000000112002256f000000000002080049c560000000000040480d9cac000000000008080131358000000000010080b6bab00000000000201016cf560000000000040082d9cac0000000000080101b39580000000000100102672b00000000000200104fe7e000000000004002008080000000000008001054138000000000010000b200200000000000200014ce560000000000040002880f000000000000800041010000000000001000080021
|13=>0x1000004465600000000002000000b000000000000040000000008000000000040030267af00000000000800604ce5e0000000000100000888340000000000104611b39580000000000208c22772b00000000000411844de560000000000082100d9cac0000000000104201339580000000000200c0367ab00000000000400c06ce560000000000080180d9ca4000000000010029133d58000000000020050267eb00000000000400a04cf56000000000008014099cac000000000010028133158000000000020050063eb0000000000040088008100000000000080108d98ac0000000000100001b3048000000000020000008000000000000038001cce56000000000007000299eac00000000000e00053395800000000001c0009002a00000000000380004cf560000000000070000000a000000000000c0905b39580000000000181000602c
|14=>0x1041004cf56000000000020800008008000000000040d04132b780000000000818002672f00000000001024284cade000000000020480099fac0000000000409001339580000000000812002272f000000000010240008ffe0000000000202300dbeac00000000004042613a85800000000008080002004000000000010040044e5600000000002003089dcfc0000000000400601b39580000000000800c02673b00000000001001106cf5e0000000000200181d98a40000000000400301b39580000000000800483672b00000000001000846ce5e0000000000200100d9cac000000000040020133d580000000000800402672b00000000001000100c000000000000020002009000000000000040002133d58000000000080000367ab00000000001000004df56000000000020000099cfc0000000000400001339d80000000000800002672b
|15=>0x1455806cf560000000000282100dbcac000000000050028133f580000000000a004002409000000000012011064fd60000000000240208ddcfc0000000000480401b3d780000000000900802772f00000000001201004ce7e0000000000240080d9fac0000000000480101b39580000000000900202676b00000000001200106fff60000000000240020dbeac000000000048004197f7800000000009000832feb00000000001200104fffe00000000002400209bebc000000000048004117f5800000000009000237f3f00000000001200044fe7e0000000000240000d9ffc00000000004800017bd5800000000009000026f2b00000000001200004cff6000000000024000099fac000000000048000133d58000000000090000047fb00000000001074184ce5e000000000020891199eac0000000000410621b39d80000000000820c43672b
|16=>0x200180c0c54000000000040030099cac0000000000800401bb9580000000001000802672b00000000002000e0ecc52000000000040014199dac0000000000800203339580000000001000287af2b0000000000200044f6e560000000000400089ebcbc00000000008001139397800000000010002063a0b0000000000200040c4e7e000000000040008189cbc0000000000800103030100000000001000206020a0000000000200040a541600000000004000808dcbc0000000000800080210200000000001000082672b00000000002000084ce560000000000400009488a8000000000080000733958000000000100000a672b00000000002000004cede00000000004000008c83c0000000000800001010800000000001000001420e00000000002000002841400000000004000001180800000000008000002108000000000010000004204
|17=>0x20120004ce56000000000400400099cbc000000000800800133958000000000e020040270b0000000000d0000044656000000000180004081d2c0000000000c80103b3f58000000000190020767ab0000000000320040e4f56000000000064008099eac0000000000c800433ffd80000000001800002672b000000000030000004c28000000000054008398cb400000000008c0107b3958000000000114000022220000000000220240ece560000000000440205d9eac0000000000880107b3958000000000110020c2228000000000022000204448000000000044000399eac00000000008800003100000000000011000002224000000000020400080c040000000000402901998a80000000000804001339580000000001002002676b00000000002004004ce5600000000004004030882000000000008008060114000000000010010014207
|18=>0x200000446541600000000400000008af2c0000000060008021329f800000000c0000442272b000000001800008844e16000000003000001199cac0000000040801001331480000000080a284026f2b00000000101004284484200000000202008009901c0000000040400601b39580000000080800542672b00000000101000804c812000000002000a118d9cbc0000000040014221b79580000000080028443672b00000000100040c86ce560000000020008110d962c000000004000428133fd80000000080000c43672b00000000100000886081400000000200000009901c0000000040000000160000000000080000000280d000000001000000004804000000000c02000c990bc0000000018040001329580000000030080002642b00000000060010004c856000000000c000204994ac0000000018000011329580000000030000002652b
|19=>0x1400010004ce5e000000028000040499cfc000000050000080137d780000000a00000802673f00000001400000804fe5e00000002800000409bebc0000000500000081339780000000a00000102672a00000001400000024ce7e000000028000000299cac0000000500000005339500000000a00000006672b00000001400000004fe7e00000002800000009bcbc0000000500000001339f80000000a00000002672f00000001400000004ce560000000200000140998a80000000400000007331500000000600400302672f00000000400b02004ce5e000000008014008299cbc000000010024080113978000000020040010267af00000000400000084c85a00000000402400008af2c000000008048000113f58000000010090000227ab00000000201034004cade0000000040204800995bc000000008040100133d580000000100000802228b
|20=>0x2000022004cfd6000000040000405089fac0000000800008041ba9780000001000002826777f0000000200000400ccfd6000000040000080199dac000000080000100317b5800000010000020062acb00000002000004006ced6000000040000080089dac000000080000040bbb9d80000001000000203672b00000002000000005ce56000000040000000099cac0000000518000001329580000000a01d0020667af00000001402000a0cce54000000028034000099ebc00000005002c0001339780000000a0048100267af00000001400900004ce5e000000028010040099ebc0000000500200801339780000000a0040020a672f00000001400800204cfde000000028010001099cbc000000050020000133d780000000a00400002672f00000001400800004ce56000000028010000089cbc0000000500008801339580000000a00008802672f
|21=>0x2002004004ee5e000000040040020099cac00000008004894113b9f8000000100091200267ff000000020003a0004cfd6000000040006440099cac00000008000c804932b780000001000190082656f00000002000320004cffe000000040006400099cbc00000008000c8001339580000001000110092672f00000002000220104ce5e00000004000440009dcbc0000000800088001339f8000000100010081367ab00000002000200104df5e000000040004000399dec000000080008000733b58000000100010000a67ab00000002000200004de56000000040004000099eac00000008000800011387800000010000d009377ff000000020001a0104ca7e000000040002440099fac000000080004000333b580000001000040024020700000002000025104effe0000000400004a089ddfc00000008000094013bbf8000000100001202267ff
|22=>0x12000000004c85200000024000000009909c00000040000e0005339580000008000190002653f0000001000020a034de560000002000040000990a4000000400006000db395800000080000c001a6f2b00000010000180014ce560000002000030000500ac0000004000040401b39580000008000080012602700000010000100014cc520000002000020002400a8000000400004000180050000000800000000a662b00000010000000008004400000020000000004802000000028004890a113f580000005000000002272b000000080000200044e5600000008000000209102c000000088008800132978000000110008000264270000000200210000cdef600000004004008219fdec0000000800801003b7bd8000000100100200667eb0000000200200400ccef6000000040040080199dac000000080080100317b580000001001002006276b
|23=>0x10000280240cc65a0000012000060402898a400000140008c080733958000002800110501e6f2b0000005000220a01cce5600000082804004009fcbc0000010100a0080133d78000002000118500862280000004000220a01cce56000000800044000299eac000001000080281611158000002000100402c220000000040002002104fe56000000800040040b009ac000001000080080733b58000002000100100367ab0000004000200200444000000008000400000d0808000001000000200133d580000020000001803672b000000201000508c4ce5e0000004020008108b9cbc000000804000c0b132978000001008000802264070000002010000000400140000004000000210d9cbc00000080000004013a02800000100000008027027000000180000020044842000000240002400099cac000000480000880133d58000000900000000a662b
|24=>0x10000001a0064ca5e000020000003000d008bc0000400000048041b39780000800000080013672b000010000000a0024ce5e0000200000004408997bc00004000000084013b9780000800000000883672f00001000000001024ce5e00002000000002001c09c000040000000000133d580000401000100002272b0000040000105080cde560000080000200110090200000100000100321b39580000200000000802672b0000040000000084cce56000004002060011099cac0000080040904283339580000100081000046672b00000200101000a84ce560000040000600140198000000080000c0020133d580000100001000526676b00000200002000a0ccf56000004000040004010838000008000010008133958000010000000080367ab00000200000000a04ce56000002028010008099cbc000004010020010133978000008020040000267af
|25=>0x80001420000004ce56001000000402000c99cbc0020000008040018009380040000010080002672b00080000020010084ce56001000000400200099cac0020000008000019339580040000010000022672b00080000020000004ce560008001000004800884bc000c000100000001339580018000200000002672a00008001401a00404cfde000100028010008099cbc00020005000002013f978000400020050020a672f00008000400a00014ce5e000100000014048298cb4000100806000c03112878000120100091208367ef00002400200000406cf5600004020000410069bcac00008000008c010711140000100000008481b672b00002000000009074de560000400000000200998ac0000800000000001339580000848000081012202700001010000180076ce5e0000202000030002f9cbc0000404000048809329780000801000050082672f
|26=>0x12000000020020104ce56100000001000405089cac1000000800800001339d82000000a010000067f2f0400000000200010cfe7608000000004000209bcac100000000040000137d5820000000001010027f3b04000000000004004ced60800000000000020d9dac10000000000000413f9f82000000000000082673b02000000020020004ce56040000000000400099cac0400000500200001339580700000010018042672b00c00000020020084ce56010020200003000cd9cbc0200400000040059b39780400000010090032672f00400000020020004ce56008000000000400099cbc0100000000008001339580100000a10010002672b00200000020020044ce56004000000400400099cac0040100000008041339780080009000191002652b00100010000322004ce560020002000064400894ac00400000404000213395800800000800100c2652f
|27=>0x200200000080000093395c0000800000080832772f80000000020020024ce5684000000040040249dcad0100000008048001339591000000010010002672f
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x18000100100000
|8,0=>0x320c12090432d424069804145800c171e0050a5ba3e4a2000216b11916c0336ca30000008c17001bd6f4162f00719e0208cae01cf328002120af6a01e0163a5c05a0500034808090200023c008095d4000981f80c5109400370da0021f2214c0340008c0007028
|9,0=>0x1b82f0c26a2e1745f4979bf1070aef1c8ef6ca5e0b093142216202faa246bd06fc05bc71cec1ea05266cf1ea075106f94d549d4a189ca615a671f0309b12a2a256974fc2d1ab2ad070f5d41b11310993b2819a3e066c2e015dbe8515c154ab6ee928d2d30bec8658aac02f9923154cdc61bd3f4457f0bdc0170b832e873082ccc4793da1023c8e3dd768443b51ae40d9b5455945e990756d69a4fa406090bd8f
|9,1=>0x97d020b5862614554c6f6097abf95616415614c79b6cc0cdd793b0a1e977a0ce15cae823c226b72f68a4ab78306ba5c1ed142e29346c322241d5758c33b163ca0a0b5400b1b75e6910b81026d999be2641a5b02abe218b014a202b4cf3954b9267aa62664da33062015f0b950981b8cf091eb913ced294320d40f6a430be82d6607b0a8f48890a1be3b14d4f06dd8538e45e2285043556c11008b367725102ee
|9,2=>0x1bc30701aac1a0d0e60c1be325203d0c2571261b9806f3b543217337b13e3f9d3aa62b0ac0eb52df9a0a4cb83b85c27cd0d9030602d8876d0cd22dbfb453d90edac9a1c231f00c0dd864540bc84a09653b4eabfee7afa2c969f3811ce8a6305bf146340b801341043c546593e3362e02f197241bee59e0f11be4404ca4b395630e4a0b164b43300f42fa902c2e55517d127799b6104b5eccf0be1ecb60883c81
|9,3=>0x2f2de6e0b03a791fc
|10,0=>0x7312d8f6fd1c3411f624b02f74c31ab56087fcbf4631b84da4775504e510a6dcf9c0c8a986a1d57372aaf8f5ed57916c3c462c4cac3a2f18a7d947286dae6ca6998f5c19f88a5a1667a312a8b51549a5646d2525efae135431e92a563c7dea6e6fd2e84cd609ad5d3cbb339bb63d2c9f82087ec9c30aaa9f38d29d275979b529415fab5d168c610f8c13fa711927b2463e23de162a85baf55303213773ab76ea
|10,1=>0xc816e62b2ba350ba7a3d9463d47645c4f427f8e8ba6089db56874e93419fae5f265702c329c35074460e96c59a0df5139acb561321dae1a323198e2d27d6a31a8165f19744699df44909475bdf6c0cd87122370f50c463d5b717314eb23ed98f6c99fcf50c3057af4fc7a792768e124dfd45fab75a79d13a4ae5472696aedd6936dbcee94c8ecda288076da15c709629cb74a9da8625d7c6b7e6b14df6077e15
|10,2=>0x581c50bd9ed4562b0d271c42d48865cf58945b3fd4830a414ab1265acc30d72f5b8847134c9649e31cec17d1fb486ae535a03889439cdd9506d12af0403457f688bf1e0736f2256a5848ff6ce61d3349cc8de422d86735e2ed2035a2a1a20e62d2f343405fb5461e4f279dc236a7cf830be3081774aa29e23f4bd3b8d548f2aac26b15ab663a35a264fc72dcc89b8ade4c8b959add0ea57480d1691eab224a37
|10,3=>0xa5df1c62c7afe39699e7346a382c96a1a16434fbcf1af33273273350e30baaf5d98b529492459e548d837bda187b75a1fef3c11f79571d8692d9903f9070d92ce9
|11,0=>0x2bd57c90a68630c4ac7bb472fb514ba8bd84fdb15e51cebccf353a3a3e46918d2f2c76957d946635e848f4e0a891e47dd9ad10979a8a4c583b08fcb5c45d387a9bd28b19e5962acb0835d93535667c1395a74049d8b4d4edf5d452518e72b76408f4c434d6bd0d2c7215a0b52c0c23818430bee3f1935b45eb540d102416c8f4a7d2c77253634e161bc73843c94126ba25126472a08f707a00de4106a
|12,0=>0x23d17830a133755916157461252c1102c45e3d
|13,0=>0x2c
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 10 (j%128);fld (pmP (k/32)) 83 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_251 12 roots_251 ops++addP pm 1 dom_223 11 roots_223 ops++addP pm 2 dzo_91_4 8 roots_91 ops++addP pm 3 dom_254 11 roots_254 ops++addP pm 4 dom_159 8 roots_159 ops++addP pm 5 dom_253 11 roots_253 ops++addP pm 6 dzo_191_64 8 roots_191 ops++addP pm 7 dzo_190_64 7 roots_190 ops++addP pm 8 dom_247 11 roots_247 ops++addP pm 9 dom_246 10 roots_246 ops++addP pm 10 dom_239 11 roots_239 ops++addP pm 11 dom_222 8 roots_222 ops++addP pm 12 dzo_223_32 8 roots_223 ops++addP pm 13 dom_191 11 roots_191 ops++addP pm 14 dom_237 10 roots_237 ops++addP pm 15 dom_90 5 roots_90 ops++addP pm 16 dzo_94_32 6 roots_94 ops++addP pm 17 dom_127 11 roots_127 ops++addP pm 18 dom_182 8 roots_182 ops++addP pm 19 dom_252 8 roots_252 ops++addP pm 20 dom_221 8 roots_221 ops++addP pm 21 dom_91 8 roots_91 ops++addP pm 22 dom_111 8 roots_111 ops++addP pm 23 dzo_95_32 7 roots_95 ops++addP pm 24 dom_175 8 roots_175 ops++addP pm 25 dom_126 7 roots_126 ops++addP pm 26 dom_238 8 roots_238 ops++addP pm 27 dzo_222_32 7 roots_222 ops++addP pm 28 dom_189 8 roots_189 ops++addP pm 29 dzo_175_64 7 roots_175 ops++addP pm 30 dzo_125_2 6 roots_125 ops++addP pm 31 dom_207 8 roots_207 ops++addP pm 32 dzo_183_8 9 roots_183 ops++addP pm 33 dzo_175_16 6 roots_175 ops++addP pm 34 dzo_189_2 6 roots_189 ops++addP pm 35 dom_125 8 roots_125 ops++addP pm 36 dzo_188_64 6 roots_188 ops++addP pm 37 dzo_111_16 6 roots_111 ops++addP pm 38 dzo_123_4 9 roots_123 ops++addP pm 39 dzo_174_64 6 roots_174 ops++addP pm 40 dzo_182_8 8 roots_182 ops++addP pm 41 dom_164 4 roots_164 ops++addP pm 42 dom_236 6 roots_236 ops++addP pm 43 dom_173 7 roots_173 ops++addP pm 44 dzo_247_8 10 roots_247 ops++addP pm 45 dzo_246_8 9 roots_246 ops++addP pm 46 dzo_237_16 6 roots_237 ops++addP pm 47 dzo_239_16 7 roots_239 ops++addP pm 48 dom_63 6 roots_63 ops++addP pm 49 dzo_251_4 10 roots_251 ops++addP pm 50 dom_235 9 roots_235 ops++addP pm 51 dzo_219_4 9 roots_219 ops++addP pm 52 dzo_189_64 7 roots_189 ops++addP pm 53 dom_206 5 roots_206 ops++addP pm 54 dzo_173_64 6 roots_173 ops++addP pm 55 dzo_253_2 7 roots_253 ops++addP pm 56 dom_75 5 roots_75 ops++addP pm 57 dom_180 5 roots_180 ops++addP pm 58 dzo_237_2 6 roots_237 ops++addP pm 59 dom_249 9 roots_249 ops++addP pm 60 dom_166 5 roots_166 ops++addP pm 61 dzo_47_16 5 roots_47 ops++addP pm 62 dzo_173_2 5 roots_173 ops++addP pm 63 dom_89 5 roots_89 ops++addP pm 64 dzo_61_2 5 roots_61 ops++addP pm 65 dom_205 7 roots_205 ops++addP pm 66 dom_187 9 roots_187 ops++addP pm 67 dzo_218_4 6 roots_218 ops++addP pm 68 dzo_219_32 7 roots_219 ops++addP pm 69 dzo_173_16 5 roots_173 ops++addP pm 70 dom_183 9 roots_183 ops++addP pm 71 dom_45 4 roots_45 ops++addP pm 72 dom_231 9 roots_231 ops++addP pm 73 dom_119 8 roots_119 ops++addP pm 74 dzo_87_32 6 roots_87 ops++addP pm 75 dom_250 8 roots_250 ops++addP pm 76 dom_215 8 roots_215 ops++addP pm 77 dom_150 5 roots_150 ops++addP pm 78 dzo_109_2 5 roots_109 ops++addP pm 79 dzo_245_8 7 roots_245 ops++addP pm 80 dom_83 5 roots_83 ops++addP pm 81 dom_245 9 roots_245 ops++addP pm 82 dzo_215_32 7 roots_215 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54|h55|h56|h57|h58|h59|h60|h61|h62|h63|h64|h65|h66|h67|h68|h69|h70|h71|h72|h73|h74|h75|h76|h77|h78|h79|h80|h81|h82
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_91_4_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_191_64_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_190_64_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_223_32_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_94_32_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_95_32_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_222_32_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_175_64_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_125_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_183_8_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_175_16_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_189_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_188_64_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_111_16_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_123_4_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_zo_174_64_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_182_8_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_zo_247_8_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_zo_246_8_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_zo_237_16_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_zo_239_16_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_zo_251_4_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_zo_219_4_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h52;exact cpcs (by decide +kernel) lowS_zo_189_64_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h53;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h54;exact cpcs (by decide +kernel) lowS_zo_173_64_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h55;exact cpcs (by decide +kernel) lowS_zo_253_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h56;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h57;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h58;exact cpcs (by decide +kernel) lowS_zo_237_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h59;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h60;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h61;exact cpcs (by decide +kernel) lowS_zo_47_16_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h62;exact cpcs (by decide +kernel) lowS_zo_173_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h63;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h64;exact cpcs (by decide +kernel) lowS_zo_61_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h65;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h66;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h67;exact cpcs (by decide +kernel) lowS_zo_218_4_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h68;exact cpcs (by decide +kernel) lowS_zo_219_32_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h69;exact cpcs (by decide +kernel) lowS_zo_173_16_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h70;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h71;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h72;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h73;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h74;exact cpcs (by decide +kernel) lowS_zo_87_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h75;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h76;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h77;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h78;exact cpcs (by decide +kernel) lowS_zo_109_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h79;exact cpcs (by decide +kernel) lowS_zo_245_8_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h80;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h81;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h82;exact cpcs (by decide +kernel) lowS_zo_215_32_82 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_251 12 s (0,roots_251.map (·&&&dom_251)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_251 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 6 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 83 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 83 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 256 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_256 : ∀ i, 256 ≤ i → i < 384 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_384 : ∀ i, 384 ≤ i → i < 391 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 7 384 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 391 → Z 9 i = true := (range_split (range_split z9_0 z9_128) (range_split z9_256 z9_384))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 256 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_256 : ∀ i, 256 ≤ i → i < 384 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_384 : ∀ i, 384 ≤ i → i < 436 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 52 384 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 436 → Z 10 i = true := (range_split (range_split z10_0 z10_128) (range_split z10_256 z10_384))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 125 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 125 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 15 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 15 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.and, inputs := [9, 10] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [12, 7] }, { op := GateOp.and, inputs := [5, 13] }, { op := GateOp.or, inputs := [0, 6] }, { op := GateOp.and, inputs := [3, 15] }, { op := GateOp.and, inputs := [1, 4] }, { op := GateOp.and, inputs := [2, 7] }, { op := GateOp.or, inputs := [11, 14] }, { op := GateOp.or, inputs := [19, 16] }, { op := GateOp.or, inputs := [20, 17] }, { op := GateOp.or, inputs := [21, 18] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_51648_aux

theorem PEqualNP.Outside.L_meta_51648 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_51648_aux.main
