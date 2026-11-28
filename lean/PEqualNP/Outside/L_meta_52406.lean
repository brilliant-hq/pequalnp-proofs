import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52406_aux
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

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafaaaaafafa0000fafaaaaafafa0000fafaaaaafafa0000fafaaaaafafa0000
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefeeeeefafa0000fefeeeeefafa0000fefeeeeefafa0000fefeeeeefafa0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffeeeeaaee00ffeeffeeeeaaee00ffeeffeeeeaaee00ffeeffeeeeaaee00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffaffaafafaaa00fffaffaafafaaa00fffaffaafafaaa00fffaffaafafaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffeffeefefaee00fffeffeefefaee00fffeffeefefaee00fffeffeefefaee00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_74 : Nat := 0x5050000000000000505
def goal_74 : Nat := 0xffccffccffccffcccc00cc00cc00cc00ffccffccffccffcccc00cc00cc00cc00
def roots_74 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffccffccffccffccee00ee00ee00ee00ffccffccffccffccee00ee00ee00ee00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfff0fff0fff0fff0aa00aa00aa00aa00fff0fff0fff0fff0aa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_78 : Nat := 0x55550000000000005555
def goal_78 : Nat := 0xfffcfffcfffcfffccc00cc00cc00cc00fffcfffcfffcfffccc00cc00cc00cc00
def roots_78 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfffcfffcfffcfffcee00ee00ee00ee00fffcfffcfffcfffcee00ee00ee00ee00
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffccccffffccccaaaa0000aaaa0000ffffccccffffccccaaaa0000aaaa0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_84 : Nat := 0x1100110000000000110011
def goal_84 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_84 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffff0f0fffff0f0fafa0000fafa0000fffff0f0fffff0f0fafa0000fafa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffffcfcfffffcfcf0f00000f0f00000fffffcfcfffffcfcf0f00000f0f00000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffcfcfffffcfcfafa0000fafa0000fffffcfcfffffcfcfafa0000fafa0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffffccffffffcccc00cc00cc00cc00ffffffccffffffcccc00cc00cc00cc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffccffffffcceeaaee00eeaaee00ffffffccffffffcceeaaee00eeaaee00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfffffff0fffffff0f0f00000f0f00000fffffff0fffffff0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffff0fffffff0fafaaa00fafaaa00fffffff0fffffff0fafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffffcfffffffcfcf0cc00fcf0cc00fffffffcfffffffcfcf0cc00fcf0cc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffffcfffffffcfefaee00fefaee00fffffffcfffffffcfefaee00fefaee00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xeeeeeeeecccccccceeeeeeee00000000eeeeeeeecccccccceeeeeeee00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefefcfcfcfceeeeeeee00000000fefefefefcfcfcfceeeeeeee00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffaaffaaff00ff00ffaaffaaaa00aa00ffaaffaaff00ff00ffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccffccffccffccffcccc00cc00ffccffccffccffccffccffcccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeffccffccffeeffeeee00ee00ffeeffeeffccffccffeeffeeee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffafff0fff0ffaaffaaaa00aa00fffafffafff0fff0ffaaffaaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfffcfffcffccffcccc00cc00fffcfffcfffcfffcffccffcccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefffcfffcffeeffeeee00ee00fffefffefffcfffcffeeffeeee00ee00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffaaaaffff0000aaaaaaaaaaaa0000ffffaaaaffff0000aaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffccccffffcccccccccccc00000000ffffccccffffcccccccccccc00000000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffcccceeeeeeeeaaaa0000ffffeeeeffffcccceeeeeeeeaaaa0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafafffff0f0fafaaaaafafa0000fffffafafffff0f0fafaaaaafafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcfffffcfcfcfcccccf0f00000fffffcfcfffffcfcfcfcccccf0f00000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefefffffcfcfefeeeeefafa0000fffffefefffffcfcfefeeeeefafa0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffff00ffffff00ff00ff0000000000ffffff00ffffff00ff00ff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffff00ffaaffaaaaaaaa00ffffffaaffffff00ffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffffccffccffcccc00cc00ffffffccffffffccffccffcccc00cc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffffccffeeffeeeeaaee00ffffffeeffffffccffeeffeeeeaaee00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0fffffff0fff0ff00f0f00000fffffff0fffffff0fff0ff00f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffff0fffaffaafafaaa00fffffffafffffff0fffaffaafafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcfffffffcfffcffccfcf0cc00fffffffcfffffffcfffcffccfcf0cc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffffcfffeffeefefaee00fffffffefffffffcfffeffeefefaee00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_142 : Nat := 0x555500000000000000000000000000005555
def goal_142 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfccc00cc00cc00cc00cc00cc00cc00cc00
def roots_142 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfefcfefcfefcfefcfefcfefcfefcfefcee00ee00ee00ee00ee00ee00ee00ee00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_148 : Nat := 0x11001100000000000000000000000000110011
def goal_148 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_148 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fafa0000fafa0000fafa0000fafa0000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcf0f00000f0f00000f0f00000f0f00000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfafa0000fafa0000fafa0000fafa0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffccccffffccccffffccccffffcccccc00cc00cc00cc00cc00cc00cc00cc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffaf0fffffaf0fffffaf0fffffaf0fafaaa00fafaaa00fafaaa00fafaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcf0cc00fcf0cc00fcf0cc00fcf0cc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffefcfffffefcfffffefcfffffefcfefaee00fefaee00fefaee00fefaee00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffaa00aa00ffffffffaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffeecceeccffffffffeecceeccffeeffeeee00ee00ffeeffeeee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffaf0faf0fffffffffaf0faf0ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fafaaaaafafa0000fafaaaaafafa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffaa00ffffffffffffaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffeeccffffffffffffeeccffeeffeeeeaaee00ffeeffeeeeaaee00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fff0ff00f0f00000fff0ff00f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffaf0fffffffffffffaf0fffaffaafafaaa00fffaffaafafaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfffcffccfcf0cc00fffcffccfcf0cc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffefcfffffffffffffefcfffeffeefefaee00fffeffeefefaee00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_194 : Nat := 0x5000000000000000500000000000000050000000000000005
def goal_194 : Nat := 0xffffffffffffffffcccccccccccccccccccccccccccccccc0000000000000000
def roots_194 : List Nat := [xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_196 : Nat := 0x11000000000000001100000000000000110000000000000011
def goal_196 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000
def roots_196 : List Nat := [xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffccccccccccccccccffccffccffccffcccc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffeecceecceecceeccffccffccffccffccee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffaf0faf0faf0faf0fff0fff0fff0fff0aa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfffcfffcfffcfffccc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffefcfefcfefcfefcfffcfffcfffcfffcee00ee00ee00ee00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_208 : Nat := 0x10001000000000001000100000000000100010000000000010001
def goal_208 : Nat := 0xffffffffffffffffffff0000ffff0000ffff0000ffff00000000000000000000
def roots_208 : List Nat := [xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffccccffffccccffffccccffffccccaaaa0000aaaa0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0fafa0000fafa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffffcfcfffffcfcf0f00000f0f00000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffffcfcfffffcfcfafa0000fafa0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffffffffffffffffff0000ffff0000ffffff00ffffff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffaa00ffffaa00ffffff00ffffff00aaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffccccffffccccffffffccffffffcccc00cc00cc00cc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffeeccffffeeccffffffccffffffcceeaaee00eeaaee00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffffff0fffffff0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffaf0fffffaf0fffffff0fffffff0fafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffffffcfffffffcfcf0cc00fcf0cc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffefcfffffefcfffffffcfffffffcfefaee00fefaee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffffffffffffffffffcccccccccccccccccccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffffffffffcccccccceeeeeeeecccccccceeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fafafafaf0f0f0f0aaaaaaaa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffaa00aa00ffaaffaaff00ff00ffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffccccccccffccffccffccffccffccffcccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffeecceeccffeeffeeffccffccffeeffeeee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fff0fff0fff0fff0ff00ff0000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffffffffaf0faf0fffafffafff0fff0ffaaffaaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfffcfffcfffcfffcffccffcccc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffffffffffffffffffff0000ffff0000ffff00000000000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffffffffff0000ffffaaaaffff0000aaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffffffccccffffeeeeffffcccceeeeeeeeaaaa0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffffffffffff0f0fffff0f0fffff0f0f0f00000f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffffff0f0fffffafafffff0f0fafaaaaafafa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffffffcfcfffffcfcfffffcfcfcfcccccf0f00000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffffffcfcfffffefefffffcfcfefeeeeefafa0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffffffffffffffffff0000ffffff00ffffff00ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffffaa00ffffffaaffffff00ffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffffccccffffffccffffffccffccffcccc00cc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffeeccffffffeeffffffccffeeffeeeeaaee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffffffffff0f0fffffff0fffffff0fff0ff00f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffffaf0fffffffafffffff0fffaffaafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffffcfcfffffffcfffffffcfffcffccfcf0cc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffffefcfffffffefffffffcfffeffeefefaee00
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
def isoMvS_74:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_74:Lower true dom_74 roots_74 goal_74 4:=lower_iso_b isoMvS_74 (by decide +kernel) lowS_41
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_41
def isoMvS_148:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_148:Lower true dom_148 roots_148 goal_148 4:=lower_iso_b isoMvS_148 (by decide +kernel) lowS_41
def isoMvS_194:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_194:Lower true dom_194 roots_194 goal_194 4:=lower_iso_b isoMvS_194 (by decide +kernel) lowS_41
def isoMvS_196:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_196:Lower true dom_196 roots_196 goal_196 4:=lower_iso_b isoMvS_196 (by decide +kernel) lowS_41
def isoMvS_208:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_208:Lower true dom_208 roots_208 goal_208 4:=lower_iso_b isoMvS_208 (by decide +kernel) lowS_41
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
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_slice_b [(0x303000003030000,1,17)] (by decide +kernel) lowS_41
namespace S_212
def pG:List (Nat×Nat):=[(4,20),(4,68),(4,132),(16,20),(16,80),(16,144),(64,68),(64,80),(64,192),(128,132),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_212.map (·&&&dom_212)
def gM:=goal_212&&&dom_212
def NN:Nat→Nat
|3=>3
|4=>6
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x1fd340cca707cb7
|4,0=>0x556e843993313b3162fc133d105da5
|5,0=>0x8d08864bc40626e
|6,0=>0x626e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x4400440000000000440044000000000040004000000000004000400000000000000000000000000000000220022000000000022000000011000000000000001100000000000000100000000000000010880088000000000088008800000000008800800000000000880084400440000000000440044000000000044000000000000004400022002200000000002200220000000000220022000000000000000000011000000000000001100000000000000110000000000000010880088000000000000000000000000008800880000000000000004400400000000000440040000000000044004000000000004400422002200000000002200000000000000220022000000000022000110011000000000010001000000000001100110000000000100010880000000000000088000000000000008800000000000000880004000400000000000400040000000000040004000000000004000422002200000000000000000000000000220020000000000000000110011000000000011001100000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x327063270a32703270532903e297d327032c70b3270a3297287065403210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x8411004
|4,0=>0x956056d565454c5
|5,0=>0x335b96a4
|6,0=>0x384
|_,_=>0
def wAt:=mkWire dB 15 213 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x234c1705cd074810740d725cd
|_=>0
def oO:Nat→Nat→Nat
|3,0=>0x200
|4,0=>0x624200000022
|5,0=>0x918100
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfba9630
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>8
|4,0=>0x13004
|5,0=>0x1b5
|6,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_208 4 roots_208 ops++addP pm 1 dom_196 4 roots_196 ops++addP pm 2 dom_84 4 roots_84 ops++addP pm 3 dom_148 4 roots_148 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_212 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_148 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_208 4 s (0,roots_208.map (·&&&dom_208)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_212 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_208 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124)],[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_212==dom_212)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_212 gM v ys):RunD true dom_212 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_212 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_212 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_212 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_212 roots_212 goal_212 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_212
theorem lowS_212:Lower true dom_212 roots_212 goal_212 7:=S_212.noCircuit
def isoMvS_29:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_29:Lower true dom_29 roots_29 goal_29 4:=lower_iso_b isoMvS_29 (by decide +kernel) lowS_27
def isoMvS_51:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=lower_iso_b isoMvS_51 (by decide +kernel) lowS_27
def isoMvS_53:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_53:Lower true dom_53 roots_53 goal_53 4:=lower_iso_b isoMvS_53 (by decide +kernel) lowS_27
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_57
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 4:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_27
def isoMvS_78:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_78:Lower true dom_78 roots_78 goal_78 5:=lower_iso_b isoMvS_78 (by decide +kernel) lowS_57
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 4:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_27
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_57
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_57
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_57
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 5:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_57
def isoMvS_99:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 4:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_27
def isoMvS_105:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_57
def isoMvS_106:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_43
def isoMvS_113:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 4:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_27
def isoMvS_114:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 4:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_27
def isoMvS_120:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 4:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_27
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 4:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_27
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_57
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 4:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_27
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 5:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_57
def isoMvS_198:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_43
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_43
def isoMvS_209:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 5:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_57
def isoMvS_216:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 5:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_57
def isoMvS_226:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_43
def isoMvS_240:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_240:Lower true dom_240 roots_240 goal_240 5:=lower_iso_b isoMvS_240 (by decide +kernel) lowS_57
theorem lowS_31:Lower true dom_31 roots_31 goal_31 5:=lower_slice_b [(0xcccccccc,8,10)] (by decide +kernel) lowS_29
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
def dzo_57_4:=0x3030303030303030
def gzo_57_4:=0x3030302030302000
def gsh_57_4:=0x303030203030200
theorem lowS_zo_57_4_41:Lower true dzo_57_4 roots_57 gzo_57_4 5:=lower_iso_b (d1:=dom_57) (r1:=roots_57) (T1:=gsh_57_4) [(dom_57,4)] (by decide +kernel) (lower_slice_b (T:=gsh_57_4) [(0x303000003030000,0,16)] (by decide +kernel) lowS_41)
namespace S_61
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(4,20),(5,13),(5,21),(5,37),(8,9),(8,40),(12,13),(12,28),(12,44),(16,17),(16,20),(24,25),(24,28),(24,56),(32,33),(32,40),(36,37),(36,44),(36,52),(48,49),(48,52),(48,56)]
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
|4,0=>0xb6d8e19fc8
|5,0=>0xa5e019bec497d24
|6,0=>0xd596d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccccc00cc00022002200220022cc88cc88cc88cc8b30033003300330000cc00cc0088008b333333300000000cccc0000cccc0003300330022002200c0c0c0c0c0c0c0c2222222222222222
|_,_=>0
def sP:Nat→Nat
|0=>0x436109436104361084376104310543210
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
|0=>0x182
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x20
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0xf9c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x19
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_57 5 roots_57 ops++addP pm 1 dom_53 4 roots_53 ops++addP pm 2 dzo_57_4 5 roots_57 ops++addP pm 3 dom_41 4 roots_41 ops++addP pm 4 dom_29 4 roots_29 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_61 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_57_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_29 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_57 5 s (0,roots_57.map (·&&&dom_57)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_61 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_57 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
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
theorem lowS_62:Lower true dom_62 roots_62 goal_62 6:=lower_slice_b [(0x5050505050505050,16,20),(0x5555000055550000,4,20)] (by decide +kernel) lowS_42
theorem lowS_79:Lower true dom_79 roots_79 goal_79 6:=lower_slice_b [(0xaaaa000000000000aaaa,8,9)] (by decide +kernel) lowS_78
theorem lowS_91:Lower true dom_91 roots_91 goal_91 6:=lower_slice_b [(0xa0a0a0a000000000a0a0a0a,8,9)] (by decide +kernel) lowS_90
namespace S_94
def pG:List (Nat×Nat):=[(2,10),(2,66),(4,20),(4,68),(6,14),(6,22),(6,70),(8,10),(8,72),(12,14),(12,28),(12,76),(16,20),(16,80),(18,22),(18,26),(18,82),(24,26),(24,28),(24,88),(64,66),(64,68),(64,72),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_94.map (·&&&dom_94)
def gM:=goal_94&&&dom_94
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x70d60
|4,0=>0x4f6c5225a70cf2e0088a
|5,0=>0x673e262b523b1dc23fa8132c70cbad0aa4009f9b03866020d5
|6,0=>0x4f7614c25d3432f0c8a5
|7,0=>0x4c25d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaa000000000000a0a00001555400000000000154022a2a2a280000000222222220000000000000000545454540000a0aa000000000000a0a0000155540000000000015152aaaaaaa800000002aaa8000444444440000000044444444aaaa88880000000000000001540154000000000154015402aaaaaa20000000022222222555555550000000000000000aaaa000000000000aaaa000155555554000000015401540282828280000000028282828555455540000000044444444
|0,1=>0x2aaa8000000000000000555555550000000050505050222222220000000000000000141414140000000014140000000002a8000000000000000555555000000000055555500aaaaaa000000000000000001555511100000000155551112aaaaaaa8000000022222222555555550000000055555500
|_,_=>0
def sP:Nat→Nat
|0=>0xcc1410660a0991982820cd80a0921982820cc1892e91991620cc1412a3305049c8660c4901982821828790660a1c41982d41066605043050b21828511260a0e3304a418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682ced9ab2f654a918f3186
|6,0=>0xc8d7d6cb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 26 95 0x7fffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1920911a10a6191a10411499191092
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x520041311200000100
|6,0=>0x91008171
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0xffde6e60a183080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x2506430010
|6,0=>0x8789
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_92 5 roots_92 ops++addP pm 1 dom_84 4 roots_84 ops++addP pm 2 dom_74 4 roots_74 ops++addP pm 3 dom_78 5 roots_78 ops++addP pm 4 dom_90 5 roots_90 ops++addP pm 5 dom_86 5 roots_86 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_94 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_86 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_92 5 s (0,roots_92.map (·&&&dom_92)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_94 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_92 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_94==dom_94)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_94 gM v ys):RunD true dom_94 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_94 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_94 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_94 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_94 roots_94 goal_94 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_94
theorem lowS_94:Lower true dom_94 roots_94 goal_94 8:=S_94.noCircuit
namespace S_107
def pG:List (Nat×Nat):=[(1,9),(1,33),(2,10),(2,34),(2,66),(3,11),(3,35),(3,67),(8,9),(8,10),(8,40),(8,72),(32,33),(32,34),(32,40),(64,66),(64,72),(65,67),(65,73),(65,97),(96,97),(96,98),(96,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_107.map (·&&&dom_107)
def gM:=goal_107&&&dom_107
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xb40cf
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0000000000000f0f00000000f0000000f0000000f0000000f00c0c00000c0c00000c0c00000c0ca0a00000a0a00000a0a00000a0af0f00000f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 108 0xfffffffffffffffffffffffffff
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
addP pm 0 dom_106 5 roots_106 ops++addP pm 1 dom_105 5 roots_105 ops++addP pm 2 dom_43 5 roots_43 ops++addP pm 3 dom_75 5 roots_75 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_107 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_75 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_106 5 s (0,roots_106.map (·&&&dom_106)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_107 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_106 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_107==dom_107)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_107 gM v ys):RunD true dom_107 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_107 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_107 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def pG:List (Nat×Nat):=[(1,17),(1,33),(2,34),(2,66),(3,19),(3,35),(3,67),(16,17),(16,80),(18,19),(18,50),(18,82),(32,33),(32,34),(48,49),(48,50),(48,112),(64,66),(64,80),(65,67),(65,81),(65,97),(96,97),(96,98),(96,112)]
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
|4,0=>0x1e85e1888c
|5,0=>0x88c8c245e20f31a
|6,0=>0x88c8c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000c000f000c000f000c000f000cf000f000f000f000c000c000c000cf0000000f0000000a0000000a0000f000f000f000f0000000000000000f000f00000000000f000f000000000000000000000000f000c000f000cf0000000f0000000f0000000f0000c000c000c000c000c000c000c000ca000a000a000a000a000a000a000a
|_,_=>0
def sP:Nat→Nat
|0=>0x42105421054821054271054106543210
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
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
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
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=lower_slice_b [(0x220022000000000022002200000000002200220000000000220022,16,17)] (by decide +kernel) lowS_212
theorem lowS_214:Lower true dom_214 roots_214 goal_214 8:=lower_slice_b [(0x440044000000000044004400000000004400440000000000440044,64,66)] (by decide +kernel) lowS_212
theorem lowS_234:Lower true dom_234 roots_234 goal_234 6:=lower_slice_b [(0x50000000500000005000000050000000500000005000000050000000500,2,10)] (by decide +kernel) lowS_226
def isoMvS_55:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_iso_b isoMvS_55 (by decide +kernel) lowS_31
def isoMvS_87:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_iso_b isoMvS_87 (by decide +kernel) lowS_79
def isoMvS_93:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 6:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_91
def isoMvS_103:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 5:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_31
def isoMvS_109:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 7:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_61
def isoMvS_110:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 7:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_59
def isoMvS_117:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 7:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_61
def isoMvS_118:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_61
def isoMvS_121:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 6:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_91
def isoMvS_122:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_59
def isoMvS_124:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 7:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_61
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 5:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_31
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_79
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 7:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_61
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 7:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_61
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 7:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_107
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 7:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_61
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 6:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_91
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 6:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_91
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 7:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_61
def isoMvS_203:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 7:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_59
def isoMvS_205:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 7:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_61
def isoMvS_206:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 7:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_107
def isoMvS_211:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 7:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_59
def isoMvS_217:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 6:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_91
def isoMvS_218:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 7:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_107
def isoMvS_220:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 8:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_213
def isoMvS_227:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 7:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_59
def isoMvS_229:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 7:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_61
def isoMvS_233:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 6:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_91
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 6:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_91
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 6:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_91
def isoMvS_244:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 8:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_213
def isoMvS_248:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 6:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_91
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xcccccccccccccccc,8,10)] (by decide +kernel) lowS_61
theorem lowS_95:Lower true dom_95 roots_95 goal_95 9:=lower_slice_b [(0xaaaaaaaa00000000aaaaaaaa,8,9)] (by decide +kernel) lowS_94
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0f00000f0e00000e000
def gsh_107_4:=0xf0f00000f0f00000f0e00000e00
theorem lowS_zo_107_4_43:Lower true dzo_107_4 roots_107 gzo_107_4 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_43)
def dzo_43_4:=0xf0f00000f0f0
def gzo_43_4:=0xf0e00000e000
def gsh_43_4:=0xf0e00000e00
theorem lowS_zo_43_4_43:Lower true dzo_43_4 roots_43 gzo_43_4 5:=lower_iso_b (d1:=dom_43) (r1:=roots_43) (T1:=gsh_43_4) [(dom_43,4)] (by decide +kernel) (lower_slice_b (T:=gsh_43_4) [] (by decide +kernel) lowS_43)
namespace S_111
def pG:List (Nat×Nat):=[(1,9),(1,33),(2,10),(2,34),(2,66),(3,11),(3,35),(3,67),(4,68),(5,13),(5,37),(5,69),(6,14),(6,38),(6,70),(7,15),(7,39),(7,71),(8,9),(8,10),(8,40),(8,72),(12,13),(12,14),(12,44),(12,76),(32,33),(32,34),(32,40),(36,37),(36,38),(36,44),(36,100),(64,66),(64,68),(64,72),(65,67),(65,69),(65,73),(65,97),(96,97),(96,98),(96,100),(96,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_111.map (·&&&dom_111)
def gM:=goal_111&&&dom_111
def NN:Nat→Nat
|4=>3
|5=>10
|6=>17
|7=>7
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xfef895ef7653102
|5,0=>0xf2b03c1ef8ad873ab87f867de681373ed0232e8e2a5a716071
|6,0=>0xf5dfdf2877efb32e3cbddbf7cb6911b3306a7492982927fa397221e5edaa57a5c5509452dc514e8e0fe04
|7,0=>0xba452932265714d5234f520c339ecc0d0bf
|8,0=>0x4f37e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000f0f0000000000000000555500000000000055550000550033330000333300003333000033005555000055550000555500005500ff000000ff000000ff00000000000f0f0000ff0f000000000000ff00ff000000ff000000ff000000ff00ffaa0000ffaa0000ffaa0000aaaacccc0000cccc0000cccc0000ccccffff000000000000ffff00000000ffff0000ffff0000ff000000ff00ffff0000ff000000ffff0000ff00ffcc0000ffcc0000ffcc0000ccccf0f00000f0f00000f0f00000f0f0aaaa0000aaaa0000aaaa0000aaaaffff0000ffff0000000000000000
|0,1=>0xf0f00000fff00000f0f00000fff000000000ffff000000000000ff000000000000000000ff000000ff00ffff000000000000ffff0000ff00ff0f0000ff0f0000ff000000ff00ffff0000ffff000000000000ff00000000000000000000000000ff000000000000000000ffff0000ff00ffff0000ffff0000ffff0000ff00ffff0000ffff0000ffff0000000000ff000000ff000000ff0000000000000000ff00000000000000ff00fff00000fff00000fff00000fff05555000055000000555500005500
|_,_=>0
def sP:Nat→Nat
|0=>0x38700324470dc1632447082a6488e1010d149c20324470cc0649c3203c8649c2079a293c0064244701927801e6488ee019220b406488ec018ab11c24588e1019270a8061a44101102380c32882418820
|1=>0x32447080c5488e1050c911c20324470c8068a4e1010c911c20327623840649c207992b11c20219223c006488f00193d38406488e1e0346488e1050c5488e12512238406ca4e101922
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa5055005
|5,0=>0x4563f63963362d62762161b61560f6
|6,0=>0xb87b17ab6a569e79779078978367c77576e76776075975274b7
|7,0=>0xe77e07d97d36cc7c57bf6
|8,0=>0xee6
|_,_=>0
def wAt:=mkWire dB 30 112 0xffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x481301326489325483102a2430120732520732514932636d4833014813013254bd102901326a26301203325201325325489a27301102326102325
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1e2709a2608005894248902388c2288821884208802
|7,0=>0x261946418c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xfff7b7777162603f3d3730250a030100
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0xc25701a47999b2932
|7,0=>0xecdfde8
|8,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_110 7 roots_110 ops++addP pm 1 dom_79 6 roots_79 ops++addP pm 2 dom_43 5 roots_43 ops++addP pm 3 dzo_107_4 6 roots_107 ops++addP pm 4 dom_109 7 roots_109 ops++addP pm 5 dom_107 7 roots_107 ops++addP pm 6 dzo_43_4 5 roots_43 ops++addP pm 7 dom_103 5 roots_103 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_111 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_107_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_43_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_103 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_110 7 s (0,roots_110.map (·&&&dom_110)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_111 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_110 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_111 gM v ys):RunD true dom_111 gM v (ori ys):=h
def Z (s:Nat):=barP dom_111 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_111 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_111 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_111 roots_111 goal_111 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_111
theorem lowS_111:Lower true dom_111 roots_111 goal_111 9:=S_111.noCircuit
def dzo_87_32:=0xff00ff0000000000ff00ff00000000
def gzo_87_32:=0xff00fe0000000000fe00ee00000000
def gsh_87_32:=0xff00fe0000000000fe00ee
theorem lowS_zo_87_32_84:Lower true dzo_87_32 roots_87 gzo_87_32 6:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_32) [(dom_87,32)] (by decide +kernel) (lower_slice_b (T:=gsh_87_32) [(0xaa00aa0000000000aa00aa,0,1),(0xcc00cc0000000000cc00cc,0,2)] (by decide +kernel) lowS_84)
namespace S_119
def pG:List (Nat×Nat):=[(1,17),(1,33),(2,34),(2,66),(3,19),(3,35),(3,67),(4,20),(4,68),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,23),(7,39),(7,71),(16,17),(16,20),(16,80),(18,19),(18,22),(18,50),(18,82),(32,33),(32,34),(36,37),(36,38),(36,52),(36,100),(48,49),(48,50),(48,52),(48,112),(64,66),(64,68),(64,80),(65,67),(65,69),(65,81),(65,97),(96,97),(96,98),(96,100),(96,112)]
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
|0=>0x52652452552d52652452552552552462d52752631f524525
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x62198000600
|6,0=>0x592480081
|7,0=>0x3c5c2d1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 9
def pmP:Nat→Nat
|0=>0x1ff99b1828100
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1208
|6,0=>0x301b501
|7,0=>0x1b6
|8,0=>5
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
def dzo_42_16:=0x505000005050000
def gzo_42_16:=0x504000004000000
def gsh_42_16:=0x50400000400
theorem lowS_zo_42_16_42:Lower true dzo_42_16 roots_42 gzo_42_16 4:=lower_iso_b (d1:=dom_42) (r1:=roots_42) (T1:=gsh_42_16) [(dom_42,16)] (by decide +kernel) (lower_slice_b (T:=gsh_42_16) [] (by decide +kernel) lowS_42)
def dzo_106_16:=0x5050000050500000505000005050000
def gzo_106_16:=0x5050000050500000504000004000000
def gsh_106_16:=0x505000005050000050400000400
theorem lowS_zo_106_16_42:Lower true dzo_106_16 roots_106 gzo_106_16 5:=lower_iso_b (d1:=dom_106) (r1:=roots_106) (T1:=gsh_106_16) [(dom_106,16)] (by decide +kernel) (lower_slice_b (T:=gsh_106_16) [(0x505000005050000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_107_16:=0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16:=0xf0f00000f0f00000f0e00000e0a0000
def gsh_107_16:=0xf0f00000f0f00000f0e00000e0a
theorem lowS_zo_107_16_42:Lower true dzo_107_16 roots_107 gzo_107_16 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_16) [(dom_107,16)] (by decide +kernel) (lower_slice_b (T:=gsh_107_16) [(0xa0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_42)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,10),(8,40),(8,72),(16,17),(16,80),(18,19),(18,26),(18,50),(18,82),(24,25),(24,26),(24,56),(24,88),(32,33),(32,34),(32,40),(48,49),(48,50),(48,56),(48,112),(64,66),(64,72),(64,80),(65,67),(65,73),(65,81),(65,97),(96,97),(96,98),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|4=>11
|5=>96
|6=>286
|7=>130
|8=>18
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xc239791fb58ae7f840346b4076925d685384022124cd221e2d02639
|5,0=>0xf5917f42b3f30fbe91b6dff3fd79d3cba21c476fc3296c2959c1b17b2c8fb2b80b0d94b0499afcb1abc5aabb06aa2c8aa16ea151f9e1a79af6b9954a98edc90f319044e8f2488eeac8dea98a95f873fc819927b7777548773d0d718226f6a36962c67b77678596613b625f65f6325c4b35bcff5a1da599ea58e305621e556285543850a64505e34f17c4ecb34c20248b9e45ff7453b1423a73f4c93f3a83cb6f3c13837e7932ab430c133046c2e9472dc3e2daf929d76224701fb221e6e21bc0f1b7d41af491aa2c198ec18cd912e1912a0d129d61249411af510aa6109c30da900c4100b1340a55209ce1091b3048db
|6,0=>0x445e2436d042bc3429a0426f7419d64135c407ae403334019c3feb93f8de3e4653d8d83ca593ad673ac553a1973976a3934e38fcb38cd338c893833435f74359b8352da33588334033285e318f2310cf30c132dc3e2db312d6602d21b2cfd32cd922ca302c8992c7372c45c2b8992a19a29d6e294582911a2901f28c16287712845c275db26e7e26a562676f26768242e123eb7219802107620fe3208691fdea1f3071e0c41d5641c5741bde31b81f1ac5e1a66e1a27c1917418afd1854a1827b1793d1741017402172911574215733144fc1431713ecd1340c1339511466111f9109c3107f5105c71041a0fc1d0effc0e6420e4e40e00e0dede0d8de0d2100d1770ce040c09c0bf0b0bced0b3240a52c084e107b5407a4c079810765206f3905eae05d3a05a99050d504d6e0346d032ce02ec4024bd023ed0148f00dc8007d7
|6,1=>0xbbc39bbac7bb4e5b5dc8b3b27b0b1dafae9abff2a9b57a9938a7af1a73fca6162a1343a0d91a08679ffff9dfad9d1759d0509c1819be0a9bdcd9bd4e9b4e59ab1e97d44975f19676c956d494d4d948e293f3791e17917148bb078b741897d4880298776487591873e28554e845be834b8822f1819928182980ea67ec677e51f7d4b87b6d87abea7a5f676b71767bc74df374cf87429f7423b716c76df0b6c80968f8767aeb6757b66c9066c3566b616645e66357653ec64bfb647bb6460564039635e9633f6631d46211a611be606aa601ce5fc0b5f8b45f4dd5ede65e7a75e7755dfe45d2905d1d05b7cd5b4155abee59a935965558c10587dc5846f5815157ebd56e76569b7558fa554c055438535f1530bf52f46522c051f844fa294f6034f4764e6904e45f4c5204c1c54ba444a4e64a3b448e5846ca646b16465d54566d
|6,2=>0xff4cbf72b4f545df0c6eee511e81b6e4babe4067e0d6ce08bbde9cede3cedbfbbd9312d8978d65a0ce94fce0b9cba21c89e2c82e7c5a81c36a9c0790bf731bed59be66bbe129bd8f2bc667
|7,0=>0xf6c29f60caf0108ea376d8978d32fccf374cd78fc9c0ac99c6c7803c5a81c37a2b063baf2deaee04acb45a5d67a1c589c5e79aead9a1b59a1369920e93d03907508eb9b8e39f8ceb38a63785320851da851048264381ea47b99d7b94478e10779817634a75a0870faa70ed16b95b6b85e6b81866b9c64ff4611be5f86f5ef3f5e34e5a9d3599c357f54560344ffd34f9294f6de4f6444c8204c3964b08a4938f487b546a12446b542bb83f9493df5c3dc363b21c3a7ed3a197395313910435a62353c12ef062e5222e2852e1d02df802dbae2cd922a9472a8852a0392982b297df279862748f25f6125268243b72329121a542093d205631fcde1e7811e5361dd671d0481ac5e18cf51861b15f7914dab1489e14394141ed1340012c1f0f5cd0ce6c0cc950ca2c0b41709d1a09a400755005fa1054840416e01a200137e001c7
|7,1=>0xfb527f7f4a
|8,0=>0xb518893d037f49378ef06900d685a762b5b5f5a85e0d45459947c683c58532d0c300162131a1cf4b1b67807721
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f000f0f0f000f0f0f000f0f0f000030003000c000c00030003000c000cf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0cf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0ae0e0e0e0e000e000e0e0e0e0e000e00f0c0f0c0f0c0f0c0f0c0f0c00000000f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0a0f0a0f0a0f0a0f0a0f0a00000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f0f000f000f0f0f0f0f000f00f0f00000f0f00000f0f00000f0f0000f0a0f0a0c080c080f0a0f0a0c080c08e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0000000000000000
|0,1=>0xf0f0f0f0f0f0f0f0f0c0f0c00000000f0f0f000b0b0b000f0f0f000b0b0b000000000000000000f0f0f0f0c0c0c0cf0f0f0f0c0c0c0c0f000f000c000c00f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0cf0f0f0f000000000f0e0f0e00000000f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f000f0f0f000f0f0f0f0f0f0f00f0f0f0f0f0f0f0f0f000f000f000f0000f000f000c000c000f000f000c000cf0f0f0c0f0f0f000f0f0f0c0f0f0f00f0f0f0f000000000f0f0f0f00000000f0e0f0e0f0e0f0e0f0e0f0e0a0a0a0a30303030c0c0c0c030303030c0c0c0cf000f000f000f000f000f000f000f00e0e0e0e0e0e0e0e0e0e0e0e00000000
|0,2=>0xc0c0c0c0c0c0c0c0c0c0c0c0c000c00f0c0f0c0f000f000f0c0f0c0f000f003030303030303030303030303020302f0e0f0e000000000f0e0f0e00000000f0e0f0e0a0a0a0a0f0e0f0e0a0a0a0a4040404040404040404040404040404f0f0f0f0f0c0f0c0f0f0f0f0f0c0f0c30303030f0c0f0c030303030f0c0f0cf0f00000f0f00040f0f00000f0f000400000000f0f0f0f000000000f000f00f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a5050505050505040505050505050504f0f0f0f0f0f0f0f0e0e0e0e0e000e003030303000000000303030300000000c0c0c0c000000000c0c0c0c00000000a0a0a0a0f0f0f0f0a000a000f000f00
|0,3=>0xa0a0a0a0e0e0e0e0a0a0a0a0e0e0e0e504050405040504050405040504050400000000f0e0f0e000000000f0e0f0e00f000f00040004000f000f00040004f0f0f0f0f0f0f0f0f0f0f0f0f000f00f0f0c0c0f0f00040f0f0c0c0f0f00045050505000000000d0d0d0d0c0c0c0cf0c0f0f0f000f000f0c0f0f0f000f0000000000f0a0f0a000000000f0e0f0ef040f040f040f040f040f040f040f040000000000000000f0f00000f0f0f0cc0c0c0c0c0c0c0c0c040c040c000c00f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e000000000000000000f000f000c000cf0f0f0f0f0f0f0f000f000f000c000c3030303030303030101010101000100
|0,4=>0x3030303030303030303030300000000a0a0a0a000000000f0e0f0e00000000f0f0f0f0f0f0f0f0c0c0c0f00000000f0f0f000f0f0f000f000f000f0f0f00f000f000f030f000f000f000f030f0000000000c0c0c0c000000000c0c0c0cf0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e00f000f00000000000f000f000c000c00000000f0a0f0a000000000f0a0f0af0f0f0f0f0f0f0f0f0f0f0f0c0c0c0ca0e0a0e0a0e0a0e0a0e0a0e0a0e0a0e00f000f000f000f000f000f000c000cf0f0f0f0c080c080f0f0f0f0c080c08002000200020002000200020a0a0a0af0f0f0c0f0f0f0c0f0f0f0c0f0f0000f000f000f000f000f000f000e000e00
|0,5=>0x505050505050505050505050000000000f000f00000000000f000f00000000302030203020302030203020302030200f000f000f000f000f000f000e000ef0f0f0f040404040f0f0f0f04040404f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e5050505000000000505050500000000d0d0d0d0c0c0c0c0d0d0d0d0c0c0c0cf0f00000f0f00000f0f03030f0f03003030303030303030303030303000300f030f030f0c0f0c0f030f030f0c0f0cc0c0c0c0f0e0f0e0c0c0c0c0f0e0f0ef0f0f000f0f0f000f0f0f030f0f0f00c0c0c0c0c080c080c0c0c0c0c080c0800000000e0e0e0e000000000e0e0e0e00300030c0c0c0c000300030c0c0c0c
|0,6=>0x1010101010101010101010100000000f0f0f040f0f0f040f0f0f040f0f0f04f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0af0f03030f0003000f0f03030f000300f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0ef0f0f0f030203020f0f0f0f03020302c0f0c0f0c0c0c0c0c0f0c0f0c0c0c0c0000000000000000f0c0f0c0f0c0f0c000000000000000030303030300030000000000000000005050505050005005050505050505050500050005000500f0f0f0f0f0f0f0c0f0f0f0f0f0f0f0c0080008000c000c00080008000c000cc0c0c0c0f0f0f0c0c0c0c0c0f0f0f0c0000000000000000f0f0f0f0f000f00f0f00000f0f00000f0f0f0f0f0f0f00
|0,7=>0xe000e000e000e00e000e000e000e000e000e000e000e505050505050505050505050500050000f000f000f000f000f000f000a000aa0a0e0e0a0a0e0e0a0a0e0e0a0a0e0e0000000000000000c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0504050405040504f0f0f0f030303030f0f0f0f0300030030303030300030003030303030003000000c0c00000c0c00000c0c00000c0c000000000000000000f000f00000000f0f00000f0f00000f0000000f0f0000f0c0f0c000000000f0c0f0c00000000f0f0f0f0f0f0f0f000000000f0a0f0af0f0f0f0f0f0f0f0303030303000300f0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c
|0,8=>0xf0a0f0a0f0a0f0a0f0e0f0e0f0e0f0eb0b00000b0b00000b0b00000b0b0000f0b0f000f0b0f000f0b0f000f0b0f0030303030303030303020302030203020000000000000000f0f0f0f00000000f0f00040f0f00040f0f00040f0f0004f000f0c0f000f0c0f000f0c0f000f0cf0f0f0f0f0f0f0f050505050000000080808080c0c0c0c080808080c0c0c0c8080808080c080c08080808080c080c0040004000400040004000400040004f0f0f0f030303000f0f0f0f03030300f0f0f0f0a0a0a0a0f0f0f0f0e0e0e0e00000000f0f0f0f000000000f0c0f0ca0a0a0a0a0e0a0e0a0a0a0a0a0e0a0e5050505040404040505050504040404
|0,9=>0xf0a0f0a030203020f0a0f0a030203022020202020a020a02020202020a020af0f0f00000000000f0f0f0000000000f0f0f0c0c0c0c0c0f0f0f0c0c0c0c0c0000000000000000505050504040404f0f0f0f0f0f0f0f0303030300000000f0f00000f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0ac0c0c0c0c000c000c0c0c0c0c000c00f0f0f0f0f0f0f0f0c0c0c0c0c000c00b0b0b0b0b000b000b0b0b0b0b000b000000000000000000c0f0c0f0c0c0c0cf0f0f0f000000000f0f0f0f0c0c0c0cf0f0f0f0f000f000303030303000300f0f0f0f00000f0c0f0f0f0f00000f0cf0f0f0f0f000f000f030f030f000f00
|0,10=>0xd0d0d0d0d0c0d0c0d0d0d0d0d0c0d0c000000000000000030303030000000000300000f0f0000000300000f0f0000c0c0c000f0f0f000c0c0c000f0f0f000030003000000000003000300000000f0f0f0f0f0f0f0f0505050505000500f0f0f0f0f0f0f0f000f000f00000000c0c0c0c0c0c0c0c0f0f0f0f0c0c0c0ca0a0a0a0f0f0f0f0a0a0a0a0f0a0f0a00000000f0f0f0c000000000f0f0f0cf0f0f0f0f0f0f0f000000000e0e0e0e303030f000000000303030f00000000f0f0f0f0c0c0c0c0f0c0f0c0c0c0c0c0000000040404040000000004040404e0e0e0e0a0a0a0a0e0e0e0e0a0a0a0af0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a
|0,11=>0xf0f00000f0f000000000000000f0000f0f0f0f000e000e0f0f0f0f000e000ef000f000f040f040f000f000f040f04f0f0f0f00000c0c0f0f0f0f00000c0cf030f030f000f000f030f030f000f00f0f0f0f050505050f0f0f0f05000500f0f0f0f000400040f0f0f0f00040004f0a0f0a0f0e0f0e0f0a0f0a0f0e0f0ef0f0f0f0f0f0f0f000000000f0c0f0c00000000303030300000000030003000000000000000000f0f0f0f0f0a0f0af0f0f0f0f0f00000f0f0f0f0f0f000000000000f0c0f0c000000000f0c0f0cc080c080c080c080c080c080c080c08f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0c0000000000000000f0f0f0f0f0c0f0c
|0,12=>0xc000c00000000000c000cf0f0f0f000c000c0f0f0f0f000c000cf000f0f0f000f0f0f000f0a0f000f0af0f0f0f0a0e0a0e0f0f0f0f0a0e0a0eb0b0b000b0b0b000b0b0b000b0b0b0030303000f0f0f00030303000f0f0f00f0f0f0f0f040f040f0f0f0f0f040f04f000f000f0c0f0c0f000f000f0c0f0cf050f050f000f000f050f050f000f00c0c0c0c000400040c0c0c0c000400040000f0f00000f0f00000a0a00000a0a0000000000000000f0a0f0a0f0a0f0af0f0f0f000000000f0f0f0f0f0a0f0a00f000f0000000c000f000f0000000cf0f0f0f050405040f0f0f0f05040504f000f000f0e0f0e0f000f000f0e0f0e
|0,13=>0xf0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c0000000000000000f0f0f0c0f0f0f0cf0f0c0c0f0f0c000f0f0c0c0f0f0c000000000000000000d0d0d0d0c0c0c0cf0f00000f0f00000f0f000f0f0f000000000000f0f0f00000000000f0f0f00c0c0c0c0000000c0c0c0c0c0000000cf0f0f0f0f000f0c0f0f0f0f0f000f0c50d050d000c000c050d050d000c000c00f000f000f000c000f000f000f000c0030003000300030003000300000000000000f0000000c0000000f0000000c3030303030303030303030302020202f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0ad0d0d0d0d0d0d0d0d0d0d0d0c0c0c0c00200020a0a0a0a000200020a0a0a0a
|0,14=>0x5050505050505050505050504040404e0e0e0e0e0a0e0a0e0e0e0e0e0a0e0af0a0f0a0f0a0f0a0302030203020302f000f0f0f000f0c0f000f0f0f000f0cf050f050f040f040f050f050f040f04a0f0a0f0a0f0a0f0a0f0a0f0a0a0a0a30303030303030303000300030003001010101010101010100010001000100f0f00000f0f0f0c0f0f00000f0f0f0ca0a0a0a0a0a0a0a0f0f0f0f0e0e0e0ef0f00000f0f00000a0a00000a0a0000f0f0f000f0f0f000f0a0f000f0a0f00000000003030300000000000303030030303030f0f0f0f00000000000000000000f0f00000f0c00000f0f00000f0cf000f000f000f000f0e0f0e0f0e0f0e
|0,15=>0xf0f0f0f000000000f000f000000000020202020a0a0a0a020202020a0a0a0af030f03000000000f030f0300000000303030003030300030303000303030000c000c000c000c000c000c000c000cf0f000f0f0f000c0f0f000f0f0f000c30300000f0f0000030300000f0f0000f030f000f0f0f000f030f000f0f0f000000000050505050000000005000500f0f0f0f0f0f0f000f0f0f0f0f0f0f0050505050505050005050505050505000000000000400040000000000040004f0f00000f0f04040f0f00000f0f0404000000000000000000000000f0c0f0cf0d0f0d0f0c0f0c0f0d0f0d0f0c0f0cf0f0f000c0c0c000f0f0f000c0c0c00
|1,0=>0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0af000f0f0f000f000f000f0f0f000f00f000f000f000f000f0c0f0c0f0c0f0cf0f0f0f0f0f0c0c0f0f0f0f0f0f0c0c5050505050005000505050505000500a0a0a0a0a0a0a0a0e0e0e0e0e0e0e0e0000f0f00000f0000000f0f00000f00f0f0c0c0f0f00000f0f0c0c0f0f0000f000f000f000f000f0f0f0f0f000f0000f0000000f0000000f0000000f000000f000f000f000f000f000f000000000000f0f0000000000000f0f00000000f0f00000f0f0f0f00000000000000000000000000000000e0e0e0e0e0e0e0e0000f0f00000c0c00000f0f00000c0cf0f0f0f000000000303030300000000
|1,1=>0x30003000f000f00030003000f000f00
|_,_=>0
def sP:Nat→Nat
|0=>0x40641e170302044040c80c1806028341e21040580014018440c0510050061f0881810140f0440c08000103a030d82000140186c380800050060a0b81810030d0440c080001006070302000180a05c0c080003c10120b0001a150403800140780802000200c26060003c1012070001a03088400a0d078201c000680c180b00010060a048200803038180a04018080200
|1=>0x88d010000a00c361719820280f0302064000a03c0c081880028030882060000a00c222f040001a03170201c0014834062e04000280f030202c000a00c2208168001e2c0601810000200c5606000501e0815058000d0184410280001032030d8241014138440c0800050061b048204c190781810160009406110581800040680c1801000500611030900014018444606
|2=>0x218500611008002803088bc0a080a00c22062100028410881810000184410120700052030882024000a00c8006040001a03088201c000a03c18061f800080d018207c00018440c081e800280f0302078000680c221004000760d0186c10000a0e82206040002803088e40c050a03c7006040000611030206e0006864061100814080d018d810000a0d40611030202803
|3=>0x948000d0a03c18010000c22082794400140181c220602834061104140000d078b810000a03c2e060413c064e08818100001844024725000280f089340c080a1302e0604000280f2581810000680c5c080b000080d0186c10000a00c0411008000849018300c000a03c0c0824000280f0e0181000018440c3f2380008460186c10000a03c180622800280f030208800
|4=>0xe80c22060417800250a00c22062e8001a0f088202400230501e1703020280303020b8000216c061b040000825019680c000a00c2210030141a0317020000f0882024000a00c360b040001a151702000040186cb0080000c22080905800032a844101200050ae110302000140785c105600034065508820000308950104a000340611058200014298440c08000500611
|5=>0x30202c003585006110302000041280c360604000d414018440c080006406113481810000a00cd011030141014078b80c0800050061103020ce000a00c22060419800190a00c220604194c814018440c0800050061103020c6000a03c22620302000600a0440c0800064061708818102224850061b088200004018440c082f8001a030888410160006428030d85c0c08
|6=>0x3b9d80014089d00c0800050061f088181014018440c08390003203088240c082f0500611040a82c000e8642803088181014018440c08388001a14078300c08000642803380440c0802050061b041280014018440c0837800286e0881810000a00c2206040f4006d0a00c1811030001a14078440208000104a030601800143600c2206040001a14018440205000640611
|7=>0x1844d20604000062c060440c080005006110581810000a00c220640820000401844b006040001a1401844028000050061103020fe00128500611031f80014018440c083e800280308818107c000500611031481000020500611031ec0014018440c052e8004a140186c220100050060c08818f4050683c2221040002803088181079001e028030881810000a00c2208
|8=>0x64061103020ee0006a2c1e110302000140185c22060417c288a060440c080001028034481810000a00c220903021106d0a00c2e1103020280f08818108000050061b088210e00068500611042140014018440c0540000280308818108600050060c1b01810004205006110302000830a00c220604000280f2d0300c08000642803088cc0c080a00c2206042080014
|9=>0x78181016000502e113a018100002050061117820001401a402206040002803478440c08000ec28030881810000a00c2206040c80014018440c053f0001a19018440208000511a110302000140185c220103014280308818108c00010061b03020b2000a00c361100814001401844020623800321401844105600050061b089e80a080a00c2206040c4000d018441012
|10=>0x1a7c2206040002803088193c000a00c36112c0200014018b80c08000101a140186c10000a2701e11030200014018440c084d800280f08818109a00264281b0881810004c0500611030200014018440c960405006110325410000a00c2294030200014018447206040012614018440c050405006110302124004885006110302000140a8b80c08000500611178200014
|11=>0x400032030881810ab00050060c088187e000a00c2206042a80014018441206042a408a8018440c080005006110329c1000018b02201030200014018440c0853000080308818108800050061b0b8180a080a00c2206040f00014018440c0852800280f0881810a400010b6030881810000a00d4611030200014078440c0851000280f08a840c00500501e0c030200014
|12=>0xa00c2206042dc0014078440c08288000611030207a001d8500611048181014018440c085b0016a14018440c08000501e0c030210a005a00c2206042cc00140184402b200034280308914100058850061103020003b0a00c22082b0016014018440c080005006115781810000200c2206042b800610680c2206040002811030215a000a03c22065602000460a03c2206
|13=>0x30217e00068501e060405800be0a00c2206040007614018440c0504118061103020bc000200c22060413c00040a00c0c080b00028035e8440c0800050061b088fc1000022f006110302000140a8440c080003428030d85c10000c80d76110302000ba0a00c2206040002803060440c450005006110302088000a03c1801030017214018440c080005006b8088181000
|14=>0x4220280f0181810160033028030881810000a0440ccb0400028110302194006485006110302000040a00d90060400028030db1c0c080005006110302090000a00c22066302000040a0440c0862800081d018440c080018428030d81810000a00c221c03020000d0a03c2206040018614018440c0800050061103021840060850061103020001401b002206040002811
|15=>0x340673088200014018440c086b80028030881810d600050061103021aa00128501e11008180014018440c086a00028030881810d3000642803690440c080c80c22060414400490a00c22064000008033981810000a00c22d10302000290a00c220104000280308819a0000a03c22060432800046700c22060400028cd0881810000c83c22060408800140185c2206
|16=>0x406428030d8441208128501e0c0300028dd08818100006850060c0880400140186c223304000280308b700c08000a516030881810000680c5c1104000081401818105d000501e11030210e000a36c220604000280f08819b2080007428030d84410000203406110082000d80a00c2206040002803038440c08000101a030d82000140185c22060413c0814018441056
|17=>0x18440cea04000760d018440c08000501e112c01810000a00c2e11041580014018441022748002803638440c0500050061103021d0000a39c06110302000e60a00c22060400028e40881810000a03c22060438c0014078440c087101028030d80410000c80c22060411c0014018440c7a029641a140881810c500050061103021c2000a00dc0110302000146f00c2206
|18=>0x3516030d84410001d80c2206040880014018442006040002803788440c08000501ef00881810001d850061b030200014018440c087780028030d85c02080005006117701810000685006360882000044580c36060400032140184402060281028031b01810000a00c2206043b4001401bb02206040001a1401844107e000a41a030888410000a00dd611030200014
|19=>0x4000065a160440c0800050061103021ee00230500617088181093018440c082f0000849018440c080003c22081112800040a00c22067a80028e4030200014018440c087a000280f0b8181022000101a03088181000020340606040580014018440c087180028f30881810000680c5c080016c280f0881810000a00c2206043c800290a00c2206040005214018181016
|20=>0x81810000a00dfa110302000140196818110302000250a00c22090302000040a00c180604000280f0881810fc00050061100821f6000a03c2206040a80014018440c08570002803088188a080005006110325c100002064280308818100049850061103020001407a742206040004a14078440c0800051f40308818100001844101200051f0110302000147800c2206
|21=>0x30219e000a03c2206041640014018440c052c8008c190a00c2206040000814018440c08678003a14018440c08000500611030202c0002050061103020ec000a00ce01103020001401844d20604000280308818f6000a00c22060413c00bc0a00c220604000280308819fc000a00c22060419400290a00c36110302000140184402082500006110408894000a00c2e11
|22=>0xa22c061b0881810000a00c220903020b20012850061103021f60050050060c0881810000c8500611048181014018440c08818ec28030881810000a00c2233030200014018440c7a041780014018460406040002803088181101000ec0814018440c080005006110302200000685006110081810000a00d90110302000044580c220604000280308bfc0c08000500611
|23=>0xa0440c08830000819018440c0800051be030d8440c0800050061103020ba000a00c181100818000d018444208000102803088180a0800050060c0881810850003428030880410000a00c2206043f00014018440c0874800280308818110500050061103020ee000a00c5c06040000814018441206040003214018440c05040501e110302094000a00cb411008181000
|24=>0x2c80028033806c22060400168140186c220604000280308818109a0005022060431400040a00c220604128000d0a03c220604000da190a00c22060400029080881810000a0440c08728001a14018440c08808001a8b018440c080041c28030881810000c850061b0881810007b050061103020000d0e850061103020000d0a00c22060405800250a00c2e1103020000d
|25=>0x4000080d0a00c220604000280f0b81810000a00c22060442c00040a00c22063d0200014088191c080005006d208818100012850060c088180014018440c081f000280f088184208000500611031e810590011828030881810000a00c230a03020000d0a00c22060282000041280c2206040001a0308818105e0005006110302212000a00c22a10300028030b8440c08
|26=>0x881810000a00c2e110302044000a00c2206041d400148780c36110302000290a00c220604000280f088040c080003428030b8440c0800050070e0881810000a044020604418004606850061103020001401c3422060400028036905c2206040021814018440c08000642803088040c0800034280f018440c0800050060c088180a000200c220604164000d0a00c2206
|27=>0x7d80028030881810590005006110301410000a00c2206040a800250a00c220604000280f0881810000a00c2206041d800b40a00c2206040002811030220c000c850061103020005b0a00c2206040002803170440c08000a41a14018440c08000502206043e400040a00c360604001321408818100002034061103020001401818111000050061b088209400860342803
|28=>0x28030881810000a00c220610820000d0a00c22060400028030b8440c08000521e030881810000a03c0611030200014018440c08250002803088181000020500611030200014018440c08
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32502d50285023501e50195014500f500a500550005
|5,0=>0x1b061aa61a4619e61986192618c61866180617a6174616e61686162615c61566150614a6144613e61386132612c61266120611a6114610e6108610260fc60f660f060ea60e460de60d860d260cc60c660c060bb50b560af60a960a3609d60976091608b6085607f60796073606d60676061605b6055604f60496043603d60376
|5,1=>0x26c62666260625a6254624e62495244523e62395233622d62276221621b6215620f6209620361fd61f761f161eb61e561e051da61d461ce61c861c261bc61b66
|6,0=>0x424741d7416740f7408740173fa73f373ec73e573de73d773d073c973c273bb73b473ad73a6739f73987392638b7384737d73776371636a7363735c7355734e7347734073397332732c6325731e73177311630a730372fc72f572ee72e772e072d972d362cc72c572be72b772b072a972a3629c7295728e72877280727972727
|6,1=>0x5db75d475cd75c675bf75b875b175aa75a3759c7595758e75886581757a7574656d7567656075597552754b7544753d7537653075297522751b7514750d7507650164fb64f474ed74e674df74d874d174ca74c374bd64b674af74a874a1749a7493748c7485747f64787471746a7463745c7455744e7447744074397432742b7
|6,2=>0x792778c6785777e77777770776a6764675d7756774f77487741773a7733772c7725771e771777107709770276fc66f576ee76e776e076d976d276cb76c476bd76b766b076a976a2769b7694768e6687768076797672766c6665765e7657765076497643663c7635762e7627762076197612760c660575fe75f775f075e975e27
|6,3=>0x947794079397932792b7924791d7916790f7908790178fa78f378ec78e578de78d778d078c978c278bc68b578af68a878a1789a7893788c7885787f68787872686c6865785e78577850784a6843783c7836682f78287821781a7813780d680677ff77f967f277eb77e477dd77d677cf77c877c177ba77b467ad77a677a067997
|6,4=>0xa107a0b5a0569fe79f779f079e979e279db79d569ce79c959c279bb79b479ad79a679a0699b5994798d7986797f79787971796a7963795c7955794e7
|7,0=>0xbdd7bd76bcf8bc78bc07bb97bb27bab7ba47b9e6b968b8f7b887b808b788b708b688b608b597b536b4c7b457b3d8b367b2f7b278b207b188b117b0a7b037afc7af57aee7ae68ade8ad77ad07ac88ac17aba7ab46aad7aa67aa06a997a918a8a7a846a7c8a757a6d8a658a5e7a577a507a497a427a3b7a347a2c8a257a1e7a177
|7,1=>0xdab8da56d9e7d986d917d8b6d847d7c8d748d6d7d658d5e7d577d4f8d487d417d398d327d2a8d237d1b8d138d0c7d057cfe7cf68cf06ce97ce18cdb6cd47ccd7cc67cbf7cb78cb07ca97ca18c9a7c937c8c7c866c7e8c768c6e8c677c616c598c527c4a8c446c3e6c368c2f7c287c208c197c118c098c018bfa7bf37beb8be47
|7,2=>0xdba7db37
|8,0=>0xe357e2e7e277e207e197e127e0c6e057dfe7df77df07de97de27ddc6dd57dce7dc86dc17
|9,0=>0xe3c6
|_,_=>0
def wAt:=mkWire dB 273 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x8851068870a0190a018018450081003021018b90a019088850a018031650a023068870a0180a019068870a0180a01902004088850a0190a018018450a1290a01a088510a005030210685c0a0190485103001068870a0180a019068bb0a0180a019088650a019030210a001008010304503021068bb0a0190a0180a0190a018148870a0180a0190a045008100a0450a0010685c0a0190c86c0a001060640a001
|1=>0x8819019d70a05f08801398010d850088190011d06053030010c8190201b0885103051018450a01a088190885100866030211b00d088a9030230c8210a0010a01901845088210a021088510305103021068470a0190a0cd030150881903179088520d80308819088850a01801845088510201708851088010684501985020030880100851030210c8230a0010a0180a019068870a0190a018030650a00108819
|2=>0xa05f1d8180200100847030210a019030210a00108a39018ab03023088190304503021030ee0c845068870a0180a0190201b0a0450a0010880101a150303308851089d9030010a023128010a021088010682303051031670a023068230305108a150303308821030150a16803031008100885103021031650a023030510b8060880100847089b6041d90181a0601b0882103045030030a0190a018018451f001
|3=>0x30330a06e088190601803021088210881a0a05d019cf0d85008819030650a0010d85208819250210305303001088520a168008452c8010a0230881900145008530a0a9030231281a10821030500184501845088214b82202018031650a023088190885103051088194e81907850068030a01901a2d0a003060654b8010201808851150120a0450a1e903003018b9088850a0181d8180a05d068470a019019d7
|4=>0x78870a0180a33d0201a08851018160400103052018452c8010a023068470a019078ab0184503023078870a018018450a01a08851088190311f060530181600021088510685c0a0190a1290a01a018450a3110600300853030210198702003088510a01902001088510c81b0a001030510a02104129030530a0450a1d90181a078850a01801845088890a01b03033088210882103021018452d0530303108851
|5=>0xa0230d8530e8210a01908b9501814040010683e0a019108020a018018450605308821018166f8030d80d088210a0210184501a5d02018008010304503021088850a0180a0190601b019d50a05f0336b07853068030a0195e0450a1d9060640a0010a0190881908851030660a0011d81b020010d850088190a0190680d0a01901845060010085303021030510d850088190317d0a0010d85103045398220d850
|6=>0x300307850018450a02101845068870a0180a01908be5018870a0180683c0a019030650a001128190a0210a01b0a01a018457b0230200d08b9501814040010328303052018450a1290a01a0885106847030510683e0a0191281a0a0210a019088850a0180a0a9030230a0190a05d0c8040683c0a01908851030450302108851088a90680f0a019008470a0180a0190c84708851031650a023030ee0a05d08965
|7=>0xa0030a05c088010201a088510a023018450a023000210c8190a0010201a08851068030a019068470a0190a0450181a0b819088010317908852041d90181a0c81b0a0010a1d90181a10822030500b823088010d8510881903053030210a01b0a01a03021088010a3ef0881a0303108821030010a02108851088210781b01845030210881a01845030230485203001043ed0881a02018088510a0450a0010a1e9
|8=>0xa0010d80d08819030320882103021088210a0180a0190885100021030330882103021030510781b018450b81b088010c8470a0010201b08851088850a01803001088510a001040010a01a018450084503021030450a003030010a0230a0210881a0605108821030010a00100413018520a05d088010301504001030030885200803030210680f0a01902001088510a1eb030030302103051089290a01a08851
|9=>0x8851018ab030230b821088010a021088210d823088190a01801845030030a023068010a0193d021030030a0190a0210885108852030510200f0885110821030500a023088010d801088190185108819000890305201816040010a01a08851018450a0190c8210a001018850a01801814040010a019030510a00308a2d0a003088190a0010200d08851068030a019068470a0190a02108801018470a0190a045
|10=>0xa02304001030230a021018450181a01851018470a0010a0a903023088850a0180a019018870a018088190885101a2d0a0030885103051088870a01803053088190a0190a01b088010a05f088010881901821068450a01903021018450a01908c110185201847030210a019089e9030030b821088010680d0a019030210a0010a01900021088210a023088510a01908851030510184508801020230885103003
|11=>0xa0180a0190880101821018450a01a088510881a
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x94c00008c8000084800007c80000000000000000000001c30000000064c00000000000000000060400000000000000153000000000001230000000000000003cc0d20000000000000000000a30244000000000002040000000000000006200000000000000000004200880000008000
|5,1=>0x10cc412000000010040000fc43b40e483540cc80000c0c00000002d300002c10000000000000000000000a10000000000000000000000000
|6,0=>0x25cc000000000025840000000942244c00023c88e123088b100008a10000882218885121048131fc800000007c31e4c7721d840001d447321c480001b8c6c21a4c00019c8652188c00018085e217085b1000059215c854314c451214044f1000000013484c1128848211880000000000
|6,1=>0x3ac80003a48e810000e620000e420000e31380cdf13784dc23688d823588d4234880003408cf1330cca2000000032080000000c5330c8c122fc8bd2000000000000002ec8b832d4c0000000b412c880002c080000000ad32ac80002a48a722948a32280c9e227080002688000
|6,2=>0x4ecd3924dc93524cc80004c0d2d300012b24a840004a09262000125148c9203478800000011c2464d1810001162000114244c512144090d3428c0004208000418800040cc0000000000000101240040000000ff13f48fa33e440003e0400000000000000f530000f323c48ef20000ed2
|6,3=>0x6388000000000000018c200018a262458720001861614583260480005fc80005f857c25e4d7725d0c0005c880005c4400000016f200016c35a8800059cc000000164358c400058495f2574800056c9592558d54254894f300014d200014c1000000052c54925205462510942250093e2
|6,4=>0x1b836d4db3200000006c480006bc9ac36a89a736985a42684d9f267499b2660d96200000006544000650593100019126404000
|7,0=>0x8e4a3728d4a3328c4a2f28b4a2b28a4a272894a232884a1f2874a1b2864a172854a132844a0f2834a0b2824a072814a0328049ff27f49fb27e49f727d49f327c49ef27b49eb27a49e727949e327849df27749db27649d727549d327449cf27349cb27249c727149c327049bf26f49bb2
|7,1=>0xac86b02ab8aac2aa8aa82a98aa51a8caa12a7ca9d2a6ca9a1a60a962a546932a44a8f2a34a8c1a28a882a1c6852a0ca8129fca7d29eca7929dca7529cca7129bca6e19b0a6a29a0a662990a622980a5e2970a5a2960a562950a52294464f2934a4b2924a472914a432904a3f28f4a3b2
|7,2=>0xad4ab32
|8,0=>0xb1c6c61b146c41b0c6c210002c11b006bf1af86bd1af06bb1ae86b91ae06b71
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0xb2800054800024600010b000084000040800020200010000006400003100001840000c000004100002000000ca0000530000250000108000082000040000011800008000003400001200000800000280000120000080000028000008000002000000
|1=>0x825000412400208400100a00080100040000014000008090004000001f6c000fa60006db00032d8001800000bb60005d30002bf800136c00090600045b00022500010080008000003900000fd800070400034000019b0000cd0000648000300000167
|2=>0x28e4801456c00a0a600405200201d001002000608600214300109000084080042000020c3001040000808000400a0020030010010008004002fb6001608000aed800556c0029b600130a000945000476c002334001198000861000430400210000105b
|3=>0x20080010016c080014040002018001006877c0343ae01917900c42d804a51c023206011173008881804254c0210000104000081a9804000402000000a55b004aec8024424011412008a030042ed802136c01020200800b003822801600c00a4060051d3
|4=>0x82afd84151ec20a3a610447708086104015cc200ac210004408001004000042000000c10420428ed82085941001900800c0040020014640c0a22060501530228e981145cc08a286041901020a6d810482808240404110202080501040000804a6040202
|5=>0x3028e9980454cb021b25800db2c0069940436c9820a64931f52428e9920034c8243ae320412180aa9885036c4262a6213053109481884a14c4242b62101db1080e988110404080242015db1008ed880436c4020b62004121002080800608400116200002
|6=>0x58015ce400006e120d3660069b000b4d8001a68c00424094eba04874d00500e8002c2320aa998d016cc600b661555330aa39985516cc288a6612053
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x202000018003222022802000200000200180000000000000900000000000000060002000200020000000000000200000200000000001200000000110000000e0000000002020000000000021200000018000000000300000000001302000200
|6,0=>0x100021600520002006d457f0402024c3b2a520002522b0100000100004415070202000000000c0d2453003a98370c0000310c004e6e5a41500202000c0005000039250000011d0002010118005200020c1851230100003d61523a008f0c19003c0c2d00561973001f0c5218000c9644955255970000023a020202000000
|6,1=>0xc000000251b00a018020052120202000c00950c9a021e000c001800000200af02000e0000361800027b0200071a8602023b00a000180000570c65840101020806a00c4f0700a122000682000b0200121306010000025c02000100027c290206a2000c000500ae0000000002120000710764180012000000000800020c020041
|6,2=>0x30220200000200024502990a14063b0870350200008000122100081200
|7,0=>0x804686bf834a47aa4360d181ad15c72f9033c9c126a476624083d08c0f27cb756fa73ebb6c1f8d48c14b59c8a993ab83a592a89aa35f8b15c3173c589eb9b4727731203878c6cdb67e4b15b8a6689b421c88bdb3cf7a3f79c2cc4a6a3489602eb063917dba405bce5eb2bcb249ca856b4b544b69268ec566ac9d6787942cbeb1
|7,1=>0x314d
|8,0=>0x4b9fcdd2c14b408a2e5db53174c0b2c49cb7
|9,0=>0x10
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_115 7 roots_115 ops++addP pm 2 dom_42 4 roots_42 ops++addP pm 3 dom_121 6 roots_121 ops++addP pm 4 dom_107 7 roots_107 ops++addP pm 5 dom_74 4 roots_74 ops++addP pm 6 dom_59 7 roots_59 ops++addP pm 7 dom_57 5 roots_57 ops++addP pm 8 dom_90 5 roots_90 ops++addP pm 9 dom_113 4 roots_113 ops++addP pm 10 dom_105 5 roots_105 ops++addP pm 11 dom_114 4 roots_114 ops++addP pm 12 dom_91 6 roots_91 ops++addP pm 13 dzo_42_16 4 roots_42 ops++addP pm 14 dom_75 5 roots_75 ops++addP pm 15 dom_120 4 roots_120 ops++addP pm 16 dzo_106_16 5 roots_106 ops++addP pm 17 dom_99 4 roots_99 ops++addP pm 18 dom_83 4 roots_83 ops++addP pm 19 dom_27 4 roots_27 ops++addP pm 20 dom_41 4 roots_41 ops++addP pm 21 dzo_107_16 6 roots_107 ops++addP pm 22 dzo_43_16 5 roots_43 ops++addP pm 23 dom_51 4 roots_51 ops++addP pm 24 dom_106 5 roots_106 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_42_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_106_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_107_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_43_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_106 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 7 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 11 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 96 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 96 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 256 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_256 : ∀ i, 256 ≤ i → i < 286 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 30 256 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 286 → Z 6 i = true := (range_split z6_0 (range_split z6_128 z6_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 130 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 130 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 18 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 18 0 = true)
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
def dzo_121_4:=0x30303030303030303030303030303030
def gzo_121_4:=0x30303030303030303030302030302000
def gsh_121_4:=0x3030303030303030303030203030200
theorem lowS_zo_121_4_41:Lower true dzo_121_4 roots_121 gzo_121_4 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_4) [(dom_121,4)] (by decide +kernel) (lower_slice_b (T:=gsh_121_4) [(0x3030000030300000303000003030000,0,16),(0x3030303030303030000000000000000,0,64)] (by decide +kernel) lowS_41)
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(4,20),(4,68),(5,13),(5,21),(5,37),(5,69),(8,9),(8,40),(8,72),(12,13),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,56),(24,88),(32,33),(32,40),(36,37),(36,44),(36,52),(36,100),(48,49),(48,52),(48,56),(48,112),(64,68),(64,72),(64,80),(65,69),(65,73),(65,81),(65,97),(96,97),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccc00000000cccccccc000000033330000333300003333000033330000cc00cc00cc00cc00cc00cc00cc00cc0303030303030303030303030303030308888888888888888888888888888888b3333333333333330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>6
|_,_=>0
def wAt:=mkWire dB 6 126 0x3fffffffffffffffffffffffffffffff
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
addP pm 0 dom_124 7 roots_124 ops++addP pm 1 dom_61 7 roots_61 ops++addP pm 2 dom_117 7 roots_117 ops++addP pm 3 dom_109 7 roots_109 ops++addP pm 4 dom_121 6 roots_121 ops++addP pm 5 dzo_121_4 6 roots_121 ops++addP pm 6 dom_93 6 roots_93 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_121_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_93 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_124 7 s (0,roots_124.map (·&&&dom_124)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_124 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_125==dom_125)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_125 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_84_32:=0x110011000000000011001100000000
def gzo_84_32:=0x110010000000000010000000000000
def gsh_84_32:=0x1100100000000000100000
theorem lowS_zo_84_32_84:Lower true dzo_84_32 roots_84 gzo_84_32 4:=lower_iso_b (d1:=dom_84) (r1:=roots_84) (T1:=gsh_84_32) [(dom_84,32)] (by decide +kernel) (lower_slice_b (T:=gsh_84_32) [] (by decide +kernel) lowS_84)
def dzo_58_4:=0x5050505050505050
def gzo_58_4:=0x5050504050504000
def gsh_58_4:=0x505050405050400
theorem lowS_zo_58_4_42:Lower true dzo_58_4 roots_58 gzo_58_4 5:=lower_iso_b (d1:=dom_58) (r1:=roots_58) (T1:=gsh_58_4) [(dom_58,4)] (by decide +kernel) (lower_slice_b (T:=gsh_58_4) [(0x505000005050000,0,16)] (by decide +kernel) lowS_42)
def dzo_46_16:=0x5555000055550000
def gzo_46_16:=0x5554000054500000
def gsh_46_16:=0x555400005450
theorem lowS_zo_46_16_42:Lower true dzo_46_16 roots_46 gzo_46_16 5:=lower_iso_b (d1:=dom_46) (r1:=roots_46) (T1:=gsh_46_16) [(dom_46,16)] (by decide +kernel) (lower_slice_b (T:=gsh_46_16) [(0x505000005050,0,4)] (by decide +kernel) lowS_42)
def dzo_110_16:=0x55550000555500005555000055550000
def gzo_110_16:=0x55550000555500005554000054500000
def gsh_110_16:=0x5555000055550000555400005450
theorem lowS_zo_110_16_42:Lower true dzo_110_16 roots_110 gzo_110_16 6:=lower_iso_b (d1:=dom_110) (r1:=roots_110) (T1:=gsh_110_16) [(dom_110,16)] (by decide +kernel) (lower_slice_b (T:=gsh_110_16) [(0x5050000050500000505000005050,0,4),(0x5555000055550000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_92_32:=0x11111111000000001111111100000000
def gzo_92_32:=0x11111110000000001110110000000000
def gsh_92_32:=0x111111100000000011101100
theorem lowS_zo_92_32_84:Lower true dzo_92_32 roots_92 gzo_92_32 5:=lower_iso_b (d1:=dom_92) (r1:=roots_92) (T1:=gsh_92_32) [(dom_92,32)] (by decide +kernel) (lower_slice_b (T:=gsh_92_32) [(0x110011000000000011001100,0,8)] (by decide +kernel) lowS_84)
def dzo_94_32:=0x55555555000000005555555500000000
def gzo_94_32:=0x55555554000000005554554400000000
def gsh_94_32:=0x555555540000000055545544
theorem lowS_zo_94_32_84:Lower true dzo_94_32 roots_94 gzo_94_32 6:=lower_iso_b (d1:=dom_94) (r1:=roots_94) (T1:=gsh_94_32) [(dom_94,32)] (by decide +kernel) (lower_slice_b (T:=gsh_94_32) [(0x444444440000000044444444,0,2),(0x550055000000000055005500,0,8)] (by decide +kernel) lowS_84)
def dzo_106_4:=0x5050000050500000505000005050
def gzo_106_4:=0x5050000050500000504000004000
def gsh_106_4:=0x505000005050000050400000400
theorem lowS_zo_106_4_42:Lower true dzo_106_4 roots_106 gzo_106_4 5:=lower_iso_b (d1:=dom_106) (r1:=roots_106) (T1:=gsh_106_4) [(dom_106,4)] (by decide +kernel) (lower_slice_b (T:=gsh_106_4) [(0x505000005050000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_122_4:=0x50505050505050505050505050505050
def gzo_122_4:=0x50505050505050505050504050504000
def gsh_122_4:=0x5050505050505050505050405050400
theorem lowS_zo_122_4_42:Lower true dzo_122_4 roots_122 gzo_122_4 6:=lower_iso_b (d1:=dom_122) (r1:=roots_122) (T1:=gsh_122_4) [(dom_122,4)] (by decide +kernel) (lower_slice_b (T:=gsh_122_4) [(0x5050000050500000505000005050000,0,16),(0x5050505050505050000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_86_32:=0x550055000000000055005500000000
def gzo_86_32:=0x550054000000000054004400000000
def gsh_86_32:=0x5500540000000000540044
theorem lowS_zo_86_32_84:Lower true dzo_86_32 roots_86 gzo_86_32 5:=lower_iso_b (d1:=dom_86) (r1:=roots_86) (T1:=gsh_86_32) [(dom_86,32)] (by decide +kernel) (lower_slice_b (T:=gsh_86_32) [(0x4400440000000000440044,0,2)] (by decide +kernel) lowS_84)
namespace S_126
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(4,20),(4,68),(6,14),(6,22),(6,38),(6,70),(8,10),(8,40),(8,72),(12,14),(12,28),(12,44),(12,76),(16,20),(16,80),(18,22),(18,26),(18,50),(18,82),(24,26),(24,28),(24,56),(24,88),(32,34),(32,40),(36,38),(36,44),(36,52),(36,100),(48,50),(48,52),(48,56),(48,112),(64,66),(64,68),(64,72),(64,80),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_126.map (·&&&dom_126)
def gM:=goal_126&&&dom_126
def NN:Nat→Nat
|5=>4
|6=>15
|7=>24
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xdc077999713c8a43b4e8
|6,0=>0xedae39f5aa9c5357e95e714266144d4b63f46bd03fd8834f71328be30db8303f02fb170c515
|7,0=>0xe45c6e09eed5137d4fb5b4f4aa795aa646996a207fe8e7083f6dfc860d3b5e57f5b94f541f05374b4d5b6387d5357e229cd2239901f4ab04e7e00e68
|8,0=>0xe29658bf857e9954457d38cc628a5525b0e00334
|9,0=>0x464f4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa0a0a0a0a0a0a0a000000000000000155555555555555555554000155540002aa22aa22aa22aa22aa22aa22aa22aa205050505050505050505000005050000a0a0a0a0a0a0a0a0a0a00000a0a00001555555540000000155555554000000008888888888888888880088008800880005500550055005500440044004400440000aaaa0000aaaa0000a0a00000a0a000000001551155100000000155115512aaa80002aaa80002aaa80002aaa800055005500550055005500550055005500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a1111111111111111111111111111111100002aaaaaa22aaa800000002aa22aa255555555555555550000000000000000
|0,1=>0xaaa8aaa8aaa8aaa8aaa8aaa8aaa8aaa955555555555555555555555400000002aaaaaaa80002aaaaaaaaaaa8000000011111111111111110000000000000000aa22aa22aa22aa22aa00aa00aa00aa0000440044004400440000000000000002aaaaaaaaaaaaaaa800000002aa22aa255555555555555555544554455445544aaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a155555555555555555401540154015402aaaa8282aaaa8282aaaa8282aaaa828004500450045004500440044004400440000aaaa0000aaaa000000000000000111115555111155551111111111111112aaaaaaaaaaaaaaaa22222222222222255455545554555455544554455445544
|0,2=>0x550055005500550000000000000000aaaaaaaa00aa00aaaaaaaaaa000000015555111155551111555511115555111002a8022002a8022002a8022002a802255005555550055555500550055005500
|_,_=>0
def sP:Nat→Nat
|0=>0x4ca14d58344a1560c22001440c26402853560d100a14d10b0802856030880051170c21802855834422151440c218028510309400a14d10348028534344800a1501030801440c21803ca14d1023001442c21802850c92001030871801440c2040
|1=>0x1034422856040d10802851034422008c51030802851030a100a1581030802855840c270a1440c22002858040c200a15f1030802855840d108510308601e1440d10802840c21c07451030802853560c200a15b10308028510308068a14d103080
|2=>0xa1440c200a14d10308028510308070a1440d10802851170c200a5451030802851030803ca8851030807851030802855840d10802853445c308029514d10308028510b08078510309c785
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x9303180cc006
|6,0=>0x1e58e4e6c632b979caee50724b909c76e34716b899c3ee187
|7,0=>0x8f445a21d10868133f19e90ec873337ddb0ed17653b0dd78eb5757b2a1d44c9c64aba39d0ee7f8
|8,0=>0xab3d3de90f4179d3ccde58f266
|9,0=>0x15d6
|_,_=>0
def wAt:=mkWire dB 37 127 0x7fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x142444508044010808446080444d1408d0d10244010804a361024201280455e0c04a4d140821110044710808d02102440914082010844401444c2011004409102440108044090ce050111144460804a3610244460804a36102424d14084460804d3d10243020c08a36102433a1024501
|1=>0x40908082010c0450d0c08509280440108044090c04409143433814042022804201280444508044460804a91100a213
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x80ce99c132658c999121e4348000b212418c19803
|7,0=>0xa253ca694b29251ca29432824fc9e93b2724dc9a9332624bc9692b25249c929232
|8,0=>0xb43646c0d71ac3546a0d31
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x4e7a094740ebf81d1902000035fc04800075d00c22017ec02cd8057f00afa015ec028c8049f00200003fc007e8009b00106001f4000f8001e000340004400060000b000100000c000100000
|1=>0x48739902228f47d0ebf9a53d30322294ec2ebf82759
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0xd11b2572cf14f0031c2646
|7,0=>0x2639d885d30876058e49e88a71a7e6394510
|8,0=>0x5534e4a1e825
|9,0=>0x11
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_94 8 roots_94 ops++addP pm 1 dzo_84_32 4 roots_84 ops++addP pm 2 dom_62 6 roots_62 ops++addP pm 3 dom_118 7 roots_118 ops++addP pm 4 dom_124 7 roots_124 ops++addP pm 5 dzo_58_4 5 roots_58 ops++addP pm 6 dzo_46_16 5 roots_46 ops++addP pm 7 dom_84 4 roots_84 ops++addP pm 8 dom_122 7 roots_122 ops++addP pm 9 dzo_110_16 6 roots_110 ops++addP pm 10 dom_110 7 roots_110 ops++addP pm 11 dzo_92_32 5 roots_92 ops++addP pm 12 dzo_94_32 6 roots_94 ops++addP pm 13 dzo_106_4 5 roots_106 ops++addP pm 14 dom_92 5 roots_92 ops++addP pm 15 dzo_122_4 6 roots_122 ops++addP pm 16 dom_42 4 roots_42 ops++addP pm 17 dzo_86_32 5 roots_86 ops++addP pm 18 dom_106 5 roots_106 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_126 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_84_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_58_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_46_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_110_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_92_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_94_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_106_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_122_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_86_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_106 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_94 8 s (0,roots_94.map (·&&&dom_94)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_126 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_94 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_126==dom_126)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_126 gM v ys):RunD true dom_126 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_126 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 15 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_126 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_slice_b [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,16,17)] (by decide +kernel) lowS_214
theorem lowS_221:Lower true dom_221 roots_221 goal_221 9:=lower_slice_b [(0x22222222000000002222222200000000222222220000000022222222,8,9)] (by decide +kernel) lowS_220
namespace S_222
def pG:List (Nat×Nat):=[(2,10),(2,66),(2,130),(4,20),(4,68),(4,132),(6,14),(6,22),(6,70),(6,134),(8,10),(8,72),(12,14),(12,28),(12,76),(12,140),(16,20),(16,80),(16,144),(18,22),(18,26),(18,82),(18,146),(24,26),(24,28),(24,88),(24,152),(64,66),(64,68),(64,72),(64,80),(64,192),(128,130),(128,132),(128,144),(128,192),(136,138),(136,140),(136,152),(136,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_222.map (·&&&dom_222)
def gM:=goal_222&&&dom_222
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x6eb8c
|7,0=>0x98a795290d515fb4bec715d81
|8,0=>0x68c4462fd6
|9,0=>0xbad5e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x14141414000000001414000000000000141414140000000014140002aaaaaaa800000002aaaa828000000002aaaaaaa800000002aaaa82850505050000000005050505000000000505050500000000050505050aaaa000000000000aaaa000000000000aaaa000000000000aaaa000155555554000000000000000000000001555555540000000000000002aaaa828000000002aaaa828000000002aaaa828000000002aaaa82855555555000000005555000000000000555555550000000055550000aa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa0155555554000000014141414000000001555555540000000141414142222222200000000222222220000000022222222000000002222222255555555000000005555555500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x7381605738160732816047328107381a609473816097381605438160543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d4835c67
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 223 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1e1865d98661276611765c98661d76619875d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x1ffec6fe7eff5f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x63784
|8,0=>0x25
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_220 8 roots_220 ops++addP pm 1 dom_94 8 roots_94 ops++addP pm 2 dom_214 8 roots_214 ops++addP pm 3 dom_218 7 roots_218 ops++addP pm 4 dom_206 7 roots_206 ops++addP pm 5 dom_158 7 roots_158 ops++addP pm 6 dom_202 5 roots_202 ops++addP pm 7 dom_142 4 roots_142 ops++addP pm 8 dom_154 4 roots_154 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_222 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_154 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_220 8 s (0,roots_220.map (·&&&dom_220)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_222 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_220 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_222==dom_222)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_222 gM v ys):RunD true dom_222 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_222 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_222 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_234_1:=0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a
def gzo_234_1:=0xa0a00000a0a00000a0a00000a0800000a0a00000a0800000a0a00000a00
def gsh_234_1:=0x50500000505000005050000050400000505000005040000050500000500
theorem lowS_zo_234_1_194:Lower true dzo_234_1 roots_234 gzo_234_1 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_1) [(dom_234,1)] (by decide +kernel) (lower_slice_b (T:=gsh_234_1) [(0x50000000500000005000000050000000500000005000000050000000500,0,8),(0x50500000000000005050000000000000505000000000000050500000000,0,32)] (by decide +kernel) lowS_194)
namespace S_235
def pG:List (Nat×Nat):=[(1,9),(1,33),(2,10),(2,34),(2,66),(2,130),(3,11),(3,35),(3,67),(3,131),(8,9),(8,10),(8,40),(8,72),(32,33),(32,34),(32,40),(32,160),(64,66),(64,72),(64,192),(65,67),(65,73),(65,97),(65,193),(96,97),(96,98),(96,104),(96,224),(128,130),(128,160),(128,192),(129,131),(129,137),(129,161),(129,193),(136,137),(136,138),(136,168),(136,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_235.map (·&&&dom_235)
def gM:=goal_235&&&dom_235
def NN:Nat→Nat
|7=>2
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xc3ffd96981
|8,0=>0xfffda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xe0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0ea0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0af0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f00c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c20200000202000002020000020200000202000002020000020200000202f0f00000f0f000000000000000000000f0f00000f0f0000000000000000f0f00000f0f00000f0f00000f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c788b3b22c688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xcc06
|8,0=>0xc6
|_,_=>0
def wAt:=mkWire dB 8 236 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x797a
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x441
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 6
def pmP:Nat→Nat
|0=>0xfefcf80
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>6
|8,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_227 7 roots_227 ops++addP pm 1 dom_171 7 roots_171 ops++addP pm 2 dom_107 7 roots_107 ops++addP pm 3 dom_203 7 roots_203 ops++addP pm 4 dom_234 6 roots_234 ops++addP pm 5 dom_233 6 roots_233 ops++addP pm 6 dzo_234_1 6 roots_234 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_235 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_234_1_194 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_227 7 s (0,roots_227.map (·&&&dom_227)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_235 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_227 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_235==dom_235)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_235 gM v ys):RunD true dom_235 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_235 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_235 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_235 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_235 roots_235 goal_235 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_235
theorem lowS_235:Lower true dom_235 roots_235 goal_235 9:=S_235.noCircuit
namespace S_249
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(8,9),(8,40),(8,72),(16,17),(16,80),(16,144),(24,25),(24,56),(24,88),(24,152),(32,33),(32,40),(32,160),(48,49),(48,56),(48,112),(48,176),(64,72),(64,80),(64,192),(65,73),(65,81),(65,97),(65,193),(96,97),(96,104),(96,112),(96,224),(128,144),(128,160),(128,192),(129,137),(129,145),(129,161),(129,193),(136,137),(136,152),(136,168),(136,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_249.map (·&&&dom_249)
def gM:=goal_249&&&dom_249
def NN:Nat→Nat
|7=>3
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x7ed4d2c020263cd
|8,0=>0x2c020
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000000000c0c0c0c0000000303030300000000030303030000000003030303000000000303030300000000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c000303030303030303030303030303030303000300030003000300030003000300c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c0202020202020202020202020202020202020202020202020202020202020202c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c000000000000000303030303030303030303030303030300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x35688fab446ad11ac688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0x35cec07
|8,0=>0x146
|_,_=>0
def wAt:=mkWire dB 8 250 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc161
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x11001
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 6
def pmP:Nat→Nat
|0=>0xfff7df3ff01f000
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x8b
|8,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_248 6 roots_248 ops++addP pm 1 dom_185 6 roots_185 ops++addP pm 2 dom_241 6 roots_241 ops++addP pm 3 dom_233 6 roots_233 ops++addP pm 4 dom_217 6 roots_217 ops++addP pm 5 dom_216 5 roots_216 ops++addP pm 6 dom_121 6 roots_121 ops++addP pm 7 dom_209 5 roots_209 ops++addP pm 8 dom_57 5 roots_57 ops++addP pm 9 dom_105 5 roots_105 ops++addP pm 10 dom_240 5 roots_240 ops++addP pm 11 dom_169 5 roots_169 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_249 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_169 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_248 6 s (0,roots_248.map (·&&&dom_248)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_249 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_248 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_249==dom_249)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_249 gM v ys):RunD true dom_249 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_249 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_249 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_249 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_249 roots_249 goal_249 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_249
theorem lowS_249:Lower true dom_249 roots_249 goal_249 9:=S_249.noCircuit
def isoMvS_159:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_iso_b isoMvS_159 (by decide +kernel) lowS_119
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 10:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_123
def isoMvS_189:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 9:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_125
def isoMvS_190:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 10:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_126
def isoMvS_207:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=lower_iso_b isoMvS_207 (by decide +kernel) lowS_111
def isoMvS_219:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_219:Lower true dom_219 roots_219 goal_219 10:=lower_iso_b isoMvS_219 (by decide +kernel) lowS_123
def isoMvS_237:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 9:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_125
def isoMvS_238:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_235
def isoMvS_243:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 10:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_123
def isoMvS_245:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 9:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_221
def isoMvS_246:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_222
def isoMvS_250:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 9:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_235
def isoMvS_252:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_221
def dzo_47_16:=0xffff0000ffff0000
def gzo_47_16:=0xfffe0000fefa0000
def gsh_47_16:=0xfffe0000fefa
theorem lowS_zo_47_16_42:Lower true dzo_47_16 roots_47 gzo_47_16 6:=lower_iso_b (d1:=dom_47) (r1:=roots_47) (T1:=gsh_47_16) [(dom_47,16)] (by decide +kernel) (lower_slice_b (T:=gsh_47_16) [(0xaaaa0000aaaa,0,1),(0xf0f00000f0f0,0,4)] (by decide +kernel) lowS_42)
def dzo_85_32:=0x330033000000000033003300000000
def gzo_85_32:=0x330032000000000032002200000000
def gsh_85_32:=0x3300320000000000320022
theorem lowS_zo_85_32_84:Lower true dzo_85_32 roots_85 gzo_85_32 5:=lower_iso_b (d1:=dom_85) (r1:=roots_85) (T1:=gsh_85_32) [(dom_85,32)] (by decide +kernel) (lower_slice_b (T:=gsh_85_32) [(0x2200220000000000220022,0,1)] (by decide +kernel) lowS_84)
def dzo_93_32:=0x33333333000000003333333300000000
def gzo_93_32:=0x33333332000000003332332200000000
def gsh_93_32:=0x333333320000000033323322
theorem lowS_zo_93_32_84:Lower true dzo_93_32 roots_93 gzo_93_32 6:=lower_iso_b (d1:=dom_93) (r1:=roots_93) (T1:=gsh_93_32) [(dom_93,32)] (by decide +kernel) (lower_slice_b (T:=gsh_93_32) [(0x222222220000000022222222,0,1),(0x330033000000000033003300,0,8)] (by decide +kernel) lowS_84)
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000ffff0000fffe0000fefa0000
def gsh_111_16:=0xffff0000ffff0000fffe0000fefa
theorem lowS_zo_111_16_42:Lower true dzo_111_16 roots_111 gzo_111_16 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xaaaa0000aaaa0000aaaa0000aaaa,0,1),(0xf0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff0000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_95_32:=0xffffffff00000000ffffffff00000000
def gzo_95_32:=0xfffffffe00000000fffeffee00000000
def gsh_95_32:=0xfffffffe00000000fffeffee
theorem lowS_zo_95_32_84:Lower true dzo_95_32 roots_95 gzo_95_32 7:=lower_iso_b (d1:=dom_95) (r1:=roots_95) (T1:=gsh_95_32) [(dom_95,32)] (by decide +kernel) (lower_slice_b (T:=gsh_95_32) [(0xaaaaaaaa00000000aaaaaaaa,0,1),(0xcccccccc00000000cccccccc,0,2),(0xff00ff0000000000ff00ff00,0,8)] (by decide +kernel) lowS_84)
def dzo_59_4:=0xf0f0f0f0f0f0f0f0
def gzo_59_4:=0xf0f0f0e0f0f0e000
def gsh_59_4:=0xf0f0f0e0f0f0e00
theorem lowS_zo_59_4_43:Lower true dzo_59_4 roots_59 gzo_59_4 6:=lower_iso_b (d1:=dom_59) (r1:=roots_59) (T1:=gsh_59_4) [(dom_59,4)] (by decide +kernel) (lower_slice_b (T:=gsh_59_4) [(0xf0f00000f0f0000,0,16)] (by decide +kernel) lowS_43)
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(4,20),(4,68),(5,13),(5,21),(5,37),(5,69),(6,14),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,10),(8,40),(8,72),(12,13),(12,14),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(18,19),(18,22),(18,26),(18,50),(18,82),(24,25),(24,26),(24,28),(24,56),(24,88),(32,33),(32,34),(32,40),(36,37),(36,38),(36,44),(36,52),(36,100),(48,49),(48,50),(48,52),(48,56),(48,112),(64,66),(64,68),(64,72),(64,80),(65,67),(65,69),(65,73),(65,81),(65,97),(96,97),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|5=>1
|6=>12
|7=>68
|8=>151
|9=>98
|10=>14
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x11811
|6,0=>0xedd64e684cd8c55d0d6496da6772f776b586d7374b2483e7673938e099d8
|7,0=>0xff331fef70f90e3f44c4f29d0f1779e9734e6871e47d4e0eadde1abd95edd5f95d4865d1cb1c5243c1a3bbe9e5b8930b7afdb2b9da6efaa54c8a2cee9f7bb9ae3b9809b95e29944e793bff91b6b9124290a818ef768e7aa881918662a82b2b803eb7f4777e69e7dc0a5b8375b7b15a57b556c3542e3519ad47f15417693e1a43d9883bc1d2e5ab2bebd2609d219a61d1651980718d7918d0b0ef9d0c8c008af502de801dac0162b0142a
|8,0=>0xd774dd7144d4e28d3f38d2f42d1fb8d1906cdbbacdb67cd37ecc039cb051c819bc7447c73a5c5e73c2380beb18b9182b9000b4ed5b4b84b3f30acb06ac323aac99aa570a9331a8787a5717a30c6a21ba9c7119b7479b10e96ae79627693785935c89261091e5e902c68ee308ed188d8bb8652284c87842a583fc48360682dba80dd9757bf7571972ab37195c6fa0c6f7d56f6266eb126e9426c7936c17b6a316695ff65e9b64eb06430d6410f63c4e60864602275e6215df415c4055a631575e45734455b4654be754a42539425118350b0a50a9c4adfd485b2474d746afc44651418123ec2d3b9cd39f30395ed394e235f7b353d03443d30f192ec2d2eac02e02c2a9002a1aa29f9627744259ad23ece214141fd70194981915818ff916c9e16a7215dd514fea14fb6141e61281911db20ad6a08e5607a9404b790353d00e28
|8,1=>0xff2e2fd6a5fc7fbfc704fa09df8573f7aaaf5e16f5dd7f465cf3fb7efbbfebbdae482fe377ce1425dec8bdd798dcc01dc480d989ad8f7ed83f8
|9,0=>0xfe357fbb43fb94df673becff9eaa72ea352e20b7da8e5d6882d36d5d07fbcec71ca7b0c9aedc957ac865cc4208c325ac2985beff6be5d1bdd15bc06aba0a2b82cbb5882b3405b273db0c01b0480afc7da8ed5a8a85a8201a7f38a7e31a3af5a36faa21fa9f5f99dff69ba129aaee9850095391916238dc818d0008b9c88418680b068056c7e247776fa6d9c26d9546aa6d6a3f769d196778562a6f61f9f615095ff4c5e22c5808a574565680a4c25446fad46f5d46698445313d5ff3d36c3b2ce3a679348ea348752d9422d77a292942689625ab42258c1bda51a4a0156f1113e4107890ea430d80a0c80709697093d004d130398a
|10,0=>0xf90dcf69ed925d18d3bf83c7d761fa715436c3bf581865456c5254f43a5320b1905c14
|11,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff000000ff00000000ff00ff0033333333333333333333333333003300ffffff00ffffff000000000000000000ccccccccccccccccccccccccccccccccffffffffffffffffffffff00ffffff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffff0000000000000000ffccffccffccffccffccffccffccffccffffffffffffffffcccccccccccccccc0f0f0f0f0f0f0f0f0f0f0f000f0f0f00ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000033000000333333333333003300
|0,1=>0xffff0000ffffff0000000000ffffffff00000000ff00ff0000ff00ff00cc00cc00ff00ff00cc00cc333333333300330033333333330033000f0f03030f0f03030f0f00000f0f00000f0f03030f0f03030f0f03000f0f0300ffffff00ffffff00ffffff00ffffff00ffffffffffffffffffffffffff00ff00ffffffccffffffcccccccccccccccccc000000ff000000ffffffffffff00ff0000000000000000003333330033333300cccccccccccccccccccccccccc00cc00ffffffffffffffffffff0000ffff0000ffffffffff00ff00ffffffffff00ff00ffffffffccccccccffffffffcccccccc0f0f0f0f0f0f0f0f0f0f00000f0f0000
|0,2=>0xcccccccccccccccccccccccccccccc00ffffff00ffffff00ffffff0000000000ffff3333ffff3333ffff3300ffff33000000000000000000ffff3300ffff33003333333333333333333333333333330033333333330033333333333333003300ffffffffffffffffffffffff00000000ffff0000ffff00ff00000000000000000000ffff0000ff000000ffff0000ff00ffffaaaaffffaaffaaaaaaaaaaaaaaaa00ff00ff00ff00ff00ff00ff00000000ffffffffffffffffffffffccffffffccffffffffffffffffffccffccffccffcc3333333333333333333333003333330033333333333333333300330033003300ffff0000ffffffffffff0000ffffff00
|0,3=>0xff000000ffff00ff00ff00ff00ffff3333ffff3333ffff0000ffff00003333333333333333000000000000000055555555555555555555555555555500ffffffffffccffccffffffffffccffcc0000000000000000ffffffccffffffccffffccccffffccccffffccccffffcccc0000000000000000ffffff00ffffff00ffffffffffffffffffffccccffffcccc0f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0cffffffff0000ffffffffffff0000ff0000ff00ff000000ff00ff00ff000000000000ffff0000ffff0000ff000000ff000000000000000000ffffffffff00ff000f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0c0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00
|0,4=>0xff00ffffff00ffffff00ffffff00ff00ffffffffffff00000000000000000000ffffffffffffff00ff00ff00ff00ff00000033330000333300003300000033000000ffff0000ffff000000000000000000000000ff00ffff00000000ff00ff00ccccffffccccffffccccffccccccffccffffffffffff0000ffffffffffff0000000000000000000000ff00ff00ff000033333333333333333333000033330000fffffff0fffffff0f0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0cf0f0f0f0f0f0f0f0f0f0fffff0f0fcfcf0f0f0f0f0f0f0f0f0f0fffff0f0fff0ff00ffffff00ffffff00ff00ff00ff00ffffffccffffffccffffffccffffffcc
|0,5=>0xffffffffff00ff000000000000000000ffffffffffffff00ffff0000ffff000000000000000000000000ffff0000ff000000ffff0000ffff0000ffff0000ff00000000ff000000ff000000ff000000000000000000ff00ff0000000000000000aaaaaaaaaaffaaffaaaaaaaaaaaaaaaa0000000000ff00ff0000000000ff0000ffffffff0000ffffffffffff00000000ffffffffff00ffffffffffffff00ff000000ffff0000ffff0000ffcc0000ffccffff0000ffff0000ffffffffffffff00ffffffffffffffffffffffffffff00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000ffffffffffffff00ffffffff000000000000ffff0000ffff0000ffff00000000
|0,6=>0xaaaaaaaaaaaaffffaaaaaaaaaaaaaaaaffffffffff00ff00ffff0000ff000000ffff0000ff000000ffffffffff00ff003333333333333333333333330000000000003333000033330000333300000000ffffffff33333333ffffffff33330000000000cc000000cccccccccccccccccc0000ffff0000cccc0000ffff0000ccccffffffffffffffff0000ffff0000cccc000000ff000000ff0000000000000000ffffffff000000ffffffffff000000003333330033333300333333003333330000000000ffffffff00000000ffff0000ff00ff00ffffffffff00ff00ffffff0000000000000000000000ffff0000cccc000000000000000000000000ffffff00
|0,7=>0xff00ff00ff00ff00ff000000ff0000ffffffff00ff00ffffffffff00ff0000ffffffffffffff00ffffffffffffff005555555555555500555555555555550000000000ffffffff0000000000000000aaaaaaaaffffffffaaaaaaaaaaaaaaaaffffffffffff0000ff00ff00ff000000ff33ff33ff33ff33ff33ff00ff33ff00ffffffffffffffff3333330033333300ffffffffffffffff0000ffff0000ff00ffffffffffffffffffffffffffffcccc0000000000000000ffffffffccccccccffff0000ffff0000ffffffffffffccccffffffffffffffffffffffffffffff00ffff0000ffff00ffffff0000ffff0000000000000000ffff0000000000000000
|0,8=>0xffff0000ffffffffffff0000ffff00000000000000000000ffffffffffff0000ff00ff00ffffffffff00ff00ff00ff0033333333333300003333333333330000ccccffffccccffffccccffffcccccccc00000000ffffff0000000000ffffff00ffffffffffffffff00000000ffffff00ffffffffffffffffffffffffcccccccc0000ffff0000ffff0000ffff0000ccccffff00ffffff00ffffff0000ffff000000ff00ff00ff00ff00000000000000000f0f000f0f0f000f0f0f00000f0f0000000000ff00000000ffffffff00000000ffffffaaffffffaaaaaaaaaaaaaaaaaa00000000ffffffff00000000ffffff0000000000000000003333333333330000
|0,9=>0xffffffffffffccccffffffffffffccccffffffff00ff00ffffffffff0000000000ff00ff00ff000000ff00ff00ff0000ffffffff33333333ffffffff00000000ff33ff33ff33ff33ff00ff00ff00ff00
|_,_=>0
def sP:Nat→Nat
|0=>0x40a02010e090519040302010e0905040a0c01101d0905040a0c01101e09051913020c011d0905040a011c1b090504030a07011a1805040302170105040a010e060916050403020c010504080302011505040a010e100905040a1401060912110408011009050403020c010f05040302010e0d05040803070106050403020100
|1=>0x13040a02010e090519040302070121050b0408030207011229040a0c0110091105040a0c010609290504030a0c011005040a020c26091805040a0c010609121113040802010905040a0c011025090504230a0201220905040a0c011c100905040a0c012106090504030a070c0106051f04030a020c01050408030c010609050b
|2=>0x40a0c013609050403020c01340905040a02010e33090504030a020701223205040a0c0110090504230a0c0131090504030a020c0115050408030201220905040a0c01300905040a022f0109050403021701052e0403020c0105040a0c01061e09052c04030a020c011211040a0c01100905040a02012b0905040a02012a0905
|3=>0x7011805040a0c0110090504033f020c011205040a0c011b0905040a020c3c093b05040a0c01100905040a0c011a0905040a0c0131090504230a0c010609050b040a02140109053a04230a020c0105190403021401090539130a02011c090538040803020c01290504030a0c010618050403020c010d052d04030a0207011205
|4=>0x30a020c0147090504030a0c010609120513040a0c011009053a04030a020c0105040a0c01211a09110504080a01100905040a02011c460905130a450c0105040a0c0144090504030a0c011a0905040a430c01090504030a0c013109053e040a02011c09120504080c01100905040a420c01090504410a02012a090540040302
|5=>0x40a020c010905040a020c0155095405040a020c01090519040302070c01122913040a020c010905040a0c01520929051304030a020c0151040a020c010905044f0a020c010905044d0a020c010905040a020c014c0905040a020c014a0905040a020c01150905040a450c010905040a02490c0109110519130a020c01090504
|6=>0x50403020c010d05040a020c016009055e040a020c010905040a020c015d09121113040a020c010905040a0c013609052004030a020c010905040a020c015c0905040a02170109052e040a020c01090504230a02012109052404030a020c010905040a020c015b0905040a020c590905040a02010e0905040a020c0158095605
|7=>0x20c016b09290504030a020c01336a05040a020c010929040a020c014e05040a026901093505040a020c0109050b040a020c012109050b04030a02070c0105190403020c01210905040a020c01670912050408020701096505040a020c0109050b040803020c0109050403020c0164090504620a020c010905040a020c016109
|8=>0x20c01097205040a020c01090571040a020c0109320513040a020c010905040a020c6f09052d040a020c010905040a0c011b0905046e0a020c010918050b040a020c01090504030a020c015c0905040a020c012209050408030207011805190403020c0109051904020c011d096d05040a020c01090504030a02010e0905040a
|9=>0x40040a0207010905040a020c013409120539040a020701091257040a020c0109350504030a020c010905040a020c017764090504780a020c010911050b040a020c010905040a020c01770905040a020c0176091105190403020c01090540130a020c01097505040a020c0109120539130a020c010929040a020c015f7305040a
|10=>0x1090504030a020c7a0504030a0207012105040a79020c0109053904030a020701052d04030a020c01092905190403020c013b0513040a020c0109050b040a020c011e0929040a020c0127090504030a020c012209050408030201210929040a020c016809053804030a020c0105190403020c011e09110538040a020c010905
|11=>0x40a020c01810905040a0214010905040a020c018009290539040a0207011205130408020c0109110504080302010912053e040a020c010905190a020c014609180513040a020c0109052d040a020c0121097e05040a020c010905040a02011c093d0504030a0c01100905040a020c7c090504080a0c011009560504410a020c
|12=>0x20c010905400403020c010905190a020c0163091205040a0c01100911051304080a02010905040a020c01470905130a020c010d05040a0c01060929050b04030a020c01052404230a020c01090504030a79020c010905040a020c01092805040a020c82091205040a020c014609120537040a020c01092905040a0c01100905
|13=>0x539040a02011c0905040a028b0c01090513040a020c011c090504030a0214010905040a020c0189091805040a020c01330905040a020c0187091105040a0c01100905040a0c018409050b04230a020c0109050403020c0125090513040a020c011d090513040a020c011e0905130a020c0164090519042303020c010983040a
|14=>0x20c010905040a020c018c090504080a020701090519040a020c018a095705040a020c0109050b040a020c01091211040a020c01090519040a020c01640905190403020c01090520040a020c01091105040a020c0133090513040a020c0125095105040a020c0109121104080201090524040a020c01090504030a020c018109
|15=>0x109703205040a020c010905040a020c018a09050b04030a020c01090586040a020c010905040a020c01096605040a020c01640905040a020c7a09050423030a020c010905040a020c0127090539040a0207010905040a020c01680905040a020c01095a05040a020c016c090538040a020c010905048d0a020c01090539130a
|16=>0x40a020c0150090537040a020c01093b05040a020c0109110519040a020c01090504900a020c010905040803020c01094805040a02070c01095305040a020c01097405040a020c0109053e040a020c01091205040a02070c01094805390a020c0109058f040a020c01098e05040a020c0109290519040a020c010905040a020c
|17=>0xa020c01099105040a020c01092905040a020c01850504030a020c013d05040a020c01330905040a020c01630912050408020c01092905040a02070c01051304030a020c01091805040a020c0109051304080a020c01091205040a020c01093d05040a0c01100905040a020c0121090504030a02070c0105040a020c01460905
|18=>0x5040a020c013d180504030a020c010905040a020c011d0905040a020c011e09120513040a020c010905040a020c017f0905040a020c01094e0504410a020c0109110504080a020109290504030a020c01098805040a020c01090513040a0c011009290513040a020c01090504030a020c012109053904030a020c0109051913
|19=>0x40a020c01094b0540040a020c0109120539040a020c01090519040a02070c010905040a020c011c09110504030a020c01090504030a020c01330905040a020c01095f480504030a020c0109110513040a020c010905040a020c019209290539040a020c01092905040a020c0150090504030a020c017b0519390a020c010929
|20=>0xa020c010905040a020c01097b05040a020c01093d05040a020c0109859405040a020c01090504230a020c01091129040a020c01094829040a020c01091229040a020c0109290504030a020c0105040a020c01090d0504030a020c011e097d05040a020c01094805190a020c01099305040a020c010905040a020c0125091205
|21=>0x5040a020c010905040a02070c01090519040a020c01091105040a020c01094805040a020c01091205040a020c01092905040a020c010905040a020c01094b0539040a020c01090504030a020c01090504080a020c0109051304
|_=>0
def sO:Nat→Nat→Nat
|5,0=>6
|6,0=>0x53704c7045703e7037703070297022701b7014700d70067
|7,0=>0x242623b7233822c7224821c8214820d720581fe71f681ef71e781e071d881d171ca71c281ba81b281aa81a2819a8192818a8182817a8172816a8162815a8152814a8142813b7134712e6127711f8117810f8108710170f980f180e980e180d980d180ca70c280ba80b280aa80a2809a8092808a8082807a8072806a8062805a8
|7,1=>0x2608258825082488
|8,0=>0x463945c7454844d7445843c9433942b8424741b9413840b840383fb83f293ea83e373dc73d483cb93c293b993b183a983a1839893908388838083797371836983618358935173489340833973318329832093188311730a730282fa82f282ea82e282d992d272c992c272ba82b282aa82a2829a8293728b82829279927182689
|8,1=>0x674866c8664865b9653864c7645763c9633962a9622861b76129609960185f985f275ea85e285d995d185c895c085b795ae95a6859e8596858f7587857e9577756f8567855f8556954e8545953c9534852b9523851b8513850a950194f984f184e894e084d794ce94c684bd94b584ad84a4949c8494848b9484747c8474846c8
|8,2=>0x73287299720971887117709870096f886f086e796df86d786ce96c686be86b776ae96a6869d9694968c8683967c7
|9,0=>0x93f8937892e9926891e8915990c990398fb88f388eb88e388db88d388cb88c388ba98b288a998a098997891888988818879887188698860985888508847983f8837882f8826981e8816880e880597fd87f587ed87e497dc87d487cc87c577bc97b487ac87a4879c8794878c8784877c8774876c8763975b8753874b8742973a8
|9,1=>0xa5b8a538a4b8a438a3b8a338a2b8a229a1a8a128a0a8a0289f999f189e899df99d789ce99c599bd89b499ab99a3899a99919989898189798970996889608957994f89478
|10,0=>0xacb8ac38abb8ab38aab8aa38a9b8a938a8b8a838a7b8a738a6b8a638
|11,0=>0xad37
|_,_=>0
def wAt:=mkWire dB 149 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc094100d0a0942831050a414251302c10250b02c6425040a42825050944c0b0409404a1270981429050a41431040942831240cc108d0a07430250b02c30250403428252009c1079050382c0b040342825040346033050342825180cc140d0a094102904094442b050c430350503464240a09410290b07c3025040342825050a414311302c10250c0942c0b040342825
|1=>0x403428252409c108d0a0743025040a460300503428250409414290b09c100d0b02c14250403428250503464240a0941029030ccdc0b040743025350ac14cd0403828250b0cc100d0a0942c1f0c094100d0a094100d0a094484d0409414290a09430351909010290a094a464040a414252d09c1085030cc2825050a414311302c1025040946033290a41425030cc1029
|2=>0x380cc6427040a408351909010290c334100e0a0941025050c410294803c14110a0942c0b040342825050a44c0b040949027042340c310a09414311302c10250a0c410250409408351909010292d02c1085030cc900b042340c31050a44c0b0409428310c09410210a0942831290a44c0b030dc64240a09410293e02c10f5050a430262d02c1085030cc2825180c0140d
|3=>0xa0946013290a414250c0d46424040a4a464040a41425030cc0c310a094108d030c4282504258a42b050940569120981429180cca42905094484e040941429570a4152d04098108e0a0743025320444827050a430250a0941029050a41025050954c0b2904414250a09410250509414351909010290a504a413050942939480901411042180c330a09415060a4b41026
|4=>0x40382825054644c330409520240504414250c0dc6424040a414cd040382825030cc100d0a0943025040342825030cc2825040a5a0251104c14310a0c414290c09415991909810290403428250a0c464330a09410290a634144e04094444f040941431190902825040a414e21909c1029045f44824050a4484f040941429040941429050c4dc0b040743025041e4140e
|5=>0x408410250a0c4444d040941431040941031050a44824050a41425740444427050c4484d040941429045a44826050a410251209c1429017052026050441085030cc28253e02c10f50c098484c04094142905034100d0a09460130503428250b0cc6425040a430250a0942831050342825040a4442b050c41029124bc1026050a46033050342825046c8a433050941425
|6=>0xa0942825040a414250508410250a0c4140e040342825050944813050a42c33040342825030cc28250a0c44413050c414250b09c100d0a094140e0a09410291909c1431040a410210a0c43025570ac152d040981429040c43025050a4152d0409814cd040382825640946433040a42919130cc1025190941431040a59025190cc1029270944813050a414310a0941029
|7=>0x1302c1025050b86425040a46030290a414254807c14110c09410310c0941425050a410250a0c414310a0942831043d414290c0981029130cc102504094a429050941085030cc2825057f44c2b040944833050a430260a0944c0b04095f4070519410291302c10250a0c415050a4b41026017b414260a0943025030cc28254803014110a0942825040c43025042140c33
|8=>0x40340c310a094602b05034282504094442b050c41025050382825040946433040a40c310a0941029050dc6424040a410210a0942831040a4144e0409414291302c1025050c410250a0c5200f050442825040946424040a42c0b19094102905094100d0a094108d0a07430254803014110a0949c261204c1429010d46424040a41429130cc1025390941031050a41425
|9=>0x40941031480cc14110a0c43025051981029054b41026190941029050a41431190cc10290a0941029041e4140e0a094143104038282504094a42b0509414351909010290a0c41429050c44c21040942831050b8100d0a0941031120cc14290c504a413050941025120cc1429180c0140d0a09628250519810290a0962013290c41425050c44c0b04096180b048542826
|10=>0x130cc10252904c1425040743025050842831050c410290a3d430260a09428310504430252904414251109c1431043d43026050a43025040c41411047b414264809c1411040a414254809814111209c1429051981029040342825048542826190981029190cc1029017b41426030c428251204c1429040c430251104c1431120981429290cc14251909c10290a7b41426
|11=>0x50982825040c410290c0981425050342825110ac1431050382825040941429130ac10254809014110a4b41026050c428310a0941425290c414251302c1025040941425030cc2825040c42825040941029053d430260a09814250c0982825040382825051381025050a428310c0941425040942825290a41425040942831050a430261302c1025030cc28250a0943025
|12=>0xc0941029050c41411050a414250409810310a09428310409414260c0982826480c414110a0743025050c41425050441425050a414250a0941425190901029050382825051941029050441029058542826290ac1425040981429190c41029040c414290c0941029120cc1429050c42825040382825120901429050442825040941431480ac1411040c414252904c1425
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x3140000000084000000001100000000004
|7,0=>0x279000026cc000260c0002510000000090423888a42190000000082400000001f907a41d907421c886e41a90691198c62400005f3000000016d0592000056314904e400004a41190000000042410083c40e103530c502e300002a40000264000000008901f3070c184054c0000000114
|7,1=>0x29d000028d0a21
|8,0=>0x5a0d653588d5f3570d593558d533540d4d3528d473510d4134f8d3b34e0d3534c8d2f34b0d293498d233480d1d3468d173450d113438d0b3420d053408cff33f0cf933d8cf333c0ced33a8ce73390ce13378cdb3360cd53348ccf3330cc93318cc33300cbd32e8cb732d0cb132b8cab3
|8,1=>0x8a0e253888e1f3870e193858e133840e0d3828e073810e0137f8dfb37e0df537c8def37b0de93798de33780ddd3768dd73750dd13738dcb3720dc53708dbf36f0db936d8db336c0dad36a8da73690da13678d9b3660d953648d8f3630d893618d833600d7d35e8d7735d0d7135b8d6b3
|8,2=>0x26b39a0e653988e5f3970e593958e533940e4d3928e491918e433900e3d38e8e3738d0e3138b8e2b3
|9,0=>0xbb0aea2ba0ae62b90ae22b80ade2b70ada2b60ad62b50ad22b40ace2b30aca2b20ac62b10ac22b00abe2af0aba2ae0ab62ad0ab22ac0aae2ab0aaa2aa0aa62a90aa22a80a9e2a70a9a2a60a962a50a922a40a8e2a30a8a2a20a862a10a822a00a7e29f0a7a29e0a7629d0a7229c0a6e2
|9,1=>0xcc0b2e2cb0b2a2ca0b262c90b222c80b1e2c70b1a2c60b162c50b122c40b0e2c30b0a2c20b062c10b022c00afe2bf0afa2be0af62bd0af22bc0aee2
|10,0=>0xcfc73e1cf473c1cec73a1ce47381cdc7361cd47341ccc7321
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x80600000080400000080100000071f0000007170000006c200000068600000061700000061400000061200000060d00000060600000060000000048600000040800000040000000020000000010400000008200000008000000006000000004200000001800000001400000001200000000b000000008000000006000000005000000004000000002000000000
|1=>0x4200000003f4f000003f1f000003f0f000002f1f000002f17000002e5f000002e3f000002e1f000002c1400000275f00000269f00000265f00000263f00000205d000001f49000001f1f000001e00000001d0e00000161f000000f9f000000f97000000f25000000f1f000000f17000000e86000000e02000000e00000000d14000000c4a000000c14000000900
|2=>0x13e1f00001374f000012f2f000012f1f000012f0f000012e3f000012e1700001270f0000126cf00001265f00001263f00001261f000010f9f000010f97000010f1f000010e1700001079f00001071f00001068400001012800000a61f000009002000008000000006e17000004f1f000004e94000004e10000004c14000004c0000000471f000004694000004414
|3=>0x98204000094202000090e1f000090e1700009061f000089c0c000088a06000088600000088006000084c0a000084812000084802000046717000044c14000042f57000042f1700004271f00004230f00004204f00004071f00004061f00003021f00002071f000019006000018e17000016e37000016e17000016e1500001480400001461f00001420e000013e5f
|4=>0x20e71700020cf1700020bf1f00020bf1b00020af1700020a71f00020871f00020871700020671f000206617000204e1f00020471f00020470f000202e17000200f1f000200e0000020078400020071f00020071d00020070f00011af1f00011a61f000116f17000116e17000112f1f000112e17000106f17000106617000102e1f000102e17000100604000100200
|5=>0x2200617002080797002016617002012e17002008717002008602002008317002006717002002717002000f1f002000e08002000c1000180071f00180051f000800f1700061e79f0004127df000411f1f00041171f00041079f000401204000400e0000031cf1f00028065f00028061f00021ee1700021cf1f000216f17000216f15000215e1f000212f1f00020e71f
|6=>0x1020af1701020471b01020461f01020461701020061f010080e1f01000460000c00171f00c00055f00c00051f009000717004c10f9f004908f1f004800f1f00480071f004800517002290e1700228961f002288f1700228871f00228865f002280e1700228071f00221079700220961f002208f15002208e1700220871f00220861f00220805f002200f1f00220071f
|7=>0x840000f1f40080051f24000071f10010000010004275f100040f1710000275f10000271f10000071708000621508000401806000071f042000f1f040000f1f020000e1701228865f01061079f01029461f01029061f01028471f01028465f01028405f01028071f
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x9000004000004000004
|7,0=>0x30008496a00020002000700003005150400000600000f1d114a0b08090c0243000d0000040100016b36001f0400001320190e0108100014001d0000041e0a0f1000003f
|8,0=>0x3e64d017824ed241aa631cf4777fb2651c839c16e17957b52484b9f5e8d7ecea6e853c26a37880c6126dde2972743e8e7a8d444c347e327c765e62688cda671c90eb37d5be452154f0b4dc1cb73b234b931bbd2e262d7dc21c1a5d967b6c481c7c14d844c51c3a31ab3ae9bb988e39ca5b8fd3461cbc423b423869566163b14d
|8,1=>0x9275451ca85440c754baee92f395d6b325edd98158221b
|9,0=>0xa2f094a5999f1c7359599197c060ce5cc3e3f11c89e6889d9eb65fdfb8dda0c8ac1c6ce24794d42b6f3d519bc17151b0cb9a2bc4afcdd16fef4fa1aee7e570f08ba9e052cc5f5387a442c9a62a531c55f6f2cf2fe41c9a5128ad8a35669451a75a51
|10,0=>0x1c50db86bfa01c2c1c334f282728
|11,0=>0x18
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 36 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_126 10 roots_126 ops++addP pm 1 dom_125 9 roots_125 ops++addP pm 2 dom_119 9 roots_119 ops++addP pm 3 dom_61 7 roots_61 ops++addP pm 4 dom_95 9 roots_95 ops++addP pm 5 dom_103 5 roots_103 ops++addP pm 6 dom_117 7 roots_117 ops++addP pm 7 dom_43 5 roots_43 ops++addP pm 8 dom_63 8 roots_63 ops++addP pm 9 dom_123 10 roots_123 ops++addP pm 10 dom_111 9 roots_111 ops++addP pm 11 dzo_47_16 6 roots_47 ops++addP pm 12 dom_109 7 roots_109 ops++addP pm 13 dzo_85_32 5 roots_85 ops++addP pm 14 dzo_87_32 6 roots_87 ops++addP pm 15 dzo_93_32 6 roots_93 ops++addP pm 16 dzo_111_16 7 roots_111 ops++addP pm 17 dom_59 7 roots_59 ops++addP pm 18 dom_55 5 roots_55 ops++addP pm 19 dom_85 5 roots_85 ops++addP pm 20 dom_79 6 roots_79 ops++addP pm 21 dzo_95_32 7 roots_95 ops++addP pm 22 dom_41 4 roots_41 ops++addP pm 23 dzo_107_4 6 roots_107 ops++addP pm 24 dzo_59_4 6 roots_59 ops++addP pm 25 dom_87 6 roots_87 ops++addP pm 26 dzo_107_16 6 roots_107 ops++addP pm 27 dzo_121_4 6 roots_121 ops++addP pm 28 dom_93 6 roots_93 ops++addP pm 29 dzo_110_16 6 roots_110 ops++addP pm 30 dom_62 6 roots_62 ops++addP pm 31 dom_31 5 roots_31 ops++addP pm 32 dom_53 4 roots_53 ops++addP pm 33 dzo_46_16 5 roots_46 ops++addP pm 34 dom_115 7 roots_115 ops++addP pm 35 dzo_86_32 5 roots_86 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_85_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_87_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_93_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_111_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_95_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_107_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_59_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_107_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_121_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_110_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_46_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_86_32_84 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_126 10 s (0,roots_126.map (·&&&dom_126)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_126 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 68 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 68 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 151 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 23 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 151 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 98 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 98 0 = true)
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
def dzo_220_1:=0x22222222000000002222222200000000222222220000000022222222
def gzo_220_1:=0x22222222000000002222222000000000222222200000000022222200
def gsh_220_1:=0x11111111000000001111111000000000111111100000000011111100
theorem lowS_zo_220_1_196:Lower true dzo_220_1 roots_220 gzo_220_1 6:=lower_iso_b (d1:=dom_220) (r1:=roots_220) (T1:=gsh_220_1) [(dom_220,1)] (by decide +kernel) (lower_slice_b (T:=gsh_220_1) [(0x11001100000000001100110000000000110011000000000011001100,0,8),(0x11110000000000001111000000000000111100000000000011110000,0,16)] (by decide +kernel) lowS_196)
def dzo_151_8:=0xff00ff00000000000000000000000000ff00ff00
def gzo_151_8:=0xff00fe00000000000000000000000000fe00ee00
def gsh_151_8:=0xff00fe00000000000000000000000000fe00ee
theorem lowS_zo_151_8_148:Lower true dzo_151_8 roots_151 gzo_151_8 6:=lower_iso_b (d1:=dom_151) (r1:=roots_151) (T1:=gsh_151_8) [(dom_151,8)] (by decide +kernel) (lower_slice_b (T:=gsh_151_8) [(0xaa00aa00000000000000000000000000aa00aa,0,1),(0xcc00cc00000000000000000000000000cc00cc,0,2)] (by decide +kernel) lowS_148)
def dzo_198_1:=0xaa00000000000000aa00000000000000aa00000000000000aa
def gzo_198_1:=0xaa00000000000000a800000000000000a80000000000000000
def gsh_198_1:=0x55000000000000005400000000000000540000000000000000
theorem lowS_zo_198_1_198:Lower true dzo_198_1 roots_198 gzo_198_1 5:=lower_iso_b (d1:=dom_198) (r1:=roots_198) (T1:=gsh_198_1) [(dom_198,1)] (by decide +kernel) (lower_slice_b (T:=gsh_198_1) [] (by decide +kernel) lowS_198)
def dzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00
def gzo_215_8:=0xff00ff0000000000ff00fe0000000000ff00ff0000000000fe00ee00
def gsh_215_8:=0xff00ff0000000000ff00fe0000000000ff00ff0000000000fe00ee
theorem lowS_zo_215_8_148:Lower true dzo_215_8 roots_215 gzo_215_8 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_8) [(dom_215,8)] (by decide +kernel) (lower_slice_b (T:=gsh_215_8) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,0,2),(0xff00ff00000000000000000000000000ff00ff0000000000000000,0,64)] (by decide +kernel) lowS_148)
def dzo_214_1:=0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa
def gzo_214_1:=0xaa00aa0000000000aa00a80000000000aa00a80000000000aa0000
def gsh_214_1:=0x550055000000000055005400000000005500540000000000550000
theorem lowS_zo_214_1_198:Lower true dzo_214_1 roots_214 gzo_214_1 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_1) [(dom_214,1)] (by decide +kernel) (lower_slice_b (T:=gsh_214_1) [(0x550000000000000055000000000000005500000000000000550000,0,16)] (by decide +kernel) lowS_198)
def dzo_214_8:=0x55005500000000005500550000000000550055000000000055005500
def gzo_214_8:=0x55005500000000005500540000000000550055000000000054004400
def gsh_214_8:=0x550055000000000055005400000000005500550000000000540044
theorem lowS_zo_214_8_148:Lower true dzo_214_8 roots_214 gzo_214_8 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_8) [(dom_214,8)] (by decide +kernel) (lower_slice_b (T:=gsh_214_8) [(0x440044000000000044004400000000004400440000000000440044,0,2),(0x550055000000000000000000000000005500550000000000000000,0,64)] (by decide +kernel) lowS_148)
def dzo_206_1:=0xaaaa000000000000aaaa000000000000aaaa000000000000aaaa
def gzo_206_1:=0xaaaa000000000000aaa8000000000000aaa8000000000000aa00
def gsh_206_1:=0x5555000000000000555400000000000055540000000000005500
theorem lowS_zo_206_1_198:Lower true dzo_206_1 roots_206 gzo_206_1 6:=lower_iso_b (d1:=dom_206) (r1:=roots_206) (T1:=gsh_206_1) [(dom_206,1)] (by decide +kernel) (lower_slice_b (T:=gsh_206_1) [(0x5500000000000000550000000000000055000000000000005500,0,8)] (by decide +kernel) lowS_198)
def dzo_213_8:=0x33003300000000003300330000000000330033000000000033003300
def gzo_213_8:=0x33003300000000003300320000000000330033000000000032002200
def gsh_213_8:=0x330033000000000033003200000000003300330000000000320022
theorem lowS_zo_213_8_148:Lower true dzo_213_8 roots_213 gzo_213_8 6:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_8) [(dom_213,8)] (by decide +kernel) (lower_slice_b (T:=gsh_213_8) [(0x220022000000000022002200000000002200220000000000220022,0,1),(0x330033000000000000000000000000003300330000000000000000,0,64)] (by decide +kernel) lowS_148)
def dzo_149_8:=0x3300330000000000000000000000000033003300
def gzo_149_8:=0x3300320000000000000000000000000032002200
def gsh_149_8:=0x33003200000000000000000000000000320022
theorem lowS_zo_149_8_148:Lower true dzo_149_8 roots_149 gzo_149_8 5:=lower_iso_b (d1:=dom_149) (r1:=roots_149) (T1:=gsh_149_8) [(dom_149,8)] (by decide +kernel) (lower_slice_b (T:=gsh_149_8) [(0x22002200000000000000000000000000220022,0,1)] (by decide +kernel) lowS_148)
def dzo_222_1:=0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa
def gzo_222_1:=0xaaaaaaaa00000000aaaaaaa800000000aaaaaaa800000000aaaaaa00
def gsh_222_1:=0x55555555000000005555555400000000555555540000000055555500
theorem lowS_zo_222_1_198:Lower true dzo_222_1 roots_222 gzo_222_1 7:=lower_iso_b (d1:=dom_222) (r1:=roots_222) (T1:=gsh_222_1) [(dom_222,1)] (by decide +kernel) (lower_slice_b (T:=gsh_222_1) [(0x55005500000000005500550000000000550055000000000055005500,0,8),(0x55550000000000005555000000000000555500000000000055550000,0,16)] (by decide +kernel) lowS_198)
namespace S_223
def pG:List (Nat×Nat):=[(1,9),(1,17),(2,10),(2,66),(2,130),(3,11),(3,19),(3,67),(3,131),(4,20),(4,68),(4,132),(5,13),(5,21),(5,69),(5,133),(6,14),(6,22),(6,70),(6,134),(7,15),(7,23),(7,71),(7,135),(8,9),(8,10),(8,72),(12,13),(12,14),(12,28),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,26),(18,82),(18,146),(24,25),(24,26),(24,28),(24,88),(24,152),(64,66),(64,68),(64,72),(64,80),(64,192),(65,67),(65,69),(65,73),(65,81),(65,193),(128,130),(128,132),(128,144),(128,192),(129,131),(129,133),(129,137),(129,145),(129,193),(136,137),(136,138),(136,140),(136,152),(136,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_223.map (·&&&dom_223)
def gM:=goal_223&&&dom_223
def NN:Nat→Nat
|5=>2
|6=>67
|7=>273
|8=>252
|9=>75
|10=>10
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x129480cecc
|6,0=>0xfff2ffe58cf7829f1cbaed0d9ea0a5e9f6be97f3e2bafe253edb5cdd890cd74add680dd213cc6eccc64dfc1d8abe617b9f90b9d0cb5d65b2f13b1739b1296aa787a66e0a5e6ba36a6a13a69c6899c1a8993bb970239503f89b4f85ef9858da84853786d773f7173a7d6fe416c774675d366210623925d36b56e4552adb524f35075e502504d8713ffeb3df8e35a4b32dfd3190b2e9522a4d6291801d3a8116a20e9ba0c20c06943
|7,0=>0x7d8117cf3e7b4387ad1d7a113793c478a0f76ddb762d6739397319472747705fc6fa206f3656e93d6c6a46b53e6ace76939b692d468d796852a67a196459e6378f6281360cfd5ea8e5e3625d4c55cbcd5c6f65b3d85a2775856657ab754c2f523af51932515624e3374da994c61f4c5854a2d549f5b49c3b48fa54859647fd446f4244dc344cf54415543134430c7404243fb223f2303e6123e51f3e0583e037388c6372e136ff73554c3503e34b67348e93479a31e953108d30c932ff402fe442c81e2c5812a1522954c274e1271d32554124aab2459a22d7c22004214682065b1f0231e42f1dcd91cb491c1751b87e1abdb1a9ba1a83919db418a91181ae179621750e15e3615e3113ae81393e125e4116791123a0e5480dd410c2720a8f20a6810a4f00a0fa07e94074e70741205d5a045c103e600328301c69008bb0050c
|7,1=>0xeef57ee07fedb1fed747ed6a1eb787eb731eb5d0eaf69e92f9e8e7de899ae78b9e5cbce48e0e42e0e2f30e1765e173de0c1ce0143df4fddeff1de58dddcd5dd90edac4dda18cd8999d74add739fd6eecd6800d5bacd4bcdd4941d3857d2b16d1ec7cfe34cfb83cf8e5cf571cc48ecb176ca828c7cdec76a9c732cc708ec6340c5966c3371c26eac15e2bf670be26ebdc36bc425bb39cb9e4cb784db756db740fb587bb5575b4ee7b4c6cb4a7db42e4b22e4b1c46b16ddb15f5afb99af63eaeec6aeafbaddbcac9f8ac632abcbaab2cdaa735a8f65a87dfa553fa543aa5274a5056a4dd5a438aa2487a2269a0ff49fe519fb679f8809f3039ee2b9da0e9c0d89b22f9aea09ab53990f99610096084940678f86a8ece48c1518b5c18ac598998c893d28849488407863e785c2484ed78491d80f9680922804d27fad67e1a97d9e2
|7,2=>0xfe430fdf9cfdaccfd28dfc5fdfb374fb36bf9a0bf850bf7caaf6490f54b5f32c8f27edf1004f0732ef0a4
|8,0=>0x8d80f8d5cd8d4808bf708ba428b9958b6d58a22889f3c8744385de28529f83dab8344781e1780ff67fc8e7f51f7da267d89e7cc15779a776cc872e25724097217a70f3f708986e0ac6df246d2346cbe36b6376b3e46b15268303665976378f636506351c614476129c602265fb0b5d7fd5c6c15ba765b6f85b0c4567745593854f3d5395e52ea1521fc5032c4f68c4e2044e0c24de6a4db6749f5b45d64459e14387c435734315042e13410ad40790401c64014b3f4ba3f0653e0903d3543d1c83b0113900c38dee34e7c3462233bbe310e22eb7c2dd932db022a3ac29d0527eb52696f2521224c7e249db2491023a35237a92340022e4622e2521f191e8d31bd621ba7b1b4fe19b1018bd815dfc151e514d2e14c8d14c3212f2110c700f2120e6780d9680d5f60c4d80aec70a29809899098280647602ac702874025e201348
|8,1=>0xff5a4fd408fc756fac1ff872cf6467f613df474cf3e8af36a2f33d0f2fd6f1f4eefbb8eb1beeab48ea17de9b6ae87fee818ee7e80e7e7ce52fae49e0e3487e321ee2d8ae13ebe0054dff70ded84dea0edda38dd7e0dcf72dacdada2a3d9fead915dd75dbd5520d4276d3927d3414d324bd29c6d1f9ad0906d086ad03bed0045cf845cf5b6cf3dbce920ccc36caaaaca670ca3d2c9c94c867bc8532c636dc5a0ac4e1dc39d3c2ac3c0958be6d8bd54cbc413bbf9cbaa82ba4e2b8e9cb8843b7904b6c32b66d7b65a7b5200b4939b435fb31f2b1efcb1cdeb1aa7af616ae090adb4cace5cac3ecab2a6aaab7aa5b6a9f15a94a4a8a19a8457a7397a5ec4a4bd0a4aa7a3f0ca2a3da1e42a0e36a000a9ddb99c72e9b27f99cd59833797b6996a34966ad937259333792f8492c4a920318f3338ec238dd82
|9,0=>0xfabeaf87e1f3466ef716edbb5ebe47e8212e7662e3df7dc4cdd969fd6d3cd3c4accafdcb6dfc99b0c6a28c3d59c0783beed0becb9bbd72b8715b1177b0de1b0d29a256fa123f9d6319cbaf9b39594b129068c87e358782b8160d7f0917ea407b49b713936c231635dd628ed5916d5894857c13561e5518fd501d24ce6e4a179430f93d23c3bf222ef292e12b2e1172b96d27042267b125e9b1cc081c6c21c0f51c02819e4415ed01073a0b0380882306d07061a1038b4036c101bca
|10,0=>0xe5cbdbebecae79e94644799007474a6375a5bfd64e3a91f14a
|11,0=>0x1730e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff000000000000000000000000ffffffff0000000000000000ffffffff00000000ffffcccc00000000ffffffff00000000ffffccccffffffff00000000ffffffff00000000ffff000000000000ffff0000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa33333333000000003333000000000000333333330000000033330000ffffffff00000000ffffffff00000000ffffffff00000000000000000000ffff000000000000ffff000000000000ffff000000000000ff00cccccccc00000000cccccccc00000000cccccccc00000000ccccccccffffff0000000000aaaaaa0000000000ffffff0000000000aaaaaa000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0000ffffffff00000000ffff000000000000ffffffff00000000ffff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0ffffffff00000000aaaaaaaa00000000ffffffff00000000aaaaaaaa33003333000000003300333300000000330033330000000033003300ffffffff00000000ffffffff00000000000000000000000000000000
|0,1=>0xffffffff00000000aaaaaaaa00000000ffffff0000000000aaaaaa00ffffffff00000000ffff000000000000cccccccc00000000cccc0000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000000000000000000000000000000000000f0f0f0f000000000f0f000000000f0f0000000000000f0f0000000000000f0f0000000000000000ffffffff00000000ffffffff00000000cccccccc00000000cccccccc0000000000000000000000000000000033333333000000003333000033333333000000003333333300000000333333330000000033333300aaffaaff00000000aaffaaff00000000aaffaaff00000000aaaaaaaaffffffff00000000ffffffff00000000ffffff0000000000ffffff005555555500000000555555550000000055555500000000005555550000000000000000005555555500000000000000000000000055555500ffffff0000000000ffffff0000000000ffffff0000000000ffffff0000000000000000000000000000000000ffffffff00000000ffffccccffff000000000000ffff000000000000ffff000000000000ffff000033333333000000003333333300000000333333330000000033330000
|0,2=>0xff00ff0000000000ff00ff0000000000ff00ff00000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0c0cff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ff00330333030000000033033303000000003303330300000000330333000f0f0303000000000f0f0303000000000f0f0303000000000f0f00000000ffff000000000000ffff000000000000ffff00000000000000003333333300000000333333330000000033333333000000003300330000000000000000000000000000000000ffff333300000000ffff0000ffffffff00000000ffffff0000000000ffffffff00000000ffffff0055555555000000005555550000000000555555550000000055555500ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00ffffffff00000000cccccccc00000000ffffffff00000000cccccccc0f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f00ffffcccc00000000ffffcccc00000000ffffcccc00000000ffffcccc0000ffff000000000000ffff00000000000000ff000000000000000055055505000000005505550500000000550555050000000055055500
|0,3=>0x33333333000000003333333300000000333333330000000000000000ff00ff0000000000ff00ff0000000000ffffffff00000000ffffff0055005500000000005500550000000000555555550000000055555500000000ff000000000000000000000000000000ff00000000ffff000000000000000000000000000000000000ffffffff00000000ffffff0000ff00ff0000000000ff00000000000000ff00ff0000000000ff000055555555000000005555555500000000555555550000000055555500f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0ccccffffffff00000000ffffffff00000000ffffffff00000000ff00ff0000000000000000000000000000000000ffffffff00000000ffff0000cccccccc00000000cccccccc00000000ffffffff00000000ffffcccc00000000000000000000ffff0000000000ff00ff000000000000000000000000000000000000cccc0000000033333333000000003333ccccffffffff00000000ffffffff00000000ffffffff00000000ccccccccffff000000000000ffffffff00000000ffff000000000000ffffccccffffffff00000000ffffffff00000000333333330000000033330000
|0,4=>0xffffff0000000000ffffff0000000000ffffff000000000000000000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff000000ffff000000000000ff00000000000000ffff000000000000ff00ff0fff0f00000000ff0fff0f00000000ff0fff0f00000000ff0fff0000ff00ff0000000000ff00ff0000000000ff00000000000000ff000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000000000000000000000000000000000000000ffff000000000000ff00ffff000000000000ffff000000000000ffffffff00000000ffffff000000ffff000000000000ffff000000000000cccc000000000000ccccffffffff00000000ffffffff00000000ffffcccc00000000ffffcccc0000000000000000ffffffff000000000000000000000000ffffff00ffffffff00000000ffffffff00000000ffffffff00000000ffffff00ffffffff00000000ffffffff00000000ffffffff00000000ffffcccc000000ff00000000000000ff00000000000000ff0000000000000000aaaaaaff00000000aaaaaaff00000000aaaaaaff00000000aaaaaaaa33333333000000003333333300000000333300000000000033330000
|0,5=>0xffffffff000000000000ffff00000000ffffffff000000000000ff00ffff00ff00000000ffff00ff00000000ffff00ff00000000ffff000000000000000000000000000000000000ffff00ff00000000ffff0000cfcfcfcf00000000cfcfcfcf00000000cfcfcfcf00000000cfcfccccffffffff000000005555555500000000ffffffff000000005555550003030303000000000303030300000000030303030000000003030000ffff333300000000ffff333300000000ffff333300000000ffff0000000f000f00000000000f000f00000000000f000f00000000000f0000ffffffff00000000ffff000000000000ff00ff0000000000ff0000000000ffff000000000000ffff000000000000ff00000000000000ff00ffff000000000000ffff000000000000ffff00ff000000000000000000000000000000000000000000000000ffffff0000000000ffffff00ffffffff00000000ffff000000000000000000ff000000000000000000000000000000000000ffff0000000000000000000000000000ccccffffffff000000000000ffff00000000ffffffff000000000000ccccffffffff00000000ffffffff0000000000ff00ff0000000000ff0000
|0,6=>0xffffffff000000000000000000000000ccccccccffffffff000000003333333300000000ffffffff000000003333000000000000000000000000000000000000ffffffff00000000ff00ff00ffffffff00000000eeeeeeee00000000ffffffff00000000eeeeeeee00ff00ff0000000000ee00ee0000000000ff00ff0000000000ee00ee0000000000000000000000000000000000ff00ff0000000000ff00000000000000000000ffffff00000000000000000000000000ffffff00000000000000000055555500000000000000000000000000555555000000ffff000000000000ffff000000000000ffff000000000000ccccffffffff00000000ffffffff000000000000ffff000000000000ff00000000000000000000000000000000000000000000000000ffffff00ffffffff000000000000000000000000ffffffff00000000ffffff00ff00ff0000000000ffffffff00000000ff00ff0000000000ffffff000000000000000000ffffffff000000000000000000000000ffff00005500550000000000555555550000000055005500000000005555550000000000000000000000ffff0000000000000000000000000000ff00
|0,7=>0xffffffff000000000000000000000000ff00ff00ffffffff00000000ffffffff00000000ffffffff00000000aaaaaaaaffffffff00000000ffaaffaa00000000ffffffff00000000ffaaffaa0000000000000000ffffffff000000000000000000000000ffffcccccccccccc00000000ffffffff00000000cccccccc00000000ffffccccffffffff0000000000ff00ff00000000ffffffff0000000000ff000000003333000000000000333300000000000033330000000000000000ccccffff00000000ccccffff00000000ccccffff00000000cccccccc0000000000000000333333330000000000000000000000003333000055555500000000005555550000000000555555000000000055555500ffffffff000000005555550000000000ffffffff0000000055555500ffffffff00000000ffffaaaa00000000ffffffff00000000ffffaaaa00000000000000000000000000000000ffffffff00000000ffffaaaaffffffff00000000ff00ff0000000000ffff000000000000ff000000000000000000000000ff00ff00000000000000000000000000ff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x100918044142030464005080c4024200884108030f00146840620f801c442033c080120a342031008e841030e0f36388840630c8a22106180c3c0110820b861e0028d080c41514148840620a0026142080418012221018c203c70d080c60b141420310084800a104070c002840608080
|1=>0x441420304400220a1018c322828d080c417141488410097000a442030460011086862b1e00711080cf0c14156840620100221062c0c3c011086862b143c284100831b0014208041950022106290c3c02822101a4182828d080c42614348a50620f8022101a41864522080cf0c1414884
|2=>0x1e0028d080c6291439b0d080c4024e442080418035221018c603c884105430f004422418ac50022101881829a223a101821600884063198f004423218ac780621420310080110890d0c0c28e85080c4070088284060980044142033c0800d082061c1e6c284063008a00882841008300
|3=>0x4c3c011082062b1efc011080c43d1e0028d080c4261e00e85080c40254008a50620f800af0203103001108213061e00284063008f00ec28d080c4020a3420310500220a1019e1829136080d20c1414203107c0110820106740088410e430f00d820818187aa221040c5c3c01108e040c
|4=>0xa442080418011080c4141e00284062012a00148840620b8a004420818b850f008868406c860a1e4420818187af0044203186050f0089b0d080c40c1e38911080c40c150c884103170f0015684062060a0044208184030f004420311047800a1018805000220a101b218280362210188
|5=>0x2518884062060f2615b0406201008a4420310305002210d0818b87801c4420818187801a1040c0c3cd801a44203105c50f2414684062060f2c4420818187801c44203184078022101883c305052210188723c00d08206061ea80270a342031030505221018804640121a44203103079d
|6=>0x80c6181e0111d0a1018804008ce062014d003890d080c40c1f18284066840c1438884066860a233020818187802c14203103051222101b2103078e221018c603c00522104020c00284062064b1438884067860f0044203180450f0044208181a50f0120684062060f0044203483238a
|7=>0x1a101880402311082062e1e01f0522101880400e91080d21a1828b051a101880400291080c402a400291080c40ca20029108206231e0028d080c40c1629105080c6191e00284062060f4200284062060a9e00691082062e1e008b708206061e0028d080c40c742a28d22101881828691
|8=>0x1468406c840c1414203103200a221040c0d607802212b8310305432210188183c0450a3420310300220a1019a0400884062060a1f54884642062e1e0110d08206061e00284062060fa6023051a10188182910d080c6101e00e8406206091e007362210188040220522101880400705
|9=>0x1e0028d080c40c14fd411080c40c143c291080c4022001105080c10b0015684062060f00ece91080c40c1e14884062061914586914a0c402009ce91080c40200d4291080c4020034884063148a1e14208181879b00748840620a8f00442031030c8a1e1420818187aa0014884063148a
|10=>0x343050f3a442081818e0f8c4420348305110820606b43c00d2210188283c01d2210188723c005221040c5c3c01d6c10188183d505221018804c0005221018c303c03622101887a3c03b0a44203100800522101883c08011080c41f1e00712221019a183c9856c1018818288840620619
|11=>0x2c14684062060a441420818187801c4420818b87802210188723c01d6c4420818187a20a1018c203c011082062b1e01b04062060f5514291080c40c0074884062010b0038291080cd0200f8884062060a1e44203116c7800a44203100a5000a34203103052f3a442031009d004474203
|12=>0x1e00291080c43d1e0028406206091401885080c40c1e01a91080c40c143d105080cd0c1474884103118f0045283100ab003a442031098780441420318c07801cd8884062060ab244203343050f44142033c307801c44203182c5001c14684062060a2212e0818187807c14884062060a
|13=>0x103030a1f0c884103030f00ec884062060a1e16704062060a5444203343080a1f0c884063080f01182840620100221040c463c00d080c40c16286840620609143c28d6e101881829a8522101881828291080cd0c14fd11d6c10188183ec91080cd0c1e00291095c188040111d080c60b
|14=>0x103048f0088e8406c860f00ec291080c40c14148840620f0c14d8884069040c14348840620a8a1ed4884066860f0046704103030a1e74208181879b0039b0d080c40c1e9c884103030f0038684063058f007420818187aa00882b6080c4020048e91080c40c1e4ce85080c402004421a
|15=>0x54748840620b8f00442031184780221018818c0c8f221040c0c7050f447420348305000a101880e008840621c8a1e02311080d21a1828291080c40cbe01a91080c6191e002b61a10188044420334206301e4420818ac50f0044203343080f0174884062060a1e48291080c4020034203
|16=>0x118691080d20c1564884069060a009c28d080c4020044208182c30f00ec691080c40c1e38e91080c40200d8884103030a1e146840620a8f00442081819d0f016488406c860f0074884103170f00348840620f8f004420318047aa00748840630c0f0038291080cd0c1415b04062060a
|17=>0x80c4261400284062014b00348840621c8f00d8684062060f5518884103030f0088e84103030f004420818b87808c442031840780221040c46287801a44203116c7804474203184078022941880e0229d221018818008840630c0f009db11080c40200ec28d080c40c1e388840630c8f
|18=>0x1e0028d080c4027400884063008f010c911080c40c1f10884103030f0044203483080a0118284062060a8c142033420100221018c523d50044d8203103050f221190818187800a44257062060a1a442081818e0f2c142031008011080d90c203c0221a101a4182b211080c40c1400291
|19=>0x18ac7802414884062060a221040c0c3df80261420818187800a44203100b0001a44203103330f0a44203100a800441019e183c0051a10188042c0220ad8203103050e1a101881829b0d221040c0c3d105080c60b1400911080c40c143c691080d20c14fc884482060614002840620609
|20=>0x58691080c40c143c29108206061e00691080c40c203c011080c417143c0130ad820310307804e1488406201001c14884062060a003488406206491e023051a101880400b114a0c402001420310327801a44208188c780861488406201002444203342060f3a4420318a4780b244208
|21=>0x6e101881828011080c40c8e287d92210188183df800a4670406201004444203343050f4474284062060f0044203103350f0046703103268f0044203103180b1e02311080d20c1e00884062340f001488406684020044203103338f00d5b11080c40c1e00884063148f00588840620a8f
|22=>0x2210188183c0462210188043c0440a4420310307801a45b84062060a1e75b11080c40c1e3828d080c40c1e00291080c4021600691080c40c943c03e0a4420310307802c14684062060f001488406206521e00884062014d0014884062013a0044203103058a0044203103048a1e00291
|23=>0x1e00684062060b1e01a852210188183c011080c4071e008840620656143ce91080cd0818287c33a442031030780a8142031030780c84420310307800a4420310987800ad8884062010022b420310307aa0088284066860f0044203103288f0194884062060f0046704062060a1ea8736
|24=>0x2210188183c01d080c40c1ea800522101883c3078086442031030780261420310305002210188183e1000a44203103080f004420318a450f0088284063058f0044203103300f008828406201003a46704062060a1e586914a0c40c1e0088406206501e00883100b58f009ce91080c40c
|25=>0x38291080cd0c1e00291080c40c943c0052338203103051d6c44203103050f444420348305003a442031031d0f0045684062060f01188840690d0c1e00291080cd08182a411080c40c1e01111080d90c1e02a114a0c40c1e00291080c40c603c011080d21a182af11080c40c1e01d85
|26=>0x103370f0118691080d20c1e0231d2210188183c046221018818287b6221018818287c6221019a10087804e44203100800e221018818280161a4420310547802c442031008780221018818647802210188052c78022101882a3c065221018818287803a4420818187803a44203103058f
|27=>0x1a4420310087802210188183e7803ad8691080c40c1f0c884062060a1e00291095c188183c01d22101a4103050044342034830780447420310307808874884062060f0015b11080c40c147488406c840c1e0070522101880400884103030f0114884062060f00452831032b0f0044203
|28=>0xc4884062060f010c884066840c1e02211080c40c1e008ad080c40c143c0220ad820310307801c3420310307807c4420310307803a4420310307bf0044203103290f0044203100a00f004ce85080c40c1e01111080d90c143c011080c4027402305080c40c1e02f11080c40c143c046
|29=>0x103380f0014203103052a0074884062060f5e03191080c40c1e00884062130f007488406206101e002b61a10188183ce910820606143c02222101b234307802414884062060f0014684062010044342031008780b24420310307806c34884062060f221019a18287bf4e14884062060a
|30=>0x1e00b11080c40c143c88406206101e00e8d080c40c1ea8011080c40cbe3c00d080c40c143d511080c40c96287910820606143c00e24442031030780221019a1030c8f010c691080c40c1e01a91080c40c1e00691080d2081828884066860f7e0088406206491e008a59c0c4020044203
|31=>0x3a1488406201004ed8884062060f00ec884062060f0044203107860f004c28406201003a44203103250f0088e84062060a1e013851a10188183c0052210188182c5008c44203342060a1f0e311080c40c1e008b7080c40c1ea800e3a4420310307800a442031031d0a0058e91080c40c
|32=>0x1400711080cd0c1e00e916e10188183c011080c40c943c0160a10188183c044221018818287802c34884062010f0014203103258f00348840620a8f007469108206061e0088406906471e00684062060f5400884e20c40c1e02191080d908183c011080c40c143e780221018818c0780
|33=>0x100a38f01c8884062010f0044203103200a1e4420364307bf0088284062060a0014684062063a1e01162080c40c1e0069108206061e0228d2210188183c011080c4171e01111080cd021e01111080f78c1e02305080cd08183c0461a44203103050fb244203103050f001488406c840c
|34=>0x1e0088407dc40c1e0088406206661e00291080c40c14fc00e221018c163c011080c40cec3c0051a10188182911d1a10188183c005221018819807804434203103050f22101a41829f800a44203103280f0014684062060b1e008840623a0f004c8a506201001a44203642060a1e44203
|35=>0x10307808834884062060f0014203103200f01e8884062060f00442031033c8f0044257062060f0034884062060a1efc884062060ff0008840623a8a1e00e85080c40c1ea8011080c40c123c011080c40c20287808c14684062060f00588a5062060f010c291080c40c1e00991da0c40c
|36=>0x18e87802210188de30780244420310307802210188192850f0034884062060a1ebc291080c40c323c01d0a4420818187800a10188183d50044d8203103078022101880558780f64420310307807cd8884062060f010c711080c40c1e00291080c40c14bc00d2294203100804622101b2
|37=>0x80cd0c1e00884062060a1ea80220a10188183c011f810188043c0732210188043c0161a4420310307801a442031008780d24420310307800ad8884062060f0045b84062060a1e008ce080c4021e00291080c40c163c011080c40c9a3c01d2210188183c011080cd08043c0052210188
|38=>0x143c291080c40c14008e2080c40c1e007052210188183c022221018818287802338203103050f4e44203103078022101881958780221019a103050f1a44203482060f0074884062060a1e00991080c4021e0088407b04021e02a11080c40c1e00991080c4751e0088406206471e01111
|39=>0x47684062060f0074291080c40c1e00884062060f7e00985080c40c1e008a5080c4020044203482060a0044203642060f00452ce062060f004420311f410f0118884062060f00d8884062060f0014684062060f0044203103058f00442031031d0f0074691080c40c1e00691080c40c
|40=>0x80c40c1e00884062060a1efc011080d91a10307802644203103050f00148840620100444420310087808c44203342060f0038884062060f0044203642060a1e00b11080c40c1e00884062064b1e009914a0c40c1e00884062060f5e008840623a8f0088884069060f004c8ce062060f
|41=>0x23382031030780221019a103078022101881828780444420310307800a46704062060f004427e062060f0014884066840c1e00884062060f54008840690d0c1e0110d080c40c1e00884062060a1ebc0270a442031030780221018819007808c34884062060f0045b84062060f00348a5
|42=>0x884062060f0044203482060f004420310087800a44203103078026442031030780229420310307801a442031030780
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0xcc0006
|6,0=>0xe1b86f1c36ae1ae70d3b86858334e19370c638615c2fce17770b8385a5c2c4e15b70aa38535c28ce13f709c384c5c254e123708e38455c21ce1077080383e5c1e4e0eb707238375c1ace0cf706438305c174e0b3705638295c13ce097704838225c106c07c703ab81b9c0cee060702cb8149c096e044701eb80d9c05ee0287010b8069c026e00c7
|6,1=>0x76183a2e1ca7
|7,0=>0x1e540f0a077503b281d540e8a0735039281c540e0a06f5037281b5b8d8e06b7035471a640d15c67b0335819738c9dc63f03178187c0c1e0600e2f8817840ba205c102d8816840b22058102b8815840aa5c54302998148c0a26050302798139389adc4c7025b8129c092e0487023b8119c08ae0447021b810a38835c40b01fd80fac07b9c3cd01de8
|7,1=>0x2e1b96ee0b6705ab82d1c1671cb29058c82c2415f20ae9056d72b2c15760aab054d82a2c14f60a6b052d8292c14760a2ce50e8283413fa09ed04ee82734137dc9af04cf8263c12fe096f04af8253c127e092f048f8243c11fe08ef0470723441185c8b3045182253910a0875043282154108a0835041282054100a07f503f281f540f8a07b503d28
|7,2=>0x3dd41eca0f56e7a383cdc1e4e0f17078383bdc1dce0ed7076383adc1d4e0e970743839dc1cce0e570723838dc1c4e0e170703837dc1bce0dd706e3836dc1b4e0d98e6c5735f39ada0d5d06a6834f41a5a0d1d0686833f419da0cdd0666832f4195dcc9f06487320418e20c6106288310418620c2106088300417e20be105e882f0b97660ba305ca7
|7,3=>0x4d73a69a133d099684c74261a12fd097684b7ba59e12bf095784a83a522128109388498424a2124109197488c2429d20508fa8479ba3ae11c708db8469c2331d18908bc845a422b2114cc89e844bba23e110f087f843bc21be10cf085f842bc213e108f083f841bc20be104f081f840bc203e100f07ff83fbc1fc1cfd107e083ec41f498f9507c28
|7,4=>0xa328515ba891d4390a1485064281213f909f484f64279213b909d484e642715d37b09b58
|8,0=>0x623cb0fe186f0c2f86143b07e582d2c0e8603baffa57ed0bed95f33af7a17ab2bcc95e242ef217690bac85d1cae6e17270b8b85c14ade656e30b6895afcad5e169d2b46859ecacd256572b22958dbac4e16170b02957ccabc615d12ae0856c42b3e558f0abf855b4aaba154eea9f854bc2a3a550eea7f853b4a9ba14cb2a5d852a4a93214872a3a9
|8,1=>0x72ecb9525c990e44871dcb8ce1c570e22970ccb849dc150e0196fc4b7c21bcf2dde96eacb7325b890dbc86d9cb6ae1b452d9a86c9bb62e1b070d7b86b94b5a65ac30d5986a84b525da830d389698434a21a410d1976884b42219ff2cf69676cb39619b92cd48665cb30e19752cb286554328a19350c9196453b20a18f32c7186344b18218b10c508
|8,2=>0x83b441b660cb105d882a4c12e6087103b88194c0aa2045101a8808cc02260010ff887f7cbf9e1fbf0fd877e7cbf1a5f7b2fb497d5cbe8a5f332f9097c3cbdfa5eed0f6e87b2cbd761eab0f4d87a2c3cf25e672f2a979143c6a1e250f0a8781bbbee1de70eea977143b6ddda52eca8760cbae25d5f2ea8775043a621d210e88873fcb9de1cdd2e668
|8,3=>0x9364498e64b5325199244c9022471123089144487e642d320d9902c47f263e731eb88f1c476e23a711ca98e1446ea236331a988d04c65e631f118698bf445da22dd116598aec4556229cf145989e4c4d222591123988d4c44de218f103987dc43ce21d710e3886dc434a619510c2885ccc2c9e15510a2884ccc242610f307e9
|9,0=>0xa3d4d1c668d1345f9a2c3d142288f343f8a1b4d0ba284d141e8a0b4503de80f13ff89fbc4fba67cd13de89ebbcf3e278f13bf89dbc4ebe274f139f89cbc4e3e270d337e89bb44dba26cb335c99aa44d322689133c8999cccaa6645131a898944c2a260512fa8978ccba625c312d989684cb22258112b799574ca9a253b32958946c4a1624f932748
|9,1=>0x535e699f14c69a5f452da295d14a59a4e4d252291734838
|10,0=>0x2a4f15207a8c454422a1115008a7c453c229d114e08
|11,0=>0x152f7
|_,_=>0
def wAt:=mkWire dB 127 224 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa11223d3a470a01183d223d2c08083d1a112201183d223d2c081a112201183d6e23082922011e010a113a0f0a01223d3a0f222910011e010a0126082211183d223d0c033a0f1a3d223d220118bd082a1e014e330a111e012201083d2c08183d1a113a6b222910011e011e010a68100122210a6b0a21223d2c331a111e012201
|1=>0x1a3d22010a111e012201223d183d0a6b100186031a91103d22013a0f0a01183d223d8a332c3f1a112201183d3a470a01223d223d18bd082a1e01860f22c9102910291e013a0f2229082a1e0188233a1122293a031a3d1c032291103d0a69223d1001222a190908aa222a1a232201183d223d10291e017c336c110a034e332201
|2=>0xa01183d223d1a131e012201223d0a6810010a215a2308a9222a23251a962201083d103d1e01226a100186038c3d226910010a032211183d223d883f3a1122291e01860f0a69223d221a3a0f1a3d2201220118bd082a1e011c030a21223d3a0f1a3d1a11220186231c010a21223d0a681e01223d100188333a110a013a0f3a47
|3=>0x1001880f3a110a011e010a232201223d223d234274010a13223d2628223d22111e01860f1a91103d3a0f22291e0122011e010a13223d2c3f1a11220188232c3d1a110a012221183d223d0801183d2296083d1c030a21223d2269223d10010a211e01223d100108193a0f0a01223d1a111e012201223d860322c9343d10013a0f
|4=>0x223d3a0f0a01223d1e010b380801223d0b490a6a223d10012c3f1a11220110012221183d223dac2a233a080122213a0f1a3d2201a816260322111a211e012201223d1a3d220122de082922291e010a03183d223d3a110a01183d223d22010a21183d223d6c110a03183d223d22291001103d1e012201183d223da43d0a6a223d
|5=>0x102a1e012201223db20322fd102a1e01183d0a01223d22210a23183d223d0a014e030a11223d0a6b223d1001083d183d1a1122010a110a01183d223d6c210a03183d6e23082922011e01221a3a0f0a01223d2c331a3d1a11220120033a2322291e013a0f3a470a01223d6e2308291e01223d223d102922011e011e011a232201
|6=>0x2c331a112201183d0a01223d2201223d082a1e010a130a01183d223d22291e010c033a0f0a01223d1a212201103d1e013a0f0a01223d8a332c3f1a1188333a110a01223d860f1c010a213a032229222a1e011601183d223d88233a110a01183d4e030a11223d0a681001183d223d2c081a112201183d1c030a21223d0a032211
|7=>0x10016c213a03222922211e01223d10013a110a01223d183d233a0801083d4e330a010a11223d1601223d223d102a1e0122010a21223d3a0f0a01223d0a031a111e012201223d22213a0f0a01223d88331a952201083d3a0f0a030a01223d0a01223db20f22fd102a1e013a032229222a1e01883f3a110a01223d0a21183d223d
|8=>0x223d0a011c030a21223d0a012211183d223d10013a0f22291e0188033a1122291e010801222a3a2322291e0186230a69223d10011a212201183d223d880f1a952201083d22011e010a23223d22de08291e01223d082922011e016c210a03223d102a223d0b380801183d223d223d7c336c110a0322de08291e0123490a6a223d
|9=>0x223d32010a6b223d1001b20f22fd102a1e0186230a69223d1001bc0322bd082a1e01183d1c030a2188472c3d1a112201102922291e014e030a11223d0a681e01223d10013a0322292c331e011a11220110650a6b223d100108013a0f22291e01221a3a0f0a01223d223d3a0f0a010a11223d3a0f2229222a1e010a032221183d
|10=>0x183d223d3a033a0f22291e012c33223d1a1122013a210a01223d2c08183d1a1188233a110a01223d0a21223d0a031e01222918bd082a1e01c633c4111a3f220132010a6b223d10010c033a0f22291e0122291e0126082211183d223d88333a1122291e01103d22691001c03d0b3a0801223d10650a6b223d10010a032201183d
|11=>0x2201183d223d88332c3d1a113a473a031a3d22013a0f0a01223d860f0a69223d10011a213a231a3d2201880f3a1122292a3d2c331a110a01223d2608083d2211183d2c3f1a3d1a11220188231a952201083d183d0a030a11223d4e030a11223d0a210a6b223d1a212201103d0a112201183d223d88032c3d1a1122010a010a21
|12=>0x2201103d3a0f22291e0188473a110a01223d0a132201183d223d5a2308a9222a1e011c031c010a21223d3a0f3a110a01223d22291e0122691e01223d1001223d183d226910010b381e010801223d0c033a0f1a3d2201223d1a112201183d10293a2322291e0122212201103d1e01ca3d262b22111e014e331e010a11223d1a13
|13=>0x83d1a112201183d2628223d22111e01880f2c3d1a111c010a21183d223d86030a69223d10016e23082922291e0122fd102a1e011c030a21223d3a0f0a012211223d92011a962201083d74010a13183d223d0a6810012221223d0a232201183d223d0a0322211e010a212201223d3a0f3a031a3d2201860322c910291e01102a
|14=>0x801183d223d100122211e010a012221223d6c130a03223d08012296083d0a23223d2269103d1001d233263f22111001183d223d22ca343d10010a03223d6e2308291e012c331a1122011e011a1122013a0f0a01223d3a231a3d220118bd082a1e010a032211223d0a11183d223d1e010a21223d1a962201083d2201183d223d
|15=>0x2221223d8e3d226a1001262b22111e010801222a1e010a030a21223d44012221183d3a110a01223d082922011e010a030a01223d22010a21223d0a23183d223d3a131a3d22016c110a03223d223d1a1122010a6a1001183d2296083d0a13183d223d1e010a23223d22de08291e0108291e01223d1e01226a100122fd102a1e01
|16=>0x1e013a230a01223d6e2308291e010a232221223d0b3a0801223d2221183d223d080122291e01083d1a11220174010a13223d09b21009183d0a010a11223d0a232201223d6c210a03223d26082211183d1e01233a080122291e0110013a210a01223d223d26032211a83d260322114e330a11223d0a03183d223d222a1e011001
|17=>0xa01223d10010a21223d3a130a01223d1e010801223d3a0322291e012221103d1e010a010a13223d08a9222a1e01103d226910011e01223d100123b54a03083d102922211e01083d2603221116010a23223d1001103d1e0122bd082a1e014e030a11223d2229222a1e010a68223d10010a69223d1001223d22111e0108aa222a
|18=>0x1e010a03223d222910291e010a21183d223d3a0f0a01223d2c3f1a112201233a0801083d803d1a2322011a21103d22011a211a3d22011a2122011e013a0322291e01183d226910010a11183d223d2291103d1e012c331a1122011a112201183d0a6b223d1001183d1a1322012c331a112201262b22111e013a0f0a01223d0a23
|19=>0x83d08a9222a1e010a032221223d0a212201223d6c110a03223d102a22291e010a6a223d1001183d1a2322010a012211223d222110291e010a13183d223d44012221223d22bd082a1e011a212201183d262822111e013a031a3d220122c910291e010b380801223d2229103d1e0122012221103d0a012221223d3a110a01223d
|20=>0x343d10011a962201083d083d0801183d1a972201083d223d222a1e012229082a1e01c4111a3f22014e330a11223d3a230a01223d0a032201223d3a0f22291e01343d222110011c030a21223d2201183d223d22012221183d22fd102a1e013a031a3d2201102a1e0110011e010a11223d23bd343f10010a69223d10011a952201
|21=>0xa01223d222922211e0122010a11223d1e010a23223d1e01226910018c3d22691001222a1e010a010a21223d1e010a13223d1a3d1a1122011a1122011e013a230a01223d3a471a3d2201ac3d233a0801222a22011e011a1322011e013a0f22291e011c030a21223d0a6b223d1a91103d22016c210a03223d2201103d1e016423
|22=>0x223d10291e010a21223d1001082922291e013a130a01223d1a112201223d3a1122291e01183d1a1122011a132201223d2c331a1122013a0f1a3d2201103d226a10013a471a3d22011a942201083d22c9343d1001262822111e0116010a23223d0a01183d223d0a030a11223d4e030a11223d0a68223d10012211183d223d3a13
|23=>0x1e01102a103d1e0174010a13223d0a232201223dea3d26332211083d2211183d102922011e01183d226a1001e6032209183d1a2322011e0110fd102a1e011e012221223d22010a13223d22211a3f22013a0f1a3d22012c3f1a11220118bd082a1e0110012221183d343f222110012269223d10011a2122011e0122fd102a1e01
|24=>0x1a3f2201963d1a1322010b380801223d102a22011e0122fe102a1e011e01263322113a470a01223d22de08291e013a2322291e011a212201223d1a112201083d1c010a21223d4a032211083d10a9222a1e019a012296083d223d102a1e010a230a21223d1a93103d22011e012201223d1a3d222122010b3a0801223d22212201
|25=>0x1e010801183d0a23223d2296083d0a01223d183d10010a13223d343f10011c030a21223d3a1322291e01082a22011e010a6b223d10013a0f0a01223d3a470a01223d0a032221223d233a0801183d8c3f226910016c110a03223d1c010a21223d223d082a1e01183d2201083d343d226910012c3d1a1122011a232201223dc421
|26=>0x183d226910010a03223d2201223d0a23223d0a13223d1a3d220122011e011e01223d1a3f22010a21223d22211e0108011e010a11223d233a08011e011001103d220122291e012211183d1009183d2603221126332211226a100122211001222a1e012221223d0809183d2209183d1a1122012201183d263f22110a03223d0829
|27=>0x1e01103d100122212201082a1e010a11223d1a2322011a21220108291e012201083d102a1e01343d100122111e01183d223d2221183d226910010a21223d10291e011a1122011a1322012211083d082a1e01263322112221103d221108014a03083d0a01223d102a1e012211223d083d183d103d1e01343d10010801083d0401
|28=>0x103d183d223d2211083d2201080110011e0122210801223d9c3f0801223d1001222a
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0xc1400000000000000000002c400000a1000000000000000000000000000000012201f5000000000e18000000000000d8817400000000000000000000000000000000000000000013401e802d003a0000000000000000000000000000000043000000000020000000000000000000
|6,1=>0xd540000000
|7,0=>0x1fe83f0c7c20f711e683bd07618e931ca8388c6f98db41ae8350c6898cd41928315060a000017a82e505b18b3300002bd055a0a74146827d04e180001308251048988d41128215041187e40f481dcc39a06f40d6819d031a06030bc416902b985520a4613cc2708000096611d022900000000108c1f203a4
|7,1=>0x38e870d00001c0300006f4cdd19b6436486c08d621a8434a6688ccf219b332e8650cc89800031a86250c2a182330040000be217842ea65c5000016d42d465990b1215f32b6855d0a9a14f4296851d0a1a13f427864e109a2131325a84a8c0001264246647d08e9119422c644908720000214841908198000
|7,2=>0x50e8a0d13fa27b44ee89cd137a26c34d08994d311a5e44b8496112a22504498892c523a000048688fd11da23744668000117a22d24546899111221e4434885cd09a210341c4000000020a44122818d0199ff43f867e10fa99f143da87ac8f509e9100000000f2a1e233c227750eca00003aa87450e791cb4
|7,3=>0x6928d150000341467e4ced19ba333465e8cad193a32526428c75000000000000c6518aa311461a8c25182a30145fa8be8d7b200005e66bbd175a2e835ca6b8c96fa2db45ae8b4d1681acd35946000163200005848af915d22b6400000001599ab030000ab115512a825488a8114e2298452c4a491479a8b4
|7,4=>0x38036f88de11ba9b7146da8da51b31b6330000d7d000035b46ae8d4d1a7a34d2
|8,0=>0x87870e4e1b1c33386070b4e151c2738487084e0f1c1b38307054e091c0f38187024e031c0338024ff8dfd9bf837ea6fc8df79bec37d26f98df19be037ba6f68deb9bd527a46f3cde61bc9378c6f0cde01bbd37746edcdda1bb1375e4eb0dd49ba637466e849cf1b9b37306e54dc91b8f37186e24dc31b833
|8,1=>0x9f873e4e7b1cf339e073b4e751ce739c87384e6f1cdb39b07354e691ccf39987324e631cc3398072f4e5d1cb7396872c4e571cab39507294e511c9f39387264e4b1c9339207234e451c8739087204e3f1c7b38f071d4e391c6f38d871a4e331c6338c07174e2d1c5738a87144e271c4b38907114e211c3f3
|8,2=>0xb7476dceda1db13b5c76aced41da53b44767cece1d993b2c764cec81d8d3b14761cec21d813afc75ecebc1d753ae475bceb6956a3ace7590eb09d5e3ab67560eaa9d523a9e7530ea515473a887504e9f1d3b3a7074d4e991d2f3a5874a4e931d233a407474e8d1d173a287444e871d0b3a107414e811cff3
|8,3=>0xcdc79acf341e653cc4797cf2e1e593cac794cf281e4d3c94791cf221e413c7c78ecf1c1e353c6478bcf161e293c4c788cf101e1d3c34785cf0a1e113c1c782cf041e053c0477fcefe1df93bec77ccef81ded3bd4779cef21de13bbc776ceec1dd53ba4773cee61dc93b8c770cee01dbd3
|9,0=>0xdde5bb4b7596e92dce5b94b7196e12dbe5b74b6d96d92dae5b54b6996d12d9e5b34b6596c92d8e5b14b6196c12d7e5af4b5d96b92d6e5ad4b5996b12d5e5ab4b5596a92d4e5a94b5196a12d3e5a74b4d96992d2e5a54b4996912d1e5a34b4596892d0e5a14b4196812cfe59f4b3d96792cee59d4b3996712
|9,1=>0x1c14b8197012dfe5bf4b7d96f92dee5bd4b7996f12
|10,0=>0x3880f0f1e1c3c347860f0b1e143c247840f071
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 15
def pmP:Nat→Nat
|0=>0x2800000000900000000210000000080000000016c00000004400000000d800000003400000000c800000003000000000b8000000028000000009000000002200000000840000000200000000064000000016000000004c0000000120000000044000000010000000003000000000a00000000240000000080000000018000000004000000000c0000000020000000004000000000
|1=>0x6004000001800000000405800000101000000040040000010000000003efc000000f7f0000003ab8000000e7f0000002efc000000b3f0000002afc000000a7f00000028fc000000a01000000215c00000083500000020500000008130000002048000000810000000200000000033f0000000ce8000000200000000060800000013200000004a800000011000000004000000000b7
|2=>0xaafc000002a3f0000008cfc0000022bf0000008af80000022ac0000008a3800000213200000082d80000020b4000000829800000208200000080900000020040000008008000001a7f00000068fc000001a1e0000006828000001a09000000680000000181e000000606c0000018170000006058000001814000000604800000180d00000060300000018080000006018000001804
|3=>0x239fc000008abf00000228fc00000883f0000020ee000000839a0000020bf00000081b2000002068800000811000000202880000080a0000002020000000803a00000200c800000802e000002008000000801f000002006c00000801a00000200600000080120000020038000008008000002000c000008001000002000000000420900000100500000040100000010008000002b3f
|4=>0x48000000011a3f0000046018000010abf0000042aec000010a3f00000428ac00001083f000004204000001033e000004048800001010000000400d800001003400000400c0000010020000004007c0000100100000040034000010004000004000000000aabf000002a8fc00000a26e00000288fc00000a22e00000286c800000a11000000268fc00000981c0000026068000008fff
|5=>0x2868fc00008c80000002128fc000081a3f0000206800000080219000020005000008001000002000240000800040000200008000041a6f0000106050000028a3f000009287c000021a3f00000860580000210100000084008000020a6f00000828fc000020a1f000008000800001887f00000620fc00001801f000006003c000012aff000004aafc00001229b00000482d8000012004
|6=>0x8000f800020003200008000b000020002a00008000a0000200026000080008000020000800008000040001a9a3f00006a20480001a08030000632008000188a3f0000622054000188813000060204c00018080200004868fc000121a1f00004828fc000120a1f000042687c000109a190000406004000100a3f000040082c000100010000040002000010000200002928fc0000a4a1f
|7=>0x10828fc000408a1f000102283c000400a3f000100201800040020b000100001000040000200010000000002100260000828a2000020a23e0000822afc000208a3f00008202c800020803c000080acfc000202a3f0000808cb80002022be00008086c800020213200008084980002021160000808028000200b3f0000802afc000200a3f0000800efc00020033f0000800cf8000200188
|8=>0x40200e800100801b000400ac7400100223d00040068fc0010018120004002cf4001000a7f00040028fc0010008100004000cf400100008a00040000d8001000030000400004000100000a0004000010000521a3f00014068fc000501a120001406818000500a1200014020fc00050081200012068fc000481817000120601c000480817000120205800048081500010a28fc000421a3f
|9=>0x180829fc004c20a6f0012082838004481a7f00110869bc004420a7f0011022938004121a7f00104829fc00410da7f00102028fc004024a7f00100869fc004020a4e001008097800400ca3f0010026970004008a7f001000004000248180200080421fc001a1001f000484007c00120801f000482007400120801b000480acfc001200a3f00048020fc00120001f000404007c00100883f
|10=>0x1100969fc042008a7f0100023afc040008a7f0100003bfc040000a7f00902868fc024080a3f00900868fc024004a3f00900028fc024000a3e008000204801000020100208028fc00820010a00208000c8008200028002080006000820000c00208000280082000090020800004008008bbf0020020efc0080081b400200206c800800819600200028fc00800009800200000e8008000001
|11=>0xa3000029fd940000a7f21180039fc804800e7f20100031fc60000083f05100969fc104021a6f04000469fc0c400087f0300003bfc080010a7f
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x68000000000000000068000000000000c000040000000000000000002c0900000040000000420c00000000000000000000000000c010583c00000000000000000004000001800000000000
|7,0=>0x780c0052004b47c2c031d0d07a080080c023436404007d8385e1d1e00033126ca64003b113388851061ac0c1601814b086149380cb81b8280013311e0203b08190a600961c97c00018082e214b914042615b1004dd9e874ec5918321ae000dbf4040a0000ddb405982c2000048303a0100b7cc267820300609a9ca80a0a12804147329019ee0005220a80000029728d
|7,1=>0x2d19d160b8884c062d06d2aa4103d9d4000000118112f6bbd416059c808d4000802e800a01041583b058fd6c044200204000184c1663000000c0200018a402030a8026b0fad01478018051e110b0462c5101849f2184f830222a34084021c332480e430b000163c37d24f20b13b0a14a087994003d10ad5f003053800d320324128650027cae107bb402c0005998202e
|7,2=>0x749892804d8088180c52000a8740320081228e
|8,0=>0x8624cb84f8a0d0fe8275d928f1a3b93cdb42579c114f22623db8a418ac1547d42d068f213bcecb6d49b0c65d56571f0465520b323cec6193e88e17e3bd62f677aae07270cd45604f6d42536c6b0a05aaabb111050a128328e54e602f66b2b258d468bc23a5500c5851b4ad6022c19a2029f58d2d0885b8a213371bc09eaa4651eb03672242cd57681f1bd1823cf0aaa9
|8,1=>0x18914582434ca53937a18fe98489d53df4873eaac9f138bd514aab38d19555055c5df913511f4faf056bce389d4955668ea1c59d0f1d728b4fc7c67d5472353c5163ee92e1349ec95d34dfd30361764c31a5abd34a863aac6365213c60493a2d35761523925923136b1a50fe3e15c20e74d3d232fc9faae44b741d55b6a6363a0af5eaec5cdd15828d028ab
|9,0=>0x3359a3492180fd1b839f6910e80c5ddeb0ad56e905f92b5964ab58554beb07fa9e2eb09d3b9deabb4d21347d4d2c0f87d189f546e566c0196e644c82bf6b60d646835918ced568695717e9886ce134ff3e8e13c34
|10,0=>0xbc3218afdfe7d658d06233
|11,0=>0x31
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 38 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_222 10 roots_222 ops++addP pm 1 dom_207 9 roots_207 ops++addP pm 2 dom_95 9 roots_95 ops++addP pm 3 dom_219 10 roots_219 ops++addP pm 4 dom_159 9 roots_159 ops++addP pm 5 dom_221 9 roots_221 ops++addP pm 6 dom_158 7 roots_158 ops++addP pm 7 dom_205 7 roots_205 ops++addP pm 8 dom_93 6 roots_93 ops++addP pm 9 dom_213 8 roots_213 ops++addP pm 10 dzo_220_1 6 roots_220 ops++addP pm 11 dom_215 9 roots_215 ops++addP pm 12 dzo_151_8 6 roots_151 ops++addP pm 13 dom_157 7 roots_157 ops++addP pm 14 dzo_198_1 5 roots_198 ops++addP pm 15 dom_79 6 roots_79 ops++addP pm 16 dom_143 5 roots_143 ops++addP pm 17 dzo_215_8 7 roots_215 ops++addP pm 18 dom_142 4 roots_142 ops++addP pm 19 dom_198 5 roots_198 ops++addP pm 20 dom_87 6 roots_87 ops++addP pm 21 dom_29 4 roots_29 ops++addP pm 22 dom_151 6 roots_151 ops++addP pm 23 dom_206 7 roots_206 ops++addP pm 24 dom_31 5 roots_31 ops++addP pm 25 dom_94 8 roots_94 ops++addP pm 26 dzo_214_1 6 roots_214 ops++addP pm 27 dom_77 4 roots_77 ops++addP pm 28 dom_211 7 roots_211 ops++addP pm 29 dzo_214_8 6 roots_214 ops++addP pm 30 dzo_206_1 6 roots_206 ops++addP pm 31 dom_220 8 roots_220 ops++addP pm 32 dom_214 8 roots_214 ops++addP pm 33 dzo_213_8 6 roots_213 ops++addP pm 34 dzo_149_8 5 roots_149 ops++addP pm 35 dzo_222_1 7 roots_222 ops++addP pm 36 dom_150 5 roots_150 ops++addP pm 37 dom_148 4 roots_148 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_223 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_220_1_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_151_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_198_1_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_215_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_214_1_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_214_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_206_1_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_213_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_149_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_222_1_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_148 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_222 10 s (0,roots_222.map (·&&&dom_222)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_223 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_222 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_223 gM v ys):RunD true dom_223 gM v (ori ys):=h
def Z (s:Nat):=barP dom_223 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 67 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 67 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 273 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 17 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 273 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 252 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 124 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 252 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 75 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 75 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 10 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_223 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def gzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000e0a0000
def gsh_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000e0a
theorem lowS_zo_235_16_42:Lower true dzo_235_16 roots_235 gzo_235_16 7:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_16) [(dom_235,16)] (by decide +kernel) (lower_slice_b (T:=gsh_235_16) [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000,0,64),(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_250_1:=0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def gzo_250_1:=0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a080a0a0a0a0a0a0a080a0a0a0a0a0a0a00
def gsh_250_1:=0x505050505050505050505050505050405050505050505040505050505050500
theorem lowS_zo_250_1_194:Lower true dzo_250_1 roots_250 gzo_250_1 7:=lower_iso_b (d1:=dom_250) (r1:=roots_250) (T1:=gsh_250_1) [(dom_250,1)] (by decide +kernel) (lower_slice_b (T:=gsh_250_1) [(0x500050005000500050005000500050005000500050005000500050005000500,0,8),(0x505000005050000050500000505000005050000050500000505000005050000,0,16),(0x505050500000000050505050000000005050505000000000505050500000000,0,32)] (by decide +kernel) lowS_194)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,10),(8,40),(8,72),(16,17),(16,80),(16,144),(18,19),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,160),(48,49),(48,50),(48,56),(48,112),(48,176),(64,66),(64,72),(64,80),(64,192),(65,67),(65,73),(65,81),(65,97),(65,193),(96,97),(96,98),(96,104),(96,112),(96,224),(128,130),(128,144),(128,160),(128,192),(129,131),(129,137),(129,145),(129,161),(129,193),(136,137),(136,138),(136,152),(136,168),(136,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|9=>4
|10=>2
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0xcaf43bdd972d3af175c1
|10,0=>0x527d9502c6
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ef0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a303020203030202030302020303020203030202030302020303020203030202505040405050404050504040505040405050404050504040505040405050404f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0ef0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x7543210785432107b5432107854c21075432a107543291076543210
|_=>0
def sO:Nat→Nat→Nat
|9,0=>0x6210822008
|10,0=>0xa2208
|11,0=>0x307
|_,_=>0
def wAt:=mkWire dB 13 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x35549324d5b3d4982cd5824d5
|_=>0
def oO:Nat→Nat→Nat
|9,0=>0x62422202
|10,0=>0x9181
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xcbf4bf3bf1ff0ff0bf000
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>0x952
|10,0=>0x1e
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_243 10 roots_243 ops++addP pm 1 dom_187 10 roots_187 ops++addP pm 2 dom_123 10 roots_123 ops++addP pm 3 dom_219 10 roots_219 ops++addP pm 4 dom_250 9 roots_250 ops++addP pm 5 dom_235 9 roots_235 ops++addP pm 6 dzo_235_16 7 roots_235 ops++addP pm 7 dom_249 9 roots_249 ops++addP pm 8 dom_233 6 roots_233 ops++addP pm 9 dom_248 6 roots_248 ops++addP pm 10 dzo_250_1 7 roots_250 ops++addP pm 11 dom_234 6 roots_234 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_235_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_250_1_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_234 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_243 10 s (0,roots_243.map (·&&&dom_243)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_243 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
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
def dzo_169_4:=0x30300000303000000000000000000000303000003030
def gzo_169_4:=0x30300000303000000000000000000000302000002000
def gsh_169_4:=0x3030000030300000000000000000000030200000200
theorem lowS_zo_169_4_41:Lower true dzo_169_4 roots_169 gzo_169_4 5:=lower_iso_b (d1:=dom_169) (r1:=roots_169) (T1:=gsh_169_4) [(dom_169,4)] (by decide +kernel) (lower_slice_b (T:=gsh_169_4) [(0x3030000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_233_4:=0x303000003030000030300000303000003030000030300000303000003030
def gzo_233_4:=0x303000003030000030300000303000003030000030300000302000002000
def gsh_233_4:=0x30300000303000003030000030300000303000003030000030200000200
theorem lowS_zo_233_4_41:Lower true dzo_233_4 roots_233 gzo_233_4 6:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_4) [(dom_233,4)] (by decide +kernel) (lower_slice_b (T:=gsh_233_4) [(0x30300000303000000000000000000000303000003030000000000000000,0,64),(0x30300000303000003030000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_249_4:=0x3030303030303030303030303030303030303030303030303030303030303030
def gzo_249_4:=0x3030303030303030303030303030303030303030303030303030302030302000
def gsh_249_4:=0x303030303030303030303030303030303030303030303030303030203030200
theorem lowS_zo_249_4_41:Lower true dzo_249_4 roots_249 gzo_249_4 7:=lower_iso_b (d1:=dom_249) (r1:=roots_249) (T1:=gsh_249_4) [(dom_249,4)] (by decide +kernel) (lower_slice_b (T:=gsh_249_4) [(0x303000003030000030300000303000003030000030300000303000003030000,0,16),(0x303030303030303000000000000000003030303030303030000000000000000,0,64),(0x303030303030303030303030303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_245_8:=0x3300330033003300330033003300330033003300330033003300330033003300
def gzo_245_8:=0x3300330033003300330033003300320033003300330033003300330032002200
def gsh_245_8:=0x33003300330033003300330033003200330033003300330033003300320022
theorem lowS_zo_245_8_148:Lower true dzo_245_8 roots_245 gzo_245_8 7:=lower_iso_b (d1:=dom_245) (r1:=roots_245) (T1:=gsh_245_8) [(dom_245,8)] (by decide +kernel) (lower_slice_b (T:=gsh_245_8) [(0x22002200220022002200220022002200220022002200220022002200220022,0,1),(0x33003300000000003300330000000000330033000000000033003300000000,0,32),(0x33003300330033000000000000000000330033003300330000000000000000,0,64)] (by decide +kernel) lowS_148)
def dzo_252_1:=0x2222222222222222222222222222222222222222222222222222222222222222
def gzo_252_1:=0x2222222222222222222222222222222022222222222222202222222222222200
def gsh_252_1:=0x1111111111111111111111111111111011111111111111101111111111111100
theorem lowS_zo_252_1_196:Lower true dzo_252_1 roots_252 gzo_252_1 7:=lower_iso_b (d1:=dom_252) (r1:=roots_252) (T1:=gsh_252_1) [(dom_252,1)] (by decide +kernel) (lower_slice_b (T:=gsh_252_1) [(0x1100110011001100110011001100110011001100110011001100110011001100,0,8),(0x1111000011110000111100001111000011110000111100001111000011110000,0,16),(0x1111111100000000111111110000000011111111000000001111111100000000,0,32)] (by decide +kernel) lowS_196)
def dzo_236_1:=0x222200002222000022220000222200002222000022220000222200002222
def gzo_236_1:=0x222200002222000022220000222000002222000022200000222200002200
def gsh_236_1:=0x111100001111000011110000111000001111000011100000111100001100
theorem lowS_zo_236_1_196:Lower true dzo_236_1 roots_236 gzo_236_1 6:=lower_iso_b (d1:=dom_236) (r1:=roots_236) (T1:=gsh_236_1) [(dom_236,1)] (by decide +kernel) (lower_slice_b (T:=gsh_236_1) [(0x110000001100000011000000110000001100000011000000110000001100,0,8),(0x111100000000000011110000000000001111000000000000111100000000,0,32)] (by decide +kernel) lowS_196)
def dzo_181_8:=0x330033003300330000000000000000003300330033003300
def gzo_181_8:=0x330033003300320000000000000000003300330032002200
def gsh_181_8:=0x3300330033003200000000000000000033003300320022
theorem lowS_zo_181_8_148:Lower true dzo_181_8 roots_181 gzo_181_8 6:=lower_iso_b (d1:=dom_181) (r1:=roots_181) (T1:=gsh_181_8) [(dom_181,8)] (by decide +kernel) (lower_slice_b (T:=gsh_181_8) [(0x2200220022002200000000000000000022002200220022,0,1),(0x3300330000000000000000000000000033003300000000,0,32)] (by decide +kernel) lowS_148)
def dzo_221_32:=0x3333333300000000333333330000000033333333000000003333333300000000
def gzo_221_32:=0x3333333300000000333333330000000033333332000000003332332200000000
def gsh_221_32:=0x33333333000000003333333300000000333333320000000033323322
theorem lowS_zo_221_32_84:Lower true dzo_221_32 roots_221 gzo_221_32 7:=lower_iso_b (d1:=dom_221) (r1:=roots_221) (T1:=gsh_221_32) [(dom_221,32)] (by decide +kernel) (lower_slice_b (T:=gsh_221_32) [(0x22222222000000002222222200000000222222220000000022222222,0,1),(0x33003300000000003300330000000000330033000000000033003300,0,8),(0x33333333000000003333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_105_4:=0x3030000030300000303000003030
def gzo_105_4:=0x3030000030300000302000002000
def gsh_105_4:=0x303000003030000030200000200
theorem lowS_zo_105_4_41:Lower true dzo_105_4 roots_105 gzo_105_4 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_4) [(dom_105,4)] (by decide +kernel) (lower_slice_b (T:=gsh_105_4) [(0x303000003030000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_185_4:=0x303030303030303000000000000000003030303030303030
def gzo_185_4:=0x303030303030303000000000000000003030302030302000
def gsh_185_4:=0x30303030303030300000000000000000303030203030200
theorem lowS_zo_185_4_41:Lower true dzo_185_4 roots_185 gzo_185_4 6:=lower_iso_b (d1:=dom_185) (r1:=roots_185) (T1:=gsh_185_4) [(dom_185,4)] (by decide +kernel) (lower_slice_b (T:=gsh_185_4) [(0x30300000303000000000000000000000303000003030000,0,16),(0x30303030303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
namespace S_253
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(4,20),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,40),(8,72),(12,13),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(24,25),(24,28),(24,56),(24,88),(24,152),(32,33),(32,40),(32,160),(36,37),(36,44),(36,52),(36,100),(36,164),(48,49),(48,52),(48,56),(48,112),(48,176),(64,68),(64,72),(64,80),(64,192),(65,69),(65,73),(65,81),(65,97),(65,193),(96,97),(96,100),(96,104),(96,112),(96,224),(128,132),(128,144),(128,160),(128,192),(129,133),(129,137),(129,145),(129,161),(129,193),(136,137),(136,140),(136,152),(136,168),(136,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1fffffffffffffffff
def xsM:=roots_253.map (·&&&dom_253)
def gM:=goal_253&&&dom_253
def NN:Nat→Nat
|7=>2
|8=>15
|9=>27
|10=>6
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x12b3103594
|8,0=>0xe060387e766117b5efa357ff349f5f30ea428e50252801717616a270df060bfb20b99d097f9
|9,0=>0x9dfcd7d88a710486590c5e4d557a81548a0506e44de494981f3c7483ae09334ee32d09252ec1abe01414812fca11d850ebf00e3250d549075ab0629b0559a01ee90021e
|10,0=>0x7762c47063460ee206101e31b0a7a6
|11,0=>0x1e31b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccc0000cccc0000cc000000cc03333333333333333333333333333333333333300333333003333330033333300cccccccccccccccccc00cc00cc00cc00cccccccccccccccccc00cc00cc00cc03333333333333333333333333333333333333333333333332222222222222222cccccccccccccccccccc0000cccc0000cccccccccccccccccccc0000cccc0003333333333333333333333333333000033333333333333333333333333330000cccccccccccccccccccccccccccccccccccc0000cccc0000cccc0000cccc0003030303030303030303030303030303030303030303030303030303030303030cccccccccccccccccccccccccccccccccccccccccccccccc0000000000000003333333300000000333333330000000033333333000000003333333300000000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc00033003300330033003300330033003300330033003300330033003300330033008888888888888888888888888888888888888888888888888888888888888888303030303030303030303030303030303030303030303030303030003030300cccccccccccccccc0000000000000000cccccccccccccccc0000000000000003333333333333333333333333333333300000000000000000000000000000000
|0,1=>0xcccccccccccccccccccccccccccccccccccccccccccccccccccc8888cccc888b33333333333333333333300333333003333333333333333333333003333330000000000000000000000000000000000cccccccccccccccccccccc00cccccc03333333333333333000000000000000033333333333333333333222233332222ccccc0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c0000000000000000000000000000000033333030333330303333303033333030cccccccccccccccccccccccccccccccccc00cc00cc00cc00cc00cc00cc00cc033333333333333333333333333333333333333333333333333330000333300000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c0000000000000000000000000000000000033333333333333333333333333330000cccc8888cccc8888cccc8888cccc8888cccc8888cccc8888cccc8888cccc8888000000000000000000000000000000033332222333322223333222233332222cccccccccccccccc8888888888888888cccccccccccccccc888888888888888b333333333330000333333333333000033333333333300003333333333330000ccccccccccccccccccccccccccccccccc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c3333330033333300333333003333330033333300333333003333330033333300
|0,2=>0xccccccccc0c0c0c0ccccccccc0c0c0c3333333333333333333330303333303033333333333333333333303033333030cccccccccccccccccccccccccccccccccccccccc00000000cccccccc0000000333332323333323233333232333332323333323233333232333332323333323200cc00cc00cc00cc00c000c000c000c000cc00cc00cc00cc00c000c000c000c0000000033333333000000003030303000000000333333330000000030303030cccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000003330333033303330333033303330333033303330333033303330333033303330ccccccccc0c0c0c0ccccccccc0c0c0c0ccccccccc0c0c0c0ccccccccc0c0c0c0000333300003030000033330000303000003333000030300000333300003030ccccccccccccccccc8c8c8c8c8c8c8c8ccccccccccccccccc8c8c8c8c8c8c8c8000333300003333000030300000303000003333000033330000303000003030c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8000000000000000333322223333222200000000000000003333222233332222c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c00003333333333333333303030303030303033333333333333333030303030303030
|0,3=>0x303030303030303030303030303030303030303000000000303030300000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1210c10062c91080c71851204431c67c51080c10067451080c10067051080c10066856442030461440d70405861442030401941442130404862444480c11902c42031c01851080cf04018e14d20304018914420c0c12862442031c61440c2040
|1=>0x66c5344203040a462451080c10061448080c70061681200c100614420398100640512020304019e1442030402861442030401851252030404861448080c10061442039010065451232010062c51084c30068851080c1006245344203040185
|2=>0x401851232030404861442030401851080c10066c51080c10062c51080c7012a451080c1006144203c0102f1851080c10066c51200c1006b851080c10066051080c1029b451080c1006b051080c1006144203ac1006144203a810061686480c1
|3=>0x61442030401851080c7040185344203
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xee007
|8,0=>0x1edce8e6d732c1760ab04d82338fa06d02e813407a02d00e8
|9,0=>0x55e29f14789fc4de25f12788fc45e21f10787fc3da5db2e586ec3561992c485e42d21572a384dc24e1170829
|10,0=>0x30d17e8bb45ba2cef5f8
|11,0=>0x18e7
|_,_=>0
def wAt:=mkWire dB 49 254 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x45600d2014615201601720143210c5430514155070c54501101582014741011404505001400520148011d541010c55e03345440550155030c5406e1004815608c51d0404a0318b41150c155030c5402118540150404415045493614044052444501101431d1404101001462d0054115
|1=>0x4044052034615205450500146051856d23180409e20648052055b05205451d04046051805b0d2056013201601b20144012044405205411900541012014811201671720644152014d15101462d
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x2000
|8,0=>0xb8d59a834a688cf99c332658c999031a628c39843
|9,0=>0x194b19612be574ad9592ae554a995129e534a594928e514a194127e4f49d93926e4d4999312
|10,0=>0x358ea1d23a0400671
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x200020bca50200000bce50102000bda70100000bfff0100000bdbf01000003cf70080080bc670070004b8850042004bca70030004bea70030004bca70010184fc270010004fca50008804fca70004810aee40003d008c470002800bca700020023df70001100be6700003808c670000280bc670000200bc670000072acc40000030bee50000020bce5000000f783e0000000fce70000000bcaf0000000bca700000003c21000000003fe00000000000
|1=>0x8402080bc674262024bca54011084bc272502004bce71400004fce71010004bcf70c24014fca50c200047caf0c18804bca70928004bca70828024bca50808004fca70482802bee70414064bca50402800bee70400802bee70400080bc670202022bce5
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x40
|8,0=>0x389264729815a30645e250
|9,0=>0x236eeb155a576f9e89303a94edac8714aa684d2e0
|10,0=>0x3dfc44097
|11,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 44 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_252 9 roots_252 ops++addP pm 1 dom_220 8 roots_220 ops++addP pm 2 dom_125 9 roots_125 ops++addP pm 3 dom_205 7 roots_205 ops++addP pm 4 dzo_93_32 6 roots_93 ops++addP pm 5 dom_221 9 roots_221 ops++addP pm 6 dzo_169_4 5 roots_169 ops++addP pm 7 dom_213 8 roots_213 ops++addP pm 8 dom_157 7 roots_157 ops++addP pm 9 dom_173 7 roots_173 ops++addP pm 10 dom_189 9 roots_189 ops++addP pm 11 dom_237 9 roots_237 ops++addP pm 12 dom_249 9 roots_249 ops++addP pm 13 dom_245 9 roots_245 ops++addP pm 14 dzo_233_4 6 roots_233 ops++addP pm 15 dom_244 8 roots_244 ops++addP pm 16 dom_105 5 roots_105 ops++addP pm 17 dom_109 7 roots_109 ops++addP pm 18 dzo_249_4 7 roots_249 ops++addP pm 19 dom_121 6 roots_121 ops++addP pm 20 dom_229 7 roots_229 ops++addP pm 21 dzo_245_8 7 roots_245 ops++addP pm 22 dom_117 7 roots_117 ops++addP pm 23 dzo_252_1 7 roots_252 ops++addP pm 24 dom_188 7 roots_188 ops++addP pm 25 dom_236 6 roots_236 ops++addP pm 26 dom_124 7 roots_124 ops++addP pm 27 dom_61 7 roots_61 ops++addP pm 28 dzo_236_1 6 roots_236 ops++addP pm 29 dzo_57_4 5 roots_57 ops++addP pm 30 dzo_181_8 6 roots_181 ops++addP pm 31 dom_57 5 roots_57 ops++addP pm 32 dzo_121_4 6 roots_121 ops++addP pm 33 dom_169 5 roots_169 ops++addP pm 34 dom_233 6 roots_233 ops++addP pm 35 dom_41 4 roots_41 ops++addP pm 36 dzo_221_32 7 roots_221 ops++addP pm 37 dom_181 6 roots_181 ops++addP pm 38 dzo_105_4 5 roots_105 ops++addP pm 39 dom_185 6 roots_185 ops++addP pm 40 dom_217 6 roots_217 ops++addP pm 41 dom_93 6 roots_93 ops++addP pm 42 dzo_185_4 6 roots_185 ops++addP pm 43 dom_248 6 roots_248 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_93_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_169_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_233_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_249_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_245_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_252_1_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_236_1_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_57_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_181_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_121_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_221_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_105_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_zo_185_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_248 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 9 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_253==dom_253)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_253 gM v ys):RunD true dom_253 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_253 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 15 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 27 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 27 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 6 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 6 0 = true)
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
  · exact z7 i (Nat.zero_le i) hi
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
def dzo_250_4:=0x5050505050505050505050505050505050505050505050505050505050505050
def gzo_250_4:=0x5050505050505050505050505050505050505050505050505050504050504000
def gsh_250_4:=0x505050505050505050505050505050505050505050505050505050405050400
theorem lowS_zo_250_4_42:Lower true dzo_250_4 roots_250 gzo_250_4 7:=lower_iso_b (d1:=dom_250) (r1:=roots_250) (T1:=gsh_250_4) [(dom_250,4)] (by decide +kernel) (lower_slice_b (T:=gsh_250_4) [(0x505000005050000050500000505000005050000050500000505000005050000,0,16),(0x505050505050505000000000000000005050505050505050000000000000000,0,64),(0x505050505050505050505050505050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
namespace S_254
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(2,130),(4,20),(4,68),(4,132),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(12,14),(12,28),(12,44),(12,76),(12,140),(16,20),(16,80),(16,144),(18,22),(18,26),(18,50),(18,82),(18,146),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,40),(32,160),(36,38),(36,44),(36,52),(36,100),(36,164),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,68),(64,72),(64,80),(64,192),(96,98),(96,100),(96,104),(96,112),(96,224),(128,130),(128,132),(128,144),(128,160),(128,192),(136,138),(136,140),(136,152),(136,168),(136,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|9=>4
|10=>2
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0xf3efc9668478d810d4d5
|10,0=>0x59fec1a434
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x555550505555505055555050555550505555505055555050555550505555505022222020222220202222202022222020222220202222202022222020222220200001515000015150000151500001515000015150000151500001515000015152aaaa2222aaaa2222aaaa2222aaaa2222aaaa2222aaaa2222aaaa2222aaaa2225454545454545454545454545454545454545454545454545454545454545454aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa000000015555515155555151555551515555515155555151555551515555515155555152aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80005500550055005500550055005500550055005500550055005500550055005500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a11111111111111111111111111111111111111111111111111111111111111112aaaaaaaaaaaaaaa80000000000000002aaaaaaaaaaaaaaa80000000000000005555555555555555555555555555555500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x75432107c5432107548321075432b1075432a107954831076543210
|_=>0
def sO:Nat→Nat→Nat
|9,0=>0x6210822008
|10,0=>0xa2208
|11,0=>0x307
|_,_=>0
def wAt:=mkWire dB 13 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x534c9c2d4d588c9524c9584c9
|_=>0
def oO:Nat→Nat→Nat
|9,0=>0x62422202
|10,0=>0x9181
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x27fbbf5fe3fc5f800
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>0x4a2
|10,0=>0x2b
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 11 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_246 10 roots_246 ops++addP pm 1 dom_190 10 roots_190 ops++addP pm 2 dom_126 10 roots_126 ops++addP pm 3 dom_222 10 roots_222 ops++addP pm 4 dom_252 9 roots_252 ops++addP pm 5 dom_250 9 roots_250 ops++addP pm 6 dzo_250_4 7 roots_250 ops++addP pm 7 dom_238 9 roots_238 ops++addP pm 8 dom_236 6 roots_236 ops++addP pm 9 dom_248 6 roots_248 ops++addP pm 10 dom_234 6 roots_234 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_250_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_234 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_246 10 s (0,roots_246.map (·&&&dom_246)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_246 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 4 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 2 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 2 0 = true)
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
def isoMvS_191:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_191:Lower true dom_191 roots_191 goal_191 12:=lower_iso_b isoMvS_191 (by decide +kernel) lowS_127
def isoMvS_247:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_247:Lower true dom_247 roots_247 goal_247 12:=lower_iso_b isoMvS_247 (by decide +kernel) lowS_223
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,40),(8,72),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,160),(36,37),(36,38),(36,44),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,68),(64,72),(64,80),(64,192),(65,67),(65,69),(65,73),(65,81),(65,97),(65,193),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,130),(128,132),(128,144),(128,160),(128,192),(129,131),(129,133),(129,137),(129,145),(129,161),(129,193),(136,137),(136,138),(136,140),(136,152),(136,168),(136,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffffffffffff
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
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_191 12 roots_191 ops++addP pm 2 dom_253 12 roots_253 ops++addP pm 3 dom_251 12 roots_251 ops++addP pm 4 dom_247 12 roots_247 ops++addP pm 5 dom_127 12 roots_127 ops++addP pm 6 dom_223 12 roots_223 ops
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
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_223 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.and, inputs := [9, 10] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [3, 5] }, { op := GateOp.and, inputs := [12, 13] }, { op := GateOp.or, inputs := [3, 7] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [15, 16] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [4, 18] }, { op := GateOp.or, inputs := [11, 14] }, { op := GateOp.or, inputs := [20, 17] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52406_aux

theorem PEqualNP.Outside.L_meta_52406 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52406_aux.main
