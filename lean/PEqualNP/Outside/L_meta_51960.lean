import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_51960_aux
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
def dom_50 : Nat := 0x5000500050005
def goal_50 : Nat := 0xffffcccccccc0000ffffcccccccc0000ffffcccccccc0000ffffcccccccc0000
def roots_50 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xffffcccccccc0000ffffcccccccc0000ffffcccccccc0000ffffcccccccc0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_52 : Nat := 0x11001100110011
def goal_52 : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000
def roots_52 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfffffcfcfcfc0000fffffcfcfcfc0000fffffcfcfcfc0000fffffcfcfcfc0000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfffffcfcfcfc0000fffffcfcfcfc0000fffffcfcfcfc0000fffffcfcfcfc0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffffcccccccc0000ffffcccccccc0000ffffcccccccc0000ffffcccccccc0000
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffffeecceeccaa00ffffeecceeccaa00ffffeecceeccaa00ffffeecceeccaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_60 : Nat := 0x1111111111111111
def goal_60 : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000
def roots_60 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffffaf0faf0aa00fffffaf0faf0aa00fffffaf0faf0aa00fffffaf0faf0aa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffffcfcfcfc0000fffffcfcfcfc0000fffffcfcfcfc0000fffffcfcfcfc0000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffffefcfefcaa00fffffefcfefcaa00fffffefcfefcaa00fffffefcfefcaa00
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

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xffffaaaaffffaaaaf0f00000f0f00000ffffaaaaffffaaaaf0f00000f0f00000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xffffccccffffccccfcfc0000fcfc0000ffffccccffffccccfcfc0000fcfc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xffffeeeeffffeeeefcfc0000fcfc0000ffffeeeeffffeeeefcfc0000fcfc0000
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

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xffffff00ffffff00f0f00000f0f00000ffffff00ffffff00f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xffffffaaffffffaafaf0aa00faf0aa00ffffffaaffffffaafaf0aa00faf0aa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xffffffccffffffccfcfc0000fcfc0000ffffffccffffffccfcfc0000fcfc0000
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xffffffeeffffffeefefcaa00fefcaa00ffffffeeffffffeefefcaa00fefcaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_98 : Nat := 0x5000000050000000500000005
def goal_98 : Nat := 0xffffffffcccccccccccccccc00000000ffffffffcccccccccccccccc00000000
def roots_98 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xffffffffaaaaaaaaf0f0f0f000000000ffffffffaaaaaaaaf0f0f0f000000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xffffffffccccccccfcfcfcfc00000000ffffffffccccccccfcfcfcfc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xffffffffeeeeeeeefcfcfcfc00000000ffffffffeeeeeeeefcfcfcfc00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffffaaffaaaa00aa00aa00aa00ffffffffffaaffaaaa00aa00aa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffffeeffeeeecceeccaa00aa00ffffffffffeeffeeeecceeccaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xffffffffffaaffaafaf0faf0aa00aa00ffffffffffaaffaafaf0faf0aa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xffffffffffccffccfcfcfcfc00000000ffffffffffccffccfcfcfcfc00000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xffffffffffeeffeefefcfefcaa00aa00ffffffffffeeffeefefcfefcaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_112 : Nat := 0x10001000100010001000100010001
def goal_112 : Nat := 0xffffffffffff0000ffff000000000000ffffffffffff0000ffff000000000000
def roots_112 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffffffffffaaaaffff000000000000ffffffffffffaaaaffff000000000000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffffffccccffffcccccccc0000ffffffffffffccccffffcccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffffffeeeeffffcccccccc0000ffffffffffffeeeeffffcccccccc0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xffffffffffff0000fffff0f0f0f00000ffffffffffff0000fffff0f0f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xffffffffffffaaaafffff0f0f0f00000ffffffffffffaaaafffff0f0f0f00000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xffffffffffffccccfffffcfcfcfc0000ffffffffffffccccfffffcfcfcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xffffffffffffeeeefffffcfcfcfc0000ffffffffffffeeeefffffcfcfcfc0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffffffaaffffaa00aa00aa00ffffffffffffffaaffffaa00aa00aa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffffffccffffcccccccc0000ffffffffffffffccffffcccccccc0000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffffffeeffffeecceeccaa00ffffffffffffffeeffffeecceeccaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xffffffffffffff00fffff0f0f0f00000ffffffffffffff00fffff0f0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xffffffffffffffaafffffaf0faf0aa00ffffffffffffffaafffffaf0faf0aa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xffffffffffffffccfffffcfcfcfc0000ffffffffffffffccfffffcfcfcfc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xffffffffffffffeefffffefcfefcaa00ffffffffffffffeefffffefcfefcaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafaf0f00000f0f00000f0f00000f0f00000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fcfc0000fcfc0000fcfc0000fcfc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffafafffffafafffffafafffffafafcfc0000fcfc0000fcfc0000fcfc0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffff00ffffff00ffffff00ffffff00cccc0000cccc0000cccc0000cccc0000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffaaffffffaaffffffaaffffffaaeeccaa00eeccaa00eeccaa00eeccaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfffffff0fffffff0fffffff0fffffff0f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffafaf0aa00faf0aa00faf0aa00faf0aa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fcfc0000fcfc0000fcfc0000fcfc0000
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffafffffffafffffffafffffffafefcaa00fefcaa00fefcaa00fefcaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0fcfcfcfc00000000fcfcfcfc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_176 : Nat := 0x100010001000100000000000000000001000100010001
def goal_176 : Nat := 0xffffffffffff0000ffffffffffff0000ffff000000000000ffff000000000000
def roots_176 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffffff0000ffffffffffff0000ffffcccccccc0000ffffcccccccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fffff0f0f0f00000fffff0f0f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fffffcfcfcfc0000fffffcfcfcfc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffffaaffffffffffffffaaffffaa00aa00aa00ffffaa00aa00aa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffaaffffffffffffffaaffffeecceeccaa00ffffeecceeccaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffafffffffffffffffafffffefcfefcaa00fffffefcfefcaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfafafafafafafafafafafafafafafafaaaaaaaaaaaaaaaaa0000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfefefefefefefefefafafafafafafafaeeeeeeeeeeeeeeee0000000000000000
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

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0ff00ff00ff00ff000000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffafffafffafffafffaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffcfffcfffcfffcfff0fff0fff0fff0ffccffccffccffcc0000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffefffafffafffafffaffeeffeeffeeffeeaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffccccffffccccffff0000ffff0000ffffccccffffcccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffaaaaffffaaaaffffeeeeffffeeeecccc0000cccc0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0ffff0000ffff0000f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffafafffffafafffffafafffffafaffffaaaaffffaaaaf0f00000f0f00000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfffff0f0fffff0f0ffffccccffffccccfcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefffffafafffffafaffffeeeeffffeeeefcfc0000fcfc0000
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

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffff0fffffff0fffffff0fffffff0ffffff00ffffff00f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffafffffffafffffffafffffffaffffffaaffffffaafaf0aa00faf0aa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcfffffff0fffffff0ffffffccffffffccfcfc0000fcfc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffffffafffffffaffffffeeffffffeefefcaa00fefcaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffccccccccffffffff00000000ffffffffcccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeffffffffaaaaaaaaffffffffeeeeeeeecccccccc00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0ffffffff00000000f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfffffffff0f0f0f0ffffffffccccccccfcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaaa00aa00aa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffff00ff00ffffffffffccffcccccccccc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffffaaffaaffffffffffeeffeeeecceeccaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffffffffffafffaffffffffffeeffeefefcfefcaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffff000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffff000000000000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffccccffffffffffff0000ffffffffffffccccffffcccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffffffffffaaaaffffffffffffeeeeffffcccccccc0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffff0f0fffffffffffff0f0ffffffffffff0000fffff0f0f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffffffffff0f0ffffffffffffccccfffffcfcfcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffffffffffafaffffffffffffeeeefffffcfcfcfc0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffffffffffaaffffffffffffffaaffffaa00aa00aa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffffffffff00ffffffffffffffccffffcccccccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffffffaaffffffffffffffeeffffeecceeccaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffffffffffaffffffffffffffaafffffaf0faf0aa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffffffffff0ffffffffffffffccfffffcfcfcfc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffffffffffaffffffffffffffeefffffefcfefcaa00
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_50
def pG:List (Nat×Nat):=[(2,18),(2,34),(16,18),(16,48),(32,34),(32,48)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3f
def xsM:=roots_50.map (·&&&dom_50)
def gM:=goal_50&&&dom_50
def NN:Nat→Nat
|2=>1
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|2,0=>0xe0b89
|3,0=>0xe0b89
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x140014000000028000000280004000400040004
|_,_=>0
def sP:Nat→Nat
|0=>0x924
|_=>0
def sO:Nat→Nat→Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wAt:=mkWire dB 3 51 0x7ffffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_50 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_50 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_50==dom_50)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_50 gM v ys):RunD true dom_50 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_50 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_50 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_50 gM s xsM):False:=by
  have hmin:2≤s:=by have hl:=run_len h;change 3≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_50 roots_50 goal_50 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_50
theorem lowS_50:Lower true dom_50 roots_50 goal_50 4:=S_50.noCircuit
def isoMvS_52:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_52:Lower true dom_52 roots_52 goal_52 4:=lower_iso_b isoMvS_52 (by decide +kernel) lowS_50
def isoMvS_73:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_73:Lower true dom_73 roots_73 goal_73 4:=lower_iso_b isoMvS_73 (by decide +kernel) lowS_50
def isoMvS_82:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_82:Lower true dom_82 roots_82 goal_82 4:=lower_iso_b isoMvS_82 (by decide +kernel) lowS_50
def isoMvS_98:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_98:Lower true dom_98 roots_98 goal_98 4:=lower_iso_b isoMvS_98 (by decide +kernel) lowS_50
def isoMvS_112:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_112:Lower true dom_112 roots_112 goal_112 4:=lower_iso_b isoMvS_112 (by decide +kernel) lowS_50
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_50
def isoMvS_176:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_176:Lower true dom_176 roots_176 goal_176 4:=lower_iso_b isoMvS_176 (by decide +kernel) lowS_50
theorem lowS_54:Lower true dom_54 roots_54 goal_54 5:=lower_slice_b [(0x44004400440044,16,18)] (by decide +kernel) lowS_52
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_slice_b [(0xc0c0000000000000c0c,64,66)] (by decide +kernel) lowS_73
namespace S_85
def pG:List (Nat×Nat):=[(1,65),(4,20),(5,21),(5,69),(16,20),(16,80),(17,21),(17,81),(64,65),(64,80),(68,69),(68,84)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_85.map (·&&&dom_85)
def gM:=goal_85&&&dom_85
def NN:Nat→Nat
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x168b5
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc00000000000000cc0003000300000000000300030880088000000000088008b300330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xe4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|_,_=>0
def wAt:=mkWire dB 4 86 0x3fffffffffffffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_85 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_85 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_85==dom_85)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_85 gM v ys):RunD true dom_85 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_85 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_85 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_85 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_85 roots_85 goal_85 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_85
theorem lowS_85:Lower true dom_85 roots_85 goal_85 4:=S_85.noCircuit
namespace S_114
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,66),(16,18),(16,48),(16,80),(32,34),(32,48),(32,96),(64,66),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_114.map (·&&&dom_114)
def gM:=goal_114&&&dom_114
def NN:Nat→Nat
|3=>3
|4=>7
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x5616f1bc380d592
|4,0=>0x8cedc3e9952215f1a1ca0ebad0cb8f0bbdf
|5,0=>0x774af5b4071a28e
|6,0=>0x774af
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa000a000a0008000a000a000a00094001400140014001400140000000280028002800280028000000280005000500050005000400040004000400000000a000800000000000a0008400040004000400040004000000008000800080008000800000008000500050000000000050004000000008000800080008000800080008000940014001400000014001400140002800280020002000280028002000250004000500040005000400050004a000a00000000000a000a0000000140000001400000014000000140000800080008000800080008000800050005000500050000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x327032705327032c70f3270e32c73d2c753420327b0327a032790827065403210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x21022004
|4,0=>0xa952aa0536a5948a8c5
|5,0=>0xe51a2af5
|6,0=>0x3d4
|_,_=>0
def wAt:=mkWire dB 16 115 0x7ffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x375c10341d205c1724dd324dd
|_=>0
def oO:Nat→Nat→Nat
|3,0=>0x200
|4,0=>0x624222000000
|5,0=>0x9181
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xf76530
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>8
|4,0=>0x11600
|5,0=>0x12d
|6,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_112 4 roots_112 ops++addP pm 1 dom_98 4 roots_98 ops++addP pm 2 dom_82 4 roots_82 ops++addP pm 3 dom_50 4 roots_50 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_114 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_112 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_50 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_112 4 s (0,roots_112.map (·&&&dom_112)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_114 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_112 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_114==dom_114)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_114 gM v ys):RunD true dom_114 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_114 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_114 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_114 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_114 roots_114 goal_114 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_114
theorem lowS_114:Lower true dom_114 roots_114 goal_114 7:=S_114.noCircuit
def isoMvS_83:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_75
def isoMvS_86:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_75
def isoMvS_89:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_75
def isoMvS_90:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_75
def isoMvS_92:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 4:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_85
def isoMvS_101:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 4:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_85
def isoMvS_102:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 5:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_75
def isoMvS_113:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_75
def isoMvS_116:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_54
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_75
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_75
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_75
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 4:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_85
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_75
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_75
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_54
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 7:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_114
def isoMvS_195:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 4:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_85
def isoMvS_197:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 4:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_85
def isoMvS_201:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_54
def isoMvS_202:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 4:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_85
def isoMvS_204:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 4:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_85
def isoMvS_210:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_75
def isoMvS_212:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_75
def isoMvS_226:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_75
def isoMvS_228:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 5:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_75
def isoMvS_240:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_240:Lower true dom_240 roots_240 goal_240 5:=lower_iso_b isoMvS_240 (by decide +kernel) lowS_54
theorem lowS_59:Lower true dom_59 roots_59 goal_59 6:=lower_slice_b [(0xa0a0a0a0a0a0a0a,8,9),(0xf000f000f000f00,1,9)] (by decide +kernel) lowS_50
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_slice_b [(0xaa00aa0000000000aa00aa,64,65)] (by decide +kernel) lowS_86
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
|0=>0x3ff77d646123ca080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x34162005
|6,0=>0x7a98
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_90 5 roots_90 ops++addP pm 1 dom_82 4 roots_82 ops++addP pm 2 dom_89 5 roots_89 ops++addP pm 3 dom_73 4 roots_73 ops++addP pm 4 dom_83 5 roots_83 ops++addP pm 5 dom_75 5 roots_75 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_91 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_83 _ g hchk
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
def dzo_89_4:=0x303030300000000030303030
def gzo_89_4:=0x303030200000000030302000
def gsh_89_4:=0x30303020000000003030200
theorem lowS_zo_89_4_73:Lower true dzo_89_4 roots_89 gzo_89_4 5:=lower_iso_b (d1:=dom_89) (r1:=roots_89) (T1:=gsh_89_4) [(dom_89,4)] (by decide +kernel) (lower_slice_b (T:=gsh_89_4) [(0x30300000000000003030000,0,16)] (by decide +kernel) lowS_73)
namespace S_93
def pG:List (Nat×Nat):=[(1,9),(1,65),(4,20),(5,13),(5,21),(5,69),(8,9),(8,72),(12,13),(12,28),(12,76),(16,20),(16,80),(17,21),(17,25),(17,81),(24,25),(24,28),(24,88),(64,65),(64,72),(64,80),(68,69),(68,76),(68,84)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_93.map (·&&&dom_93)
def gM:=goal_93&&&dom_93
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x6af21018c0
|5,0=>0xeca141e1fd11d1c
|6,0=>0x4011c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc88cc8800000000cc88cc8b3333333000000002222222200cc00cc00000000000000033003300000000003300330044444444000000004400440333300000000000033330000c0c0c0c000000000c0c0c0c222222220000000022222222cc00cc00000000008800880333333330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x463204963204638204632074635043210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 94 0x3fffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x182
|_=>0
def oO:Nat→Nat→Nat
|5,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0xfa0e0
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x29
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_89 5 roots_89 ops++addP pm 1 dzo_89_4 5 roots_89 ops++addP pm 2 dom_85 4 roots_85 ops++addP pm 3 dom_92 4 roots_92 ops++addP pm 4 dom_73 4 roots_73 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_93 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_89_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_73 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_89 5 s (0,roots_89.map (·&&&dom_89)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_93 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_89 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_93==dom_93)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_93 gM v ys):RunD true dom_93 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_93 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
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
theorem lowS_115:Lower true dom_115 roots_115 goal_115 8:=lower_slice_b [(0xa000a000a000a000a000a000a000a,64,65)] (by decide +kernel) lowS_114
def dzo_116_1:=0x220022002200220022002200220022
def gzo_116_1:=0x220022002200220022002000200000
def gsh_116_1:=0x110011001100110011001000100000
theorem lowS_zo_116_1_52:Lower true dzo_116_1 roots_116 gzo_116_1 5:=lower_iso_b (d1:=dom_116) (r1:=roots_116) (T1:=gsh_116_1) [(dom_116,1)] (by decide +kernel) (lower_slice_b (T:=gsh_116_1) [(0x110011001100110000000000000000,0,64)] (by decide +kernel) lowS_52)
namespace S_117
def pG:List (Nat×Nat):=[(1,65),(4,20),(4,36),(5,21),(5,37),(5,69),(16,20),(16,48),(16,80),(17,21),(17,49),(17,81),(32,36),(32,48),(32,96),(33,37),(33,49),(33,97),(64,65),(64,80),(64,96),(68,69),(68,84),(68,100)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_117.map (·&&&dom_117)
def gM:=goal_117&&&dom_117
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xd27bd
|5,0=>0xeeb24
|6,0=>0x96c74
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x330033003300000033003300330000c000c000c000c000c000c000c000c330033000000000033003300000000cc000000cc000000cc000000cc0002200220022002200220022002200220c000c000c0000000c000c000c000330033003300330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8ea1a3a84688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 118 0x3fffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x8d
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
addP pm 0 dom_116 5 roots_116 ops++addP pm 1 dzo_116_1 5 roots_116 ops++addP pm 2 dom_113 5 roots_113 ops++addP pm 3 dom_101 4 roots_101 ops++addP pm 4 dom_52 4 roots_52 ops++addP pm 5 dom_85 4 roots_85 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_117 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_116_1_52 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_52 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_85 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_116 5 s (0,roots_116.map (·&&&dom_116)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_117 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_116 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_117==dom_117)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_117 gM v ys):RunD true dom_117 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_117 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_117 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_117 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_117 roots_117 goal_117 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_117
theorem lowS_117:Lower true dom_117 roots_117 goal_117 7:=S_117.noCircuit
theorem lowS_118:Lower true dom_118 roots_118 goal_118 8:=lower_slice_b [(0x500050005000500050005000500050,16,20)] (by decide +kernel) lowS_114
theorem lowS_199:Lower true dom_199 roots_199 goal_199 5:=lower_slice_b [(0xcc00000000000000cc00000000000000cc00000000000000cc,64,66)] (by decide +kernel) lowS_197
theorem lowS_211:Lower true dom_211 roots_211 goal_211 6:=lower_slice_b [(0xa000a00000000000a000a00000000000a000a00000000000a000a,64,65)] (by decide +kernel) lowS_210
theorem lowS_217:Lower true dom_217 roots_217 goal_217 6:=lower_slice_b [(0x3030000000000000303000000000000030300000000000003030000,64,80)] (by decide +kernel) lowS_201
def isoMvS_61:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 6:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_59
def isoMvS_94:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 6:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_87
def isoMvS_103:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_87
def isoMvS_107:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 8:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_91
def isoMvS_109:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 7:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_93
def isoMvS_110:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_87
def isoMvS_121:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 8:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_91
def isoMvS_122:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 8:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_115
def isoMvS_124:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 7:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_117
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_87
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 7:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_93
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 8:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_91
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 6:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_87
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 8:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_118
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 8:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_91
def isoMvS_203:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 7:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_117
def isoMvS_205:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 7:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_117
def isoMvS_206:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 5:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_199
def isoMvS_213:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 6:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_211
def isoMvS_214:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 8:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_91
def isoMvS_218:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 6:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_211
def isoMvS_220:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 6:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_211
def isoMvS_227:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 6:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_211
def isoMvS_230:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 8:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_91
def isoMvS_233:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 6:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_217
def isoMvS_234:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 6:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_211
def isoMvS_241:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 6:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_217
def isoMvS_242:List (Nat×Nat):=[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 8:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_118
def isoMvS_244:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 8:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_118
theorem lowS_63:Lower true dom_63 roots_63 goal_63 7:=lower_slice_b [(0xaaaaaaaaaaaaaaaa,8,9),(0xff00ff00ff00ff00,1,9)] (by decide +kernel) lowS_54
theorem lowS_95:Lower true dom_95 roots_95 goal_95 9:=lower_slice_b [(0xf0f0f0f000000000f0f0f0f0,16,20)] (by decide +kernel) lowS_91
theorem lowS_119:Lower true dom_119 roots_119 goal_119 9:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa,64,65)] (by decide +kernel) lowS_118
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,65),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,72),(10,11),(10,26),(10,42),(10,74),(16,18),(16,48),(16,80),(17,19),(17,25),(17,49),(17,81),(24,25),(24,26),(24,56),(24,88),(32,34),(32,48),(32,96),(33,35),(33,41),(33,49),(33,97),(40,41),(40,42),(40,56),(40,104),(64,65),(64,66),(64,72),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c688
|_=>0
def sO:Nat→Nat→Nat
|9,0=>6
|_,_=>0
def wAt:=mkWire dB 6 124 0xfffffffffffffffffffffffffffffff
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
addP pm 0 dom_122 8 roots_122 ops++addP pm 1 dom_121 8 roots_121 ops++addP pm 2 dom_115 8 roots_115 ops++addP pm 3 dom_107 8 roots_107 ops++addP pm 4 dom_91 8 roots_91 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_91 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 8 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_123 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_73_4:=0x30300000000000003030
def gzo_73_4:=0x30200000000000002000
def gsh_73_4:=0x3020000000000000200
theorem lowS_zo_73_4_73:Lower true dzo_73_4 roots_73 gzo_73_4 4:=lower_iso_b (d1:=dom_73) (r1:=roots_73) (T1:=gsh_73_4) [(dom_73,4)] (by decide +kernel) (lower_slice_b (T:=gsh_73_4) [] (by decide +kernel) lowS_73)
def dzo_124_1:=0x22222222222222222222222222222222
def gzo_124_1:=0x22222222222222222222222022202200
def gsh_124_1:=0x11111111111111111111111011101100
theorem lowS_zo_124_1_52:Lower true dzo_124_1 roots_124 gzo_124_1 6:=lower_iso_b (d1:=dom_124) (r1:=roots_124) (T1:=gsh_124_1) [(dom_124,1)] (by decide +kernel) (lower_slice_b (T:=gsh_124_1) [(0x11001100110011001100110011001100,0,8),(0x11111111111111110000000000000000,0,64)] (by decide +kernel) lowS_52)
def dzo_105_4:=0x3030000030300000303000003030
def gzo_105_4:=0x3030000030200000303000002000
def gsh_105_4:=0x303000003020000030300000200
theorem lowS_zo_105_4_73:Lower true dzo_105_4 roots_105 gzo_105_4 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_4) [(dom_105,4)] (by decide +kernel) (lower_slice_b (T:=gsh_105_4) [(0x303000000000000030300000000,0,32)] (by decide +kernel) lowS_73)
def dzo_60_1:=0x2222222222222222
def gzo_60_1:=0x2222222022202200
def gsh_60_1:=0x1111111011101100
theorem lowS_zo_60_1_52:Lower true dzo_60_1 roots_60 gzo_60_1 5:=lower_iso_b (d1:=dom_60) (r1:=roots_60) (T1:=gsh_60_1) [(dom_60,1)] (by decide +kernel) (lower_slice_b (T:=gsh_60_1) [(0x1100110011001100,0,8)] (by decide +kernel) lowS_52)
def dzo_53_8:=0x3300330033003300
def gzo_53_8:=0x3300320032002200
def gsh_53_8:=0x33003200320022
theorem lowS_zo_53_8_52:Lower true dzo_53_8 roots_53 gzo_53_8 5:=lower_iso_b (d1:=dom_53) (r1:=roots_53) (T1:=gsh_53_8) [(dom_53,8)] (by decide +kernel) (lower_slice_b (T:=gsh_53_8) [(0x22002200220022,0,1)] (by decide +kernel) lowS_52)
def dzo_121_4:=0x30303030303030303030303030303030
def gzo_121_4:=0x30303030303030203030303030302000
def gsh_121_4:=0x3030303030303020303030303030200
theorem lowS_zo_121_4_73:Lower true dzo_121_4 roots_121 gzo_121_4 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_4) [(dom_121,4)] (by decide +kernel) (lower_slice_b (T:=gsh_121_4) [(0x3030000030300000303000003030000,0,16),(0x3030303000000000303030300000000,0,32)] (by decide +kernel) lowS_73)
def dzo_117_8:=0x33003300330033003300330033003300
def gzo_117_8:=0x33003300330033003300320032002200
def gsh_117_8:=0x330033003300330033003200320022
theorem lowS_zo_117_8_52:Lower true dzo_117_8 roots_117 gzo_117_8 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_8) [(dom_117,8)] (by decide +kernel) (lower_slice_b (T:=gsh_117_8) [(0x220022002200220022002200220022,0,1),(0x330033003300330000000000000000,0,64)] (by decide +kernel) lowS_52)
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,65),(4,20),(4,36),(5,13),(5,21),(5,37),(5,69),(8,9),(8,72),(12,13),(12,28),(12,44),(12,76),(16,20),(16,48),(16,80),(17,21),(17,25),(17,49),(17,81),(24,25),(24,28),(24,56),(24,88),(32,36),(32,48),(32,96),(33,37),(33,41),(33,49),(33,97),(40,41),(40,44),(40,56),(40,104),(64,65),(64,72),(64,80),(64,96),(68,69),(68,76),(68,84),(68,100)]
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
|5,0=>0xe9e98928f679b9c1d9d4
|6,0=>0xc3401990c09660690bd07e4a47d4a7765ee657a847955389d430bc12dbab2cf6324d8916be1
|7,0=>0xd91c7bea8eb9058b00d9aefafad7dcac1c3a7da69cf7492b86862497ba9f78af5784606be2d616cc59708439713eb0c38a132396122f751499b0fc83
|8,0=>0xc4d75b25508e2267749274b3a6951e642d20f7ba
|9,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccccccc0000cccccccccccc00033333333333333333333333333330000cccccccccccccccc0c0c0c0c0c0c00000000000333311110000000033330000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0000333300003333000033330000000000000000cccccccc00000000cccc00000330033003300330022002200220022888888888888888888008800880088003030303030300000303030303030000cccccccc00000000cccccccc000000033330000333300003333000033330000cc00cc00cc00cc00cc00cc00cc00cc0222222222222222222222222222222220ccc0ccc0ccc00cc0c0c0c0c0c0c00033333333333333330000000000000000
|0,1=>0xc0c0c0c0ccccccccc0c0c0c0c0c0c0c000000000000333300000000000000000000cccc0000cccc00000000000000033333333000033333333333300000000cccc8888cccc8888cccc8888cccc88880000000333322220000000033332222cccccccccccccc00cccccccccccccc033333333333300333333333333330000444444444444444400000000000000000330033003300330000000000000000cccccccc00cc00cccccccccc000000033333333333333333333000033330000cccccccccccccccccccccccc000000033223322332233223322332233223322cccccccccccccccc888888888888888b3003300330033002200220022002200
|0,2=>0xcccccccc88888888cccccccc8888888b0333033303330333030303030303030ccccccccccccccccc0c0c0c0c0c0c0c00000000333333330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xf1442c22006051032c200f4d40cb08f4d40cb0801440c21805cf4c32c22803d51032c20131540cb08a1440d10860131032c224014448308600f1442c24003850cb08a00510308d0051032c23000cb08a2401440862001440c71801440c2040
|1=>0x1038421440e20804c51038420051038428051037c200e1440cb0803931440cb0804c51032c274f1440cb4420051032c201e3c51120cb0807051032c200510b0900051032c26801440c21803c55032c20191440cb0805451032c20055040cb089
|2=>0x51032c20051032c20171440e10801440cb4420051120cb0804c51032c200f1440cb0801440cb0808231440cb0801442c22004c55040cb0931541032c20051032c22803c51032c20174c5
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x9303180cc006
|6,0=>0x1e1ce2e6b6323975cace4f7243905c74e337163895c3ec187
|7,0=>0x903465e2310a78143f19eccef774b38d9b8ed4866bb1617ceb6857baa5944e9c64aba39d0ee7f8
|8,0=>0xab3d41a92f4279dbcd1e5af267
|9,0=>0x15d6
|_,_=>0
def wAt:=mkWire dB 36 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1408f011445311140440214042011444f021444309144457510083440805b171024f2f14444011444f0d14445590c094171004346080451154445590c085111004501144440114042023cbc5114c4c50115643024c4c5013cbc511385d3111404f2f14445110d10201384cf011444511
|1=>0x2022c042010c245011444502142434608044011404401140531314042021444b011404b590c08b0114045022c04b81
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x80ce99a32e650c911021c43084987208604c00800
|7,0=>0xa253ca694b29251ca29432824fc9e93b2724dc9a9332624bc9692b25249c929232
|8,0=>0xb43646c0d71ac3546a0d31
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x1413a1fe7c37cf8669f0532a09adc134f8269d04d2e08b74105b8209501000018fc031e8061d0030000314005f800800006e0008c000f8001e0002c0004c000600005000080000c000100000
|1=>0xa45ab2925e514eaa2dd401ca4031474cf8a2d5
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40000
|6,0=>0x409124f1c314c18c38a4c0
|7,0=>0x95025735d85c79d68b4a366265681b4a67c8
|8,0=>0x7dd927615620
|9,0=>0x14
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 8 roots_121 ops++addP pm 1 dzo_73_4 4 roots_73 ops++addP pm 2 dom_109 7 roots_109 ops++addP pm 3 dom_61 6 roots_61 ops++addP pm 4 dom_93 7 roots_93 ops++addP pm 5 dom_73 4 roots_73 ops++addP pm 6 dzo_124_1 6 roots_124 ops++addP pm 7 dom_124 7 roots_124 ops++addP pm 8 dzo_105_4 5 roots_105 ops++addP pm 9 dzo_60_1 5 roots_60 ops++addP pm 10 dzo_53_8 5 roots_53 ops++addP pm 11 dzo_121_4 6 roots_121 ops++addP pm 12 dom_89 5 roots_89 ops++addP pm 13 dom_117 7 roots_117 ops++addP pm 14 dzo_89_4 5 roots_89 ops++addP pm 15 dzo_116_1 5 roots_116 ops++addP pm 16 dom_116 5 roots_116 ops++addP pm 17 dom_52 4 roots_52 ops++addP pm 18 dzo_117_8 6 roots_117 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_73_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_124_1_52 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_105_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_60_1_52 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_53_8_52 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_121_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_89_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_116_1_52 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_52 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_117_8_52 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 8 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
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
theorem lowS_207:Lower true dom_207 roots_207 goal_207 8:=lower_slice_b [(0xcccc000000000000cccc000000000000cccc000000000000cccc,64,66)] (by decide +kernel) lowS_205
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_slice_b [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,64,65)] (by decide +kernel) lowS_214
theorem lowS_219:Lower true dom_219 roots_219 goal_219 9:=lower_slice_b [(0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000,1,129)] (by decide +kernel) lowS_91
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=lower_slice_b [(0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a,64,65)] (by decide +kernel) lowS_242
namespace S_246
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,66),(4,20),(4,36),(4,132),(6,22),(6,38),(6,70),(6,134),(16,18),(16,20),(16,48),(16,80),(16,144),(32,34),(32,36),(32,48),(32,96),(32,160),(64,66),(64,80),(64,96),(68,70),(68,84),(68,100),(68,196),(128,132),(128,144),(128,160),(130,134),(130,146),(130,162),(130,194),(192,194),(192,196),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_246.map (·&&&dom_246)
def gM:=goal_246&&&dom_246
def NN:Nat→Nat
|4=>10
|5=>46
|6=>170
|7=>127
|8=>30
|9=>6
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x3eb8127199232291f6130bbe20b95c0969e0917504db502871
|5,0=>0xa07bb8ee8080eee59422554334d38a4b976477cf43a6c3ee8a3b2fa36fee33b6e32d693092630694274e7233ab216db211a920a7f1d2d91ba631b24b18ab7187ef15026149e8143111331512ff7119c20eabb0d0fc0d0330ae9307d1d07a5206e00057fd04d220451503e7e03da1033e30043f
|6,0=>0x411f840d0540ac7406504037f3f8033e7533d5f93d50c3c8633bfae3bdec3a55e39ad53976d3879f385fc3857937bb5377cf36d1934b653463c33b7231f8630929307732e6c22e6202dd0f2cf5f2c6542bba92b2cb2a97a27cbb2596824d3f24cca2488f2457e2392e22b0e2256a2224121d411fba71eb9c1dc7f1d4c21cc311c9051b4c61b4bc1b30e1a9371a85b19a3d182df1810f17f1617da21773217509156b5149bb147111462313ec712c5812a07128801260811e041192c115ef0fa760f6010f3620eff60ef8b0ef8a0e8af0e7a20e7680e4af0dd170db470d8990d7120d6cd0d2950c98b0c84c0c36b0c2240c0e30be5f0b7770ae930ac190aa450a8840a02509e740949d08d6f08c290875a07d1d0735d06f6c06909063f905d1f05d0605b2a0403503e0e03bed039160253b0251a0244801cf100562003390013f
|6,1=>0xb6784b52af93e8590e8f8b35b895c58207d7db2d7309a72eaa67d3e66e8764d806389763849626d05dc175d10f5936f58df55746154054528ca506744f1a74ebf74bb5d4a5f649c36495ef4936a47db94728b464b4457fe43a2c433174300b4235e42259420aa416b2
|7,0=>0xbc2b69c46399141814847d10e784db76edc72d1c6e0e966c686197d5c7a85bc545758b570a953b97520f3509bf5094a4fc184e9b64c51f47e4e43a5341a114035f3fcb03f71f3cad73bab93abcf3a9dc39cc63725835b7035773351b23334032c2b318f730822300752f7c02f2ad2f08f2d2e82d0b92bd8b2b9bc2b3c52a9952a97a2a8c82a75229de329b3828a9d262da254e7253f72496e22c58229c0208de1f4921ea111dc811d9bd1d7ab1d36d1b5541b4bc1a6841a619198af1925e18b89188d3187da187831855116b141674015f7415e1d14cc61495814923140f6133b91282a11f9a11491113dc1080c105910fe570d7f30d7600d04f0cd8c0c3860b7280b5b40af470961908f7b08c2108b8108a0307f2307cee07769076ee06e9306d840621905c7b046df038a3032880321802469017b4010ab00f2400f19
|8,0=>0x6b9036a6ee657435b3a158e394d7ca4943d445703f3873ebc13b66f39ef539eee3558032ae22d2e12aa2f2a936286ae1f0a61912c16a0711b5011677110050e92d0c6150a03b024f200ada
|9,0=>0xc6bda6d4fd42c423f43d300171122d
|10,0=>0x3f43d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaa00aa00aa00a000aa00aa00aa00a000aa00aa00aa00a000aa00aa00aa00a154015401100110015401540110011001540154011001100154015401100112a802a802a802a802a802a802a802a802a002a002a0000002a002a002a000055005500550055000000000000000000550055005500550000000000000000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a154015401540000015401540154000001540154015400000000000000000002a802a802a802a802a802a802a802a802a802a802a802a800000000000000055005500000000005500550000000000550055000000000055005500000000aa00aa00aa00aa00aa00aa00aa00aa0000000000000000000000000000000154015401540154015401540154000001540154015401540154015401540002a8000002a8000002a8000002a8000002a8000002a8000002a8000002a800055005500550000005500550055000000550055005500000055005500550000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa0000000000aa00aa0000000154015401540154015400000154000001540154015401540154000001540002a802a802a8028002a802a802a8028002a802a802a8028002800280028002844004400440044004400440044004400440044004400440044004400440044
|0,1=>0xa000a000a0000000a000a000a0000000a000a000a0000000a000a000a000044004400440044000400040004000000440044004400440004000400040002a802a802a8000002a802a802a80000022002200220000002200220022000055005500550055005500550000000000550055005500550055005500000000aa00aa00aa00aa00aa00aa00aa000000aa00aa00aa00aa008800880088000154015401540154015401540154015401540000015400000154000001540002a802a802a8022002a802a802a8022002a802a802a8022002200220022002255005500550000005000500050000000550055005500000050005000500000aa00aa00aa00aa00a000a000a000a000aa00aa00aa00aa00a000a000a000a154015401540154015401540154015401100110011001100110011001100112a802a802a802a802a802a802a802a802a802a802a8000002a802a802a800055004400550044005500440055004400550044005500440055004400550044aa00aa00aa00a000aa00aa00aa00a000a800a800a800a000a800a800a800a154015401400140015401540140014001540154014001400154015401400142a802a802a802a802a802a802a802a802a802a802a8000002800280028000054005400540054005400540054005400540054005400540054005400540054
|0,2=>0xa000a000a000a000a000a000a000a0002000200020000000200020002000004000400040110000400040004011000040004000401100004000400040110000000000000000000000000000000028002800280028002a802a802a802a0000000000000000000000000000000055005500550055005500550055000022002200220022002200220022002000220022002200220022002200220020140014001400140014001400140014001400140014001400140014001400000000000000000002a802a802a802a8000000000000000002a802a802a8000000055000000550000005500000055000000550000005500000055000000002200220022002200220022002200000022002200220022002200220022000014001400140014001400140014001400040004000400040004000400040002a8028002a8028002a8028002a8028002a8028002a8028002a8028002a80285400540054000000540054005400000054005400540000005400540054000000000000000000000000000000000000aa00aa00aa00a800aa00aa00aa00a800000000000000015401540154011000000000000000000154015401540110000000000000000000000000000000028802880288028002880288028802855005500550055000500050005000000550055005500550005000500050000
|0,3=>0x220022002200220022002200220022002200220022000000220022002200004400440044004400440044004400440044004400440044004400440044000288028802880280028802880288028002880288028802800288028802880284500450045004400450045004500440045004500450044004500450045004400000000000000008a008a008a00880000000000000000008a008a008a0088000000000000000000000000000000004400440044000000440044004400008800880088008800000000000000000088008800880088008800880088000550055005000500055000000500000005500550050005000550000005000000a000a000a000a000a000a000a000a000a000a000a0000000a000a000a000154015401540110015401540154011001540154015401100154015401540112a802a802a802a802a002a002a0000002a802a802a802a802a002a002a00000000550000005500000055000000550000005500000044000000550000004400000000aa00aa0000000000aa00aa0000000000aa00880000000000aa0088000044000000000000004400000000000000440154000000000044015400000000000000000002a802a802a802a0000000000000000002a802a802a802a00000000000000000000000000000000550055005500500055005500550050
|0,4=>0x200020002000000020002000200000002000200020000000200020002000154015401540154015401540000000001540000015400000154000000000002a802a802a802a802a802a802a802a802a802a80220022002a802a8022002255005500550055005500550055005500550044005500440055004400550044aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa008800aa00aa00aa008800000000000000015401540154015400000000000000000154015401540112a802a802a802a802a802a80280028002a802a802a802a802a802a8028002805000500050004000500050005000400050005000500040005000500050004aa00aa00aa00aa00aa00a000aa00a000aa00aa00aa00aa00aa00a000aa00a154015401540154015401540154015400440044004400000044004400440002a802a802a802a802a802a802a802a802a802a802a802a802a802a80000000550055005500550055005500550055000000000000000000550055005500000000000000000000aa00aa00aa0000000000000000000000aa00aa00aa000014001400140014001400140014001400000000000000000014001400140002a802a802a8022002a002a002a0022002a802a802a8022002a002a002a002200000000000000000000000000000000550055005500440055005500550044
|0,5=>0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa00aa00aa00aa0000140014001400140014001400140000001400140014001400140014001400000002a8000002a0000002a8000002a0000002a8000002a0000002a8000002a5500550055005500550055005500500055005500550055005500550055005000000000aa00aa0000000000aa00a00000000000aa00aa0000000000aa00a044004400440000004400440044000000440044004400000044004400440002a802a802a802a002a802a802a802a002a802a802a802a002a802a802a802a5500550055005500550055005500550055005500550055005500550055000000000000000000000a000a000a00000000000000000000000a000a000a000000000000000000000000000000000000000000015401100000000001540112a802a802a802a802a802a802a802a80000000002a802200000000002a80225500000055005500550000005500550055000000550055005500000055000000000000000000000000aa000000a00000000000000000000000aa000000a154015401540154000001540000014001540154015401540000015400000140000000000000000088008800880000000000000000000000880088008800000000000000000000000000000000000550055005500550055005500550050
|0,6=>0xaa00aa00a800a800aa00aa00a800a800aa00aa00a800a800aa00aa00a800a80000000000000000000000000000000044004400440044004400440044000088008800880080008800880088008000880088008800800088008800880080000000000000000550055005500500000000000000000005500550055005000000000000000000000000000000000a000a000a000a000aa00aa00aa00a0000000000001500000000000000150000000000000015000000000000001500000000000000002a802a802a802a8000000000000000002a8000002a800044004400440044004400440044004400550055005500440055005500550044000000000000000088008800880088000000000000000000aa00aa00aa008940014001400140015401540154014001400140014001400154015401540140280028002800280028002800280028002800280028002000280028002800255005500550055005500550055005500550055005500550055000000550000aa000000aa000000aa00aa00aa00a000aa000000aa000000aa00aa00aa00a0000000000000000000000000000000000000000000000001540154015400000002a8000002a8000002a800000280000002a8000002a8000002a8000002800000000000000000000000000000000550055005500000055005500550000
|0,7=>0xaa00aa0000000000aa00aa0000000000aa00000000000000aa000154015401540154000000000154015401540154015401540000000001540000000028000000200000002800000020000000280000002000000028000000200005500000055000000500000005000000055000000550000005000000050aa00aa0088008800aa00aa0088008800aa00000088000000aa00000088000000015400000110000001540000011000000154000001100000015400000112a802a802a802a802a802a802a802a8000002a800000220000002a8000002211001000110010001100100011001000110010001100100011001000110010a000a000a000a000aa00aa00aa00a800a000a000a000a000aa00aa00aa00a80000000154015000000000015401500000000001540150000000000154015000000002a802a80000000002a802a80000000002a802a80000000002a8000550054005500540055005400550054005500540055005400550054005500540a000a000a000a000a0000000a0000000a000a000a000a000a0000000a000110011001100110011001100110011001540154015401500154015401540150000000002800280000000000280000000000000028002800000000002800055005500050005005500550005000000550055000500050055005500050000
|0,8=>0x2a802a80000000002a800000000000002a802a80000000002a80001100110011001100110011001100110011001100000000001100110000000000000000a800a80000000000a800a80000000000a800a80000000000a800a8000000000001540000000000000140000000000000015400000000000001400000000000000002a8028002a80280000000000000000002a8028002a802855005500000000005500550055005000550055000000000055005500550050000000000000000000000000aa00aa00000000000000000000000000aa000000000001540154000000000154015400000000015401540000000000000000000088000000800000008800000080000000880000008000000088000000800000000000000000000000000000000550055005500550055005500000000aa000000aa000000aa000000aa000000aa00aa00aa00aa00aa00aa00aa0000000154000001540000015400000000000001540000015400000154000000028002a8028002a8028002a802800280028002a8028002a8028002a8028002800000000000055000000000000005500000000000000550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c080b00280c04030513000c08050b2b0c070805002a0c0729080b002807080527260c07151c050b000a1508140b1d0c0e25240c07232208050b00040e05210b0c041c050100070f08051e0c071508140b1b151c050b19040e1a0b1b06081a0b190612051100150814130c04120211000f0e050d0c06030501000403020100
|1=>0xc15080501000c06080501000704031a0b270c1c050b19070412053500070408250d000c0403050b390c150e050b1d0c0438170007041214240c07041c02003707360805350b070b0034330c07040e052f0c07120511000c040b00320c07313008050b000814052f0c0708050b2e0c070f1c05180007030501000c2d2208050b
|2=>0xc4a1508050b0007304908050b000c36080510480c07041c470b00073008250510000c2208050b001f070e08050b460c0704451c020b00072c0802050b00090608050042070f0805410c074008050b3f0c08053e2a0c0708053d3c0c070412051e0c070f08053b0007220805003707040814350b073603050b1d0c0403140b3a
|3=>0x7300408140b000c0408540b000c07081a0b000c0a041c25001f0c074908050b270c0708050b3b001f073008250517000c0802050b0052071c08050b2751070805002a0c0703081a0b00280c0805410b0c07504908050b000c0403050b001d0c041c47250b00073608050b4f0c07044e0b000c07084c0b00340c0708050d0b00
|4=>0x71c050b000a070608050b005707230408050b000c300608050b000c08140b1d0c07034c050b00330c2c1c08050b0009040e1a0b160c044d140b0c07230e08050b000c04120500480c0758080b00280c07431c08050b27070408020b005707300408020b000c0f2208050b00070308050b00550c08020b00280c0708050b2b0c
|5=>0x50b3e090c0704451a0b00090c084705005e0c07080538170007041247000c0704601c020b00070805002f0c075f0403050b000c044d4c0b000c07041c050b180007041205005e0c07060403050b000940081a050b000c08250b005d0c0704470b005b0c0704050b005b0c070412140b5a0c072c1508050b000c362208050b16
|6=>0x71c08020b002807660805001f0c07041c0b00610c0703080500650c07040364020b000c6308020b000c074b4008050b000c29080500370c07082510005d0c0708050b00570c073608050b3f0c07041205004f0c075f08050b0009074908050b2b0c070408050b3e0c070802170b00610704124725000c07044503020b000708
|7=>0x1c020b00076c0847050b00070308050b003a0c060408251700070408140b4f0c07666b08050b000c0408253c000c075808050b270c0704600e1a0b000c5908050b000c07081a050037090c4008050b16000c0403690b000c6708050b00070608050b2b0c070802050b00570760081a0500370c2204081a0b00070f040e140b0c
|8=>0x723008050b000c680403050b000c040e4c0b160c07044902170b000704080513000c070802050b2b0c071270050b000c076f08140b5d0c0708050b276e0c07580805002a0c07044d031a0b000c0805100b6d0c0704082500200c075c050b005b0c0704080500420c075f6208050b0007081a051600370c1c08050b0057071504
|9=>0x6d0c1508050037090c0e050b16330c0704127410000c075f08050b390c071560080500370c0408140b3f0c070608050b180007041c0b00730708050b00463a0c3608050b3a0c073608053d0b0c0708053d210b000c08050b271f0c070408020b180007040e0b005d0c07044312020b00075c6c08050b00071c47050b005b07
|10=>0x4031a0b000c0449020b000704080b00280c070f041c051700070f080b005d0c07772208050b00070f360805100c07230805100b000c04250b00760c0704291c050b00070408050b11000c3604081a0b160c220814050b1607362208050b5a0706050b00750c07593108050b000736050b00330c0704031a0b005a0c3008050b
|11=>0x8057b0b000c0708050b00790c07044d03050b000c070e081a050b160c4d0814050b0c0704080b00780c071508050b163f0c2208050b0048070814050b6d0c070f08053c000c070805103d000c076808050b5a0c076008050b00460c6008050b270c070f080524000c07362208050b51073608050b460c0766041c050b000736
|12=>0x60805170b00070408050b003a0c0708050b3c000c070408053d0b000c0708050b007d0c07040802170b000712084705000c075c0608050b000c07041c1a0b000c07046f12050b000c0704080b00730c070f6c08050b000c074d084c050b000c07120805007c0c076008050b003a0c070864050b00750c070847050b005b0c07
|13=>0x16003a0c0708050b00200c071c08050b00610c070403050b005a0c070814050b5a0c0703086402050b000c150308050b00090c15040e050b000c070f082505001f0c0729081a050b000c0708050b007e0c0708050b00750c0715600308050b000c0f0805001f0c070825050b007d0c071208472505000c0745030802050b0007
|14=>0x1208050b000c0708050b00570c07046003050b000c0805810b000c07360408050b160c070805100b00760c07042908050b000c07360408250b000c07360e08050b160c072c08050b000c07030805690b000c046f050b000c07040e050b5a0c074308050b00570c07040e05100b0c070608050b270c0708050b000c800708050b
|15=>0x590874050b000c078808050b000c0708050b16007f0c08050b00870c073608050b00480c07044308250b000c071c084702050b00070e08050b00340c070854050b000c070814050b00850c070f04080510000c0703080500370c070403050b00090c08050b007f090c5c0802050b000c078308050b000c070408640b000c0759
|16=>0x1d0c07044d0e050b000c070408050b008a0c0736220408050b000736220e08050b00070e084c050b160c0749080205170b00070408050b00460c070f0847050b000c07064308050b0007360874050b000c074d03081a050b000c660408050b000c075c1c08050b000c070802050b270c075908050b000c070403050b16000c
|17=>0x708050b3c001f0c07154508050b000c072c0802050b000c07220408050b00075f0408050b000c07081a050b008c0c15046008050b000c044d050b16000c075f6008050b000c070814050b8b0c07044303050b000c0708050b008209071208740510000c0704491c050b000c071c08050b0073070f301208050b000c0408050b
|18=>0x708053d0b000c070f3608050b000c070f041c050b000c0704031a0b000c3608050b001f0c07041c050b001f0c070825050b005b0c070f08050b005a0c0708050b167a0c074b08050b16000c0708050b005a1f0c07490802050b000708053d0b005a0c0704080500370c07431c08050b00074b0408050b000c0708050b18000c
|19=>0x50b000c070408250b000c070e08050b160c07041c050b000c0708050b00730c0708050b00780c070f0408050b000c0708050b005a0c07081405100b0c07087405100b000c07084702050b000c070408050b001f0c0708050b008d0c07450308050b000c074d08050b000c072208050b0007060408050b270c070f080510000c
|20=>0x1208050b000c070805100b000c0712082505000c0703081a050b000c150408050b000c07360814050b000c070608050b000c070408050b00090c07046008050b000c070e081a050b000c0708050b007f0c07491208050b000c0708050b008b0c074308050b000c0712080510000c070864050b000c07150308050b000c073608
|21=>0x8050b000c070408050b000c070814050b000c070825050b000c0708050b000c07
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2d50285023501e50195014500f500a500550005
|5,0=>0x13b6135612f61296123611d61176111610b610560ff60f960f360ed60e850e260dc60d660d060cb50c560bf60b960b360ad60a850a2609c60966090608a6085507f60796073606d60676061605b6055604f604a5044603e603860326
|6,0=>0x2ec72e662e062d972d362cc72c572be72b772b072a972a2729b7294728d7286727f72796272726b7264725e62577250724a6244623d7236722f72287221721a7213720c720571ff61f871f171eb61e471dd71d671cf71c871c171bb61b471ae61a771a071997192718c6185717f61787171716a7164615d7156714f714871417
|6,1=>0x4aa74a3749c7495748e7487748074797472746b7464745d7456744f74487441743a7433742c7425741e741774107409740273fb73f473ed73e673df73d873d173ca73c373bc73b573ae73a863a2639b7394738d7386737f73787371736a7363735c7355734e7347734073397332732b7324731d7316730f7308730172fa72f37
|6,2=>0x5ce75c775c075b975b275ab75a4759d7596758f75887581757a7574656d7566755f75587551754a7543753c7535752e7527752075197512750b750474fd74f674ef74e874e174da74d374cc74c664bf74b874b17
|7,0=>0x7ac87a5779e7797778f8788778177798772776b7764775c8754874c8744873c8735772e7727772077188711770a770376fb86f476ec86e486dd76d586cd86c586bd86b586ae76a7769f869876908688868086797671866a7662865b7654764d7645863e7636862f7627861f861876108608860085f975f275ea85e375dc75d57
|7,1=>0x98e6986897f7978797089688962695a8952894a8942893b7933892b8924791c8915790e790688ff78f788ef88e788e078d888d178c988c188b988b278aa88a3789b8893888c7884887c8874886c8864885c8854884c8844883c8835782d8825881d8815880e7807780077f887f177ea77e377db87d387cb87c387bc77b48
|8,0=>0xa6b7a647a5c8a548a4d7a458a3d8a358a2e7a268a1f7a187a117a0a7a0289fb79f479ed79e679df79d879d089c979c279ba89b289aa89a3799b89947
|9,0=>0xa947a8d7a867a806a797a727
|10,0=>0xa9b6
|_,_=>0
def wAt:=mkWire dB 142 247 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x150bc101d080c41431240c410010410020150b004202d18074105c05084302d080c4105c050842c2908074102405084301d080742c75041601421040902015080c4140104160201508004142d0410020152000c7c31080547431050041058080542801080c4102405084102405074201518074202d0417020150500410580805420010410020150b0a4102408054201d
|1=>0x150042015360bc100108054145d08054302d080c4002d0f07c9421050b41421050c4701d080c40821050c5102f43074201518004105c08054f0331f0042015240c4140104100201504160201d050841421040742c290409020150c0742c290409020150600c103108074141d080c428010409014210c074142d2407410400805420010416020150c0b40848080b41431
|2=>0x40b41421360cc1001080541d591403c201d05004080d0807414010f07c102d0805410260c074141d0409020150c074102f080c4302d0f07c9421050b4314d02128202d050c49c330600c7015080c51417030c4201d18004105c08054302d08074105805084001d250c42031050b4d8430400420150805470680507420314d05c205905164901d041002015000b52c33
|3=>0x8004211e250c4142d5c08c105d080542c31080b4100304074181f040c42015360cc100108054001d080c4102408054301d040c4105f08055641f04104002d0f07c102d0805414010416020150007421321407414011c054203105074201508004201508164001d05005641f0e254142d360bc1001050840c310807418330600c1471080c4105f05084302d050c43c1f
|4=>0x400c20150c624102708054301d5800c10250c074205d0c0b42015250c4142d080b40c310807414315800c102508054202508054301d0802414310b0c44808050c4202d080549431050b4202d050c420310407c20150b469681d0400c20150407c201508164145900074105c08054302d080c4182f040c42015080741031050852c1f0e1a4141d0800564170e254142d
|5=>0x46a41042080541c31150bc2069050752c1f0416420151a0cc201d050742015680cc01810407c20155c00c182d040c42015430bc18330802414311507c542f1a084141d360cc100105084140108004102d0805415161c0742031040cc20154905c702d080c52c2f03144140108074081d050c4154d02128202d050c4d81f360741001080542041000b4d81d08055682f
|6=>0x212c14316f05c4801080b41803040c42015580bc102508054301d080540c0105074201d041042015040bc211e084749431440bd0c1d040cc20155f0cc31810407c201500074542f081a4141d0617c70150c0b42031040742031050c420150f0cc943125084fc1f1500c0c15080741031050b420155a0bc1003050850c2d040cc2015040bc1803040c4201508004101f
|7=>0x600c4101f08054101f150bc101d080545403040742015040c4105c080542c31080c42015020bc1431075a9681d0400c20155a07c10030400420155a0b420150b5a410030805414310417020150c0b5bc170e0b42001040cc202d5c0cc105d080551c2305174302d0f07c102d08054101f08054145900074205d05084302d0b1d4105808054001d5c00c211d020b421c5
|8=>0x80c414310805410250c074102d0805420316f05c4815080b4d833040042015040b4100108055641f0410420157408c9401050b4543304074142118074105c080542c3104004141d08054d83314084001d050041003360cc1001080556023060741031590cc104108054002d08145302314074201d0400c141d08054542f0407420150c074145900074201505104002d
|9=>0x8164145900074145e0b0c4202d0407c20156408c14250c074211e250c4142d0e1a0141d08005e81d050e8200103004201d05084141d00074200108164001d050049403050b420151500c101d080545049080b47c01080553c2d0410c20150407c20153a07580030407c201504100102d08054002d2200cd8330400420155a0742015040cc100108074141d08054702d
|10=>0x407420150f0bc2095050b454331a084141d7f0c468230507421921a0c4141d1507c0c1508074102f040b420150e25c2001250c4142d080b40c31080741431040c420150c0b4105b08054001d001f4102f080542d690400c20150e25c142d08004143108054302d250c4142d080b4182d040c42015080c4141d080544801080b4142108054082f050c43c33040b42015
|11=>0x807414210b8241472080c4100108054001d087481441000b4543304074201504004142d0805438150007420010607c103108054683305074201d081042015000b420010400c2015040cc201508054002d080041803040c420150409820150c074105b080547c31040bc201505498702d080c410030807414213600c205105004201d02074143103054201d0c0742001
|12=>0x50c4104108054002d07004201d0508421d125004142d088949433050b4001d081a8141d1c1a8141d080c4d82f040042015040cc142d080542031020b414314d05c381d08004161908098301d14128202d040b42015000b4542f03054201d0807414210c0741c31081a8141d08474082d050c416111c07c20310509420150c0745049080b414010417c20150c0b4101f
|13=>0x50042042000b4201d040cc20151c05c301d080c4202d05104002d05084702d080c42031020bc14310f07c4815080b4105808054001d0e074200108054105e0c0b4d833040042015360cc1439080041459000742001050c4205d0c0b5681d0400c2015250849431050b50c31040cc201508144502d050040c0105074201d430b41033080547095050b420310600c2009
|14=>0x5084201d050742015040bc2015080c4102f050851c23250c4142d0400c2015050e82001000741059080541003040bc2015120c41431080b4100308054542f040742015060cc7015080c4105908054001d0417020150c0b4102f080540c3103054201d0607c2009050c4d833040042015600c4101f080540c0308074141d0407c101d08054205905084001d0407c2015
|15=>0x8054141d080046823050744831080b42042000b4103308054202d000b46831050740c1508074100108054142d08054001d08004203108054082f050c49403050b4102d080541003080541401000b41441000b4082d050c4102f08054200a050c40c3108074205900074d8330400420150600c103108054102d08054002d5a0b41003080541001040b42015080c4102d
|16=>0x80541401050b4202d000b4202d050b4141d08074101d0805420510500410310805420150c074101f
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0xaa01140000038c05200730000010c0020000
|5,0=>0x35186730000000000000000c86000030205d30b8215d42a18504096a000023a00000886101000003c406ea0000000032500000000000000005e60a94000000004c800000000000000008cc10181c4000000000000193
|6,0=>0x24c448908f211a422c8454488a10d4214641cc81a0ff41f863e107b10f241dc83a907398e431c2637506d18d821aa634506718cb3192431506118be417662dd05a9000016282bc855a0a920000000052a0a1413a800004d189640000249047988c31108214c40a07e300001ecc3ba07340000000037a06d2
|6,1=>0x3c260000eea1da33b04754ce919cf339c272cce419c4438266f8cdd99b8336886c10d711ad135466990d1219e433486590c9998f43186624cc31985130466008be997942ec65c90b7216a42cc858ccafa15b42b065588a99950329a65250a2a000028640000a0913e3274800009b9935226284b8c9599283
|6,2=>0x12e980004b6496492b1a5424a080001262248448c4914520a23d447648e0d1a9a32345e68b0d149a263444887cd0da217442868411069a0940000815101920033fa67e50fb19f243dc87a90f321e42
|7,0=>0x6326c58d899b10361a6c28d839b0436026bf8d7d9af835ea6bc8d779aec35d26b98d719ae035bc4b6cd6c1ad535a64b40d669aca358e6b10d609abe35766ae0d5a9ab2355e6ab0d5512a735486a84d4f1a9b35306a54d491a8f35186a24d431a83350069f4d3d1a7824ea69c8d379a6c34d26998d319a603
|7,1=>0xf38de59bc8378a6f08ddf9bbc37744edcdda1bb2275e6eb49d51ba7374a4e88dcf9b9c37326e5c9ca1b91371c6e2cdc41b8537046e009be9b7a36ee6dd0db89b6e36d66da0db29b6326c06d74dad1b5736a86d44da71b4b36906d14da11b3f36786ce4d9b1b3336606cb4d951b2736486c84d8f1b1c2
|8,0=>0x2059409280e5014a01940127fe4ff49fd93f927ee4fd49f993f127de4fb49f593e927ce4f949f193e127be4f749ed93d927ae4f549e993d12
|9,0=>0x2088c10181e20002070c0d1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0xa40001200002280003800006a0000c00001480002800004c0000840001000001a00003000005c0000b000015000028000048000088000100000180000280000480000800000e0000180000280000400000600000800000800000
|1=>0x800000b02c016050024890048540082a40101d80202f0040520080a001010802020004012008020010020020000020040030a80060c000c030010100020040030400020800021c000420000800000a000011c00020000030000057
|2=>0xd85001a8bc0341f80662f00c95e0188fc030bf80613f00c0fe0180fc0301d80602e00c050018000026150044000082040100e40201c0040320080600100a8020148040280080400100600200900401000801801002002002004002
|3=>0x4827c0804e01001002000803004005a8fc0b51701603f02827c05047809514010a280210400400840800a01000001c27e0384ec0701f80c13a0182340284e80508c0081320102360204480403000802600d87e01b0ec0361c806c2a
|4=>0x10805a2098a0410020804081000502000404000004e07f0900d21200e42303f84603f08805a10a2a0212178420bf0840081002802003f84002008002c1000001f01f83c03e0780700f00a01e01303803807006c0d80f81a01c02603f
|5=>0x20c97e4182fc8301f9024af20491c4092248103f9008862009524005fc800ac90002d2000204000005309f8a413e1482302804e05008f0a000812c07e2580e44b01609400912005a21a0fc4341708680e10cc7e2188f84301f884628
|6=>0x8080728180e0a301f94603d28c072510024a200214400128405a5080b0a100694003528000a4200fc8345f90683f
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x2020004040200020400
|5,0=>0x4020000000002000c04220a041813000100022600180b0000090000000002090000010000000002022000000002
|6,0=>0x30004626080f7d05b28eac33080c1e300fb701700c420b091a600c16711e308a2f08064201a41c0d132b346728662615731303000800052143000808879c3f290c7e85364999194b9a9d090d7b13080a52a20f0804902430b8bb01b3089b7c470216080016085e0800004213720028ce00357b0f5401cf02000f830900009e30
|6,1=>0x300010203c32c0014c90425c7ad084f010e12018c50468f32c80840011900441565012d2a4376033104
|7,0=>0x39a86f56126b631d4d811fbe070db00e619f2380054a53cba9913db7418d53a697af776938ba08caca92ae3e4ca71bb76c64aa565b176dc05d104d843c5a0167615ca627a1798b563ba1c5965fc4c656a5b6b40cb9aa5a01567e379375513e68485d562e6a0c86a0ab3a5667bd828811a5b57745197f01748456bdbac1bcc2
|8,0=>0x6f6362ccab5a55c05db15756597a62cd6dbea1786d6e569598895578a3bf
|9,0=>0x56946d4e5857
|10,0=>0x56
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_244 8 roots_244 ops++addP pm 1 dom_114 7 roots_114 ops++addP pm 2 dom_180 7 roots_180 ops++addP pm 3 dom_230 8 roots_230 ops++addP pm 4 dom_242 8 roots_242 ops++addP pm 5 dom_214 8 roots_214 ops++addP pm 6 dom_240 5 roots_240 ops++addP pm 7 dom_116 5 roots_116 ops++addP pm 8 dom_210 5 roots_210 ops++addP pm 9 dom_54 5 roots_54 ops++addP pm 10 dom_86 5 roots_86 ops++addP pm 11 dom_102 5 roots_102 ops++addP pm 12 dom_52 4 roots_52 ops++addP pm 13 dom_118 8 roots_118 ops++addP pm 14 dom_182 8 roots_182 ops++addP pm 15 dom_226 5 roots_226 ops++addP pm 16 dom_166 5 roots_166 ops++addP pm 17 dom_178 5 roots_178 ops++addP pm 18 dom_228 5 roots_228 ops++addP pm 19 dom_150 5 roots_150 ops++addP pm 20 dom_212 5 roots_212 ops++addP pm 21 dom_176 4 roots_176 ops++addP pm 22 dom_112 4 roots_112 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_246 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_52 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_176 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_112 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_244 8 s (0,roots_244.map (·&&&dom_244)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_246 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_244 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124)],[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124)],[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_246==dom_246)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_246 gM v ys):RunD true dom_246 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_246 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 10 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 46 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 170 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 42 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 170 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 127 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 127 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 30 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 30 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 6 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_246 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_246 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_246 roots_246 goal_246 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_246
theorem lowS_246:Lower true dom_246 roots_246 goal_246 11:=S_246.noCircuit
theorem lowS_249:Lower true dom_249 roots_249 goal_249 9:=lower_slice_b [(0x303030303030303000000000000000003030303030303030000000000000000,1,65)] (by decide +kernel) lowS_185
def isoMvS_111:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_111:Lower true dom_111 roots_111 goal_111 9:=lower_iso_b isoMvS_111 (by decide +kernel) lowS_95
def isoMvS_126:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_iso_b isoMvS_126 (by decide +kernel) lowS_119
def isoMvS_159:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_iso_b isoMvS_159 (by decide +kernel) lowS_95
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 10:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_125
def isoMvS_221:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 9:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_219
def isoMvS_222:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_215
def isoMvS_235:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_235:Lower true dom_235 roots_235 goal_235 9:=lower_iso_b isoMvS_235 (by decide +kernel) lowS_219
def isoMvS_250:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 9:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_243
def dzo_126_1:=0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def gzo_126_1:=0xaaaaaaaaaaaaaaaaaaaaaaa8aaa8aa00
def gsh_126_1:=0x55555555555555555555555455545500
theorem lowS_zo_126_1_54:Lower true dzo_126_1 roots_126 gzo_126_1 7:=lower_iso_b (d1:=dom_126) (r1:=roots_126) (T1:=gsh_126_1) [(dom_126,1)] (by decide +kernel) (lower_slice_b (T:=gsh_126_1) [(0x55005500550055005500550055005500,0,8),(0x55555555555555550000000000000000,0,64)] (by decide +kernel) lowS_54)
def dzo_58_1:=0xa0a0a0a0a0a0a0a
def gzo_58_1:=0xa0a0a080a080a00
def gsh_58_1:=0x505050405040500
theorem lowS_zo_58_1_50:Lower true dzo_58_1 roots_58 gzo_58_1 5:=lower_iso_b (d1:=dom_58) (r1:=roots_58) (T1:=gsh_58_1) [(dom_58,1)] (by decide +kernel) (lower_slice_b (T:=gsh_58_1) [(0x500050005000500,0,8)] (by decide +kernel) lowS_50)
def dzo_51_8:=0xf000f000f000f00
def gzo_51_8:=0xf000e000e000a00
def gsh_51_8:=0xf000e000e000a
theorem lowS_zo_51_8_50:Lower true dzo_51_8 roots_51 gzo_51_8 5:=lower_iso_b (d1:=dom_51) (r1:=roots_51) (T1:=gsh_51_8) [(dom_51,8)] (by decide +kernel) (lower_slice_b (T:=gsh_51_8) [(0xa000a000a000a,0,1)] (by decide +kernel) lowS_50)
def dzo_75_4:=0xf0f0000000000000f0f0
def gzo_75_4:=0xf0e0000000000000a000
def gsh_75_4:=0xf0e0000000000000a00
theorem lowS_zo_75_4_75:Lower true dzo_75_4 roots_75 gzo_75_4 5:=lower_iso_b (d1:=dom_75) (r1:=roots_75) (T1:=gsh_75_4) [(dom_75,4)] (by decide +kernel) (lower_slice_b (T:=gsh_75_4) [] (by decide +kernel) lowS_75)
def dzo_54_1:=0xaa00aa00aa00aa
def gzo_54_1:=0xaa00a800a80000
def gsh_54_1:=0x55005400540000
theorem lowS_zo_54_1_54:Lower true dzo_54_1 roots_54 gzo_54_1 5:=lower_iso_b (d1:=dom_54) (r1:=roots_54) (T1:=gsh_54_1) [(dom_54,1)] (by decide +kernel) (lower_slice_b (T:=gsh_54_1) [] (by decide +kernel) lowS_54)
def dzo_55_8:=0xff00ff00ff00ff00
def gzo_55_8:=0xff00fe00fe00aa00
def gsh_55_8:=0xff00fe00fe00aa
theorem lowS_zo_55_8_54:Lower true dzo_55_8 roots_55 gzo_55_8 6:=lower_iso_b (d1:=dom_55) (r1:=roots_55) (T1:=gsh_55_8) [(dom_55,8)] (by decide +kernel) (lower_slice_b (T:=gsh_55_8) [(0xaa00aa00aa00aa,0,1)] (by decide +kernel) lowS_54)
def dzo_62_1:=0xaaaaaaaaaaaaaaaa
def gzo_62_1:=0xaaaaaaa8aaa8aa00
def gsh_62_1:=0x5555555455545500
theorem lowS_zo_62_1_54:Lower true dzo_62_1 roots_62 gzo_62_1 6:=lower_iso_b (d1:=dom_62) (r1:=roots_62) (T1:=gsh_62_1) [(dom_62,1)] (by decide +kernel) (lower_slice_b (T:=gsh_62_1) [(0x5500550055005500,0,8)] (by decide +kernel) lowS_54)
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0e00000f0f00000a000
def gsh_107_4:=0xf0f00000f0e00000f0f00000a00
theorem lowS_zo_107_4_75:Lower true dzo_107_4 roots_107 gzo_107_4 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xf0f0000000000000f0f00000000,0,32)] (by decide +kernel) lowS_75)
def dzo_119_8:=0xff00ff00ff00ff00ff00ff00ff00ff00
def gzo_119_8:=0xff00ff00ff00ff00ff00fe00fe00aa00
def gsh_119_8:=0xff00ff00ff00ff00ff00fe00fe00aa
theorem lowS_zo_119_8_54:Lower true dzo_119_8 roots_119 gzo_119_8 7:=lower_iso_b (d1:=dom_119) (r1:=roots_119) (T1:=gsh_119_8) [(dom_119,8)] (by decide +kernel) (lower_slice_b (T:=gsh_119_8) [(0xaa00aa00aa00aa00aa00aa00aa00aa,0,1),(0xff00ff00ff00ff0000000000000000,0,64)] (by decide +kernel) lowS_54)
def dzo_118_1:=0xaa00aa00aa00aa00aa00aa00aa00aa
def gzo_118_1:=0xaa00aa00aa00aa00aa00a800a80000
def gsh_118_1:=0x550055005500550055005400540000
theorem lowS_zo_118_1_54:Lower true dzo_118_1 roots_118 gzo_118_1 6:=lower_iso_b (d1:=dom_118) (r1:=roots_118) (T1:=gsh_118_1) [(dom_118,1)] (by decide +kernel) (lower_slice_b (T:=gsh_118_1) [(0x550055005500550000000000000000,0,64)] (by decide +kernel) lowS_54)
def dzo_115_8:=0xf000f000f000f000f000f000f000f00
def gzo_115_8:=0xf000f000f000f000f000e000e000a00
def gsh_115_8:=0xf000f000f000f000f000e000e000a
theorem lowS_zo_115_8_50:Lower true dzo_115_8 roots_115 gzo_115_8 6:=lower_iso_b (d1:=dom_115) (r1:=roots_115) (T1:=gsh_115_8) [(dom_115,8)] (by decide +kernel) (lower_slice_b (T:=gsh_115_8) [(0xa000a000a000a000a000a000a000a,0,1),(0xf000f000f000f0000000000000000,0,64)] (by decide +kernel) lowS_50)
def dzo_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_123_4:=0xf0f0f0f0f0f0f0e0f0f0f0f0f0f0a000
def gsh_123_4:=0xf0f0f0f0f0f0f0e0f0f0f0f0f0f0a00
theorem lowS_zo_123_4_75:Lower true dzo_123_4 roots_123 gzo_123_4 7:=lower_iso_b (d1:=dom_123) (r1:=roots_123) (T1:=gsh_123_4) [(dom_123,4)] (by decide +kernel) (lower_slice_b (T:=gsh_123_4) [(0xf0f00000f0f00000f0f00000f0f0000,0,16),(0xf0f0f0f000000000f0f0f0f00000000,0,32)] (by decide +kernel) lowS_75)
def dzo_118_8:=0x55005500550055005500550055005500
def gzo_118_8:=0x55005500550055005500540054000000
def gsh_118_8:=0x550055005500550055005400540000
theorem lowS_zo_118_8_54:Lower true dzo_118_8 roots_118 gzo_118_8 6:=lower_iso_b (d1:=dom_118) (r1:=roots_118) (T1:=gsh_118_8) [(dom_118,8)] (by decide +kernel) (lower_slice_b (T:=gsh_118_8) [(0x550055005500550000000000000000,0,64)] (by decide +kernel) lowS_54)
def dzo_91_4:=0xf0f0f0f000000000f0f0f0f0
def gzo_91_4:=0xf0f0f0e000000000f0f0a000
def gsh_91_4:=0xf0f0f0e000000000f0f0a00
theorem lowS_zo_91_4_75:Lower true dzo_91_4 roots_91 gzo_91_4 6:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_4) [(dom_91,4)] (by decide +kernel) (lower_slice_b (T:=gsh_91_4) [(0xf0f0000000000000f0f0000,0,16)] (by decide +kernel) lowS_75)
def dzo_122_1:=0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def gzo_122_1:=0xa0a0a0a0a0a0a0a0a0a0a080a080a00
def gsh_122_1:=0x5050505050505050505050405040500
theorem lowS_zo_122_1_50:Lower true dzo_122_1 roots_122 gzo_122_1 6:=lower_iso_b (d1:=dom_122) (r1:=roots_122) (T1:=gsh_122_1) [(dom_122,1)] (by decide +kernel) (lower_slice_b (T:=gsh_122_1) [(0x5000500050005000500050005000500,0,8),(0x5050505050505050000000000000000,0,64)] (by decide +kernel) lowS_50)
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,65),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(4,20),(4,36),(5,13),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,72),(10,11),(10,26),(10,42),(10,74),(12,13),(12,28),(12,44),(12,76),(14,15),(14,30),(14,46),(14,78),(16,18),(16,20),(16,48),(16,80),(17,19),(17,21),(17,25),(17,49),(17,81),(24,25),(24,26),(24,28),(24,56),(24,88),(32,34),(32,36),(32,48),(32,96),(33,35),(33,37),(33,41),(33,49),(33,97),(40,41),(40,42),(40,44),(40,56),(40,104),(64,65),(64,66),(64,72),(64,80),(64,96),(68,69),(68,70),(68,76),(68,84),(68,100)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|5=>28
|6=>167
|7=>284
|8=>201
|9=>62
|10=>7
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xe0d81a826ea4ae09244771ab17001868c6367f51525a84ec134cd73498533f8533dc743c6053b0153119b303662afac21e541ee8915be81543213b13110ff0a61d07c5d06e75
|6,0=>0x88c2c85afd8512484675837bb8257c812437f8327c4eb75e9770c5e708ac700186ec9a6e9e86e8ce6e6976e5ac6a9c668c636870c6516d6421f61cd6604025fac75f0915e9bc5e4c45e1255d1f15cb615c4645a52d5a18659caf5862b554e25496e533af52ace516304ed934e8504de5f4d6e649fad49d084847446295443ee4334642a0b41ebb41c29412fe3e2d03b1f037f8a357183514b336bd313db2f2f02da902d5732b8272b7ca2948e291df27f4627eab27cf727c75243ae240b12305322850227372203021ed3219e6203d51f5ff1f0c01c9e41c62c1c1ce1b6991ac5d19a4018ce417ba016e1a160cc155a514dfe14d231495d141a613661122b810c600f9e60f2b70ef800e62c0dd990d8590d64b0c6d00c6180bd350b28d0ad0309f0108bca08b580744f0609d05faa058d902f9901262010f900fed00e9300a1a
|6,1=>0xdfc0fdc9cdd9a0fd6766cfad3c948fc2afebe9ebbcd82bc55ab4323af8b0aea9ea99b4a9920a89e2a86e5a7bb6a3edda3665a2b4ea169ea10b7a033f9de369d4659cf8f9b0ef9aba496e719616095ff091780900cd8dffa8cea58bf0f899b1891dd
|7,0=>0x354e1349c6345073325832de03262f324d331d6d319693154d311512f1ef2ebd72c46f2bdaa2bc4a2ba9c2b8c72a40829f0a29c57293d5291df29030289d72893d2885d27c75267cb25a882547c230da2309d22c9e22b0b2288221f6521a4c20dfe20b26205ac203d51fe571f77e1e6df1dfcc1d8b41d6f81d4021bdc61b3931b0f91ac2f1937718b07187ea186d4172211715016bea16726161621590e1513314dfe136b012c2b12572122e611b53115ff10f5010d8b106c8100cc0ffd80fe840fdbc0fb530f8110f6400f3230f2b90ecf70ebb90eac20e6900e4e20c8760c5dd0b9560b8480b46a0b10c0a9ef0a42509c9509a69099a8098fb0938c08d68080ed07977071cb06eb706cb7065b805b3c05b21059880572a0554d04f5804e17040120393803646034d802efe02b910229201f8a0194700698004ac0041200079
|7,1=>0xaea9eae1c9ad6d8ac840ac3ebaacdba9830a8f64a881da7fc9a7b19a5c79a36ef9fc3f9f2439e2519d6609befc9adcf95efe955139444392737907ee9021f9004f8fcfe8eae58e6988c5978b97c8a5ee8a5878a255883a1849c88388a82b28803eb7fc9f7f3097ecdb7e8aa7a85d78ed076d9c73276729ed71b537181870e51700186f21c6e95a6e1dd6bede68e8e6421f62952618a760fce60d27608c3600685fd175e4c45e22c5e1895aeee5aa1f5a6b359d9158aa2582b257d8b562655562854fc15481f53c9f53bd053b91538c3537a4522b151828516085067a4f7684ee094e85d4cadb4ca514ba5748c9e4895546dfe469424670245be742b80424714238741b51411594114940d2c405023fecd3ecb83e3b73db343d22a3c6fe3c6c83c3083c2cb3c1863c0cc3abb93aad138b3b38958385fa380df375cd3710c35f9f
|7,2=>0xfc383f9a67ea033e774ce58ace451de35cfd93bbd6e88cf137cdd3fcb08fca5fbc84cbc7808c4563c28d0c26dac22cbbff50bc7eebab0fb80c8b69b8b562eb5214b262db1250
|8,0=>0x57b3156bd4562d5558a354a425118350c88500d54e97b4e2454cadb4a86e4906c48b9a4885d478e54735946afc4664145e9f459e144ea744e244453143c6142c9e4206740dfe405bd3f3f23e3e43d8f1394e2364263623135f7b3567134b1b32d7b327d931b82307b82fcbe2ecda2e2fe2e0842e02c2d3a22cbba2b5e629a532931c292f128a282839d273b32709126e42266cd266222626725c8c24cd623b5322ffd203d51f5651f4ea1eafc1debb1dbea1d9561cb801c85d1ba101b9141b6141b0f91a50e19fbd17cbb16c9e16a721606715f8c15e2c1552c14fb614dfe1471d141e013ef013c89125c211e0111aa911508114a2111d80fed80fa180f41c0eca80ebb90e1c20da290bbd00b8470b02f0ad6a0acb30aa520997009671084d807c170719b05d2605c1c055de051f804cc9035c80314402b6201a3b012030064e
|8,1=>0xe65a3e26dbde3a1da7c5d9c1cd3a1cd31ebcbf56c6a81bff21bf3bfbdb3ebcce3b9d21b4d6cb3d5ab394bb31e7b0e4bb0329ad8ada43319b76099c2a94d6f9427993a2a908c39022c8b7ee8a32489e4c89a38881f7872458454f7f5037dd797dc9a7d56f7c20e7bc6e7a97b79a2178f9c78adb782b276d9c76afd75cb673f90733387212b7195c6febf6de3e6bf2b6b400677c1664f665c3e6408e639346295261f7b6114d60dc96082b5e5555e22c5cb625c0695854f
|9,0=>0xe4e3bd1688cdf3fcdcabc509cbf443bdd15b9c81b704bab3a1a8a85a24cba21fa9bd3f970e58a22c86f7086c6d838d3750a86fa536a3f76765b5e22c585bf577fb4816946f5d4453144481417553a67932dba3254f323e42f4812258c2150d1e23a1c7781ab8a19d3e16c5d16ab616568156f1155f212bb11284a10b800c8070bb3f0a2af0a1040969708daf0707503e2f0398a037ed02baf02084
|10,0=>0xa1f3f8d3bf83c7d5254f43a533b65b05c14
|11,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x333333330000000033330000fffffffffffffffff0f0f0f0f0f0f0f0333333333333333333333333333300000000ffff0000ffff0000ffff0000000000000000ffffffff00000000ffff0000ffffffffffffeeeeccccccccccccccccffffffffffffffff0f0f0f0f0f0f0000ffff0000ffff0000ffff0000ffff000003030303030311110303030303030000ffffffffffffffff0000000000000000ffffffff00000000ffffffff00000000ffffffffffffffffffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ffffffccffffffccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000
|0,1=>0xffffffffffffff00ffffffffffffff00ffffffffffffffffffffffff00000000ffffffffffffffccfcfcfcfcfcfcfccc00bb00bb00bb00bb00ab00ab00ab00aacccccccccccccccccccccccccccccccc5f5f5f5f5f5f55550f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f000055555555555555550000000000000000ffffffffffff0000ffffffffffff0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffaaaaaaaaaaaaaaaa131313131313111103030303030300003333333333333333030303030303000000ff00ff00ff00ff00aa00aa00aa00aaffffffffffffffffffffffffffff000000003333000033330000333300000000
|0,2=>0x333033303330033030303030303000000000000ffff00ff00000000ffff000011111111111111110303030303030000ffffffffffffff00ffff0000ffff0000ffcfffcfffcfffcccccccccccccccccc33333333000011113333333333330000fffffffffffffafafffff0f0f0f0f0f0ffffffffffffff00ffff000000000000ffffff00ffffff00ffffff00ffffff00ffffffffffffff00ffffffff00000000ffffffffffffffccffffccccccccccccffffffffffffccccfcfcfcfcfcfccccc5511551155115511551155115511550003030303030303030303030303030000ffffffffffffaaaaffff0000ffff0000ffffffffffffff00f0f0f0f0f0f0f000
|0,3=>0x5555555555555555550555055505550000000000ffffffff000000000f0f000000000000000055550000ffff000000000000ffff000000ff0000ffff0000000033333333333333333303330333033300ffffff00ffffff000000000000000000555555555555555555005500550055005500550055555555550055005555550000bb00bb00bb00bb00bb00bb00bb00aa000033330000333300000303000000000000000033333333000000000303000000ff00ff00ff00ff00af00af00af00aaffffffffffffffaaff00ff00ff00ff0000000000111111113333333333330000ffffffffffffffffff00ff00ff00ff00ffafffafffafffaaaaaaaaaaaaaaaaaa
|0,4=>0xff33ff33ff33ff33ff33ff33ff33ff00ffff5555ffff5555ffff0000ffff000000000000ffff555500000000ffff000033333333333333333030303030300000000000ff000000ffffffffffffff0000ffffaaaaffffaaaaffffaaaaffffaaaaffffffffffff5555ffffffffffff000033333333333311113333333333330000ffffffff00005555ffffffffffff0000ffffffffffffff000000000000000000ffffffffffffffcccccccccccccccccc00000000000000ff00000000ffff0000000000000000ffff0000000000000000ffffffffaaaaaaaa0000000000000000ffffffffaaaaaaaaffffffffaaaaaaaaffffffffeeeeeeeecccccccccccccccc
|0,5=>0xfcfffcfffcffccccfcfcfcfcfcfcccccffffffffffffffffffffffffffffff003333333333330033333333333333000000ff00ff00ff00ff00ff00ff00ff00aaffffffffffffffffffffffffaaaaaaaaffff0000ffff5555ffff000000000000ffffafafffffaaaaffff0000ffff0000ffffffffffffaaaa0000000000000000ffffffffffffaaaaffffffffffffaaaa00000000000000000f0f0f0f0f0f0f000000ffff0000ffff0000ffff0000aaaa00ff00ff00ff00ff00ff00ff00aa00aaffffffffffffffffffffff00ffffff0055555555555555555555550055555500ffff5555ffff5555ffff5555ffff000055555555555555550505050505050000
|0,6=>0xffff00ffffff00ffffff0000ffff0000f5f5f5f5f5f5f5f5f0f0f0f0f0f0f0f0ffffffffffff00000000000000000000ffffffffffffff00ff00ff00ff00ff0033333333333333333333333333332222003300330033003300030003000300000f0f0f0f0f0fffff0f0f0f0f0f0f000003030303030333330303030303030000ffffffff0000ffffffffffff00000000ffffffffffff0000f0f0f0f0f0f000000f000f000f000f000f0f0f0f0f0f000000000000000000ffffff0000ffff0000ffff0000ffffffffffff0000ffff0000f0fff0fff0ff0000f0f0f0f0f0f00000f0fff0fff0fff0fff0f0f0f0f0f0f0f000ff00ff00ff00ff0000000000000000
|0,7=>0xaaaaaaaaaaaaaaaa0f0f0f0f0f0f0000f0f0f0f0f0f0fffff0f0f0f0f0f00000ff0fff0fff0fff00ff0fff0fff0fff0000330033003300333333333333330000f0f0f0f0f0f0ffff0000000000000000ffffffffff00ff000000000000000000000000000000333300000000000000000b0b0b0b0b0b0b0b0b0b0b0b0b0b0a0a00000000ffffffff000000000000000000ff00ff00ff000000ff00ff00ff0000aaffaaffaaffaaaaaaffaaffaaffaaaaff0fff0fff0fff000000000000000000ffffffffffffffffffffffffffffaaaa00000000ffffffff00000000ffffaaaa303030303030333330303030303000000fff0fff0fff00ff0f0f0f0f0f0f0000
|0,8=>0xffffffffffffcccccccccccccccccccc00ff00ff00ff00ff0f0f0f0f0f0f00003030303030303333000000000000000000000000ffffaaaa00000000ffff00000000ffff0000ffff00000f0f00000000000000000000ffffffffffff000000000303030303030101030303030303000000aa00aa00aa00ff00aa00aa00aa00aa0f0f0f0f0f0f55550f0f0f0f0f0f00000000000000000000ff0fff0fff0fff00bbbbbbbbbbbbbbbbababababababaaaa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00ffffffffffffffaaaaaaaaaaaaaaaaaa11111111111111111111111111110000000055550000555500000000ffff00000000000000000000ffffffffffffff00
|0,9=>0xffffffffffffffffffffffffff00ff00555555555555555555555555550055000000ffff0000aaaa0000ffff000000000000000000000000ffffffffffffaaaa0000ffff0000ffff0000000000000000ffffffffffffffffffffaaaaffffaaaa00ff00ff00ff00ff00ff00ff00000000ffff00ffffff00ffffff00ffffff000000000000555555550000000055550000ffffffff00005555ffff00000000000055505550555055555500550055005500ffffffffffff3333ffffffffffff0000ffffffffffffffff03030303030300000f0f0f0f0f0f000f0f0f0f0f0f0f000000000000000000000f0f0f0f0f0f0000ffffffffffffffffafafafafafafaaaa
|0,10=>0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffff0000ff00000055555555555500005555555555550000ff55ff55ff55ff00ff55ff55ff55ff000000ffff0000ffff0000ffff0000ff0055555555555555555555555555555500000000000000ffff000000000000aaaaffffffff0000ffffffffffff0000aaaa00ff00ff00ff00ff00ff00ff00ff0000afafafafafafaaaaafafafafafafaaaaafafafafafafaaaa0000000000000000ffffffffffffffffff0fff0fff0fff000f0f0f0f0f0f05050f0f0f0f0f0f0000ffffffffffffaaaaaaaaaaaaaaaaaaaa00000000ffffaaaa00000000ffffaaaaffffffff55555555ffffffff00000000
|0,11=>0xffffffffffff00ffffffffffffff000000ff00ff00ff00ff00ff00aa00ff00aa0f000f000f0000000f0f0f0f0f0f00005555555555555555555500005555000000000000000000000000ffff0000ff0055555555555500000000000000000000ff55ff55ff55ff00ff00ff00ff00ff00ff00ffffff00ffffff00ffffff00ff00ff00ff00ff00ff00ffffffffffff0000ffffffaaffffffaaaaaaaaaaaaaaaaaa00000000ffffffff00000000ffffff00ff00ff00ffffffffff00ff00ffffff00aaaaffffaaaaffffaaaaffffaaaaaaaa0000000000000000ffffffffffff000055005555550055555500555555005500000000000000ffffffff0000ffff0000
|0,12=>0xf0f0f0f0f0f0fffff0f0f0f0f0f0fafaffffffff00ff00ffffffffff000000000000000055555555ffffffff00000000f0f0f0f0f0f0fffff000f000f000ff00ffffff00ffffff00ffffff0000000000fff0fff0fff0ffffff00ff00ff00ff0000f000f000f000ff0000000000000000f0f0f0f0f0f0f5f5f0f0f0f0f0f0f0f0000000000000000000000000ffffaaaaffffffffffffffff00000000ffffaaaa00000000000055550000000000000000ffffffff00005555ffffffff00000000000000ff000000ff000000ff0000000000ff00ff00ff00ff00ff000000ff0000ffffffff00ff00ffffffffff00ff0000000000000000ffff000000000000ff00
|0,13=>0xff00ff00ff00ff00fa00fa00fa00fa0000555500000000ffffffff0000000000ff00ff00ff00ff00f000f000f000f0ffffffffffffffff5555555555550000ffffaaaaffffaaaa000000000000000000ff00ff00ff00ffffffffffffff0000f5f5f5f5f5f50000f0f0f0f0f0f0000000000000000000005555555555550000ff00ff00ff00ff00ff55ff55ff55ff00ddddddddddddcccccccccccccccccccc0000ffff000055550000ffff00000000f5f5f5f5f5f5f0f0f0f0f0f0f0f0f0f0aaaaaaaaaaaa0000ffffffffffff0000bbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaa55555555555555555555555500000000aaaaaaaaaaaaffffaaaaaaaaaaaaaaaa
|0,14=>0xffff0000ffff0000aaaa0000aaaa000000ff000000ff0000000000000000ffffffff000000ffffffffff00000000fffffffffffff0f0f0f0f0f0f0f0f0f0ffffffffffff0000aaaaaaaaaaaa00000000ffff0000ff000000ffff0000ff0000000000ffffffff00000000f0f0f0f0ffffffffaaaaaaaaffff0000aaaa0000fffff0fffffff0fffffff0f0fffff0f0f0f0fffff0f0fffff0f0f0f0f0f0f0f055555555555555555555555555550000f0f0f0f0fffffffff0f0f0f0f0f0f0f00000000000ff00ff0000000000000000f0f0f0f0f0fff0fff0f0f0f0f0f0f0f0fffffff0fffffff0f0f0f0f0f0f0f0f0fffffffffffffffffafafafafafafafa
|0,15=>0xffff0000aaaa0000ffff0000aaaa000000000000aaaaaaaaaaaaaaaaaaaaf0f0f0f0f0f0fffff0f0f0f0f0f0f0f00f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0aff00ff00ff00ffff000000000000000000ff00ff00ff00000000000000000000ff00ff00ff00ff00ffffffffffffff00ff00ff00ff000000ffffffffffff0000ffffffffffffffff0000ffff0000ff00ffffffaaffffffaaff00ff00ff00ff00ff00ff00ffffffffff00ff00ff00ff0055005500555555555500550055005500ffff00ffffff00ffffff00f0ffff00f00000ffff0000ffff0000ff000000ff00ffffffff0000ffffffffffff0000ff00ffffffff55555555ffffffff55550000
|1,0=>0xffff0000ffff0000f0f00000f0f0fffffffffffffffffffff0f0fffff0f00000000000000000ffffaaaaffffaaaa
|_,_=>0
def sP:Nat→Nat
|0=>0x18045e06018383601060b80a08018045a060f0b0061b008003c2c01858020d02820062b008240a0401858022a0f0a442030d8044c250200c2c010f0100624008141003118880c1e1080c36010c814080305004321e0400c3a010282002130e0180a0801854280602820021309018220307004200f01838020d0602c0a08018280209028200601038180a04018080200
|1=>0xf0200616200040a080186c7e19030440a080183836390b8200601098f80c1e1080c2c1b008f406160d804782e030141003008ec120602820061b1c8000c26020a006160d8040a0801858720d03078080801858363802820060109818300504058020d1b8182e03008d86a060282002131a0180a081986c2a190f0200616008c80a081886c6019028200601098180a08
|2=>0x68180a0801838363906014a2030706c020c0282006012804c0c0502020060e0d8e00a081886c021923014104f01804440602938060e0d804181e0400c1c1b009340a040400c020d2612c0a04018583601029280803070041a050400c2c15240188e050200c2c1b0081410030d8e412060f0200616228040a04018583601220141003008500c180f010061b008648611
|3=>0x188036010282036010c9700c050400c36300c8182e1e1080c2c1b0081410030d804120608814100e0d804a81e04168060e0d8040a590186c02190305c0a040185814010281010030d804ac170280c02131b01822050400c020d26014101b00800a8060b878060e0d804aa0504058020d2a0182e1e0200c2c1b2907810030b100020c0882006011103c0c050400c2c01
|4=>0x185836013398c061b008640c1e0200ccc1b0081410030d804ca060282066160d8540a043200c2c1b008781003008881e060f18c060e0d80418050403836012a0302e050200c1c1b2901410030d804340602820065f0081822050400c36012b01458030d8043206028200616009740c1f028200601098183c260400c1c1b008141003008645e060183836010602c0a04
|5=>0x307808030b06cea050400c1c1b1c02c08030706c020c0581410030d80412740f09808030b06c021102820060e009ac2208018383601390440a08018581401028200601069c40c050400c026b000180a080182802190301410310d804e0060b878de030706c02050400cdc01240183c0436058360102810100307004d6050400c0213350180a0801804d268030444c04
|6=>0xd804180b0307810030706c027202820067e008340c05041f40601098183c080186c02003d01410030b004f8060f0b006160d8040a080180426063d87810030b0041a7a02820060109818f2050400c020d3c01822030706c020c0585c3c080706c02120f020060e00834ee050406c02091a01822030b004200f0300c36010003016060f020062400818061600834180b
|7=>0x803c0c170f0102c1b008480a08018ac0219030141003008ec320602820061b00a1c0c0504218061b008240a0801874020608820060e008341e050400d0a01098180a0801804260602820060106a100c050400c36830c8180a080180504220307810030d80432460281006160d805028002820061b008240a08018045e0602820061b009fc0c260200c2c1b0082c0616
|8=>0x28200601098191a050400c025d0c8180a080d804005c03014101600834b80602810060e0d8051805020201c1b009702e05040cc2c1b0a8781003120042e030d805163e0307914040185836010282006010981886050400c024844818220801838020d0581410030d80412460282036010ca200c1e0400c1c010683c2e1e0200cc21b0081410030a80426060b80c2c01
|9=>0x9ac320602820061b4a8640c050400c0268030141003009c05e06028200661008340c94028200601098180a08018041a930301410030082426060282006012ea480c030b06c020c170180a080d80522120301410034800426060f0100616478043c0801838020d05814100307004ba0608814100e0d804b8050400c3601470183e1e0200c36010c8141003008349806
|10=>0x188583601230440a080b06c0212030780a980400c1c1b0081410030b00490060c07810030b23c021f0f020060e0d8042e050200cdc1b008180a0801858020d031e40a040400c1c1b00a5c0a044b00c2c1b0081822410f020060e0d804ae1e0400c36010c818060e0d804180b030141003009a00c430186c02190602c0c05040c436010c9d02e050400c022f030141003
|11=>0x282148030d80432060293810030d805460602820060e0d80418600281006160da880c050200c1c1b00a8540050400c2c01240180a040186c02000326c2e1e0400c2c1b4f0183c080185836014e8182e050200c1c1b0a80422050400cc21b0081822050200c1c1b008300a08018041a00032703c050400c2c1b0081408030b0041a064d81534080183836010585c0a08
|12=>0x9d80a210185836010305c0a030b06c02ab030780a080185836aa0301410030d80412063d8440a040183836014d9043c080183836010601410030b0041a82030440a030d804000c0305d4008019b83601030440a0801838020d0f02006160d80418420baa010030b06c02060881408030b06c023a02820061b008654e0608814061600834180602820061b008640ca5
|13=>0x400c2c1b0a8183c040400c2c1b009c80a08019843601060180a080185836b1060182e1e0200c36010c818b6050400c2c01068180ab00185836010307810ae0185836010b878083101858360102820fa030d80412062b81410030b0041a060b8149c030b06c2a06028202c1b0084818060f02158160d8040c174f87810030706c02050200c1c1b0082c861e0200c2c1b
|14=>0x8240c110280c2c1b008300c05040c42c1b5b05c0a2c018583601032bc3c0401858360106044b6050400c1c1b0081410030d85402910304410030b06c02b50305c3c040183836010307808085a00c2c1b0081408030b00802050400c1c1b5980418170282006010484c0c050400c360138018c0050400c2c01068182e050405836012e018b6050400c3601000189205
|15=>0x200c2c1b0083016175013806160d8040c1e02820060e0dacc02050400c36015e818c0050400c2c015e0340c1e02820060e0d8e40a040400c1c1b00aec0a080186c02090307810030b06c02580f01410030706c02550b81408030b06c72060282172160d8040c1e0281010030b06ca41e02810060e0d804181e0282006160dac40cb70282006160d8040c5702820061b
|16=>0x185836010282006010c84c0c050400c2c15008340c1e0200c2c1b0082d36110f014060e0d80418050400c36010d0180a080185836380305c08030d804320b0301410030d80432c0030440a080183836015e01410030b004ba060b99cc6030b06c02060b8140616008342006028202c1b00af816060f0141003070041a1e0400c36010c81886050400c36015e0000c1e
|17=>0x18581401030780a08018583601632c80a080185836390301410030b0041a062199c08030b06c020b0315c0a080186c2a190305cce04018583601030440a08018383615008140808018041a000305d88080185836010307810030b06c02b50305c08030706c020b0301410030706c020c6181410030d85402000301410030d80546060c30410030b06c020b0307c3c04
|18=>0xf02006160d8045c060281160030b06c02060f015960801838360102810060e0d804169b5002006160d80416060f01010ae0185836010281042030b06c02060282006200d8040c170280c2c01068300c174f87808030b06c020504328061b008640c050400c36010c819921e028201c1b00950220502020060e008340a0801b2036010301410030d85402090305c0a08
|19=>0xb0041a062481410033706c02065f81410030706c02060b87810030706c021839814080801838360102820060e0d804780602820061b00af40c1e1082006160d8040a080d8043212030799a080185836014005c3c080185836015f81410030d804320602820061b00864a0060282006cc0d804320602820061b008240c4302820060e0d854020c088141003008340006
|20=>0x29bc06160d80478060b87808030d80432170400c2c1b008b80c053180c36010c81886050400c2c1b0a9609208018583601268180a4a0200c3601000180a0801b3c360103014940401858020d0305c9c030b06c024d031cc22050400c1c1b008440a0801858020d032fc0a080186c02920307810033306c02063981410030d80400060f014de08018383601398141003
|21=>0x185836830305c3c080185836012307858030b06c02110282006160d8040c050400c36a60a8640c050400c3601348182208018383601058182e1e0185836012a8182e1e0200c1c1b0081410030da4002090301410030706c02bc0581410030b348020d03014101b0a80432120305c3c080183836016881410030db4002190304410030d804320b0301410030b004d606
|22=>0x400c2cd6008183c08018383601058180a08019f836010305c08030706c020b0282006160d855aa06028200601098182e1e0200c2c1b008603c630400c1c1b0081410033086c023c0307810030706c02430282006010486426060185836010602c0c050400c2c1b510183c050200c2c1b00b0c22050405836012a0182e1e0200c2c1b00b080a0801b5036010305c0a08
|23=>0x3086c0211028200616009ac0c050400c020d0c81822050400c1c1b00a9c3c05020202c1b008480a081886c0219031800a080186c0200538182e1e3780c2c1b008180a0801858020d538180a080186c028403014080801858026b0301408b0018583601028200601068880c0502020060e0d8054e17028202c1b00a200c050400c36013481886490282006160d8040c05
|24=>0xc8182e050186c0209458180a080186c0219033140a086b85836010304410030706c020b0880c2c1b00830160602820061b00a8c0c17029bc060e0d8040c1e0200c2c1b0090c0a080186c0291030603e170f01006160d8040a0801838020d0301006160d804180b0305c0a080186c021a0305c0a6f0186c02190305c0a0801858025d0307810033306c021e028101003
|25=>0x183836010581410860186c02190304410030b0041a0f0301410030d80412060c01410030082426060b814100e0d80424060881410030706c0218028202c1b009700c0502020061b00a100c05020200601068880c1102820067e0d8040c050400db21b0081900110282006160d8042e050406c0219090180a080186c0200030600a0801858020d0306100050400c3601
|26=>0xb81410030084c0cda0282006160d8040c7302820061b008640c170185836010602c0c1e0400c2c010683c0c1102820060e008340c110282006160d8048c050400c3601049400c49028200616009200c050400c36010c8188c11028200601068640c1e0400c2c8f008180a040400c1c01068182e050400c2c013581822050400c36014201822050400c020d110183c08
|27=>0x400c1c1b0085c0a4e018583601030603c0513820060e0d8040a080186c0291030144e04018583601058180a080183836012181410030b06c02dc0301410030b06c2adb0282006160d9d40c170f01006160d804861e0200c2c1b009b40a080189002060f020061b0080016060f02006160083416060881410160d804b80602820061b0086832060f01006160d8041843
|28=>0xd8040c170400c2c1b0082c0cd30282006160d8040c495001410030b06c02060b87810030b06c2a01030440808018583601058180a0801b8436010301410030b06c02d1060180a040185836016d814100e0d805be0602820060e0d80416060881410030b06c0299031240a0801858360103061bc080185836010301408080183836016e8440a040400c1c1b008180a63
|29=>0x8180a0801858020d0305c3c080185836010310c2e050400cc21b00818c01e02820060e0d804c0050400c2c1b598040c1f0881410030b06c02060f02006160d8040c6d0b81408030b06c02063001410037206c029b0282006160d804aa060f01410030b06c02e5030149c0801838360103014080801b9036013b81408030b06c020c0301410037106c0206028840616
|30=>0x2020060e0d805781102820060e0d8043c040400c2c1b009dc3c050400dcc1b008183c05040583601090182205018583601060182e053780c2c1b008182e050400c2c1b00b000c1702820061b0a804320602820061b008000c1e0281010310185836010282006160d8052e060881534080185836010319c0a080183836014d85c0a530200c2c1b008180a083600c2c1b
|31=>0x9d80c170298c06160d8040c050400c2c1b00b600cb20282006160d8040c60028200616200040c0502020060e0d85402115787810030b06c02062b85c0a08018583615030780808018583601058180a080186c02090301410030706c02a10301494040183836010282006160d80416060c05c0a08018383615008183c0502020060e0d8040c1e0282006610d8040c05
|32=>0x2d8780a080183836010293810030b06c2a060887810030b06c020b030780a270200c2c1b0081408080183836013b81596080185836010315c2e050200c2c1b008180a080186c0219030600a04043a006160d8040c050400c2c1b008198aa00293810030b06c0206028202c1b009500c050400c1c1b008302e050400c2c1b00b940c057382006610d8040c1e0400c2c1b
|33=>0xd80400060281010030b06c029703014080801858020d0301410037606c02064f8780a040400c2c1b0085c0a040185836015e01822050400c2c1b00818c0051602006160d8040c050400c2c1b00bac0c05040c42c1b00ba80c050400c2c1b00aec0c0502020060e0d80416060b81410033086c02060f020060e0d805d217028202c1b008480cbf0b81410030b06c0206
|34=>0x28200616008340cf00282006160d8040c410282006160dbbc0c050200c2c1b00a840c110281010030706c0217028202c1b0a8042406028201c1b008480ced0282006160d8040c170282006160db4002060885c10030b06c020b030153408018583601058183c054c02006160d8040c170298c06160d8040c430282006160d8040c430f87810030b06c0206028101003
|35=>0x400c1c1b008780a0801b9836010881410030b06c020602bcc10030706c02065901410030b06c2a01031cc0a080185836010301410030b06d6601060180a08018591e010307c0a08018383601030149c08018583601268183c0801858360136bc40a080185836010301408030b06c020b0310c3e050400c36010c81822050400c36010001822050200c2c1b008193611
|36=>0xa8040c170f020060e0d8040c050400c2c1b00bdc0c05043d82c1b008180a080185836010630c0c170f020061b008640c1e0400c1c1b009dc3c050202006160d80584050400c2c1b00b540c180f01010030b06c020b0293810033706c02060f01410030b06d66010301410030b06d44060281010030b06c02bb030780a080185836012a8180a080185836f4030780a04
|37=>0x8300c050400c2c1b00819f4050200c2c1b0082c0c9b7c81410030b06c02060881410030b06c02062185c0a0801858020d030440a040400c3601000182e05040c42c1b00818c01e028202c1b009500c110281010030b0041a060281010030706c020b2481410030b06c02067c01410030b06c0206300780a040400c2c1b008600a080185836015481822050400c2c1b
|38=>0xd8040c170f01006160d8040c1702820060e0d8040c184005c0a080185836010301410030b06c02a70305c0a080186c0219030602e050400c2c1b008198a730881410030b06c020602820fa030d80432060f014de080185836010301410030d80432063d81410030b06c02067d99c0a080183836010305c0a080186c0209031cc0a040400c2c1b008180a08018583615
|39=>0xc8180a0801bf43601030440a08018583601538180a080185836011e0180a080183836010310ce6170282006160d8040c050400c36017e018ae050400c2c1b0a8180a080186c02190310c2e1e0400c1c1b0085c0a08018583601031182217028200616008340c170200c2c1b0082c0c050400c3615008640c1e3182006160d8040c1e0400c2c1b0081886053182006e4
|40=>0xb06c020602a680808018583601031043c0801858360103014a6080185836010305c0a08018383601030780a08018583601030603c050400c2c1b00a6c0a27040c42c1b008180a080185836017f8182e050400c36010c8180a080183836013b81410030b06dfc060282006660d8040c170f01006160d8040a080186c02090c81822050400c1c1b0081822050400c3601
|41=>0x8180a080185836010338cae050400c2c1b008182e050400c2c1b00818304102820060e0d8040c050400c2c1b0081884053782006160d8040c600282006e60d8040c9b0f01410030b06c02d10301408030b06c02064d81410f50185836010301600080185836010301410310b06c02063001410030b06c72060281010030706c02670282006160d8040c1e029281003
|42=>0x400c2c1b00818ee050400c2c1b008300c050202006160d85402060881410030b06c020602c0410030706c02063381410030b06c02064d81410030b06c02ef032c80a080185836010301410030b06c02062181410310185836390307c2e050400c2c1b008180a6f0400c2c1b008180a08018383601030600a080185836015e0182e050200c2c1b008195e05138202c1b
|43=>0xd8040c050400c1c1b00818ee050400c2c1b009d80c050202006160d804160602820060e0d85402060b81410030b06c02062181410030b06c02063685c0a08018583615008183c050202006160d8040c050400c36010c8180a080183836016e81822050202006160d8040c050400cdc1b0081830050400c1c1b00c080c050400dc81b008180a0801b801c1b008180a04
|44=>0x1410030b06c020602820060e0d8040c170282006160d8040caf0282006160d8040c050202006160d8040c050400c2c1b00818ee050400c2c1b0a8040c050400c2c1b00818c01e0281010030b06c02050400c2c1b00a6cee0502020060e0d8040c050400cc21b008182217028200616
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x50302698128c08e60443020980f8c0766038301a980c8c05e602c301498098c0475020b00ed806ac030501530091803cc018600930031800cc0006
|6,0=>0x12db8951c49ae246711fb88e1c464c22b711238875c42ce20f71043880983f8c1f570f73879dc3c0e1d970e93872dc388e1bd70db386bdc350e1a170cd3864dc318e18570bf385ddc2e0e16970b13856dc2a8e14d70a3384fdc270e13170953848dc238e1166087b8421c202e0fa7079b83b1c1cae0de706bb8341c192e0c2705db82d1c15ae0a67
|6,1=>0x2093902dc808e3fd71fb38fbdc7d0e3e171ed38f51879ae3c671e030ee5c764e3ab71d238e75c72ce39061c4b8e09c6f6e37471b6b8d99c6bee35871a930d2dc688e33d719b38cbdc650e321718d38c4dc618e306617fb8be585e4e2eb717238b75c5ace2cf716438b05c574e2b3715638a95c53ce2986148b8a29c506e27c713ab89bd84d0e2626
|6,2=>0x147dca30e51172853940dc9f8e4f57277b13a1c9c2e4da7269b9331c98ae4be725bb92c1c954c4a3724e39255c91ce4877240391e5c8e4e46b723239175c8ace44f72252910dc878e43572173909dc840e4197
|7,0=>0x38939c2a0e0506fa837941baa0dc506da836941b2dcd88e6bc835a41ab20d49069c834ab9a360d0b067e733bb99be0ccf065f832bc193e0c8f063f831bc18c1cc510620830c418420c11060082fc417c20bd105e172ed3974a0b9505c282dd416ca0b5505a282cdb964e0b17058382bdc15ce0ad7056382aeb1559ca9d0546829f414da0a5d05268
|7,1=>0x481c23ee11e708eb8471c236e11a708cb8461c22ee116708ab8451c226e1127088b8441c21f1d0eae86d8432c217610ace84f7423c20fe106f0830741442082103108117404c20060ff307f183f4c1f860fb307d273e541f0dcf78e7b483d641e95cf3b079583c6c1e160efb077583b7b1d9e0ebf075783a7c1d1e0e7f07378398b1ca60e4307198
|7,2=>0x579c2bb595cb0add856b3ab3a158d0abf755bc2abe154f0a9f854bc2a3e150f0a80753c429c5d4d30a61852d3a94a14950a43751dc28ce14570a23850dc2851d4190a0484fe427d213d909e484ee42752139ae9c674dfba6e1d36109a884d0426621321098884c0425e212e1096884b04256212a1094884a0ba4e6126309298490c2469d225090b7
|7,3=>0x66e3b35219990cc5765ec32d6195b0ca6764f4325a191d0c86863f431da18dd0c6776303b16218a2ec4986213b0ea18650c2b7611c306e18270c0b8602b2ff617eb0bee75f342f7a17ad0bce85e342efa176eebaf85d43ae85d7330b9185c4c2e0616f4eb7285b5bad91d6b90b5665a742d1dd67f0b38759842ca5d644eb1a858942c2a1606eafb8
|7,4=>0x6dac36b9db50cda086cc436421b110d8086bcbb5c61ad30d6186acc35461a930d41869cc34c61a530d22768d4344a1a150d02867dbb3ce19d70ce38
|8,0=>0x7dd4becddf570fa477cdcbe4a5f132f8187bcc3dc9ded50f6287ad43d4a1e950f41979c4bcc5de512f20878bcbc3e1e0d2efe877bbbbba5dcb2edd876ac3b325d890ebb975a3bab21d472e9b8749c3a2e1d08ee7d773ac39b61cc92e5b97294b92ddc852e3b771a3b8b21c472e1a9709bb82e1c052dfb76f94b7aa1bc6edda96e9bb72e1b88edbd7
|8,1=>0x8e54c70de37711b298d5bc68e2335319288c54460662f3117188b4c458622b3115098a4bc5062271312f98934c4766229310c8882443f221e730eb88723c36e61a530c99860c42e6216310a988504c2622122f08988404c1e220e11067982fc415e209f1046981f440d6605b1024980ebc059e01b300587fec3fd61fdb0fe497eebbf561f992fc39
|8,2=>0x9ef44f56679cf3c689df44edde75d33a599cec4e56271b138589bec4dd626d9336399adc4d4a66933340999c44cbe664f131f898bc4c3e260d32fd997ac4bb265c912db9969c4b2a658332b989584caa22541129799474ca1a24fb32758936c4999e4bb325589273c9166479323489164488e6438f21399054c80de3f711f478f64479223b731d38
|8,3=>0x14247a0ebd059e81d140689ff44fdde7dd33e68
|9,0=>0x2c3b16158b06c5819ebfb35f58af6c57926bb915d39ae5c570a6b7335b27ad5456866b3315918ac53d60a2af335718ab44d5822ab1154f9aa3c54fe2a6f152f8a934d47a2a2d150e8a83453fa29ed14ee8a72cd37629ab14cc9a62452ee696714ab8a51c526e2928f48d7a42c51f268e7346b8a31c516e28a5344a8a21450ea2865142b7
|10,0=>0x5955ec9b16458b1ec58d62c5b16258
|11,0=>0x165c7
|_,_=>0
def wAt:=mkWire dB 259 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x4079028192486f0b861028210d9190f8180b80d04015028190d86a0c8610b85b02821040190b81a028190b85b040790d9092081802805028190b819008c602821018190d826028260c8190b85b04015018250c8190b85b0282102098028e9138180400d040190d8260c8190b85b028210284e0404e0d8260c8190b85b1406d138180400d04019028191006d0f8380b80d040150b0190d86a0c8610b85b02821
|1=>0x19612b8180b8050282100819028360b0360886f0407902819028213106d0b9840b181028210181a2f01b0880d02811040190f0230281902812040190b019040190f8380b80d028210b01902819041612b8180b805028210f0212d80f0f005028190d961040192b8180b805028210404e0d8260c8190b85b02821070340b019028110401902819298070200d040190d909208180280502819028360b0360886f
|2=>0xf8180b80d0401502819088230281102812040190b019040150886f040793306d028190b838040150b019009d904019028190b80f040153986f0880502811040190d9610b8192b8180b805068670886f0b819028210c9810b85b0282102821041810b0190181a0281904019019b50b818028210d8260c8190b85b028210d9a60c90d0b81a0282102099028e9138180400d0401904019028190b838040150b019
|3=>0x4019070340b01902811040190282100819019612b8180b805028213306d028190b838040150b019028260c8190b85b028360b0190886f0407902819028190b18104015040190181a0d8260c8190b85b02821028360886f0b8190a80f0081902819040191006d0f8380b80d028210b0190b019028360886f04079028190d8260c8190b85b028210d9c20c9810181a0b85b02821088670886f0b8190282104119
|4=>0x28110401902812040190b019018190f8180b80d02821018560081902811040190b01904265028192486f0b861028210081a028190d9b50b818040150b80d04015028190b0190b06104015040190081a0b8360886f0b819028210082e02812040190b019040790b01902805028190d9c20c9810181a0b85b110190b03602811040190d8260c8190b85b028210d9b504019028190b818040153980f0880502811
|5=>0x28050281902aa50b856040150081902811138180400d040190886f08823028110401953018008650b85b02821018250c8190b85b028210181a028190b01904019009b50b818028210292a0b01904005040190885b028110401a04019028214f8070f00d02819208300f02302821040190b0190b1810181a02811040190882302811040190b0190885b0886f02811040193981b0880504079028190401a0886f
|6=>0xc8190b85b028210b8050886f0b81902821040610282101ab5028190b807040150f00d04015028190b0190402e02812040190b01904019028190b80f040152b8100b80502821040192f0230f8190b80d028212f0070880d040790c9ed0c81a0b85b028210401a0b0190281104019028050407a028190b0190886f02811040190885b08823028110401904015028610b0610081a0b0190886f028110401920818
|7=>0xc81b0b85b028212f0170880d04079028190401904015028190b019020170d8e9138180400d040190407a028190b0190d8260c8190b85b028210c9810181a0b85b028210886f590190b81b028213980f2b8190b805028210885b04079028190b861028214d01702005040190f023028190181a04019028190b85b0886f0407902819021b7040190b8180282102819022bc0280d0401904019028190401501819
|8=>0x407a028190b0190c9830b85b02821008c601819028190b019488190c81b0b85b028212b8180b80504015028192d8230f005028190b019008c604019028210181901ae90b860028210081a02819298070200d04019040190407a028190b01900ae2018310407a089830181a02811040190c8190282108823590190b81b02821008e901819138180400d041190f8180b80d028210f0230f0210f005028190b019
|9=>0x28210081a0201702b090200f04019040190b80d04015028190d8260c8190b85b028210886f028110401902017028190b0190407a04079028190c8610081a0b85b0282100ad20182d028120401902017040190b85b028210200702811040195f86f0b981028210181a0290d0410d0b81a02821040360886f0b819028210b0190886f04079028190b81a028190b85b02017028190282102861040610081a00831
|10=>0x28190b0190b0190886f02811040190b3150b862028210081a0c8190b85b028210d9612b8180b80502821638190f12a0400502819008c6018190b81b028210885f0886f0b819028210290d02812008190b85b02821040190290d0b81a040150b0190081902811040190886f0885b0281102b150b862040150081a2f0170880d040790281902812040190b0190407a028190b0190885b02811040192485b0b861
|11=>0x2081802805028190f81b040150b85b0b981028210181a0c8190b85b028210c8190b81a02821008190407a028190b0190885b0886f028110401902a620426502819021b7040190b818028210b0190f09c0400d02819020170b0190401a040190201702861040190081a02819022bc040192b8100b8050f8380b80d028210b019088230886f0b819028210f00d0401504019028190c81a0b85b028212d80f0f005
|12=>0x4019040610081a0b0190880502811040190886f590190b81b028215f85b0b981028210181a028190b838040150b0190885b0880502811040190b01904181028190181a0886f08805028110401902939040610b0610081a0b0190b981028210181a0081a04015028190b0190b0190880502811040190b0190433a029810181a0c9830181a0b85b028210410920818028050281901856008190b85b028210f10b
|13=>0xb019008250c8190b85b028210200702812040190b019008350886f02811040190b85b01856028210081904015028190b0190b81a0b85b02821088170b8190b85b040153986f088050281104019041810433a029810181a04019028190b85b040155f8170b981040150181a0410d0b81a0b85b028212b8180b8050282100819248170b861040150081a0885b02015040190b2a50b85602821008190886f02015
|14=>0x2981028190b81a040150b0190d8260c8190b85b028210881708823028110401900ae90b860028210081a0f023028190f0212d80f0f00502819028210200f02819040190b2e90b860028210081a009190f8180b80d02821028190f8180b80d04015041e9578180280d02819698190b863028210081a008190b85b028210c90d0b81a0b85b028210282d02812040190b0190416e0f00502819040190401502819
|15=>0x28190181a2f05b0880d02811040193986f0880502811021b7040190b818028210b0360886f028110401902811040190b01901b420090d0b81a028210c90d0b81a0b85b028210bb150b862028210081a0dae90b860028210081a0281902812040190b019088670b8190b85b028210282102812040190b01904282028610d8260c8190b85b028210281904015040190081a02819041dd0281a0b0190b1810433a
|16=>0x2485b0b861028210081a02821041810b0190181a040190b81a04015028190c81b0b85b028210b80d0282102819040190b0190886f02811040190c8610081a0b85b02821041810181a0b85b5f86f0b981028210181a028190b838040150b0190b1810181a02819040193986f0880502811040190b85b0886f0b819028210b0190880f02811040190a80f0081902819040190b85b01981028210181a0282104181
|17=>0xd8260c8190b85b02821018560b01902821008190081a02811040193980f0880502811040192f05b0880d028110b0360886f0281104019088670b8190b85b028210b9b80b061028210081a2f01b0880d02811040190b85b0282101856008190885b0081a02811040190886f0081a02811040190f81b02821040260c8190b85b0282101b610b85702821008190281102812040190b01908817088230281104019
|18=>0x282108823088170b81904015028360886f04079028190b0190886f02811040190b8190f8180b80d0c8190b85b028212486f0b861028210081a0b85b0f8180b80d028210b85b0886f0b81902821028190d9b50b818040150886f0b019028113986f2b8190b805028212f05b0880d02811040190b0360886f02811040190281902812040190b0193e81b0b85b02821028360886f04079028190c8190b85b02821
|19=>0x28190400d0b0190c81b0b85b02821020170400d040190b019041de0281a568190b80702821008192501804005009d90b80f028210b81202821028190401904019028190b818040153306d0b838028210b019088170885b0407902819088170886f04079028193980f0880502811040190c8610081a0b85b0282104019028320407a028190d8260c8190b85b02821591810181a0b81b02821088050b8190b85b
|20=>0x81a040190b1dd0281a0f02302819040190b38d029820181a041092081802805088170b819040150b863028210081a04281028610081a0281904015008190281202811040190b0e9138180400d0f0230f0070281925018040050401901b82070050b01902812040190b0190f00f04079028190b861028210081a02b6f2501804005040190700f0b0190b01902811040190b019041dd0281a04061028210081a
|21=>0x28210181a0b8c60282101819008190b85b028210885b02811040190181902819040190082e02812040190200502811040190b01902a6d0401a0200d0282104019019b50b818028210886f02811040190b81a04015028190b181028210181a028190b0190181a008310407a028190b8190b80d02821028190b8180401504015040190181a0b1dd0401a0281a0416e0f00502819088070407902819040610b019
|22=>0x410d0b81a028210b85702821008190181a0b81b028210d909208180280500819040190b0190f0210280d02819008190b805028210201704019028190c8190b85b0282125017040050b0190b019040050401902017040190081a0b01902821008190b01902819040190b181028190181a02007040190b0190b01902811040190281a04019028190b26d0401a0281902819018560081908823028110401904181
|23=>0x401902812040190b0190b181028210181a0283a028190b0190282101856008190b981028210181a0f005028190b01900819040610081a088170407902819028190400d040190b0190281a040190f09c0400d02819040190b805028210081a0b85b028210210402805040190b862028210081a02861040610081a2d80f0f005028190407a028190b019088070b81902821041850b1810181a028190b80f04015
|24=>0x2811040190b0190185602821008190b019018560081902bb9041820181a0090d0b81a02821088170b819040150281204019042650f00f028190410d0b81a02821031b70b818028210b80d04015028190885b02811040190082e02812040190886f02811040190b1b50b818028210f00d04019028190401502007040190181a0281104019041e9578180280d0b8540282100819042be018190280d022be0280d
|25=>0xf005028197a807019dd0281a0b0190281904019028190b26d0401a590190b81b02821043750700f0b019008190b81b028210880502811040190407a028190d9b50b818028210b80d028210b0190293a040610081a028190b8180401502bc9040c6018190402e02812040190b80d0b85b028210885b0281104019028110401a040190886f028110401902af10200704019040560081902805250170400504019
|26=>0x181a2d80f0f005028190886f028110401902812040190b0190b861028210081a0b983028210181a0081a02819040190b856028210081900819028110401904015028190b01975019578230280d01b6d25018040050407a02819028190b85b040150b0190281a028190200f028190401904282028610081a020170401902819040610b0610081a008310407a02819009b50b81802821022be0280d040190416e
|27=>0x281904019028210b0190081a0f81b0b80d028210880f02811040190081a0b85b028210b862028210081a088050281104019018650b85b0282104181028190181a0c81a0b85b028213b01a0b80f0282102a6d0401a0b0190c8190b85b028210880502811040190407a00819028190b980028210181a028120401a040195900d0b81b028210b81a0b819028210886f0b819028210885b02811040190198102821
|28=>0xb838028210b0190282102819040190c8190b85b028210b01902811040190b8190b85b028210b10d041de0281a0880f02811040190433a029810181a0b81a028210b0192b8190b805028212b85b20821028050b80502821008190b81a0b85b0282104015028190b0190f8180b80d028210886f0b81902821028120282104019008190b85b02821029dd041dd0281a0b81a04015028190b1dd041dd0281a02821
|29=>0x181a0b0190081a020070401902821040190400d0280d029820181a2082102805028210081a028050b0192081802805041810181a0b26d0401a0f007028190401a04019019dd0281a2501b04005019810181a008c601819040190b01902a6d0401a0400502819020050401902805028190200d04019028210b019028190081a0401a02819018190400d20823028050b85b028210281a0b019009b70b81802821
|30=>0x181a02819040190401a0281a040190b0190b1810181a0b819028210281a0b0190b80f028210281204019008190b0190b81a028210b81802821028210081902819040190b85b028210700f0b01902811040190b0610081a0403a0b0190b1dd0281a070050b0190281a040190407a0281900819040190281104019040390b01902a6d0401a04056008190b81b02821041de0281a008c6018190b80d0282104181
|31=>0xb019028210280d040190281a00819
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1ca00000000000000000000000000000000000000000000000000520000000000000000046000000100000000000000000000000
|6,0=>0x1d9400000000ea2000038286c4000000000000000000019d43128000000017540000594000000002a2800009ea12d00000000000011d021a03e500000000000000000000000000000000000000000000007660000000036500000c9017202950000095010280000000071000001750000000009a0000
|6,1=>0x1d0a38d46fa0dc31b0800000000000000034d46728ca4000000000000000000000000000c55000000000000000182800000000000178a0000000000000002dd45b08b42000000000000af500002a940000000000000005320000144827900000000136625d000009250000239045208550000201400007b5
|6,2=>0x441000000000000000000000002188000000000000000421081a800000003fd000000001f683e840000000000000000000f551e0a3b4c0000000000000000000000
|7,0=>0x3c287750ed19d823aa6748c0001cf339867210e221c0437a66e50db9000036686bd0d5a1a74346867d0ce1998432886410c69989430a86050bf197a42ec80000b9216e42d480000b3996342be80000ada15742aa4548ca7214a428c850909f213b326e84cd098192c42508491090211c4230800008a20000
|7,1=>0x5666abd155a2a745468a8494f1a9a452c8a4cd47a28b45106a14d411a7e44f489d9139226f34da49a5132a26144bc697452d1a5644a48939000024a448e60001229241447a88e8c000236400008c9117222a444c888910f221a442e684d108920d441288151020a0043fa67e50faa1f413e087b4cf4a1e54
|7,2=>0x7328e551c8a38e37148e191c19b7f46f68ddd1b9a36f46d86da4db2a36146ba8d651aaa351469a8d251a31b42467e6cf499ca33546628cb5194a32546428c7518ca31546228c35184a30546028bf517d92f745e860001789aed45d28b98d7122de45b48b591699ad1259a8b25162a2c230000af915d22b64
|7,3=>0x8f891e123a9c7148dc71a9233246248bc916922b245248a0513100004484888910121e2438486890c4e16a429400010952111c1e48349059209240e48149019201200007fc80001fd23f737e68fbd1f61be847c88f811ee23d847a88f411e713ca478c8f091df9bbb476e8ecd1d7a3ad27528e951d0a39d4
|7,4=>0x9ce938d26fa4db49ae934d267a4cb498e930d25fa4bb496e92cd2581cad39529295250a49d49347259249248e4914921ce41a4803
|8,0=>0xb507694ed11d9f3b387664ecb1d933b207634ec51d873b087604ebf1d7b3af075d4eb91d6f3ad875a4eb31d633ac07574ead1d573aa87544ea71d4b3a907514ea11d3f3a7874e4e9b1d333a6074b4e951d273a487484e8f1d1b3a307454e891d0f3a187424e831d033a0073f4e7d1cf739e873c4e771ceb3
|8,1=>0xcce5990f309e5e3cb67960f2a9e523c9e7930f249e463c867900f1e9e3a3c6e78d0f189e2e3c5858a4f131e233c407874f0d1e173c287844f071e0b3c107814f011dff3bf877e4efb1df33be077b4ef51de73bc87784eef1ddb3bb07754ee91dcf3b987724ee31dc33b8076f4edd1db73b6876c4ed71dab3
|8,2=>0xe4a7c88f8f9f1c3e327c58f899f103e1a7c28f839f043e027bf8f7d9ef83dea7bc8f779eec3dd27b98f719ee03dba7b68f6b9ed43da27b38f659ec83d8a7b08f5f9ebc3d727ad8f599eb03d5a7aa8f539ea43d427a78f4e16993d2c7a4cf481e8d3d147a1cf421e813cfc79ecf3c1e753ce479bcf361e693
|8,3=>0x7403e7a7ce8f9b9f343e627cb8f959f283
|9,0=>0x3de97bb2f725edcbda97b32f625ebcbd697ab2f525e9cbd297a32f425e7cbce979b2f325e5cbca97932f225e3cbc6978b2f125e1cbc297832f025dfcbbe977b2ef25ddcbba97732ee25dbcbb6976b2ed25d9cbb297632ec25d7cbae975b2eb25d5cbaa97532ea25d3cba6974b2e925d1cba297432
|10,0=>0x1f147e20fc31f843f047e00fbf1
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 15
def pmP:Nat→Nat
|0=>0x40c0000000010100000000040000000000080000000000170000000000590000000001440000000004e00000000012400000000048000000000118000000000440000000001040000000004000000000008c0000000001c0000000000640000000001800000000005800000000014000000000044000000000100000000000240000000000800000000001c000000000060000000000140000000000400000000000c0000000000200000000000400000000000
|1=>0x45740000000105c0000000041640000000105100000000413800000001049000000004120000000010450000000041100000000104100000000406400000001018000000004044000000010090000000040200000000100400000000400400000001000000000003e38000000008100000000010000000000020000000000057c0000000015d0000000005400000000014f000000000510000000001410000000005000000000011000000000041c00000000104
|2=>0x4016c0000001004100000004006000000010010000000040030000000100010000000200000000000515f00000001457400000005059000000014124000000050480000000140240000000444000000001057c00000004141000000010500000000040580000000101440000000404800000001011c0000000404400000001010c000000040410000000101000000000401100000001002000000004001000000010000000000020400000000060040000000115f
|3=>0x400400c000010000000000020040040000060015300000101456c0000040415f00000101052400000401149000001000d740000040030500000100057c000004001410000010004700000040011800000100044000000400100000001000144000004000410000010000600000040000800000100000400000400000000000400004000000821570000002001100000004415d00000010000000000020000000000044f7c00000010f9f000000043e70000000103dd
|4=>0x100000f00000400001c00001000005000004000010000010000030000040000060000090101740000240015f0000080505600000201015f000008040440000020100580000080401400000201000800000801412400002005048000008010164000020040490000080100600000200205800000800457c0000200016f00000800057c0000200014f00000800052c00002000118000008000170000020000590000080001600000200001800000800002400001001101
|5=>0x190141640000640415d00001900457c0000640115d0000190041640000640015f000019000574000064000590000190001040000600015f0000111005740000444000900001101953c0000440415d0000110001640000400417f0000100101640000400104d0000100005fc0000400015f0000100005540000400014f000010000220000040000840000100001ec000040000570000100001380000400004c0000100001200000400004700001000011800004000041
|6=>0x8101056c0002040011b0000810004680002040001a00008001012c0002000030a0000800005b0000200000100000800000380002000000c000080000000000100000420000300007fc0000a01401c00002804057c0000800100200002000400400008000003000020000004000080000000000191445740000645015f0000191400240000641115d0000190441640000641100900001904057c0000641015d00001901857c0000640615d00001901457c0000640515d
|7=>0x11904057c0004440115d00010904057c0004000515f0001000145740004000415f00010000457c0004000115d000100004474000400010500001000041000004000100100010000057c0004000015d0001000005340004000011f000100000414000400001000001000001040004000001f000100000008000400000010000980407fc0002601015f00009800057c0002400117f00009000457c0002400017f00009000057c0002400008e0000900002080002400000e
|8=>0xd0400447c0034040415f000c0101457c00300404158000c0100057c00300400147000881000448002020001500008010000000020000004100050101043c0012040011a00048000057c0012000011a00040c04057c0010201015f0004080004600010040400000040100057c0010040011d000400000400000cc0001ff0003100007fc000a400015f0002100006dc0008400017f0002100000580008200017f00020800057c000800000540002000000000004645015f
|9=>0x440100057c0104040415f00408900057c0100200015f00400101457c0100040415f00400100057c01000400008004000010120008840050540022000041b8008240001df0020900000780082000001c0020180005fc0080400017f00201000057c0080400000c0020100000180080200015f00200000012c008000000080011001045740044000415f0011000041640040641015d0010190404740040201015f0010001065700040000105100100000406000400000019
|10=>0x40110001457d0004201515f40010001457d0000645015f4000190545750000641015f21001800057c8302440015d20a01000057c820070101dd2080180001748200400015d2080100001748200000415d200010000574800040000d510500005057c4120001415f10400005057c400400141df10010000057c4004000015d10010000047c4000000000108001800857c2000400004004000000000c0800000000001c00000057c0200600015d0080080405440120040015f
|11=>0x20000400015f508130040575404000103df50100004057d4004c01017f500000050f7d008040001ff
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x70000000000000000000000000000001400000000004000080000000000000
|6,0=>0x179740c08070000000001cc5e0600000000000000002000000860009000000002800002b000d83865000005c61000040000000002400040480000011700001000742419171780011001f4000015000ba1200000000000004ec000005000122c8002400161a40000000381041000000000000000000000000000010000067000101c1700048720000004007c000000800
|6,1=>0x2e000200000000000000008000000000088400000480000009900000000000016168c40000000000000
|7,0=>0x328c161223821a08d0a8c4120b070740c3735c69e20618825de6f1a51024254811800561880010106b87401413500554d64e2101c81050499844a189cd418031ad28d53401872ee2385804026c04801210123e18dc0e91c040057b6868de5582415489126c082f2d8f410090c8005eec01800109983800646c05384903c1b02c12060b04ce01459c5526524dc055c2e
|7,1=>0x792a424a0228c86c5f3585894143f3d800a01d0d99e955c012383d000581416318382636118383e0043000dc080d0f4e0167a121180f2f0f404f041b243ac67504d0917099c826162789890eb768be54c7038302a20540085f46008f4122f5380460cd020289648099819c0e6a0e10092248883c88008861c5a02001ea0d1b42c9a6d90004e2083b94e2402005407813
|7,2=>0x272dcc4330584c020e919428a543e8d88a04099fc5ec20405890415a0745e04
|8,0=>0x4d30e3c825ec4c691f7c0f47ead56c19f6d9ab2254a55969c922be8dbe25c3f7fc513a244c3967f0d4157ac353474d1143da032e81367827d1210abca149636fafd5a4fa3ba0f135423ce130a81389071069bf176c4aa8f113371dbf1bb2f534963298202412f11979e57d18924c13cd1642c52cb62b1602ee01abf53703b2ad62c38565387b0042cfa92724b2c20952
|8,1=>0x513190294fe7c258e8896436eccad7bd7cf6551ebc170bb622f1a51c3a8f898a2a5c3e953a934a657054483cf4552b8f50f511e998804f41b8d455b86d64e127651c8361a4b4cd7d389950988ff5953d42ac
|9,0=>0x52897fa58aeca9d8a1d2c060b9972f3a68fd2d4cad589782973902c8b97216175588ea25a2ad204e512ad45d82628962ab5753d834f2a8fa5d41a1130a057658bd9ccc1f35c
|10,0=>0xa4813f14ae9c889
|11,0=>0x29
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 46 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_125 10 roots_125 ops++addP pm 1 dom_118 8 roots_118 ops++addP pm 2 dom_126 9 roots_126 ops++addP pm 3 dom_111 9 roots_111 ops++addP pm 4 dom_95 9 roots_95 ops++addP pm 5 dzo_126_1 7 roots_126 ops++addP pm 6 dom_123 10 roots_123 ops++addP pm 7 dzo_58_1 5 roots_58 ops++addP pm 8 dom_119 9 roots_119 ops++addP pm 9 dzo_51_8 5 roots_51 ops++addP pm 10 dom_73 4 roots_73 ops++addP pm 11 dom_121 8 roots_121 ops++addP pm 12 dom_75 5 roots_75 ops++addP pm 13 dom_61 6 roots_61 ops++addP pm 14 dzo_75_4 5 roots_75 ops++addP pm 15 dom_90 5 roots_90 ops++addP pm 16 dom_59 6 roots_59 ops++addP pm 17 dzo_121_4 6 roots_121 ops++addP pm 18 dom_91 8 roots_91 ops++addP pm 19 dzo_53_8 5 roots_53 ops++addP pm 20 dzo_105_4 5 roots_105 ops++addP pm 21 dzo_54_1 5 roots_54 ops++addP pm 22 dzo_55_8 6 roots_55 ops++addP pm 23 dom_93 7 roots_93 ops++addP pm 24 dom_115 8 roots_115 ops++addP pm 25 dom_63 7 roots_63 ops++addP pm 26 dzo_62_1 6 roots_62 ops++addP pm 27 dom_122 8 roots_122 ops++addP pm 28 dom_124 7 roots_124 ops++addP pm 29 dom_54 5 roots_54 ops++addP pm 30 dzo_107_4 6 roots_107 ops++addP pm 31 dom_110 6 roots_110 ops++addP pm 32 dom_87 6 roots_87 ops++addP pm 33 dom_103 6 roots_103 ops++addP pm 34 dom_107 8 roots_107 ops++addP pm 35 dom_94 6 roots_94 ops++addP pm 36 dzo_119_8 7 roots_119 ops++addP pm 37 dzo_118_1 6 roots_118 ops++addP pm 38 dom_102 5 roots_102 ops++addP pm 39 dzo_115_8 6 roots_115 ops++addP pm 40 dom_50 4 roots_50 ops++addP pm 41 dzo_60_1 5 roots_60 ops++addP pm 42 dzo_123_4 7 roots_123 ops++addP pm 43 dzo_118_8 6 roots_118 ops++addP pm 44 dzo_91_4 6 roots_91 ops++addP pm 45 dzo_122_1 6 roots_122 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_126_1_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_58_1_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_51_8_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_75_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_121_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_53_8_52 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_105_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_54_1_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_55_8_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_62_1_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_107_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_119_8_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_118_1_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_zo_115_8_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_zo_60_1_52 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_zo_123_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_zo_118_8_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_zo_91_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_zo_122_1_50 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_125 10 s (0,roots_125.map (·&&&dom_125)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_125 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 28 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 28 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 167 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 39 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 167 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 284 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 28 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 284 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 201 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 73 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 201 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 62 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 62 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 7 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 7 0 = true)
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
def dzo_141_2:=0xcccc0000000000000000000000000000cccc
def gzo_141_2:=0xccc800000000000000000000000000008800
def gsh_141_2:=0x333200000000000000000000000000002200
theorem lowS_zo_141_2_141:Lower true dzo_141_2 roots_141 gzo_141_2 5:=lower_iso_b (d1:=dom_141) (r1:=roots_141) (T1:=gsh_141_2) [(dom_141,2)] (by decide +kernel) (lower_slice_b (T:=gsh_141_2) [] (by decide +kernel) lowS_141)
def dzo_203_4:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0
def gzo_203_4:=0xf0f0000000000000f0f0000000000000f0e0000000000000a000
def gsh_203_4:=0xf0f0000000000000f0f0000000000000f0e0000000000000a00
theorem lowS_zo_203_4_75:Lower true dzo_203_4 roots_203 gzo_203_4 6:=lower_iso_b (d1:=dom_203) (r1:=roots_203) (T1:=gsh_203_4) [(dom_203,4)] (by decide +kernel) (lower_slice_b (T:=gsh_203_4) [(0xf0f0000000000000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_75)
def dzo_205_2:=0xcccc000000000000cccc000000000000cccc000000000000cccc
def gzo_205_2:=0xcccc000000000000ccc8000000000000cccc0000000000008800
def gsh_205_2:=0x3333000000000000333200000000000033330000000000002200
theorem lowS_zo_205_2_141:Lower true dzo_205_2 roots_205 gzo_205_2 6:=lower_iso_b (d1:=dom_205) (r1:=roots_205) (T1:=gsh_205_2) [(dom_205,2)] (by decide +kernel) (lower_slice_b (T:=gsh_205_2) [(0x3333000000000000000000000000000033330000000000000000,0,64)] (by decide +kernel) lowS_141)
def dzo_217_4:=0x30303030000000003030303000000000303030300000000030303030
def gzo_217_4:=0x30303030000000003030303000000000303030200000000030302000
def gsh_217_4:=0x3030303000000000303030300000000030303020000000003030200
theorem lowS_zo_217_4_73:Lower true dzo_217_4 roots_217 gzo_217_4 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_4) [(dom_217,4)] (by decide +kernel) (lower_slice_b (T:=gsh_217_4) [(0x3030000000000000303000000000000030300000000000003030000,0,16),(0x3030303000000000303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_73)
def dzo_201_4:=0x3030000000000000303000000000000030300000000000003030
def gzo_201_4:=0x3030000000000000303000000000000030200000000000002000
def gsh_201_4:=0x303000000000000030300000000000003020000000000000200
theorem lowS_zo_201_4_73:Lower true dzo_201_4 roots_201 gzo_201_4 5:=lower_iso_b (d1:=dom_201) (r1:=roots_201) (T1:=gsh_201_4) [(dom_201,4)] (by decide +kernel) (lower_slice_b (T:=gsh_201_4) [(0x303000000000000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_73)
def dzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
def gzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000f0f0a000
def gsh_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000f0f0a00
theorem lowS_zo_219_4_75:Lower true dzo_219_4 roots_219 gzo_219_4 7:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_4) [(dom_219,4)] (by decide +kernel) (lower_slice_b (T:=gsh_219_4) [(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000,0,16),(0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_75)
def dzo_217_2:=0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c
def gzo_217_2:=0xc0c0c0c000000000c0c0c08000000000c0c0c0c000000000c0c0800
def gsh_217_2:=0x3030303000000000303030200000000030303030000000003030200
theorem lowS_zo_217_2_137:Lower true dzo_217_2 roots_217 gzo_217_2 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_2) [(dom_217,2)] (by decide +kernel) (lower_slice_b (T:=gsh_217_2) [(0x3030000000000000303000000000000030300000000000003030000,0,16),(0x3030303000000000000000000000000030303030000000000000000,0,64)] (by decide +kernel) lowS_137)
def dzo_221_2:=0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc
def gzo_221_2:=0xcccccccc00000000ccccccc800000000cccccccc00000000cccc8800
def gsh_221_2:=0x33333333000000003333333200000000333333330000000033332200
theorem lowS_zo_221_2_141:Lower true dzo_221_2 roots_221 gzo_221_2 7:=lower_iso_b (d1:=dom_221) (r1:=roots_221) (T1:=gsh_221_2) [(dom_221,2)] (by decide +kernel) (lower_slice_b (T:=gsh_221_2) [(0x33330000000000003333000000000000333300000000000033330000,0,16),(0x33333333000000000000000000000000333333330000000000000000,0,64)] (by decide +kernel) lowS_141)
def dzo_201_2:=0xc0c0000000000000c0c0000000000000c0c0000000000000c0c
def gzo_201_2:=0xc0c0000000000000c080000000000000c0c0000000000000800
def gsh_201_2:=0x303000000000000030200000000000003030000000000000200
theorem lowS_zo_201_2_137:Lower true dzo_201_2 roots_201 gzo_201_2 5:=lower_iso_b (d1:=dom_201) (r1:=roots_201) (T1:=gsh_201_2) [(dom_201,2)] (by decide +kernel) (lower_slice_b (T:=gsh_201_2) [(0x303000000000000000000000000000003030000000000000000,0,64)] (by decide +kernel) lowS_137)
namespace S_223
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(2,18),(2,66),(3,11),(3,19),(3,67),(3,131),(4,20),(4,132),(5,13),(5,21),(5,69),(5,133),(6,22),(6,70),(6,134),(7,15),(7,23),(7,71),(7,135),(8,9),(8,72),(8,136),(10,11),(10,26),(10,74),(10,138),(12,13),(12,28),(12,76),(12,140),(14,15),(14,30),(14,78),(14,142),(16,18),(16,20),(16,80),(16,144),(17,19),(17,21),(17,25),(17,81),(17,145),(24,25),(24,26),(24,28),(24,88),(24,152),(64,65),(64,66),(64,72),(64,80),(68,69),(68,70),(68,76),(68,84),(68,196),(128,129),(128,132),(128,136),(128,144),(130,131),(130,134),(130,138),(130,146),(130,194),(192,193),(192,194),(192,196),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffff
def xsM:=roots_223.map (·&&&dom_223)
def gM:=goal_223&&&dom_223
def NN:Nat→Nat
|4=>6
|5=>27
|6=>129
|7=>358
|8=>262
|9=>75
|10=>12
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x8138d4016e3675f2f2952d6fa09891
|5,0=>0xa98f59764294f2e943597563b620275d9d8563465190f4804042a60309df2fe792f8e62ace029d5f27f8421550214a91528811ace0f7660e8840959e06e1206d08015a1
|6,0=>0xcf3a4c4ddfa8dd9a5f61a2cbf9cf449a7e999c95889aa8800484f09824f28193c804d27f16b7e5a77c3d87c1517a1c4798ff74d9872aa17180c7076f6fb2e67d9063d9e5e8825d1d15c39a5b25a5a9aa567fc565ec5351a51e7e5190f510214e5474bc86482e84779b45be44456b443a441cd54004d3f5853c4da3c45b3a2cf3972438e523826737f7936a81362ba35eec32c1a3237830bdb2f2e32e9522e7bb2e39a2c25e2ad292ab1a2a8452863628166280e82804c2696425477249d5249422453723d8723b6c233f522a411ddc91dc841cd631c61e1c5041bf871ae4c18dca185b617df61766615bb3152881510c1470d13bd5137b812010117ec1112910c500ed570cd720c4330c04d0bc830afe70a863099a60959e090150853c076520724c06dbb0601404e6a049b60477e03eec02d3d02bb1026a60205101c99000cd
|6,1=>0xd7ddc
|7,0=>0x2215c21e6d21d67219ed212832065b2009d1fe6a1f7b31f72a1ea001e87b1dc841da731d8c11d8641d7f31d0961d07d1ce591cca41baec1b9391ae4c19b44199c3195c81928b1857e1853317e56177fc174111716616fc7168c5159e9158b6156e5154d614bff14a511481614721146fb145fb14481132c1126de1269a117ec11598110ad1104c10b6b107cf1060a1004d0f7400f4c60f0e50eeb40eac20e2970e0ae0d26c0cea90cdf90ca490c71b0c7080c63c0c10b0bed30bb8d0b7dc0b73e0b3f40b1420b05e0ae620ad970abee0a8f20a6d50a40109e1609c4909b09096260948508ea608877087f4085d307e9407d0707810077b2072b70724c071bc06783066a7063ce061a105fe405e5805bab0533a0518204f4404da104d5304ba5049040471904439043e4035fd0314902443017b2014310117a00881002d2000d9
|7,1=>0x5a4455a34f5a2a8596545907458ce157ff057f10573f656f7256aec56774560a85544754d1f5436f53f1b53ed45395e53657528a15207f515cd510215060b502a84e3254e2044de6a4db4b4d4624c8c24bf9d4be0c4b0a64aa254a8624a6324a3954a1dd49a854924e48bff488874839d4820b480a047bbc469a146926463a046215459e14544a4456b43e9443cef4313442ffd428dd42863425ea4233f41f9b41dad419304087f3f74b3f62c3e3a23e2c63e2623d6083d24a3ce963bff73bb173b6213adfb3a4c23a493399483972438ffa385733846c3759f36697362d8361ed35e4935c8f35bf23517034caa34b6734adf319ad30c93300cb2fc3f2f3312ef5a2eab42e9d12dfc62d0d62cebc2cc352c6a42b9392b0e82a3ac29eaa29c8d29c712996826a15260ba25cc12587624c79248772404f2347122ff022c4822392
|7,2=>0xef716e49e0ddf75d842bd55a1ca717c6e14c0f5dbafe2b95aab8428b756db7435b537ab4ec8b20bcb16ddb102db0cc3b06a4aefedac5f6aa24fa6178a59f4a49f2a4135a3744a1deba1a5ea0e36a05d29fe939b3f99a81d9a7bc9a4b8986a69818297932966da9610095ecd95dcc95658922ab8fd798f2e28ef1c8e20b8deb78dd828dbc28c82d8c7368ae4689efc89e2d8800483fbc8344782d3f804d2804af7ff367f3c07e5f67d70e7b60677c4575c7c7512f7405371a48704486f3656e3276e2266d5d76d3ac6c6a96c4a769b3566d0265d576506164079638d6635bf62ee662ac9600c85e1e35de865d7be5d0ea5cbcd5c5f25c5225b2cc5aa575a91c
|8,0=>0x2ff4d2f8ef2f6502f4342f2332eb7f2eb7c2ddfb2d3ed2cd582c1d62bdc42b9162b4252b0e82a3f82a3ac2a38b2a2912a19229e3329d5529d05299682906928f70283e527fdf27e9d274af27342267b12590e254dc2521224c082276d221e921e2021deb218ec21631215df210251f7b31f6d21ec4d1e48e1dde91dddf1dd4f1c5df1bd2a1baf51ba7b1b4fe1aaa11a7931a6641a12419b251960f1945b1927c1922418a5d184b417fe517e9f178271752016c001620d15b511548415194148971448113bbf1325b131621256312054117ff0f5420f4c20f2040e9bb0e6f40e4ca0dabd0c8500b8950b2fa0b0b80aea80ac290abd80a6d80a50f0a29809e1609c8d09a3209899097f209561094f6082310724e06f4a06e2606d6c061a105691054ac050f404dea044340428003415027100137d01348011630077d0018800034
|8,1=>0xce64cce059ccfbac8532c6525bc413bb8ebba4e2b1aa7ad2a8ac5f6ab2a6a9670a6d71a66b7a3d73a25c8a0e369ff479b48996c9a9554a919ff90e2c90d6f8fd7c8dd828d80f8c0228b01f880048529f84f05834d78344782d0981e6d81dff81544814337e3377cc157ca7c7bf027b3b17537a749a372a7c6f9e56f61c6d6b16ce666ca4c68c90686c06732466fef63f3c63e7762a3461447611be60df0604935ff1f5fe385f4805e7f25e4af5e0925dacc5d1935c9a959cd45975b58ce1576ab5707556ec1567745614955ce853f8453db65395e52b545182e50da750d3550c59501d4501134f54f4e3254e2044e0c24de6a4dc444add2484454820b4637645d64459e14583c4553f443164422c4348342e134255f41cc43d23c3bd643a31c3881337d8d36dae36d7d35bf23541034aa533f68333563157530e2c308963085d
|8,2=>0xef716e8637e49e0e3691df84ade5a9
|9,0=>0xef716e6fffd969fc9c91a8185a69a0a4f6f98faf913958f4038bbcd8792d81d6d7f09179181775b66a7c1635dd61f14613415d7cc5c7645ad655916d58948569ae54e2b4fb1e4974c48c2b43356433343d23c3c6023b8da3335631c35316252e77f2da2c2d8b92bad4267b125d3d25aeb25512242cf222a521d1020b521ed201ddfe1ca421bd4519e441515913ef51073a0ea690e53b0e1de0d6750c8c40c7390c2bb0c2740bbda0b10506dfe06d07061a105aff023f100d2c004f5
|10,0=>0x946447474a6f9056e16e6375a5bfd64e3a93c8fb3bd92259c11f14a1730e
|11,0=>0x1730e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffff0000000000ffffff0000000000ffffff000000000000000000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00ffffffcc00000000ffffffcc00000000ffffffcc00000000ccccccccffffffff00000000ffff000000000000ffffffff00000000ffff0000ffffffff00000000ffffffff00000000ffffff0000000000ff00ff00ffffffaa00000000ffffffaa00000000ffffffaa00000000aaaaaaaa000055550000000000000000000000000000555500000000ffff0000ffffffaa00000000ffffffaa00000000ffffffaa00000000ff00ff00ffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaaffffffff00000000ffffffff00000000ffff000000000000ffff0000fffffafa00000000fffffafa00000000fffffafa00000000f0f0f0f0000055550000000000005555000000000000000000000000ffff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0cccccccc00000000cccccccc00000000cccccccc00000000cccccccc000055550000000000000000000000000000555500000000aaaaaaaa
|0,1=>0xfffff0f000000000fffff0f000000000fffff0f000000000f0f0f0f000ff00ff0000000000ff00ff0000000000ff00ff0000000000aa00aaffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffffffff00000000aaaaaaaa00000000ffffffff00000000aaaaaaaaffffaaaa00000000ffffaaaa00000000ffffaaaa00000000ffffaaaaffffffff00000000ffffffff00000000ffffffff0000000000000000ffffaaaa00000000ffffaaaa00000000ffffaaaa0000000000000000ffffffff00000000ffffaaaa00000000ffffffff00000000aaaaaaaaffffffff00000000ffffffff00000000ff55ff0000000000ff55ff00ffffeeee00000000ffffeeee00000000ffffeeee00000000ccccccccff0000ff00000000ff0000ff00000000ff0000ff00000000ff5500aaffffffff00000000ffffffff00000000000000000000000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000ffffffff000000000000000000000000ffffffff0000000000000000fffffff000000000fffffff000000000fffffff000000000f0f0f0f0aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa
|0,2=>0xffff000000000000ffff000000000000ffff00000000ffff0000ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00000055550000000000000000000000000000555500000000ffffaaaaaaffaaaa00000000aaffaaaa00000000aaffaaaa00000000aaaaaaaa555555550000000055555555000000005555555500000000550055003333333300000000333333000000000033333333000000003333330000000000000000000000aaaa0000000055550000000000005555aaaaffffffff00000000ffffffff00000000ffffaaaa00000000ffffaaaaffffffff000000000000000000000000ffffffff00000000ffff0000000000ff000000000000000000000000000000ff00000000ffff0000000055550000000000005555000000000000000000000000aaaaaaaa0f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000ffffff0000000000ffffff0000000000ffffff0000000000ffffff00ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00000000000000000000000000000000000000000000000000ffff0000ffffff0000000000ffffff0000000000ffffff0000000000ff00ff00
|0,3=>0xffffffff00000000ffffffff000000000000ff000000000000ffff00ff00ffff00000000ff00ffff00000000ff00ffff00000000ffff0000ffffcccc00000000ffffcccc00000000ffffcccc00000000ccccccccff00ff0000000000ff00ff0000000000ff00ff0000000000ff55aa000f0f0f0f000000000f0f0f0f000000000f0f0f00000000000f0f0f000f0f0505000000000f0f0505000000000f0f0505000000000f0f0000ffff555500000000ffff555500000000ffff555500000000ffff550055550000000000005555000000000000555500000000000055000000555555550000000055555555000000005555555500000000555555000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f00ffffaaaa00000000ffffaaaa00000000ffffaaaa00000000aaaaaaaa00ff00ff0000000000ff00ff0000000000ff00ff00000000000000003333333300000000333333330000000033333333000000003333000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00aaf0f0f0f000000000f0f0f0f000000000f0f0ffff00000000f0f0aaaaffff000000000000ffff000000000000ffff00000000000000000000
|0,4=>0xf0f000f000000000f0f000f000000000f0f000f000000000f0f000000ff00aa0000000000ff00aa0000000000ff00aa0000000000aa00aaaaaaffff00000000aaaaffff00000000aaaaffff00000000aaaaaaaaffffffff00000000ffffff0000000000ffffffff00000000ff00ff000000000000000000ffffffff000000000000000000000000ffffff000000ffff000000000000ffff000000000000ffff000000000000ff0055005555000000005500555500000000550055550000000055005500ffffffff00000000aaffaaaa00000000ffffffff00000000aaffaaaaaaffaaaa00000000aaffaaaa00000000aaffaaaa0000000000000000ffff555500000000ffff555500000000ffff555500000000ffff0000ff55ff0000000000ff55ff0000000000ff55ff0000000000ff00ff005555555500000000555555550000000055115511000000005511550033333333000000003333000000000000333333330000000033330000000000ff000000000000000000000000000000ff00000000ff00ff00ffffffff00000000ffffffff00000000ffffffff00000000aaaaaaaa0000ffff000000000000aaaa000000005555ffff000000005555aaaa
|0,5=>0xffff000000000000ffff000000000000ffff000000000000aaaa00000f0f0f0f000000000f0f0f0f0000000000000000000000000f0f0f00000000ff00000000000000ff00000000000000ff0000000000aa00aaff33ff3300000000ff33ff0000000000ff33ff3300000000ff33ff000f0f0f0f000000000f0f0f0f00000000030303030000000003030000f5f5f0f000000000f5f5f0f000000000f5f5f0f000000000f0f0f0f0333333330000000033332222000000003333333300000000333322220f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0a0a333333330000000033333333000000003333333300000000333333000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0000ffff00ff00000000ffff00ff00000000ffff00ff00000000ffff00000f0f0f0f000000000f0f0f0f000000000f030f03000000000f030f00ffffffff00000000ffffffff00000000ffff000000000000ff000000555555550000000055555555000000005555555500000000000000005555555500000000555555550000000055005555000000005500550033330033000000003333003300000000333300330000000033330000
|0,6=>0x5555555500000000555555550000000055ff55550000000055ff5500ffffffff00000000ffffffff00000000ffffff0000000000ffffff00ffffffff00000000ffff000000000000aaaaaaaa00000000aaaa0000aaaa000000000000aaaa000000000000aaaa000000000000aaff00000000555500000000000055550000000000005555000000000000550000005555000000000000555500000000000055550000000000000000000000ff00000000000000ff00000000000000ff00000000ff00ff00000000000000000055555555000000000000ffff0000000000000000ffffffff00000000ff55ff0000000000ffffffff00000000ff55ff00ff55ff0000000000ff55ff0000000000ff55ff0000000000ff55ff000f0f0f0f000000000f0f0f0f000000000f0fffff000000000f0fff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff000055555555000000005555555500000000555555550000000055ff5500333311110000000033331111000000003333111100000000333311000000aaaa000000000000aaaa000000000000aaaa000000005555aaaa00000000000000000000000000000000ffffffff00000000ffffff00
|0,7=>0x5555555500000000000000000000000055550000ffffffff000000005555555500000000ffffffff0000000055550000ffffffff00000000ffffffff00000000ffffffff00000000ffffff000f0f0f0f000000000f0f0f0f000000000f0f0a0a000000000f0f0a0affffffff00000000ffffffff00000000ffffffff00000000ffffaaaaffffffff00000000ffffaaaa00000000ffffffff00000000ffffaaaa000000ff00000000000000ff00000000000000ff0000000000000000ffffffff00000000ffffff0000000000ffffffff00000000ffffff00000000000000000000000000000000000000000000000000ffffff00000000000000000000000000000000000000000000000000ffffaaaa000055550000000000005555000000000000555500000000ffff0000aaaaaaaa00000000aaffaaaa00000000aaaaaaaa00000000aaffaaaa000000000000000000ff000000000000000000000000000000ff0000ffaaffaa00000000ffffffaa00000000ffaaffaa00000000ffffffaaff0000ff00000000ff0000ff00000000ff0000ff00000000ffff00000000ffff000000000000ffff000000000000ffff0000000000ffff00
|0,8=>0x3333333300000000030302020000000033333333000000000303020200ff00000000000000ff00000000000000ff00000000000000ff0000aaffaaaa00000000aaffaaaa00000000aaffaaaa00000000aaffaaaaffffffff00000000ffffffff000000000000000000000000ffffff000000ffff000000000000ffff000000000000ffff0000000000000000aaaa000000000000aaaa000000000000aaaa000000000000ffff0000f0f0f0f000000000a0a0a0a000000000f0f0ffff00000000a0a0aaaa55550000000000005555000000000000555500000000000000000000ddddcccc00000000ddddcccc00000000ddddcccc00000000ccccccccff00ff0000000000ffffff0000000000ff00ff0000000000ffffff00ff0fff0f00000000ff0fff0f00000000ff0fff0000000000ff0fff00ffffffff00000000ff0fff0f00000000ffffffff00000000ff0fff00555555550000000055555555000000005555555500000000555500000000000000000000000000000000000000ff00000000000000ff0000aaaaaaaa00000000aaaaaaaa00000000aaffaaaa00000000aaffaaaa0000000000000000aaaaaaaa000000000000000000000000aaffaaaa
|0,9=>0xffff000000000000ff00000000000000ffff000000000000ff0000000000ffff000000000000ff00000000000000ffff000000000000ff0000000000000000005555000000000000000000000000000055550000ff00ff0000000000ff55ff0000000000ff00ff0000000000ff55ff00ff00ffff00000000ff00ffff00000000ff00ffff000000000000000000000000000000000000000000000000000000000000000000ff0000ffffffff00000000ffffffff00000000ff00ff0000000000ffffff00ffffffff00000000ffffffff000000000000000000000000ffffaaaaffffffff000000000000000000000000ffffffff00000000ffffaaaa00000000000000000000000000000000555500000000000055550000aaaaaaaa00000000aaaaaaaa00000000ffffaaaa00000000ffffaaaa00aa00ff0000000000aa00ff0000000000aa00ff0000000000aa00aaff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ff00ffffffff000000000000000000000000ffffffff0000000000ff0000ffffffff000000000f0f0a0a00000000ffffffff000000000f0f0a0a0f0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0a
|0,10=>0x33330000000000003333000000000000333300000000000033330000ffccffcc00000000ffccffcc00000000ffccffcc00000000ffccffcc0f0f0f0f000000000f0f0f0f00000000030300000000000003030000ffffff0000000000ffffff0000000000ffffff00000000000000ff0000000000000000000000000000000000ffff000000000000ffff0000ffffffff00000000ffffaaaa000000000000ffff000000000000aaaaffff000000000000ffff000000000000ffff000000000000ff000000ffffffff000000000f0f0f0f00000000ffffffff000000000f0f000033333333000000000303030300000000333333330000000003030000cccccccc00000000ccccfffc00000000cccccccc00000000ccccfffcffffffff000000000f0f0f0000000000ffffffff000000000f0f0f000f0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f003333333300000000030303000000000033333333000000000303030000000000000000000000000000000000ffffaaaa00000000ffffaaaaff00ff0000000000ff00ff0000000000ff00ff0000000000ffffff00aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaffaaaa
|0,11=>0xffffffff00000000ffffffff00000000aaffaaaa00000000aaffaaaa00ff00000000000000ff00000000000000ff00000000000000000000ccffcccc00000000ccffcccc00000000ccffcccc00000000cccccccc00000000000000000000000000000000000000000000000055550000ffffffff00000000ffffffff0000000000000000000000005555000000000000000000000000000000000000ffffffff00000000ffffaaaa0000000000000000ffffaaaa000000000000000000000000ffffaaaa0f0f0f0f000000000f0f0f0f0000000000000000000000000f0f0a0a00000000000000000000000000000000ffffff0000000000ffffff00ffff0000000000000000000000000000ffff00000000000000ff00000000000000000000ffffffff000000000000000000000000ff00ff00ffffaaaa00000000aaaaaaaa00000000ffffaaaa00000000aaffaaaaaaaaaaaa00000000aaaaaaaa00000000ffffffff00000000ffffaaaa3333333300000000333333330000000033333333000000003333222200550055000000000055005500000000005500550000000000000000ffffffff00000000ffffffff00000000333300000000000033330000
|0,12=>0xffff000000000000ffff000000000000ffff000000000000aaaa0f0f0f0f000000000f0f0f0f000000000f0f0f0c000000000f0f0f0cffffffff00000000ffffffff00000000ffffffff0000000055550000ffffffff00000000ff00ff0000000000ffffffff00000000ffffff00ffffffff00000000ffffffff00000000ffffffff00000000ff55ff005555000000000000555500000000000055550000000000005555000000aa00ff0000000000aa00ff0000000000aa00ff0000000000000000ffffffff00000000ffff000000000000ffffffff00000000aaaa00000000000000000000ffffffff000000000000000000000000aaffaaaaffffffff00000000ffffffff00000000ffffffcc00000000ffffffccffffffff000000000000000000000000ffffffff00000000ff55ff00afafafaf00000000afafafaf00000000afafaaaa00000000afafaaaa000000000000000000000000000000000000ffff000000000000ff00ffff000000000000ffff000000000000ffffffff00000000ffffff000000000000000000ffffff00000000000000000000000000ffffff00ffffffff00000000ff00ff0000000000ffff000000000000ff000000
|0,13=>0xf0f0f0f000000000f0f0a0a000000000f0f0f0f000000000f0f0a0aaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000ffffaaaaff00000000000000ff00000000000000ff00000000000000ff550000555555550000000055555555000000005555555500000000ffff000000000000000000000000000000000000aaffaaaa00000000aaffaaaa0000ffff000000000000aaaa000000000000ffff000000000000aaaa33333300000000003333330000000000333333000000000033333300ffffffff00000000ffffffff000000003333330000000000333333000f0f0f0f000000000f0f0f0f00000000030303000000000003030300aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000ffff0000ffffffff000000000000000000000000ffffffff00000000ffffff0033333333000000000000000000000000333333330000000033333300ffffffff00000000ffffffff00000000ffffffaa00000000ffffffaa0000ff000000000000ffff00000000000000ff000000000000ffff0000ff00ff0000000000ff00ff00000000003300330000000000330000ffffffff00000000ffffffff00000000555500000000000055550000
|0,14=>0xffff000000000000ffff000000000000ffff000000000000aaaaaaaaf0f0f0f000000000f0f0f0f000000000f0f0ffff00000000f0f0fafaffffffff00000000ffffffff00000000ffffeeee00000000ffffeeee0f0f0f0f000000000f0f0f0f000000000f0f0e0e000000000f0f0e0eff00ffff00000000ff00ffff00000000ff00ffff00000000ff0000000000ffff000000000000ffff000000000000ffff00000000ff00ff00ffffffff00000000000000ff00000000ffffff00000000000000000000000000000000000000ffff0000000000000000000000000000ff000000000000000000ffffffff000000000000000000000000ffffaaaaffffffff00000000aaaa000000000000ffffffff00000000ffff00000000ffff000000000000ffff000000000000aaaa00000000aaaaaaaaffffffaa00000000ffffffaa00000000ffffffaa00000000ffaaffaaffffffff00000000fafafafa00000000ffffffff00000000fafafafafff0fff000000000fff0fff000000000fff0fff000000000fff0fff0ffffffff00000000fffffafa00000000ffffffff00000000fffffafa33333333000000003333323200000000333333330000000033333232
|0,15=>0xffff0000000000000000000000000000ffff0000ffffffff000000005555000000000000ffffffff0000000055550000fffff0f000000000fffff0f000000000fffff0f000000000fffff0f000000f0f0000000000000f000000000000000f0f0000000000000f00ffffffcc00000000ffffffcc00000000ffffffcc00000000ffffffcc00000000000000000000000000000000ffffffcc00000000ffffffcc000000ff00000000000000ff00000000000000ff00000000000000aa00000000000000000000000000000000bbbbbbbb00000000bbbbaaaa0000ffff000000000000ffff000000000000aaaa000000000000aaaaffffffff000000000000ffff00000000ffffffff000000000000aaaaffffffff00000000aaaaaaaa00000000ffffffff00000000aaffaaaaffffffff00000000ffffffff00000000333333330000000033330000000000000000000000000000000000000000000000000000ff55ff00fffffff000000000fffffff000000000fffffff000000000fffffff0ff55ff0000000000ff55ff0000000000ff55ff00000000000000000033331111000000003333111100000000333311110000000033330000
|1,0=>0x55555555000000005555000000000000555555550000000055550000ffffffff00000000ffffffff00000000555555550000000055550000ffffffff00000000ff0fff0000000000ffffffff00000000ff0fff00eeeeeeee00000000eeeeeeee00000000eeeeeeee00000000eeeeeeeeffffffff00000000ffffffff00000000ffccffcc00000000ffccffccffffffff00000000ffffffff00000000bbbbaaaa00000000bbbbaaaabbbbaaaa00000000bbbbaaaa00000000bbbbaaaa00000000bbbbaaaa0f0f0000000000000f0f0000000000000f0f0000000000000f0f0000fafafafa00000000fafafafa00000000fafafafa00000000fafafafaffffffff000000000f0f000000000000ffffffff000000000f0f0000ffffffff00000000ffffffff00000000aaaaaaaa00000000ffffaaaa00000000000000000000000000000000555555550000000055550000ffffffff00000000ffffffff000000000000000000000000ffff0000000000000000000000ff00ff00000000000000000000000000ff000033332222000000003333222200000000333322220000000033332222ffffffff00000000ffffffff00000000333322220000000033332222
|1,1=>0xf0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0affff0f0f00000000ffff0a0a00000000ffff0f0f00000000ffff0a0accccffff00000000ccccffff00000000cccceeee00000000cccceeee0000000000000000ffffffff000000000000000000000000aaaaaaaa0000000000000000ffffffff000000000000000000000000ffff0000aaaaaaaa00000000ffffffff00000000aaaaaaaa00000000ffffaaaaff00ff0000000000ff00ff0000000000ff55ff0000000000ff55ff00ffff000000000000ffff000000000000ff00000000000000ff000000ffffffff00000000ffff000000000000ffffffff00000000ff000000ffffeeee00000000ffffeeee00000000ffffeeee00000000ffffeeee00ff00ff0000000000ff00000000000000ff00ff0000000000ff000000000000000000000000000000000000eeeeeeee00000000eeeeeeeeff00ff0000000000ff00ff0000000000ffffff0000000000ffffff00ff00000000000000ff00000000000000ff00000000000000ffff00000000000000000000aaaaaaaa000000000000000000000000ffffaaaa33333333000000003333333300000000333322220000000033332222
|1,2=>0xffffffff00000000ff00ff000000ff00000000000000ff00000000000000ff0000000000ff00ff00f0f0ffff00000000a0a0aaaa00000000f0f0ffff00000000a0a0aaaaffffffff00000000f0f0f0f000000000ffffffff00000000f0f0f0f0ffff000000000000ffff000000000000aaaa000000000000aaaa00000000000000000000ff55ff00000000000000000000000000ff55ff00afafaaaa00000000afafaaaa00000000afafaaaa00000000afafaaaaffffffff00000000afafaaaa00000000ffffffff00000000afafaaaaffffffff00000000aaaaaaaa00000000ffff000000000000aaaa0000fcfcfcfc00000000fcfcfcfc00000000fcfcfcfc00000000fcfcfcfc0000fcfc000000000000fcfc000000000000fcfc000000000000fcfcffffffff00000000ffffffff00000000ffffffff0000000000ff0000f0f0f0f000000000fffffafa00000000f0f0f0f000000000fffffafaff33ff0000000000ff33ff0000000000ff33ff0000000000ff33ff000f0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f0000ff0fff0f00000000ff0fff0000000000ff0fff0f00000000ff0fff00
|1,3=>0xaaaaaaaa00000000ffffaaaa00000000aaaaaaaa00000000ffffaaaafffffcfc00000000fffffcfc00000000fffffcfc00000000fffffcfcffffcccc00000000ffffcccc00000000ffffcccc00000000ffffccccff0fff0000000000ff0fff0000000000ff0fff0000000000ff0fff000000000000000000ff0fff00000000000000000000000000ff0fff000000000000000000fff0fff0000000000000000000000000fff0fff0ffff000000000000fffffff000000000ffff000000000000fffffff033333333000000003333333300000000222222220000000022222222ffff0000000000000000000000000000ffff000000000000555500000000fafa000000000000fafa000000000000fafa000000000000fafa00000000000000000000fff00000000000000000000000000000fff033333333000000000000000000000000333333330000000033330000ffffffff00000000fffff0f000000000ffffffff00000000fffff0f033333333000000003333303000000000333333330000000033333030ffffffff00000000aaaaaaaa000000000000ffff000000000000aaaa00000000000000000000000000000000333333000000000033333300
|1,4=>0x54545454000000005454545400000000545454540000000054545454ffffffff00000000ffffffff00000000ffffcccc00000000ffffcccc0f0f0f0f000000000f000f00000000000f0f0f0f000000000f000f00ffff000000000000aaaa000000000000ffff000000000000aaaa0000fffcfffc00000000fffcfffc00000000fffcfffc00000000fffcfffc33303330000000003330333000000000333033300000000033303330ffffffff00000000ffffffff00000000cccccccc00000000cccccccc0000fff0000000000000fff0000000000000fff0000000000000fff0
|_,_=>0
def sP:Nat→Nat
|0=>0x50500c0801004381a1082004010384818200100414140307c02100f0483a08010040e120200c04010e0641803010580e190982004010c05018030105820140985c04010504818030285820140a808021009050260e0100414120300c220105048260e0103414120603822010803c180e01034140c0401402070602c04010502410020081c0c03028040004018080200
|1=>0xa018060206840240f1189c1c0200840342f1700c0401080505a130180802100a0740602008b0241409820040103868241301808562a0905036030100452120a0a018030100420190980c0a01000504e03010040e190302004010e0644c030100414140602c04010803c0c080105820120600c0401128640c030087048190300c04010e064260e088041412060880401
|2=>0x84024140982004010e06428060184402100d048263c0100420120a010060200840241911830060206840280c0400802100d0500c030084048120784c0610150ec24140980c02071d048283901808023809050260e0100414120980c02371b048280c0180802350c8503a200100438100a018060200840240f0600c04011a8d02813010406632090502603188042012
|3=>0x611404010806828130180802490905026030100490470a1188a020084024140980c0444218482823030b804010803c262e01004200f0a0185c2001004201a098b8040d0803c28132100802100785026080100482120a08c0c030103420120600c04160805036030100480120a08c0401080fc24141f00c040108048280c018087a070806818060180802100784c0605
|4=>0x905018130180802070c87406020087032140600c04010503c281307004204f0d04826030810ca8120a08ca6020084034120300c3e0108048a40c1100c043d08050460c0700820430d09c06020084032140993004010803c280c01808024909050260301004a2120a04c06102813c241409808020a27048284601808024d090500c4c1000802100d12c0602008409414
|5=>0x682824140980802350f048281b01808026109050c04b0980c04010806c04012f878241411830060108178280c1000802100d05026021e8403c120a04c04010817424142308004010804828132e00c205b090500c032d004201a0904c1002008d424140980c20592c048282101808021c0c8500c030280420120c8304403010046a140980c20572b0482855100080210
|6=>0x999804010504828133480802100905026030815c6c120a04c06020084034680319ccc020084034130180420650905096130100420640a04c061106840241409838220108068240601808021c0c8740602008d424140980c040131848281301840865809050361304008021c0a0300602008ac601409838040d080481e1301808020a090502603010acc4120a04c0602
|7=>0xe0683213100080210090502603008dc48120a08406020092424140608804010803c281301808023709050e2030100420120a00c0401081c024140e80c040124848281300840b01e09050260301004de120a1b8262e01004200f0d80c0401368682603010ac66120a00c0401361ac24140300c04010e068d41322808022b090502603010dc54120a018400200870201a
|8=>0x870207e0a04c5c03008406c120a04c06101995834120a1ec260300840f8120a06c260300840b0120a01806020084034123c9dc262e0180802100a04c04010817c3c120a154cc020084024140600c040124868280200840c84a0905042030100414120a06cec0601808021c0e80c0401050482875018080210090502666010046e120a1c8262e0100490140300c0401
|9=>0x840248b0a07426030100420120a04c06010822448120a04c06024384034120a1e8ec130180802100a08c26200100420120a08c260200840c8120a06c3a030100482120a218262e01004201a0a04d08030084048120a04c06020087034190a04c06020820c66120a1ec26030084048120a04c160301004201a091e826030100506120a04c060200a0500120a04c0602
|10=>0x3d26026030100420140e84c0602008ac24140980c04101984868140d81806020084024194b86c0c030100420124a84c06020090424140980802104a04916140624c06020084034140988806020084124140980c041047848280601808028d0d0482622010042012078500c030100420120784c061f0081c201a09230262e0180802100a03044030100420300a0bc0602
|11=>0xa1b8469f0100420120a08c180200840c8120a04c5c0301040541a0a1e826020084064120a04c0601080913c120a03006020084034880a01826020084064120a06c42030100482120a04d380200870201a0a08c180e01004201a3d80c04010817c24140980c04102b86824140300c04012423424140600c04010806936144c84c06020084024142300c0401080491014
|12=>0x5504828130180802352704828230e80c04102184828131080c04011584828235480802100d04828780304c06020084034280d84c060200870341b0300c041019848281301841502453848281301808022b4d0482813018094c100905046130180820a309050260301040a0120a28826030081c207c091e0260301040ae120a284262e0100420120a04c060200a803412
|13=>0x980c040103848281301808821059048280c0980c040103868a41301004381e092c428060180820330922c28460980c04012084828060187c02100d048262e01004201a3c850360301004da120a01806020084024790a04d5c03082b424140980c0a010804828460980c040103848281d0180802102f848281d01808021009064282301808021056048281b018080210
|14=>0xa04c5c02008401e140dae40c030100438140980c048708048a4140980c0401082ec34125d04c06020084034124500c040108048d4140d84c0601082e024143c04c06020810c34140600c040103840348b0980802100f04860141080c04010804832143704c0602080cc24143e84c0601080d824145b84c0602080a824140980c04015a04828603704c06020084024b3
|15=>0x1004201a0980c02070815834123d04c060200840341411b04180e0100420144604c06020084034126084c06010809024140980c040124848281301b000401080682603010057e8d0d0483a13018042058090503a2001004201a090502603012f420120a04c060203840661a090745e030100420120a154262e01004201a0a04c44030f80420120a08c2622010045612
|16=>0x100438140983806021e84034126304c0601080ec24140e88006020084024141183952020084024145d030260301004201a0324c060200840241409b14cc020084024141404c0601081f034120980c02c4082a024140d9d82603010043814098800401080486814119dc180301004201409838060200a8024140980c0401159cc24146101806020084024142584c1c03
|17=>0x3300802100905046c10600c041021850260300840b0120a0bc06020084024140d84c1002008402414098380602008d434120180802104112824140999804010804992140e83806020084024305d04c06020084024143b84c0602008402414108b806020084116140980c04010832034140980802410f04962140980c04011a86824140980c040146b1c24140da602603
|18=>0x980c04102c848281b018080210678482813018087a10091482813018082c100906428131700c04102b84828130180420ce0905026030100420cd09050ee0c0980c04010805198130180802100d050180301004201a07850f4b90980c04102c8502622018082033090500c1301808205709050c0131100c040108048f0130180802100785174130180820590905026cb
|19=>0x9d024140980c04011604868141400c04010817c24140980c04106a0482806098b8060108090341301004201e0922c28d30980c04014084828230100420d209051180c0980c04010805046550180802100905026030100438105d86846530100420120a04c06020810da2120a03040020084034140980c204312048281301808024108340241311008022b090d02828
|20=>0x840bc120a04c06020082824140980c04102806824142a84c06020814024140e80c0401081282414098b8060200920e81409b700602008402414098880602008dc24140600c040146b6c24140304c060200841b41a0980c04010e048d4140980802100f33c24140980c02106c35c241409b5806020084024141189c06020084034145d0182603010042012098880602
|21=>0x840246a0a04c44200100420120a04c440200840c8120a04c060208165be120a08406020084094120a08c0c030104054120a04c06050084034120a2e826030104086120a06c3a030100420120a12c262e0180802100a00c04010826894120a378260301004381a0a04d26020084024790a06c2603010049a120a04dba02008403c120a04c06020084024790a3042603
|22=>0x71008202a09050f0600980c0401080683a03010046a120a0a026030104086120a06c0c1301808021c0d06c42030100420120a15426030100420120a074060200840248b0a1e972130180820430a1ec2602008403c120a1ec0602008419e120a04c0602008ac70120a1e8260301041c0120a08c3a030104066120a04c40020090420120a04c0602008706a1a0a1180602
|23=>0x100420124d850f61301808203309050360c0180802410d0502603010048212350502602008703c12290502603010043810668502693018080210090504e130700c040108068462201004204a09050260301004921a090502603010040e830d04846060180420240d048260301004388309051841301808021009050f01301808022b090503a03008404812458504613
|24=>0x104086e80905036e70980c04010e051cc130180802100d05026030100420e50d048269301808024909050c01d0980c040108048181301808022b0d050fa4b0980c0401080502602008702032090500c2e0180802100d0c1aa130180820d40905026e401808023509050e4134e008021c09050460c0300c040108068f06e0980c0401080682603718082059090502603
|25=>0xa0742603010046e120a0a0360c0180802100d0a026030104164120a228060200840248b0a06c26030105820120a04c8a020084024145084c44020084024141192c18030100420140980dd4020084024140600c043d080505e0301004201a09050180301004205f0d050461d010042064090502603010042012748503a13018406624090503606018043824090502603
|26=>0x84024140980c04017784024140980c0401080481e140980ddc010804828130180802370905036130100420320905050030100420cf0905026030081c20ec090504606018082043090503a0375808021009050260301004141a0905018200180802100d0502603010046a1235050260b1000802100d0482603080cc48120a0e426030100456120a1540602008402430
|27=>0x100420124585036130180438240905026667980802100905036130180420ec090503a660100420120a1ec26030100506120a03006020084060520a030260301004200f0a04c0602008d424190a1f426030100420120a04c0602080a948120a3c826030104054120a04c0602008d424340a04ccc020084024f10a04c0602083c024520a08c260e0104054120a04c4002
|28=>0x18080210091e428132280802100d0482813018080207082ec240c0980c0401083d8280c0180802100d22c281b1080c04010e068281301808021c1a84828130180802f54084828270180802100d22c2823112a4040108048281b0e80c04010e068281301840865b0905046131700802100785026220180802a009050f61301004203209050180301004204a0d050aa03
|29=>0x180802100922028130180802370d048281d0180802100926c280c0300c040108069161d4980c0401080482813498080210090d0280601808021025048281301804208312048281301004201e7c848281301808020a0903c28060180420240d0491613018080210418482821018080210091e4281d0180820330922c282309838040115848281301809f01021848281d
|30=>0x180802107f06828060980c04010830c24143d06c2603010040e120a08c26030100420120785026030100420fc09051f41301808021009050260301004201245850260301004204a0905036030100438cf0905046a90100420120a04c060200a8024140980c20332b048281d3300802100d04828131100c04101504828214980c040108048281d0980c20332b048281d
|31=>0x300c04010804829050980c04010384024141406c260300840f8120a06cec13018080210090502603010042104090503613018082043090503a13018080210090512a13018080207090502603010042091090503a030100420ca0d048281b8180c04010804828131700c04010840824140983806020084034121806c260301004210009050dc237f80c0401080482813
|32=>0x9c2c1c020084024145104c06020081c20123e88c26030100420120a06d301301808021009050260301004209a090503a130180420240905026030100420121a2f8281301808030a84840241437018260301004201a0926426030100420120a04c06020081c341229018260301004208309050181301804205609050260301004381229050260383804210609051f623
|33=>0x1808021009050262201808022b0d04828130180802070844024140e84c5c0301004201a0a1e0262201808021009050260200870201e0905046c10600c040108050260301004210e09050270d1700c040108048281301805881012048281b5104c06020087024147684c06020081c20120a0a036130180a180109050360c01808204309050501b0600c0401080482823
|34=>0x100420120a04c422e0180802100d050c0131700c040108048281301804207c0905046131100802100905036130180802106f848280c0983806020810c24148b0a026030100420120a1b8260e01804203b0905026030100421150d05036130180a2801090504606098b804010804828cc8984c060200840241409c4806020084024340a04c0602008402430290522213
|35=>0xa04c1c03010042092090502603010042012459e4291e0980c04010804828130180a3a0108048281b0980c04018e048287b1404c06020084024148d04c06020084024140980c04010812834120a03026220180802100d05027190100420120a04c0602008ac24141184c1c0200841b2120a04c07170100420120a1b89613018080210090500c03010051a120a3182603
|36=>0x840341245850268a01808021009052461301808021009050fa0c0980c04010804828c10604c0602008402813018087a100d04828280e84c060200840241409c881c0200840241409c8006020084024140d84c06e30100424140980c02105684828ed0d84c06020084024140600c04010832834143d04c06020084034145084c06020084034120a04c0602009042452
|37=>0x84024141183006020084148120a04c1c030100420820d048dc230980c04010806824230e80c04010806824140980d52020084024140983806020084034124584c0602008d434120a06c0602008424a120a04c440e01808022b090503a0301004201218050dc138580c0401080482813018080210920682414098080241080782414142882603010040e100904c0602
|38=>0x4ba8826030100420120a04c0602008d4201a0905036030100656120a04ccd2a0100420120a08d82131700802100a04d26030100420124585026030100420da0d050260301006501009050260301004212709050266733008021009051440c0980c040108048281b0604c06020084034140980c0401082ec24145d04c06020084024140980e18010809024143b84c0602
|39=>0xa04c0602008402452458500c131700c040108068501301804202409050dc130180802106c848287b0980c04010806824140980c04010833424140980c040103841a0121404c0601081f024143008c26030100420120a0a026030100420120a030260301004201a45850260e01808021025048287a5c84c060200840288c0980c04010804828231080c0401080682414
|40=>0x97008021009050260301004212d09050361d01808021009051e423098b804010804828230600c0401080682813018080210091e428130180802106f84828238d80c040108048280c018080210180510c130700802100905018130180802107b848281301808021074048281b0600e58020084028130180802104d06824140e84c06020084034120a06c260301004381a
|41=>0x980c04012087024146104c06020084024141384c06020084034140980c04011586824140e84c06020084024520a04c060200904209d09050460657008021009050461d0300c040108048287d0988806020084024141184c44020084034120a06c42030100420120a15426030100420120a1801813018080210090503a0301004201245850360c0300c0401080482813
|42=>0xe84c0602080cc24140d81806020087024143c30418130180802100a1e0262e0180802100d050268a0180802100d04828130180802100922028130187c02100905026030100420124d851c27a0980c04010804828130700c04010826824140988406020084024520a04d26030100420120a1b8181301808021009050260301004821a0914828210180802100922c281b
|43=>0x922c28237f83804010804828133300802100d04828060980c02101206824785b84c06020084024140980c021054090241411b040c030100420120a04c0602084c824143b84c06020084034120a04c5c030104054120a04c06a901004201a09050269c0100438100905026030100438102f848281301808021098848281d0180802100d04860140980c0401084c02414
|44=>0x180802109b8482803008421136090502622070080210090d028131700c021012048287d0e84c06020084024140980c04010806824790a08c26030104054120a03006020084034300a04c060200904205f0905026030100421350905026030104268120a0a026030100421100905026030104066120a0300c130180802100d06c2603010042012350504613018080210
|45=>0x980c041021848287a1404c06020084024140980c04010806824880a04c06020084034124d850fa130180802100905026930180802100d04828131100c04010804860141080c040108068248b0a04c40020084024142a84c06020084034120a074060200840341245850461d0980c04010804828130180802100903c281b0980c04019c04828139700802100d0482813
|46=>0x1004201a0903c28131100c04010804916143d84c06020087020120a04c06020084106120a0740c0301004201245850273b0180802100905026220180802102504828130180820330d048280c0980c040108068a4142304c06020084024520a030060200840348b0a4e426030100420120a07426030100420830905026030100420f6090503a130180820330d0482806
|47=>0x1004201a090c0280c0980e58020084028130180802100922c28a10980c04010804828130180802102504828130180802104186824140980c04010804868790a07426030100420124585026211100c040108048281d0180802106504828131100c04010826824140e84c44030100420120a04c40030100420120a018060200840248b0a0740c13018082033090502603
|48=>0x980c040108048281b0980e4c020084024140980c050c082bc24140980e4c028604024149f04c06020084024141184c060200841b2120a04c42030100420120a1e818130180802100905018060980c040108048286e0983806020084024149e84c07260104024140980c04010827824140e84c06020084024141406c26030100420120a04c06e3010043810090502603
|49=>0xa3f426039600420120a04c440e01808021009051fa1301808021c0804828131700c04010806828f21184c06020084024140304c06020087020120a06c260301004201a0905026030100438108404828130180802103984828130180802108784828130180420240905182130180802100905026030100421400905027220180802100905026220180802100d048293f
|50=>0x905026030145002100905027430180802100905026210180802100d0482813018080210a1048281d0980c04010806824140300c04010832824140980c04010e0413a120a0a026030100420120a06d72130180802100905026660100420120a06c26030150402100905026ff0180802070804828130180a19410804828230604c06020084024140980c040108068248b
|51=>0x980c0401084842414a304c06020084024140304c06010809024140980c04010851424141184dc4020084024140e81826030100420120a04c06020084024520a08c0c030100420120a04c06020084288120a03026038380802100905046ff0180802100905018130180802100d050271b0180802100905026030100420fe09050260371808021009050260301004211c
|52=>0x1c9804010804828130180a180108048293d0980c0401080482813018080210090502603010042012458502603010042125090502622018080210090502603010042012180504e130180802100905026030100420ca0d04828f20980c04010804828130180802100d048a4140d84c06020087024140980c04010836424140980c04010841824140980c04010851c2414
|53=>0x980c04010804828230980c04010804828060980c04010804828130180802106504828137f80c04010804828130700c04010804828130180a82010804828130180802100d0482813018080210578482813
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32a0145007a8029400aa0005
|5,0=>0x2e98168c0ae6054302898138c0966048302298108c07e603c301c980d8c06660303016980a8c04e6024301098078c0366018300a98048c01e6
|6,0=>0x13bb89c1c4d2e262712db8951c49ae246711fb88e1c462e22a7111b8871c42ae20e7103b8801c3f2e1f270f5b8791c3bae1d670e7b8721c382e1ba70d9b86b1c34cc19f70cc38645c314e18370be385d5c2dce16770b038565c2a4e14b70a2384f5c26ce1306094b8489c236e1147086b8419c1fee0f87078b83a9c1c6e0dc706ab8339c18ee0c07
|6,1=>0x21ab90b9c84ee420720cb9049c816e40471feb8fd9c7dee3e871f0b8f69c7a6e3cc71e2b8ef9c76ee3b071d530e8dc738e39571c738e1dc700e37971b938dadc6c8e35d71ab38d3dc690e341719db0cd1c65ae326718fb8c61c622e30a7181b8bf1c5eae2ee7173b8b81c5b2e2d27165b8b11c57ae2b67157b8aa1c542e29a7149b8a31c50ae27e7
|6,2=>0x43c7
|7,0=>0x31ac18b9cc4d061f730bc183e0c0f05ff82fbc17be0bcf05df82ebc173e0b8f05bf82dbc16c1cb5105a082cc416420b11058082bc415c20ad1056082ac415420a910540829c414c5ca54e522828db944e0a170503827dc13ce09d704e3826dc134e099704c3825dc12ce095704a3824dc124e09170483823dc11ce08d70463822dc114e089704438
|7,1=>0x41642092103908148406420120ff907f483f641f920fb907d483e6b9f19cf7d07b683d741e9dcf3f079783c7c1e1e0eff077873b841da20ec1075883a841d220e810738839841ca20e410718838841c25ce0306f98378c1ba60dc306d98368c1b29cd8506bb7359c1ab1cd4ae69d834ac1a360d0b067d833ac19b60ccb065d832ac19360c8b063d8
|7,2=>0x5124287214290a0c8502427f213e909ec84f2ba77613ab09cd84e33a6fa136d09ae84d3ba67e1330e99174c4c260612f3097184b4c258612b3095274a54250a1275093284954248a1235091284854240a11f508f28475ba391d1b908d4846642312117908b48456422921139089484464221210f9087484364219210b90854842642112107908348
|7,3=>0x6114306a18250c0a860142fea17e50bea85f142f6a17a50bca85e142eea17650baa85d142e6a17250b8a85c142dea16e50b6b75b1c2d6e16a70b4b85a1c2cee16670b2b8591c2c6e16270b0b8581c2bee15e70aeb8571c2b6e15a70acb8561c2aee15670aab8551c2a6e15270a8b8541c29ee14e8ea6c85324297214a90a4c8522428f214690a2c8
|7,4=>0x70d4384a1c150e0286fd437ca1bd50de286edbb74e1b970dc386ddc36ce1b570da386cdc364e1b170d8386be3b5d21ad90d6576af3b55a1a9d0d46869f434da1a5d0d26868f4345a1a1eed07867fc33de19df0ce7866fc335e19a0ecc88660432e21964ccaa86514326a19250c8a8641431ea18e50c6a86314316a18a50c4a8621430ea18650c2a8
|7,5=>0x1e8d0f3e879b43cbdde50ef21778cc3c461e130f01877cc3bc61dd30ee1876cc3b461d930ec1875cc3ac61d530ea1874cc3a461d130e81873cc39c61cd30e61872cc39461c930e41871cc38c61c530e227
|8,0=>0x8b4cc589e2b5115198a44c4fe626d312e8893444766229310b98814c3ea21e330e8986fcc35a619d10c6885f442d6615b10a4984dcc24a61151081983c4c1c220cf305e982b4413a208b303c9819cc0ae2047101a98094402a20050ff997f84bf9e5fbd2fd687e743f1a1f7d0fb687d6cbe961f392f9397c54be065ef30f7097b3cbd7a5ead0f4e8
|8,1=>0x9c04cdde66dd336779afc4d5e269d3346899f44cda265d1325998e4cc5226191304897e44bce65d532e1996c4cb42258f32bf895bc4aba654d129d994a4ca322507327a9939449aa24c332598928c4922648112388918448a5e441321889084481e63ff11f698f6cc79623bb11d588e64c712237731b298d5bc691e337319388c54c60de2f711729
|8,2=>0xacccd6462b1135808abc455c22acf355e9aaacd5362a8cf53e8a9acd4b26a47351b8a894d4266a0314f89a78453a229c114d79a674d31a297b34b49a55cd28e293714929a454520668f4f4728a354518668b314518a24c51062874f4328a14cd086283314109a03ccffe27ed33ee89f344f7667a933cc89e244ef2276733ab89d14ce66672313898
|8,3=>0xbdacdeb62f49379b9bc9c5e2e2f0537799bb84dd9e6ebf17569ba745d166e7b17349b95cdc8e2e3717129b8545c066df316f09b73cdb7a6dad16cd9b624daee6d68f6ab9b514da666d2316898b40c59e62ce4f6699b30c59626c9f36478b1fc58da6c5d16277b0f4d85dec1f16069afecd7d62bdb15e58aee4d7522b9735c47addcd6ce2b5535a28
|8,4=>0x2fd317e18becc5f426f8f37be9
|9,0=>0xd00467e233e119e88cf046762339f39c78cdfc66de335d39a68ccf4665a331d19868cbf465da32dd19659caec6552729919439c9dc64ca7256f9229c8cce446321138ff9c7bc63ba71cb38dd8c6a4e32e718538b99c58c62a63144f89a8c494622a310338798c384e1a230c118588c27ce11e307d38359c164e092303918148c05ce00a6ff337f18
|9,1=>0x696a34a51a4a8d21468ea34633a298d104e86234211a088
|10,0=>0xd5cc6ac635531aa18d4cc6a4635131a818d3cc69c634d31a627
|11,0=>0x1ac17
|_,_=>0
def wAt:=mkWire dB 328 224 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x9849098680a0490803d118680980d008c1098680a049098490185110049018c1098680986809051098510083d118680a0490980d01865080690d86809051098410d868008c1098680a049098491186801865080490d8680a0490984111868018510803d118680980d1a868080c1098680083d118680980d0986b0e8c309868018490986901865080490d8680984109849118680a04909849008650d86809051
|1=>0x905103049098510986909051098bb42849018910300b098510d8680a049140490300b030410985110051018c109868090510605109849082090983b018513f84903073098513e80b3c051098b90e80b0e80709869140491400b03041098513d80b3d0510d8493c06b0a049098b93a049081cd098bb09849118680a04908049098510d86809051098410083d11868090510980d01065098510d8680905109841
|2=>0x80490a0490980d01851098493e807118690980d09851082390980f072690988b07049098691104301869098510d8680984103849082590981f0805107049410490983b0185100a46480490d80b0984108239090510980f098510186911868090510980d0985111868090510980d08051010c1098680a049098680a0490984910a2d0986a0986b450690994b0806a00a21099480806a3d06b060410984911868
|3=>0x9868090510600706051098490980d098880186909051098510600d09849080490d85109841098410e807030490985100aa2120490300b0985100a96520491180b0980d2a807098d10186a090511400b140530981d3e8073c0510600d098490988b17051082690988b01869098b8018490980d06051098493c0070a049098b9018493d80f3d051060413d80f0307108049080690986b090510905101a7509873
|4=>0x90510986b0d868090510300d0e807030493e80b098891705101849082d909ad701851118513c053118490601f098493d80709905038490806a080510807a2080f0e051080490e8070e84f0304909851099490905109851010c1098680a0490601c098410805109849099920e80f03049098510080d012c25785109807010650d8680a04909841098690d86809841118870986b090513d2af098530d849080c1
|5=>0x9869090510e27509873080493b8511186b090510980d4984301a2d0986a030b809051018490985146851082390980f3d80b0e841060510984909869018c1098680905100af9098d00186a0e8070805109869090510e8c30986809869010c1098680a0490980d070490185101849118680a0490980d5e0510990708069090513d8530d86909051098414c00b5c8510d84b060070600d09849098682080f08069
|6=>0x18650d8680905101851080c109868090513306a0905101b29098680185109869018490986a0986b06104080690a049098490807a2080f0384908051080650d868090510984101851008c109868090510300d09888018510980d3d05306041098491400b03041090510985112049080910300b09851098680186a09051082690988b07049098bb110430184909b0d030ba018490985109839018510e80b08051
|7=>0x4f851098b8018490980d09849018c1098680a049038494b0510981f080511100f1104307049018513d0070d849098413d84f140490d851008650d86809051098413e8073c051098b93c06b0600d09849108b9018490986b0a04909849118680a0490d84b3d0070d8490e80709869090513e807030b9018493c05317051098b911849118680a0490980d330690905101b29060070980d10a2d0986a0986b09051
|8=>0x980d2a807098d10186a2a807098d10186a090510988a09869090513a049081cd098bb109490986b0806a0905109889070490185109849082390980f09872080490d9060e051098416c851118070980d0e94b0986909051098513d0530604109849098bb0186a0905109904038490981d6a8075b849118530980d09051018490985140839082090983b11a7f098b80980d1184b099e51186a090510987308049
|9=>0x98670d86809051099e51186a0980d09a2d0d0c3098683d04b0600709849099052080f03849080513d84f0990503849098ac1104307049708073d00906041098490e8070986909051098680905108049080c1098680a049099a90d86a0905109868090510986909051098513c007118490980d010650d86809841108690986b090513e84b3c051098b90986b0a0490986a090510d86a090510803d1186809051
|10=>0x80c109868090514e04101a750987308049098510980d0984911849118510980d0d2fb098d0090510e8070e84103049098510a049098490994a090512080f0e0515d8494e851098730d0c30986809051018510986b0988a07049018514984301a2d0986a09869090513d051098711104317051098b90300b0e84f098513c007118490980d3c0530600d0984909869080c1098680984106007098490984108049
|11=>0x8650d8680905101a21099480806a018690986b09051118510980d110c3098680905109849008c1098680905110a2d0986a0986b099040a04909849030490985137307118510980d0300b0e8070304909851080490d85109841450490994b0806a0a049038c3080510986801a2d0986a090513c05306051098491104301869098493e84b09889170513d80f3d051098710986809051098515b849118530980d
|12=>0x980d1a868080c1098680905110889018690986b090510186a09051330680905101b2909843018513c007118490980d01af9098d00186a0d1e7098d20186a090513d80f140490d85109906038490981d7680b140050981d098510980d06007098490803d11868090510980d09849018c1098680a04910051018c109868098ad1104307049018513e8430e80d0304909851098490d851098413d8071404903041
|13=>0x9869098d20905101a21099480806a090515e05109907038497b8490981e08051098490d0c3098680d9040e05109841082090983b018510986a0986b0a0490988807049098690a049013d221851060070984901849118680980d0988b07049018513d80f099050384908051018690a0490986a098d10186a0905108049098410300b098517680b140050d8510986901b2909843099050384909849118680a049
|14=>0x118510980d090516504909843030ba01849080510d8490984111868090510980d7e8ba01849098097d85309ab90080d0e05108049098880980d0704901851098690905101b29098433c00717051098b90e80b0e80703049098513e843118690980d09a6d4706a09051098510986a0a049098490986a090513e84f030b901849098510803d11868090510980d0300b090510986a0e807098690808a070490980d
|15=>0x98070a0490300d098517f839018510984b080510806a090510e84303049098510e80b0605109849208430e05108049840490980b0104109851118050980d7f81d080510984b1400b0d851098410d86b09051098410601f080510984909841060070984909a2d0986a09051082590981f08051480490d80b098410984309869090517f851098410984b030bb09851018510986809051808510d807098410984b
|16=>0x9853110430186909051140070981d0805101849098690a04917051098b9018492080f0e05108049098491184b0980d878510604309849174210980b01849080910300b09851080490d85309841140050981d08051008410d85109841060070984109849098490d8510984100839018510980d140530981d37049118510980d5c8510d84b098410988b07049018510300b0304909851098d00186a09051082bd
|17=>0x984901a590981f0805111043070490185101851118070980d8c04909838018513704b0300d0985109851082390980f370050300d09851018490986b0a0493c053098b9018491400b03041098510980d07049018513d00b0d849098410600701851098490d8510d805098413700b09839018510600f0a049098498605309841008410980d01849098515580d098530186a09051098680806a090514a84b55841
|18=>0x60390185109849098491184b0980d008c109868090510304903041098510185101abd0980701c850600b09849010710804909841012c25785109807140050d851098410a0490984309849060410a049098491080d0986b09051208430384908051410490983b018510986a0905109c7d0e00b0804900bdd0981e08051098410384b080511404903041098518d8410304b098510988a0186909051018690a049
|19=>0x9841098494e85109873080493d0530604109849008410300b09851608531184b0980d098491180b0980d0a0490983b0185109051118510980d09869090510980d098880704901851018510986a09051080c1098680905109c9a010050984111043070490185109868098690905107005098390185147069090510980f2080f0384908051140530981d0e84f09869090510994b0806a090515c8090d84b09841
|20=>0xd86909051098417f05165049098434b0510981f080511400b03041098513c053118490980d03a590981f080510986a0a049098490988a07049018510d8490d84b09841608511184b0980d0986b090510980d0d85309841080c109868090510981c08051098413304b01b29098431184b0980d0986a09051098720a0490804994849084210980b0307008049098513304901b2909843098490d8530984109051
|21=>0x984909a2d0986a098410984909851018c309868090510e4230980b0804909869090510984101849118090980d0980d0a049098491186a090510980d3d00b06041098490980d0304b09851098680a049098497f80d018510984b0981e080510603a01851098490984901049098410988b0186909051108690986b09051080490a049098410986a0806a090510905101849098510300b0304109851118070980d
|22=>0x806a09051010c1098680a0494706a090510980f3d00906041098490988b070490806a0905101a2d0986a090510300d0984909851081490806a090510986a0986b090510e051080490984109cbd1705301849108490986b0a049110430186909051098690806a0e0510987308049018050980d09851030490980d0985109889070490185101869090510980d0986b0905109841098d10186a090513c0530600d
|23=>0x98510d86a090510986a090510980d018510984b0905101b29098430300b0905109851118530980d120490300b09851098511184b0980d9980706009098491186b0980d3c007098b90184909888018690905101a750987308049099040e051080495587208049098530986809869090515b807118530980d0e80703049098510984108049098513c04b0600d098490a049098b9018490994b0806a0905109948
|24=>0x986b09051018c10986809051098d10186a090510986a0986909051060510980d0984911868090510980d0081e0805109841018c3098680905109c730384b0805109c1e0980b010411100f0704901851018490300b098510e80d0304909851098d20186a090513c007118490980d098680a049098490990403849080510638a098490100d1380755849098531400703041098510e80703049098510905109849
|25=>0x980d0986a090513d05109871080490e84303049098510e84f03049098519e04b01c210980b0988a07049018510e80709869090510806a0a04909849099490806a090510986a0a0490984909ce97104b0100d0e84303049098517b8490981e080510e80709869090510985106007098490d8490d85109841099480806a090514706a090510980f09889070490185101a2d0986a090510186909868090510986a
|26=>0x9805118070980d0986b090510604109849098490985109839018510100509805098ba0184903049098510d851098410e00908049098680905101049098490d0c309868090511080d0986b090510988a07049018510e84309869090510186a0905109a2d0986a018690986b090510304909843098510988b0704901851018690986909051018c109868090510e84f03049098510e80703049098511186809051
|27=>0x905100b8a0100d09869090510984309851098730804903041098510d84b0984101b29098430085109841080510984b00851008410980d098490986a090510104909809070490185108049098090a04901849118090980d080490985109051098410980b08049098bb0184906043098490300b098511184b0980d09b8a0100d01abd0980701869090517f8410984b0100509841098070084101005008419e809
|28=>0x100500841098050986a0905109c9a01005070490185109868090515584909853090510984309b890100d0806a090510804909841118070980d840490980b93043010050600b0984903005098510300b098511700b018490980d0100d03049098510806a090510980d09851098700804909849010410980d0984b0a049098490304b09851650490984383849010410384b080518605300841012b90080d0986b
|29=>0x980d09851098430984b01851008510905109807
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x74000000000000000000000000000043000000000000000000000000020000000000000000000000000000000000
|6,0=>0x1d1800000000000000036406a20000000000000000000000000006460000000000000000000000000000000bcc15a000004ca000012880000000000010a0201000006d400000000000000000001a1000000000000164000004cc000000000000000000010301e202d00000000000000000000000
|6,1=>0x51300000000000000009c600000000000000000000000000000000000000000000000000000000000000000000000000000000000000092a000000000000000000022a0000000000000000000000000000000000000000000000000000000000000000080a0f4c0000000
|6,2=>0
|7,0=>0x72a0e141bc636906c10d531a4634086620c93000000006318c3317e82ed00000b8316a60000591800000002bcc0000ac300002a100000000148828104e209841288241000008d3114621cc000084310261fc83e907b20f421d903a100000e081b1035106730c86184c2f185a40ae600002a18000
|7,1=>0x638c00018b331066110c1117e42f660000bba00002e865c10b6996942ca8588caf215b30000560caa9951400000000a6a14940000518ca19800027e84f0c9c9935400004c8c97992d225464a08922120423c446900001164224843908520000000041cc82190131fc63ecc0000f741e863c4c76a0e94
|7,2=>0x880d0e98000432886050b1213341e8830c000209340c68145011a0023f880000fc200003e887c10f699ea300007990f1980000000780cee21d933ac674cce819cd339280000e319c4200007010de99b9400006d8cd99800000006c0cd621a84348800000001a0433e20000ce1999300000000caa1914
|7,3=>0x57a6ae515b1ab330000ac0d5622aa25504a989519aa0353c4a6cd4c1a9620000a508000291351c6a2cd441a8535046a0093e9a7a34ee69d0d38226d34d469991319a6124ba8968d2c125620000000129224f30000930d249800048e491492190000000000011fa23c347088d4d191a2e445668a0d1312233
|7,4=>0x6b86d64daaa353269e8d2d0000348368a6d0c800033f46768cdd0000000066a4cc5000032d46546000193200000000c8cd901b1d3632800018aa31140000c38c00030a40000c191819b0030000bf4d7d1af735ea4bc8d7722eb35d06b989719adf45bc200016e12d845aa6b48d679acc35926b18d619ac03
|7,5=>0x7564e9d000000007468e80c00039c40000e64dcb1b9240000e409c6200000000e211c3100000000e0cdc0180006fa6de51bb1b7246e040001b69b6a36ce6d949b1935f4
|8,0=>0x8c87184e2f1c5b38b07154e291c4f38987124e239445288470fce1e1c39386c70cce181c2d3854709ce121c21383c706ce0c1c1538247040a069c0a380e7010e009bff27f86fe4dfb1bf337e06fb4df51be737c86f84def1bdb37b06f54de91bcf37986f24de393c437826ef8ddd9bb9276c6eccdd81bad3
|8,1=>0xa3e7474a8d1d173a287448a88150d3a14741ce821d0139fc73ece7c1cf539e473bce761ce939cc738ce701cdd39b4735ce6a1cd1399c732ce6494c639867300e5e9cba396e72d0e589cae395672a0e529ca2393e7270e4c9c9639285244e471c8b39107214e411c7f38f871e4e3b1c7338e071b4e351c673
|8,2=>0xbb27758ee99dd03b9a7728ee39dc43b8276f8edd9db83b6a76ccad895ae3b5676a0ed29da23b3e7670ecc9d972b287644ec71d8b3b107614ec11d7f3afa55e8ebb9d743ae275b8eb59d683aca7588eaf9d5c3ab4555ceaa1d513a9c752cea41d453a847500a9e9d3a3a6e74d0e989d2e3a5674a0e929d223
|8,3=>0xd287a44f471e8b3d107a14f411e7f3cfa59e8f3b9e743ce279b8f359e683cca7988f2f9e5c3cb27958f299e503c9a7928f239e443c8278f8f1d9e383c6a78c8f179e2c3c527898f119e203c3a7868f0b9e143c227838f059e083c0a7808eff9dfd2bf657e0efa9df23be057b4ef51de73bca5788eef9ddc3
|8,4=>0x3521ea13d3c7a6cf4c96972
|9,0=>0xe4a5c8cb90971f2e3a5c6cb8c97172e2a5c4cb88970f2e1a5c2cb8497072e0a5c0cb8096ff2dfa5becb7c96f72dea5bccb7896ef2dda5bacb7496e72dca5b8cb7096df2dba5b6cb6c96d72daa5b4cb6896cf2d9a5b2cb6496c72d8a5b0cb6096bf2d7a5aecb5c96b72d6a5accb5896af2d5a5aacb5496a72
|9,1=>0x1cecb9c97372e6a5cccb98972f2e5a5cacb9497272
|10,0=>0xe8e3d187a28f441e863d087a08f401e7e3cf879e88000
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 15
def pmP:Nat→Nat
|0=>0x9000000000001100000000000210000000000040000000000007e00000000000f400000000001e000000000003a000000000006e00000000000d00000000000188000000000030000000000005a00000000000a00000000000120000000000020000000000003a000000000006000000000000a000000000001200000000000200000000000034000000000006000000000000a000000000001200000000000200000000000028000000000004000000000000600000000000080000000000008000000000000
|1=>0x10000000000001b6000000000032a000000000064c00000000008fc00000000010400000000002000000000000204000000000040200000000008000000000000e600000000001b2000000000036200000000006c00000000000c40000000000180000000000027a00000000004900000000000900000000000117000000000021a0000000000400000000000042000000000007e00000000000fa00000000001c8000000000038000000000006800000000000b80000000000150000000000026000000000004a
|2=>0x206400000000040c000000000080e0000000001015000000000201a00000000040300000000008050000000001009000000000201000000000040180000000008018000000001002000000000200200000000040000000000005de0000000000bb800000000017600000000002df000000000059e0000000000a74000000000148000000000028f400000000051e0000000000a080000000001400000000000259000000000043f8000000000846000000000106600000000020a0000000000410000000000080c
|3=>0x64fe000000000c9f000000000191e000000000280000000000040240000000008044000000001004000000000200000000000038fe0000000006efc000000000d3f8000000001a7800000000034900000000006830000000000d048000000001a08000000000307800000000060b000000000090e80000000011f0000000000237e00000000046f000000000083f800000000107200000000020ac00000000041300000000008240000000001042000000000208000000000040fc00000000081f000000000103c
|4=>0x174fa000000002e8f0000000005c3f800000000b27f00000000164fa000000002c8fc00000000591e000000000b07f00000000160fa000000002c17c00000000581e800000000b03c00000000158fc00000000291fc00000000513f800000000a1bc00000000140fe00000000281f4000000005026800000000a000000000001355000000000261f000000000482d0000000008b2c000000001049000000000202bc0000000040100000000008008000000001000800000000200000000000030038000000006000
|5=>0x100438000000020080400000004002f80000000800020000000100002000000010008800000001783f800000002e07f000000005703800000000ac97400000001482f80000000230480000000044080000000008802400000000f83f800000001b2ff00000000360fe00000000464840000000088068000000010924000000002043a0000000040060000000008000000000000f87d000000001e8fe000000003c9fc00000000783f800000000f05f00000000177fa000000002eef0000000005dbe800000000ba7f
|6=>0x30009e00000006001080000000c0007000000018000b000000025509e000000046e1bc000000088416800000011002700000002160fe000000042a1fc00000008503f800000010802f000000020500a00000004049fc0000000804168000000100821000000020009000000004000a0000000080000800000009187f0000000120426000000023c1fc00000004782f800000008b87f00000001160fe000000022a0fc00000004511f800000008a07f000000010647e00000002080fc000000040c3f8000000081005
|7=>0x8025a000000010041fc000000200826000000040103e00000008008b40000001000a6000000020002d00000004000180000000800000000000082e1bc00000010523f800000020a47d00000004144fc00000008281fc000000101c20000000020147f000000040289c00000008051300000001004b4000000020086c00000004008ac000000080112800000010022480000002004420000000400882000000080084800000010009c00000002000ba00000004000940000000800010000000100000000000018a07d
|8=>0x100100400000020020020000002000000000000220b87f00000042170fe000000842c5bc00000108503f8000002109077000000420304e000000840419c00000100d83f800000200f07f000000401e0fa000000802c1fc00000100583e800000200a27f000000401200800000040a29740000008040000000001000012000000100000800000018281fc000000300a3f800000040f47f000000081e4be000000103c1fc00000020782f800000040f05d00000008172fe000000102c1fc00000020483b800000040525a
|9=>0x501401008800040080ae17c000801005c3f800100000b87f0000c140120be00010084ac5fc00020101582f800040200b07f00004000560be000040103c1fc00008020092d80000e0022010000009001249600001040bc9fc00002081193f800004008b2df000008001e4fe000008006c17c00000800009000000100000000000014210048000002802c1fc00000500503f8000008018825000001001e09e000002002d17c00000400587f800000800b0fd000001001619e000002002c1bc0000040055768000008009001
|10=>0x5020140160fe0a000280281fc10000500503f820000600f07f04000040560fe08000080281fc10000000783f810804002f27f020010211c0fe04000080241fc08000085383d80c200220800401000140160fe020002000e1b404000100503f808000000002000800140120c0008080003c1fc00c00101783f8010100006008002000001c0fe00210004ac1bc00410100783f800800102e07f001000201e0fe00200000bc1fc00400001583e800800000e47f001000001c0fe002000000c8fc0028000944278003808009877
|11=>0xc4000040140ff088002802c1fe10c10100503fc01810202f07f802020005e0df000002902c17d10000100503fa2000020098772002004000042400002002009050000701583f8a0000a00b07f140000c0140fe28000080281fc5000000058398481000000021
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x4000000000000000002000000000000000200000000000000000000
|6,0=>0x1c0000000000100000000000000000000000000000000000000000000000000000b8000000000003c00000000000000000000000000000000000000160080000000000c000000000021b0000000000000000020000000000000000000703e00040006c0000000023000068000000000003f000000006000c400000000000291c8100000000000000
|6,1=>0
|7,0=>0x18c001c020780c0706bdc4800049100c7a380180e5000008023b548000e070000616000d94c5a7b0001838010102d9e40012a0000a0f224560000018c6010e070001f0b3380a8400001661f66a0c3806170703c0b00000225502b980006030005a0000050000900164000031a0514202281c0002048c800060207038037083002000607c0206008700d0c008003800
|7,1=>0xe07c92190007174bc012ec02021d1500c0100004000b242001a51169040232242f828010e230380202804041d000003c06000043800008740600000004206428703833018102206001e0020002cb0a401149f0012d7c8a838047e000fc002bb9c2001002183800000e0441c5f008221c0f800020600240021f000040c00000100ade2b800001f8e8000c0d00000f207
|7,2=>0x29168000038008008c000189660003a03c000009ca40000121c4000e15c0207030000c062b8086f1e0480c4a522595c00012880c0035358d00000291ac00290480050000000402010f11c3e1e000180014000508410000041264030762009008700d0d1f8000c5c03004380d0e0043882
|8,0=>0xfaa8b71582bec3ac65827608ab36a61893b812d1c6ec39a604297b0ba5454f38381a05a4c2e5c900888be0343aacdec0c36287dbe1f0e50e32d20c359dceb8923a1e9809472521e334e9e0b243d99e2f3b41b9f452312bdd3202619dc13548bfe94adb3cae66d1aa3604cd94c438c2ac76c0da8135b2f6853f5734cb69c93a8e2d4338330382894119342e5f8a2875a
|8,1=>0x321d8a8684c1bd10280e90d1e4d81192480f2f1f696156aa2ea419309991eef141692e74381b131184c262acea5a89843234d95697228fc953c010e4252ab77c515fb4e03498ccc960260e52a90b047c3d2c26148989a074a48f72b7128dd49265e8142b5009c5f751a51e23249292c983ad30fe8f5c1dd38fe073ca620835308a693a0d4030a08bb6c791a2e995970a
|8,2=>0x12e98479c4a44f
|9,0=>0x262c8f54c271314947b2adc9cb1d1abf3ea25b1428f9e296b1084e2754d486ada6ba97b6a7e36c98dcba27536bd7a0e97a3bd59492b5b2130c752cbe7336a6c19eab1b2d66bb5cb5262609f7b56d4ea06d55d2f32
|10,0=>0x8a4f628a5795451ea5b15be708d
|11,0=>0x8f
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 51 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_222 9 roots_222 ops++addP pm 1 dom_214 8 roots_214 ops++addP pm 2 dom_95 9 roots_95 ops++addP pm 3 dom_159 9 roots_159 ops++addP pm 4 dom_157 8 roots_157 ops++addP pm 5 dom_91 8 roots_91 ops++addP pm 6 dom_215 9 roots_215 ops++addP pm 7 dzo_141_2 5 roots_141 ops++addP pm 8 dzo_75_4 5 roots_75 ops++addP pm 9 dom_141 5 roots_141 ops++addP pm 10 dom_151 6 roots_151 ops++addP pm 11 dom_75 5 roots_75 ops++addP pm 12 dom_207 8 roots_207 ops++addP pm 13 dom_219 9 roots_219 ops++addP pm 14 dom_203 7 roots_203 ops++addP pm 15 dom_221 9 roots_221 ops++addP pm 16 dom_206 5 roots_206 ops++addP pm 17 dzo_203_4 6 roots_203 ops++addP pm 18 dom_156 5 roots_156 ops++addP pm 19 dom_158 6 roots_158 ops++addP pm 20 dom_94 6 roots_94 ops++addP pm 21 dom_87 6 roots_87 ops++addP pm 22 dom_199 5 roots_199 ops++addP pm 23 dom_149 5 roots_149 ops++addP pm 24 dom_155 7 roots_155 ops++addP pm 25 dom_205 7 roots_205 ops++addP pm 26 dom_201 5 roots_201 ops++addP pm 27 dzo_205_2 6 roots_205 ops++addP pm 28 dom_86 5 roots_86 ops++addP pm 29 dom_202 4 roots_202 ops++addP pm 30 dom_137 4 roots_137 ops++addP pm 31 dom_154 4 roots_154 ops++addP pm 32 dom_195 4 roots_195 ops++addP pm 33 dzo_217_4 6 roots_217 ops++addP pm 34 dzo_201_4 5 roots_201 ops++addP pm 35 dom_197 4 roots_197 ops++addP pm 36 dom_73 4 roots_73 ops++addP pm 37 dom_213 6 roots_213 ops++addP pm 38 dom_90 5 roots_90 ops++addP pm 39 dzo_219_4 7 roots_219 ops++addP pm 40 dom_211 6 roots_211 ops++addP pm 41 dzo_217_2 6 roots_217 ops++addP pm 42 dom_85 4 roots_85 ops++addP pm 43 dom_93 7 roots_93 ops++addP pm 44 dom_218 6 roots_218 ops++addP pm 45 dzo_221_2 7 roots_221 ops++addP pm 46 dom_92 4 roots_92 ops++addP pm 47 dom_217 6 roots_217 ops++addP pm 48 dom_204 4 roots_204 ops++addP pm 49 dom_220 6 roots_220 ops++addP pm 50 dzo_201_2 5 roots_201 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_223 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_141_2_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_75_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_203_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_205_2_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_217_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_201_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_zo_219_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_zo_217_2_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_zo_221_2_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_zo_201_2_137 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_222 9 s (0,roots_222.map (·&&&dom_222)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_223 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_222 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_223==dom_223)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_223 gM v ys):RunD true dom_223 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_223 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 27 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 27 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 129 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 129 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 358 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 102 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 358 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 262 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 6 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 262 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 75 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 75 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 12 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_223 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_247:Lower true dom_247 roots_247 goal_247 12:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,64,65)] (by decide +kernel) lowS_246
def dzo_249_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_249_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c0c0c0c0c0c0c0c0c0c0c0c0c0c0800
def gsh_249_2:=0x303030303030303030303030303030203030303030303030303030303030200
theorem lowS_zo_249_2_137:Lower true dzo_249_2 roots_249 gzo_249_2 7:=lower_iso_b (d1:=dom_249) (r1:=roots_249) (T1:=gsh_249_2) [(dom_249,2)] (by decide +kernel) (lower_slice_b (T:=gsh_249_2) [(0x303000003030000030300000303000003030000030300000303000003030000,0,16),(0x303030300000000030303030000000003030303000000000303030300000000,0,32),(0x303030303030303000000000000000003030303030303030000000000000000,0,64)] (by decide +kernel) lowS_137)
def dzo_250_1:=0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def gzo_250_1:=0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a080a080a00
def gsh_250_1:=0x505050505050505050505050505050505050505050505050505050405040500
theorem lowS_zo_250_1_50:Lower true dzo_250_1 roots_250 gzo_250_1 7:=lower_iso_b (d1:=dom_250) (r1:=roots_250) (T1:=gsh_250_1) [(dom_250,1)] (by decide +kernel) (lower_slice_b (T:=gsh_250_1) [(0x500050005000500050005000500050005000500050005000500050005000500,0,8),(0x505050505050505000000000000000005050505050505050000000000000000,0,64),(0x505050505050505050505050505050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_50)
def dzo_233_2:=0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c
def gzo_233_2:=0xc0c00000c0c00000c0c00000c0800000c0c00000c0c00000c0c00000800
def gsh_233_2:=0x30300000303000003030000030200000303000003030000030300000200
theorem lowS_zo_233_2_137:Lower true dzo_233_2 roots_233 gzo_233_2 6:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_2) [(dom_233,2)] (by decide +kernel) (lower_slice_b (T:=gsh_233_2) [(0x30300000000000003030000000000000303000000000000030300000000,0,32),(0x30300000303000000000000000000000303000003030000000000000000,0,64)] (by decide +kernel) lowS_137)
def dzo_243_8:=0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00
def gzo_243_8:=0xf000f000f000f000f000f000f000f000f000f000f000f000f000e000e000a00
def gsh_243_8:=0xf000f000f000f000f000f000f000f000f000f000f000f000f000e000e000a
theorem lowS_zo_243_8_50:Lower true dzo_243_8 roots_243 gzo_243_8 7:=lower_iso_b (d1:=dom_243) (r1:=roots_243) (T1:=gsh_243_8) [(dom_243,8)] (by decide +kernel) (lower_slice_b (T:=gsh_243_8) [(0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a,0,1),(0xf000f000f000f0000000000000000000f000f000f000f0000000000000000,0,64),(0xf000f000f000f000f000f000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_50)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(16,18),(16,48),(16,80),(16,144),(17,19),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,56),(24,88),(24,152),(32,34),(32,48),(32,96),(32,160),(33,35),(33,41),(33,49),(33,97),(33,161),(40,41),(40,42),(40,56),(40,104),(40,168),(64,65),(64,66),(64,72),(64,80),(64,96),(128,129),(128,136),(128,144),(128,160),(130,131),(130,138),(130,146),(130,162),(130,194),(192,193),(192,194),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|8=>2
|9=>13
|10=>4
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x9e9a05b099
|9,0=>0x9bd43961f878c095a70a514c14c4824366a3649f3163b30ef02d3af175c101f29
|10,0=>0x96f85527d9411753e1f9
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x303030003030300030303000303030003030300030303000303030003030300505040405050404050504040505040405050404050504040505040405050404f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0ef0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0cf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cf0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f00f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000000f0f0c0c000000000f0f0c0c000000000f0f0c0c000000000f0f0c0cf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|0,1=>0xf0f0f0f0f0f0c0c0f0f0f0f0f0f0c0c0f0f0f0f0f0f0c0c0f0f0f0f0f0f0c0ce0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0000f0f00000a0a00000f0f00000a0a00000f0f00000a0a00000f0f00000a0af0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0000f0f00000c0c00000f0f00000c0c00000f0f00000c0c00000f0f00000c0cf0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0af0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c00000000f0c0f0c000000000f0c0f0c000000000f0c0f0c000000000f0c0f0cf0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f00
|_,_=>0
def sP:Nat→Nat
|0=>0x5a4c520c205250628c20c24c520c204d4c5b90205a8c520c20498a41d820626a629020498a41d0209a4c520c20498a41c420498a41bc20498a41b8204b4c520c20625062906102d4828c20398a418820
|1=>0x24c520c2049a4520c204a0c520c204c0c520c20
|_=>0
def sO:Nat→Nat→Nat
|8,0=>0x87008
|9,0=>0x7086886085885084884083883082882081880f9
|10,0=>0x908888808788
|11,0=>0x987
|_,_=>0
def wAt:=mkWire dB 25 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2153113154994913114a131130d20d32549133248d48d30d32a49158d4994ca21581331540f31140d31148d3114994913114954a2311
|_=>0
def oO:Nat→Nat→Nat
|8,0=>0xcc03
|9,0=>0x1e2709a26096250922408e2308a220862
|10,0=>0x8c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0x2033bf804efd813bf600e7c61bdf09befc21b9f060efc103ff013efc043ff00aefc01b9f004f7c007bf000ffc003bf000e7c00000
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>0x64
|9,0=>0x24194c32dd2824ed
|10,0=>0x891e5
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 22 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_187 10 roots_187 ops++addP pm 1 dom_123 10 roots_123 ops++addP pm 2 dom_250 9 roots_250 ops++addP pm 3 dom_242 8 roots_242 ops++addP pm 4 dom_243 9 roots_243 ops++addP pm 5 dzo_249_2 7 roots_249 ops++addP pm 6 dom_203 7 roots_203 ops++addP pm 7 dom_235 9 roots_235 ops++addP pm 8 dom_249 9 roots_249 ops++addP pm 9 dom_219 9 roots_219 ops++addP pm 10 dom_233 6 roots_233 ops++addP pm 11 dzo_250_1 7 roots_250 ops++addP pm 12 dzo_201_2 5 roots_201 ops++addP pm 13 dzo_217_2 6 roots_217 ops++addP pm 14 dom_201 5 roots_201 ops++addP pm 15 dzo_233_2 6 roots_233 ops++addP pm 16 dom_217 6 roots_217 ops++addP pm 17 dom_218 6 roots_218 ops++addP pm 18 dom_234 6 roots_234 ops++addP pm 19 dzo_243_8 7 roots_243 ops++addP pm 20 dom_227 6 roots_227 ops++addP pm 21 dom_241 6 roots_241 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_249_2_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_250_1_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_201_2_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_217_2_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_233_2_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_243_8_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_241 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_187 10 s (0,roots_187.map (·&&&dom_187)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_187 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 13 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 13 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 4 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 4 0 = true)
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
def isoMvS_191:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_191:Lower true dom_191 roots_191 goal_191 12:=lower_iso_b isoMvS_191 (by decide +kernel) lowS_127
def isoMvS_239:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_239:Lower true dom_239 roots_239 goal_239 12:=lower_iso_b isoMvS_239 (by decide +kernel) lowS_223
def isoMvS_253:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_251
def isoMvS_254:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_247
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,28),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,18),(16,20),(16,48),(16,80),(16,144),(17,19),(17,21),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,36),(32,48),(32,96),(32,160),(33,35),(33,37),(33,41),(33,49),(33,97),(33,161),(40,41),(40,42),(40,44),(40,56),(40,104),(40,168),(64,65),(64,66),(64,72),(64,80),(64,96),(68,69),(68,70),(68,76),(68,84),(68,100),(68,196),(128,129),(128,132),(128,136),(128,144),(128,160),(130,131),(130,134),(130,138),(130,146),(130,162),(130,194),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffffffffffffffff
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
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_191 12 roots_191 ops++addP pm 2 dom_253 12 roots_253 ops++addP pm 3 dom_251 12 roots_251 ops++addP pm 4 dom_247 12 roots_247 ops++addP pm 5 dom_239 12 roots_239 ops++addP pm 6 dom_223 12 roots_223 ops
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
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_223 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [4, 5] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.or, inputs := [0, 3] }, { op := GateOp.or, inputs := [10, 8] }, { op := GateOp.and, inputs := [9, 11] }, { op := GateOp.or, inputs := [6, 8] }, { op := GateOp.and, inputs := [1, 13] }, { op := GateOp.or, inputs := [7, 8] }, { op := GateOp.and, inputs := [2, 15] }, { op := GateOp.and, inputs := [0, 3] }, { op := GateOp.and, inputs := [5, 4] }, { op := GateOp.or, inputs := [12, 14] }, { op := GateOp.or, inputs := [19, 16] }, { op := GateOp.or, inputs := [20, 17] }, { op := GateOp.or, inputs := [21, 18] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_51960_aux

theorem PEqualNP.Outside.L_meta_51960 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_51960_aux.main
