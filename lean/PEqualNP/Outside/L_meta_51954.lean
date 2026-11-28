import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_51954_aux
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

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xeeeeeeeeeeeeeeeeaa00aa00aa00aa00eeeeeeeeeeeeeeeeaa00aa00aa00aa00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfafafafafafafafaaa00aa00aa00aa00fafafafafafafafaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfefefefefefefefeaa00aa00aa00aa00fefefefefefefefeaa00aa00aa00aa00
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

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffaaaaffffaaaaaa00aa00aa00aa00ffffaaaaffffaaaaaa00aa00aa00aa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffeeeeffffeeeeeeccaa00eeccaa00ffffeeeeffffeeeeeeccaa00eeccaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffafafffffafafaf0aa00faf0aa00fffffafafffffafafaf0aa00faf0aa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffefefffffefefefcaa00fefcaa00fffffefefffffefefefcaa00fefcaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_97 : Nat := 0x3000000030000000300000003
def goal_97 : Nat := 0xffffffffaaaaaaaaaaaaaaaa00000000ffffffffaaaaaaaaaaaaaaaa00000000
def roots_97 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_98 : Nat := 0x5000000050000000500000005
def goal_98 : Nat := 0xffffffffcccccccccccccccc00000000ffffffffcccccccccccccccc00000000
def roots_98 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xffffffffeeeeeeeeeeeeeeee00000000ffffffffeeeeeeeeeeeeeeee00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfffffffffafafafaaaaaaaaa00000000fffffffffafafafaaaaaaaaa00000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfffffffffcfcfcfccccccccc00000000fffffffffcfcfcfccccccccc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfffffffffefefefeeeeeeeee00000000fffffffffefefefeeeeeeeee00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffaaaaaaaaffaaffaaaa00aa00ffffffffaaaaaaaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffccccccccffccffcc00000000ffffffffccccccccffccffcc00000000
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffeeeeeeeeffeeffeeaa00aa00ffffffffeeeeeeeeffeeffeeaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfffffffff0f0f0f0ff00ff0000000000fffffffff0f0f0f0ff00ff0000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffffffffafafafaffaaffaaaa00aa00fffffffffafafafaffaaffaaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffffffffcfcfcfcffccffcc00000000fffffffffcfcfcfcffccffcc00000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffffffffefefefeffeeffeeaa00aa00fffffffffefefefeffeeffeeaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffffffffffaaaaaaaaaaaa00000000ffffffffffffaaaaaaaaaaaa00000000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffffffcccccccccccccccc0000ffffffffffffcccccccccccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffffffeeeeeeeeeeeecccc0000ffffffffffffeeeeeeeeeeeecccc0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffffffffffff0f0f0f00000f0f00000fffffffffffff0f0f0f00000f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffffffafafafaaaaaf0f00000fffffffffffffafafafaaaaaf0f00000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffffffcfcfcfcccccfcfc0000fffffffffffffcfcfcfcccccfcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffffffefefefeeeeefcfc0000fffffffffffffefefefeeeeefcfc0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffffffffff0000ff00ff0000000000ffffffffffff0000ff00ff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffffaaaaffaaffaaaa00aa00ffffffffffffaaaaffaaffaaaa00aa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffffccccffccffcccccc0000ffffffffffffccccffccffcccccc0000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffffeeeeffeeffeeeeccaa00ffffffffffffeeeeffeeffeeeeccaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffffffffff0f0fff0ff00f0f00000fffffffffffff0f0fff0ff00f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffffafafffaffaafaf0aa00fffffffffffffafafffaffaafaf0aa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffffcfcfffcffccfcfc0000fffffffffffffcfcfffcffccfcfc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffffefefffeffeefefcaa00fffffffffffffefefffeffeefefcaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

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

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffff0fff0fffffffffff0fff0ffccffcc00000000ffccffcc00000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffafffafffffffffffafffaffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffffaaaaffffffffffffaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffaaaaffffffffffffaaaaeeeeeeeecccc0000eeeeeeeecccc0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

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

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffff0fffffffffffffff0fffcffccfcfc0000fffcffccfcfc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffafffffffffffffffafffeffeefefcaa00fffeffeefefcaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaaaaaaaaaaaaaaaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeffaaffaaffaaffaaeeeeeeeeeeeeeeeeaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0f0f0f0f0f0f0f0f00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffafffafffafffafffafafafafafafafafaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffcfffcfffcfffcfff0fff0fff0fff0fcfcfcfcfcfcfcfc0000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffefffafffafffafffafefefefefefefefeaa00aa00aa00aa00
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

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffafafffffafafffffafafffffafafffffafafffffafaf0f00000f0f00000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfffff0f0fffff0f0fffffcfcfffffcfcfcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefffffafafffffafafffffefefffffefefcfc0000fcfc0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffff00ffffff00ffffff00ffffff00ffff0000ffff00000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffffaaaaffffaaaaaa00aa00aa00aa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffffff00ffffff00ffffccccffffcccccccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffffaaffffffaaffffeeeeffffeeeeeeccaa00eeccaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fffff0f0fffff0f0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffafffffffafffffffafffffffafffffafafffffafafaf0aa00faf0aa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcfffffff0fffffff0fffffcfcfffffcfcfcfc0000fcfc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffffffafffffffafffffefefffffefefefcaa00fefcaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeffffffffaaaaaaaaffffffffeeeeeeeeeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffafafafafffffffffafafafafffffffffafafafaaaaaaaaa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfffffffff0f0f0f0fffffffffcfcfcfccccccccc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefefffffffffafafafafffffffffefefefeeeeeeeee00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffffffffaaaaaaaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffff00ff00ffffffffccccccccffccffcc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffffaaffaaffffffffeeeeeeeeffeeffeeaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fffffffff0f0f0f0ff00ff0000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffafffffffffffafffafffffffffafafafaffaaffaaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcfffffffffff0fff0fffffffffcfcfcfcffccffcc00000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffffffffffafffafffffffffefefefeffeeffeeaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaaaaaaaaa00000000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffccccffffffffffff0000ffffffffffffcccccccccccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffffffffffaaaaffffffffffffeeeeeeeeeeeecccc0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fffffffffffff0f0f0f00000f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffafafffffffffffffafafffffffffffffafafafaaaaaf0f00000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffffffffff0f0fffffffffffffcfcfcfcccccfcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffffffffffafafffffffffffffefefefeeeeefcfc0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffff00ffffffffffffff00ffffffffffff0000ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffffffffffaaffffffffffffaaaaffaaffaaaa00aa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffffffffff00ffffffffffffccccffccffcccccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffffffaaffffffffffffeeeeffeeffeeeeccaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffff0fffffffffffffff0fffffffffffff0f0fff0ff00f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffffffffffafffffffffffffafafffaffaafaf0aa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffffffffff0fffffffffffffcfcfffcffccfcfc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffffffffffafffffffffffffefefffeffeefefcaa00
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
def isoMvS_97:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_97:Lower true dom_97 roots_97 goal_97 4:=lower_iso_b isoMvS_97 (by decide +kernel) lowS_41
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
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 4:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_51
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 4:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_51
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_43
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_43
def isoMvS_89:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 4:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_51
def isoMvS_99:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_86
def isoMvS_101:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 5:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_43
def isoMvS_102:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 5:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_43
def isoMvS_105:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_86
def isoMvS_106:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_43
def isoMvS_108:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 4:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_51
def isoMvS_113:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_43
def isoMvS_114:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_86
def isoMvS_116:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_43
def isoMvS_120:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 4:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_51
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_43
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_43
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 4:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_51
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_43
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 4:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_51
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_43
def isoMvS_195:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 4:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_51
def isoMvS_198:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 4:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_51
def isoMvS_201:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_43
def isoMvS_204:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 4:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_51
def isoMvS_210:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_43
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_86
def isoMvS_216:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 4:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_51
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 5:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_86
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
|0=>0x1f41c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xca
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_43 5 roots_43 ops++addP pm 1 dom_51 4 roots_51 ops++addP pm 2 dzo_43_16 5 roots_43 ops++addP pm 3 dom_58 4 roots_58 ops++addP pm 4 dom_41 4 roots_41 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_43_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_58 _ g hchk
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
theorem lowS_79:Lower true dom_79 roots_79 goal_79 5:=lower_slice_b [(0xcccc000000000000cccc,64,66)] (by decide +kernel) lowS_77
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_slice_b [(0xaa00aa0000000000aa00aa,64,65)] (by decide +kernel) lowS_86
namespace S_107
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,34),(2,66),(3,11),(3,35),(3,67),(8,9),(8,40),(10,11),(10,42),(10,74),(32,33),(32,34),(32,40),(32,96),(64,65),(64,66),(64,96),(72,73),(72,74),(72,104)]
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
addP pm 0 dom_106 5 roots_106 ops++addP pm 1 dom_105 5 roots_105 ops++addP pm 2 dom_99 5 roots_99 ops++addP pm 3 dom_43 5 roots_43 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_107 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_43 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_106 5 s (0,roots_106.map (·&&&dom_106)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_107 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_106 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
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
def dzo_105_4:=0x3030000030300000303000003030
def gzo_105_4:=0x3030000030300000302000002000
def gsh_105_4:=0x303000003030000030200000200
theorem lowS_zo_105_4_41:Lower true dzo_105_4 roots_105 gzo_105_4 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_4) [(dom_105,4)] (by decide +kernel) (lower_slice_b (T:=gsh_105_4) [(0x303000003030000000000000000,0,64)] (by decide +kernel) lowS_41)
namespace S_109
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(4,68),(5,13),(5,37),(5,69),(8,9),(8,40),(12,13),(12,44),(12,76),(32,33),(32,40),(32,96),(36,37),(36,44),(36,100),(64,65),(64,68),(64,96),(72,73),(72,76),(72,104)]
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
|4,0=>0xee8bc
|5,0=>0xc47e9
|6,0=>0xf22e7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3333000022220000333300002222cc000000cc000000cc000000cc03333000000000000333300000000c0c00000c0c00000c0c00000c0c222200002222000022220000222200cc00000088000000cc0000008b333000033330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x95a1a5684688
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
addP pm 0 dom_105 5 roots_105 ops++addP pm 1 dom_108 4 roots_108 ops++addP pm 2 dzo_105_4 5 roots_105 ops++addP pm 3 dom_101 5 roots_101 ops++addP pm 4 dom_41 4 roots_41 ops++addP pm 5 dom_77 4 roots_77 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_109 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_105_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_77 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_105 5 s (0,roots_105.map (·&&&dom_105)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_109 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_105 h
def symsG:List (List (Nat×Nat)):=[[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
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
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_slice_b [(0x5050000050500000505000005050,64,68)] (by decide +kernel) lowS_106
namespace S_117
def pG:List (Nat×Nat):=[(1,33),(1,65),(4,20),(4,68),(5,21),(5,37),(5,69),(16,20),(16,80),(17,21),(17,49),(17,81),(32,33),(32,96),(36,37),(36,52),(36,100),(48,49),(48,52),(48,112),(64,65),(64,68),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_117.map (·&&&dom_117)
def gM:=goal_117&&&dom_117
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x10e0e
|4,0=>0x369e525f0209c1a06d94
|5,0=>0x488c63fe4436fa42d60b2818a26847189bb1162e0c5a0095b1
|6,0=>0x96c7475d74298130ebe4
|7,0=>0x96c74
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc00cc00c000c000cc00cc00c000c3300330033003300330033000000008c008c008c008c00880088008800880001100000011000000000000000044004400000044004400440000000030003000300030003000200030002cc00cc00cc00cc00cc000000cc000330022003300220000000000000000cc00cc0000000000cc00cc000000033003200330032003000300030003088008800880088008800880088008b30033003300330000000000000000cc00cc00cc008800cc00cc0000000330000003300000033000000330000c000c000c000c000c000c000c000c330033003300330022002200220022
|0,1=>0x3200320032003200320032003200320c000c000c000c00000000000000000000000000000003300330030003000000000cc00cc000000000088008b3003300300030000000000000000044004400440044004000400040004000033000000330000000000000000cc00cc00cc00cc00cc00cc00c000c000033000000330000003000000030
|_,_=>0
def sP:Nat→Nat
|0=>0x1c41290e20948716025238e209487104a4bd8e209482080b521c4129287104b321d21292513882521c25811ee104a43882d290e20948c3882b21c45510e909507118a418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682ced9ab2f654a918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 25 118 0x3fffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x9539109201f291790705391391092
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x524100002200110100
|6,0=>0x918171
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0x3ff7adf585230a080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x580320410
|6,0=>0x6a79
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_116 5 roots_116 ops++addP pm 1 dom_84 4 roots_84 ops++addP pm 2 dom_101 5 roots_101 ops++addP pm 3 dom_97 4 roots_97 ops++addP pm 4 dom_113 5 roots_113 ops++addP pm 5 dom_85 5 roots_85 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_117 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_85 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_116 5 s (0,roots_116.map (·&&&dom_116)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_117 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_116 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_117==dom_117)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_117 gM v ys):RunD true dom_117 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_117 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_117 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_117 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_117 roots_117 goal_117 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_117
theorem lowS_117:Lower true dom_117 roots_117 goal_117 8:=S_117.noCircuit
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_slice_b [(0xc0c00000c0c000000000000000000000c0c00000c0c,32,34)] (by decide +kernel) lowS_169
theorem lowS_179:Lower true dom_179 roots_179 goal_179 6:=lower_slice_b [(0xc000c000c000c0000000000000000000c000c000c000c,16,18)] (by decide +kernel) lowS_177
theorem lowS_213:Lower true dom_213 roots_213 goal_213 6:=lower_slice_b [(0x220022000000000022002200000000002200220000000000220022,64,65)] (by decide +kernel) lowS_212
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_slice_b [(0x30300000303000000000000000000000303000003030000000000000000,1,65)] (by decide +kernel) lowS_169
def isoMvS_62:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 5:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_55
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 7:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_59
def isoMvS_93:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 7:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_59
def isoMvS_103:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_87
def isoMvS_115:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_107
def isoMvS_118:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_107
def isoMvS_121:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 7:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_109
def isoMvS_122:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_109
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 7:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_59
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_110
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 7:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_59
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 8:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_117
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 6:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_110
def isoMvS_167:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_110
def isoMvS_173:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_171
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_110
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 8:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_117
def isoMvS_182:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 6:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_179
def isoMvS_185:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 8:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_171
def isoMvS_186:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 6:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_179
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 8:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_117
def isoMvS_203:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 7:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_59
def isoMvS_205:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 6:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_179
def isoMvS_206:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 5:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_55
def isoMvS_211:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 6:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_179
def isoMvS_214:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 7:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_107
def isoMvS_217:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 6:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_179
def isoMvS_218:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 7:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_59
def isoMvS_220:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 7:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_109
def isoMvS_227:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 7:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_107
def isoMvS_229:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 6:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_213
def isoMvS_230:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 6:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_179
def isoMvS_234:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 8:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_117
def isoMvS_236:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 6:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_179
def isoMvS_241:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 6:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_213
def isoMvS_242:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 6:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_213
def isoMvS_244:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 6:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_213
def isoMvS_248:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 6:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_179
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xf0f0f0f0f0f0f0f0,16,20)] (by decide +kernel) lowS_59
theorem lowS_95:Lower true dom_95 roots_95 goal_95 8:=lower_slice_b [(0xcccccccc00000000cccccccc,16,18)] (by decide +kernel) lowS_93
def dzo_43_4:=0xf0f00000f0f0
def gzo_43_4:=0xf0e00000a000
def gsh_43_4:=0xf0e00000a00
theorem lowS_zo_43_4_43:Lower true dzo_43_4 roots_43 gzo_43_4 5:=lower_iso_b (d1:=dom_43) (r1:=roots_43) (T1:=gsh_43_4) [(dom_43,4)] (by decide +kernel) (lower_slice_b (T:=gsh_43_4) [] (by decide +kernel) lowS_43)
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0f00000f0e00000a000
def gsh_107_4:=0xf0f00000f0f00000f0e00000a00
theorem lowS_zo_107_4_43:Lower true dzo_107_4 roots_107 gzo_107_4 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_43)
namespace S_111
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,34),(2,66),(3,11),(3,35),(3,67),(4,68),(5,13),(5,37),(5,69),(6,38),(6,70),(7,15),(7,39),(7,71),(8,9),(8,40),(10,11),(10,42),(10,74),(12,13),(12,44),(12,76),(14,15),(14,46),(14,78),(32,33),(32,34),(32,40),(32,96),(36,37),(36,38),(36,44),(36,100),(64,65),(64,66),(64,68),(64,96),(72,73),(72,74),(72,76),(72,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_111.map (·&&&dom_111)
def gM:=goal_111&&&dom_111
def NN:Nat→Nat
|3=>1
|4=>30
|5=>85
|6=>62
|7=>14
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xf9aad
|4,0=>0xfd236ef6d2ec51be1e69dca90da547c1f3094cfc907688bb2d865bf80c2678c926a8db6933d580cd4fb424f0094df704da924b0273be6237fa333c3533851245d2242a118a171256d10fa9
|5,0=>0xfdd93fc030fad72f2e5bf29fcf070feed88ead30e8524e7fece5cc4e537bdd4cfd9fdad94cad7a8ed626dd5bc7d3b64d3191cee84ca8f0c809ec4de8c236ec0c74b8e0eb6582b5c19b48a5b4039adb73a9247a9228a7cafa3616a1a9994ea39035a88207867de8638d84fc1831d681e5280ef37cc907a250712026e9b06c5b2684a76813764dc062a81613df600075ef625c73659815557485427c536a250c284b120480cb43b95413a1395f93840233c6032c5b2b1f02a9bf2985a29634231e222bad1a6d713d440d7270a79906bce0610400faa
|6,0=>0xf973cf819ff6bcfec403eb955ea35de7b0be5fbcde69cdda15dc12bdbf7cdadc9da2ddd9ca8d5974cf0bdc4822c1894c0515bdcc3b9e9db3306afe01ad353aa47e9cdbf95961956c192ee78e3978ccc28aac885f7f82a3d819eb8154a7f19977d6f701856fe7569e4c5edaa5baa35a9e5585fc57a5c52dc5522df4b56048e1a4482e3e6bb3a2d12621021fe71c49e1bc7c1658514873147710fe04
|7,0=>0xe3277ba452932268097a7e80571b6770f98642a662cf15cd9b520c32c61c29dca0d0bf
|8,0=>0x4f37e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff000000ff0000ff000fff00000faf000000ff000000aaffff0000aaaa0000ffff0000aaaaffff0000ff000000ffaa0000ff00cccc0000cccc0000cccc0000ccccbbbb0000abab0000bbbb0000aaaaffff000000000000ffff0000000000000000afaf000000000000aaaaffff0000ffff0000000000000000ff000000ff000000ff000000ff00ffff0000cccc0000eeee0000ccccaaaa0000aaaa0000aaaa0000aaaaffff0000ffff0000ffff00000000ffff0000aaaa0000ff000000aa00f0f00000f0f00000f0f00000f0f0eeee0000eeee0000eeee0000eeee
|0,1=>0x111100000000000011110000000000000000fefe000000000000fefeffff0000ffff0000ffff0000ff00ffff0000ff000000ffff0000ff0013130000030300001111000000001111000001010000111100000000ffff0000cccc0000ffcc0000ccccffff0000afaf0000ffff0000aaaa00000000ffff000000000000aaaaffff0000aaaa0000ffaa0000aaaaffff0000fefe000000000000000003330000030300000033000000003333000023230000333300002222eeee0000eeee0000eeee00000000ffff0000ffff0000aaaa0000aaaaffff0000ffff0000ff000000ff00
|0,2=>0x333300003333000011110000000000ff000000ff000000ff000000aa0000000000000000ffff0000aaaaf0ff0000f0fa0000f0ff0000f0fa00ff000000aa000000ff000000aa00ff00000000000000ff0000000000000000ffff000000000000ff005f5f00000f0f0000555500000000ffff0000ffff000000ff00000000333300003333000033330000330033330000333300003333000022225555000055550000555500000000ffff000000000000ff0000000000ffff0000ffff0000ffff0000aaaaffff00000f0f0000ffff000000005555000054540000555500005454
|0,3=>0xaaaa0000aaaa0000ffff0000aaaaf1f10000f0f00000f1f10000f0f000000000aaaa000000aa0000aaaa5555000000000000555500000000ffff0000ffff000000ff000000aaffff0000fefe0000ffff0000fefe5555000055550000555500005500ffff000000000000aaaa000000003333000003030000333300000000ffff0000fafa0000ffff0000fafaffff0000ffff0000ff0000000000afaf0000afaf0000aaaa0000aaaa5555000055550000550000005500aaaa0000aaaa0000aaaa0000aa000f0f00000f0f0000000000000000000000000000000000ff000000aa
|0,4=>0xfff00000f0f000000ff0000000011110000101000001111000010103333000033330000003300000000000000000000000000ff00000000bbbb0000bbbb0000bbbb0000aaaaefef0000efef0000eeee0000eeee3333000033330000333300000000ffff0000f0f00000ffff0000f0f0ffff0000ffff0000555500000000bbbb0000aaaa0000bbbb0000aaaa00aa000000aa000000ff000000aa0000000000000000ffff0000000055550000050500005555000000000000000000000000ffff0000ff00fefe0000fefe0000fefe0000fefe1111000011110000111100000000
|0,5=>0xfafa0000fafa0000fafa0000fafa0000000000000000ff000000ff0000000000000000005555000000005555000050500000555500005050f0ff0000f0f00000f0ff0000f0f0ff000000ff000000ffff0000ff00f5f50000f0f00000f5f50000f0f000ff000000ff000000ff00000000ffff0000ffff0000eeee0000eeeeffff0000eeee0000ffff0000eeeeffff0000ffff0000ffaa0000ffaa00ff000000ee000000ff000000ee
|_,_=>0
def sP:Nat→Nat
|0=>0x421800712180200e241011644182022c206087cf073a5808b0e70b01161c486086c3890c10d0706643010860486001c6860248389200401706583011624300085448608503890c1098712180922234190020008b083c38916107071a3008b0e2430a081c48600203830c042840608080
|1=>0xe7518116103ad12180800e711811610389582c22b0e0458454a43890c2c2280e3449002003890c049040e248010044490022c22712400844c1c486021128706248010010490022c2241218085081c4860200b8706191811610199200420904040074424801000cb10022c686007838d
|2=>0x22de87064008b08a46a10c2c2074218584781c4811611d877424300081c486022dc87061808b08e1b0d121800712182370ed848b08ac38932180840e24835022c20d12185b40e2480100cc38920045b20e34486001d8891611587622408b08c03890c0422f0e24b06022c389022c22e
|3=>0xe2480116123890c040460e243000878389022c2450e3620602003a112180040e24300681c48616121871218584101e10920045844424301001c4868210f87064118116106830c045911218084801c4860211307120808b081df890c04007442480116104867c002071a1808b701c490
|4=>0x21038d121a0800e24080094039812185840e3418602003890c2c24f0e24300093838920045842e24301093438116126290e24301961038d120402b0e24b10022c3890d280040e0c49002124a112182370e0c486020088d124008b2234190022c203200458479206890c003c8122c22b
|5=>0x3a2430116103890c04584a81c486034c0040e36206022c2071218084921c48616d020712180040ec51090c045840f4848602002071218584541d8b612185840efc486022c207121808b093038920040040e26890022c207382430b081d88918045840e2480116e438920045916624c90
|6=>0x12180800f58486022c2071204584561c4c40c040040e0c48602124871241181161038d121808b221d0890c2c2071a0c301161039c902430b081c186022c23c0e2430116123871a2408b08ac3892004584521c1890c045910908486022c207903448616103890c04584701c486aa2c207
|7=>0xe243011612c87121a080081c1892004584121808b08a43890c2c2580e2430100443890c045844e1c486ae2c2075a2430116103831218080081c486022c2240e34490022c207124008b08f03892004591080c4900c045849024300081c486020021f0e248011612607121808b085c38d
|8=>0xe2430100103c812185840e2435b16103890c04591081c486022c22a0e26d011610389881808b081ce090c045840e34486022c207121808b08f03890c2c20762d86890c2c207124008b08a83890c8c08b081c490022c2330e74490022c2071a2430b081d8890c2c23c0ec4e092004584
|9=>0x90c045840e248011610389201808b081c1890c04584
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x4aa8905116a219440a87c50eea1c9436a86850c6a17942ca854509ea129422a8405076a0d9418a82c504ea08940ea8185026a039404a8045
|5,0=>0x422c82d902b1ff63f2c7cd8f6b1e763c2c76d8eb29d06394c7118df31b86364c6b18d331a06334c6518c731886304c5f18bb317062d4c5918af315862a4c5318a3a9416276c4d5897b1296246c47588bb1116216c41587fb0f961e6c3b5873b0e161b6c355867b0ca5188c2f985c30b26158c299850309a6
|5,1=>0x28f6512ca0d93eb27764e2c9ad932b25f64b2c94d926b2476482c8ed91ab22f6452c88d90eb2176
|6,0=>0x2183c297844f06de0a3c0d780ceffddfc3bf267d8cf95defb3d967a4ef319e2bbbe776eeec1dd4bba36738ee599c7bb887702eded9ba3b6e66ceed81dacbb527698cd15d9f3b377660eca5d913b1b7628ec35d833b0065f2ebc9d75bae475bccb6196932cb7588eaf5d5bb2b07552ea8d94e3a957
|7,0=>0x246b48678fef1e5a39b46d68ccf17de2cb4527896f111e1ebc376
|8,0=>0x4936
|_,_=>0
def wAt:=mkWire dB 92 112 0xffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x21e1611021e0611121d12011611121b021e1a0512118811121f12430c1d16110c1d20110c1d021e20131211020116111211062f161112111211121312051203130616111611021e0611121d1203161112401211121d1a40121f121d1244124212441a05422f121120131611021e1a1f0600121d081d16110c1d16111a40121d
|1=>0x2a9121b1a1f12111611121d0613121d0c1d12110c1d12130c1d081d121d161112051203161112430c1d1246081d161112111a1b1211121f1611062f121d12400c1d121112c5021e1211121d12051213781d12131a1b121112420c1d121d381f1219121112051244081d02f11213381d1219001d1611121f1211062f121d08c5
|2=>0xc1d0c1d121d161112050211081d121b0c1f121f121912111213021e1a0512110c1d121b12400c1d20130c1d12410c1d1211021e1213021e12191247081d020116110c1d121d12420c1d901312051611081d541d121b
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11001000000000000000000000000000000000000000000000000000000000000000000000000000000000
|5,0=>0x2312212110000002011e20000000001c20000000001a21821711520000001411311210001110001010000000000000000f10e10d10c10000000000a2000091000000000000000000081000000000000000062033000000000021000000000000
|5,1=>0x2b1000292000000000000000000000000000272000000261000251241
|6,0=>0x9b29929729529329128f28e18c28a28828628428228027e27c27a27827627427227116f26d26b26926720006526326125f25e15c25a25915815625425225114f24d24b24924720004524324123f23d23b23923723523323122f22d22c1
|7,0=>0xaa1a91a81a71a61a51a41a31a21a11a019f19e19d1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x1338098004a4024101080080002e6017100b80054402a001100081004000100007100380014c00a40051002800120008800400018000800020000f00018000800020000
|1=>0x80a820118a6a6464221210cdcc66a6237111b1880402ee6171309bf84dcc26c6134309010480022e611410810020000804037701b980dc406ce036301a980d4006200270
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x2080000000000000000000000000000000000000000
|5,0=>0x50040000004400000060111401451450800022800004c00000c81610000820806801400000004a94aa000006002000000000080000000060000005000000
|6,0=>0xf1566032fb922f3615f6842d3623228a61f224b2df01c896594b211b631e5db3fb8f9380fdb570c4efabd0d2e6746
|7,0=>0x9a7e25eb59f79f8df7df1
|8,0=>0x24
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 17 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_109 7 roots_109 ops++addP pm 1 dom_102 5 roots_102 ops++addP pm 2 dom_108 4 roots_108 ops++addP pm 3 dom_105 5 roots_105 ops++addP pm 4 dzo_43_4 5 roots_43 ops++addP pm 5 dom_103 6 roots_103 ops++addP pm 6 dom_107 7 roots_107 ops++addP pm 7 dzo_105_4 5 roots_105 ops++addP pm 8 dom_43 5 roots_43 ops++addP pm 9 dom_110 6 roots_110 ops++addP pm 10 dom_106 5 roots_106 ops++addP pm 11 dom_99 5 roots_99 ops++addP pm 12 dzo_107_4 6 roots_107 ops++addP pm 13 dom_79 5 roots_79 ops++addP pm 14 dom_75 4 roots_75 ops++addP pm 15 dom_77 4 roots_77 ops++addP pm 16 dom_41 4 roots_41 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_111 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_43_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_105_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_107_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_41 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_109 7 s (0,roots_109.map (·&&&dom_109)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_111 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_109 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_111 gM v ys):RunD true dom_111 gM v (ori ys):=h
def Z (s:Nat):=barP dom_111 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 30 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 30 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 85 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 85 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 62 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 62 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 14 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_111 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_119:Lower true dom_119 roots_119 goal_119 9:=lower_slice_b [(0xcc00cc00cc00cc00cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_117
def dzo_82_8:=0x50005000000000005000500
def gzo_82_8:=0x50004000000000004000000
def gsh_82_8:=0x500040000000000040000
theorem lowS_zo_82_8_82:Lower true dzo_82_8 roots_82 gzo_82_8 4:=lower_iso_b (d1:=dom_82) (r1:=roots_82) (T1:=gsh_82_8) [(dom_82,8)] (by decide +kernel) (lower_slice_b (T:=gsh_82_8) [] (by decide +kernel) lowS_82)
def dzo_41_16:=0x303000003030000
def gzo_41_16:=0x302000002000000
def gsh_41_16:=0x30200000200
theorem lowS_zo_41_16_41:Lower true dzo_41_16 roots_41 gzo_41_16 4:=lower_iso_b (d1:=dom_41) (r1:=roots_41) (T1:=gsh_41_16) [(dom_41,16)] (by decide +kernel) (lower_slice_b (T:=gsh_41_16) [] (by decide +kernel) lowS_41)
def dzo_107_16:=0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16:=0xf0f00000f0f00000f0e00000e0c0000
def gsh_107_16:=0xf0f00000f0f00000f0e00000e0c
theorem lowS_zo_107_16_41:Lower true dzo_107_16 roots_107 gzo_107_16 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_16) [(dom_107,16)] (by decide +kernel) (lower_slice_b (T:=gsh_107_16) [(0xc0c00000c0c00000c0c00000c0c,0,2),(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_114_8:=0x5000500050005000500050005000500
def gzo_114_8:=0x5000500050004000500050004000000
def gsh_114_8:=0x50005000500040005000500040000
theorem lowS_zo_114_8_82:Lower true dzo_114_8 roots_114 gzo_114_8 5:=lower_iso_b (d1:=dom_114) (r1:=roots_114) (T1:=gsh_114_8) [(dom_114,8)] (by decide +kernel) (lower_slice_b (T:=gsh_114_8) [(0x50005000000000005000500000000,0,32)] (by decide +kernel) lowS_82)
def dzo_115_8:=0xf000f000f000f000f000f000f000f00
def gzo_115_8:=0xf000f000f000e000f000f000e000a00
def gsh_115_8:=0xf000f000f000e000f000f000e000a
theorem lowS_zo_115_8_82:Lower true dzo_115_8 roots_115 gzo_115_8 6:=lower_iso_b (d1:=dom_115) (r1:=roots_115) (T1:=gsh_115_8) [(dom_115,8)] (by decide +kernel) (lower_slice_b (T:=gsh_115_8) [(0xa000a000a000a000a000a000a000a,0,1),(0xf000f00000000000f000f00000000,0,32)] (by decide +kernel) lowS_82)
def dzo_105_16:=0x3030000030300000303000003030000
def gzo_105_16:=0x3030000030300000302000002000000
def gsh_105_16:=0x303000003030000030200000200
theorem lowS_zo_105_16_41:Lower true dzo_105_16 roots_105 gzo_105_16 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_16) [(dom_105,16)] (by decide +kernel) (lower_slice_b (T:=gsh_105_16) [(0x303000003030000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_83_8:=0xf000f00000000000f000f00
def gzo_83_8:=0xf000e00000000000e000a00
def gsh_83_8:=0xf000e00000000000e000a
theorem lowS_zo_83_8_82:Lower true dzo_83_8 roots_83 gzo_83_8 5:=lower_iso_b (d1:=dom_83) (r1:=roots_83) (T1:=gsh_83_8) [(dom_83,8)] (by decide +kernel) (lower_slice_b (T:=gsh_83_8) [(0xa000a00000000000a000a,0,1)] (by decide +kernel) lowS_82)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,40),(10,11),(10,26),(10,42),(10,74),(16,18),(16,80),(17,19),(17,25),(17,49),(17,81),(24,25),(24,26),(24,56),(24,88),(32,33),(32,34),(32,40),(32,96),(48,49),(48,50),(48,56),(48,112),(64,65),(64,66),(64,80),(64,96),(72,73),(72,74),(72,88),(72,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|4=>7
|5=>18
|6=>46
|7=>36
|8=>12
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xfd0e2a94309ed0d6925d676bf2330f1c0f2
|5,0=>0xe0906d9236d47e2be3c9a8d18a1b5f7ffcc6fd6c6bec7505e3453b1446a943e2123c9f1b4531655306b8105d26
|6,0=>0xdce8fced96bed59b24d49fb729a51d98955968c08e53a896287c19d7a44878a1c7805976b717423b6849b61c7d61a7e579b654777543a9531e74f7394ea6b499174690846359412b3407ae38fcb387743543a349df2d0122c7372bd9d2ba2f28e90275e31bde30dede0bced0a52c08f6a02725
|7,0=>0xf5353c9061be9ccb2b7cad72f9fdb69aead861467b99d78e107284b6240e5d3245b4b159b0154e6c544c54710b42ad93f9493dc3639e853953139104389f02f8832a9472a039205631fafa1e7811d0481861b125040fa540cc95
|8,0=>0xf62e7c16e0a269a78ef06900d62b5b5f5a847c6832d0c1cf4b08cdd07721
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000f000a000f000f000e000af0f0f0f0c0c0c0c0f0f0f0f0c0c0c0ce0e0e0e0e0e0e0e0e0e0e0e00000000f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f0000f0f0f0f0f0f0f0f0f0c0f0c0e0c0e0cf0f0f0f0f0f0f0f0f000f000a000a00f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af000f000f000f000f000f000f000f00e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ef0f0f0f0f0f00000f0f0f0f0c0c0000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00f000f000a000a000f000f000a000af0f0f0f0f0f0f0f0000000000000000
|0,1=>0xf0f0f0f0f0f0f0f0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c1010101010101010101010100000000f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0ef000f000a000a000f000f000a000a005050505050500000505050504040000f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e5050505040404040505050504040404f0f0f0f0f0f00000f0f0f0f0f0f000050505050505050505050505000000000000f0f00000f0f00000c0c00000c0cf0f0f0f0f0f0f0f0e0e0e0e0e0e0e0ef0f00000f0f00000c0c00000c0c0000f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f0c0c0c0c0a0a0a0a08080808
|0,2=>0xf0f0000000000000f0f00000000000000000000f0f0f0f0e0e0e0ef0f0f0f030303030f0f0f0f02020202f0f0f0f0f0f0f0f0f000f000f000f00000000000000000000000000e0e0e0e3030303030303030303030302020202d0d0d0d0d0d0d0d0d0d0d0d0c0c0c0cc0c0c0c0f0f0f0f0c0c0c0c0e0e0e0ef0f0f0f0f0f0f0f0f0f00000f0f000000000000e0e0e0e000000000e0e0e0ef0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a3030303030303030303030300000000f0f0f0f0f0f0f0f000000000e0e0e0e000000000000000050505050404040400000000f0f0f0f000000000a0a0a0af0f0f0f0f0f0f0f000f000f000a000a
|0,3=>0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0af0f0f000f0f0f000f0f0f000f0f0f00f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c30303030303030303000300030003000000000000000000f000f000f000f00f0f0f0f0f000f000f0f0f0f0f000f0050505050505000005050505050500000000000000000000e0e0e0e0e0e0e0e0000000000000000f0f0f0f0c0c0c0cf0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c
|_,_=>0
def sP:Nat→Nat
|0=>0x2480c21ca18d0c01060c26806512860cc44a1920982ca18540010614200e28634200e44a1853174460cc58b0c20550042c614200744a1940d12860c24072c615300b28848308728635244a1854040c23c038a18d30b2892051071850040c2040
|1=>0xb2860c28c02ca1830a200744a18330b29b4830802ca1850e100b2830a000e44a1850802ca2030974460c25805df4460c201e2ca18508044b28650308b2860c274038b28614c01c2ca1830805ce1850805d11833022db0c25401d12861522ca
|2=>0x5d1b0308b2864829802ca1830ab0042c60c200b2860c2a802ca1a90c20192ca18330038b2860a400744a1835802ca1a80c200b9ca0c20402ca18332600b9460c25402c61530803912860a401e2ca1829002ca19209800744a1920c244a183098
|3=>0x7912ca1830801d12860c20312ca1830802cac060c200b2860c29002ec0c2bc02ca1940cc0801cb2864830802ca18309002e2ca1830802ca18d0c200e44a1833021cb28615200744a1850c02ca48308101764e18308064b28648202d2ca183080
|4=>0x801cbdca18308044b2860c25805ce1830802ca6c30802f50c2bc02cab050c200b2860c26002c61430af0172ec0c200e2ca1850802ca1830b600e2cad43080d0b28648308044b2860cc0972c60c2cc064b2861430802ca1940c200b286c83080
|5=>0x1830802f82860c200b2860c20342ca1830802ca1833020072ca1830805cb2860c200b2b50c20112ca183080d0b9ca1830805cb18330200b2830810112cab030872ca1850c07cb2860cc08044b28614308038b28648201e2ca18308038b2860cc
|6=>0xb2860c200b2861430802cab030802f72860c200be4a
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x1e5065414503d40a50154005
|5,0=>0x22188261f187661c186a619185e61654536135847610583b60d582f60a58236
|6,0=>0x6fddb876c5daa768dd9c7655d8e761dd8075ed57475b5d676581d597549d4b7511d3d74d9d2f74a1d22646dd147435d0673fdcf873c5ceb6391cdd735d8d0732d4c472f5cb672bdca87285c9a725188e6
|7,0=>0xafa2b77ac5aab6a91e9c8a5228d7a19e7e89da26e89a1a626971a557939e477905a3a78cde2c789221d7859e0e881de0077e21f177a9de37771dd6673a1c68
|8,0=>0xc41f0a6c0defc7bd5eef6ba1ee17b69ed37b35ac67
|9,0=>0x3176
|_,_=>0
def wAt:=mkWire dB 58 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x8e832d14bc2012c0422d187022d0c04c2f08041011c6c22d6c0471808b510b00b4a2d00b4a2d48b430114043090c0422d2ca432d0834b012ca42010c0480d6c0471808b5114083532d48a030114b43092d352280834301445020d2d352280c052090c04e302c342010c043012034301
|1=>0x14b420d4824301140c309443402d2c0422d00e832d4864301443c02d0064a2f0cc42010c0422d38c0b0d08040664450b010c24301187822d28b432d1c3422d2c04b29180452f083532d48a0301442c70d08b4039442cb012cc861e08b452f083522b00352280834301443c02d00b4301
|2=>0x3091804a0d2824a1918b420108b4a2d180cb01280462d2ca42011c6c22d2c046010c2422d2cc42012c043090cb430148b43012c342012c24a0d442cb0128b432d1c6022d2ca8603180430908e832d0834a2f2ca46010cb420db03c6012c346030c0462d2c042015c2ca2d
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11001000
|5,0=>0x1d11941721431220000000e40c2000000000093072043031021
|6,0=>0x6736616330006210006025e25c20005935720005430005315125014e24d14b24924724434224110004013e23d10003a33733523230002f32c32a22822620000002422131e3
|7,0=>0xb02ae2ac2aa2a82a62a42a22a029e29c29a29829629429229028e28c28a28828628428228027e27c27a27827627427227026e26c26a2
|8,0=>0xbc1bb1ba1b91b81000b71b61b51b41b31b21
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x200e8010000003a4a0018a50001f68000f0000060200030000014480005b4000292000140000090000030400018000008000003280001840000c0000048000022000010000005000002400001000000740000140000080000020000008000002000000
|1=>0x4007081da4f40ebafa07483d03629e81b0cf40d827a06832c032a1e81904f40ab0fa054a7d02281e81123f40831ca034a7d0166fc80b23f404b87a0241bd00a41e804009001065000830800408400180f400bafa0050bd00251f80100fc00807a00402b
|2=>0x83a61ea0970f480e87e40040b10b41e88510404240301a4b3d0c018484b23e424967a1248f909241e842038410b07a081825
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x8100
|5,0=>0x100a34083000030700000010e20102
|6,0=>0x411360080a08481807a0c02600605a71c60f0b027c4a80040598007028c542900e2464980286979d
|7,0=>0x94955b588fcb38745660f76891305c8dec678b24c05b0a44552c5cbe6cd2397
|8,0=>0x86d66ce9e865c164dd233
|9,0=>0x21
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_98 4 roots_98 ops++addP pm 2 dom_59 7 roots_59 ops++addP pm 3 dom_121 7 roots_121 ops++addP pm 4 dom_115 7 roots_115 ops++addP pm 5 dom_91 7 roots_91 ops++addP pm 6 dzo_82_8 4 roots_82 ops++addP pm 7 dom_82 4 roots_82 ops++addP pm 8 dzo_41_16 4 roots_41 ops++addP pm 9 dom_41 4 roots_41 ops++addP pm 10 dzo_107_16 6 roots_107 ops++addP pm 11 dzo_114_8 5 roots_114 ops++addP pm 12 dzo_43_16 5 roots_43 ops++addP pm 13 dom_97 4 roots_97 ops++addP pm 14 dom_107 7 roots_107 ops++addP pm 15 dom_89 4 roots_89 ops++addP pm 16 dzo_115_8 6 roots_115 ops++addP pm 17 dzo_105_16 5 roots_105 ops++addP pm 18 dzo_83_8 5 roots_83 ops++addP pm 19 dom_58 4 roots_58 ops++addP pm 20 dom_120 4 roots_120 ops++addP pm 21 dom_83 5 roots_83 ops++addP pm 22 dom_105 5 roots_105 ops++addP pm 23 dom_106 5 roots_106 ops++addP pm 24 dom_99 5 roots_99 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_82_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_41_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_107_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_114_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_43_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_115_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_105_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_83_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_99 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 7 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 46 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
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
def dzo_84_8:=0x110011000000000011001100
def gzo_84_8:=0x110010000000000010000000
def gsh_84_8:=0x1100100000000000100000
theorem lowS_zo_84_8_84:Lower true dzo_84_8 roots_84 gzo_84_8 4:=lower_iso_b (d1:=dom_84) (r1:=roots_84) (T1:=gsh_84_8) [(dom_84,8)] (by decide +kernel) (lower_slice_b (T:=gsh_84_8) [] (by decide +kernel) lowS_84)
def dzo_116_8:=0x11001100110011001100110011001100
def gzo_116_8:=0x11001100110010001100110010000000
def gsh_116_8:=0x110011001100100011001100100000
theorem lowS_zo_116_8_84:Lower true dzo_116_8 roots_116 gzo_116_8 5:=lower_iso_b (d1:=dom_116) (r1:=roots_116) (T1:=gsh_116_8) [(dom_116,8)] (by decide +kernel) (lower_slice_b (T:=gsh_116_8) [(0x110011000000000011001100000000,0,32)] (by decide +kernel) lowS_84)
def dzo_121_4:=0x30303030303030303030303030303030
def gzo_121_4:=0x30303030303030303030302030302000
def gsh_121_4:=0x3030303030303030303030203030200
theorem lowS_zo_121_4_41:Lower true dzo_121_4 roots_121 gzo_121_4 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_4) [(dom_121,4)] (by decide +kernel) (lower_slice_b (T:=gsh_121_4) [(0x3030000030300000303000003030000,0,16),(0x3030303030303030000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_117_8:=0x33003300330033003300330033003300
def gzo_117_8:=0x33003300330032003300330032002200
def gsh_117_8:=0x330033003300320033003300320022
theorem lowS_zo_117_8_84:Lower true dzo_117_8 roots_117 gzo_117_8 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_8) [(dom_117,8)] (by decide +kernel) (lower_slice_b (T:=gsh_117_8) [(0x220022002200220022002200220022,0,1),(0x330033000000000033003300000000,0,32)] (by decide +kernel) lowS_84)
def dzo_57_4:=0x3030303030303030
def gzo_57_4:=0x3030302030302000
def gsh_57_4:=0x303030203030200
theorem lowS_zo_57_4_41:Lower true dzo_57_4 roots_57 gzo_57_4 5:=lower_iso_b (d1:=dom_57) (r1:=roots_57) (T1:=gsh_57_4) [(dom_57,4)] (by decide +kernel) (lower_slice_b (T:=gsh_57_4) [(0x303000003030000,0,16)] (by decide +kernel) lowS_41)
def dzo_45_16:=0x3333000033330000
def gzo_45_16:=0x3332000032300000
def gsh_45_16:=0x333200003230
theorem lowS_zo_45_16_41:Lower true dzo_45_16 roots_45 gzo_45_16 5:=lower_iso_b (d1:=dom_45) (r1:=roots_45) (T1:=gsh_45_16) [(dom_45,16)] (by decide +kernel) (lower_slice_b (T:=gsh_45_16) [(0x303000003030,0,4)] (by decide +kernel) lowS_41)
def dzo_85_8:=0x330033000000000033003300
def gzo_85_8:=0x330032000000000032002200
def gsh_85_8:=0x3300320000000000320022
theorem lowS_zo_85_8_84:Lower true dzo_85_8 roots_85 gzo_85_8 5:=lower_iso_b (d1:=dom_85) (r1:=roots_85) (T1:=gsh_85_8) [(dom_85,8)] (by decide +kernel) (lower_slice_b (T:=gsh_85_8) [(0x2200220000000000220022,0,1)] (by decide +kernel) lowS_84)
def dzo_109_16:=0x33330000333300003333000033330000
def gzo_109_16:=0x33330000333300003332000032300000
def gsh_109_16:=0x3333000033330000333200003230
theorem lowS_zo_109_16_41:Lower true dzo_109_16 roots_109 gzo_109_16 6:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_16) [(dom_109,16)] (by decide +kernel) (lower_slice_b (T:=gsh_109_16) [(0x3030000030300000303000003030,0,4),(0x3333000033330000000000000000,0,64)] (by decide +kernel) lowS_41)
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(4,20),(4,68),(5,13),(5,21),(5,37),(5,69),(8,9),(8,40),(12,13),(12,28),(12,44),(12,76),(16,20),(16,80),(17,21),(17,25),(17,49),(17,81),(24,25),(24,28),(24,56),(24,88),(32,33),(32,40),(32,96),(36,37),(36,44),(36,52),(36,100),(48,49),(48,52),(48,56),(48,112),(64,65),(64,68),(64,80),(64,96),(72,73),(72,76),(72,88),(72,104)]
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
|5,0=>0x8a638740ed52c9600357
|6,0=>0xd2990ccf5ab979fb4a2bb2d86a7fa286e646ce8950ea34c009474d430f89201a21a96206ebc
|7,0=>0xca6a8bfefea0ab393a47894b283a7c78c4a5fceb5f2b15eac45d3c5592ef5921c5291e4965843d003eb0c263ca1f1a20f0760dd3f0964008ea502f71
|8,0=>0xb382a789cf74b3a642d25341313dea0f7ba067c2
|9,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c0c0c0c0c0c0c00000000000000033333333222222223333333322222222cccccccc0c0c0c0ccccccccc0000000111111110101010111111111000000000000cccc0000cccc0000c0c00000c0c3333000033330000303000003030000000cc00cc0088008800cc00cc0088008b3333333000000003333333300000000888888888888888888888888888888883330333032303230033003300220022cccc0000cccc0000cccc0000cccc00033003300330033003300330033003300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c1111111111111111111111110000000000000000cccccccc000000008888888b3333333333333330000000000000000
|0,1=>0xcccccccc44444444cccccccc00000003333222233332222333322223333222200000000cccc888800000000cccc888b3033303330333033300330033003300cccccccccccccccccccc0000cccc00003030303030303030303000003030000cccccccccccccccccc00cc00cc00cc023232323232323232222222222222222cccccccccccccccc00cc00cc0088008b3333333333333333333333300000000cccccccc8888cccccccccccc888888880003333000033330000000000000000ccccc0c0ccccc0c0ccccc0c0ccccc0c33333333333333333030303030303030cccccccccccccccc888888888888888b3333333333333333333333322222222
|0,2=>0x11111111000000000000000000000000cccccccc00000000000000033003300333333333300330033003300ccccccccc8c8c8c8ccccccccc8c8c8c91111111111111110000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xe58510344e5851034402051034420162051034422050c75c03961440c20081520c72405481440c70081431c90142131431c900e2040c72c03881032870101440c704038d1440c70081440c73002031c92c02032872402050c71801440c2040
|1=>0x1034470081440d11e33881440d10081590c78162051031c20081440c70402058831c08481440c70081431c901f2051031c03881444831c02051031dd00815c0c70081441da0162056431ce2051031c05162056431c03884c51031c0205103607
|2=>0x81440c70081444831c02131440c70162051031c02051031c08c87851031c02056431c03881440c70081440c700f4081440c70105881440c70081032870081440c70245881440d11d6205
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x9303180cc006
|6,0=>0x1e58e4e6b73239798aee50724b909c76e34716b899c3ee187
|7,0=>0x8fbc5e222d0a781bbee1e8eed773b37e1b0ed2665bb1597ceb6857baa5946c9d64ac239d0d07f7
|8,0=>0xab3d3de90f4179d3cd1a5af267
|9,0=>0x15d6
|_,_=>0
def wAt:=mkWire dB 37 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x20051231c0448d2008e0d2074e1320748811c08301207487a147443d0c0836e140480110045022074801100481d143473d0c088011c0481d20047012074701587c801587c801207561f2004e132074e51140881d1408e132074e13207454a0c0481d15203012075121448c70120f4302
|1=>0x3011434801200851d100481d0c08e01207561d20045480c04e0220747012004701200470120087012074702100561f
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x80ce99a33045c4a913220634c590830a608c01000
|7,0=>0xa253ca694b29251ca29432824fc9e93b2724dc9a9332624bc9692b25249c929232
|8,0=>0xb43646c0d71ac3546a0d31
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x10a8a16bfc2c7b82145039c6073840e3b818f7031ea063840c3b809f5009e6011dc023180403004fa0080000a2800e3001c400300003a800620008600104002000018000080000c000100000
|1=>0xa20eb0a5d50d7f989f5285fe427d484bb900f5
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>1
|6,0=>0x1a30728e2030840c6350140
|7,0=>0x65151858c6db94b55e84f61f9e389e4dd720
|8,0=>0x9265d79de4a0
|9,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_117 8 roots_117 ops++addP pm 1 dzo_84_8 4 roots_84 ops++addP pm 2 dom_121 7 roots_121 ops++addP pm 3 dzo_116_8 5 roots_116 ops++addP pm 4 dom_109 7 roots_109 ops++addP pm 5 dom_93 7 roots_93 ops++addP pm 6 dom_124 7 roots_124 ops++addP pm 7 dom_61 6 roots_61 ops++addP pm 8 dzo_121_4 6 roots_121 ops++addP pm 9 dzo_117_8 6 roots_117 ops++addP pm 10 dom_84 4 roots_84 ops++addP pm 11 dzo_57_4 5 roots_57 ops++addP pm 12 dzo_45_16 5 roots_45 ops++addP pm 13 dom_105 5 roots_105 ops++addP pm 14 dzo_85_8 5 roots_85 ops++addP pm 15 dom_41 4 roots_41 ops++addP pm 16 dzo_105_4 5 roots_105 ops++addP pm 17 dom_116 5 roots_116 ops++addP pm 18 dzo_109_16 6 roots_109 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_84_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_116_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_121_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_117_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_57_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_45_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_85_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_105_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_109_16_41 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_117 8 s (0,roots_117.map (·&&&dom_117)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_117 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
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
def dzo_118_8:=0x55005500550055005500550055005500
def gzo_118_8:=0x55005500550054005500550054000000
def gsh_118_8:=0x550055005500540055005500540000
theorem lowS_zo_118_8_86:Lower true dzo_118_8 roots_118 gzo_118_8 6:=lower_iso_b (d1:=dom_118) (r1:=roots_118) (T1:=gsh_118_8) [(dom_118,8)] (by decide +kernel) (lower_slice_b (T:=gsh_118_8) [(0x550055000000000055005500000000,0,32)] (by decide +kernel) lowS_86)
def dzo_86_8:=0x550055000000000055005500
def gzo_86_8:=0x550054000000000054000000
def gsh_86_8:=0x5500540000000000540000
theorem lowS_zo_86_8_86:Lower true dzo_86_8 roots_86 gzo_86_8 5:=lower_iso_b (d1:=dom_86) (r1:=roots_86) (T1:=gsh_86_8) [(dom_86,8)] (by decide +kernel) (lower_slice_b (T:=gsh_86_8) [] (by decide +kernel) lowS_86)
namespace S_126
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,66),(4,20),(4,68),(6,22),(6,38),(6,70),(8,40),(10,26),(10,42),(10,74),(12,28),(12,44),(12,76),(14,30),(14,46),(14,78),(16,18),(16,20),(16,80),(24,26),(24,28),(24,56),(24,88),(32,34),(32,40),(32,96),(36,38),(36,44),(36,52),(36,100),(48,50),(48,52),(48,56),(48,112),(64,66),(64,68),(64,80),(64,96),(72,74),(72,76),(72,88),(72,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_126.map (·&&&dom_126)
def gM:=goal_126&&&dom_126
def NN:Nat→Nat
|4=>3
|5=>10
|6=>17
|7=>7
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xc66f667f7715fcb
|5,0=>0xed006dd3accc835c4a48b10cf7bd075fb794b7852f3582279a
|6,0=>0xf26c7e14d2b8a0ab43e7acd39a071b9351f7c0a4700a4499f846672455fe36d493600c170ed1074e04bea
|7,0=>0xf8beae6db0e68db8751f85fd0649f7524f4
|8,0=>0x464f4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaaaaaaaaaa00aa00aa00aa00141400001414141414140000141400008888888888888888888888888888000555555555555000000000000000000000a0a0a0a0a0a0a0a0a0a00000a0a000001540154000000000154015400000002aaaaaaaaaaaaaaa8000000000000000555555555555505050505050505050508888888888888888888888888888888955555554000000015555555400000002aaaaaaaaaaaaaaaaaaa80002aaa800055555555555555555555555500000000aaaa0000aaaa0000aaaa0000aaaa000154015401540154015401540154015402828282828282828282828282828282855555555555544444444444444444444
|0,1=>0x2aaaaaaaaaaaaaaaaaaaaaaaaaaa80000000555500005555000055550000000000000000aaaaaaaa000000000000000155540001555555555554000155540000000000000002aaa8000000000000000555555555555000055555555555500000000000000000000aaaaaaaaaaaa000155555555555555540154015400000002a802aaaaa802aaaaa802a802a802a80000000005555555500000000555500000000aaaa0000aaaa00000000000000015555555400015555555555540000000002aaaaa80002aaa802a802a8000000005050505050505050505050505050000
|_,_=>0
def sP:Nat→Nat
|0=>0x188274e6e618827498613d9261d4274986209e8930c275267230c413a4c5184ea498620812418827618613c526188f04986f3ad26188ee498620b52618907498a209d8619d6a498a241cc51040418820
|1=>0x30c413a4c309d492186209d3830c413a4c3784e930c413a766188274ccc5188274e0c5104e9e986209d2618827e24c3104e961b43104e9c106209d2628de13a4c5188eb498623ad26
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa5055005
|5,0=>0x4563f63963362d62762161b61560f6
|6,0=>0xb87b17aa7a379c79578e78778167a77376d66766075975274b7
|7,0=>0xe86e17da7d46cd7c67bf7
|8,0=>0xee6
|_,_=>0
def wAt:=mkWire dB 30 127 0x7fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x30b32530d1253261a61a51a530d20d325c2430d1ed32630d3251251a52871a52871a5c2630dc2730d52530b14d1a63161a51a630b34d1a61a530b
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1e270800689825894248902388c2288821884208802
|7,0=>0x261946418c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xfffdbd7d6958483f3d302c20120f0900
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x5b0c4a66199229396
|7,0=>0x8ecfedd
|8,0=>7
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_124 7 roots_124 ops++addP pm 1 dzo_118_8 6 roots_118 ops++addP pm 2 dom_86 5 roots_86 ops++addP pm 3 dom_118 7 roots_118 ops++addP pm 4 dom_110 6 roots_110 ops++addP pm 5 dom_122 7 roots_122 ops++addP pm 6 dzo_86_8 5 roots_86 ops++addP pm 7 dom_62 5 roots_62 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_126 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_118_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_86_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_62 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_124 7 s (0,roots_124.map (·&&&dom_124)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_126 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_124 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_126 gM v ys):RunD true dom_126 gM v (ori ys):=h
def Z (s:Nat):=barP dom_126 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
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
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_slice_b [(0xcccccccc000000000000000000000000cccccccc,16,18)] (by decide +kernel) lowS_157
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_slice_b [(0xcccc0000cccc00000000000000000000cccc0000cccc,32,34)] (by decide +kernel) lowS_173
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
theorem lowS_207:Lower true dom_207 roots_207 goal_207 8:=lower_slice_b [(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0,64,68)] (by decide +kernel) lowS_203
theorem lowS_215:Lower true dom_215 roots_215 goal_215 8:=lower_slice_b [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,64,65)] (by decide +kernel) lowS_214
def dzo_217_2:=0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c
def gzo_217_2:=0xc0c0c0c000000000c0c0c08000000000c0c0c0c000000000c0c0800
def gsh_217_2:=0x3030303000000000303030200000000030303030000000003030200
theorem lowS_zo_217_2_137:Lower true dzo_217_2 roots_217 gzo_217_2 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_2) [(dom_217,2)] (by decide +kernel) (lower_slice_b (T:=gsh_217_2) [(0x3030000000000000303000000000000030300000000000003030000,0,16),(0x3030303000000000000000000000000030303030000000000000000,0,64)] (by decide +kernel) lowS_137)
namespace S_219
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(2,18),(2,66),(3,11),(3,19),(3,67),(3,131),(8,9),(8,136),(10,11),(10,26),(10,74),(10,138),(16,18),(16,80),(16,144),(17,19),(17,25),(17,81),(17,145),(24,25),(24,26),(24,88),(24,152),(64,65),(64,66),(64,80),(72,73),(72,74),(72,88),(72,200),(128,129),(128,136),(128,144),(130,131),(130,138),(130,146),(130,194),(192,193),(192,194),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_219.map (·&&&dom_219)
def gM:=goal_219&&&dom_219
def NN:Nat→Nat
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x798d4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000f000f00000000000f000f00000000000f000f00000000000f000f00c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0ca0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f0000000000000000000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>6
|_,_=>0
def wAt:=mkWire dB 6 220 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_218 7 roots_218 ops++addP pm 1 dom_155 7 roots_155 ops++addP pm 2 dom_91 7 roots_91 ops++addP pm 3 dom_203 7 roots_203 ops++addP pm 4 dom_217 6 roots_217 ops++addP pm 5 dzo_217_2 6 roots_217 ops++addP pm 6 dom_211 6 roots_211 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_217_2_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_211 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_218 7 s (0,roots_218.map (·&&&dom_218)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_218 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_219==dom_219)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_219 gM v ys):RunD true dom_219 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_219 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_219 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_219 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_219 roots_219 goal_219 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_219
theorem lowS_219:Lower true dom_219 roots_219 goal_219 9:=S_219.noCircuit
theorem lowS_221:Lower true dom_221 roots_221 goal_221 9:=lower_slice_b [(0x33333333000000000000000000000000333333330000000000000000,1,65)] (by decide +kernel) lowS_157
namespace S_235
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,34),(2,66),(3,11),(3,35),(3,67),(3,131),(8,9),(8,40),(8,136),(10,11),(10,42),(10,74),(10,138),(32,33),(32,34),(32,40),(32,96),(32,160),(64,65),(64,66),(64,96),(72,73),(72,74),(72,104),(72,200),(128,129),(128,136),(128,160),(130,131),(130,138),(130,162),(130,194),(192,193),(192,194),(192,200),(192,224)]
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
|6,0=>0x4bbbc
|7,0=>0x61f5d5de5e12e870e79c09799
|8,0=>0x2ff10040d9
|9,0=>0xfffda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000f0f00000f0f00000f0f00000f0f00000f0000000f0f00000f0000000000000000000000000000000000f0f00000f0000000f0f00000f00f0000000f0000000f0000000f0000000f0000000f0000000f0000000f00f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0f00000f0f00000f0f00000f0f00000000000000000000000000000000f0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f00f0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000f0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0ca0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0af0f00000f0f000000000000000000000f0f00000f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x78210673821064782106a4782106a782106978210654821065732106543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x2286dd4735c67
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
|0=>0x21976521765217655b785e1765a178619785d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x1ffec5fe7eff5f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x78246
|8,0=>0x53
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_234 8 roots_234 ops++addP pm 1 dom_171 8 roots_171 ops++addP pm 2 dom_233 8 roots_233 ops++addP pm 3 dom_227 7 roots_227 ops++addP pm 4 dom_203 7 roots_203 ops++addP pm 5 dom_107 7 roots_107 ops++addP pm 6 dom_195 4 roots_195 ops++addP pm 7 dom_75 4 roots_75 ops++addP pm 8 dom_99 5 roots_99 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_235 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_99 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_234 8 s (0,roots_234.map (·&&&dom_234)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_235 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_234 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]]
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
theorem lowS_237:Lower true dom_237 roots_237 goal_237 9:=lower_slice_b [(0x303000003030000030300000303000003030000030300000303000003030,64,68)] (by decide +kernel) lowS_233
namespace S_243
def pG:List (Nat×Nat):=[(1,33),(1,65),(1,129),(2,18),(2,34),(2,66),(3,19),(3,35),(3,67),(3,131),(16,18),(16,80),(16,144),(17,19),(17,49),(17,81),(17,145),(32,33),(32,34),(32,96),(32,160),(48,49),(48,50),(48,112),(48,176),(64,65),(64,66),(64,80),(64,96),(128,129),(128,144),(128,160),(130,131),(130,146),(130,162),(130,194),(192,193),(192,194),(192,208),(192,224)]
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
|5,0=>0x738ed68ba908cfd
|6,0=>0xc9fbb95cc434a3b26ffd1588f
|7,0=>0xcdcdeb16009ee7322684
|8,0=>0x7a9f6
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xe000e000e000e000e000e000e000e000e000e000e000e000e000e000e000ef000f000f000f000a000a000a000a000f000f000f000f000a000a000a000af000f000f000c000f000f000f000c000f000f000f000c000f000f000f000cf000f000f000f000f000f000f000f000f000f000f000f000f000f00000000f000f000c000c000f000f000c000c000f000f000c000c000f000f000c000cf000f000f000f000f000f000f000f00000000000000000000000000000000f000f000f000f000f000f000f0000000f000f000f000f000f000f000f0000f000f000f0000000f000f000f0000000f000f000f0000000f000f000f0000f000f000f000f000f000f00000000000f000f000f000f000f000f00000000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000af000f00000000000f000f00000000000f000f00000000000f000f00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c5000500050005000500050005000500050005000500050005000500000000f000f000f000f000f000f000f000f000f000f000f000f0000000000000000f000f000f000f0000000000000000000f000f000f000f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x54360a54f360a543e60a754360a85360ad85360ac5436108b360a75436185361098536187361543210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x2d832806
|6,0=>0x2a746e758bb116
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
|0=>0xd960541545510a54d544295042954551
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x10000
|6,0=>0x8171523212
|7,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xc5da7ed1f64a010807ec00c000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40
|6,0=>0x38bd
|7,0=>0xb6e
|8,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_227 7 roots_227 ops++addP pm 1 dom_177 5 roots_177 ops++addP pm 2 dom_163 5 roots_163 ops++addP pm 3 dom_115 7 roots_115 ops++addP pm 4 dom_241 6 roots_241 ops++addP pm 5 dom_210 5 roots_210 ops++addP pm 6 dom_242 6 roots_242 ops++addP pm 7 dom_211 6 roots_211 ops++addP pm 8 dom_195 4 roots_195 ops++addP pm 9 dom_225 5 roots_225 ops++addP pm 10 dom_83 5 roots_83 ops++addP pm 11 dom_179 6 roots_179 ops++addP pm 12 dom_51 4 roots_51 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_243 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_51 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_227 7 s (0,roots_227.map (·&&&dom_227)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_243 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_227 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
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
theorem lowS_245:Lower true dom_245 roots_245 goal_245 9:=lower_slice_b [(0x33003300330033000000000000000000330033003300330000000000000000,1,65)] (by decide +kernel) lowS_181
def isoMvS_190:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_183
def isoMvS_222:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_126
def isoMvS_231:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 8:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_215
def isoMvS_238:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_183
def isoMvS_246:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_243
def isoMvS_249:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 9:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_237
def isoMvS_250:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 9:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_221
def isoMvS_252:List (Nat×Nat):=[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_221
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xcccccccccccccccccccccccccccccccc,16,18)] (by decide +kernel) lowS_125
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_slice_b [(0xcccccccccccccccc0000000000000000cccccccccccccccc,16,18)] (by decide +kernel) lowS_189
def dzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00
def gzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00aa00
def gsh_215_8:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00aa
theorem lowS_zo_215_8_86:Lower true dzo_215_8 roots_215 gzo_215_8 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_8) [(dom_215,8)] (by decide +kernel) (lower_slice_b (T:=gsh_215_8) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xff00ff0000000000ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_86)
def dzo_87_8:=0xff00ff0000000000ff00ff00
def gzo_87_8:=0xff00fe0000000000fe00aa00
def gsh_87_8:=0xff00fe0000000000fe00aa
theorem lowS_zo_87_8_86:Lower true dzo_87_8 roots_87 gzo_87_8 6:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_8) [(dom_87,8)] (by decide +kernel) (lower_slice_b (T:=gsh_87_8) [(0xaa00aa0000000000aa00aa,0,1)] (by decide +kernel) lowS_86)
namespace S_223
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(2,18),(2,66),(3,11),(3,19),(3,67),(3,131),(4,20),(4,68),(4,132),(5,13),(5,21),(5,69),(5,133),(6,22),(6,70),(6,134),(7,15),(7,23),(7,71),(7,135),(8,9),(8,136),(10,11),(10,26),(10,74),(10,138),(12,13),(12,28),(12,76),(12,140),(14,15),(14,30),(14,78),(14,142),(16,18),(16,20),(16,80),(16,144),(17,19),(17,21),(17,25),(17,81),(17,145),(24,25),(24,26),(24,28),(24,88),(24,152),(64,65),(64,66),(64,68),(64,80),(72,73),(72,74),(72,76),(72,88),(72,200),(128,129),(128,132),(128,136),(128,144),(130,131),(130,134),(130,138),(130,146),(130,194),(192,193),(192,194),(192,196),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffff
def xsM:=roots_223.map (·&&&dom_223)
def gM:=goal_223&&&dom_223
def NN:Nat→Nat
|9=>3
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0x946447474a6375a
|10,0=>0x1730e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffff0000000000ffffff0000000000ffffff0000000000ffffff00ffffffff00000000ffffffff00000000ffff000000000000ffff0000ffff000000000000ffff000000000000ffff000000000000ffff0000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0cccccccc00000000cccccccc00000000cccccccc00000000ccccccccaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaaffffffff000000000000000000000000ffffffff0000000000000000ffffffff00000000ffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x7543210975432108754321076543210
|_=>0
def sO:Nat→Nat→Nat
|9,0=>0x4211008
|10,0=>0x187
|_,_=>0
def wAt:=mkWire dB 10 224 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1d570541
|_=>0
def oO:Nat→Nat→Nat
|9,0=>0x21441
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 6
def pmP:Nat→Nat
|0=>0x2ff9fdff1fc00
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>0x11a
|10,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_222 9 roots_222 ops++addP pm 1 dom_159 9 roots_159 ops++addP pm 2 dom_221 9 roots_221 ops++addP pm 3 dom_219 9 roots_219 ops++addP pm 4 dom_215 8 roots_215 ops++addP pm 5 dom_95 8 roots_95 ops++addP pm 6 dom_207 8 roots_207 ops++addP pm 7 dzo_215_8 7 roots_215 ops++addP pm 8 dom_87 6 roots_87 ops++addP pm 9 dzo_87_8 6 roots_87 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_223 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_215_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_87_8_86 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_222 9 s (0,roots_222.map (·&&&dom_222)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_223 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_222 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_223 gM v ys):RunD true dom_223 gM v (ori ys):=h
def Z (s:Nat):=barP dom_223 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 3 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 3 0 = true)
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
namespace S_247
def pG:List (Nat×Nat):=[(1,33),(1,65),(1,129),(2,18),(2,34),(2,66),(3,19),(3,35),(3,67),(3,131),(4,20),(4,68),(4,132),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,23),(7,39),(7,71),(7,135),(16,18),(16,20),(16,80),(16,144),(17,19),(17,21),(17,49),(17,81),(17,145),(32,33),(32,34),(32,96),(32,160),(36,37),(36,38),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,112),(48,176),(64,65),(64,66),(64,68),(64,80),(64,96),(128,129),(128,132),(128,144),(128,160),(130,131),(130,134),(130,146),(130,162),(130,194),(192,193),(192,194),(192,196),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7ffffffffffffffff
def xsM:=roots_247.map (·&&&dom_247)
def gM:=goal_247&&&dom_247
def NN:Nat→Nat
|9=>1
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0xf9dd7
|10,0=>0x3ef7d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ac688fac688
|_=>0
def sO:Nat→Nat→Nat
|9,0=>8
|10,0=>0x87
|_,_=>0
def wAt:=mkWire dB 8 248 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
|0=>0x3f80
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>1
|10,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_246 9 roots_246 ops++addP pm 1 dom_183 9 roots_183 ops++addP pm 2 dom_245 9 roots_245 ops++addP pm 3 dom_243 9 roots_243 ops++addP pm 4 dom_119 9 roots_119 ops++addP pm 5 dom_231 8 roots_231 ops++addP pm 6 dom_215 8 roots_215 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_247 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_215 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_246 9 s (0,roots_246.map (·&&&dom_246)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_247 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_246 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_247==dom_247)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_247 gM v ys):RunD true dom_247 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_247 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_247 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_247 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_247 roots_247 goal_247 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_247
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=S_247.noCircuit
def dzo_211_8:=0xf000f00000000000f000f00000000000f000f00000000000f000f00
def gzo_211_8:=0xf000f00000000000f000f00000000000f000e00000000000e000a00
def gsh_211_8:=0xf000f00000000000f000f00000000000f000e00000000000e000a
theorem lowS_zo_211_8_82:Lower true dzo_211_8 roots_211 gzo_211_8 6:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_8) [(dom_211,8)] (by decide +kernel) (lower_slice_b (T:=gsh_211_8) [(0xa000a00000000000a000a00000000000a000a00000000000a000a,0,1),(0xf000f00000000000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_243_8:=0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00
def gzo_243_8:=0xf000f000f000f000f000f000f000f000f000f000f000e000f000f000e000a00
def gsh_243_8:=0xf000f000f000f000f000f000f000f000f000f000f000e000f000f000e000a
theorem lowS_zo_243_8_82:Lower true dzo_243_8 roots_243 gzo_243_8 7:=lower_iso_b (d1:=dom_243) (r1:=roots_243) (T1:=gsh_243_8) [(dom_243,8)] (by decide +kernel) (lower_slice_b (T:=gsh_243_8) [(0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a,0,1),(0xf000f00000000000f000f00000000000f000f00000000000f000f00000000,0,32),(0xf000f000f000f000f000f000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_249_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_249_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c0c0c0c0c0c0c0c0c0c0c0c0c0c0800
def gsh_249_2:=0x303030303030303030303030303030203030303030303030303030303030200
theorem lowS_zo_249_2_137:Lower true dzo_249_2 roots_249 gzo_249_2 7:=lower_iso_b (d1:=dom_249) (r1:=roots_249) (T1:=gsh_249_2) [(dom_249,2)] (by decide +kernel) (lower_slice_b (T:=gsh_249_2) [(0x303000003030000030300000303000003030000030300000303000003030000,0,16),(0x303030300000000030303030000000003030303000000000303030300000000,0,32),(0x303030303030303000000000000000003030303030303030000000000000000,0,64)] (by decide +kernel) lowS_137)
def dzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def gzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000e0c0000
def gsh_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000e0c
theorem lowS_zo_235_16_41:Lower true dzo_235_16 roots_235 gzo_235_16 7:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_16) [(dom_235,16)] (by decide +kernel) (lower_slice_b (T:=gsh_235_16) [(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c,0,2),(0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000,0,64),(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_210_8:=0x5000500000000000500050000000000050005000000000005000500
def gzo_210_8:=0x5000500000000000500050000000000050004000000000004000000
def gsh_210_8:=0x50005000000000005000500000000000500040000000000040000
theorem lowS_zo_210_8_82:Lower true dzo_210_8 roots_210 gzo_210_8 5:=lower_iso_b (d1:=dom_210) (r1:=roots_210) (T1:=gsh_210_8) [(dom_210,8)] (by decide +kernel) (lower_slice_b (T:=gsh_210_8) [(0x50005000000000005000500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_171_16:=0xf0f00000f0f000000000000000000000f0f00000f0f0000
def gzo_171_16:=0xf0f00000f0f000000000000000000000f0e00000e0c0000
def gsh_171_16:=0xf0f00000f0f000000000000000000000f0e00000e0c
theorem lowS_zo_171_16_41:Lower true dzo_171_16 roots_171 gzo_171_16 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_16) [(dom_171,16)] (by decide +kernel) (lower_slice_b (T:=gsh_171_16) [(0xc0c00000c0c000000000000000000000c0c00000c0c,0,2),(0xf0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_242_8:=0x500050005000500050005000500050005000500050005000500050005000500
def gzo_242_8:=0x500050005000500050005000500050005000500050004000500050004000000
def gsh_242_8:=0x5000500050005000500050005000500050005000500040005000500040000
theorem lowS_zo_242_8_82:Lower true dzo_242_8 roots_242 gzo_242_8 6:=lower_iso_b (d1:=dom_242) (r1:=roots_242) (T1:=gsh_242_8) [(dom_242,8)] (by decide +kernel) (lower_slice_b (T:=gsh_242_8) [(0x5000500000000000500050000000000050005000000000005000500000000,0,32),(0x5000500050005000500050005000500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_233_16:=0x303000003030000030300000303000003030000030300000303000003030000
def gzo_233_16:=0x303000003030000030300000303000003030000030300000302000002000000
def gsh_233_16:=0x30300000303000003030000030300000303000003030000030200000200
theorem lowS_zo_233_16_41:Lower true dzo_233_16 roots_233 gzo_233_16 6:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_16) [(dom_233,16)] (by decide +kernel) (lower_slice_b (T:=gsh_233_16) [(0x30300000303000000000000000000000303000003030000000000000000,0,64),(0x30300000303000003030000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(16,18),(16,80),(16,144),(17,19),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,96),(32,160),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,66),(64,80),(64,96),(72,73),(72,74),(72,88),(72,104),(72,200),(128,129),(128,136),(128,144),(128,160),(130,131),(130,138),(130,146),(130,162),(130,194),(192,193),(192,194),(192,200),(192,208),(192,224)]
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
|6,0=>0x2e3ad
|7,0=>0x9b51f8022a48946
|8,0=>0xed39cecd14e9790e314cd779ebe13fb5ab8b39cb94db6882b887c0172e13277fc26ed81f51f
|9,0=>0xf1d37efcb1efa83e8b19e6b33e04efdcc81d77f1d0d99d08b8ce76ec98c2bf69bbb4e2af092a7da19b70296cf4921598b088876ad8464b8131e7fc0b7ea1877bf777acb701b66ea586a9eb626475fa065cb885b79e5ab025690252a46501ea4df9647fd547eb8479684432140e33363683163b2a3a82961b24b9f1c8c21c20b10b3a0f6ef05b9c03c5a
|10,0=>0xeb5f5db635c34dfaeeaeac43596f8592b816c0fe58b411497e
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f0f0f0c0c0f0f0f0f0f0f0c0c0f0f0f0f0f0f0c0c0f0f0f0f0f0f0c0cf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a30303030303030303030303030300000303030303030303030303030303000000000000f0a0f0a000000000f0a0f0a000000000f0a0f0a000000000f0a0f0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|0,1=>0xf0f0f0f000000000f000f00000000000f0f0f0f000000000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f0f0f0f000f0000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000ef0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e504050405040504050405040504050405040504050405040504050405040504f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a50505050404040405050505040404040505050504040404050505050404040400f000f000f000f000a000a000a000a000f000f000f000f000a000a000a000a00000000f0c0f0c000000000f0c0f0c000000000f0c0f0c000000000f0c0f0c302030203020302030203020302030203020302030203020302030203020302f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0af0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0cf0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0ce0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e
|0,2=>0x5050505050505050500050005000500050505050505050505000500050005000000000000000000f0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f0000000000e0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0e50505050500050005050505050005000505050505000500050505050500050000000000f0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0af0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0000000000000000f0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0f0a303030303000300030303030300030003030303030003000303030303000300f0f0f0f0f0c0f0c0f0f0f0f0f0c0f0c0f0f0f0f0f0c0f0c0f0f0f0f0f0c0f0c00f000f000c000c000f000f000c000c000f000f000c000c000f000f000c000cf0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a0f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0af0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e
|_,_=>0
def sP:Nat→Nat
|0=>0x1851c408100645414404018a1440c10063451ce10020628b1471010123c91501c10063531471003cd24b14704048f24b1c100644b1471010064454040403cd2451ce00634b14710100628b1440c100c1851c40810081851c40810061440c2040
|1=>0x2451c404048a2531c404028914711904028914711804028914711704018a5051c40403062851c404044a24540404034a24b1471010122892c710100f28914738100a25415010100a2451c458101528914710100c18a2c51c404048f2451ce040
|2=>0x1220403cd2451c404044a24b14710100628540710100a26114710102028914710100a2451c47c101a28914738404018d14710101e28914710100628b14710100a2451c474100a25c14710100a2531473840122891501c404028914711b04068a
|3=>0xa0100a2451c49c102618a14710100f2892c51c100d2891473840064451c404018a1473840402892d31c40402899451c404034a25314710048f2451c40402891471240408ca2451c404048a2451ce10100a26114738404018a4c51c4040289147
|4=>0x1c404044a2451c40402895051c404018a14710101228914710100d28914710100a2451ce10100818a14710101228950710100a2451c4b0102b28914710100a2451c408101128950510102a18a14710100f2891501c100a2451c4a4100a2451c4
|5=>0xa2451c40402894c51c40402891501c40402892c51c40403ca245
|_=>0
def sO:Nat→Nat→Nat
|6,0=>7
|7,0=>0x17803e0078
|8,0=>0x88920207971c9c6b7191c5b914e04c711203d70d602e709dc1f8
|9,0=>0x24588f623588b62258876215883620587f61f587b61e587761d6773a1c686fa1b686ba1a6867a195963258485f217485ae563856e153852e14294edd3384ae123846e113842a50283ea0f283aa0e2836a0d2832a0c282e64b182a60a182660918
|10,0=>0xa5228c8a1227c89d226c8995e5d895624d8
|11,0=>0x29c7
|_,_=>0
def wAt:=mkWire dB 45 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1444a1110147111474b1f1444a2d14445111874a252854a111014a2528b85112874a25147481f1814a25289440528145111814a251c44a112854a0528945051444a1128145112844a151444a2528747112894a1d2814a1110145112894a05207c5111814a2528b85112894a2e1444a25
|1=>0x1414a11285521f2854a51147440528545391014a2514151172874a112814a1d1444a251c44b051444a411c44a4e1414a391014a2528152052854a2514445421c454111474405141471128554131474d1128145052855113287453a1014a521474a25147461d2894a1d1c44a051444a15
|2=>0x5051c445112844a1d1474a252854a0510146052894a15147531314152072854a2e1444a1d14746152894a111c44a421c452132854a3a10146112894a1114444052814a252874a2510145051444b071444a05
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x64033003
|8,0=>0x3433132e32b32832532231f31c31931631331030d30a3
|9,0=>0xa32a129f29d29b29929729529329128f28d28b28928728528328127f27d27b27927727527327126f26d26b26926726526326125f25d25b25925725525325124f24d24b24924724524324123f23d23b2392372
|10,0=>0xae1ad1ac1ab1aa1a91a81a71a61a51
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x9657ac00250deb0008457ac002105eb00080d7ac002015eb000480bc0001202ce0003e77a4000b0deb0002837ac00080deb0001617ac000505eb0000d37ac00026feb000097fac00024deb0000877ac00020deb0000637ac000185eb00001ff2800004feb0000137ac000025eb000003fac000005eb0000003000000003000000003800000000
|1=>0x44841fac110085e70318117ac0c600deb0308037ac09a02feb026803fac08202feb020803fac08200deb011287728044a0deb0103e37ac040a1deb0102037ac04018deb0100417ac04002deb0100037ac03e025eb0078017ac01826feb0060097ac01024feb004013dac010005eb00180d7ac006025eb0018057ac00600deb0018017ac004005eb
|2=>0x846c03fad011105fb2044017bc512187eb1108417ac402105eb1000617ac31034feb0c40417ac20210deb0808417ac20034feb0800417ac13b005eb04c8417ac112585eb
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0xc101
|8,0=>0x65aa77ef96182ee848d91052aa
|9,0=>0x13583b2a20e4f3e4d8a1843d247561473864597b47ae631b890029d6e954ae50785bc672d2ad8a8a4cc9c7080c462888d
|10,0=>0x1b120e6a1ca4c50320
|11,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 34 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_235 10 roots_235 ops++addP pm 1 dom_187 9 roots_187 ops++addP pm 2 dom_171 8 roots_171 ops++addP pm 3 dom_185 8 roots_185 ops++addP pm 4 dom_233 8 roots_233 ops++addP pm 5 dom_249 9 roots_249 ops++addP pm 6 dom_250 9 roots_250 ops++addP pm 7 dom_219 9 roots_219 ops++addP pm 8 dom_123 10 roots_123 ops++addP pm 9 dzo_211_8 6 roots_211 ops++addP pm 10 dom_243 9 roots_243 ops++addP pm 11 dzo_243_8 7 roots_243 ops++addP pm 12 dom_218 7 roots_218 ops++addP pm 13 dom_155 7 roots_155 ops++addP pm 14 dom_242 6 roots_242 ops++addP pm 15 dzo_217_2 6 roots_217 ops++addP pm 16 dzo_249_2 7 roots_249 ops++addP pm 17 dom_210 5 roots_210 ops++addP pm 18 dom_248 6 roots_248 ops++addP pm 19 dom_211 6 roots_211 ops++addP pm 20 dzo_235_16 7 roots_235 ops++addP pm 21 dzo_210_8 5 roots_210 ops++addP pm 22 dom_186 6 roots_186 ops++addP pm 23 dzo_171_16 6 roots_171 ops++addP pm 24 dom_203 7 roots_203 ops++addP pm 25 dom_234 8 roots_234 ops++addP pm 26 dzo_242_8 6 roots_242 ops++addP pm 27 dom_179 6 roots_179 ops++addP pm 28 dzo_233_16 6 roots_233 ops++addP pm 29 dom_217 6 roots_217 ops++addP pm 30 dom_241 6 roots_241 ops++addP pm 31 dom_137 4 roots_137 ops++addP pm 32 dom_201 5 roots_201 ops++addP pm 33 dom_227 7 roots_227 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_211_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_243_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_217_2_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_249_2_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_235_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_210_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_171_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_242_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_233_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_227 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_235 10 s (0,roots_235.map (·&&&dom_235)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_235 h
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
def dzo_245_8:=0x3300330033003300330033003300330033003300330033003300330033003300
def gzo_245_8:=0x3300330033003300330033003300330033003300330032003300330032002200
def gsh_245_8:=0x33003300330033003300330033003300330033003300320033003300320022
theorem lowS_zo_245_8_84:Lower true dzo_245_8 roots_245 gzo_245_8 7:=lower_iso_b (d1:=dom_245) (r1:=roots_245) (T1:=gsh_245_8) [(dom_245,8)] (by decide +kernel) (lower_slice_b (T:=gsh_245_8) [(0x22002200220022002200220022002200220022002200220022002200220022,0,1),(0x33003300000000003300330000000000330033000000000033003300000000,0,32),(0x33003300330033003300330033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_213_8:=0x33003300000000003300330000000000330033000000000033003300
def gzo_213_8:=0x33003300000000003300330000000000330032000000000032002200
def gsh_213_8:=0x330033000000000033003300000000003300320000000000320022
theorem lowS_zo_213_8_84:Lower true dzo_213_8 roots_213 gzo_213_8 6:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_8) [(dom_213,8)] (by decide +kernel) (lower_slice_b (T:=gsh_213_8) [(0x220022000000000022002200000000002200220000000000220022,0,1),(0x330033000000000033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_249_4:=0x3030303030303030303030303030303030303030303030303030303030303030
def gzo_249_4:=0x3030303030303030303030303030303030303030303030303030302030302000
def gsh_249_4:=0x303030303030303030303030303030303030303030303030303030203030200
theorem lowS_zo_249_4_41:Lower true dzo_249_4 roots_249 gzo_249_4 7:=lower_iso_b (d1:=dom_249) (r1:=roots_249) (T1:=gsh_249_4) [(dom_249,4)] (by decide +kernel) (lower_slice_b (T:=gsh_249_4) [(0x303000003030000030300000303000003030000030300000303000003030000,0,16),(0x303030303030303000000000000000003030303030303030000000000000000,0,64),(0x303030303030303030303030303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_212_8:=0x11001100000000001100110000000000110011000000000011001100
def gzo_212_8:=0x11001100000000001100110000000000110010000000000010000000
def gsh_212_8:=0x110011000000000011001100000000001100100000000000100000
theorem lowS_zo_212_8_84:Lower true dzo_212_8 roots_212 gzo_212_8 5:=lower_iso_b (d1:=dom_212) (r1:=roots_212) (T1:=gsh_212_8) [(dom_212,8)] (by decide +kernel) (lower_slice_b (T:=gsh_212_8) [(0x110011000000000011001100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_237_16:=0x3333000033330000333300003333000033330000333300003333000033330000
def gzo_237_16:=0x3333000033330000333300003333000033330000333300003332000032300000
def gsh_237_16:=0x333300003333000033330000333300003333000033330000333200003230
theorem lowS_zo_237_16_41:Lower true dzo_237_16 roots_237 gzo_237_16 7:=lower_iso_b (d1:=dom_237) (r1:=roots_237) (T1:=gsh_237_16) [(dom_237,16)] (by decide +kernel) (lower_slice_b (T:=gsh_237_16) [(0x303000003030000030300000303000003030000030300000303000003030,0,4),(0x333300003333000000000000000000003333000033330000000000000000,0,64),(0x333300003333000033330000333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_244_8:=0x1100110011001100110011001100110011001100110011001100110011001100
def gzo_244_8:=0x1100110011001100110011001100110011001100110010001100110010000000
def gsh_244_8:=0x11001100110011001100110011001100110011001100100011001100100000
theorem lowS_zo_244_8_84:Lower true dzo_244_8 roots_244 gzo_244_8 6:=lower_iso_b (d1:=dom_244) (r1:=roots_244) (T1:=gsh_244_8) [(dom_244,8)] (by decide +kernel) (lower_slice_b (T:=gsh_244_8) [(0x11001100000000001100110000000000110011000000000011001100000000,0,32),(0x11001100110011001100110011001100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
namespace S_253
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(4,20),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,40),(8,136),(12,13),(12,28),(12,44),(12,76),(12,140),(16,20),(16,80),(16,144),(17,21),(17,25),(17,49),(17,81),(17,145),(24,25),(24,28),(24,56),(24,88),(24,152),(32,33),(32,40),(32,96),(32,160),(36,37),(36,44),(36,52),(36,100),(36,164),(48,49),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,80),(64,96),(72,73),(72,76),(72,88),(72,104),(72,200),(128,129),(128,132),(128,136),(128,144),(128,160),(192,193),(192,196),(192,200),(192,208),(192,224)]
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
|9,0=>0x8ed3d7c3e97a78f66fce5918855a7a4be4f4a34142aa6247591c19b1c14700776
|10,0=>0x66f6a3343a2609120610
|11,0=>0x1e31b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc00cc00cc000000cc00cc00cc000000cc00cc00cc000000cc00cc00cc0003333333333332222333333333333222233333333333322223333333333332222cccccc00cccccc00cccccc00cccccc00cccccc00cccccc00cccccc00cccccc03333332233333322333333223333332233333322333333223333332233333322cccccccc88888888cccccccc88888888cccccccc88888888cccccccc8888888b322332233223322332233223322332233223322332233223322332233223322cccccccccc00cc00cccccccccc00cc00cccccccccc00cc00cccccccccc00cc02222222222222222222222222222222222222222222222222222222222222222cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000003333000033330000333300003333000033330000333300003333000033330000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc03232323232323232323232323232323232323232323232323232323232323232c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c1111111111001100111111111100110011111111110011001111111111001100cccccccccccccccc0000000000000000cccccccccccccccc0000000000000003333333333333333333333333333333300000000000000000000000000000000
|0,1=>0xccccccccc0c0c0c0ccccccccc0c0c0c0ccccccccc0c0c0c0ccccccccc0c0c0c1111111110101010111111111010101011111111101010101111111110101010cccccccccc88cc88cccccccccc88cc88cccccccccc88cc88cccccccccc88cc8b33033303330333033303330333033303330333033303330333033303330333000000000ccc0ccc000000000ccc0ccc000000000ccc0ccc000000000ccc0ccc00000000332233220000000033223322000000003322332200000000332233220c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c0b333333333330000333333333333000033333333333300003333333333330000
|_,_=>0
def sP:Nat→Nat
|0=>0x81cc51a02049cc520d0105ce62910101cc51a2c1054e628d0102ce65146101cd429101024e650d0101cc51a26101cc51a24101cc51a22101cc51a1e1038e628d0101d8628d010256650c20398a418820
|1=>0x1cc51a02049cc51a02059cc51a0203b4c51a020
|_=>0
def sO:Nat→Nat→Nat
|8,0=>0x87008
|9,0=>0x6f96785f85784f84783f83782f82781f81780f8
|10,0=>0x908888808788
|11,0=>0x987
|_,_=>0
def wAt:=mkWire dB 24 254 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x29d3a129931d29d1a11a119dba319d5953a12a13a11a128d2a129da1f28d51f2a150f2a181731d5993a16a12993952a13a14a329d1a1
|_=>0
def oO:Nat→Nat→Nat
|8,0=>0xcc03
|9,0=>0x1e2709a26096250922408e2308a220862
|10,0=>0x8c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0x8043f741c7e72063e71607ff1423f7100bf71007f70e23ff01c3f70183e7010bf7007be70063e70047e70007f70003ff0003f70003e7000000
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>0x83
|9,0=>0xb341ec308ed72a28
|10,0=>0x19649
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 24 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_189 10 roots_189 ops++addP pm 1 dom_125 10 roots_125 ops++addP pm 2 dom_249 9 roots_249 ops++addP pm 3 dom_213 6 roots_213 ops++addP pm 4 dzo_245_8 7 roots_245 ops++addP pm 5 dom_233 8 roots_233 ops++addP pm 6 dom_252 9 roots_252 ops++addP pm 7 dom_245 9 roots_245 ops++addP pm 8 dom_237 9 roots_237 ops++addP pm 9 dom_221 9 roots_221 ops++addP pm 10 dom_220 7 roots_220 ops++addP pm 11 dzo_213_8 6 roots_213 ops++addP pm 12 dom_241 6 roots_241 ops++addP pm 13 dzo_249_4 7 roots_249 ops++addP pm 14 dzo_212_8 5 roots_212 ops++addP pm 15 dom_205 6 roots_205 ops++addP pm 16 dzo_237_16 7 roots_237 ops++addP pm 17 dzo_244_8 6 roots_244 ops++addP pm 18 dom_212 5 roots_212 ops++addP pm 19 dom_248 6 roots_248 ops++addP pm 20 dom_244 6 roots_244 ops++addP pm 21 dom_217 6 roots_217 ops++addP pm 22 dom_236 6 roots_236 ops++addP pm 23 dom_229 6 roots_229 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_245_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_213_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_249_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_212_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_237_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_244_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_229 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_189 10 s (0,roots_189.map (·&&&dom_189)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_189 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
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
def dzo_214_8:=0x55005500000000005500550000000000550055000000000055005500
def gzo_214_8:=0x55005500000000005500550000000000550054000000000054000000
def gsh_214_8:=0x550055000000000055005500000000005500540000000000540000
theorem lowS_zo_214_8_86:Lower true dzo_214_8 roots_214 gzo_214_8 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_8) [(dom_214,8)] (by decide +kernel) (lower_slice_b (T:=gsh_214_8) [(0x550055000000000055005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_86)
def dzo_246_8:=0x5500550055005500550055005500550055005500550055005500550055005500
def gzo_246_8:=0x5500550055005500550055005500550055005500550054005500550054000000
def gsh_246_8:=0x55005500550055005500550055005500550055005500540055005500540000
theorem lowS_zo_246_8_86:Lower true dzo_246_8 roots_246 gzo_246_8 7:=lower_iso_b (d1:=dom_246) (r1:=roots_246) (T1:=gsh_246_8) [(dom_246,8)] (by decide +kernel) (lower_slice_b (T:=gsh_246_8) [(0x55005500000000005500550000000000550055000000000055005500000000,0,32),(0x55005500550055005500550055005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_86)
namespace S_254
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,66),(4,20),(4,68),(4,132),(6,22),(6,38),(6,70),(6,134),(8,40),(8,136),(10,26),(10,42),(10,74),(10,138),(12,28),(12,44),(12,76),(12,140),(14,30),(14,46),(14,78),(14,142),(16,18),(16,20),(16,80),(16,144),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,40),(32,96),(32,160),(36,38),(36,44),(36,52),(36,100),(36,164),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,68),(64,80),(64,96),(72,74),(72,76),(72,88),(72,104),(72,200),(128,132),(128,136),(128,144),(128,160),(130,134),(130,138),(130,146),(130,162),(130,194),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|4=>10
|5=>35
|6=>102
|7=>256
|8=>245
|9=>105
|10=>12
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xfb603f4714e87b3d556f89c8b8298533d2c1a7a8134a204dfa
|5,0=>0xfa73cf6a3fe4b13dacb9c6dcfbbb14b7771b3877add59ac5719e0f69a4e899da8931e29163279c26744546c75e6a31e6895950e614a19c49b5b4828e462d9328e02e6ad28188221fa20e82104560f5490a74303cb8026c5
|6,0=>0xf9966e8699e35e8e135dda93dd041ec7fcec41c9c2e79c2d86c0b7ec0306bf118bd5a0bce81b5290ad07fabdb5aa5cda9525a5096a5024a3812a378fa1f3aa1e019e0f69c76c97e04977859643f949bb8a483895768924b7e94779a9b7879a77c8277b8d73d886c75e6bcd368c6668959645db6300b5c4d15b0f65a9f959d5c57f3555c6e5554354f1553df051b504ec1e4ea074ad4e4773e44adc43f2640dfd40dfc3b5a336725335b73248b3179e2e3072d6f92cc6f2c2b12a4e92822228188267ec24525228c220e8220e341c9c8183d9181231730f147d913dd51207d113720c97c0b3910879f067ea0628c0603405623054cc04e7e01e9b01ab500721
|7,0=>0x4ccbf4c8224bc9d4b0914a1e749c054875445ebf44d8c446a4445a94386742ee142d94424834240c42113417e9407d63f93e3f68e3f5e53ee583e3563dcbe3d8813d4ef3ca1c3b5ad3a489395ff38e6938d8c383213809e3792b377693569834d7734a603421433e4833c0433094315043134630a153089b3073930517300b52eaef2dbd52d1742cc6f2c7592c4472c0882af852ab662aa612a30d2962d28f5c281f1259922572d256832512524fcc2355222d0c229e722967225b02146f2017a1f95c1f7891f6921f22e1b6071a9d21a3801994918da1184281838c181231766d16e2516ad81617f15ccf15771153481435b13c9c13ba612e9f1280d11e3110dff103cd0f2560e48a0dd920d2eb0cf920bfed0b53a0a922093850933207a700710006b3f06b35046980409003ff303c6e0371102f6b02ac701235009840062b
|7,1=>0xf3ac8f1cafeea17ee664ee5caed81dea967e8699e7dc3e79aee72c4e4706e43a3e35e8dba7cdae75da8ebda217d659fd0477ce096cc221caac2c8cfec7d7bc60a1c5f71c42f7c407dc3f44c264ec0a13bf873bc412b9fafb72ddb6957b5e0bb4081b2c5aacd00ac531aaedbaa78da7a91a7581a4255a32c1a186ea1102a0a5a9e39d9cac09b2b29ab1598a9b9643f9530093fa492b30926fa902a78ba6f8a9a5897ca884df873108674885645845d68302982431819c980817806007f4c17ec8d7e8117ce3b7c9db78cde788637818f774e575a5a7526c74095729d47290f723cb7038f703796f1b56e7b868c6667b32673b6672e164f4a6395163364622ac6109d5fc545d2e55cfca5bfc15bc515b39159b0a59435593505863957f35570da55c6e55219549cb53d7252a25529a751e4c519365159f50b764f9b84dbcb4d0ec
|8,0=>0x4face4eeb84dd744dc424cef04bdd14bce14b32e4b25649cdb490ed486ec47e57477d6475f4470cf46c5945dd441a7d40f3d40cd540c5b400ad3ffd33dcbe3c66f3c5073b58d3aa783a73d3a58b39fd539d8539609387a83798d35fdb35ce4357623476c33d64314e2310d8303d62fbb92e23a2de482d9852d8da2d6182ce252a5db2a3d829cb62932e28d79279b9278c72759b25aa72540324f7b241f523b7023a2c237f0215ae212d91fba21faf31f42d1f0481e9621e9311d60d1d44d1cc091c0b01bb8d19cb918df5185481809f177fd1718b16a351652a16455163e81617f15eaa15e58155fc14c151316a128e81287511d65119db10cde0ee950e4730e2ad0df3c0c4f60bf350bf210bd5c0b7970a8df0a7500638605f1d05dd405d2c05b9705939056cc043fe03b18027af01dde0196e00f75009230070100678005a0
|8,1=>0xf782cf6970f3fa0f1f2aefb15ef7d2ee447ed6c9ec9e8e8cebe700fe487ae43a3e4300e2a9ce022cde565da6e6d9806d8273d252accacbcc219cb91fcae11c7a76c19f0c064fbe9ecbc810bbe81b84fbb81e4b53c7b47d5b4347b3f63b1d2fb13e1b0a52aeadbadbdcad84cad4caac370aa427a69009f5079e54a9cac098dc398414914248e2038cec38bb338aad48626f84ac2844558443182b5f8262281e8880f08805208048d803288015f7c7f57af577acd078d59786d677ccd7798076416753ce73de67382071dd26fa7d6d2116c93869c0a67258652a86514f64fb562e0062b466210f61de261c60612b860eb360a465f7f45eec75c3855b1e15b0265a95a5831f579d155f3f5509454e6654ca554748545415405a538d252ef2523d2504334fbf7
|9,0=>0xf4da3f4801f29b8f0b04e9fdae2dbbdc5c1da902d732ec9c09c8e55c2ca0c0043bd694b8b7aa1bc79d5639abf79705894f9d9302692a018cfe98cec38c6ff891c686ce0864a481d7280c2b7ea7978406782bf76fdf7485873afa71621698956902167abf6799762b875b5375b1cb5ad9e590df5892557ca756d8056d695665054eb651c9f5123c4f2014c92e4b93a4b885459db42733425cf414ff40d04404563fe4e3c3ab3b7e63937a389b3354923545b324d73225831e4a3124d30a152dd962af2e2ab44286c92559c23e1b227c520f57205401d1f8188e117c7d172e913ad4138e812cc211dc910944101780fd6c0f44b0ed650b30006cb605f3b0551504cad0390f03069
|10,0=>0xe050cca50cc5d3eba90fa74c97d51a5b02e420a2371a02224d1a4340a6d4
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa000000000000000000000000000000015554000000000000000000000000000155555555555400000000000000000002aaa8000000000002aaa80000000000000002aaaaaaa800000000000000000005555000000000000000000000000000055555555000055550000000000000000aaaa000000000000aaaa0000000000000000aaaa0000aaaa00015401540154015401540154015401540154015401540154015401540154015402aaaaaaaaaaaa2222aaaaaaaaaaaa2222aaaaaaaaaaaa22222222222222222225555555555555555555555550000000055555555555555555555555500000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaa0000aaaa0000aaaa00015555555555555401555555555555540155555555555554015401540154015402aaaaaaaaaaaa8282aaaaaaaaaaaa8282aaaaaaaaaaaa82828282828282828285555555555555555555555555555555555555555000000005555555500000000aaaaaaaaaaaaaaaaaaaa0000aaaa0000aaaaaaaaaaaaaaaaaaaa0000aaaa000155555555555554015555555555555401555555555554000154015400000000028282828282828282828282828282828282828282828282828282828282828284444444444444444444444444444444444444444444444444444444444444444
|0,1=>0xaaaa000000000000aaaa000000000000aaaaaaaa0000aaaa000001540154015401540154015401540154015401555555555401540155555400002828282828282828282828282828282828282828282828282828000028280000055005500550055005500550055005500550055005500550055005500000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000154015401540154015401540154015401540154000000000154015400000002a802a802a802a802a802a802a802a802a802a80000000002a802a80000000005555555555555555555555555555555555555555555500005555555555550000000000000000aa00000000000000aa00000000000000aa00aa00aa00aa00aa015555555555555555555555555554000155555555555555555555555555540002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80005555555555550000555555555555000055555555555500005555555555550000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000015555555555555555555555555555555400000000000000000000000000000002aaaaaaaaaaaaaaa80000000000000002aaaaaaaaaaaaaaa80000000000000005555555500000000555555550000000055555555000000005555555500000000
|0,2=>0xaa00aa00aa00aa00aa00aa00aa00aa00220022002200220022002200220000000154015400000154015401540000015401540154000001540154015400000002a802a802a802a802a802a802a802a8000000000000000002a802a802a8000000055005500550055005500550055005500550055005500000055005500550000000000000000aaaa000000000000aaaa0000000000000000aaaaaaaaaaaa000000000000000000015555555555555554000000000000000155555555555400008888888888888888000000000000000088888888888888888888888888880001111111111111111111111111111000011111111111111111111111111110000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaa00000001555400015554000155540001555400015554000155540001555400000002a802a802a802a802a802a802a802a802a802a802a802a802a802a800000000011111111111111111111111111111111111111111111111111111111111100000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000001540154015401540154015401540154015401540154015401540154015400002828000028282828282800002828282828280000282828282828000028280000000000000000000000055550000000000000000555500000000555555550000
|0,3=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0001555555555555555555555555555555554141414141414141414141414141414002a802a80028002802a802a80028002802a802a80028002802a802a8000000055005500550055005500550055005500550055005555555555005500555500000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a02020202020202020202020202020001555555555555555555540001555400015555555400000001555400000000000000000002aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002aaa80000000000000000000000000000000000055555555555555555555555555550000aaaaaaaaaaaaaaaaaaaaaaaa00000000aaaa0000aaaa0000aaaa0000000000000154015401540154015401540154015400440044004400440044004400440002a802a802a802a802a802a802a802a802a802a802a8000002a802a802a800000550055005500550055005500550055005500550055005500550055005500000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aaaaaa00aa00aa00aa00000000000000015554000000000001555400000000000155540000000000000000000000000000000000000002aaaaaaa80002aaa80002aaa80000000000000000505050505050505050500050505000505050505050505050505000505050000
|0,4=>0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00a800a800aa00aa00a800a955555554000000015555555400000001555555540000000155540001555400000002aaa80002aaa8000002a8000002a80002aaa80002aaa8000002a800000000055005500550055005500550055005500550055005500550055000000550000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a0a0a00154015401540154015401540154015401540154015401540154015401400140000000000000000000000000000000000000000000000002aaaaaaaaaaa8000555555555555555500000000000000005555555555555555555555555555000000aa00aa00aa000000aa00aa00aa000000aa00aa00aa000000aa00aa00aa0001555555555555555555555555555555555401540154015401540154015401540000000002aaaaaaa800000002aaaaaaa800000002aaaaaaa8000000000000000111111111111000011111111111100001111111111110000111111111111000000aa00aa00aa00aa00aa00aa00aa00aa002200220022000000220022002200000000000000000000444444444444000000000000000000004444444444440002aaa80002aaaaaaaaaaa80002aaaaaaaaaaa80002aaaaaaaaaaa80002aaa80005555555555555555555555555555555555555555555555555500550055005500
|0,5=>0xaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa000000015555555555555555555555555555555555555555555555554141414141414142aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa222222222222222222222222222222211111111111111111111111111111111111111111111000011111111111100000000000000000000000000000000000000000000aaaaaaaa00000000aaaa0001555555555555555555555555555555540000000155555554000000015554000000000000000000000000000000000002aaaaaaaaaaa80002aaaaaaaaaaa800055555555505050505555555550505050555555555050505055555555505050500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000000000000000000000001555555555554000000000000000000015555555555540002aaaaaaaa22222222aaaaaaaa22222222aaaaaaaa22222222aaaaaaaa22222225555550055555500555555005555550055555500555555005555550055555500aaaaaaaaaaaaaaaaaaaa00aaaaaa00aaaaaaaaaaaaaaaaaaaaaa00aaaaaa00015555555555555555555555555555555555555555515151515555555551515152aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a5454545454545454545454545454545454545454545454545454545454545454
|0,6=>0xaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa0000aaaa00aaaaaa00015555555555555555555555555555555444444444444444444444444444440002aaaaaaaaaaaaaaaaaaaaa802aaaaa802aaaaaaaaaaaaaaaaaaaaa802aaaaa801111111111111111111111111111110011111111111111111111111111111100aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaa00015555555555555555555555555555555444444444444400004444444444440002aaaaaaaaaaaaaaaaaaaaaaaa82828282aaaaaaaaaaaaaaaaaaaaaaaa8282828050505050505050505050505050505050505050505050505000000000000000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aaaaaaaaaa00aa00aa0000000000140014001400140014001400140014001400140014001400140000001400000000282800002828000028280000282800002828000028280000000000000005555555555554444555555555555444455555555555544445555555555554444aaaa8888aaaa8888aaaa8888aaaa8888aaaa8888aaaa8888aaaa8888aaaa88895555555400015555555555540001555555555554000155555555555400000002a82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa802a82aa805555555555555555555555555555555555555555555544445555555555554444
|0,7=>0xaaaaaaaaaaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaa00000000aaaa00000000000000000000000155540001555400000000000000000001555400000002aaaaaaaaaaaaaaa80002aaa80002aaaaaaaaaaaaaaaaaaa80002aaa8000000055555555555555555555555555555555555555555555555555555500555555000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000a0a0a000154015401540154015401540154015400000000000000000154015401540002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa22222222aaaaaaaa22222225500550055005500550055005500550055005500440044005500550044004400aa00aa00aa00aa00aa00aa00aa00aa00aa00aa0000000000aa00aa000000aa000000000014141414000000001414141400000000141414140000000014140002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2222aaaa2222aaaa2222aaaa222555555555555555555555555555555555555555550505050555555555050505000aa00aa00aa00aa00aa00aa00aa00aa00aa00aaaaaa000000aa00aaaaaa00015555555555555555414141414141414155555555555555554141414141414142aaaaaaaaaaaaaaaaaaaaaaaaaaaaa802aaaaaaaaaaaaaaaaaaaaaaaaaaaaa805500550055005500550055005500550055005500555555555500550055505550
|0,8=>0xaaaaaaaaaaaaaa00aaaaaaaaaaaaaa00aaaaaaaaaaaaaa00aaaaaaaaaaaaaa01555555540154015555555554015400015555555401540155555555540154000000000000000000000000000000000002aaaaaaaaaaaaaaaaaaaaaaaa8282828005500550055005500550000005500000055005500550055005500000055000022222222222222222222222222222222222222220000000022222222000000015401540154015401540154015401540154015401555555555401540155555402aaaaaaaaaaaaaaa8000000000002aaaaaaaaaaaaaaa800000000000000000005500550055005500550055005500550055005500555455545500550055545554aaaaaaaaaaaaaaaa00aa00aa00aa00aaaaaaaaaaaaaaaaaa00aa00aa000000000000000000000001555401555554015400000000000000015554015555540002aaaaaaa800000002aaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaaaaaa80000000555500005555000055550000555500005555000055550000000000000000aa00aa00aa00aa00aa000000aa000000aa00aa00aaaaaaaaaa000000aaaa0001555555555401540155555555540154015555555554015401555555555401540002a802a802a802a802a802a802a802a802a802a802a8022002a802a802a80220000000000000000000000005555555500000000000000000000000055550000
|0,9=>0xaaaa0000aaaa0000aaaa000000000000000000000001555555555555555400000000000000015555555400000002aaaaaaaaa2a2a2a2aaaaaaaaa2a2a2a2aaaaaaaaa2a2a2a2aaaaaaaaa2a2a2a000000000000000000000000000000000055005500550055005500000055000000000000000000000000000000000000aaaaaaaaaaaaaaaaaaaa0000aaaa0001555555540000000155555554000000015555555555555555555555555554000002a802a802a802a802a802a802a802a802a802a802a802a80000000000000005550555055505550555055505550555055505550555055505550555055505550aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88000000015151515000000001515151500000000151515150000000015151515000000000000000000000000000000000282828282828282828282828000000055551111555511115555111155551111555511115555000055551111555500000a0a0a0a0a0a0a0a0a0a0a0a000000000a0a0a0a0a0a0a0a0a0a0a0a000000015555555555555555555555555555555414141414141414141414141400000002aaaaaaaaaaaaaaaaa802a802a802a802aaaaaaaaaaaaaaaaa802a802a802a800000555500005555000055000000550000005555000055550000550000005500
|0,10=>0xa0a0a0a000000000a0a0a0a000000000a0a0a0a0000000000000001555555555555555555555555555555540000000151515150000000015151515000000000000000000000000000000002aaaaaaaaaaaaaaaaaaaaaaa80000000505050505050505050505050505050505555555555555555555555555050505000000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000a0a0a0a1540154015401540154015401540154015555555555555555555554015555540000000002aaaaaaa800000002aaa8000000000002aaaaaaa800000002aaa80000055005500550055005500550000000000550055005500550055005500000000aaaa00aaaaaa00aaaaaa00aaaaaa0000aaaa00aaaaaa00aaaaaa00aaaaaa0000000155540001555400015554000000000001555400015554000155540000000000000000000000000000000000000002aaaa2222aaaa2222aaaa2222aaaa222555555550000000055555555000000005555555555554444555555555555444400000000aaaa888800000000aaaa888800000000aaaa888800000000aaaa8888000000000000000000000000000000015555540155555401555554015555540000000002aaaaaaa800000002aaaaaaa800000002aaa8000000000002aaa80000000000055555555000000005050505000000000555555550000000050505050
|0,11=>0xa8a8a8a800000000a8a8a8a8000000000000000000000001555554000000000000000000000000015555540088888888888888888888888888888888888800008888000088880000888800000000000000000000055005500550000000000000000000000550055005500000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa000000000000000155115510000000015511551000000001551155100000000155115512aaa802aaaaa802aaaaa802aaaaa802aaaaa802aaaaa802aaaaa80002aaa80005555555555555555555555555555555500005555000055550000550000005500aaaaaaaaaaaaaaaa00aa00aa00aa0000aaaaaaaaaaaaaaaa00aa00aa00aa000155555555555555555555555555555554000000015555111000000001555511100000000000000000000000000000000000000002aaaa222000000002aaaa22255005500550055005500550055005500550055005000500055005500500050000000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaa0000aaaa0000000000015555555400000001555555540000000151515150000000015151515002a802a802a802a802a802a802a802a802a802a80280028002a802a802800285500550055005500555555555555550055005500550055005555555555555500
|0,12=>0xaa00aa00aa00aa00a000a000a000a000aa00aa00aa00aa00a000a000a000a001500150015001500150015001500150015001500150015001500150015001500000000000000002aa82aa82aa82aa800000000000000002aa82aa82aa82aa81111110011111100111111001111110011111100111111001111110011111100aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88aa88aa88aa88aa88aa88aa88aa880000000000000000000000000000000155115511551155115511551155115512aaaaaaaaaaaaaaaaaa82aa82aa82aa82aaaaaaaaaaaaaaaaaa82aa82aa82aa80055005500550055005500550055005500550000005500000055000000550000aaaaaaaaaaaaaaaaaaaaaaaaaa00aa00aaaaaaaaaaaaaaaaaaaaaaaaaa00aa000000000000000000000000000000000155555555555555555401540154015402aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa55555555554455445555555555445544555555555544554455555555554455440a080a080a080a080a080a080a080a080a080a080a080a080a080a080a080a080000000000000001555555555555540000000000000000015555555555555402aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa802a802aaaaaaaaa802a805050505055555555505050505555555550505050555555555050505050505050
|_,_=>0
def sP:Nat→Nat
|0=>0x8071701000f0415060500111604150a01090415020100110e150a05001204030a01000f0d150a05001108070a01000f0815060109121610070a010908150605001204030a05000f08070a01090f040c0601000d030a05000e0b0a01000d0c0a010004030a050908070a0509080b0a0109040306050008070605000403020100
|1=>0x1a0f04031901000f040c0a01000f100306050012081517010912100c0601001204150a05091104030a050013080b0a01000f08070a05001308150a01091204030601000f1808150a010908070601000f10031705001208150a0509120d030a01000f0415060100111810030a010910030a05001204031701000f10030a050912
|2=>0xa01000f1214271901001311142501002611121808150a01000f1b150a0021111210031701000f12101525001d111210150a24231112101506050011121610150a0109121015002322111208150a00211312140a0100201112101f0a01001112101501001e11121015001d1c11121b030a01000f1210070a0109110f04030100
|3=>0x111210152d0100131104030a0100130f1015001d2c111204150a0500110f2b10150a010011101501282211121015060100111208070a0100130f101500231a1112041501001a110f04030a01000f101519002311120415190100110f2a10151901001308070a01000f1404150a01291110150a28231112140325010013120815
|4=>0x10033111204030a0100133210030601000f12101501241c111210150a0023111204150a0100110f140319010013101519001d131108070a0100133210150a010013311407250100131110152500231112101500301a1112101501282f1112100701002e1112101500231c11121007060100131108151701000f1208150a0021
|5=>0x109110410150a01291110150a0500111238100a0100261108150601000f121610070a01000f14370a0100130415170100110f10030a0109131210150a0030111210150a050911120415060100131110030a05001312041506010011101501283611121015010022111210030a05001210153500231112101534001d11121015
|6=>0x14040301001a131604150a01000f101517050011122a100a0100261214040319010013100701002e131110150a283b1112100b0a0100110f10070a0500131108150a0109131210153400231112100c0a01000f1208150a05001312143a0a0100130d150a0100110f1610153501001308150a0109120a0100263911121810150a
|7=>0x111210153e01001c13111610150a012842121610150a002311120441150a010013111015400a001d11123f101501002c111214100301002c111208150a01090f1210030a01000f121015170100111204150a0500131110150a281d111210153e003d13110415060100110f10030a05000f1210153c0100111238150a01003911
|8=>0x2211121007150a0124111210150a01004d11123f2a10150a010012142a10030a01001210150a001d4c11121b101501004a11121b1501001c1145121007150100221112480410150a010011101534010011124810150a0100131210150a01284711121015460a012811121810150a0124111210150a0021131112101501004443
|9=>0x1000f12100315340100111210153a0a0100131455070a0144111210150a0100110f121810150a012811121410540a0128111210531501001a11121b10150a01241112161015010022111210155001004f11121015340100131112104e150a010011121810150a0100110f144904150a0100111027150a012811121b10150100
|10=>0x1a131145181015015d002c11380410150a0100111455150a015c111214081535010011120410150a01005a115910150a012811120403150a01001345581b150a0057111210030a0100133212561003150a0128123810150a012811120810150a012813121610150a0124111204150a01001132120807150a0100134508150a
|11=>0x5e01001c1112161810150a01001318100a01002611121063150a015c11121462150a0100111210070a010013110f1015610a001d11121859101501001a110810150a012842121b10150a012811121403190100111210270a0100261112164910150a0100126010150a015c111208150a0100130f125f10150a5e001112041501
|12=>0x410031501001a13081501001c11451269101501004a11125f101501003d11123f10153401001112101501006711124b101501004a11122a10153501001112163810150a010013041003151901001314081501002c111210150a001d66111210030a001d1165126410150a015c111210150601001112100715015d002c111015
|13=>0x1d111210150a01001132120810150a0124111210150a016c1112142a08150a0100125808150a3e001310150100442c11121410070a012811126b1003150a0100121455150a016a1112481810150a010011101506010013111210271501001c1112101535010013116210270a0100111210070a010026111208101501004a1112
|14=>0x1311126210070a010011121410630a015c11126910150a0057111210150a0021114512145608070a0100121053150a010011121063150a016a11121027152501001112481007150a01001110150a016e2811122a101501002c11123f10150a001d111216100a01002611121410030a001d11121015170100110f12106d150a00
|15=>0x3e001311146b10030a01001210070a010013113216101501001c1112381810150a01001110030a0100113212161410070a0100130410150a720013681003150a016c1112101570010011124810150a01291112381027150a01001108150a0100133212145604030a010012490810150a0100125808150a005711121415250100
|16=>0x1519010026111210751501002c111208150a01003913121410630a016a1112481410070a010011381007150a0100117110150a0128111214370a0100111218150a010039111252101501004f111210150a002311121b150a010011321204150a0100110f380810150a01001318101501007311121410150a016c1112581b150a
|17=>0x2213111214157801001112101577010011124b101501001c11121404150a01281112101501004a1311125808150a5e0013121410150a00231112101501002211121003150a002311125804150a505d11641810150a015d11101501004a1112101501001a26111210150a002313111210150a001d76111204150a010013110f10
|18=>0x1001311146b08150a0100123f10150a002311121610150a01000f1208150a01001132121015195e010013110810150a01007f12181410630a015d111003150a01007d12101501001a5b111210151901005b1112100315010022111210157201004a11121027150a007b11126b101501007a11126b10152d0100111210150100
|19=>0xa0100391311102715340100111210150a05001112381003150a01001318101501001a131156101501007a11123f10150100221112181015190100131110031525010013121027151901001311820403150a0100131015060100110f126410150100811112161404150a01001314040a010026111210157201001c1312141519
|20=>0x12101501004f11123f101519010011125804150a5e001311101501002e13111214100a0100261112181410030a0100138508150a0100111210150a010913111210030a010026111256101501002c111210150a0500131112101501002e111210150100431112181015340100111210031501001a111210158301001a11120415
|21=>0x197201001310150a0129111210150a8301001112101588010011123810150a0100131110152d01001112141b0a0100261112106f15010087111282040315460100111404630a015d111410270a001d11120410150a0023111210155101004f111210861501001a111214101501004311123f101501001a1112165610150a0128
|22=>0x1314080a0100261112140415190100131110030a01000f1210071501002c131110158a010011121408070a0100133f3810150a0100113f10150a010011121015170100111210150a01001189123f10152501001112560810150a012812181408150a010013141b1501001c111210150100571c111218101535010013111015
|23=>0xa010011120410031501001a111214100a01008c11121041150a010011451210150a01007e111214150a01008b111216561003150a010012163810150a01001112041003151901001112821027150a0100111210150a3e0013116810030a0100130f1210150a0500110f12101517010013111214041501001a13111404030a01
|24=>0x10011121810071501002c111214106d030a01001112161b10150a010011124b10150a5e010011125f10150a010011125808150a3e00111210150a0100901312181455150a010011121810150a015d0011641075150a010011128f1610150a01001112165910150a01001112141027070a010011128e10150a010011128d1015
|25=>0x10150a010011121007150a010013114510150a0100110f1210150a001d1112560810150a01001210150a01009511121094150a010011120810150a010080111208150a0100134512141519010011120410150a01005b11121003150a01007e111210150a01009211121404150a0100441112561015460a01001112601810150a
|26=>0x315460a0100111b150a0100114512185610150a01001112141075630a01001112181410150a015d00111404150a010013111003150a0100139912101598975011121027070a01001184120410150a5e01001311601007150a010011121455070a010011125f10150a010013111210150a015d9611125804150a500011126418
|27=>0x10150a505d11129d10150a50015d11121003150a001d1112380810150a0100111210150a01009c11122a10150a01001112690810150a01001312041027150a0100131118101501001a111210150a010013110f1210150a001d131112161410070a0100111218101519010011129a10150a010011121003150a01001a11120410
|28=>0xa31112107c150a010011121610150a01001312691b10150a01001112641063150a015d111210a2150a01001311181410630a0100111210150a015d00a11110150a0100a0131210150a01009f1112149e150a010011121610150a012811121410070a015d0011180410150a0100131110150a5e00116812590410150a01001158
|29=>0x1311121b1003150a01001312142a10150a0100111210a7150a01001112601063150a01001112161003150a01281112641410070a010011125810150a3e00131110150a0100a613121b10150a01002611126b5610150a01001112041063150a015d11145515970a011112a410150a01001112581b08150a0100111210150a015d
|30=>0x8150a01001145121015460a0100a91112102707150a001d111210150a01006a441112161410150a01001312106f1501001a11121027150a01004c1112145610070a01001112107c03150a01001112161410150a01281112711610150a01001112161003150a0100131210150a01001132124810150a01001112107c150a0100
|31=>0x10011121007150a010013119904150a010013114510150a010039111210631501001a11120810150a01281112ac10150a01001112580815980a0011121b101501001c111210631519010011123f0410150a010011121054070a0100131110150a0100ab1112821003150a0100131210150a01001311321210aa150a01001112
|32=>0x5210150a0100111210150a0100b2111210150100b1111210150a010039131112081007150a0100131b101501001c1311121b10152501001112561003150a0100124b6910150a01001112b010150a01001112100715910a01001310150a010011af121410150a01001132126910150a0100131210150a0100ae1112481410150a
|33=>0x121007150a01005c11126b10150a010011125210150a51010011120410150a720100138510150a0100111204101501001a13111b10152501001311121810150a01005c1112181007150a010013115810150a5e001112041003150a01001304101519010013110810150a01002611121404150a015d00111003150a0100391112
|34=>0x100131210150a0100b611121063150a0144111210150a0100b511123f1810150a010011121015b40100111210270a0100118412145604150a010011126010150a0100111208101501001c11123f1027150a01001112106d27150a01001112106f150a010011121b1007150a01001311145610030a0100125810150a5e001311
|35=>0x131112601410150a01001112101501001a11122a0410150a0100111210150a0100a913121b04150a01001145123f1007150a01001112821003154601001112145910030a010011121410630a015d111210150a0100b8111210150a0100b7111210150a7200136812821007150a01001311146b10150a01001112100315400a
|36=>0x1001112101501001c1311121015250100111210150a01004c11121410030a0100131210150a01007d1112106d150a0100131214150a0100ba11120810150a010013681210150a01005b1112101501001c1112145608150a0100127410150a0100131110031501001a11121003151901001112140415460a01001110b9150a01
|37=>0x1015370a0100111210150a01005c111210150ac00100111210150a0100bf11129d10150a015d11121810150a010013111003150a01004c11125210150a5001001112101525010013111210150a01004c13111210150a0100be111214100a0100bd111210150a0100bc11121810150a0100441112820415460100118f1408150a
|38=>0x121b08150a0100114512c210150a0100111210155001001a1112101519500100111210153a0a0100111214ad150a010011123f10150a010011129d10150a51010011121410150a01005c1112102715910a010013121408150a010013125804150a015d0011c11003150a01001112181410150a010013111027150a0100119912
|39=>0x1210150a01001a1112041015460a010011581015980a001112081054150a0100111210150a50015d111210150a0100114512106315460a01001112107563150a0100111210150a0100c31112181b10150a01001112161027150a010011123f1003150a010011121b1027150a0100111210150a01007f11123f10150a01001311
|40=>0x100111210150a0100ba111210150a5150010011121410150a015d0011121015c60a0100111210150a0100131168121015c50a0100111210150a3e01001311c410150a010011121408150a01001112081015910a010012821015970100111210150a010011681210150a0100131145121007150a015d0011821007150a010011
|41=>0x1546010011121015b30a0100111210150a0100c81112c710150a010011120410150a7201001112160810150a0100111210150a0100931112821063150a01001112041003150a0100111210159891010011121b0810150a010011127410150a0100111210150a0100961112081007150a0100111210150a0100bb11125804150a
|42=>0x121015c90a010011120810150a01001312100315460a010011121810150a010011121015910a0100131210150a0100131199121027150a0100111210150a5e010013111210150a0100a31112641063150a010011121054150a010013111210150a01001199121075150a0100111210150a5e0100111210150a01009011121054
|43=>0x111210150a0100cc11128f1410150a010011121015c90a72010011121063150a015d1112181410150a010011121015980a3e00111210150a0100a01112102703150a01001112ad10150a010011128f10150a01001112690810150a01001112141015460a010011121015cb0a010011121015ca0a010011121027150a01001311
|44=>0x1003150a0100131210150a0100cf11120410150a010013111015989701001112101501001a111210150a0100ce1112101519010011125610150a010011121015cd0a010011120410150a5001001112100715970a0100111210541591010011121015c50a500100111210150a01008b11120810150a3e01001112821015460100
|45=>0x111210150a01008c1112106d150a010011121410150a01001311121015980a500011125510150a3e01001112c110150a010011125810150a3e00111210150a510100111210150a0100a9111210a2150a01001112180410150a010011121015460a5001001112145610150a010011125810150a015d0011121410630a01001112
|46=>0x121015970a010011121003150a0100111210150a010013111210150a0100111210150a3e010011121063150a010011121007150a010011121015460a010011121054150a010011120410150a0100111210150a500100111210150a015d0011121015980a010013111204101501001a1112106d03150a01001112041015190100
|47=>0x10150a010011
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x5aa0285011a80794032a0145007a8029400aa0005
|5,0=>0x3f981f0c0f260763039981c0c0da606a303398190c0c2605e302d98160c0aa6052302798130c0926046302198100c07a603a301b980d0c062602e3015980a0c04a6022300f98070c0326
|6,0=>0x15c38ac5c554e2a4614eb8a59c520c2897141389edc4e8e26d71333897dc4b0e2526125b8911c47ae2367117b88a1c442e21a7109b8831c40ae1fe70fbb87c1c3d2e1e270edb8751c39ae1c670dfb86e1c364c1ab70d238675c32ec19070c4b8609c2f6e17470b6b8599c2bee15870a8b8529c286e13c709ab84b9c24ee120708cb8449c216e1047
|6,1=>0x77ee3b871d8b8ea9c746e39c71cab8e39c70ee38071bcb8dc9c6d6e36471aeb8d59c69ee34871a0b8ce9c666e32c7192b8c7d8630e3117185b0c11c5fae2f67177b8ba1c5c2e2da716a30b35c58ce2bf7
|7,0=>0x2dd416ca0b56e5a382cdc164e0b17058382bdc15ce0ad7056382adc154e0a970543829dc14ce0a570523828dc144e0a170503827e393d209dae4e5826ec1356099b04c5825ec12d6095b04a5824ec1256091b0485823ec11d608db0465822ec1156089b0445821ec10d6085ce426820f4105a081d040681ff40fda07dd03e681ef40f5a079d03c68
|7,1=>0x3dab9eb60f4b079d83cac1e360f0b077d83bac1db60ecb075d83aac1d360e8b073d839ac1cb60e4b071d838ac1c360e0b06fd837ac1bb60dcce6de836bb9b3e0d8f06bf835bc1abe0d4f069f834c39a420d110680833c419c20cd10660832c41945cc930641831cc18c60c530621830cc18460c14e60282fd417ca0bd505e282ed4174a0b9505c28
|7,2=>0x4d5c268e1337099384c5c260e12f8e97484b64259212b9095484a642512127909348496424921239091484864241211f908f574773a39a11bd08d684674231a117ee8b784583a2a21142e8998448c2226110308798438c21a610c308598428c21261084e83a8419420add047081c740a42032100907fc83fa41fb20fc907dc83ea41f320f8907bc8
|7,3=>0x5cec2e56171b0b8585bf3adda16dd0b6775afc2d61d6a2eb4985a0c2ce9d6650b2a859142c6a16250b0a858142bedd5e8eaec8572bab7615aceace856342afa156eeaaf8553c2a7e152f0a8f8543c29fe14f0ea7085344298214b10a5085244290214710a30851442885d434ea1285054280a13f509f284f5ba78e13b709d384e5c270e137709b38
|8,0=>0x6decb6d61b592da486cdcb64e1b170d8296bccb5c61ad12d5f96ab4b53a1a8b2d3e769acb4b25a472d1b86894b42a1a050cf996784b3a219c2ecd98668c332619812cb88658bb2a2593f2c9786474b21658f92c7396354b18658b12c50862443102186f2c2f86134b07658292c0b9601c2fee17e52bea85f0caf6617a30bc895dfcaeda575b2ba58
|8,1=>0x7edc3f4e1f970fc387ddc3ece1f552fa287cd43e465f112f8087bc43dbe5ecd2f5d97aa4bd321e872f3a9798cbca25e3f2f16978743c1a1dfb2ef49775cbb8e1db52ed197644bb021d710eaf97534ba7a1d2d0e8e8742cb9f61ceb0e6d87324b96e5ca70e4a9721438ea1c650e2a87114386a1c232e098700c37e61be12de886efcb75e1b9f0dc69
|8,2=>0x8f9cc7b1e3c731db88e94c726638131b798d7c469e233f119788c74c61662f9317488b64459222b7315478a64450e6277113388954c486623311109884443fe61ed30ee8872cc37621ab10cd88624c2ee616530aa88514426a2123308988404c1e220e1106978304c162209f3047881fc40da605d1026880f44056601b100587fe4bfce5fd70fe38
|8,3=>0x13ab99d14ce666721338889bfccdda66dd136689af44d5a269d1346899ecccd266573323898dc4c4a66133300997c44bc225d112e0896c44b42258f32be995b44ab6654b129d894ac4a32650af27c993a449b5e4cb125d892ac4936248b123c991a448b5e44b121d890ac4836240b11fc9
|9,0=>0xae1c56ea6b6515aa8ad0cd6626b2115888abfcd5de2adf15669aaf4555a2a9b35458a9e4d4d22a5735229a8d4544a2a1515028a7d453ca29d514e28a6ccd342699114bf9a5b4d2ba294b349d8a4ac52326909147c8a3a451ae68c5345a8a28cd126288314398a18c50a6284314198a084d02227ff33f789f7c4f9e27bd33d689e744f16677933b48
|9,1=>0x17179b87c5c1a6dfd16f68b7745b966dbb16d49b6645b122d7916b48b5645a8e6d3536919b444da022cf116708b34459822cb2f6518b253d90a2c7516319b144d8822c2f360f8b034d7fa2bed15ed9af24d7722ba735cb8
|10,0=>0xbbbc5dbe2ecf17607bac45d422e9117408b9c45cc22e5117208
|11,0=>0x177f7
|_,_=>0
def wAt:=mkWire dB 208 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x14130484511104283d14130405512114504c010f4544514130444914130043d111544c501211454410a0f4504c101544449111245445151044841010f44c5012114544114130544514130405510124444915124504c101544845111041028121144841000f44451131404845000f44c5012114405510124283d141304449010f44455131404845000f4504c121144441
|1=>0x80744045114944c521211454411600c44511510458030815444414101c5515101384449011246c2b1013444491600c20553f01c4859081549c07131544449180ac604510074544911154602b121445441000f4504c10154484511104283d141304055101244449010f44455131404845151045445101544049111245445010f44c50121145449180a0485115104003d
|2=>0x1b14c54410411440491413040551211444413f0a0409d031244449040305445101244ccb141384055111245803111442855151040c69040ac40493f0ac485908155482b1051540493f0a06c55101349d17151344449121444c5012114544112034580303104fc2b1b154482111104fc03080744045181146047100744851151052c2b1b0144821111046c2b11124fc2b
|3=>0x64124418d10324504e111244c501211454492701c1c4515124604b040ac48412811c5803081545803151145441040a048411013444493811c205511104401d15124504c121144441040ac4449180ac401d15124fc4b040345445101244851151046028101144851151056c490403854451012448211110458031611c0c411600c20551211444413f00c4859081544441
|4=>0x101546c2b101344449180a010551012444490807440454b0ac6c051208454451012444491b0ac482110684044e11124fc28080744045151246c67041141028101244d61100144449180a0401d15124485a08154444115114602b101144851151049c07071145449151d89c0703124485115104283d141304055111244801180ac401d15124504512144544118114401d
|5=>0x1015454497100c582903104456512148544112034485a031044c5a0815448451208444411b0a054411013444491214454411269444416f1146855040ac48411b0a0404d1112448a11600c2055111049c412701c1c45151244821111049c07101540c4915114283f14130405511124fc030708448551214454411011448051001444491600c44511015454490a0f4504c
|6=>0x121640c4100124484101104000512144005115104fc071b154404d2701c1c4515124404914130444904114102810124544d11124fc4b080744045081545441070804855111041c412710c1c45740044961011046c530411448411413040551012444490815444410415448417100c582911144404d1112420551b0ac482112144485a111449c53101540c49151144451
|7=>0x11124fc07070844855111044451131404845151046c53101544821111044449040a0404980114201e1011454491214454417e114100f10124fc2b102740c494b0ad784112725f007270a41c4515125584911148544111148fc2b1b154404d15105e428105d400490a5bc100e151144049120845803111444841151052c2b105e4044d1301444493f01c604512144fc07
|8=>0x14130405511125882b84104544e11125a82b1244400521510460451007454490419c102810124544d11124fc28102741c45010f44c5012114544103104445504154102b10124fc2b080744045151241055040a048411b0a044551013444491112410281012444551210444490a0f4504c101544449141144055101241045101246c2b11014404d111241028101544049
|9=>0x10125200311594485215114fc4b1b154404d11125ac285612444521510410451210468451a154102b121044049100a454450a1245401101245441151049c070711454493f01c100d11155a82b124440052040ac100d1012458031611c4441040a0100d101244c0511125882b84104544e18114485112144544110804201e101145449000f4504c10154485903104043d
|10=>0x141304449010f44c501211454410a0fc504c101544055101244449151144055101244449120844441040a0405510124444915114504c101544449180ac484510074544915124405512114444112384485a11104220108078404515124615b1214454411b0a06c551208444411600c58470815444411412440551b0ac1045121045441180a01055101244845011141028
|11=>0x1134444910684044e1112440051201444411112644570a1144001121445441141244801151058c49106340055141142851151044852151041c451015454498c1040c2b1115449a6080144441040ac5445101245441030ac44551013844490403c54451012440550400c40491611c0c4111154485a081544441151141028101244c55100a4444901124044e111245445
|12=>0x10440551512441a1011384449105080049010044841011040005121440051151044c43111245449141304055111249c070711454491611c20551110420fb120144441158b4100310124201e15124404e12114444115104102812104100e15114100f101264c490801c444112104005215104504715104401d15124602b100745449030a44455151042055120844441
|13=>0x1511428491811c401d15124200512114444115134404911124102b041544841141304055111249c07151344449111444055151241055040a048419b1040c4b15114102b1511440491012454450a1244c431013444491411c5441101558c4900154504912004544110154404911124284e1511444490a0042805000149c5707114544910124044d111246001100745449
|14=>0x10014482111104418e1500400490346454450a12420551211444410801448211110400491063400555412c542911124540112144544112004401e1512444497210c04450708848551110454410411c40491600c205511104544912004544111124105512104044e0113444491812c1055121044005001240401120054041000149c070312454451612c2055111040d1b
|15=>0x270ac1c45151244452101545449270a40c49151145803111445441160a4205511104484503104445515458404e111244565121485441270a4544d1112444551013444491811c485115106a055080ac444164124418d0015458030310444551215400511510448051001444490815c48451110448211110444521510400551012400491510440010a00694416312c0055
|16=>0x121485441130ac444915124404e101244449102781c45151240055040ac48411600c205511106b405120884441101142805011046c2b12084444100154102812104100d15114404912114542915124417a01134444911154402911124504e1015444490a9b40c4b151146c431208444411003854450a1249c07071145449001485441121144451151046855040ac4841
|17=>0x100745449130144005111244449151144049111241028101246c5712084444110124480115104409e031245445740044961011044146501240401740ac496101104409e151344449111244045151246c2b1013444491b0a04821111045847031044455080144441560a444521510454490a11444491358c400511124504e111244561100144449961254043000144565
|18=>0x106340055046380055121046045100745449740a04961011049c570711454491114848411510451751200454411b0ac482111104409d071145449030a40c49151146855040ac484112154404d11124445211154544110014044d11124600310074544956124445215105404901004044510124444910b341c4715124102b1012444491b0a0404d11124401d151244845
|19=>0x12584400511124102b151144049151141028101244049120a4544115994284e1112449910014454410419c1028101246047041544841100385445111246c430411440490807440451512440291511428491214844551510454011200454419012644570a114451d0a148544101114044e111244855100a444495612444521510444550a1344449a3124418e001559003
|20=>0x101244449270ac0c491511441455012404011b0a0404d111249c2b151344449085482855111041c03101545449560ac4452151040052151044029101242849101142851151046c2b1013444491b0a04821111049c2b07114544910154544511126ec450415c4841030a45445111265c430a004544101138484511104100e1511440491b0ac4821111044045111485441
|21=>0x1b154404d111246c431208444418f11c2851151040401040ac404901004102810124100c15114404910154482211104201d10114544910505404901004600312144544115134284511124405512114444100124484101104411915114284911124485115104544d0a138444908070404515124600310074544901454404e111241142101240401105040049010041055
|22=>0x1104425e0a0054049010044801151044a460a114044e1112429410100404491112608010a10454411110444291110428010a104044e11124404e11124004915124402915124102b1012440490a124280501104285511104004901004404e1112454010a1258c49001565c070a0041045041544841100340c4915114409d03124544513154404d111268445100785449
|23=>0xa004544d1112644050a11448451110454450a124401d15124284511124284e111241c4515124044d11124418e00154418d00154542911124284e111241c0115124044d1112644570a11454290a1241c47151241c2b1512420291110404451012420551110420071110400550a10454451012428050a1144821111044961011054043000144045151241057121044841
|24=>0x15104400500124005515104544511125c82b0111440491112428050a004102b1012429420100410281012444521510446620a01440490100428011512428450a15429410100410031012448051110440290a12550030a154285115105c8290111454010012448511510448050a015c843011140c49151144822111042851151042005111044829151042975001265c4b
|25=>0xa00454451112404490015454490a124285510124040100124280511124102b101240c29151141028101240c2b1511550450a15440551112428050001440010112441190a1244805011054049010040c4311155504b0a1541055121042849010044452
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x10800000000000000000000000000000000000000000000000000000000000000000000000000000000220004
|6,0=>0x1a203310000000017280000000000000002a4000000000000264000000000000000000000000000000000000000000000000000000000224000000000000000000008440e28000000000000ba80000000000000001430000000000000000000000000001040000000000000000000000000000c4
|6,1=>0x2ba80000000000000000000a4a1354000000009280000000000009020000000000008880000000000000000000000041307a800000000000000000001ca000000000e040000000
|7,0=>0x1de63b847520e821ca638c870180001bc436cc6ba0d521a2833500000000196400006418000188830105e2000017082d4c58a000015a8000054a0a63000028cc50189d313462590000093311e8230c000089310e4000041a08120fc6000000007a40ee61d0c000070400001b1035106730000190c30205c4
|7,1=>0x5e0cba9800000005c8cb8116c400005a88b4100000000591000016130000575000015942ae454d0a7a00000000530c00014a228c80000a120000000000009f993c3270800009b1133326064b8800012b324e848d090191d3234646448aa112321e6434884a10540000408c8010fe21f663e0c7a98f23
|7,2=>0x42068310000209340e480d0ffa00003f687dd0f9a1f033d887a88f3980000000790cf099dd43b467644eb19d2439c87344e4a1c633884704c0001be337486dcc000000036866c4cd719ab300006a48000000034c66944d0a19e333660000cc1994432446408c6998b200000000c41985330285f8c00017b3
|7,3=>0x57c6ae915b9ab435608ab895522a64544800014f229b352e800014a1a9045188a289432000050669fd13e1a7b100009dd139a27124da89a51331a6244be6000000025c34b26958c00025334a24938d26124a248c890cd209000047a88e511aa232345e6000116922a344c88909109800043a8868d0b22133
|8,0=>0x6ea6dc8db79b6c36d26d98db19b6036ba6d68dac135536a46d3cda61b49368c6d0cda01b3d36746cdcd9a1b31365c6cacd941b2536446c7cd8e931a362e6c549899310361a6c2c984930636066c00d7f12fb35f06bd4d791aef35d86ba4d7392e435c26b78d6d9ad835ac4b4cd681acd35946b1cd621ac13
|8,1=>0x86470bce161c29384c708ce101c1d3834705ce0a1c11381c702ce041c0628067000dfe9bfa37ee6fd0df89bee37d66fa0df29be237be6f70dec9bd637a66f40de69bcb27924f18de19bc0377a6ee8ddb9bb437626eb8dd59ba8374a6e88dcf9b9c37326e58dc99b90371a6e28dc39b8437026df8dbd9b783
|8,2=>0x9dc73ace741ce539c4737ce6e1cd939ac734ce681ccd3994731ce621cc1397c72ece5c1cb5396472bce561ca9394c728ce501c9d3934725ce4a1c91391e5230e449c8639067204a3f1c7b38f071d4e391c6f38d871a4e331c6338c07174e2d1c5738a87148a279c4c3892711ca221c41387c70ece1c1c353
|8,3=>0x58c3b127618ec19d803afa75e8ebb9d743ae275b8eb59d683aca7588eaf9d5c3ab27558ea99d503a9a7528ea39d443a8274f8e9d9d383a6a74c8e979d2c3a52749ca921d213a3c746ce8c1d153a24743ce861d093a0c740ce801cfd39f473dce7a1cf13
|9,0=>0xc1a582cb0496072c0a580cb0095ff2bfa57ecafc95f72bea57ccaf895ef2bda57acaf495e72bca578caf095df2bba576caec95d72baa574cae895cf2b9a572cae495c72b8a570cae095bf2b7a56ecadc95b72b6a56ccad895af2b5a56acad495a72b4a568cad0959f2b3a566cacc95972b2a564cac8958f2
|9,1=>0x65f2cba596cb2c96572caa594cb28964f2c9a592cb2496472c8a590cb20963f2c7a58ecb1c96372c6a58ccb18962f2c5a58acb1496272c4a588cb10961f2c3a586cb0c96172c2a584cb08960f2
|10,0=>0xcd639a873488000cd0399c7330e651cc8398c7310e611
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x150000000000002980000000000052000000000000a00000000000013c0000000000026000000000000480000000000008e000000000001140000000000020000000000000200000000000003e00000000000060000000000000980000000000012800000000000200000000000003c00000000000058000000000000a00000000000012000000000000220000000000004000000000000070000000000000c00000000000014000000000000200000000000003000000000000040000000000000600000000000008000000000000080000000000000
|1=>0xc340000000000184c00000000003010000000000042200000000000840000000000010200000000000186000000000003060000000000060000000000000bf800000000001510000000000024e000000000004880000000000083800000000001040000000000020600000000000400000000000006f800000000000d0000000000001400000000000027e000000000004480000000000085000000000001080000000000020c00000000000410000000000008100000000000100000000000001fc00000000000380000000000005f000000000000b6
|2=>0x877e000000000107fc00000000020df8000000000419f0000000000832e0000000001043c00000000020800000000000409e0000000000810000000000010040000000000200400000000004004000000000080000000000000c0000000000001526000000000010220000000000203c0000000000400000000000006ff80000000000ca00000000000161800000000002858000000000050700000000000a040000000000117c0000000000224000000000004030000000000080400000000000ffe00000000001c1800000000003270000000000061e
|3=>0x2005c8000000004007f8000000008005f0000000010009000000000200008000000004000080000000042000000000000502360000000008000e00000000100004000000001a457000000000341bf00000000060c3c000000000c0078000000001800b8000000003001000000000060000000000000906fc00000000120df0000000001477f000000000283fe00000000040220000000000800f0000000001000000000000010000000000000186f400000000028ff8000000000501c00000000009bfe000000000127f800000000023ff800000000043ff
|4=>0x8033b80000000081080000000001000400000000011089e0000000022035c000000004402b80000000082adf8000000010493f00000000208b7e0000000041167c0000000082205000000001043ff0000000020877e00000000410ef800000000820ff800000001041bf00000000202974000000004027fc000000008044e0000000010089a0000000020112c0000000040221800000000804400000000010080b0000000020100e00000000402008000000008021e0000000010042e000000002008540000000040103800000000801ff800000001003e0
|5=>0x1000877e000000200018540000004000309800000080002010000000c0883fe000000181017fc00000020020df8000000204061300000004060020000000080010040000000a0250c0000000140189c0000000220937e000000044124fc000000084200a000000010108ae00000002009b7c00000004012e7c00000008024ff800000010049bf00000002001b7e0000000400285000000008000500000000100009600000002000000000000038022800000000500002000000008040000000000080a3fe0000000101477c0000000201d6e000000004032dd
|6=>0x10100a17400000200a120500000040100002000000800051b80000008004031000000100012e7c00000200024cf800000400041ff000000800083be000001000102fc0000020000081000000400000a000000080000000000000b8810ad4000001310205a800000260040bd0000004000837e00000078100a00000000e0020df800000160401b70000002c00017e000000501106fc000000a0020df800000100100af0000002000876e000000400106fc000000702217f8000000c0406ff0000001008002200000020100004000000401239f8000000800477f
|7=>0x200000024000004000000448000044060205f000008802849bd0000110000877a000022000106fc00004220020df800008400041ff0000105840856e000020b00106fc00004120020df8000080e2042bf0000100c40837e000020028122f800004004024ff800008004041bf0000100010837e000020000146fc0000200000000000002120004150000041808837e0000082800000800001040200008000020004001500000290008c7e000004000116fc00000800004510000010000060e0000020000001000000204a126fc000004070200600000080c0400c
|8=>0x2200000a3be000420038102f400084005020df80010080c051bf0002010180837e000400030106fc000800040285c800100008041bf0002000000a37e0002800000844800044220021df800088040041bf0001020000404400020110010cd8000402200209f8000804010010000010080000200000200004106fc0002084020001000041000045b70000820000097e000100501106fc000200802000b0000401004001500008008088bee0000c4000097ec00010008020df800010001041ff00002000200a64000040000107fc0000800000a850000100000050a
|9=>0x2020c000837e004041000106fc008002200209f801000400041ff0020008000837e004000004107fc00800000020ff801000000002020010100800837e0010c0004007ec002080000008d000401000041bf00080000000240000c2201010ef400184400021df800308082043ff000410014087fe00082002810ff400104000028df800200480043bf0004008000073a00080020010ffc00100040021df80020008000201000400009000200008000120001000100000035ef8002000000639f0004000000c33e0008000001683000100000021ff800200000043bf
|10=>0x20800800402140400400000048008008000000890100100000010a020000002083dc024450000106fc04884000020ff809044400041f700b0108800837e015004100106fc02840200020df804880240041bf0090000800817e010200500106fc020000200205f802420001041bf00484000200218009004000000a0010080000009900200041020180003230800083fe005044000107fc00a08800002ff801410040041ff002820000003f6005001040127fc0089c000030ff801108800041bf0020600200837e0040a1040127fc00810008020df801020010005bb
|11=>0x2404001000000848000000000054800201310205e9000402020401419a0004800837e330000900106fc62800120020df8810004420c1ff1012510000837e200001048327b830080114020df854000100041bf0a002200008a7e105000100107fc20808020022ff841000240041bf0804105800877e100400880106fc20024024020df840002120045bf08000204008b7e10000078000afc20000090020df840000020041bf0400100800837e05620000010efc0ac40000020df815400440041ff0230a80000837e0460a1040127fc08c08000020df8104004402417f
|12=>0x4c1010048041ff902020000083ff204000000306fd068c0030020dfa09804000041bf41202200008bfe824021000106fd04800200020d39202080c0041bf
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x10000000000000000000000000000000000000000000000000802
|6,0=>0x28000000000001006000001b800000017800000002000000000000001601000000000000100000054000000000082f000001a0000000000700000002400000000000000000000000000000000000d000000000000bc3c00000003c0000000003b00000000000000000200000000000000000c
|7,0=>0x4040037810a60700004f2003435000100004c009d010204600000100006530001a00000000c101580004041b9100024110e448060c8bc0e241d1d81c0300068040101014483d3da9cda02053a40a00020040a0103814004e29800f4000682c184e238082468108004c1c00058020602030001012808000203000b248010000017120900008001551216000915208
|7,1=>0x29600c2440008647d038009802548000c1c228c44a00031980ad30001c50020389d9c540200000020e218001c52818043a02818040004830222c01000081007829c60016818183c120b8004601158ba002b81c0ea402ad8040000008a659120540c5b1499c18066e80800026902c0000030100a02000100000013b43602120000436050dc049e000002c02041f0a402
|8,0=>0xa8ac959766d174ff49785741f045a4412a70464f5fe6989a22988b329ae9c4a204e57887844795602385aab0c95ab2e768e58c268ebe85bed58924c2e882df3c346f89607cecbcde4239c429646b0522d513a84e0ec5c180553f41b821b0791341eec327978b8b05617c089f370cc04ac38c3dd242a7aa24d2d795017ac47436cd4859e3bc715b2817d8e8a0d0c2bd19
|8,1=>0x34100d424e60faaa73532ea4d5e5ebf0fa06627a4e07f33562e5dcf6be90dfd2891c02690c6c2decd5f6b976047e2fcdb026448be0eb2e6b17625017555c128128b941c696641672dcae1ce2cc9643343e5d479c9d6d90ed367a494db84ee6bbfcc9cd2b28b09c8fd40c901cc507602cf374113497254d49db10678009f8f54e4d5405e
|9,0=>0x18796542533a9f17af36db3476ea90a4302a87479b29214490cf9f3702e9d30d6fc1cfaf52078d96ad60bbda4d9887d25d5964714470b5a4ccf95b0e30d163e978e326154aa5db23741aab9ae36298acd59744a4f95d2f7a98d7f30c15d577438bdee35635650ac317515aee7578ade28d6e51d4ad984
|10,0=>0xaca40ba5a8c319cd14b94a99f68
|11,0=>0x5d
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 55 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_252 9 roots_252 ops++addP pm 1 dom_238 9 roots_238 ops++addP pm 2 dom_222 9 roots_222 ops++addP pm 3 dom_190 9 roots_190 ops++addP pm 4 dom_126 9 roots_126 ops++addP pm 5 dom_234 8 roots_234 ops++addP pm 6 dzo_86_8 5 roots_86 ops++addP pm 7 dom_188 8 roots_188 ops++addP pm 8 dom_246 9 roots_246 ops++addP pm 9 dom_86 5 roots_86 ops++addP pm 10 dom_110 6 roots_110 ops++addP pm 11 dom_158 6 roots_158 ops++addP pm 12 dom_62 5 roots_62 ops++addP pm 13 dom_54 4 roots_54 ops++addP pm 14 dom_250 9 roots_250 ops++addP pm 15 dom_210 5 roots_210 ops++addP pm 16 dom_206 5 roots_206 ops++addP pm 17 dom_198 4 roots_198 ops++addP pm 18 dom_204 4 roots_204 ops++addP pm 19 dom_154 4 roots_154 ops++addP pm 20 dom_174 6 roots_174 ops++addP pm 21 dom_218 7 roots_218 ops++addP pm 22 dom_58 4 roots_58 ops++addP pm 23 dom_122 7 roots_122 ops++addP pm 24 dom_150 5 roots_150 ops++addP pm 25 dom_124 7 roots_124 ops++addP pm 26 dzo_212_8 5 roots_212 ops++addP pm 27 dom_84 4 roots_84 ops++addP pm 28 dom_236 6 roots_236 ops++addP pm 29 dom_248 6 roots_248 ops++addP pm 30 dzo_214_8 6 roots_214 ops++addP pm 31 dom_186 6 roots_186 ops++addP pm 32 dom_102 5 roots_102 ops++addP pm 33 dom_108 4 roots_108 ops++addP pm 34 dom_212 5 roots_212 ops++addP pm 35 dzo_210_8 5 roots_210 ops++addP pm 36 dzo_118_8 6 roots_118 ops++addP pm 37 dom_182 6 roots_182 ops++addP pm 38 dom_220 7 roots_220 ops++addP pm 39 dom_118 7 roots_118 ops++addP pm 40 dzo_114_8 5 roots_114 ops++addP pm 41 dom_82 4 roots_82 ops++addP pm 42 dom_230 6 roots_230 ops++addP pm 43 dzo_242_8 6 roots_242 ops++addP pm 44 dzo_246_8 7 roots_246 ops++addP pm 45 dom_166 4 roots_166 ops++addP pm 46 dzo_244_8 6 roots_244 ops++addP pm 47 dom_244 6 roots_244 ops++addP pm 48 dom_214 7 roots_214 ops++addP pm 49 dom_120 4 roots_120 ops++addP pm 50 dzo_116_8 5 roots_116 ops++addP pm 51 dom_242 6 roots_242 ops++addP pm 52 dom_216 4 roots_216 ops++addP pm 53 dom_116 5 roots_116 ops++addP pm 54 dom_114 5 roots_114 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_86_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_212_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_214_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_210_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_118_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_114_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_zo_242_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_zo_246_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_zo_244_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_zo_116_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h52;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h53;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h54;exact cpcs (by decide +kernel) lowS_114 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 9 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 10 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 35 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 102 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 102 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 256 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 245 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 117 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 245 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 105 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 105 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 12 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 12 0 = true)
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
def dzo_47_16:=0xffff0000ffff0000
def gzo_47_16:=0xfffe0000fefc0000
def gsh_47_16:=0xfffe0000fefc
theorem lowS_zo_47_16_41:Lower true dzo_47_16 roots_47 gzo_47_16 6:=lower_iso_b (d1:=dom_47) (r1:=roots_47) (T1:=gsh_47_16) [(dom_47,16)] (by decide +kernel) (lower_slice_b (T:=gsh_47_16) [(0xcccc0000cccc,0,2),(0xf0f00000f0f0,0,4)] (by decide +kernel) lowS_41)
def dzo_119_8:=0xff00ff00ff00ff00ff00ff00ff00ff00
def gzo_119_8:=0xff00ff00ff00fe00ff00ff00fe00aa00
def gsh_119_8:=0xff00ff00ff00fe00ff00ff00fe00aa
theorem lowS_zo_119_8_86:Lower true dzo_119_8 roots_119 gzo_119_8 7:=lower_iso_b (d1:=dom_119) (r1:=roots_119) (T1:=gsh_119_8) [(dom_119,8)] (by decide +kernel) (lower_slice_b (T:=gsh_119_8) [(0xaa00aa00aa00aa00aa00aa00aa00aa,0,1),(0xff00ff0000000000ff00ff00000000,0,32)] (by decide +kernel) lowS_86)
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000ffff0000fffe0000fefc0000
def gsh_111_16:=0xffff0000ffff0000fffe0000fefc
theorem lowS_zo_111_16_41:Lower true dzo_111_16 roots_111 gzo_111_16 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xcccc0000cccc0000cccc0000cccc,0,2),(0xf0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff0000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_205_2:=0xcccc000000000000cccc000000000000cccc000000000000cccc
def gzo_205_2:=0xcccc000000000000ccc8000000000000cccc0000000000008800
def gsh_205_2:=0x3333000000000000333200000000000033330000000000002200
theorem lowS_zo_205_2_141:Lower true dzo_205_2 roots_205 gzo_205_2 6:=lower_iso_b (d1:=dom_205) (r1:=roots_205) (T1:=gsh_205_2) [(dom_205,2)] (by decide +kernel) (lower_slice_b (T:=gsh_205_2) [(0x3333000000000000000000000000000033330000000000000000,0,64)] (by decide +kernel) lowS_141)
def dzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def gzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000fffe0000fefc0000
def gsh_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000fffe0000fefc
theorem lowS_zo_239_16_41:Lower true dzo_239_16 roots_239 gzo_239_16 8:=lower_iso_b (d1:=dom_239) (r1:=roots_239) (T1:=gsh_239_16) [(dom_239,16)] (by decide +kernel) (lower_slice_b (T:=gsh_239_16) [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,0,2),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,0,64),(0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_175_16:=0xffff0000ffff00000000000000000000ffff0000ffff0000
def gzo_175_16:=0xffff0000ffff00000000000000000000fffe0000fefc0000
def gsh_175_16:=0xffff0000ffff00000000000000000000fffe0000fefc
theorem lowS_zo_175_16_41:Lower true dzo_175_16 roots_175 gzo_175_16 7:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_16) [(dom_175,16)] (by decide +kernel) (lower_slice_b (T:=gsh_175_16) [(0xcccc0000cccc00000000000000000000cccc0000cccc,0,2),(0xf0f00000f0f000000000000000000000f0f00000f0f0,0,4),(0xffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_171_4:=0xf0f00000f0f000000000000000000000f0f00000f0f0
def gzo_171_4:=0xf0f00000f0f000000000000000000000f0e00000a000
def gsh_171_4:=0xf0f00000f0f000000000000000000000f0e00000a00
theorem lowS_zo_171_4_43:Lower true dzo_171_4 roots_171 gzo_171_4 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_4) [(dom_171,4)] (by decide +kernel) (lower_slice_b (T:=gsh_171_4) [(0xf0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_43)
def dzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def gzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fe00ff00ff00fe00aa00
def gsh_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fe00ff00ff00fe00aa
theorem lowS_zo_247_8_86:Lower true dzo_247_8 roots_247 gzo_247_8 8:=lower_iso_b (d1:=dom_247) (r1:=roots_247) (T1:=gsh_247_8) [(dom_247,8)] (by decide +kernel) (lower_slice_b (T:=gsh_247_8) [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,0,1),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000,0,32),(0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_86)
def dzo_59_4:=0xf0f0f0f0f0f0f0f0
def gzo_59_4:=0xf0f0f0e0f0f0a000
def gsh_59_4:=0xf0f0f0e0f0f0a00
theorem lowS_zo_59_4_43:Lower true dzo_59_4 roots_59 gzo_59_4 6:=lower_iso_b (d1:=dom_59) (r1:=roots_59) (T1:=gsh_59_4) [(dom_59,4)] (by decide +kernel) (lower_slice_b (T:=gsh_59_4) [(0xf0f00000f0f0000,0,16)] (by decide +kernel) lowS_43)
def dzo_173_16:=0x333300003333000000000000000000003333000033330000
def gzo_173_16:=0x333300003333000000000000000000003332000032300000
def gsh_173_16:=0x33330000333300000000000000000000333200003230
theorem lowS_zo_173_16_41:Lower true dzo_173_16 roots_173 gzo_173_16 6:=lower_iso_b (d1:=dom_173) (r1:=roots_173) (T1:=gsh_173_16) [(dom_173,16)] (by decide +kernel) (lower_slice_b (T:=gsh_173_16) [(0x30300000303000000000000000000000303000003030,0,4),(0x33330000333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,28),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,18),(16,20),(16,80),(16,144),(17,19),(17,21),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,96),(32,160),(36,37),(36,38),(36,44),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,68),(64,80),(64,96),(72,73),(72,74),(72,76),(72,88),(72,104),(72,200),(128,129),(128,132),(128,136),(128,144),(128,160),(130,131),(130,134),(130,138),(130,146),(130,162),(130,194),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|6=>2
|7=>14
|8=>81
|9=>225
|10=>228
|11=>73
|12=>10
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xc299443b0e
|7,0=>0xe877fdf595d0194bbb32a73c2986ec9841c95729927cd907dc7642d4b0d7355472b1ea
|8,0=>0xffb96fd270fc643f9310f6504f2dbcefc3eec036e86bde8371e627ae125adfdb0dcba5dc1d2d8f2dd313cd12edd1015c8861c38f1bdafabd367bbf0bbbef5ba219b04a8afb03ad4e5acb40a9be4a973c9c0dc9a0f494eec91c968ecd38e1e9874b384884821fa7e6867dc0e7a5fd788cb7870e6f22962e935e64c5cd4057629567e4512f54fc764f3144cae04412241c01416ea408e63f17f38661385092c56029d14293ca2492021b422178a1d2181b3361b066183731828e17fbe155900fff80d21208730052cc01ac4
|9,0=>0x8a03c88a038257781e2680b517feba7eb147a299786ac774f57733d76aa075a6374f8574bd674afc748b073e8371e1c711377102670e27701166f8cf6cb356c5176be076af206a12067ff46672b6601f61db360bd65fcb85ee1c5cbe95bd745bb775a44758b0158acf5850a580cd57bf6573a0572af56f3b558915557354c2a53c275226350b09502c54fa2b4e1ca4c8ae4c5de4c2c14bfe749082475a946b7b4600f45ddd44dd2444eb3f16b3eb3f3bcf3398fe3814c37cc337a213775136a5d34a5e330f23274d31b293012f3004a2f78a2f6a52cff32cc6a29b7527bb7271f926c0a24b0a2425e210b11d9711cd271c9b318ec718af5189c8186d117eed1689e1583214919141c3134b612dad12af9124a111d52117b00ebbc0d6190c5b80a0fd096380705505ffa0569e055a504b6303d7b0333702cb0029c20200700841
|9,1=>0xfdd0bfb341f9d69f9500f9247f71c7f5d07f4363f211af18e8f10f2f08b8f06deef87bed80bea553e9134e8838e6347e3cb8e26afe1296dcc66db0e3daecbd93a0d90a9d8d19d7d42d7bc7d7861d4de4d44b2d2711d2181cf027cefd0cef19cea03c9361c6256c5562c5395c484bc13bac0b53bf6c5bf2c3bf11bbe71fbd81dbd4e2baff7b965cb78f3b49bab2715b1e92b150bb140fb0f6aaf752af1aaac102ac014abf2faa799a90ada8026a7d14a60eaa413ca3a82a38bda14cba01439cbc49bc4c9ad0e9ab0599c24998f89957f994109923d990b2965bc9627a95a9d94dac93dd2939e590b0c8dfc38ded08d9e48d34b
|10,0=>0x8c6148a89987dca86dab84e65838de8368280c047f8227e8487cb2d7b5077b274787af7826274a3870f4970c956f2276f00d6ec216e10f6cd326bff9691036719c66f8d6629b64b6f6466a63cc5636d8625e861c9c615ae613a5604c45e9c05ce5c5bca35b22a5a98c5a39a5987358a75583a855fef53baa53855532ea503904f7dd4f7654f2a34ee384c81a4be754b00a4a613486c6477f04759f4399542a574174b40dbf4008f3dea83ce9b3ccfe3c85f3b8253b6ef3b6753b47639419382093572d3535f34d883413e339973364a3351732a913239c322b72f2142e43c2b59b2ab05267e8243742417823e8f2387e2331e2285f21be31fe931f5c51dc5f1cab51bbf41b3c418b70187ed18068177ea15e1012126111801065e0fcd50dbe10d4c80be020b9450b8c70b2520ac370794e0777506d6702f54009af008b700253
|10,1=>0xfe2c0fd981fbc1dfb2fefa340f86adf7ef6f661af2de1f204cf11a2f091deefb7ed4aaeace5e7e2ae7951e718ae3820e0f36e0778e0722e054fdf395dd58cdbb13db837da826d9fafd8f88d87d1d77fcd719dd6a71d6871d4a4bd45cdd37c9cf896cf14bcf125cdf9acda86cb895cb403c86ffc5122c377cc1800c0e19c0ad7bea0ebe551bde6fbba8db960ab7931b7362b6279b5fd8b51cdb40abb3b7cb3b16b2994b2125b158ab1432b0d45b0996add82ad9d3ab270aa914a8a37a7754a60e1a4f15a4dfba2367a1d56a1a7a9f4339ec4a9d31b9c5a59c1349b6849b5f19ad309a3589890d983b09475094217935c5915e3903948fc018d0ef
|11,0=>0xfd2f7fd1ddf8e3af8a8bf7f3ef2f5cecb32e469ae178ddd90fdb393d8230cf279ce015cb2c7c7aa2c3e3fc1b85c00dcbc505b6b15a763da4cc5a4803a36dca26869b4f297a6396f2d7e9c37707776ca56e3d66c4d76bd976b3706afc166b74668d7642dc5cbf95a18058c9957fb95631b51a4a4ea874ba7e47d6c44cc4433cd3799a35a80348f5343e131fd22bfee2b8302777424a6b1f2b11884614d98130ba0c8b809e0809463092f707de907c2805d8e055e901f4c
|12,0=>0xfff0bdd9d2c33a399b3f9892d8fd7c792e461e180eef70c075
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffff0000ffffffffffff0000ffffffffffff00000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00ff00ff00aa00aa00ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaaaaaaaaaaaaaaaaa00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00ff00ff00aa00aaffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
|0,1=>0x3333333333333333333300333333003333333333333333333333003333330000ffffffffffffffffffffffffffffffffffffffffffffaaaaffffffffaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000ffffffffffffffaaffffffffffffffaaffffffffffffffaaffaaffaaffaaffaa55555555555555555555555555555555555555555555555555555555550055003333333333333333333333333333333333333333333333333333333333330000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff0000000000ff00ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa00aa00aa00aa00aaffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000
|0,2=>0x555555555500555555555555550055555555555555005555555555555500550033333333333333333333000033330000333333333333333333333333333333000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ff00ff00ff00ff00ffffffffffffccccffffffffffffccccffffffffffffcccccccccccccccccccc00000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000ff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000ff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff00000000000000000000ffffffffffffffff0000000000000000ffffffffffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000
|0,3=>0xffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00000000000000000000ffff00ffffff00ff0000000000000000ffff00ffffff000000000000000000000000000000000000ffffffffff00ff00ffffffffff00ff000000000055555555000000005555555500000000555555550000000055005500ffffffffffff0000ffffffffffff0000ffffffffffff0000ff00ff00ff0000000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff00fffffffffffff0f0fffffffffffff0f0fffffffffffff0f0f0f0f0f0f0f0f0f0ffffffffff00ff00ffffffffff00ff00ffffffffff00ff000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffff0f0fff0ffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00ffffffff00000000ffffff0000000000ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff000000000000000000ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff000000000000000000ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff00000000
|0,4=>0xffffffff00000000ffffff0000000000000000000000ffff0000ffff00000000000000000000ffff00000000ff00ff00ff00ff00ff00ffffff00ffffff00ff00ff00ff00ff00ffffff00ff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00000000000000000000000000000000000000ffff0000ff000000ffff0000ff0000000000000000000000000000000000000000000000000000000000ffffff00ffffffffffffffffffffffffffffffff000000000000000000000000ffffff005555555555555555555555555555555555555555555555555555555555555500ffffff00ffffff00ffffff00ffffff00ffffff0000000000ffffff0000000000ffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000000000000f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f0f0f0f0f0f0f0f0f000f0f0f0000ffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff000000003333333333333333333333333333333333333333333333333333333333333300000000000000000000000000000000000000000000000000ffffffffff00ff00ffffffffffffffffffffffffffffffff0000000000000000ffffffffff00ff00
|0,5=>0xff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000000000000000000000000000000000ffffff00ffffff00ffffff00ffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f000000000000000000000000000000000000000000ffffff0000000000ffffff00000000000000000000ff00ff00ff00ff000000000000000000ff00ff00000000ffff0000ffff0000ffff00ffffff00ffffff0000ffff0000ffff00ffffff00000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffff00ffff0000ffff0000ffff0000ffff0000ffffffffffffff00ffffffffffffff000000000000000000ffff0000ffff00000000000000000000ffffffffffffff0000000000ffffffff00000000ffffff0000000000ffffffff00000000ffffff00ffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff0000000000
|0,6=>0xffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff0000000000000000000000ffff0000ffff00000000000000000000ffff0000ff003333333333333333333333333333330033333333333333333333333333333300000000000000ff00000000000000ff00000000000000ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000ffffffffffffffffffffffffffffffff0000000000000000ffffffffffff00000000000000000000ffffffffffff00000000000000000000ffffffffffff000000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00ff00ff0000ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff0000000000000000ffff000000000000ffff000000000000ffff000000000000ff000000000000000000ffffffffffffffff0000000000000000ffffffffff00ff00ffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffff00ffffffffffffffffffffffffffffffff00ff00ff00ff000000ff00ff00ff00000000000000000000ffffffffff00ff000000000000000000ffffffffff00ff00ffff0000ffff0000ffffffffffffff00ffff0000ffff0000ffffffffffffff00
|0,7=>0xff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000000000000000000000000000000000000000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ff00ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ff00000000000000000000000000000000000000000000000000ffffffffffffff00ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff000000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff0000f0f0f0f0f0f0f0f0f0f0fffff0f0fff0f0f0f0f0f0f0f0f0f0f0fffff0f0fff0ffff0000ffff00ffffff0000ffff00ffffff0000ffff00ff0000000000000000ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ff0000000000000000000000ffff0000ff0000000000000000000000ffff0000ff00ffffffffffffffffffffffffffffffff00000000000000000000ffff0000ff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffff00000000000000000000ffff000000000000ffff000000000000ffff0000000000000000ff00ff00ff00ffffff00ff00ff00ffffff00ff00ff00ffffff00ff00ff00ff0000000000000000000000000000000000ffff0000ffff0000ffffffffffffff00
|0,8=>0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffff0000ff000000ffffffffffffffff00ff00ff00ff0000ffffffffffffffff00ff00ff00ff0000ffff00ffffff00ffffff00ffffff00ffffff00ffffff0000ffff00ffffff000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000ffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffff000000000000ffffffff00000000ffffffff00000000ffffffff00000000000000000f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffff00ffffffffffffffff0000000000000000ffffffffffffffff0000ffff0000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff0000ffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff0000ffffffffffffffff0000ffff0000ff00ffffffffffffffff0000ffff0000ff00ffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ff000000000000000000000000000000000000000000000000000000ffff0000ff00ffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffffff00ffffffffffffffffffffff00ffffff00ffffffffffffffffffffff0000000000
|0,9=>0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00000000000000000000000000ffffffff000000000000000000000000ffffff00ffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff000000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffff0033333333333333333333333333330000333333333333333333333333333300000000000000000000ffffffffffffff000000000000000000ffffffffffffff00ffffffffffffffffffffffffffffffff0000000000000000ffffffffffffff0000000000000000000000000000000000ffffffffffffff00ffffffffffffff00ffffffffffffffff0000000000000000ffffffffffffffffffffffffffff000000000000000000000000000000000000ffffffffffff0000ffffffffffff000033333333333333330000000000000000333333333333333333333333333300000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000000000ffff0000ffff00ffffff0000ffff00ffffff0000ffff00ffffff0000ffff0000ff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ff00ff00ff00ffff0000ff000000ffff0000ff000000ffff0000ff000000ffffffffff00ff00
|0,10=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00000000ffffffffffffffffffffffffffffffff00000000ffffff0000000000ffffff000000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff00ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ff00ffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00000000ffff0000ffff000000ff000000ff0000ffff0000ffff000000ff0000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffff00000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff0000ffffffffffffff00ffffffffffffff00ffffffffffffff00ffff0000ffff0000000000000000000000000000ffffff00000000000000000000000000ffffff000000000000000000000000000000000000ff00ff00ff000000ff00ff00ff0000ffffffffffffffff0000000000000000ffffffffffffffff00ff00ff00ff0000ffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff0000ffffffffffffffffffff0000ffff0000ffffffffffffffffffffffffffffff00
|0,11=>0xff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffff00ff00000000000000000000000000000000000000000000000000ffffff00ffffff00000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffff00ffffff000000000000000000ffffff00ffffff000000000000000000ffffff00ffffff00ffffffff00000000ffffffffffffff00ffffffff00000000ffffffffffffff0000000000000000000000000000000000ffffffffffffffffffffff00ffffff00ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff00000000ff00ff00ff00ff00ffffffffffffff00ff00ff00ff00ff00ffffffffffffff000000ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000ff00ffffff00ffffff00ffffff00ffffff00ffffff00ff00ff00ffffff00ff000000000000000000ffffffffffffffff0000000000000000ffffffff00000000ffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffff000000000000ffffffff00000000ffffffff00000000ffffff0000000000ffffff000000000000000000ffffffffffffffff0000000000000000ffffff00ffffff00ffffffff00000000ffffffff00000000ffffffffffffff00ffffffffffffff00
|0,12=>0xffffffffffffffffffffffffffffffff0000ffff0000ff000000ffff0000ff0000000000000000000000000000000000ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffff00ffffffffffffffff00000000ffffff00ffffffffffffffff00000000ffffff00ffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff0000ffff000000000000000000000000000000000000ffffffffffffffffffffffffffff0000ff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffff00ffffffffffffff00000000000000000000ff00ff00ff0000000000000000000000ff00ff00ff0000000000000000000000000000000000000000000000000000ffffffffffff0000ffffffffffffffff0000000000000000ffffffffffffffffffffffffff00ff00000000ff000000ff000000ff000000ff000000ff00000000000000ff00000000ffffffffffffffffffffffffffffffff0000000000000000ffffff00ffffff00
|_,_=>0
def sP:Nat→Nat
|0=>0xd06050a04030211001205190a0403020d1e06050a040302000e050a041817000d0c06050a040302001506051d03091a000e050a03181a000d1506051b03091a0f0605190a040302000e050a031813000d1506051404091700150605140309130012050a040302110d0c060b0a040309080605070403020006050403020100
|1=>0xa03091328000d231524051404030900240e051b0a0309130d24050a04030925000d15061c051d040309000e1c050a040318000d15061c051b0403090f15060b051d0403090f0e0b050a0403180f0d0c0e050a030913000d1024050a040318000d12200a04030908221506050a0403090f0e20050a0403180f000e050a04091f
|2=>0x50a04092e000d0c06050a04030900080e050a04091728000d06050a04030200240e051b0a0409170d0e050a03092d000d2c0e050a03091a0f0d06052b040309000c0e050a040917000d15060514040309260012050a042a090d1615060514040309000e050a03091a28000d1220050a040309290f240e051b0a03091a0d0e05
|3=>0x3a0006051b0403093a0f060e05140a040917000e050a03091a29000d0e050a04031826000d0e200a3903090006051b04030938160e050a040318000d0e050a370309000d0e35050a0403090f0e200a04030900330e201b04030931060e05140a030913001506050a03091a0f00221506051404030900300e050a04032f000d0e
|4=>0xd400e0b050a0403090f1506050a030913000d240e3e050a0403090d3d0e050a03091a0f0024050a0403183c000d060e051d0a03091a00150e051d03091a000d060e051b0a03091a0f150e051b03091a0f0d0e05190a040302000d06050a3b0403090012050a0403020d06050a04030900330e0b0a3903090d06051d040309
|5=>0xb0a0403090f060b050a040309290f240e050a04030949001506050a040917000d0e050a040348000d104714040309000e050a04032f000d06052b0a040309000e0b0a042a090d410e050a03091a000d210e050a03091a000d060b0a04030908210e050a030913000d0e050a030944000d0e050a03094443000d0e050a040942
|6=>0x6050a0403090f00240e05270a040309000d150e20051b0403090f0e050a0403094f000d0e054d0a040309000d0e050a042a09000d160c0e050a040309000d0e050a0403094c000d0e050a0403094b0f000e050a04030211000d120e051d0a03091a0d210e050a040917000d0e050a04091f43000d12050a3b0403090d100c06
|7=>0x9000d0e050a04030957000d0e05550a040309000d530e050a040309000d1024051b0a0403090d160e050a04030928000d0e050a04030951000d16240e051b0a0403090d240e50050a040309000d2315060514040309000e1c050a04030929000d0c0e050a04030926000d0e0b050a040309290f0d240e050a0403094a000d34
|8=>0xd06050a040309290f00060e36050a0403090f15060b05140403090006050a0403095f0f00150e20051d0403090f00100c06050a0403090f00120e5e050a0403090f0e050a0403092826000d100e0a0403095d000d231506050a0403090f000e050a03095b000d240e051b0a040309260d0e050a0403095a0f000e58050a0403
|9=>0xa04030900150e1c051d040309000d0e050a04030965000d060e1c051b0a0403090f060e0b051d0a0403090f150e1c051b0403090f0d150e0b051d0403090f0d630e050a040309000d0e050a040309620f00600e200a040309000d240e3f050a040309000d220c0e050a040309000d3d0e0b050a0403090f120e050a03091a0f
|10=>0x40309080d210e20050a0403090f0046300e050a040309000d150e1c050a03091a000d0e35050a040309000d3d0e1c050a0403090f00670e050a0403090f0d23240e05140a040309000e200a04030900310e050a04030966000d1506051d040309000e050a040318000d060e050a030913000d1506051b0403090f060e1c051d
|11=>0x50a04096d000d240e050a03091a000d0e050a040309520f0d102124050a040309000d16060e05140a040309000e056c040309000d240e050a0403096b000d1506051d0403090f000e050a0403180f000d0605140403093a00240e050a030913000d410e20050a0403090f0006050a04030900380e050a04030968000d12050a
|12=>0x50a04030974000d410e0b050a0403090f0d210e1c050a040309000d730e050a040309000d0e052b040309000d210e0b050a0403090f0d10470a040309000d0e05710a040309000d06050a0403093a0f00700e050a040309000d0e050a0403096f0f0d060e05140a04030926000e050a0403096e000d06051b0403093a000d0e
|13=>0xc0e050a0403090f00300e050a0403097f000d0e050a0403097e000d7c0e050a040309000d7b0e050a040309000d0e050a040309790f0d120e20051d0a0403090f0e050a780309000d0e050a040302000d0e050a04030900770d060e050a040917000d150e050a03091a000d0e050a04030976000d410e1c050a040309000d0e
|14=>0xe050a04030985000d0e050a0403094a000d240e050a040917000d0e05270a040309000d150e050a03091a0f000d0e32201b0403090f100e201b0a0403090f22060e05140a040309000e050a04030983000d0e050a04030982000d810e050a040309000d0e80050a040309000d12050a040309290f0d1012201b0a0403090d23
|15=>0xd540e050a0403090f00240e050a0403094c000d0e470514040309000e050a0403098e0f0d10060b140a040309000e3e050a040309000d0e050a030989000d120e32200a0403090f880e050a040309000d22060e050a0403090f152406051404030900120e1c051d0a0403090d0e50050a040309000d0e050a04030987000d
|16=>0xd1012321b0403090d10060b0a0403090f0c060e0b050a0403090f2c0e20050a0403090f0e47050a0403090f001006051d0a040309000e20050a040309280f00240e20051d0a040309000e3f050a040309000d1006051b0a0403090f240e20051b0a0403090f0e051b040309380d100c24050a040309000d231524050a040309
|17=>0xe0b050a040309280f0d240e1c051b0a0403090d240e0b051d0a0403090d161506050a040309000d0e051d0403093a000d0e051b040309310d0e050a040994000d0e051b0403093a0f0d1024050a04030928000d0e92050a040309000d0e050a04030925000d900e050a040309000d24050a04030929000d0e058f0a04030900
|18=>0x16210e050a040309000d0e200a0403099b0f000e050a030913000d0e050a390309000d100c060b0a040309000d0e05140a04099a000d980e050a040309000d0e051d0a03091a000d970e050a0403090f000e050a04030900330d1506050a04030926000d150e0591040309000d0e051b0a03091a0f0d0e1c050a04030928000d
|19=>0xe050a040309000d221506050a040309000d9f0e050a040309000d460e050a040309000d15060b050a0403090f240e050a040318000d24060e050a030913000d210e050a04030926000d2c0e1c050a0403090f0d10063214040309000e050a3b040309000d0e050a0403096b000d0e050a0403099d000d9c0e050a040309000d
|20=>0x15061c050a0403090f000ea2050a040309000d240e050a0403180f000d0e050a040309a8000d0e050a040309a7000d0ea6050a040309000d0e050a04030949000d060e050a03091a0f000e050a040309a3000d0e200a04030900081012200a0403090f0ea2050a04030943000d0e8d051b040309000d0e050a040309a1000da0
|21=>0xe20050a040309290f00400e050a0403090f000e050a040309a9000d0e050a040309ab000d24060e050a040917000d150e050a04096d000d0e050a040309aa000d230e051b0a0403090f0e0b0a040309080d0e050a04030943a9000d0e050a040917000d1012051d0a0403090d340e200a0403090f0010240605140a04030900
|22=>0xdae0e050a040309000d0e20051b0a0403090f21240e050a040309000d0e050a040309ad000d950e051b0a040309000d101205140a040309000d0e47050a040309000d22240e050a0403090d0e200a0403095f0f0034060514040309000e050a0403097f000d06050a04030900080e052b0a040309000d0e050a040309840f0d
|23=>0xd230e050a0403090f000e050a0403094e000d120e320514040309000d100e9e0a040309000d340e0514040309000d0e050a04030900080d0e050a04099a000d1012050a0403090f0d23240e050a040309000d0e050a040309b2000d0eb1050a040309000db00e050a040309000d0e051d0a0403097d000d120e050a040309af
|24=>0x99b000d16060e050a040309000d99150e050a040309000d0e36050a0403090f0d67150e050a040309000d0e05b50a040309000d0e050a040309ac000d0e20051d0a0403090f000e050a0403097d000d340e050a0403090f000d21240e050a0403090f000db30e050a040309000d120e20051b0a0403090d970e050a04030900
|25=>0xa0403095f0f000d100e050a04030986000d1006320a040309000d150e050a04030900450db70e050a040309000d0e1c051b0a0403090f0d0e0b051d0a0403090f0d960e050a040309000d1012051b0a0403090d34990e050a040309000d060e050a04030926000d0e050a04030929000d23060e05140a040309000e200a0403
|26=>0x26000d0e32200a0403090f000e050a040309b8000d1024050a040309000d0e050a04030900720d0e32201b040309000d0e8d050a040309000d0e050a040309290f000d100e201b0a040309000d16240e050a040309000d0e5c050a040309000d060e0b05140a040309000e1c051d0a040309000d150e0b0514040309000d0e05
|27=>0xd120e32200a040309000d150e051d040309000d060e051b0a0403090f150e051b0403090f0d0c240e050a040309000d340e200a040309000d22060e050a040309000dba0e050a040309000d0eb9050a040309000d120e32051b0403090d060e0b050a0403090f640e050a040309000d0e050a04030984000d240e050a040309
|28=>0x50a04030943000d3d0e050a0403090f00060e1c050a0403090f00240e050a04030928000dbf0e050a040309000d400e050a040309000d0ebe050a040309000d0e050a04030900bd0d100605140a040309000ebc050a040309000d0e050a04030956000d0e0b050a0403098c000d060e051d0a04030900120e9e050a04030900
|29=>0x94b000d0e050a040309a5000d100e321b040309000d1012320a040309000d060e051d0a0403090f00150e051d0403090f000d0e05140403093a000d10b4050a040309000d0e200a0403095f000d10060b0a040309000d0c060e0b050a040309000d2c0e20050a040309000d0e050a04030900380d1006051b0a040309000d0e
|30=>0xd0e050a0403095a000d0e051b0403099b000d210e050a040309000d060e32050a0403090f000e050a04030900310d0e051b0a0403098a0d240e050a040309280f000d0e050a0403093a0f000d100e050a04099a000d0e050a040309c1000d0ec0050a040309000d3406050a040309000d060e320514040309000e050a0403
|31=>0xb050a040309000d210e050a0403090f000d0e050a040309c4000d230e320a040309000d990e050a040309000d670e050a040309000dc30e050a040309000d0c150e0b050a040309000d06050a0403095f000dc20e050a040309000d100c06050a040309000d231506050a040309000d120e20050a0403090f410e050a040309
|32=>0x30952000d120e051d0a0403090dc70e050a040309000d1012200a040309000d0e050a040309b60f000e05c60a040309000dc50e050a040309000d24060e05140a040309007a0e050a04099a000d7a0e05140a040309000d0e8b050a040309000d0e050a04030962000d23060e050a0403090f00410e050a0403090f000d1506
|33=>0x90f0d100e051b0a0403090f0d0e050a0403095d000d160e050a040309000d0e1c050a03091a000d120e1c050a0403090f0d0ec8050a040309000d690e05140a040309000d100e0b140a040309000d0e050a0403096f000d100e5e0a040309000d7a0e050a0403090f0d100e200a0403090f00340e051b040309000d0e050a04
|34=>0xe050a040309000d102406050a040309000d0e050a04030979000d100e1c0a040309000d230e051b0a040309000d0e05910a040309000d0e050a040309c9000d1624060e050a040309000d100e0b0a0403090f0d0e050a04030926000d120e051d0a0403090f0d0e32051d040309000d100e051d0a040309000d0e32051b0403
|35=>0x4030928000d150e20051b040309000d240e051b0a0403090d0e050a03091a000d100ebb0a040309000d120e32050a0403090f0d1006050a0403090f00240e20050a0403090f00cb0e050a040309000d06050a0403093a000d060e050a04030900af0e051b0403098c000d24060e050a04030926000dca0e050a040309000d6a
|36=>0xd100e3214040309000d0e050a04030959000d950e320a040309000d230c0e050a040309000d240e1c050a040309000d0e050a04030986000d0e050a040309cc000d240e0b050a0403090f0d060ebb050a040309000d220e050a040309000d0c060e050a0403090f000e5e050a0403090f00150e20050a0403090f000e050a
|37=>0xa040309000d600e050a040309000d150e1c050a040309000d2c0e050a0403090f0d150e0b050a0403090f0d0e050a040309280f000d240e051d0a040309000d120e5e050a040309000d240e051b0a0403090f0d610e20050a040309000d100e360a040309000d300e050a040309000d0e050a03091a0f000d0e050a0403098e
|38=>0x1506051b040309000d540e050a040309000d150e1c050a0403090f000d0e050a04030975000d0e050a0403099b0f000d152406050a040309000d15060514040309000e051b0403093a000d240e32050a040309000d230e050a04030986000d3d0e0b050a040309000d0e05140403099b000d0c0e0b050a040309000d060e3605
|39=>0x403090f000d060e051b0a040309000d120e32050a040309000d060e05140a04030900150e0514040309000d060e0b050a040309000d240e050a0403090f000d340e050a040309000d100e200a040309000d340e32050a040309000d0e050a040309b6000d0e050a04030900930d1506050a0403090f000e050a040309a4000d
|40=>0xd0e0b050a0403090f0d120e20050a040309000d0e0b05140a040309000d0c060e050a040309000d0e5e050a040309000d150e20050a040309000d0e20050a0403090f002c0e050a040309000d150e0b050a040309000d1006050a040309000d0e050a0403098c000d0e050a0403095f000d0eb4050a040309000d150e050a
|41=>0x514040309000d100e05140a040309000d34100e050a040309000d0e051d0a0403090f000d1506050a040309000d0e1c050a0403090f000d0e050a0403093a000d1012050a040309000d0c150e050a040309000d0ebb050a040309000d0e051d0a040309000d0e051b0a0403090f0d7a100e050a040309000d0e1c050a040309
|42=>0x309000d0e9e050a040309000d0e32200a040309000d34150e050a040309000d0e9e32050a040309000d0e050a040309008a0d0e050a04030900450d150e051b040309000d230e050a040309000d060e050a0403090f000e32050a0403090f000d0e36050a040309000d24060e050a040309000d0e3632050a040309000d0e32
|43=>0xe050a0403099b000d23100e050a040309000d060e32050a040309000d100e050a0403090f000d100e320a040309000d0e20051b0a040309000d950e050a040309000d2c150e050a040309000d120e050a0403090f0d3d0e050a040309000d0e050a04030900af0d0c0e050a040309000d120e05140a040309000d610e050a04
|44=>0xe20050a040309000d0e0b050a040309000d0e050a0403090f000d0e32050a040309000d120e050a040309000d0e05140a040309000d690e050a040309000d100e0b0a040309000d0e32051b040309000d100e051b0a040309000d23060e050a040309000d240e050a040309000d7a0e050a040309000d120e051b0a0403090d
|45=>0xe050a040309000d150e050a040309000d060e050a040309000d100e050a040309000d0e051b0a040309000d
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0xee0007
|7,0=>0xed006e80334017a00ad004e8023400fa006d002e80134007a002d000e8
|8,0=>0x14bc8a3e050d227e813ac89b244c7225a9128c8922447f22369116c8892443902157106c0819c3fd01f680f6c879243b721d470e6b8712437901b480d640695c339219390c54860642f3017090b3c8581c2af214f80a3484fdc26d212d9093384764229210b9081483e641e120e7906f48356419920c3905d482c64151209f904c3823e410d207e8
|8,1=>0x326918ec8c5246172303817d48bc645d122df916bc0b41c59102c0815cb8ac2454f22a07
|9,0=>0x2bdc15c68acf455da2aa4952a8a832537a297c149a4a3d05168286c941609f744f1a2744937a89a944caa260512de495d24a5924dd12468911247f923b491b648c9245b9228d111e887d2434a215c90868833040fa20348ff647e923eb91f148f66479f43c691de50eca8753239fa1cad0e2e8703437891b750d9646b9235391a5c0d068671232f9
|9,1=>0x3e041ede4f5d27a593ce49e4a8f13278093bbc9dba4ecb275c93a951d2a0e832737a39749c964e392713938549c064def46eda37249b6e4da526c9935fd1ade0d5f06a6934ec9a524d172681a33c499ba8cc9465b9329c19268c8306389317c989a4c3b2613a305498064bf305f092f3c97768ba745cb82e0d16e24b5f25a782cf496528b1905839
|9,2=>0x5054a80653f129eea4f2ca77253a729ca94e0526da935949a484cdca64a5313298094bb525b652cb095d84a9d252a528329389497ca49a5239491394854a40291ed48eca47152362919f28c7845fc22da515948a3944d4a2465111287f943bc21be10cb485c9429ca12a50814836a416ca09250354812840451ffa8feb27eba3f1c1f6a4fa327c89
|9,3=>0xb349595cac8e16352b128584cac0255ed4aed95724ab6e55a34ac8955fcaada555d0aa4a54e42a4e55152a80a53b529b654c74a5a9528ca922547f2a369516ca896143b0a13a
|10,0=>0x6c84b61e5afb4d7496b5cb58a5ab32d5096a3cb4f69a674d29a6904b45a9a194d02a67c533ba99cb2cdba6694b322997d4cb596564b28a99314c8f9642d31f258e54c68a62fcb15698992c43961cd30c2584d4c1bb6094b02297ff2bf695f6caf8e97b52bd195e44af02176f2bada5d24ae6e57252b88a5bfcadda56db2b63a5ad4ad42968d4b3d9
|10,1=>0x7f2cbf725fa72fca97e0cbedadf5b2fa497cd53e429f0f2f7e97bacbdb25ec72f59a7a84bd1e5e796f32a794cbc825e2f2f0e9782cbbf25de72eea9770cbb5e9d9b4ec4975dcbaca5d532e9eb74a53a2e5d034e789737cb9969cb74e529724cb9025c6f2e2e9712cb8725c254e0996ffd37d69bd92de396ed4b7429b8f2dbda6da4b6ae5b452d999
|10,2=>0x91ecc8cea4535220990b54836640751fa98f85479e63bf11d698e65470e637351b098d3cc67a632b318ab8c0cc5e262dd516598ae4c54aa2933140989adc4b262473119a8884c41aa1fb30f3a8754c38661b130cea862cc2eea16350a8984fcc25a611b3084983dcc1ca60d33060982bcc13a608b303ba8194c0a2a03f301698065400a9ff14feea
|10,3=>0x9c94ce266701337799b74cd8ee6b53350a9a354cfa266b332ba990d4c5ea61d3304a97d54bc665cf52de996a54b2aa58152b6a95654a8aa53332909943cc9fa64eb326c9931cc966a49f52469
|11,0=>0xaf6d578eabb355d09ae3556f66b6755aa9ad0cd6626b1f3585aabe4d5ce6ad53560aaab555366a89353b9a994d4a66a3f55169a865540aa9f334efaa72d536ea9a534c8aa5fcd2da695954a39a4d4d246690f547e9a3acd1aea8c35457aa274d112a87734329a145507e682d340d9a024cfeaa7e153e6a9eeccf52679553c0a9dbcceba6749539b9
|11,1=>0x16419b1c4d8be6c4b561bab094d8266c0135f79
|12,0=>0x2d3736929b44cda026cef366e9b32cd9726ca7364a9
|13,0=>0x16a48
|_,_=>0
def wAt:=mkWire dB 205 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x50d400352300c00350605438352109c543d0e0a41435000d424210e0d4403c0e05400350e0042421100f03815000d43835100f00035090843835100f03815000d438350a0f47013050f400350e0a470130e0d4143d000d4383509084403c0e05400350a0d4580f060b438350500428351604c182d0e0d41401090843801100f03815000d414010e0d4403c0e0540035
|1=>0xe0d428350e0a40c210e004403c0e05400352405418010e0d428350e0a438761c04c383d050f400350a0d418010605438350e0a4581324054383d000d4389e0a26490170e0f400350a0f4143d0e0a43835000d48427150f4143d000d438290e0a43835050f42801000d438290a0f414010e0d400352109c543d000d43829050048427240a448350e004403c0e0043815
|2=>0x150f028010e0a43835000d48427240a490150e0f40035063602c29050043835000d41435340f05415000d438290a004c83c050d41429000d458132300428350605438351c04c143d0e0a43835000d48c030a0d418150e0d418290e0d4403c0e0540035090843835100f03815000d4580f24054383d000d448290e0047013050f438350a084403c0e05400352405c1801
|3=>0xe0f400350a0f438351c04c143d000d4283d0e0a47013050f400351c04c3835050f400351c04c3829050f4280109084403c0e0540035101d038150a0f43835000d424210e004403c0e05400350e0d4d03c1505400350e0a4140104084403c0e05400350a0f454170e0a43835000d428011505c38290e0d400350a0d4580f060b4383505004143504084403c0e0540035
|4=>0x50a400350e0a4580f060b438350500418c8050a428350e0d438154609c5515050f800350e0a438350a084403c0e0540035050040c21100f03815000d4543d0e0a47013050f40035050043835100f03815000d45813240a490150e0f40035050050435150fc00350e0a438291604c182d0e0d414013f00c14a1240ac383d000d454370e0a47013050f438622109c9029
|5=>0xe0d45415000d438290a26490170e0f400350a0043829050d400350636838350b0a414010a4e4182f0e0d4140103084403c0e0540035230041815060a438352105cb0351500438291520c3829050d4003509084403c0e05400350a0f438011c04c143d000d4580f240a490150e0f40035101d06c350e05438010a0040035060a438350e05414010e1d9283524328383d
|6=>0xe0d438295c04c2c510a0d414010a00490170e0f40035000d418ca050a4383505594186f0a0043835151c82c350e0a414010a56438720b0d414015400cf415150dc3829120d438150e0042801240ac90150e0f40035520d438da0b0a414010a00490150e0f40035000d428350605438350e0a4143d0e1d8283d000d490170600418290e0d414010e1d8283d000d40035
|7=>0x150d438295f0d40035100ac38156105414351500c382905284902b0e0f400352300c1815060a43835150dc00350e0a414010e0047013050f400350e0d438760a0f400350b0a414010e0d400350e0d438290a0d414010e0d40035100ac38150a0f43829050d400350e05418290e0d400350e004c837050a40035240ac90170e0f400351c0ac2c350e0541401000d41815
|8=>0xd43829150b400350e0a41401060042835060543835320f01435050a400355f0f40035100ac38150e0d4283d000d438292109cb0351500438291604c182d0e0d414010a00438290e0d40035050f438350a0f400350a0f4143d000d438290529838760a0f400350e0d4143d0a00400350a0f414010e0d400350e0a4143d0a00400350a0f400350e0a41401640543003
|9=>0xe00438152300428350605438350a08c403c0e0540035160ac90150e0f400350a0f438290e0d400352109c38750a0f400351505c38350a0d438291604c90150e0f40035150fc3829050d40035150f038290e0d400356a0ada4351000c38150e004403c0e0540035150f43829050d40035300a43915050f800350e0a470130b0d414010636038350b0a41401150dc143d
|10=>0xe0a41401150f4143d000d438290e314c83c050a400350a084403c0e0540035150f400350e0a414010e05418c8050a438350a724403e0e05400351505c38290e0d40035600dd84151500c3829000d4b0171500438292405c18010e0d428350c0bc38510a0d414011505c38350a00438296703cb0151500438290e0f47013050f40035000d438da0b0a41401240a44835
|11=>0xe05438010a00400350605418290e0d43915050f800352c20c14351500438290e7d414760a0f40035340fc5415000d438297a0ac48150e00400350a0f43801050d4003504754542f0e0a4140109084403c0e05400353a0f85417000d438291603c182d0e0d414010e0a470130b0d414016f0d4b017150043829150fc143d000d43829750d4542f0e0a41401150fc0035
|12=>0x50f43801000d490c80e0f41429000d52c011520c14350e0a61801230ac40350e05490ca0e0f41429000d4580f24054383d000d428992405c383d000d438291c04c143d000d41435000d414290a00428010e0541435000d48c030a0d418150e0d610353a00454170e0a454730b0d43829050058481050d454030e0a51c010632014290e0d438010e1d8283d000d41435
|13=>0xa0043835000d428010e0f41435000d42801150f000350e0a438150600418290e0d418010605438350e0a400353d05454370e0a48417240a4383d000d428350632014290e0d57c01000d4402b0e05428350e0d43815050063403058c4182b0e0d62c13058a4383e000d400350e0041429050d50415150fc00350e0a48c03060543835000d418010e0d428350e0a4283d
|14=>0x1505c00350e0a4902b120d438010e054164d150f800350e0a43a460a454143e000d45517050f800350e0a4383d0e1d8283d000d454700b0d438290500414290e05438010a0043835000d43815050041401060a43835000d40035050d454010e0a400350632014290e0d438150a0f43835000d41435240ac383d000d414350e0f4283d000d414a1240ac383d000d43815
|15=>0x7a03c382d0500664353400c54150e0a4283d1c04c143d000d4d0371505400350e0a4d03c1505400350e0a490170600438350e0a42915050f800350e0a47013050f42801000d4143d240ac383d000d41401240ac383d000d4383d050f42801000d414010e0f4283d000d48c010605438350e0a454170a0f400350e0a4c83c000d414290a006580f9500440370e0542801
|16=>0x50f800350e0a43835000d43829050048427240a4383d000d458132405418010e0d490292405c383d000d4386d050f42801000d414290a0d438350e05440741400428350e054582b24054383d000d44a7a0e0048029050d439751c0ac2c3505004902924054383d000d400350e3281429050d4581324054383d000d41021100f03815000d418290e0d43815050042835
|17=>0x5004182b0e0d48427240a4383d000d439720b144283505004882b2300c40350e05414e1150f000350e0a694351232814290e00438351c04c143d000d690011014c28350e0541435100f03815000d438010e0541435000d4150d8c004182b0e0d42801058c4182b0e0d5e8530e0b4283505004f42d150dc3829050048c030605438350e0a454710b0d43829050045515
|18=>0xd4e8011505c3829050d438760a0f40035410d4543f000d438290543a3001060ac3835ac0043017150d438291603c90150600438356703c542d0e0a41401790d5e82b0e0b414010a00418150e0d40035100f000350e05414018c004182b0e0d4580f24054383d000d46c350e05438010a00414351505400350e0a428350600438350e054143d0e0a43835000d42e31
|19=>0xd418010605438350e9e88029050d67803200a414350e5e4c837050a414760a0f400350a0f83801000d43abd0a0f800350a0041435000d490290e0f400359b0d438ca050a440370a00438150a0d438010e05418c8050a438351600c90150e0f40035000d41435100ac38150e0d42835150543829300ac3915050f800350e0d4403c0e05400350a084403c0e0540035
|20=>0x50a41435060b4383505004d003150543829320041429000d4542d0e0a414010ab6418170e0d43017150d43829050d4283d000d414760a0f400351505400350e0a490290e0f40035b405418030e0d414350e0042801340dc54150e0a418150e0d40035060bc3835050043801050a42835320d414290e0542835150543829100f03815000d5e80f0e0b414010e0543801
|21=>0x58c4182b0e0d438760a0f400350a00414350e05490150e0f400350b14428350500438350a0d41401050f4283d000d438290a0d41401000d4402b0e0548c2b100d438150e0d414290e054143e000d43829690a440030e054143d0a004003505004283d000d65401100dc38150e05438010a004d0031505438292405c18010e0d438760a0f400350a0d418150e0d438ca
|22=>0xe0d4283d0e0d400350e0048029050d43801050a414350a0f400350e0a428010e0d400350e0a42801000d41801060a438350e3241429050d48c030605438350ebb4c803050a4d8370b0a414010e00414290a00414010e0d400350c00c54350e0a4e8011505c38292405c383d000d41435050a40035b600418170e0d448350e0043815100f83815000d41435050a42801
|23=>0xa0f400350e0a4283d000d454170a0d438290600c38350e0541435100ac38150e0d43815050041401060a43835050d454010e0a4543c000d438290a00438350e0563001060ac3835150dc00350e0a4143d0e0d40035240ac383d000d6d0290600c3835610d454030e0a4c83f050a40035320f81429000d428350e0d438155e004c837050a438720b0d4140105004182b
|24=>0xe05418290e0d418150e0d438290e0041435000d4543f000d438290632814290e0d438ca050a428012c0d454010e0a414290e0d40035320f01429000d4383e0a0040035240ac383d000d45417000d438297a03c40010e05418cb050a43835bb0d4c803050a438c9050a438350a0d414290e0d45483050d438291232814290e0043815050a428010e00414290e0543835
|25=>0x500414350e00438150605c3835000d42a290e0f80035950a440370e05418010e0d428357a03c382d05004382d0a0d41401058a4383e000d57c35100ac3815060543835000d4543f000d438290e0d438290500438750a0f40035101bc28010e0544035050a438153400c54150e0a4b015150043829100fc3815000d454350e0a414010e0d4402b0e054f401150dc3829
|26=>0xe05414012405c383d000d438010a0f400351b0d414290a00450010a0d43815000d414290a00438150a00400351c0ac2c350500490150e0f400351c04c2c3505004143d0e004003505af4283e000d428351000c38150e054283505004b017150043829320dc14290e05448150e00400350e0541435000d438c9050a428010e3682c2905004283d0e00400357a0dc382d
|27=>0x50d428010e0a4383d0a00400351c04c2c3505004c803050a438150e0041429000d438150e0d400350e0f41435000d4b0371500438291505c38350e0a4283e0e0d400350a004182b0e0d490170600438350632414290e0d5a4351000c38150600438350e055e82b0e0b414010b0d438150500418150a00438350a454143e000d66c010e32814292405418010e0d40035
|28=>0xd43801320dc14290e0f42801000d414351500c38293200414290e0543915050f800351c04c143d000d57c01100ac38150a0d414290e054186f0a0043835100dc14290e0541815060a438350e0f4143d000d48c2b100d438153a0d454170e0a4383d000d414013200c14290e0d48c03100d43815060a43835000d4c837050a400350e0a41435000d4902b0e0f40035
|29=>0xe0d400351014c28350e05438350a00438293d05454370e0a4143d000d43829150bc38290500438ca050a400350600438350e0a438350a0d438291505c28010e0a4383d050a40035230ac40350e05454370e0a414010e32814290a0d438510a0d414010e0d42c290500584151500c38290b0d43829050040035150043829000d4382905004902b0e0f400350e0f4283d
|30=>0x150d438293200c14290a0f400350a00400351000438150b0d41401000d414010e00414350a0d41401060a43835320dc1429050d43829050d400351500438290e0a414010e0d43815060ac3835100ac38150600c3835000d438290a0043835050a438010e0d428350a0d438290e0d414010e0f40035150543829050d438150e32414290605c3835150f800350e0a43829
|31=>0xe0540035050a438150a0041435100dc38151500438290e0040035150dc38290a0f80035150d438290e00428351500c3829200a41435050a41435150543829320d414290e0f80035050f800350a0043829100d438150e0d40035050a400350b0a41401060043835320041429050a428350a0d43815100a438150a0f400350e0d43829050f400351505c38290e0043815
|32=>0xe0a438350e0542801050d41401000d414290e00428351000c38150e0541401050a428010a00438150605438350e0f400350e0b414010e00428010e3281429100d43815050a43835
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x30502b502830000023501e5000001950145000000f500a500550005
|8,0=>0x1165000000000000111510c5107510340fe50f950f450f040ec40e840e350de50d950d450cf50ca50c55000000000c050bb50b6500000b150ac50a750a2509d50994000000000945000008f508b4000008740825000007d5078507350000072106e4000006950654060505b50565051504c504750000043403e503a403550000
|8,1=>0x1584153514e5000014951445143113e513950000134512f512a512550000120511b5
|9,0=>0x252424e424a42464242423e423a42364232422e422a42264222421e421a42164212420e420a4206420241fe41fa41f641f241ee41ea41e641e241de41da41d641d241ce41ca41c641c241be41ba41b641b241ae41aa41a641a2419e419a419641924191118d4189418541814180117c417841744170416c416841644160415c4
|9,1=>0x351434d434943454341433d433943354331432d432943254321431d431943154311430d43094305430142fd42f942f632f242ee42ea42e642e242de42da42d642d242ce42ca42c642c242be42ba42b642b242ae42aa42a642a2429e429a42964292428e428a42864282427e427a42764272426e426a42664262425e425a42564
|9,2=>0x451444d444944454441443d443944354431442d442944254421441d441944154411440d44094405440143fd43f943f543f143ed43e943e543e143dd43d943d543d143cd43c943c543c143bd43b943b543b143ad43a943a543a1439d439943954391438d438943854381437d437943754371436d436943654361435d435943554
|9,3=>0x4d444d044cc44c844c444c044bc44b844b444b044ac44a844a444a0449c449844953491448d448944854481447d447944754471446d446944654461445d445944554
|10,0=>0x5953592358f358c3589358635833580357d357a357735743571356e356b356835653562355f355c3559355635533550354d354a354735443541353e353b353835353532352f352c3529352635233520351d351a351735143511350e350b35083505350234ff34fc34f934f634f334f034ed34ea34e734e434e134de34db34d83
|10,1=>0x6553652364f364c3649364636433640363d363a363736343631362e362b362836253622361f361c3619361636133610360d360a36073604360135fe35fb35f835f535f235ef35ec35e935e635e335e035dd35da35d735d435d135ce35cb35c835c535c235bf35bc35b935b635b335b035ad35aa35a735a435a1359e359b35983
|10,2=>0x7153712370f370c370937063703370036fd36fa36f736f436f136ee36eb36e836e536e236df36dc36d936d636d336d036cd36ca36c736c436c136be36bb36b836b536b236af36ac36a936a636a336a0369d369a369736943691368e368b368836853682367f367c3679367636733670366d366a366736643661365e365b36583
|10,3=>0x781377e377b377837753772376f376c3769376637633760375d375a375737543751374e374b374837453742373f373c3739373637333730372d372a372737243721371e371b37183
|11,0=>0x802280027fe27fc27fa27f827f627f427f227f027ee27ec27ea27e827e627e427e227e027de27dc27da27d827d627d427d227d027ce27cc27ca27c827c627c427c227c027be27bc27ba27b827b627b427b227b027ae27ac27aa27a827a627a427a227a0279e279c279a27982796279427922790278e278c278a2788278627842
|11,1=>0x81428122810280e280c280a2808280628042
|12,0=>0x81f181e181d181c181b181a18191818181718161
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 16
def pmP:Nat→Nat
|0=>0x47ee0000000008f9c0000000011eb80000000023c7000000000478a0000000008b1c00000000110000000000020000000000003f0e00000000040080000000003e380000000001b40000000000300000000000054800000000008800000000001040000000000204000000000040000000000006300000000000c0000000000014000000000002580000000000400000000000040000000000006400000000000880000000000090000000000008000000000000c00000000000080000000000008000000000000
|1=>0x347ee0000000068f9c00000000d1e3800000001a2e50000000030104000000005ca1c00000000b1e380000000133d7000000002678e0000000048f9c0000000091eb80000000123c7000000002459c00000000446080000000071f3800000000e3c70000000018284000000002c8080000000051fb800000000a3d7000000001478e00000000288180000000040e100000000080c60000000010104000000002020000000000400100000000073c7000000000c78e00000000100980000000019eb80000000033c7
|2=>0x1047ae0000000208f1c0000000411c7000000007e3d700000000b47ee0000000118f1c0000000218c000000000430c000000000847ee0000000108f9c0000000211eb80000000423c700000000747ae00000000a8f1c00000001514180000000280c6000000005012c00000000a024800000001404100000000263d7000000004c78e00000000982080000000111eb80000000223c7000000004030c0000000080208000000010040000000002000200000000400000000000078b8c00000000e063800000001b3d7
|3=>0x24030000000004803000000000899eb80000001101d3000000021c78e0000000428f5c0000000831e380000001023d7000000020478e00000003f8f5c0000000791eb80000000d80c200000001947ce000000031ca1c0000000611eb80000000c23c7000000017c7ae00000002e8fdc00000005d1a180000000b80b600000001667ae00000002c8f5c00000005806a00000000aa36700000001447ae0000000268fdc00000004d1eb800000009805600000001247ae00000002401500000000431e380000000823e7
|4=>0x20e67ae00000041ac2980000008319fb80000010631d2000000208412400000040a8218000000805103000000087e3c7000000106478e0000002078f1c00000040b1e380000008133f7000000100478e000000200825c000000400801000000069a3d70000000d247ae000000188060400000031006080000006200830000000c000020000001268f5c00000022e061000000043234700000008101040000001008f1c00000020008900000004000c2000000080002c0000000708fdc0000000a10ab0000000122080
|5=>0x202447ae0000040488f1c0000080551e380000100a23d700000200947ae0000040128f1c0000080211e380000100422a7000002007478e00000400a8f5c0000080111eb80000100223c700000200147ce0000040028f5c0000080051e380000100023c7000002000440000000400080100000080000200000010000001000001c10430e000003800c61c0000030010e380000020923d7000000402678e0000008008f1c0000008818c80000001102104000000220416400000044080180000008799eb80000010e33d7
|6=>0x10000478e000010418cfdc00002040b1e380000408063c7000008080200400001005003500000200951fb800004010a3f700000801747ee00001002e03480000200551fb80000400a80b600000801347ae0000100208f1c0000200311fb800004005e3c7000008008c7ae0000100118f1c00002001d1fb800004003a347000008004c78e000010008cfdc0000200108d200000400210b600000800401c80000100078f1c00002000b1eb80000400133c7000008002478e000010000cf1c0000200011e380000200406c7
|7=>0x1010020040000201c88f5c0000403011eb800008049a3d700001008a478e0000201108f9c0000402091e380000804122a700001008001840000200c08f1c0000400a11eb80000801423c700001002447ae000020044cf1c0000400891fb80000801123c700001002067ae000020040cf1c0000400811eb80000801023c700001000e47ae0000200178f1c0000400211e3800008004209300001000747ae0000200088f5c00004001104080000800033d7000010000678e0000200008fdc0000400011f380000800023d7
|8=>0x2a000478e0000500228fdc0000a000d1fb800011013a3d7000022023478e00004402e8f5c0000880551eb80001100823c700002200147ce00004020b8f1c00008020d1e3800010010a3c7000020020478e0000400210e1c0000800191e3800010002a3d700002000500000000400088f1c0000800051e380001000063c7000020000478e0000301268f5c00006022f1e380000c04522c7000018083c78e0000301068f5c00006020c84300000c04000c2000018028458e0000300408f9c0000600011e38000080c023c7
|9=>0x80000478e0000d40018b0c0001800051e380002811433d7000050000c78e00009420f8f1c0001280071e380002408873c7000048100e78e000090005cf1c0001084131e3800021081b3e7000042019478e0000840108f1c0001080171e380002100263c7000040221478e000080410cf5c0001008011e38000201002002000040106e7ae000080209cf5c00010040b9e380002000e63d700004001947ae0000800318f9c0001000239eb80002000463c7000040000e78e0000800008f1c0000e020d1e3800018041a3c7
|10=>0xa0004c78e0001400008f1c0002401011e380004800223c7000090000478e0001100298f1c0002200051e380004100223c700008020c67ae0001004088f5c00020041b9eb80004008263d7000080100478e0001000488f1c0002000811e380004000e63d700008001747ee00010002d8f5c0002000539eb80004000863e7000080010c78e00010001d8f5c00020002f1f3800040003a3f700008000547ee0001000088f1c00020000f9e3800040001e3e7000080003478e0001000028f1c0002000031f380004000063c7
|11=>0x80202947ee0010040028f9c0020006011e380040004023c7000800060478e0010000408f1c0020000011e380020000a239500040000445000006000008f1c000c000001e380012010433d700010401207ae000200030cf5c0004000491eb80008000533d700010000867e6000200004cf1c0003484031e380006500c23c70000c2014c7ce0001840298f1c0003080311fb80006100563c70000c001cc7ae0001800318f1c0003000311fb80006000563c70000c0008c7ce0001800058f1c0003000011e3800054001e3d7
|12=>0x81a003c78e0010340018f1c0020602099e380040c04123c7000818082230400103004c8fdc0020600911fb80040c011a3f700081802047ee001030004cf1c0020600091e380040c00033c7000818000478e0010240518f5c00204809f1e380040901263d7000812022c7ae0010240418f9c0020480831e380040803823e700081003847ce0010200608fdc0020400a11fb80040801423e700081002347ee0010200468f9c0020400831e380040801033c700081002047ee0010200008f9c0020280011e3800404010a3f7
|13=>0x400020145040080002018f1c0100000811e3802000000a302004000000c78e0040000008f1c0044000219eb80088000023c70008ea008478e0011c40038f9c0023480a31e380046901063c70008ca008c78e0011500098fdc0022080a51fb800441014a3e7000880040478e0011000108f1c0022000111e380043500263c700086a003c78e0010c4040cf9c0021880471f380042108073e700082a014478e0010540068f1c0020a80011fb800411090b3f700082201147ce0010402008f1c0020800431fb80041000223c7
|14=>0x40006500423c78000c0000478f0001040108f1e0001800051e3c0001100023c740010800007ee4000008008f1c4101004439e388002008873c7100008400438e2000008008f1c2004000011e382240801033c7040060000478e080084200cf9c1001004811e382002000123d7040022001478e0800042408f1c0800000011e380808000023c70080100d300ae010000002000c01100085996a002030000a3c7004040110e78e0080802008f1c010000c0d9e380200010b23d7
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x4020200004030001c04000180c0402
|8,0=>0x20180401124890c020f004f8264255000023a0080000000b03c88084580c200608808825d3e05e06e80180000c07c064009240ae00605110000087000cc0400070f00083558a80043010001a021328830a30504c0009390941800
|9,0=>0xdc49dbe2c45268a4df85ac1513f096c6ca22a9b7e7eb4344990825a8cfea3596a5d8381d53dd67e806f9fdcab10da3a621d75cff5c4f49beb7573e6231321a13e69fb08b89f9f33f30a378d2c49960ee285cef731c9b761d34a48727990a50a218f35b2682dc972662532cc56d411784d9da27a24e580d0ee2b3bd3d5f0bdfc3da04a56b261f8f26e262634548baf2df
|9,1=>0x17867e7c563911d6d8e882424cc5848596c4845eb68724d64da4cc579a137d61701196a51771b42cee2f911dcfa8f312b0b3ab864febc7728aef90157ff4ea3d7bd1e10a78b7ab8649a23ef204b353388761d3b870da1cd4cadb6825b580e85085d20d8e17b8a5dc468feee6c93
|10,0=>0x185a35b7a25e6d8cf683ba8e2df58c5ef31c580b4c8e6ea447b591d337d61b6b5b373301a2b3a5305c5b7e88347027ccb207cad058dde54b46f1db64cf2e3fc1c2b6a96ac7374638be574d569a1d383bb04bb66c7c0d1311bd942658a74edafa7595bea6634a714682eb8385d27422b7d68d4b21c7a19cef54a1a69f679e11f4aa076ecf6d7d8033c40ae90ec0c6b4b1
|10,1=>0xebc4478676271beb27e655c31ab238e3f9d9a572798a7794daebd373a7501ddceef58349cc25433d801ad6f61832d5eb0dc419aed6a8cd54eb7b7db9c6c69d0500dfc492d24f5cbe2caa8cd5d2ecaff4797d1ae8a0ab32e6faf9ad36cf8ee7c7b8566204422cd3eace2ac7b2e3cde4fe
|11,0=>0x2391dfa829831f0cc0b0b246ea9302b08f185f6f92738d26ff72658ddb9243b82b20d57fce32eab02dcb6b65e1576fd2f38b06c07f872e109c18521583d0ab8c71a5468231ebb47d1861e4c6e6ac6c93683d
|12,0=>0x1be3411878a8200eac0bcc1
|13,0=>0x1c
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 51 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_247 11 roots_247 ops++addP pm 2 dom_223 11 roots_223 ops++addP pm 3 dom_238 9 roots_238 ops++addP pm 4 dom_63 8 roots_63 ops++addP pm 5 dom_183 9 roots_183 ops++addP pm 6 dom_191 11 roots_191 ops++addP pm 7 dom_239 11 roots_239 ops++addP pm 8 dom_127 11 roots_127 ops++addP pm 9 dom_253 12 roots_253 ops++addP pm 10 dom_203 7 roots_203 ops++addP pm 11 dom_123 10 roots_123 ops++addP pm 12 dom_175 9 roots_175 ops++addP pm 13 dom_251 12 roots_251 ops++addP pm 14 dom_207 8 roots_207 ops++addP pm 15 dzo_87_8 6 roots_87 ops++addP pm 16 dom_95 8 roots_95 ops++addP pm 17 dzo_47_16 6 roots_47 ops++addP pm 18 dom_111 9 roots_111 ops++addP pm 19 dom_159 9 roots_159 ops++addP pm 20 dzo_119_8 7 roots_119 ops++addP pm 21 dom_151 6 roots_151 ops++addP pm 22 dom_87 6 roots_87 ops++addP pm 23 dzo_111_16 7 roots_111 ops++addP pm 24 dom_43 5 roots_43 ops++addP pm 25 dzo_205_2 6 roots_205 ops++addP pm 26 dom_205 6 roots_205 ops++addP pm 27 dom_125 10 roots_125 ops++addP pm 28 dom_231 8 roots_231 ops++addP pm 29 dom_219 9 roots_219 ops++addP pm 30 dom_119 9 roots_119 ops++addP pm 31 dom_215 8 roots_215 ops++addP pm 32 dzo_215_8 7 roots_215 ops++addP pm 33 dzo_239_16 8 roots_239 ops++addP pm 34 dzo_175_16 7 roots_175 ops++addP pm 35 dzo_171_4 6 roots_171 ops++addP pm 36 dzo_235_16 7 roots_235 ops++addP pm 37 dom_79 5 roots_79 ops++addP pm 38 dzo_247_8 8 roots_247 ops++addP pm 39 dzo_59_4 6 roots_59 ops++addP pm 40 dzo_245_8 7 roots_245 ops++addP pm 41 dom_141 5 roots_141 ops++addP pm 42 dom_55 5 roots_55 ops++addP pm 43 dzo_171_16 6 roots_171 ops++addP pm 44 dzo_246_8 7 roots_246 ops++addP pm 45 dom_167 6 roots_167 ops++addP pm 46 dzo_243_8 7 roots_243 ops++addP pm 47 dzo_237_16 7 roots_237 ops++addP pm 48 dzo_173_16 6 roots_173 ops++addP pm 49 dom_243 9 roots_243 ops++addP pm 50 dom_103 6 roots_103 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_87_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_47_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_119_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_111_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_205_2_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_215_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_239_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_175_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_171_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_235_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_247_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_zo_59_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_245_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_zo_171_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_zo_246_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_zo_243_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_zo_237_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_zo_173_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_103 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 2 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 14 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 81 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 81 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 225 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 97 128 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 225 → Z 9 i = true := (range_split z9_0 z9_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 228 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 100 128 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 228 → Z 10 i = true := (range_split z10_0 z10_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 73 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 73 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [5, 0] }, { op := GateOp.or, inputs := [1, 0] }, { op := GateOp.or, inputs := [2, 1] }, { op := GateOp.or, inputs := [4, 8] }, { op := GateOp.or, inputs := [7, 6] }, { op := GateOp.or, inputs := [2, 11] }, { op := GateOp.or, inputs := [7, 8] }, { op := GateOp.or, inputs := [4, 6] }, { op := GateOp.and, inputs := [9, 5] }, { op := GateOp.and, inputs := [12, 13] }, { op := GateOp.and, inputs := [15, 10] }, { op := GateOp.and, inputs := [14, 3] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_51954_aux

theorem PEqualNP.Outside.L_meta_51954 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_51954_aux.main
