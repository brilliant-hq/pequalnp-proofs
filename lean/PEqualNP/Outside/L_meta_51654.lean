import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_51654_aux
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
def dom_25 : Nat := 0x3030303
def goal_25 : Nat := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00
def roots_25 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeeeccffaaaa00ffeeeeccffaaaa00ffeeeeccffaaaa00ffeeeeccffaaaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafaf0ffaaaa00fffafaf0ffaaaa00fffafaf0ffaaaa00fffafaf0ffaaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefefcffaaaa00fffefefcffaaaa00fffefefcffaaaa00fffefefcffaaaa00
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

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xeeeeeeeeeeeeeeeeaaaa0000aaaa0000eeeeeeeeeeeeeeeeaaaa0000aaaa0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfafafafafafafafaaaaa0000aaaa0000fafafafafafafafaaaaa0000aaaa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffaaaaaaffaaaaaaffaaaa00ffaaaa00ffaaaaaaffaaaaaaffaaaa00ffaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffeeeeeeffeeeeeeffaaaa00ffaaaa00ffeeeeeeffeeeeeeffaaaa00ffaaaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffafafafffafafaffaaaa00ffaaaa00fffafafafffafafaffaaaa00ffaaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffefefefffefefeffaaaa00ffaaaa00fffefefefffefefeffaaaa00ffaaaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_98 : Nat := 0x5000000050000000500000005
def goal_98 : Nat := 0xffffffffcccccccccccccccc00000000ffffffffcccccccccccccccc00000000
def roots_98 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xffffffffeeeeeeeecccccccc00000000ffffffffeeeeeeeecccccccc00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_100 : Nat := 0x11000000110000001100000011
def goal_100 : Nat := 0xfffffffff0f0f0f0f0f0f0f000000000fffffffff0f0f0f0f0f0f0f000000000
def roots_100 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfffffffffafafafaf0f0f0f000000000fffffffffafafafaf0f0f0f000000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfffffffffcfcfcfcfcfcfcfc00000000fffffffffcfcfcfcfcfcfcfc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfffffffffefefefefcfcfcfc00000000fffffffffefefefefcfcfcfc00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffaaaaaaaaaa00aa00aa00aa00ffffffffaaaaaaaaaa00aa00aa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffcccccccccccccccc00000000ffffffffcccccccccccccccc00000000
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffeeeeeeeeeecceeccaa00aa00ffffffffeeeeeeeeeecceeccaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfffffffff0f0f0f0f0f0f0f000000000fffffffff0f0f0f0f0f0f0f000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffffffffafafafafaf0faf0aa00aa00fffffffffafafafafaf0faf0aa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffffffffcfcfcfcfcfcfcfc00000000fffffffffcfcfcfcfcfcfcfc00000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffffffffefefefefefcfefcaa00aa00fffffffffefefefefefcfefcaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffcccccccccccccccc00000000ffffffffcccccccccccccccc00000000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffeeeeeeeeeeeeccccaaaa0000ffffffffeeeeeeeeeeeeccccaaaa0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffffffff0f0f0f0f0f0f0f000000000fffffffff0f0f0f0f0f0f0f000000000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffcfcfcfcfcfcfcfc00000000fffffffffcfcfcfcfcfcfcfc00000000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffefefefefefefcfcaaaa0000fffffffffefefefefefefcfcaaaa0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffaaaaaaffaaaa00ffaaaa00ffffffffffaaaaaaffaaaa00ffaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffccccccffccccccff000000ffffffffffccccccffccccccff000000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffeeeeeeffeeeeccffaaaa00ffffffffffeeeeeeffeeeeccffaaaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffffffff0f0f0fff0f0f0ff000000fffffffffff0f0f0fff0f0f0ff000000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffafafafffafaf0ffaaaa00fffffffffffafafafffafaf0ffaaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffcfcfcfffcfcfcff000000fffffffffffcfcfcfffcfcfcff000000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffefefefffefefcffaaaa00fffffffffffefefefffefefcffaaaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeaa00aa00aa00aa00aa00aa00aa00aa00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_145 : Nat := 0x3000300000000000000000000000000030003
def goal_145 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_145 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_152 : Nat := 0x101010100000000000000000000000001010101
def goal_152 : Nat := 0xffffff00ffffff00ffffff00ffffff00ff000000ff000000ff000000ff000000
def roots_152 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffaaaa00ffaaaa00ffaaaa00ffaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffccff000000ff000000ff000000ff000000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffaaaa00ffaaaa00ffaaaa00ffaaaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xffffff00ffffff00ffffff00ffffff00ff000000ff000000ff000000ff000000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xffffffccffffffccffffffccffffffccff000000ff000000ff000000ff000000
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffaaaa00ffaaaa00ffaaaa00ffaaaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeecccccccc00000000cccccccc00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfcfcfcfcccccccccfcfcfcfcccccccccfcfcfcfc00000000fcfcfcfc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfefefefeeeeeeeeefefefefeeeeeeeeefcfcfcfc00000000fcfcfcfc00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffccffccffccffccffccffccffccffcccccccccc00000000cccccccc00000000
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeeecceeccaa00aa00eecceeccaa00aa00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffafffaffaaffaafffafffaffaaffaafaf0faf0aa00aa00faf0faf0aa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffcfffcffccffccfffcfffcffccffccfcfcfcfc00000000fcfcfcfc00000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffefffeffeeffeefffefffeffeeffeefefcfefcaa00aa00fefcfefcaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffccccffffccccffffccccffffcccccccccccc00000000cccccccc00000000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeeeccccaaaa0000eeeeccccaaaa0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffcfcffffccccfffffcfcffffccccfcfcfcfc00000000fcfcfcfc00000000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffefeffffeeeefffffefeffffeeeefefefcfcaaaa0000fefefcfcaaaa0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffccffffffccffffffccffffffccffccccccff000000ffccccccff000000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffeeeeccffaaaa00ffeeeeccffaaaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffff0ffffff00fffffff0ffffff00fff0f0f0ff000000fff0f0f0ff000000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffcffffffccfffffffcffffffccfffcfcfcff000000fffcfcfcff000000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffeffffffeefffffffeffffffeefffefefcffaaaa00fffefefcffaaaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_193 : Nat := 0x3000000000000000300000000000000030000000000000003
def goal_193 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000
def roots_193 : List Nat := [xs256.getD 0 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_194 : Nat := 0x5000000000000000500000000000000050000000000000005
def goal_194 : Nat := 0xffffffffffffffffcccccccccccccccccccccccccccccccc0000000000000000
def roots_194 : List Nat := [xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaafafafafafafafafa0000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xffffffffffffffffccccccccccccccccfcfcfcfcfcfcfcfc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeefefefefefefefefe0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaaaaaaaaaaaaaaaaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffffccffccffccffcccccccccccccccccc0000000000000000
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffeeffeeffeeffeeeeeeeeeeeeeeeeeeaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xffffffffffffffffff00ff00ff00ff00f0f0f0f0f0f0f0f00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xffffffffffffffffffaaffaaffaaffaafafafafafafafafaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xffffffffffffffffffccffccffccffccfcfcfcfcfcfcfcfc0000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xffffffffffffffffffeeffeeffeeffeefefefefefefefefeaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffffffccccffffcccccccccccccccccccc0000000000000000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffeeeeffffeeeeeeeeeeeeeeeeeeeeaaaa0000aaaa0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xffffffffffffffffffff0000ffff0000f0f0f0f0f0f0f0f00000000000000000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xffffffffffffffffffffaaaaffffaaaafafafafafafafafaaaaa0000aaaa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xffffffffffffffffffffccccffffccccfcfcfcfcfcfcfcfc0000000000000000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xffffffffffffffffffffeeeeffffeeeefefefefefefefefeaaaa0000aaaa0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffffffffffffffffffff00ffffff00ff000000ff000000ff000000ff000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffffaaffffffaaffaaaaaaffaaaaaaffaaaa00ffaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffffccffffffccffccccccffccccccff000000ff000000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffeeffffffeeffeeeeeeffeeeeeeffaaaa00ffaaaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xffffffffffffffffffffff00ffffff00fff0f0f0fff0f0f0ff000000ff000000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xffffffffffffffffffffffaaffffffaafffafafafffafafaffaaaa00ffaaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xffffffffffffffffffffffccffffffccfffcfcfcfffcfcfcff000000ff000000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xffffffffffffffffffffffeeffffffeefffefefefffefefeffaaaa00ffaaaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffffffffffccccccccccccccccffffffffcccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeffffffffeeeeeeeecccccccc00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffff0f0f0f000000000fffffffff0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffafafafaaaaaaaaafffffffffafafafaf0f0f0f000000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffcfcfcfcccccccccfffffffffcfcfcfcfcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffefefefeeeeeeeeefffffffffefefefefcfcfcfc00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffff00ff00ff00ff00ffffffff000000000000000000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffffffffaaaaaaaaaa00aa00aa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffccffccffccffccffffffffcccccccccccccccc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffffffffeeeeeeeeeecceeccaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffff0fff0ff00ff00fffffffff0f0f0f0f0f0f0f000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffafffaffaaffaafffffffffafafafafaf0faf0aa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffcfffcffccffccfffffffffcfcfcfcfcfcfcfc00000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffefffeffeeffeefffffffffefefefefefcfefcaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffccccffffccccffffffffcccccccccccccccc00000000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffffffeeeeeeeeeeeeccccaaaa0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffafaffffaaaafffffffffafafafafafaf0f0aaaa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffcfcffffccccfffffffffcfcfcfcfcfcfcfc00000000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffefeffffeeeefffffffffefefefefefefcfcaaaa0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffffffaaaaaaffaaaa00ffaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffccffffffccffffffffffccccccffccccccff000000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffeeffffffeeffffffffffeeeeeeffeeeeccffaaaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffff0ffffff00fffffffffff0f0f0fff0f0f0ff000000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffaffffffaafffffffffffafafafffafaf0ffaaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffcffffffccfffffffffffcfcfcfffcfcfcff000000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffeffffffeefffffffffffefefefffefefcffaaaa00
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_25
def pG:List (Nat×Nat):=[(1,9),(1,17),(8,9),(8,24),(16,17),(16,24)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3f
def xsM:=roots_25.map (·&&&dom_25)
def gM:=goal_25&&&dom_25
def NN:Nat→Nat
|2=>1
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|2,0=>0x22873
|3,0=>0x22873
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3030000c000c02020202
|_,_=>0
def sP:Nat→Nat
|0=>0x924
|_=>0
def sO:Nat→Nat→Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wAt:=mkWire dB 3 26 0x3ffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_25 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_25 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_25==dom_25)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_25 gM v ys):RunD true dom_25 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_25 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_25 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_25 gM s xsM):False:=by
  have hmin:2≤s:=by have hl:=run_len h;change 3≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_25 roots_25 goal_25 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_25
theorem lowS_25:Lower true dom_25 roots_25 goal_25 4:=S_25.noCircuit
def isoMvS_98:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_98:Lower true dom_98 roots_98 goal_98 4:=lower_iso_b isoMvS_98 (by decide +kernel) lowS_25
def isoMvS_100:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_100:Lower true dom_100 roots_100 goal_100 4:=lower_iso_b isoMvS_100 (by decide +kernel) lowS_25
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_25
def isoMvS_145:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_145:Lower true dom_145 roots_145 goal_145 4:=lower_iso_b isoMvS_145 (by decide +kernel) lowS_25
def isoMvS_152:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_152:Lower true dom_152 roots_152 goal_152 4:=lower_iso_b isoMvS_152 (by decide +kernel) lowS_25
def isoMvS_193:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_193:Lower true dom_193 roots_193 goal_193 4:=lower_iso_b isoMvS_193 (by decide +kernel) lowS_25
def isoMvS_194:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_194:Lower true dom_194 roots_194 goal_194 4:=lower_iso_b isoMvS_194 (by decide +kernel) lowS_25
namespace S_75
def pG:List (Nat×Nat):=[(1,9),(1,65),(2,66),(3,11),(3,67),(8,9),(10,11),(10,74),(64,65),(64,66),(72,73),(72,74)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_75.map (·&&&dom_75)
def gM:=goal_75&&&dom_75
def NN:Nat→Nat
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x87e93
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000000000000000f00c0c0000000000000c0ca0a0000000000000a0af0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xe4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|_,_=>0
def wAt:=mkWire dB 4 76 0xfffffffffffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_75 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_75 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_75==dom_75)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_75 gM v ys):RunD true dom_75 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_75 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_75 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_75 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_75 roots_75 goal_75 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_75
theorem lowS_75:Lower true dom_75 roots_75 goal_75 4:=S_75.noCircuit
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_slice_b [(0x30303030000000000000000,1,65)] (by decide +kernel) lowS_25
theorem lowS_102:Lower true dom_102 roots_102 goal_102 5:=lower_slice_b [(0x44000000440000004400000044,32,34)] (by decide +kernel) lowS_100
namespace S_153
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,129),(8,9),(8,24),(8,136),(16,17),(16,24),(16,144),(128,129),(128,136),(128,144)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_153.map (·&&&dom_153)
def gM:=goal_153&&&dom_153
def NN:Nat→Nat
|3=>3
|4=>7
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x42462298961b196
|4,0=>0x5fdc05f2df489e32fe7e1dd111aef80cd57
|5,0=>0x747c0351d028e2
|6,0=>0x747c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x303030300000000000000000000000003000300c080c080000000000000000000000000c080c0b03030200000000000000000000000003030302c0c0c000000000000000000000000000c0c0c00000000000000000000000000000000030303004040400000000000000000000000000040404030300000000000000000000000000000302000000000000000000000000000000000000c0c0c0a02020200000000000000000000000002020202c0c00000000000000000000000000000c0c000303030300000000000000000000000000000000c0c08080000000000000000000000000c0c080b03030300000000000000000000000003030000c000c000000000000000000000000000c000c0303030300000000000000000000000002020202
|_,_=>0
def sP:Nat→Nat
|0=>0x51645164b51645e1645e1065d104c5164b3164a51643510451694816475163210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x21022004
|4,0=>0xa952aa0536a5948a8c5
|5,0=>0xe51a2af5
|6,0=>0x3d4
|_,_=>0
def wAt:=mkWire dB 15 154 0x3ffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x514516445161591565456455946551
|_=>0
def oO:Nat→Nat→Nat
|3,0=>2
|4,0=>0x82620042002200
|5,0=>0xb1a1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfcb9630
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>1
|4,0=>0xe8610
|5,0=>0x136
|6,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_152 4 roots_152 ops++addP pm 1 dom_137 4 roots_137 ops++addP pm 2 dom_25 4 roots_25 ops++addP pm 3 dom_145 4 roots_145 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_153 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_152 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_25 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_145 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_152 4 s (0,roots_152.map (·&&&dom_152)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_153 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_152 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_153==dom_153)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_153 gM v ys):RunD true dom_153 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_153 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_153 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_153 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_153 roots_153 goal_153 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_153
theorem lowS_153:Lower true dom_153 roots_153 goal_153 7:=S_153.noCircuit
def isoMvS_77:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 4:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_75
def isoMvS_83:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 4:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_75
def isoMvS_85:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 4:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_75
def isoMvS_99:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_89
def isoMvS_101:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 5:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_89
def isoMvS_105:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 4:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_75
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_89
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_89
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 4:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_75
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 4:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_75
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 4:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_75
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 4:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_75
def isoMvS_195:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_102
def isoMvS_197:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 5:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_89
def isoMvS_198:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_89
def isoMvS_201:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_102
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_89
def isoMvS_204:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 4:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_75
def isoMvS_210:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_89
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 4:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_75
def isoMvS_216:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 5:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_89
def isoMvS_226:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_102
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 4:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_75
theorem lowS_59:Lower true dom_59 roots_59 goal_59 6:=lower_slice_b [(0xc0c0c0c0c0c0c0c,32,34),(0xf0f0f0f00000000,2,34)] (by decide +kernel) lowS_25
theorem lowS_79:Lower true dom_79 roots_79 goal_79 5:=lower_slice_b [(0xcccc000000000000cccc,64,66)] (by decide +kernel) lowS_77
def dzo_89_2:=0xc0c0c0c000000000c0c0c0c
def gzo_89_2:=0xc0c0c0c000000000c080800
def gsh_89_2:=0x30303030000000003020200
theorem lowS_zo_89_2_25:Lower true dzo_89_2 roots_89 gzo_89_2 5:=lower_iso_b (d1:=dom_89) (r1:=roots_89) (T1:=gsh_89_2) [(dom_89,2)] (by decide +kernel) (lower_slice_b (T:=gsh_89_2) [(0x30303030000000000000000,0,64)] (by decide +kernel) lowS_25)
namespace S_91
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,66),(3,11),(3,19),(3,67),(8,9),(8,24),(10,11),(10,26),(10,74),(16,17),(16,24),(18,19),(18,26),(18,82),(64,65),(64,66),(72,73),(72,74),(72,88),(80,81),(80,82),(80,88)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_91.map (·&&&dom_91)
def gM:=goal_91&&&dom_91
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x4ded80ca42
|5,0=>0xdef41bb4d8a39ec
|6,0=>0x9f8ac
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f00000000000f0f0f00f0f0a0a000000000f0f0a0af0f0000000000000f0f000000a000a00000000000a000a0000f0a0000000000000f0af0a0000000000000f0a0000f000f00000000000f000f00c0c0c0c000000000c0c0c0ca0a0a0a000000000a0a0a0af0f0f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x732109732108732107321603215043210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 92 0xfffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc6
|_=>0
def oO:Nat→Nat→Nat
|5,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0x1f6a040
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x8b
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_89 5 roots_89 ops++addP pm 1 dom_75 4 roots_75 ops++addP pm 2 dzo_89_2 5 roots_89 ops++addP pm 3 dom_83 4 roots_83 ops++addP pm 4 dom_25 4 roots_25 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_91 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_89_2_25 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_25 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_89 5 s (0,roots_89.map (·&&&dom_89)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_91 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_89 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_91==dom_91)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_91 gM v ys):RunD true dom_91 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_91 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_91 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_91 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_91 roots_91 goal_91 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_91
theorem lowS_91:Lower true dom_91 roots_91 goal_91 7:=S_91.noCircuit
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_slice_b [(0xaa000000aa000000aa000000aa,64,65)] (by decide +kernel) lowS_102
theorem lowS_155:Lower true dom_155 roots_155 goal_155 8:=lower_slice_b [(0xc0c0c0c0000000000000000000000000c0c0c0c,128,130)] (by decide +kernel) lowS_153
theorem lowS_167:Lower true dom_167 roots_167 goal_167 5:=lower_slice_b [(0xaa000000aa0000000000000000000000aa000000aa,128,129)] (by decide +kernel) lowS_166
namespace S_203
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(2,66),(2,130),(3,11),(3,67),(3,131),(8,9),(8,136),(10,11),(10,74),(10,138),(64,65),(64,66),(64,192),(72,73),(72,74),(72,200),(128,129),(128,130),(128,136),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_203.map (·&&&dom_203)
def gM:=goal_203&&&dom_203
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x8dfbc
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000000000000000f000000000000000f000000000000000f00c0c0000000000000c0c0000000000000c0c0000000000000c0ca0a0000000000000a0a0000000000000a0a0000000000000a0af0f00000000000000000000000000000f0f0000000000000000f0f0000000000000f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 204 0xfffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_202 5 roots_202 ops++addP pm 1 dom_139 5 roots_139 ops++addP pm 2 dom_201 5 roots_201 ops++addP pm 3 dom_195 5 roots_195 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_203 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_195 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_202 5 s (0,roots_202.map (·&&&dom_202)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_203 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_202 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_203==dom_203)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_203 gM v ys):RunD true dom_203 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_203 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_203 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_203 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_203 roots_203 goal_203 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_203
theorem lowS_203:Lower true dom_203 roots_203 goal_203 7:=S_203.noCircuit
def dzo_201_4:=0x3030000000000000303000000000000030300000000000003030
def gzo_201_4:=0x3030000000000000302000000000000030300000000000002000
def gsh_201_4:=0x303000000000000030200000000000003030000000000000200
theorem lowS_zo_201_4_137:Lower true dzo_201_4 roots_201 gzo_201_4 5:=lower_iso_b (d1:=dom_201) (r1:=roots_201) (T1:=gsh_201_4) [(dom_201,4)] (by decide +kernel) (lower_slice_b (T:=gsh_201_4) [(0x303000000000000000000000000000003030000000000000000,0,64)] (by decide +kernel) lowS_137)
namespace S_205
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(4,68),(5,13),(5,69),(5,133),(8,9),(8,136),(12,13),(12,76),(12,140),(64,65),(64,68),(64,192),(72,73),(72,76),(72,200),(128,129),(128,136),(128,192),(132,133),(132,140),(132,196)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_205.map (·&&&dom_205)
def gM:=goal_205&&&dom_205
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x91a54
|5,0=>0x21a66
|6,0=>0x70a42
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3300000000000000330000000000000033000000000000003300cccc000000000000cccc0000000000008888000000000000888b0300000000000003030000000000000303000000000000030308888000000000000888800000000000088880000000000008888033000000000000003300000000000000220000000000000022cccc0000000000000000000000000000cccc0000000000000003333000000000000333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xd191a5644688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 206 0x3fffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_201 5 roots_201 ops++addP pm 1 dom_204 4 roots_204 ops++addP pm 2 dzo_201_4 5 roots_201 ops++addP pm 3 dom_197 5 roots_197 ops++addP pm 4 dom_137 4 roots_137 ops++addP pm 5 dom_77 4 roots_77 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_205 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_201_4_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_77 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_201 5 s (0,roots_201.map (·&&&dom_201)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_205 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_201 h
def symsG:List (List (Nat×Nat)):=[[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_205==dom_205)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_205 gM v ys):RunD true dom_205 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_205 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_205 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_205 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_205 roots_205 goal_205 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_205
theorem lowS_205:Lower true dom_205 roots_205 goal_205 7:=S_205.noCircuit
theorem lowS_206:Lower true dom_206 roots_206 goal_206 6:=lower_slice_b [(0x5050000000000000505000000000000050500000000000005050,64,68)] (by decide +kernel) lowS_202
theorem lowS_217:Lower true dom_217 roots_217 goal_217 8:=lower_slice_b [(0x3030303000000000000000000000000030303030000000000000000,1,65)] (by decide +kernel) lowS_153
namespace S_218
def pG:List (Nat×Nat):=[(2,66),(2,130),(8,24),(8,136),(10,26),(10,74),(10,138),(16,24),(16,144),(18,26),(18,82),(18,146),(64,66),(64,192),(72,74),(72,88),(72,200),(80,82),(80,88),(80,208),(128,130),(128,136),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_218.map (·&&&dom_218)
def gM:=goal_218&&&dom_218
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x33705
|4,0=>0x3c1e810db606c2b03044
|5,0=>0x410ca3460e307b0207a418c6b188fe0a17d09df10920b06437
|6,0=>0xc97a5613542c1311a861
|7,0=>0xc97a5
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa0a0808000000000a0a080941410100000000014141010000000001414101000000000141410128280000000000002828282800000000282800000000000028280005050505000000000505050500000000050504040000000005050404202020200000000020202020000000000000000000000000000000000000000000000014141414000000000000000000000000141410100280000000000000028002800000000002800000000000000280005050505000000000505050500000000050500000000000005050000a0a0a0a0000000000000000000000000a0a0a0a000000000000000141414140000000014140000000000000000000000000000000000020202020000000002020202000000000202020200000000020202025050505000000000505050500000000000000000000000000000000a0a0000000000000a0a0000000000000a0a0000000000000a0a000140014000000000014001400000000001400140000000000140014028282828000000002828282800000000202020200000000020202025050505000000000504050400000000050505050000000000000000
|0,1=>0x28282828000000002828000000000000282828280000000028280000050005000000000005000500000000000000000000000000000000002000200000000000200020000000000000000000000000000000000000000000000014141414000000000000000000000000141400028282020000000002828202000000000000000000000000000000000050005000000000005000500000000000500000000000000050000
|_,_=>0
def sP:Nat→Nat
|0=>0xc453906229c95188a720c4539283104a720c4539263908a720cb03906229c9140cb0391e3114e472045391a3114e460c453906209c8b50c4520ca93910229cc31140418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47684af19b330654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 22 219 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x19d11229171040b191191392185291
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x61420031210200
|6,0=>0x918171
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0x3fdef9db611409180
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x6104352
|6,0=>0x7a98
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_216 5 roots_216 ops++addP pm 1 dom_202 5 roots_202 ops++addP pm 2 dom_210 5 roots_210 ops++addP pm 3 dom_152 4 roots_152 ops++addP pm 4 dom_194 4 roots_194 ops++addP pm 5 dom_154 5 roots_154 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_218 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_152 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_154 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_216 5 s (0,roots_216.map (·&&&dom_216)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_218 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_216 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_218==dom_218)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_218 gM v ys):RunD true dom_218 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_218 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_218 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_218 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_218 roots_218 goal_218 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_218
theorem lowS_218:Lower true dom_218 roots_218 goal_218 8:=S_218.noCircuit
def isoMvS_61:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 6:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_59
def isoMvS_93:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 7:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_91
def isoMvS_107:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 7:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_91
def isoMvS_109:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 7:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_91
def isoMvS_115:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_91
def isoMvS_121:List (Nat×Nat):=[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 7:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_91
def isoMvS_122:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 6:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_59
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 6:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_59
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 7:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_91
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 6:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_59
def isoMvS_174:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 5:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_167
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_91
def isoMvS_182:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 5:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_167
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_91
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 6:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_59
def isoMvS_199:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 6:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_103
def isoMvS_211:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 7:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_203
def isoMvS_213:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 7:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_205
def isoMvS_214:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 6:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_206
def isoMvS_220:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 7:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_91
def isoMvS_227:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 7:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_203
def isoMvS_229:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 8:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_218
def isoMvS_230:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 7:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_203
def isoMvS_233:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 7:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_205
def isoMvS_234:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 7:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_205
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 7:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_91
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 7:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_205
theorem lowS_63:Lower true dom_63 roots_63 goal_63 7:=lower_slice_b [(0xcccccccccccccccc,32,34)] (by decide +kernel) lowS_61
theorem lowS_95:Lower true dom_95 roots_95 goal_95 8:=lower_slice_b [(0xcccccccc00000000cccccccc,64,66)] (by decide +kernel) lowS_93
theorem lowS_111:Lower true dom_111 roots_111 goal_111 8:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc,32,34)] (by decide +kernel) lowS_109
def dzo_57_2:=0xc0c0c0c0c0c0c0c
def gzo_57_2:=0xc0c0c0c0c080800
def gsh_57_2:=0x303030303020200
theorem lowS_zo_57_2_25:Lower true dzo_57_2 roots_57 gzo_57_2 5:=lower_iso_b (d1:=dom_57) (r1:=roots_57) (T1:=gsh_57_2) [(dom_57,2)] (by decide +kernel) (lower_slice_b (T:=gsh_57_2) [(0x303030300000000,0,32)] (by decide +kernel) lowS_25)
def dzo_114_8:=0x5000500050005000500050005000500
def gzo_114_8:=0x5000500050004000500040005000000
def gsh_114_8:=0x50005000500040005000400050000
theorem lowS_zo_114_8_98:Lower true dzo_114_8 roots_114 gzo_114_8 5:=lower_iso_b (d1:=dom_114) (r1:=roots_114) (T1:=gsh_114_8) [(dom_114,8)] (by decide +kernel) (lower_slice_b (T:=gsh_114_8) [(0x50000000500000005000000050000,0,16)] (by decide +kernel) lowS_98)
def dzo_106_16:=0x5050000050500000505000005050000
def gzo_106_16:=0x5050000050400000504000005000000
def gsh_106_16:=0x505000005040000050400000500
theorem lowS_zo_106_16_98:Lower true dzo_106_16 roots_106 gzo_106_16 5:=lower_iso_b (d1:=dom_106) (r1:=roots_106) (T1:=gsh_106_16) [(dom_106,16)] (by decide +kernel) (lower_slice_b (T:=gsh_106_16) [(0x500000005000000050000000500,0,8)] (by decide +kernel) lowS_98)
def dzo_27_32:=0xf0f0f0f00000000
def gzo_27_32:=0xf0e0e0c00000000
def gsh_27_32:=0xf0e0e0c
theorem lowS_zo_27_32_25:Lower true dzo_27_32 roots_27 gzo_27_32 5:=lower_iso_b (d1:=dom_27) (r1:=roots_27) (T1:=gsh_27_32) [(dom_27,32)] (by decide +kernel) (lower_slice_b (T:=gsh_27_32) [(0xc0c0c0c,0,2)] (by decide +kernel) lowS_25)
def dzo_91_32:=0xf0f0f0f000000000f0f0f0f00000000
def gzo_91_32:=0xf0f0f0f000000000f0e0e0c00000000
def gsh_91_32:=0xf0f0f0f000000000f0e0e0c
theorem lowS_zo_91_32_25:Lower true dzo_91_32 roots_91 gzo_91_32 6:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_32) [(dom_91,32)] (by decide +kernel) (lower_slice_b (T:=gsh_91_32) [(0xc0c0c0c000000000c0c0c0c,0,2),(0xf0f0f0f0000000000000000,0,64)] (by decide +kernel) lowS_25)
def dzo_121_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_121_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c080800
def gsh_121_2:=0x3030303030303030303030303020200
theorem lowS_zo_121_2_25:Lower true dzo_121_2 roots_121 gzo_121_2 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_2) [(dom_121,2)] (by decide +kernel) (lower_slice_b (T:=gsh_121_2) [(0x3030303000000000303030300000000,0,32),(0x3030303030303030000000000000000,0,64)] (by decide +kernel) lowS_25)
def dzo_115_8:=0xf000f000f000f000f000f000f000f00
def gzo_115_8:=0xf000f000f000e000f000e000f000a00
def gsh_115_8:=0xf000f000f000e000f000e000f000a
theorem lowS_zo_115_8_98:Lower true dzo_115_8 roots_115 gzo_115_8 6:=lower_iso_b (d1:=dom_115) (r1:=roots_115) (T1:=gsh_115_8) [(dom_115,8)] (by decide +kernel) (lower_slice_b (T:=gsh_115_8) [(0xa000a000a000a000a000a000a000a,0,1),(0xf0000000f0000000f0000000f0000,0,16)] (by decide +kernel) lowS_98)
def dzo_107_16:=0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16:=0xf0f00000f0e00000f0e00000f0a0000
def gsh_107_16:=0xf0f00000f0e00000f0e00000f0a
theorem lowS_zo_107_16_98:Lower true dzo_107_16 roots_107 gzo_107_16 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_16) [(dom_107,16)] (by decide +kernel) (lower_slice_b (T:=gsh_107_16) [(0xa0a00000a0a00000a0a00000a0a,0,1),(0xf0000000f0000000f0000000f00,0,8)] (by decide +kernel) lowS_98)
def dzo_99_8:=0xf0000000f0000000f0000000f00
def gzo_99_8:=0xf0000000e0000000e0000000a00
def gsh_99_8:=0xf0000000e0000000e0000000a
theorem lowS_zo_99_8_98:Lower true dzo_99_8 roots_99 gzo_99_8 5:=lower_iso_b (d1:=dom_99) (r1:=roots_99) (T1:=gsh_99_8) [(dom_99,8)] (by decide +kernel) (lower_slice_b (T:=gsh_99_8) [(0xa0000000a0000000a0000000a,0,1)] (by decide +kernel) lowS_98)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,24),(10,11),(10,26),(10,42),(10,74),(16,17),(16,24),(18,19),(18,26),(18,50),(18,82),(32,34),(32,96),(33,35),(33,41),(33,49),(33,97),(40,41),(40,42),(40,56),(40,104),(48,49),(48,50),(48,56),(48,112),(64,65),(64,66),(64,96),(72,73),(72,74),(72,88),(72,104),(80,81),(80,82),(80,88),(80,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|4=>1
|5=>3
|6=>9
|7=>18
|8=>10
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x540e2
|5,0=>0xbb69e2c99800022
|6,0=>0x3c8342c99c251d7219410dbcf07cd101d6e00366000fa
|7,0=>0x9a1b599a476c7f147c683741435f0c2963a264ea1fb3e1dab61c0861be1a197810dbd3064a90594500e26003ce
|8,0=>0x80dcd6900d62b5b5e0f547c68450bc32d0c1cf4b15bd407721
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f000f0f0f000f0f0f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f00000000c0c0c0c0c0c0c0c0c0c0c0c0000000000a000a000a000a000a000a000a000af000a000f000a000f000a000f000a000000f0a00000f0a00000f0a00000f0a00000000f0f0f0f000000000c0c0c0cf0f00000f0f00000f0f00000f0f0000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f000000000c0c0c0c0000000000f000a000f000a000f000a000f000af0f0f0f000000000f0f0f0f00000000f0e0c0c0f0e0c0c0f0e0c0c0f0a0000f000f000f000f000f000f000f000f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0000000000000000
|0,1=>0xf0f0f0f0000000000000000f0f0f0f0f0f0f0f000a000a000a000af0f0f0f000a000a0f0f0f0f000a000a0000000000000000a0a0a0a0a0a0a0a50505050505050500000000000000000000f0f00000f0f0000000000000000f0000000f0000000f000f000f000f00f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c30b030b030b030b000a000a000a000aa0a0a0a0a0a0a0a0000000000000000f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a5050505050505050a0a0a0a0a0a0a0af0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0a00000f0a00000f0a00000f0a0000f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a3030303030303030000000000000000
|0,2=>0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c4040404040404040c0c0c0c0c0c0c0ce0e0e0e0e0e0e0e0c0c0c0c0c0c0c0c00f000f000f000f0000000000000000f0f000f0f0f000f0f0f00000f0f0000a0a0a0a000000000a0a0a0a0a0a0a0a
|_,_=>0
def sP:Nat→Nat
|0=>0x3007c42021c17803843c80870407442021c10042021dc6c42191c10044480870404042021d43c80870490042021c15c010808755438408704a00e1120870401081c11404043c808d04010808d04c0082c71810021c12890081c60450040c2040
|1=>0x1080870408842021d50401080870406e71080870409842021c10042021c101f3842021c102510f2021c10042021d55842029010042021d50401080a30401082c70401210870402021c124010808706000e1112021c10043c80870407c42021c1
|2=>0x1080870401080870405843c8087040108087040
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x45816c056
|6,0=>0x4e523b901c74c337163895c3ce177
|7,0=>0x18f0c165db2d1d5cca8651327192ae8d842c1f60ece6e833b9858b6c538
|8,0=>0x21af0678033e5de4eeb7723b75dacecf7
|9,0=>0x1146
|_,_=>0
def wAt:=mkWire dB 40 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1002024202040410210148111008401107480904041001d6c10004047590401108201488908098131c0417f1008805100440220242061008031081840120244310818103040826b20088051c0955b0404100604c701556c10104013230815320081510b2014e1c1004e1c1004206
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x103388002cc921c8520c803
|7,0=>0xd0b22c0af1b4ab2a4a7294a32849f2749b26497254932
|8,0=>0xf87d1003c1ec7a1e4781dc761
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0x8c356b07ad501fa43ab4417e80abcd0109812212876209ac353f8627b0c25e180ac21fd8340a045fe089fc113d8222b04414081bc0e048150a005fe00428007f8002b0001000008000080000
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x5180e210466
|7,0=>0x1276b2b6ece9882f48e3959
|8,0=>0x1f766def8fa5f
|9,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 7 roots_121 ops++addP pm 1 dom_91 7 roots_91 ops++addP pm 2 dzo_57_2 5 roots_57 ops++addP pm 3 dom_115 7 roots_115 ops++addP pm 4 dzo_114_8 5 roots_114 ops++addP pm 5 dom_107 7 roots_107 ops++addP pm 6 dzo_106_16 5 roots_106 ops++addP pm 7 dzo_27_32 5 roots_27 ops++addP pm 8 dzo_91_32 6 roots_91 ops++addP pm 9 dom_122 6 roots_122 ops++addP pm 10 dom_99 5 roots_99 ops++addP pm 11 dzo_121_2 6 roots_121 ops++addP pm 12 dzo_115_8 6 roots_115 ops++addP pm 13 dom_59 6 roots_59 ops++addP pm 14 dzo_89_2 5 roots_89 ops++addP pm 15 dzo_107_16 6 roots_107 ops++addP pm 16 dom_98 4 roots_98 ops++addP pm 17 dzo_99_8 5 roots_99 ops++addP pm 18 dom_25 4 roots_25 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_57_2_25 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_114_8_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_106_16_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_27_32_25 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_91_32_25 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_121_2_25 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_115_8_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_89_2_25 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_107_16_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_99_8_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_25 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 7 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 18 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
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
theorem lowS_126:Lower true dom_126 roots_126 goal_126 7:=lower_slice_b [(0x44444444444444444444444444444444,32,34)] (by decide +kernel) lowS_124
theorem lowS_175:Lower true dom_175 roots_175 goal_175 8:=lower_slice_b [(0xf0f00000f0f000000000000000000000f0f00000f0f0,32,36)] (by decide +kernel) lowS_171
def dzo_155_32:=0xf0f0f0f0000000000000000000000000f0f0f0f00000000
def gzo_155_32:=0xf0f0f0e0000000000000000000000000f0e0e0c00000000
def gsh_155_32:=0xf0f0f0e0000000000000000000000000f0e0e0c
theorem lowS_zo_155_32_153:Lower true dzo_155_32 roots_155 gzo_155_32 8:=lower_iso_b (d1:=dom_155) (r1:=roots_155) (T1:=gsh_155_32) [(dom_155,32)] (by decide +kernel) (lower_slice_b (T:=gsh_155_32) [(0xc0c0c0c0000000000000000000000000c0c0c0c,0,2)] (by decide +kernel) lowS_153)
namespace S_187
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,129),(2,34),(2,130),(3,11),(3,19),(3,35),(3,131),(8,9),(8,24),(8,136),(10,11),(10,26),(10,42),(10,138),(16,17),(16,24),(16,144),(18,19),(18,26),(18,50),(18,146),(32,34),(33,35),(33,41),(33,49),(33,161),(40,41),(40,42),(40,56),(40,168),(48,49),(48,50),(48,56),(48,176),(128,129),(128,130),(128,136),(128,144),(160,161),(160,162),(160,168),(160,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_187.map (·&&&dom_187)
def gM:=goal_187&&&dom_187
def NN:Nat→Nat
|4=>3
|5=>24
|6=>55
|7=>20
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x3da6c0b07001446
|5,0=>0x9dac16fa816915466c6862348535a2495cb460583c5b8389b4379eb2b47924b901e1381b4a918a6c1688c1187f118660f82b0b07008e7705a8c00734
|6,0=>0xb892ab73d8a658e8c88189478815cf720c16fb6e6cb346b91463f9a63bd4535a25186848ded47e24433603ab9537446355f233ff931e0b31925302e72ce502b55d2a340288a525c3425b1b24b901f0f51e5921b4a91a96519b6d1909d1884b16930144801274d11fc1119230d5990c93e0a32909cf107e86071610559505528044bd0408102a7101ff7
|7,0=>0x7003865e856270453dc24787f44d1a433603ea54342b8220eb1c80e191ec1673712e24103a60d89c0c5e00235100f2b00598
|8,0=>0x824c96a8884e612
|9,0=>0x3dbb0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0c0f0f0f0c00000000000000000e0e0e0c0e0e0e0cf0f0f0f0f0f0f0f00000000000000000000000000000000f0f00000f0f000000000000000000000f0f00000f0f0000f0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0a0000f0f00000f0f000000000000000000000f0000000f00f0f0f0f0f0f0f0f00000000000000000f0f00000f0f0000f0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0f0af0f0a0a0f0f0a0a00000000000000000f0f0a0a0f0f0a0af0f0f000f0f0f0000000000000000000a0a0a000a0a0a00f0f0f0a0f0f0f0a00000000000000000f0f00000f0f0000a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0af0f0f0f0000000000000000000000000f0f0f0f00000000f0f0f0f0f0f0f0f00000000000000000f000f000f000f00c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0ca0a0f0f0a0a0f0f00000000000000000a0a0a0a0a0a0a0a0000f0a00000f0a000000000000000000000f0a00000f0a
|0,1=>0xf0000000f00000000000000000f0f00000f0f0000a0a0a0a0a0a0a0a00000000000000000a0a0a000a0a0a00f0f0f0a0f0f0f0a00000000000000000f0f0f0a0f0f0f0af0f0f0f0f0f0f0f00000000000000000f0f0a0a0f0f0a0a50505000505050000000000000000000505050005050500f0f0f0a0f0f0f0a0000000000000000000000000000000050505050505050500000000000000000505050005050500f0f0f0f0f0f0f0f0000000000000000000f000a000f000a00f000f000f000f0000000000000000000000000000000050505050505050500000000000000000000000000000000f0f0f000f0f0f0000000000000000000f0f0f000f0f0f00f0f05050f0f050500000000000000000f0f00000f0f0000f0f0a0a0f0f0a0a00000000000000000f000a000f000a0000f000f000f000f0000000000000000000f0000000f0000f0a0f0a0f0a0f0a00000000000000000000000000000000f000f000f000f0000000000000000000f000f000f000f00
|0,2=>0x50505050505050500000000000000000500050005000500a0a0a000a0a0a0000000000000000000f0f0f000f0f0f00f0a0f0f0f0a0f0f00000000000000000f0a0f0a0f0a0f0af0f000f0f0f000f00000000000000000f0f000a0f0f000af0f0f0f0f0f0f0f00000000000000000f0f0f000f0f0f000000f0f00000f0f000000000000000000000000000000000000f0f00000f0f000000000000000000000a0a00000a0a0000a0f00000a0f000000000000000000000a0a00000a0af0f0f0f0f0f0f0f00000000000000000f0a0f0a0f0a0f0a00000000000000000000000000000000f0f0f0a0f0f0f0af0f0a0a0f0f0a0a00000000000000000000000000000000f0f0e0e0f0f0e0e00000000000000000c0c0c0c0c0c0c0c00000000000000000000000000000000f0f0a0a0f0f0a0af0f0f0a0f0f0f0a00000000000000000f000f000f000f00f0f0f0e0f0f0f0e00000000000000000c0c0c0c0c0c0c0cf0f00000f0f000000000000000000000f0a00000f0a0000
|0,3=>0xf000a000f000a0000000000000000000f000a000f000a005000500050005000000000000000000000000000000000000505000005050000000000000000000000000000000000005000000050000000000000000000f000f000f000f000000000000000000000000000000000050505000505050000000050000000500000000000000000000000000000000f000f050f000f0500000000000000000f000f000f000f0000f000f000f000f0000000000000000000f000a000f000aa0a0a0a0a0a0a0a00000000000000000f0f0f0a0f0f0f0a000000f0000000f00000000000000000000000a0000000af0f000f0f0f000f00000000000000000f0f00000f0f000050505050505050500000000000000000505000005050000a0a0a0f0a0a0a0f00000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0a0f0f0f0a000000f0000000f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x12040214e10a7d008511009e2ce11d34308c11c3490c210d0c26d610a40215a10d40264e10d08561710640214e10d2421ce11550308511008100e10d41308c1021522ce1060c21443503c538434908c2c420a2430842030871060c21440c2040
|1=>0x14e108402152384b0d40214e12b40214b38435008549610d25008138434340216910a40216510d4021683843504c214e12040230538454a08548e12635008538454840230e10d42414e11570908e10d0c23001158c908e10a89008510d42114e
|2=>0x10d40233338474d0c214e10d0d008114420a40230e12b3500993843500853b210d9d0085a84c4d40214e10d40264e10829008c10d402305c0419008538428d25008c10d0d008cbc4b8d40214e11540214b38435008560e12334940238436d402
|3=>0x9e38435008539a12b35009e384350085e8e10d40214ee4437840214e11c343402144350085dce13635008538481008538434340264e11c34940238435009b39612b3500853843430856ce10d243085a8454d40264e10d40217538457440214e
|4=>0x85384acd40214e10d40217e38474d40214e10d2500853bd10d0d008c14e10d4021733848cd40214e10829008538434340230510d0d0085bce10d4020453843500853bc10d0d008558454d40230538437b08538454824238418d40214e115350
|5=>0x10d40214e10d40214e5c434340214e115350085384acd0d00853843500853a5108349402384ad535008538434940214ea84755350
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa50154005
|5,0=>0x2618926231886620187a61d186e61a18626171856614184a611183e60e183260b1826608541b605580f6
|6,0=>0x211682da0477f5df677bdde87785dda774ddcc7715dbf66e1db176a9da37671d957639d877601d7975c9d6b7591d5d7559d4f7521d4264f193574bd9287485d1a744dd0c7415cfe73ddcf073a5ce2736dcd473398c77301cb972c9cab7291c9e6
|7,0=>0xa8e29c7a55e8d8a1627d89d9e6f79a1e6089622517929e4378f1e3488b5e26787de178
|8,0=>0x2b97ac9eab7
|9,0=>0x2c06
|_,_=>0
def wAt:=mkWire dB 63 188 0xfffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x14e4d1534e553a40d4d4524e05410c5d039556d035acdd539350483b14d4a4334e4c4314e6b372904d3916a4d3a30dc53934e4838345480c34550399cd0c4114e4a4334e5d3b54550350a5483814d4d3114e426974e151540d483934555303504539356453a0c81039351503924e1015
|1=>0x14d4d1534e453940e431740e45a934e883a14d453a40e4d4114e509720e0535350454114d6b1454e5d38545503574e951540d4c3514e67340c55039ac5c33530d45394056b1754e553214e4dc154e9035285c53934e45a934e8d1514e4d390cd50396ce951740d49394056b170cd5039
|2=>0x40e903940d433540e483814d454114d553940d501534e951540d433540e484314d551540d493a405453940e4a1734e483b
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1120000000000d40000000000000b2000000000000000083062000042000004000000000
|6,0=>0x6e36b30006926630000006330006120000005e35c25a20000000005915725525234f30004d24a34824534320004033d33b23830003623423130002f20002d22b22830002622422130001e31b3192163000133
|7,0=>0x9729529329128f28d28b28928728528328127f27d27b2792772752732712
|8,0=>0x9b19a1991
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x6ed3f310bf2ecaf27c9b23c86214822007f15045104400fc2907c160501002c09020060100300800
|1=>0x37fd1b1fabe8b
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xc00001400000030000000040c0040180000
|6,0=>0x62c00cc0001800c000d0c30003930c35420036011c80066c15c05014000c00483c00c36c0344245018
|7,0=>0x45c89d66349e9205cd79f69671c84a
|8,0=>0x1c712
|9,0=>0xd
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_155 8 roots_155 ops++addP pm 1 dom_186 7 roots_186 ops++addP pm 2 dom_179 7 roots_179 ops++addP pm 3 dzo_155_32 8 roots_155 ops++addP pm 4 dom_171 7 roots_171 ops++addP pm 5 dom_153 7 roots_153 ops++addP pm 6 dom_163 4 roots_163 ops++addP pm 7 dom_59 6 roots_59 ops++addP pm 8 dom_170 4 roots_170 ops++addP pm 9 dom_178 4 roots_178 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_187 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_155_32_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_178 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_155 8 s (0,roots_155.map (·&&&dom_155)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_187 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_155 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_187==dom_187)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_187 gM v ys):RunD true dom_187 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_187 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 55 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 55 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 20 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 20 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_187 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_139_4:=0xf0f00000000000000000000000000000f0f0
def gzo_139_4:=0xf0e00000000000000000000000000000a000
def gsh_139_4:=0xf0e00000000000000000000000000000a00
theorem lowS_zo_139_4_139:Lower true dzo_139_4 roots_139 gzo_139_4 5:=lower_iso_b (d1:=dom_139) (r1:=roots_139) (T1:=gsh_139_4) [(dom_139,4)] (by decide +kernel) (lower_slice_b (T:=gsh_139_4) [] (by decide +kernel) lowS_139)
def dzo_203_4:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0
def gzo_203_4:=0xf0f0000000000000f0e0000000000000f0f0000000000000a000
def gsh_203_4:=0xf0f0000000000000f0e0000000000000f0f0000000000000a00
theorem lowS_zo_203_4_139:Lower true dzo_203_4 roots_203 gzo_203_4 6:=lower_iso_b (d1:=dom_203) (r1:=roots_203) (T1:=gsh_203_4) [(dom_203,4)] (by decide +kernel) (lower_slice_b (T:=gsh_203_4) [(0xf0f00000000000000000000000000000f0f0000000000000000,0,64)] (by decide +kernel) lowS_139)
namespace S_207
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(2,66),(2,130),(3,11),(3,67),(3,131),(4,68),(5,13),(5,69),(5,133),(6,70),(6,134),(7,15),(7,71),(7,135),(8,9),(8,136),(10,11),(10,74),(10,138),(12,13),(12,76),(12,140),(14,15),(14,78),(14,142),(64,65),(64,66),(64,68),(64,192),(72,73),(72,74),(72,76),(72,200),(128,129),(128,130),(128,136),(128,192),(132,133),(132,134),(132,140),(132,196)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_207.map (·&&&dom_207)
def gM:=goal_207&&&dom_207
def NN:Nat→Nat
|3=>1
|4=>30
|5=>85
|6=>62
|7=>14
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x13e51
|4,0=>0xf2a33ee4a5e720ce6066dce5ec8337c285bbbafaa29117a34b776907298f6f59d66c93643205aaac55a7a54cbe497032961327fbb220f91cdda174af118d80e55d07e3f05ae703440015ad
|5,0=>0xff6cffede8fe1acf7adaf1374f0a47eeb62ed546eb106de7d7d733cd56c8d4e51d2a99d0789cd18dcc67bcc470cac3bc7d6fc742cc608cc3c5ec35bac23dfc08a1bf0fdbc2c4b9c78b61b4b5b68b1581afbdca8e92a7b00a33d39f10d9ccad9c5459c1ce95d5c94a818feea8a9bb7d74474f3b6fb3c6df0e62f666139f5dc475ca5c5ac3956cb44c09d48cac45875442ad440293d167387fc33289327032fc992f3122e0142c7cf2aceb270ae2606e24d5d2133616a7210bfc10b710ee6f0c6770b676084fc07f31037a3036c802e6d02d9000a2c
|6,0=>0xfaf44f69d5f6215f3943eea45ea52de9519e2b33dd16fdd03bdbf78d56fdc9a8ac460fc39fcc276fc0d50bc016b5da8b09a9af788aeb87acb37a7faca446ba0e0a9f3209dee69baa691fc091d0a8f1778e9918e61280f4380e567e50e7db2d771be6ea556a972698b4689c764cd0639b35ad7351c2a50fee4d64d495cc478ca466fc441b627c93258db1f6441efd5163fc136e30d2dd083df022f2
|7,0=>0xe18edd7b68c9b4cc25deb00f0aa0629c40e5f21e3c9222eeae1f9cf0e83105caa025ca
|8,0=>0x22f88
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff000000000000ffff0000000000000f0f0000000000000000ffff000000000000ff00000000000000ffff000000000000ff00cccc000000000000cccc000000000000cccc000000000000ccccffff000000000000ffaa000000000000aaaa000000000000aaaaffff000000000000aaaa000000000000ffff000000000000aaaaeeee000000000000eeee000000000000eeee0000000000000000ffff000000000000ffcc000000000000cccc000000000000ccccff00000000000000ff00000000000000ff00000000000000ff00aaaa000000000000aaaa000000000000aaaa000000000000aaaaffff0000000000000000000000000000ffff00000000000000001313000000000000111100000000000003030000000000000000ffff000000000000ffff00000000000000000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0eeee000000000000eeee000000000000eeee000000000000eeeeffff000000000000ff00000000000000aaaa000000000000aa00ffff000000000000ffff000000000000ffff0000000000000000
|0,1=>0xffff000000000000eeee000000000000cccc000000000000cccc5555000000000000555500000000000054540000000000005454111100000000000011110000000000000000000000000000000000000000000000000000000000000000ffff000000000000aaaaffff0000000000000000000000000000fefe00000000000000000333000000000000003300000000000003030000000000000000ffff000000000000ffff000000000000afaf000000000000aaaabbbb000000000000bbbb000000000000abab000000000000aaaaffff000000000000ffaa000000000000ff00000000000000ff00ffff000000000000ffff000000000000ffff000000000000ff0000000000000000000000000000000000afaf000000000000aaaaffff000000000000ffff000000000000ff00000000000000ff00111100000000000011110000000000000101000000000000000000000000000000000000000000000000fefe000000000000fefe3333000000000000333300000000000023230000000000002222ffff000000000000ffff000000000000aaaa000000000000aaaa
|0,2=>0xaa000000000000aaaa000000000000aaaa0000000000000000ffff0000000000000000000000000000ff00ffff00000000000000ff000000000000ffff00000000000000aaefef000000000000eeee000000000000efef000000000000eeeeffff000000000000ffff000000000000fafa000000000000fafa00ff00000000000000ff00000000000000aa00000000000000aaaaaa000000000000aaaa000000000000aaaa000000000000aa0033330000000000003333000000000000333300000000000033000f0f00000000000000000000000000000f0f0000000000000000ffff000000000000ff000000000000000000000000000000000000ff00000000000000ff00000000000000ff00000000000000aaafaf000000000000aaaa000000000000afaf000000000000aaaafefe000000000000fefe000000000000fefe000000000000fefeffff000000000000ffff000000000000ffff000000000000aaaa0fff00000000000000ff0000000000000faf00000000000000aa000000000000000000ff000000000000ffff000000000000ff00
|0,3=>0xffff0000000000005555000000000000ffff0000000000000000ffff00000000000000ff000000000000ffff0000000000000000f0ff000000000000f0ff000000000000f0fa000000000000f0fa3333000000000000333300000000000033330000000000002222bbbb000000000000bbbb000000000000bbbb000000000000aaaa3333000000000000333300000000000003030000000000000000ffff000000000000aaaa000000000000000000000000000000005f5f00000000000055550000000000000f0f000000000000000033330000000000000033000000000000333300000000000000000fff00000000000000ff0000000000000f0f000000000000000055550000000000005555000000000000050500000000000000005555000000000000555500000000000055550000000000005500111100000000000011110000000000001010000000000000101055550000000000005500000000000000555500000000000055005555000000000000555500000000000055550000000000000000f1f1000000000000f1f1000000000000f0f0000000000000f0f0
|0,4=>0x333300000000000033330000000000003333000000000000000000ff00000000000000ff000000000000000000000000000000000000000000000000ffff0000000000000000000000000000aaaa111100000000000011110000000000001111000000000000000055550000000000005555000000000000000000000000000000003333000000000000111100000000000033330000000000000000000000000000000000ff000000000000000000000000000000aa0000000000000000ffff00000000000000000000000000000000aaaa000000000000ffff000000000000aaaa000000000000aaaabbbb000000000000bbbb000000000000aaaa000000000000aaaaffff000000000000ff00000000000000ffff000000000000000000000000000000000000000000000000ffff000000000000ff00000000000000000000ff0000000000000000000000000000000000ff00000000000000ff00000000000000ee00000000000000ee00aa00000000000000ff00000000000000aa00000000000000aaffff000000000000ffff000000000000f0f0000000000000f0f0
|0,5=>0xff000000000000000000000000000000ff00fafa000000000000fafa000000000000fafa000000000000fafaf5f5000000000000f5f5000000000000f0f0000000000000f0f05555000000000000555500000000000050500000000000005050ff00000000000000ffff000000000000ff00000000000000ff0000ff00000000000000ff00000000000000ff0000000000000000ffff000000000000ffff000000000000eeee000000000000eeee0000000000000000555500000000000000000000000000000000ffff000000000000ffaa000000000000ffff000000000000ffaaffff000000000000eeee000000000000ffff000000000000eeeef0ff000000000000f0ff000000000000f0f0000000000000f0f0ffff000000000000ffff000000000000fefe000000000000fefe
|_,_=>0
def sP:Nat→Nat
|0=>0x634386100cf87002011e0c104120e18e8e0608e04100839b0820386341040232182031a1c0801060386085c18d2018b031a3030304043041008a86085018d18184070c4c20e06088001c0c487002090220184072218208044030f1c0c68c002018b1410403121c0080e182840608080
|1=>0x8218020e1820e063578608397031a1c2031a1d68608201240c1042c041c304060882a0c1158d0ea83041c0c6a90c10703041c0041c0c3a80c1040220193842c0c6870c984033e1c30406343a50c1040d484030410481070c1070304882080634600100c80614343a10c1018d1604220
|2=>0xe01c885608806083818220182081a403861e381890e182081a1c338082018d1640008061c337083818d681820e0634606083818d441c2080624386085c18d0e182081a1c336082118220182081a1c335082018d6818208041d986082018d181820e0609906083818d0ec42080608e06
|3=>0x100c1470c1040305183041c0c6878a122031a1c3431c0c68b64107031a1c02606083c20c1018d0f043041a1d5064e1018d0e04304100c1220c1200d0ea83041c0c6877e1040d2a1c304100c68700987031a1df047a343aa0c104030ef0304100dd870c104070ce820e0634807002018d
|4=>0x1e10403042c00411401070c104030ea03041c0c3809e107031a2c8041c0c687012ca031a1c326880c6870d384030534304100c11000184030e185041c0c69c0e104030e1a6041d1018d0e0040d0e187cb100c38694104031a4033906343c90c104230e1821d100c1100d2040d321c304
|5=>0x634587082200d201c304100c6877e182080608806082158d0e1820806343be0c104031a2c380082018d0f34304100c6900e0030e0634386092c403a408386082018d201c348100c6c70e1820e880c6870c10b0e0634386082288d0e182080e187ba0838182161044004403041008386
|6=>0x100c3800d3c20806345900c104030e1a784100c6870c12a0806343800d2e98e0634386082018d0e1824328206870c9c20e06343b20c107031a1c004100c69c0e1821411006870c104020e1938410343861e1040d481c30410343864e127088008386080c6900ea830410348070c9c20e
|7=>0x1a1c331082018d0e182261c5018d0e182085c0c6870c10703041c30410343864e1258e0634386093ab880634386082158d201c304100c107001820e06348070c104031a1c304722018216182080634386ac10403041c304903818d0e18243100ea820e1820e100c6870010423041c304
|8=>0x100c6870c10403041c304100c6870c1270806348070c107080634386083818d0e1820806343800c104031a1c3049022d0d0e182080634386092c4031a2c38608201820e1821d1c0c6870c1130806351070c12208063438608584031a1c30406343aa0c104591a1c30410343d80c10403
|9=>0x8063438608206870c9c2088034386096c18d0e18214
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x4aa8905116a219440a87c50eea1c9436a86850c6a17942ca854509ea129422a8405076a0d9418a82c504ea08940ea8185026a039404a8045
|5,0=>0x424c831903320063f4c7d18f731e863c4c7718eb31d06394c7118df31b86364c6b18d331a06334c6518c731895306c5f58bbb17162d6c5958afb15962a6c5358a3b1416276c4d5897b1296246c47588bb1116216c41587fb0f961e6c3b5873b0e251b8c35986830ca6188c2f985c30b26158c299850309a6
|5,1=>0x28f6514aa1193f327864e4c9b1933326064b4c95192732486484c8f191b32306454c89190f32186
|6,0=>0x2183c297844f06de0a3c0e6810d0099fdbbf477daef99df033d977a4ef2dde23bbd776ceebddd4b3a27736ee51dc6bb867700cde5db93b6c66caed79dabbb507692ed09d9e3335765ceca1991331c662aec3d9843b0175f6cbd1d76bae765c2cb69d69bacc758aeaf9d5bbab07552ea89d4dba956
|7,0=>0x246b4876902d1e9e3a346d78ccf17de2cb4527896f115a1f3c377
|8,0=>0x4936
|_,_=>0
def wAt:=mkWire dB 92 208 0xffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 1000003 zs)
def oP:Nat→Nat
|0=>0x10120c11201b0e110e110c110e12101904191a1d0c120e110f210c121c1310191c1110190739101210191a1d0e1906111a1d1a020e110e12201b04000c111c13161004121a1d0c1204121c1f1c101c4016110e191a3e0e11161006410e110c1116110e1106091a1d1c1f1a1d061a1a1d0e110e111a1d061a46131a1d16111c40
|1=>0x6410e111a1d0c110e11101916100e191a1d0e191a1d0c121c12101904111a1d0c1106091a1d1a020c110e111a020c1116120e190e121c1d10191c121019061a1c1f10190c11101916130e1906111a1d061a4e11061a0e9d061a061a10121a1d061110420e110e11061a0e1910190e1106110d2d0e121a1d0e1106410e110d39
|2=>0x61a0611101b10111a1d10120e11101910190c110c12061d0e120e1904121a1d1c10101916110e191c13101910010c1110420e11072d0e12801f06110e020c111c1010191011281b10111a1d10190e12061a10191012
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11000000000000000000000000000000000000000000000000001000000000000000000000000000000000000
|5,0=>0x1d20000001c11b10000001a11910000000001811620000000000000000000000001511411311210000000000001020000000000f10000000000d20000000000000b2000000000000000000092000072061000051000041000000000000022
|5,1=>0x2932810002710000002612512410000002310002120000002010000001f1
|6,0=>0x9b29929729529329128f28d28b28928818628428228020007e27c27a27827620007427227026f16d26b26a16826626516326126015e25c25a25915725525325124f24d24b24924724524324123f23e13c23a23823623423223022e22c2
|7,0=>0xaa1a91a81a71a61a51a41a31a21a11a019f19e19d1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x9a00490023e011d008e004540228010400810040001040040001e000e0006c0031001200080003a001c000b80058002a00140008000300010000400018000800020000
|1=>0x40451426e80b2401911048627e3137169f886fc434e213f109d884cc423e21111011080804010113d089d8300c1020053f029d810ec08200200009f804f402760137
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x80000000000000000000000002000000000000000000
|5,0=>0x4c200400010410000200100010000e0070000820001040000020c000000000001611654000001e00000200002a000900140000000017905500100080000029
|6,0=>0x95a2d92d0e3d25d58c8ae640f1f7e0a007c8e86dda619218448153708173c32b744af8bb266d4d3ca79ff8f29b271
|7,0=>0xcf98eb9ebae38acb36ae3
|8,0=>0x21
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 17 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_205 7 roots_205 ops++addP pm 1 dom_198 5 roots_198 ops++addP pm 2 dzo_139_4 5 roots_139 ops++addP pm 3 dom_199 6 roots_199 ops++addP pm 4 dom_203 7 roots_203 ops++addP pm 5 dom_206 6 roots_206 ops++addP pm 6 dom_195 5 roots_195 ops++addP pm 7 dom_202 5 roots_202 ops++addP pm 8 dom_139 5 roots_139 ops++addP pm 9 dzo_201_4 5 roots_201 ops++addP pm 10 dom_204 4 roots_204 ops++addP pm 11 dom_201 5 roots_201 ops++addP pm 12 dom_79 5 roots_79 ops++addP pm 13 dzo_203_4 6 roots_203 ops++addP pm 14 dom_77 4 roots_77 ops++addP pm 15 dom_75 4 roots_75 ops++addP pm 16 dom_137 4 roots_137 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_207 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_139_4_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_201_4_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_203_4_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_137 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_205 7 s (0,roots_205.map (·&&&dom_205)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_207 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_205 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_207 gM v ys):RunD true dom_207 gM v (ori ys):=h
def Z (s:Nat):=barP dom_207 gM mpG SD SS NN hAt idxH ori 1000003 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 30 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 30 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 85 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 85 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 62 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 62 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 14 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_207 gM mpG SD SS NN hAt idxH ori 1000003 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_207 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_207 roots_207 goal_207 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_207
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=S_207.noCircuit
namespace S_219
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,66),(2,130),(3,11),(3,19),(3,67),(3,131),(8,9),(8,24),(8,136),(10,11),(10,26),(10,74),(10,138),(16,17),(16,24),(16,144),(18,19),(18,26),(18,82),(18,146),(64,65),(64,66),(64,192),(72,73),(72,74),(72,88),(72,200),(80,81),(80,82),(80,88),(80,208),(128,129),(128,130),(128,136),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_219.map (·&&&dom_219)
def gM:=goal_219&&&dom_219
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x5755f
|7,0=>0xb63217fcd06c7c461a52587d2
|8,0=>0x2fd77088ca
|9,0=>0x798d4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f0f0f0f000000000f0f0f00000000000f0f0f000000f0f0000000000000f0f0000000000000f000000000000000f00f0f0f0f000000000f0f0f0f00000000000000000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000f000f00000000000f000f00000000000f000f00000000000f000f00f0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f00f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000f0f0f0f000000000f0f0f0f000000000f000f00000000000f000f00c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0ca0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f0000000000000000000000000f0f0f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x76210873621085762108a7621084736210a736210857321087621908543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d4835c67
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 220 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1a176561765e1685cd685a1765ce685e1685d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfff637f7f9f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x7ba3
|8,0=>0x1a
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_218 8 roots_218 ops++addP pm 1 dom_155 8 roots_155 ops++addP pm 2 dom_217 8 roots_217 ops++addP pm 3 dom_211 7 roots_211 ops++addP pm 4 dom_203 7 roots_203 ops++addP pm 5 dom_91 7 roots_91 ops++addP pm 6 dom_195 5 roots_195 ops++addP pm 7 dom_75 4 roots_75 ops++addP pm 8 dom_83 4 roots_83 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_83 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_218 8 s (0,roots_218.map (·&&&dom_218)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_218 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_219==dom_219)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_219 gM v ys):RunD true dom_219 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_219 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_219 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_219 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_219 roots_219 goal_219 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_219
theorem lowS_219:Lower true dom_219 roots_219 goal_219 10:=S_219.noCircuit
def dzo_217_4:=0x30303030000000003030303000000000303030300000000030303030
def gzo_217_4:=0x30303030000000003030302000000000303030300000000030202000
def gsh_217_4:=0x3030303000000000303030200000000030303030000000003020200
theorem lowS_zo_217_4_153:Lower true dzo_217_4 roots_217 gzo_217_4 8:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_4) [(dom_217,4)] (by decide +kernel) (lower_slice_b (T:=gsh_217_4) [(0x3030303000000000000000000000000030303030000000000000000,0,64)] (by decide +kernel) lowS_153)
namespace S_221
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(4,68),(5,13),(5,21),(5,69),(5,133),(8,9),(8,24),(8,136),(12,13),(12,28),(12,76),(12,140),(16,17),(16,24),(16,144),(20,21),(20,28),(20,84),(20,148),(64,65),(64,68),(64,192),(72,73),(72,76),(72,88),(72,200),(80,81),(80,84),(80,88),(80,208),(128,129),(128,136),(128,144),(128,192),(132,133),(132,140),(132,148),(132,196)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_221.map (·&&&dom_221)
def gM:=goal_221&&&dom_221
def NN:Nat→Nat
|4=>3
|5=>15
|6=>35
|7=>15
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xb8fb53aa6b05f14
|5,0=>0xf9ebf9741f900d77aef6479664639f432413dc253836c3708926aa91fc7a1320008f3102d5c
|6,0=>0xe0adcbe03aaa922900d7888708510b7638875699647d35c9bc5656148077431e741afc34d8d33144324ba2f0112ee462b4d52448723a08220181f1a418d34184ab140eb1312b118e40e4f30b9e806799042de028350254d
|7,0=>0x969ec8a6cd795096491263ee25566e4ec6749865367362bb7f250da246c21ff96098a00445c
|8,0=>0xeb7931670b125d8
|9,0=>0x7369e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc88cc8800000000cc88cc8800000000cc88cc8800000000cc88cc8b333333300000000333333330000000033330000000000003333000000cc00cc0000000000cc00cc0000000000880088000000000088008a2222222000000002222222200000000222222220000000022222222cccccc8800000000cccccc8800000000cccccc8800000000cccccc8b3332222000000003333222200000000333322220000000033332222cc88cc8800000000cc88cc8800000000cc88000000000000cc8800033333333000000003333333300000000330033000000000033003300cccc000000000000cccc000000000000cccc000000000000cccc00033003300000000003300330000000000330033000000000033003300cccccccc00000000cccc888800000000cccccccc00000000cc0088033333300000000003333330000000000333333000000000033333300cccc888800000000cccc888800000000cc00880000000000cc0088030303030000000003030303000000000303030300000000030303030cccccccc00000000cccccccc0000000088888888000000008888888b3333333000000000000000000000000333333330000000000000000
|0,1=>0xcccc00cc00000000cccc00cc00000000cccc008800000000cccc008b33333330000000033333333000000003333330000000000333333000000cccc000000000000cccc000000000000cc00000000000000cc00000332200000000000033220000000000003322000000000000332200cc00cc0000000000cc00cc0000000000cc00880000000000cc00880001111000000000000111100000000000011000000000000001100cccccccc00000000cccccccc00000000cccccc8800000000cccccc891111111000000001111111100000000110011000000000011001100cc00cc0000000000cc00cc0000000000cc00880000000000cc00880000033330000000000003333000000000000222200000000000022220000cccc000000000000cccc000000000000cc88000000000000cc8b333333300000000333333330000000033223322000000003322332200000000000000000000000000000000cc88cc8800000000cc88cc880330022000000000033002200000000003300220000000000330022cccccccc00000000cccccccc000000000000000000000000000000033333333000000003333333300000000333322220000000033332222
|0,2=>0x3300000000000000330000000000000022000000000000002200000000000000000000000000000000cccccc8800000000cccccc8b3113311000000003311331100000000331133000000000033113300cccc000000000000cccc000000000000cc88000000000000cc8800033333333000000003333333300000000003300220000000000330022
|_,_=>0
def sP:Nat→Nat
|0=>0x30044438808c00440608c01138718231800a38f20201708c58044608c54044718508c44a2460804440c230044439408c00b38808c00718308100429308044e1820520042880810101cf20200a38608d00b1c808100a2480801c61420440c2040
|1=>0x88608c0113e118230044818231501110e3c23004460813150111c608c80045f1c608c0113873c608100724608c0111d408c34045e1c60813001cf08c74044718205c01140708c6c04441d308c0111c608c68044a1c608d0111d708c011647182
|2=>0x30044b1c608c0111c608c5804474c608c0111072023004473c60810111c608c90044e18204c5801d708130044608c54044a38f18201110e18204c0231c608c01138750608c0073c230d0111c608c6c044a3860810101d708c0112c7202300447
|3=>0x1c608c01110718230044720608c0111c608130044a38608c01110718204c0111c608c74044e1cf18230044718204c34044750608c01140718204c0112c73c608c01138720608c010287182
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x18d8bac57628b12d88ac3f61cb0cd85ac27610b06d82ac0f6
|6,0=>0x54de98f4579fb4e1e62f2a791bc71e2af0f6843c05df4ef37763b95dbced77683b25d84ebb75a3ab5d4ce9f74c3a45d14e8463eb9dd8e0e697
|7,0=>0x709f751b37d5c68e338f948c64615efb1767b7bda1ec2f5a7
|8,0=>0x75dfa0fc97
|9,0=>0x1de6
|_,_=>0
def wAt:=mkWire dB 37 222 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3d146311d151311cc4a191cc541c3d1541f20c541f1814c4518a87311818c4538f06311d1541b20c46451c846451c886451cf863138c47453d1c63118191311900e311d147191d1464538c474520cc6453ce074518c48281cc464520c4645286473120a07311914c451c151312864731
|1=>0x7191914c451cc474531147191c8864518c47451818c4520c46451c14c451cf46311d14645291473110c47191c18c453d1c631191471944c46311968706311470631150181c14c451d488311914c452d1c4311c64831191541b
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x3cc618a210414c0000008208800002
|6,0=>0x13ce694a38e600230c33824f8c003b3000e48003726a400191b025c400159a834c4909112023c4000e119300058ca1122
|7,0=>0x1b8b616a2d0598b21622c0578ae15a2b0558aa1522
|8,0=>0x1c8788f01
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x5ff5263df3012fb2df1df1dd1050ff0fb0df0d70cf07f05d05104704504104002001e01201000c00a008006004002000
|1=>0xccfc47c0cadb
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x3201106000287004
|6,0=>0xf14e30028b0570120040021c034404051c0821070400530151c1
|7,0=>0x2345a2507627a085f5196d8
|8,0=>0x16694
|9,0=>0x14
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_217 8 roots_217 ops++addP pm 1 dom_205 7 roots_205 ops++addP pm 2 dom_220 7 roots_220 ops++addP pm 3 dom_93 7 roots_93 ops++addP pm 4 dom_213 7 roots_213 ops++addP pm 5 dom_197 5 roots_197 ops++addP pm 6 dzo_217_4 8 roots_217 ops++addP pm 7 dom_153 7 roots_153 ops++addP pm 8 dom_212 4 roots_212 ops++addP pm 9 dom_85 4 roots_85 ops++addP pm 10 dom_204 4 roots_204 ops++addP pm 11 dom_77 4 roots_77 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_221 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_217_4_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_77 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_217 8 s (0,roots_217.map (·&&&dom_217)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_221 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_217 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_221==dom_221)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_221 gM v ys):RunD true dom_221 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_221 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 35 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_221 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_slice_b [(0x50505050000000005050505000000000505050500000000050505050,64,68)] (by decide +kernel) lowS_218
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_slice_b [(0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc,32,34)] (by decide +kernel) lowS_229
def dzo_137_32:=0x3030000000000000000000000000000030300000000
def gzo_137_32:=0x3020000000000000000000000000000020000000000
def gsh_137_32:=0x30200000000000000000000000000000200
theorem lowS_zo_137_32_137:Lower true dzo_137_32 roots_137 gzo_137_32 4:=lower_iso_b (d1:=dom_137) (r1:=roots_137) (T1:=gsh_137_32) [(dom_137,32)] (by decide +kernel) (lower_slice_b (T:=gsh_137_32) [] (by decide +kernel) lowS_137)
def dzo_98_8:=0x500000005000000050000000500
def gzo_98_8:=0x500000004000000040000000000
def gsh_98_8:=0x5000000040000000400000000
theorem lowS_zo_98_8_98:Lower true dzo_98_8 roots_98 gzo_98_8 4:=lower_iso_b (d1:=dom_98) (r1:=roots_98) (T1:=gsh_98_8) [(dom_98,8)] (by decide +kernel) (lower_slice_b (T:=gsh_98_8) [] (by decide +kernel) lowS_98)
def dzo_227_8:=0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f00
def gzo_227_8:=0xf0000000f0000000f0000000f0000000f0000000e0000000e0000000a00
def gsh_227_8:=0xf0000000f0000000f0000000f0000000f0000000e0000000e0000000a
theorem lowS_zo_227_8_98:Lower true dzo_227_8 roots_227 gzo_227_8 6:=lower_iso_b (d1:=dom_227) (r1:=roots_227) (T1:=gsh_227_8) [(dom_227,8)] (by decide +kernel) (lower_slice_b (T:=gsh_227_8) [(0xa0000000a0000000a0000000a0000000a0000000a0000000a0000000a,0,1),(0xf0000000f0000000f0000000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_98)
def dzo_226_8:=0x50000000500000005000000050000000500000005000000050000000500
def gzo_226_8:=0x50000000500000005000000050000000500000004000000040000000000
def gsh_226_8:=0x500000005000000050000000500000005000000040000000400000000
theorem lowS_zo_226_8_98:Lower true dzo_226_8 roots_226 gzo_226_8 5:=lower_iso_b (d1:=dom_226) (r1:=roots_226) (T1:=gsh_226_8) [(dom_226,8)] (by decide +kernel) (lower_slice_b (T:=gsh_226_8) [(0x500000005000000050000000500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_98)
def dzo_201_32:=0x30300000000000003030000000000000303000000000000030300000000
def gzo_201_32:=0x30300000000000003020000000000000303000000000000020000000000
def gsh_201_32:=0x303000000000000030200000000000003030000000000000200
theorem lowS_zo_201_32_137:Lower true dzo_201_32 roots_201 gzo_201_32 5:=lower_iso_b (d1:=dom_201) (r1:=roots_201) (T1:=gsh_201_32) [(dom_201,32)] (by decide +kernel) (lower_slice_b (T:=gsh_201_32) [(0x303000000000000000000000000000003030000000000000000,0,64)] (by decide +kernel) lowS_137)
def dzo_203_32:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f00000000
def gzo_203_32:=0xf0f0000000000000f0e0000000000000f0f0000000000000e0c00000000
def gsh_203_32:=0xf0f0000000000000f0e0000000000000f0f0000000000000e0c
theorem lowS_zo_203_32_137:Lower true dzo_203_32 roots_203 gzo_203_32 6:=lower_iso_b (d1:=dom_203) (r1:=roots_203) (T1:=gsh_203_32) [(dom_203,32)] (by decide +kernel) (lower_slice_b (T:=gsh_203_32) [(0xc0c0000000000000c0c0000000000000c0c0000000000000c0c,0,2),(0xf0f00000000000000000000000000000f0f0000000000000000,0,64)] (by decide +kernel) lowS_137)
def dzo_139_32:=0xf0f00000000000000000000000000000f0f00000000
def gzo_139_32:=0xf0e00000000000000000000000000000e0c00000000
def gsh_139_32:=0xf0e00000000000000000000000000000e0c
theorem lowS_zo_139_32_137:Lower true dzo_139_32 roots_139 gzo_139_32 5:=lower_iso_b (d1:=dom_139) (r1:=roots_139) (T1:=gsh_139_32) [(dom_139,32)] (by decide +kernel) (lower_slice_b (T:=gsh_139_32) [(0xc0c00000000000000000000000000000c0c,0,2)] (by decide +kernel) lowS_137)
namespace S_235
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(2,34),(2,66),(2,130),(3,11),(3,35),(3,67),(3,131),(8,9),(8,136),(10,11),(10,42),(10,74),(10,138),(32,34),(32,96),(33,35),(33,41),(33,97),(33,161),(40,41),(40,42),(40,104),(40,168),(64,65),(64,66),(64,96),(64,192),(72,73),(72,74),(72,104),(72,200),(128,129),(128,130),(128,136),(128,192),(160,161),(160,162),(160,168),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_235.map (·&&&dom_235)
def gM:=goal_235&&&dom_235
def NN:Nat→Nat
|4=>7
|5=>18
|6=>46
|7=>36
|8=>12
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xeaeef95bb27baba433203ec792e02f1ecca
|5,0=>0xc612fc504da3ad5a060f9554e8e1f08addb7c2d96fd106032c4535b4520e2525f2385b1ebad1949716c110818d
|6,0=>0xff3bde794ae37f8e072dcc6c4bf907b3826ac72daa973a9314a35429739e93fab8d0cf8c77e8ab02854767de427b50b726d96f6ac6e7aa6a42f6a176684ab617a36065956ff4539994f0d64ba93489b8370fe2e8642e47b25142240001f36c1d349180691492811cc80d4a80a63407b2e01035
|7,0=>0xec058cbe26b7e19a470c98ff29599a910978688b833497e0f87d91b7bf177ad6a671a3668dc63a2b6111f5d5145b5685a9685580e54e434661144e4c43df33d0122dbb82c17129cc02985a25c0f173db13426108330aa6104e4d
|8,0=>0xfffdae15d7afa9aacfbe88bd051d3d4ab7443ee62ff100fdce040d9019d0
|9,0=>0xfffda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0000000000000c0c0000000000000f0f0000000000000c0cc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0ca0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0af0f00000f0f00000f0000000f0000000f0f00000f0f00000a0000000a0000000000f0f0000000000000f0c0000000000000f0f0000000000000e0cf0f00000f0f00000f0f00000f0f00000000000000000000000000000000f0f00000f0f00000f0f00000f0f00000c0c00000c0c00000c0c00000c0cf0f00000f0f00000a0a00000a0a00000f0f00000f0f00000a0a00000a0ae0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0ef0f00000f0f00000a0a00000a0a00000c0c00000c0c0000080800000808f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f00f0f00000f0f00000c0c00000c0c00000f0f00000f0f00000c0c00000c0cf0f00000f0f00000f0f00000f0f00000a0a00000a0a00000a0a00000a0ae0e00000e0e00000e0e00000e0e00000e0e00000e0e0000000000000000
|0,1=>0xf0f00000f0f00000f0000000f0000000f0f00000f0f00000f0000000f005050000050500000505000005050000050500000505000004040000040410100000101000001010000010100000101000001010000000000000000c0c00000c0c00000c0c00000c0c00000f0f00000f0f00000e0e00000e0e00000000000000000000000000000000f0f00000f0f00000a0a00000a0a5050000050500000505000005050000040400000404000004040000040430300000303000003000000030000000303000003030000020000000200f0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f0000000050500000505000005050000050500000505000005050000000000000000f0f00000f0f00000f0f00000f0f00000f0f0000000000000c0c00000000f0f0000000000000c0c0000000000000f0f0000000000000c0c00000000f0f00000f0f00000f0f00000f0f00000e0e00000e0e00000e0e00000e0ef0000000f0000000f0000000f0000000a0000000a0000000a0000000a0000f0000000f0000000f0000000f0000000a0000000a0000000a0000000af0f00000f0f000000000000000000000f0f00000f0f0000000000000000f0f00000f0f00000f0c00000f0c00000f0f00000f0f00000e0c00000e0c
|0,2=>0xf0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000000000000000000000000000000f0f00000f0f00000e0e00000e0ef0f00000f0f00000f0f00000f0f00000f0f00000f0f00000e0e00000e0ef0f00000f0f00000f0f00000f0f00000f0f00000f0f00000a0a00000a0a0000000000000000e0e00000e0e000000000000000000000e0e00000e0ef0f00000f0f00000f0f00000f0f0000000000000f0f0000000000000c0c0000000000000000000000000000000030300000303000002020000020200000000000000000000000000000000e0e00000e0e00000e0e00000e0e000000000000000000000000000000000000000000000000e0e00000e0ef0f00000f0f00000f0f00000f0f00000f0f00000f0f00000c0c00000c0cf0f00000f0f00000f0f00000f0f00000303000003030000020200000202d0d00000d0d00000d0d00000d0d00000d0d00000d0d00000c0c00000c0c30300000303000002020000020200000303000003030000020200000202f0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f0000000030300000303000003030000030300000303000003030000000000000000f0f00000f0f00000e0e00000e0e00000f0f00000f0f00000e0e00000e0e
|0,3=>0xf0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f00f0f00000a0a00000f0f00000a0a00000f0f00000a0a00000f0f00000a0af0f00000c0c00000f0f00000c0c00000f0f00000c0c00000f0f00000c0cf0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00f0f00000f0f00000f0c00000f0c00000f0f00000f0f00000f0c00000f0c0000000000000000f0000000f00000000000000000000000f0000000f0000000000000000000000000000000000f0f0000000000000f0f0000000050500000505000005050000050500000505000000000000050500000000f0f00000f0f00000f0f00000f0f000000000000000000000e0e00000e0e
|_,_=>0
def sP:Nat→Nat
|0=>0x58d44a10308d6851031c644a10e34c64a60338815710350e20511038d30a0c758d44e54d4912840c72481440c70811440d408d1440ce2002841c24d128e3523d12840ce3461441c230a10740c28e34c3ca38d30b2840c92001031c61440c2040
|1=>0x88438d49128339504d44a1033881572840c935184a10380e0512987ce3451031ce2052840ce35e44a10324e20d14338134f44a10e34c2840ce35174a10370e3512840ce04545710739344a10308d6912840c739b44a10308d00a10238d30a0c7
|2=>0xce20d1440ed38d44a1031ceb112840eb24d44a1031c20512840ce35100a11f1ce20a0ce36a44a10338da512840e808d44a10338d1912840e038d14a1039ce3512847e638d14a10338d9512840e438d44a0ce58d44a10338d8c52847e038834a
|3=>0x12f0c238d44a103ace3512840ce04d15110380e20d44a10338dc512840c224d44a6033883512840ce3515ca10308e04d1440f038d44a10350e2112af0ce34f44a1031c23452847ce34584a10398d4612840c724844a103b8e3512840c224d158
|4=>0x2840c738144a10350e3512840ce36344a6031ce3512840c238135128338d3d12840ce20d14a10350738d44a13324e3512b27ce3512a21033813512840ceb0835128438d4d12840c724d44a60324e35110339b3512840e638d1512b20c738d44a
|5=>0x38d44ae040ce3512b710338d44ac8338d44ad840ce351284d4338d44a11f38d44a6040ce3512840c938d44a11f38d14a884d4338d44a1340ce3512b2cce3512980ce37144a61f38d44a1031ce34544a10324e20d44a10338d15184a10398e351
|6=>0x40ce3512840ce3512840c738d44a10338d1512840c2
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x1e5065414503d40a50154005
|5,0=>0x22188261f187661c186a619185e61618535135847610583b60d582f60a58236
|6,0=>0x6fddb876c5daa768dd9c7655d8e761dd8165ed97475b5d66757dd58754994c6515d3e74ddd3074a5d22746dd1474399077401cf973c9ceb7391cdd73614d17329cc372f1cb752c1ca97289c9c6255c8e7
|7,0=>0xb01ab88ac5eab6a91e9e6a5a28e8a1a27f79e1e7179a9e63796e2556939e4688fde3968c6229888da1c7859a0f781e20077e21f177a9de2876ddd47735dc67
|8,0=>0xc45b0a7c0defc7bd5eee7ba1ae17b69ed46b35ec67
|9,0=>0x3176
|_,_=>0
def wAt:=mkWire dB 57 236 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2914d1654a44083914e223514345351430634a44083914d1629149451d14e3544a44290d1440a39153450c10d2920acd162914e350c10d2920acd451c50d3939155291020e454d1430434a472934e4e314d1430434a552934e44083914d2924d4e291c50d3939149203514e293914e31
|1=>0x10a4e2920acd453854a4538d442b0cd4e451d1cd392914d2920e4d4560dc4293914e2910a4d45345912934a47471ca4d391028e450d14e162914a4580ace4544a4e2944a4429351471534551291d1cd3934a471444a4e350d14d393514f291028e451cace352480d4538a474534e4345
|2=>0xe3544a4e45103443510ac4390ca434510a4e290d14a4511143290c24e450d1c42b60dc42910a434544a4e353514e293858a452514e2934a4e3524d4e2920ecd4510a4e3534a4e451028e452914d451ca4e3538a43470d1442b34a444520a4d450c10d2938d4e29
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11001000000000000000
|5,0=>0x1c21b11830000001530001320f40b40000000a1082062051000023
|6,0=>0x6716616426220005f35e10005d15a35735615425225114e34b34830004624334120003f20003e13b33923723523323123012e22b30000000002922630002512322030001e2
|7,0=>0xae2ac2aa2a82a62a42a22a029e29c29a29829629429229028e28c28a28828628428228027e27c27a27827627427227026e26c26a2682
|8,0=>0xba1b91b81b71b61b51b41b31b21b11b01
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0xd080001820000300000040d00005b20000a240001400000241000042000008200000ce000018c00003100000360000060000009800001200000230000042000008000000a0000010000001c8000011000002000000280000040000004000000600000080000008000000
|1=>0xf40f201b81e403317c80640d100ae4f2015194402903c804a0fd008d4f201189e4022428803a1f9005cdf200a81e4010028001a1fd00342f2006077000c02e001727d00240fa003e8f400747e800a4f9000c0fe00081ec00103c80020690004096000800000072080006dd
|2=>0x408707941c40f641b81e441f83c840100b0446040088800c0873bc810e769021ccd204383f408703c810088d0200e82027c3e404103c807f2f9
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x81000000000
|5,0=>0x7820200005001c30900002070e0800b
|6,0=>0x21d2e0461028646ad787cf110881531001c591003800d8244722062098a8030000028c00d3090016
|7,0=>0x772e1267d00d9a24c23c952cce326b0d42c948534868dcaa79919d447cb9eb6
|8,0=>0x4b15cb89b395cfa0edfaf
|9,0=>0x25
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 27 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_234 7 roots_234 ops++addP pm 1 dom_194 4 roots_194 ops++addP pm 2 dom_137 4 roots_137 ops++addP pm 3 dom_233 7 roots_233 ops++addP pm 4 dom_171 7 roots_171 ops++addP pm 5 dom_227 7 roots_227 ops++addP pm 6 dom_107 7 roots_107 ops++addP pm 7 dzo_137_32 4 roots_137 ops++addP pm 8 dom_105 4 roots_105 ops++addP pm 9 dzo_98_8 4 roots_98 ops++addP pm 10 dom_98 4 roots_98 ops++addP pm 11 dom_170 4 roots_170 ops++addP pm 12 dzo_227_8 6 roots_227 ops++addP pm 13 dom_203 7 roots_203 ops++addP pm 14 dzo_226_8 5 roots_226 ops++addP pm 15 dzo_201_32 5 roots_201 ops++addP pm 16 dzo_99_8 5 roots_99 ops++addP pm 17 dzo_203_32 6 roots_203 ops++addP pm 18 dzo_139_32 5 roots_139 ops++addP pm 19 dom_193 4 roots_193 ops++addP pm 20 dom_232 4 roots_232 ops++addP pm 21 dom_139 5 roots_139 ops++addP pm 22 dom_226 5 roots_226 ops++addP pm 23 dom_195 5 roots_195 ops++addP pm 24 dom_202 5 roots_202 ops++addP pm 25 dom_201 5 roots_201 ops++addP pm 26 dom_99 5 roots_99 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_235 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_137_32_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_98_8_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_227_8_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_226_8_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_201_32_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_99_8_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_203_32_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_139_32_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_99 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_234 7 s (0,roots_234.map (·&&&dom_234)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_235 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_234 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_235==dom_235)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_235 gM v ys):RunD true dom_235 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_235 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 46 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
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
def dzo_100_8:=0x1100000011000000110000001100
def gzo_100_8:=0x1100000010000000100000000000
def gsh_100_8:=0x11000000100000001000000000
theorem lowS_zo_100_8_100:Lower true dzo_100_8 roots_100 gzo_100_8 4:=lower_iso_b (d1:=dom_100) (r1:=roots_100) (T1:=gsh_100_8) [(dom_100,8)] (by decide +kernel) (lower_slice_b (T:=gsh_100_8) [] (by decide +kernel) lowS_100)
def dzo_228_8:=0x110000001100000011000000110000001100000011000000110000001100
def gzo_228_8:=0x110000001100000011000000110000001100000010000000100000000000
def gsh_228_8:=0x1100000011000000110000001100000011000000100000001000000000
theorem lowS_zo_228_8_100:Lower true dzo_228_8 roots_228 gzo_228_8 5:=lower_iso_b (d1:=dom_228) (r1:=roots_228) (T1:=gsh_228_8) [(dom_228,8)] (by decide +kernel) (lower_slice_b (T:=gsh_228_8) [(0x1100000011000000110000001100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_100)
def dzo_205_32:=0x333300000000000033330000000000003333000000000000333300000000
def gzo_205_32:=0x333300000000000033320000000000003333000000000000323000000000
def gsh_205_32:=0x3333000000000000333200000000000033330000000000003230
theorem lowS_zo_205_32_137:Lower true dzo_205_32 roots_205 gzo_205_32 6:=lower_iso_b (d1:=dom_205) (r1:=roots_205) (T1:=gsh_205_32) [(dom_205,32)] (by decide +kernel) (lower_slice_b (T:=gsh_205_32) [(0x3030000000000000303000000000000030300000000000003030,0,4),(0x3333000000000000000000000000000033330000000000000000,0,64)] (by decide +kernel) lowS_137)
def dzo_229_8:=0x330000003300000033000000330000003300000033000000330000003300
def gzo_229_8:=0x330000003300000033000000330000003300000032000000320000002200
def gsh_229_8:=0x3300000033000000330000003300000033000000320000003200000022
theorem lowS_zo_229_8_100:Lower true dzo_229_8 roots_229 gzo_229_8 6:=lower_iso_b (d1:=dom_229) (r1:=roots_229) (T1:=gsh_229_8) [(dom_229,8)] (by decide +kernel) (lower_slice_b (T:=gsh_229_8) [(0x2200000022000000220000002200000022000000220000002200000022,0,1),(0x3300000033000000330000003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_100)
def dzo_169_4:=0x30300000303000000000000000000000303000003030
def gzo_169_4:=0x30300000302000000000000000000000303000002000
def gsh_169_4:=0x3030000030200000000000000000000030300000200
theorem lowS_zo_169_4_137:Lower true dzo_169_4 roots_169 gzo_169_4 5:=lower_iso_b (d1:=dom_169) (r1:=roots_169) (T1:=gsh_169_4) [(dom_169,4)] (by decide +kernel) (lower_slice_b (T:=gsh_169_4) [(0x3030000000000000000000000000000030300000000,0,32)] (by decide +kernel) lowS_137)
def dzo_141_32:=0x33330000000000000000000000000000333300000000
def gzo_141_32:=0x33320000000000000000000000000000323000000000
def gsh_141_32:=0x333200000000000000000000000000003230
theorem lowS_zo_141_32_137:Lower true dzo_141_32 roots_141 gzo_141_32 5:=lower_iso_b (d1:=dom_141) (r1:=roots_141) (T1:=gsh_141_32) [(dom_141,32)] (by decide +kernel) (lower_slice_b (T:=gsh_141_32) [(0x303000000000000000000000000000003030,0,4)] (by decide +kernel) lowS_137)
def dzo_101_8:=0x3300000033000000330000003300
def gzo_101_8:=0x3300000032000000320000002200
def gsh_101_8:=0x33000000320000003200000022
theorem lowS_zo_101_8_100:Lower true dzo_101_8 roots_101 gzo_101_8 5:=lower_iso_b (d1:=dom_101) (r1:=roots_101) (T1:=gsh_101_8) [(dom_101,8)] (by decide +kernel) (lower_slice_b (T:=gsh_101_8) [(0x22000000220000002200000022,0,1)] (by decide +kernel) lowS_100)
def dzo_233_4:=0x303000003030000030300000303000003030000030300000303000003030
def gzo_233_4:=0x303000003030000030300000302000003030000030300000303000002000
def gsh_233_4:=0x30300000303000003030000030200000303000003030000030300000200
theorem lowS_zo_233_4_137:Lower true dzo_233_4 roots_233 gzo_233_4 6:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_4) [(dom_233,4)] (by decide +kernel) (lower_slice_b (T:=gsh_233_4) [(0x30300000000000003030000000000000303000000000000030300000000,0,32),(0x30300000303000000000000000000000303000003030000000000000000,0,64)] (by decide +kernel) lowS_137)
namespace S_237
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(4,36),(4,68),(5,13),(5,37),(5,69),(5,133),(8,9),(8,136),(12,13),(12,44),(12,76),(12,140),(32,36),(32,96),(33,37),(33,41),(33,97),(33,161),(40,41),(40,44),(40,104),(40,168),(64,65),(64,68),(64,96),(64,192),(72,73),(72,76),(72,104),(72,200),(128,129),(128,136),(128,192),(132,133),(132,140),(132,164),(132,196),(160,161),(160,164),(160,168),(160,224)]
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
|5,0=>0xb56ea716b96af2f088c0
|6,0=>0xe2e83d6459c23a4c165579b56671e5601f84fc9d37f6132f112e8f31d02c19fce0840003c32
|7,0=>0xf12ded9e20cc577b7b40b2972b05c3a9a3f882117ebd77228e61e365b2ae53d315229c4bf66455fc38e52369d6337de2cff628b3026db4211251f837
|8,0=>0xfb4b1e6adae6538bad38743d369c8943d2941762
|9,0=>0xf0cad
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c00000c0c00000c0c0000000000000c0c00000c0c00000c0c0000000333300003333000033330000000000003333000033330000333300000000c0c00000c0c00000c0c0000000000000c0c00000c0c00000c0c0000000033330000333300003333000033330000222200002222000022220000222200000000cccc000000000000c0c0000000000000cccc000000000000c0c003300003333000000330000003300000022000033330000002200000022cccc000000000000cccc000000000000cccc000000000000cccc000000033000000330000003300000033000000330000003300000033000000330000000000000000000000000000000000cccc0000cccc000088880000888911100001111000011110000111100001111000011110000000000000000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c33330000000000003030000000000000333300000000000030300000000088880000888800008888000088880000888800008888000088880000888803300000033000000330000003300000022000000220000002200000022cccc0000cccc00000000000000000000cccc0000cccc000000000000000333300003333000033330000333300000000000000000000000000000000
|0,1=>0xcc440000cc440000cc000000cc000000cc440000cc440000cc000000cc033330000333300003030000030300000333300003333000030300000303000000000000000000000000000000000cccc0000cccc0000000000000002222000022220000222200002222000033330000333300002222000022228c8c00008c8c000088880000888800008c8c00008c8c000088880000888b33300003333000033000000330000003333000033330000330000003300cccc0000c0c00000cccc0000c0c00000cccc0000c0c00000cccc0000c0c333300003333000033330000333300003333000033330000222200002222cccc0000cccc000000cc000000cc0000cccc0000cccc000000880000008b3330000333300003333000033330000222200003333000022220000222200000000cccc0000000000000000000000000000cccc000000000000000222200003333000022220000222200002222000033330000222200002222cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000000000000003333000033330000222200002222000033330000333300002222000022220c0c00000c0c000000000000000000000c0c00000c0c000000000000000111100001111000011110000111100000101000001010000000000000000
|0,2=>0xcc000000cccc0000cc000000cc000000cc000000cccc0000cc000000cc0000000000000000000000000000000001111000011110000000000000000cccc0000cccc0000cccc0000cccc0000c8c80000c8c80000c8c80000c8cb3330000333300003333000033330000333300000000000033330000000044440000444400004444000044440000444400000000000044440000000111100001111000000000000000000001111000011110000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x92054873012481523136491430810092056070c12450d70402481523130492054870d33891430810092055830402481543010092054811802450c20510092050c14002483033c100920d30304014308b0402450ca0402481470461440c2040
|1=>0x4c100920548c0402481580c100e24814c0c10092050c19002488c50c100920548374025a1437402481580d304024814c0c14402481438410097c50c10092051c30402481521c304020510304024815c0c10092054834c024815b0c10096850d3
|2=>0x92050c10092053030406492050c10096850c10092050d30403892050c10092050c18008892050c10092050c14406492053030402050cb0402450c20402481520d304026514304025a143
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x9303180cc006
|6,0=>0x1e1ce4c6b73239798aee50724b909c76e34716b899c3ee187
|7,0=>0x8f4461a24d0a88233f5deceef773c381db2ed276633121790b5757b2a1d4109a649ba31d0ae7f6
|8,0=>0xab3d3de92d4279dbcd1e5af267
|9,0=>0x15d6
|_,_=>0
def wAt:=mkWire dB 38 238 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc045310c0410d040c805040c34d04045060c0620f2404881043c04a043404a0435e241415d0d040c305040510d1418805040404a04343010c1410120c83011c0404a04343010c04305040404a04348320c0540154349065434906043434e040450620c83010c04e1724143013850905
|1=>0x30124548050404905043c90114189150c05e2714148320c0430504048552418805040410d0034c050c049050c04c06
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x848f19c2326604a993222438c610930c600019803
|7,0=>0xa253ca694b29251ca29432824fc9e93b2724dc9a9332624bc9692b25249c929232
|8,0=>0xb43646c0d71ac3546a0d31
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x64ea09dd4119a81f2303e42078dc0bdf8173702e6a05c840b1b80b330146e0288c0401803230064400c00015e8023500444008000040000650004600084000c00010000080000c000100000
|1=>0x219bac006560ceac00c5131ba07351af7e18efc2bdf85737
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40
|6,0=>0xb6c444940e0c2287140188
|7,0=>0x99e3508a071aa1895c8d251f6553e4616761
|8,0=>0x4e7857a577dd
|9,0=>0xc
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_229 8 roots_229 ops++addP pm 1 dzo_100_8 4 roots_100 ops++addP pm 2 dom_205 7 roots_205 ops++addP pm 3 dzo_228_8 5 roots_228 ops++addP pm 4 dom_233 7 roots_233 ops++addP pm 5 dom_236 7 roots_236 ops++addP pm 6 dzo_205_32 6 roots_205 ops++addP pm 7 dzo_229_8 6 roots_229 ops++addP pm 8 dom_173 6 roots_173 ops++addP pm 9 dom_109 7 roots_109 ops++addP pm 10 dzo_169_4 5 roots_169 ops++addP pm 11 dom_100 4 roots_100 ops++addP pm 12 dzo_141_32 5 roots_141 ops++addP pm 13 dzo_201_4 5 roots_201 ops++addP pm 14 dzo_101_8 5 roots_101 ops++addP pm 15 dom_101 5 roots_101 ops++addP pm 16 dom_201 5 roots_201 ops++addP pm 17 dzo_233_4 6 roots_233 ops++addP pm 18 dom_137 4 roots_137 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_237 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_100_8_100 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_228_8_100 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_205_32_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_229_8_100 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_169_4_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_100 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_141_32_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_201_4_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_101_8_100 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_233_4_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_137 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_229 8 s (0,roots_229.map (·&&&dom_229)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_237 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_229 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
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
def dzo_230_8:=0x550000005500000055000000550000005500000055000000550000005500
def gzo_230_8:=0x550000005500000055000000550000005500000054000000540000000000
def gsh_230_8:=0x5500000055000000550000005500000055000000540000005400000000
theorem lowS_zo_230_8_102:Lower true dzo_230_8 roots_230 gzo_230_8 6:=lower_iso_b (d1:=dom_230) (r1:=roots_230) (T1:=gsh_230_8) [(dom_230,8)] (by decide +kernel) (lower_slice_b (T:=gsh_230_8) [(0x5500000055000000550000005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_102)
def dzo_102_8:=0x5500000055000000550000005500
def gzo_102_8:=0x5500000054000000540000000000
def gsh_102_8:=0x55000000540000005400000000
theorem lowS_zo_102_8_102:Lower true dzo_102_8 roots_102 gzo_102_8 5:=lower_iso_b (d1:=dom_102) (r1:=roots_102) (T1:=gsh_102_8) [(dom_102,8)] (by decide +kernel) (lower_slice_b (T:=gsh_102_8) [] (by decide +kernel) lowS_102)
namespace S_238
def pG:List (Nat×Nat):=[(2,34),(2,66),(2,130),(4,36),(4,68),(6,38),(6,70),(6,134),(8,136),(10,42),(10,74),(10,138),(12,44),(12,76),(12,140),(14,46),(14,78),(14,142),(32,34),(32,36),(32,96),(40,42),(40,44),(40,104),(40,168),(64,66),(64,68),(64,96),(64,192),(72,74),(72,76),(72,104),(72,200),(128,130),(128,136),(128,192),(132,134),(132,140),(132,164),(132,196),(160,162),(160,164),(160,168),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_238.map (·&&&dom_238)
def gM:=goal_238&&&dom_238
def NN:Nat→Nat
|4=>3
|5=>10
|6=>17
|7=>7
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x86bf728ec4276b0
|5,0=>0xfcd07be277a802b99feb755f74a2f844fdb3aaa42d4101789b
|6,0=>0xfc598f37fae9ae9e4d92bf3b6bb41fa61ae9d8b49640a95ac7958ac855715a52a595b637b5033b9d1655f
|7,0=>0xe24a4c64638474880e15647543cb3c3155e
|8,0=>0x1305b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaa000000aa000000aa000000aa0000000000000000000000000000000155540001555400000000000000000001555400000000000000000000000028280000282800002828000028280000282800002828000028280000000111100001111000011110000111100001111000011110000111100000000aaaa0000aaaa0000aa000000aa000000aaaa0000aaaa0000aa000000aa00141400001414000014140000000000001414000014140000141400000002aaa80002aaa800000000000000000002aaa80002aaa8000000000000000555500000000000055550000000000005555000000000000555500000000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a1555400015554000111100001111000015554000111100001111000011112aaa80002aaa80002aaa80002aaa80002aaa80002aaa8000000000000000555500005555000055550000000000005555000055550000555500000000aa000000aa000000aa000000aa000000aa000000aa000000aa000000aa0155540001555400014140000141400001555400014140000141400001414222200002222000022220000222200002222000022220000222200002222555500005555000055550000555500000000000000000000000000000000
|0,1=>0x2aaa80002aaa80002aaa80002aaa8000000000002aaa8000000000000000555500005555000055550000555500005555000055550000555500000000aa000000aaaa0000aa000000aa000000aa000000aaaa0000aa000000aa00000000000000000000000000000000015554000155540000000000000002aaa8000000000002aaa8000000000002aaa80002aaa80002aaa8000000055550000555500000055000000550000555500005555000000000000000000000000aaaa000000000000aaaa000000000000aaaa00000000000000000000000000000000000000000000000155540001555400015554000000000000000000000002aaa80002aaa800000000000000000002aaa80000000000000005555000000000000000000000000000055550000000000000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa0000000000000000000000000000000000000000000000015554000000000000000002a80002aaa8000002a8000002a8000000000002aaa8000000000000000050500000000000005050000000000000505000005050000050500000000
|_,_=>0
def sP:Nat→Nat
|0=>0x384a9220e1481f640ce14811519c29011030a920221670a4083853403d0338532020e14c40818609010670b80819cc90202a481e819c25720616a408188290206762408585490106730103398a418820
|1=>0x40ce1481070a40f220670a40859c2904d033852040ce14d00819c25481033853a020670a7a024c670a41c40ce14811b38520ca0670a40819c29701030a92041c38481033853704d03
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa5055005
|5,0=>0x4563f63963362d62762161b61560f6
|6,0=>0xb87b17aa7a469d79679068a68377c77576e76776075975274b7
|7,0=>0xe86e17db6d47cd7c67bf7
|8,0=>0xee6
|_,_=>0
def wAt:=mkWire dB 30 239 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1824251a5401426481483a014264254019a54011d14264694839a440121f4254bd1824814011824252034259a740121f4254251a51824269a6401
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1e2709a2609625092240800388c2288821884208802
|7,0=>0x261946418c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xfffded7d6f6d684b3924201c18090600
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x39785c28046336613
|7,0=>0xbdfcdee
|8,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_236 7 roots_236 ops++addP pm 1 dzo_230_8 6 roots_230 ops++addP pm 2 dom_206 6 roots_206 ops++addP pm 3 dom_230 7 roots_230 ops++addP pm 4 dzo_102_8 5 roots_102 ops++addP pm 5 dom_234 7 roots_234 ops++addP pm 6 dom_102 5 roots_102 ops++addP pm 7 dom_174 5 roots_174 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_238 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_230_8_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_102_8_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_174 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_236 7 s (0,roots_236.map (·&&&dom_236)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_238 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_236 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_238 gM v ys):RunD true dom_238 gM v (ori ys):=h
def Z (s:Nat):=barP dom_238 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_238 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_238 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_238 roots_238 goal_238 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_238
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=S_238.noCircuit
def isoMvS_119:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_119:Lower true dom_119 roots_119 goal_119 8:=lower_iso_b isoMvS_119 (by decide +kernel) lowS_111
def isoMvS_125:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_125:Lower true dom_125 roots_125 goal_125 10:=lower_iso_b isoMvS_125 (by decide +kernel) lowS_123
def isoMvS_183:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 8:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_175
def isoMvS_190:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 8:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_175
def isoMvS_215:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_207
def isoMvS_243:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 10:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_235
def isoMvS_245:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 10:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_237
def isoMvS_246:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_238
def isoMvS_249:List (Nat×Nat):=[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_221
def isoMvS_250:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_237
def isoMvS_252:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccccccccccccccccccc,126),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 10:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_123
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xcccccccccccccccccccccccccccccccc,32,34)] (by decide +kernel) lowS_125
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_slice_b [(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,32,36)] (by decide +kernel) lowS_187
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_slice_b [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,64,66)] (by decide +kernel) lowS_221
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,32,34)] (by decide +kernel) lowS_237
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,24),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(16,17),(16,24),(16,144),(18,19),(18,26),(18,50),(18,82),(18,146),(32,34),(32,96),(33,35),(33,41),(33,49),(33,97),(33,161),(40,41),(40,42),(40,56),(40,104),(40,168),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,66),(64,96),(64,192),(72,73),(72,74),(72,88),(72,104),(72,200),(80,81),(80,82),(80,88),(80,112),(80,208),(128,129),(128,130),(128,136),(128,144),(128,192),(160,161),(160,162),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1fffffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ac688
|_=>0
def sO:Nat→Nat→Nat
|11,0=>7
|_,_=>0
def wAt:=mkWire dB 7 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_187 10 roots_187 ops++addP pm 2 dom_249 10 roots_249 ops++addP pm 3 dom_243 10 roots_243 ops++addP pm 4 dom_235 10 roots_235 ops++addP pm 5 dom_219 10 roots_219 ops++addP pm 6 dom_123 10 roots_123 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_123 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
  · simp [NN] at hi
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
namespace S_253
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,24),(8,136),(12,13),(12,28),(12,44),(12,76),(12,140),(16,17),(16,24),(16,144),(20,21),(20,28),(20,52),(20,84),(20,148),(32,36),(32,96),(33,37),(33,41),(33,49),(33,97),(33,161),(40,41),(40,44),(40,56),(40,104),(40,168),(48,49),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,96),(64,192),(72,73),(72,76),(72,88),(72,104),(72,200),(80,81),(80,84),(80,88),(80,112),(80,208),(128,129),(128,136),(128,144),(128,192),(132,133),(132,140),(132,148),(132,164),(132,196),(160,161),(160,164),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffff
def xsM:=roots_253.map (·&&&dom_253)
def gM:=goal_253&&&dom_253
def NN:Nat→Nat
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|11,0=>0x1e31b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3333333300000000333333330000000033333333000000003333333300000000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0003300330033003300330033003300330033003300330033003300330033003300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c2222222222222222222222222222222222222222222222222222222222222222cccccccccccccccc0000000000000000cccccccccccccccc0000000000000003333333333333333333333333333333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ac688
|_=>0
def sO:Nat→Nat→Nat
|11,0=>7
|_,_=>0
def wAt:=mkWire dB 7 254 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_125 10 roots_125 ops++addP pm 2 dom_249 10 roots_249 ops++addP pm 3 dom_245 10 roots_245 ops++addP pm 4 dom_237 10 roots_237 ops++addP pm 5 dom_221 10 roots_221 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_221 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_253==dom_253)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_253 gM v ys):RunD true dom_253 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_253 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
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
def dzo_118_8:=0x55005500550055005500550055005500
def gzo_118_8:=0x55005500550054005500540055000000
def gsh_118_8:=0x550055005500540055005400550000
theorem lowS_zo_118_8_102:Lower true dzo_118_8 roots_118 gzo_118_8 6:=lower_iso_b (d1:=dom_118) (r1:=roots_118) (T1:=gsh_118_8) [(dom_118,8)] (by decide +kernel) (lower_slice_b (T:=gsh_118_8) [(0x550000005500000055000000550000,0,16)] (by decide +kernel) lowS_102)
def dzo_110_16:=0x55550000555500005555000055550000
def gzo_110_16:=0x55550000555400005554000055000000
def gsh_110_16:=0x5555000055540000555400005500
theorem lowS_zo_110_16_102:Lower true dzo_110_16 roots_110 gzo_110_16 6:=lower_iso_b (d1:=dom_110) (r1:=roots_110) (T1:=gsh_110_16) [(dom_110,16)] (by decide +kernel) (lower_slice_b (T:=gsh_110_16) [(0x5500000055000000550000005500,0,8)] (by decide +kernel) lowS_102)
def dzo_158_32:=0x555555550000000000000000000000005555555500000000
def gzo_158_32:=0x555555540000000000000000000000005554545400000000
def gsh_158_32:=0x5555555400000000000000000000000055545454
theorem lowS_zo_158_32_152:Lower true dzo_158_32 roots_158 gzo_158_32 6:=lower_iso_b (d1:=dom_158) (r1:=roots_158) (T1:=gsh_158_32) [(dom_158,32)] (by decide +kernel) (lower_slice_b (T:=gsh_158_32) [(0x4444444400000000000000000000000044444444,0,2),(0x5050505000000000000000000000000050505050,0,4)] (by decide +kernel) lowS_152)
def dzo_186_4:=0x505050505050505000000000000000005050505050505050
def gzo_186_4:=0x505050505050504000000000000000005050505050000000
def gsh_186_4:=0x50505050505050400000000000000000505050505000000
theorem lowS_zo_186_4_154:Lower true dzo_186_4 roots_186 gzo_186_4 6:=lower_iso_b (d1:=dom_186) (r1:=roots_186) (T1:=gsh_186_4) [(dom_186,4)] (by decide +kernel) (lower_slice_b (T:=gsh_186_4) [(0x50505050000000000000000000000000505050500000000,0,32)] (by decide +kernel) lowS_154)
def dzo_246_8:=0x5500550055005500550055005500550055005500550055005500550055005500
def gzo_246_8:=0x5500550055005500550055005500550055005500550054005500540055000000
def gsh_246_8:=0x55005500550055005500550055005500550055005500540055005400550000
theorem lowS_zo_246_8_102:Lower true dzo_246_8 roots_246 gzo_246_8 7:=lower_iso_b (d1:=dom_246) (r1:=roots_246) (T1:=gsh_246_8) [(dom_246,8)] (by decide +kernel) (lower_slice_b (T:=gsh_246_8) [(0x55000000550000005500000055000000550000005500000055000000550000,0,16),(0x55005500550055005500550055005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_102)
def dzo_222_32:=0x5555555500000000555555550000000055555555000000005555555500000000
def gzo_222_32:=0x5555555500000000555555540000000055555555000000005554545400000000
def gsh_222_32:=0x55555555000000005555555400000000555555550000000055545454
theorem lowS_zo_222_32_152:Lower true dzo_222_32 roots_222 gzo_222_32 7:=lower_iso_b (d1:=dom_222) (r1:=roots_222) (T1:=gsh_222_32) [(dom_222,32)] (by decide +kernel) (lower_slice_b (T:=gsh_222_32) [(0x44444444000000004444444400000000444444440000000044444444,0,2),(0x50505050000000005050505000000000505050500000000050505050,0,4),(0x55555555000000000000000000000000555555550000000000000000,0,64)] (by decide +kernel) lowS_152)
def dzo_154_4:=0x5050505000000000000000000000000050505050
def gzo_154_4:=0x5050504000000000000000000000000050000000
def gsh_154_4:=0x505050400000000000000000000000005000000
theorem lowS_zo_154_4_154:Lower true dzo_154_4 roots_154 gzo_154_4 5:=lower_iso_b (d1:=dom_154) (r1:=roots_154) (T1:=gsh_154_4) [(dom_154,4)] (by decide +kernel) (lower_slice_b (T:=gsh_154_4) [] (by decide +kernel) lowS_154)
def dzo_230_16:=0x55000000550000005500000055000000550000005500000055000000550000
def gzo_230_16:=0x55000000550000005500000055000000550000005400000054000000000000
def gsh_230_16:=0x5500000055000000550000005500000055000000540000005400000000
theorem lowS_zo_230_16_102:Lower true dzo_230_16 roots_230 gzo_230_16 6:=lower_iso_b (d1:=dom_230) (r1:=roots_230) (T1:=gsh_230_16) [(dom_230,16)] (by decide +kernel) (lower_slice_b (T:=gsh_230_16) [(0x5500000055000000550000005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_102)
def dzo_236_16:=0x1111000011110000111100001111000011110000111100001111000011110000
def gzo_236_16:=0x1111000011110000111100001111000011110000111000001110000011000000
def gsh_236_16:=0x111100001111000011110000111100001111000011100000111000001100
theorem lowS_zo_236_16_100:Lower true dzo_236_16 roots_236 gzo_236_16 6:=lower_iso_b (d1:=dom_236) (r1:=roots_236) (T1:=gsh_236_16) [(dom_236,16)] (by decide +kernel) (lower_slice_b (T:=gsh_236_16) [(0x110000001100000011000000110000001100000011000000110000001100,0,8),(0x111100001111000011110000111100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_100)
def dzo_238_16:=0x5555000055550000555500005555000055550000555500005555000055550000
def gzo_238_16:=0x5555000055550000555500005555000055550000555400005554000055000000
def gsh_238_16:=0x555500005555000055550000555500005555000055540000555400005500
theorem lowS_zo_238_16_102:Lower true dzo_238_16 roots_238 gzo_238_16 7:=lower_iso_b (d1:=dom_238) (r1:=roots_238) (T1:=gsh_238_16) [(dom_238,16)] (by decide +kernel) (lower_slice_b (T:=gsh_238_16) [(0x550000005500000055000000550000005500000055000000550000005500,0,8),(0x555500005555000055550000555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_102)
def dzo_156_32:=0x111111110000000000000000000000001111111100000000
def gzo_156_32:=0x111111100000000000000000000000001110101000000000
def gsh_156_32:=0x1111111000000000000000000000000011101010
theorem lowS_zo_156_32_152:Lower true dzo_156_32 roots_156 gzo_156_32 5:=lower_iso_b (d1:=dom_156) (r1:=roots_156) (T1:=gsh_156_32) [(dom_156,32)] (by decide +kernel) (lower_slice_b (T:=gsh_156_32) [(0x1010101000000000000000000000000010101010,0,4)] (by decide +kernel) lowS_152)
def dzo_116_8:=0x11001100110011001100110011001100
def gzo_116_8:=0x11001100110010001100100011000000
def gsh_116_8:=0x110011001100100011001000110000
theorem lowS_zo_116_8_100:Lower true dzo_116_8 roots_116 gzo_116_8 5:=lower_iso_b (d1:=dom_116) (r1:=roots_116) (T1:=gsh_116_8) [(dom_116,8)] (by decide +kernel) (lower_slice_b (T:=gsh_116_8) [(0x110000001100000011000000110000,0,16)] (by decide +kernel) lowS_100)
def dzo_108_16:=0x11110000111100001111000011110000
def gzo_108_16:=0x11110000111000001110000011000000
def gsh_108_16:=0x1111000011100000111000001100
theorem lowS_zo_108_16_100:Lower true dzo_108_16 roots_108 gzo_108_16 5:=lower_iso_b (d1:=dom_108) (r1:=roots_108) (T1:=gsh_108_16) [(dom_108,16)] (by decide +kernel) (lower_slice_b (T:=gsh_108_16) [(0x1100000011000000110000001100,0,8)] (by decide +kernel) lowS_100)
def dzo_102_16:=0x550000005500000055000000550000
def gzo_102_16:=0x550000005400000054000000000000
def gsh_102_16:=0x55000000540000005400000000
theorem lowS_zo_102_16_102:Lower true dzo_102_16 roots_102 gzo_102_16 5:=lower_iso_b (d1:=dom_102) (r1:=roots_102) (T1:=gsh_102_16) [(dom_102,16)] (by decide +kernel) (lower_slice_b (T:=gsh_102_16) [] (by decide +kernel) lowS_102)
def dzo_154_32:=0x50505050000000000000000000000000505050500000000
def gzo_154_32:=0x50505040000000000000000000000000504040400000000
def gsh_154_32:=0x505050400000000000000000000000005040404
theorem lowS_zo_154_32_152:Lower true dzo_154_32 roots_154 gzo_154_32 5:=lower_iso_b (d1:=dom_154) (r1:=roots_154) (T1:=gsh_154_32) [(dom_154,32)] (by decide +kernel) (lower_slice_b (T:=gsh_154_32) [(0x404040400000000000000000000000004040404,0,2)] (by decide +kernel) lowS_152)
def dzo_218_4:=0x50505050000000005050505000000000505050500000000050505050
def gzo_218_4:=0x50505050000000005050504000000000505050500000000050000000
def gsh_218_4:=0x5050505000000000505050400000000050505050000000005000000
theorem lowS_zo_218_4_154:Lower true dzo_218_4 roots_218 gzo_218_4 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_4) [(dom_218,4)] (by decide +kernel) (lower_slice_b (T:=gsh_218_4) [(0x5050505000000000000000000000000050505050000000000000000,0,64)] (by decide +kernel) lowS_154)
def dzo_234_16:=0x505000005050000050500000505000005050000050500000505000005050000
def gzo_234_16:=0x505000005050000050500000505000005050000050400000504000005000000
def gsh_234_16:=0x50500000505000005050000050500000505000005040000050400000500
theorem lowS_zo_234_16_98:Lower true dzo_234_16 roots_234 gzo_234_16 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_16) [(dom_234,16)] (by decide +kernel) (lower_slice_b (T:=gsh_234_16) [(0x50000000500000005000000050000000500000005000000050000000500,0,8),(0x50500000505000005050000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_98)
def dzo_218_32:=0x505050500000000050505050000000005050505000000000505050500000000
def gzo_218_32:=0x505050500000000050505040000000005050505000000000504040400000000
def gsh_218_32:=0x5050505000000000505050400000000050505050000000005040404
theorem lowS_zo_218_32_152:Lower true dzo_218_32 roots_218 gzo_218_32 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_32) [(dom_218,32)] (by decide +kernel) (lower_slice_b (T:=gsh_218_32) [(0x4040404000000000404040400000000040404040000000004040404,0,2),(0x5050505000000000000000000000000050505050000000000000000,0,64)] (by decide +kernel) lowS_152)
def dzo_220_32:=0x1111111100000000111111110000000011111111000000001111111100000000
def gzo_220_32:=0x1111111100000000111111100000000011111111000000001110101000000000
def gsh_220_32:=0x11111111000000001111111000000000111111110000000011101010
theorem lowS_zo_220_32_152:Lower true dzo_220_32 roots_220 gzo_220_32 6:=lower_iso_b (d1:=dom_220) (r1:=roots_220) (T1:=gsh_220_32) [(dom_220,32)] (by decide +kernel) (lower_slice_b (T:=gsh_220_32) [(0x10101010000000001010101000000000101010100000000010101010,0,4),(0x11111111000000000000000000000000111111110000000000000000,0,64)] (by decide +kernel) lowS_152)
namespace S_254
def pG:List (Nat×Nat):=[(2,34),(2,66),(2,130),(4,36),(4,68),(6,38),(6,70),(6,134),(8,24),(8,136),(10,26),(10,42),(10,74),(10,138),(12,28),(12,44),(12,76),(12,140),(14,30),(14,46),(14,78),(14,142),(16,24),(16,144),(18,26),(18,50),(18,82),(18,146),(20,28),(20,52),(20,84),(20,148),(22,30),(22,54),(22,86),(22,150),(32,34),(32,36),(32,96),(40,42),(40,44),(40,56),(40,104),(40,168),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,68),(64,96),(64,192),(72,74),(72,76),(72,88),(72,104),(72,200),(80,82),(80,84),(80,88),(80,112),(80,208),(128,130),(128,136),(128,144),(128,192),(132,134),(132,140),(132,148),(132,164),(132,196),(160,162),(160,164),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1fffffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|5=>16
|6=>72
|7=>187
|8=>270
|9=>138
|10=>14
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xb5c80abd1f90a667f3ad7a6ab7617c62bf45a96c48bff475ab297df1ad8d108b90c6f208be10813e
|6,0=>0xfb8eee2fa2e27b6c9f5ac0855bf208b4fa5b4ca4b3cdcaf419a8697a5539a0d329f9cc9be919732f9650d900a68f4db8c9c18ae7488d9788be6850e281e9c7de957d4097a52a77f4e74b9371dd268f1e60c505ea965a0d3589c857b65574e85402a4ee944e13b45607411903c8793b9453a0652c4d929f6b26b88255ae1cca81bd161b1731987f18de9178a3170a4168361643313e541176010e1410a751011b1003f0ea070e9150ced606e30048cb02ff6003a1
|7,0=>0x70e416dd6b6c01e69e1768c66688c86880d66711632c5614ff6107260fd0605425ff3d5fe5b5e84b5e5a25d3e25cff25ca005bb0659c515823257f35576ae56d0656b8b56ae5555a854fb35496b54410537535220b520865195950b774df1f4cef04cb664b7df4a9fd4a7144a5304a0b148e7f47caa47ca447ad24716d4707d45827453dc44bcb4454f434b942af84256741ec14150c4100f3fb9d3cda83be0c3831b380c137ddb378603451432b1231e5831b6f31ac0316dd30db3303ee2f8862f1fe2b4282ac7c2a0d9296c1295712742f271412659e25d962474722dc7207ae1fd7a1fa5d1e7441dbe51d0291cca81c23f1a89619edb199ed1920b17ae916e25163be1600e1557b14d9b14c201448f0f9180f8470efe00e3cc0dcd60d0f80ca630c2400a1e1085570691a065bc04e8c0434003ef603cbf019f8016040120e
|7,1=>0xfa43ff2180ebf28ebdeceacabe710ee5deae4f19e0ffedb9ffce557ce39bcc845c9adbc36d4c1f30c1b5abb0d2b9b9ab9b91b60b1b4bf2b4386b333ab208daea67a9644a6bdba66f3a05b59fe729f3d09dbc19d40f99eed945839190890a3f8f9398f7fb8eee48e6528d72e8b92386df386c4286a83869088285f800217e9657bef17b78977fbc76f1775b16745fa716da7167a
|8,0=>0x4450a440c243654401d13f58f3ec1c3eaa13d9fc3d9d23bb863b74c3b58d3acf73a73d3a1a83833a381bf37aa137926370c336c9835753342b7329553223230a77308fc30819303ee2f8862eff62ed0a2e4ca2d61f2d5f82ce252b3492b01229b1829a0d28e88286bf2775727254271a22702726b9d26a2226418258962548b2519d24bbb2498f23a2c234e5215ae214682115420dfb207361f0a61ed171e7301e68e1d7bd1d2771cd501bec41b62a1b4501abe91a3441a29b1a19419edb195f118e6e1851e178b7177d71765c166501617f14eb713c77127261215e111f9110150fd8c0fce70fbde0f9640f2920f21a0f0960d0160ce850c4880c03c0bec10bb390b87c0ae230ac080ab700a846091f50904c0900b08e900879b0836f070ea0700e06ce7053f4052ae04fe0049f7034c10341802fdb01dde019ab0161e00163
|8,1=>0xd68c9d1cb4ced6fce4fecd820cd21acafa0cae25c8cebc6fb5c638ec5d3ec5973c52d1c4f5dc2667c0f29c0517bebecbddc2bab0eb7e55b7bf8b6ea5b3e06b2ec0b28d1b0a5eafd61af816ae918adc12ad4abaca4aac8cfabc73aa427a9d93a7937a599ea43e7a34e9a2d57a166e9f9ae9c6269c5089a56f99e07997349676c9667b96540964259507792d2a923ac8d8578d7a18d6f48d4dc8d1258cca88c07d8a9e08a13888c81878fb8707586a8386908851a681e4381da681cf681b7e80d1e7e9657ac8e7a3ba79cb877b6a76c7c758ef73a7d73540714f96d83b6d6c06ccf46bc366ba636b9bd6849b66d646476d6396662f9e612485c46b5b0265a78f5862c577f5558c751f0c51e2e50c205092f4fe054fbf74ea324de244c5694c28a4b45e4b1bc4b0d34a92a49d81492224848147c6d46dd445d0045a174510a4454f
|8,2=>0xff660f8947f24aaecf45e707be700fe295ee1420e137bde528de47bdd790d9ccfd7a5c
|9,0=>0xcf81cc801bc638ec5d3ec5255c50d5c3940c1ebcbf051b6f26b0177ae712a99e0a8774a5351a39f0a273fa0f2ca0dd99eade9dbaa9da0a972b1958549436d941c09345692a018fb9f8ce7988eb280cff7f24a7aa7c7775976d8972f416ef8b6e0346dee66dd176c32e686a967e106711a65b5d64b8f60eff60de6605b95b1cb5ad9e585ad585375751156f0c56d6954286539cf53562522035123c50c2050596500545003a4f2014d4d14c92e4b93a49db747b4646dd4425cf416e3414ff3ffcc3fe4e3d4b33c6213c3ab3953638d90389b33707c36f003662f33e4b33270328963271b31e4a317e42f6772f2ea2d67c2d5cf2b2f72ab1e275262638b21468205401a9e919edb18e6e17bb716a2c168ea15bb313c7713a97134f811d3311bb811865109bc10944103ed0f6aa0f44b0c0080b17906e3106cb60551504c900274d
|9,1=>0xfc636fc33afa3ebf8cfcf37ffe6084e2dbbde940dcdb9d2f1d
|10,0=>0xc5d3e8a5a08a42584770758d07553b6f64d62c054b78a46dd4420a2406e8371a02224d
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaaaaaaaaaa88aa88aa88aa88888888888888888888888888888888881414141414141414141414140000000014141414141414141414141400000002a802a802a802a802a802a802a802a802a8000002a8000002a8000002a8000005555555555555555555555550000000055555555555555555555555500000000aaaaaaaaa0a0a0aaa0a0a0a0a0a0a0a0aaaaaaaaa0a0a0a0a0a0a0a0a0a0a0a15555555555555555555555555555555400000000000000000000000000000002aaaaaaaaaaaaaaaaa802a802a802a802aaaaaaaaa8000002a8000002a8000004444444444444444444444444444444444444444444444444444444444444444aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa000000000000000000000044440000444444444444444444444444444400000002aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002aaaaaaa800000005555000055550000555500005555000055550000555500005555000055550000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a1555555555555555511111111111111115555555511111111111111111111111002a802a802a802a802a802a802a802a802a802a802a802a802a8000002a80005555555555555555555555555555555555555555555555550000000000000000
|0,1=>0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aa000000aa015555555401540154000000000000000155555554000000000000000000000002aaaaaaa802a802aaaaaaaaa802a802aaaaaaaaa800000002aaaaaaa800000000055005500550055005500550055005500000000000000000000000000000000aaaaaaaa88aa88aa8888888888888888aaaaaaaa88888888888888888888888955555555555555555555111155551111111111111111111111111111111111102828282828282828282828282828282828282828282828282828282800000005555555555555555555500005555000055555555550000005500000055000000aaaaaaaaaaaaaaaaaaaaaa00aaaaaa00aaaa0000aaaa0000aaaa0000aaaa00015555555555555555555555555555555554015401540154015401540154015402aaaaaaaaaaaaaaa80000000000000002aaaaaaaaaaaaaaa8000000000000000550055005500550055005500550055005500550055005500550000005500000000aa00aa00aa00aa00aa00aa00aa00aa00aa000000aa000000aa000000aa000155555555555555554141414141414141555555554141414141414141414141400002aaa80002aaa80002aaa80002aaa80002a8000002a8000002a8000002a805555555544444455444444444444444455555555444444444444444444444444
|0,2=>0xaaaaaaaaaaaaaaaa0000aaaa0000aaaaaaaaaaaaaaaaaaaa00000000000000004444444444444444444444444444444444444444444444444444444400000000282828282828000028282828282800002828282828282828282828280000000000055550000555500005555000055550000000000000000000000000000000000000000000000000000aa000000aa00aa00aa00aa00aa00aa00aa00aa00aa015555555555555554015401540154015555555555555555540000000000000002aaaaa802aaaaa802aaaaa802aaaaa802aaaaa802aaaaa802aaaaa802aaaaa800000111100001111000011110000111111111111111111111111111100000000aa000000aa000000aa00aa00aa00aa00aa000000aa000000aa000000aa0000015555555555555554000000000000000155555554000000000000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaa800000005555555555555555555555555555555555550000555500005555000055550000aa00aa00aaaaaaaaaa00aa00aa00aa0000000000000000000000000000000001540154015555555554015401540154015401540155555555540154015401540000000002aaaaaaa8000000000000000000000002aaaaaaa80000000000000005555550055555555555555005555550055550000555500005555000055550000
|0,3=>0xaaaaaaaaaaaaaaaa00000000000000000000000000000000000000000000000155555555555555555151515151515151515151515151515151515151515151500000000000000000888888888888888888888888888888880000000000000000000000000000000555555555555555500000000555555555555000055550000aaaaaaaaaaaaaaaaaa00aa00aa00aa00aaaaaaaaaaaaaaaaaa00aa00aa00aa015555555555555555555400015554000000000000000000000000000000000002aaaaaaaaaaaaaaaaaaa80002aaa80002aaaaaaaaaaaaaaaaaaa80002aaa80000000000055555555000000005555555500000000555555550000000000000000aaaaaaaaa0a0aaaaa0a0a0a0a0a0a0a0aaaaaaaaa0a0a0a0a0a0a0a0a0a0a0a15555555555555555540154015401540000000000000000000000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaa800000550055005500550055005500550055005500550055005500000000000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a0a0a0a0a0a0a0a0a000000015555555400015554000000000000000155555554000000000000000000000002aaaaaaa80002aaaaaaaaaaa80002aaaaaaaaaaa800000002aaaaaaa800000005555555544445555444444444444444455555555444444444444444444444444
|0,4=>0xaa00aa00aa00aa00aa00aa00aa00aa00aa000000aa000000aa000000aa00aa015401540154015401540154015401540155555555555555540000000000000002aaaaaaaaa802a802aaaaaaaaa802a802aaaaaaaaaaaaaaaaaaaaaaa800000005555555555555555555555555555555555555555555555555555555555005500aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aa000000444444444444444444444444000000444444444444444444444444440000000000000000000000000002aaa80002aaaaaaaaaaaaaaaaaaaaaaaaaaa80000000555500005555000055550000555500005500000055000000550000005500000000aa00aaaaaaaaaa00aa00aa00aa00aa00000000aaaaaaaa00000000000000001414141414141414141414140000001414141414141414141414141400000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8000000000005500000055000000555500005555000055000000550000005500000055000a0a0a0a0a0a0a000a0a0a0a000000000a0a0a0a0a0a0a0a0a0a0a0a00000001555555540000015400000000000000015555555400000000000000000000000000000000000000000002aaa80002aaa800000002aaaaaaa80000000000000005555555555555555444444444444444444444444444444444444444444444444
|0,5=>0xa0a0a0a0a0a0a0a0a0a0a0a00000a0a0a0a0a0a0a0a0a0a0a0a0a0a000000000000000000000001555555555555555400000000000000000000000000000002aaaaaaaaaaaaaaaaaaa80002aaa80002aaaaaaa800000002aaa8000000000005555555555555555555555555555555500000000555555550000000000000000aaaaaaaaaaaa0000aaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaa0000000155540001555400000000000000000001555555555555555400000000000000002828282828280000282828280000000028282828282828282828282800000000000000000000000000000000000000055555555555555555555555500000000aaaaaaaaaaaaaaaaaa00aa00aa00aa00aaaaaaaaaa00aa00aa00aa00aa00aa015555555555540001555555555555555555540001555400015554000155540002aaaaaaa800000002aaaaaaaaaaaaaaa800000000000000000000000000000000055005500550000005500550055005500550000005500000055000000550000000000000000000000aa000000aa0000aaaa0000aaaa0000aaaa0000aaaa00015555555555555555555555555554000155555554000000015555555400000002aaaaaaaaaaa802aaaaa80002aaa80002aaaaaaaaaaa80002aaa80002aaa80000000000000000000000000000000000000005555000055550000555500000000
|0,6=>0xaaaaaaaaaaaaaaaaaaaaaaaa00aa00aaaaaaaaaaaaaaaaaaaaaaaaaa0000000155555555555555555555555554015401555555540000000155555554000000000002aaaaaaaaaaa80002aaa80002aaa800000002aaaaaaa80000000000000005555000055555555555500005555000000000000000000000000000000000000aaaa0000aaaaaaaaaaaa0000aaaa0000aaaa0000aaaaaaaaaaaa0000aaaa0000000154000000000000015400000154015401540154015401540154015401540002a802a802a802a802a802a802a802a800000002aaaaaaa800000000000000000000000000000000000000000000000555555555555555555005500550055000000000000000000aaaaaaaaaaaaaaaa00000000aaaaaaaa00000000000000015401540154015401555555555555555554015401540154015401540154015402a8000002a8000002aaa80002aaa80002a8000002a8000002a8000002a8000005555555555005500555555555555555555005500550055005500550055005500aaaa0000aa000000aaaa0000aaaa0000aa000000aa000000aa000000aa00000000000000000000000154015401540154000000000000000000000000000000008888888888888888888888880088008888888888888888888888888800000005555555555555555555555550000555555555555555555555555555500000000
|0,7=>0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaa000000000001555400015554000154000001540000015554000155540001540000015402aaaa2222aaaaaaaaaaaa2222aaaa2222222222222222222222222222222222200000000000000005555555500550055000000000000000055555555000000000000000000000000aaaaaaaaaaaaaaaa0000000000000000aa00aa00aa00aa000000000000000000015401540154015555555555555555540000000000000002aaaaaaaaaaaaaaa8000002a8000002aaaaaaaaaaaaaaaaa80000000000000000000005500000055000000550000005500000000000000000000000000000000aaaaaaaaaaaaaaaaaaaaaaaa000000aaaaaaaaaaaaaaaaaaaaaaaaaa000000015555555555555554000155540001555555555554000000000000000000000002aaaaaaaaaaaaaaaaaaaaa802aaaaa802a802a802a802a802a802a802a802a80555500005555000055555555555555555555000055550000555500005555000000000000000000000000000000000000aaaaaaaaaaaaaaaa00000000000000015555555400000001555555540000000155555555555555555555555400000002aaaaaaaaaaaaaaaaaa82aa82aa82aa8282828282828282828282828282828280000000055000000550055005500550000000000550055005500550055005500
|0,8=>0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00015555540155555555555554015555540154015401540154015401540154015400000000000000000000000002aaaaaaa8000000000000000000000002a802a805050505050505050505050505555555550505050505050505050505055505550aaaaaaaa000000aaaaaaaaaa000000aaaaaaaaaa00000000aaaaaaaa000000015555555555555555555555555555555555555401555554015555540155555402aaaaaaaaaaaaaaaaaaaaaaaaaaaaa802aaaaaaaaaaaaaaaaaaaaaaaaaaaaa8005050505050505050505050505050500050505050505050505050505050505000000aaaa0000aaaa0000aaaa0000aaaaaaaaaaaaaaaaaaaaaaaaaaaa000000015555555555555555555555555555555555540001555555555554000155540002a802a802a802a802a802a802a802a802a8000002a802a802a8000002a80000055555555555555555555555555555555555555555555555555555555555500000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000155555555555555555555555555555555540154015555555554015401540154000002aaa80002aaa80002aaa80002aaa80002a8000002aaa80002a8000002a800000000000000000000000000000000000000000555555550000000000000000
|0,9=>0xaaa0aaa0aaaaaaaaaaa0aaa0aaa0aaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0000000015555540000000000000000000000000155555554000000000000000000000000000000000000000002a802a80000000000000000000000000000000505050505050505050505050505550555050505050505050505050505050505000000000aaaaaaaa00000000000000aa00000000aaaaaaaa00000000000000015555555555555555555555555555555555555555555555555401540154015402a802a802a802a802a802a802a802a802a802aaaaa802aaaaa802aaaaa802a800000555500005555000055550000555500005555000055550000000000000000aaaa0000aaaa0000aaaa0000aaaa0000aaaaaaaaaaaaaaaaaaaaaaaa00000001555400015555555555540001555555555554000155555555555400015554000000000000000000000000000000000002aaa80002aaaaaaaaaaa80002aaa80000000000000000000555555550000005500000000000000005555555500000000aaaaaa00aaaaaa00aaaaaa0000000000aaaaaaaaaaaaaaaaaaaaaaaa0000000155555554000155555555555400000001555555540000000155555554000000008888888888888888888888888888888888888888888888888888888888880005500555555005555550055555500555555005500550055005500550055005500
|0,10=>0xaaaa000000000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa000000000000000000000000000000000000000000015554000155540000000000000002aaaaaaa800000002aaaaaaa800000002aaaaaaa80002aaaaaaaaaaa8000000000550055005500550055005500550055000000000055005500000000000000000000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa0000000000000000000000015555555400000000015401540000000155555554000000000000000000000000000000000002aaa80002aaa800000000000000000002aaa800000005500550055005500000000000000000055555555555555550000000000000000aaaaaaaaaa00aa00aaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaa000000000000015555555554000001540000015400000001555555540000000000000002aaaaaaaaaaaaaaaaaaaaa802aaaaa802aaaaaaaaaaaaaaaaaaaaa802aaaaa805555555555555555555555550000000000000000000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa00000000aaaaaaaa000000015555540155555400000000000000000155555555555555540000000000000002aaaaaaaaaaaaa802aaaaaaa800000002aaaaaaaaaaaaaaaaaaaaaaa800000001111111111111111111111110000111111111111111111111111111100000000
|0,11=>0xaaaa0000000000000000000000000000aaaa0000000000000001540154015400000154015401540154015401540154000001540154015401540002a802a802a802a802a802a802a802aaaaaaaaaaaaaaaaa8000000000000000555555555555000055555555555500005555555555550000000000000000000000000000aaaaaaaa0000000000000000000000000000000000000000000000000000000155555554000000015555555400000000000000000000000000000002aaa8000000000002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80000000000000000000555555550000555500000000000000005555555500000000aaaaaa00aaaaaaaaaaaaaa00aaaaaa00aaaaaa00aaaaaaaaaaaaaa00aaaaaa015401540154015401540154015401540154015401555555555401540154015402aaa80002aaa80002aaa80002aaa80002aaaaaaaaaaaaaaa80000000000000005555555500000000555555555555555555555555000000005555555555005500aaaaaaaaaaaa00000000000000000000aaaaaaaaaaaa000000000000000000015555555555540001555555555554000155555555555400015555555555540002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000000000000000000000555500005555000000000000000000000000000000000000000000000000
|0,12=>0xaa00aa00aa00aa00aa00aa00000000000000000000000000000000000000011111111155555555111111111111111111111111111111111111111111111110000000000002aaa8000000000002aaa80000000000000000000000000000000555555555555555500000000000055555555555555555555000000000000000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa000000015555555555555555555555555401540154015401540154015401540154015402aaaaaaaaaaaaaaa80000000000000002a802a802a802a800000000000000000555555555555555555555555000000005555555555005500555555550000000000000000000000000000aaaa0000aaaa00000000000000000000000000000001555555555555555554015401540154015401540154015401540154015401540002a802a802a802a802a802a80000000002a802a802a802a802a802a80000000550055005500550055005500555555550000000000000000000000000000000000000000aaaaaaaa00000000aa00aa0000000000aaaaaaaa00000000aa00aa015555555555555555555555555555555400000001555555540000000154015400000002a8000002a80000000000000000000002a8000002a80000000000000005555005555550055555500005555000055550055555500555555000055550000
|0,13=>0xaa00aa00aa00aa0000000000aa00aa00aa00aa00aa00aa01555400015555555555540001555400015554000155540001555400015554000282828282aaaaaaaa82828282aaaaaaaa8282828282828282828282828282828000055550000555500005555000000000000555500005555000055550000000000000000aaaaaaaa00000000aaaaaa0000000000aaaaaaaa00000000aaaaaa000001555400015554000155540001540000015554000155540001555400015402aaaaaaaaaaaaaaaaaaaaaaaaa802a802aaaaaaaaaaaaaaaaaaaaaaaaa802a800000000000000000000000000000000055555555555555555555555555005500000000000000000000000000aaaaaaaa000000000000000000000000aaaa00000154015400000000015401540154015400000000000000000000000000000002aaaaaaaaaaa80002aaaaaaaaaaa80000000000000000000000000000000000055550055555500555555005555550000555500555555005555550055555500000000000000000000000000000000000000aa00aa00aa00aa0000000000000001555400015554000155540001555400015400000154000001555400015554000000000000000000000000000000000002aaaaaaaaaaaaaaaaaaa80002aaa80005500550055005500550055005500550055555555555555555555555555005500
|0,14=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000001555400015555555555540001555554015554000155555555555400015555540000000002aaaaaaa8000000000002aaa800000002aaaaaaa80000000000000005555555555555555555555555555000055555555555555550000000000000000aa00aaaaaa00aaaaaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa000000000000000000000000015555555400000000000000000000000000000002aaa80002aaa80002aaa80002aaaaaaaaaaa80002aaa80002aaa80002aaa8000000000550000005500000055000000000000005500000055000000550000000000000000aaaa0000000000000000000000000000aaaaaaaa0000000000000000015401540154015400000000000000000000000000000000000000000000000222aa22aa22aa22aa22222222222222222222222222222222222222222222222505050505050555550505050505055555050505050505050505050505050505000000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaa00000000000154015400000000000000000000000001555555540000000000000000000000000000000002a802a800000002aaaaaaa800000002aaaaaaa800000000000000055555555000000005555555500000000550055000000000055005500
|0,15=>0xaaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa000000000000000000000000000000000000000000000000015555555554015402a802a802aaaaaaaaa802a802aaaaaaaaa802a802aaaaaaaaa802a802a802a805500550055005555550055005500550055005500550055555500550055005500aaaaaaaa00000000aaaaaaaaaaaaaaaaaaaa000000000000aaaa0000aaaa0001540154015401540154015400000000015555555555555555555555540000000002a802a802a802a802a802a802a802a802a802a80000000002a802a800000005555555555555555005500550055005555555555555555550055005500000000aaaaaaaaaaaaaaaaaaaaa0a0aaaaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00154000001540154015400000154000001540000015401540154000001540002aaaaaaa8000000000000000000000002aaaaaaa802a802a80000000000000005555555500550055555555550055005555555555005500555555555500000000aaaaaaaa00000000aaaaaaaa0000aaaaaaaaaaaa00000000aaaaaaaa000000015554000155540001555400015554000155540155555401555554000155540002aaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaaaaaaaaaaaaaaaaaaaaaaaaaa80000505050505050505050505050505000005050505050505050505050505050000
|1,0=>0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa000000aa00aa00aa0000015555555555555555555555540000000155555554000000015555555400000002aaaaaaa8000000000000000000000002aaaaaaaaaaaaaaa80000000000000000000555500005555000000000000000000005555000055550000000000000000aa00aaaaaa00aaaaaa00aa00aa00aa00aa00aaaaaa00aaaaaa00aa00aa00aa014155415541554155414141414141414141414141414141414141414141414142aaaaaaaaaaaaaaaaaaa80002aaa80002aaaaaaaaaaa80002aaa80002aaa800055555555555555555555555555555555555555555500550055555555550055000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aa000000aaaa0000aa015555555555555555555555540000000154015401540154015401540000000002a8000002a8000002a802a802a802a802a802a802a802a802a802a802a802a805555555555555555555555555555555500550055005500550055005500000000aaaaaaaaaaaaaaaaaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa000155540001555400015554000000000001555555555555555555555554000000000000000000000000000000000000000000000002aaaaaaa800000002aaa80005555555555555555555555555555000000000000000000000000000000000000
|1,1=>0xaaaaaaaaaa00aa00aaaaaaaaaa00aa000000000000000001540154015401540154015401540154015401540154015402aaaaaaa800000002aaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaa800000005500550055005500550055005500550055555555555555555500550055005500aaaaaaaa00aa00aaaaaaaaaa00000000aaaaaaaa00aa00aaaaaaaaaa000000015400000154000001540154015401540154000001540000015401540154015402aaa80002aaa80002aaaaaaaaaaaaaaa8000000000000000000000000000000000550055005500550000000000000000005500550055005500000000000000000000aaaa0000aa000000aaaa0000aa000000aaaa0000aa000000aaaa0000aa014141414155555555414141414141414141414141414141414141414141414142aaaaaaaaaaaaaaa800000002aaaaaaaaaaaaaaaaaaaaaaa800000002a802a8050505050505050505050505055555555505050505050505050505050505050500000000000aa00aa0000000000aa00aa000000000000000000000000000000015555555554015400000000000000000155555555555555540000000000000002aaaaaaa8000002aaaaaaaaa800000002aaaaaaa8000002aaaaaaaaa800000005555555555555555555555555555555555555555555500005555555555550000
|1,2=>0xaaaaaaaaaaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000001555555540000000155555554000000015555555400000002aaaaaaaaaaaaaaaa828282828282828282828282828282828282828282828285555000055555555555500005555555555550000555500005555000055550000aaaaaaaaaa00aa00aaaaaaaaaa00aa00000000000000000000000000000000000000000000000001555555555401540000000000000000015555555554015402aaaaaaaaaaaaa802aaaaaaaaaaaaa802aaaaaaaaaaaaa802aaaaaaaaaaaaa805555555555555555555555555555555500005555000055550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x380c101f0009818240201c0602050144016018202a05038201c1f0a82818040380c360a060101a12040280a040386832000281006020980018070c00c100a0285c2c08070540a040a00c040006010060209828180709020220a028101a030100018040380c200a028100e0f0700018040680c040a060100e0b040280a040480c1000028100e03030000a04018080200
|1=>0x130146a040380c04000281c100e088541405020580e03010000a040380c04001a0140e08198442a0a028101a030105414050201c0630178280a04018b80215050140807040b42a0a060100e12040285805020ac100e0a8280a040380c042a0501452040380c0400028100e031405414050b81c100e0a8280a04138201c1505030080701808141c028100e0b040541405
|2=>0x406426150501408071f0007a050200c04130a8280a041e01c0608000140807018b800360281c240808854140502034062e0a8280a040a020321505030080d018204c0a060100e37040285805148902c08070540a040380c2015050300a170b00c1015028100e030100038050201c061a000e01804038dc100a028100e080c8006c050203410190a8280a07018202200
|3=>0x28100e082305414050200c5c130a8281804018202626051140a040380c34000281c100e220541405068201c15050b00a04038208615050140807018c0000a028e41a0807054140c020580e120402818040380c1042050140814018b82a0a028101a03040004c0c148100e12040280a070c00c1015050140807040380036028100e030400082050203410330a8280a04
|4=>0x28580e48040382a0a028109e0304054144d028100e030405414050200c10130a8e0140c0201c2408050149607018202a0a028100e0325054140c148100e030102892050201c06080001408070d0382a0a0601408070186800052400c1015238280a07040643e15050140816040382a36028101a120405414050205006080009818040380c360a0e0140814040382a0a
|5=>0x203406080a8280a291205806080a8841805148902c03040540a04038481015050b00a0403820b215051600a040680c101505014085701820000a0281006082a054140c0294c0e030405414520201c0608000540a040380c0415050700a510380c101505014083b038203200050141a03040bc2a0a028d40807040642a0a128140803040040015028900807018082a0a
|6=>0x405414050201c060f0001452040380c5c15050140807040382a0a310140807019845415050140807040642a0a0e01408070417c2a0a0281c100e08854140c148100e030409814050201c100e00028bc050201c06080a97014050201c100e08854140c128101a03040541445028100e03040006c05021740e03040000a040182026152e0280a240201c10190a8288a05
|7=>0x40002a05021c006080a8280a040380c34000a8140807019842a0a370100e030405414050201c06080a9b414050201c0602000280a043500c10150501408160380c5c15050140807018b82a34050140807018202a69050140868038201c15050300807018203c0a060102c07018204c0a028100e0304000ce0a060140e65018202a0a028100e082c854142c0281cc603
|8=>0x380c1000190288a050205006080a8280a04039ec100e0a8280a040380c10003d1dc0a040380c1015050300a040380c10001b0140807018202a76050145204038206615050300a043a80c101505014e804038201c150501408071b8202a0a028107607018b8000a028100e0304000703a028d40807018b82a0a3901408030404c2a0a028100e082f854142c028100e71
|9=>0x50b00a04038f88000028100e0317054141c028100e03040a84c0a028100e08070541436028100e0807054680a028a40807018200026028100e08071f82a0a028102c07040cc2a0a060100e0304098141c06014080d040382a0a028100e033e8541425028101a03040002a053e0100e03040a81405148102c080705414050380c101f0a8e014050215c06080a8280a04
|10=>0x38201c000501408070420c2a0a2c01408030404c2a0a0283406080a884142c060141a0304054142c0281c06084085414053f8101a03040541405020580e03040004c051a8100e080705414050201c06080009868050380c10110aa0014051201c06080a9b00a040680c10151302818051c83406080a8280a24020580e08070540a7f0201c0608150280a04038dc1015
|11=>0xa8280a040382066150507018040380c040a029f0080701820000a028100e8c04054140c12810060809854140c458100e0304054140512010100e098541405450100e080705414050201c10880a8280a350201c0608000990e050201c06080a8288a050200c10130a82818050380c10440a8280a39020ec0e08070280a044280c1015050140807040385e1505014083b
|12=>0x5014080701820007a0aa4c0a040380c1015052480807018202a0a028a40807090202a0a060140816018202a36028101a080705414051c8900e080705414050201c0608000983825028102803040002a05120100e080705438050b85806080a8140816040382a0a0e014080701a442a0a060140814018202a0a028112007040382a0a028100608478541405022380608
|13=>0xc855300a4b8140807018202a0a029fc08030404c2a0a028100608098544c0a028100e03010000a950201c06080005418050201c061a0a8281805020201c130a82818040380c1032050b04a050200c1013000540a940201c06080a8280a040b00c1015238280a040380c1000338140816038481015050140807018202a420501408030404c2a21050300a04018202615
|14=>0x50140807018c02a0a028100e0350054142c028110a0304054b80a028100e9f0405414050203406080a8e014050380c10810a97014050201c06080aa7814050201d38080a8280a0403820be2f0a8280a040380c10154d8280a040680c1015400280a222400c1015050140807040382a0a3c01408070186c2a0a0e1140a07018203e15050140899018202a0a028100e08
|15=>0xa8294e050201c06080a82838050201c062e00028bc05148100e080c85414050201c06080aa981405528100e08070541472028101a030405414050205006080a8e014050201c100e0a87058a30201c06080a8280a290201c06020a8280a040380c80001e814080d018202a5c050140807018205e3205014080704064000a2f0300a07018203e15052840a040380c1015
|16=>0x50300a040380c10130a8280a040380c1015052755e040380c1015050142e07018202a0a028104e030405414ad028100e030405414050380c101f00054140c128900807018202a0a028100e0304055580a0281c900304054e60a2c0140807018202a0a0e0140807018202a5c558280a040380c1015550280a040380c10a90a8284a040380c1015521140a240201c0608
|17=>0x4002858055b8100e03040541405022d80e0304054140c128100e0304054141c028100e03042d42a0a028a40816018202a21050300a290205806080a82924050201c06080a82968050201c06080a8280a041580c1015051bc0a040380c102a0a8280a040380c10150508c0a040380c1015588288a050201c06080a828380c028100e7b018202a0a028100e030404c2a21
|18=>0x4054420c0289008160380c1015028100e03042f42a0a028100e0304055780a0e8140807018205415050140e03040442a0a02ae40e0304054140c0e8100e0304054141c060140807018202a0a1b0300a040380c10151a0280ab80201c06080a8281805148100e08070541425028100e03040a82a0a06014080701820fc15050940a290201c0608000540a040380c1015
|19=>0x201c06080a828de050201c06080a8280a04038f88015050940a041d81c0608000140807018218415050300a350201c06080a8281805020580e080705414050201c06080a8e0142c028a40807018202a26050940a040b01c0608000540a040380c10152e0284a050201c06080005468056001c06080a8280a045f00c10150501408070182000b50a8280a24020580e03
|20=>0x380c10150f0280a040b01c06080a89814055c0100e0304054142c060140807018202a0a638940a350201c06080005418051c81076070182014050201c060800055780a028118c030405414054a8100e030405414050201c06080a829880c028100e03040bc2a0a0281c0608088002a0a06014083b0380c1000050940a040182026150522c0a040380c101505014fe29
|21=>0x28100e03041402a0a02810c807018202a0a028100e03043302a0a290140807018202a0a0601408660380c101505014080701821961505014fe040b01c06080a82818310201c06080a8280a046501c06080a8280a240200c10130a884140c0289008030404c2a0a02a280807018202a21050300a8a0201c06080a828b6050201c06080a82990050201c06080a8280a04
|22=>0x380c10000ab400a040380c1015050140807018202a0a6781408070182196000a8283a050201c0608000541405020ec0608648280a044801c06080a884140c028112007018202a0a028100e03040548e0a0e1b80807018202a0a028100e0304054da0a028100e03040553038050140807018202a5c050b00a0401820021505014080701b382a0a028100e03040002a3a
|23=>0x28100e030405414d6028101a0304054420a06014080d018202a0a0601472240380c101505014080701900000a128100e0304055aa0c028100e0807054141c2281472040380c1000050940a040380c10000a8700ad40201c06080a8280ad20380c10150501448040380c1015108701805120100e030405438050205806080a884141c060140816018202a0a0e015a204
|24=>0xa82858050237c06080a8280a040b01c100e0a8280ade0380c10150501408076e8202a5e029fc0807018202a0a0e094080701821b8150501408030404c2a73050140807018202a0a2f0140807018202a26050700a040380c10db0a8280a291205806080a8140857018202a0a028100e03043682a0a6c0140807018202a0a028100e030435c2a0a028a40807040382a0a
|25=>0x2f014080701821c6000a828c0050201c06080a8285805022080e0304054144c028100e030405414050201c06087405414050201c06080ab9c14050201c06e50a8280a040380c102f0a8280a0403b901015050140807040382a0a2f014080701821c615050140807018202ae205071c2040380c101505014083b01821c015051140a044d01c06080a828e4050201c0608
|26=>0xa8280a0403821e01505014080701821de5e028100e03040006c050201c06080a8841478060140807018202a0a3c015dc040380c1015050140807040382a0a0e0140807018202aed050b00a7f0201c0608000280a040380c1000130280a040380c10ec0a8280a040380c04150501408076e82000150501408eb018202a0a02ba40807018202a0a028100e0304000700a
|27=>0x201c06080a8280a0d018202a0a1601408030404c2a21050300a04018202615053cc0a040380c101505014720d018202a0a028a40807018202a3805014080701821de0a028102c07018202a80050140807040640015052480807018202a0a028e40e03042cc14050203406080005414057901c06080a8280a041105806080a8280a290201c06080aa0014050201c1019
|28=>0x50146a040380c10151c0281805688100e03040541489028100e030405414f4028100e03040002a0a7d0140807018202a0a0e0140807018202a32050b00a041d81c100e0a8280a040380c10f80a8280a070182088150501408070182000ef0501408160380c10151c0280a0403bdc1015051140a040380c10154c0280a040380c10f60a8280a040380c10157a829e805
|29=>0x40546c050201c06088085414050201c06080a82a0005020500608000541405023f40e03040002a0a7f0140807018202a0a028100e031705414050201c06400001408160380c10152e02818040380c1026050940807018202a0a520140814018202a0a02811fa07018202a0a0281076070182000380501408fc018202a0a028a40807018202a5c0501408fb0380c1015
|30=>0x281c0608838541445028100e0304000145e028110407018202a5c0501408078300c1015050140905018202a0a3901452040380c1015050300aa50201c06080a8280a040380c11040a8280b030380c1000053f80a040380c10000a8280a040380c5c000a82a04050201c06080a8280a040b00c102a0a8280a040380c101510870580c028100e0304054382c028102c03
|31=>0x18202b12050140807018200026888140807018202a0a028580e48018202a21050300a160392006080a8280a0403b7410000a814090f018202a0a870100e030405414050201c06080005414050201c06080aa8814050242c0608000280a0403c2810150501612040380c1015050140807018682a0a028100e081985414050201c06083c8541472028102c07018202a0a
|32=>0x8b0202a0a028100e0304001de050201c060817855da0a028100e03043bc0a042e81c06080a828b005020580e0304054140c128a40807018202a0a06014080701820000a2f0940a040380c10002f0140807018221a5e2281452040380c1015050140807018222a15051600a290201c06080a8284a050203406080a8280a0403c501015050140807040380015050140807
|33=>0x108281805020580e030405414050201c060800028bc050201c06080885414050201c060800054700a028100e030445c2a0a02890080d018202a0a028100e03043e42a0a028100e03040557e0a028100e0304002180a028a40807018202a21050300a290201c06080a8280a040380c10151c0280a040380c10e00a8280a040380c1015052ec0a04038481015050140807
|34=>0x4055920a029ac0807018202a0a0e8140807018202a0a0281234030405414050231806080a8280a043401c06080a8280a390201c0608398280a040380c10152e0280ac00380c1015050140807018202a0a8c8140807018202a0a310300a040380c1015051780ac00201c06080a8280a07018202215050940a040380c10152f01408076e8202a0a5d01408160380c1015
|35=>0x28100e030405414d9028100e03040541425028100e0304054142c028123807018202a0a390140807018202a0a028100e030405414b08d8140807018202a0a028100e0304054420a0e0300a040380c1015050704a051c8100e030405414050201c06080a82a26050201c06080ab4c14053a0100e03040541425028100e03040002a0a028100e03040561a0a028100e03
|36=>0x380c10000501408160380c10000a8280a040380c10000a8d014051a8100e030405414ff128100e03040541405120102c07018202a050201c06080a828bc05148100e03040002a0a028100e03040541436028100e0304054680a028100e0304000143f028100e03041f82a0a8f8140807018202a0a028123c03040541405148102c030405414050201cf60304054151d
|37=>0xa82a42050201c06080a8280a040380c1015900280a0403b7410150501448040182026150501514040380c1015050146a040380c10000a8281805020ec0e030405414051c810760701820150e028100e030405414050201c060800054145e880140807018202a0a028100e03040bc2a0a028100e03040a82a0a0e0140807018202a0a750940807018202a0a5d014083b
|38=>0x12814080701821f215050140807019002a0a028101a030405414050201c060800054141c028e44807018202a0a028100e03043702a0a2281408070182000150501448040380c10150e0140816018202a0a0e0140807018202a5e5d4880a040380c1015050304a040380c1015051140a040380c10150501408900380c1015050140807018202a73050b0b0050201c0608
|39=>0x50140807018202a0a3c0140807018202a2605014080701820e60a2f0300a040380c10000a8280a39020ec0e030405414050201c06080a968140c028100e08070541425028100e03040002a05020ec0e03040002a0a02c900807018202a0a028107607018218615050140807018200015052e9fe051c8100e030405414ff028100e03040002a0a028100e03040541523
|40=>0x28100e0304054145e028100f250405414050201c100e0a8280a040380c1015052900a040380c10c30a829fe05020ec06080a8280a390201c06088c0284a050201c06080a828bc25028102c07018202a0a028100e0304055660a028100e03040007e05023180e030405414050201c06080aaa0141c029fc0807018202a0a028100e030405414551281452040380c1015
|41=>0x148100e03040541425028100e030405414050201c0608399780a040380c11270a8280a040380c10154002964ff0201c06080a82a4c040380c10150501408070182000155d0154a040380c1015050140807018202ac1050140807018202a1c1601408160380c1015398283a050201c06080a8283805148100e0304054e60a870100e030405414050201c060800054151d
|42=>0x28100e030405414050201c06080005414050201c06080a884140c028100e03040541405020ec0e030405414050201c06080a82974050201c06080a8287eff028100e030405414050201c06080a82838050201c06080a9cc14050201c06080a828bc05020580e030405414050201c06080ac301405
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x2d30151809cc0486021300f1806cc030601530091803cc018600930031800cc0006
|6,0=>0x10ab8839c40ee20070fcb87c9c3d6e1e470eeb8759c39ee1c870e0b86e9c366e1ac70d2b8679c32ee19070c4b8609c2f6e17560b73859dc2c0e15970a93852dc288e13d709b384bdc250e121708d38451821ae106707fb83e1c1e2e0ea7071b8371c1aae0ce7063b8301c172e0b27055b8291c13ae0967047b8221c102e07a7039b81b580cce0606
|6,1=>0x126b8919c47ee2387118b88a9c446e21c7
|7,0=>0x219c10b1c849041c820a41032080903fd71fb38fbdc7d0e3e171ecc0f49c796e3c381ddc0ece075703a471ce40e520719038481beb8ddd86df036781afc0d5e06a0e34971a0c0ce6066303298190c0c660624e30a818140bea05e502ea817140b6dc5a702cc7162b8af6056ce2ae8153b8a7e0530e290814440a0204f102717134c098604b6c2547
|7,1=>0x311c1871cc29060c8302b97f9cbed05f062f441785cbb305d182e4c17060b74e5b282d54168a0b35059282c5b960e0af7057472b6415920ab9055572a6c15160a7b05358296c1499ca3d051682874141a09fd04f86278413a209c104d8826841322098104b88258412a5c94304998248c12260904e47a8239411aa08c6e45b8229c112e0887043b8
|7,2=>0x1fb60fcb07dd83eac1f360f8b07bd83db39eba0f4ee79f83cbc1e3e0f0f077f83bc39dc20ed1076173acc1d460e930742739d41cca0e550723738dc1c4e0e170704737e41bd20dd906e4836f31b5a0d9d06c6835f41ada0d5d06a6834fb9a5e0d1f0687833fc19de0cdf06687330419620ca2e6498320c18e60c63062b6
|8,0=>0x501c27ea53e509eb74f1c276e13a529c994e04a6de535d29a684ceca659d31ee98694beca5d252d9096484adca551d29ae944949dca4ca52550921948c4a43e520d28fd947ac23b611c928dc8469ca32a518508ba8459ba2aa5145089a8448ca22250ff287694374219dd0c0e8597428c21261081283884184209e503d281684074201dcffd27f59
|8,1=>0x60c4304218110c0085fc42fc217d10bdf95ec3af45d7912bbf95db4aeba174eeb9e95cacae3257072b7b85b9c2dae16c52b5995a93ad2656812b3795983aca2163f2b169587bac21d6010af8857842ba215c10ad79567c2b1a557d0ab68556caa9255372a92954542a0a14f50a7195344a97e54ad2a4d95224a8f5d46b0a2d85124a87214272a0b8
|8,2=>0x7094b82a1c050dfa86f9bb7ae1bc70ddb86ea3b72e5b88edbb96d9c36b1db4aed9d86cb3b63a1b0b2d7e76bbbb5c1dad2ed6096abcb53e1a8f0d3e969b434ba1a4d0d1f768bc3441da110cff967b4b3b659cb0cdd866ac3336198cecbe865bbb2be194f0c9e964bbb23e190d2c7d963b3b1ba18ceec60762bcb13e188f0c3f861b4b0ba184eec207
|8,3=>0x8094402de0070ffb87fa3bfb21fc72fda97e9bbf31df8aefbd87dac3eb9df4eef9f87cc3be45df130f8097bcbbdc25ecf2f5f87ac3bd3e5e8d2f3e879bbbcba5e4d0f1e878b43c365e092efd777ac3bb61dcb0edc976a43b35dd8ecebe975bbbabe1d50eea0874bcba41dd0f2e7f873b4b9b65ccb0e5c9729cb92a5c850e3a8719bb8ae1c452e1b7
|8,4=>0x2106f07c783abc1b260ccd05e882acc1326087303b881a3c0ae6047101a9
|9,0=>0x945c4a0e24f712729934cc98624b312518924c490264711230891444882243112117904c480623f311f188f44c78223b111d088e4446fe636d31ad98d2c4676232b118c98c2445f222e9116c88b2bc579e2ad114e88a3444fde26f112f88934c47a222ef10f8883c43fa61eb30ed8872c437261a910cc8862442f2216910ab98514c26a2125108a8
|9,1=>0xa4ccd2426912f4818a3c4d1c5e8d4f4628a2d4514a289514419a1c4d0c22852f4218a0c4d042281113ff99fbc4fbe27cf13de99eaccf36278b13bd89da4ceb22747339a99c8cce226701137799b83cda5e6c1335889a844d1e667f13378997c4c9e263f13178987c4c1a65fd12f6897744b9de5bf12d789674cb16657b12b589564ca92253912939
|9,2=>0x29d4f4e28a6d4534a2996f4c38a5dc52ce295714a29
|10,0=>0x2ab315518aa4c55062a7315318a94c54862a3315118a84c540629f314f18
|11,0=>0x15617
|_,_=>0
def wAt:=mkWire dB 296 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2855018c918854028b102029038290600f0285503829020d9028551d828038550a829040e91c8280205502855018c918854028b10202a040990a8291285402829040990a8291285402829040c918854028b10a8b102855018991285402829040990a8711285402829040990a82912854028290409902855128540282902855040991285402829038290208d11028038850285602855040790e854028710382a
|1=>0x382a2280f028010a829038900a8b1020b10202a1a81f020010a8290409912854028290600f02058028550394306093020290285502939000730382a0a8290285501899128540282926010060590382902855040991285402829028550a82902855040e91c8280205502855040790e85402871028010a829040e91c828020550285501899128540282901899128540282902855200020a82901901040fd0a828
|2=>0xa9790a82a0600f028551201c020290282902855028010a8291d828038550a829128e402829020552280f06029028550602903890020290285502029038290201d028560201d0285502029038290189912854028292d80f029690a8b30202a0602b03890028550a8290389912854028290395a021551082a0285602855020db1d828038550a829028e91c828020550409912854028290382a020790e85402871
|3=>0x1c8280205537823028a90a8710382a0288d1102803885028560a829040991285402829039b33582802085028562282306029028550e854028710382a028551285402829028550009b12854028290a8290285533010039790a82a2d80f029690a8b302190039551082a028560a829040d91d828038552282306029028552280f06029028553000f028bd0a8b10202a0205a038290600f02855128540282902855
|4=>0x28a90a8710382a038290600f02855038790e854028710382a18854038d402801020010a829000db0a8291d82803855029e50a9e1020720382a1d82802855038550a829130b112854028293900f029cd0a82b038e9028551c82802055018c918854028b10202a22823028010a8290a8291c82802055029cd03892020290a82b3000f028bd0a8b10a829018d91d82803855038cb18854028b10202a0a829040e9
|5=>0x12854028293582802029020850285612854038900202902829020550389002029028550600f0285502029038290a8710382a1285702829018c918854028b10a82901901040fd0a8282282306029028550a87112854028291d828038550600f028550a82912854028290600f03855028553900f029cd0a82b0285512854028290600f038900202902855041b13582802085028560a82903890020290282937857
|6=>0x2029028290285502855029e1020720382a0600f0285503892020294480f060a50201d028550a82912854028292c0b10202a0602b028550280103892020290a8290219a02855039790a82a02055038550600f0285503a180217110829028560a8290600f028554200f0609102029028550202a0389002029028560202a0389002029028550220a03971108290285603890128570282912854038290a8290a829
|7=>0x12854028291d8280285503829038550600f038900202902855020290600f12854028291a81c020010a8290382a020290600f0285503829020d91d828038550600f02855038710382a420230609102029028551a81c1c82902055028550202a0600f028554201f060910202902855039b13582802085028563900f029cd0a82b028550409912854028290a8290e857028710382a01a350605a03829028551201f
|8=>0xe854028710382a028014d013038010a8290394106093020290285512854038920202902829040990a82912854028294b02b020e1028020a82902855040e91c8280205503892020290600f0285518854028b10285503892020290a8290009b0a829128540282901899128540282945854029e1020720382a4501f148290201d12037038900202902855000db1d828038550a829060c4028b10202a0285501899
|9=>0x20290a82b0202a0382a0600f0285512a9302829060280285504099128540282920002040fd0a8280a82910829038900285618854028b10a8b12280f028010a82a0a8294d0131d829038550285502a890a9e3020720382a040c918854028b10202a30023028bd0a8b103a1810829028560188d11028038850285601a75060720382a02855128560389002829020580382903885028560600f1482a0285504079
|10=>0x28550389202029060720382a0285502ac30a8b00202a020d91d828038553a01c021790a82a02ab912056020294d013038010a82902029028290285503972108290285602058038290a82b0602b028551082902856028aa0a8710382a3f813128570282902829060280285502801020290a82902aa10a8730382a0a82a22823028010a8292280f0602902855109e10207202856020ed0600f02855029cd03890
|11=>0x38020a82918857028b10202a0600f0201d028550a871028290382a020ee0385502855028290201d0a8291285602829148850201d0285603a0112856028290382a0282902855000b30202a0a829038290201d02856038290201d0285502ac10a8b00202a029ed0b05703829038eb1c82802055028a90a8710382a110280388502856598295905402811028010382a0a829028550b05703829038920202902856
|12=>0xa829028290385561829028ee038551c8290205502855038290600f02855028020202a0a82912854028290201d02829038290a82940029128560282902829038020a82902305148560381103aff5905602811000b30202a0a829028560202903829028550202903829398710a82b0382a59000028110a829028710a8710382a450131482903811022ef0aae80282a028710382a02855028551d8280385502855
|13=>0x2029148290201d02856148290201d02855029690a8b30202a02b250b054038290e854028710382a12854038290282918857028b10202a1c82a020550285502829020010a8290205503855028550a8291d85803829038553582b02085028566282a0601f02855028550a8b10202a0205a038290a82902855038550a829038920202902829029e1020720382a1285702829028a90a8710382a01901040fd0a828
|14=>0xb0540382903855038b1028560202a02855038b10202a10871028560382a028d91d82803855108b1028560202a02802020020a82910829028561a81f020010a829042ed0aae80282a1c828020550a829060930202902855039551082a028560ab35028b20202a028e91c8280205502855039790a82a2281f0602902855038291285702829028b10202a0285503a9106028028550285603892020290285503892
|15=>0x2029028550201d0600f0285510872028560382a0389002029028560389002029028550285502029020550a829040fd0a8280282959028028110382a0600f0285502801020550a8290382a0a829023150601f028550234f0b0560382902029028560382a02855020290382a03871028560382a02855038710382a1c82b020550a8292c01d0602b02855060700382a028552281f028010a829028710382a0a829
|16=>0x202a0a82a0600f02855028d6020010a8290e85602871028db1d828038550285a038290385502801038010a829029cd0a82b0202a0389b1285402829038290600f02855022ed0aae80282a01ae90282a0a82a0382a128570282906013028290285503892020290a82b1302a128540282912854028290382a02a96148550201d0201d02029038290389912854028296c8130601d028556c82b0601d0285506092
|17=>0x28560382a1482a0201d028550230d028ee038550382a0600f02855028be0a8b10202a0a829128570282912854028290a8290ab55590280281104099128540282901ae90282a0a82903ac10a8b00202a023a90602a02855028020a82a0a829028d6020010a829028bd0a8b10202a039711082902856060590382902855060a70201d0285518856028b10202a043990a8700382a0ab1d0a8b20202a01b35028b2
|18=>0x208502856700560285a03829028d1038020a82903890020b10202a02856038920202902855038920202902b1d0a8b20202a1201c0202902055028020a829399790a82b0a82a12856028292280f028010a82902ac10a8b00202a59054020550281103890020290a8290234d0b056038290382903885028560201d12856028292280f06029028557880f0601102855399790a82b0a82a0a8291d8280385502072
|19=>0x382910829028561285402829028550282906028028551a81c020010a829038e1028020a82903855028020a82903afd590560281110829028561208702029028560a8291c82b0205502855060a50201d02855028d1038020a829060730382a0285518854028b10202a038550600f028557c8551281f0282933013039790a82a000ff0a8280a82902802038290a829018e91c8280205502801020020a8293581f
|20=>0x281d028010a82a0a829108290285606058038290285503ac30a8b00202a0201d029cd0a82b02855148550201d628290601f028550a829020fd0a8280a82922823028010a829060b30202a028550a871038710382a0202a028560382a028550202a0382a1d828038290385502b461c82b020557882806011028551a81c020010a829038e1028020a8297f8030281d0a829228230602902855040fd0a8280a829
|21=>0x602b0285503890020290282901ba90602a028550a8290600f028550ac4f028720382a0a829128540282902b05148560201d02058038290285602058038290285501ae90282a0a8298801c590290281102aed0aae80282a868290aaeb0282a0a9e3020720382a03c31020560a82901b990a8700382a020991285402829040e91c828020553900f029cd0a82b0a9e1020720382a029cd038290a82b840137f829
|22=>0xa82a0a8290205a03829028020a8297f8130281d03890020291281f028295905602811020560a8290201d028560201d02855028020a8290285a038290aae80282a01899128540282901aed0aae80282a000ff0a8280a8290a8b10202a000ff0a8280a829128e40282902055038290602b0285502855028290201d028550a82a0a8290a82a028290a8290aaeb0282a0a82a028010201d0a829700550285a03829
|23=>0x601d02855028290202a039cd0a82b029cd0a82b0a8b00202a02c6103856028560382a0382a028550282902055028720382a0b05603829021790a82a028290a8290aaeb0282a0b054038290208502856028710382a03c3302056038fd0a8281d82b038550a82b02055108290285602461038568602a020560a8720382a0a82a0285502461038560205a038290a82a0282901ae90282a03829028560382902855
|24=>0x28a50201d860290205601ae90282a0389202029148290201d020010a82903855028550205503855028fd0a8280a82a0a82959029028110a8b10202a0a8710382a0602a028550282a02829038550a829038290a829038020a829020010a829028290281d0202903829000570a8290201d0a8291d82803855038020a8290a8280a829020ee038557f82b0281d038ff0a828038290201d0b05703829029790a82a
|25=>0x28290201d020720382a12854028290a82b0a82a0a8290285502055038550a8b30202a0600f02855028290a829038550a829022e90282a028ee038550282a0a829020550281d0281d0a8297f8280281d1281f02829040fd0a82803890020290382a0a82902029020550601302855028010a829020290382a038710382a0282a0a82a7f8570281d02829028550602902855038b10202a0a82b0202a0602b02855
|26=>0xa82b0a82a03829020560201d028290a82b0a82a0aae90282a1285602829028110281d028ff0a8280282a0a829148550201d148560201d0202a0382a038290a82b028710382a0a82b0201d028fd0a8280a9790a82a029790a82a018fd0a8280600f028550602802855028ee03855038550281d03856020550a82a02829038290282959054028110a8280a829038fd0a8280a8730382a12857028291082a02856
|27=>0xa8290285602855038550282a0a8280281d0382a
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x29200000000000000004d50000000000000000000125000000000000115000000000000000000004050000000000000000000000000003c40708000019a800005e80a9400000000000099000000000448000000001e4000000000d2000002c804900000000000003900000000014801540000005
|6,1=>0x16d000000000aca00000000000
|7,0=>0x45d08a1911300004350851906420483f907d20f6400003c907720eb3000000000000e741c8638106e20d931aa834506718000000032cc63a0c3418062f10000000017082d10582000015a62a5052a0a1413c626904b9893411e822d043a08340fe81f0c3c200000ea61c8c37986b40ce8000031a05f4
|7,1=>0x3c6877d0eda1d833a887410e699c9438a87050dea1b9436a80000d8a1ae335486990d1219e433480000cb99934000063d0c5a18743086604c00017e300005e90bb217242dc85a90b3996342c06574caca00002ac654cca8194d329285150a0a13d4274600009b213512628000096a129424a8488c8f991b4
|7,2=>0xa2d1441a85350469f9000027a44ec89ccd37a26c34d26995130a25d44b28958d299a4f40000000000024b400000001241a44448268f511ca235400000000000231445a88a5112a221443c686cc000000042e8850d08220d34128815000020143fc67e90fb21f423e627bd0f5a1e74
|8,0=>0x6906d189a19b40367a6ce8d9b9b3436626cb8d959b28364a6c88d8f9b1c36326c58d899b10361a6c28d839b0436026bf8d7d9af835ea6bc8d779aed25d46b9cd721ae135bc6b6cd6c1ad535a46b3cd661ac9358c6b0cd601abd35746adcd5a1ab1355c6aacd541aa535446a8094f129b35306a54d491a8f3
|8,1=>0x8087004dff1bfb37f06fd4df91bef37d86fa4df31be337c24f78ded9bd837aa6f48de79bcc37926f18de19bc0377a6ee8ddb9bb437626eb8dd59ba9274c6e8cdd01b9d37346e5cdca1b91371c6e2cdc41b8537046dfcdbe1b7936ec6dccdb81b6d36d46d9cdb21b6136c02d74dad1b5736a86d44da71b4b3
|8,2=>0x98272f8e5d9cb8396a72c8e579cac3952729ca521ca2293e7270e4c9c9639267240e469c8a390e7210e409c7e38f671e0e3a9c7238de71b0e349c6638c67180e2e9c5a38ae7150e289c4e38967120e229c42387e70f0e1c9c37286870c4e171c2b38507094e111c1f38387064e0b1c1338207034e051c073
|8,3=>0xaf675e0eba9d723ade75b0eb49d663ac67580eae9d5a3aae7550ea89d4e3a967520ea29d423a7e74f0e9d15373a6874c4e971d2b3a50749c6921d213a3c746ce8c1d153a24743ce861d093a0c740ce801cfd39f473dce7a1cf139dc73ace7494e639ca3388e6f9cdc39b27358e699cd0399a7328e639cc43
|8,4=>0x2d19da03b3a766cacc1d953b24763cec61d893b0c760cec01d7e2
|9,0=>0xc485888b10161e2c385868b0c16162c285848b08160e2c185828b0416062c085808b0015fe2bf857e8afc15f62be857c8af815ee2bd857a8af415e62bc85788af015de2bb85768aec15d62ba85748ae815ce2b985728ae415c62b885708ae015be2b7856e8adc15b62b6856c8ad815ae2b5856a8ad415a62
|9,1=>0xd485a88b50169e2d385a68b4c16962d285a48b48168e2d185a28b4416862d085a08b40167e2cf859e8b3c16762ce859c8b38166e2cd859a8b3416662cc85988b30165e2cb85968b2c16562ca85948b28164e2c985928b2416462c885908b20163e2c7858e8b1c16362c6858c8b18162e2c5858a8b1416262
|9,2=>0x35c16b62d685ac8b5816ae2d585aa8b5416a62
|10,0=>0x3638ec61d8a3b107618ec21d823b0075f8ebe1d7a3af075d8eba1
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 15
def pmP:Nat→Nat
|0=>0x900000000004480000000021e0000000010e00000000085800000000424000000002100000000010600000000082000000000400000000001f200000000041000000000190000000000c00000000005a0000000002c0000000001380000000009400000000048000000000200000000000c00000000004800000000016000000000090000000000400000000001c0000000000c00000000004000000000018000000000080000000000200000000000
|1=>0x10078000000080200000000400a00000002002000000008830000000030200000000101a0000000080a000000003af80000000153c000000008240000000040900000000201000000000d2000000000614000000002500000000010f800000000804000000002fe0000000016c000000000b200000000056c000000002a40000000014c000000000a50000000005240000000029000000000144000000000a00000000004bc0000000024e00000000124
|2=>0x80a2000000040508000000202820000001013f0000000809780000004047c0000002021e00000010109000000080808000000404000000002004200000010012000000080088000000400080000002000200000010000000000019878000000095fc00000004ade0000000255f0000000129f8000000085fc000000042be00000002148000000010a10000000084fc0000000425e0000000210f0000000108500000000840c0000000420000000002042
|3=>0x1000900000008001000000038a1e0000001c10f0000000d0bf80000006847c00000024afe0000001251f0000000928e8000000485fc000000242de0000001215f0000000909f8000000484bc0000002423e0000001210f000000090810000000481740000002401e0000001112f0000000888f80000004242000000020a9e0000001051f0000000828780000004142c0000002063e0000001017f000000080bc8000000405bc000000202a40000001014f
|4=>0x800bf8000002c0c7c0000014061e0000009311d000000488978000002440b40000012063e0000009012f0000004808f8000002004bc0000010023e000000800600000004000a00000020003c000000800100000003210f0000001809f8000000c047c000000600240000002210f0000001028f800000081068000000406be0000002031f00000010183000000080c10000000402940000002011f00000010089000000080430000000400360000002001a
|5=>0x200009e8000100004000000402005c000010b115f000008488b78000042415bc000021202de0000108016f00000810a8f800004041d7c000020206be0000101031f000008080b780000404047c000020202320000101006d000008003af8000040015b400002000abe0000100054f0000080028f800004000d7c0000200063e0000100016f000006000978000024487fc000012242fe0000091211f00000180487800000800020000002242fe000001001ff
|6=>0x400400978002002004380010006623e0008003130f0004001018f800200048dfc0010002467e0008001217f0004000909f8002000484ec0010002063e000800103020004000818000020004057c0010002021e0008000217f000400003af8002000015bc00100000a9e0008000042c00040000185000200000c20001000002a400080000144000200080e180008004a08c0002502427e0001201211f00004188687800020c4243c0000812225e0000401016f
|7=>0x80000088f8040000044380200000221401000001106008000001af8024000c041c0120002029e0090001010f00480008083801c100405bc00900120ade0040101012f00200040ab78010000485fc008000048be0040000215f002000000870010000000240080000000000120010107000800080c780040004061c0020002029e0008401031f0004200808780021000046c0010212225e0008101016f000408080978002002484fc0010012020c0008008217f
|8=>0x8008081af804004040c7c02002000ebe0100091210f0080005188780400024443c0200010267e0100008131f0080000d08780400004c46c020000246fe0100001231f008000090a780400004847c0200002423a0100001210f008000088bf80400004457c0200002227e0100001111d00800008887804000044408020000206be0100001031f0080000808f80400000cc7c0200000461e01000002207008000010a78040000084bc0200000423a0100000210f
|9=>0x40000082a782000004143c100000202be0800001014f04000008084820000001428100000002de0800000015a040000000968200000000340800002029e0300108135f01800000b8f80c00000047c041000206be0200101075f0100080828f808004040d7c040020006be020000121420100000909f808000048108040000200a40200000200a010000000ac0080000001680280200263e0108400031f0084004089f804004244c7c020021222be0100101117f
|10=>0x110000001af88800000047c42000102ebe2040009016f1000001018f8800000404bc2020002c27e1010001217f080800010bf8400000785fc2000002427e1000000217f0800000108f82800004057c11200020a9e0808401071f04040008287820200002c7c10008122a5e0800101055f040001080a782000024042010000060a3e0800002050a040000092bf8200000494fc10000024a5e0800001217f040000090bc82000004857c100000242920800001094b
|11=>0x880000094dfa000000000488000012025e4000001211f2000000000208c004244dfc440000206be2200000237f
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x8000003800000000000040000000001a0000000000000800000000800000000000150000000000000000040280032000b0d00000000100000010000004000000800010080000000080000020b8003a
|7,0=>0x1a4432020083804c320004163e0280002041c820320501800040100104320106af800020026844190285008a00104d8e000101004020caf440143f000a612088001e081c01004190015c04160001c08c600b11445100308020200000006601158320436a9c0400000080201011440000080684200020450e1c020041ab100864dc522a8087e000b010049203800fa01
|7,1=>0x14404020101c00052c0093e0d499443207350101a51000000001000001a2f0114810010000000bf5187c32190205800000d0089e160c8f00001010640c500605c0adc
|8,0=>0x99cb99cfa8816cb74a52bc6753720c94b43b0e10836b097c403c4784429fa523b168576386a90ec9b399c5e527558a4ef2b70b79a6caa1548e4e62f89590fe4a452cb4e2445a7101461fe72a65b2b04b3a1223d925c0f25cb23d7e070eb5c2f254e043a049c9948963bd06044caca516443208e33139099ab5a048ca14fd819c1ba72361ad98b2388081a75545182227
|8,1=>0x22d61d5102c969a8cbaca58f0734843e2ef462bad2126994eecd4f382010aa93b0c2966882060391459bd4b629af4d53e54339e4b6ad30c2cfed1768b06e2919a71d8a98b1da536777469ceaa2243218494c1fcec0a749c5367283c211af97b1288c6f18addee5f319ccecc2aac48965d15cd964fb3296a3874a9ba9700239c20542868bdce356952ba22736b2253ab2
|8,2=>0xf87a1688c5ab91aa2a834338a059a7f
|9,0=>0x81a38ec763b1edf1465b421794468568c915899a4e68b46164ed3f901d2a2695ab821344b14bac0af50888e49ba6cf237053b584d33f831d27d5b59d5e46db71cf644793b3cce310a393a3cd75a3955f183b239b31e3b48abe7544354f3307847e7e71a61ca8aba8041dc47639b49824d311d968bb2cc39b110a3c85ff47aa3a2a0738c98268df8e9b1c88ea49a59e73
|9,1=>0xec762cd74e7444f16888da
|10,0=>0xb2599f478947696c08c073923010836
|11,0=>0x1d
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 45 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_246 9 roots_246 ops++addP pm 2 dom_238 9 roots_238 ops++addP pm 3 dom_250 10 roots_250 ops++addP pm 4 dzo_118_8 6 roots_118 ops++addP pm 5 dzo_110_16 6 roots_110 ops++addP pm 6 dzo_158_32 6 roots_158 ops++addP pm 7 dzo_186_4 6 roots_186 ops++addP pm 8 dom_222 9 roots_222 ops++addP pm 9 dzo_246_8 7 roots_246 ops++addP pm 10 dzo_222_32 7 roots_222 ops++addP pm 11 dzo_154_4 5 roots_154 ops++addP pm 12 dzo_230_16 6 roots_230 ops++addP pm 13 dom_126 7 roots_126 ops++addP pm 14 dom_218 8 roots_218 ops++addP pm 15 dom_186 7 roots_186 ops++addP pm 16 dom_190 8 roots_190 ops++addP pm 17 dom_230 7 roots_230 ops++addP pm 18 dzo_236_16 6 roots_236 ops++addP pm 19 dzo_238_16 7 roots_238 ops++addP pm 20 dom_188 6 roots_188 ops++addP pm 21 dzo_156_32 5 roots_156 ops++addP pm 22 dzo_116_8 5 roots_116 ops++addP pm 23 dom_124 6 roots_124 ops++addP pm 24 dzo_102_8 5 roots_102 ops++addP pm 25 dzo_108_16 5 roots_108 ops++addP pm 26 dzo_102_16 5 roots_102 ops++addP pm 27 dom_220 7 roots_220 ops++addP pm 28 dom_236 7 roots_236 ops++addP pm 29 dom_242 7 roots_242 ops++addP pm 30 dzo_154_32 5 roots_154 ops++addP pm 31 dom_102 5 roots_102 ops++addP pm 32 dzo_218_4 6 roots_218 ops++addP pm 33 dzo_234_16 6 roots_234 ops++addP pm 34 dom_206 6 roots_206 ops++addP pm 35 dzo_218_32 6 roots_218 ops++addP pm 36 dzo_230_8 6 roots_230 ops++addP pm 37 dom_214 6 roots_214 ops++addP pm 38 dzo_220_32 6 roots_220 ops++addP pm 39 dom_154 5 roots_154 ops++addP pm 40 dom_122 6 roots_122 ops++addP pm 41 dom_198 5 roots_198 ops++addP pm 42 dom_174 5 roots_174 ops++addP pm 43 dom_182 5 roots_182 ops++addP pm 44 dom_234 7 roots_234 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_118_8_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_110_16_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_158_32_152 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_186_4_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_246_8_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_222_32_152 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_154_4_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_230_16_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_236_16_100 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_238_16_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_156_32_152 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_116_8_100 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_102_8_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_108_16_100 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_102_16_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_154_32_152 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_218_4_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_234_16_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_218_32_152 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_230_8_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_220_32_152 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_234 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 72 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 72 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 187 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 59 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 187 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 270 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 14 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 270 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 138 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 10 128 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 138 → Z 9 i = true := (range_split z9_0 z9_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 14 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_254 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_247:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_iso_b isoMvS_247 (by decide +kernel) lowS_239
def dzo_159_32:=0xffffffff000000000000000000000000ffffffff00000000
def gzo_159_32:=0xfffffffe000000000000000000000000fffefefc00000000
def gsh_159_32:=0xfffffffe000000000000000000000000fffefefc
theorem lowS_zo_159_32_153:Lower true dzo_159_32 roots_159 gzo_159_32 9:=lower_iso_b (d1:=dom_159) (r1:=roots_159) (T1:=gsh_159_32) [(dom_159,32)] (by decide +kernel) (lower_slice_b (T:=gsh_159_32) [(0xcccccccc000000000000000000000000cccccccc,0,2),(0xf0f0f0f0000000000000000000000000f0f0f0f0,0,4)] (by decide +kernel) lowS_153)
def dzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a000
def gsh_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a00
theorem lowS_zo_251_4_155:Lower true dzo_251_4 roots_251 gzo_251_4 10:=lower_iso_b (d1:=dom_251) (r1:=roots_251) (T1:=gsh_251_4) [(dom_251,4)] (by decide +kernel) (lower_slice_b (T:=gsh_251_4) [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,0,32),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,0,64)] (by decide +kernel) lowS_155)
def dzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
def gzo_219_4:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0f000000000f0a0a000
def gsh_219_4:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0f000000000f0a0a00
theorem lowS_zo_219_4_155:Lower true dzo_219_4 roots_219 gzo_219_4 9:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_4) [(dom_219,4)] (by decide +kernel) (lower_slice_b (T:=gsh_219_4) [(0xf0f0f0f0000000000000000000000000f0f0f0f0000000000000000,0,64)] (by decide +kernel) lowS_155)
def dzo_223_32:=0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def gzo_223_32:=0xffffffff00000000fffffffe00000000ffffffff00000000fffefefc00000000
def gsh_223_32:=0xffffffff00000000fffffffe00000000ffffffff00000000fffefefc
theorem lowS_zo_223_32_153:Lower true dzo_223_32 roots_223 gzo_223_32 10:=lower_iso_b (d1:=dom_223) (r1:=roots_223) (T1:=gsh_223_32) [(dom_223,32)] (by decide +kernel) (lower_slice_b (T:=gsh_223_32) [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,0,2),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,0,4),(0xffffffff000000000000000000000000ffffffff0000000000000000,0,64)] (by decide +kernel) lowS_153)
def dzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def gzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fe00ff00fe00ff00aa00
def gsh_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fe00ff00fe00ff00aa
theorem lowS_zo_247_8_102:Lower true dzo_247_8 roots_247 gzo_247_8 8:=lower_iso_b (d1:=dom_247) (r1:=roots_247) (T1:=gsh_247_8) [(dom_247,8)] (by decide +kernel) (lower_slice_b (T:=gsh_247_8) [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,0,1),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000,0,16),(0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_102)
def dzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def gzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000fffe0000fffe0000ffaa0000
def gsh_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000fffe0000fffe0000ffaa
theorem lowS_zo_239_16_102:Lower true dzo_239_16 roots_239 gzo_239_16 8:=lower_iso_b (d1:=dom_239) (r1:=roots_239) (T1:=gsh_239_16) [(dom_239,16)] (by decide +kernel) (lower_slice_b (T:=gsh_239_16) [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,0,1),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,0,8),(0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_102)
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000fffe0000fffe0000ffaa0000
def gsh_111_16:=0xffff0000fffe0000fffe0000ffaa
theorem lowS_zo_111_16_102:Lower true dzo_111_16 roots_111 gzo_111_16 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xaaaa0000aaaa0000aaaa0000aaaa,0,1),(0xff000000ff000000ff000000ff00,0,8)] (by decide +kernel) lowS_102)
def dzo_119_8:=0xff00ff00ff00ff00ff00ff00ff00ff00
def gzo_119_8:=0xff00ff00ff00fe00ff00fe00ff00aa00
def gsh_119_8:=0xff00ff00ff00fe00ff00fe00ff00aa
theorem lowS_zo_119_8_102:Lower true dzo_119_8 roots_119 gzo_119_8 7:=lower_iso_b (d1:=dom_119) (r1:=roots_119) (T1:=gsh_119_8) [(dom_119,8)] (by decide +kernel) (lower_slice_b (T:=gsh_119_8) [(0xaa00aa00aa00aa00aa00aa00aa00aa,0,1),(0xff000000ff000000ff000000ff0000,0,16)] (by decide +kernel) lowS_102)
def dzo_103_8:=0xff000000ff000000ff000000ff00
def gzo_103_8:=0xff000000fe000000fe000000aa00
def gsh_103_8:=0xff000000fe000000fe000000aa
theorem lowS_zo_103_8_102:Lower true dzo_103_8 roots_103 gzo_103_8 6:=lower_iso_b (d1:=dom_103) (r1:=roots_103) (T1:=gsh_103_8) [(dom_103,8)] (by decide +kernel) (lower_slice_b (T:=gsh_103_8) [(0xaa000000aa000000aa000000aa,0,1)] (by decide +kernel) lowS_102)
def dzo_103_16:=0xff000000ff000000ff000000ff0000
def gzo_103_16:=0xff000000fe000000fe000000aa0000
def gsh_103_16:=0xff000000fe000000fe000000aa
theorem lowS_zo_103_16_102:Lower true dzo_103_16 roots_103 gzo_103_16 6:=lower_iso_b (d1:=dom_103) (r1:=roots_103) (T1:=gsh_103_16) [(dom_103,16)] (by decide +kernel) (lower_slice_b (T:=gsh_103_16) [(0xaa000000aa000000aa000000aa,0,1)] (by decide +kernel) lowS_102)
def dzo_231_8:=0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00
def gzo_231_8:=0xff000000ff000000ff000000ff000000ff000000fe000000fe000000aa00
def gsh_231_8:=0xff000000ff000000ff000000ff000000ff000000fe000000fe000000aa
theorem lowS_zo_231_8_102:Lower true dzo_231_8 roots_231 gzo_231_8 7:=lower_iso_b (d1:=dom_231) (r1:=roots_231) (T1:=gsh_231_8) [(dom_231,8)] (by decide +kernel) (lower_slice_b (T:=gsh_231_8) [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,0,1),(0xff000000ff000000ff000000ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_102)
def dzo_231_16:=0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
def gzo_231_16:=0xff000000ff000000ff000000ff000000ff000000fe000000fe000000aa0000
def gsh_231_16:=0xff000000ff000000ff000000ff000000ff000000fe000000fe000000aa
theorem lowS_zo_231_16_102:Lower true dzo_231_16 roots_231 gzo_231_16 7:=lower_iso_b (d1:=dom_231) (r1:=roots_231) (T1:=gsh_231_16) [(dom_231,16)] (by decide +kernel) (lower_slice_b (T:=gsh_231_16) [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,0,1),(0xff000000ff000000ff000000ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_102)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(5,133),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,24),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,28),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,17),(16,24),(16,144),(18,19),(18,26),(18,50),(18,82),(18,146),(20,21),(20,28),(20,52),(20,84),(20,148),(22,23),(22,30),(22,54),(22,86),(22,150),(32,34),(32,36),(32,96),(33,35),(33,37),(33,41),(33,49),(33,97),(33,161),(40,41),(40,42),(40,44),(40,56),(40,104),(40,168),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,68),(64,96),(64,192),(72,73),(72,74),(72,76),(72,88),(72,104),(72,200),(80,81),(80,82),(80,84),(80,88),(80,112),(80,208),(128,129),(128,130),(128,136),(128,144),(128,192),(132,133),(132,134),(132,140),(132,148),(132,164),(132,196),(160,161),(160,162),(160,164),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|8=>2
|9=>13
|10=>52
|11=>31
|12=>7
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xb6bca6ddc3
|9,0=>0xe0c44dd0135d7f2493ba3eb3136ce635c7a2931c28e5a25ec118d011460511034
|10,0=>0xe646fcf52bc9634baf6eb7931aeafca60e1900808e4858505683c3b825c6820937792e6f8036ea776e10f6d2066c6016ae7c654c461a6e5bd855a143570fe55fef4f7654d0964a1ec4759f3ee0c3aa4e382093535f32aec32573322b72f5cb26fd02331e21be31fe931dc5f1d42a1cf84187ed15e1013b0f0f0090c0460be020b945
|11,0=>0xe8aaedb393c4d63b08a3ac8f0a51fba4cc5a309799cfb97a63904577e9c37c24276ca5736916e3d66b37066f0c6551f641235cbf94c8e347d6c44cc4433cd3799a343e11d9860c8b807c2801f4c
|12,0=>0xdd9d2c33a38fd7c792e461e180eef70c075
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffffff0000ffff0000ff00ff00ff00ff00ff000000ff000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
|0,1=>0xffffffffffffff00ffffffffffffff000000000000000000ffffffffffffffff0000000000000000ff00ff00ff00ff00ffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffff00ffffff00ffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000000000ffffffff00000000ffffffff00000000ffffff0000000000ffffff000000000000000000ffffffffffffffff0000000000000000ffffff00ffffff0000000000000000000000000000000000ffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00ffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00ffffffffffffffffff00ff00ff00ff00ffff0000ffff0000ff000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffff00ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffffffffffffffffffffffffffffffffffffffff00000000000000005555555555555555555555555555555555555555555555555555550055555500
|0,2=>0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000ffffffff00ff00ffffffffff00ff00ffffffffff00ff0000ffffffff00ff00000000ffff0000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff00ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ff000000ff0000000000000000000000000000000000ffffffffffffffffff00ff00ff00ff0000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000000000ff000000ff000000ff000000ff000000ff000000ff000000000000000000000000000000000000000000000000ffffffffffffffffffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffff00ffffff000000ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ff00ffffff00ffffff00ffffff00ffffff00ffffff00ff00ff00ffffff00ff00ffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff000000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00
|0,3=>0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00000000000000000000000000000000000000ffff0000ffff0000ff000000ff00ffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffff00ffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff0000ffff000000000000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00ffff0000ffffffffffff0000ffffffffffff0000ffffff00ffff0000ffffff000000ffff0000ffff0000ff000000ff000000ffff0000ffff0000ff000000ff00ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ff000000ff00000000000000000000ff00ff00ff00ff000000000000000000ff000000ff0000000000ff000000ff000000ff000000ff000000ff00000000000000ff00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x19828808101124f18e14b08100919614a20100d24718528b20100d2465c52c20402461480c204024630510b08100658a20100d24718e1480403491c628808141124718c21508100718a20100d5091c62880814091c63852c100d2461440c2040
|1=>0x1c62840810142471972880810111c62a420204024718a2020408891c628808102124718c29c2020401c614a20100d2477c62880810091cf18e28b0810091c674a20204024718a70204025b1c62840810116c718a2020406891c664a202040247
|2=>0x4025b1c6288081009a473c658a20204024719328808101124719229c2020404491c660a20204024718a2150810091cf18a2020405091c64ca20204024719229c20204024718a20204085124718e14b08100918c29c2020404471a7288081009
|3=>0x4024718a202040c491c628420204046f1c65ca2c20402473c614a2c808100918c2842c20401c628808103024718a10808102f1ee18a20204024718a202040449a4718a202040b091c630aac80810071852842c204024628808102a44718a102
|4=>0x1cf18e2880810091e018a20204024718a2020409891c638a20100d24718a202040e091c628b0810096c71b6288081011247dc62880810091c628b0810332471b62880810091c6d0a20204024718a202040c891c629c20204026f1cf19614a202
|5=>0x2020402471972880810091c638a2c204024718a21e0810091c630a1080810078c628b20204024719228808101124719628b2020402471922880810091c630a2020404473c614a20204024718c28b202040247e4614a20204024718a202040b49
|6=>0x24794638a20204024718528b20204024628808103524718a202040449bc718a202040a891c658a20204024718a10b0810091c65cc2880810091c6288081009bc71a82880810091fa18a20204024719214a20204024718e28808101124719230a
|7=>0x62880810091e518a202040247ec62880810091c630a20204024718a2020404491c638a2020402473c62880810091c628b20204024718a20100d
|_=>0
def sO:Nat→Nat→Nat
|8,0=>0x1e0007
|9,0=>0x7791ba464a16e453812e04380ea43190a2420805e40f8
|10,0=>0x96a651992263ea8d662c988e61a9846607a7f2df397a69e0975a9cd97125bb96ca5a8a67e596963658495ee57295a295ea54ed4a9506537a4ba524a46a91284228ff93da4ed93924db934a4c993024b792b68a4926e49292264809
|11,0=>0x37e8dd2b6b9d8a758ad3e7469cf6733acaa7219c6270eac12afaabc66e89b7e6d69b32ac2aae2aaf9a9a69caa4aa88a9fe675a9b26639
|12,0=>0x3bc9ece7aa9e867989e3e7869
|13,0=>0x3c58
|_,_=>0
def wAt:=mkWire dB 60 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x28b481d4c7ce45288491d1894a21287481d1484f0b1894a1d3c2c625287481d3894a21287481d2874c2c289481d2894a1d209481d1484f0b1894a1d2884f0b1894a1d4c0ce45288491d28944142094a1d148cf0b1894a1d4c0d221291491d2074a213c2c6252874a1d2094c2c289481d
|1=>0x105082528745231894a1d4884a452474845291491d70ac8452474a21287481d2114a252476821307ca2520588252874c21289491d226652b187632b18b481d70ac8452474845289491d3c2c625287601f18e4a212074a211894a792c9c81d708c8452474846209491d1968a2d2075627
|2=>0x2094845291891d148462528744162094a1d29188252474a11209481d1894a1d2074a25209481d94eca211874a46209491d19448162874e46288491db494a2e207441f2094a2528748252074c23289491d708c41d2094e46288491d3874a211894e45288491d2114a45247571f3084a25
|3=>0x1494a1d288491d3074a253084a25288481d2c9c81d2094a2518b481d291491d28b481d291491d289491d1894a1d289481d1884a1d28b881d288462518e4a2194ac61d3c2ca2118944172094a1d708cb252074a6d211891d1964a2d2074a12209481d29b48462474ad518b881dcc7442b
|4=>0x61d18a4a252474a21189481d3c2c625288461d287481d18b881d291891d308ca2528b481d209481d3084a25291891d307ca251854a1d
|_=>0
def oO:Nat→Nat→Nat
|8,0=>0xaa005
|9,0=>0x3a41b20c905c82a413208903c81a40b204901c80a4
|10,0=>0x6b9b50da26ce3659b20d8a6c235f9af0d726b63599ac0d5a6aa3539a90d4269e34d9a60d2a6923479a30d126863419a00cfa67a33b99d0ce266e33599a0cca66232f9970cb26563299940c9a64a3239910c8263e3
|11,0=>0x458a285122881438a1850a2841418a0850228013f89f84fa27c13d89e84f227813b89d84ea27413989c84e227013789b84da2
|12,0=>0x47863a31c18d8c686323181
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 13
def pmP:Nat→Nat
|0=>0x31ccf00031acf000318cf00011bcf000119cf0000fecb0000dccf0000dccb0000dacf0000d8cf00003dcf00003c4b000039ef000039df000039cf000038cf0000264800001e4b00001ddf00001dcf00001bff00001bcf00001acf000019ff000019ef000019df000019cf0000194f000018cf0000184b000007ff00000000
|1=>0x6201bef06001bcf050039cf04a01ddf04801ddf04203bef04201dcf042019cf022419ef020039ef01101bcf010019cf00c01bff00801bff008019df008019cf00443ecf004019cf00201bcf002019cf00181bcf00143ecf00043dff00043bff00043acf000439ff000439ef000419cf00033ecf00033ccf00033acf000326cc
|2=>0x800119cf580539cf400119cf288039df28003ccf280019ff20401ddf20043def100119cf100019cf0a2439ef080439cf080419ef06203dff06203c78062039ff
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>0x101
|9,0=>0x43c3ca0b1aa4d0e5620c05
|10,0=>0x2e1e239364d61b0ee900c7ea11268cf8dad222241286d11b582b829f6109eaf80186328c6da36326d0958adcda4
|11,0=>0x58e4b36b032a4acdc063724549669c8ca9cf153b627e64d2078dc7
|12,0=>0x6e7860a24e90
|13,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 32 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_253 12 roots_253 ops++addP pm 2 dom_251 12 roots_251 ops++addP pm 3 dom_239 11 roots_239 ops++addP pm 4 dom_175 8 roots_175 ops++addP pm 5 dom_183 8 roots_183 ops++addP pm 6 dom_247 11 roots_247 ops++addP pm 7 dom_223 11 roots_223 ops++addP pm 8 dzo_159_32 9 roots_159 ops++addP pm 9 dom_231 9 roots_231 ops++addP pm 10 dom_111 8 roots_111 ops++addP pm 11 dom_191 11 roots_191 ops++addP pm 12 dom_127 11 roots_127 ops++addP pm 13 dom_119 8 roots_119 ops++addP pm 14 dzo_251_4 10 roots_251 ops++addP pm 15 dzo_219_4 9 roots_219 ops++addP pm 16 dzo_223_32 10 roots_223 ops++addP pm 17 dom_155 8 roots_155 ops++addP pm 18 dzo_247_8 8 roots_247 ops++addP pm 19 dzo_118_8 6 roots_118 ops++addP pm 20 dom_103 6 roots_103 ops++addP pm 21 dom_63 7 roots_63 ops++addP pm 22 dzo_239_16 8 roots_239 ops++addP pm 23 dzo_111_16 7 roots_111 ops++addP pm 24 dzo_119_8 7 roots_119 ops++addP pm 25 dzo_103_8 6 roots_103 ops++addP pm 26 dzo_103_16 6 roots_103 ops++addP pm 27 dzo_231_8 7 roots_231 ops++addP pm 28 dom_95 8 roots_95 ops++addP pm 29 dzo_231_16 7 roots_231 ops++addP pm 30 dom_215 9 roots_215 ops++addP pm 31 dom_207 9 roots_207 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_159_32_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_251_4_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_219_4_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_223_32_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_247_8_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_118_8_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_239_16_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_111_16_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_119_8_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_103_8_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_103_16_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_231_8_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_231_16_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_207 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 13 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 13 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 52 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 52 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 31 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 31 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 7 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 7 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 7] }, { op := GateOp.or, inputs := [3, 4] }, { op := GateOp.or, inputs := [9, 6] }, { op := GateOp.and, inputs := [8, 10] }, { op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [12, 13] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.and, inputs := [7, 15] }, { op := GateOp.and, inputs := [3, 4] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [11, 14] }, { op := GateOp.or, inputs := [19, 16] }, { op := GateOp.or, inputs := [20, 17] }, { op := GateOp.or, inputs := [21, 18] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_51654_aux

theorem PEqualNP.Outside.L_meta_51654 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_51654_aux.main
