import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52382_aux
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
def goal_43 : Nat := 0xffaaffaaee00ee00ffaaffaaee00ee00ffaaffaaee00ee00ffaaffaaee00ee00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfffafffaaa00aa00fffafffaaa00aa00fffafffaaa00aa00fffafffaaa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xfff0fff0cc00cc00fff0fff0cc00cc00fff0fff0cc00cc00fff0fff0cc00cc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfffafffaee00ee00fffafffaee00ee00fffafffaee00ee00fffafffaee00ee00
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

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
def goal_59 : Nat := 0xffeeffaaeeeeee00ffeeffaaeeeeee00ffeeffaaeeeeee00ffeeffaaeeeeee00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafffaaaaaaa00fffafffaaaaaaa00fffafffaaaaaaa00fffafffaaaaaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefffaeeeeee00fffefffaeeeeee00fffefffaeeeeee00fffefffaeeeeee00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xeecceecceecceeccee00ee00ee00ee00eecceecceecceeccee00ee00ee00ee00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffccccffffcccceeee0000eeee0000ffffccccffffcccceeee0000eeee0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffcfcfffffcfceeee0000eeee0000fffffcfcfffffcfceeee0000eeee0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffccccffffcccccccccc00cccccc00ffffccccffffcccccccccc00cccccc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffeeccffffeecceeeeee00eeeeee00ffffeeccffffeecceeeeee00eeeeee00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffcfcfffffcfccccccc00cccccc00fffffcfcfffffcfccccccc00cccccc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffefcfffffefceeeeee00eeeeee00fffffefcfffffefceeeeee00eeeeee00
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

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfffffffffcfcfcfcf0f0f0f000000000fffffffffcfcfcfcf0f0f0f000000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfffffffffcfcfcfcfafafafa00000000fffffffffcfcfcfcfafafafa00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffaa00aa00ffaaffaaaa00aa00ffffffffaa00aa00ffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffeecceeccffaaffaaee00ee00ffffffffeecceeccffaaffaaee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfffffffff0f0f0f0fff0fff000000000fffffffff0f0f0f0fff0fff000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffffffffaf0faf0fffafffaaa00aa00fffffffffaf0faf0fffafffaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffffffffcfcfcfcfff0fff0cc00cc00fffffffffcfcfcfcfff0fff0cc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffffffffefcfefcfffafffaee00ee00fffffffffefcfefcfffafffaee00ee00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffffffcccccccc0000cccc0000ffffffffffffcccccccc0000cccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffffffcccceeeeaaaaeeee0000ffffffffffffcccceeeeaaaaeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffffff0f0fafafafaaaaa0000fffffffffffff0f0fafafafaaaaa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffffffcfcfcfcf0f0cccc0000fffffffffffffcfcfcfcf0f0cccc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffffffcfcfefefafaeeee0000fffffffffffffcfcfefefafaeeee0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffffaa00ffaaffaaaaaaaa00ffffffffffffaa00ffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffffccccffccff00cccccc00ffffffffffffccccffccff00cccccc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffffeeccffeeffaaeeeeee00ffffffffffffeeccffeeffaaeeeeee00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffffffffff0f0fff0fff000000000fffffffffffff0f0fff0fff000000000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffffaf0fffafffaaaaaaa00fffffffffffffaf0fffafffaaaaaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffffcfcfffcfff0cccccc00fffffffffffffcfcfffcfff0cccccc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffffefcfffefffaeeeeee00fffffffffffffefcfffefffaeeeeee00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

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

def dom_146 : Nat := 0x5000500000000000000000000000000050005
def goal_146 : Nat := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000eeee0000eeee0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfccccc0000cccc0000cccc0000cccc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefeeeee0000eeee0000eeee0000eeee0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffcccccccc00cccccc00cccccc00cccccc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeeeeeee00eeeeee00eeeeee00eeeeee00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffffcfffffffcfffffffcfffffffccccccc00cccccc00cccccc00cccccc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffefffffffefffffffefffffffeeeeeee00eeeeee00eeeeee00eeeeee00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaa00000000aaaaaaaa00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f000000000f0f0f0f000000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfefefefefefefefefefefefefefefefefafafafa00000000fafafafa00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffccffccffccffccffccffccffccffccff00ff00cc00cc00ff00ff00cc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeffaaffaaee00ee00ffaaffaaee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffafffafffafffafffafffafffafffafffafffaaa00aa00fffafffaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcfff0fff0cc00cc00fff0fff0cc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffefffefffefffefffefffefffefffefffafffaee00ee00fffafffaee00ee00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeeeaaaaeeee0000eeeeaaaaeeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f000000000f0f0f0f000000000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffafafffffafafffffafafffffafafafafafaaaaa0000fafafafaaaaa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcfcf0f0cccc0000fcfcf0f0cccc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffefefffffefefffffefefffffefefefefafaeeee0000fefefafaeeee0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffccffffffccffffffccffffffccffccff00cccccc00ffccff00cccccc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffeeffaaeeeeee00ffeeffaaeeeeee00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fff0fff000000000fff0fff000000000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffafffffffafffffffafffffffafffafffaaaaaaa00fffafffaaaaaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfffcfff0cccccc00fffcfff0cccccc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffefffffffefffffffefffffffefffefffaeeeeee00fffefffaeeeeee00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeecccccccccccccccc0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfafafafafafafafafafafafafafafafaf0f0f0f0f0f0f0f00000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfefefefefefefefefefefefefefefefefcfcfcfcfcfcfcfc0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffccffccffccffccffccffccffccffcccccccccccccccccccc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeeecceecceecceeccee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0f0f0f0f0f0f0f0f00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffafffafffafffafffafaf0faf0faf0faf0aa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcfcfcfcfcfcfcfcfccc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffefffefffefffefffefefcfefcfefcfefcee00ee00ee00ee00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeffffccccffffcccceeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffafafffffafafffffafafffffafafffff0f0fffff0f0aaaa0000aaaa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfccccc0000cccc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefffffefefffffefefffffcfcfffffcfceeee0000eeee0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffffffccffffffccffffccccffffcccccccccc00cccccc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffffeeccffffeecceeeeee00eeeeee00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fffff0f0fffff0f00000000000000000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffafffffffafffffffafffffffafffffaf0fffffaf0aaaaaa00aaaaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfffffcfcfffffcfccccccc00cccccc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffffffefffffffefffffefcfffffefceeeeee00eeeeee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffaaaaaaaaaaaaaaaaaaaaaaaaffffffff00000000aaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffccccccccccccccccccccccccffffffffcccccccc0000000000000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeeeeeeeeeeeeeeeeeffffffffccccccccaaaaaaaa00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffafafafafafafafafafafafafffffffff0f0f0f0fafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfcfcfcfcfcfcfcfcfffffffffcfcfcfcf0f0f0f000000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefefefefefefefefefefffffffffcfcfcfcfafafafa00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffff00ff00ff00ff00ff00ff00ffffffff00000000ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffaaffaaffaaffaaffffffffaa00aa00ffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffccffccffccffccffffffffccccccccff00ff00cc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffeeffeeffeeffeeffffffffeecceeccffaaffaaee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffff0fff0fff0fff0fff0fff0fffffffff0f0f0f0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffafffafffafffafffafffffffffaf0faf0fffafffaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcfffcfffcfffcfffcfffffffffcfcfcfcfff0fff0cc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffefffefffefffefffffffffefcfefcfffafffaee00ee00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffeeeeffffeeeeffffffffffffcccceeeeaaaaeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffff0f0fffff0f0fffff0f0fffffffffffff0f0f0f0f0f000000000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffafafffffafafffffafafffffffffffff0f0fafafafaaaaa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffcfcfffffcfcfffffffffffffcfcfcfcf0f0cccc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffefefffffefefffffffffffffcfcfefefafaeeee0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffaaffffffaaffffffffffffaa00ffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffccffffffccffffffffffffccccffccff00cccccc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffeeffffffeeffffffffffffeeccffeeffaaeeeeee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffff0fffffff0fffffff0fffffffffffff0f0fff0fff000000000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffafffffffafffffffffffffaf0fffafffaaaaaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffcfffffffcfffffffffffffcfcfffcfff0cccccc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffefffffffefffffffffffffefcfffefffaeeeeee00
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
def isoMvS_100:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_100:Lower true dom_100 roots_100 goal_100 4:=lower_iso_b isoMvS_100 (by decide +kernel) lowS_41
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_41
def isoMvS_138:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_138:Lower true dom_138 roots_138 goal_138 4:=lower_iso_b isoMvS_138 (by decide +kernel) lowS_41
def isoMvS_146:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_146:Lower true dom_146 roots_146 goal_146 4:=lower_iso_b isoMvS_146 (by decide +kernel) lowS_41
theorem lowS_43:Lower true dom_43 roots_43 goal_43 5:=lower_slice_b [(0xc0c00000c0c,8,10)] (by decide +kernel) lowS_41
namespace S_46
def pG:List (Nat×Nat):=[(2,10),(4,36),(6,14),(6,38),(8,10),(8,40),(12,14),(12,44),(32,36),(32,40),(34,38),(34,42)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_46.map (·&&&dom_46)
def gM:=goal_46&&&dom_46
def NN:Nat→Nat
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x98604
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaa0000000154000001540282800002828444400004444
|_,_=>0
def sP:Nat→Nat
|0=>0xe4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|_,_=>0
def wAt:=mkWire dB 4 47 0x7fffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_46 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_46 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_46==dom_46)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_46 gM v ys):RunD true dom_46 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_46 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_46 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_46 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_46 roots_46 goal_46 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_46
theorem lowS_46:Lower true dom_46 roots_46 goal_46 4:=S_46.noCircuit
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_slice_b [(0xa0a00000000000000000000000000000a0a,8,9)] (by decide +kernel) lowS_138
def isoMvS_45:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_45:Lower true dom_45 roots_45 goal_45 5:=lower_iso_b isoMvS_45 (by decide +kernel) lowS_43
def isoMvS_51:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=lower_iso_b isoMvS_51 (by decide +kernel) lowS_46
def isoMvS_53:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_53:Lower true dom_53 roots_53 goal_53 4:=lower_iso_b isoMvS_53 (by decide +kernel) lowS_46
def isoMvS_57:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_43
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 4:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_46
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_43
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_43
def isoMvS_99:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 4:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_46
def isoMvS_101:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 5:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_43
def isoMvS_102:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 5:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_43
def isoMvS_105:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_43
def isoMvS_108:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 5:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_43
def isoMvS_114:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_43
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_43
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 5:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_43
def isoMvS_147:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_139
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_43
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_43
def isoMvS_154:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_139
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 4:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_46
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 4:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_46
def isoMvS_169:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 5:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_139
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_43
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_43
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 4:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_46
def isoMvS_195:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 4:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_46
def isoMvS_197:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 4:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_46
def isoMvS_202:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_43
def isoMvS_204:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 4:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_46
def isoMvS_225:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 4:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_46
def isoMvS_226:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 4:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_46
def isoMvS_228:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 5:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_43
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 4:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_46
theorem lowS_47:Lower true dom_47 roots_47 goal_47 6:=lower_slice_b [(0xcccc0000cccc,8,10)] (by decide +kernel) lowS_45
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_slice_b [(0xcc00cc00cc00cc,16,18)] (by decide +kernel) lowS_53
theorem lowS_59:Lower true dom_59 roots_59 goal_59 6:=lower_slice_b [(0xc0c0c0c0c0c0c0c,8,10)] (by decide +kernel) lowS_57
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
|0,1=>0xcccc0000cccc000088880000888911100000000000011110000000000000000c8c8000000000000c8cb333000033330000330000003300cccc0000cccc0000cccc0000cc0333300003333000033330000000000cc000000cc000000cc000000000000000000000001111000000000c0c0000000000000c0c00000003333000033330000111100000000
|_,_=>0
def sP:Nat→Nat
|0=>0x144401ca2200e5113203d0a2200e5110183944405cf5288803d0a2034e51101339444048e32881139444040e5138803944069d45610072880b3a92401ca8110e62888018820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682ced9ab2f652c8d8f2986
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 26 110 0x3fffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1d29d2832d9a1329d2832bc289
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x513200000021110001
|6,0=>0x817161
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0x3ff6fb5b61230a080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x430021605
|6,0=>0x7a89
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_108 5 roots_108 ops++addP pm 1 dom_41 4 roots_41 ops++addP pm 2 dom_45 5 roots_45 ops++addP pm 3 dom_105 5 roots_105 ops++addP pm 4 dom_100 4 roots_100 ops++addP pm 5 dom_101 5 roots_101 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_109 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_100 _ g hchk
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
theorem lowS_143:Lower true dom_143 roots_143 goal_143 6:=lower_slice_b [(0xaaaa0000000000000000000000000000aaaa,8,9)] (by decide +kernel) lowS_142
theorem lowS_155:Lower true dom_155 roots_155 goal_155 6:=lower_slice_b [(0xa0a0a0a0000000000000000000000000a0a0a0a,8,9)] (by decide +kernel) lowS_154
theorem lowS_167:Lower true dom_167 roots_167 goal_167 5:=lower_slice_b [(0xaa000000aa0000000000000000000000aa000000aa,32,33)] (by decide +kernel) lowS_166
namespace S_171
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(2,10),(2,130),(3,11),(3,35),(3,131),(8,9),(8,10),(8,40),(8,136),(32,33),(32,40),(34,35),(34,42),(34,162),(128,129),(128,130),(128,136),(160,161),(160,162),(160,168)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_171.map (·&&&dom_171)
def gM:=goal_171&&&dom_171
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x57c85
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000000000000000000000000000f0f00000000f0000000f00000000000000000000000f0000000f00c0c00000c0c000000000000000000000c0c00000c0ca0a00000a0a000000000000000000000a0a00000a0af0f00000f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 172 0xfffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_170 5 roots_170 ops++addP pm 1 dom_169 5 roots_169 ops++addP pm 2 dom_43 5 roots_43 ops++addP pm 3 dom_139 5 roots_139 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_171 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_139 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_170 5 s (0,roots_170.map (·&&&dom_170)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_171 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_170 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_171==dom_171)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_171 gM v ys):RunD true dom_171 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_171 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_171 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_171 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_171 roots_171 goal_171 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_171
theorem lowS_171:Lower true dom_171 roots_171 goal_171 7:=S_171.noCircuit
theorem lowS_173:Lower true dom_173 roots_173 goal_173 6:=lower_slice_b [(0x30300000303000000000000000000000303000003030,32,36)] (by decide +kernel) lowS_169
def dzo_147_32:=0xf000f000000000000000000000000000f000f00000000
def gzo_147_32:=0xf000e000000000000000000000000000e000a00000000
def gsh_147_32:=0xf000e000000000000000000000000000e000a
theorem lowS_zo_147_32_146:Lower true dzo_147_32 roots_147 gzo_147_32 5:=lower_iso_b (d1:=dom_147) (r1:=roots_147) (T1:=gsh_147_32) [(dom_147,32)] (by decide +kernel) (lower_slice_b (T:=gsh_147_32) [(0xa000a000000000000000000000000000a000a,0,1)] (by decide +kernel) lowS_146)
namespace S_179
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,129),(2,18),(2,130),(3,19),(3,35),(3,131),(16,17),(16,18),(16,144),(32,33),(34,35),(34,50),(34,162),(48,49),(48,50),(48,176),(128,129),(128,130),(128,144),(160,161),(160,162),(160,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_179.map (·&&&dom_179)
def gM:=goal_179&&&dom_179
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xb5971
|5,0=>0x1bcc
|6,0=>0xc94e1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000f000f0000000000000000000f0000000f0000c000c000c000c0000000000000000000c000c000c000cf000f000000000000000000000000000f000f00000000f0000000f00000000000000000000000f0000000f0000a000a000a000a0000000000000000000a000a000a000a300030003000300000000000000000003000000030000f000f000f000f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8ea133a84688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 180 0xfffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_177 5 roots_177 ops++addP pm 1 dom_163 4 roots_163 ops++addP pm 2 dzo_147_32 5 roots_147 ops++addP pm 3 dom_147 5 roots_147 ops++addP pm 4 dom_146 4 roots_146 ops++addP pm 5 dom_51 4 roots_51 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_179 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_147_32_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_51 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_177 5 s (0,roots_177.map (·&&&dom_177)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_179 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_177 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff0000ffff0000ffff0000,112)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_179==dom_179)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_179 gM v ys):RunD true dom_179 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_179 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_179 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_150_32:=0x5500550000000000000000000000000055005500000000
def gzo_150_32:=0x5500540000000000000000000000000054005000000000
def gsh_150_32:=0x55005400000000000000000000000000540050
theorem lowS_zo_150_32_146:Lower true dzo_150_32 roots_150 gzo_150_32 5:=lower_iso_b (d1:=dom_150) (r1:=roots_150) (T1:=gsh_150_32) [(dom_150,32)] (by decide +kernel) (lower_slice_b (T:=gsh_150_32) [(0x50005000000000000000000000000000500050,0,4)] (by decide +kernel) lowS_146)
namespace S_182
def pG:List (Nat×Nat):=[(2,18),(2,130),(4,36),(4,132),(6,22),(6,38),(6,134),(16,18),(16,144),(20,22),(20,52),(20,148),(32,36),(34,38),(34,50),(34,162),(48,50),(48,52),(48,176),(128,130),(128,132),(128,144),(160,162),(160,164),(160,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_182.map (·&&&dom_182)
def gM:=goal_182&&&dom_182
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x88f540a16b
|5,0=>0xb381e59b9702507
|6,0=>0xd5c39
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x2a8000002a800000000000000000000000000000005500440055004400000000000000000055004400550044aa00aa00aa00aa000000000000000000aa000000aa000110011001100110000000000000000001100110011001108800880088008800000000000000000088000000880005500550000000000000000000000000055005500000000aa000000aa0000000000000000000000aa000000aa000140014001400140000000000000000001400140014001422002200220022000000000000000000220000002200005500550055005500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x432604326094832604732604325043210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 183 0x7fffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc2
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x400
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0x1f41c80
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x99
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_150 5 roots_150 ops++addP pm 1 dzo_150_32 5 roots_150 ops++addP pm 2 dom_166 4 roots_166 ops++addP pm 3 dom_180 4 roots_180 ops++addP pm 4 dom_146 4 roots_146 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_182 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_150_32_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_146 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_150 5 s (0,roots_150.map (·&&&dom_150)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_182 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_150 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_182==dom_182)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_182 gM v ys):RunD true dom_182 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_182 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_182 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_182 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_182 roots_182 goal_182 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_182
theorem lowS_182:Lower true dom_182 roots_182 goal_182 7:=S_182.noCircuit
namespace S_227
def pG:List (Nat×Nat):=[(1,33),(1,129),(2,66),(2,130),(3,35),(3,67),(3,131),(32,33),(32,96),(34,35),(34,98),(34,162),(64,66),(64,96),(65,67),(65,97),(65,193),(128,129),(128,130),(160,161),(160,162),(160,224),(192,193),(192,194),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_227.map (·&&&dom_227)
def gM:=goal_227&&&dom_227
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x10ae404941
|5,0=>0x796a367c1b58a5e
|6,0=>0x67c1b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0000000f0000000c0000000c0000000f0000000f0000000c0000000cf0000000f0000000a0000000a0000000f0000000f0000000a0000000af0000000f00000000000000000000000f0000000f0000000000000000f0000000c00000000000000000000000f0000000c00000000000000000000000000000000f0000000c00000000000000000000000f0000000cf000000000000000f000000000000000f000000000000000f00000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000ca0000000a0000000a0000000a0000000a0000000a0000000a0000000af0000000f0000000f0000000f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x32160382160321603271603215043210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x156414a6
|6,0=>0x1b5
|_,_=>0
def wAt:=mkWire dB 9 228 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0xf8820
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x21
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_226 4 roots_226 ops++addP pm 1 dom_225 4 roots_225 ops++addP pm 2 dom_163 4 roots_163 ops++addP pm 3 dom_99 4 roots_99 ops++addP pm 4 dom_195 4 roots_195 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_227 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_195 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_226 4 s (0,roots_226.map (·&&&dom_226)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_227 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_226 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xffffffffffffffff0000000000000000,64),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xcccccccccccccccccccccccccccccccc,126),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_227==dom_227)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_227 gM v ys):RunD true dom_227 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_227 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_227 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_227 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_227 roots_227 goal_227 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_227
theorem lowS_227:Lower true dom_227 roots_227 goal_227 7:=S_227.noCircuit
def isoMvS_61:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 6:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_47
def isoMvS_87:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_iso_b isoMvS_87 (by decide +kernel) lowS_47
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 6:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_59
def isoMvS_94:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 6:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_47
def isoMvS_103:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_47
def isoMvS_107:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 6:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_59
def isoMvS_110:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_59
def isoMvS_115:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 6:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_59
def isoMvS_117:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_59
def isoMvS_118:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 8:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_109
def isoMvS_121:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 6:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_59
def isoMvS_122:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 6:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_59
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 6:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_47
def isoMvS_151:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_143
def isoMvS_157:List (Nat×Nat):=[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 6:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_143
def isoMvS_158:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 6:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_143
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_59
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 6:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_59
def isoMvS_185:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 7:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_171
def isoMvS_186:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_179
def isoMvS_188:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 5:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_167
def isoMvS_199:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 5:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_167
def isoMvS_203:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 7:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_179
def isoMvS_205:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 7:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_182
def isoMvS_206:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 6:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_59
def isoMvS_213:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 6:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_59
def isoMvS_214:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 6:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_173
def isoMvS_220:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 5:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_167
def isoMvS_229:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 6:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_59
def isoMvS_230:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 6:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_59
def isoMvS_233:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 7:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_179
def isoMvS_234:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 6:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_59
def isoMvS_236:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 6:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_59
def isoMvS_244:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 6:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_59
theorem lowS_63:Lower true dom_63 roots_63 goal_63 7:=lower_slice_b [(0xcccccccccccccccc,8,10)] (by decide +kernel) lowS_61
theorem lowS_111:Lower true dom_111 roots_111 goal_111 9:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc,8,10)] (by decide +kernel) lowS_109
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,18),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,10),(8,40),(16,17),(16,18),(16,80),(24,25),(24,26),(24,56),(24,88),(32,33),(32,40),(32,96),(34,35),(34,42),(34,50),(34,98),(48,49),(48,50),(48,56),(48,112),(64,66),(64,80),(64,96),(65,67),(65,73),(65,81),(65,97),(72,73),(72,74),(72,88),(72,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|7=>3
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x62b5b1cf4b07721
|8,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c688b1a23d8d11ac688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0x398ee07
|8,0=>0x146
|_,_=>0
def wAt:=mkWire dB 8 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xb1a1
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x441
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 6
def pmP:Nat→Nat
|0=>0xfff6ff3ff01f000
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x53
|8,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 6 roots_122 ops++addP pm 1 dom_121 6 roots_121 ops++addP pm 2 dom_115 6 roots_115 ops++addP pm 3 dom_107 6 roots_107 ops++addP pm 4 dom_91 6 roots_91 ops++addP pm 5 dom_43 5 roots_43 ops++addP pm 6 dom_59 6 roots_59 ops++addP pm 7 dom_90 5 roots_90 ops++addP pm 8 dom_105 5 roots_105 ops++addP pm 9 dom_83 5 roots_83 ops++addP pm 10 dom_57 5 roots_57 ops++addP pm 11 dom_114 5 roots_114 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_114 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 6 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
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
  · exact z7 i (Nat.zero_le i) hi
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
theorem lowS_159:Lower true dom_159 roots_159 goal_159 7:=lower_slice_b [(0xaaaaaaaa000000000000000000000000aaaaaaaa,8,9)] (by decide +kernel) lowS_158
theorem lowS_175:Lower true dom_175 roots_175 goal_175 8:=lower_slice_b [(0xf0f00000f0f000000000000000000000f0f00000f0f0,32,36)] (by decide +kernel) lowS_171
def dzo_151_32:=0xff00ff00000000000000000000000000ff00ff00000000
def gzo_151_32:=0xff00fe00000000000000000000000000fe00fa00000000
def gsh_151_32:=0xff00fe00000000000000000000000000fe00fa
theorem lowS_zo_151_32_146:Lower true dzo_151_32 roots_151 gzo_151_32 6:=lower_iso_b (d1:=dom_151) (r1:=roots_151) (T1:=gsh_151_32) [(dom_151,32)] (by decide +kernel) (lower_slice_b (T:=gsh_151_32) [(0xaa00aa00000000000000000000000000aa00aa,0,1),(0xf000f000000000000000000000000000f000f0,0,4)] (by decide +kernel) lowS_146)
namespace S_183
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,129),(2,18),(2,130),(3,19),(3,35),(3,131),(4,36),(4,132),(5,21),(5,37),(5,133),(6,22),(6,38),(6,134),(7,23),(7,39),(7,135),(16,17),(16,18),(16,144),(20,21),(20,22),(20,52),(20,148),(32,33),(32,36),(34,35),(34,38),(34,50),(34,162),(48,49),(48,50),(48,52),(48,176),(128,129),(128,130),(128,132),(128,144),(160,161),(160,162),(160,164),(160,176)]
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
|4,0=>0xeef41e58bad48bb9b0bb090e7
|5,0=>0xfb964d2c2dc399bbeb2daf9b09fd878f8c27dcdb71753545fd3eb7e19ad315b0a0adf102ea6
|6,0=>0xf4680f10e9efb13e6ed6e6b41e551ce0fa4de917da542d49a5cfe32cb550ca919c4d7cbab12b6c5db58a3aab8aa886da2c3f9cd979be4a93dc57dcdb7153464b825a76257a834d263478c13c77329752252e017374107170e6620df13
|7,0=>0xbde3ebc3d3ac7aaa886da2cd0918037a75f6b2e96b0c260448
|8,0=>0x8a6fe
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff000000ff000000000000000000000000000000000000ff00cc00ff00cc000000000000000000cc00cc00cc00cc330000003300000000000000000000003300000033000033003300330033000000000000000000000000000000000000ff000000ff000000000000000000ff000000ff0000aa00aa00aa00aa000000000000000000aa00aa00aa00aa0000330000003300000000000000000033000000330000ff000000ff0000000000000000000000ff000000ff0000fe00fe00fe00fe000000000000000000fe00fa00fe00faee00ee00ee00ee000000000000000000ee00aa00ee00aaff00ff00ff00ff00000000000000000000000000000000ff00ff00000000000000000000000000ff00ff00000000ff00ff00ff00ff000000000000000000ff000000ff0000f000f000f000f0000000000000000000f000f000f000f0ff00aa00ff00aa000000000000000000aa00aa00aa00aa3300330033003300000000000000000033000000330000
|0,1=>0xff00f000ff00f0000000000000000000f000f000f000f0cc000000cc0000000000000000000000ff000000ff0000ff00ff00330033000000000000000000ff00ff000000000000000000000000000000000000000033000000330000cc00cc00cc00cc000000000000000000ff00cc00ff00cc0000ff000000ff00000000000000000000000000000000ff00ff000000ff000000000000000000ff00ff00000000ff003300ff0033000000000000000000ff000000ff000000000000000000000000000000000000ff00cc00ff00ccff00ff00ff00ff000000000000000000ff00ff0000000000000000000000000000000000000000ff00ff00000000cc00cc00cc00cc000000000000000000cc000000cc0000ff00ff00ff00ff00000000000000000033000000330000ff00cc00ff00cc000000000000000000ff00cc00ff00ccff00ff00ff00ff000000000000000000cc00cc00cc00cccc00cc00cc00cc000000000000000000cc00cc00cc00cc
|0,2=>0xff000000000000000000000000000000ff00ff000000000000cc000000cc000000000000000000cc00cc00cc00cc00000000000000000000000000000000ff000000ff00000000ff00000000000000000000000000ff00ff00000000ff00ff00ff00ff000000000000000000ff00cc00ff00ccff00ff00ff0000000000000000000000ff00ff00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x40a70511b20240a15920240a1442c240a11808a34559720240a10308a00f58808a00554808a00510320218510808a0051080861442022933044830912840cb0902840c240110308e2840c228d3042c228010b08a2440c22891081c61440c2040
|1=>0x11820240a14420240114420238a1440c809028510808a34531620240a3451032022801440c240a34510808a00588809028512120240a1445c80902858080902851080902801440c80942851087d028510809428510878240a15d20240a144202
|2=>0x2024502851080902853c420240a3451080902856a520240a14420290a15648809028510320240a3044830902851080902931444a309028511220244a1560c80902855888c240a1440c809140a10309028f54320240a15522309028512309029a
|3=>0x420240a14448809028558809028554809028510320240a144223090285108090285304
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a94c8c5e62c3149898c4662030ed46ac2f614b09143ea196
|6,0=>0x15f6acb549e96f4479ebcd9e5ef28790bc69e28d0d7833c019f2ef3676b399dbeed8768bb29d88cbe65bbac1d54ca374e3a59920c89741b1f1ceae6f6
|7,0=>0x344f9c6cb363df10f817bd3dcded8f657
|8,0=>0x1a96
|_,_=>0
def wAt:=mkWire dB 38 184 0xffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x8411054417205481740590152050843205846b205903f20504152054815205c81520508152054816205ca3d205103d205041520548150d0c81510fc81410f481408f48140d0081520cc4314058469205833f205081550a4340205481528f4814205503d2050815
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xa300000000000000000073000610003300c00
|6,0=>0x2f2b4ac1ac6a100291000000028198a5100232002127c800001e1745c168982000005880000142489113c800000d2
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xf6fd9eefb9e6e4c906218821080a007ed99625811404b1083b0a8120400e00c0200400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xc000000201c0611060
|6,0=>0xca1a46014518195385416aa4052ac2c00180155127000d
|7,0=>0x1f7c6b58cedfb
|8,0=>0xe
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_182 7 roots_182 ops++addP pm 1 dom_53 4 roots_53 ops++addP pm 2 dom_166 4 roots_166 ops++addP pm 3 dom_179 7 roots_179 ops++addP pm 4 dom_181 6 roots_181 ops++addP pm 5 dom_149 5 roots_149 ops++addP pm 6 dom_167 5 roots_167 ops++addP pm 7 dzo_151_32 6 roots_151 ops++addP pm 8 dom_151 6 roots_151 ops++addP pm 9 dom_55 5 roots_55 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_183 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_151_32_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_55 _ g hchk
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
def dzo_155_32:=0xf0f0f0f0000000000000000000000000f0f0f0f00000000
def gzo_155_32:=0xf0f0f0e0000000000000000000000000f0e0f0a00000000
def gsh_155_32:=0xf0f0f0e0000000000000000000000000f0e0f0a
theorem lowS_zo_155_32_146:Lower true dzo_155_32 roots_155 gzo_155_32 6:=lower_iso_b (d1:=dom_155) (r1:=roots_155) (T1:=gsh_155_32) [(dom_155,32)] (by decide +kernel) (lower_slice_b (T:=gsh_155_32) [(0xa0a0a0a0000000000000000000000000a0a0a0a,0,1),(0xf000f000000000000000000000000000f000f00,0,8)] (by decide +kernel) lowS_146)
namespace S_187
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,10),(2,18),(2,130),(3,11),(3,19),(3,35),(3,131),(8,9),(8,10),(8,40),(8,136),(16,17),(16,18),(16,144),(24,25),(24,26),(24,56),(24,152),(32,33),(32,40),(34,35),(34,42),(34,50),(34,162),(48,49),(48,50),(48,56),(48,176),(128,129),(128,130),(128,136),(128,144),(160,161),(160,162),(160,168),(160,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_187.map (·&&&dom_187)
def gM:=goal_187&&&dom_187
def NN:Nat→Nat
|7=>2
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xd5862ab001
|8,0=>0x3dbb0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000f0f0f0f0000000000000000000000000f0f0f0f0000000000000000000000000000000000000000f0f0f0f00000000f0f00000f0f000000000000000000000f0f00000f0f0000f000f000f000f0000000000000000000f000f000f000f00c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x34688f1a22c688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xcc06
|8,0=>0xc6
|_,_=>0
def wAt:=mkWire dB 8 188 0xfffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc1c3
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x441
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 6
def pmP:Nat→Nat
|0=>0xfefd780
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>6
|8,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_186 7 roots_186 ops++addP pm 1 dom_185 7 roots_185 ops++addP pm 2 dom_179 7 roots_179 ops++addP pm 3 dom_171 7 roots_171 ops++addP pm 4 dom_59 6 roots_59 ops++addP pm 5 dom_155 6 roots_155 ops++addP pm 6 dzo_155_32 6 roots_155 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_187 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_155_32_146 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_186 7 s (0,roots_186.map (·&&&dom_186)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_187 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_186 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_187==dom_187)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_187 gM v ys):RunD true dom_187 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_187 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_187 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_187 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_187 roots_187 goal_187 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_187
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=S_187.noCircuit
namespace S_231
def pG:List (Nat×Nat):=[(1,33),(1,129),(2,66),(2,130),(3,35),(3,67),(3,131),(4,36),(4,68),(4,132),(5,37),(5,69),(5,133),(6,38),(6,70),(6,134),(7,39),(7,71),(7,135),(32,33),(32,36),(32,96),(34,35),(34,38),(34,98),(34,162),(64,66),(64,68),(64,96),(65,67),(65,69),(65,97),(65,193),(128,129),(128,130),(128,132),(160,161),(160,162),(160,164),(160,224),(192,193),(192,194),(192,196),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_231.map (·&&&dom_231)
def gM:=goal_231&&&dom_231
def NN:Nat→Nat
|4=>5
|5=>16
|6=>36
|7=>9
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xf6415baf0b8c74e637f141612
|5,0=>0xd944cd3486b6f31a754e88774821a6733a56c0705f81758d8045c3a3905b24c9c1dc140e60108208
|6,0=>0xe576fda142d9c79d7569d5472cf4accd1f4b806ba919da50bea03b89ea379c02e95a4a90dbe75ada707566b0f866dd0669a0621f7615fb60e365518e45c3a4494535fa82667211bf1102940ae4c06c0104e9c040ab0378900c99
|7,0=>0xe576fbf021a938ba13cc9360b8cb884096b34ab90513c
|8,0=>0x9aff0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff000000000000000000000000000000ff00000000000000000000000000000000ff000000ff0000000000000000000000ff000000ff00000000ff00000000000000ff00000000000000ff00000000000000ff00000000aa000000aa000000aa000000aa000000aa000000ff000000aa000000aaff000000ff0000000000000000000000ff000000ff0000000000000000ff000000aa000000aa000000aa000000ff000000aa000000aa000000aaff000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000000000000000000000000000ff000000ff000000ff00000000ff000000ff000000ff000000ff000000ff00000000000000ff00000000ff000000f0000000f0000000f0000000ff000000f0000000f0000000f0ff000000ff000000ff000000ff000000ff000000ff000000000000000000000000ff000000ff000000ff00000000000000ff000000ff00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0cc000000cc000000cc000000cc000000cc000000cc000000cc000000ccaa000000aa000000aa000000aa000000aa000000aa000000aa000000aaff000000ff000000ff000000ff00000000000000000000000000000000
|0,1=>0xff00000000000000ff00000000ff000000ff0000000000000000000000ff000000ff000000ff000000005500000055000000000000000000000055000000550000000000000000aa00000000000000ff00000000000000aa00000000000000ff0000000033000000330000003300000033000000330000003300000000000000003300000000000000330000000000000033000000000000003300000000ff000000ff000000ff000000ff000000330000000000000033000000000000000000000000ff000000000000000000000000000000ff0000000000000000ff00000000000000ff00000000000000ff00000000000000000f0000000f0000000f0000000f0000000f0000000f0000000f00000000ff000000cc000000cc000000cc000000ff000000cc000000cc000000ccff000000ff000000ff000000ff000000ff0000000000000000000000003300000033000000330000003300000000000000330000000000000000ff000000ff0000000000000000000000ff0000000000000000000000005500000055000000550000005500000055000000550000005500000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000
|0,2=>0xff000000ff000000aa000000aa000000ff000000ff000000aa000000aa000000003300000000000000000000000000000033000000000000000000000000ff000000000000000000000000000000ff0000000000000000aa000000aa000000ff000000aa000000aa000000aa000000ff000000aa00000000aa000000aa000000aa00000000000000aa000000aa000000aaff000000ff0000003300000000000000ff000000ff0000003300000000000000000000000000000000000000000000000000000000ff000000000000000000000000ff000000aa0000000000000000000000ff000000aaff00000000000000ff000000000000000000000000000000ff000000000000000000000000ff000000ff0000000000000000000000ff000000005500000055000000550000000000000055000000550000005500000000ff000000ff000000ff000000ff00000000000000ff0000000000000000cc000000cc000000cc000000cc000000ff000000cc000000ff000000ccff00000000000000ff00000000000000ff000000000000000000000000ff000000cc000000ff000000cc000000ff000000cc000000ff000000ccff000000ff000000cc000000cc000000ff000000ff000000cc000000cc
|0,3=>0xff000000ff00000000000000003300000033000000000000000000000033000000330000000000000000ff000000ff000000ff000000cc000000ff000000ff000000ff000000cc00000000ff000000ff000000ff00000000000000000000000000000000ff000000ff0000005500000000000000ff000000ff0000005500000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2db00d0c20592c718204b0101820402430813c06030815c02030813c03420562c01c35412c01c308a2c01c308114f40e0c20403430812d434304b4c03430811523430912c038308100d0c230b0070c22852460810081820401c60811440c2040
|1=>0x452ec3430812c03430ab2c0343081a8b00d0c204b5003690c204b0283430812c03670c204b00d9830812c03430812d43460812c034308194b00d0c204b90034304b6c08cd0c12c03430812e20213438012c078d0c204b00d7030812c0343045
|2=>0x2c03430812cf00d6030812c034380204b0103430812c0603081b40c8d0c204b00d0c228b0070c204b3c04030813c024d0c204b00d0c204bc4d0c20702c040d0c2bc10100c205a2c020d0c204b01f0c204bb403430812ee0070c204bb401cd0c2
|3=>0x3430812c040d0c204b00d0c204b7403430812f400d0c2bc12c03430812f300d0c2045
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x38b1b14ccc6062d315189cc4862130f186cc30615309183ea196
|6,0=>0xb13d71aaaf4f6a43d09a76f356973c9de40f197893c2de08efd77b3bc19d2ee276dbb51d9aec676032e9966eac7533281932e92745ba11cfae776
|7,0=>0x1a17cd3e4df18f857bf3dddee0f697
|8,0=>0x1a86
|_,_=>0
def wAt:=mkWire dB 53 232 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x34b412e2c0c12d08b8b0134b0b3608b4d2e2cd813d34b0b3434b4d2c3454b013c08d2c34b4b3704fcd2c345cb1e3c04d2c34b82162c0427d340cb7d35dc2162c05a0108d903f34b4d2c
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xc00
|6,0=>0x1f2001d2705a260962001510000000000504000012200000444000010138800000d12c892000002047114832
|7,0=>0x291a0671986519063188611
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xed9dc9d5dcd967d5d947d479440208181180100060041040036031021020018006004001000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xc00000000000000020
|6,0=>0x29c07499ca03c000012d00400600090a00c0840259201
|7,0=>0x11acf169d256
|8,0=>0x17
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_227 7 roots_227 ops++addP pm 1 dom_195 4 roots_195 ops++addP pm 2 dom_197 4 roots_197 ops++addP pm 3 dom_230 6 roots_230 ops++addP pm 4 dom_167 5 roots_167 ops++addP pm 5 dom_199 5 roots_199 ops++addP pm 6 dom_103 6 roots_103 ops++addP pm 7 dom_102 5 roots_102 ops++addP pm 8 dom_101 5 roots_101 ops++addP pm 9 dom_166 4 roots_166 ops++addP pm 10 dom_229 6 roots_229 ops++addP pm 11 dom_228 5 roots_228 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_231 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_228 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_227 7 s (0,roots_227.map (·&&&dom_227)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_231 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_227 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_231==dom_231)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_231 gM v ys):RunD true dom_231 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_231 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
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
def dzo_137_64:=0x303000000000000000000000000000003030000000000000000
def gzo_137_64:=0x302000000000000000000000000000002000000000000000000
def gsh_137_64:=0x30200000000000000000000000000000200
theorem lowS_zo_137_64_137:Lower true dzo_137_64 roots_137 gzo_137_64 4:=lower_iso_b (d1:=dom_137) (r1:=roots_137) (T1:=gsh_137_64) [(dom_137,64)] (by decide +kernel) (lower_slice_b (T:=gsh_137_64) [] (by decide +kernel) lowS_137)
def dzo_171_64:=0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000
def gzo_171_64:=0xf0f00000f0e000000000000000000000f0f00000e0c0000000000000000
def gsh_171_64:=0xf0f00000f0e000000000000000000000f0f00000e0c
theorem lowS_zo_171_64_137:Lower true dzo_171_64 roots_171 gzo_171_64 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_64) [(dom_171,64)] (by decide +kernel) (lower_slice_b (T:=gsh_171_64) [(0xc0c00000c0c000000000000000000000c0c00000c0c,0,2),(0xf0f00000000000000000000000000000f0f00000000,0,32)] (by decide +kernel) lowS_137)
def dzo_139_64:=0xf0f00000000000000000000000000000f0f0000000000000000
def gzo_139_64:=0xf0e00000000000000000000000000000e0c0000000000000000
def gsh_139_64:=0xf0e00000000000000000000000000000e0c
theorem lowS_zo_139_64_137:Lower true dzo_139_64 roots_139 gzo_139_64 5:=lower_iso_b (d1:=dom_139) (r1:=roots_139) (T1:=gsh_139_64) [(dom_139,64)] (by decide +kernel) (lower_slice_b (T:=gsh_139_64) [(0xc0c00000000000000000000000000000c0c,0,2)] (by decide +kernel) lowS_137)
def dzo_169_64:=0x30300000303000000000000000000000303000003030000000000000000
def gzo_169_64:=0x30300000302000000000000000000000303000002000000000000000000
def gsh_169_64:=0x3030000030200000000000000000000030300000200
theorem lowS_zo_169_64_137:Lower true dzo_169_64 roots_169 gzo_169_64 5:=lower_iso_b (d1:=dom_169) (r1:=roots_169) (T1:=gsh_169_64) [(dom_169,64)] (by decide +kernel) (lower_slice_b (T:=gsh_169_64) [(0x3030000000000000000000000000000030300000000,0,32)] (by decide +kernel) lowS_137)
namespace S_235
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(2,10),(2,66),(2,130),(3,11),(3,35),(3,67),(3,131),(8,9),(8,10),(8,40),(8,136),(32,33),(32,40),(32,96),(34,35),(34,42),(34,98),(34,162),(64,66),(64,96),(65,67),(65,73),(65,97),(65,193),(72,73),(72,74),(72,104),(72,200),(128,129),(128,130),(128,136),(160,161),(160,162),(160,168),(160,224),(192,193),(192,194),(192,200),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_235.map (·&&&dom_235)
def gM:=goal_235&&&dom_235
def NN:Nat→Nat
|4=>11
|5=>96
|6=>286
|7=>130
|8=>18
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xee1a8c67c27a3ab50ca340c0c369522bd261b95315cfd022c601940
|5,0=>0xfa394f5d37f28e5f03f9dbd24d93b7d90eecd626cd39accb75cb156c5382c1bd6bd162b1164accf2abd85a75daa5b8ca48f0a31c69ef6a9eaeb9910392f938fa738f17285cb5840118376c826cc7ee177a6497a6417445171e9b6f5286f2666e5046dc276baf36884165ac96049d5f4415e5795cc065a0a75944058e1b5855558147564405294c51fb451f0b4bd1a4ae9d4a7a3491cd481a641de0406fc3dded3d08a3ac1c37f8837dc53709034ccc32175316d830bd730af32fc812fb8a2cd63295db2954f25cf9211a7209571e4831ad2b18a5f15f3f1228b11bbd112860c4160b4d709659079c1054080464e044ce
|6,0=>0x4cdee4c4d44b6654b0e4498274959a494c747c4b47567474c6463cf44cd2424bb4183d412513ec1d3e2713e11b3e0833daa83d52e3d4a93d2813ca2c3c5433b5ef39c31384593822637d96378f736683363b9358dd34dbe34a70341b833cd232792324ea3202e31bde3168e315d930908307772fec22f84e2d1052c1e52c1aa2c13d2bed92be222b7f32ab6d2a0b929c4128dd42703c25ef525e7825cd22587a2541f241cc23837236a6233f32301222e8321c2b215d32142d1ff5c1fe211f2191dae91ce821c7131c61b1c59e1bf3e1bb891b8b11b3d41a588190201850f166cb14524141b012e4812aee12ade1268d1228b11f2310d7110c0a0dc640cfbf0cf2e0cdea0cc0f0c8870c7bb0bac00b7790b0680a32f09848090bf082ac079c106ffc05a460591803c3b039f3034a20339602625022a4020a901e0800d550044f
|6,1=>0xb91a2b6ad9b6916b631fb623fb5f30b5c5bb1ea2b0d09ad9b8acfbdabb26ab1eeaafbba5223a4574a01179f7669eaeb9ea3d9e2fb9dbe29d4669d19c9bc959bb939b9de9a37e9a32b9833797e419785e9709296349931429301692f9391cd491a25905b78f1458ea3b8dba689a0488d9e881bf86fbe8522184c29831898228e80b4c8081c8080f7eaac7e1bf7c9a87833276ccd7695e7692175791755627448b73cf873a1a732e67305e7232171f607196f718e570734705c96f7116f3f56ede46e40f6d5926d5166c1c76b98a6a7c36a0a869e7c695ce6936668c856816b67bca679d467842669d665dc465b79655ce637056356062f3062c3161b1d60ecb60b2f5f47e5bc1d5aa7e592845926b5843c58409583e15644054d28548e9547755411353f045306a52bb45175f50ef9502bc4fee84f5e04f1a14e3064de534dc61
|6,2=>0xf9b0cf77b5f6423f3852f36c3f03f9ed446ec12febc14ea590e98b7e7f69e081cdd90bdab0fd7db5d65ffd3fd3c9ba8c5dc4c498bc2f9ebe1fbbdd91bc6eebbf9cbb4cdbb270ba907b9271
|7,0=>0xfd804f169de56d6cff88ccf02c518ec2c9cc228dc1d05bd9cfb98f8b1465ab8aba5223a0f719f8869ba529aef59785e95b0295662938588f0478dd948c8638b5f08a9b48a5c689c37898a687362866c7861607e6d27d17f7cbd97bf177b6427a24e78a59776057619575bec73e1c712886f9f66d20b6cb116b71b6a1cd69dc865a1c651c964a5863b596252d6051c5d5145c4005aa7e57c655680855fa75373352f8b523d0519565161b5041b503834aa8e489d04730946bcb4632544e4c424ee40cff3d6683b72a3891e3845937e053745c365fa358353400f338ee2ff862fb992eb3e2c79c2c26229cc029bab27a6d27a592555f22cc6219ac20f5c1be4b1bb651b6d11adba19fe519a5619020168de1439c136831342612e871150d0fb540e79c0e71a0e1e10d47d0ca6c0a9d70a420095be09007082ac03e3803467031d2
|7,1=>0xff74afd8a5
|8,0=>0xfffdaeb905bf13bb98f8b5646b3f5b9bef088bd084e95727135d9894bb3143ee62ff101dc930937e040d9019d0
|9,0=>0xfffda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x50500000505000005050000050500000a0a00000a0a00000a0a00000a0a00f0000000f0000000f0000000f0000000a0000000a0000000a0000000af0f00000c0c00000f0f00000c0c00000f0f00000c0c00000f0f00000c0ce0e00000e0000000e0e00000e0000000e0e00000e0000000e0e00000e00f0f00000f0f00000f0a00000f0a00000f0f00000f0f00000f0000000f00f0c00000f0c00000f0c00000f0c00000f0c00000f0c00000f0c00000f0ce0e00000e0e00000e0e00000e0e00000e0000000e0000000e0000000e00f0f00000e0e00000f0f00000e0e00000f0f00000e0000000f0f00000e00f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0af0f00000f0f000000000000000000000f0f00000f0f0000000000000000f0f00000f0f00000f0f00000f0f00000000000000000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0f00000f0f00000f0000000f0000000f0f00000f0f00000f0000000f00c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0cf0f00000f0f00000f0f00000f0f00000a0a00000a0a00000a0a00000a0a0050000000500000005000000050000000a0000000a0000000a0000000a
|0,1=>0xf0500000f0500000f0500000f0500000f0a00000f0a00000f0a00000f0a00000000a0a0000000000000a0a0000000000000a0a0000000000000a0af0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00f0f00000f0f00000f0f00000f0f0000000000000a0a0000000000000a0aa0a00000a0a00000a0a00000a0a00000a0a00000a0000000a0a00000a0000000000f0f0000000000000f0f0000000000000f000000000000000f0000000000000000000000000000000000a0a00000a0a00000a0a00000a0a50500000505000005050000050500000000000000000000000000000000f0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f00e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0ef0000000f0000000f0000000f0000000f0000000f0000000f0000000f00e0e00000e0e00000e0e00000e0e00000e0e0000000000000e0e00000000f0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0af0f00000f0000000f0f00000f0000000a0a00000a0000000a0a00000a00f0f00000f0f00000f0f00000f0f00000c0c00000c0c00000c0c00000c0c
|0,2=>0xf0f00000f0f00000f0f00000f0f00000202000002020000020200000202f0000000f0000000f0000000f0000000f0500000f0500000f0000000f003030000030300000303000003030000020200000202000002020000020200000000f0f00000000000000000000000000000f0f0000000000000f0a5050000050500000505000005050000000a0000000a0000000a0000000aa0a0000020200000a0a0000020200000a0a0000020000000a0a00000200c0c00000c0000000c0c00000c0000000f0f00000f0000000f0f00000f0050400000504000005040000050400000504000005040000050400000504f0f00000f0f00000f0f00000f0f00000e0e00000e0e00000e0e00000e0e00000000000000000000000000000000e0e00000e0e00000e0e00000e0e50500000505000005050000050500000505000000000000050500000000e0e00000e0e00000e0e00000e0e00000e0c00000e0c00000e0c00000e0cf0e00000f0e00000f0e00000f0e00000f0e00000f0e00000f0e00000f0ef0f00000e0e00000f0f00000e0e00000f0f00000e0e00000f0f00000e0ef0c00000f0c00000f0c00000f0c00000f0c0000000000000f0c00000000a0a00000a0a00000a0a00000a0a00000000000000000000000000000000
|0,3=>0x50500000505000005050000050500000505000005000000050500000500f0f00000a0a00000f0f00000a0a00000f0f00000a0a00000f0f00000a0af0a00000f0a00000f0a00000f0a00000f0a0000000000000f0a00000000f0f00000f0f00000f0f00000f0f00000a0800000a0800000a0800000a08f0f00000f0f00000f0f00000f0f00000f0a00000f0a00000f0a00000f0af0a00000f0a00000f0a00000f0a00000f0000000f0000000f0000000f00c0c00000c0c00000c0c00000c0c00000e0e00000e0e00000e0e00000e0e00f0000000f0000000f0000000f0000000f0000000e0000000f0000000ef0f00000f0f00000a0a00000a0f00000f0f00000f0f0000000000000000f0f0000000f00000f0f0000000f00000f0f0000000a00000f0f0000000af0f00000f0f000000000000000000000f0f00000f0f000003020000030200000000000000000000000000000000f0c00000f0e00000f0c00000f0ef0000000f0000000f0000000f0000000f0000000e0000000f0000000e00f0f00000f0f00000f0f00000f0f00000f0f00000a0a00000f0f00000a0a00000000f0f0000000000000f0f0000000000000000000000000000000000a0000000f0000000a0000000f0000000a0000000a0000000a0000000a
|0,4=>0xe0e00000e0e00000e0e00000e0e00000c0c00000c0c00000c0e00000c0ef0f00000f0f00000f0200000f0200000f0f00000f0f00000f0200000f0250500000505000005050000050500000f0a00000f0a00000f0a00000f0a50500000500000005050000050000000505000005000000050500000500c0e00000c0e00000c0e00000c0e00000c0e00000c0e00000c0e00000c0e00f0000000f0000000f0000000f0000000e0000000e0000000e0000000ef0f00000f0a00000f0f00000f0a00000000000000000000000000000000f0200000f0200000f0200000f0200000f0200000f0200000f0200000f02f0f00000f0f00000f0000000f0000000f0f00000f0f00000f0200000f0200000000000000000000000000000000c0c00000f0e00000c0c00000f0ef0f00000f0f000000000000000500000f0f00000f0f0000000000000000f0a00000f0a00000f0a00000f0a00000f0000000f0000000f0a00000f0aa0a00000a0200000a0a00000a0200000a0a00000a0000000a0a00000a0000300000003000000030000000300000002000000020000000200000002f0f00000a0a00000f0000000a0000000f0f00000f0f00000f0000000f00a0a00000a0a00000a0a00000a0a00000a0a00000a0800000a0a00000a08
|0,5=>0xc0c00000c0c00000e0e00000e0e00000c0c00000c0c00000e0e00000e0e0000000000e000000000000000e000000000000000e000000000000000ea0a00000f0f00000a0a00000f0f00000a0a00000f0a00000a0a00000f0af0f00000f0f00000f0f00000f0f00000002000000020000000200000002f0f00000f0500000f0f00000f0500000f0f00000f0000000f0f00000f0000000000000000000000000000000000f0e00000f0e00000f0e00000f0ef0f00000f0f00000e0e00000e0e00000f0f00000f0f00000e0000000e000040000000400000004000000040000000400000c0c0000000400000c0c30300000b0b0000030300000b0b0000000000000a0a0000000000000a0af0f00000f0f00000f0f00000f0f000005050000050000000505000005005050000050500000505000005050000050500000504000005050000050430300000303000003030000030300000303000003030000030200000302f0f00000a0a00000f0f00000a0a00000f0f00000a0000000f0f00000a0000000000000000000000000000000000f0c00000f0c00000f0c00000f0c00b0000000b0000000b0000000b0000000a0000000a0000000a0000000af0d00000f0d00000f0000000f0000000f0d00000f0d00000f0000000f00
|0,6=>0xb0b00000b0b00000b0b00000b0b00000a0a00000a0a00000a0a00000a0a00a0000000a0000000a0000000a0000000a0000000a0000000a0000000a0000000000000000000000000000000050400000504000005040000050400000000e0e0000000000000e0e0000000000000e0e0000000000000e0e0000000000000000f0f00000f0f00000000000000000000000000000000f0000000f0000000f0f00000f0f00000f0000000f0000000f0000000f00a0f00000a0f00000a0f00000a0f00000a0a00000a0a00000a0a00000a0af0f00000f0f00000f0f00000f0f00000f0f00000f0000000f0f00000f00e0e00000e0e00000e0e00000e0e00000c0c00000c0c00000c0c00000c0c30300000303000003030000030300000302000003020000030200000302f0f00000f0f00000a0a00000a0a00000f0f00000f0f0000000000000000f0b00000f0b00000f0b00000f0b00000f0a00000f0a00000f0a00000f0a000000000000000000a0000000a00000a0a00000a0a00000a0a00000a0a00000000000000000000000000000000f0a00000f0a00000f0a00000f0a303000003030000030300000303000000000000020200000000000002020000000000000000a0a00000a0a000000000000000000000a0a00000a0a
|0,7=>0x80800000808000008080000080800000a0a00000a0a00000a0a00000a0a30200000302000003020000030200000302000003020000030200000302f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f0030300000303000003030000030300000303000003030000030000000300a0a00000f0f00000a0a00000f0f00000a0a00000a0a00000a0a00000a0a2020000020200000202000002020000020200000202000002020000020250500000505000005050000050500000505000005050000050000000500d0d00000d0d00000d0d00000d0d00000d0d00000c0c00000d0d00000c0cf0f00000f0f00000f0f00000f0f00000f0f00000c0c00000f0f00000c0cf0f00000f0f00000f0f00000f0f00000f0f00000f0c00000f0f00000f0c101000001010000010100000101000001000000010000000100000001000000000000f000000000000000f00000000000000000000000000000000f0c00000f0c00000f0c00000f0c00000504000005040000050400000504a0a00000a0a00000a0a00000a0a00000a0000000a0000000a0000000a001010000010000000101000001000000010100000100000001010000010000a0000000a0000000f0000000f0000000a0000000a0000000a0000000a
|0,8=>0xb0b00000b0a00000b0b00000b0a00000b0b00000b0a00000b0b00000b0a00000000f0e0000000000000f0e0000000000000f0e0000000000000f0e30300000303000003030000030300000000000000000000000000000000f0f00000f0f000000000000050500000f0f00000f0f0000000000000000d0d00000d0d00000d0d00000d0d00000d0c00000d0c00000d0c00000d0ca0a00000a0a00000a0000000a0000000f0f00000f0f00000f0000000f00a0a00000a0a00000a0a00000a0a00000f0f00000f0f00000f0a00000f0af0300000f0300000f0300000f0300000f0300000f0000000f0300000f00f0000000f0a00000f0000000f0a00000f0000000f0a00000f0000000f0af0f00000f0f00000f0f00000f0f00000c0e00000c0e00000c0e00000c0e00000000f0f0000000000000f0f0000000000000e0e0000000000000e0ef0f00000f0f00000f0000000f0f00000f0f00000f0f00000f0000000f00a0800000a0800000a0800000a0800000a0800000a0800000a0800000a08f0f00000f0f0000000000000f0f00000f0f00000f0f0000000000000f000000000000000000f0f00000c0c000000000000000000000f0f00000c0cf0000000f0f00000f0000000f0f00000f0000000f0000000f0000000f00
|0,9=>0xf0300000f0300000f0300000f0300000f0200000f0200000f0200000f020000000030200000000000003020000000000000302000000000000030200200000002000000020000000200000002000000020000000200000002f0d00000f0d000000000000000000000f0d00000f0d0000000000000000f0f00000f0f000000000000000000000f0f00000f0f00000f0a00000f0a40400000404000004040000040400000c0c00000c0c00000c0c00000c0c00000000000000000000000000000000302000003020000030200000302f0f00000f0f00000f0000000f0000000a0a00000a0a00000a0000000a00f0f0000030300000f0f0000030300000f0f0000000000000f0f00000000c0c00000c0c00000c0c00000c0c00000c0e00000c0e00000c0e00000c0e00000000000000000000000000000000f0f00000f0c00000f0f00000f0cf0f0000050500000f0f0000050500000f000000050000000f0000000500f0000000f0500000f0000000f0500000f0000000f0000000f0000000f00f0500000f0500000f0500000f0500000f0000000f0000000f0000000f00f0f00000f0f0000000000000f0f00000f0f00000f0f000000000000000030300000300000003030000030000000303000003000000030300000300
|0,10=>0xf0f00000f0f00000f0f00000f0f00000f0f00000e0e00000f0f00000e0ec0c00000f0e00000c0c00000f0e00000c0c00000f0e00000c0c00000f0ef0f0000000000000f0f0000000000000f0f00000f0c00000f0f00000f0c0000000000000000000000000000000000a0000000a0000000a0000000a00000000000000000000000000000000505000005050000050000000500f0f00000f0f00000f0f00000f0f00000303000003000000030300000300f0f00000f0c00000f0f00000f0c00000f0f00000f0c00000f0f00000f0c00000000000000000000000000000000f0f00000e0e00000f0f00000e0ef0f0000000500000f0f0000000500000000000000000000000000000000f0a0000000000000f0a0000000000000f0a00000f0a00000f0a00000f0af0f0000050400000f0f0000050400000f0f0000050400000f0f00000504f0f00000f00000000000000000000000f0f00000f0f0000000000000000f0f0000000f00000f0f0000000f00000f0f0000000000000f0f00000000a0a00000a0a00000f0f00000f0f00000a0a00000a0a00000f0a00000f0aa0a00000a0a00000f0f00000f0f00000a0a00000a0a00000a0a00000a0af0a00000f0a00000f0f00000f0f00000f0a00000f0a00000f0a00000f0a
|0,11=>0xa0a00000a0a00000a0000000a0000000a0a00000a0a00000a0000000a00f0f00000f0f00000f0f00000f0f00000a0a00000a0a00000a0000000a00f0f00000f0f00000f0f00000f0f000000000000000000000a0a00000a0a0000000050500000000000005050000000000000000000000000000000000500000005000000050000000500000000000000000000000000000000f0f00000f0f00000f0f00000f0f0000000a0000000a0000000a0000000af0f00000f0f000000000000000f00000f0f00000f0f000000000000000000000000f0f0000000000000f0f0000000000000a0a0000000000000a0a00000000000000000000000000000000202000002020000020200000202f0e00000f0e00000f0e00000f0e00000000000000000000000000000000f0f00000f0a00000f0f00000f0a00000f0f00000f0a00000f0f00000f0a30b0000030b0000030b0000030b0000000a0000000a0000000a0000000af0f00000f0f00000f0f00000f0f0000000000000f0a0000000000000f0af0f00000b0b00000f0f00000b0b00000f0f00000a0a00000f0f00000a0af0f00000f0a00000f0f00000f0a00000f0f0000000000000f0f00000000f0a00000f0a000000000000000000000f0a00000f0a00000f0a00000f0a
|0,12=>0xf0f0000050500000f0f0000050500000f0f0000000000000f0f00000000c0f00000c0f00000c0f00000c0f00000c0e00000c0e00000c0e00000c0e00000000a0f0000000000000a0f0000000000000a0a0000000000000a0af0c0000050400000f0c0000050400000f0c0000050400000f0c0000050430300000303000003030000030300000303000000000000030300000000f0f00000c0c000000000000000000000f0f00000c0c0000000000000000f0f00000f0c00000f0000000f0000000f0f00000f0c00000f0000000f00f0e00000f0e00000f0e00000f0e00000c0c00000c0c00000c0c00000c0cf0f0000050500000f0f0000050500000f0f0000050000000f0f0000050000000000000000000000000000000000303000003000000030300000300d0d00000d0d00000d0000000d0000000d0d00000d0d00000d0000000d00f0f00000f0f0000000f0000000f00000f0f00000f0f0000000a0000000af0f00000f0f00000f0f00000f0f0000000e0000000e0000000e0000000ef0f00000000000000000000000000000f0f0000000f0000000000000000f0a00000f0a00000f0a00000f0a0000000000000000000000000000000000400000004000000040000000400000c0c00000c0c00000c0c00000c0c
|0,13=>0xf0c00000f0c00000f0c00000f0c00000a0800000a0800000a0800000a08f0800000f0800000f0800000f0800000f0a00000f0a00000f0a00000f0af0500000f0500000f0500000f0500000f0500000f0000000f0500000f00b0b00000b0b00000b0b00000b0b00000b0b00000a0a00000b0b00000a0af0f00000f0f00000a0a00000a0a00000f0f00000f0f00000a0000000a003030000030200000303000003020000030300000302000003030000030200f0000000f0000000f0000000f0000000f0000000c0000000f0000000c0000000000000000f0f00000f0f000000000000000000000f0a00000f0aa0a00000a0a00000a0a00000a0a0000000200000002000000020000000210100000101000001010000010100000101000000000000010100000000f0f00000f0300000f0f00000f0300000f0f00000f0000000f0f00000f00f0f00000f0f00000f0f00000f0f0000050400000504000005040000050450500000505000000000000000000000f0f00000f0f0000000000000000f0500000f0500000f0000000f0000000f0f00000f0f00000f0000000f00f0f00000f0f00000a0a00000a0a00000f0f00000f0f00000a0a00000a0a50500000505000005050000050500000500000005000000050000000500
|0,14=>0x5050000050500000505000005050000050400000504000005040000050400000000005000000000000000500000000000000000000000000000000f0000000f0000000f0f00000f0f00000f0000000f0000000f0a00000f0a00f0000000f0000000f0000000f0000000200000002000000020000000250500000505000005000000050000000f0f00000f0f00000f0000000f0000e0000000e0000000e0000000e0000000e0000000e0000000e0000000e00500000005000000000000000000000f0f00000f0f0000000000000000f0f00000f0f00000f0f00000f0f00000f0200000f0200000f0200000f02f0f00000f0f00000f0f00000f0f00000f0e00000f0e00000f0e00000f0ed0d00000d0d000000000000000000000d0d00000d0d00000000000000000080000000800000008000000080000000a0000000a0000000a0000000af0000000f0000000f0f00000f0c00000f0000000f0000000f0f00000f0c00f0000000f0000000f0000000f0000000f000000000000000f00000000f0f0000030200000f0f0000030200000f0f0000030200000f0f0000030200f0000000f0000000f0000000f000000000000000000000000000000004040000040400000404000004040000040c0000040c0000040c0000040c
|0,15=>0x30300000303000003030000030300000300000003000000030000000300c0c00000c0c000004040000040400000c0c00000c0c0000040400000404c0c00000e0e00000c0c00000e0e00000c0c00000e0e00000c0c00000e0e00f0000000f00000000000000000000000f0000000f0000000000000000000000000000000000f0000000f00000000000000000000000a0000000a00f0000000f0000000f0000000f0000000f0000000f0000000a0000000af0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0a00000f0af0f0000030300000f0f0000030300000f0f0000020200000f0f0000020200000000000000000000000000000000f0f00000f0000000f0f00000f0050500000505000005000000050000000505000005050000050000000500a0a00000a0a00000a0f00000a0f00000000000000000000000000000000f0300000f0300000f0300000f0300000f0000000f0000000f0000000f0000000000f0a0000000000000f0a0000000000000f0a0000000000000f0af0f0000000e00000f0f0000000e00000f0f0000000e00000f0f0000000e0050000000500000005000000050000000500000000000000050000000000000000303000000000000030300000000000002020000000000000202
|1,0=>0xf0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f0000000050000000500000005000000050000000f0000000f0000000f0000000f00f0f00000000000000000000000000000f0f00000f0f0000000000000000f0f00000f0f00000f0000000f0000000000000000000000000000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000a0a00000a0af0f0000000000000f0f00000f0f00000f0f0000000000000f0f00000000f0500000f0500000f0500000f0500000000000000000000000000000000f0f00000f0f000002020000020200000f0f00000f0f0000020200000202f0f00000f0000000f0f00000f00000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000a0a00000a0a00000000000000000000000000000000f0f00000f0f00000f0000000f00f0f00000f0f00000f0a00000f0a00000f0f00000f0f00000f0a00000f0af0f00000f0f00000f0f00000f0f00000f0c00000f0c00000f0c00000f0cf0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000f0f00000f0f00000c0c00000c0c00000f0f00000f0f00000c0c00000c0c0000000000000000f0a00000f0a000000000000000000000f0a00000f0a
|_,_=>0
def sP:Nat→Nat
|0=>0x30100e1d138080c040a8980425030102a24090180a041187404010305c4407010180a0d108542406028103e15010040c0403874041c030102a020d8180a0403808021a030102a02078000c040383004060284c0e02088181a150a0040c130180824110201c12100301006020780008030103c1c0d038300c050202c0401000101409008181007010180a04018080200
|1=>0x90dc0a130a8082411030100615010041e360200c0412028100602090440a040500c2c19028102a02090d40a170981c0401030106815010480c04198082406028100e09010180a171900c0412028100602090386204018082430028100e1d010bc0c04018b80412028100e1d010b40c15010485806028102a02008ac0c040a8085406028a41a15090180a040e8402428
|2=>0xa80824450283426150b0040c042200c04120284c0803010481c040a8088606028107402008000c17018082425028100602091080a04208540412028102a02200180a170200c043f028100e1d010040c041d008020e030f87a15010180a080a8082406028102a161e0180a041d8e80401030103e150103c0c040500c72120281004121c0180a170681c2c06028102a02
|3=>0x10180a040a848a806028102a14010040c0401808240e0294c0e02030140815010fc0c05021482a3909018080301048a20502028a0020901408030a93c24050200c2a0207810144e010480a042685404010304c2a022601830040500c9612028f826070e8080c0401808244a0284c2a02090189204240740401030108e15010480a0d0a8502406028102a46010480c04
|4=>0x2d8102a02090180a04119682a020901808150103c1c060202c74020081076150103c0c041d00802060200c7402008102a09010040c04118742012030102a59010480a0d0a80836060285c08030106c0a040a848b006028102a02008000c0d0a848ae06028101409090180a040a808ac060c0100602008384004038082206028102a022a8180a040500c2c010285c6407
|5=>0x2054041b03014085a0a8082406028102a02091b40c050201c2a02360180a040500c2c12028100e6a010480c05020540469090180a040a8083606028100615338480a040a808246603014080b0a8082405021902a02090180a040185404123181408620a8580406028102a02091840c05020742a5f090180a040a808245e030140815011742406028102a02091700c05
|6=>0x90180a0424074041203014081501048f206028102a78010480c053b0102a02090180a040a80824750301408150100424063a0102a02091cc0c0502054481203014080a0180824190284c08520a8082406020540412388180a041d808240e03014081501048e0060283426150b0480c0502054046f370180a040505472120301408030a8e404120285c7c07010180a13
|7=>0x98102a02090380c040a808248202a04081d0a80824050681c2a020f0180a04400540401090181a040a848500602810061501048fe050b8540412128180a040a808244203014081d0a808f612030103a02091f80c0502054247c030142e0d0380824060285c0815010fc0c050200c2a023d8480a13020ec2a02090182e04038580406028100e15010040c053b8102a16
|8=>0x3854046f0301408150104918050201c3a020c8180a680201c041203014081545808240602810068a0a8082405020280610090140889018540412028111015010480c0506a1c2a02090180a040a808243c030140815430082406028102a02092140c05022102a020901426040a8980412031a01a15010480c05068102a16008180a040a8590606029a02e04018082405
|9=>0x90c40815010489406028102a96010480c054a8102a02090180a040aa5004120301408930a8082406028340815090b40c050685404120e0180a3e0201c3a02030142604490540412031a07c15010480c05020742a16080480c040385404124881408030a8582012028100e02090380c0502054048f090180a040a8082406029240815010491c06028100e02390180a04
|10=>0xa8082406028100e92010480c05098102a16010040c040a808249e03014080a0a92c24060281014150104938050226c2a02090180a044485404120301408030aa682405020742a02009e80c130a808244c0301408150104932060281006150104930050208c2a02090180a040a808980602860081501004fc06028103a150106c0c051f25c2a02090180a04018540401
|11=>0x301006151300824050205404124c0180a04050742c120301550040a8082406028102a02090180aa7020742a123e0180a045305404120301426040185404120c2940815010480c05190100e15010180a040a80824a4028f94615010480c05022882a02090180a045005404120301408150a008240602810b4070a8082406110101415090180a0d0a8483c0602a34089f
|12=>0xa808240602ac80815010480c05020740401090380c040185404120e014080301004240e02ac40815010480c050201c3a020081808b00a808240602abc0815010480c05020555c02090180a040a8300412030155a040a8082406028102a16012b00c05020540412288180a040a808020f030100615010495605020540412550180aa9020542c12030152e040e8540412
|13=>0x20ec2a020081840040e8540412032f0080a0a89c2406028100e15011a40c050200c2a27010480a041185404190301408150b00974060284c08030a8080212020540412558180a170205404125c81408070a8097006028100615010496e050208c2a02090196c170200c0412029d02e220a808240602ad42615010480c050205404125a0180a040a80824b303014083b
|14=>0x10481c0602b1c0815010480c05020540412630180a040ab140412028102a02008380c20020289002090180a040a80824c4030140815010498606028102a02093080a04310540412031ac0815600480c050ba5c2a02090180a040a858022d0301408030a80824be028102a27090b40c05020742a16010040c1709854041203060080a0a8580206028103a15010497a06
|15=>0x1d00824050205404126a0180a0405074040109018081504808240602811a415010480a170200c040109014081501345a006028103a15010485e060200c2a02090b40acf020742a02090180815670082406028102a02093340c05023302a02090180a040185404190c05c2a020932c0c05023242a020901408070e8080212030102ac8090180a040a8082456030140803
|16=>0x103c0c041d00824060284c0815010fc0c050205404dc090180a040a80824db028100e15011fc0c0502054043f03014081501049b4060285c1a150b0480c050b8102a020d8180a040a80824d90301408070e808240618811b015010480c050985404125c0180a130a808249003014081501049ae06028102a02093580c05020542c10370180ad5020540412030140803
|17=>0x205404010330408500a8082405408102a02008480a040185404010901408070a858200602ad42e04018082405020e82a02008180803010481c05020540412728180ae4020540412028102a0200849c606710102a02090180a04058e80412028c80815010480ce10205424e003014081501049be06028102a020915c0c05023782a02090180a046e8540412030140815
|18=>0x10480c0d0a80824f303015e4040a8082406028102a02093c40c05020540412780180a040a80824ef030140815010480c0577011da15010480c05020742a02378480c040a80824ec030140803758540412028102a10093a80c050684c3a15010480c220201c2a02030140815010497006708102a02093a40a04740540412030141a0a0a8483c0602811ce15010480c05
|19=>0x7d0180a040a808240e030c4083a010040c0d0a80824e30301408070a8085a06028107615010480c31518102a02008480c047c854041203015f0040a808240602bdc0807010480c05020542012140180a040a80824b9028100e1d010480c8d190103a15010480c680205404010901808030a80824057a8100ef4010480c05023240412028100e15130080c05098100e1d
|20=>0xe8542c02090180a040a8580419030142e130a8082406028102afd010480c050205404010308026040a80824fc02aa40815010480c05020283a02090180a040e85404120323408030a8082405468103a1501048c006028102a02348480c050205404125c0180a040a808249d030140815010492006028100615010044004758540412028102a02093ec0c05020540412
|21=>0x718180a1702054041203014301702054041203014e8040a80824ff0301408150b008dc06028102a39010480c05020540401090380c050201c2a02090180a1802054ce12030140815093f80c050205404120f0180a8d0208c2a16010480c050201c2a02008180a040a80824d003014083b0a80802120301408070a808f406028102a02090940c057b8102a02090180a04
|22=>0x1854041202810d415010480c05021f42a02090180a041185404120301444040a85804120301408030a8082419028100e15010042406028102a270100424060284c081d0a8082406028102a02091fc0c0502054047b090180a0d020282a120301409030a8082406028100e150104a0406028103a15010483c06028100e15808082406028120015010480c05020540412
|23=>0x90180a2202054041203014081501049a6051f0102a10010480c050205404120301582040a92c04120301408154d0480c050201c2a02090180a31021482a02090180a0401c142a020901408150100424061881208070a8082406028f80815010480c05708107415010480c05020540401090b40c05020542c10090180a17020540401090180a04038542c02030147c04
|24=>0xa8082406028112415010480c051f0102a02090180a8d020540412030160e040a808241c0301408150100424067085c08150b0082406028102a020932c0c050201c2a02090180abb020540401094180c05024142a02090180ab50b8102a02090180a040a808240e0301408870a8082406028102a270b00824060285c7c15010480c05020ec2a02090180ab50201c2a02
|25=>0x901830041d8742a02090180a17020542002090180a040a80832060c0102a028580424060283408150b0480c0502054041232814080a0a808241e0301408070a8400412030161415010480c050205404125e8180a040a89c041203014081501048dc0602a3426040a8080212030100615010042406028102a02092dc0c050205404120301612040a808250802834081d
|26=>0xa8082406028342a02090780c05020540412650140815010042406028f808070a8080c05020540412830180a040185404010901408030a808240510010061501048f4050205404123f0180a040a8580401090180a041d0082406028109015010480c055485c0815010480c05020540412868140815010495806029a0081d0a8082406028100615010480b0c020742a02
|27=>0x28102a02090180a6b020540412370180a040a8082419030141a040a8082406028103a15010480c05020540412030151a040a80824fc0284c0815010480c05020542002090180a04870082406028100e1d010480c05068102a02008480c05408102a020901426040a85804120301408150142c24060281006150b00824050b81006020901408150100424fc02810460a
|28=>0x815010480c050205404120301408030a80824050200c2a02090180a040a8080212030140815010480c05100102a02091e80c05878102a02090180a17020540412030140815013442406
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32502d50285023501e50195014500f500a500550005
|5,0=>0x1b161ab61a5619f61996193618d61876181617b6175616f61696163615d61576151614b6145613f61396133612d61276121611b6115610f6109610360fd60f760f160eb60e560df60d960d360cd60c760c160bb60b560af60a960a3609d60976091608b6085607f60796073606d60676061605b6055604f60496043603d60376
|5,1=>0x26c62675261625c52575251624b6245623f62396233622d62276221621b6215620f6209620361fd61f761f161eb61e651e061da61d461ce61c861c351bd61b76
|6,0=>0x422641b7414740d7407640073f973f363ec73e573de73d773d073c973c273bb73b473ae63a773a073997392738b7384737d7376736f73687361735a7353734c7346633f73387331732a7323731c7315730e7307730162fa72f372ec72e572df62d872d172cb62c562be72b862b172aa72a3729c7295728e72877280727972727
|6,1=>0x5dc75d575ce75c775c075b975b365ac75a5759e7597759075897582757b7574756d7566755f75587551754a7544653d7536752f75287521751a7513750c750574fe74f774f074e974e274db74d474cd74c674bf74b874b174aa74a3749c7495748e74877481647a7474646d7466745f74587452644b7444743d7436742f74287
|6,2=>0x796678f77896782777b7774776d7767676077597752774b7745673e77386731772a7723771c7715770e7707770076f976f276eb76e476dd76d676cf76c876c176ba76b376ac76a5769e7697769076897682767b7674766d7666765f76587652664b7644763d7636762f76287621761b6614760d760675ff75f875f175ea75e37
|6,3=>0x945793e7937793079297922791b7915690e7907790078fa68f468ed78e678df78d878d268cc68c578bf68b878b178ab68a4789e6897789078897882787d5877687078697863685c7856684f78487841783a7833782c7825781e781778107809780277fc67f577ee77e777e167da77d377cc77c577be77b777b077a977a3679c7
|6,4=>0xa116a0b6a0479fd79f679f159ea79e379dc79d579ce79c779c079b979b369ac79a5799e79977990798b5984797d7976796f79687961795a7953794c7
|7,0=>0xbe17bda7bd46bcc8bc57bbe7bb77baf8ba78ba07b988b917b898b827b7b7b747b6d7b667b5e8b577b4f8b478b3f8b387b317b2a7b237b1b8b138b0b8b047afd7af58aed8ae67adf7ad87ad08ac88ac26abc6ab48aac8aa57a9e7a968a8f7a887a817a798a727a6b7a647a5e6a577a507a497a427a3b7a338a2c7a257a1e7a177
|7,1=>0xdac8da66d9e8d977d907d8a6d837d7b8d747d6e6d677d607d597d527d4b7d447d3d7d358d2f6d287d208d1a6d137d0b8d047cfd7cf58ced8ce76cdf8cd87cd26cca8cc28cbc6cb57cae7ca68c9f7c978c907c897c836c7b8c747c6c8c657c5e7c577c4f8c487c408c388c317c298c227c1b7c138c0c7c057bfd8bf67bf06be88
|7,2=>0xdbb6db47
|8,0=>0xe366e306e297e227e1b7e147e0d7e067dff7df87df17dea7de37ddc7dd57dcf6dc87dc17
|9,0=>0xe3c6
|_,_=>0
def wAt:=mkWire dB 272 236 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa88109015090140e8580a8490088309015090140e858010490b8040284902005028490c8610a819090160284a1d88309014090150a8150901501049020151d00609015090140a815028650284a0384c09015090140c861090160284a010490a8490088309015090140b804028490e85801049020050284901005090150a8490a8490684901011008830901509014028790204a0c861090160284a0b85801049
|1=>0xa8493e80b0e8190a8493404b0b81518849020160a80509015010490a849028650a8490284a098090a9e90a8150984b3b8550a809011c90e8480a8150a8190284a050170a80909015010650284a020490a8490a81134048098550b013010490a809010490a8190a8490a9ad340480b8150a81901081090140a9950308109014038170a849011810304a0b85a0a811050491d0190a88109015090140a8150a819
|2=>0x504a038170a81901083090140a8490180409015340480207502049010160204901006090150f0150204a0a8150a861090160a815030c5020160a81902849092410a8110e8480a81546849010161f016020490284a0a8150a8490a81501055010150a8190a8790204a400190a8c5020160b017010490b8150a811010490284901049050480a8090a806090150d019020760681b020090504b0a8090984b02015
|3=>0x180709015031d10b81602006028490804a0b8161f009020490a80609015028790204a09015090150a8490a815090150b85801049050170e84a0a81500883090150901401807090150685502235010160180409015011f60e819038c70a849090160a81902005028493a01a0b8160a811020490a8160aa85091ad09858118170101d068490a80902009038160a8490104902015090150a8490504a0a80903277
|4=>0x28490a8190e84b0a815029e90104a010060901502061090160a819090160284a02055020150ab290681802009028490a81501305038140a8490a806090150e84b0a815019eb0104a0a81909015090140aa750504a0a8090d01a020760a815013070381402235010160901502afd01848090150a8110a815029810304a09014090150100509015092ed038160a84901005090150a849370150a84a0a81909015
|5=>0xa849028490ab993d01a0104a0681b0c8150284a0a8190a8490a8190a88109015090140a806090150681b0200909857021f90a8491d0190a88109014011cb0e84805004028490984b020150c861090160284a0a8490a8153404b098550932d02015031c90e8484684a010163404b0b815340480b8153b857090150a8112904a050170b04e01049010150a881090140a8190e8580a815010490ab4d0308309014
|6=>0xa8190a8150304a708490a81602006028490504a0a8090b80b0a81109014090150a81901883090140a81900819090150a88109015090140a84e020150a8160a805020b5090150b8173a0190b8160a8490200502849098557b0160184b0a8490ab29068180b01701049038130a8490b057028495a8160081b09015092350101601883090140b0570a815020150a849068490101103307038140a8490204a03814
|7=>0x50150a8090a849030150204a0a815010190a8490381b0a8490985702015090160a8110b8160a8110e80b0a8150a84a01049010650284a0a806090150a849090160108109014011830304a0204a010160b055010490a849028490e84b0a815090150a8490104a0984b020150b8170a8110a81501049010490284a020150a811010790204a09015090140a81a0201506855020090a8150a809010160a81501016
|8=>0xb01501049020490a8110a80509015038110a849068490101103083090140204901015038140a849011b90a84a01083090140a84902016050170a809018170a8190284902016038190a849020490a8160a8810901401006090150101501049090150a84901049020490a8190a9ad030160e8190a815050490a8090b011010490284a0a8190a84902849090150a81502015092370101618849020160a80902009
|9=>0xa815018140a8190a815090160e8490a815010150a811090160284a09015010490101103081090140204a0a8090a84901015021ad03016029810304a0100509015010160a84a0201509015090150804a01015370160a84a3d0190104a0a815020090a8610901601016020490b8140a811028790204a0a81609015010490a8110980b02015038160a84909015018170a8190b8490a8110a806090150a8790204a
|10=>0x9015090140104a020190a81103049030160a84a0284a020090a815010160a81a02015010150a883090140a8490a815090150681b0200901049020150081909015010490a8190a8110a8190a81a09015050490a8090204a010110681802009090150a849020490081b09015090150a819090140a8190104a0a8190101e0a84901049028490a881090140a9e90104a0b8090a8111881a020160e84a0a81502075
|11=>0xa8190a819
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xa8400000000000000000000000009cc0000000000090c00000000000000000084c000080400000001e206cc00000001920000000058c000050800000000000000000048810200000000000000000000000000000000000038800000000d1028c00001cc0520000000008c002
|5,1=>0x42400004110f503c10ec400000000000000383000036200000000d080000000322000000000000000000000000000000002e400002b3
|6,0=>0x24cc91223c88d2228c000220886221080000000822000080200000001fc47d21f047a21e087621d087131c046e200006d11b0400000006b11a0c662190800018c400000000001848000178c5c200000001688573154800014c850300004d3000000012c8000124847200000000000461
|6,1=>0xdc23688d820000d6234ccd120000cf23384cc2324c0000000c72310cc313048bf22f840002ecc0000000ba12e0800000000002d88b42000000000000000000b312c48af22b84ac22ac40002a48a8129c4a52000000028c8a1227c89c326c40000000983000000025880000000000
|6,2=>0x4b8d2c24a4c00049c9252000122348091d30000000468c0004609162454513244840004444000438d0c200010a241cd05241050224008fe23f08fa23e440003e04f62000000000000000000f423c88f110000ee30000ed10000eb23a84e820000e5338c80003884e020000de20000000
|6,3=>0x634800062c98a162098530001823000181100017e35ecd7a15dcd7615d457235c080005b896d15ac968300016625908000000162257cd5d256c959255c955254c80000001512540400000014f153854c252894910001463000000050cd4034f893c24e893824d8800000000004ccd312
|6,4=>0x6c8daf30001ad20001aa36a080000001a716985a4268c40006849a0167899d166c99a16609962000194264c4000648400064458f2
|7,0=>0x8c0a2e28b0a2a28a0a262890a222880a1e2870a1a28646172854a132844a0f2834a0b2824a081818a042808a0027f89fc27e89f827d89f427c89f027b89ec27a89e827989e427889e027789dc27689d9175c9d5274c9d1273c9cd272c9c9271c9c5270c9c126fc9bd26ec9b926dc9b52
|7,1=>0xab06aa2aa0aa62a90aa22a80a9e2a70a9a2a646972a54a932a44a8f2a34a8b2a24a872a14a832a04a7f29f4a7b29e4a7729d4a7419c8a7029b8a6c29a8a682998a642988a61197ca5d296ca59295ca55294ca51293ca4d292ca4929206462910a422900a3e28f0a3a28e0a3628d0a322
|7,2=>0xabcaad2
|8,0=>0x2c11b006bf1af86bd1af06bb1ae86b91ae06b71ad86b51ad06b31ac86b11
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0x40400010000003880000c300002c00000a900002900000a0000027400009800002280000880000208000080000012c000042000010000003d000008c000022000008400002000000740000180000028000009000002000000500000100000020000004000000
|1=>0x808c0020110008010002003000800000104a00040a80010020004000000deb000372c00090300020840007eb0001e2c00074b0001bac00060000017ac0005cb000152c0004eb0000e080002e00000a00000202000078c0001e200005080001200000428000102
|2=>0x40028010002004000000a1eb00251000090420021108008440002060c0080a20020008004d6b00122640045190010424004090001022c004082001020000402b0010080004011001004000400a0010008004001000d17c00314200097ac0020ef00082b400203b
|3=>0x44dac0111eb00446a401116b00443ac0110df004412c01100300437a401092100420840107eb0041c000105eb004172c0104000040c8801030200408080101eb00407880101e0004052c010109004040c01010200403bc01008e00402280100890040200010021
|4=>0x4000000d10eb03407340c01cf030032c0b000a020002007846b01611ac05806b014073c04c1cb010400004038a010062804000200cc1ac03116b00c0c8803030200c000002050a0080c0802024b008080802014b00617ac0181eb006072c01814b004d7bc01354f
|5=>0x143008c50403b14029ac50006b104400c400b01100280c35844b0d6012c24000208211181840fb056d12c15954b053012c1495cb052512c1440fb04801ac11c04b044a5a411206b04305ac1091cb04217ac1081eb04202ac1049fd04127ec10286b0402d2c10026b
|6=>0x21090cf402000cd040fb301004c94c0cb24103ac8d004b228002884018a210032c84000020800008100022000e0880028a200000053002314801ac50c04b
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x28002e230a0a000000000200020000130000020000000000000000001d0002000012000000000000000900000002000000000020001200000202000008000002000200000000000202000000000000000000000200000a0700020200000202
|6,0=>0x2050500025f61000f18024800005e06491f0103001c00c33b100000000261000000000037050112051200020a2601000029029366120000bf0000010000003905010e34c7050202000005000200000a0216020205055e1b2200494900001e8a0b05008700190002009105000002c07000156b00560000010002010000000a
|6,1=>0x200100a3e070010004a005e2512200a27320f005512016a00020c0000022a730501020202004d02490000994b3c051e006a00003f1d140f0202020000006b46422078000f050057021f00003a000247013833005d00200200025e020a01141090029f00c84e00000000005e0202008c004900134901002d0200500200020000
|6,2=>0x241d0055002f010000123d011200025d0212b68b41020004490049000355
|7,0=>0x17a51aafa9ce80ba52426992b28284a6a0767232cf652ccb968d894c725ba485510d97a8a2679d594372a7408e627b2b6f4fb46d58b8c5693075ca88c4a36c1a7f367164bcb77db5637460ab15a19498b3bd53836e339a717ebec15a21d1af9b63c6ad3536666e725c68b96e8687319cc90d77cc542d7ad0c2bbac447c952dcd
|7,1=>0x718c
|8,0=>0x69b1af81722dd2c9b0972c72ae8f79459eaa
|9,0=>0x11
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 26 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_233 7 roots_233 ops++addP pm 1 dom_227 7 roots_227 ops++addP pm 2 dom_138 4 roots_138 ops++addP pm 3 dom_203 7 roots_203 ops++addP pm 4 dom_137 4 roots_137 ops++addP pm 5 dom_105 5 roots_105 ops++addP pm 6 dom_171 7 roots_171 ops++addP pm 7 dom_202 5 roots_202 ops++addP pm 8 dom_234 6 roots_234 ops++addP pm 9 dom_226 4 roots_226 ops++addP pm 10 dom_170 5 roots_170 ops++addP pm 11 dom_232 4 roots_232 ops++addP pm 12 dom_43 5 roots_43 ops++addP pm 13 dom_41 4 roots_41 ops++addP pm 14 dzo_137_64 4 roots_137 ops++addP pm 15 dzo_171_64 6 roots_171 ops++addP pm 16 dom_107 6 roots_107 ops++addP pm 17 dom_99 4 roots_99 ops++addP pm 18 dzo_139_64 5 roots_139 ops++addP pm 19 dom_75 4 roots_75 ops++addP pm 20 dzo_169_64 5 roots_169 ops++addP pm 21 dom_163 4 roots_163 ops++addP pm 22 dom_225 4 roots_225 ops++addP pm 23 dom_195 4 roots_195 ops++addP pm 24 dom_169 5 roots_169 ops++addP pm 25 dom_139 5 roots_139 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_235 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_137_64_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_171_64_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_139_64_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_169_64_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_139 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_233 7 s (0,roots_233.map (·&&&dom_233)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_235 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_233 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_235==dom_235)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_235 gM v ys):RunD true dom_235 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_235 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
theorem lowS_237:Lower true dom_237 roots_237 goal_237 9:=lower_slice_b [(0x333300003333000033330000333300000000000000000000000000000000,1,129)] (by decide +kernel) lowS_109
def isoMvS_95:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_95:Lower true dom_95 roots_95 goal_95 7:=lower_iso_b isoMvS_95 (by decide +kernel) lowS_63
def isoMvS_119:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_119:Lower true dom_119 roots_119 goal_119 9:=lower_iso_b isoMvS_119 (by decide +kernel) lowS_111
def isoMvS_125:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=lower_iso_b isoMvS_125 (by decide +kernel) lowS_111
def isoMvS_126:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_iso_b isoMvS_126 (by decide +kernel) lowS_111
def isoMvS_189:List (Nat×Nat):=[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 8:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_175
def isoMvS_190:List (Nat×Nat):=[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_183
def isoMvS_207:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=lower_iso_b isoMvS_207 (by decide +kernel) lowS_183
def isoMvS_215:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 8:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_175
def isoMvS_219:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_219:Lower true dom_219 roots_219 goal_219 9:=lower_iso_b isoMvS_219 (by decide +kernel) lowS_187
def isoMvS_221:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 9:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_183
def isoMvS_222:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 8:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_175
def isoMvS_238:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_123
def isoMvS_243:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 10:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_235
def isoMvS_245:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 9:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_123
def isoMvS_246:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_237
def isoMvS_249:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_235
def isoMvS_250:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_235
def isoMvS_252:List (Nat×Nat):=[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_231
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,18),(2,66),(3,11),(3,19),(3,35),(3,67),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(6,14),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,10),(8,40),(12,13),(12,14),(12,44),(12,76),(16,17),(16,18),(16,80),(20,21),(20,22),(20,52),(20,84),(24,25),(24,26),(24,56),(24,88),(28,29),(28,30),(28,60),(28,92),(32,33),(32,36),(32,40),(32,96),(34,35),(34,38),(34,42),(34,50),(34,98),(48,49),(48,50),(48,52),(48,56),(48,112),(64,66),(64,68),(64,80),(64,96),(65,67),(65,69),(65,73),(65,81),(65,97),(72,73),(72,74),(72,76),(72,88),(72,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|6=>6
|7=>6
|8=>7
|9=>3
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xd6b4ec757591756778ca3631c267f9
|7,0=>0xf3475d61c08a13986515675af17904
|8,0=>0xde17cd61c0aa9a7934af86515761fa4c783
|9,0=>0xe74f2761fa31191
|10,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffaaaaaaaaaaaaaaaaaaaaaaaafffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000ffffffff0000000000000000ffffffff00000000000000000f0f0f0f0f0f0f0f0f0f0f0f00000000ffffffff000000000000000000000000ffffffff00000000ffffffff00000000ffffffffffffffff0000000000000000ffffffffffffffffffffffff0000000000000000ffffffffffffffff00000000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000f0f0f0f0f0f0f0f00000000
|_,_=>0
def sP:Nat→Nat
|0=>0xe217684321a7c43d21b643d21984321a76843d217843d2f764321a9684321a7643e2184321a76543d21543d21543210654321a64321054321a64321a06543210
|1=>0x843d217843d21796843d2178c43d217843
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0x2161a71460e6077007
|7,0=>0x4974183b63472d7276
|8,0=>0x7c77486d76675f7578507
|9,0=>0x9388b8838
|10,0=>0x9b7
|_,_=>0
def wAt:=mkWire dB 16 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x8721d78b65871b78761e78a1c875b78771d788658721c6de1d6df1d78a1dd961c69e1c8772d879e2cb61e789a78721da9e1c875a78721da9e1c875a78721d
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x3ccc324c630cc03
|7,0=>0x78db360c0054d23
|8,0=>0x2d2aca929ca528ca12
|9,0=>0x311c06f1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 10
def pmP:Nat→Nat
|0=>0xbf7b3f3b060200
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x9249
|7,0=>0x22a1b
|8,0=>0x1b69b6
|9,0=>0x1b6
|10,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_126 9 roots_126 ops++addP pm 1 dom_123 9 roots_123 ops++addP pm 2 dom_95 7 roots_95 ops++addP pm 3 dom_125 9 roots_125 ops++addP pm 4 dom_119 9 roots_119 ops++addP pm 5 dom_111 9 roots_111 ops++addP pm 6 dom_91 6 roots_91 ops++addP pm 7 dom_63 7 roots_63 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_63 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_126 9 s (0,roots_126.map (·&&&dom_126)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_126 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 6 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 6 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 7 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 3 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_127 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_159_32:=0xffffffff000000000000000000000000ffffffff00000000
def gzo_159_32:=0xfffffffe000000000000000000000000fffefffa00000000
def gsh_159_32:=0xfffffffe000000000000000000000000fffefffa
theorem lowS_zo_159_32_146:Lower true dzo_159_32 roots_159 gzo_159_32 7:=lower_iso_b (d1:=dom_159) (r1:=roots_159) (T1:=gsh_159_32) [(dom_159,32)] (by decide +kernel) (lower_slice_b (T:=gsh_159_32) [(0xaaaaaaaa000000000000000000000000aaaaaaaa,0,1),(0xf0f0f0f0000000000000000000000000f0f0f0f0,0,4),(0xff00ff00000000000000000000000000ff00ff00,0,8)] (by decide +kernel) lowS_146)
namespace S_191
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,10),(2,18),(2,130),(3,11),(3,19),(3,35),(3,131),(4,36),(4,132),(5,13),(5,21),(5,37),(5,133),(6,14),(6,22),(6,38),(6,134),(7,15),(7,23),(7,39),(7,135),(8,9),(8,10),(8,40),(8,136),(12,13),(12,14),(12,44),(12,140),(16,17),(16,18),(16,144),(20,21),(20,22),(20,52),(20,148),(24,25),(24,26),(24,56),(24,152),(28,29),(28,30),(28,60),(28,156),(32,33),(32,36),(32,40),(34,35),(34,38),(34,42),(34,50),(34,162),(48,49),(48,50),(48,52),(48,56),(48,176),(128,129),(128,130),(128,132),(128,136),(128,144),(160,161),(160,162),(160,164),(160,168),(160,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffffff
def xsM:=roots_191.map (·&&&dom_191)
def gM:=goal_191&&&dom_191
def NN:Nat→Nat
|7=>5
|8=>16
|9=>11
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xefd6deb37a933bc92954921b5
|8,0=>0xdc3abcedf1c06bfb8713b3a3ca4d229e53094b2778e3b6d1045291f47cdd3b7583565d200100af09
|9,0=>0xe03e0c502bbef169e530890367caac72d4b644615dccf47cdd36c33
|10,0=>0x2bff1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff0000ffff00000000000000000000000000000000ffffffff0000ffff0000000000000000ffffffff000000000f0f0f0f00000f0f00000000000000000f0f0f0f0000000000000000000000000000000000000000ffffffff0000000000000000ffffffff0000000000000000000000000000000000000000ffffffff0000000000000000ffffffff00000000ffffffff333333330000000000000000ffffffff00000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0333333333333333300000000000000000000000000000000ffffffff000000000000000000000000ffffffff00000000ffff0000ffff00000000000000000000ffff0000ffff0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00cccccccccccccccc0000000000000000ccccccccccccccccaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa0f0f0f0f0303030300000000000000000f0f0f0f00000000ffffffffffffffff00000000000000000000000000000000
|0,1=>0xffffffffcccccccc0000000000000000ffffffffccccccccffffffffffffffff0000000000000000ffff0000ffff0000ffffccccffffcccc0000000000000000ffffccccffffcccc333333333333333300000000000000003333333300000000ffff0000000000000000000000000000ffffffff000000000000ffff0000000000000000000000000000ffff00000000ffffffffffffffff00000000000000000000ffff00000000ffffffff0000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffccccccccffffffffffffffff0000000000000000cccccccccccccccc0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0c0c0c0cffffffffffffffff0000000000000000ffffffff000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2910310185220625c4a440c57030a440c4089483140062906280305220620458522062044a440c403148818ac0a18a440c40714881881129103154c520c52030a418a00714831340a29103118a418820
|1=>0xc522062044c522062018a440c40598a440c403b0a440c403148818ae0e18a440c40314881881536ca440c40368a440c4089488188066148818811291031641161488188c522062c81c6
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0x1b71470d7076007
|8,0=>0x9188a78287a87376b86475d75674f7478407388308297227
|9,0=>0xe78df8d78d07c88c08b88b08a88a17998
|10,0=>0xef7
|_,_=>0
def wAt:=mkWire dB 29 192 0xffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x30130218230331730d30028128d30130388f30130330188f30133d2823033023173013573008a33018a330133f282303301601303b8131734d18133d282300301a2334d1818838a330172333d28262d3033024a331d182
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0xc324c630cc03
|8,0=>0xb4ab2a4a7294a32849f2749b26497254932448f2
|9,0=>0x391e0771d8751d0731c8711c06f1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xd23f6faf6eaf6abf6a3f66ff56ef483f2eaf2aef28ff28bf283f243f20ff20bf203f1faf1eaf1a3f0aaf04bf00a7008f007f002f001d00070000
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x209885
|8,0=>0x4c3336c5abdb64865510
|9,0=>0x6a87bbf0eb7152
|10,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 16 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_190 9 roots_190 ops++addP pm 1 dom_187 9 roots_187 ops++addP pm 2 dom_183 9 roots_183 ops++addP pm 3 dom_189 8 roots_189 ops++addP pm 4 dom_157 6 roots_157 ops++addP pm 5 dom_175 8 roots_175 ops++addP pm 6 dom_143 6 roots_143 ops++addP pm 7 dom_63 7 roots_63 ops++addP pm 8 dzo_155_32 6 roots_155 ops++addP pm 9 dom_61 6 roots_61 ops++addP pm 10 dom_47 6 roots_47 ops++addP pm 11 dzo_159_32 7 roots_159 ops++addP pm 12 dom_45 5 roots_45 ops++addP pm 13 dom_159 7 roots_159 ops++addP pm 14 dom_141 5 roots_141 ops++addP pm 15 dom_173 6 roots_173 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_191 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_155_32_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_159_32_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_173 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_190 9 s (0,roots_190.map (·&&&dom_190)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_191 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_190 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_191==dom_191)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_191 gM v ys):RunD true dom_191 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_191 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 11 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_191 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,32,36)] (by decide +kernel) lowS_235
def dzo_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000
def gzo_219_32:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0f000000000f0e0f0a00000000
def gsh_219_32:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0f000000000f0e0f0a
theorem lowS_zo_219_32_146:Lower true dzo_219_32 roots_219 gzo_219_32 7:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_32) [(dom_219,32)] (by decide +kernel) (lower_slice_b (T:=gsh_219_32) [(0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a,0,1),(0xf000f00000000000f000f00000000000f000f00000000000f000f00,0,8),(0xf0f0f0f0000000000000000000000000f0f0f0f0000000000000000,0,64)] (by decide +kernel) lowS_146)
def dzo_187_64:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000
def gzo_187_64:=0xf0f0f0f0f0f0f0e00000000000000000f0f0f0f0f0f0e0c0000000000000000
def gsh_187_64:=0xf0f0f0f0f0f0f0e00000000000000000f0f0f0f0f0f0e0c
theorem lowS_zo_187_64_137:Lower true dzo_187_64 roots_187 gzo_187_64 7:=lower_iso_b (d1:=dom_187) (r1:=roots_187) (T1:=gsh_187_64) [(dom_187,64)] (by decide +kernel) (lower_slice_b (T:=gsh_187_64) [(0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c,0,2),(0xf0f00000f0f000000000000000000000f0f00000f0f0000,0,16),(0xf0f0f0f0000000000000000000000000f0f0f0f00000000,0,32)] (by decide +kernel) lowS_137)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,10),(2,18),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,10),(8,40),(8,136),(16,17),(16,18),(16,80),(16,144),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,40),(32,96),(34,35),(34,42),(34,50),(34,98),(34,162),(48,49),(48,50),(48,56),(48,112),(48,176),(64,66),(64,80),(64,96),(65,67),(65,73),(65,81),(65,97),(65,193),(72,73),(72,74),(72,88),(72,104),(72,200),(128,129),(128,130),(128,136),(128,144),(160,161),(160,162),(160,168),(160,176),(160,224),(192,193),(192,194),(192,200),(192,208),(192,224)]
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
|9,0=>0xfb416a432426029182a8
|10,0=>0xe3d5958b41
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x6543210c654321086543210c65432a1b65432106543219076543210
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
|0=>0x605851058180d85a6c4180585
|_=>0
def oO:Nat→Nat→Nat
|9,0=>0x62422202
|10,0=>0x9181
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x8ff47f37f1ff0ff07f000
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>0x8aa
|10,0=>0x1e
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_187 9 roots_187 ops++addP pm 2 dom_219 9 roots_219 ops++addP pm 3 dom_249 10 roots_249 ops++addP pm 4 dom_243 10 roots_243 ops++addP pm 5 dom_235 10 roots_235 ops++addP pm 6 dom_123 9 roots_123 ops++addP pm 7 dzo_219_32 7 roots_219 ops++addP pm 8 dom_91 6 roots_91 ops++addP pm 9 dom_59 6 roots_59 ops++addP pm 10 dzo_187_64 7 roots_187 ops++addP pm 11 dom_155 6 roots_155 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_219_32_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_187_64_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_155 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
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
def isoMvS_223:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_iso_b isoMvS_223 (by decide +kernel) lowS_191
def isoMvS_247:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_iso_b isoMvS_247 (by decide +kernel) lowS_239
def isoMvS_253:List (Nat×Nat):=[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 11:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_239
def isoMvS_254:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 11:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_239
def dzo_173_64:=0x333300003333000000000000000000003333000033330000000000000000
def gzo_173_64:=0x333300003332000000000000000000003333000032300000000000000000
def gsh_173_64:=0x33330000333200000000000000000000333300003230
theorem lowS_zo_173_64_137:Lower true dzo_173_64 roots_173 gzo_173_64 6:=lower_iso_b (d1:=dom_173) (r1:=roots_173) (T1:=gsh_173_64) [(dom_173,64)] (by decide +kernel) (lower_slice_b (T:=gsh_173_64) [(0x30300000303000000000000000000000303000003030,0,4),(0x33330000000000000000000000000000333300000000,0,32)] (by decide +kernel) lowS_137)
def dzo_214_32:=0x55005500000000005500550000000000550055000000000055005500000000
def gzo_214_32:=0x55005500000000005500540000000000550055000000000054005000000000
def gsh_214_32:=0x550055000000000055005400000000005500550000000000540050
theorem lowS_zo_214_32_146:Lower true dzo_214_32 roots_214 gzo_214_32 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_32) [(dom_214,32)] (by decide +kernel) (lower_slice_b (T:=gsh_214_32) [(0x500050000000000050005000000000005000500000000000500050,0,4),(0x550055000000000000000000000000005500550000000000000000,0,64)] (by decide +kernel) lowS_146)
def dzo_191_64:=0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def gzo_191_64:=0xfffffffffffffffe0000000000000000fffffffffffffefc0000000000000000
def gsh_191_64:=0xfffffffffffffffe0000000000000000fffffffffffffefc
theorem lowS_zo_191_64_137:Lower true dzo_191_64 roots_191 gzo_191_64 8:=lower_iso_b (d1:=dom_191) (r1:=roots_191) (T1:=gsh_191_64) [(dom_191,64)] (by decide +kernel) (lower_slice_b (T:=gsh_191_64) [(0xcccccccccccccccc0000000000000000cccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,0,4),(0xffff0000ffff00000000000000000000ffff0000ffff0000,0,16),(0xffffffff000000000000000000000000ffffffff00000000,0,32)] (by decide +kernel) lowS_137)
def dzo_159_64:=0xffffffff000000000000000000000000ffffffff0000000000000000
def gzo_159_64:=0xfffffffe000000000000000000000000fffffefc0000000000000000
def gsh_159_64:=0xfffffffe000000000000000000000000fffffefc
theorem lowS_zo_159_64_137:Lower true dzo_159_64 roots_159 gzo_159_64 7:=lower_iso_b (d1:=dom_159) (r1:=roots_159) (T1:=gsh_159_64) [(dom_159,64)] (by decide +kernel) (lower_slice_b (T:=gsh_159_64) [(0xcccccccc000000000000000000000000cccccccc,0,2),(0xf0f0f0f0000000000000000000000000f0f0f0f0,0,4),(0xffff0000000000000000000000000000ffff0000,0,16)] (by decide +kernel) lowS_137)
def dzo_211_32:=0xf000f00000000000f000f00000000000f000f00000000000f000f00000000
def gzo_211_32:=0xf000f00000000000f000e00000000000f000f00000000000e000a00000000
def gsh_211_32:=0xf000f00000000000f000e00000000000f000f00000000000e000a
theorem lowS_zo_211_32_146:Lower true dzo_211_32 roots_211 gzo_211_32 6:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_32) [(dom_211,32)] (by decide +kernel) (lower_slice_b (T:=gsh_211_32) [(0xa000a00000000000a000a00000000000a000a00000000000a000a,0,1),(0xf000f000000000000000000000000000f000f0000000000000000,0,64)] (by decide +kernel) lowS_146)
def dzo_158_32:=0x555555550000000000000000000000005555555500000000
def gzo_158_32:=0x555555540000000000000000000000005554555000000000
def gsh_158_32:=0x5555555400000000000000000000000055545550
theorem lowS_zo_158_32_146:Lower true dzo_158_32 roots_158 gzo_158_32 6:=lower_iso_b (d1:=dom_158) (r1:=roots_158) (T1:=gsh_158_32) [(dom_158,32)] (by decide +kernel) (lower_slice_b (T:=gsh_158_32) [(0x5050505000000000000000000000000050505050,0,4),(0x5500550000000000000000000000000055005500,0,8)] (by decide +kernel) lowS_146)
def dzo_189_64:=0x3333333333333333000000000000000033333333333333330000000000000000
def gzo_189_64:=0x3333333333333332000000000000000033333333333332300000000000000000
def gsh_189_64:=0x333333333333333200000000000000003333333333333230
theorem lowS_zo_189_64_137:Lower true dzo_189_64 roots_189 gzo_189_64 7:=lower_iso_b (d1:=dom_189) (r1:=roots_189) (T1:=gsh_189_64) [(dom_189,64)] (by decide +kernel) (lower_slice_b (T:=gsh_189_64) [(0x303030303030303000000000000000003030303030303030,0,4),(0x333300003333000000000000000000003333000033330000,0,16),(0x333333330000000000000000000000003333333300000000,0,32)] (by decide +kernel) lowS_137)
def dzo_223_32:=0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def gzo_223_32:=0xffffffff00000000fffffffe00000000ffffffff00000000fffefffa00000000
def gsh_223_32:=0xffffffff00000000fffffffe00000000ffffffff00000000fffefffa
theorem lowS_zo_223_32_146:Lower true dzo_223_32 roots_223 gzo_223_32 8:=lower_iso_b (d1:=dom_223) (r1:=roots_223) (T1:=gsh_223_32) [(dom_223,32)] (by decide +kernel) (lower_slice_b (T:=gsh_223_32) [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,0,1),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,0,4),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,0,8),(0xffffffff000000000000000000000000ffffffff0000000000000000,0,64)] (by decide +kernel) lowS_146)
def dzo_222_32:=0x5555555500000000555555550000000055555555000000005555555500000000
def gzo_222_32:=0x5555555500000000555555540000000055555555000000005554555000000000
def gsh_222_32:=0x55555555000000005555555400000000555555550000000055545550
theorem lowS_zo_222_32_146:Lower true dzo_222_32 roots_222 gzo_222_32 7:=lower_iso_b (d1:=dom_222) (r1:=roots_222) (T1:=gsh_222_32) [(dom_222,32)] (by decide +kernel) (lower_slice_b (T:=gsh_222_32) [(0x50505050000000005050505000000000505050500000000050505050,0,4),(0x55005500000000005500550000000000550055000000000055005500,0,8),(0x55555555000000000000000000000000555555550000000000000000,0,64)] (by decide +kernel) lowS_146)
def dzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
def gzo_215_32:=0xff00ff0000000000ff00fe0000000000ff00ff0000000000fe00fa00000000
def gsh_215_32:=0xff00ff0000000000ff00fe0000000000ff00ff0000000000fe00fa
theorem lowS_zo_215_32_146:Lower true dzo_215_32 roots_215 gzo_215_32 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_32) [(dom_215,32)] (by decide +kernel) (lower_slice_b (T:=gsh_215_32) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xf000f00000000000f000f00000000000f000f00000000000f000f0,0,4),(0xff00ff00000000000000000000000000ff00ff0000000000000000,0,64)] (by decide +kernel) lowS_146)
def dzo_157_64:=0x33333333000000000000000000000000333333330000000000000000
def gzo_157_64:=0x33333332000000000000000000000000333332300000000000000000
def gsh_157_64:=0x3333333200000000000000000000000033333230
theorem lowS_zo_157_64_137:Lower true dzo_157_64 roots_157 gzo_157_64 6:=lower_iso_b (d1:=dom_157) (r1:=roots_157) (T1:=gsh_157_64) [(dom_157,64)] (by decide +kernel) (lower_slice_b (T:=gsh_157_64) [(0x3030303000000000000000000000000030303030,0,4),(0x3333000000000000000000000000000033330000,0,16)] (by decide +kernel) lowS_137)
def dzo_143_64:=0xffff0000000000000000000000000000ffff0000000000000000
def gzo_143_64:=0xfffe0000000000000000000000000000fefc0000000000000000
def gsh_143_64:=0xfffe0000000000000000000000000000fefc
theorem lowS_zo_143_64_137:Lower true dzo_143_64 roots_143 gzo_143_64 6:=lower_iso_b (d1:=dom_143) (r1:=roots_143) (T1:=gsh_143_64) [(dom_143,64)] (by decide +kernel) (lower_slice_b (T:=gsh_143_64) [(0xcccc0000000000000000000000000000cccc,0,2),(0xf0f00000000000000000000000000000f0f0,0,4)] (by decide +kernel) lowS_137)
def dzo_175_64:=0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000
def gzo_175_64:=0xffff0000fffe00000000000000000000ffff0000fefc0000000000000000
def gsh_175_64:=0xffff0000fffe00000000000000000000ffff0000fefc
theorem lowS_zo_175_64_137:Lower true dzo_175_64 roots_175 gzo_175_64 7:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_64) [(dom_175,64)] (by decide +kernel) (lower_slice_b (T:=gsh_175_64) [(0xcccc0000cccc00000000000000000000cccc0000cccc,0,2),(0xf0f00000f0f000000000000000000000f0f00000f0f0,0,4),(0xffff0000000000000000000000000000ffff00000000,0,32)] (by decide +kernel) lowS_137)
def dzo_218_32:=0x505050500000000050505050000000005050505000000000505050500000000
def gzo_218_32:=0x505050500000000050505040000000005050505000000000504050000000000
def gsh_218_32:=0x5050505000000000505050400000000050505050000000005040500
theorem lowS_zo_218_32_146:Lower true dzo_218_32 roots_218 gzo_218_32 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_32) [(dom_218,32)] (by decide +kernel) (lower_slice_b (T:=gsh_218_32) [(0x5000500000000000500050000000000050005000000000005000500,0,8),(0x5050505000000000000000000000000050505050000000000000000,0,64)] (by decide +kernel) lowS_146)
def dzo_185_64:=0x303030303030303000000000000000003030303030303030000000000000000
def gzo_185_64:=0x303030303030302000000000000000003030303030302000000000000000000
def gsh_185_64:=0x30303030303030200000000000000000303030303030200
theorem lowS_zo_185_64_137:Lower true dzo_185_64 roots_185 gzo_185_64 6:=lower_iso_b (d1:=dom_185) (r1:=roots_185) (T1:=gsh_185_64) [(dom_185,64)] (by decide +kernel) (lower_slice_b (T:=gsh_185_64) [(0x30300000303000000000000000000000303000003030000,0,16),(0x30303030000000000000000000000000303030300000000,0,32)] (by decide +kernel) lowS_137)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,10),(2,18),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,40),(8,136),(12,13),(12,14),(12,44),(12,76),(12,140),(16,17),(16,18),(16,80),(16,144),(20,21),(20,22),(20,52),(20,84),(20,148),(24,25),(24,26),(24,56),(24,88),(24,152),(28,29),(28,30),(28,60),(28,92),(28,156),(32,33),(32,36),(32,40),(32,96),(34,35),(34,38),(34,42),(34,50),(34,98),(34,162),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,68),(64,80),(64,96),(65,67),(65,69),(65,73),(65,81),(65,97),(65,193),(72,73),(72,74),(72,76),(72,88),(72,104),(72,200),(128,129),(128,130),(128,132),(128,136),(128,144),(160,161),(160,162),(160,164),(160,168),(160,176),(160,224),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|7=>5
|8=>58
|9=>280
|10=>311
|11=>79
|12=>8
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xd7ebbcd9d9bc64f4e3150777e
|8,0=>0xddeb4b04e1b0430a15589c6038720486a768499083592826967aa596ef336a9ac68f3968de1661ad6373a60ef2601c95d1d558fba542cc50d8a4f8784c40c48f6945e844177f40e573fe5e3d68e373a43624c3455f33af533a8d325f631a492976f23ab9205531fa431ec521ab1f1867714efe1350e1165a114f210e8b10d8d0d2050cafe07f470564e0415f0350b020b5
|9,0=>0x2a0562a02629fcf29f7029e1529c9d29ba4292692923a278d1276f6275632732f26f5d256b124fc124a68249ce23f3e23e022324622850222a5209432077320566204b2200591fab61f7521ed5c1ea381e8e01e5f51e57c1e3bd1e1a61d3881d24d1ca341b7391a3b119b0119a43197b0194b118a9317f7117ef717ddd174d616c05167181623715e5315d8215ac51590215427153a6150cc14d5b14900148101439313ce3138fe1383b134b6131fe12af91286210b28103590fd8c0fb6a0f55e0f2be0e60a0e4e00db590d6de0d1a40d0cb0d04b0cd450cc230c9540c7e10c75f0c6950c57c0b7040b5cc0b26b0a9cf09d7a09886094390917d085a107ff407dc607d7c07b9d07ad706c0305f260599005622055e1053db04eba04ba70485203f8803e9a03d7b03d12030e50303c02f5102b6f01f9601c6c01b1a010cd000bb
|9,1=>0x8f4ae8e5d68cbc38b6e38a94286ffa82d5c8245281df68130480fc67e5bf7abf87a3d77a15a79d6b7824b75d787516674de071a4170d78706a46ff706e0c76ddd26d7dd6cb486cb356c5136b4cc6b4046af7d6a6dd69e8766d8164ee95e7e15e6bb5d34f5c7c75a80b59a04591765910d5801257a995772456ede56e925412d532ad522c351edb4fdcd4f0954eebe4ece64e8ab4e3e14e27f4dfc64d3164c07f4a4f449ec949e0a48cd9482074711c469fe45cda4479b43cc243a9a42c20421d541776414f6411504090a406fc406e43f16b3f11c3db193d8613d29f3c1ef3b39c3abf63ab693aa073a6b7387393846637c8137a0437878377413760336af73638435bda34d4634a5e33414323623217631c9931b6e31b4631b293115030a9e302fe2fea32f5c32f4162ee072e46c2d05c2bedf2bb9e2b3032a7772a6bd2a376
|9,2=>0xf38d5da7f2d1483d01bdc5c2fc33d9c2ff2c2ebbbfc4abd971bd367af432aa083a242aa07d09665b963e995b0495aa99522b9302492f609202891b3e
|10,0=>0x1ce1a1ce131cc881cab51ca521c81a1c7db1c5c51c1b71bc221b3c41a98d1a5fc1a41c19e4b19ae41900418846184e4184101806817c6e17b571785f177ea1636a15e1015b2415a4414e4d14b6c1434713ddb1314d1265c1232f11a89117f711477112d310a6c10a39105bf1054b103bf103a40fb510f6a50f0090edb50ed4c0ecd30e93a0e86f0e5490e5420e3760e2270e1730d8cc0ce5a0ca540c7870c60c0c1440c0460be170b9450b54b0b2520aa470a9cc0a47c0a306097100928f090fd08ea108b4708a25089b3085a9084ab080ae07e6807d9607cd7079790794e078600785307775074730736806e91068510656405f5805d8205d4705c09059bc0585c054ed04d1304b66048e60407a03f7803b4c03870037a2032970316e02f3702b5f0247a0240e01c840180e012ce010d7010b700eda008b7005a10037c00111
|10,1=>0x5b12659873597f4595705921c57aa9576b85694155fc955e9d55442551905504154d2c549b3534fe533e552cb55151e4f7654eede4ebe14d7a74d6724d0b34c81a4be754ab2749f2e4828c47f7c4779d475f8474d8471964637444efe445e543e15439954376342a5740e3440dbf4083c400dc3eaeb3df343dea83d66b3ccfe3c85f3b6ef3b2703b2293b0de3ae753a9a639b8a39a0a3820936d1a35fcc354e6350233490433a7d326c632018318303156c30de8309022f9142f8dc2f5cb2e43c2d9982d7e62d75f2ce062c2fc2bf0b2bd562b86b2b72d2ab7a2a40b299ae28e4928c5528574284c52803927ef527a99275bd2720e267e8265dd2648c2640f257fc24e9e24cbf24be422db122543224c521e5921e0721be3217902166b20f35200ed1fb431fac51f8d41f7941eb621dc5f1dba31d7761d5821d4771d30d1ceac
|10,2=>0xf98cee8584dff72d7e22d0d5bcd78ec741fc230db6c90afe66a8215a4dfba1aaea152aa1118997d298f68922d18c1c98927a87dca8089480863804b47edbf7dd0f7ca0f7bf1a77bdb769257651a759dd72ec471c2a70f3270b906ec8e6d6196c12169b8b698f36873a6719c6701665727651dc6484d6408d604c4603e45f9c85efda5e9115c5855b5d1
|11,0=>0xf2f5ce7831da71aba73cb9dadb41029dbb29d9fc91dc18c95c7edd27b4c7770777176a6a72a668d7662fa5eba25e4015a1805849750bdf502d84ee2e4cdb14531042b6241a2c4070f3f63c3c6273c0493a11138da636fe4362c53345b3264b2f2082bfee2b8302b3d12b1ad2ab0429dba28a2e2777424a6b2404923098215681e1d61d95b1aa4f1a6ae1884618457180be13b19130ba10b7e106ef105cb0e20b0c8b80a64609e0809463092f7083860824807de907c2807b36062e7031b302dfd01f4c01703
|12,0=>0x795a9792e465c4f5146d3ec662da100eef70c075
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ee00ee00ff00ff00ee00ee0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000eeee0000eeeeffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffffffffffff00eeeeeeeeeeeeee00ffffffffffffff00eeeeeeeeeeeeee00ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000000ffff0000ffff0000eeee0000eeee0000333300003333000033330000333300003333000033330000222200002222ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
|0,1=>0xffffffff00000000ffff000000000000ffffffff00000000ffffff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0effffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff003333333333333333333333333333333333333333333333333333333333333300ffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff005555555555555555444444444444444455555555555555554444444444444444ffffffffffffffffff00ffffff00ffeeffffffffffffffffff00ffffff00ffeeffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffffffccccccccccccccccffffffffffffffffccccccccccccccccffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffffffffaaffaaffaaffaaffffffffffffffffffaaffaaffaaffaa
|0,2=>0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc0000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff00ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffffffffffeeffeeffeeffeeffffffffffffffffffeeffeeffeeffeeffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffff00ffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffff003333333333333333333333333333333333333333333333333333330033333300ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffff00ff00cccccccccc00cc00ffffffffff00ff00cccccccccc00cc00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff0000000000ffffffff0000000000ff00ee00000000ffffffff0000000000ff00eeffff0000ffff0000ffff0000ffff0000ffffffffffffff00ffffffffffffff00
|0,3=>0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaccccccccccccccccccccccccccccccccddddddddddddddddddddddddccccccccffffffffffffffffffffffffffffffffffffffffffffffffffffffffffccffccffffffffffffffffffffffffffffffffffffffffffccffccffffffffffccffccffffffffffffffffffffffffffffffffccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffffccffccffccffccffccffccffccffcc00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00ccffffffffeeeeeeeeffffff00eeeeee00ffffffffeeeeeeeeffffff00eeeeee00ffffffffffffffffffff0000ffff0000ffffffff00000000ffff000000000000ffffffffffffffffffffffffffffffffffffffffeeeeeeeeffffffffeeeeeeee0000000000000000000000000000000000ff00ff00ee00ee00ff00ff00ee00eeffffffccffffffccffffffccffffffccffffffccffffffccffffffccffffffccffffffffffffffccffffffffffffffccffffffffffffffccffffffffffffffccffffffff000000ffffffffff000000eeffffffff000000ffffffffff000000eeffff0000ffff00ffffff0000ffff00eeffff0000ffff00ffffff0000ffff00eeffffffffffffffffffccffccffccffccffffffffffffffffffccffccffccffcc
|0,4=>0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffeeeeeeee00000000000000000000000000000000ffffffffffffffffffffffffeeeeeeee00000000000000000000000000000000ffffffffeeeeeeeeffffffffeeeeeeeeffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff0000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff000000000f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f0000000000000000000000000000000000000000ffffffffffffffffffffffff0000000000ff00ff00ff00ff00ee00ee00ee00ee00ff00ff00ff00ff00ee00ee00ee00ee0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0cffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeeeffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000aaaa0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaaffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000a0a0000000000000000000000000000000011111111111111111111111100000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000
|0,5=>0xffffffffffffff00ffffffffffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00005555555555555555111111111111110055555555555555551111111111111100ff00ffffff00ffeeff00ffffff00ffeeff00ffffff00ffeeff00ffffff00ffeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeee0000000000000000ff00ffffff00ffee0000000000000000ff00ffffff00ffee00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ee00ee00000000000000000000000000000000000000ff000000ff000000ff00000000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffffff000000ff000000ff000000ff000000005555555555555555555555555555555555555555444444445555555544444444ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000333300003333000033330000333300003333000033330000330000003300ffffffffffffffffffffffffffeeffeeffffffffffffffffffffffffffeeffee00ff00ff00ff00ff00ff00ff00ee00ee00ff00ff00ff00ff00ff00ff00ee00ee
|0,6=>0x33333333333333333333333300000000555555555555555555555555555555555555555555555500555555555555550000000000000000000000000000000000ffffffffffffffffccccccccccccccccffffffffaaaaaaaaffffffffaaaaaaaaffffffffffffffffffffffffeeeeeeeeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffeeeeeeeeeeeeeeeeffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffffffffffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeee00000000000000000000000000000000ffffffffffffffffeeeeeeeeeeeeeeee3333333333333333333333333333333333333333333333332222222222222222ffffffffaaaaaaaacccccccc88888888ffffffffaaaaaaaacccccccc888888880f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00ffffffffffffffff5555555555555555ffffffffffffffff5555555544444444ffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc0f0f0f0f0f0f0f0f05050505050505050f0f0f0f0f0f0f0f05050505040404040f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0affffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000
|0,7=>0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffffffffffffffffffffffccffccffccffcc3333333333333333333333333333333333333333333333333300330033003300ffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000000000000000000000000000000000ffffffffffffffffffffff00ffffff000000000000000000000000000000000000000000ffffffff00000000ffffff0000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000ffffffffffffffffffffffffffffffffccffccffccffccffccffccffccccccccffffffffffffffffffffffffffffffff5555555555555555555555550000000055555555555555555555555500000000555555555555555555555555000000000000ffff0000ffff0000ffff0000ffff000055550000555500005555000000005555555555555555555500005555000055555555555555555555000055550000ff55ff55ff55ff55ff55ff00ff55ff00ff55ff55ff55ff55ff55ff00ff55ff00ffffffffffffffffffffccccffffccccffffffffffffffffffffccccffffcccc
|0,8=>0xffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffaaaaffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeee0000000000000000ffffffffff00ff000000000000000000ffffffffff00ff00ffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaffffffffaaaaaaaaffff0000aaaa0000ffffffffaaaaaaaaffff0000aaaa0000ffffffffffffffffffffffeeffffffeeffffffffffffffffffffffeeffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeffffffffffffffffffffffffeeeeeeee3333333333333300333333333333330033333333333333003333333333333300ffffffff00000000ffffffff00000000ffffffffffffffffffffffffeeeeeeeeffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa000000000000000033333333222222223333333322222222333333332222222233333333222222220000000000ff00ff0000000000ff00000000000000ff00ff0000000000ff0000ffffffffffffffffffffffffffffffff0000000000ff00ff0000000000ff0000ffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00
|0,9=>0x5555555555555555555555555555555555555555555555550000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f00ffffffffffffffffffffeeeeffffeeeeffffffffffffffffffffeeeeffffeeeeffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffffffffffaaaaffffaaaaffffffffffffffffffffaaaaffffaaaa00ff00ff00ff00ff00ff00aa00ff00aa00ff00ff00ff00ff00ff00aa00ff00aaffffffffff55ff55ffffffffff55ff00ffffffffff55ff55ffffffffff55ff000000ffff0000ffff0000ffee0000ffee0000ffff0000ffff0000ffee0000ffee0000555500005555000055440000554400005555000055550000554400005544ffffffffffffffff5555555555555555ffffffffffffffff555555550000000055555555555555555555555555555555555555550000000055555555000000000000ffff0000ffff00005555000055550000ffff0000ffff00005555000000000000ffee0000ffee0000ffee0000ffee0000ffee0000ffee0000ffee0000ffeeffffffff0000ffeeffffffff0000ffeeffffffff0000ffeeffffffff0000ffee00000000ffffffff00000000ffffffff00000000ffffffff00000000aaaaaaaa
|0,10=>0xaaffaaffaaffaaffaaeeaaeeaaeeaaeeaaffaaffaaffaaffaaeeaaeeaaeeaaee00ff00ff00ff00ff00cc00cc00cc00cc00ff00ff00ff00ff00cc00cc00cc00cc00000000aaffaaff00000000aaeeaaee00000000aaffaaff00000000aaeeaaee00000000ffffffff00000000cccccccc00000000ffffffff00000000ccccccccffffffffffffffffccccccccccccccccffffffff00000000cccccccc00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffcccccccc3333333333333333333333333333333333333333333333333333333300000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff00000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff000000000000000000000000000000000000ffffffffff00ff00ffffffffff00ff000000000000000000ffff0000ffff00000000000000000000ffffffffffffff0055115511551155115511550055115500551155115511551155115500551155003333333333333333333300003333000033333333333333333333000033330000ff33ff33ff33ff33ff33ff00ff33ff00ff33ff33ff33ff33ff33ff00ff33ff00ffffffffffffeeeeffffffffffffeeeeffffffffffffeeeeffffffffffffeeee1111111111111111111111001111110011111111111111111111110011111100
|0,11=>0x555500005555000055550000000000005555000055550000555500000000ffffffffffffffffffffffffffffffff0000555500005555000055550000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffff005555555555555555555555555555555555555555555555554444444444444444ffffffffffffffffffffffffffffffffffffffffffffffffccccccccccccccccffffffff55555555ffffffff55555555ffffffff55555555ffffffff4444444433333333333333333333333333333333333333330000000033333333000000000000ffff0000ffcc0000ffff0000ffcc0000ffff0000ffcc0000ffff0000ffccffffffffffccffccffffffffffccffccffffffffffccffccffffffffffccffccaaaaffffaaaaffeeaaaaffffaaaaffeeaaaaffffaaaaffeeaaaaffffaaaaffeeffffffffffffffffffffffffffffffccffffffffffffffffffffffffffffffcc00ff00ff00ee00ee00ff00ff00ee00ee00ff00ff00ee00ee00ff00ff00ee00ee3333333333333333333333330000000033333333333333333333333300000000ffffffffffffffffffffffccffffffccffffffffffffffffffffffccffffffccffffffffaaffaaffffffffffaaeeaaeeffffffffaaffaaffffffffffaaeeaaee00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00ff00ff00cc00cc
|0,12=>0xff00ff0000000000ee00ee0000000000ff00ff0000000000ee00ee0000555500005555000044440000444400005555000055550000444400004444ff00ff55ff00ff55ff00ff44ff00ff44ff00ff55ff00ff55ff00ff44ff00ff44ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffffffffffccccccccccccccccffffffffffccffccffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00000000ffffffffffffffffffffffffccccccccffffffffffffffffffffffffccccccccff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffff00ffffff0000000000000000000000000000000000ffffffffffffffffffff0000ffff0000ffffffffff00ff00ffffffffff00ff00ffffffffffffffffffffffffffffff00ffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeecccccccccccccccc0000000000000000000000ff000000ff0000000000000000000000ff0000000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000ff55ff55ff55ff55ff44ff44ff44ff44ff55ff55ff55ff55ff44ff44ff44ff441111111111111111111111111111111111111111111111110000000000000000ffffffff11111111ffffffff11111111ffffffff11111111ffffffff00000000
|0,13=>0xffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00ffffff000000000000000000ffeeffeeffeeffee0000000000000000ffeeffeeffeeffee0000ffff0000ffff0000eeee0000eeee0000ffff0000ffff0000eeee0000eeee0000000000000000ffffffccffffffcc0000000000000000ffffffccffffffccffffffff00000000ffffffffffffffccffffffff00000000ffffffffffffffccffffffffffeeffeeffffffffffeeffeeffffffffffeeffeeffffffffffeeffee0000ffff0000ffee0000ffff0000ffee0000ffff0000ffee0000ffff0000ffee0000000000000000ffffffffffffffff0000000000000000ffffaaaaffffaaaaffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffaaaa0000111100001100000011110000110000001111000011000000111100001100ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff000000000000ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff0000000000ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff000000005555555555555555555555555555555555555555555555555555000055550000ffffffff55555555ffffffff55555555ffffffff55555555ffffffff55550000
|0,14=>0xff00ffffff00ffffff00ffffff00ffffff00ffffff00ff00ff00ffffff00ff00ffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00ff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ff00000000000000ffff000000000000ffff000000000000ffff000000000000ff0000000000000000000000000000000000ffffffffffffffffffffffffaaaaaaaaccccccccccccccccccccccccccccccccffffffffffffffffffffffffeeeeeeeeffffffffffffffff3333333333333300ffffffffffffffff3333333333333300ffffffffff00ff00ffff0000ff000000ffffffffff00ff00ffff0000ff000000ffffffffffffffffffffffffffffffffffffffffff00ff00ffff0000ff000000eeeeffffeeeeffeeeeeeffffeeeeffeeeeeeffffeeeeffeeeeeeffffeeeeffee0000ffff0000eeee0000ffff0000eeee0000ffff0000eeee0000ffff0000eeeeffffffffffffffffffffffff00000000eeeeeeeeeeeeeeeeeeeeeeee0000000000330033003300330033003300330033003300330033003300330033000000000000000000000000333333333300330000000000000000003333333333003300ffffffffffffffffffffffffffffffff0000000000000000333333333300330000000000ffffffff00000000ffff000000000000ffffffff00000000ffff0000
|0,15=>0xffffffffffffffffffffff00ffffff00ffffffff00000000ffffff00000000000000000000000000000000000000000033333333222222223333333322222222ffffffffffffffff0000000000000000ffffffffffffffff3333333322222222ffffffff00ff00ffffffffff00ee00eeffffffff00ff00ffffffffff00ee00ee1111111111111111111111110000000011111111111111111111111100000000ffffffffffffffffffffffffffffffff11111111111111111111111100000000000000000000000000ff00ff00ee00ee000000000000000000ff00ff00ee00eebbbbbbbbbbbbbbaabbbbbbbbbbbbbbaabbbbbbbbbbbbbbaabbbbbbbbbbbbbbaa0000000000000000ffffffaaffffffaa0000000000000000ffffffaaffffffaaffffffff00000000ffffffffffffffaaffffffff00000000ffffffffffffffaa0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000cc00cc0033003300330033003300330033003300330033000000000033003300000000ffffffffffffffff0033003300330033ffffffffffffffff0033003300000000000000000000000000ff00ff00ff00ff000000000000000000ff00ff000000000055005500550055005500000055000000550055005500550055000000550000ccddccddccddccddccddccccccddccccccddccddccddccddccddccccccddcccc
|1,0=>0xffff0000ffff0000ffff0000ffff000000ff000000ff000000ff000000005555555555555555000055550000555555555555555555550000555500000000aaaaaaaaaaaaaaaaffffffffffaaffaaaaaaaaaaaaaaaaaaffffffffffaaffaaff00ff00ff00ff00ff00ffffff00ffffff00ff0000000000ff00ffff00000000ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaacccccccc888888880000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000000000000000ffff0000ff000000ffff0000ff000000ffff0000ff0000000000000000005555554455555544555555445555554455555544555555445555554455555544ccccccccffffffffccccccccffffffffccccccccffffffffcccccccceeeeeeeeffffffffffffffffffffffffffffffff55555555555555555555000055550000ffffffffffffffffffffffffffffffffffffffff55555555ffffffff55550000ffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00cc00ccffaaffaaffffffffffaaffaaffeeffeeffaaffaaffffffffffaaffaaffeeffee000000000000ffff000000000000ffff000000000000ffff000000000000aaaa00000000ffffffff00000000ffffeeee00000000ffffffff00000000ffffeeeeffffffffffffffff0000000000000000ffffffffffffffffffffffffffffff00
|1,1=>0xffffffffffffffffffff0000ffff00000000000000ff00ff0000000000ff00000000000000000000ffffffffffffff000000000000000000ffffffffffffff000000000000000000ffffffffffffeeee0000000000000000ffffffffffffeeeeffffffffffffffffffffffffffffffff33333333222222223333333322222222ffffffffffffffffffffffffffffffffffffffffffffffff3333333322222222ff00ff00ff00ff00ff33ff33ff33ff33ff00ff0000000000ff33ff3300000000ffffaaffffffaaffffffaaeeffffaaeeffffaaffffffaaffffffaaeeffffaaee000000000000000000000000000000000000ffff0000ffff0000ffff0000ff00ffffffffffffffffffffffaaffffffaaffffffffffffffffffffffaaffffffaa000000000000000000330033003300330000000000000000003300330000000000000000ffffffff00000000ffffffff00000000ffffff0000000000ffffff00ffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffff003333333333003300333333333300330033333333330033003333333333003300ffffbbbbffffbbaaffffbbbbffffbbaaffffbbbbffffbbaaffffbbbbffffbbaa00000000ffffffff00000000ffffffff00000000ffffffff0000000000000000ffffffffffffffffffffffffffffccccffffffffffffffffffffffffffffcccc
|1,2=>0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff000000000000ffffffff00000000ffffcccc00000000ffffffff00000000ffffccccccccffffcccceeeeccccffffcccceeeeccccffffcccceeeeccccffffcccceeee0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa00cc00ff00cc00ee00cc00ff00cc00ee00cc00ff00cc00ee00cc00ff00cc00ee0000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000ffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00ff0000330033002200220033003300220022003300330022002200330033002200225555555555555555555544445555444455555555555555555555444455554444ff55ff55ff55ff55ff55ff44ff55ff44ff55ff55ff55ff55ff55ff44ff55ff44ffffffffffffffffffffffffffffffffffffffffff00ff00cccccccccc00cc00aaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaffffaaaaaaaaffffffffffffffffaaaaffffaaaaffffffffffffffffffffaaaaffffaaaaaaaa1111111111001100111111111100110011111111110011001111111111001100ffff1111ffff1100ffff1111ffff1100ffff1111ffff1100ffff1111ffff1100000000000000000000000000ffffffff000000000000000000000000eeeeeeee
|1,3=>0xff00ffffff00ffffff00ffccff00ffccff00ffffff00ffffff00ffccff00ffccddddddddddddddddddddddddccccccccddddddddddddddddddddddddcccccccc00000000555555550000000044444444000000005555555500000000444444440000000000000000ffffffffffffffff0000000000000000ffffffff0000000000ff00ee00ff00ee00ff00ee00ff00ee00ff00ee00ff00ee00ff00ee00ff00eeffffffff00ff00eeffffffff00ff00eeffffffff00ff00eeffffffff00ff00eeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaa000000000000000000000000ffffffff000000000000000000000000ffffaaaaffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffff0000000000000000000000000000000000ffffffffffffffffffffffffffffff000055005500550055005500440055004400550055005500550055004400550044ffbbffbbffbbffbbffbbffaaffbbffaaffbbffbbffbbffbbffbbffaaffbbffaa000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000003333333333333333111111111111111133333333333333331111111100000000ffffffeeffffffeeffffffeeffffffeeffffffeeffffffeeffffffeeffffffee0f0f0f0f0f0f0f0f05050505050505050f0f0f0f0f0f0f0f0505050500000000
|1,4=>0x5555555555555555555555555555555555555555555555555555555500000000ffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa000000ff000000aa000000ff000000aa000000ff000000aa000000ff000000aabbbbbbbbbbaabbaabbbbbbbbbbaabbaabbbbbbbbbbaabbaabbbbbbbbbbaabbaa3333333333333333333333333333333333333333333333330000000000000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffff0000ffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00000000aaaaffffaaaaffaaaaaaffffaaaaffaaaaaaffffaaaaffaaaaaaffffaaaaffaaffffffffffffffff0000ffff0000aaaaffffffffffffffff0000ffff0000aaaa0000000000000000000000000000000033333333330033003333333333003300ffffffffffffffffffffffffffccffccffffffffffffffffffffffffffccffcc0000000000000000000000000000000055555555555555555555555500000000555555555555550055555555555555005555555555555500555555555555550000ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aaffff3333ffff3333ffff3333ffff0000ffff3333ffff3333ffff3333ffff00000000ffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc
|1,5=>0xffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaffffaaaa00000000000000000000000000000000ffffffffffffffffffffaaaaffffaaaaffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffff00005555555555005500555555555500550055555555550055005555555555005500ccffccffccffccffccffccffccffccffccffccffccffccffcccccccccccccccc00000000000000000000ffff0000ffff00000000000000000000ffff00000000000000000000000000000000000000000000000000000000ffffffffaaaaaaaa00000000ffffffaa00000000ffffffaa00000000ffffffaa00000000ffffffaa00000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff000000000000ff00ff0000000000ff00ff0000000000ff00ff00000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffaaaaaaaa00000000000000005555555555005500000000000000000055555555550055000000ffff0000ffff0000ffff0000aaaa0000ffff0000ffff0000ffff0000aaaaaaaaaaaaffffffffaaaaaaaaeeeeeeeeaaaaaaaaffffffffaaaaaaaaeeeeeeee00000000ffffffcc00000000ffffffcc00000000ffffffcc00000000ffffffcc0000000000000000ffffffffffffffff0000000000000000ffffff00ffffff00
|1,6=>0x333300002222000033330000222200003333000022220000333300002222ffffffffffffffffffffffffffffffff3333333333333333333333330000000033333333333333333333222233332222333333333333333333332222333322220000000000000000ffffffffffffaaaa0000000000000000ffffffffffffaaaa00000000000000000000000000000000ffffffffaaaaaaaaffffffffaaaaaaaaffff0000ffff0000ffff0000ffff0000ffffffffffffaaaaffffffffffffaaaa0000000000000000ffffffffaaaaaaaa0000000000000000ffffffffaaaaaaaaffffffffffffffffffffffffffffffff00000000ffffffff00000000cccccccc0033003300330033003300000033000000330033003300330033000000330000ffffffffffffffff5555555555005500ffffffffffffffff5555555555005500ffffffffffffffffffffffffffffffffffffffffffffaaaaffffffffffffaaaaffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff001111111111111111111111111111111111111111000000001111111100000000ccccffffccccffccccccffffccccffccccccffffccccffccccccffffccccffccffff0000ffffffffffff0000ffffccccffff0000ffffffffffff0000ffffccccffffffffffffffffffffffffffffffff00ff00ff00ff00ff00cc00cc00cc00cc
|1,7=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00ccff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffff00ff000000000055555555000000005555000000000000555555550000000055550000000000000000000000000000000000000000ffff0000ff000000ffff0000ff00ffffffffffffffffffffffffeeeeeeeeffffffffffffffffffffffffeeeeeeeeff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffff00ff00ccffccffccffccffccffccffccccccccccffccffccffccffccffccffcccccccc3333333333333333333333333333000033333333333333333333333333330000ccffccffcceecceeccffccffcceecceeccffccffcceecceeccffccffcceeccee5555555555555555555555554444444455555555555555555555555544444444aaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaaffffffffffffffff0000ffff0000ff00ffffffffffffffff0000ffff0000ff00000000000000ffff000000000000ffff000000000000ffff0000000000000000ffff00ffffff00ffffff00ffffff00ffffff00ffffff0000ffff00ffffff0000ffffffff55555555ffffffff55555555ffffffff55555555ffffffff0000000000ff00ff00ff00ff00ff00cc00ff00cc00ff00ff00ff00ff00ff00cc00ff00cc
|1,8=>0xaaaaaaaaffffffffaaaaaaaaffffaaaaaaaaaaaaffffffffaaaaaaaaffffaaaa0055005500550055005500550000000000550055005500550055005500000000
|_,_=>0
def sP:Nat→Nat
|0=>0x409c0e12030140626000204a12110141224018204607058880a0c0480010180b8542413028501208038480c050480c420004080240602824061f000200e1203024061e000200e1d090180a030e00010070d8580c05018681007090640c050480c00080c05c2c150981428080881c1a100283000080381412030783800080382c0c05050240008038180a04018080200
|1=>0x38341622028300008038480c09019080008038480c05020f806000401c243a028240639000200e38090180a0901800102a1b8180a09018b40e12028101203078d400330384844050600c00081901c24060282406000401c62120301412030002022070684c0a1401800102f0383416300280c0008178482605060b80008128480c0504890062d1501c1a29028240600
|2=>0x600010070e8480c050480cac00038480a04049541e00040600e160a84c0a14018200e1d0301412032980010070e8180a031314800080384858050480ca000041380e12030140809018009a070901408090183c000706848120325000102a2483444050480c102a0383420050602400081781c242c0280c90000401c243a030240647000202207068180a4601800102f
|3=>0x200cce001501c162b110141800040440e15098180a14018204a12030141266018b40e1d090181203328001017038342c13028500008038480c09019880008038480c090198400082f81c24050480cbc00038480c050480cba000401c245a030141203000200e12028240659000204607058180a4604800101103834260506000102f090880a24018202207090400c05
|4=>0x19e00008038480c053b0240600041000e12158880a0c018200e1203014120339800102a039c40c050480c00080b81ce012098180a09000209a07090180a040480c0007090180a0c019bc00081381c3a1203014126e000205e25090180a0c1f800d807090180a6b0480c00082001c1a16098141800041a80e160a8180a140182080070682c5605060001007090180a68
|5=>0x480c5a004308c2406028240685000200e12030141203418001007058180a09219100008038342c060291806000401c1a0b158141800040440e15030142803040a80e0b158180a0c0002104071a0480c050480c00080b81c6812030141281000200e123f0180a033e800102f038342406029180600040bc0e120301428033d0200e1203024067b001e81007090180a09
|6=>0x480d2600042440e12030141203000200e12159c40a09018001007478480c050480c00084681d1c12030141203000211a07058480c050602400081501d1806028301200040a8920d030141203000203007090180a093700010250922c0c050480c000803a282406028240600042240e12030141203000200e34090180a03440001087038480c050480c0008128480c05
|7=>0x50000102f2004856220280c102a03834560504a040600041800e120301412030027c5e07090a40c05018001007092000c0901a7400080c01d3812030141203000213607068180a140480c00082781c2406028101203000200e120301418094c800102f038480c05018685a084c01c2471030141203000200e120301412034b8001007090180a0901a580008038480c05
|8=>0x203063090141203580001007090180a0901ab400082001c165703014123f0001c1a12098141203560001007090180a095580c5a63038480c0501aa40008038480c050480d4e00041000e0d0904c0a0c0480010a5038480c050480c00081781c2a12160180a03000200e12030141203520001007092880c050600c00085081d1c12030141281000200e12030141203
|9=>0x3014180354800102f038342406028310200040a80e12158880a0c01800102f248480c0504a0406085b81c1612110141203000200e120301412b60180010b5038d024060282406000405c0e160904c0c050a0001007068480a0901ad00008150340c050480d6600040cc0eb2090180a09018001051038480c050480c0008038480c0502024aa00042c40e12030141203
|10=>0xb0180a094080d86080383424c2028240600040a80e0d400141203000218007090180a09018001007090180a0901af800081501c1a100282406000401c3a120301412035e800102f0382c242b110140600042e80e12030141203000200e120301412035c800f4180904c0a09428001007068580c050620400080c05c2a12030141281040605e0b090180a0c000200e12
|11=>0x570b40e1203014120367800102f038480c05019200008038499a060282406000413c0e12030141203000200e0b2b8180a09408b40e1203024069d000219607090180a0901800105b0384856220280c00080383424050480d9400043240e0d058180a09018001007090e80c05019f400086301c24060282406000401c240602b141203000200e12030141203620001007
|12=>0x6d81c24060282406000401c2406028240664000200e120301412036c80010362681c2406028101203001000e0d090b00a090180010d6038480c050480c0008038480c050480daa00040bc800b090180a0c000200e12030141203690001017038542413030142809043400e12030141203000205e070d8480c050600c00083001c1a0602824062d000940e12030141203
|13=>0x1e81c243a030141203000200e12110180a0901b940008150bc2a06028500608038480c05720240600041000e0d090ac0a0c018001007090180a0901b8c00081e01c247e030141203000202207090180a46018001007090180a0901b8400080384826060283146000401c24df030141203000205e07093780c0501800102f090180a24018001007470180a0901b740008
|14=>0x18b40e0d0b04c0a0c000213607068180a094080010180385424130283012000401c24060283012816182080070595c0c0504a041007090ad00051d80c0007090180a0901bb000081181c160602850120300021d407090180a09018001007090180a0901ba40008038582410030141800040940e15090180a092180c0e12738180a09018001007090180ae60480c0008
|15=>0x190400081b01c2406028101255000200e120301412f801a2000081281c24060285012033d3d80e12030141203000202e070b0540c050a00c1007090180a0901bd40008038480c050480de60004044800d030141203000202207068180a14018001007068480a0901bc800081505c1a13028240008038480c057802406000401c24ee030141203000203025090880a09
|16=>0x1281c240602824061a168600e120282406b0000200e8e090180a0901c0400088017c0e120301412030002030070b04844050600c000803bfc24060282406000405c4a12030142809018b40e120301412037e80010fc038480c050480c90000401c24060282406fa000200e1203014183b3a0001007090180a0901be400080b81c1a12158141281000200e12030140809
|17=>0x38d02406028310200040a80e0b030141243000202207068180a0c0180010072b8180a092180c8800038480c050480c0109041000e12030141203840001033038480c0501a200008038480c05838240600044140e12030141203000200e12030141203820001018178480c050a00c5a082001c1612158180a0c000200e12818180a09018001007090180a0901c080008
|18=>0xb0480c050480c00080c01c24060282406dd0002054070d8ac0a09018001007094300c050480c0008179002406028310208038341630028240600040600e16090400a0901800102a0382c6006028240600040602e16090180a09408001007090180a090190400081b01c240602824aa000401c2406028261603000204a12030141266018001007090180a0c04a540008
|19=>0x168000e06028101203070001007090180a0901c50000803c4824060282406000401c245c03014120300020c0070681412032f0001049090180a0901802231003848260602824060004060b6120981412000401c240602824070f000200e12158880a0c408200e15030141203768001007090180a0901c380008038582a130301428030401c1a1603014061a000221a07
|20=>0x2001c2c12098180a0c000200e128d0180a0901800102a20034fe050480c0008038480c05049b800081501c1a300282406000401e32120301412af018001007090180a0901c6000081781e2e12030141203000202e070685844050480c00080881c1a06028250203000200e0d058880a0c0480010183184844050480c0008038480c050480e2c00041800e0b030141203
|21=>0x384820060282406000401e2e12030141809000200e12030141325018001007090180a099180c000803c842406028240600040600e160904c0a140180010070301412430183800081181c1606028301200040604a12030142809018b40e12030141203900001007090180a0901c7c00088f01c2406028301203000223a07090180a09018001007090180a0901c6c0008
|22=>0x30141203990001007090181809019ec00082001e6212030141203000200e12030240730000200e1203014d0092180c012f0384826060283012000401c241303014120397000102f090180aab018001007090180a0901cac00081381c5012030141203000200e12948180a09018001007068480a0901ca000081781c1612158180a81000200e12930180a09018001011
|23=>0x110142803041a80e70090180a090180010180385824130283000082d81c3612030141203000227207090180a09018001007090180a0901ce000080384856060480cf600040bc0e0d090880a0c018001136038480c050480c0008038480c050480e6a000401c2534030141203000200e12030141203998001025090180a0940cb000080c01c2c12030148c03000200e12
|24=>0x282406000401c240602cf81203000213607090180a140480c0008038480c0504a04070a0408c5e12030141203000200e120301412039e800102a20048fe06028240600040600e12110141281018200e0d090c00a09018001007092000c051d82406000c05c2a12030142809018227812030141203888203017380480c050480c00089d01c2406028240600040605e12
|25=>0x38480c0504a0407110401c2406028240743000204a07090180a14048fc0600038480c050a0240742000200e12030147609019dc00081e01c24060282406000401e8212030141203000205e25091fc0c050480c00cc038480a09019dc00082001dae12030141203000200e1203014128101ae400080384a7e060282406000405c0e160a8180a0901800112f038485606
|26=>0x30141203168bc0e0d090880a09018001007090180a0901d1c00081781c2406029180600040600e12098141809000200e12030141203a30001145038480c050480c0008038480c0506025022d040bc800d090180a0901800102f0383424060285006000405c4a120301428090180010079e0480c050602406000405c0e34090180a09018001007090180a0901d100008
|27=>0x200e0d0b0880a09018001007090180a0901af00008038480c0504d3006000401c2422030141203560216e07090180a094080c00083e01c242b030141203000200e1203014280316d2c1025038480c050480c3400045280e12030141203000200e120301412035c0001149038480c050480c0008038480c0504d2006000405c0e15090ac0c050480c00080395c2422
|28=>0x1781c242b030150203000200e12110141203169e81007090180a680480c000803d402406028240600040a85e0b030141203000200e12400180a0901bb40008038480c050480e9e00045380e15090180a09018001007090180a0901d340008038480c050480c00860401c24220301412033a0200e15090180a460480c10070b0540c0504a0406082001c242b030147603
|29=>0x98141203000200e0d030141203a00001007090180a0901a200008038480c0504a0406c3041000e12110180a3b0480c10070a84856060282502030401c240602824075300020302f090180a09018b400080395c2406028240677000200e12030141203970001007090180a140480e58000401c240602826a403000200e12110180a6d0480c1007090180a0901d440008
|30=>0x203007090880a140480c1025090180a0901c4c00081281c2437030141203000205482090180a09018001007090ac0c050480dc000045540e12030141203000205417090180a094080010a103a3824060282406000401c24800301412033e800102a0382c0c05048fc0008038480c050480ea8000401c24800282406003d0214217038480c050480c00080c01c2a12
|31=>0x282406bf000200e12030141203ad0001063038480c0504a040600041000e0d091fc0a09018001159038480c050480c0008038480c0506024072a00020f812030141203004441025038480c050480da62d0001c2406028240758000200e12400180a0901d5c0008038480c050480c5a00ab020540703014120361800102a038545606028240600040a80e0b030141281
|32=>0xae81c24060282406000401c2c12030141203ae0001025038486006028240600040bc0e1203014188100020d407090180a140480c0008038342c06028300600043300e12030141809018001018038542406028301203000205e07090180a0c1f800102f038342406028300600041800e12030141203168000e1203016b6090180010110384826060282406000401c2406
|33=>0x2d881203000200f61090180a0901800105b128480c050480c00083181c242b030140600040a99212030141203000200e12030141203b000010074d04856060282406000408c0e12030141203168001007afb5c24060282406000401c2a12030141809408229207090180a09018b400082001c1a16030141203000200f5e090180a09018001007093a00c050480c0008
|34=>0x401c24ef030141203000204a070901812033d80010070b05426060282406000401c242b030141881000202e07090180a09018029608038342413028501203000200e1203014280901b0c1007090180a0901d3c5a00040a80e12098180a140480c00081790024060280d66000401c24060282406ed000204a07058480c0504a0400082481c24060282502030401c2406
|35=>0x158180a09018001007090180a0901d5c00080384844060283012810426c0e12030141281000200e12030141203b30001007140490006028240600041000e0b090880c050480c1018178542406028240600041000e8c090180a09018001007090180a09019f40008b285c0e12030141203000200e120301576030052c1018038480a090192c0008038480c050480ec600
|36=>0x2824064b000448012030141203000202207090180a14018001017128480c0504a04000803d7c240602824860300022d407090180a0901800102aa70480c050480c0008038480c050480d2a000401cae120301412030027ed207068480c050480c0008038480c050480ed000040602e12030142809018001007090180a0901d9c000803834162b028240600040a80e0b
|37=>0x18200e12098180a09428001040090180a09018022208038480c050480ede000401c240602824076e000205e07090180a0c018b4000803b202406028240600040a88012110180a09018200f3c090ac0c050480c00086601c2c12030141203000200e12030141203b6800116c038480c050480c0008b481c2c12030141203000203007638480c050480c00081281c247f
|38=>0x90180a09018013e08038480c050a024067a0401c6812110141203000205e07068480c0504a0406000401c501203014120300020f8070901812033d80010aa3181c2406028240600040a80e0b030141809000200e12030141203b80001007068180a0901ca80008038480c050a0240648000200e12030148c09019200008038480c0504a0658000401c2a12030141243
|39=>0x480c0008038480c050480ee8000401c240602824073b000203007058480c0504a0400080c0942406028501203000202207090180a0c0180010070695c0c050480c5a00038480c050480de800040a8f812030141203000200e12030141203005cc1007b90480c050480c0008038342406029181203000202e070684856050480c0008038342c0602825020300022e207
|40=>0x30141203bb0001060038480c0504a0406000401c242b030141203960001007090180a09ba80c0008038480c050480e582d000200e12030141809018b800081781c2a12030141803000200e12148180a09018001007380482606028501203000200e120301412af018001040038342422028240608038480c050480c342d040940e15090180a09018b4d4070b0480c05
|41=>0x480c0008138600e120301412030002080070901812033d80010070d9e42406028240600041000e1d090180a090180010180b8582406028240600041f00e12030141203001e81049038480c050480c5a005501c2406028240600040602e12030141281000204a07090880c050480c5a180384844050480c5a08038d024060283006000401c240602ddc1203000200e12
|42=>0x3b6024060282406000401c1612030141281168203007090180a09018029608038480c05bc82406000401c240602824071c000204607058180a09018001007090c00c050480c5a086601c2406028ec1203000200e12030142803598001025038542406028247e030001c1a16098141203000200e12030141203bc0001169038480c051d8240600042082e07090180a3b
|43=>0x48001007090180a0c0180296082001c247f030147609018008007058485606028240600040940e12030141809018b400cc0395c2406028240600043ac0e1203014120300022f607090180a090180011690395c2406028240600040bc0e12080180a0901800108d038480c050480c5a082001c1a0b030141203000208007090ac44050480c117a038480c050480c0008
|44=>0x40d80e12030140809018001007090180a091200c0008039e42a12030141203000200e9c090180a0901800105b0384826060282400080b81c240602aec1203000200e12110180a0901ae400081281c24060282406004f81c6812030141281018001007090180a0901df400080382cae06028247e001281c2406028301294000200e12030141203be00010180b8482605
|45=>0x480c5a00889000e160904c0c050480c00081281c242b030141203168000e1203014180921800111e038480c050480c00081281c242b3f81412030001c1a12158141803000205407090ac0c050600c00081501c2a130301412030002054120301412033a000102f0386c2406028240600043680e12160180a09018001007090180a0901bec0008bf01c2406028240600
|46=>0x222007090180a090180010170386c24060282406000401e781203014120316820f849038480c050480c002a200480c0504a040608038480c0504e040600040bc0e123f8180a140180010070901812033d800102a03854fe06028240600040a80e12158180a094080c0008038480c050480f0000041240e12030141809018001007090180a0901dfc0008128480c05
|47=>0x90180a0901800102f200480c050480c00081781c2406028500600041f00e12030141203168001023038480c050480c000803a6824060282406000401c240602850123f018001007090880c0504a040608038480c050480e80000401c24060282406d30002030070b0480c050480c00082001c1a12030141809018001007988480c050480c00083e01c2406028301203
|48=>0x200f3c090180a0901800112f0385424060282406000401c2406029182809018001007380542406028240600040940e12110180a0901800102a0b8480c050480c00082001c2c12030141203000200e12158880a09018001007090180abb0480c00082001c1a12030141203000200e15090180a140480c102503848fe06028240600038482606028301200040940e15
|49=>0x90180a094080c00080b8942406028240600045a40e12030141203000203007090180a3b0480c0008038480c050480e5400040a84a12030141203000200e120301412032580010400384856060282406000401c240602aec1203168001007090ac0c050600c00081281c1612030141203000200e12160180a0901800102f038480c050600c00081781c247f030141203
|50=>0x40600e0b090180a0901800106a038480c050480c0008038342406028501203000205e07090180a094080c00081781c2406028247e03000208007090180a3b0480c0008038480c053682406000401c2406028307603000200e9a0a8480c050480c0008038480c050480e58000401c2c120301412810180010cc038480c050480c00080c01c2a12030141203000200e0d
|51=>0x480d66000401c2480030141203168001007090180a0c0480c5a00041009207090180a09018001007090ac0c051d80c0008038480c050480c5c000401dae12030141203000200e12030140809018001007090400c050480c000803834240602830120300020c607090180a09018001025038480c050480d28000401c242b03014128101800114e0b81c2406028240600
|52=>0x98180a09018001018038480c050a02406000401c247f030147609018000e0b090ac0c050480c00082481c2406028240600040a80e1203014280901800107c2001c2406028240600040940f3c090180a0901800102a038480c0504a0406000405c0e12098180a09000204a07090180a0901b4c00081281c240602824062d002088007090180a09018001040038480c05
|53=>0x38480c050480c00080384856060282406000401c240602824062d000200e16090180a09018001007090180a0c0480c0008038480c050a02406000401c2406028250203000208007090180a09018001007091fc0c050480c00083e01c24060282406000401c2c12
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0x20800c40042001100008
|8,0=>0x42f220e9102c87f243e721ea90f14076643a121c880e0406e2035f21a690cf40656431b018670bec85d242d7216290acc8542428f213e909ac84b6024b011c9089c842a420320f890784039e41bd20d5906738316417920b3905548286413120908044401fe40ed206e8032c817240a7204a9021400e6406300289
|9,0=>0x231c916688a30448921fc90d688592422a20cc9042480d43fd91fac0fae87c523d991e848f1a877943b2a1d4c8e82472d438d91c248dee46e5236991b048d5a86994343919d48cc64651231f918b48c36460922fb917948ba645c122d79167c0b1e057d22b4a15550a86452f428e9142c89f244e7226a9130c8962449d4245911e488ca84550220a
|9,1=>0x35649a8e4d3526919344c1a024cef266e9332c996e8ca34648931fc98da4c5b2623a30d498428c0f25fe92fac97b24bc725da92e94172a0b8325b892d7c96968b39259392c5496064af1256f92b3495764aa9254b92a0d14de8a5d2525928ec14524a172502927cc93be89cb44dc926951326497f44b5a2564928e493344909243c91fa48eb246c9
|9,2=>0x47bca3ba51cb28dc9469ca326918128b794574a29651392892a444ca20250ef286e94325216a90a14847941f4a0d650574822940cca042500d47fca3f951fa28fbf27d693e6c9f124f7727b293d4c9e824f31078f93c349dfa0eed076d93b1d1d6a4ea3274983a049cda8e5b2724938dc9c4a4e132700937b51bb28dc906db9368d1b224d7d46b59
|9,3=>0x5a0d2ce616612b26a58ecac5256154b01957bd2bba55cb2adc9569cab2695812ab795574aa9655392a92a544caa0254ed4a6d95324a97214a72a49a5204a8da94594a22a50cca842540f29fe94faca7b253c729da94e8ca726137f49b784d74a69a133b299494c5ca60a52f1496ea4b2ca57252a9094b94a0d24de925b4924948dca44a521329009
|9,4=>0x60f5305a18194c0395fdc2fc697d12bdea5eacaf3257872bb9a5d84ae9e573d2b9595c64ae0a96f32b7095b352d7a16ab2b4ba
|10,0=>0x73b539b65cc92e5b97294b9229c7f2e35a7164b88e5c352e1197044b7fa9beb2dec96f1cb76a5ba14dc6a6decb6ce9b552da196cc4b63e5b096d7b96b8d35a25abf2d5696a6cb5125a772d31a693d34769a274d09a6804b3de59dd2ce4a66d53342998f2cbe965acb2b259454c98a647cb21698f74c7296345317e58ad2c4d9621d30ea58632c289
|10,1=>0x86b4c336618750b9a857d429a61395092a844cc20260ef306da831d416a60a15047981ed40cae053301fa80b4c03660074ffa97f8cbf9e9fbb4fd497e553f065f6f4fae97d253e6a9f232f87a7bf4bdd65ed92f62a7accbd3e9e8d2f3d9799d3ca69e412f1797874bc129df54ef197744bb7e5dab4ecba7614bae29d5d4ea5974dd3a4a5d132e809
|10,2=>0x996ccc9266355310a983ccbfa65eb32ec9971ccb6a65a152c7995f4cad2a55552a1994c4ca3aa509527b99394c9a664c13256a926cc9126477323299145487e642b520c9901cc7e6a3e131e798ef4c756639751c1a8dbd46b6a349319aa8c8cc62262ff317698b6cc58ea2b53150a8a3544f662675128b88fcc45a62195103987d4c3c661d130df9
|10,3=>0xac4cd6026aef356e9ab25556e6aa535499aa04d4daaa5b3523aa8d4d4466a0f54fcba79553a669bf54d5aa65d5306a97134af9a534d2766929348b9a414d1e668df5465aa2e4d14aa891543eaa1acd0aae84334189a07cd01a67f953f399f54cf82a7ad53cd99e24ceee676533a999d04ce5aa7195382a9bc54dbe66cd335bb9a94cd26667f53369
|10,4=>0x5e46ef11377eabbacddaeaec537599ba84dd1e6e7b57358b95d5c82ee2f370dab824dbee6de176e6ab6ecdb526d9736c29b5c55abaad4b369bab48d5a226cff3675ab364d98aacb336509b23558f2ac673629ab104d8622c1d56059afec57d26bd555dfbaead572eab8535b99ad7d5696ab393592a
|11,0=>0xcf8d679eb3bb59d49ce5ce70a737339b09cd35667673275989acbfd65d6b2d93962acac5653ab289593b9c994e4a2b23f3915ac864e40ab1f158ef9c734e372b1a738ca9c60ce2deb15b58a49c4d562467111387eac3ace1aeb0c35857ac26d6112707558319c144e07ab02b380c9c01cdfe6afe137e79beed5f526f9737c1abdc4debe6f4d379ca
|11,1=>0x6a0e74f35a6fad334e972b4a73a49ad1fd68d6b4575a229d0c5683e740b59fba
|12,0=>0xd65ceb0a75733ab09d53cea7a752b3a8c9
|13,0=>0x1ad48
|_,_=>0
def wAt:=mkWire dB 386 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x128540004903821078231b01b0201d1a01d068250304901825090190b01d04849018190304915801030250900d0481d0300d0c04b0301d018250c05000021038190002503821000b1018ad04819140270e81d0e801038210c050000250381903001018490480d0681d0304900049038190181d000250300d0a8190a00f0902509001048010902500049038190181d000250300d098010300d090250383506001
|1=>0x301d00049018192a04b1401d0e80106821090190e801068212881b1481d16001098250300d278231b0010201d06021018251b01b1b0230201d0602101825090190293225801030960382120023038010901903849030010480d0004d01819060010480d0382501849030010480d0901902916039112184b1f8010182104905200131f82501821038011e81b000f11d01d1d8190482103831068010384900021
|2=>0x34823060210480d0480d0481903849018490300100025090010b01d04849018190b8500380d04801038210002109019048490181d000250300d02992001553180f1d81d048210318213823300192b81d090212e0032d84b0601d0182503835060010b01d018250304904849018190c05003825000250381903001098010300d090252c021200772b819090210001d1b00f1b01b0201d06021018250480109025
|3=>0x211681b3e017038b500021039e60d82306801090191d9dd2001b048210001d04819018250300103801091d63a0212000f03801031c90901d01856090010300d0b0010380d090251b0230201d0602101825200ef0480d048210001d1380f0e81d06821030490481d0480d0382101821039ad3680d0a0230480109019018190001d0480d090250b81900049048010380d09019018490480d048190380134827
|4=>0x4901819248310480d2002303801198271a01d0b01904849039a123023060010480d1685c0181d0002103821038350b8270181d03049420210c0560381909001018492184b1f801018210304904849060010480d0900d048190480d090190900117849000250481d0900d01825048190901d0b8010380d0902506825030490380d01801049f5400273f801030210382503049060010480d0382500025030b6
|5=>0x30491b0010201d0602101825018254d01b0920501801000210a00f000250481d031c90185609001090a60a04d000250300d1802f048890184903001092564a00101896038214901d090b2098250300d031c9048190185609001092412181f1f8010182105825018490182501849000620301d0901d0680d090190480d0901d03049200230001d1380f0c15d0301d090210b8540380d00049038213804d0a825
|6=>0x382155027318011d81d048210c2a20a82103819090010182503801030490181900082530490c0230301d00049030310481d0182501a8a0328d0485609001018250328d0485609001018014701d0b00d090250606e01825068010901904819030010481d0001d030490000d048190901d0395d1680f0002109021038250a04d000250300d4f0174001d3f80103021470010b00d03819048490581d0480101849
|7=>0x48190480d0384903001038250180120023038011581d04819018490300101ae15b84b030bd0481d0b019048490181d000250300d0316e090190601d018250384920027030490001d1a0011a01d0b01904849038a50a04d000250300d1b00f0201d060210182503abd01ab903052048010301d3181b1d81d0482103abe01ab90305204801018490380109021018210385203049000250300d000211285000025
|8=>0x90250a81b0900101801030690a00f04801090193f8010901903849030216081d04a7e018b6000215f8212002f0900d038010004d018190901d030491401f0e80106821090190481903825018490300103af15d80f000ed0482112827030b603821000210b8270300d0301d0181d0901909025018010480d090010000d0301d0181d018250301d0900d0481d3e02701825200210001d0480d090190382501801
|9=>0x395d030490002109021038210002103052048012401f2301b060010480d0311a0481d060010480d033390a02f0900d04801200111d80d048210001d00021018010900d090214f017660212001903801468ed04821000620301d03001048190601d018253b8212001b09019038010a01d0480101849030493f0271d0013f8250302103b21638190a8230900104a191685c0380d000210a92e090010309603821
|10=>0x701fd0302103856090010481d16003098250300d0a06003819000250481d4e04b002390b00d090256e01d000d20b01904849001553180f1d81d048216d04b2d8190601d018251b0230201d06021018250001d060190480d0901903b616b8031f849018210c23b0b00d0381904849018250481d018490001d6a01b698010909603821090010181d000250300d03b4501aa20015d090210480d0481d0680109019
|11=>0x304975825410232000d0380144001118270681d0304901825098010300d0902503821000fd0900101821740210c0540381909001060b90c04b0301d01825039f91d0013f825030212d84b0601d0182500025000490481d0901d200101d80d048210001d090190480d04819038013e0af200210481903801038e91d0013f825030210b01d04849060010480d710210a062000250301d018250a8270004901819
|12=>0x48217a001032e60489603821038590001d09019048490b01d0304904801090250012e0901903096038210181d018190901d0304904bc50a84f0004901819778010334d0909603821000190301d00021038210480d0901901819048490581d0180101849030490480d0301d00049018190000d0a81b090010480d0001d018010900d090211102103001048190482103bb64004b3f80103021048010900d0681d
|13=>0xb00d090250017d118230681d03049000190480d03819048490d8940382106801090190380d0480103821000217f0010b8ef0181d048212301b060010480d7d821200330480d03801048212000f0480d038015a0032d81b0601d0182503025030490380d01801048211b00f0201d0602101825118270681d030490382100025030b6000217b81d46003098490181900049048010380d090255d8631d8010301d
|14=>0x304901825018491f801038490182103859090250304901825090212184b1f801018210c4280301d090b60002103801018d20b01904849198270c059038190484904a412181f1f8010182103c19390210185609001002c13181b1d81d048210481d000250381900021018490480d04819038015604d0a01f000250300d039122184b1f80101821000210a00f00025038211e01b0c0ed0301d048214e01f00239
|15=>0x4901819048490a00f0480109019048494680d000620301d2304b0301d060010480d0901d03025068010901912b0f0a81b0004903821038010480d03825018010a0190480101849030490301d09801018190484901849000ad048190901d018010380d0381904849200131d80d048210001d0198d3180f1d81d048210baec0a0210380d048010b85003821000250181d0480d4a00101896038210180106825
|16=>0x480d09019038191d81d00019048210a12e0480103096038212b81d0900d00021090213484b02001060210480d004550e81f068210304905c4d01849048620301d033952d84b0601d01825030493001b2b81d09021038b63e023038b5000213801d0a825000490181903819018190601d018250932a3b8212001b03801030250480d03001018011404b0a9fd09001030216a00f6980109096038210902500025
|17=>0x304900021038190002503821200121d80d048210001d0aa9b0c023000490301d118030681d03049002860b8590380d090258e001428210b8270181d018190001d0480d090255709603821030520480109019030210901d0001d1380f118210681d0304903049000ad048190901d01ab903052048016615f090212001903801002310302d0900d0380d048490300109019038590000d09019048490184903001
|18=>0x18193801f0a82500049018190481d128500002503821034b604cb10905e0181d0e8010e81d06821030493fca92004b0302103801030490b8af030250181d0900d0382503025018010349d3800f0b00109025098010b01d090250300d002310680d090190480d120210c05003819048010049101b4d090960382109489060620301d01825018190480103819048493484b218251f801018210480d0900d0681d
|19=>0x68012035d058210900d038012035e058210900d038013e017200210481903801030010481d03049018259b8236604920019038013804f0a825000490181909a8d0a82700049018193e03709019200210380103821018010905e0181d0301d04849060010480d04a564a00101896038213e0170480d2002103801038010b04d0300d0902502a564a001018960382134823218251f80101821038550182500049
|20=>0x3821035010905204801090010380d0902520049030250001d049d12000f038010b849000250181d0000d090b600021038250681d030490b8520380d04801030210901d0001d038190180103001000ad048190901916819000210482109001000250301d0181d038b63e003038b5000210301d0b0010380d0902503ced0323a0b00d0902503825000250381903001090510300d018190480d038190484903831
|21=>0x60010480d0480d0301d018190c0ef0301d04821200ad048190380100021018010480d090190481d0001d09019000250481d03821000250181d0480d00096038210b0190380d090252480f20023038010000d038b6000211180f0681d030490480103821018210b81b0380d048012001b048210001d179fd0382503021092cd200270001d0382503821030216601b2001903801058210900d038010180104896
|22=>0x1685c0380d000212000f03001038010a00d09001048010000d09001048490482104819038010484903001090195d80f000ed0482101c4d048620301d000190385204801038ad030250180120021048190380100025048b6000210a00f000250382103b1d0a823090015b84b030bd0481d3d01d030b600021018b90c04b0301d048190380d090010001900021090210481d0300109019960010905e0181d0481d
|23=>0x4801118270681d030490a81b09001018010482103001038010900103025018014104b2000d038010481d03819000212001b090210001d3801f0b001090250b84b000250181d5600d0385204801030010a023048011a01f0b0190484903825030250180100019030b60002123023060010480d0e8030682109019018490481d0901d4004b3f801030213e00f20021038011f81d09001018210685e0181d03049
|24=>0x210382103a3209849018194001f3f801030211686303819000210a81b000490901d00049048190901d038490900d0180100025038190300103821048620301d128540004903821038492000d038010481903856090010053a038fd018210901d0380d018014701d0b00d09025400273f801030210901d0184901821408620381901801031e9030b6000210b8590380d090250301d00049018190901909052
|25=>0xc05403819090019e04900096038210c00f03819048490a01900025038210480d03825018010981d000250300d0902503049018250480d20019038010480d03819090010480d03825018210481d0304901825090950002103821049e9030b6000210b01d090250300d2002f0900d038016980309096038211d81d0000d048210304903021038011685e0380d000212004b018250001d3e01f200210001d09096
|26=>0x2103049000250300d0a81b04801090013e00f038b5000210901d000250300d200270481d0001d4004b3f80103021018490382101801018012002303801048b90c04b0301d560490385204801038210601d01825038ed04819048210901d200250001d570210305204801092050302501801000210681d030496b8011f8490182100049018010480d3d01d030b6000210001d09019048494d0230920501801
|27=>0x301d0181d0a8af048190900104819018490304901849048190901d4001f3f801030210480d03001018010905d0380d0180100571018620301d400493f80103021030010900d038010481d000490301d058190900d03801400273f801030210b95d0181d0902116825048b600021b201b0c0210301d01ae604896038210334d09096038213e01700095038210902500049018190480d03025018010181d048b6
|28=>0x59821200270001d000210481d01825638190a82309001030010901d0001d0481900096038210c00103819048494d02709205018010026e018a90901d0b8030380d090250a82303819090011281b0382103021178490481d0001d17849000250481d038210380d01801218491f80101821095ad0b8230181d038fd03849018214a00101896038211680f0002109021090190005e0181d56021038520480100025
|29=>0x210912d030960382103049060010480d0181d04819090190000d09019048494f81d018b60002100025030b6000210483503001090190901903825018010d82106801090193e0172002103801318011d81d048210901d0900d0480d3801b0b001048492004b030490001d0311a0a00d048012301b060010480d018010905e0181d000fd09001018210b8270181d0300d3e01f200210001d0b85b0380d09025
|30=>0xd09021030250905e0181d01c29090b600021000210905e0181d0c04b0301d01825090010481d018250a04d000250300d0a049000250300d01ab903052048010304903001038010a00f04801000210900103821000210c00d0381904849170010c04b0301d0323a0b00d0902501801018490301d038190002503821178490481d01825030490002109021032e604896038210901d200210001d8501f090b6
|31=>0x4821200190380164827038510480109001038210182109019018190484997827200490001d048210005e0181d048210005d0181d0c15d0301d090213e01720021038010d82306801090192b819090210001d0380d03819048491681d030b6000213e023038b50002164821200250001d0000d0301d0181d03001038210002100021038190300106825030490182504d090305e0181d6480f200250001d2b81d
|32=>0x90210300d0301d0181d01825048b6000210380104821030210900d04819038010480d0382100021090212001903801410232000d03801410252000d03801090210005e0181d038250004d0300d00021000620301d090190900d038010300104819038019e01900096038216b8031f849018210000d0900d000210301d048b600021049dd2001b03801428210b8270181d0900d0681d03049000210488903001
|33=>0x382103021048190480d0901901825048190901d0901d00049018192000f0901d0001d0481d0680109019038b1098250300d200330480d038012481920023038010201d06021018250c05003819048010d8230a8190900123049060010480d018190601d018250a0210380d04801030010489603821018b60382100021090ad03025018010b8560380d09001018210900d090210480d01896038210c15f0301d
|34=>0x3801090190480d0b04d0300d090250480d200210380197825200490001d0181d06801090193e003038b500021248212002303801018010901d0001d7000d03856090010480103825030213e0172002103801090010384903021038490302501801019de2001b038010480d2002303801032ee000ed048211681f0002103821038010300d0902504819038210002140821018010480d118030681d0304903025
|35=>0x3096038210481903801048b50002103025018250184903821098250300d0481d018250382503021000960382103855090010a00d04801048550900103821030010181d0901d03801090250481903001000ed04821090190380109001048010382103021018250300d00049038210481d0001d000250481d038b5000210681d03049092050180104801018210300101801090520480109096038210381904849
|36=>0x30b500021000210480d200230380104819048210c04b0301d1f84901821060210480d0004d0300d090190480d1d81d04821018960382103025018010b8210181d018490301d0981d0300d048010901903825018010382501821048210001d0a02304801048210182501855090010905e0181d01801090252001903801038190900101801090190181d038210005e0181d0301d048212004b0001d038210901d
|37=>0x481900021090250480d0480101801038010302120021038010300d09025038190480104821030210900d048192002303801000250901d2002103801000960382103849018010181d0300d090960382103821000212000d03801200270001d
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x560023000000020000
|8,0=>0xca50c640c150bd40b850b350ae500000a950a45000009f5000009b400000992094508f508c30875082507d507850762071506c50675062505d505a3000000000582053504e504950445042203d503a3036400000000032402e402950245021301e3019501540105000000000000000000b50000
|9,0=>0x1c741c341bf41bb41b741b341af41ab41a741a3419f419b41974193418f418b41874183417f417b417741734170316c416841644160415c415841562152414e414a41464142413e413a41364132412e412a41264122411e411a41164112410f310b4107410340ff40fb40f740f340ef40eb40e740e340df40db40d740d340cf4
|9,1=>0x2c442c042bc42b842b442b042ac42a842a442a0429c429842944290428c428842844280427c427842744270426c426842644260425c425842544250424c424842444240423c423842344230422c422842244220421c421842144210420c42084204420041fc41f841f441f041ef11eb41e741e341df41db41d741d341cf41cb4
|9,2=>0x3be43ba43b643b243ae43aa43a643a2439e439a43964392438e438a43864382437e437a43764372436e436a43673363435f435b435743561352434f334b43474343433f433b43374333432f432b43274323431f431b43174313430f430b4307430342ff42fb42f742f342ef42eb42e742e342e032dc42d842d442d042cc42c84
|9,3=>0x4bb44b744b344af44ab44a744a3449f449b44974493448f448b44874483447f447b447744734470346c446844644460445c445844544451344d444a34464442443e443a44364432442e442a44264422441e441a44164412440e440a4406440243fe43fa43f643f243ee43ea43e643e243de43da43d643d243ce43ca43c643c24
|9,4=>0x5174513450f450b45074505250144ff24fb44f744f344ef44eb44e744e344df44db44d744d344cf44cb44c744c344bf4
|10,0=>0x5d835d535d235cf35cc35c935c635c335c035bd35ba35b735b435b135ae35ab35a835a535a2359f359c3599359635933590358d358a358735843581357e357b357835753572356f356c3569356635633560355d355a355735543551354e354b354835453542353f353c3539353635333530352d352a352735243521351e351b3
|10,1=>0x69836953692368f368c3689368636833680367d367a367736743671366e366b366836653662365f365c3659365636533650364d364a364736443641363e363b363836353632362f362c3629362636233620361d361a361736143611360e360b36083605360235ff35fc35f935f635f335f035ed35ea35e735e435e135de35db3
|10,2=>0x75837553752374f374c3749374637433740373d373a373737343731372e372b372837253722371f371c3719371637133710370d370a37073704370136fe36fb36f836f536f236ef36ec36e936e636e336e036dd36da36d736d436d136ce36cb36c836c536c236bf36bc36b936b636b336b036ad36aa36a736a436a1369e369b3
|10,3=>0x81838153812380f380c380938063803380037fd37fa37f737f437f137ee37eb37e837e537e237df37dc37d937d637d337d037cd37ca37c737c437c137be37bb37b837b537b237af37ac37a937a637a337a0379d379a379737943791378e378b378837853782377f377c3779377637733770376d376a376737643761375e375b3
|10,4=>0x8bd38ba38b738b438b138ae38ab38a838a538a2389f389c3899389638933890388d388a388738843881387e387b387838753872386f386c3869386638633860385d385a385738543851384e384b384838453842383f383c3839383638333830382d382a382738243821381e381b3
|11,0=>0x93e293c293a29382936293429322930292e292c292a29282926292429222920291e291c291a29182916291429122910290e290c290a2908290629042902290028fe28fc28fa28f828f628f428f228f028ee28ec28ea28e828e628e428e228e028de28dc28da28d828d628d428d228d028ce28cc28ca28c828c628c428c228c02
|11,1=>0x95c295a29582956295429522950294e294c294a294829462944294229402
|12,0=>0x96519641963196219611960195f195e1
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 16
def pmP:Nat→Nat
|0=>0x9006c00000000000000001200c000000000000000002401300000000000000000480020000000000000000089022000000000000000010016000000000000000002002400000000000000000400440000000000000000080040000000000000000010005000000000000000002000400000000000000000400040000000000000000080000000000000000000003f9e40000000000000000060080000000000000000008042000000000000000001008000000000000000000200180000000000000000040010000000000000000008000000000000000000000800000000000000000000080100000000000000000010010000000000000000000100000000000000000000010800000000000000000001e00000000000000000000300000000000000000000020000000000000000000003000000000000000000000180000000000000000000008000000000000000000000
|1=>0x42bb8f200000000000000085761e4000000000000001082614800000000000000205c8790000000000000003e290f200000000000000049721e400000000000000082e43c8000000000000000d5c879000000000000000120000000000000000000021721e4000000000000000424029000000000000000084800000000000000000008900ac0000000000000001120018000000000000000220023000000000000000040004600000000000000008000180000000000000000950024000000000000000104011000000000000000015c87900000000000000001b10f2000000000000000020000000000000000000003e418000000000000000005d87900000000000000000b90f200000000000000001719e400000000000000002e23e800000000000000005c17d00000000000000000b10f600000000000000001601e4000000000000000024028000000000000000004804c
|2=>0x2208b80fa00000000000004403701e400000000000008802e03c80000000000001002dc87b00000000000002000bbcf200000000000003105701e400000000000005302e43c800000000000008805c84900000000000001083b80f200000000000002021701e400000000000004002e43c8000000000000050d0401100000000000000a00b80f200000000000001203741e400000000000002026f07e80000000000000400dc079000000000000008019810a00000000000000c000000000000000000001202e43c800000000000001105e07d00000000000000220b80f2000000000000004200013800000000000000822e43c800000000000001005c87900000000000000108980da000000000000002002000000000000000000302e428800000000000000605c849000000000000000c00989200000000000000103621e400000000000000202e43c800000000000000405c079
|3=>0x11000b90f200000000000021511701f40000000000004280ae03c80000000000008500cc07900000000000010450b98f200000000000020001721e400000000000040002c43e80000000000008000000010000000000001000000000000000000000184410000000000000000030082002700000000000006010400060000000000000a220b80f200000000000014409301ec00000000000020882703e800000000000041005e87900000000000008020bc0fa00000000000010041701e400000000000020048000c000000000000024405c07900000000000004202b80f200000000000008141701e400000000000010202e43c800000000000020405c07900000000000004080980f20000000000000802001000000000000000100400011000000000000020015c079000000000000030042d00200000000000005403701e400000000000008882e03c80000000000001104ce0fd
|4=>0x44220800ac00000000000088005721e400000000000100c926037800000000000200925ca7b00000000000040003b90f200000000000080007701e40000000000010000ae43c800000000000182085c879000000000000210c0b90f200000000000042085721e400000000000082006e93c800000000000100605cc4900000000000020042b985200000000000040049739e400000000000080062e724800000000000100055ca2900000000000020008b18f20000000000004000a159a400000000000080002cd3c80000000000010000588790000000000002000089cf200000000000034405381f40000000000006800af03e8000000000000c90d4407900000000000018400b90f2000000000000304317a1f400000000000060822442e8000000000000c0015c07900000000000011a9ab80f200000000000022601721e400000000000044a62e43c8000000000000890cde8fd
|5=>0x1000009000000000000000200001000e0000000000003440b2e43e800000000000688005c87f000000000000b1008b50f2000000000001220136a1e400000000000244002f43c800000000000488005ca7900000000000091000b10f200000000000120001701f400000000000208282e03c800000000000408905c879000000000000810482905200000000000101101701e400000000000200402e43c800000000000400804c82800000000000080042a90d2000000000001000132a2fc00000000000200002e63c800000000000400005c8790000000000006a001980f2000000000000c4001721e40000000000018010ae63c800000000000300025c87900000000000060000b90f2000000000000c0001621e400000000000154c1ae03d800000000000228615c07900000000000044a018000c000000000000894010007800000000000112006402700000000000022400c0006
|6=>0x21022c980da000000000004022b5621e40000000000080452ae43c800000000001008275c829000000000002003009a0f2000000000004004412817800000000000800402e53c800000000001000805c87900000000000200100b80f200000000000400041661e40000000000080004ae03d80000000000100000000320000000000019300abd0fa000000000003220a17a1e40000000000060e202f03c800000000000c10015e87d00000000000181000b90f200000000000300104181e400000000000600202e03c800000000000c00005cc7900000000000121019b7dfa000000000002400316f9f400000000000480022e43c800000000000810405c0790000000000010200493076000000000002021017a1e400000000000404102c43c800000000000800285fe7900000000000100050bb8f200000000000200001731e400000000000400002400d0000000000008000048002
|7=>0x2000000b84f200000000004000000730c400000000006000002e43c800000000009200a15cc79000000000012001c0b98f200000000002300001721e400000000004480002e514800000000008001805c87900000000001000000b90f2000000000016000a1731e400000000002800202e43c800000000004a04084207c00000000000920004b98f200000000001204219661ec00000000002408032c43d800000000004800028804200000000000900000b90f20000000000120000132000000000000024000024000000000000004480005c47d0000000000086004eb9cf200000000001080000000b0000000000020c0042e63c8000000000041082f5ce7900000000000820800000a000000000001000801721e400000000002000002e43c800000000004000000004c00000000000780040b80f200000000000920001701f400000000000c00402c43c8000000000018000048000
|8=>0x3800000b90f200000000006002201729e40000000000c000412e73c800000000018000815c27900000000002a01146b9cf20000000000540028d739e40000000000a80040ae53c800000000014c30425d07900000000002980040b90f2000000000052c4011621e40000000000a108026545c800000000014050124c07900000000002802004bb4f200000000005000001729e40000000000a000002e43c800000000014000005c27900000000002800000b80fa000000000042420336a3f40000000000824c012f43f800000000010488805ca7900000000002091100b90f200000000004102001729e400000000008200002e43c800000000010114005c07900000000002022000b90f200000000004040401719e400000000008020012e13f800000000010010825ca7b00000000002000100b94f200000000004000201709e400000000008000002e63c800000000010000005c879
|9=>0x4220318b90f600000000008440601709ec000000000108808265429800000000021040905d279000000000042010c0980e200000000008401400341e400000000010800c92e03d800000000021001825c07b00000000004200301bb4f200000000008400601769e400000000010800c02e53c8000000000210010c5c87900000000004200120ba4f200000000008400031721e400000000010800004683c800000000021000000000a000000000041000209408c00000000008044603301ec00000000010088c02e03d800000000020101005de7900000000004011308b90fe0000000000800a185701e400000000010008806603d80000000002001000dc07b00000000004002000b80f200000000008002181721e400000000010004022e424800000000020001105c07900000000004000020b80f2000000000080000112009800000000010000006e43d800000000020000005c079
|10=>0xe800000390a20000000001c0100217a14400000000038000002e33c800000000061001805ca790000000000c000010bb8a200000000010060821721e400000000020081042e624800000000040100005c87900000000008011218b90f2000000000100221217a1e400000000020041042ec3c800000000040040005e879000000000080014c0b90f200000000010000411721e400000000020000022e43c800000000040000000ce4900000000007808000b94f20000000000d010001729e400000000018080802e73c80000000002d000085ce7900000000004a10016b88f600000000009400009701ec00000000012408022403f000000000024800000006e0000000000481c010b80f200000000009030021721e400000000012020042f43c800000000024020405c87900000000004801080b90a2000000000090000217a1e400000000010c000a2e03e800000000021800104a05e
|11=>0x108008000b90f20000000020d010001729e400000000412041042f43c800000000820040005c85100000000102808410bd0a200000000205004009729e40000000040800401ae43c800000000804000405c87900000000100180000bd04200000000200022085621e400000000300000000683c800000000414120405887900000000082820000b50f2000000001040900000018000000000200c00482dc3c800000000400900205c87900000000080100040bb0f200000000100186011621fc00000000200204482dc3e800000000400020015c879000000000800008000048000000000100000001701f400000000200000002783a800000000200000005d87900000000020080000b90f2000000000400200000010000000000050c02072e03e8000000000a000500cc07b00000000014000804b80f200000000021205009381d40000000004200000262368000000000800000000084
|12=>0x10001e0024b9cf200000002000300009721e4000000040002000020020000000008000000205c87900000000803000104b9cf200000001004000209739e400000002002c00012e33c800000004000c08145c87900000000800120008b98f2000000010002040097a0c400000002000400002fe3c800000004000410005e83100000000800081000bd0f200000001000000011721e400000002000000002e43c800000002094000005c77900000000402820000b90f200000000805000001701e400000001000508092541d800000002000300005c07900000000400060000980f200000000800044249721ec0000000080c004402653c800000001010220005887900000000202011106b84f200000000404000201729e400000000800244022c43c800000001000488004ca7900000000200082000b9062000000004000060017a0c400000000800000402e43c800000001000000005c879
|13=>0x8000244210900f000000010000400631661e400000020000800406cc3c800000040000b00405c47900000008000100800be8fa0000001000008c401001f800000020000080006cf3c800000040000084095c07900000008000004080b90f200000010000001401341e4000000200000020000016000000040000001084805800000008000000080b90f200000008100000201721e400000010200000002e03c800000020001000a058c7900000004000020801024b000000008000040003679e400000010000080002c63c800000020000004000044000000002000084000000040000000400000800100050000000080000100020002000000010000005105c17900000002000000908982da00000003000240001730a400000006000200082e43c80000000c000400005c87900000001102902000bd06200000002005700209739e400000004008001402e53c800000008004000005c879
|14=>0x40000000100b80f200000050408000001729e4000000a0800050402e43c800000140000070005c07d00000028000001000b90f200000040504028001721e400000080018204602e13c800000100014020405c87900000020002005000b90f600000040000000801721e400000080000000402e424800000100000000005c879000000200000000000900200000020040008001701e4000000400001d224ae23c800000080000084415c079000000100000058a2b80b200000020000008005701e40000004000000620ee03c80000008000000020800080000000c080020020bb4f200000018000000001741e400000020200400002fc3c800000040400000005d87900000008008010490bb8f20000001000c0320017a1fc00000020012624302f43c800000040024808605e87900000008004200800ba0f2000000100081021017a1ec0000002000a4a4302d43c8000000400018201000078
|15=>0x1000000120028b945200002000000040001731e400004000000080002e43c800008000000001805c87900001000000000100b90f200002000000000001721e400002000000010002e03c800004000000000005c07900000400008000200a9092000008000000208011000400001000000005002a4048000011010100a1005887b00000220200010200b90f200000440000000001721e400000800a00200002e43e800001001000080005c87d00000200080042001b10f6000004001000800000000000000800200000406c43d800001000400000005c07d000002000000c0020b90f200000400000122011621f4000008000001000000000800001000000088005c87d000002000000000109000000000224000001441705f400000440000010002e03c800000800021280155c07d00000100000044002b90f200000200000082021721e400000400000000042e03c800000404010000825c279
|16=>0x8001000001400b90f200010002000000881671e400020004000001002e43c800040008000000205c87900008001000000000b90f200010001000302001721e400020000010841002e43c800040000001083285c87900008000000180000b90f2000100000002000a1721e40002000000020410ae43c800040000000400005c87900008000000011210b90f200010000000022021721e400020000000040802e424800040000000080005c87900008000000000040b90f200010000000000001721e400020000000000002e418800020040024050404e07500004008000000080b90f2000080002040008013214400010000002404102e43c800018002000000001ca3100001001000380120b90f200002001000400209729e400004000020080002e73c800008000008100805ce7900001000001020020b94f200002000002000001721e400004000000841c42e43c8000080000010018c5c879
|17=>0x100002000002221b80f20020000400000404b721ec00400008000000086041c80080000000002000400040008002000001e800b80fa00100004000020001701e40020000800002a802703e800208000008488205ce7900041000001010490b98f200082000002002181711e40010400000400010ae23c800208000008000005c47900041000001000000b80f200080001005000009729e40010000040c020002e43c800200000810c88285e87900040000102002000b90f200080000018000001779e4001000000280000006428800200000014c10015e87900040000002800080b90f200080000000000001721e4000c0000000000802e43c000100000010488805ca7900020000000091000b90f200040000000000041f21e000080000000000002e43c800080000000000005c87900008001000280004b90f2000100020003000c1721e400020004000005102e43c80004000800000a2059879
|18=>0x201400008000200b80f200402400000522011621e400804000004080002e73c801008000000100805c87900201000000020000b9cf200400800010000c01721e400801000020000802e43c8010020000400000044849002002200040010801009000400400400100201721e400800800000000402e43c801000008000c00145c87900200000800200124b94f200400001000400209729e400800002000000002e43c8010000000210820c5c87900200000000291008b101200400000000400101721e40080000000010441ae43c801000000000200825ca7900200000000040002b90f200400000000040181739e400800000000040802e424801000000000008215c87900200000000000200b90f200400000000000041721e400800000000000022e43c80080080000008820408b100100002004002021b80f600200004008000443301ec00400008000208286e03c800800010000400005c879
|19=>0x2000000200040000b90f2040000004000060032a0fc0800000000a11000ae43c810000000010088835c07b02000000002000000b90f2040000000000a0005701e404200000040000002603d808000040000000005ca7901000000004208100bbcf202000000008010201779e404000000000840042ee3c808000000001001004c27901000000000200100b94f201080000000000001721e402000800800000002e43c804001001000000005c07900800008200004100b10f201000010000002201621f402000020000000402dd3c804000040000000205f87900800000302080000b90f2010000005000320017a1f402000000000400002e43c804000000000000004000400580002000000000b82f200808004000810403623e4010100000000000024041002000010000040009885b00400000000400000b80fa00800000000102183623e401000000000000002e03c801010000000000101c839
|20=>0x180060000000000001f21e4c4100000420020002e43c888200000060000005ce7910000028108018000b90f220000000210010001721e440000000400004302e43c880000000010000005c8790a000000900082000b90f210080001000000009739e42000000040000410ae43c840000000010000005c879040000040000000000002008000000100040001701e410000000000000402e43c814001141000200005c87902800220200001000b90f205000040400002201621e40a000000000208002e43c81000100000120803d887b02000020202020100b14f204000001000004001721e408000000808318002e43c810000001000284025c27f
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x601c0000800
|8,0=>0x28c031d8460800f10c00078190001b000040000213c3b01c011e01a0042a004011e02918c0a020000243204401004020484e034000000c04c540f40a02c2e03806000000000023800
|9,0=>0xb1b62b5a70e2643847a159f66a90019085400be8a83168da6094476307a5fa250f0df60d72982691060e4c58b658f7601622fc307e8b073d294ec881612236925041e17b81e38a7e300ff7ddec2cd6a5fce722e4f0f0a23941635cdb995df2f52f82961780653a9d39d0919a1106387a091751e8371b63960976114267ca3d0da363382857d2e1cccb1c5ab07208075ff470c22b09d1e96905e587559d55de7
|9,1=>0x6b0c97e4ee4006707db1582790b0e6190215748a24c7a0a04a315d62819c650796368b9ec2f3c1481c8dc8397b97cac749f85dd895ac832b1393f900254ab7306531d9c4ad14054184c1d47d441112119095e1822d0b23c9107a9c8ac240743b101564af0d0ed0d4ef2504105180924e3304777d9663e50f6e43c838ae4560d345ca6811b18a0c6d13a5f253404e4750235915b0b1e57a42d3282727cb13813d
|9,2=>0x191e016633a0661f0021e87a89833155b135d0950cd41ea296a624541b5
|10,0=>0x2edfd4f22ca55368d1ef9e09e8589a67d347445e295bf5485f8c202145da87650a08f57d10c8823a6663572571514eb9221e708d61edc499a06550d566e626e0aa59dc39313375cdd9adb05d0e92a2405051da268c21a321fdc71a1b3a012c4de46171fb738f3790b4810989b1e23e9ce7017a3c5d84fc7d264bc4d56e45897862419c54c2d95a6f25633e6f66187a4e1963dbd5b5f07054f34d7064d4b62a52
|10,1=>0x2721ca414e3f1f11348924a4da0d5518a6e93a57a362844e8f15d1c618b84a9a246a3f335e85f46a47e2b1adbe641afa2904814c47367d98547258808be0e2e4fd85d2d2d5288ce038f94944a28978706ca814193e5122e1b10c6dd818016843622a1273824420fa1a2e90e49a9482d5684231321fe291c81cc6f331387167aa390537a3b362919761583a1b89c52490fb421cb408f461511519de78dad20654
|10,2=>0x1ba99c822dd186858471a7565e96655409c1f37ee38286075711769461131bb9a8f2799dd9fe5a5b05b3647e92a238de435bd7f84c2c168f8944758057976d0a5e165465dc
|11,0=>0x10b140a99446ea217343221508b287cf676686669fca1e4627a9296563176458492354c84741074c951954a791e761a5219f03f49c591024b620d2851eb96c4b21da81259283e6d535ae678c67b43a97285235a414cc37a88f40cd09dd58528a68749b
|12,0=>0xe4270ac482312008991
|13,0=>0x22
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 10 (j%128);fld (pmP (k/32)) 87 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_251 12 roots_251 ops++addP pm 1 dzo_173_64 6 roots_173 ops++addP pm 2 dzo_214_32 6 roots_214 ops++addP pm 3 dom_253 11 roots_253 ops++addP pm 4 dom_239 11 roots_239 ops++addP pm 5 dom_247 11 roots_247 ops++addP pm 6 dom_254 11 roots_254 ops++addP pm 7 dom_205 7 roots_205 ops++addP pm 8 dom_244 6 roots_244 ops++addP pm 9 dzo_191_64 8 roots_191 ops++addP pm 10 dzo_159_64 7 roots_159 ops++addP pm 11 dom_109 8 roots_109 ops++addP pm 12 dom_175 8 roots_175 ops++addP pm 13 dom_207 9 roots_207 ops++addP pm 14 dom_118 8 roots_118 ops++addP pm 15 dom_191 11 roots_191 ops++addP pm 16 dom_127 11 roots_127 ops++addP pm 17 dzo_211_32 6 roots_211 ops++addP pm 18 dom_223 11 roots_223 ops++addP pm 19 dom_237 9 roots_237 ops++addP pm 20 dom_215 8 roots_215 ops++addP pm 21 dom_183 9 roots_183 ops++addP pm 22 dom_221 9 roots_221 ops++addP pm 23 dzo_158_32 6 roots_158 ops++addP pm 24 dom_245 9 roots_245 ops++addP pm 25 dzo_159_32 7 roots_159 ops++addP pm 26 dom_222 8 roots_222 ops++addP pm 27 dzo_189_64 7 roots_189 ops++addP pm 28 dom_252 9 roots_252 ops++addP pm 29 dom_94 6 roots_94 ops++addP pm 30 dom_246 9 roots_246 ops++addP pm 31 dzo_223_32 8 roots_223 ops++addP pm 32 dom_231 9 roots_231 ops++addP pm 33 dom_150 5 roots_150 ops++addP pm 34 dom_238 9 roots_238 ops++addP pm 35 dzo_222_32 7 roots_222 ops++addP pm 36 dom_189 8 roots_189 ops++addP pm 37 dom_149 5 roots_149 ops++addP pm 38 dzo_215_32 7 roots_215 ops++addP pm 39 dzo_151_32 6 roots_151 ops++addP pm 40 dzo_157_64 6 roots_157 ops++addP pm 41 dom_204 4 roots_204 ops++addP pm 42 dzo_143_64 6 roots_143 ops++addP pm 43 dom_63 7 roots_63 ops++addP pm 44 dzo_175_64 7 roots_175 ops++addP pm 45 dom_190 9 roots_190 ops++addP pm 46 dom_126 9 roots_126 ops++addP pm 47 dom_182 7 roots_182 ops++addP pm 48 dom_199 5 roots_199 ops++addP pm 49 dom_167 5 roots_167 ops++addP pm 50 dom_141 5 roots_141 ops++addP pm 51 dom_111 9 roots_111 ops++addP pm 52 dom_159 7 roots_159 ops++addP pm 53 dom_181 6 roots_181 ops++addP pm 54 dom_119 9 roots_119 ops++addP pm 55 dom_87 6 roots_87 ops++addP pm 56 dom_228 5 roots_228 ops++addP pm 57 dom_173 6 roots_173 ops++addP pm 58 dom_142 5 roots_142 ops++addP pm 59 dom_214 6 roots_214 ops++addP pm 60 dom_158 6 roots_158 ops++addP pm 61 dom_166 4 roots_166 ops++addP pm 62 dzo_187_64 7 roots_187 ops++addP pm 63 dom_213 6 roots_213 ops++addP pm 64 dom_157 6 roots_157 ops++addP pm 65 dom_124 6 roots_124 ops++addP pm 66 dom_220 5 roots_220 ops++addP pm 67 dom_61 6 roots_61 ops++addP pm 68 dom_117 6 roots_117 ops++addP pm 69 dom_206 6 roots_206 ops++addP pm 70 dom_95 7 roots_95 ops++addP pm 71 dzo_218_32 6 roots_218 ops++addP pm 72 dzo_219_32 7 roots_219 ops++addP pm 73 dom_47 6 roots_47 ops++addP pm 74 dom_230 6 roots_230 ops++addP pm 75 dom_229 6 roots_229 ops++addP pm 76 dom_125 9 roots_125 ops++addP pm 77 dom_236 6 roots_236 ops++addP pm 78 dom_143 6 roots_143 ops++addP pm 79 dom_174 6 roots_174 ops++addP pm 80 dom_151 6 roots_151 ops++addP pm 81 dom_188 5 roots_188 ops++addP pm 82 dom_103 6 roots_103 ops++addP pm 83 dom_110 6 roots_110 ops++addP pm 84 dom_46 4 roots_46 ops++addP pm 85 dzo_185_64 6 roots_185 ops++addP pm 86 dzo_171_64 6 roots_171 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54|h55|h56|h57|h58|h59|h60|h61|h62|h63|h64|h65|h66|h67|h68|h69|h70|h71|h72|h73|h74|h75|h76|h77|h78|h79|h80|h81|h82|h83|h84|h85|h86
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_173_64_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_214_32_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_191_64_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_159_64_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_211_32_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_158_32_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_159_32_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_189_64_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_223_32_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_222_32_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_215_32_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_zo_151_32_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_157_64_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_zo_143_64_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_zo_175_64_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h52;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h53;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h54;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h55;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h56;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h57;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h58;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h59;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h60;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h61;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h62;exact cpcs (by decide +kernel) lowS_zo_187_64_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h63;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h64;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h65;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h66;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h67;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h68;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h69;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h70;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h71;exact cpcs (by decide +kernel) lowS_zo_218_32_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h72;exact cpcs (by decide +kernel) lowS_zo_219_32_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h73;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h74;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h75;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h76;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h77;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h78;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h79;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h80;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h81;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h82;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h83;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h84;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h85;exact cpcs (by decide +kernel) lowS_zo_185_64_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h86;exact cpcs (by decide +kernel) lowS_zo_171_64_137 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_251 12 s (0,roots_251.map (·&&&dom_251)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_251 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 58 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 58 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 256 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_256 : ∀ i, 256 ≤ i → i < 280 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 256 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 280 → Z 9 i = true := (range_split z9_0 (range_split z9_128 z9_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 256 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_256 : ∀ i, 256 ≤ i → i < 311 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 55 256 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 311 → Z 10 i = true := (range_split z10_0 (range_split z10_128 z10_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 79 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 79 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 8 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 8 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [2, 4] }, { op := GateOp.or, inputs := [0, 3] }, { op := GateOp.or, inputs := [1, 8] }, { op := GateOp.or, inputs := [9, 10] }, { op := GateOp.and, inputs := [7, 11] }, { op := GateOp.or, inputs := [2, 6] }, { op := GateOp.or, inputs := [13, 9] }, { op := GateOp.and, inputs := [5, 14] }, { op := GateOp.and, inputs := [6, 10] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [3, 4] }, { op := GateOp.and, inputs := [17, 18] }, { op := GateOp.or, inputs := [12, 15] }, { op := GateOp.or, inputs := [20, 16] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52382_aux

theorem PEqualNP.Outside.L_meta_52382 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52382_aux.main
