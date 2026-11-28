import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_51622_aux
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

def dom_74 : Nat := 0x5050000000000000505
def goal_74 : Nat := 0xffccffccffccffcccc00cc00cc00cc00ffccffccffccffcccc00cc00cc00cc00
def roots_74 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffeeffeeffeeffeeee00ee00ee00ee00ffeeffeeffeeffeeee00ee00ee00ee00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_78 : Nat := 0x55550000000000005555
def goal_78 : Nat := 0xfffcfffcfffcfffccc00cc00cc00cc00fffcfffcfffcfffccc00cc00cc00cc00
def roots_78 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfffefffefffefffeee00ee00ee00ee00fffefffefffefffeee00ee00ee00ee00
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_81 : Nat := 0x300030000000000030003
def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffeeeeffffeeeeaaaa0000aaaa0000ffffeeeeffffeeeeaaaa0000aaaa0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_84 : Nat := 0x1100110000000000110011
def goal_84 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_84 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffffafafffffafafafa0000fafa0000fffffafafffffafafafa0000fafa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffffcfcfffffcfcf0f00000f0f00000fffffcfcfffffcfcf0f00000f0f00000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffefefffffefefafa0000fafa0000fffffefefffffefefafa0000fafa0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffffaaffffffaaaaaaaa00aaaaaa00ffffffaaffffffaaaaaaaa00aaaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffffccffffffcccc00cc00cc00cc00ffffffccffffffcccc00cc00cc00cc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffeeffffffeeeeaaee00eeaaee00ffffffeeffffffeeeeaaee00eeaaee00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfffffff0fffffff0f0f00000f0f00000fffffff0fffffff0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffffafffffffafafaaa00fafaaa00fffffffafffffffafafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffffcfffffffcfcf0cc00fcf0cc00fffffffcfffffffcfcf0cc00fcf0cc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffffefffffffefefaee00fefaee00fffffffefffffffefefaee00fefaee00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffaaffaaffaaffaaffaaffaaaa00aa00ffaaffaaffaaffaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccffccffccffccffcccc00cc00ffccffccffccffccffccffcccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeffeeffeeffeeffeeee00ee00ffeeffeeffeeffeeffeeffeeee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffafffafffafffafffaaa00aa00fffafffafffafffafffafffaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfffcfffcfffcfffccc00cc00fffcfffcfffcfffcfffcfffccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefffefffefffefffeee00ee00fffefffefffefffefffefffeee00ee00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffaaaaffffaaaaaaaaaaaaaaaa0000ffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffccccffffcccccccccccc00000000ffffccccffffcccccccccccc00000000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffeeeeeeeeeeeeaaaa0000ffffeeeeffffeeeeeeeeeeeeaaaa0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffff0f0fffff0f0f0f0f0f0f0f00000fffff0f0fffff0f0f0f0f0f0f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafafffffafafafafafafafa0000fffffafafffffafafafafafafafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcfffffcfcfcfcfcfcf0f00000fffffcfcfffffcfcfcfcfcfcf0f00000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefefffffefefefefefefafa0000fffffefefffffefefefefefefafa0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffff00ffffff00ff00ff0000000000ffffff00ffffff00ff00ff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffffaaffaaffaaaaaaaa00ffffffaaffffffaaffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffffccffccffcccc00cc00ffffffccffffffccffccffcccc00cc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffffeeffeeffeeeeaaee00ffffffeeffffffeeffeeffeeeeaaee00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0fffffff0fff0fff0f0f00000fffffff0fffffff0fff0fff0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffffafffafffafafaaa00fffffffafffffffafffafffafafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcfffffffcfffcfffcfcf0cc00fffffffcfffffffcfffcfffcfcf0cc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffffefffefffefefaee00fffffffefffffffefffefffefefaee00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfafafafafafafafafafafafafafafafaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfefefefefefefefefefefefefefefefeee00ee00ee00ee00ee00ee00ee00ee00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_145 : Nat := 0x3000300000000000000000000000000030003
def goal_145 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_145 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 7 0]

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

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffccccffffccccffffccccffffcccccc00cc00cc00cc00cc00cc00cc00cc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeaaee00eeaaee00eeaaee00eeaaee00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffafafffffafafffffafafffffafafafaaa00fafaaa00fafaaa00fafaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcf0cc00fcf0cc00fcf0cc00fcf0cc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffefefffffefefffffefefffffefefefaee00fefaee00fefaee00fefaee00
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

def dom_164 : Nat := 0x110000001100000000000000000000001100000011
def goal_164 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_164 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

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
def goal_169 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffccccccccffffffffccccccccffccffcccc00cc00ffccffcccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeffeeffeeee00ee00ffeeffeeee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0fff0fff000000000fff0fff000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffafafafafffffffffafafafafffafffaaa00aa00fffafffaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfffcfffccc00cc00fffcfffccc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffefefefefffffffffefefefefffefffeee00ee00fffefffeee00ee00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffffaaaaffffffffffffaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffffffccccffffffffffffcccccccccccc00000000cccccccc00000000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

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

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffffffffff0000ffffffffffff0000ff00ff0000000000ff00ff0000000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffaaaaffffffffffffaaaaffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffccccffffffffffffccccffccffcccc00cc00ffccffcccc00cc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffeeeeffffffffffffeeeeffeeffeeeeaaee00ffeeffeeeeaaee00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fff0fff0f0f00000fff0fff0f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffafafffffffffffffafafffafffafafaaa00fffafffafafaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfffcfffcfcf0cc00fffcfffcfcf0cc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffefefffffffffffffefefffefffefefaee00fffefffefefaee00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffaaffaaffaaffaaaaaaaaaaaaaaaaaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffccffccffccffccccccccccccccccccffccffccffccffcccc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeeeeeeeeeeeeeeeeeffeeffeeffeeffeeee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffefefefefefefefefefffefffefffefffeee00ee00ee00ee00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeaaaa0000aaaa0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefffffefefffffefefffffefefffffefefafa0000fafa0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffff00ffffff00ffff0000ffff0000ffffff00ffffff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffffaaaaffffaaaaffffffaaffffffaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffffccccffffccccffffffccffffffcccc00cc00cc00cc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffeeeeffffeeeeffffffeeffffffeeeeaaee00eeaaee00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcfffffcfcfffffcfcfffffffcfffffffcfcf0cc00fcf0cc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffffefefffffefefffffffefffffffefefaee00fefaee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffccccccccffffffffcccccccccccccccccccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefefffffffffefefefefefefefefefefefefefefefe00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffff00ff00ffffffff00000000ff00ff00ff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffaaaaaaaaffaaffaaffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffccccccccffccffccffccffccffccffcccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffeeeeeeeeffeeffeeffeeffeeffeeffeeee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffafffffffffafafafafffafffafffafffafffafffaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcfffffffffcfcfcfcfffcfffcfffcfffcfffcfffccc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffffffffefefefefffefffefffefffefffefffeee00ee00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffff0000ffffffffffff0000ffff0000ffff00000000000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffaaaaffffffffffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffccccffffffffffffccccffffccccffffcccccccccccc00000000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffffffffffeeeeffffeeeeffffeeeeeeeeeeeeaaaa0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfffffcfcfffffcfcfcfcfcfcf0f00000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffffffffffefefffffefefffffefefefefefefafa0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffff00ffffffffffff0000ffffff00ffffff00ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffffffffaaaaffffffaaffffffaaffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffffffffccccffffffccffffffccffccffcccc00cc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffffeeeeffffffeeffffffeeffeeffeeeeaaee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffff0fffffffffffff0f0fffffff0fffffff0fff0fff0f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffffffffafafffffffafffffffafffafffafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffffffffcfcfffffffcfffffffcfffcfffcfcf0cc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffffffffefefffffffefffffffefffefffefefaee00
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
def isoMvS_74:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_74:Lower true dom_74 roots_74 goal_74 4:=lower_iso_b isoMvS_74 (by decide +kernel) lowS_41
def isoMvS_81:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_41
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_41
def isoMvS_145:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_145:Lower true dom_145 roots_145 goal_145 4:=lower_iso_b isoMvS_145 (by decide +kernel) lowS_41
def isoMvS_148:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_148:Lower true dom_148 roots_148 goal_148 4:=lower_iso_b isoMvS_148 (by decide +kernel) lowS_41
def isoMvS_161:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_161:Lower true dom_161 roots_161 goal_161 4:=lower_iso_b isoMvS_161 (by decide +kernel) lowS_41
def isoMvS_162:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_162:Lower true dom_162 roots_162 goal_162 4:=lower_iso_b isoMvS_162 (by decide +kernel) lowS_41
def isoMvS_164:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_164:Lower true dom_164 roots_164 goal_164 4:=lower_iso_b isoMvS_164 (by decide +kernel) lowS_41
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
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_43
def isoMvS_78:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_78:Lower true dom_78 roots_78 goal_78 5:=lower_iso_b isoMvS_78 (by decide +kernel) lowS_45
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_45
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_43
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_45
def isoMvS_89:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_43
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_45
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 5:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_45
def isoMvS_105:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_43
def isoMvS_106:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_43
def isoMvS_113:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_45
def isoMvS_114:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 4:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_27
def isoMvS_116:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_45
def isoMvS_120:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 4:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_27
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 4:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_27
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_45
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_43
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_45
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_45
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 4:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_27
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_43
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 5:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_43
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_43
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 5:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_43
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_43
def isoMvS_172:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 5:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_45
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_43
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_45
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 4:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_27
def isoMvS_201:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_45
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_45
def isoMvS_209:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 5:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_43
def isoMvS_216:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 4:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_27
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 5:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_45
def isoMvS_226:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_45
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 4:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_27
def isoMvS_240:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_240:Lower true dom_240 roots_240 goal_240 4:=lower_iso_b isoMvS_240 (by decide +kernel) lowS_27
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
|0=>0xf9c80
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x16
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_46 5 roots_46 ops++addP pm 1 dzo_46_16 5 roots_46 ops++addP pm 2 dom_60 4 roots_60 ops++addP pm 3 dom_42 4 roots_42 ops++addP pm 4 dom_54 4 roots_54 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_62 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_46_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_60 _ g hchk
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
namespace S_91
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,10),(2,66),(3,11),(3,19),(3,67),(8,9),(8,10),(8,72),(16,17),(16,80),(18,19),(18,26),(18,82),(24,25),(24,26),(24,88),(64,65),(64,66),(64,72),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_91.map (·&&&dom_91)
def gM:=goal_91&&&dom_91
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x9f8ac
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0000000000000f0f0000f000f00000000000f000f00c0c0c0c000000000c0c0c0ca0a0a0a000000000a0a0a0af0f0f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 92 0xfffffffffffffffffffffff
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
addP pm 0 dom_90 5 roots_90 ops++addP pm 1 dom_89 5 roots_89 ops++addP pm 2 dom_83 5 roots_83 ops++addP pm 3 dom_75 5 roots_75 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_91 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_75 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_90 5 s (0,roots_90.map (·&&&dom_90)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_91 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_90 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_91==dom_91)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_91 gM v ys):RunD true dom_91 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_91 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_91 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
|0=>0xffddad48c183080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x2407350010
|6,0=>0x8689
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_92 5 roots_92 ops++addP pm 1 dom_84 4 roots_84 ops++addP pm 2 dom_78 5 roots_78 ops++addP pm 3 dom_90 5 roots_90 ops++addP pm 4 dom_74 4 roots_74 ops++addP pm 5 dom_86 5 roots_86 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_94 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_74 _ g hchk
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
theorem lowS_107:Lower true dom_107 roots_107 goal_107 6:=lower_slice_b [(0xa0a00000a0a00000a0a00000a0a,8,9)] (by decide +kernel) lowS_106
theorem lowS_109:Lower true dom_109 roots_109 goal_109 6:=lower_slice_b [(0x3030000030300000303000003030,32,36)] (by decide +kernel) lowS_105
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_slice_b [(0xaa000000aa0000000000000000000000aa000000aa,32,33)] (by decide +kernel) lowS_166
namespace S_248
def pG:List (Nat×Nat):=[(8,40),(8,72),(16,80),(16,144),(24,56),(24,88),(24,152),(32,40),(32,160),(48,56),(48,112),(48,176),(64,72),(64,80),(96,104),(96,112),(96,224),(128,144),(128,160),(136,152),(136,168),(136,200),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_248.map (·&&&dom_248)
def gM:=goal_248&&&dom_248
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x444be13ef4
|5,0=>0x61e7347128255d6
|6,0=>0x47128
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x101010101010101010001000100010001010101010101010100010001000100808080808080808080808080000000008080808080808080808080800000004040404000000000404040400000000040404040000000004040404000000000002020000020200000202000002020000020200000202000000000000000101000001010000010100000101000001010000010100000101000001010000800080008000800080008000800080008000800080008000800080008000804040404000000000404040400000000040004000000000004000400000000020202020202020200000000000000000202020202020202000000000000000101010101010101010101010101010100000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x64310648310643107643106315043210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x156414a6
|6,0=>0x1b5
|_,_=>0
def wAt:=mkWire dB 9 249 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
|5,0=>0x12
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_240 4 roots_240 ops++addP pm 1 dom_216 4 roots_216 ops++addP pm 2 dom_184 4 roots_184 ops++addP pm 3 dom_120 4 roots_120 ops++addP pm 4 dom_232 4 roots_232 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_248 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_232 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_240 4 s (0,roots_240.map (·&&&dom_240)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_248 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_240 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_248==dom_248)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_248 gM v ys):RunD true dom_248 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_248 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_248 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_248 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_248 roots_248 goal_248 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_248
theorem lowS_248:Lower true dom_248 roots_248 goal_248 7:=S_248.noCircuit
def isoMvS_79:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_79:Lower true dom_79 roots_79 goal_79 6:=lower_iso_b isoMvS_79 (by decide +kernel) lowS_47
def isoMvS_87:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_iso_b isoMvS_87 (by decide +kernel) lowS_47
def isoMvS_93:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 7:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_91
def isoMvS_110:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_109
def isoMvS_115:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 6:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_61
def isoMvS_117:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_109
def isoMvS_118:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 6:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_61
def isoMvS_121:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 7:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_91
def isoMvS_122:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_59
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 6:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_61
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 5:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_55
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_47
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 6:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_61
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 7:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_59
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 7:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_62
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 6:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_107
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 7:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_91
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 7:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_91
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_91
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 6:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_107
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 7:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_91
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 7:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_91
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_59
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 7:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_59
def isoMvS_203:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 6:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_109
def isoMvS_211:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 6:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_109
def isoMvS_217:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 7:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_91
def isoMvS_218:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 6:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_61
def isoMvS_227:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 6:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_109
def isoMvS_230:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 6:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_109
def isoMvS_233:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 7:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_91
def isoMvS_234:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 7:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_91
def isoMvS_241:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 7:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_91
def isoMvS_242:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 6:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_61
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
|0,1=>0xccccccccffccffcc00000000ff00ff00ffff3333ffff000000ff00ff00000000ff000000ffff0000cc00cc00ff00ff000000000033003300ffccffccccccccccffffffff33003300ffffffffccccccccffccffccffccffcc00000000ffccffcccccccccccc00cc00ccccccccccccccccff00ff0000000000ffffffffffff0000
|0,2=>0xfff0fff0f0f0f0f000ff0000ffff0000ffffffffffccffcc00cc00ccccccccccffffff00ffff0000ffff00ffffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x48150b0ca0920591160ca0920440d80815c328204d1160d508140a0920541031c24842c32822040c248114b0ca0880c24811440d108118b0ca0811902ca08118b0cf08130b2820463840c204d30b0ca2481031c21830811400c20461440c2040
|1=>0xca0920464042ca09204309205c78b0ca0811902ca09205e2e12824812e02824815cb0ca09204b0ca09f4812c360a08158b0d52820442ca09204e2c33ca09204b28248139e2c31ca09210328248134b74a09204b29b09204b0ca0926812c3282
|2=>0xca09204d2c354a09204b0ca09205c2c32824813102d528248110b0ca0930502ca09204c10b0ca0920440d109204b0ca0930442c35424812c394a4812ca0920648cb0ca09204b0d509205e10b0ca0811842c309204c2c32820622c328204d30b
|3=>0xb0ca0920562c328248110b0ca09204b0ca09205e40b2824812c329109204b28248138b
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
|0=>0xb492ca4b2a2c34b282c38b4b2924b2b292cb0d2c34b292ca04482ca4b294424b280d1cb282ca8b292ca514a2ca0b2a2cac44b2ca43452ca03712cad1492ca0b294414b282ca43352d2c3732caca372ca51492ca4b282ca51052ca4b284c144482ca44472ca4b28
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xa30009100063000000cc03000000000000000
|6,0=>0x301002f1002d2acaa1a0a62002519063184800000007c9d2001b26480000172001610000050931448f238400000d1
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xfafe9c3301bee2082e027edf97ad2044510409003a4c93043b088200680e00c0200400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xc070104228c0000000
|6,0=>0x711a9541f09018d67800dc0589500181380ccc16980007
|7,0=>0x27ad477295f77
|8,0=>0xb
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_62 7 roots_62 ops++addP pm 1 dom_29 4 roots_29 ops++addP pm 2 dom_54 4 roots_54 ops++addP pm 3 dom_59 7 roots_59 ops++addP pm 4 dom_45 5 roots_45 ops++addP pm 5 dom_61 6 roots_61 ops++addP pm 6 dzo_47_16 6 roots_47 ops++addP pm 7 dom_47 6 roots_47 ops++addP pm 8 dom_31 5 roots_31 ops++addP pm 9 dom_55 5 roots_55 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_63 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_55 _ g hchk
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
theorem lowS_95:Lower true dom_95 roots_95 goal_95 9:=lower_slice_b [(0xaaaaaaaa00000000aaaaaaaa,8,9)] (by decide +kernel) lowS_94
theorem lowS_111:Lower true dom_111 roots_111 goal_111 7:=lower_slice_b [(0xaaaa0000aaaa0000aaaa0000aaaa,8,9)] (by decide +kernel) lowS_110
theorem lowS_119:Lower true dom_119 roots_119 goal_119 7:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_118
def dzo_107_16:=0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16:=0xf0f00000f0f00000f0e00000e0a0000
def gsh_107_16:=0xf0f00000f0f00000f0e00000e0a
theorem lowS_zo_107_16_42:Lower true dzo_107_16 roots_107 gzo_107_16 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_16) [(dom_107,16)] (by decide +kernel) (lower_slice_b (T:=gsh_107_16) [(0xa0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_42)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,10),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,10),(8,40),(8,72),(16,17),(16,80),(18,19),(18,26),(18,50),(18,82),(24,25),(24,26),(24,56),(24,88),(32,33),(32,34),(32,40),(48,49),(48,50),(48,56),(48,112),(64,65),(64,66),(64,72),(64,80),(96,97),(96,98),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|7=>2
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x300161b678
|8,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f000f0f0f000f0f0f000f0f0f00f0f00000f0f00000f0f00000f0f0000f0f0f0f000000000f0f0f0f00000000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00f0000000f0000000f0000000f0000f0f0f0f0f0f0f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2e8d0be342c688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xcc06
|8,0=>0xc6
|_,_=>0
def wAt:=mkWire dB 8 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xd1d3
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x441
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 6
def pmP:Nat→Nat
|0=>0x1fdf80
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>5
|8,0=>2
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_121 7 roots_121 ops++addP pm 2 dom_59 7 roots_59 ops++addP pm 3 dom_91 7 roots_91 ops++addP pm 4 dom_115 6 roots_115 ops++addP pm 5 dom_107 6 roots_107 ops++addP pm 6 dzo_107_16 6 roots_107 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_107_16_42 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 7 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
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
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(4,20),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(8,9),(8,40),(8,72),(12,13),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,56),(24,88),(32,33),(32,36),(32,40),(48,49),(48,52),(48,56),(48,112),(64,65),(64,68),(64,72),(64,80),(96,97),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|5=>3
|6=>5
|7=>4
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xcd8f4ace6f76423
|6,0=>0x393fc37917204bc0406700ecb
|7,0=>0xb324d8e2268d60a53413
|8,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x33333300333333003333330033333300cccc8888cccc8888cccc8888cccc888b3333333333333333300330033003300cccccccccccccccccccccccccc00cc030303030303030303030303030303030888888888888888888888888888888880003333000033330000323200003232cccccccc00000000cccccccc000000033333333333333333333333322222222cccccccccccccccc00000000000000033333333333333333333333300000000cccc0000cccc0000cccc0000cccc00033003300330033003300330033003300c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8cb3333333333333332222222222222222
|_,_=>0
def sP:Nat→Nat
|0=>0x732a95732195732a0957e32a957d32a9543c2a96432a95432195b432a95432a0972198564321543210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x2d82b005
|6,0=>0x2b648e798bb916
|7,0=>0x8ccfddc3b17
|8,0=>0x4c6
|_,_=>0
def wAt:=mkWire dB 15 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2a5954c939495755d5756a5755d5955d5
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x100
|6,0=>0x7261423112
|7,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x9fd5ed57d2801fd016006000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>8
|6,0=>0x64e5
|7,0=>0xedb
|8,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 7 roots_121 ops++addP pm 1 dom_92 5 roots_92 ops++addP pm 2 dom_116 5 roots_116 ops++addP pm 3 dom_61 6 roots_61 ops++addP pm 4 dom_124 6 roots_124 ops++addP pm 5 dom_109 6 roots_109 ops++addP pm 6 dom_93 7 roots_93 ops++addP pm 7 dom_117 6 roots_117 ops++addP pm 8 dom_45 5 roots_45 ops++addP pm 9 dom_85 5 roots_85 ops++addP pm 10 dom_29 4 roots_29 ops++addP pm 11 dom_120 4 roots_120 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_120 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 7 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_125==dom_125)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_125 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_slice_b [(0x55555555000000005555555500000000,2,34)] (by decide +kernel) lowS_94
theorem lowS_175:Lower true dom_175 roots_175 goal_175 8:=lower_slice_b [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,8,9)] (by decide +kernel) lowS_174
def dzo_148_8:=0x1100110000000000000000000000000011001100
def gzo_148_8:=0x1100100000000000000000000000000010000000
def gsh_148_8:=0x11001000000000000000000000000000100000
theorem lowS_zo_148_8_148:Lower true dzo_148_8 roots_148 gzo_148_8 4:=lower_iso_b (d1:=dom_148) (r1:=roots_148) (T1:=gsh_148_8) [(dom_148,8)] (by decide +kernel) (lower_slice_b (T:=gsh_148_8) [] (by decide +kernel) lowS_148)
def dzo_180_8:=0x110011001100110000000000000000001100110011001100
def gzo_180_8:=0x110011001100100000000000000000001100110010000000
def gsh_180_8:=0x1100110011001000000000000000000011001100100000
theorem lowS_zo_180_8_148:Lower true dzo_180_8 roots_180 gzo_180_8 5:=lower_iso_b (d1:=dom_180) (r1:=roots_180) (T1:=gsh_180_8) [(dom_180,8)] (by decide +kernel) (lower_slice_b (T:=gsh_180_8) [(0x1100110000000000000000000000000011001100000000,0,32)] (by decide +kernel) lowS_148)
def dzo_42_16:=0x505000005050000
def gzo_42_16:=0x504000004000000
def gsh_42_16:=0x50400000400
theorem lowS_zo_42_16_42:Lower true dzo_42_16 roots_42 gzo_42_16 4:=lower_iso_b (d1:=dom_42) (r1:=roots_42) (T1:=gsh_42_16) [(dom_42,16)] (by decide +kernel) (lower_slice_b (T:=gsh_42_16) [] (by decide +kernel) lowS_42)
def dzo_182_8:=0x550055005500550000000000000000005500550055005500
def gzo_182_8:=0x550055005500540000000000000000005500550054004400
def gsh_182_8:=0x5500550055005400000000000000000055005500540044
theorem lowS_zo_182_8_148:Lower true dzo_182_8 roots_182 gzo_182_8 6:=lower_iso_b (d1:=dom_182) (r1:=roots_182) (T1:=gsh_182_8) [(dom_182,8)] (by decide +kernel) (lower_slice_b (T:=gsh_182_8) [(0x4400440044004400000000000000000044004400440044,0,2),(0x5500550000000000000000000000000055005500000000,0,32)] (by decide +kernel) lowS_148)
def dzo_174_16:=0x555500005555000000000000000000005555000055550000
def gzo_174_16:=0x555500005555000000000000000000005554000054500000
def gsh_174_16:=0x55550000555500000000000000000000555400005450
theorem lowS_zo_174_16_42:Lower true dzo_174_16 roots_174 gzo_174_16 6:=lower_iso_b (d1:=dom_174) (r1:=roots_174) (T1:=gsh_174_16) [(dom_174,16)] (by decide +kernel) (lower_slice_b (T:=gsh_174_16) [(0x50500000505000000000000000000000505000005050,0,4),(0x55550000555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_150_8:=0x5500550000000000000000000000000055005500
def gzo_150_8:=0x5500540000000000000000000000000054004400
def gsh_150_8:=0x55005400000000000000000000000000540044
theorem lowS_zo_150_8_148:Lower true dzo_150_8 roots_150 gzo_150_8 5:=lower_iso_b (d1:=dom_150) (r1:=roots_150) (T1:=gsh_150_8) [(dom_150,8)] (by decide +kernel) (lower_slice_b (T:=gsh_150_8) [(0x44004400000000000000000000000000440044,0,2)] (by decide +kernel) lowS_148)
def dzo_170_16:=0x50500000505000000000000000000000505000005050000
def gzo_170_16:=0x50500000505000000000000000000000504000004000000
def gsh_170_16:=0x5050000050500000000000000000000050400000400
theorem lowS_zo_170_16_42:Lower true dzo_170_16 roots_170 gzo_170_16 5:=lower_iso_b (d1:=dom_170) (r1:=roots_170) (T1:=gsh_170_16) [(dom_170,16)] (by decide +kernel) (lower_slice_b (T:=gsh_170_16) [(0x5050000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
namespace S_190
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,130),(4,20),(4,36),(4,132),(6,14),(6,22),(6,38),(6,134),(8,10),(8,40),(12,14),(12,28),(12,44),(12,140),(16,20),(16,144),(18,22),(18,26),(18,50),(18,146),(24,26),(24,28),(24,56),(24,152),(32,34),(32,36),(32,40),(32,160),(48,50),(48,52),(48,56),(48,176),(128,130),(128,132),(128,144),(128,160),(136,138),(136,140),(136,152),(136,168)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_190.map (·&&&dom_190)
def gM:=goal_190&&&dom_190
def NN:Nat→Nat
|4=>7
|5=>18
|6=>46
|7=>36
|8=>12
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xdd266b8b3a75ac05c23c4bf992b4a01cf19
|5,0=>0xf488ad8a07aeee0911857a02e73ada7314a6d2cc69b9f69aec4274e3d1c933e272f3b81ce5518abc0862d08107
|6,0=>0xd6a21d0923d0213cd58cb8223b39d6ad858ab103a133a9b3619809b96d6e94e0d9447d807b17fd9c75079706aa6f67d6ed61698575d9965c78d5ac4659804590915515a5480a52fc2415fe392493820633c5b276e42474622ebc1942b165b014bb10c6750b9200ab3a05d0005a0702888005e7
|7,0=>0xf7d54d9556d72c4d48cbc7791bc458b80a1a07a985f1d8579e8418b801a27bf79781326cd5b667bf61ad75c09f52f9d516df4dc724380e2ea112dc612cc532cbc923b0522bd92218c1582312df8116b70aefd094af044eb01cc4
|8,0=>0xf79e0ddffdd48b9b9ce6b0c04788b7766075c5ff27715202fd1b6a708f02
|9,0=>0xf79e0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaa000000000000000000000000aaaaaaaa00000001555555555555555400000000000000015541554151415142aaaaaaaaaaaaaaa80000000000000002a802a8022002200555555555555555500000000000000005555555500000000a8a8a8a8a8a8a8a80000000000000000a8a8a8a8a8a8a8a9555555554141414000000000000000011111111101010102aaaaaaaaaaa800000000000000000002aaaaaaaa8280000505050505050505000000000000000005050505050505050888888888888888800000000000000008888888888888888015401540110011000000000000000000154015401100112aaaaaaaaaaaaaaa80000000000000000000000000000000555555555050505000000000000000005555555550505050aaaa0000aaaa00000000000000000000aaaa0000aaaa0001540154015401540000000000000000015401540154015402a2a2a2a2a2a2a2a00000000000000002a2a2a2a00000000555555555555555500000000000000004444444444444444
|0,1=>0xa0a0a0a00000000000000000000000008080809555555555555555400000000000000015555555511111112aaaaaaaaaaaaaaa80000000000000002aaaaaaaa8282828555555555454545400000000000000005555555554545454aaaaaaaaaaaaaaaa0000000000000000aa00aa00aa00aa00141414141414141400000000000000001414141400000000888888888080808000000000000000008888888880808085555555555555555000000000000000054545454545454540000aaaa0000aaaa00000000000000000000a0a00000a0a155555555555511100000000000000001555555555151111028282828282828280000000000000000280028002000200550055004400440000000000000000005500550044004400aaaa0000aaaa00000000000000000000a0a00000a0a0000155555555555555540000000000000001414141414141414002a802a802a80220000000000000000002a802a802a0022555555554444444400000000000000005555555544444444
|0,2=>0xa8a8a8a941414141555555540000000000000001414141415151515000000002aaaaaaa8000000000000000000000002222222245454545454545450000000000000000454545454444444400000000000000000000000000000000a8a8a8a8a8a8a8a9555555555401540000000000000000015555555554015402aaaa8282aaaa82800000000000000002aaaa8282aaaa828555555555555555500000000000000000055005500440044aaaaaaaaaaaa00000000000000000000aaaaaaaaaaaa0000000000000000000000000000000000015555555551515152aaaaaaa8282828280000000000000002aaaaaaa8202020205050505050505050000000000000000050505050404040400000000a8a8a8a8000000000000000000000000a8a8a8a844444444444444440000000000000000444444440000000008080808080808080000000000000000080808080000000050505050505050500000000000000000404040404040404
|0,3=>0x2aaaa2222aaaa22200000000000000002aaaa2222aaaa22255555500555555000000000000000000555555005555550000000000aaaa0000000000000000000000000000aaaa0000000000000000000000000000000000015555555541414142aaaaaaaaaaaaaaa80000000000000002aa82aa82aa82aa855555555555555550000000000000000555500005555000000000000000000000000000000000000aa00aa00aa00aa00444444444444000000000000000000004444444444440002aaaaaaaaaaaaaaa80000000000000002aaaaaaaaa2a2a2a555555555555555500000000000000000000000054545454
|_,_=>0
def sP:Nat→Nat
|0=>0x881ca10c0db1da40c0c260810c0c22c03030921d93c308b28510c0c26073d42075c53c334b21624220715030308b48f0cd20754f0d42d21500c20481440c20471493c22c71500c20522481d11494022c53c338d2cc0c22ca2481c61440c2040
|1=>0x3c30881e414f0c22008c53c22d31c530f0db20768c3c30880223c30881e114c3c30881e03c33481cc3c308b2003c30881df14c3c309820710c0db2073c34881c615e3c308b20574f0c21da15c3c30880053c36cb2003c81c65c52500881c5303
|2=>0x8b22d15030309220710f0c22c014f0c248764540c0c222214f0d44881c53c3088b071493c220715030308b20540f0c2ac816a3c22075c53e90c81c61677040881c540c0c22003c3207a059de3022071503c308b48598f0c22071653c30881c5
|3=>0x30f0db20710f0f320714c3c30881e214f0c2207c8540fa430881c53c30881da1503c308b20530f0c22c81c510c0c22001f13c30881c53c30881ca14f0c22008859cc6c81cf0c2207c053c30881ef14f0c20481c53c30ae2071503c30982053c3
|4=>0x3db207dc574f0c22071503c308800578f0c22001c53f3207dc574c3c30881c570f0c22071503f40c22071763c30881c53c3d4220714f0c260800714f0c220764530f0c24881cf0c81c61443c36c81c59cf08b20716a3f40c22071673c2207c85
|5=>0x881c53c3cc81c53f40c220714f0db0881c510f0c220714fa430881c53f80c220714f0c22c81c59cf0881c510f0c22001c59cf6c81c53c36c80073c3ccb2071443030881c53c308b2001503c309220714f0884c714f0c2ac81c570f0c22c81c5
|6=>0xf0c220714f0c220714c3c30881c53c309220714fe43
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x1e5065414503d40a50154005
|5,0=>0x22188261f187661c186a619185e61618526135447610583b60d582f60a58236
|6,0=>0x6fddb876c5daa769559e765dd907625d8275edd7475b5d66757dd587545d4b6511d3d74d9d2f74a1d2264719157439d077401cf973c9cec6395cde735dcd0732d4c472f5cb672c18a97289c9b7251c8e6
|7,0=>0xafa2b86ac9aab7a91e9d7a5628f6a21e8089e9a7379b1e648979a56893de478901e3978c622a788de1d6859e0f781e20077e99f377ae1e477721d57739dc68
|8,0=>0xc45b0a7c0defc7bd9aef7ba1ee17b69ed37b31ec66
|9,0=>0x3176
|_,_=>0
def wAt:=mkWire dB 58 191 0x7fffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1cf4f150cf4815705cb3f1c8481d0d20815308c53d0854c1f3c540231c54551090073d00847153c5421520f42421cf50151cf453d107483d20745091c54815100071520f521d205521d205481d15442401cf4f4d0d208152054551090073d1484c2c1c84c2c1c84f4d0d208152054d21
|1=>0x20f481d0cf4f090c5671f0cf453d085421720f4c1f3c5671f0cf43211cf4c2314f47211cf481d3c55c1510744001c5483d00f4f0d14f42152cfcc2c2074f1500fc0211c5403f1c54815307c53d14842401cf4c233d343482054b171c8520f205500b1cf4f0d20f451d14f473d1854242
|2=>0x3c548150c742170c5421520f43210c2481d0cf471520f42150cf45091c5481d085cf1520f47211c54f1d20543482054b172074b3d1c8433f085441520f473d1c5403d1c54f0e085cc2114f441d20f450d1cf441720f424920540211c5441f20f4f1520542421cf4215
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11001000000000
|5,0=>0x1c11930001720000000001520001140e30d10a3091072052023
|6,0=>0x6726436316035f10005c35b15925725610000005425135014d30004b24924724524233f33d23c13b10000003923633333120002f22c30000002a22732522322212021d3
|7,0=>0xaf2ad2ab2a92a72a52a32a129f29d29b29929729529329128f28d28b28928728528328127f27d27b27927727527327126f26d26b2692
|8,0=>0xbb1ba1b91b81b71b61b51b41b31b21b11
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x3374000c88000300000085d0002140000819000202000080400020000004910000f140000980000224000088000020000004d0000120000044000010400003700000d40000180000048000010000003400000c0000020000004000000c0000020000004000000
|1=>0x203050080c1001d65d404107701041d403db7d00e69d403587d00d017003187500c39500299fd00a4dd402757900879d40218f500843dc01557d0054df401537500449d400737d00145d40040440008f3400208d00080240012f500041dc00107500041c4001000
|2=>0x203d17540a4dd480d02011249dc40801308a41dc20802306847f418008d048f5c4121d7504846f4121175040b0440b1c7502c61d40b107502c01500a11fd
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x20400000
|5,0=>0x21c002000000200160c8880418201
|6,0=>0x1e1c95d1d007ce841444c800e2493b0a11008265541322480001e84d8d00606170061b8828f87b2
|7,0=>0x34e952f8324b3c91297444e991bf97321bd8b01aa970d28335ac08339cda39c
|8,0=>0x44ad8d149356429f4a339
|9,0=>0x22
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 26 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_188 7 roots_188 ops++addP pm 1 dom_164 4 roots_164 ops++addP pm 2 dom_158 7 roots_158 ops++addP pm 3 dzo_148_8 4 roots_148 ops++addP pm 4 dom_186 7 roots_186 ops++addP pm 5 dom_174 7 roots_174 ops++addP pm 6 dom_62 7 roots_62 ops++addP pm 7 dom_148 4 roots_148 ops++addP pm 8 dzo_180_8 5 roots_180 ops++addP pm 9 dzo_46_16 5 roots_46 ops++addP pm 10 dom_42 4 roots_42 ops++addP pm 11 dzo_42_16 4 roots_42 ops++addP pm 12 dom_182 7 roots_182 ops++addP pm 13 dom_60 4 roots_60 ops++addP pm 14 dzo_182_8 6 roots_182 ops++addP pm 15 dzo_174_16 6 roots_174 ops++addP pm 16 dzo_150_8 5 roots_150 ops++addP pm 17 dzo_170_16 5 roots_170 ops++addP pm 18 dom_162 4 roots_162 ops++addP pm 19 dom_154 4 roots_154 ops++addP pm 20 dom_184 4 roots_184 ops++addP pm 21 dom_46 5 roots_46 ops++addP pm 22 dom_170 5 roots_170 ops++addP pm 23 dom_150 5 roots_150 ops++addP pm 24 dom_172 5 roots_172 ops++addP pm 25 dom_166 5 roots_166 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_190 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_148_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_180_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_46_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_42_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_182_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_174_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_150_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_170_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_166 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_188 7 s (0,roots_188.map (·&&&dom_188)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_190 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_188 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_190==dom_190)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_190 gM v ys):RunD true dom_190 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_190 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 46 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_190 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_231:Lower true dom_231 roots_231 goal_231 7:=lower_slice_b [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,32,33)] (by decide +kernel) lowS_230
theorem lowS_235:Lower true dom_235 roots_235 goal_235 8:=lower_slice_b [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a,8,9)] (by decide +kernel) lowS_234
namespace S_249
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(8,9),(8,40),(8,72),(16,17),(16,80),(16,144),(24,25),(24,56),(24,88),(24,152),(32,33),(32,40),(32,160),(48,49),(48,56),(48,112),(48,176),(64,65),(64,72),(64,80),(96,97),(96,104),(96,112),(96,224),(128,129),(128,144),(128,160),(136,137),(136,152),(136,168),(136,200),(192,193),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_249.map (·&&&dom_249)
def gM:=goal_249&&&dom_249
def NN:Nat→Nat
|5=>4
|6=>26
|7=>17
|8=>4
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x228451f1da04aeb03d0f
|6,0=>0x60fe254c984cbe54a5da489ab4841d4542c40eea2fc562e98e2dcb82c5d22759a22c69209b31b2271b0b20aa390a68d08fdb08c72060f902c4d02a490209d02044
|7,0=>0x659b354cc74f77a4f37b47d1147aa431eab25e681fce612854102730ea7b0d45c0d0cd0a4c20943c08a93
|8,0=>0x54c622c020263cd262dc
|9,0=>0x2c020
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c0000080803000300030003000000000000000000030003000300030003000300020002c0c0c0c0c000c000c0c0c0c0c000c000c0c0c0c0c000c000c0c0c0c0c000c0303030303030300030303030303030003030303030303000303030303030300c0c0c0c080808080c0c0c0c080808080c0c0c0c080808080c0c0c0c0808080b02030203020302030203020302030203020302030203020302030203020302c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c030303030303030303030303030303030000000000000000000000000000000080808080808080808080808080808080808080808080808080808080808080b03000003030000030300000303000003030000030300000303000003030000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c0000000303030003030300030303000303030003030300030303000303030003030300c0c08080c0c08080c0c08080c0c08080c0c08080c0c08080c0c08080c0c080b03030303030303030303030303030303000300030003000300030003000300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0808080808080808080808080808080b03030303030303000000000000000003030303030303030000000000000000
|0,1=>0xc0c0c0c0c0c0c0c0c0c0c0c000000000c0c0c0c0c0c0c0c0c0c0c0c000000030303030303030303030303030303030303030303030303020202020202020200000000000000000000000000000000c0c0c0c0c0c0c0c080808080808080b000300030003000300030003000300030303030303030303020302030203020000c0c0000080800000c0c0000080800000c0c0000080800000c0c0000080b00030303000302030003030300030203000303030003020300030303000302c0c0c0c0c0c00000c0c0c0c0c0c00000c0c0c0c0c0c00000c0c0c0c0c0c000303030203030302030303020303030203030302030303020303030203030302c0c0c0c0c0c0c0c0c0c0c0c080808080c0c0c0c0c0c0c0c0c0c0c0c0808080b0303030303030302020202020202020303030303030303020202020202020200c000c000c000c000c000c00080008000c000c000c000c000c000c0008000b03030303030303030003000300030003030303030303030300030003000300000000c000000080000000c000000080000000c000000080000000c0000000b03030303030303030303030303030303030303030303030000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000c000c000c0000030300000303000003030000020200000303000003030000030300000202
|0,2=>0xc0c0c0c0c0c0c0c0000000000000000080808080808080b030303030303030303000003030000030303030303030303030000030300004040404040404040404040404040000040404040404040404040404040400030303030303020203030303030302020303030303030202030303030303020200000000000000000000000000000000c0c0c0c0c0c08080c0c0c0c0c0c08080000000000000003030202030302020000000000000000030302020303020200c000c00080008000c000c00080008000c000c00080008000c000c0008000b0003000303030203000300030303020300030003030302030003000303030200000000c0c0c0c000000000c0c0c0c0000000008080808000000000808080b03030303030303000000000303030303030303030303030000000002020202c0c0c0c0c0c0c0c00000c0c000008080c0c0c0c0c0c0c0c00000c0c000008080000000000000000000303000002020000000000000000000003030000020200000000c0c0c0c000000000c0c0c0c000000000c080c08000000000c080c0803000300030003000300030003000300030002000300020003000200030002c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c0c0c080c0c0c080c0c0c0800030200000302000003020000030200000302000003020000030200000302
|0,3=>0x303030303030303030303030303030303030000030300000303000003030000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000c0c0c000c0c0c000c0c0c0303030303020302030303030302030203030303030203020303030303020302c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c080c080c080c080c080c080c0800000000000000000000000000000003020302030203020302030203020302c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c08080c0c08080c0c08080c0c080800000000000000030203020302030200000000000000000302030203020302
|_,_=>0
def sP:Nat→Nat
|0=>0x14608780021f14625e1c814628258020c1462870081467091c02192c42470081466891c021915824700814658754020d2c628020518a4470081462474c02051912411c014624740020b14418a0081491cf0081461ce00830b18a0081440c2040
|1=>0x1c0205c46247008146c091c02192c62470081462941c021f146247488146247bc0205b862561c8146247b4022cac51891c07c5a862472051061e9008146a091c02051891e60081462479402051891e40081891e3008146247880205846247008
|2=>0x51891c0205d862470081462470081460891c020b1462470085cb14624700814625e1c020b16e1891c02050c62410082df1891c0205d462470082c51891d2008d0b146247008146cc9047008146c89
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x9303180cc006
|6,0=>0x18aebe75bbac1d52ea274dba51d1cc8774039e5ce4e6b7323975cace4f7243905c76c34716b899c3ee187
|7,0=>0x14089cbcc6254f2378e3c5221910487ebbd9ddeee8770bb69da6ecc7
|8,0=>0xae3d59a9ef487
|9,0=>0x1636
|_,_=>0
def wAt:=mkWire dB 55 250 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1c84a231c943211c64a031c945191c549011c9480114041031c840191c043151c643031c64b271c567012184a19286c91d588470120947251c0463524547257495623147451925b47152864725257961524547151c954212404725489481d20049191c547251c54d1924549211c84719
|1=>0x18849211c54b011c541011c846011c547211c6451d140762518840211c54b251c54125
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x19803
|6,0=>0x2d2564a4800281000000000004c4909111f3386688c1162284488798c300024c00063
|7,0=>0x4f29a52ca494728a50ca093f27a4ec9c93726a4cc9892f2
|8,0=>0xa6200290d11
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x120e6904092c414814608004303a469810230403b0060148d300908c800b3cc0053a600104000080000037ec0011a60008000003a880004800001a600009800004080002000000c000005400002080001000000280000110000070000008000002000000
|1=>0x80ec69c0167ce0013fec010d3310240980330c804422401dd3
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x103
|6,0=>0x1018201300000039050c1ca1422413cb004008
|7,0=>0x236dc66295a8575675a479f61d
|8,0=>0x98d4a0
|9,0=>0x11
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_248 7 roots_248 ops++addP pm 1 dom_233 7 roots_233 ops++addP pm 2 dom_225 5 roots_225 ops++addP pm 3 dom_113 5 roots_113 ops++addP pm 4 dom_241 7 roots_241 ops++addP pm 5 dom_161 4 roots_161 ops++addP pm 6 dom_217 7 roots_217 ops++addP pm 7 dom_185 7 roots_185 ops++addP pm 8 dom_81 4 roots_81 ops++addP pm 9 dom_209 5 roots_209 ops++addP pm 10 dom_145 4 roots_145 ops++addP pm 11 dom_121 7 roots_121 ops++addP pm 12 dom_73 4 roots_73 ops++addP pm 13 dom_240 4 roots_240 ops++addP pm 14 dom_41 4 roots_41 ops++addP pm 15 dom_232 4 roots_232 ops++addP pm 16 dom_120 4 roots_120 ops++addP pm 17 dom_184 4 roots_184 ops++addP pm 18 dom_57 5 roots_57 ops++addP pm 19 dom_169 5 roots_169 ops++addP pm 20 dom_177 5 roots_177 ops++addP pm 21 dom_153 5 roots_153 ops++addP pm 22 dom_216 4 roots_216 ops++addP pm 23 dom_201 5 roots_201 ops++addP pm 24 dom_105 5 roots_105 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_249 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_161 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_145 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_105 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_248 7 s (0,roots_248.map (·&&&dom_248)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_249 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_248 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_249==dom_249)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_249 gM v ys):RunD true dom_249 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_249 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 26 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 26 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 17 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 4 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_249 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_249 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_249 roots_249 goal_249 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_249
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=S_249.noCircuit
def dzo_234_16:=0x505000005050000050500000505000005050000050500000505000005050000
def gzo_234_16:=0x505000005050000050500000505000005050000050500000504000004000000
def gsh_234_16:=0x50500000505000005050000050500000505000005050000050400000400
theorem lowS_zo_234_16_42:Lower true dzo_234_16 roots_234 gzo_234_16 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_16) [(dom_234,16)] (by decide +kernel) (lower_slice_b (T:=gsh_234_16) [(0x50500000505000000000000000000000505000005050000000000000000,0,64),(0x50500000505000005050000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_106_16:=0x5050000050500000505000005050000
def gzo_106_16:=0x5050000050500000504000004000000
def gsh_106_16:=0x505000005050000050400000400
theorem lowS_zo_106_16_42:Lower true dzo_106_16 roots_106 gzo_106_16 5:=lower_iso_b (d1:=dom_106) (r1:=roots_106) (T1:=gsh_106_16) [(dom_106,16)] (by decide +kernel) (lower_slice_b (T:=gsh_106_16) [(0x505000005050000000000000000,0,64)] (by decide +kernel) lowS_42)
namespace S_250
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(2,130),(8,10),(8,40),(8,72),(16,80),(16,144),(18,26),(18,50),(18,82),(18,146),(24,26),(24,56),(24,88),(24,152),(32,34),(32,40),(32,160),(48,50),(48,56),(48,112),(48,176),(64,66),(64,72),(64,80),(96,98),(96,104),(96,112),(96,224),(128,130),(128,144),(128,160),(136,138),(136,152),(136,168),(136,200),(192,194),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_250.map (·&&&dom_250)
def gM:=goal_250&&&dom_250
def NN:Nat→Nat
|4=>11
|5=>96
|6=>287
|7=>130
|8=>18
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xf1aaddb56fd7fa88503b623ad5e7165516b30ccc2c0561d3d815b75
|5,0=>0xf0d37e9cd3d3de8d0879cfaa0cf123ca64cc5e0bc2d95c10a1b0d65b0c68ad9e8ac043a3ac1a11fa9c1f5987c39830a8f68a8b2618aac582085812857fba97c8387c82e7b71074a3972b0a716c76e6016a55b6207a611a460d9860d365ecf05d36f5a9e15a8a359b8e5939955b0953f455283451ebf5039e5014d4f9204e8884d5054c32f4b49d4a3ee498294904f425213ecf53e5713c5123c3653b92a3aa7438f9837ca73670b341aa32a74309b22aea429ab42509f2454c221b9215a120cb1205841c64518ba418303166bd1568f14b5a1358d0fbcf0bea80b69c078cd05f9c052770380e02ca10137f00c2500384
|6,0=>0x544bd529a95232050fa84fa6e4f7d44e0284cbd64b74b4985f4982948ded4860f4843947233464f843eb641f194182f4125e404793f8053d8563bffd3bf2a3b3823a1c439efc3929837dce36d3e369093494e333c33304e32fd332ef7326c331f4830d1930c51307db302fe2f1422ec912ec012e7d82da3f2d3eb2ca8b2c64829fd028f3c27fb426cfa26801236e223623230c421863213542068d201551f9761f7fb1edc41e94e1e8601e7cd1e1c11de7f1d7311d4e11d3ad1d39b1b7741967b18ba418480182d11800d168fb166bd15f0a159ed157101515f139d713725134ec133bf12cfc124a911ef011d1910ba4101520fc880f5fa0edd20ed460c4b20b22f0af670af070ac50096e3086680850807be9071d206c0606b8f06248058b70585204a9c0484e03c5103c1b0319c02ee30231b0116f00dab007f8000f6000ad
|6,1=>0xb6704b4b8db4b2fb3d1ab31e9b2b13b1338b09f4afe78abcaeab130aa85faa3a2a9e95a8146a7ce0a7544a7166a66b7a5c84a427ca3d6ba2cf2a11faa0d2ca028d9f9fa9f5a59ee319e9aa9c4429b9489b3349ad5b9a6649a21199e7697cac9784d970f396a4d968b193c7c9361392634911c690b2f8fa6d8bce989a16889fb8833287f5f8636c84ecf835c4823568131a80ccf809957f7c27f0657d4157d1fc7b3357a88e79d9179d4d79ba2795e2761bf7555874a39746b773a6b7235471a17719c9716c7705f76e9456e45e6dcb96dbf26c38f6bd506b6426b2ab6b2096ab946a7c668889687bb67fb5670c666b5965be765679655f164fe864b2f643ad639e86390761e0f61aac60fa1602bb601be5ee1b5ee175e9575e7fd5e2fb5b60d5a8675a2ac5a0d55954258172579b757783571f15701756e1a5669f54ed8544ed
|6,2=>0xfff11fe01ffcf5bfc19ff8d7ff5eadef77feb145e5d09d89efd4308d3239d3122d1454cd56ccd33acd14fcc80ecbbe2cababc981cc97bdc8c96c75d1c5c95c497abf053b9f5fb9bc1b9b36b9613
|7,0=>0xee08ceac9ce41c5e352fd1044d0fe7cd61cc90b7c043bbc0f4baa03b4689b2691b0afcabfccab758a76daa5c7ea212ca05319eaf99da759c9669c4949a951998479709d94b2b909ee908028d2cd8d08e87e70878458462282be67a64876dd876c0975558745e3732c2723ee6f0b96e56f6d01d6cce26c3d56939d643de604295fb1a5b2e75aa40599d258bcb581725531b54ed852248506314f1fe4df004cf014b87a49fce49d1d493834732646e4c466b245fa345f1a45d2744c6c41c424125e4039d3fee13da783a4f83961c38b65387f038003352ff34d60334b531eba30d192ec312d3fb2b7eb2abc52a9fd29dee29a3c2473e23f8f2399221ecf20cdb1f1421c3ce1b61f1ac7e1ab251947d18e5817ec0178f516b3515a8e1188a1104e0fbc30fab00d8510af0709c37089e406ea0062a604d080460f01e7301b1000793
|7,1=>0xf8d7ff09c5
|8,0=>0xef2e1d1425c043bbf0be9d415701046a71b66ea96234959a6b5329e4679b3811a309b61cf321991212b8d015c3
|9,0=>0xef2e1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa0a08080a0a08080a0a08080a0a08080a0a08080a0a08080a0a08080a0a080941414101414101014141410141410101414141014141010141414101414101000800080800080000080008080008000008000808000800000800080800080505050505000500050505050500050005050505050005000505050505000500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0808080808080808080808080808080941414141010101014141414101010101414141410101010141414141010101282828282828282828282828282828282800280028002800280028002800280505050505000500050505050500050004040404040004000404040404000400a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000000000a0a0a0a0000000141414141010101014141414101010101400140010001000140014001000100282828282828282800000000000000002828282828282828000000000000000505050500000000050505050000000005050505000000000505050500000000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a000141014101410141014101410141014101410141014101410141014101410141282828282828282828282828202020202828282828282828280028002000200505050505050505050505050505050500000000000000000000000000000000
|0,1=>0xa000a000a000a0008000800080008000a000a000a000a000a000a000800080141414141414141414141414141414140400040004000400040004000400040280028002800280000000000000000002800280028002800280028002000200001000105000500000100010500050000010001050005000001000105000500a0a0a0a0a000a000a0a0a0a0a000a000a0a0a0a080008000a0a0a0a0800080141414141414141410101010101010101400140014001400100010001000100282828282828282828282828000000002828282828282828282828280000000505050505050505040404040404040405050505050505050404040404040404a0a0a000a0a00000a0a0a020a0a00000a0a0a000a0a00000a0a0a020a0a000141414141414141414141414000000001400140014001400140014000000000202020202020202020202020202020202020202020202020202020202020202500050005000500050005000500050005000500050005000500050005000500a0a0a0a0a0a0a0a0a0a0a0a000000000808080808080808080808080000000141414141414141414141414141414141414141414141414000000000000000080808080800080008080808080008000808080808000800080808080800080005000505000500000500050500050000050005050005000005000505000500
|0,2=>0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000a000a000a01414141414141414141414141414141414141414140014001414141414001402828282828282828280028080000000028282828282828282800280800000005050404050504040404040405050404050504040505040404040404050504040000000000000000a000a000a000a0000000000000000000a000a000a000a0141414140000000014141414140014001414141400000000141414141400140282828282828282828282828282828282800280020002000280028002000200505050500000000050405040000000005050505000000000504050400000000a0a0a0a000000000a0a0a0a000000000a080a08000000000a080a080000000101010101010101010101010101010101010101010101010101010101000100282828282820282028282828282028202828282828202820282828282820282505040405050404050504040505040405050504050505040505050405050504a000a00000000000a000a00000000000a000a00000000000a000a000000000101410141410141010141014141014101014101414101410101410141410141202020202028202020202020202820202020202020282020202020202028202505050405050504050505040505000005050504050505040505050405050000
|0,3=>0x2000200020002000200020002000200020202020200020002020202020002004000400040004000404040404000400040004000400040004040404040004000280028002800280028002800200020002800280028002800280028002000250505050505050505000500040004000505050505050505050005000400040000000000a0a0a0a000000000a0a0a0a000000000a000a00000000000a000a000000000000000001400140014001400141414140000000014141414140014028280000282800002828002828280020282800002828000028280028282800250505050505050501010101010001000505050505050505010101010100010000a000a00000000000a000a00000000000a000a00000000000a000a0000000000000000404040400000000000000000014001404140414000000000000000002800280028002800200020002000200028002800280028002000200020002505050505050505000500050000000005050505050505050005000500000000a080a08080808080a080a08080808080a080a08080808080a080a080808080941410101414101014141010141410101414101000140010141410100014001280028002800280028002800200020002800280028002800280028002000200505050505050505050005000500050005050505050505050500050005000500
|0,4=>0xa0a0a0a0a0a0a0a0808080808080808000000000a0a0a0a000000000808080940014001400140014001400140014001400140014001400140014001000100000000000000000000000000000000002828002828280020282800282828002505040405050404050504040505040405050404050505040505040405050504a0a00000a0a00000a0a00020a0a00000a0a00000a0a00000a0a00020a0a000040404040404040404040404040004000404040404040404040404040400040002800280028002800280028000000000028002800280028002800280000000101010101010101010101010101010101010101010101010101010101000100a0a0a0a0a0a0a0a0a0a0a0a080808080a0a0a0a0a0a0a0a0a0a0a0a080808094101410141014101410141000000000141014101410141014101410000000000000000280028000000000028002800000000002800280000000000280028000500050504050400050005050405040005000505040504000500050504050400a000a000a000a0008000800080008000a000a000a000a000a000a0008000941014101010141014101410101014101410141010101410141014101010141002800280028002800000000000000000028002800280028002800280020002000000000000000000000000000000005040504050405040504050405040504
|0,5=>0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000a00000000000a000a000000000141414141414141414141414141014101414141414141414141414141410141000000000000000000000000000000000028002800280028002800280000000404040405040504040404040504050404040404050405040404040405040504a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000000000000000a000a000a000a01414141414141414141414141414141414141414000000001414141414001400000000028282828000000002828282800000000282828280000000028202820000000000000000000000000000000050505050500050005050505050005008080808080808080a0a0a0a0808080808080808080808080a0a0a0a080808080000000141414140000000010101010000000001414141400000000101010100000000000000000000000000000000282828282828282028282828282828250005000500050005050505050005000500050005000500050505050500050000000000000000002020202020002000000000000000000020202020200020140014001414141414001400141414141400140014101410140014001410141282828282800280020202020200020002828282828002800202020202000200000000000000000000000000000000005000500050005000500050005000500
|0,6=>0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000000000a000a00000000000a000a01400140010001000140014001000100014001400100010001400140010001000028002808280828000000000000000000280028082808280000000000000000000500000005000000050000000500000005000000050000000500000005008080a0808080a0808080a0808080a0808080a0808080a0808080a0808080a0941414141414141400140014001400141010101010101010001000100010001282828282828282808080808000000002828282828282828080808080000000000000000000000010101010000000000000000000000000101010100000000a0a00000a0a00000a0a02020a0a00000a0a00000a0a00000a0a02020a0a000141400001414000014140000141400001414000014141400141400001414140282828282800280028202820280028002828282828002800282028202800280000050500000000000005050000000000000505000000000000050500000000a0a0a0a0a0a0a0a00000a0a000000000a0a0a0a0a0a0a0a00000a0a0000000141414141414141400000000000000001414141414141414141414140000000080008000800080008000800080008000000000008000800000000000800080000000000000000050505050000000000000000000000000505050500000000
|0,7=>0xa0a0a0a000000000a0a0a0a000000010101010101010101010101010101010141414141010101014141414101010100280028002800280028002800280028002800280028002800200020002000250505050505050500000000000000000505050505050505050505050404040400000000000000000000000000000000a0a0a0a000000000a0a0a0a0a000a0001400140014001400140014001400140010001000100010001000100010001202020202020202028282828282828282020202020202020282028202820282505040400050004050504040005000405050404000500040505040400050004a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a080a080a080a080a080a080a080a0800000001414141400000000141414140000000014101410000000001410141282828282828282828282828282828282828282828282828202020202020202000000000000000000000000000000001000100010001000100010001000100a0a00000a0a00000a0a00000a0a0000080a0000080a0000080a0000080a000000000000000000000000000141414140000000000000000000000001010101000000002828282800000000282828280000000020202020000000002020202001000100010001000100010000000000010001000100010001000100000000
|0,8=>0xa0a0a0a0a000a0000000000000000000a0a0a0a0a000a01414141400000000141414140000000014141414040004001414141404000400028002800200020002800280020002000280028002000200028002800200020000000000000000000000000000000050505050505050505040504050405040000000000a000a00000000000a000a0000000000080008000000000008000800000000000000014101410141014100000000000000000141014101410141282828282828282828202820282028202828282828282828282028202820282100010001000100010001000100010001000100010001000100010001000100a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000a000a000a000a000a000a000000014101410141014101410141014101410101010101410141010101010141014120202020282828282020202028282828202020202820282020202020282028200005050000050500000505000005050000050500000505000000000000000000000000000000000000000000000000a0a0a0a0a080a080a0a0a0a0a080a0941414141414141014141414141414101414141414141410141414141414141282828280028002828282828002000202828282800280028282828280020002005000501050105000500050105010500000000000000000000000000000000
|0,9=>0xa080a08000000000a080a08000000000a080a08000000000a080a080000000000000000000000014141414141414140000000000000000140014001400140000000000028002000000000002800200000000000280020000000000028002101010100000000010101010000000001010101000000000101010100000000a020a020a000a000a020a020a000a000a020a020a000a000a020a020a000a0140014000000000014041404000000001400140000000000140414040000000282800002828000028280000282800000008000000080000000800000008000101010100000000050105010500050001010101000000000501050105000500a000a000a000a000a000a000a000a000a0a0a0a0a000a000a0a0a0a0a000a014141414141414141414141414141414141414141414141414141414000000008080808080808080808080808080808080808080808080808080808000000050505050505000005050505050500000505050505050000050505050505000000000000a080a08000000000a080a08000000000a080a08000000000a080a0941414141414141414141414141414141414141414141414141414141400140282828282828282800000000282028202828282828282828000000002820282505050505050505050505050500050005050505050505050505050505000500
|0,10=>0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a080a080a080a094141414000000001414141400000000141414141400140014141414140014000000000000000000000000000000000282828282828282828282828202020250505050404040405050505050405040505050504040404050505050504050420202020000020002020202000002000202020200000200020202020000020141414140014001414141414001400141414141400100010141414140010001282828202828282028282820282828202828282028282820282828202828282000000000000000050505040505050400000000000000000505050405050504a0a0a0a08080808000a000a000800080a0a0a0a08080808000a000a00080009414141414141414141414141414141410101010101010101410141014101410000000028282020000000002828202000000000282820200000000028282025000500000001000500050000000100050005000000010005000500000001000000000000000000a0a0a0a0808080800000000000000000a0a0a0a0808080901010101010101014101410141014101010101010101010141014101410141282828282828282828282828282828280000000028202820000000002820282505050505050505050505050505050505050505010001000505050501000100
|0,11=>0xa0a0a0a0000000008080808000000000a0a0a0a00000000080808080000000000000001414141000000000141414100000000014141410000000001414141000000000000000000000000000000002828282828282828282828280000000500050005000500050005000500050005050505050505050505050505000500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a080808080a0a0a0a0808080800000000000000000000000000000000000000004000400000000000400040000000000000000000000000000000000000000000000000282028202820282101010101010101010101010000000001010101010101010101010100000000a000a000a0a0a080a000a000a0a0a080a000a000a0a0a080a000a000a0a0a09400140014001400141414141410141014001400140014001414141414101412828282828282828282828282828282800280028002800280020002000200021010101010101000101010101010100010101010101010001010101010101000000000000000000000000000000000000000000a0a0a0a000000000808080941400001414000014141414141410101414000014140000141414141414101282828280800080028282828080008002828282808000800282828280800080000000000000000000000000000000005050505050505050404040404040404
|0,12=>0xa0a0a0a0a0008000a0a0a0a0a0008000a0a0a0a0a0008000a0a0a0a0a00080000004001400140000000400140014000000040014001400000004001400140282820202800200028282020280020002828202028002000282820202800200505050501010101050505050101010105050505010001000505050501000100a0a0a0a080808080a0a0a0a080808080a0a0a0a0a080a080a0a0a0a0a080a0901010101010101010101010101010101414141414101410141414141410141002800282828282800000000000000000028002828282828000000000000000505050500050004050505050005000405050505000500040505050500050004002000200000000000200020000000000020002000000000002000200000001414141414141414141414141414141404040404040404040404040400000000000000028282828000000002820282000000000282828280000000028202825050504050500000505050405050000050505040505000005050504050500008080a0a08080a0a08080a0a08080a0a08080a0a08080a0a080808080808080901014141010101010101414101010101010141410101010101014141010101282028282820282028202828282028202820282828202820282028282820282504050405040504000000000504050405040504050405040000000005040504
|0,13=>0xa0a08080a0a08080a0a08080a0a08080a0a08080a0a0808080808080808080800000000000000000000000000000000000000014101410000000001410141280028002800280028002800280028000000000028002800000000002800280000000000000000000000000000000001010101010101010101010100000000a000a000a000a000a0a0a0a0a0a0a0a0a000a000a000a000a080a080a080a0940014001400140014001400140014000000000004000400000000000400040002800280028002800280028002800280028002800280028002800280000000000000000000000000000000000000000000000000000000505050505000500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a080a08000000000a080a080000000141414140000000000140014000000001414141400000000001400140000000282828282828282828282828282828280000000008000800000000000800080000000000000000050505050505050500000000000000000505050505000500a0800000a080a080a0800000a080a080a0800000a080a080a0800000a080a0941400141414001014140014141400101414001414140010141400141414001282828280000000028282828282028202828282800000000282828282820282500040005000400050004000500040005000400050004000500040005000400
|0,14=>0xa0a00000a0a0000000000000a0a00000a0a00000a0a0000000000000a0a00000001414000014100000141400001410000014140000141000001414000014128002828280028002800282828002800280028282800280028002828280028000000000000000000000000000000000000000005000500000000000500050000000000200020000000000020002000000000002000200000000000200020141414141414141414141414141414140000000000000000141414141400140282800002828000028282828282800002828000028280000282828282828000404040404040404040404040404040405040504050405040504050405040504a0a0a0a0a0a0a0a000a000a000a000a0a0a0a0a0a0a0a0a000800080008000801400001414000000140000141400000014000014140000001400001414000202820202828202020282020282820202028202028282020202820202828202505050500000504050505050000050405050505000005040505050500000504a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a0a080a080a080a0801400101414101000140010141410100014001014141010001400101414101280028002800280028002800280028002828282828282828282028202820282505000005050000050500000505000005050000050500000000000000000000
|0,15=>0xa0a00000a0a00000a0a00000a0a0000000a0000000a0000000a0000000a000001400141414141400140014141414140000000000000000000000000000000080800000808000008080000080800000808000008080000080800000808000400040005000500040004000500050004000400050005000400040005000500a0a0a0a0a0a0a0a0a000a00000000000a0a0a0a0a0a0a0a0a000a000000000000004040000040000000404000004000000040400000400000004040000040282808082828080028280808282808002828080828280800282808082828080404050504040504040405050404050404040505040405040404050504040504a0a08080a0a0808000000000a0a08080a0a08080a0a0808000000000a0a08080000000000000001404140414001400000000000000000014041404140014000000000000000000000000000000000002800280020002000280028002000240404040404040404040404040404040404040405040504040404040504050400200000a0a0000000200000a0a0000000200000a0a0000000200000a0a000140014001414141410001000101010101400140014141414100010001010101282828282828282828282828282828282020202028202820202020202820282000000000000000000500050000000000000000000000000005000500000000
|1,0=>0x141414001414140014141400141414001414140014141400141414001414140282828002828000028282800282800002828280028280000282828002828000505040400000000050504040000000005050404000000000505040400000000a0a0a0a0a0a0a000a0a0a0a0a0a0a000a0a0a0a0a0a0a000a0a0a0a0a0a0a00010001010101010001000101010101000100010101010100010001010101010808080808080808080808080808080808000800080008000800080008000805050005050500050505000505050005000000000000000000000000000000000000a0a00000a0000000a0a00000a0000000a0a00000a0000000a0a00000a0141414140000140014141414000014001414141400001400141414140000140000028200000282000002820000028200000282000002820000028200000282505050505050505050505050505050505050000050500000505000005050000
|_,_=>0
def sP:Nat→Nat
|0=>0x104814058140003110542005000101e14108140004100502a0500010061f0a814000407850161e02810061d0a814000c0185438050006c0803048540a040180834050003032030106000040b8502a050003c200d0280018030b054240a018502612078442005000101e0904014180f06814000c070340a000600c0c0b028280609040140e03010180a04018080200
|1=>0x1c01400190785030370001006140a8d800040185468350001006090a8200a04078503034000300615068140004190502a05000101e310c0140004018085e18000301e1508014002e0500c280b028641e14088140004078501005000101e2d0a05400040a0b03005000a814030101400040185052150286406280a0540003138502a05000100614130140025018542005
|2=>0x58148e04018086000018542210028001403230500a00078542005000300615220140004018548605000101e420a0140004018c42a1200010061520814000c0500c8005000101e141f8140004078507c05000101e181e81400040180878000600c6605000101e14058ec0a2e0500c0405000e808030a0542419018546e350003006330681400041c8502a05000101e14
|3=>0xa14c0a001283006330280008030a0582a120200c28150d0481819018242a12019482a45028001803110540a000200c045102800080f280440a000602806020280008030a0549e120200c2a3d028000803230c02a000200c9c1502800084d018502a0502130281502800084b0a0540a000200c8c140c000080f0a1280a0001854923b0280008030a1200a00170101e14
|4=>0x2d01006140a814000c0c80c04150280018030b0540a00018502a5902800180f118440a000200c04090c0481803198440a002c028060202800180f1981400030a8401a0500030320f0a060000c070cc0a000615c0602028001803230540a000200c04302b00008030a0042a002a81006140a814080f0a0440a000611c06020280014070180812052a028060202800080f
|5=>0xa054de050001006140c05468000200c281536800140401850d6050006408030a02c2a120200c28153501400040185030153480008670a0602a0500010cc140a8140004019942815028000803010502a63001880803180502a000200c281530814000a3000c041402800080f0a17c2a052f01006140a8140004018502a5d028000803049702a050001006142d82c2a05
|6=>0x200c28153d0480a04019e428150280008030a054a205000101e780a0540a000203c28181b814000a0c80c280b0280006020a054ec050006408030a1d42a000200c28151c01400040a1cc16150280032030a0602a37000b8080f0a0540a000200c28153901400250200ca0150280008031785016150283014030a0540a000200c12140a9c40a04018502a7002800080f
|7=>0x1a2428150016008030aa200a000200c28154381400040185016151d81408030a2182a0500030080f280540a000200c28850a81400040185052150283008140a81508004181006140a81400820200c2815028010204018502a050000c4e140a8140004018502a054001006151b8d40a003f01006140a8480a04018502a7d02800f804018502a05001ec08030a0540a00
|8=>0x28000803010bc2a050025006140aa4c0a001501006020a81400920200c28150280008030a0552205002411e04018502a004701006140a8140004018502a3f028001e151b9140a000200c28151f0140004018551a6c028000803460502a050001006180a8f40a00051fc06020a0140004018502a8b028001803370540a000200c045b0a814000401a282815090003204
|9=>0x1a7c28050001006140a9280a000200c289e058540a04018502a9d028001847018502a050011c080f0a0600a001281006140a814001901a6c281502800320401824281509010069a0a0540a00020502a99028001407018242815028b808030a02c2a052a02806140a814000401a6028150280008030a0a42a0500030b004018242a054b8100615440140004018502a95
|10=>0x2800080301054de050001006300a054ac000200c28155581400aa0200c2815028001804078502a050003032030a0542400022a006140a80008030a0554e050003014030a0440a000200d4c140a8140004018082a3b02800080f0a2902a05000641e140a8dc0a000628c06140a814000a0200d44140280008030a05542050023c08030a05424005001006140a814000a
|11=>0x18502a6802800080f0a060d005002c408030a0540a000c810061458054003a0200c2815028000803578502a050028c0803010500a000200c049e0a8140004019402a11028015c0a018502a05000101e030a0440a001701006020a81400470200c0414028001419018c02815000300633028015a04018502a05002b008030a0540a000200c60140a9a4000c2b80c2815
|12=>0x18502205000101e300a06000570200c0414028000803230502a050001006141582c2a12018084e140a81400b60200c28150280008030a0556a0500030c003010540a000501006090a02c0a04018502ab40280008030a05566050001028730a81400b2020502a050011c08030a0540a000501c06020a0140004338502a050011c08030a05424004786408030a054000c
|13=>0x2800180a0185016050001006c10a0540a000200c2815600140019018502abf0001006140aaf80a005e01006140a8140004018502aba028005404018502a12000101c140a814000401ae42815028000803180502ab80016014030a0540a00038101e090a0540a540203c28150280008035b8502a050001006140a94c0a001283006230a81400250200c2811028001404
|14=>0xa0540a000203c66140280014040180812050002806020a0dc0a000200c281508814000c0500c04050000cee140a9d80a000203c281564800180407850220500320080f0a0540a005d8101e14058140004018547a05000101c330a014000401809361502800147f018502a120281006140ab180a000200c2815628140004620502a050001028c30a814000c050100602
|15=>0x200c5e140a80014040a0540a840001006140ab540a00022a006020a05400250200c121502801a804018502a050006406300a05538004782806140a814000401b4c2815028001804018543c0500011a4030a0540a006881006140a81400cf0203c281502800080f0a0559c05000119a030a0540a006601006140a81400cb0200c2815028000803048552605003280803
|16=>0x6e81400580203c281502800087f018505615090101e090a02c0a04018502adc0280018040785030050001006db0a0540a000501006142e0140004018502a1a028001819018503015000303203048540a00060101e090a8140004018502ada0280008030a055b2050036008030a0540a000200dae140a8145c040185510050001006020a06024000500c28156b0140019
|17=>0x203c2815028008e030a0546e050039008030a0540a000600c461508814000c018502ab80280006090a054ec050001006e30a0540a00020502ae202800080304854920500030061508014000401b84281502800180f118540a000203c28110280008146f8140004018502c150280008030a055bc050001006020a1580a000200c04300c0001803198540a000203c2815
|18=>0xa81400570200c28180280008030a055dc050001006140a9d80a002381006310a814000401809da15028012c04018501615028101e140abb00a000200c12157581400ea0200c281502801d204010502a05000101e140aa740a0002090281502800540a018502a050001c08033b8502a050506406140a8480004018502ae7028000803048546a050001028e50a8140097
|19=>0x198500a0002051be15028000803140502a050001028157b814000401bd82815028005c0a018502a05000101e140ab880a000200c28157a81400030a8400a000203c281524814000401851e8150280008140abcc0a000200c2815790140004018502ab80900006270a02c2a050001006090a8440a000200c28f10a814000a018502af0028003204018c42a0500010282c
|20=>0x3000c281502800140401824281502800086001808281502800180a018502a050001c0803180502a05000311e04018502a050001006147d85400470200c28180a81400ae0200c281502801200c0200c2815028004a0c0200c281502800180a0200c28150280014040185056150280008030a055f405000101ecd0a0540a00023e406140a814000401851f015028000803
|21=>0xaa4c0a000501006020a01400043f80c2815090141803118540a000501006300a0540a000200d14140a81400190200c280b0a8140004018502add0280008030a1ac2a050016008030a0540a000501006140a9140a004b01006140a8140004078502aa5028001804018502a12028000803010242815028001804018242a050001006400a0540a000200c12140a8480a0a
|22=>0xa81400040185056154e0140004018502a1e0280008090a055fa050001006140abb00a000606408030a0540a000200c60140c0540004018516015028012004018502a05002500803010502a050009408030a0540a000200c281502bf80803048548a0500028fe030a0540a000601028157e8140004018503015340140004018502afc028012e04018502a05000100614
|23=>0x1006330a0540a00020502aff028000803510502a05002f408030a0540a000200c04140a9900a000200c5e090a0540a00020502a05420000803448082815028001804018502a11028003204018242815028000860078502a05002ec08030a02c2a050003006140aa700a000200c28155f814000c0203c28150280008030a054e205000101e14158540a000200d3e14
|24=>0x601006140c0540a001701006090a0540a002b81006140a81400e9020502a050001006140ac040a000501c06140a8140004078c028150280008030a16c2a05000120003010502a050001006300a05538050001006140ab1c0a000203c28152281400470200c28150280008a9018502a05002c408030a0540a000203c28230a8140004018502a4902800080f048502a05
|25=>0x528140004018c0280b0a8140004018082818028017604018502a05000100614058548a05000100602048540a000501006140a8480a000200c2815378140004018502a058202806140a8dc0a000200cee090a0540a000601006140ac0c0a000200c28153a0140004018502a110280008030a0ac1615028020404018502a05000941404018502a050001006090a02c2a05
|26=>0xa0540a000200c28153180008140a815c0008383008030a0540a000200c290602800087f0185056150280008030a054ac050001006142e0540a00020502ae60280008030a05606050001006020a0558e050000c2a3722814000401850ea180a81400045480c04140a8140004018502b050280008030a0602a12000300803280540a002382808030a0540a000200c2815
|27=>0x200c28500a8140004018502a120280008030a0546e050002808030a0540a000203c06140a81400070200c2815028000900018502a050001006140a9900a000200c66140280008030a1d42a0500030080f018502a050001212140a81400070200c12140a8160e04018502a0500010fe03180502a050001006090aa200a000203e10140a8140004078503005000300803
|28=>0x4018502a050001006140a8140004018504615028001804018502a05000100614158540a000200c28180a8140004078502a050001006140aa700a000c81006140a81400048500c28150280008140abf40a00
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32502d50285023501e50195014500f500a500550005
|5,0=>0x1ae61a861a2619c61966190618a6184617e61786172616c61675161615b6155614f61496143613d61376131612c51275121611b6115610f6109610360fd60f760f160eb60e560df60d960d360cd60c760c160bb60b560af60a960a3609d60976091608b6085607f60796073606d60676061605b6055604f60496043603d60376
|5,1=>0x26c62666260625a6254624e62495243623d62385232622c62266220621a6214620e6208620261fc61f661f061ea61e461de61d861d261cc61c661c061ba61b46
|6,0=>0x424741d741674106409740273fb73f473ed73e673df73d873d173cb63c473bd73b673af73a963a3639c7395738e7387738073797372736b7364735d7356734f73487341733a7333732c7325731e731773107309730272fb72f472ee62e772e072d972d272cb72c562be72b772b072a972a2729c6295728e72877280727972727
|6,1=>0x5de75d775d075c975c275bb75b475ad75a6759f759a5593758c7585757e7577757075697562755b7554754e6547754075397532752b7524751d7516750f7508750174fb64f474ed74e674df74d874d174ca74c374bc74b664af74a874a1749a7493748c7485747e7477747074697462745b7454744d7446744064397432742b7
|6,2=>0x791778a7783777c7776676f77687761775b6754774e6747774077397733672d6726771f77187711770b670566fe76f776f076e976e366dc76d576ce76c776c166ba76b376ac76a5769e7697769076897682767b7675666e7667766076597652764b7644763d7636762f76296623661c7615760f6608760175fa75f375ec75e57
|6,3=>0x945793e79377930792a6923791c7915790e7907790168fa78f378ec78e578de78d778d078ca68c378bd68b678b068aa68a5589e78977890788a6884687d7876786f78696862785b7854784d7846783f78387831782a7823781c7816680f7808780177fa77f377ec77e577de77d777d077c977c277bb77b477ad77a6779f77987
|6,4=>0xa177a107a097a0279fc69f669ef79e969e279db79d479cd79c859c179ba79b469ad79a6799f79987991798a7983797d6976796f79687961795a7953794c7
|7,0=>0xbeb7be47bdc8bd48bce6bc68bbe8bb68baf7ba78ba07b997b927b8b7b847b7d7b758b6e7b677b607b588b517b4a7b437b3b8b347b2e6b277b207b197b118b0a7b037afc7af57aee7ae86ae08ad97ad18aca7ac37abc7ab48aad7aa67a9e8a968a8f7a887a817a7a7a728a6a8a637a5b8a538a4d6a458a3e7a368a2e8a268a1e8
|7,1=>0xdb38dad6da67d9f7d978d907d897d836d7c7d766d706d688d626d5a8d537d4c7d466d3f7d378d316d298d218d1a7d137d0c7d048cfd7cf58cee7ce77cdf8cd87cd08cc97cc36cbc7cb48cac8ca57c9e7c968c8f7c878c807c788c708c697c636c5c7c557c4e7c477c3f8c378c307c297c227c1b7c147c0d7c067bff7bf87bf26
|7,2=>0xdc26dbb7
|8,0=>0xe3d6e367e2f7e287e217e1b6e147e0d7e067e006df97df27deb7de47ddd7dd67dcf7dc87
|9,0=>0xe436
|_,_=>0
def wAt:=mkWire dB 267 251 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x608f0205102050018cd1185502051020500c8080c8550a05502051020500a001020150a0110608f0205102050060600205102115020550205201064010640201506001020510206101064020151b9150205302052018551288f020510205001010020250a001060cf0205102050060cf0205102050180010a0550a0150608f0205102050020250a0010602c02051020ad0a0170608f0205102050048600a001
|1=>0x5050020550184a060553b8100a02d37002050503f855020030a02e0a8010606002051018550205302015020553b813010010a815019d30a02f0a8150a01d020010a049000150a8010211502055020521b815020533701605050020550a9b134015020630a815019a102063038520200132015018120a01502003118010185502050048660a0010a9150a013158010a0170a0010a05501855118550205102050
|2=>0xa011548170100d060570a011048130a0010a297078130a0120185502055010130a055060170a011010100a0550a0010a8010603e020510c8550a27102057020d70a06201903010030a0550a01d020010a0114b057180010a0550a0150200a0a055020ad0a01706049020510a01102053020520185523853020610a0550a0110505002055158010a017010170a055248010c853020260a001048130a00137001
|3=>0x104b0a0550c85706003020510185530051020170205102050020510a0110a8150a015018550a05530055010640a055020150a0173b810010011a8010a0620600d02051019d30a02f0a80101a8d050170a055019a102063020610a8150c851020630a8151802d0a80102055048170a001021410a0030605702051020250a00102061020551185502051020500a01502057228010205202115020520185502015
|4=>0x10100a0550a055020af0a0170a0150184a00015548170100d05051020550a0150a0570505368011078500603c020510200a0a055018551185502050020550a0120a055020550a0110a02d01855118160a01002051018552385302061018cd11855020500a31d010120a0550c85701a7d010100184a028010a0550a0110a3090a9913000a0a05502060020150a8155e8510c8035d852020ad0a017018cd02050
|5=>0x20550a0620a8150ab990188f020500a1fd020030206102051020500c857021de04855200150a0550788f01855020500c853020150608f02051020500a2c10c00301855020510205006057020510ab8101848028010c8240a055020620a0550a0150a8151185502051020500600302051018550a0010a8010c82f0a801018550a0110205502052048600a001020150a0110a001018550a0110604b020514f801
|6=>0xa01102051020550a011020550a0170603c020510600f02051010100a0550ab8101848028013003e0185502017020250a0010788f020500608f02051020500200101a7f010100a0550a8150c857020153b8100a02d06057020510a11c0c8550abbd0198302017020630a8150a0550a191018120204900015038520505202055478010a01101981020170603e020517400d280550a003020ad0a0170a02d02015
|7=>0xa00102055020030185702051020630a8150a273020570a1fd02003010130a0550a0550205500015020030205102050020550a015010170a055020150a8010a1ff020030a9b101852060030205102055020520c801020150781301855020510a0550a0010a0110a001010030a055000150a0010205502017020550a0010a05502017020550a0110a01502001060170a011118150a010020610a815021410a003
|8=>0x20500c85302015018550a0011185502050019430a003158550a0170c803020150a05501812048150a0010184a02801010150a05506057020510a0010201501855020170202d0a8010205102057020600a81501855020510202e0a801018550a017010100a055020570a017440010a057018570a001038520200102051020150a0150a8150c0030a8150c85102015018110a055060550205111802020500a013
|9=>0x18550a0150a8010a0550a8150202d0a8010a0130a8010a0550a001020550001522801020523600201852020550a012048550a001020510a02f0a80106057020510a0170a801021b10185205051020550a0010a80102051048110a001300550201701981020170100f0a05502055020010a01501855158010a0170a055018010a01502057010120a0550205201855020610a8150100d0a055022210a05701855
|10=>0x18570a003028010a012020550185502001018010181211855020500c0010a815020510188d02050020010a0010600d020510a015020030a0570a0010781001855018550a8150a0dd0a01232015018120184802801020511185602050020030a017020620a8150a915020520188f020500600f02051010120a055020520a0120c0010a8150100d0a055048570a001028010a815020510a003050150205507813
|11=>0x2050020510a0170a81501855020570201501851
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x98800000000000908231000021207501a30000000000000000000000000000000019100001720000000050c000000000000000000000000044c00000000e302cc09200000720000000014800000000000000000000002300000000000000000000000000020000000
|5,1=>0x442000000010103d300003940000381000000000000000dc436100000000d08000000031300002e30b080000a4c0000000281
|6,0=>0x23c88e100008b3224887200000002148832000000020487e31f440001f040001e88782000076200000000000742000072200007021b886c21ac40001a4868119880000000633180c000000000017885c2168800000005731548532000051213c800000004c300004a212084620000000
|6,1=>0xd623544d320000d1233c8cd23304cb1320c0000000c620000c4200000000000c132fc8bd20000bb20000b922dc8b520000b412c88b020000ae20000ac22a88a91000000029c80002948a230000a02000000000009f100009e126cc99225c895200009410000000244c0000000000
|6,2=>0x4ac80004a0c000498800048cd22147cd1e100011d146c9183454c00045040004489102438800043090a241cc000414904140890023f88fd13ec8fa13e080000000f623d44f413c4cef23b0ceb13a4800039c80000000e520000e23380800037c4dd236c8da10000d910000d81
|6,3=>0x63498b26249872610d82260457f200017d25e8d7825dc40005d497415c897025b4d6b25a0d66258cd612578d5d157055b1560d5530001532000150353894c200014a25208000514d432000000050493e300013d14ec93a14e080004d89342000133100000004c8531100012f200012d2
|6,4=>0x6e080006d89b426c4c0006b8c0006b09aa20001a730001a6168cda2168099e2670800000019a265cd9520000000000192364098f1
|7,0=>0x8d4a3328c4a2f28b4a2b28a4a272894a232884a1f2874a1b2864a172854a132844a0f2834a0b2824a072814a0328049ff27f49fb27e49f727d49f327c49ef27b49eb27a49e727949e327849df27749db27685d827589d427489d027389cc27289c827189c427089c026fc5be16f09ba2
|7,1=>0xac86b02ab8aac2aa8aa82a98aa42a88aa02a78a9d1a6ca992a5ca952a4ca912a3ca8d2a2ca892a1ca852a0ca8129fca7d29eca7929dca7529cca7129bca6d29aca6a19a0a662990a622980a5e297465b2964a572954a532944a4f2934a4b2924a472914a432904a3f28f4a3b28e4a372
|7,2=>0xad4ab32
|8,0=>0x2c71b186c51b106c31b086c11b006bf1af86bd1af06bb1ae86b91ae06b71
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0x20280010080008000002820001010000700000306000103000070800036000019a0000c900006000002180001060000820000408000200000096000040000018000008000002800000d000004800002000000e0000050000018000008000002000000
|1=>0x494800233400119800088300044000021ac0010aa000834000408800201c00100a0008010004000001e08000e0400050000027f80013ec0009de0004eb00026100012fc00095e0004a1000222800110400088000043f00021780010a400083e00040b
|2=>0x40008016104008000002600001241800910c00480e00210000102080081000040060020020010008006154003082001815000c02800506c00208000102700080a8004044002002000cff000677800339800199e000caf000641000303c00180c000983
|3=>0x1829780c14ac060a5403048f01401400a0024045c04021ccb010e2180870040419de020ccb01062f808312c04181e020c01010002008000402408001200000832180418000209de01010000800000233bc01199e008c8f004607802210c010052008028
|4=>0x104625882132c40093620008710000084c312c25093e12848f088627843902c21489e10544b08222584071042008b610002008000003060041820060866010408000202004100126040886020400810020808000403848f018e2580c37bc061a5e03072b
|5=>0x400277a001054e11856708c0b28000090204a465185e32852f1942178ca10ac6148163026cb160a458a2922c5141062866cb1413418a0932c5009162800971400438a000004c1996252ecb129265890163c480b16228ccb105247882903c411996208c6b
|6=>0x123842b804004ac09f3922189c90440f480225a40107d00895e8044114013c120091bd0019dc800c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1b000008010016000e000000000e0c00000100003100010f000400000e0000000001000000010e000114010000000000000000000b00010000010000000000000001000003010100010000010000000000000100000000000000010000
|6,0=>0x580e01000106010e0e2e00003b000100000004320100340001bb0200091d1d00510054070e8b00021a182200010000001d006c03060158008600003e000000013300040130000058010000014c0e0068002601000200000002000f00101d016d00013301000055045d000001016f5600349b9000013b00003e00021d530000
|6,1=>0x1d02010128010c6a001d14010e00010e1d1d141d2d0215067d13670e9c2f00010096021000040f001e2500005870001c011a0100011d003300000c67006e000100001d003d000400500c0d01004d013d34006c00015f34000602870002671d17580e010c010000014a49b13b195c01005800005f001f01000c011d8500aa0056
|6,2=>0x7005f387e0062000107002c000a07331d011d0000023a3400000034578f
|7,0=>0x6166c9b643c59fb247a07e7b4441ad2a45b937478cbac7af468dbd5bac9427c66bbf8452c4602d4259984bc811c078a4b692a3c2cb3c7264b3b82965a695487c24a73fc39e89352ba15e39746393a27336bf7f6988abaea57a4e44c176818a47712150792d119d5a4499974fa8bc32bec991ca7726404f2b12478e2d864a4f05
|7,1=>0x47b0
|8,0=>0x42478223adb572a9b7802db47583b69acca0
|9,0=>0x20
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_248 7 roots_248 ops++addP pm 1 dom_186 7 roots_186 ops++addP pm 2 dom_242 6 roots_242 ops++addP pm 3 dom_234 7 roots_234 ops++addP pm 4 dom_240 4 roots_240 ops++addP pm 5 dom_226 5 roots_226 ops++addP pm 6 dom_90 5 roots_90 ops++addP pm 7 dom_178 5 roots_178 ops++addP pm 8 dom_162 4 roots_162 ops++addP pm 9 dom_42 4 roots_42 ops++addP pm 10 dom_122 7 roots_122 ops++addP pm 11 dom_218 6 roots_218 ops++addP pm 12 dom_216 4 roots_216 ops++addP pm 13 dzo_42_16 4 roots_42 ops++addP pm 14 dom_120 4 roots_120 ops++addP pm 15 dzo_234_16 6 roots_234 ops++addP pm 16 dom_74 4 roots_74 ops++addP pm 17 dom_202 5 roots_202 ops++addP pm 18 dom_154 4 roots_154 ops++addP pm 19 dom_184 4 roots_184 ops++addP pm 20 dzo_106_16 5 roots_106 ops++addP pm 21 dzo_170_16 5 roots_170 ops++addP pm 22 dom_232 4 roots_232 ops++addP pm 23 dom_114 4 roots_114 ops++addP pm 24 dom_106 5 roots_106 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_250 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_42_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_234_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_106_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_170_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_106 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_248 7 s (0,roots_248.map (·&&&dom_248)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_250 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_248 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_250==dom_250)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_250 gM v ys):RunD true dom_250 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_250 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_250 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_250 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_250 roots_250 goal_250 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_250
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=S_250.noCircuit
def isoMvS_159:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_iso_b isoMvS_159 (by decide +kernel) lowS_63
def isoMvS_183:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 8:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_175
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_123
def isoMvS_189:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 9:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_123
def isoMvS_207:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_207:Lower true dom_207 roots_207 goal_207 7:=lower_iso_b isoMvS_207 (by decide +kernel) lowS_119
def isoMvS_215:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 7:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_111
def isoMvS_219:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_219:Lower true dom_219 roots_219 goal_219 9:=lower_iso_b isoMvS_219 (by decide +kernel) lowS_125
def isoMvS_222:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_126
def isoMvS_237:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 9:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_125
def isoMvS_238:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_125
def isoMvS_243:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_125
def isoMvS_246:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_125
def isoMvS_252:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 10:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_250
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000ffff0000fffe0000fefa0000
def gsh_111_16:=0xffff0000ffff0000fffe0000fefa
theorem lowS_zo_111_16_42:Lower true dzo_111_16 roots_111 gzo_111_16 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xaaaa0000aaaa0000aaaa0000aaaa,0,1),(0xf0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff0000000000000000,0,64)] (by decide +kernel) lowS_42)
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,10),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(4,20),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(6,14),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,10),(8,40),(8,72),(12,13),(12,14),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(18,19),(18,22),(18,26),(18,50),(18,82),(24,25),(24,26),(24,28),(24,56),(24,88),(32,33),(32,34),(32,36),(32,40),(48,49),(48,50),(48,52),(48,56),(48,112),(64,65),(64,66),(64,68),(64,72),(64,80),(96,97),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7ffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|7=>1
|8=>3
|9=>4
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x289ae
|8,0=>0xbf24a3eae91040e
|9,0=>0xfd72af69ede4ea81a2c0
|10,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0fff0f0f0fff0f0f0fff0f0f0fff0ffffff00ffffff00ffffff00ffffff00ff000000ff000000ff000000ff00000000ff000000ff000000ff000000ff00000000ff000000ff000000ff000000ff00ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ffffffff00000000ffffffff00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00ffff0000ffff0000ffff0000ffff00ffffffffffffffff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x5764320576432805b76432057643290576a4320576c3205ba43205432980543210
|_=>0
def sO:Nat→Nat→Nat
|7,0=>6
|8,0=>0x51c6b867
|9,0=>0x670ae11c1b8
|10,0=>0x3b7
|_,_=>0
def wAt:=mkWire dB 13 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1da765db76121769d9761da76e61769db
|_=>0
def oO:Nat→Nat→Nat
|7,0=>3
|8,0=>0x725232
|9,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xffbf7f1f00
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>1
|8,0=>0x93
|9,0=>0x8e3
|10,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_126 9 roots_126 ops++addP pm 1 dom_63 9 roots_63 ops++addP pm 2 dom_125 9 roots_125 ops++addP pm 3 dom_123 9 roots_123 ops++addP pm 4 dom_95 9 roots_95 ops++addP pm 5 dom_119 7 roots_119 ops++addP pm 6 dzo_111_16 7 roots_111 ops++addP pm 7 dom_111 7 roots_111 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_111_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_111 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_126 9 s (0,roots_126.map (·&&&dom_126)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_126 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 4 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_127 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_151_8:=0xff00ff00000000000000000000000000ff00ff00
def gzo_151_8:=0xff00fe00000000000000000000000000fe00ee00
def gsh_151_8:=0xff00fe00000000000000000000000000fe00ee
theorem lowS_zo_151_8_148:Lower true dzo_151_8 roots_151 gzo_151_8 6:=lower_iso_b (d1:=dom_151) (r1:=roots_151) (T1:=gsh_151_8) [(dom_151,8)] (by decide +kernel) (lower_slice_b (T:=gsh_151_8) [(0xaa00aa00000000000000000000000000aa00aa,0,1),(0xcc00cc00000000000000000000000000cc00cc,0,2)] (by decide +kernel) lowS_148)
def dzo_149_8:=0x3300330000000000000000000000000033003300
def gzo_149_8:=0x3300320000000000000000000000000032002200
def gsh_149_8:=0x33003200000000000000000000000000320022
theorem lowS_zo_149_8_148:Lower true dzo_149_8 roots_149 gzo_149_8 5:=lower_iso_b (d1:=dom_149) (r1:=roots_149) (T1:=gsh_149_8) [(dom_149,8)] (by decide +kernel) (lower_slice_b (T:=gsh_149_8) [(0x22002200000000000000000000000000220022,0,1)] (by decide +kernel) lowS_148)
def dzo_171_16:=0xf0f00000f0f000000000000000000000f0f00000f0f0000
def gzo_171_16:=0xf0f00000f0f000000000000000000000f0e00000e0a0000
def gsh_171_16:=0xf0f00000f0f000000000000000000000f0e00000e0a
theorem lowS_zo_171_16_42:Lower true dzo_171_16 roots_171 gzo_171_16 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_16) [(dom_171,16)] (by decide +kernel) (lower_slice_b (T:=gsh_171_16) [(0xa0a00000a0a000000000000000000000a0a00000a0a,0,1),(0xf0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_181_8:=0x330033003300330000000000000000003300330033003300
def gzo_181_8:=0x330033003300320000000000000000003300330032002200
def gsh_181_8:=0x3300330033003200000000000000000033003300320022
theorem lowS_zo_181_8_148:Lower true dzo_181_8 roots_181 gzo_181_8 6:=lower_iso_b (d1:=dom_181) (r1:=roots_181) (T1:=gsh_181_8) [(dom_181,8)] (by decide +kernel) (lower_slice_b (T:=gsh_181_8) [(0x2200220022002200000000000000000022002200220022,0,1),(0x3300330000000000000000000000000033003300000000,0,32)] (by decide +kernel) lowS_148)
def dzo_183_8:=0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00
def gzo_183_8:=0xff00ff00ff00fe000000000000000000ff00ff00fe00ee00
def gsh_183_8:=0xff00ff00ff00fe000000000000000000ff00ff00fe00ee
theorem lowS_zo_183_8_148:Lower true dzo_183_8 roots_183 gzo_183_8 7:=lower_iso_b (d1:=dom_183) (r1:=roots_183) (T1:=gsh_183_8) [(dom_183,8)] (by decide +kernel) (lower_slice_b (T:=gsh_183_8) [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa,0,1),(0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc,0,2),(0xff00ff00000000000000000000000000ff00ff00000000,0,32)] (by decide +kernel) lowS_148)
def dzo_175_16:=0xffff0000ffff00000000000000000000ffff0000ffff0000
def gzo_175_16:=0xffff0000ffff00000000000000000000fffe0000fefa0000
def gsh_175_16:=0xffff0000ffff00000000000000000000fffe0000fefa
theorem lowS_zo_175_16_42:Lower true dzo_175_16 roots_175 gzo_175_16 7:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_16) [(dom_175,16)] (by decide +kernel) (lower_slice_b (T:=gsh_175_16) [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0,0,4),(0xffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
namespace S_191
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,10),(2,34),(2,130),(3,11),(3,19),(3,35),(3,131),(4,20),(4,36),(4,132),(5,13),(5,21),(5,37),(5,133),(6,14),(6,22),(6,38),(6,134),(7,15),(7,23),(7,39),(7,135),(8,9),(8,10),(8,40),(12,13),(12,14),(12,28),(12,44),(12,140),(16,17),(16,20),(16,144),(18,19),(18,22),(18,26),(18,50),(18,146),(24,25),(24,26),(24,28),(24,56),(24,152),(32,33),(32,34),(32,36),(32,40),(32,160),(48,49),(48,50),(48,52),(48,56),(48,176),(128,129),(128,130),(128,132),(128,144),(128,160),(136,137),(136,138),(136,140),(136,152),(136,168)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7ffffffffffffffff
def xsM:=roots_191.map (·&&&dom_191)
def gM:=goal_191&&&dom_191
def NN:Nat→Nat
|5=>11
|6=>65
|7=>170
|8=>338
|9=>177
|10=>17
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xcfb76bc21cb9e058c73e71ca36cc1f4c59e2523c18bf80fd1604bbb
|6,0=>0xfac9bdf31bded05decbcdcfb6bf9fcbcee4bce73b9da4aed18a6ae6a4d058b20e88ef183f8b8271a77fde7600b71fa26f0876dbd169f4065a34636db5ef905e85f5e1265dfb45aff659f8d4eb494a01749a0f4931248525455304389a3e1733d2763990c353c734c043311032cf63206b30754307352b9152adea28ed3263df25f9a253f720dfb207051f33c17d7d128a011bab11b0e0fb350ab800a61e0591903c3c
|7,0=>0x8320e81bec7f70e7e9e07dd8f7d1e77cc707b6cf75c8e759c0740bb733c473251730df718016f6506e12e6dbf767d9e63bab62b8d610225f2dd5f1425eb3a5e9ea5e5675e43d57daf57b4253dde538cd508f84f7824ef024e39c49ea148cce4837c483664831347d8447c32478c5464d74603a45d2b4587f45860454894219d3ff153f1e93eab03e26d3d9f03d9d63c19b3acfc3a5d53a52238a303839437c623783336ff73634b35d6235830356ff344673441133e1f3332e326ae31d703150c307722ea2f2d2fa2a7962a1d9290c328eaf2785e275b42721b2706226cd6268c9246bb239802247c1f80b1f0121ea3b1dc001d5891c18d1c0b31bfba1b97a1ab631a8ba1946118c9318a69184d91619f15c34141601272611c93100e60cad10bb6c0ae5d0a5ae09be309ac207cc107bcb0788a05d79036320349f033ae0062f
|7,1=>0xffc36eb9e6e2ca5d621ad2e2dd2314d109cd0f65cfac4cf633cd1f0ca58ec2056c2018bb7d4bb51fb9315b6cf6a9b08a65a6a61d4a3847a382a9f2969d2c99a43d9a069998f597472956059361a8fe148e68a8b8fd8b2888ab9a8841687f5c87a878720486ac285d39
|8,0=>0x34db634a1c3424933fc33364d32dcc329093250f3205b3203131f5d31b53312b8311de31110310e530b1c30aa530940305052f2da2f1b02e5a42e02d2db942cd0b2cbd92c5162bab52b3b32ad5f2a0cc29a84299852951e291b02828b27ea02750d27106261512546024a3824512242182252c211571f6d11f5961ec7d1e6b11e34d1ddcc1d42b1d0411ce641cd0b1c9bc1c9b51c5101b03719a10199fc1919918ede18e991874616e5816e2216b031641914f9f14a77141bc1374012e87126fa12359122dd11db811da611b6a1086f0fb4e0f37b0eaaa0e92e0e21f0c82d0be730bba20b73a0b1b60a5ae0a08a095d2095a7092d408e9d08ac20869c076c9076a40766007324070d806f9006a2b0686805a8a053d704df404c1a0476903f2003ed303d060348c032f102d8402716025ec01eab01a5301865017370154600a6b
|8,1=>0x7cec97ccf67c3487c1ba79be078cd677211769707614d75ec975e4f75e2b75c917558473fd9735ae72bc970ef7707db6f9886de626ceda6c0496b1f06b1cc6aa2768f09685c66819567e8c67a78658a765838648ad645c964584631c460ee35ffa45fdc15fb045f9ff5f9835f8745e35c5d9b75d4d75d4c45d3815ceaf5bd965b6025a53f595485850057af6578255777d5717f56d48565375532954ee554ec7543145409c53bdb533fb5330b519c2512c650b1d50afb4fe274fad44ef024e1fd4dcb74d81c4d6a54cf8b4c95e4c2684be184bb854b4764b45e4b2324b21c4afd64a9294a6dc49d2a4964147b92479d9477c5473f74513d449bc44143433ba430f14184b411fd40ad63fd523faf23f9f03f93d3f08f3edf33e65a3e1ee3d6513d2d43c9ce3c4be3ba1d3b9f43b6f93b621397c538dc737be13747536a9a36484
|8,2=>0xfd447f7c56f347eee8cbee050ec52be9a2ee241ce0936dc44adbe11d98aed900ed5f70d56bbd0ff8d0770cdd19cd545cc4fccb247cb211ca9cfc6aefc3a5dc31a8c1d5ec1a6fc0491bfb29bde71bbe77ba3fcb9490b68d5b5e42b2401af322ae57bacb7eaa55fa90a2a8725a72c6a6f25a6de7a47dea2b6ea29e0a2417a11709f40f9ced79c9fd9b1fc9a4f09a3fa9839997e7996785961df95ee395906943ca9434390f05906a48fd428ed878e27b8b0f989d59877e387605856ca840cc840438379782a237f8aa7e9dd7dbb1
|9,0=>0x90bcc8fce28ef488e8f68e65a89cd089b3b8507784d1c8423f825f1824b281b40808777cd4a776c677482759ff74c6574aae7491f725ef6f40d6d8c26c13c664a76553f63c016135e612f85f44d5f3675d6fc5d1775cc8d5bd7a5b77e58cc954a68541ae537854f9644f8b74eb564d25a4cb074ba964b0d44a16049a8d490ee45c4745608440f4430a141c56417d840aa13e5983e2283c6193c2313a6ae3a2cb3864835b5b3565d354a23476e33fec3216c30a633046d2f0b02efb32dfae2db9f2bff02ba282ad412abd4296fa292e728cd028960276112758f26f642430f23f4223a7023a592340520f9e208652038f1ff421deb51db981d1541c7061c0521a2bd182d716c1d16b3f168ad153ac150a61396b138dc120be110890e0960dd980d9b60d92d0d4c40c0a209a56092e5050920430f0415303a230303e0135500ddc
|9,1=>0xf3b1bef625e6920e2041d99d9d7066d538dd31abd22a4cffd7c9fb9c79a9c7946c1c0ec06bfbfde2bdbc2ba3f0b9364b6b21b4f1cb2f57b2e5eb2078b1196b0b00b0075aec65ae499ad368a9b39a8918a7647a63ada5a14a59f9a4810a31b6a148da0eb59f3969bb749b2389973398b889879896a559622e94fa8
|10,0=>0xe03e0be20094cff82e517caac74ef86d5896b2b3644615dccf5cc9a410592eaa62e0372145d1deb50b970
|11,0=>0x2bff1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff000000000000000000000000ff00ff00ffffffffffffaaaa0000000000000000ffaaffaaaaaaaaaaffffffff000000000000000000000000ffffffff00000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00eeeeeeeeeeeeeeee0000000000000000eeeeeeeeeeaaeeaa0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0000ffffffffffffffff00000000000000000000000000000000ffffffffffff00000000000000000000ffffffffffff0000fffffffffffff0f00000000000000000fff0fff0f0f0f0f0cccccccccccccccc0000000000000000ccccccccccccccccffffffffffffffff0000000000000000ffffffff00000000ffff0000ffff00000000000000000000ffff0000ffff0000ffffffffffffcccc0000000000000000ffccffccccccccccffffffffffffffff0000000000000000ff00ff00ff00ff00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa
|0,1=>0xfffff0f0fffff0f03333333333333333000000000000000033333333330033000000000000000000000000000000000000000000ff000000ffffffffffffffff0000000000000000ffffffffffff0000ffffffffcccccccc0000000000000000ffffffffccccccccffffffffffffffff0000000000000000ccccccccccccccccffffffffffff00000000000000000000ff00ff00ff000000ffffffffffff00000000000000000000ff00ff0000000000cccccccccccccccc0000000000000000cccccccccc00cc00ffffffffffffffff0000000000000000ffffffffff00ff0000000000000000000000000000000000ffffffffffff000000ff00ff00ff00ff000000000000000000ff00ffff00ff00ffffffffffffffff0000000000000000fffffffff0f0f0f0ffffffffffffffff0000000000000000ffffffffccccccccfcfcfcfcfcfcfcfc0000000000000000fcfcfcfcfcfcfcfcfafafafafafafafa0000000000000000fafafafafafaaaaa
|0,2=>0xffff0000ffffffffffffffff0000000000000000ff00ff00ffffff00fffffffff0f0f0f00000000000000000fffffffff0f0f0f0330333033303330300000000000000003303330333003300f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0c0cffff0000ffff00000000000000000000ffff000000ff000000000000000000000000000000000000ffffffff00ffff0000ffff0000ffff00000000000000000000ffff0000ffff00ffffffffffffffff0000000000000000f0f0f0f0f0f0f0f03333333333333333000000000000000033333333000000000f0f03030f0f030300000000000000000f0f03030f0f0000ff00ff00ff00ff000000000000000000ff00ff00000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0000000000ff00ff00ff00ff000000000000000000ff00ff000000000000000000000000000000000000000000000000ff00ff00
|0,3=>0xffffffffffffffff0000000000000000ff00ff000000ff000000ffff0000ffff00000000000000000000ffff00000000ffffffffff0000000000000000000000ffffffffff00ff0000ffffff00ffffff000000000000000000ffffff000000000000ffff0000ffff000000000000000000ffffff00000000ffff0000ffff00000000000000000000ffff000000000000ffffffffffffffff0000000000000000ffffffffff0000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00ffffffffffffffff0000000000000000ffffffff0f000f00333333333333333300000000000000003333333333303330ffffffffffffffff0000000000000000ff00ff00ff000000000000000000ffff000000000000000000ff00ff0000000000ff00ff00ff0000000000000000000000ff00ffffff0000333333333333333300000000000000003333333333330000ffffffffffff00000000000000000000ffffffff00ff0000ffffffffffffffff000000000000000000000000ffff0000
|0,4=>0xff000000ff0000000000000000000000ff000000ff0000ffffffff00ffff000000000000000000ffffffff00ffff00ffffffffffffffff000000000000000000ffff0000ffff00ffffffffffff00000000000000000000ffffffffff00ff00ff0000ffff0000ff0000000000000000ff0000ff00000000ffffffffffffffff0000000000000000ffffffff00ffff00ffffffffffffffff0000000000000000fffffffffcfcfcfc000000000000ffff0000000000000000000000000000ff00ff00ff00ff00ff000000000000000000ff00ff000000ff000000000000000000000000000000000000ff00ffffff000000ff000000ff0000000000000000000000ff0000ffff0000ffff0000ffff00000000000000000000ff000000ff000000ffffffffffff00000000000000000000ffffffffff0000000000ffff0000ffff00000000000000000000ff00ff00ff000f000f000f000f0000000000000000000f000f000f000f00ffffffffffffffff00000000000000000f000f000f000f00
|0,5=>0x3333333333330000ff00ff00ff00ff000000000000000000ff00ff00ffffff00ffffffffffffcccc0000000000000000ffffffffffffccccffffffffffffffff0000000000000000fffffffffff0fff0ffffffffffffffff0000000000000000ffffffffffffccccffffff00ffffff000000000000000000ffffff00ffffff00ffffffffffffffff0000000000000000ffffffffffffff00ffffffffff00ff000000000000000000ffffffffff00ff00ffffffffffffffff0000000000000000ffff0000ffff0000555555555555555500000000000000005555555555555500ffffffffffffffff0000000000000000ffffffff00ff0000ff000000ff0000000000000000000000ff000000ff00ff000f0f00000f0f000000000000000000000f0f00000f0f0000ff000000ff0000000000000000000000ff000000ff000000ff00ff00ff0000000000000000000000ff00ff00ff0000000000ff000000ff0000000000000000000000ff000000ff00
|0,6=>0xffffffffffffffff0000000000000000fcfcfcfcfcfcfcfcfffffffffcfcfcfc0000000000000000fffffffffcfcfcfc330033003300330000000000000000003300330033003300333300003333000000000000000000003333000033330000fffffffff0f0f0f00000000000000000ff00ff00f000f0000f0f0f0f0f0f000000000000000000000f0f0f0f0f0f0000030303030303000000000000000000000303030303030000333333333030303000000000000000003333333330303030ffffffff000000000000000000000000ffffffffff00ff000000ffff0000ffff00000000000000000000ff000000ff000000000000000000000000000000000000ff000000ff00000000ffff0000ffff000000000000000000ffff0000ffff00ff00ff00ff00ff000000000000000000ff00ff00ff000000000000000f0f0f0f0000000000000000000000000f000f00ffff00ffffff00ff0000000000000000ffff00ff00000000ffff3333ffff33330000000000000000ffff3333ffff0000
|0,7=>0xffff0000ffff00000000000000000000ffff0000ff000000333333333333000000000000000000003333333333330000ffffffff333300000000000000000000ffffffff333300000f0f0f0f0f0f0f0f00000000000000000f000f000f000f00fffff0f0fffff0f00000000000000000fffff0f0fffff0f0ffffffffffffffff00000000000000003333333333330000ffffffffffffffff0000000000000000fff0fff0fff0fff0333333333333333300000000000000003300330033003300000033330000333300000000000000000000330000003300ffccffccffccffcc0000000000000000ffccffccffccffccffffffffffffffff0000000000000000ff000000ff000000cccccccccccccccc0000000000000000cccccccccccccc00ff0fff0fff0fff0f0000000000000000ff0fff0fff00ff00ffffff00ffffff000000000000000000ffffff00ffff0000000000000000000000000000000000003300330033003300cccccccccccccccc0000000000000000ffccffccffccffcc
|0,8=>0xf0f0f0f0f0f0f0f00000000000000000f0f00000f0f0000ffffffffffffffff0000000000000000ffffffff0000ff000f0f0f0f0f0f0f0f00000000000000000c0c0c0c0c0c0c0c33333333333333330000000000000000333333333333330000ff00ff00ff00ff000000000000000000ff00ff00ff00000000ff000000ff0000000000000000000000ff00ff00ff00f0f0f0f0f0f0f0f00000000000000000f0f000f0f0f000f0000000000000000000000000000000000000ff000000ff00fafafafafafafafa0000000000000000fafaaafafafaaafaffff0000ffff00000000000000000000ff000000ff00ff00ffff00ffffff00ff0000000000000000ffff00ffffff000000000000000000000000000000000000ffff00ffffff000000000000ffccffcc000000000000000000000000ffccffcc0000ffff0000ffff00000000000000000000ffffff00ff0000ff00ff00ff0000000000000000000000ff00ff00ff0000ff00ff00ff00ffff0000000000000000ff00ff0000000000
|0,9=>0xffffffffffffffff00000000000000000000ffff0000ff00ffffffffffffffff00000000000000003333000033330000ffffffffffffffff0000000000000000ff33ff00ff33ff00f0fff0fff0fff0ff0000000000000000f0fff0ff00000000cc00ff00cc00ff000000000000000000cc00ff00cc00ff00ffffffffffffffff0000000000000000ffccffccffccffcc00000000000000000000000000000000ffccffccffccffcc00000000000000000000000000000000ff00ff00ff00ff00ffffffffffff0000000000000000000000ff00ff00ff0000ffffffffffffffff0000000000000000ffffffff33330000333333333300330000000000000000003333333333003300333333333333333300000000000000003333000033330000ff00ff00000000000000000000000000ff00ff000000ff0000000000ffffffff000000000000000000000000ffff0000fff0fff0f0f0f0f00000000000000000fff0fff0f0f0fff0fff0fff0fff0fff00000000000000000fff0fff0fff0fff0
|0,10=>0xff000000000000000000000000000000ff00ffffffff333333330000000000000000ffffffff33330000ff00ff00ff00ff000000000000000000ff000000ff000000ffffffffff00ff000000000000000000ffffffffff000000ffffffff00ff00000000000000000000ffffffff00ff000000000000ffff0000000000000000000000000000ff000000ffffccccffffcccc0000000000000000ffffccccffffcccc00000000ffff0000000000000000000000000000ffff0000ffffffffffffffff000000000000000000ff00ff00ff0000000f000f000f00000000000000000000000f000f000f000000000000000000000000000000000000ffff0000ffff0000ffffffffff00ff000000000000000000ffffffffffffff000f0c0f0c0f0c0f0c00000000000000000f0c0f0c0f0c0f0cf3f3f0f0f3f3f0f00000000000000000f3f3f0f0f3f3f0f0ffffffffffffffff00000000000000000f0f00000f0f00000000ffff0000ff0000000000000000000000ffff0000ff00
|0,11=>0xf0f0f0f0f000f0000000000000000000f0f0f0f0f000f00ffff0f0fffff0f000000000000000000ffff0f0fffff0f00fffffffff3f3f0f00000000000000000fffffffff3f3f0f0ffffffffffffffff000000000000000000000000ff00ff0000000000ff00ff00000000000000000000000000ff00ff000000ffff0000ffff0000000000000000000000000000ff00ffffffff0000ffff0000000000000000ff00ff000000ff000000000000ff000000000000000000000000000000ff0000cccccccccc00cccc0000000000000000cccccccccc00cccc0000ffff0000ffff00000000000000000000ffff0000ff0000000000ffffff00000000000000000000000000ffffff00ffffffffff00ff000000000000000000ffff0000ff000000cfcfcfcfcfcfcfcf0000000000000000cfcccfcccfcccfccffffffffffffffff0000000000000000ffffff00ffffff00ffffffffff00ff0000000000000000000000ffff0000ff0000000000000000000000000000000000ffffffff33330000
|0,12=>0xffcc0000ffcc00000000000000000000ffcc0000ffccffffffffffffffff00000000000000000000ffcc0000ffcc333330303333303000000000000000003333303033333030ffffffff333330300000000000000000ffffffff33333030f0fff0fff0ff00000000000000000000f0fff0fff0ff0000000000000f0f00000000000000000000000000000f0f000000000000000000000000000000000000fffffffff0f0f0f0ffffffffffffffff000000000000000033003300330033000000ffff0000ffff00000000000000000000330000003300ccccffffccccffff0000000000000000ccccffffccccccccf0fff0f0f0fff0f00000000000000000f0fff0f0f0fff0f0fffffffff0fff0f00000000000000000fffffffff0fff0f0ffffffff0f000f000000000000000000ffffffff0f000f0033333333333333330000000000000000030003000300030000ff00f000ff00f0000000000000000000ff00f000ff00f0ffff3333ffff30300000000000000000ffff3333ffff3030
|0,13=>0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0c0c0c0cfffffffffffff0f00000000000000000fffffffffffff0f0333333333333303000000000000000003333333333333030ffffffffffffffff0000000000000000cc00ff00cc00ff00000f000f000f000f0000000000000000000f000f00000000f3f3f3f3f3f3f0f00000000000000000f3f3f3f3f3f3f0f00000000000000000000000000000000000000000ffffff00ffffffffffffff000000000000000000ffffffffffffff00ffffffffffffffff00000000000000000000ff000000ff0000ff00ff00f000f0000000000000000000ff00ff00f000f0ffff00ffffff00f00000000000000000ffff00ffffff00f0000000000000000000000000000000000000ffff0000ff00ffff0000ff0000000000000000000000ffff0000ff000000ffff0000ffff0000000000000000000000ff000000ff0000fffffffffff0fff00000000000000000fffffffffff0fff0ff000000ff0000000000000000000000ff000000ffff0000
|0,14=>0xffffffff0f0f0f0f0000000000000000ffffffff0f000f00ffffffffff0fff000000000000000000ffffffffff0fff00fffffffffffffff00000000000000000fffffffffffffff0ffffffffffffffff000000000000000000ff000000ff0000ff00ffffff00ffff0000000000000000ff00ffff00000000ff00ff00ff00ff000000000000000000cc00cc00cc00cc00ffffffffff0000000000000000000000ffffffffff0000000000ffff0000ffff00000000000000000000ffff0000ccccf0fff0fff0fff0f00000000000000000f0fff0fff0fff0f0f0f0f0f0f0f0f0f00000000000000000f0f0fff0f0f0fff0ffffff00ffffff000000000000000000ffffff0000000000ffffffff0000ffff0000000000000000ffffffff0000ff000000ffff0000ffff00000000000000000000cccc0000ccccffffffff0000ffff0000000000000000ffffffff0000ccccffffffffffff00000000000000000000cccccccccccc000000ff00ff00ff00f0000000000000000000ff00ff00ff00f0
|0,15=>0xff00ff00ff00ff000000000000000000cc00cc00cc00cc00000000ffffffff000000000000000000000000ccccccccffffffffffffffff0000000000000000fffcfffcfffcfffcffffffffffccffcc0000000000000000ffffffffffccffccffff000000ff00000000000000000000ffff000000ff0000ffffffffffffffff0000000000000000ffff000000ff00000f0f0f0f0f0f0f0f00000000000000000f0c0f0c0f0c0f0ccfcfcfcfcfcfcfcf0000000000000000cfcfcfcfccccccccf0f0f0f0fffff0f00000000000000000f0f0f0f0fffff0f0ff00ff000000ff000000000000000000ff00ff000000ff000000ffff0000ffff00000000000000000000ffcc0000ffcc030303030303030300000000000000000303030300000000ffffffffffffffff00000000000000003333333330303030ff00ff00ffffffff0000000000000000ff00ff00ffffff00ffffffff000000000000000000000000ffffffff0000ff00ffffffff0000ff000000000000000000ffffffff0000ff00
|1,0=>0xffffffffffffffff0000000000000000ffffccccffffccccff00ff00ff00ff0000000000000000000000ff000000ff00ff0fff00ff0fff000000000000000000ff0fff00ff0fff00ff33ff00ff33ff000000000000000000ff33ff00ff33ff00ffff0000ffffff000000000000000000ffff0000ffffff00ff00ff00ffffff000000000000000000ff00ff00ffffff0000ff00ff00ff00ff000000000000000000ff000000ff0000f0f0f0f0f0f0f0f00000000000000000fffff0f0fffff0f000000000000000000000000000000000ffffffffff00ff00000033000000330000000000000000000000330000003300ffffffccffffffcc0000000000000000ffffffccffffffcc333333003333330000000000000000003333330033333300000000000000000000000000000000000f0f00000f0f0000ffff0000ffff00000000000000000000ffffff00ffffff0000000000000000000000000000000000ffffff00ffffff00fffffcfcfffffcfc0000000000000000fffffcfcfffffcfc
|1,1=>0xffffffff000000000000000000000000ffffffffffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x20080c001289010150b08c020600020180100078440904054020600084400d0f8100401000781005010040c000e86c0a0406068000a028100418008180008028101801058241005070080206040540206000501013090082200028100e02030000a04010400c0f028101c0c008180a0407008020602810060c008001a040602c1409040140e02030000a04018080200
|1=>0x818000f06810182b000781205020080206000d01005010040c001982008010300028090d814080200800640818814040103000261b028100411000205a02088680008028b81801030005a12028100411000200a0c008005809028340802080180a0d020080c0015014080c0c0040c00040145202008180028068040c001382410050609802000f020020600050120d
|2=>0xb01402060010010050c8040c00100200a0c1f8040c001e8140802008180008028080206000f01005010040c001d8201801000785e09040e8180100078120809848181100024240d020080c0005014080c008180034028100406000281e081c8140401030001013060180038048206e05010040c000681018000f02812080983002001b0240a04010ac0c00078140835
|3=>0x4814181900818002f26014080200818000d258040c0013824940d008180027048202612010040c0004014040103000680824814040103000380d02030020b048140401030005e48040588e01030001205020fc02060003c1005060040c00230200a020c0040c0002834080c0d0004808028080206001141013028082206000708605010040c000e0340401030008408
|4=>0x28340802238040c0002810040103000a60f040540a0c118040c000283402060009c120d0203002062b024aa0d020300206000247a05020300206000241a0406004001e298241005060043400128701a04060042e00048200a0c00818003c048141a0401018000a06810180600028400902834080c0082c1208028306a0103000380d020080206000809c0d00818004d
|5=>0x2f8b40a0406004001e048141a04010305606000200a04060043400128202605060440c00048200a0200818002f04014bc0c008180009040147402008180008028304c06000881a0200818003e179740a0406004340006810181003024105c098300206000240a0d020306a01030001a0406018002a048200a0c008180038048141a04010180022298481a04010040025
|6=>0x3408020082c1205020080206000881e67028100401030001012028302201000241005011100206000141a04010300c0005034080c030004809068040c00320249212068100401030000a0d02008c601030001a0406004001e110241005060040c00228240a04010040c00310141a6102008020600034c004010040c00128481a0406018002a048200a0c008680c00
|7=>0x1381a01030004e09028100401030007c0f0986c0a04010040c0004058260c008180009040341801000c8da09040b404010d018001c02834040103000d805068101826008003c2d028100411030001a04008180014048140802358040c00068101801000b04409040b41806001a41205020304c06001a01a0406004001e1f0245a12028100401030001012028080206
|8=>0x4014187500818000809014080200818000d020300274000245a0d02008221a000141a04170300206000202a16028300206000141a60020080206000141a0406004002c048200a02060040c00178200a3a010300206000141a7202008020600034040c00818003e1783408700100434000401418010b800120816830de0600024dc05020080206000141a04148080206
|9=>0x2834080200818000802808020600104387d028300206000241005010040c003e0c40a04060040c00048585a05020304c06000200a79060040c001c834080c0081800092c034f657060980c000d814080208804000d020080206000f8400d02008021a00094104302830020600024100d060043406001e8102d3c8300c0004834080200868007706810ec0c030001409
|10=>0x3000760d3d810040100078120d020e8180100078121309034080c0880012080a8480a0c00818001c069fc1801030001205020080206001f8b605068100401030001013060440c00048202612060040c00048200a020c8040c00041240a0c0081800090e06c0a04010040c001c8141a04010040c0009834080c0300070090283408021f8040c003e8140802008180037
|11=>0x2281208168082206000241a040621c0c09028340802430040c000e034080200818002537014080c00868006e028101826030001005060640206000b40a040604434000e034520c008180009028350804060040c00040541801030010609068101801030010409168480a04060980c00040141880008180009040540a0c008180020040584601030001205068100401
|12=>0x68101806000e0a60902834040103000cc2f2c0340890030011e09470141a04010040c00040141801030011a0d020300200460242c0d0f8100401030000a7b0200802060003c2a05060040c003f0701a040108c02060006c0a04060444c000e0141a02220040c0004014041100818000506980080c00868000d020040c004588012080b0104601030001208028300206
|13=>0xd018005f0986c0a040604400090b034080c03000140902834080c130180038040140802008180025028340802008180042168480a0406044000902810040103000900d0203002004aa501205068101806000a81213068101801000781208068300c00368281208028080206000945a05020300c001c02410050114802060003408910601800090283408022a0040c00
|14=>0x298241a044e8300206000241a0406270020600024381b02810180103000123902834080c0081800090681004010326c00093e814080c0081800091b8141a04060040c0004834f604010040c00078241a040611c0206000241a044c8080206000541a0c00818007e048201a0c00818003204834080c00818009704814080c0c8040c004b0141a04010040c00040340401
|15=>0x54810040c00868000d010043406002a01a04060040c0053824100d060040c00530240a0d0200818010300044a406810180103000120806830020600234120d0200802060028c122d0695c08900601800090e0141a04060043406000201a0c510040c0004924260d02030020600024b00d02030020600284120d0203002060027c121b0681004010d0001a04060180022
|16=>0x188120d008180081578241a040600434003c024ce0d020080206000202605060040c0004ab81a04060040c0004ab01a04060040c00048201801030005e0906968a2010300012081d0300206000241a7b2b8304c06001541a04060040c00048701a04060040c0010824fa0d2b8300206000241a04060040c003d0240a0d42810180103000120d020080206002a8120d
|17=>0x48581a0400818004104834080c318040c000483408b4060040c0004834080200acc0c0004834082e060040c0004835640c0081800a8048200a0c00818006d04834c204060040c00048581a0400818007c048141a04010300206000f81a04060040c00588240a04060040c003f025600d02030020600024b60506810180103000120d021c00401030005a0d020080206
|18=>0xb034f604060040c00048201a9800818004f04834080c0081800b6048200a76060040c00049601a57060040c0029824100d060040c00200241a0401044021a000141a04060040c001e0241a04010040c0012834080103000820f0486c0a04060040025048201801030016a090695c180103000fc09040541a0c00818006d048b40a04060180022048340802088040078
|19=>0x4814080c00818000f04834080c00818006d1f0245a05020080206000358004060040c00048200a0200818000d5f01018010300012bd3e834080c008180009068101801030017409040341801030011609558340898008180009069ec080c00818000f048201a02290040c000483404b90081800a804834080c00818006904834080c00adc0009040341801030012809
|20=>0x624c02060002410c9060040c0004834080c0081800c704834080c00b180c0004834e404060040c0004970260d02030020600025880d02030020600025860d020080206000241a04060040c00610240a0d2d148020600024380d0203002060009412050681018010300070090681004010d018007104014080c00818006d048201a0c0081800c104834080c0081800aa
|21=>0x24100d010040c00360240a0d0203002000f0241005021d8180103000120d02030020600338120d02008a2010300012cc06810180103000120d30010180103000120806831960103000121302834080c08818000902834080200818002f06810ec0c00818003e048141a042f030020600024100c0081800ca048141a041d0080206000201a57060040c00368241a04
|22=>0x2008020600035aa04060040c0004834080c0081800d4048141a04060040c00228241a0469808020600024380d0203046010300012080695cec0c00818000906810181100800f00918834080c0081800090681004010300090090681018015981800092c034ae0c00818006c049741a04010040c0004b441a57020300206000241a04063400206000241005060440206
|23=>0x683022010d000120806830222603000120d0200802b303000f80906810f20c08818000906810180103001b6090d814080c00868000d062e40206002a0120d02008181100868000d02031b40103000fc09040b4180103000d80906810180103001b209068040c004094012080283002060008412050681004440081800d8069440206000241a040600434060035c1005
|24=>0x71034080c008180009168340802008680c0004034180103384000906810180103001c00906810180103001be09168140802060040c0004034180103001ba090403404010d018000506810040103000400d2d0040c0013824100d060040c002f8251c0506810180103000120d0203002066e000120d02008320103000125906810180103000120802a401801030001208
|25=>0x20080206000241a04010043406001980a0d02030021700024100d4c0040c00408241a04060040c00740245a0d02030de0600024100d0639c020600024720d020300206000246e0d020300206000240a0d02030a80103000120d2b8101801030017e09040080206002a0120d02031cc06000242c1306810180103000120506b94080c008180009720340802008180009
|26=>0x60040c00048201a0200818007e04820180103001240906810180103000900902834080c378040c00068040c0013824100d060040c003d1f8120806830020600348120d170300206002a0120506810180103001160906a14080c0081800090681018010d0180040028340802060040c00179601a043c8040c00048141a041d008180103000b01b02030021a00025d20d
|27=>0x68300206001b4120d02008020675000100d02008021a03000fa0d02260020600024100502008180103000b01b2b810180103000120802830020600094120506810040103000a00d0200802000f024b60d02030020600025b00d020040c0020824100506148020600024100c008180083048b41a043c8300c00048340873060040c00110240a0d02030ea01030001013
|28=>0x68305606000240a0d020080206001043808069d81801030001208068306a0103000120d02008021a001e17a0d020300206000240a0d020080206001f01a04060040c001e0241015028300206000141a04398300206000241a04060640206000241a024c0040c00540205a0c00818007e048141a043c83002060006c1a04061bc0200048141a04758300206000243808
|29=>0x3000f8a80484c240d02030020600025e00d020080206000241a04060040c001c02492050681018010300012050681018010300060ef0681004010300012ee06810180103000121c068e8180103000120d3c8300206002a0121c0b034080c00818000904014180103000440976834080c00818000906810040103001d808010300206002a0120d022600206001f81208
|30=>0x8180068048340801030004220048b40a0406004340600034080c00818004504b0c1a57020300206000241a04060040c0053024100d060040c004b8241a04480300c00478241a04060040c00798242605068100401030001a0406004001e0483404010300082a80484c1a04060440c0004834085e060040c000483408f2060040c0004bc41a04060040c00048340401
|31=>0x34080c130180068048201a0c318040c000483404f60081800a804835ca04060040c00048b41a04063dc0c0004a58fa0d02030020600024100c008180081540242a0d020300206001b4121606810180103000a60906810180103000422f048201a02220040c00048205a0c00818004f04834183f0081800a80483408020081800f504834080c0081800f404814080c
|32=>0x8180062048141a0406004002536824860d02030020600024b00d0203002060023c120d0203002f803000121c028340802008180058069ecae0c0081800090e034080c008180020048201a0c0081800690484c0a0d02008180103000dc0d02008020600024100d063140206000241a04010040c00500241a04060042e00048141a7b020304c060006c0a04060980206
|33=>0x331601aa92b830020600025de0d020300206001f0124906810180103000120d023e81801030001205068040c00279401208028e818010300012080b014080c00818000906810180103001f209028355204060043400040b5200c03000121206810180100094120506810184700818000902834080c0081800d72c034f604060980c0004834080c658040c0004834080c
|34=>0x10040c00360b41aa90203022000484c3605020300206000245a05020302206000241a047e8300206000241a04010040c003f0245a120281018010300012fc0695c080c008180009090340802008680c0004014182600818000d02260020600204120d02031ce0103000121602834080103000820902834080c318040c00048201a020c8040c00048141a04010040c00
|35=>0x60040cea000241a043b0304c010300012080681018010d018000902834080c0081800500486c1a0406098020600024100d3b0300206000241a04010040c0027824360d02030222600024100d010440206000240a0d02030020600364120d2b810180103001ac090d814080c0880400090681018010d0004a0916834080c08868000902834e404060040c00048141a04
|36=>0x220120d020300206003f8120d020300206002fc120d020300206003b0120d021e4040103000125806810180103000d809028355204060040c00048141a04060040c00208241a044c044020600024100d020300206001b4120d020080206002ec120d02008880103000120d0203002060003c120d00818004f280241a0c4c0040c00540242c0d020300206000241a04
|37=>0x6c080898008180009098141a04060040c0004834080c00819360004834080c00818002f04834083a060040c0004834080c0081800af048360204060040c0004834b404060040c0004834080c628040c00048360004060040c00048b41a04528300206000241a04060040c007f824380806830020600024100d06044020600024100d021d8180103000120d020300206
|38=>0x6810040103000a00906810184400818000904034080c088040c000499c1a044c0040c0004834b40400818004104834080c3a8040c0004834080c008180103048b41a044c0040c00048141a04060040c0036824100d48030020600024100d4c0040c0004834080c0081800a3049603604060040c0004834080c378040c000483408024c0040c0006810040103000ca09
|39=>0x2240180103000120806811300103000120d02008020600104120506810040103000100d060040c00298241a5a548300206000241a04010040c003e024100d06098020600024240d020300206000241a04060040c0082024100d060040c00350241a043c8300206000240a0d021d8180103000120d02008184400818000906811300103000a60906810e098008180009
|40=>0x81800092c034080200818000961834080c00818000906811300103001a4090403418980081800090e0141a04060040c0004834080c00818010904834089800818006c048141a04060440206000241a04060040c00650241a04060040c00180241b08020300206000260e0d020300206000241a04060040c0083024100d061480206000241b0502030020600024100d
|41=>0x3d95c18010300012080681018980081800090687c080c008180009069681801030015009028340802060040c0006810ec0200818000906968080c008680c000483408760081800bb0483408d3060040c00048340802060040c003e0241a04060040c003e0245a0d020300206001b0120d0203002060020412050681018010300042096c034080c00818000906812140c
|42=>0x3000120d0203002060035c120d5495c180103000125806810020600104120d2d1480206000241a04063d8020600025bc2d0681018010300012de040341801030001205068101801030004a0909034080c008680c00048141a04061480206000241a04060040c00340241a04063dc0206000241a7b020304c06000241a57020300206002ec120d0203002060023c120d
|43=>0x486c0a04060040c00048340802008180053048340802008180066049601a0400818006d04834180103000a0a8048b41a04010040c00048201a020081800090681018010d018005004834090c060040c00048361604060040c00048355204060043400048340890010040c00048141a040608c020600024b00d3d810180103000120d3d8300206002a0120d020314401
|44=>0x2b810180103000da09068121a0c0081800090d834080c0086800092c034ae04060040c0004834080c0081800c1048340899060040c0004834ae0c0081800a8048201a04010040c0004834089a060040c00048201a5a060040c00049601aa9020300206000241a04060040c00108240a0d02030021a03000102d060040c0004834080c00818004004bf01a04060040c00
|45=>0x30014209068101801030004a0906810181113018000916834080c088180009069ec089800818000906810040c008180066048361e04060040c000486c1a57020300206000241a04480302206000241ab2020080206000241a04060040c00870241a04060040c0035024102d020300206000241a04010040c00360241a04060040c0071824b00d02030021a03000120d
|46=>0x2d010180103000120d020080206000241a0c130040c00540245a0d02030021a03000120d4c0040c00540245a0d54810180103000120d02030020600320120d548113001030001205068101801030005e0906810040c00818006c048141a5a020300206000241015068300206000245a0d02030020600328131006810180103000120806810040c008180009068101801
|47=>0x34080c00818000902834080c0081800090681018520081800090681018110081800090681018010300150090d834080c00818000906810180103000da09068300206002a0120d02030021a03000120d2b810180103000120d54810180103000120d02030020600104120d3d810180103000120d02008180103000120d020300206002ec120d0203002060013c120d
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0xf1806cc030601530091803cc018600930031800cc0006
|6,0=>0xfc387c5c3d4e1e370ee38755c39ce1c770e0386e5c364e1ab70d238675c32ce18f70c438605c2f4e17370b638595c2bce15770a838525c284e13b709a384b5c24ce11f708c38445c214e103707e383d5c1dce0e7707038365c1a4e0cb7062b02f9c16ee0b070553028dc138e09570473821dc102c07a7039b81b1c0cae05e702bb8141c092e0427
|6,1=>0x1ff7
|7,0=>0x1f040f6207a2e3c981e0c0ee9c766e3ac71d240e75c72ce38e81c340dfdc6f2c37181b538d8a06b6e35381a638d19867d0336819740c9a063ee3178187c0c1e05ff02f78177c0b9e05bf02d8716840b25c584e2bb715a38ab9854d029e814bb8a3e050f0280713c409c204d10261712d3894a04950242811db88ce04570224710e40855c41ce2068
|7,1=>0x2e5b9711cb7905b482d6416920b39059482c641615cafb057582b6c15960abb055582a73951a0a7ee5378298394a20a4105188288414220a02e4f98279393aa09c6e4db8269c1331c98904bc825ab92b6094ce49e824b4123dc910e480823cb91c608d4e463722dc114e08970443821dc10ce08570423820e39055c81ce40771ffc0fe1c7e103e88
|7,2=>0xe18e704837e41bd20dd906e4836e41b520d9906c5735ec1ad60d5b06a5834f39a5a0d1ee6887340419e20ce10668833041965cca4e64a8321418edcc67062c731241875cc2b060d8302c17f60bece5f062f4417820bb2e5d27
|8,0=>0x487ca41e11ff08f78477c239e11bf08d78467c231e117f08b784574a29a113d08968446ca219d0fb287674374219dd0bf08578427c2121d082e83a7419ba0ae1045281a840942026500307f983f939faa0fc507d993e8c1f260f8307b893d7c9e9e0f3d279593c6c1e19cefd077683b741d964eb9275483a641d0e4e7527328395b9c8e0e3707138
|8,1=>0x58bc2c3a560d0afe857b42bba15cb2add856ac2b36158b0abd855a4aab215472a9a9549baa2e15052a7a8539ba9ae14c70a5b85294a92a14850a3a8519428a654412a188507ca81e13ff09f784f74a79dd3bf09d964e8c2722538109b884d84269e533f099784c7c2621d301097794b7c259e12bf095694a74251dd27d29377497c249e1240e9188
|8,2=>0x68dcb44e1a152d02867d433ca19d50ce2866d4334a19950cc2865d432c659512ca1764d3b24659112c80863c431c218d10c60862c4314218910c41761cc30c9d8550c21960cc304618130c0185fcc2fc617d12be085ec42f45d7930bc185dc4aec217510ba175ccc2e461714eb8285bdbadce16d70b6295ad42d4656912b40859c42cc216510b1f9
|8,3=>0x78dc3c4e1e170f03877dc3bca5dd50ee2876ccbb461d930ec1875cc3ac61d512ea0874c43a45dd130e81873d3b9ca1cd32e61872d3b94a1c950e42871dbb8ca5c550e23770dc384e1c170e0296fccb7c9dbd50de286ed437465b930dc186dd3b6ca1b550da286cdbb64e1b152d8286bdbb5ce1ad8ed6486ae435599a9b2d45869ec34d25a590d248
|8,4=>0x894c44862231310f9883c43fe21ed30ed9872c437621ab10cd88624c2f2216910ad7852c42726129108b9841c41ee20e5306a8830cc16620a31048981fcc0de205d3026880f4405a201ef00787ffc3fde1fdf0fe787efc3f5e1f9d2fc687decbed25f572fa387cdc3e4e1f170f8387bdc3dce1ed70f6387ad4bd4a1e950f42879d43cca1e56ef238
|8,5=>0x237d11b688d6cc6926339119488c64460e62f7117388b54c58a22b5115288a4cc502627111317
|9,0=>0x9e544f0a277513b289d544e8a2733339099c444e0226f1137089b3ccd7e26af134f89a3c4cfe266d332e8993bcc7e262f130f89843cc0225f112ef9973c4b7e25af12cf8963c4afe256f12af89534ca7a252d128e8942cc9f624eb126d8932c497624a9324b99214c8ea246332298910c48662424f20a8901447ea23e331e898efcc75a639d11c68
|9,1=>0xaebc573e2b90f5bf9adbc56be2b4f159f8acb4d6366b0b157d8abac55b62acb155e7aab455366a8b153c9a99cd4aa6a45151a8a89454266a0314f98a784d3a229c114d88a684531e697f14b78a574d29a293b34958a464d21228f914748a364519228b914539a25c510e287534328a154508a283514128a054500a27f333f189f4c4f89e7b513d28
|9,2=>0x176a8bb0cdd69eea337498ba0c5ce26e5f37269b8f45c566e1b17049b7e45bd22dd916e48b6e45b4e6d9716c29b5d45aca2d5516a28b4d45a4a2d1516819b3c4d9c22cd1165f9b2bc593e2c8f163f8b1bc58be2c4d361e8b0b4583dec0f15ff8afbc57be2bcf15df8
|10,0=>0x17f08bf445f822fb117d08be445f05ef7317b18bd4c5e862f3317918bc4c5e062ef317727
|11,0=>0x17f87
|_,_=>0
def wAt:=mkWire dB 273 192 0xffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x60070280a040080681102035060bf02812060fb048310281302805020350281906825028670400802035108810681102832028330602502805048350681106025008190680503025060c117825028120602502819068250280704831158010e00402811048350281906811108810283202833068250e007028110682503025028640400804831068110b8010b01802831068250602502805020350281906825
|1=>0x2813048350b01b06809060250281b048350481902035048350294b06010048310e00702811048350b8010b018028310682504945060200483502035028110682513825138352813d0601202032040080281204831010fb048310281306025028050203502819068250286704008068110602506825028310483502864040080682506811060250281b020350602502805048350691102008028110490502831
|2=>0x28120483506811060bd02812048350681104831028100483502807020350483500825048310281202813048350d811030250682503035158010e00404821020350681113035010700281106825060252d807090110d825030350b007028310483502035030950281b06825060250281204835010370483104835020070482206811028302d14b0203106825020302c8032c15d06831020250208306951060fb
|3=>0x2819068250b8010b0180680906025028070680a068250602504831100350283206825020350281906825068110200806825060250e007028110602530007020950281b06825331950200a0200b060250d03503025060250e030028110682511812068110283006825048351680a06805060250682506025020350b01b0283104835008350e004028110682506025068110281b0280502035048350483106811
|4=>0x483502035068110d00504819008350d805060250682503035048310208302832138352813d06012020320483102813068190602502805048350681102831048350601b04821068050203503025060250483104835008250b01b028310682500835060250682500819108810283202833068251680806825068050602506805031aa0400702035030b6008350483500825028190682506805060250483102035
|5=>0xb0200283104835020350497d0d022048190203500835060990203500825021e2048190101b060250e007048210203504835290250601002035048310203502819068252c8182c15d068310202506025008190680503025060c11782502812048220283102095060250281b068253981b06089028070281204835048310281004835048310283006825048310281202813031c50106b03025060250b01802831
|6=>0x2819068111682500835030050280502035028190682504008068250681106025068190281106825060250b007028310280504835010bf060250281204835069b104831048350201b048310681106825060070281136035048350201b04835068110100706025148350208302832068250480502831048350483506099020350082502025068310200500825030050602506825030350901b0d0350302506025
|7=>0x4831028130483506825060250d80503025068250303504835068450300500825048350102006811060250081906825068050302502811068254282702085028333b0370402702035060190281900835048350082502a07060220203504822028320283002831048350203502913020080682506025020050b01b06809060250b01b0283102810028190280504835048220203506825068250401b0483102035
|8=>0x68110602549805490320695e02025060fb0483102813048350200706809060052b8070481106035068250d00704819020352c81b2c15d068310202501035049ee06025020050682501037060250200506825048220401b020350281106825008190082506825030350682506025060250203504835030050281b02830028310203502035060eb02810030050602500835020354480100a232b83202025010fb
|9=>0x201b36035048350201b029050682506007010370602502005060bf02812048354d0270101906025048220401b020350e01b048210203504263048320203504008068250681106025020350280506825028310682502035060250281b068251d00a0483102810048350281906825078130680a0682506025020252d80709011028190e007048210203502035060250281b068250b00702831048350203006825
|10=>0x78100680a06025060250302502019020370302506025408250602202035061aa04007020350483102807048352c29504812060350d0070481902035060253b00706019048110083506005028110682503025009b10201b0203513035008250494d060350200704a812c013060350303503025060250280704835020074f031049b10201b02907068250600702811068250303502949068250203006025061b3
|11=>0x602504831028132c29704812060350401b0483502035049f6360350201b0901102819068254c02503261060271680a06805060250602206023020354d01b060690302506a6106027060250681102805048354a0352b81b02025568352b8300202506811028120483506011060200203502810048350203502005048110082504aad0693d060120682536035048110201b049f90401b02035020850283306825
|12=>0x2035060190200704811060350490506811060070483103025008190294b06825020300281b06825060250680a06007060250281b0682503035020352d037060110401b048110203504822068110601b008350280704835030050101b060250600706809060250e03004821020352c15c0683102025031f10100706025060c154025020372b831068120202506811068250601b0294304835020320100706809
|13=>0x61ee02005020350203c0680a060250b037028310682502813068250601b068250680506025021a1030b600835068250681106025022fd2c00706035009f5360350201b5e0135d825060370e0330482102035048320693d06012010370200506025020300681106025012a30681206025040470300502035032e32c012060352b81b04811020350200506809060250483206012020350b013068090602506825
|14=>0x41070681106007008190280504835060250281204835028130483506019060bd0281204835069aa04007020350483102810048350601b0481102035490320695e0202516827008350203502322368250601b030f90281304835118110283006825130350082506b150093d060120602506905060070310220825060070203106825020300281b068250b00702831068250106b030250602506811068250601b
|15=>0x8352b96204811060350208f0283006825060252c010060350281102830068250202506019020350101b0081906025690350226306027078130680a06025031f101007060250201b06831020250206d06025030350481148035060050208702833068250203504835030050201b04831020350b01b028310682506825060190203504b3d3b01306019040300681106025668353d81b02005020950281b06825
|16=>0x61b30201b0400804831020352c15d0683102025068250203506005020350302500819068110300500825031f101007060250609903005008250608a0280704835030250682503035012a30681206025048310302500819009f90401b0203506811008350201b0296a068250203106022060130203506811028330682502008068250602506020060210203503025049410203206825048310203502359060b6
|17=>0x29490682502030029050682506007060fb02813048352c007048110603506812048310203500a212b83202025028310280504835029680682502031069990200a0602506b8d0206a030250602506805030250d02004819020350637a0400502035090070d825030350483506805060256f01b04005020350203503025060250483102832068252d14b02030020310d02204819020350294104835020324d825
|18=>0x20350e03704821020350203e0680a06025130190483500825279410203206012049f90401b020350226304832020351803154025020370e03302811048350208502833068250490503025060070602502812048351303106035008250483102810048350302506831030352903502030060250101303025060250b0180283106825040330203506027090130d825030350d005048190083500a050602202035
|19=>0x401b00835020351303104835008250484500819030350293f06825060120601b0482102035060250606803025030250483102035069b1048320201b068250681106025020250683103035068110281b068250682502032060250b01b0680906025090110d825030352c0110683106007020350483506010069da02035060191303100835008250280704835290250682502030168250083502035048310401b
|20=>0x60252c14d06035020070281102810048350609902037008250283102811048350203502807048352c1ed06831020052782502033060250403706811060250401b04832020350e0040482102035060250682506007040250203506019049450602002035048190101b06025169b1008350201b0682501007060250294b0682502030048220483502035060890280704835040080681106025068120602706025
|21=>0x283306825068250680503025118120283006825208350202506007061aa04007020350426302035060272b807048110600534025030b6008350602502805048350b01b0680906025048310681206007168250083503005060bd0281204835490310695e0202506a212b832020250100706812060250281902805048350694102032060250b0070680906025098190280504835178250281204835069f101007
|22=>0x168190680506025068110093d060122c01306831060250b018068090602502005048350082500825068250303500825030b6008350e030048210203504831062a30203702968068250203100b29020b700835049f5360350201b060220203702035040270601b0203502007068090602502008048310203502035068050601204bd9062a3020374d0130101906025028470682500819030b6048350083502832
|23=>0x22ef0603702033048350203202035028100483502831020354d00701019060250682503025020190680502035060050901b0d82503035060bf0281204835068250494102032068310200500825041070600702035010b706805060250281b068250601b0691102008060252b8070481106035030890280704835028110682506025020050481106035028110283206825031aa0400702035060250280504835
|24=>0x81906805030250208d028300682504831048350201b0201900835030050280506825030350682500835030053b09906019008250401b04831020350083502819068252c01906831020250d035030250602502035048350082506027060220203500a0506022020350283106825060070e03002811048350400806811060250200a0682506025020190683102025069f1010070602516869068050302504bed
|25=>0x2b832020250686a030252c0070603527825060120100506025060350201b0682502019068250600706027008190601b02035068320602502008060250680a0602502032060120203706027068090602506068030250601900825048190203504835020320082503035020350601902033060250681903005008250081906811060250296a068250203104811060b6008350081906825030350901b0686903025
|26=>0x3261060270203206025020080602503005020354c035060270600706011290250203013012008250483200835068250601b020350600504832020353b007060190683103035130190082506027060250200b0602502261060270280504835061b30201b0281204835028100483506023020352d027020310613d060120093d06012548050201904812008350606a03025048210203502035030050601902035
|27=>0x602102035062a102037068310602506905060070226306027020350602702811048352b83302025048320201b0682500819020b700835540250203700a95020270496206035548320201906010020355483102019060050203504832020350600706025068250602502007020350203102019010070602502035008250d825030352d01b0203104007020350100506025048350601902008060250483202007
|28=>0x6831020050681202005009b10201b0494102032020250201906831060070203002031062a302037020b50083504005020350281b0682506869030250682502030030b60083500aa102037020050082506832020252b80702025020250200504832020353d82702005020370601106825060250601906025030250203106037060192c0100603501007060250100706025008350201b06022020350283306825
|29=>0x48310201b0206a030250481906035020250601b0614d02007030250303506831020253d83302005049da060190681202025048310203501019060250601102035068310201902833068250682503025008350203520825060070d83103035068250303504831020070200a06025068310601b0203702032068050602506811060250481902032061b10201b022ed06037030250201906005060250283006825
|30=>0x601b02037030250202502019060070200506025060370601202031060250203700825068050302506027020370680502019368250601b060270201902812048350201b0602506825020310482202035020b700835528350202706811060250494d020070281b068250300500825008350300506027020050200a060255482502019020250303503005060050200906025062970202704007020350083502035
|31=>0x682502030008190203703035
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x5000000000000000000000000000000
|6,0=>0xbc616cc00000000aca14900000511000013c80000000094a12440000454084600001f983c307260d8c0000000000000001920000000000000000000000000000000000000000001798000056800000000283046a080c0e981c102ea058400000000000000008a8000000000000000000000003500518055
|6,1=>0x615
|7,0=>0x24c6490890211e22348459089210e400004290832000020483f907d20f641e483bcc75a0e831c8838106e98da30000359069200001a0400006788cb418e831486118be417482d905920ae4154829905210a04138826100000944124423904598874106820843f207b30ee81d843a1070400001b103420662
|7,1=>0x3de87ad0f491e633c480000ef21db33b247550e8a1cd4394671cce21800038086fc4dda1b7436680000d7a0000356869d0d1a000033e866d0cba193432066310000188430880000c0217c42f085d10b8216d32d285950b0a15d42b465608aa2151329c652cca49146328484f909d2136426664bd09691294
|7,2=>0x131a00004c42980800025e24b4895912a1250449e2930c000249348a8908d1f223a446c88d08000230400008b111422244440887110d121644284841107880004186824d02a20143fa87ec8fba1f34
|8,0=>0x6406c74d8d1b1736286c44d871b0b36106c14d811aff35fa4be8d7b9af435e26bb8d759ae835ca6b88d6f9adc35b26b58d699ad0359a6b28d648ac635866b00d5e9aba356e6ad0d589aae35566aa0d529aa2353e6a70d4d129735286a44d471a8b35106a14d411a7f34f869e4d3b1a7334e069b4d351a673
|8,1=>0x7bc6f6cdec1bd537a46f3cde61bc9378c6f0cde01bbd37746edcdda1bb1375c6eacdd41ba537446e7cdce1b99372e4e50dc89b8e37166e249c31b8337006df4dbd1b7736e86dc4db71b6b36d06d94db11b5f36b86d64dab1b5336a06d34da51b4736886d04d9f1b3b36706cd4d991b2f36586ca4d931b233
|8,2=>0x93c726ce4c1c953924723ce461c89390c720ce401c7d38f471dce3a1c7138dc71ace341c6538c4717ce2e1c5938ac714ce281c4d3894711ce221c41387c70ece1c1c35386470bce161c29384c708ce101c1d3834705ce0a1c11381c702ce041c0538046ffcdfe1bf937ec6fccdf81bed37d46f9cdf21be13
|8,3=>0xaba7568eab9d543aa27538ea59d483a8a7508e9f9d3c3a7274d8e999d303a5a74a8e939d243a427478e8d9d183a2a7448e879d0c3a127418e819d0039fa73e8e7b9cf439e273b8e759ce839ca7388e6f9cdc39b27358e699cd0399a7328e6414c5398472fce5e1cb9396c72cce581cad3954729ce521ca13
|8,4=>0xc327858f099e103c1a7828f039e043c0277f8efd9df83bec57ccef81ded3bd4779cef21de13bbc776ceec1dd53ba4773cee61dc93b8c770cee01dbd3b7476dceda1db13b5c76aced41da53b44767cece1d993b2c764cc0005903b1a7628ec39d843b0275f8ebd9d783aea75c8eb79d6c3ad27598eb19d603
|8,5=>0x3279e4c3c927918f219e403c7a78e8f1b9e343c6278b8f159e283c4a7888f0f9e1c3
|9,0=>0xda05b38b6616ca2d905b18b6216c22d805af8b5e16ba2d705ad8b5a16b22d605ab8b5616aa2d505a98b5216a22d405a78b4e169a2d305a58b4a16922d205a38b46168a2d105a18b4216822d0059f8b3e167a2cf059d8b3a16722ce059b8b36166a2cd05998b3216622cc05978b2e165a2cb05958b2a16522
|9,1=>0xea05d38ba6174a2e905d18ba217422e805cf8b9e173a2e705cd8b9a17322e605cb8b96172a2e505c98b9217222e405c78b8e171a2e305c58b8a17122e205c38b86170a2e105c18b8217022e005bf8b7e16fa2df05bd8b7a16f22de05bb8b7616ea2dd05b98b7216e22dc05b78b6e16da2db05b58b6a16d22
|9,2=>0x7b22f605eb8bd617aa2f505e98bd217a22f405e78bce179a2f305e58bca17922f205e38bc6178a2f105e18bc217822f005df8bbe177a2ef05dd8bba17722ee05db8bb6176a2ed05d98bb217622ec05d78bae175a2eb05d58baa17522
|10,0=>0x7c41f863f087e08fc01f7e3ef87de8fbc1f763ee87dc8fb81f6e3ed87da8fb41
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 15
def pmP:Nat→Nat
|0=>0x40400000000001008000000000040000000000000a180000000000216800000000008180000000000202000000000008010000000000200000000000004040000000000100800000000003d8000000000008600000000000210000000000001e400000000000580000000000012000000000000400000000000007c000000000001d00000000000068000000000001900000000000060000000000001200000000000040000000000000c000000000000280000000000008000000000000180000000000004000000000000080000000000000
|1=>0xa0101000000002200060000000083917c000000020e05f0000000080001800000001ac007000000004b917c000000012e05f00000000400028000000008040400000000100000000000002301400000000084000000000002000500000000040000000000000d81f00000000030004000000000a25f0000000002886c000000000880200000000020000000000000481f0000000000c40000000000030140000000000a040000000000221f000000000084000000000002047000000000080600000000002000000000000060080000000001800
|2=>0x80028600000002000879000000080021000000002000818000000080009fc000000200001900000008000060000000200001000000008000000000000110225f0000000440002800000011000080000000400c4100000001001000000000040008000000001000019000000040000000000000c8c41300000002a81004000000098e64f0000000263897c0000000800000000000018984fc00000006200160000000183907c000000060613f00000001080038000000040603f00000001001008000000040001400000000c3917c000000028c45f
|3=>0x2323005c000000860e40f00000020c3101c000000828c40f0000002063917c000000810e45f0000002013817c000000802a44f0000002000000000000040000180000000c00897c00000030022590000000c0009fc000000200a25f0000000801c17c000000200701c0000000801c050000000200605f000000080140700000002005004000000080100300000002003a5f0000000800c9dc000000200325f0000000800a97c0000002002a590000000800a11c000000200225f0000000800817c0000002001a00000000080061000000002001008
|4=>0x20043917c000008001255f00000200000108000002210803f0000008800a87c000002200107f0000008800417c000002200087f00000088002060000002000205f000000800068200000020001008000000800040000000020000a1800000080002820000002000081000000080000020000001a00e45700000043231054000001060c40100000040a01038000001010e45f0000004023216c000001008084a0000004003216c000001000c84b00000040000060000000a01645f0000002801c17c000000a00605f000000240000200000008c8e45f
|5=>0x82003917c000020800001f0000080c00a87c000020204d81f000008081020ec000020201285f0000080804a07c000020201205f0000080803407c000020200485f0000080023204c00002000808020000080013607c000020004d8110000080010002800002000400060000080002e87c000020000a85f0000080002897c000020000a202000008000200000000200001808000008000000c0000009040e55f0000024103857c000009000a55f0000020806917c000008200907f00000208008074000008200084200000208002100000008088655f
|6=>0x8000000860000200000000a0000480222212c000120018c84f0000424183047c000102200803f00004080000000000101210802700004040e0815c000101028e05f000040402000580001010000006000040008000180000c0000100800000f0880806c000028220201f000008a802002c000022210a25f0000088800a17c000022200205f0000088000a17c000020a049a1f0000082802407c000020a00885f0000082802006c000020a00485f0000082800617c000020a00005f0000082800007c000020808801b0000082013817c000020800f011
|7=>0x14001010074000500000613f000140000180fc0005000004015000100880021fc00040102080130001000800686000040020018180001000402687c000400062303f00010000a2006c000400000e05f00010000006060000400000181000010000004820000300204000800008a290481fc000228a02203f00008a210800f4000220a40205f0000882801007c000203200883f000080881200fc000200300225f0000800c00002000020020400080000800800897c0002002001008000080080021e40002000001818000080000060000002000000869
|8=>0x4008040a87c001000802e01d000400200380fc001000800001c0004000841207c001000200625f0004000801697c0010002003a5f0004000800c9fc0010002001a7f000400080049fc001000200127b000400080001fc001000100231f0004000062897c001000011a25f0004000043e87c001000010e65f0004000043217c001000010901f000400004180fc001000010001f0004000003297c001000000705f0004000001000000088000002060002000400085000080000002100001480801207c000500800612f000140010900e40005000420029
|9=>0x4100004d97c0010222101a5f0004088807897c001022200da1f0004088800a97c001020b003a7f0004082803a97c001020814fa1f0004082040007c001020800ba1f0004082000417c001020300187f0004080843217c0010202107a5f0004080841697c001020200da1f0004080803297c001020200ca1f0004080800417c001020000da1f0004080003607c001020000ca1f0004080003207c001020000c8190004020042017c001008000105f0004020000017c001002210803f0004008840e87c001002200187f000400880041fc0010022000879
|10=>0x10080000a87c004009010905f001000a101087c004002820421f001000a001087c004002800421d001000840908740040020003a1f0010008000c86400400010032190010000223217c004000000281f00100000006168002208200084a00088200002128002200200000a0008080011206400200000000020006000243917c001800010e45f00060000431034001800002f01d000600000a4054001800000b01d0006000000005000180000000060005000402487c001220300187f0004880c00087c001200210003f0004300000697c001080001235f
|11=>0x140040040d7c005000001035f0014000000a81c004802000421f00120080010874004501008885f0011404022017c0044020003a1f0011008000c87c00440010022190011000082017c0042800102a5f0010800040004800420001000100010480033217c00410901880570010424042417c004102200803f001040480220fc004100088c85f0010200800a97c004080200225f0010088010e87c0040220002a1f0010082013217c004020800885f0010080c00a87c004020300225f0010080800a87c004020200225f0010080013217c0040200004a5f
|12=>0x4002400a957c010001010c41d004000400b107c010000890e05f004000220b817c010000802f03f004000200b957c01000008ae45f004000022b817c01000008004080034080c00897c00d0001000a1f0024082003c87c009008000083c0024000c40016c009000300225f00240008010150009000200001c0024000440897c009000110001f00240000480874008000202327f002000010ac044008000002f01d00200000004400005402000321f0014380800897c005081001335f0014204000446c0050220002a1f0014008040e85c005002000321f
|13=>0x20000280881fc080000840f01f020000081080fc08000020420370200000802c97c080000200207f0200000006887c080000000f21f0200000003c47c080000000f01f0200000000e050080000000180401840000048974018020a02605f00600820190074018020802611f006000210984fc018000062613f006000018980fc018000042613f006000008984fc018000002603f006000000900f4018000002211f006000000800b4011000002703f00404002ab007c0101000a0e05f004040028000100101000000002004008280b917c010009042c41f
|14=>0x204008842007c081002200325f0204008800a97c081002200225f0204008800617c081002200125f0204008800417c081000800e01f0204000842c97c081000200b01f0204000800c97c0810002000a5f0204000800097c081000150421f0204000003807c080800000e01f020088a80021bc080222208003f020088280488fc080202200007f020080880000fc080022a00485f020008a800893c080022a00086f020008280081bc080020802721f020000c800087c080002204803f0200008800897c080002200185f0200008800017c080002200003f
|15=>0x1000000020857c2810202012a3f0a00084800a07c280020a00206f0a00080900a17c280020200207f0a000020080194280000200207f08008a290481fc200028200383f08000a0800a1fc200028200283f04000c0000846c0e1002200221d026000000ac87c091000002321f0244000001c07c090000802631f022400200bc87c089000140631f0224000040887c089000002f21f02240000002070088022a02f21f0214000800097c084023a04883f0210000401807c081200200025f0204800800017c0810a2210a21f0204082840c97c081002300025f
|16=>0x4000000803217d000000008a25f4000000003217d000000000a25f400000000060288080000003108200400000bc0fc800000100311c2000000400c45080000004200042000000043997c4042000182a5f1010000260015c404000010085810080208002100401220200103f1004200262097c401000099a25f1000882800007c400220200007f100080080008fc400021a00005b10000800400040400020008c85f1000020262017c4000080000040100000402a003c400001008c85b1000004022047c400000018a05f100000002a007c400000008a05f
|17=>0x4004200804c97d0010022003a174004000843297d000222a00023f400088080001fd000202200221f400080084201fd000080000325f400008a801897d000022a00425f400008a801087d0000222003a1f4000088800a97d0000222002a1f4000088800897d000022200025f4000088000887d000021a00885f4000082812217d000020800805f4000080a42217d000020204c05f4000080800897d000020200221f40000800044009000002900421f4000008800097d000002200021f4000008400a87d000002000b21f4000004001297d000000210c85f
|18=>0x2280020200207f88000a4806817e200020200285f8800080000a03e001020200303f5004a80804097d400008288805f5000000a63217d081022200325f4204088800687d080002201225f4014200000897d005002100221f4014008040c87d00500001022574012200000097d004080050025f4010200020882d004080000225f4010200000817d004080000025f4010008400887d004002000221f40100040048d7d0040000d8065f4010000220097d004000018225f40100000600041004000000225f4008000803217d0010c0000325f
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x300000000000000000000
|6,0=>0x9064040000000c090003100022000000bc1d0001601c000101f01c04000000000000c00000000000000000000000000001c0001c000001609004054170501d00000000000440000000000000000601023
|7,0=>0x4a04d0381e09c001141a080e304c0801c03858004798735c3b4a44a14c4f06060568353610437013544860000b1f80069cdf0c889300021983403078010e114c192449124c047e4a36787f06496010d427507670510147c044dd0014b814000f8f67cc05380435f4090315468858000122d41d094000cc0b0401f0fd58241803e957625b38185a028de0ad0015c2c024961d817160013f03101050000d14805d
|7,1=>0x4a04f0cc360014e0a08f10cb21dc1e000023f4de1940a180ab074370743a028d2085490388c1447d14800024f21edf2250251388d
|8,0=>0x6fa098a041574eb6d65a7524b6dd2422d786d09794177639e784c83744998456b3a9bd33429541bf1bd418a14f1b16c808308e5067091b1921b19d688563074a27394c97d80927199165022ecff4f98b1c0f52fcc774e0b3062347c71454c23ce3a5297c869fc2d0c56c5cf5e5e5792514b6515fd6536559740f95a1c67b9304341b8bc387f6128624e68c54841af0b62636a1739c735ece654c6496d4842dd9
|8,1=>0x3589b651e3580d35122c65976584ad55a21189754d4bd8f9d64956d649226c24f5c464431524b9c9534876801c63dc77b6244c0423f5342f9b733c6a97204284745c11d630bc6749651ce588c5f2ddbc2560a248ed19d93341226d99d4cce83a4f85cd81770a22a92c7bd9b699190f2084219a260cb864e416d2a4de1f0e48a2c08e875ae8c9a151a46954c540d684b46943e2b508f18a00f7a4bf190b31e481
|8,2=>0x2a07a2aa4311da9660955704c354402b9d8120a96b56f76d2f3c05c4ad2c470b16906719186388ae622574045c4508577e411ae28154f43dc0b1854c220805d20d2e18336e0344c759564d415231b4ac00182850642bc3c8045e694645c909485918017a311c5
|9,0=>0x191550c18a8d9dd7c4c83ee5994e4a45deb738cc1920f498fd6b4647fe4c611e06357e76a408ccc62e5e87ee318b62a9153940d328ccc372c6426945656250f6429263883117461e18f5d77982a445e159d5e1263749e2e7d2341c9f84ea29439cc78875872581ba20291fa3bd9f7215f7797916e48921d59593b5a93f879b24289f7f9dc6aa3b591668f1b85b8a5469ca5a4b6191c3311ba975ea458a77d563
|9,1=>0x24765e5412c826ed778d53c4324488930158fe298a08fcca7adec211361a1108395b7c0ee640ce6b1436165e9490f2e931734c66ae07711f71182e4e0ec
|10,0=>0xd1909e9204418c266a1126e5c0500c6705624f40d
|11,0=>0xd
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 10 (j%128);fld (pmP (k/32)) 54 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_190 10 roots_190 ops++addP pm 1 dom_187 9 roots_187 ops++addP pm 2 dom_189 9 roots_189 ops++addP pm 3 dom_159 9 roots_159 ops++addP pm 4 dom_63 9 roots_63 ops++addP pm 5 dom_149 5 roots_149 ops++addP pm 6 dom_179 7 roots_179 ops++addP pm 7 dom_42 4 roots_42 ops++addP pm 8 dom_41 4 roots_41 ops++addP pm 9 dom_175 8 roots_175 ops++addP pm 10 dom_185 7 roots_185 ops++addP pm 11 dzo_151_8 6 roots_151 ops++addP pm 12 dzo_47_16 6 roots_47 ops++addP pm 13 dom_173 7 roots_173 ops++addP pm 14 dzo_149_8 5 roots_149 ops++addP pm 15 dzo_43_16 5 roots_43 ops++addP pm 16 dom_161 4 roots_161 ops++addP pm 17 dom_61 6 roots_61 ops++addP pm 18 dom_55 5 roots_55 ops++addP pm 19 dom_155 6 roots_155 ops++addP pm 20 dzo_171_16 6 roots_171 ops++addP pm 21 dom_29 4 roots_29 ops++addP pm 22 dom_157 7 roots_157 ops++addP pm 23 dom_153 5 roots_153 ops++addP pm 24 dom_47 6 roots_47 ops++addP pm 25 dom_183 8 roots_183 ops++addP pm 26 dzo_182_8 6 roots_182 ops++addP pm 27 dzo_181_8 6 roots_181 ops++addP pm 28 dom_59 7 roots_59 ops++addP pm 29 dom_167 6 roots_167 ops++addP pm 30 dom_148 4 roots_148 ops++addP pm 31 dom_145 4 roots_145 ops++addP pm 32 dom_188 7 roots_188 ops++addP pm 33 dzo_183_8 7 roots_183 ops++addP pm 34 dom_169 5 roots_169 ops++addP pm 35 dom_171 6 roots_171 ops++addP pm 36 dom_27 4 roots_27 ops++addP pm 37 dom_151 6 roots_151 ops++addP pm 38 dom_31 5 roots_31 ops++addP pm 39 dom_143 5 roots_143 ops++addP pm 40 dzo_175_16 7 roots_175 ops++addP pm 41 dom_51 4 roots_51 ops++addP pm 42 dom_43 5 roots_43 ops++addP pm 43 dom_45 5 roots_45 ops++addP pm 44 dom_57 5 roots_57 ops++addP pm 45 dzo_170_16 5 roots_170 ops++addP pm 46 dom_186 7 roots_186 ops++addP pm 47 dom_165 5 roots_165 ops++addP pm 48 dzo_180_8 5 roots_180 ops++addP pm 49 dom_181 6 roots_181 ops++addP pm 50 dom_147 5 roots_147 ops++addP pm 51 dom_141 4 roots_141 ops++addP pm 52 dom_163 5 roots_163 ops++addP pm 53 dom_177 5 roots_177 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_191 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_151_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_149_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_43_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_161 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_171_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_182_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_181_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_145 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_183_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_175_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_zo_170_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_zo_180_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h52;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h53;exact cpcs (by decide +kernel) lowS_177 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_190 10 s (0,roots_190.map (·&&&dom_190)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_191 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_190 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_191==dom_191)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_191 gM v ys):RunD true dom_191 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_191 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 11 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 65 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 65 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 170 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 42 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 170 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 338 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 82 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 338 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 177 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 49 128 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 177 → Z 9 i = true := (range_split z9_0 z9_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 17 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 17 0 = true)
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
theorem lowS_239:Lower true dom_239 roots_239 goal_239 10:=lower_slice_b [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,8,9)] (by decide +kernel) lowS_238
def dzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def gzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000e0a0000
def gsh_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000e0a
theorem lowS_zo_235_16_42:Lower true dzo_235_16 roots_235 gzo_235_16 7:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_16) [(dom_235,16)] (by decide +kernel) (lower_slice_b (T:=gsh_235_16) [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000,0,64),(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,10),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,10),(8,40),(8,72),(16,17),(16,80),(16,144),(18,19),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,160),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,66),(64,72),(64,80),(96,97),(96,98),(96,104),(96,112),(96,224),(128,129),(128,130),(128,144),(128,160),(136,137),(136,138),(136,152),(136,168),(136,200),(192,193),(192,194),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|7=>7
|8=>45
|9=>57
|10=>8
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xc5479ab1a65ec0035c4432e551e4f91a30b
|8,0=>0xfcf13d3ec6c8862bfefcbada6b96bbb2f35a9143a857ba1b55905f98ca76802856cb706a73c675266749a60fd66063b5a5d04f4fb4e5b34985e4231f4042e3f7643edf33c1ab382b427a4527821249e0214391b86916af915bd3129b61247b0d581083500815b03a0c039d402e2e02ccb
|9,0=>0xfe341fa886e8b19d5aadd4598cfbf0b7cf7b61fea7548a50f59913e980d595e7f91b388e75489579883547d78d7af887a9d074a497168b6a1bd69ee768a735e9145cea85b418563af4985e414a83cbc13a05d38cac37255351b534d1b347c732ed2313a7308062f6942c4362577023bdb20be2193b419398182a81752113ee813e44101c00dada06e1605c100006e
|10,0=>0xfd547e3d596c0fe4268a3ecf23e1f938755294df
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000f000f000f000f00000000000f000f000f000f000f000f0000000000000000f0f0f0f000000000f0f0f0f000000000f000f00000000000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a303030303030303030303030303030303030303030303030303030303000300f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|0,1=>0xf0f0f0f0f000f000f0f0f0f0f0f0f000f0f0f0f0f000f000f0f0f0f0f0f0f0000000000000000000000000000000000f0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f0000f000f000f0000000f000f000f0000000f000f000f0000000f000f000f0000f0f0f0f0f0f0f0f000f000f000f00000f0f0f0f0f0f0f0f000f000f000f0000000000000000000000000000f0f00000000000000000000000000000f0f0000f0f0f0f0f0f0f0f000000000f0f00000f0f0f0f0f0f0f0f000000000f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f00000000f0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000f0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f0000000000000000000000000000f0f00000f0f000000000000000000000f0f00000f0f00000000f0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f000000000000f0f00000f0f0f0f0f0f0f0f000000000f0f00000f0f0f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f000f00
|0,2=>0xf0000000f00000000000000000000000f0000000f00000000f0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f00f000f000f0f0f000f000f000f0f0f000f000f000f0f0f000f000f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f000000000000000000000000000000000000000000000000f0f0f00000000000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f000f0f0f0000000000f0f0f0f000000000f0f0f0f000000000f0f0f00000000000f0f0f0000000000f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f000f000f000f0f0f000000000000000000f0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0f00000f0f00000f0f0f0f0f0f0f000f0f00000f0f00000f0f0f0f0f0f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f0000000000000000000000000000000000000000f0f00000f0f00000f0f00000f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f0f0f0f0f00f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f0000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000
|0,3=>0xf0f0f0f0f0f0f0f00000000000000000f0f00000f0f00000000000000000000000000000000000000f0000000f0000000f0000000f00000000f0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f000000000000000000f0f0f0f0f0f0f0f00000000000000000f000f000f000f000000000000000000f0f0f000f0f0f0000000000000000000f0f0f000f0f0f0000000000000000000000000000000000f0f0f000f0f0f000f0f0f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f000f000f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000f000f000f000f000f0f0f000f0f0f000f000f000f000f000f0f0f000f0f0f000000000000000000000000000000000000000000f0f0000000000000f0f0000f000f000f000f000f000f000f000f000f000f000f0f0f000f000f000f0f0f000000000000f000000000000000f000000000000000f000000000000000f0000c0c0c0c0c0f0c0c0c0c0c0c0c0f0c0c0c0c0c0c0c0f0c0c0c0c0c0c0c0f0c0cf0f000f0f0f000f0f0f000f0f0f00000f0f000f0f0f000f0f0f000f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000
|0,4=>0xf0f00000f0f0000f0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f00000000000000f0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f0000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000f0f0f0f0f0f0f0f000f0000000f00000f0f0f0f0f0f0f0f000f0000000f0000f0f0f0f000000000f0f0f0f0f0f00000f0f0f0f000000000f0f0f0f0f0f000000000000f0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f000000000f0f0f0f000000000f0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000f0f00000f0f0000
|_,_=>0
def sP:Nat→Nat
|0=>0x8241810078305201048302746050824181002060526104830018284120cd81002030b0a104830e046060a104833200305082419802006060a582090600a940824181002060520241871418284060808022182090600289063c7010034305080c101002060b0a104830e182840608080
|1=>0x6800800c14809063c0801818284120d7803a18284120c080181858508241872a3029708241800c15690120c0800c1420906ac0800c1420906a40800c15384120c0804a18284120c0800c1420906900802a1919008241814418284120c0800c84809068008018185852e10483007c305
|2=>0xc15c84120c080103058508241810030284120ce0100286860a10483020030b0a104831e040080ce0284120c0801418284120c0801819b8508241801030284120c38010182ad120c0800c15a84120c0800c142330604006641420906040310cc0284120c0801030290120c0800ca8209
|3=>0x424c20906040060a1048334040064214b89060400d0c1420906040150c2c20906040080c1420906d00800c15684120c0800cec284120c08058198050824181005460508241810019d05082418100182940824181003030520104830e2030508cc1810018984120c90018190852e24180
|4=>0x8241810104305082418100b0305201048302182c0082418100182bf082418100c430508241810019c050824181002060508241810018284120d4010018584120d00100303052610483001829008241be020030508241bd020030508f04830201606421420906040060a104831e04006
|5=>0x18284120e4010018284120db010018284120d70100543052010483020030508241c602022860a1048302003300a104830e0068c0c1420906040060a1048388040080c14209061c0800cc02900824181010c30508241810018284120cc8101083050824181001829008241870274305
|6=>0x19805082418100182ca082418100182c90824181009830508241810054304120e3810054321082418100b03052e10483020218c0c14209060401d1018284120c0800c1420906d008010182a30824181001829008241a002006060a4020906040080cc0284120c08018182a30824181
|7=>0x30508241810018284120c38100b03050824181002030508241810018284120e381001829008241810054305082418100182a30824181
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0x2c709201e605dc0f801e0007
|8,0=>0x197863e188760217885be567857a555953254484f213484b21248475d15843250483f20f483b20e483720d483320c482f20b482b20a48272094823208391ee07381ae063816e052912a04280ea0337
|9,0=>0x36f8d9e35f8d5e34f8d1a73d9cd272c8c8e71a9c467089bfe6f78bbe2e78b7a6d68b3a2c68af66b58ab26a39a6e2938a2e28389ee27389ae263896e253892e24388ee23388ae222986a212882660187e61f187a61e187661d097221c086de5af869e19f8
|10,0=>0xebe3a78e7e3978e3e3878dfe3778
|11,0=>0x3b77
|_,_=>0
def wAt:=mkWire dB 75 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x8190a010a110c1608010a0108050c05104d08190a072a030c150801101508190c050c0508190a0738052a130a19000508190a0134050a330c051e0108320c052e0108050c050c150a300c0502010c110c050801101d0c11020126490a070a320c050c4218130c05080114271a1100050c110c050a0102011427101d0c110201
|1=>0x2010c05084d0a070c050819000508d110160c1108d958160c0112d110160c110a3d08320c0510010c110c110c0508010a1b082d0a0118130c0508012e1608050c050ab910170c110c050a0102010a1908050c05080108810a1b58860c010a11541b082d0a0108a1161b0a014c15100708191a130c1d00050a030c150801102d
|2=>0xa420801200708010c010a1108320c0508150a070a330c0508050a110c1d00050a190a0110160c1108810a1b42070a110c010a050a190c0542030a110a300c050c050801020112d110160c110a070a320c05080508150c055a0108810a1b0c0508190a010c052a130a191a110c1d000508320c050a010c110a1d0201101d0c11
|3=>0xc110a030c1608010c0508010c110a050a030c05421b0a1158160c0110170c110c1508018e050a1326190a070a05000518010c050cc20a050c11020108010a050cc10a0540050a1b16190a01080102012a110a190c8d0a030c01080126010a0716070a010c4108010a1d020108190c05161b0a010a1b0a010a070c050a430801
|4=>0x2010c010c110a1308010a190a030a050a1f020110140c11100708190c150a130a110a1908050c010a310c0510150c1110160c11
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x5902660f405a020c088004
|8,0=>0x9d34d1a5cd286913471a2cd1068534119fccf867933b19ccce066d33591a0cca66232f9970cb26563299940c9a64a3239910c8263e31d98e0c6a63231798b0c526263119880c3a61a3
|9,0=>0x1102871430a145082831410a0450027f13f09f44f827b13d09e44f027713b09d44e827313909c44e026f13709b44d826b13509a44d026713309944c826313109844c025f12f09744b825b12d09644b025712b09544a825312909444a02
|10,0=>0x8c8c6062e31618a8c506263121
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 13
def pmP:Nat→Nat
|0=>0x180f77806863f403400f000818ed003cc368008a5b4004403c0021eff0010d7780086bb400433fe0020a6d00104f6800825f400350da001286d00040420001a1e400078da0001fff0000f76800077fc00039da0000dfd0000676800021b40000082000004000000100000007800000020000000
|1=>0x100040e050827b428011da0e13ced0709c76831c25f418872da0c201e9060c4768304e1b418211da0c00aed06004768194f3b408af8fa0453c7d0228c36811263b408734da043097d021457681082bb408413da04208ed020d436810621b408293fa041486d0209436810431e408039da04008ed
|2=>0x560cc36a904a1b544031daa081c6f50105b6a80829b540038fea00086d4608476a1142bb4c8258de641286d3201436930023b45c270da2c4286d1601636899421b448f34da245096d1228476891421b448850da241286d1202672890035f448018fa24008ed120043688087ff44043dfa2002c00
|3=>0x710423b748390db441686fa208436d00421b648090db240086d910141441072bb608390df04148ed8202476c10023b60004031000186f
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x3020e0a0c101
|8,0=>0x187c89e527f38ec0c27a78a70cde8d1f0918b8646ab2675c86a3472b10699e81b731a5198e24fcb
|9,0=>0x44504e627bac5d4452aa0a542d712c9ba64e5b390ae64d8ef174ebad53a96f608d7ba2ab5a5af87a311ddc90a59b6dac1bc4
|10,0=>0xc16096828bd024
|11,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 29 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_59 7 roots_59 ops++addP pm 2 dom_187 9 roots_187 ops++addP pm 3 dom_243 9 roots_243 ops++addP pm 4 dom_147 5 roots_147 ops++addP pm 5 dom_219 9 roots_219 ops++addP pm 6 dom_249 10 roots_249 ops++addP pm 7 dom_163 5 roots_163 ops++addP pm 8 dom_211 6 roots_211 ops++addP pm 9 dom_115 6 roots_115 ops++addP pm 10 dom_155 6 roots_155 ops++addP pm 11 dom_123 9 roots_123 ops++addP pm 12 dzo_43_16 5 roots_43 ops++addP pm 13 dzo_171_16 6 roots_171 ops++addP pm 14 dom_171 6 roots_171 ops++addP pm 15 dzo_107_16 6 roots_107 ops++addP pm 16 dzo_235_16 7 roots_235 ops++addP pm 17 dom_83 5 roots_83 ops++addP pm 18 dom_203 6 roots_203 ops++addP pm 19 dom_27 4 roots_27 ops++addP pm 20 dom_51 4 roots_51 ops++addP pm 21 dom_179 7 roots_179 ops++addP pm 22 dom_235 8 roots_235 ops++addP pm 23 dom_227 6 roots_227 ops++addP pm 24 dom_233 7 roots_233 ops++addP pm 25 dom_75 5 roots_75 ops++addP pm 26 dom_107 6 roots_107 ops++addP pm 27 dom_91 7 roots_91 ops++addP pm 28 dom_43 5 roots_43 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_43_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_171_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_107_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_235_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_43 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 45 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 57 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 57 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
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
def dzo_246_8:=0x5500550055005500550055005500550055005500550055005500550055005500
def gzo_246_8:=0x5500550055005500550055005500540055005500550055005500550054004400
def gsh_246_8:=0x55005500550055005500550055005400550055005500550055005500540044
theorem lowS_zo_246_8_148:Lower true dzo_246_8 roots_246 gzo_246_8 7:=lower_iso_b (d1:=dom_246) (r1:=roots_246) (T1:=gsh_246_8) [(dom_246,8)] (by decide +kernel) (lower_slice_b (T:=gsh_246_8) [(0x44004400440044004400440044004400440044004400440044004400440044,0,2),(0x55005500000000005500550000000000550055000000000055005500000000,0,32),(0x55005500550055000000000000000000550055005500550000000000000000,0,64)] (by decide +kernel) lowS_148)
def dzo_238_16:=0x5555000055550000555500005555000055550000555500005555000055550000
def gzo_238_16:=0x5555000055550000555500005555000055550000555500005554000054500000
def gsh_238_16:=0x555500005555000055550000555500005555000055550000555400005450
theorem lowS_zo_238_16_42:Lower true dzo_238_16 roots_238 gzo_238_16 7:=lower_iso_b (d1:=dom_238) (r1:=roots_238) (T1:=gsh_238_16) [(dom_238,16)] (by decide +kernel) (lower_slice_b (T:=gsh_238_16) [(0x505000005050000050500000505000005050000050500000505000005050,0,4),(0x555500005555000000000000000000005555000055550000000000000000,0,64),(0x555500005555000055550000555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
namespace S_254
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(2,130),(4,20),(4,36),(4,68),(4,132),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(12,14),(12,28),(12,44),(12,76),(12,140),(16,20),(16,80),(16,144),(18,22),(18,26),(18,50),(18,82),(18,146),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,36),(32,40),(32,160),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,68),(64,72),(64,80),(96,98),(96,100),(96,104),(96,112),(96,224),(128,130),(128,132),(128,144),(128,160),(136,138),(136,140),(136,152),(136,168),(136,200),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|9=>5
|10=>3
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0x5a0ca56f0c3c3ab109bc103ed
|10,0=>0x5b02e420a2371a0
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x155555400000000015555540000000001555554000000000155555402aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaa80002aaa80002aaa80005555555555555555555555555555555555555500555555005555550055555500aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa0155555555555555555555555555555555540154015401540154015401540154000002aaa80002aaa80002aaa80002aaa80002a8000002a8000002a8000002a805555555555005500555555555500550055555555550055005555555555005500aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa000000015554000155540001555400015554000155540001555400015554000155540002a802a802a802a802a802a802a802a802a802a802a802a802a802a802a802a80505050505050505050505050505050505050505050505050505050505050505088888888888888888888888888888888888888888888888888888888888888880001555400015400000155540001540000015554000154000001555400015402aaaaaaaaaaaaaaa80000000000000002aaaaaaaaaaaaaaa80000000000000005555555555555555555555555555555500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x76543107d65431076a543107b65431076543e107c6543107b6a43107654391076543210
|_=>0
def sO:Nat→Nat→Nat
|9,0=>0x20831042044008
|10,0=>0xe2184288
|11,0=>0x407
|_,_=>0
def wAt:=mkWire dB 15 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x18150595b7d59d5581505956a94186d5d
|_=>0
def oO:Nat→Nat→Nat
|9,0=>0x8262422202
|10,0=>0xc1b1a1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x47fd3fe6ff17f87fc1fe000
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>0x2692
|10,0=>0x135
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_190 10 roots_190 ops++addP pm 2 dom_126 9 roots_126 ops++addP pm 3 dom_94 8 roots_94 ops++addP pm 4 dom_250 10 roots_250 ops++addP pm 5 dom_246 9 roots_246 ops++addP pm 6 dom_238 9 roots_238 ops++addP pm 7 dom_222 9 roots_222 ops++addP pm 8 dzo_246_8 7 roots_246 ops++addP pm 9 dzo_238_16 7 roots_238 ops++addP pm 10 dom_110 6 roots_110 ops++addP pm 11 dom_230 6 roots_230 ops++addP pm 12 dom_118 6 roots_118 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_246_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_238_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_118 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 5 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 3 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 3 0 = true)
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
def isoMvS_223:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_iso_b isoMvS_223 (by decide +kernel) lowS_127
def isoMvS_247:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_247:Lower true dom_247 roots_247 goal_247 10:=lower_iso_b isoMvS_247 (by decide +kernel) lowS_239
def isoMvS_253:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_251
def dzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00
def gzo_215_8:=0xff00ff0000000000ff00fe0000000000ff00ff0000000000fe00ee00
def gsh_215_8:=0xff00ff0000000000ff00fe0000000000ff00ff0000000000fe00ee
theorem lowS_zo_215_8_148:Lower true dzo_215_8 roots_215 gzo_215_8 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_8) [(dom_215,8)] (by decide +kernel) (lower_slice_b (T:=gsh_215_8) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,0,2),(0xff00ff00000000000000000000000000ff00ff0000000000000000,0,64)] (by decide +kernel) lowS_148)
def dzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def gzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000fffe0000fefa0000
def gsh_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000fffe0000fefa
theorem lowS_zo_239_16_42:Lower true dzo_239_16 roots_239 gzo_239_16 8:=lower_iso_b (d1:=dom_239) (r1:=roots_239) (T1:=gsh_239_16) [(dom_239,16)] (by decide +kernel) (lower_slice_b (T:=gsh_239_16) [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,0,1),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,0,64),(0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def gzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00fe00ff00ff00ff00ff00ff00ff00fe00ee00
def gsh_247_8:=0xff00ff00ff00ff00ff00ff00ff00fe00ff00ff00ff00ff00ff00ff00fe00ee
theorem lowS_zo_247_8_148:Lower true dzo_247_8 roots_247 gzo_247_8 8:=lower_iso_b (d1:=dom_247) (r1:=roots_247) (T1:=gsh_247_8) [(dom_247,8)] (by decide +kernel) (lower_slice_b (T:=gsh_247_8) [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,0,1),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,0,2),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000,0,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000,0,64)] (by decide +kernel) lowS_148)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,10),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,40),(8,72),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,36),(32,40),(32,160),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,68),(64,72),(64,80),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,130),(128,132),(128,144),(128,160),(136,137),(136,138),(136,140),(136,152),(136,168),(136,200),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|6=>1
|7=>3
|8=>15
|9=>53
|10=>146
|11=>59
|12=>8
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xa9b6c
|7,0=>0xb35c2481a922225
|8,0=>0xf629bd0317cceb887ada8549b748977092e5d7755b13651d9a3734f339002f8061c6c11a082
|9,0=>0xf66bdf407ee2cd4dbe44d1634c13bac09fdbaa92b7931a192d9a36999e199605e93a1f9270c8d2bb8bcae84e2980b517d63f7b274726c16e9866cf8f6cebd6cc6966981637a25ded65d3515c45e521aa4f29b4a13248dbf4659e439193cd2b299cb2978628f802710c25fe81e0d818cbc160aa12c200e4fe0be0207c2807087054ee02db6
|10,0=>0xb3ff5ade60acb43a78d3a5b6aa42a5a1d56a192d9f5979e44b9c8189b67299fb799506993ee95ca0913f290211900808edd08c48388514878bb8704081ce07fb617d4737bbfb7b27478c3574c4f6fdb46c6016b3706a04b68ad06809767d61670a96605665b75636d860adc6077d5cd975bd875a18057b4153baa533e55320650c914e0204c5a44b5d84a80149d184391941fca4113c40705402d83fcb73cdeb3c0fe392803897c37405371ad35fa3348f533cf63364a3330332db4329e031da2311092ec022ea6d2c4be2ba622b52f2b4db2a9fe2a71629cb029a032985c27498269002685f243bc2389a1fe931e49e1d9861cc021cae31c8651c69f1a4a416d511600d15c6312dfc1118010eac1031a0e6720e1ad0dc0f0be660be020b82b0b63509fc408ebb07c2807954077b704fba032ae02f5402101017a4014cd00a65
|10,1=>0xdbe44db393d87d1d8467d3456d081cccc63cb94ec8ac3c5401c4a87c0ad8bf254bf128be07abc5a2b7931b4908
|11,0=>0xdb393c4484c1893be07abc5a2bbd16b5792b08a3a7b29a36dca369ca03ff9c7b4962ee86ee67e9c37e31a7e1fd79cf27895e6fb086b3706afc167c6e6412361e185dc7c5d6395a1805889357fb94c8e3470f845bad3b6323b38d37581348f5343e1322b62fdf72a21329953297a622db01d9861d307198301827a0f41b0d8be09e0809a3607c2805d8e055e904dbe017a400a6c
|12,0=>0xdd9d2cdb7da29789892d94343890f161e180c075
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffffffffffffffffffff00ffff0000ffff0000ffff0000ffff00ffffffffffffffffffffffffffffffffffffffff00ffff00ffffffff00ffff00ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffff00ffff00ffffffff00ffff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000ffffffff00000000ffffffff0000000000ffff000000000000ffff00ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
|0,1=>0xffffffffff00ff00ffffffffff00ff00ccccccccccffccccccccccccccffccccccccccccccffccccccccccccccffcccc000000000000000000000000000000000000000000ffff000000000000ffff00ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffff0000ffffffffffff0000ff00ff00ff000000ff00ff00ff0000000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff00ffffffff00000000ffffffff00000000ffffffff00ffff00ffffffff00ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000000000000000000000000000000000ffffff0000000000ffffff00ffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffff00ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff0000000000000000000000000000000000ffffffffffffff00ffffffffffffff0000000000ffffffff00000000ffffffff00000000ffffff0000000000ffffff00ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000
|0,2=>0xffff000000000000ffff000000000000ffffff0000000000ffffff00000000000000000000000000000000000000000000ff00000000000000ff0000ffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00ccccccccccccccccccccccccccccccccccccccccccffccccccccccccccffccccffffccccffffccccffffccccffffccccccccccccccffccccccccccccccffccccffffff00ffffff00ffffff00ffffff00ff00ff00ffffff00ff00ff00ffffff00ffffffff00ff0000ffffffff00ff0000ffffffff00ff0000ffffffff00ff0000ffffffffffff0000ffffffffffff0000ffffffff00ff0000ffffffff00ff0000ffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00000000000000000000000000000000000000ff000000ff000000ff000000ff00ffff0000ffff0000ffff0000ffff00000000000000ff00000000000000ff0000ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ff00ff0000000000ff00ff0000000000ff00ff000000ff00ff00ff000000ff00ffffffffffffffffffffffffffffffffff00ff000000ff00ff00ff000000ff0000000000ffffffff00000000ffffffff00000000ffff000000000000ffff00000000000000ff00000000000000ff00000000000000ff00000000000000ff0000
|0,3=>0xff000000ff000000ff000000ff0000ffffffffffffff00ffffffffffffff000000000000ff00000000000000ff0000ffffffffffffff00ffffffffffffff0000000000000000000000000000000000ff00ff000000ff00ff00ff000000ff00ffffffffffffffffffffffffffffffff00000000ffff000000000000ffff0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fff0fff0f0f0fff0fff0fff0f0f0fff0ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000000000000000000000000000000000ffffff00ffffff00ffffff00ffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000000000000000000000000000000000000000ffff0000ff000000ffff0000ff00ffff0000ffff0000ffff0000ffff0000ffffffffffffff00ffffffffffffff0000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000ff00ffffff000000ff00ffffff00ffff0000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff0000000000ffff0000ffff0000ffff0000ffff00ffff0000ffff0000ffff0000ffff00ffff0000ffff0000ffff0000ffff0000ffffff00ffffff00ffffff00ffffff00
|0,4=>0xffffffffffff0000ffffffffffff0000ffffffffffffff00ffffffffffffff00ffffff00ffff0000ffffff00ffff0000ffffff00ffffff00ffffff00ffffff0000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffff00ffffffffffffffffffffffffffffffff0000ffff0000ff000000ffff0000ff0000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff0000000000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fff0f0f0fff0f0f0fff0f0f0fff000000000ffff000000000000ffff00000000000000ff00000000000000ff000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ffffffff00000000ffffffff00000000ffffffffff00ff00ffffffffff00ff00ff00ff00ffffff00ff00ff00ffffff00ff00ff00ffffff00ff00ff00ffffff0000ffffff00ffffff00ffffff00ffffff00ffff0000ffff0000ffff0000ffff00fff0fff0f0f0f0f0fff0fff0f0f0f0f0fff0fff0f0f0fff0fff0fff0f0f0fff000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
|0,5=>0xffffffffffff0000ffffffffffff0000ffffffffffffffffffffffffffffffffff00ff00ff000000ff00ff00ff00000000000000ffff000000000000ffff000000000000ff00000000000000ff000000ffffffffffffffffffffffffffffffff00000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00ffff0000ffff0000ffff0000ffff000000000000ff00000000000000ff000000ffffffffffffffffffffffffffffffff00000000ffffff0000000000ffffff00ffffffff0000ff00ffffffff0000ff00ffffffff0000ff00ffffffff0000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000000000000000000000ffffffff0000ff00ffffffff0000ff00ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff0000000000ffff00ffff000000ffff00ffff000000ffff00ffff000000ffff00ffff000000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff0000ff00ff00ffffffffff00ff00ffffffffff00ff00ffffff00ff00ff00ffffff00ffffffffffffffffffffffffffffffff0000ff000000ff000000ff000000ff000000ffff000000000000ffff000000000000ffff0000ff000000ffff0000ff00
|0,6=>0xffffffff00000000ffffffff00000000ff00000000000000ff000000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff000000ffffffffff00ff00ffffffffff00ff00ffffffffff000000ffffffffff00000000000000000000000000000000000000ffff0000ffffff00ffff0000ffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00000000000000ff000000000000000000ff00000000000000ff00000000000000ff00000000000000ff00ffff0000ffffff00ffff0000ffffff00ffff0000ffffff00ffff0000ffffff00ffffffffffffffffffffffffffffffff00ff000000ff000000ff000000ff00000000000000000000000000000000000000000000ffff000000000000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffff00ff00ff00ffffff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff000000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff0000000000000000000000000000000000ffff0000ffff0000ffff0000ffff000000000000ff00ff0000000000ff00ff00ffff0000ffffff00ffff0000ffffff00ffffffffffffffffffffffffffffffffff000000ff000000ff000000ff000000
|0,7=>0xffffffff0000ffffffffffff0000ffffffffffff0000ff00ffffffff0000ff00ffffffffff00ff00ffffffffff00ff00ffffffffffffff00ffffffffffffff0000000000ffff000000000000ffff0000ff00ff00ffffff00ff00ff00ffffff00ffffffffffffffffffffffffffffffffffffffff0000ff00ffffffff0000ff0000000000000000000000000000000000ffff000000ff0000ffff000000ff0000ffffffff00ff00ffffffffff00ff00ffffffffff00ff0000ffffffff00ff0000ffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ffffffff00ff00ffffffffff00ff00ffffff000000ff0000ffff000000ff000000000000ffffffff00000000ffffffff000000000000ff00000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffff00ffffff00ffffff00ffffff00ffffffffffffffffffffffffffffffff0000000000ff00000000000000ff0000ffffffffffffffffffffffffffffffffffffffffff000000ffffffffff000000ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff000000ff00ffffffffff00ff00ffffffffff00ff00ffffffff0000ff00ffffffff0000ff00ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff000000ffffffff0000ffffffffffff0000ffffff00ff000000ff00ff00ff000000ff00
|0,8=>0xffff0000ffff0000ffff0000ffff000000ff000000ff000000ff000000ff0000ffffffffffffffffffffffffffffffffff00ff00ffffff00ff00ff00ffffff00ffffffffffffffffffffffffffffffff000000000000ff00000000000000ff00ffffffffffffffffffffffffffffffffffff0000ffffff00ffff0000ffffff00ffffffffff00ff00ffffffffff00ff00ffff0000ff000000ffff0000ff0000000000ffff0000ffff0000ffff0000ffff000000000000ff00000000000000ff0000000000000000000000000000000000ffff0000ff000000ffff0000ff000000ffff000000000000ffff000000000000ffff000000ff0000ffff000000ff0000ffffff000000ff00ffffff000000ff00ffffff000000ff00ffffff000000ff00ffffffff00000000ffffffff00000000ffffffff0000ff00ffffffff0000ff0000000000000000000000000000000000ff00ff00ffffff00ff00ff00ffffff00000000000000ffff000000000000ffff000000000000ff00000000000000ff00ffff00ffffff00ffffff00ffffff00ffff000000ff000000ff000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00000000000000ff00000000000000000000000000000000000000ff000000ff000000ff000000ff0000ffff0000ffffffffffff0000ffffffffffff0000ffffff00ffff0000ffffff00
|0,9=>0xff00ff0000000000ff00ff00ffffffff00000000ffffffff00000000ffffffffffff0000ffffffffffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x504030f0007080d0c0504030f0007100c1a05040300180d0504030200070d050403020100070d0c050403020100070d0504030f1700070d0504030f020100070d0504030216000712090a05040311000e0d0504030200070e0d0c050403020007080504030f0100070e05040302010007080504030201000706050403020100
|1=>0x2f00070d090a052c0300071f0d090a052b0300070d092a0a0504030007130d092a05040300071f29090a05040300071328090a05040300070d090a050403110007240d090a050403000710090a1a050403000d090a2205040321001f0d090a051e0300070e0d0504030f020007080d0504030f0200070d050403021d0007080d
|2=>0x70d093b0a04033c00073e0d090a05040300070d27050403020007130d090a052b0300070d0c0b0504031600070d093b0a0403000715090a0504031100070d0c0504033900070d380905040337000d270a050403340007350d140a05040300070d300a0504032100070d140a0504033300070d0a0504033100070d140a050403
|3=>0x100d050403020007100d0c05040302000713090a0504031100070d14090a0504034c000d0c1a05040300070d0504034b4a00070d380a05040349001f090a05040348000d090a0504031600070d140a470403340007440d0943050403000712130d14090a050403000d0c0504034200070d09410a040300073f0d090a05040300
|4=>0xa050403400007560d090a05040300070d30140a05040300070d0504030f0200070d0c0504030f0200070d0a0504035400070d09520a05040300070d140a0504035134001c100c1b050403000d050403021700074428090a0504030007150d090a05040300074f0d090a05040300070d4e0a0504032100070d050403024d0007
|5=>0xc3a0504030007240d0a0504034a00070d090a0504031100070d0c380b05040300071c090a0504032100070d0c1b0504033400070d090a050403530007240d090a05040300070d0c0a3205040300070d090a0504035d00070d090a0504035a00070d090a050403572100070d090a0504035900070d27090a0504032100071c0d
|6=>0xd090a3d05040300070d0504030200070d61090a0504030007130d090504034b00070d0c0504030200070d14090a230504030007100d090a60050403000d14090a0504034d00071c5f10090a05040300240d091b05040300070d0c1b3205040300070d1409520a0504030007130d09450504032000070d090a5e05040300070d
|7=>0x1c0d300a05040300070d090a6b05040300070d090a0504036a000724130d094505040300071c0d680a05040300070d0c0a050403490007130d090a0504036700070d09650a0504030007580d091b0504030007240d090504034b00070d090a2205040300070d090a0504036300070d090a1a05040300070d090a050403490007
|8=>0xa0504036f00070d38090a05040300076d0d090a05040300071c100c0a05040300070d09050403375700070d0c1b0504034900070d14090a0504035100130d0c14090a05040300070d090a3d0504033c00070d0a050403373400072910090a05040300070d6c090a0504030007130d090a0504033700071c090a0504034d0007
|9=>0x40300071f0d090a0504032000070d270a0504033400070d09710a0504030007130d090a051e03000713091b0504034800070d14090a0504031100070d090a230504032100070d090a0504032e0007240d14090a05040300070d09520a0504032100070d090a7005040300071c0c0a0504034d000713090a0504034800070d09
|10=>0x34a00070d090a0504037700071c0d760a05040300070d090a0504037500070d0a050403404900070d090a0504034a00070d0c090a0504034a00071c10091b0a0504030015130d090a0504030007740d090a0504030007720d090a05040300071c140a0504032100070d0c550a05040300070d09434505040300070d270a3205
|11=>0x300070d090a0504031600070d0c090a050403160007130d2714090a050403000724090a0504034d00077a0d090a05040300070d0c091b0504030007795f0d090a050403000d09780a050403000713090a0504034d00070d09450504034d00071c58090a05040300070d0c0a0504034a00071c100a0504034000070d091b0504
|12=>0x70d091b8305040300070d090a0504038200070d090a0504032500071c0d0a0504038100070d80090a0504030007130d76090a05040300077f0d090a05040300077e130d090a050403000715130d14090a05040300070d0c450504033400070d097d0a05040300077c0d090a05040300070d097b0a05040300070d270c0b0504
|13=>0x70d090a0504038a00070d09890a05040300070d091b6405040300070d09880a05040300070d0c870a0504030007860d14090a05040300071c0d380a05040300074f0d090a05040300070d090a47040300072d1f0d090a050403000d09850a05040300070d14090a0504033600070d090a0504038400070d091b0504033700
|14=>0x70d090a0504038d00070d27090a0504033700070d090504034b6900070d27096e05040300070d09050403372600070d8c090a05040300070d098b0a050403000724580d090a05040300070d0c090a050403210007100d050403405700070d30090a05040300070d68090a0504030007150d090a0504030007100d0c0b050403
|15=>0x50403690007100d090a050403400007100d091b0a050403000d0c091b0a0504030007240d090a05040300071c0d140a0504030007240d0c090a05040300071c0d090a0504035700071c0d0a0504034000070d0c0a0504033400070d09520a0504030007100d0c090a05040300071c0d0c1b05040300070d098e0a0504033c00
|16=>0x70d140a0504033400070d38090a0504030007130d14090a05040300070d0c38090a0504030007130d090a0504034000071c5f0d090a05040300070d09620a0504035b00070d090a6e05040300070d090a0504038100070d090a050403490007580d090a05040300070d090a450504033400070d090a6005040300071c0d090a
|17=>0x91b0a05040300070d090a0504038f00072d0d091b0a05040300070d0c090a05040300070d14090a6e0504030007131f0d090a05040300070d090a0504034a00071c0d620a05040300072d130d090a05040300070d27091b0a0504030007100d090a0b05040300070d050403405700070d090a0504032600070d0c0b05040300
|18=>0x724130d090a05040300070d091b0a3205040300070d090a3a05040300070d091b0a0504033400070d0c14090a0504030007130d09620a0504030007790d090a0504030007900d090a05040300071c0d090a0504034b00070d090a0504035100070d090a0504033c00070d14090a0504032600070d0c091b05040300071c0d
|19=>0x70d14090a05040300070d090a0504034000070d090a4505040300070d0c090a05040300070d091b0a0504030007100d0c090a05040300070d14090a0504033700070d090a0504032100070d30090a05040300070d68090a05040300070d090a0504039100070d090a0504037300070d090a050403480007130d091b0a050403
|20=>0xd090a0504030007100d090a05040300070d090a0b05040300070d090a0504035b00
|_=>0
def sO:Nat→Nat→Nat
|6,0=>7
|7,0=>0x17800f80078
|8,0=>0x93908a9082807a8071906a7062805a805190498040903880308028801f9
|9,0=>0x25f8256924e8245923c9234822c8223921a92119208920081f881ef91e691dd91d581cd81c581bd81b491ab91a29198a1908188817f9176916d9165815c9153914b8142913a8132812991209117910e910680fd90f580ec90e390da90d190c890bf90b690ae80a5909c9
|10,0=>0x4a7a49da494948b9482947994709467945e9455944c94439438b42ea425941c94139409a40093f793ee93e593dba3d293c993bfa3b693ad93a4939b939293899380937793707367935e9356834ca3439339a3309327931e9314a30aa30192f982f092e792de92d592cc92c392ba92b192a8929f9295a28c9282a279927092679
|10,1=>0x6f596ec96e396da96d196c7a6be96b596ad86a4969b9691a688967f9676966d9664965b96529648a63f9635a62ab6219618960f960695fd95f495eaa5dfb5d695cd95c495bb95b295a995a09597958e9585957c9573956a95619558954f9545a53c9532a52995209517950e950594fc94f2a4e994e094d794ce94c4a4baa4b19
|10,2=>0x79c9792a789977fa776976ca763975a97519748973f9735a72ba72297199710970796fe9
|11,0=>0x9c8a9bea9b599ac99a3999a99919988997ea974a96aa9619957a94da943a93a99319927a91e9915990ba90298f8a8ef98e5a8dc98d2a8c8a8bf98b698aca8a2a898a8908887987f8876986d9863a859a84fa845a83ba832982998209817980da80497faa7f0a7e797dda7d497cb97c1a7b7a7ae97a59
|12,0=>0xa119a0899ff99f699ed99e499db99d29
|13,0=>0xa1a8
|_,_=>0
def wAt:=mkWire dB 146 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xd07434250a0742429190d4081f0c0bc2428090a4343e02074302f090a024290d0f8302f090a024290207408370c0bc28240a094343e02074302f090a024290c0bc40320d0742428090a4541f150dc504d07094283510024341d0c0bc2428090a440090d074302f090a0242907024302f0a09028250d0f4343e02074302f090a024290e0dc1c21020d4302f0a0902825
|1=>0x713828350a254247f0713828350a2547c26071382835071388035130982835250d47c26071382835270dc5099140a8241d132547c260713828350d074706c0d094281d2307428870d148241d042041c4e1309828350d0f4081d0c0bc2428090a4340902074302f090a0242910028341d0c0bc2428090a4340902074302f090a024290d024081d0c0bc2428090a4706c
|2=>0x734424371f2041c4e1309828350c074302f090a02429250447c26071382835100c8341d090a024293d05428f3073442437150dc504d0709428350c3ac2870090d428252707c502b140a4241d0a374502b07094243709364504e0709428350d1482499140a8241d342643426140a8241d2732c246c091b4281d0d3082499140a8241d042e4b4260d1b4281d25044247f
|3=>0xa09028250d074302f090a024290d074302f090a02429150dc504d070942835074a44c27070942835090a4706c0d094281d240ac4c271309428352707c246e091b4281d1307c34290d1b8281d100c8341d0a4042826052643426140a8241d0a46425130d454281f1507c4c510d0a4241d270bc28240c07424290523428870d148241d401f428260713828353d05428f3
|4=>0x90a83452090741d350c0dc2825140dc50290907424eb0a1c024355807d5c35090a82499140a8241d02074302f090a0242902074302f090a024292455c4c241309428350a5344c520d0a4241d0d098981d140a8241d0d07434250a0742429020dc302f0a0902825460d425130d454281f13374502b0d0a4241d0950425120d454281f0923428870d148241d0c0dc302f
|5=>0xa0d4302f090a02429210a8345209074341d0b07424280d0c8241d090a41c72070d424350d0c4281d090a4246c0a0742429210a43452090741c2a1309828353a0742870090d42870090d428251309c4c250a0d49c370c07424290c07c2428090a434250d148241d0d098281d090a44c520d0a4241d132044c260a0d42825091b0281d09480346e0a07570245b0742837
|6=>0xd07428266807c256d0a0dc502b0d0a4241d240dc2871090d42515070a824350a66c4026070d428f00734424371309434290a07c25a50a1cc24352709c301d090a428354007428260a6644026070d4281d570d4242a0a1c82871090d41d910a34c24372d09c346d0a074706c0d094281d1b32c246c0a07428f30734424370c0bc2428090a5896d0907c2837240ac4c25
|7=>0x2d090346d0a07410811309828350a0d4346e0a0749c37140a4241d0a21c345209074b4260d1b4281d130941c250a0d428850d148241d1b34c34260a0743037090d428250d0a4346e0a07435820b07424280c07c29010a09835b9140a0241d0a0941c35090d42827140ac241d091b8281d090a4981d140a8241d090a434290907428f3073442437140ac1c25090dc3501
|8=>0xa0d430370a07c24290d0955c35090a890270c0d428250a0981c35090d44c270d0a4281d0d5181d5d090a98829070982435072044c260a0d4242b091b8281d2409c30350a0944c270a0d428250d094341d0a074504d0709428350d6042c1d090a035cd0a62c241f0d1481c25090d44c240a0d428250a34434260a07c246c091b4281d071384c260a0d45029070942437
|9=>0x73442437091fc1c4e0a0d43425091bc281d09484346e0a07588290a0d4241f0d494246e0a0744d890a0d4241f1314434290907424290d098281f4534434260a07d601d570d4242a5c0996c1d0a0dc28240c0742429100c8341d090a440320d0742429140a434290907434320c0d42825370d4502b09074281d0a40428267907c1c71090d4516f090742837240dc4c25
|10=>0x90a4345209074242a0d074282609264502a0907425a50a1cc243513144342909074341d090a024295c09d6c1d0a0dc247c071382835070a428d3090dc25230d1b8281d0c34c24370a0943499140a8241d070c824350a0947115070a8243505264502a09074b41f0d1b4281d0743828d1090dc504e0709428351c1b834250a0749c2b091b4281d1b57c242a0a07428f2
|11=>0x91b8281d570d4242a0d098281f0b07424280a1cc24350d07428260d074281d0a07424290c0d428250709424350c0d428250a09c24350a0982435090dc28250a214345209074341d0a40428260d094281d090a428f1073442437076942873090d4502b140a4241d1c0a82872090d45028140a4241d140ac502a09074516d090742837131403429090756025570d4242a
|12=>0x907424290a0d4241f071c42435620d4241f0a1c8243507574242a073442437140a8241d0a07424290d094281d0945c281f0d1b4281d0a4042826140a0241d0713828351309c2835070982435071342835091b4281d0d0742428090a82826140a8241d090a024290709424370c07c24290d0a4241d0c07c24290d0a42826071c824350907c2837140a0241d091bc281d
|13=>0xd07424280a0dc241d0a098281f090a4281d0d0742429140ac241d0d148241d09454281f095b42837100a8341d0a62c241f0d1b8281d0d0a4281d130942835091b0281d0a1c024350d098281d
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0xc40198006
|8,0=>0x55514144b511944150f143750c942e40a5424507d41a50554105
|9,0=>0x12a4499122447911a4459112443910a441910243f90fa43d90f243b90ea43990e243790da43590d243390ca43190c242f90ba42d90b242b90aa42990a2427909a4259092423908a421908241f907a41d907241b906a4199062417905a4
|10,0=>0x7acde83794de2377cddc3764dd6374cdd03734dca371cdc43704dbe36ecdb836d4db236bcdac36a4da6368cda03674d9a365cd943644d8e362cd883614d8235fcd7c35e4d7635ccd7035b4d6a359cd643584d5e356cd583554d52353cd4c3524d46350cd4034f4d3a34dcd3434c4d2e3
|10,1=>0xaacea83a94ea23a7ce9c3a64e963a4ce903a34e8a3a1ce843a04e7e39ece7839d4e7239bce6c39a4e66398ce603974e5a395ce543944e4e392ce483914e4238fce3c38e4e3638cce3038b4e2a389ce243884e1e386ce183854e12383ce0c3824e06380ce0037f4dfa37dcdf437c4dee3
|10,2=>0xb84ede3b6ced83b54ed23b3cecc3b24ec63b0cec03af4eba3adceb43ac4eae3
|11,0=>0x3582d58b542d48b502d38b4c2d28b482d18b442d08b402cf8b3c2ce8b382cd8b342cc8b302cb8b2c2ca8b282c98b242c88b202c78b1c2c68b182c58b142c48b102c38b0c2c28b082c18b042c08b002bf8afc2be8af82bd8af42bc8af02bb8aec2ba8ae82b98ae42
|12,0=>0xd847601d7c75e1d7475c1d6c75a1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x576c014ff0053ec014db004f7c013db0043ec010130027ec009db00236c007df001f3c006db00177c001ff0007ec001db000410000ff0003ec000df00036c000c10000c800016000050000120000140000300000800000
|1=>0xe76c037df00d7ec035db00cf7c033db00c7ec031df00c76c030df00c36c02dff00b7ec02bdb00a7fc029fb00a77c029db00a37c028db009f6c025fb00977c025db008f6c021fb00877c021db00836c019df0063ec018db
|2=>0x2c36c0a3db02877c0a1db02676c098db024f6c091df02476c089fb01f7fc07ddf01e7ec079db01d7fc075db01c7ec071db01b76c069fb01a76c065fb01977c065db0187ec061df0147ec040fb00f7ec03ddb00ecd8039fb
|3=>0x11d76c469db11977c465db118f6c441db10f76c43bdb10e7ec435db10cf6c425df108f6c421db10476c409fb10176c400db0a836c231db08c36c221db08866c129db04877c121db03e76c0e9db03076c0b9db02c77c0b1db
|4=>0x50cf6d41dfb506cc9039fb40d76d02ddb40af7d02bdb40a76d028db40977d023fb408f7d021fb40876d020df40836d001db22c7fc867df219f6c83bdf20ef6c831db20a37c828db208f6c821db206b644e1df12876c481db
|5=>0x2831dba0b76e829dba0976e0edfb81e76e069db81a37e068db819f7e060df81836e03bdf80c7ee028df80977e021ff626849829db
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x10302
|8,0=>0x6070c0b07130b09050c0410080a0d
|9,0=>0xb44596e2f540b5c200f161d0a1e1509125a7780266724181c662466351d69102483219c2c2c162e762d6a6d2437355d2236498e6b
|10,0=>0x6f2491283d2e3456685826324d9b9f91243e74397da5a1260e82241f49559d40953ca40e390f6462a93b7aa2377665538c898124963726765f94386c719a8e37a68e284371724f254997797e419191a30f3a4c2624248d4d4238247cad2438487824090eb219977231ab4e76986146175b3f45962a88373c7224974a98b0632e
|10,1=>0x93515492169eac97977027ae992430338a11
|11,0=>0x49a08f472a0e246f1a6075842b2e2787a7b17b8f2e508b241b39a0575ea81b7f25242e0e9047855337aa2484377b5e24734b2914505286524baf2a
|12,0=>0xa240e23240e240e
|13,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 22 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_223 11 roots_223 ops++addP pm 2 dom_95 9 roots_95 ops++addP pm 3 dom_191 12 roots_191 ops++addP pm 4 dom_127 11 roots_127 ops++addP pm 5 dom_231 7 roots_231 ops++addP pm 6 dom_253 12 roots_253 ops++addP pm 7 dom_251 12 roots_251 ops++addP pm 8 dom_247 10 roots_247 ops++addP pm 9 dom_87 6 roots_87 ops++addP pm 10 dzo_215_8 7 roots_215 ops++addP pm 11 dzo_239_16 8 roots_239 ops++addP pm 12 dzo_247_8 8 roots_247 ops++addP pm 13 dom_239 10 roots_239 ops++addP pm 14 dzo_111_16 7 roots_111 ops++addP pm 15 dom_215 7 roots_215 ops++addP pm 16 dom_243 9 roots_243 ops++addP pm 17 dom_237 9 roots_237 ops++addP pm 18 dom_119 7 roots_119 ops++addP pm 19 dom_79 6 roots_79 ops++addP pm 20 dom_111 7 roots_111 ops++addP pm 21 dom_207 7 roots_207 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_215_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_239_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_247_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_111_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_207 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 15 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 53 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 53 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 146 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 18 128 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 146 → Z 10 i = true := (range_split z10_0 z10_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 59 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 59 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.or, inputs := [5, 9] }, { op := GateOp.or, inputs := [1, 8] }, { op := GateOp.and, inputs := [10, 11] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.and, inputs := [4, 13] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [15, 5] }, { op := GateOp.or, inputs := [16, 6] }, { op := GateOp.and, inputs := [3, 17] }, { op := GateOp.and, inputs := [5, 7] }, { op := GateOp.or, inputs := [12, 14] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_51622_aux

theorem PEqualNP.Outside.L_meta_51622 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_51622_aux.main
