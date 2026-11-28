import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52576_aux
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

def dom_74 : Nat := 0x5050000000000000505
def goal_74 : Nat := 0xffccffccffccffcccc00cc00cc00cc00ffccffccffccffcccc00cc00cc00cc00
def roots_74 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffccffccffccffccee00ee00ee00ee00ffccffccffccffccee00ee00ee00ee00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

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

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xeeeeeeeecccccccceeeeeeee00000000eeeeeeeecccccccceeeeeeee00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfafafafaf0f0f0f0fafafafa00000000fafafafaf0f0f0f0fafafafa00000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefefcfcfcfcfefefefe00000000fefefefefcfcfcfcfefefefe00000000
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
def goal_109 : Nat := 0xfffafffafff0fff0fffafffaaa00aa00fffafffafff0fff0fffafffaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfffcfffcfffcfffccc00cc00fffcfffcfffcfffcfffcfffccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefffcfffcfffefffeee00ee00fffefffefffcfffcfffefffeee00ee00
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

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffff0f0fffff0f0f0f0f0f0f0f00000fffff0f0fffff0f0f0f0f0f0f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafafffff0f0fafafafafafa0000fffffafafffff0f0fafafafafafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcfffffcfcfcfcfcfcf0f00000fffffcfcfffffcfcfcfcfcfcf0f00000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefefffffcfcfefefefefafa0000fffffefefffffcfcfefefefefafa0000
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
def goal_124 : Nat := 0xfffffff0fffffff0fff0fff0f0f00000fffffff0fffffff0fff0fff0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffff0fffafffafafaaa00fffffffafffffff0fffafffafafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcfffffffcfffcfffcfcf0cc00fffffffcfffffffcfffcfffcfcf0cc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffffcfffefffefefaee00fffffffefffffffcfffefffefefaee00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_138 : Nat := 0x50500000000000000000000000000000505
def goal_138 : Nat := 0xffccffccffccffccffccffccffccffcccc00cc00cc00cc00cc00cc00cc00cc00
def roots_138 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_142 : Nat := 0x555500000000000000000000000000005555
def goal_142 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffccc00cc00cc00cc00cc00cc00cc00cc00
def roots_142 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffccccffffccccffffccccffffccccaaaa0000aaaa0000aaaa0000aaaa0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcf0f00000f0f00000f0f00000f0f00000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfafa0000fafa0000fafa0000fafa0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffcccc00cc00cc00cc00cc00cc00cc00cc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfffffff0fffffff0fffffff0fffffff0f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fafaaa00fafaaa00fafaaa00fafaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfcf0cc00fcf0cc00fcf0cc00fcf0cc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xeeeeeeeecccccccceeeeeeeecccccccceeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfafafafaf0f0f0f0fafafafaf0f0f0f0fafafafa00000000fafafafa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfefefefefcfcfcfcfefefefefcfcfcfcfefefefe00000000fefefefe00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffccffccffccffccffccffccffccffccffccffcccc00cc00ffccffcccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffeeffeeffccffccffeeffeeffccffccffeeffeeee00ee00ffeeffeeee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffafffafff0fff0fffafffafff0fff0fffafffaaa00aa00fffafffaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffefffefffcfffcfffefffefffcfffcfffefffeee00ee00fffefffeee00ee00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffaaaaffff0000ffffaaaaffff0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffccccffffccccffffccccffffcccccccccccc00000000cccccccc00000000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffeeeeffffccccffffeeeeffffcccceeeeeeeeaaaa0000eeeeeeeeaaaa0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffafafffff0f0fffffafafffff0f0fafafafafafa0000fafafafafafa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcfcfcfcf0f00000fcfcfcfcf0f00000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffefefffffcfcfffffefefffffcfcfefefefefafa0000fefefefefafa0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffff00ffffff00ffffff00ffffff00ff00ff0000000000ff00ff0000000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffaaffffff00ffffffaaffffff00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffccffffffccffffffccffffffccffccffcccc00cc00ffccffcccc00cc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffeeffffffccffffffeeffffffccffeeffeeeeaaee00ffeeffeeeeaaee00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fff0fff0f0f00000fff0fff0f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffafffffff0fffffffafffffff0fffafffafafaaa00fffafffafafaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffefffffffcfffffffefffffffcfffefffefefaee00fffefffefefaee00
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

def dom_200 : Nat := 0x101000000000000010100000000000001010000000000000101
def goal_200 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000000000000000000
def roots_200 : List Nat := [xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffffccffccffccffccffccffccffccffcccc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffccffccffccffccffccffccffccffccee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff0aa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffffffffffffffffffcfffcfffcfffcfffcfffcfffcfffccc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffcfffcfffcfffcfffcfffcfffcfffcee00ee00ee00ee00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_208 : Nat := 0x10001000000000001000100000000000100010000000000010001
def goal_208 : Nat := 0xffffffffffffffffffff0000ffff0000ffff0000ffff00000000000000000000
def roots_208 : List Nat := [xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffffffccccffffccccffffccccffffcccc0000000000000000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

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
def goal_216 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff00aaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffffccffffffccffffffccffffffcccc00cc00cc00cc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffccffffffccffffffccffffffcceeaaee00eeaaee00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0fafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffffcfffffffcfffffffcfffffffcfcf0cc00fcf0cc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffcfffffffcfffffffcfffffffcfefaee00fefaee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffffffffffcccccccccccccccccccccccccccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffeeeeeeeecccccccceeeeeeeecccccccceeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffafafafaf0f0f0f0fafafafaf0f0f0f0fafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffefefefefcfcfcfcfefefefefcfcfcfcfefefefe00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffaaffaaff00ff00ffaaffaaff00ff00ffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffccffccffccffccffccffccffccffccffccffcccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffeeffeeffccffccffeeffeeffccffccffeeffeeee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffafffafff0fff0fffafffafff0fff0fffafffaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffefffefffcfffcfffefffefffcfffcfffefffeee00ee00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffaaaaffff0000ffffaaaaffff0000aaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffccccffffccccffffccccffffcccccccccccc00000000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffeeeeffffccccffffeeeeffffcccceeeeeeeeaaaa0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffafafffff0f0fffffafafffff0f0fafafafafafa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffffcfcfffffcfcfcfcfcfcf0f00000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffefefffffcfcfffffefefffffcfcfefefefefafa0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff00ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffaaffffff00ffffffaaffffff00ffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffccffffffccffffffccffffffccffccffcccc00cc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffeeffffffccffffffeeffffffccffeeffeeeeaaee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0fff0fff0f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffafffffff0fffffffafffffff0fffafffafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffcfffffffcfffffffcfffffffcfffcfffcfcf0cc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffefffffffcfffffffefffffffcfffefffefefaee00
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
def isoMvS_138:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_138:Lower true dom_138 roots_138 goal_138 4:=lower_iso_b isoMvS_138 (by decide +kernel) lowS_41
def isoMvS_194:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_194:Lower true dom_194 roots_194 goal_194 4:=lower_iso_b isoMvS_194 (by decide +kernel) lowS_41
def isoMvS_196:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_196:Lower true dom_196 roots_196 goal_196 4:=lower_iso_b isoMvS_196 (by decide +kernel) lowS_41
def isoMvS_200:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_200:Lower true dom_200 roots_200 goal_200 4:=lower_iso_b isoMvS_200 (by decide +kernel) lowS_41
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
theorem lowS_45:Lower true dom_45 roots_45 goal_45 5:=lower_slice_b [(0x303000003030,32,36)] (by decide +kernel) lowS_41
namespace S_202
def pG:List (Nat×Nat):=[(2,10),(2,66),(2,130),(8,10),(8,72),(8,136),(64,66),(64,72),(64,192),(128,130),(128,136),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_202.map (·&&&dom_202)
def gM:=goal_202&&&dom_202
def NN:Nat→Nat
|3=>3
|4=>7
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x3bc1f0f9ad0816a
|4,0=>0x8ed148b2935464048d1b3f2752d96c1b4a7
|5,0=>0x23cd9170380f09e
|6,0=>0x23cd9
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x1400000000000000140000000000000014000000000000000080800000000000008080000000000000808000000000000000000000000000000050400000000000000000000000000000504a0a0000000000000a080000000000000a0a0000000000000a0941400000000000010100000000000001414000000000000101002800000000000000280000000000000020000000000000002505000000000000050000000000000005050000000000000500a0a0000000000000a0a0000000000000a000000000000000a014140000000000001414000000000000141400000000000000028000000000000002800000000000000280000000000000028050500000000000000000000000000000504000000000000000080800000000000008080000000000000808000000000000080801400000000000000140000000000000014000000000000001282800000000000000000000000000002828000000000000000505000000000000050500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x53105310536108531075361531e0531d0c5310b531085a3053910873653403210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x21022004
|4,0=>0xa952aa0536a5948a8c5
|5,0=>0xe51a2af5
|6,0=>0x3d4
|_,_=>0
def wAt:=mkWire dB 15 203 0x7ffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x10455504413154550405
|_=>0
def oO:Nat→Nat→Nat
|3,0=>0x20000
|4,0=>0x42000000002200
|5,0=>0x7161
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xf7630
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>0x80
|4,0=>0x80008
|5,0=>0xe4
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_200 4 roots_200 ops++addP pm 1 dom_194 4 roots_194 ops++addP pm 2 dom_138 4 roots_138 ops++addP pm 3 dom_74 4 roots_74 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_202 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_74 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_200 4 s (0,roots_200.map (·&&&dom_200)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_202 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_200 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xcccccccccccccccccccccccccccccccc,126)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_202==dom_202)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_202 gM v ys):RunD true dom_202 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_202 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_202 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_202 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_202 roots_202 goal_202 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_202
theorem lowS_202:Lower true dom_202 roots_202 goal_202 7:=S_202.noCircuit
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
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_45
def isoMvS_78:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_78:Lower true dom_78 roots_78 goal_78 5:=lower_iso_b isoMvS_78 (by decide +kernel) lowS_45
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 4:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_27
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_45
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_45
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_45
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 5:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_45
def isoMvS_99:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 4:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_27
def isoMvS_101:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 4:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_27
def isoMvS_105:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_45
def isoMvS_106:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_43
def isoMvS_113:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 4:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_27
def isoMvS_114:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 4:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_27
def isoMvS_116:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_45
def isoMvS_120:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 4:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_27
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 5:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_45
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 4:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_27
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_45
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_45
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_45
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 4:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_27
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 4:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_27
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 4:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_27
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 4:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_27
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 4:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_27
def isoMvS_198:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_43
def isoMvS_204:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 5:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_43
def isoMvS_209:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 5:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_45
def isoMvS_210:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_43
def isoMvS_212:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 7:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_202
def isoMvS_216:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 5:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_43
def isoMvS_226:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_45
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 5:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_45
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
|0=>0xf9c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x16
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_46 5 roots_46 ops++addP pm 1 dom_60 4 roots_60 ops++addP pm 2 dzo_46_16 5 roots_46 ops++addP pm 3 dom_42 4 roots_42 ops++addP pm 4 dom_54 4 roots_54 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_62 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_46_16_42 _ g hchk
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
theorem lowS_79:Lower true dom_79 roots_79 goal_79 6:=lower_slice_b [(0xaaaa000000000000aaaa,8,9)] (by decide +kernel) lowS_78
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
|0=>0xffde6878a183080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x2605430010
|6,0=>0x8789
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_92 5 roots_92 ops++addP pm 1 dom_84 4 roots_84 ops++addP pm 2 dom_74 4 roots_74 ops++addP pm 3 dom_78 5 roots_78 ops++addP pm 4 dom_86 5 roots_86 ops++addP pm 5 dom_90 5 roots_90 ops
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
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_90 _ g hchk
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
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_slice_b [(0x5050000050500000505000005050,32,36)] (by decide +kernel) lowS_106
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
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_slice_b [(0xa0a0000000000000a0a0000000000000a0a0000000000000a0a,8,9)] (by decide +kernel) lowS_202
theorem lowS_206:Lower true dom_206 roots_206 goal_206 8:=lower_slice_b [(0x5050000000000000505000000000000050500000000000005050,64,68)] (by decide +kernel) lowS_202
def isoMvS_87:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_iso_b isoMvS_87 (by decide +kernel) lowS_79
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 6:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_61
def isoMvS_93:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 6:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_61
def isoMvS_103:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 5:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_55
def isoMvS_109:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 6:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_61
def isoMvS_117:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_61
def isoMvS_118:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 6:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_61
def isoMvS_121:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 6:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_61
def isoMvS_122:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_59
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 6:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_61
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_79
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 6:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_61
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 8:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_94
def isoMvS_167:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 5:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_55
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 7:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_107
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 6:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_61
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_115
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 6:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_61
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 6:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_61
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 6:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_61
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_59
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 6:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_61
def isoMvS_205:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 7:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_59
def isoMvS_211:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 7:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_59
def isoMvS_213:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_203
def isoMvS_214:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 8:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_206
def isoMvS_217:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 6:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_110
def isoMvS_218:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 8:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_206
def isoMvS_220:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 8:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_206
def isoMvS_227:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 7:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_62
def isoMvS_229:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 7:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_62
def isoMvS_230:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 6:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_110
def isoMvS_233:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_94
def isoMvS_234:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 8:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_206
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 6:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_110
def isoMvS_241:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 7:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_62
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 7:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_59
def isoMvS_244:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 8:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_203
def isoMvS_248:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 7:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_59
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
|0,1=>0xccccccccffccffccffff3333ffff0000ff000000ffff0000cc00cc00ff00ff000000000033003300ffccffccccccccccffffffff33003300ffffffffccccccccffccffccffccffcc00000000ffccffcccccccccccc00cc0000ff00ff0000000000000000ff00ff00ccccccccccccccccff00ff0000000000ffffffffffff0000
|0,2=>0xfff0fff0f0f0f0f000ff0000ffff0000ffffffffffccffcc00cc00ccccccccccffffff00ffff0000ffff00ffffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x48158b0ca09205b1180ca0920440da08164328204d1180d708140a0920561031c24842c32822040c248114b0ca0880c24811440d108118b0ca0811902ca08118b0cf08130b2820463840c204d30b0ca2481031c21830811400c20461440c2040
|1=>0xca0920464042ca0920430920544cb0ca0811902ca0920532e12824812e028248164b0ca09204b0ca09f4812c368a08160b0d72820442ca09204e2c33ca09204b2824813932c31ca09210328248134b78a09204b29d09204b0ca0927012c3282
|2=>0xca09204d2c35ca09204b0ca0920542c32824813102d728248110b0ca0950502ca09204c10b0ca0920440d109204b0ca0950442c35c24812c394a4812ca0920648cb0ca09204b0d709205310b0ca0811842c309204c2c32820622c328204d30b
|3=>0xb0ca0920582c328248110b0ca09204b0ca09205340b2824812c329109204b28248138b
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
|0=>0xb492ca4b2a2c34b282c38b4b2924b2b292cb0d2c34b292ca04482ca4b294424b280d1cb282ca8b292ca514a2ca0b2b2ca844b2ca43452ca03512cad1492ca0b294414b282ca43352d2c3532caca372ca4b294524b282ca4b294414b2854144482ca544d2cacb2a
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xa30009100063000000cc03000000000000000
|6,0=>0x301002f1002d2acaa1a0a62002519063184800000007c9d2001b26480000172001610000050931448f238400000d1
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xf5fd5edfb5e5f77c5711c04d8304a1280842088014c44108370c81a0180400c0200400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xc050184238c0000000
|6,0=>0x51112b416330108a8000d88593a001113c0c93ab370005
|7,0=>0x33ad5f78c5b76
|8,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_62 7 roots_62 ops++addP pm 1 dom_29 4 roots_29 ops++addP pm 2 dom_61 6 roots_61 ops++addP pm 3 dom_54 4 roots_54 ops++addP pm 4 dom_59 7 roots_59 ops++addP pm 5 dom_45 5 roots_45 ops++addP pm 6 dom_55 5 roots_55 ops++addP pm 7 dom_31 5 roots_31 ops++addP pm 8 dzo_47_16 6 roots_47 ops++addP pm 9 dom_47 6 roots_47 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_63 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_47 _ g hchk
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
theorem lowS_111:Lower true dom_111 roots_111 goal_111 8:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f0,32,36)] (by decide +kernel) lowS_107
namespace S_119
def pG:List (Nat×Nat):=[(1,17),(1,33),(2,34),(2,66),(3,19),(3,35),(3,67),(4,20),(4,36),(4,68),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,23),(7,39),(7,71),(16,17),(16,20),(16,80),(18,19),(18,22),(18,50),(18,82),(32,33),(32,34),(32,36),(48,49),(48,50),(48,52),(48,112),(64,66),(64,68),(64,80),(65,67),(65,69),(65,81),(65,97),(96,97),(96,98),(96,100),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_119.map (·&&&dom_119)
def gM:=goal_119&&&dom_119
def NN:Nat→Nat
|4=>5
|5=>16
|6=>36
|7=>9
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xcd2909aa595cee526c46256ea
|5,0=>0xe1eecd8193ca840c816b930458dd535bbe75ab19589ff572904cd5a4071d3eb1e3ead43abeb19177
|6,0=>0xfd584f89ecd8383c7cebc325bbdbbdba40cad941a120da0b8896e99873f776b067503f73eed633535d38a4f8474872e47d794507040ec93eb1e35ac63222e281ee26828210680d7770bd4c0b8f30b65809726075920371c02dda
|7,0=>0xe8d9fb3398a4ab8721ca6aedf5d38a4ec5b4930603cbe
|8,0=>0xdaa04
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00cc00ff00cc00cc00cc00cc00ccff000000ff00000000000000000000ff000000ff000000ff000000ff0000aa00aa00aa00ff00aa00aa00aa00aaff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00000000ff000000ff00ff00ff00ff0000ff00ff0000000000ff00ff0000000000000000ff00ff0000000000ff0000f000f000f000f000f000f000f000f0ff00aa00ff00aa00aa00aa00aa00aaff00ff00ff000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00000000ff00f000ff00f000f000f000f000f0cc00cc00cc00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa
|0,1=>0x330000003300000033000000330000cc00ff00cc00ff0000000000000000cc00ff00cc00ff00cc00cc00cc00ccff00ff00ff00ff005500000055000033003300330033003300330000000000000000ff00000000000000ff00000000ff000000ff0000000000000000330033003300330033003300330000330033000000330033003300000000ff00ff00ff00ff00ff000000ff00000000ff000000ff00ff000000ff00000000000000000000ff000000ff00000000ff000000ff000000ff000000000f000f000f000f000f000f000f0000ff000000ff000000ff000000000000ff00ff00ff000000ff00ff00000000
|0,2=>0xff005500ff005500ff000000ff0000ff00ff00ff00ff00ff00aa00ff00aa0000000000000000ff00ff00ff000000003300000033000000000000000000000000ff00ff0000000000000000aa00aa00ff00ff00aa00aa00aa00aaff00ff00ff00ff00aa00aa00aa00aa550055005500550055000000550000ff00ff0033000000ff00ff00330000ff00ff00ff00000000000000000000ff00ff00ff00ff0000000000ff0000ff00000000000000ff000000ff00005500550055000000550055005500000000cc000000cc00cc00cc00cc00ccff00ff0000000000ff00ff00ff0000000000000000ff0000000000000000
|0,3=>0x3300330033003300000000000000000000ff0000000000ff00ff00000000ff00cc00ff00cc00ff00cc00ff00ccff00ff00ff00ff00cc00cc00cc00cc0000ff000000ff000000cc000000cc
|_,_=>0
def sP:Nat→Nat
|0=>0x6cb20604068b64858204021518100818100738320d0810040c60403883460182c83460172c85951810085060404c83410122c42063c02c44460402d03460402c320d18f00a20604038834604c2ca2020402481810080810071031811440c2040
|1=>0x192163460402c858604038a20d18100b216346069008346040a0b9cd18100b40d18100b0c83460403883460402e620d1810252c836418100b1083460632c83468802e120d18100b20d18100b8083460402de20d19d0402c834604070b20d180
|2=>0xb20d18100bd08346c4100b20d18101f2c83420402f33460402c83460401cb21618101f2c8c8d1b100b0c835418101020d18100b20d1810302c8bcd18100b1033460402c8b8d18100bb483460402c83460402ec20d181a8b20d18f00b214181
|3=>0x20d18100b20d18100b64834604068b20d181a402c420d18100b20d18100b38858d181
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x3929b54cec6162db15589ec49621b0f586ec31615b09583ec196
|6,0=>0xb1b575aacf4f7a43d05e74f337963c95e3cf177883c29a08cfe67bbbc59d4ee376e3b599a0cc97613aedd68ead753b281d32e92745ba11cfcc777
|7,0=>0x1a17cd3e4df18f857bf3dddee0f697
|8,0=>0x1a86
|_,_=>0
def wAt:=mkWire dB 53 120 0xffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x34b883600b483534b0d2d04b812d04d883b34b0b3610bc0ad20b81392cd0d2f34b8d2d34b085934b4d2d21f413620e4d2c34b1a2d100c83504ecb342cd842e7cb830720b563b34b4d2c
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x300000000000000000000000000000000000
|6,0=>0x1f200000001e10000000000001d1001b264972001524c92100102388d1000c1000a22087118451000000c800
|7,0=>0x291a0671986519063188611
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xfc9dd5d71d597e57e15e15794203001400a60a1060041040021020019018008006004001000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x18400000000000000000
|6,0=>0x6a80012400014090058c3a0cf0042902c0e0909000020
|7,0=>0x138e23495ef6
|8,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_115 7 roots_115 ops++addP pm 1 dom_99 4 roots_99 ops++addP pm 2 dom_101 4 roots_101 ops++addP pm 3 dom_86 5 roots_86 ops++addP pm 4 dom_85 5 roots_85 ops++addP pm 5 dom_103 5 roots_103 ops++addP pm 6 dom_87 6 roots_87 ops++addP pm 7 dom_55 5 roots_55 ops++addP pm 8 dom_118 6 roots_118 ops++addP pm 9 dom_54 4 roots_54 ops++addP pm 10 dom_117 6 roots_117 ops++addP pm 11 dom_116 5 roots_116 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_119 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_116 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_115 7 s (0,roots_115.map (·&&&dom_115)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_119 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_115 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_119==dom_119)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_119 gM v ys):RunD true dom_119 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_119 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
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
def dzo_106_16:=0x5050000050500000505000005050000
def gzo_106_16:=0x5050000050500000504000004000000
def gsh_106_16:=0x505000005050000050400000400
theorem lowS_zo_106_16_42:Lower true dzo_106_16 roots_106 gzo_106_16 5:=lower_iso_b (d1:=dom_106) (r1:=roots_106) (T1:=gsh_106_16) [(dom_106,16)] (by decide +kernel) (lower_slice_b (T:=gsh_106_16) [(0x505000005050000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_42_16:=0x505000005050000
def gzo_42_16:=0x504000004000000
def gsh_42_16:=0x50400000400
theorem lowS_zo_42_16_42:Lower true dzo_42_16 roots_42 gzo_42_16 4:=lower_iso_b (d1:=dom_42) (r1:=roots_42) (T1:=gsh_42_16) [(dom_42,16)] (by decide +kernel) (lower_slice_b (T:=gsh_42_16) [] (by decide +kernel) lowS_42)
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
|0=>0x885101845068870a0190a0180200403021018b90a019088850a018031650a023068870a0190a018068870a0190a0180200401845088850a0190a0180a1290a04503053068210a0190685c0a019030650a001068870a0190a018068870a0190a0180c8450a0010305103021048210300108819068bb0a0190a0180a0190a018148870a0180a0190a04500810088510a0010685c030510c86c0a001060640a001
|1=>0x1f00108819019d70a05f08801398010d850088190011d06053030010a0190201b0885103051018450a045030530881900866030211b00d088a9030230a015000210a019018450a02108851088210305103021068470a0190c80508819031790a0470d8030881908885018450a0180885102017088510880106845019850200308801068210a0190c8230a0010a0190a018068870a0190a018048510300100845
|2=>0x19d70a05f1d8180200100847030210a019030210a00108a39018ab03023088190302108819030ee0c845068870a0190a0180201b0a045088010a00101a150303308851089d9030010a0230a01508801040010682303051031670a023068230305108a150303308821030010a16803031008100885103021031650a023030510b8060880100847089b6041d90181a030320882103045030030a0180a01901845
|3=>0xd853088190302103030088210881a0c845019cf0d85008819030650a0010a06f08819041290a01a03001088520a168008452c8010a02308819001450085315051030231281a01845108210305001845088214b82202018031650a0230201808851088190a0194e81907850068030a01901a2d0a00302015088514b801020180885115012088510a1e903003018b9088850a0181d8180c8450a001068470a019
|4=>0xa0180a33d0201a08851018160400103052018452c8010a023068470a019078ab030230184507887018450a0180a0450a01a088190311f060530181600021088510685c0a0190a1290a01a018450a3110600300853030210198702003088510a01902001088510c81b0a001020190a021041290a01a0a0450a1d90181a07885018450a018088890a01b03033088210882101845030212d053030210c84503033
|5=>0xd8530e8210a01908b9501814040010683e0a01901845108020a0180605308821018166f8030d80d0a021088210184501a5d02018030150881904001088850a0190a01803032019d50a05f0336b07853068030a01944851089d9060640a001088190885103051030660a0011d81b020010d850088190a0190680d0a01901845088010085303021030510d850088190317d0a0010301108851398220d85007887
|6=>0x7850018450a02101845068870a0190a01808be5018870a0180683c0a019048510300100851030210a01b0a01a018457b0230200d08b950181404001032830a01b01845030890a01b0885106847030510683e0a0191281a0a0210a019088850a0180a0a9030230a019088650c8040683c0a0190c845030210881908851088a90680f0a019008470a0180a0190c84708851031650a023030ee0a05d089650a023
|7=>0xa05c088010201a088510a023018450a023000210c8190a0010201a08851068030a019068470a0190181a088510b819088010317908852041d90181a0c81b0a0010a1d90181a10822030500b823088010d8510881903053030210a01b0a01a08801030210a3ef0881a0303108821030010a02108851088210781b01845030470302103023018450485203001043ed0881a02018088510a0450a0010a1e903003
|8=>0xd80d08819030320882108821030210a0190a0180885100021030330882103051030210781b018450b81b088010c8470a0010201b08851088850a01803001088510a001040010a01a0184500845030210a00308819030010a0230a0210881a0605108821030010a00100413018520c8450a0010301504001088520300300803030210680f0a01902001088510a1eb030030305103021089290a01a0a00308851
|9=>0x18ab0302308815040010a021088210d82308819018450a018030030a0230c8190a0013d021030030a0190a0210885108852030510200f088511082103050088010a0230d801088190881901851000890305201816040010a01a088510a019018450c8210a001018850a01801814040010a0190a0030a01908a2d0a003088190a0010200d08851068030a019068470a0190a021088010a019018470a0450a001
|10=>0x4001030230a021018450181a01851018470a0010a0a903023088850a0180a019018870a018088190885101a2d0a0030885103051088870a01803053088190a0190a01b088010a05f088010182108819068450a01901845030210a01908c110185201847030210a019089e9030030b821088010680d0a019030210a0010a01908821000210a0450a0230a0190885103051088010184502023088510885103003
|11=>0xa0180a0190880101821018450a01a088510881a0a023
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x94c00008c8000084800007c80000000000000000000001c30000000064c00000000000000000060400000000000000153000000000001230000000000000003cc0d20000000000000000000a30244000000000002040000000000000006200000000000000000004200880000008000
|5,1=>0x10cc412000000010040000fc43b40e483540cc80000c0c00000002d300002c10000000000000000000000a10000000000000000000000000
|6,0=>0x258c000000000025440000000932240c00023888d122c88a100008910000872214884120c48031f8800000007b31e0c7621d440001d047221c080001b4c6b21a0c0001988642184c00017c85d217045b1000059215c854314c451214044f1000000013484c1128848211880000000000
|6,1=>0x3b080003a88e910000e720000e520000e41384ce0137c4dd236c8d9235c8d5234c80003448cf2330cca2000000032080000000c53308cc022f88bc2000000000000002e88b732d0c0000000b312c480002bc80000000ac32a880002a08a622908a2227cc9d226c80002648000
|6,2=>0x4f0d3a24e093624d080004c4d2e300012c24ac40004a492720001261490921347c800000011d2468d19100011720001152450513144490e342cc000424800041c8000410c00000000000001022404400000010013f88fb33e840003e4400000000000000f630000f423c88f020000ee2
|6,3=>0x63c8000000000000018d200018b2628588200018716185842608800060080005fc57d25e8d7825d4c0005cc80005c84000000170200016d35ac80005a0c000000165359040005889602578800057095a255cd55254c950300014e200014d1000000053054a25245472514943250493f2
|6,4=>0x1b936d8db4200000006c880006c09ad36ac9a8369c5a52688da0267899c2664d97200000006584000654594100019226444000
|7,0=>0x8e8a3828d8a3428c8a3028b8a2c28a8a282898a242888a202878a1c2868a182858a142848a102838a0c2828a082818a042808a0027f89fc27e89f827d89f427c89f027b89ec27a89e827989e427889e027789dc27689d827589d427489d027389cc27289c827189c427089c026f89bc2
|7,1=>0xacc6b12abcaad2aacaa92a9caa61a90aa22a80a9e2a70a9b1a64a972a586942a48a902a38a8d1a2ca892a206862a10a822a00a7e29f0a7a29e0a7629d0a7229c0a6f19b4a6b29a4a672994a632984a5f2974a5b2964a572954a5329486502938a4c2928a482918a442908a4028f8a3c2
|7,2=>0xad8ab42
|8,0=>0xb206c71b186c51b106c310002c21b046c01afc6be1af46bc1aec6ba1ae46b81
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0x1068000818000408000202000100800080000020200008c000045800020c00010000005f00002f0000148000096000048000021000010400008000003c00000f000004800002000000c00000500000240000100000060000020000008000002000000
|1=>0x50100021a80010cc00085e00042e00021080010080008020004000001f6c000cfe000677000339800197c000cae00065300032100018fc000c3e000420000203800100800080000038b0001c48000e040006080002df0001220000908000434000213
|2=>0x2080801022000810000400a0020040010010008006004002002000800e02c0064360030000010208008080004000001a9b000c05800500000247600100100080000039fc001cbe000e5b00072b80031800014be000a53000521000290400140c000a05
|3=>0xc208006004802960201280300852d804293402143e010a1300841180408480201a4010040007909803c02c01b43600da1300692d802497c01243e008e5f00452f802295c0114a6008412004208002011c01001c008002003985801280c008416004207
|4=>0x2876f8143b4c0a143e05079302470d8102818080d36040689020180010020008000204000001854d80c287c06141602380b011404808602c042436020e57010431008210804104402080a010400008094c0404660200420100110080020040004019257
|5=>0x284929910295c851c36419e9320cf29906786c832c26418a1f206909902286c80a63e220a0210852f8810e24400488200204100100052104820200408535f04298f821196c1064a60820610410118206b64101cba08084904032f820195c100086080009
|6=>0x5021a6e010006e2021760690bb0008dd80042ea2020240398fa01840d00a43e80022632052a990095cc8042e620a1330850f9816e74c0042e519253
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x202000005002c0b020c020002000002000500000000000012000000000000000f0002000200020000000000000200000200000000000300000000260000001c0000000002020000000000020300000005000000001900000000000402000200
|6,0=>0x1000225005d0002004b3c820d020246382a5d00025d2f0100000100003b1e090202000000001a1b145a003797511a0000321a00574c7439590202001a000e00005218000001170002010105005d00021a055f130100003f775d3700af1a06003a1a2b005c064f00271a5d05001a953b945d5b9600000237020202000000
|6,1=>0x1a000000181000640502005d030202001a00941a990221001a0005000002007202001c000035050002ad020009078b0202380064000500005e1aa0880101020a0f641a580900660b000f870016020003040f010000027602000100028129020f65001a000e007300000000020300005409a1050003000000000a00021a020039
|6,2=>0x2d0b0200000200023c0298151d0f380a4e2e02000083000308000a0300
|7,0=>0x83458bb88a483d7f4179d1856f1ebd36b033cab91f68637c448acf8d2224cb564d6b42c5aa278e3eb94962c87eb36d8a69b26c99677a921ebc233a619ec4ae55a9322853a6c0cdc186491ec26aa79a40118fc79bd0ac43abbbcc48a434917931707db184be4475ce7b80c68047c989a5496049a81f90bfa26e9da38cb430b671
|7,1=>0x324a
|8,0=>0x499fcdd2b94944933178b53250b780ba9cc3
|9,0=>0x20
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_115 7 roots_115 ops++addP pm 2 dom_57 5 roots_57 ops++addP pm 3 dom_90 5 roots_90 ops++addP pm 4 dom_107 7 roots_107 ops++addP pm 5 dom_113 4 roots_113 ops++addP pm 6 dom_121 6 roots_121 ops++addP pm 7 dom_74 4 roots_74 ops++addP pm 8 dom_42 4 roots_42 ops++addP pm 9 dom_59 7 roots_59 ops++addP pm 10 dom_105 5 roots_105 ops++addP pm 11 dom_91 6 roots_91 ops++addP pm 12 dzo_106_16 5 roots_106 ops++addP pm 13 dom_114 4 roots_114 ops++addP pm 14 dzo_42_16 4 roots_42 ops++addP pm 15 dzo_107_16 6 roots_107 ops++addP pm 16 dom_75 5 roots_75 ops++addP pm 17 dom_83 4 roots_83 ops++addP pm 18 dom_41 4 roots_41 ops++addP pm 19 dom_120 4 roots_120 ops++addP pm 20 dom_99 4 roots_99 ops++addP pm 21 dom_27 4 roots_27 ops++addP pm 22 dzo_43_16 5 roots_43 ops++addP pm 23 dom_51 4 roots_51 ops++addP pm 24 dom_106 5 roots_106 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_106_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_42_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_107_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_27 _ g hchk
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
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(4,20),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(8,9),(8,40),(8,72),(12,13),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,56),(24,88),(32,33),(32,36),(32,40),(48,49),(48,52),(48,56),(48,112),(64,68),(64,72),(64,80),(65,69),(65,73),(65,81),(65,97),(96,97),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|7=>3
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x7f2e4534134624f
|8,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccc8888cccc8888cccc8888cccc888b3333333000000003333333300000000cccc0000cccc0000cccc0000cccc00033303330333033303330333033303330cc00cc00cc00cc00cc00cc00cc00cc0303030303030303030303030303030308888888888888888888888888888888b3333333333333330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x35688d5a237ad11ac688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0x398ee07
|8,0=>0x146
|_,_=>0
def wAt:=mkWire dB 8 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x354d
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x441
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 6
def pmP:Nat→Nat
|0=>0xfffedf3ff01f000
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x5a
|8,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_124 6 roots_124 ops++addP pm 1 dom_121 6 roots_121 ops++addP pm 2 dom_117 6 roots_117 ops++addP pm 3 dom_109 6 roots_109 ops++addP pm 4 dom_93 6 roots_93 ops++addP pm 5 dom_57 5 roots_57 ops++addP pm 6 dom_61 6 roots_61 ops++addP pm 7 dom_116 5 roots_116 ops++addP pm 8 dom_85 5 roots_85 ops++addP pm 9 dom_105 5 roots_105 ops++addP pm 10 dom_45 5 roots_45 ops++addP pm 11 dom_92 5 roots_92 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_92 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_124 6 s (0,roots_124.map (·&&&dom_124)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_124 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_125==dom_125)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
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
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=lower_slice_b [(0xaaaa000000000000aaaa000000000000aaaa000000000000aaaa,8,9)] (by decide +kernel) lowS_206
theorem lowS_219:Lower true dom_219 roots_219 goal_219 9:=lower_slice_b [(0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a,8,9)] (by decide +kernel) lowS_218
namespace S_222
def pG:List (Nat×Nat):=[(2,10),(2,66),(2,130),(4,20),(4,68),(4,132),(6,14),(6,22),(6,70),(6,134),(8,10),(8,72),(8,136),(12,14),(12,28),(12,76),(12,140),(16,20),(16,80),(16,144),(18,22),(18,26),(18,82),(18,146),(24,26),(24,28),(24,88),(24,152),(64,66),(64,68),(64,72),(64,80),(64,192),(128,130),(128,132),(128,136),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_222.map (·&&&dom_222)
def gM:=goal_222&&&dom_222
def NN:Nat→Nat
|4=>8
|5=>45
|6=>181
|7=>132
|8=>31
|9=>6
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x3d858239be232f01e84611d6b0e6b10ac7502cbc
|5,0=>0xc3de07881372db56ceef67314620bb565d24b80649f093dac83b5a23835735bed320e02de882d1922c85229e6f25a1725810256cd2478423d9a202931f89f1c70e1bee518f2a18a64174b5161b5147a8145640fa900bc3b0b9cc0b65509cd9091b0075ec064930586605089041ec02831
|6,0=>0x398bb3810737bc636dfd3637e35f6d34c2134202336cc32a43326ea321113150830cc12f5992f0902df902d5282c3202b9ae2b6ab2addf29e2427e20276522690b250a224a8223c8a23a71226b22256121f1d21d14218332060c1fc211ed881e59f1da151d9891d7ae1ce821cb601c0821ba7c1aeab18e8f186c9181f9181d217b2c17734170cb16f9216ed716bc7157a01495213f7913d9713cb512a8c12421121011190c1137310f0a1083c104de101840ffb70ffa30ff540fbc30f87d0f3010f2590ef3e0e9e60e5bf0e2440db7f0d95e0d6f00d3700cbfa0c3590bf050b5780b2f30ae5f0ad7a0acdb0aa710aa6e0a8d60a7140a37309cdc089c30895508723086e5086b90813c07f65071d10703b0618a05521052b90505504b3d040ad03eb40302402a1d02831024ae02246017e9013d0012df00ff000522003ce00222
|6,1=>0xc3de09c11e8f22487e7886de5847b983ab78137379ba0769c075506737ff6ef8c671d86438263e3062dd6606665f4605eeb95bece5af1e57cdf5704955ca7559d5559805502c547275181b4f7414b8a64ab6c47a2446578455b64522443d434298a42074416ab412a840ab33fda43fcf33f6833f0f13ded43d3b63d2433a77239d6d39b51
|7,0=>0x7605873c646d7e36b9fa6ad1b69b9d6787265d025eac75149650a624c3ce4aeab4ae0e4a8ed478f3458054556d453594489b444273e2923d2d53cfe83c4e83bee438c7f38c39387d4378b437741356c8355813541234a68335dc32d77327ed3264831a88310652fa342f0352ea592e07b2de5a2c62d29fd12905e28fca28e5b287262769126f672566b236d92334722561223a02183320b1f2043c201151ff361fbb31f5eb1ef971e1d41de121cc6c1c58d1b09e1af1c1ae691acb51968818cb8187a918423180d316444164031632a1620b15f0f15dc11592a14740140e4136281303b12c531299e1298d11fc211991118f310cce1015b0fc980fc000df7a0cf520cced0be0f0b1c30ad530a6900a3ee09dd209aae08ee907a80067b6065bb0651d0609d05e5c05a59058e90581b045ab04112037e702de402048008d100208
|7,1=>0xb09089c09c846d17d633
|8,0=>0x962ab88d1354b97500464b6a54a5a84a23448f353e10d3a41531a9429ee0276692680925d1c24f0e24bd61cad115662149d80ead10e24c0dec70de0e0cc540be1a0a8130882406328054ff02b63
|9,0=>0xbad5e62fd6577e12b37d05964050df
|10,0=>0xbad5e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaa00000000aa00aa0000000000aaaaaaaa00000000aa00aa0155555554000000015555555400000001555555540000000141414142aaaaaaa800000002aaaaaaa800000002a802a80000000002a802a8055555555000000005555555500000000555500000000000055550000aaaaaa8800000000aaaaaa8800000000aaaaaa88000000008888888955540000000000015554000000000001555400000000000155540002828282800000000282828280000000028282828000000002828282855555500000000005555550000000000555555000000000000000000aaaaaa0000000000aaaaaa0000000000aaaaaa0000000000aaaaaa0155555554000000015555555400000001555555540000000000000002aaaaaaa8000000000000000000000002aaaaaaa800000000000000055555555000000005555000000000000555555550000000055550000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aa00aa0155555540000000015555554000000001555555400000000141414142222222200000000222222220000000022222222000000002222222255555555000000005555555500000000000000000000000000000000
|0,1=>0xaa00aa0000000000aa00aa0000000000aa00aa0000000000a800a800015554000000000001555400000000000155540000000000015152aa82aa8000000002aa82aa8000000002aa82aa8000000000000000055554444000000005555444400000000555544440000000000000000aaaa888800000000aaaa888800000000aaaa888800000000aaaa888955555510000000015555551000000001555555100000000154015402aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002222222200550055000000000055005500000000005500550000000000550044aaaaa8a800000000aaaaa8a800000000aaaaa8a800000000a0a0a0a155555554000000011111111000000001555555540000000111111112aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002aaa800055555555000000005555555500000000505050500000000050505050aaa8aaa800000000aaa8aaa800000000aaa8aaa8000000008888888954015400000000015401540000000001540154000000000154015402aa82aa8000000002aa82aa8000000002aa82aa8000000002aa82aa855555550000000005555555000000000555555500000000055550000
|0,2=>0xa8a8a8a800000000a8a8a8a800000000a8a8a8a8000000000000000151515150000000015151515000000001515151500000000151515152aaa2aaa000000002aaa2aaa000000002aaa2aaa000000002a802a80000000000000000055555555000000000000000000000000555055500a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a000a0000014544000000000001454400000000000145440000000000014140022002a800000000022002a800000000022002a8000000000220022111111110000000011111111000000001111111100000000111100000000aaaa000000000000aaaa000000000000aaaa000000000000888955555554000000014141414000000001555555540000000141414142aaaaaaa800000002aaaaaaa800000002222222200000000222222220505010100000000050501010000000005050101000000000505000000aa00aa0000000000aa00aa0000000000aa00aa000000000088008800015554000000000001555400000000000155540000000000014140282800280000000028280028000000002828002800000000282800000000000000000000505050500000000111111110000000000000000
|0,3=>0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a00015554015400000001555401540000000155540154000000015554000002a802a80000000002a802a80000000002a802a800000000000000011111111000000001111111100000000111111110000000011101110000a000a00000000000a000a00000000000a000a00000000a0a0a0a04404440400000000440444040000000044044404000000004400440000028a880000000000028a880000000000028a880000000000028a8111111110000000011111111000000001111111100000000110011000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a000404040400000000040404040000000004040404000000011111111002a802a80000000002a802a80000000002a802a800000000028002800001111000000000000111100000000000011110000000000000000aaaaaaaa00000000aaaa00000000000088888888000000008888000115151514000000011515151400000001151515140000000111111110282828280000000028282828000000002828282800000000000000000450045000000000045004500000000004500450000000000440044
|0,4=>0x202020200000000020202020000000002020202000000000000000155540154000000015554015400000001555401540000000155540110000000000000000028282828000000000000000000000000202020250505050000000005555555500000000505050500000000054545454aa00aaaa00000000aa00aaaa00000000aa00aaaa00000000aa00aa0155555554000000015555555400000001554155400000000155415542aaaaaaa800000002aa82aa8000000002aaaaaaa800000002aa82aa855555555000000005555444400000000555555550000000055554444aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaa888955555554000000015555555400000001555511100000000155551112aaaaaaa8000000028282828000000002a802a8000000000280028000000555500000000000055550000000000005555000000000000000000000000000000000000000000000000aaaaaaaa00000000aaaa888800000000000000015555555400000000000000000000000155551112a82aa82800000002a82aa82800000002a82aa82800000002a802a8050555055000000005055505500000000505550550000000050505050
|0,5=>0xaaaaaaaa00000000aaa0aaa044444444000000004040404000000000444444440000000040404040888888880000000088888888000000008888888800000000808080811111111000000001111111100000000111111110000000011111100aaaaaaaa00000000aaaaaa0000000000aaaaaaaa00000000aaaaaa015555555400000001555555540000000155555554000000015555540000000000000000000000000000000002aaaaaaa800000002aaaaa800055005500000000005500550000000000550055000000000055000022222222000000002222000000000000222222220000000022220001555555540000000155555554000000015151515000000001515151502828282800000000282828280000000028282828000000002020202555555550000000055555555000000005555555500000000555055500000000000000000000000000000000000aa00aa0000000000a000a154015400000000015401540000000001555555540000000155415540888888880000000088888888000000008888888800000000000000051515151000000005151515100000000515151510000000050505050
|0,6=>0x22222222000000002222000000140014000000000014001400000000001400140000000000000000282828280000000028002800000000002828282800000000280028050555055000000005055505500000000505550550000000050545054000000000000000000000000000000000000000000000000aaa0aaa1555555540000000155555554000000000000000000000001554155400028002800000000002800280000000000280028000000000028000555555550000000055555555000000005555550000000000555555000000000000000000aaaaaaaa000000000000000000000000a8a8a8a9555555540000000154015400000000014141414000000001400140000002aaa8000000000002aaa8000000000002aaa8000000000002aa811001111000000001100111100000000110011110000000011001100000000aa00000000000000aa00000000000000aa000000000000000155555554000000015151515000000001555555540000000151515152aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002a2a2a2a55555555000000000505050500000000555555550000000004040404
|0,7=>0xaaaaaaaa000000000000aaaa00000000aaaaaaaa00000000000088880000000000000000000000000000000000000000000000015555111002a802a80000000002a800000000000002a802a80000000002a8000000500050000000000050005000000000005000500000000000400048888aaaa000000008888aaaa000000008888aaaa000000008888888955544444000000015554444400000001555444440000000155540000000282a800000000000282a800000000000282a800000000000282800000000000000000000000000000000005500550000000000550000aaaaaaaa00000000aaaaaaaa0000000000aa00aa0000000000aa000000000000000000000000000000000000000000000000000155555402aaaaaaa800000002aaaaaaa8000000000000000000000002aaaaa800000000000000000555555550000000000000000000000005555550000000000000000000000000000000000aaaaaaaa00000000a8a8a8a8000014140000000000001414000000000000141400000000000000000002aaa8000000000002aaa8000000000002a800000000000002a8055555454000000005555545400000000555554540000000055550000
|0,8=>0xaaaaaaaa000000000000000000000000aa00aa0044444444000000004444444400000000404040400000000040404042aaaaaaa800000002aaaaaaa80000000002a802a8000000000280028000000000000000000000000000000000000555500000000000044440000000000000000aaaaaa00000000000000000000000000aaaaaa0001540154000000000140014000000000015401540000000001400142aaaaaaa800000002a802a80000000002aaa8000000000002a800000000000000000000000000000000000005555444400000000555544440000000000000000aaaa8888000000000000000000000000aaaa888800000000000000000000000000000001554155400000000155415540000000000000000000000000000000008888888800000000808080800000000000000005555555500000000000000000000000044444444aaaa000000000000aaaaaaaa00000000aaaa000000000000aaaa88880000000000000000000000000000000014141414000000001400140002a802a80000000002a802a8000000000280028000000000028002800005555000000000000555500000000000044440000000000004444
|0,9=>0x155555554000000011111111028282828000000002828282800000000202020200000000020202020055005500000000005500550000000000550000000000000055000000000000000000000000000000000000aaaaaaaa00000000a0a0a0a000000000000000015151515000000000000000000000000151515152aaaaaaa800000002aaaaaaa8000000000000000000000002a2a2a2a00000000000000000000000000000000555555550000000055005500
|_,_=>0
def sP:Nat→Nat
|0=>0x2c12012b001209162a05000c09012905001209282705000a12261306000c121701050a12252406050901232205000a0d012106050a120901062009011f1e05000a031401051d0a1a09190500150d090105080a09011805000403090b000c12171606150d090b050a0f141306100f0e0100040d090b060c03090b050403020100
|1=>0xc120938060a0f0d013f060a2d260106000a030121050010120e01050012093c2205000a123b0105000a12143a06051209383905000a12383705000a12093605000a03020105000c1a090106050a2c090135000412092506341b120933060c120201050a1214162f0a0e013005000a2d092506050a03091305000c0f0901080a
|2=>0x12206050a492c120901000a0901180500470a0901230500151209010534000a0f0d0e09010648430a1209250543460a120901050a1112400105000a11450105000c120916010644070c03090106050a12093c050043420a1209010a4140010500151a090105000a121416062f0c0f090106080c1217010605100f0901060004
|3=>0x5806050c12090157060a1256015505000a5412012b05000a520d090105000a1225013f06051b0c120916060a1226012b06000a125001054f00040a09011805000a1112012b05000a0f12013f0600150a0f0d0901060a122e2625064e0a09012305000a124c26010500041209011c00154b12090105001b1512092506050d1209
|4=>0x1000a12093c0605000a5f120e090105070a4b09010500431b0c120901050a4a12260106121401220531000a1214015e06071509015805000a122e0e5d05004604120901060a0f12095c0500590a12090106055b070c120901060a09013005000a0f0d090106310a490901350500590a0d120901050a0f40090105000a0d0901
|5=>0x640544000a120925054f005b0a12013f0500126109012205000a0d09010605080a0d09010605630a122e0e1905000a1262095d05000a1201370605000a1226015505001b0c12091906050a0d12013705000a0312095c05000a1226090160000a495f120901060a1226320105000a0340090105000a1256261401060a542c1209
|6=>0xa0d260901063d0c12090106051c040a090123060042040a120901000a12013f6905000a0d0938053d00541209016505001b0a092523050068070a0f090106680a12013705000a1256670901060a12096601060a540901350500111209016505001b0412092805000a1109013505000a110f0e0106001b1209162705000a1209
|7=>0x12013f0572000a1209165d05000a110e013505000a0901232705001012090105000a122e265d05000a0f09017106701209010605000a120901054f003e0a0d090106050a620901230500470a12090105000a0d090106056e0a0d09016d060a0901230544000a1226011d000a6c09012305000a6a12090106053e120901056300
|8=>0x60a491209380500430a12091601060a12732e0925050a120e01054f000a410901056e000a110d093805000a09192305510012090122053d00150a09012305005a590a120901050a1226140106510a4a12093c0500120e01220572000a0e09012305000a490d2609010659040c120901050c1209010534000a12562e09160604
|9=>0x1901060a2e09011f05000a0309010508000a030901056300590a0f120901060a1267140901060a120916061c000a4112093a05000a0d1209017705041209010563005b590a0d0901050a125001053100750a1209010605740c0a120901060a0309015805000a12500916060068040c120901060a0932013005000a1256262501
|10=>0x500150a12013705000a4a0d1226010674040c120901000a12013f58050059150a120901050a0901300605000a121401051d0a120e093c050048460a120901061b1512013f05000a12621401060a4112260106001512013f0544000a12097b0551007a0a12012405000a12562601061209017905000a122601066e000a122614
|11=>0x62091625060a490f0d0901060a5f03120901050a4912261401060c0a120137050074150a120901000c12097b0106050a12670e09010048430c1209010511122601220500070a03093805000a0901237c050015120901051c00071512013f05000a12730e0901050a1273091625050a1209195d0500480a1209250611120e0122
|12=>0x5b590a12090105000a1209017f05000a122e0e14010500740a0d12090105007e0a12090105000a2c0d120901050047460a12090105000a122e14010605120e09012206050068040d12090105000a110f09010600680a0f0d090105000a1209016f05000a1209017d06000a122e091905000a12093c0500150a12095c05000a12
|13=>0x9010551000c0a12090106053d0a12090106053400040a1209190106000a120925018505000a120e26010531000a120e09010551000a091916012305001b0a120919250500830a1209010500070a03090105000a12090106052f000a1214090182050046040c12090105000a1226018105000a12091625060a12097b01054400
|14=>0x605440a120901055131000a12140901350500870a12092505000a860f090105000a120901800605680a0312090105000a126209190105000a12612e090105000a1226092501060a12090105446300480c12090105000a122e141605000a12091901054400470a1209250105000a4b1209010605000c0a031209010605150a12
|15=>0x1250090105000a120e0919010500460a1209250106050a1209018c05000a12093805008b0c12090105000a1214018a0500150a12013f05000a4912140105000a4a0f0d090105000a120e09015d050059070a12090105001b0a12091905000a1209160551000a120919012705000a128909010500880a12091605000a0d120901
|16=>0x48040a12090106000a12622e09010600481b0a12092505001209012205000a120901280605000a54120901060500480a12090106000a120901051c0047040a12090105000a0d120e090106050a0f12093805000a1209168005000a120901054f0015040a12013f0500470a12090105000a1226018e05000a1209018d05000a
|17=>0xa11120e010605005b0a0d090105000a1291090105000a127326090105000a12092501270500070a90090105000a12610e090105000c1209010605445a0a0312090105000a1262092505000a12090155060500070a8f090105000a12560919010500070a1209010563000a121401060531460a12090106050a4a0312090105
|18=>0x10605000a1209013505005b070c12090105000a122e09190605000a1209019406050a1209017106050c0a12013f05000a122e262505000a1112930105000a0d090106053d0a1209012705000a491112140105000c0a0f120901065b040a0d090105000a122e0e0105000a494a1209010500150c1209010544000a5f12090105
|19=>0x5070a0f090105000a1112260105000a1209015e05000a120e01060531000a120919060551000a12097b0105000a1226010531007a0a1209010500120901220605000a12261401060a490d26090105000a125009010605000a120938060500150a12013f0605000a120e010531000a1240090105000a1209190551007e0a1209
|20=>0x461b0a12090105000a111209010605000a12561409010500040c12090105000a4a1209010500870a12090105000a122e092505000c0a1209160105000a1214090106050a031209010605000a030d1209010500150c0a12090105000a12090106053d00680a12090105000a120901950500040a0d12090105000c0a12090106
|21=>0xa12090105000a12090105000a1226090105000a1209160105000a122e090105000a1209010605000a0d12090105000a120e09010605000a120901060544000a120901053100150a12090105000a120e090105005b0a0f1209010500480a1209160105000a1209162505000a1209010544000a0f12090106000a1209960105
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x23501e50195014500f500a500550005
|5,0=>0x12b6125611f61196113610d6107610160fb60f560ef60e960e360dd60d760d160cb60c560bf60b960b360ad60a760a2509d50985092608c60866081507b6075606f60696063605e50586052604c60466040603a6034602e60286
|6,0=>0x2e072d972d272cb72c472bd72b672af72a872a1729a7293728c7285727e7277727072697262725c6255724f62487241723b6234722d7226722062197212720b720471fd71f761f071e971e271db71d561ce71c771c071b971b271ab71a5619e71977191618a7183717c7175716f61687161715a7153714c7145713f613871317
|6,1=>0x49b7494748d7486747f74787471746a7463745c7455744e7447744074397432742b7424741d7416740f7408740173fa73f373ec73e573df63d873d263cb73c473bd73b673af73a873a2639b7395638e7387738073797372736b7364735d7356734f73487341733a7333732d6326731f73187311730a730372fc72f572ee72e77
|6,2=>0x609660275fb75f475ed75e675df75d875d175ca75c375bc75b575ae75a775a075997592758b7585657e7577757075697562755b7554754e6547754075397533652c7525751e75177511650b650474fd74f674ef74e874e174da74d374cc74c574be74b774b074a974a27
|7,0=>0x7ea87e377dd67d677cf77c877c177b987b187a987a2779b7793878c7785777d8775876d8766775f775877508748874087397731872a7723771b8713870b870386fb86f386eb86e386db86d386cb86c386bb86b476ad76a5869d8695868e768866808678867176698661865a7652864a8643763b8633862c7624861d7616760f7
|7,1=>0x9c579be79b869b089a889a179998992798b7984797c8975796d8965895e7957795079497942793b7934792c8925791d8916790e890688ff78f788f078e978e188d988d278ca88c378bb88b478ac88a5789d8895888e7887787f8877886f8867886168598851884a7843783b8833882c7825781e7816880f7808780177fa77f28
|7,2=>0x9e289da89d379cc7
|8,0=>0xac88ac08ab97ab27aab7aa38a9b8a947a8d7a867a7f7a778a6f8a678a607a597a527a4b7a438a3c7a348a2c8a248a1c8a157a0e7a0689ff79f879f179ea7
|9,0=>0xaf36aec7ae57ade7ad77ad07
|10,0=>0xaf96
|_,_=>0
def wAt:=mkWire dB 151 223 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x70601401000541094010a404010a004242107060482900054b81805004240101054c84b0131414010100448bd2e0601401011d448191106048250500448150a0041c180500424710a0046c180a0141401090044418050044871010646c180a0141401070604801000542815070601401010841c18120040015120544418000541c180a00400150a0542421070600015
|1=>0x5449110500404010a064140112004283a0906414014a05c441511004644b2505404011b15830150a00424191200448150500520030a16404154700d1815250a4441a0500498340905448251200404150a06848190a0040015121c46c180500424710a0046c180500428010103848190500424560a06448010500424fa0a3d41401090642875110604825050042421
|2=>0x12054140112264384b260056803040d428151512c28190500428010104828150500424662505494251106414011253498370905448010100454270a06414010a004041505004240e120641401094f425460106814014712c10950100444190500448151509c28190500448151200428190500400150905404011219858010105425352625824150100428151b0600429
|3=>0xd05448014d05498960905404014900c3c251205424f50500404510900424150500550171106414015401c38490906498014900c98490706814011b05428051214424010905414010e0ac50150126824010905414011215830150a00438071405424010005430050a05428015a01c303d0a0056803151242819050041c150a12400151232804c5090681401090684801
|4=>0x1912c9415010041c01120a414015605cb80101094503c0900448150500448d50e12c98010905429521106414010400428155412c44190500448150906414011600404150155864272505404010a0e898010905448010706028490500428f612068140101064241905005880116094256a1512428196109c98950905404010a0040419000556827040d428155a01c0c29
|5=>0x1106048250500498010905428361200448150500428bd2e060042505004481a256f410970a0540401093d8481a05004243e1205448010005424151106024490500448661600404156b004441b0912414010a3d428f61206814011206824150a0046c180a01414011219804190a05414014705c10950a05404010915810010a0540c070d055502b110644825050042805
|6=>0x500424950905404014800c285901054b81509014b83a0906414011231848c5090681401120940c070d054480101068486601064140112198041905005680307064140109054240101068140109228283a2600424151219804190500498490905448015b00c10490a0540512150ac30150a004b8010901414010a3f85427040042815141642401120e89801090542875
|7=>0x93d4481a05004441a12094140101064140109054240112618b8190500448190706028490500449120a0684819050056c030f0a448155605c50050900404151b06028050500448c50906814017800410370a0544912150ac10010a0556c0304124281509514241a010681401760041c1b120a400156805c30490a004281905004041a0500430490a054280101314241a
|8=>0x6200c245901054241905004285901004041505004283a09064244905004256a1512410010a05424350905448016805c30490a00568030c05428013212c04c5090681401090044418091241401015483849260046c011b05428050005424560a01430150a004140101264241509004241a0a06854270a06414010a06814010a514041a050040451090042415050042902
|9=>0x1205448010425c28150100448120a0541401010642405050056807151243015091640415010040015090f448011205414014900c3c011205448990900424150500568270c0f448156805c30150a004281a5605c50150900520030401428150a0e824492600424150103848190a12414011912c94150100428191b06028050500454270a12430150a0058803260042415
|10=>0x106814011912c5801010549415010a404010a84494170100448290d05448012e060240505004503e1205430050a05428011412c24150900404010105414010a06814015b00c3c29120560015250ac040109014501509005a0170a0d448011b06c04290500528170d09448014605494290100424010901414010a0e824190500428350a0544801120944815050043429
|11=>0xa068480100054041a0906814010e12c50150900404011b05c28051100c4825120541401250ac04010d0a434151200458011609404152e064140109054040100054281a0500410050a004281509004042501054281a0500410950a054040112444281a0500428011206414010106814010a004481a050046c1a010a41401010642815050049897090543827260042415
|12=>0x500454270400428151b06404290500404520900424158a004984b0905425450106814010106424190500428950100400150c1682801010540c070d05448010a0041c170a124984b0905424010915810010a0544899090042415090d448151200438072600424155b00c1c150a1240419010a414011901c58010105428661600404150c0f02801120546c03010a40415
|13=>0x30a434151200424590105404010919804190500428490d05c4801250549425010041c1a0500424010906814011b00404290500434250d054480104014281505004b815090140015010046c150a014283a2600424151501c2819050043849090641401040142815050046c18010a414010425428150100424191200400150301c3c0112054289601054040101318241a
|14=>0x5004342b1200400151509c30150a00424050905404012600c244909054481a1200400150a19858010105444150912424010a00448150500410490a0544801090145015090044415110044825150ac30150a00524030f09448150912424190500448010f0a4481592004b817090158803260142415190ac94150100428490f00c48150e01498010905428010a0681401
|15=>0x1200414010a00448291205424490905498070905424c50906814010106804190500405110a06814010e09c98010905429450106814010a0e824190500414010905424011200498490905425450106814010301c48190500454270a064140109314241a0500424f5120681401010680419050046c1b010a4384b2600424150a0041c150a12404250106414010c12c2801
|16=>0x9054041509014140112004241905004281a05004241a0500430150a0049801090543c2912054285901054040101054281a050044815050045803010546c010a01424490500450050900428150a0045049090046c170a01404010901428010105424010500448190500434151200430150a004481a050043429120049427010042815
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x1c60000052000000e600000218004
|5,0=>0x2a980000000145000004d4092800002318415000000000000000000000001f1800000000f441d1835506280b8c1520255042800000000000000000000e28000000000000000000032605140898000
|6,0=>0x22e8450c88990f22186421082990231fc83e907b980001ea43c507718eb31d0639887210e041bc436906b98d431a08334c64a0c6318482f905d98b8300002d4c58a0ae315842a105220a1313c626904b9895212282350451887310681fd03e907a30ec81ccc00007030da61a5033186330c2417502d90583
|6,1=>0x38e47184e121bf337860000dc99b7236866c10d621a840000694cd1199e400006690cb9994332266350c5198643084604c00017d42f645dd0b9a00002e420000b7216b32ce80000b1a16032b885610ab1152429c85290a39945228284f509d1800026e64cd097a12c3254449cc92192220000479000011b3
|6,2=>0x4e469b9135226734c68980d2e9a5c14b26958d29224e4496691d121a240347a68ec91ba233445e88b0d149800044c688910f221b342e884d107a20e141488209029a0143fa87e8cfb21f333de87ad0f419e533c28778ced99d743a867410e621c93
|7,0=>0x6546c9cd921b21363c6c6cd8c1b1536246c3cd861b09360c6c0cd801afd35f46bdcd7a1af135dc6bacd741ae625c66b8496f1adb35b24b58d699ad0359c4b2cd641ac535864b00d5f12bb35706ad4d591aaf355a4aa8d539aa435444a7cd4e1a99352c6a4cd481a8d35146a1cd421a8134fc69ecd3c1a753
|7,1=>0x7d06f94df11bdf37b86f64deb1bd337a06f34de593c8378a6f08ddf9bbc37726ed8dd99bb0375a6ea8dd39ba437426e78dcd9b98372a6e48dc79b8c37126e18dc19b8036fa6de8dbb9b7436e26dbc9b61b6936cc6d8cdb01b5d36b46d5cdaa1b51369c6d2cda41b4536846cfcd9e1b39366c6cccd981b2d3
|7,2=>0x7e86fc4df71beb3
|8,0=>0x10cca18942f285a50aca149427284a508ca10941f283a506ca0c9417282a504ca08940f281a502ca049407280a500ca0093ff27fa4fec9fc93f72
|9,0=>0x439187030dc61b0c351
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x18000022c0004480008800010e0002100004100008100010000012800024800048000088000108000200000230000400000600000b80000e0000180000280000480000800000e0000180000280000400000600000800000800000
|1=>0x651200c83c0180400220800423e008418010810020080040000063380084000088000100000151800204000287000508000724000a50001400002480004300008480010800020c00041000081800102000202000400000650000c8
|2=>0x939e0125600220800440000879e010800020f78041df00839e010734020e58041880082fe010520020a0004129008202010400020670040c800811e010224020440040830081000101240202000402000802001002402000804000
|3=>0x283be05073c0a0af01404a022010042528082040101020200800400200686780c9ce01919c03073c060000090c801001c020020039e78063cf00c39e0184bc0308f8052cf00a39e014230026ef804dcf009abc013560026a8004c58
|4=>0x98190118f3c230478451cf08a39a114724228c60450ce08a108114034224000441cf088318108818210478411880822081043302084684108c08200a1001102000002000203a39e0742200c8270149cf0293960527240a4ab0145cf
|5=>0x18851e310a24621048c420710c39e21843c4308508610310c096218104429e788508f1085122107fc420e788413f1082702104d84209888412f10809620822c4104488204110401620800c2646704c8c8099180132120260e784c0cf
|6=>0x2000022040c930839e6000988a2e7914508220a904187bc8309790602920929c411538820ef9041dd2083b241073c820c810410c2042524080bc802a41001982003204005708008e10011920011040010080002900000
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x200040004000202
|5,0=>0x400000100281400020b0000000000000200000f0e153004170a320000000000150000000000020a0400
|6,0=>0x1289d7113d004340051947a80004114a008f04955c413cc3011300dc01811d00c00006713600a01a1c13404f4e231177244e79003d4d191701178a2200470088515c1b010818391123189500023f17081712408535911305ca11145d544c171100c23b011a1f09da3405221745c69226185304c1141700dd058e44011a9f4078
|6,1=>0x4bea417a422113701441423172a1f015a03ae2c1f7b3100111c75044218bc33c7a6173e466eaa0116244338290111145c8b1476
|7,0=>0x579a9ca38d82c89957b7085760aad37dcf9ea17c57a2d3619c49c5578e635bb3296407cc27bfa9801e1166d521adbdaf55c46fb0593a8e82ba57cd57b494571bcbb156d298cfa586055ebbab2557ac5218206a73692d48079d11b0b5100d7a7a2b5250b801972fb6b96b844b17d498bb03626b96c959700c6890d774d8587dbb
|7,1=>0x8ca75793
|8,0=>0x9b5657d19c65b2bb575fb1d6726dd187596cdb678383d055d96b7fce64a194
|9,0=>0x2e94b15b577e
|10,0=>0x57
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_220 8 roots_220 ops++addP pm 1 dom_212 7 roots_212 ops++addP pm 2 dom_202 7 roots_202 ops++addP pm 3 dom_158 8 roots_158 ops++addP pm 4 dom_142 5 roots_142 ops++addP pm 5 dom_204 5 roots_204 ops++addP pm 6 dom_214 8 roots_214 ops++addP pm 7 dom_218 8 roots_218 ops++addP pm 8 dom_206 8 roots_206 ops++addP pm 9 dom_216 5 roots_216 ops++addP pm 10 dom_198 5 roots_198 ops++addP pm 11 dom_150 5 roots_150 ops++addP pm 12 dom_90 5 roots_90 ops++addP pm 13 dom_92 5 roots_92 ops++addP pm 14 dom_94 8 roots_94 ops++addP pm 15 dom_210 5 roots_210 ops++addP pm 16 dom_86 5 roots_86 ops++addP pm 17 dom_200 4 roots_200 ops++addP pm 18 dom_154 5 roots_154 ops++addP pm 19 dom_156 5 roots_156 ops++addP pm 20 dom_78 5 roots_78 ops++addP pm 21 dom_194 4 roots_194 ops++addP pm 22 dom_196 4 roots_196 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_222 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_196 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_220 8 s (0,roots_220.map (·&&&dom_220)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_222 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_220 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffffffffffffffff0000000000000000,64),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_222==dom_222)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_222 gM v ys):RunD true dom_222 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_222 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 45 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 181 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 53 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 181 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 132 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 132 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 31 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 31 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 6 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_222 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_222 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_222 roots_222 goal_222 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_222
theorem lowS_222:Lower true dom_222 roots_222 goal_222 11:=S_222.noCircuit
theorem lowS_231:Lower true dom_231 roots_231 goal_231 8:=lower_slice_b [(0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc,32,34)] (by decide +kernel) lowS_229
namespace S_235
def pG:List (Nat×Nat):=[(1,9),(1,33),(2,10),(2,34),(2,66),(2,130),(3,11),(3,35),(3,67),(3,131),(8,9),(8,10),(8,40),(8,72),(8,136),(32,33),(32,34),(32,40),(64,66),(64,72),(64,192),(65,67),(65,73),(65,97),(65,193),(96,97),(96,98),(96,104),(96,224),(128,130),(128,136),(128,192),(129,131),(129,137),(129,161),(129,193),(160,161),(160,162),(160,168),(160,224)]
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
|6,0=>0xd87e5
|7,0=>0x9b3c568854552f83fd043891e
|8,0=>0xafa9a2ff10
|9,0=>0xfffda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000f0f000000000000000000000f0000000f00f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f00f0f00000f0f000000000000000000000f0f00000f0f0000000000000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f00f0f00000f0f00000f0f00000f0f00000000000000000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0f00000f0f00000f0000000f0000000f0f00000f0f00000f0000000f00f0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0ca0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0af0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x5721865721086537218654721065937218657a218654321865972186543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x2376e14735c67
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
|0=>0x219765a1784e1764e3765e1764e176619785d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfff32ff3f7fafc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x5c9f
|8,0=>0x22
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_234 8 roots_234 ops++addP pm 1 dom_233 8 roots_233 ops++addP pm 2 dom_227 7 roots_227 ops++addP pm 3 dom_171 7 roots_171 ops++addP pm 4 dom_107 7 roots_107 ops++addP pm 5 dom_203 8 roots_203 ops++addP pm 6 dom_163 4 roots_163 ops++addP pm 7 dom_99 4 roots_99 ops++addP pm 8 dom_43 5 roots_43 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_235 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_43 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_234 8 s (0,roots_234.map (·&&&dom_234)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_235 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_234 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)]]
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
def dzo_194_1:=0xa000000000000000a000000000000000a000000000000000a
def gzo_194_1:=0xa000000000000000800000000000000080000000000000000
def gsh_194_1:=0x5000000000000000400000000000000040000000000000000
theorem lowS_zo_194_1_194:Lower true dzo_194_1 roots_194 gzo_194_1 4:=lower_iso_b (d1:=dom_194) (r1:=roots_194) (T1:=gsh_194_1) [(dom_194,1)] (by decide +kernel) (lower_slice_b (T:=gsh_194_1) [] (by decide +kernel) lowS_194)
def dzo_211_32:=0xf000f00000000000f000f00000000000f000f00000000000f000f00000000
def gzo_211_32:=0xf000f00000000000f000e00000000000f000e00000000000e000e00000000
def gsh_211_32:=0xf000f00000000000f000e00000000000f000e00000000000e000e
theorem lowS_zo_211_32_208:Lower true dzo_211_32 roots_211 gzo_211_32 6:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_32) [(dom_211,32)] (by decide +kernel) (lower_slice_b (T:=gsh_211_32) [(0xa000a00000000000a000a00000000000a000a00000000000a000a,0,1),(0xc000c00000000000c000c00000000000c000c00000000000c000c,0,2)] (by decide +kernel) lowS_208)
def dzo_209_32:=0x3000300000000000300030000000000030003000000000003000300000000
def gzo_209_32:=0x3000300000000000300020000000000030002000000000002000200000000
def gsh_209_32:=0x30003000000000003000200000000000300020000000000020002
theorem lowS_zo_209_32_208:Lower true dzo_209_32 roots_209 gzo_209_32 5:=lower_iso_b (d1:=dom_209) (r1:=roots_209) (T1:=gsh_209_32) [(dom_209,32)] (by decide +kernel) (lower_slice_b (T:=gsh_209_32) [(0x20002000000000002000200000000000200020000000000020002,0,1)] (by decide +kernel) lowS_208)
def dzo_242_1:=0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a
def gzo_242_1:=0xa000a000a000a000a000a000a0008000a000a000a0008000a000a000a0000
def gsh_242_1:=0x5000500050005000500050005000400050005000500040005000500050000
theorem lowS_zo_242_1_194:Lower true dzo_242_1 roots_242 gzo_242_1 6:=lower_iso_b (d1:=dom_242) (r1:=roots_242) (T1:=gsh_242_1) [(dom_242,1)] (by decide +kernel) (lower_slice_b (T:=gsh_242_1) [(0x5000000050000000500000005000000050000000500000005000000050000,0,16),(0x5000500000000000500050000000000050005000000000005000500000000,0,32)] (by decide +kernel) lowS_194)
def dzo_226_1:=0xa0000000a0000000a0000000a0000000a0000000a0000000a0000000a
def gzo_226_1:=0xa0000000a0000000a000000080000000a000000080000000a00000000
def gsh_226_1:=0x500000005000000050000000400000005000000040000000500000000
theorem lowS_zo_226_1_194:Lower true dzo_226_1 roots_226 gzo_226_1 5:=lower_iso_b (d1:=dom_226) (r1:=roots_226) (T1:=gsh_226_1) [(dom_226,1)] (by decide +kernel) (lower_slice_b (T:=gsh_226_1) [(0x500000000000000050000000000000005000000000000000500000000,0,32)] (by decide +kernel) lowS_194)
def dzo_210_1:=0xa000a00000000000a000a00000000000a000a00000000000a000a
def gzo_210_1:=0xa000a00000000000a000800000000000a000800000000000a0000
def gsh_210_1:=0x50005000000000005000400000000000500040000000000050000
theorem lowS_zo_210_1_194:Lower true dzo_210_1 roots_210 gzo_210_1 5:=lower_iso_b (d1:=dom_210) (r1:=roots_210) (T1:=gsh_210_1) [(dom_210,1)] (by decide +kernel) (lower_slice_b (T:=gsh_210_1) [(0x50000000000000005000000000000000500000000000000050000,0,16)] (by decide +kernel) lowS_194)
namespace S_243
def pG:List (Nat×Nat):=[(1,17),(1,33),(2,34),(2,66),(2,130),(3,19),(3,35),(3,67),(3,131),(16,17),(16,80),(16,144),(18,19),(18,50),(18,82),(18,146),(32,33),(32,34),(48,49),(48,50),(48,112),(48,176),(64,66),(64,80),(64,192),(65,67),(65,81),(65,97),(65,193),(96,97),(96,98),(96,112),(96,224),(128,130),(128,144),(128,192),(129,131),(129,145),(129,161),(129,193),(160,161),(160,162),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_243.map (·&&&dom_243)
def gM:=goal_243&&&dom_243
def NN:Nat→Nat
|4=>2
|5=>15
|6=>56
|7=>31
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x2a9da172df
|5,0=>0x900bf86df26558755af64c78d3a6cc3a441379d329bc01caad19fe1141e40872206c03027ea
|6,0=>0xe9458d2292c4d94c05d0ace26900bf8ebdf8b9978676c8541182f407e8187ab2e7686874c316f9736c8396a9356503364b40648085bab8587f858477559355524354b72448f5412ae3ad6f3a6d532142310232d8142d64a2b3422962d28e5b28cef2878b283ad2752526a8b250e219f1b146c2115af109fd107ed0ef940c0650786506f200668d05b90058e8
|7,0=>0xd3d8fcf667a2489917fd8811d84d777f8976b0de62f6c5dcc45c8c95b1795ab3843ad537d4736c0f35c4f2e2d516fd01634c1503111c2410b08100220ffd40b55c0599d0360702a060108400966
|8,0=>0xc8a367a9f6762ce655b01972117c56127920fc84
|9,0=>0x7a9f6
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000c000f000c0000000000000000000f000c000f000cf000f000f000f000f000c000f000c00000000000000000000000000000000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c0000f0000000f0000000f0000000f0000000c0000000c0000000c0000000cf0000000f0000000f0000000f0000000f0000000f0000000f0000000f00003000300030003000300030003000300030003000300030003000300030000f000f000f000f0000000000000000000f000f000f000f0000000000000000f000f000f000f000f000f000f000f00000000000000000000000000000000f000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000f000f000f000f000c000c000c000c000f000f000f000f000c000c000c000cf000c000f000c000f000c000f000c000f000c000f000c0000000000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000f000c000f000c000f000c000f000c000f000c000f000c000f000c000f000cf000f000f000f000f0000000f0000000c000c000c000c000c0000000c0000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000af000f000f000f000f000f000f000f000f000f000f000f0000000000000000
|0,1=>0xf000f000f000f000f000f000f000f000f000f000f000f000c000c000c000cf000f0000000f000f000f0000000f000f000f0000000f000f000f00000000f000f000f000f000f000f000f000f00030003000300030003000000030000000000000000000000000000000000000000000000000000f000c000f000c00000000000000000000000000000000f000f000f000f000f000c000f000cf000e000f000e000f000e000f000e000f000e000f000e000a000a000a000af000f000f000f000f000f000f000f000f000c000f000c000f000c000f000cf000f000f000f000c000c000c000c000f0000000f0000000c0000000c00003000300000003000300030000000300030003000000030003000300000000000020000000200000002000000020000000200000002000a000a000a000ac000c0000000c000c000c0000000c000c000c0000000c000c000c00000000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c0000a000a000a0000000a000a000a0000000a000a000a0000000a000a000a00000000f0000000f0000000f0000000f0000000f0000000f0000000000000000f000f000f000f000f0000000f0000000f000f000f000f000f0000000f0000f000f000f000f000f000f000f000f000c000c000c000c000c000c000c000c
|0,2=>0xf000f000f000f0000000000000000000f000c000f000c00000000000000000000f0000000f00000000000000000000000c0000000c30003000300030003000300030003000300030003000300030000000300003000300030003000300030003000300030003000300030002000200020002f000f000f000f0000000000000000000f000c000f000c0000000000000000f000f000f0000000f000f000f0000000f000f000f0000000f000f000f0000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e00000000e000e00000000000e000e00000000000e000e00000000000e000ef000f000f000f000c000c000c000c000a000a000a000a0008000800080008f000f00000000000f000f00000000000f000f000f000f000f000f000f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0000f000f000f000f000f000f000f000f000a000a000a000a000a000a000a000a0000000000000000300030003000300000000000000000002000200020002f0000000f000f000f0000000f000f000f0000000f000f000f0000000f0000f000f000f000f000f000c000f000c000f000f000f000f000f000c000f000c00000000000000000000000000000000f000c000f000c000f000c000f000c
|0,3=>0xc000c000c000c000c000c000c000c000f000f000f000f000e000e000e000ef000f000f000f000f000f000f000f00030003000300030002000200020002f000f000f000f000f000f000f000f000f000f000f000f000f000f00000000c000c000c000c000c000c000c000c000c000c000c000c000c000c00000000f000f000f000f000f000f000f000f000f000f000f000f000a000a000a000af0000000f0000000f0000000f0000000f0000000f0000000a0000000a00003000300030003000300030003000300030000000300000003000000030000f000f000f000f000f000f000f000f000f000f000f000f000f000c000f000c00000000f000f00000000000f000f00000000000f000f00000000000f00000000000000000000f000f000f000f0000000000000000000c000c000c000cf000f000f000f000a000a000a000a000f000f000f000f000a000a000a000a00000000000000000000000000000000f000f000f000f000c000c000c000ca000a000f000f000a000a000f000f000a000a000f000f000a000a000a000af000f000f000f000f000f000f000f0000000000000000000f000c000f000cc000c000c000c000f000f000f000f000c000c000c000c000f000c000f000c0000f0000000f0000000f0000000f0000000f0000000f0000000a0000000a
|0,4=>0xf000f000c000c000f000f000c000c000f000f000c000c000f000f000c000c3000300030003000300000003000000030003000300030003000000030000f000f000a000a000f000f000a000a000f000f000a000a000f000f000a000af000f000f000f000f000f000f0000000f000f000f000f000f000f000f0000f000f000f000f000f000f00000000000f000f000f000f000f000f00000000f000f000f000f000f000f000f000f000f000f000f000f000f0000000f000000000000f000f00000000000f000000000000000f000f00000000000f000000000000000000000000000000000000f000f000f000f000a000a000a000af000a000f000a000f000a000f000a000f000a000f000a000f000a000f000a00003000000030000000300000003000000030000000300000000000000005000500050005000500050005000500050005000500050000000000000000a000a00000000000a000a00000000000a000a00000000000f000f00000000e000e00000000000e000e00000000000e000e00000000000e000e00000000f0003000f0003000f0003000f0003000f0003000f0003000f0000000f000000000000000000000000000000000000f000f000f000f000f000f000f0000f000f000f000f00000000000f000f000f000f000f000f00000000000f0000
|0,5=>0xf000f000f000f000f000f000f000f000f000f00000000000f000f000000000000f0000000f0000000f0000000f0000000f000000000000000f00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x3c1058d0224404163409d122021c1634089101018f2234088086c58d022420b1a68488086488d02002033004488082c097122020b1a58488082ca8112202032240080082ca01122020d2624908082c682020020f163408e081c681121420b0c04600082c08a12202070c042840608080
|1=>0x200404622c681122020d02c048808bc38b1a0440416340ae122020b1a05689101058d02b0488086458d02ac42a0834089242058d02a0009101058d029c4884c1058d0224404404468112212841634089101058d028c488088858d0224404422c80112202200e2c681121018b3e04488
|2=>0x844681722440416340be122020b7804488088478b1a044041a05d00122020b1a05c80121038b1a05588082c6980224404061c301122020b1a044851011c0b1a04488082c6816e244041635b35022020316d0089101058d6624404222c80d020021b1634089101190b1a04488080c586
|3=>0x62c301122020b1a044c510105b41a04488082c6bb0224404426c58d02242191634080121058d022630808340b0002444416340891010d8b1a0448b8634080122021b062c68112105862004004842c681122020b1a0448e080c58d0224741082c681122020b1a0600910105bf1a04488
|4=>0x82cf8d0200488081c5861a04488082c6931222604163408910f420b1a04009112c2071634089101250b1a04488082c68192244041636401122022016340891011091163408910101a0163408910108871a04488082cf861a04488091c5901a04488080c58d0200488081c58d0200484
|5=>0x82c681122020b1a04488080c58d022442a082c68112202471634089101058d4804488081c58d022440416340801220221163408910110831634089101058d034048816340a8122278416340801222604222c681122020b1a04492101058d0338488082d48d02004889a1058d0200488
|6=>0x1058d022444d
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x154005
|5,0=>0x5e61618526131846610183a60d182e60a18226071816604180a6
|6,0=>0x779dd77741dc9770d9bd66d9daf76a59a276719957639d877601d7975c9d6c6595d5e755dd507525d4274edd3474b5d26747dd196449d0b7411cfd73d9cf063a5ce2736dcd47335cc672fdcb872c5caa728dc9c7255c8e721dc8071e5c7271adc647
|7,0=>0x2c37aee2b47ab9aa68a7a2977a41e888a0227889c226a698de5b894e24c7915e3e78dde2f889e2207862210882220177e9df377b1de57
|8,0=>0xbe9ef46bb5ee67b7ded87b45eca7
|9,0=>0x3016
|_,_=>0
def wAt:=mkWire dB 82 244 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1a2112214220062516354220062516351af40801122142270625762c02010e37162132240e350e181a25162106001221163520271a210c231a25062716350e27162132270e351602122152131a0548181a25222306231a2d1221481b1a250625163532230e3516210c211a25060316351a2d06211a2d22401a21162506001a2d
|1=>0x1221223716251a051221122108051a0112211a2516215404161108451625080112210825162116011221084616256a230225062316352235162506231635162516210c211a25022d1a2112211635162112211a251635020212210c231a25020112210625163506211635762f020109170202122108a41a051221422306251a25
|2=>0x80516351611160502211621122106251635062516351746082152131a051a111221084516251602
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x52000000000000000000000023000002000000
|6,0=>0x4d24b20004924630004334123e30003b33830000000000000003533323122f22d22a30002730000002522320000000002120001f20001d20000000000001b21921721611421311120000f20c30a2000000082071
|7,0=>0x8b28928728528328127f27d27b27927727527327126f26d26b26926726526326125f25d25b25925725525325124f2
|8,0=>0x9310009219119018f18e18d1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x27d38012e8c008f4e0043ff0021f38010e9c0042400010230006900003088001840000ba70001f380008980003840001a70000d18000498000248000120000080000038400010e00008000001100000800000300000060000020000008000002000000
|1=>0x18000c28021f3a000760881048440822100071043469c1020460465a7023083011069c08034e0291a70108108054f9c02200600d1a70061f7803059c00ca0c0061a7
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x2000000000004003000
|6,0=>0xc200224060648038700000000a54208b1003800012c00000c01802c000000808314214100364b000082
|7,0=>0x1f5b38afcaa76d97031373446c6ee697361c673ab7a4524
|8,0=>0x98f6a3a24829
|9,0=>0x10
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_242 7 roots_242 ops++addP pm 1 dom_179 7 roots_179 ops++addP pm 2 dom_115 7 roots_115 ops++addP pm 3 dom_194 4 roots_194 ops++addP pm 4 dzo_194_1 4 roots_194 ops++addP pm 5 dom_241 7 roots_241 ops++addP pm 6 dzo_211_32 6 roots_211 ops++addP pm 7 dom_211 7 roots_211 ops++addP pm 8 dom_227 7 roots_227 ops++addP pm 9 dzo_209_32 5 roots_209 ops++addP pm 10 dom_163 4 roots_163 ops++addP pm 11 dom_177 4 roots_177 ops++addP pm 12 dzo_242_1 6 roots_242 ops++addP pm 13 dom_99 4 roots_99 ops++addP pm 14 dzo_226_1 5 roots_226 ops++addP pm 15 dzo_210_1 5 roots_210 ops++addP pm 16 dom_210 5 roots_210 ops++addP pm 17 dom_226 5 roots_226 ops++addP pm 18 dom_51 4 roots_51 ops++addP pm 19 dom_208 4 roots_208 ops++addP pm 20 dom_178 4 roots_178 ops++addP pm 21 dom_209 5 roots_209 ops++addP pm 22 dom_113 4 roots_113 ops++addP pm 23 dom_147 4 roots_147 ops++addP pm 24 dom_83 4 roots_83 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_243 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_194_1_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_211_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_209_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_242_1_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_226_1_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_210_1_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_83 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_242 7 s (0,roots_242.map (·&&&dom_242)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_243 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_242 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffffffffffffffff0000000000000000,64),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_243==dom_243)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_243 gM v ys):RunD true dom_243 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_243 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 56 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 56 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 31 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 31 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
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
theorem lowS_245:Lower true dom_245 roots_245 goal_245 9:=lower_slice_b [(0x22002200220022002200220022002200220022002200220022002200220022,16,17)] (by decide +kernel) lowS_244
def dzo_208_32:=0x1000100000000000100010000000000010001000000000001000100000000
def gzo_208_32:=0x1000100000000000100000000000000010000000000000000000000000000
def gsh_208_32:=0x10001000000000001000000000000000100000000000000000000
theorem lowS_zo_208_32_208:Lower true dzo_208_32 roots_208 gzo_208_32 4:=lower_iso_b (d1:=dom_208) (r1:=roots_208) (T1:=gsh_208_32) [(dom_208,32)] (by decide +kernel) (lower_slice_b (T:=gsh_208_32) [] (by decide +kernel) lowS_208)
def dzo_170_16:=0x50500000505000000000000000000000505000005050000
def gzo_170_16:=0x50500000505000000000000000000000504000004000000
def gsh_170_16:=0x5050000050500000000000000000000050400000400
theorem lowS_zo_170_16_42:Lower true dzo_170_16 roots_170 gzo_170_16 5:=lower_iso_b (d1:=dom_170) (r1:=roots_170) (T1:=gsh_170_16) [(dom_170,16)] (by decide +kernel) (lower_slice_b (T:=gsh_170_16) [(0x5050000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_216_32:=0x101010100000000010101010000000001010101000000000101010100000000
def gzo_216_32:=0x101010100000000010101000000000001010100000000000100010000000000
def gsh_216_32:=0x1010101000000000101010000000000010101000000000001000100
theorem lowS_zo_216_32_208:Lower true dzo_216_32 roots_216 gzo_216_32 5:=lower_iso_b (d1:=dom_216) (r1:=roots_216) (T1:=gsh_216_32) [(dom_216,32)] (by decide +kernel) (lower_slice_b (T:=gsh_216_32) [(0x1000100000000000100010000000000010001000000000001000100,0,8)] (by decide +kernel) lowS_208)
def dzo_234_16:=0x505000005050000050500000505000005050000050500000505000005050000
def gzo_234_16:=0x505000005050000050500000505000005050000050500000504000004000000
def gsh_234_16:=0x50500000505000005050000050500000505000005050000050400000400
theorem lowS_zo_234_16_42:Lower true dzo_234_16 roots_234 gzo_234_16 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_16) [(dom_234,16)] (by decide +kernel) (lower_slice_b (T:=gsh_234_16) [(0x50500000505000000000000000000000505000005050000000000000000,0,64),(0x50500000505000005050000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_218_32:=0x505050500000000050505050000000005050505000000000505050500000000
def gzo_218_32:=0x505050500000000050505040000000005050504000000000504050400000000
def gsh_218_32:=0x5050505000000000505050400000000050505040000000005040504
theorem lowS_zo_218_32_208:Lower true dzo_218_32 roots_218 gzo_218_32 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_32) [(dom_218,32)] (by decide +kernel) (lower_slice_b (T:=gsh_218_32) [(0x4040404000000000404040400000000040404040000000004040404,0,2),(0x5000500000000000500050000000000050005000000000005000500,0,8)] (by decide +kernel) lowS_208)
def dzo_210_32:=0x5000500000000000500050000000000050005000000000005000500000000
def gzo_210_32:=0x5000500000000000500040000000000050004000000000004000400000000
def gsh_210_32:=0x50005000000000005000400000000000500040000000000040004
theorem lowS_zo_210_32_208:Lower true dzo_210_32 roots_210 gzo_210_32 5:=lower_iso_b (d1:=dom_210) (r1:=roots_210) (T1:=gsh_210_32) [(dom_210,32)] (by decide +kernel) (lower_slice_b (T:=gsh_210_32) [(0x40004000000000004000400000000000400040000000000040004,0,2)] (by decide +kernel) lowS_208)
namespace S_250
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(2,130),(8,10),(8,40),(8,72),(8,136),(16,80),(16,144),(18,26),(18,50),(18,82),(18,146),(24,26),(24,56),(24,88),(24,152),(32,34),(32,40),(48,50),(48,56),(48,112),(48,176),(64,66),(64,72),(64,80),(64,192),(96,98),(96,104),(96,112),(96,224),(128,130),(128,136),(128,144),(128,192),(160,162),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_250.map (·&&&dom_250)
def gM:=goal_250&&&dom_250
def NN:Nat→Nat
|4=>3
|5=>12
|6=>20
|7=>13
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xdef05cc51fbebc4
|5,0=>0xd64afd08798b71385b7a8260f2bb5824daa1fcf9140640f8e3029440137f
|6,0=>0x909948fa6d8ab9b8a95284fef66d47529a92b1aa2a73329d4f28f3c1f4911c99a1515f133bf090ab031e40305d01dcc014a0
|7,0=>0x8eef57c50f6a28949383364da34c592db352224f1302e1104e0a1a70a02c0818a
|8,0=>0x9d41537a3b22d09
|9,0=>0xef2e1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa0a0a080a0a0a080a0a0a080a0a0a080a0a0a080a0a0a080a0a0a080a0a0a0941414141414141414141414141414141410141014101410141014101410141282828282828282828002800280028002828282828282828280028002800280505050505050505040404040404040405000500050005000400040004000400a080a080a080a080a080a080a080a080a080a080a080a080a080a080a080a0941414141414141414141414141414141414141414141414000000000000000282828280000000028282828000000002828282800000000282828280000000505000005050000050500000505000005050000050500000505000005050000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000a000a000a000a000a000a000a014141414141414141010101010101010141414141414141410101010101010128282828282828282800280028002800202020202020202020002000200020050005000500050005000500050005000500050005000500050005000500050080808080808080808080808080808080808080808080808080808080808080800014141410141400001414141014140000141414101414000000001410141282828282828282800000000000000002828282828282828000000000000000505050505050505050505050505050500000000000000000000000000000000
|0,1=>0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000a000a000a01414141414141414141414141414141414141414000000001414141400000000028002800280028002800280028002800280028002800280020002000200020000000000000000505050505050505000000000000000005000500050005008080808080808080a0a0a0a0a0a0a0a08080808080808080a080a080a080a0840404040404040404000400040004000404040404040404040004000400040080808080808080808080808080808080800080008000800080008000800080500050505000505050005050500050505000505050005050500050005000500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0808080808080808080808080808080800000001410141000000000141014100000000014101410000000001410141000028280000282800002828000028280000282800002828000000000000000505050505050505050505050505050505050505050505050000000005040504a0a0a0a0a0a0a0a000000000a080a080a0a0a0a0a0a0a0a000000000a080a0941414141414141414141414141414141414141414141414101010101010101000000000000000028282828282828280000000000000000000000002820282005000500050005000500050005000500040004000400040004000400040004
|0,2=>0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0000000000000000000000014141414141414140000000000000000141414140000000282828282828282828282828000000002828282828282828282828280000000101010001010100010101000101010001010100010101000101010001010100a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a080a080a080a0941414141414141414101410141014101414141414141414141014101410141000000000000000000000000000000000808080808080808080008000800080505050005050500050505000505050005050500050505000505050005050500
|_,_=>0
def sP:Nat→Nat
|0=>0x402486c40c10092040da2802483436410096040c100920e34304024f1060402483471972482c718a2481061401035815402040d40402040d32802482c74812040d104024810640a24f34600920e34600920b30100920b14a2481c61440c2040
|1=>0x1030407883440c100920710328198810304024810368102520d1030091c390100920b10628024810314100920d1c60c02040d62810092071060ca2488c40c100982234304024810384101e8070c12482df0c100920d1c329e2041970492040dd
|2=>0x2481030402481060c100920b1030407881030402482c40ca0402481c41830402487c40c100921f1c40c10258040c100920d1c30402040d60409c8
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x283129888c3e61c30c9858c26610306d42ac0f6
|6,0=>0x6ab339d8eec075cbac9d56ea474eba61522e8b642b1f9ceee70734b98d8b8e566
|7,0=>0x12c8924475e2b10f6843c099f8cf57773ba19c2edb6
|8,0=>0x505e74f346
|9,0=>0x1486
|_,_=>0
def wAt:=mkWire dB 40 251 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1431135704050c0492e0c441010404b2904043113434111204481110049012844311040440500144010c143012405213180430570347071004101343c1111c3c011544482a0405711003482d0c4410d00143115cd03011014a0d1034101001440520b4311043402d0c4461c0434011
|1=>0xc1431124041010c444010c14d01101470510048112414401101492e0c45e05240440524040051005e072404d0f0444405241600f0044811
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x408698000000005180012215019003
|6,0=>0x806f89d9800706dc5a1b13000b8d59a834a688cf99c33445cca9123
|7,0=>0x5b2b255caa9532a253ca694b29251ca29432
|8,0=>0x17c6f0dd1
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x5843f824615c0850e603983d01843f80c217c0230ae0048ee002429000b1fc0050e600101100062f80021fc0010ae00083e00040400011300008500003fe0001f800001a4000090000028000012000008800004200001800000a0000038000010000000
|1=>0x80042bb24217d1295fe44287722101991021cc8010be3f48ff
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xd0c000018004b102
|6,0=>0x60d48850828e0201d570524f11710c
|7,0=>0x164248e589979f75b866
|8,0=>0x274da
|9,0=>0x11
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_234 8 roots_234 ops++addP pm 1 dom_242 7 roots_242 ops++addP pm 2 dom_248 7 roots_248 ops++addP pm 3 dzo_208_32 4 roots_208 ops++addP pm 4 dom_186 7 roots_186 ops++addP pm 5 dzo_42_16 4 roots_42 ops++addP pm 6 dom_218 8 roots_218 ops++addP pm 7 dom_226 5 roots_226 ops++addP pm 8 dom_232 5 roots_232 ops++addP pm 9 dzo_170_16 5 roots_170 ops++addP pm 10 dom_208 4 roots_208 ops++addP pm 11 dom_122 7 roots_122 ops++addP pm 12 dzo_216_32 5 roots_216 ops++addP pm 13 dom_42 4 roots_42 ops++addP pm 14 dzo_234_16 6 roots_234 ops++addP pm 15 dom_120 4 roots_120 ops++addP pm 16 dzo_218_32 6 roots_218 ops++addP pm 17 dom_90 5 roots_90 ops++addP pm 18 dom_114 4 roots_114 ops++addP pm 19 dzo_210_32 5 roots_210 ops++addP pm 20 dzo_106_16 5 roots_106 ops++addP pm 21 dom_202 7 roots_202 ops++addP pm 22 dom_178 4 roots_178 ops++addP pm 23 dom_154 5 roots_154 ops++addP pm 24 dom_184 4 roots_184 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_250 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_208_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_42_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_170_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_216_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_234_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_218_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_210_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_106_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_184 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_234 8 s (0,roots_234.map (·&&&dom_234)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_250 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_234 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccccccccccccccccccc,126)],[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccccccccccccccccccc,126)],[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_250==dom_250)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_250 gM v ys):RunD true dom_250 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_250 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 20 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 20 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 13 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 13 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
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
def isoMvS_175:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_175:Lower true dom_175 roots_175 goal_175 8:=lower_iso_b isoMvS_175 (by decide +kernel) lowS_111
def isoMvS_183:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 9:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_119
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 10:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_123
def isoMvS_189:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 9:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_125
def isoMvS_215:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_207
def isoMvS_221:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 9:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_219
def isoMvS_237:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 9:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_126
def isoMvS_246:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_219
def isoMvS_249:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 9:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_126
def isoMvS_252:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_219
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,16,20)] (by decide +kernel) lowS_123
theorem lowS_223:Lower true dom_223 roots_223 goal_223 12:=lower_slice_b [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,8,9)] (by decide +kernel) lowS_222
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,32,36)] (by decide +kernel) lowS_235
def dzo_198_1:=0xaa00000000000000aa00000000000000aa00000000000000aa
def gzo_198_1:=0xaa00000000000000a800000000000000a80000000000000000
def gsh_198_1:=0x55000000000000005400000000000000540000000000000000
theorem lowS_zo_198_1_198:Lower true dzo_198_1 roots_198 gzo_198_1 5:=lower_iso_b (d1:=dom_198) (r1:=roots_198) (T1:=gsh_198_1) [(dom_198,1)] (by decide +kernel) (lower_slice_b (T:=gsh_198_1) [] (by decide +kernel) lowS_198)
def dzo_230_1:=0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa
def gzo_230_1:=0xaa000000aa000000aa000000a8000000aa000000a8000000aa00000000
def gsh_230_1:=0x5500000055000000550000005400000055000000540000005500000000
theorem lowS_zo_230_1_198:Lower true dzo_230_1 roots_230 gzo_230_1 6:=lower_iso_b (d1:=dom_230) (r1:=roots_230) (T1:=gsh_230_1) [(dom_230,1)] (by decide +kernel) (lower_slice_b (T:=gsh_230_1) [(0x5500000000000000550000000000000055000000000000005500000000,0,32)] (by decide +kernel) lowS_198)
def dzo_246_1:=0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa
def gzo_246_1:=0xaa00aa00aa00aa00aa00aa00aa00a800aa00aa00aa00a800aa00aa00aa0000
def gsh_246_1:=0x55005500550055005500550055005400550055005500540055005500550000
theorem lowS_zo_246_1_198:Lower true dzo_246_1 roots_246 gzo_246_1 7:=lower_iso_b (d1:=dom_246) (r1:=roots_246) (T1:=gsh_246_1) [(dom_246,1)] (by decide +kernel) (lower_slice_b (T:=gsh_246_1) [(0x55000000550000005500000055000000550000005500000055000000550000,0,16),(0x55005500000000005500550000000000550055000000000055005500000000,0,32)] (by decide +kernel) lowS_198)
def dzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
def gzo_215_32:=0xff00ff0000000000ff00fe0000000000ff00fe0000000000fe00fe00000000
def gsh_215_32:=0xff00ff0000000000ff00fe0000000000ff00fe0000000000fe00fe
theorem lowS_zo_215_32_208:Lower true dzo_215_32 roots_215 gzo_215_32 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_32) [(dom_215,32)] (by decide +kernel) (lower_slice_b (T:=gsh_215_32) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,0,2),(0xf000f00000000000f000f00000000000f000f00000000000f000f0,0,4)] (by decide +kernel) lowS_208)
def dzo_214_32:=0x55005500000000005500550000000000550055000000000055005500000000
def gzo_214_32:=0x55005500000000005500540000000000550054000000000054005400000000
def gsh_214_32:=0x550055000000000055005400000000005500540000000000540054
theorem lowS_zo_214_32_208:Lower true dzo_214_32 roots_214 gzo_214_32 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_32) [(dom_214,32)] (by decide +kernel) (lower_slice_b (T:=gsh_214_32) [(0x440044000000000044004400000000004400440000000000440044,0,2),(0x500050000000000050005000000000005000500000000000500050,0,4)] (by decide +kernel) lowS_208)
def dzo_214_1:=0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa
def gzo_214_1:=0xaa00aa0000000000aa00a80000000000aa00a80000000000aa0000
def gsh_214_1:=0x550055000000000055005400000000005500540000000000550000
theorem lowS_zo_214_1_198:Lower true dzo_214_1 roots_214 gzo_214_1 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_1) [(dom_214,1)] (by decide +kernel) (lower_slice_b (T:=gsh_214_1) [(0x550000000000000055000000000000005500000000000000550000,0,16)] (by decide +kernel) lowS_198)
def dzo_213_32:=0x33003300000000003300330000000000330033000000000033003300000000
def gzo_213_32:=0x33003300000000003300320000000000330032000000000032003200000000
def gsh_213_32:=0x330033000000000033003200000000003300320000000000320032
theorem lowS_zo_213_32_208:Lower true dzo_213_32 roots_213 gzo_213_32 6:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_32) [(dom_213,32)] (by decide +kernel) (lower_slice_b (T:=gsh_213_32) [(0x220022000000000022002200000000002200220000000000220022,0,1),(0x300030000000000030003000000000003000300000000000300030,0,4)] (by decide +kernel) lowS_208)
namespace S_247
def pG:List (Nat×Nat):=[(1,17),(1,33),(2,34),(2,66),(2,130),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(4,68),(4,132),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,23),(7,39),(7,71),(7,135),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,50),(18,82),(18,146),(32,33),(32,34),(32,36),(48,49),(48,50),(48,52),(48,112),(48,176),(64,66),(64,68),(64,80),(64,192),(65,67),(65,69),(65,81),(65,97),(65,193),(96,97),(96,98),(96,100),(96,112),(96,224),(128,130),(128,132),(128,144),(128,192),(129,131),(129,133),(129,145),(129,161),(129,193),(160,161),(160,162),(160,164),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_247.map (·&&&dom_247)
def gM:=goal_247&&&dom_247
def NN:Nat→Nat
|5=>1
|6=>53
|7=>267
|8=>340
|9=>85
|10=>12
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x67ef5
|6,0=>0xf2d38ea8cee1668d44b1d05fdcf5c3c446ac3709c1018bfafabc70ab1da5ab81daa678a2831a18698b8798a0f2882e9836d27c80c7bfd971aec7135c702a86d09669de8683736513e5edaa5d84b5d0b4563a85279951ebf512a64e9694e6b24a316477f73e6bf36be82b5ee287dc25ca1230e81841a1032c0efa5094a6093cb053d602e66
|7,0=>0x6369e634b3621bf60ff55dd185be975bdbc5b7bc5ad625a2fd5a2b35986758ec358bec582cb57e5e57d5d55b4c555bb55475527aa526cf5209251ebf518fb51527508364d87b4bd074bc8e4b99c4abff4a4f24a4ba491024846047084459434544744c7044af943b824351842c93425a141db141c68410fa4101140c7e400043ffe93f2543e1ab3cbb23b17139ca2390d63907d390013807d3767735fc335f0d35a33351c03446e33c3233b8832c72326bf3247230b15301362ed162e5642e50b2e2ad2e27d2cd8b2b9652b1242a2652a18528a39287dc2698a2660e24c0624a8c2490c2415a218601fb071e95a1b43b1a5fd1919b17f1e17aa8177f11678f142c513a5413715121d111b74117130fa920e5ba0d5d90d0220b7ca0b34c0abbf0a2810a22c07887070e50703106811062fd0561e03cc7034de02ce30269000830
|7,1=>0xf4544f1491edfdceccf3ec9e7eb00bea35ce73cee7380e4b9fe2526e1ff1e120cddaaddc3f8db516d95c6d87e9d6479d61cfd48afd44b1d4026d1ff2d1a31d1106cca3dc97cec6049c43f7c2374c0f1cc060fbe76fbba83bb9a8ba1beb88c8b6e59b6cf7b4cb9b26ccafc88af941ae9e8ae5fcadb44ad61caa9b7aa678a613fa3f7aa2d94a19f2a09469fa7f9f9da9ed4e9e8e49d9e19c3059bf719b8cc9a7349a1eb98f7598cd89834097d339681d9592794ea89435c922ed91efb914098d32c8c4da8b3058a8898834b880ae860cd85d9684c178118e80e0c808fd807ac805387e8fc7e2a97da167d4817ae4d7ac5f7891378685778937756775ff4750fe7467773c2e7365b7307771181701566f2b16e6a36d9276d6506cdec6a3506a0d1697dd6955a68c156890c683b767f8c67b106744f6651b65b4a65276648ef63ee0
|7,2=>0xffbffffa40ff0ddfe62efd84afc5cbfad82fa8adf8015f585cf5415
|8,0=>0x4800b47a42475f5473e8470cd46f6c45f3e44ec444aa243119429c4429734285641b84417de40bf0403b33ffe93fea63f0cb3efce3eda23da113c8fc3bf8c3ad3a3a2c039ebf392cc390d638b023792937839376ef36d2a367e63658b35d44350c034df534dda33d6d3291c31a4b30f8630ef930b15304392fcab2dabc2d5ff2d42f2ceb62cd9e2c91a2c7802af842a7fa2a24f2a13429f36286b0284ef279f72624625d2e25b6924785244ba23e0923da32343c2256922223216a1203f01fce31fbff1ec511cee41b1d11a7661a62b19b331997d1997519401191fb18b36184841838c17f4617b4f177081602d1542c145e013f2213e8313aab1348412c0811f8c0ec740e7b20dd010dc380ce810cbdc0c9860bdd20b7b40b5c60b5600a5ef0914308a030778f076a1074b604d93048eb04801039450237401ae201156001d7
|8,1=>0xa6413a619ba2bf19f25a9e67e9a1eb99965984de97f5397b6594d5b934be91dbd90d458e51d8d5348cd908c7678c0be899d988dbc8859f883d586f1d86e7785d968456082fc48201f81043808fd8041a7fcee7ea487e1aa7d6a07ca1a7bed97b4c77a8d67a4dc7a16e79c7378b69785017792e766a275df075b0f742bf73d877359971fa371181710bd710b16f4c96e0846dcea6d6506d0b96c8b86c7866c00e6bfcb6bb0b6b84b6a91f6a04c69edf68ded67cb26725c66b476626665e9064a0b647226348062fc76186c60e7260c17607ea6030f5f9125ef345ec5b5e5bd5db895c8825c66c5bf905b4135ad625aabc5a5e859c28598da590a657d5d57709569625646b55ecc55e5c55da655d3355b04555bb548c953f3752d965281d51b4e5148a50a874eb444e6174d87b4c9b64c6a54c5584a2ba49c61493d848c98481f0
|8,2=>0xff0ddfe963fcedefb10bfae4ffa7e6fa1d7f8426f82b2f675af5e70f418cf13b8ee566edfdced1d4ec56beb970eb96feb763e7494e4cbce4a41e311de1a1be1004dfa1ddf7fadd2ecdc582db498db310d9e2fd8bd1d7f54d7917d6161d6087d5dc6d4186d4026d2f2bd1794cfa0ccd50dcce06c996fc9505c92d5c795ec5d42c5cd1c5bbec5b64c5a15c479ac3eb3c2ee1bf54cbeb25beaa9be98dbc707bc655bbecabba83bb111ba242b338eb1240b11fcb1171afc76af941aedb7ae3a3ad7d3ad10facca7ac70cac63dab057a9ec7a9500
|9,0=>0xf4666e6bd1e1a1bdef15d9606d8de6d18a2d0640cff7dc6caec5b6dbbffeb31d4b2322b18edaf3ecab878a90c9a63bba5de6a50629deff989e193ea090afe903338c79a8b2b289f848794985d968218f7d9817b98c75191744ac742f87311c707c66e6486ba716713a602055d0ec596df587b55754f55a5c554ec54c6c508ed4ea5a4cd8c48c354535943363403353ef2f3b2063b0dd3a5b234a6b30b152efde2592e22d95217f21f2e61c8191aa1d17c83179111517712946103460fb490f5380e78e0a91d09031054eb026a7025bf02040019af
|10,0=>0xf9dd7e32aade92dc7110b47c39ac026aad465042346ae343e91950c17a11
|11,0=>0x3ef7d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000ff000000ff000000ff000000ff000000ff000000ff00000000000000000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff000000000000000000000000000000000000ff00ff00ff00ff00ff000000ff0000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc0000ff000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000ff00f000ff00f000ff00f000ff00f000ff00f000ff00f000f000f000f000f0aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa33003300330033003300330033003300330033003300330033003300000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000
|0,1=>0xff000000ff000000ff000000ff000000ff000000ff00000000000000000000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff0000ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00cc00cc00cc00cc000000000000000000000000ff00ff000000ff00000000000000ff00ff0000ff00ff00ff00ff00aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000ff000000ff000000ff000000ff000000ff000000ff000000aa000000aa0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aaff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00aa000000aa00000000ff000000ff000000ff000000ff000000ff000000ff0000000000ff000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000000000aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000aa000000aa0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000000000
|0,2=>0xff00ff00ff00ff000000000000000000ff000000ff000000000000000000000000ff000000ff00550000005500000055000000550000000000000000ff00000000000000ff00000000000000ff00ff00ff00000000000000000000000033003300330033000000ff000000ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000ff000000ff000000ff000000ff000000ff000000ff00ff00ff00ff0000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00aa00aa00aa00aa330033003300330033003300330033003300330033003300330033003300000000ff000000ff000000ff000000ff000000ff0000000000ff00ff00ff00005500550055005500550055005500000055005500550055005500550055000055005500550055005500550055005500550055005500550000000000000000ff00ff0055005500ff00ff0055005500ff00ff0055005500ff00ff00000000ff00ff00ff00ff00cc00cc00cc00cc00ff00ff00ff00ff00cc00cc00cc00ccff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00ccff00ff00ff00ff00cc00cc00cc00cc00ff000000ff000000cc000000cc0000
|0,3=>0x33000000330000003300000033000000330000003300000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0000000033000000330000003300000033000000330000003300330033000000000000ff000000ff000000ff000000ff000000000000000000550000005500000000ff000000ff005500ff005500ff000000ff000000ff0055000000550000330033003300330033003300330033003300330033003300330000003300000000ff000000ff000000ff000000ff000000ff000000ff000000cc000000cc000000000000000000000000000000000000ff000000ff000000ff00000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff000000000000000000000000ff00ff00ff00ff000000ff000000ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00ff00cc00ff00cc00ff00cc33003300330033003300330033003300330000003300000033000000330000ff000000ff000000aa000000aa000000ff000000ff000000aa000000aa0000ff00f000ff00f000fa00f000fa00f000ff00f000ff00f000fa00f000fa00f0ff00f000ff00f000ff00f000ff00f000ff00f000ff00f000fa00f000fa00f0ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00000000
|0,4=>0xcc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff0000000000000000cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc000000cc0000ff00ff00ff00ff00ff00cc00ff00cc00ff00ff00ff00ff00ff00cc00ff00ccff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00000000ff000000ff00000000000000ff000000ff000000ff00000000000000000000ff000000ff000000ff000000ff000000ff00000000000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00ff00ccff000000ff000000ff000000ff000000ff000000ff000000ff0000000000003300330033003300330000003300000033003300330033003300000033000033003300000033003300330000003300330033000000330033003300000000ff003300ff003300ff003300ff003300ff003300ff003300ff000000ff0000cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00cc00cc00ccff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff0055000000550000550055005500000055005500550000005500550055000000550055005500000000ff000000ff000000ff000000ff000000ff000000ff00ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc00cc00cc00cc00cc
|0,5=>0xff00ff00ff00ff00ff000000ff000000cc00cc00cc00cc00cc000000cc0000aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aa00ff00aa00ff00aaff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000000000ff00ff00ff00ff00ff000000ff00000000000000000000005500000055000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff0000ff000000ff0000000000000000000000ff000000ff00000000000000ff00000000000000000000ff00ff00ff00ff000000000000000000ff00ff00000000ff00cc00ff00cc00cc00cc00cc00cc00ff00cc00ff00cc00cc00cc00ff00ccff00ff00ff00ff003300000033000000ff00ff00ff00ff0033000000330000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff000000ff000000ff00ff0000000000ff000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00ccff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff00ff000000ff000000aa00aa00aa00aa00aa000000aa0000ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff0000000000ff000033000000330000003300000033000000330000003300000033000000330000
|0,6=>0xcc00cc00cc00cc00ff00ff00ff00ff00cc00cc00cc00cc00ff00cc00ff00cc00000000000000000000000000000000330033003300330033000000330000ff00ff00ff00ff00ff00ff00ff00ff003300330033003300330000003300000000ff000000ff000000ff000000ff0000003300000033000000000000000000000000ff00000000000000ff00000000000000ff00000000000000000000cc00cc00ff00cc00cc00cc00ff00cc00cc00cc00ff00cc00cc00cc00cc00ccff00ff00ff00ff00ff00ff00ff00ff0000000000ff00000000000000ff0000ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000ff00ff00ff00ff00ff00aa00ff00aa00ff00ff00ff00ff00ff00aa00ff00aaff00000000000000ff00000000000000ff00000000000000ff000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00000000000000ff000000ff000055000000550000005500000055000000550000005500000000000000000000f500f000f500f000f500f000f500f000f500f000f500f000f000f000f000f055005500550055005500550055005500550055005500550055005500550000ff000000ff000000ff000000ff000000aa000000aa000000aa000000aa000055005500550055005500550055005500550000005500000055000000550000
|0,7=>0xff000000ff0000000000000000000000aa000000aaff000000ff000000ff00ff00ff00ff00ff000000ff000000ff00aa00ff00aa00000000000000000000000000000000000000000000000055000000550000ff00ff00ff00ff000000000000000000ff00ff00ff00ff0055000000550000000000000000000000000000000000000000ff000000ff000000cc000000ccff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000cc000000cc000000000000ff00000000000000ff00000000000000ff0000000000000000aa00aa00aa00ff00aa00aa00aa00ff00aa00aa00aa00ff00aa00aa00aa00aa00005500000055000000550000005500000055000000550000000000000000ff00ff0000005500ff00ff0000005500ff00ff0000005500ff00ff000000000000ff000000ff0000000000000000000000ff000000ff00ff000000ff000000000000000000000000000000000000000000000000000000000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff0000ff00ff0000000000ff00ff0000000000ff00ff00ff00ff00ff00ff00ff00005500550000000000550055000000000055005500550055005500550055000000000000000000003300330033003300000000000000000033000000330000
|0,8=>0xf000f000ff00f000f000f000ff00f000f000f000ff00f000f000f000f000f0ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000000000000000000000000000000000000000000000000000000000000000ff000000ff0000ff00ff00ff00ff0000000000ff000000ff00ff00ff00ff0000000000ff00000000ff000000ff000000cc000000cc000000ff000000ff000000cc000000ccff000000ff000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00550000005500000000ff000000ff000000ff000000ff000000ff000000ff00ff000000ff0000ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa0000000000000000ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00000000ff00ff0000000000ff00ff0000000000ff00000000000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00ff00aa00ff00aa00ff00aa0000000000000000ff00ff00ff00ff000000000000000000ff00aa00ff00aaff00ff00ff00ff003300330033003300ff00ff00ff00ff0033000000330000ff00ff00ff00ff00ff000000ff0000000000ff000000ff000000000000000000000000ff00ff0000000000ff00000000000000ff00ff0000000000ff0000
|0,9=>0xff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff000055005500000000005500550055005500550055000000000055005500550000ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000ff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00ff0000ff000000ff000000ff000000ff000000ff00ff00ff00ff00ff00cc00ff00ccaa000000aa000000aa000000aa000000aa000000aa000000ff000000ff0000ff00ff00ff00ff00aa000000aa000000ff00ff00ff00ff00ff000000ff0000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ff00cc00000000000000000000000000000000ff000000ff000000ff000000ff0000ff00ff00ff00ff00ff00ff00ff0000000000ff000000ff000000ff000000003300330033003300330033003300330033003300330033000000000000000000000000000000000000ff000000ff0000000000000000000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00ff00aa00000000000000000000000000000000ff00ff00ff00ff00ff00aa00ff00aa0000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000000000ff0000
|0,10=>0xff00ff0000000000ff00ff00000000000000000000000000ff000000000000ff00000000000000ff00000000000000ff00000000000000ff0000000000000000000000000000000000000000000000000000ff00aa00ff00aaff00ff00ff00ff000000000000000000ff00ff00ff00ff00ff00aa00ff00aaaa00aa00ff00aa00aa00aa00ff00aa00aa00aa00ff00aa00aa00aa00aa00aaff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff00000000dd00cc00dd00cc00dd00cc00dd00cc00dd00cc00dd00cc00cc00cc00cc00ccff00ff00ff00ff00ff00ff00ff00ff00550055005500550055000000550000550055005500550055000000550000005500550055005500550000005500000000000000000000ff00ff00ff00ff00000000000000000055000000550000ff00ff0055000000ff00ff0055000000ff00ff0055000000ff00ff000000005500550000000000550055000000000055005500000000005500550055000000000000ff00ff0000000000ff00ff0000000000ff00ff00ff000000ff0000000000000000000000000000000000000000000000000000ff00ff00ff0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ff00ff00ff00000000ff000000ff000000ff000000ff00550000005500000055000000550000
|0,11=>0xff00ff00ff0000000000000000000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00ff00ff00000000ff00000000000000ff00000000000000ff0000000000ff00ff00000000aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00aa00aa00aa0000000000000000ff00ff00ff00ff000000000000000000ff00cc00ff00cc000000000000000000000000000000000000ff000000ff000000aa000000aa0000000000000000ff00aa00ff00aa000000000000000000ff00aa00ff00aaff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff0000ff00f000ff00f000ff00f000ff00f000fa00f000fa00f000fa00f000fa00f0ff000000ff000000ff000000ff000000ff00000000000000ff00000000000000000000000000000000ff000000ff0000000000000000000000cc000000ccff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00ff000055005500550055005500550055005500550055005500000055005500550000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff000000ff00000000000000000000ff000000ff0000000000000000000000ff000000ff0000
|0,12=>0xaa000000aa000000aa000000aa000000aa000000aa00aa00aa00aa00aaff00ff00ff00ff000000000000000000ff00ff00ff00ff00ff000000ff0000ff00ff0033000000ff00ff0033000000ff00ff0033000000ff00ff003300000000000000000000000000000000000000000000ff00ff0000000000ff000000000000000000005500000055000000000000000000000055000000550000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000055000000550000ff00ff00ff00ff000000ff000000ff00ff000000ff000000000000000000005500550055005500550055005500550055005500550055005500000055000000000000000000000000000000000000ff00ff00ff00ff00cc00cc00cc00cc0000000000000000ff00ff00ff00ff000000000000000000aa00aa00aa00aa0000ff000000ff005500ff005500ff00000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0033000000330000ff00ff00ff00ff00ff00ff0000000000ff000000ff000000ff000000000000000000000000000000000000ff000000000000000000000000000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000ff0000ff00ff00ff00ff00ff00ff00000000000000ff000000ff000000ff00000000
|0,13=>0xcc00cc00ff00cc00cc00cc00ff00cc00cc00cc00ff00cc00cc00cc00ff00cc0000cc000000cc000000cc000000cc000000cc000000cc00cc00cc00cc00ccff00ff00ff00ff005500000055000000ff00ff00ff00ff005500000055000000000000000000000000000000000000ff00ff00ff00ff005500000055000000000000000000005500550055005500000000000000000055000000550000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00ff00aa00ff00aaaa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00330000003300000033000000330000ff00ff00ff00ff00ff00ff00ff00ff005500000055000000550000005500000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00aa00ff00aa00000000000000000000000000000000ff00ff00ff00ff0033000000330000ff00ff0000000000ff00ff0000000000ff00ff00ff000000ff00ff00ff000055000000550000005500000055000000550000005500000055000000550000ff00ff00ff000000ff00ff00aa000000ff00ff00ff000000ff00ff00aa0000ff00ff000000ff00ff00ff000000ff00ff00ff000000ff0000000000000000
|0,14=>0xff000000ff000000aa000000aa000000ff000000ff000000aa000000aa0000000000000000ff00ff00ff00ff000000000000000000cc00cc00cc00cc000000000000000000000000000000005500000055000000550000005500000000000000000000000000000000000000000000ff00000000000000ff0000ff00cc00ff00cc00ff00cc00ff00cc00ee00cc00ee00cc00ee00cc00ee00cccc00cc00cc00cc00cc00cc00ff00cc00cc00cc00cc00cc00cc00cc00ff00ccff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000cc000000cc00000000000000000000000000000000ff00ff00ff00ff00ff00ff00000000ff000000ff000000ff000000ff000000000000000000000000000000ff000000000000000000000000000000000000ff00ff00ff00ff00aa00aa00aa00aa00000000000000000000000000000000ff00ff00ff00ff0000000000ff0000ff00ff0000000000ff00ff00ff000000ff00ff0000000000ff00ff00ff000055005500000000005500550055000000550055000000000055005500550000ff000000ff000000ff00000000000000ff000000ff000000ff0000000000000000ff000000ff000000ff000000ff000000cc000000cc000000cc000000ccff005500ff005500ff005500ff005500ff005500ff005500ff000000ff0000
|0,15=>0xaa00aa00aa00aa00ff00aa00ff00aa00aa00aa00aa00aa00ff00aa00ff00aa00000000000000000000000000000000ff00aa00ff00aa00ff00aa00ff00aa
|_,_=>0
def sP:Nat→Nat
|0=>0x110a0902060504110a09250f2304110a09020f05210a20020f1e050403090200050a1d020706000b0a09021c0600051a040a09021305110a090217050a09021606000504110a09140f0504110a02010f0504110a0902130511100a09020f0d050a09020e000d0b0a090207000d050c0b0a09020a090208070600050403020100
|1=>0x50a023a39060036050b0a0902000535040a02340f2b050309020600051a0432090200051131090206300b0a02010600050c2f0a09020e05110a09022e062d0b0a09020600050b0a09020f2c05110a0201061f2a050a090206001205110a1d0206120504030902002912030902060029120a09280600050b0a022706002605
|2=>0x3f000511480a09020f06052f0a090208002b050a1d02060005110a2202470f050b0a024606000503090207060005450a4402060029120a1d020600050b030201060005040a09024300050b0a280106000504110a09420f29410a0902060005040a40020f3f050b09023e0600050b0a023d060005110a09023c0605040a09023b
|3=>0x9020f05110a09020f064f29480a0902060005110a094e020600054d0a0902390600050c0b2f0a09020f0d05110b0a09020f050b0a0902064b00051a040a09023300050b0a40020f063f050c0b0a09024a06050b09023e0f0600051a0c0a0902060e05110a0902080f0605350b0a023a0600051a0b0a09140600051a0a090206
|4=>0x4110a090200050b5d0a09020f06053504110a09020f05040b0a09025c0005110b0a09420f0605040b0a09250f0023040b0a09020f004c0504110a09020f05410b0a090206005b05110b0a090206050b0a5802060005110a0902570f1e0b550a0902060005211a0a5402060005110a090252061e0b0a0902510600120504110a
|5=>0x9020600050b0a0201061f000504110a09020f24056704110a09020f050b650a09020f06050b630902060005110b0a0962060005110a0902470f05110a09021712050b0a1d020600051a0a094e0206000504110a0902600f050b0a095f020f5b0504110a0902060504110a092506001e560c0b0a09020605210a20020600055e
|6=>0x56f0b0a22020600054d110a09020f050b0a4009026d0629120a0902060e0005043209020029050a09280f060029370b2f0a09020005040a0902066c00050b0a6a02060005040b0a09021700050a090269060e00050b0a0902060e00050b0a02460f06005b051a0b0a090206051a0b0a09250600050b0a4402063f00231a0b0a
|7=>0x90200057e040a09020600051a0b0a2240020f05450b0a40020600050b0a09027c0f000521110a02340f060504110a09020f15050b0a0902130605110b0a09027a06050b0a09780f0600760b0a09020600050a090207061f000504750a090200050b0a090273060005040b0a0971060005450a0902063f0029050309020f0600
|8=>0x40020f062b050b2f0a090200050b0a40028206000504110a0902850f0583110b0a09020f29050a1d0206000521110a028206001e050a0902068100050b0a0942060e00050b2f0a09028000051a0b0a0962060005040a4009020f0e05040c110a091b025b050b0a09020f06050b0a4002340f06054d110a2209020f1e050b2f0a
|9=>0x6000535040a02340600050a09028c0f0e00050b0a40028b0f12050b2f0a0902008a050b0a09020600050a090280060e00050b0a09028906005b050b0a092506001e050a0902060e001e0b0a090207060005110a1d020f06050b0a0227060005040309020f0005880a090206000504110a09025206050b0a0928060005211a0a
|10=>0x2060005110a09023906000521110a023a060005450b0a22020f0072560c0b0a09020629680a0902060e004c05110a0902061f0591110b0a090206290504110a09020f050a090290060e002b050a0902060e002b0b0a0902070600050b8f09020600300b0a09020f06001205110a0902061f050b0a09620f0600058d0a090208
|11=>0x2063f0005350b0a2240020f054d0b0a02470f0005040b0a40020f94050b0a090206790005110a090208060005040a0902390f00050c0b0a092506000504110a0902470f68050b0a024606008a05040a0902060005110a4409020f06051a0309020600120b0a0902070600050b0a40023a060029480a09020f060012300b0a09
|12=>0x20f063f05110b0a0227060005911a0b0a090206290b550a09020600050c0b0a097106009b120b0a09020600059a110a09020600290b0a090251060005980b0a09020f00050b0a97020f060005112f0a09020f0e05040a090295060005110b0a02010f06050b2f0a09420600059104110a090206050b0a0902080600050b0a40
|13=>0x51a0a0902064f000521110a54020f0672050b0a09710600050b0a22023a0f00050b2f0a09021500051103090206051a0a0902080600050b0a099e0600051a0b0a09020600051a480a0902060005110a09021906051a0a0902390600059d0b0a09020600050b0a09029c0f0005211a0a023a060005110b0a09140f0605110a09
|14=>0x19060005450b0a54020600051a0b0a09420600050ba30a09020600058604110a09020fa1050b0a09020f002b050b0a0902060005210a4002390600051a0b0a02270600051a880a090206000504110a09020f0e05350b0a22020f0504750a09020f0005110a0902170605110a0902a00605910b0a09020f060504110a09420600
|15=>0x50a090207060e0005490b0a09020600a50b0a09020600050c0b2f0a0902050b0a02270f0600a2050a0902060e0005490a0902390600050b09023e060029050a1d020f06000504110a091802050b0a0201060e0029680b0a09020600050b0a09a40600050b2f0a0902070005211a0a02470600054d0b0a026d060005860a09
|16=>0x90224050b0a5402063f00050b8d0a02010600050b0a0246060e00050b0a54023a06000535110b0a22020f29120a0902061f009b050a0902060e00050b0aa902060029050a0902060e00290b0a090207060005040b0a0902a60012050b030902060005110a2202470600050c0b0a0902930612050b0a09280600052f0a09020e
|17=>0x61f000504110a09020f94050b0a0978060005ac0b0a09020f00120b0a0902068e00050b0a09ab0600290503090206000504110a5409020f0521040a40020f29050a09280600051a0a1d02060005110b09023e060005040b0a0902aa00050b0a0246060068050b0a0902060029050a0942060e0005110a44090206000504110a
|18=>0x620600059d0b0a09140600050b0a09a40f0600050a090273060e00129d0b0a09020600051a0b0a0201060005210a5402390600051a0c0b2f0a0902050a090274060e00051a0b09023e0600050b0a0902070600051a0a4409020600050b0a2240020f0e05040c112f0a0902050c110a0902060e05110a0902063f002b050a0902
|19=>0x4c05110b0a09b3060005212f0a09020600050b0a0902690f0605210b0a5422020600050b0a0902130600b2050b0a09020600051a0b0a0902600600050b0a0902af0600050b0a4002069400050b0a0902700600056704110a09020600050b0a0902aa06000504110a0918020f05490b0a023a0600300b0a09020600050b0a09
|20=>0x1a110b0a0953020629b60a0902060005110b0a09023a0600050b0a2209027006002956040b0a0902060005040c0b0a091b0200050b0a02010f0600050b0a0902b50600051a0b0a0902062400054d0b0a2209020f00054d110a0902060005490b0a09020f060005671a0b0a09020600b4050bb10a0902060005040b0a09020f15
|21=>0x5bb0b0a09020600058d0a0902060e00050b0a0902a80600054d110a220902060005450b0a09020f060029050b2f0a09020600050b0a09140f060029050a09020f060e00050b0a0902ba060005ad0b0a0902060005b90b0a095306007205040b0a0902060005110b0a0902b80600050bb7090206001e050c0b0a0902060005
|22=>0x2060012050b0a0902061f00050b0a0902c00600050b0a09026d0600be050b0a090206000504110a09028506000583110b0a09020600051a0b0a0902061500bd0b0a0902060005860b0a09180600050b0a1d020f0600059d0b0a0902061500050b0a09bc02060005110b0a09020706000521040a09020f0005040b0a09025206
|23=>0x50b0a0902c4570600051a0b0a0902850600050bc30a090206002905040b0a09020f00051a0b0a09023a0600050c110b0a09020605040b0a09250600050b0a0902c1060005860b0a0902060e00051a110a0902500600050b0a22020f940005040b0a09028506004c0d050b0a090206000592110b0a090206000549350b0a09
|24=>0xb0a40020f0605210b0ac702060005040b0a0902470f00050b0a4409020f060005040a09020f0e00057e0b0a09020600050b0a0902060e0005211a0a0902060068050b0a09020f0600050b0a40028b0600050b0a090206c50504112f0a09020005040c0b0a09020f050b0a2209020f0e0005110b0a0902062405110a0902060e
|25=>0x50b0a0902ca0600bf560b0a0902060005040b0a09029306001e050b0a09250600050b0a090273060005040a09023406004c370b0a09020600051a0b2f0a090200050b0a54400206940005110b0a5409020f06290504110a0902060005110a090206c900050c0a0902500600050b0a0902c80600051a0b0a09020706000521
|26=>0x600050b0a0902380600050b0a400902390600cd0b0a09020f060005110b0a0902ba060005110a0902610629051a0b0a0902060005110b0a09020f0694050b0a09021306054d040b0a09020f0005921a0b0a090206000504110a0902470600050b0a09023a0f060005110b0a09027b0600050b0a0902cc0600050b0a09020677
|27=>0x60005350b0a09020f06050b0a0902070f0600051a0b0a090247060005ce0b0a09020f0030050b0a09020f060005350b0a02340600051a0a0902060e00a2050b0a09020f0600050b0a09020f063f0005670c0b0a0902060029050a0902061f009f050b0a09020600054d0b0a540902060005350b0a2240020600230b0a09020f
|28=>0x50b0a091406150072050c0b0a09020600050b0a0902890600d10b0a0902060005920b0a09020f0600120b0a090206150005860b2f0a09020600050b0a090206d000050b0309020600050b0a09cf060005110a09020f061f055e0b0a09020600050b0a092806000584110b0a09020f06050b2f0a09020f00054d04110a0902
|29=>0x5211a110a0902060005110b0a0918020f06300b0a09020f060005d50b0a090206009b050b0a09020f0600050b0a0902d4060005040b0a0902a80600050b0a09020664008a050b0a09020600050b990a09020600054d1a0b0a0902060005210b0a54020f0600d3370b0a09020600051a0a0902500f060005110bc30a090206
|30=>0x9020f00050b0a09027d0f06004c37110b0a0902060005040b0a09026d0600290b0a090280060005040b0a09020f0e0005110b0a0902c8060005040a09021f001e0504960a0902060005040a0902d8060005860a09610600050b0a5402069400050b660a09020600050b0a0902d70f06560b0a0902d6060005110b0a0902060e
|31=>0xb0a09b30600055e0b2f0a0902060005350b0a2202060029050b0a09420f0600050b0a0902dc0600050b0a0902db0600050b0a09027369060005da0b0a09020600050b0a09023906001205110b0a09020f06050b0a090206d900050b0a0902068e004c0b0a090285060037050b2f0a090200050b0a540902060e000586040b0a
|32=>0xe00050b0adf020f060005110a0902500f06050b0ade02060012050b0a02010f060029120b0a09020600051a110a0902060e004c05110b0a09020f06050b0a0902080600058604110a0902060005ad0b0a09020f0600051a0c110b0a090206230b0a0902062400050b480a09020600050b0a090206790005040b0a0918020005
|33=>0x2060005110b0a0902600f0629590b0a09020600056f0b0a09020600050b0a0902c4060005040b0a0902cc0600059a0b0a09020600051a0b0a0902c8060005861a0b0a09020600bd0b0a09020f0600050b0a0902064f00055e110b0a09020600050b0a0902e10f0605860b0a09180f060005e00b0a09020600051a0b0a090206
|34=>0xb0a09e60600050b0a0902b8850600050b0a0902e5060005211a0a09020f060005040b0a09024a0600050a0902ae060e0005110b0a09020f062405490b0a40090206000504110a091b0200050b0a09e30600051a0b0a09020600050b5d0a0902060005040b0a4009020f051a0b0a2209020f0005110b0a09420600059d0b0a09
|35=>0xa0902850f060504110a09020f29050a09020f061f00050b0a540902390600050b0a0902e706002b050b0a090206000521040a02470600050b0a0902066b0012050b0a0902060e000535110b0a22020600050b0a0902730f0600051a0b2f0a09020f003705110b2f0a090200050b0a0902c80f0600050b0a0902740f06000586
|36=>0x600050b0a0902890f0600050b0a02010600050b0a09420f0600050b0a09028234060005490b0a090206000521040a40020600050b0a0918062400050b0a09020f06d000050b0309020f06005b050b0a09020600050b0a09cf0f0600050b0a40023406000504110a0902a70600050b0a0902510600050b0a09280f060005110b
|37=>0x902390f0600050b0aea020600051a0b0a0902069400050b0a0902e90600050b0a09020f068e00050b0a1d020600050b0a0902340f06050b0a092802060012050b8d0a0902060005450b0a090206001e05110b0a09020600050b0a0914060029050a0902060e00051a0b0a5409020600050b660a09020f0600050b990a09020f
|38=>0x2060005e00b0a09020f060068050b0a09020600051a0a0902061f00050b0ade020f060029120b0a09020f06001e0504110a09020600050b0a0902080f0600050b480a09020f0600050b0a0920020600050b0a09020f067900050b0a440902060e002b05110b0a0902060005da0b0a09020f060068050b0a0902060e00050b0a
|39=>0x51a0b0a09020f06002b051a0b0a090206000d05110b0a09020600051a0b0a0918020600050b0a090289d70600059d0b0a09020f06000549110b0a09020600050b0a0902570f00050b0a0902c40f0600050b0a090252060005110b0a0902c6061e051a0b0a09020600050b0a09020f064f000504110b0a09020f050b0a4409
|40=>0x902060005491a0b0a090206002b050b0a09020f060005830b0a09020600050b8d0a0902061500050b0aeb020600050b0a090207060012051a0b0a0902060030050b0a09020600a2050b0a0902060029050b0a0902060e00050b0a0902063f00230b0a0902060005490b0a5409020600050a0902ae0f060e00050b0a09023a06
|41=>0x50b0a0902610600050b0a09e60206000567040b0a0902060005040c0b0a09020600050b0a090247060012050b0a09020f060005110b0a09020f06300b0a090206009b050b0a09020600050b0a090206870005450b0a0902069400050b0a2240020f05210b0a54020600051a0a0902500600050b660a090206150005920b0a
|42=>0x2060e00050b0a09ee0206002905110b0a09020600050b0a0902ae0f0600050b0a09020f062400050b0a0902ed0600054d0b0a2209020600050b0adf020600050b0a09020f061f00050b0a0902ec06000521110a09020600e4050b0a0902060029050b0a09420600054d0b0a0902060005110b0a09028506000504960a090206
|43=>0xa09020f0600050b0a0942060005f00b0a09020600054d040b0a09020600050b0a0902d80600050b0a544009020600050b0a09024a0600050b0a0902ef060005040b0a09024706005605040b0a09020600050b0a0902500f0600050b0a2209020f0005860b0a091b0600050b0a0902d20f0600050b0a09020f061500050b0a09
|44=>0x50b0a09020694000504110a0902060005210b0a09020f0600050bb60a09020600050b0a540902060037050b960a09020600050b0a0902690600050b0a0902a70600050b0a091b530600bf050b0a090206000586110b0a09020600050b2f0a0902060005ce0b0a0902060005040b0a4009020600050b8d0a0902060029050b
|45=>0xb0a09020600050b0a09028b060012050b0a0902060005040b0a095302060005f10b0a0902060005210b0a40020600050b0a0918020600050b0a09028006001e050b0a0902060005860b0a09020f0600050b0a09020f060e0005040b0a091b020005840b0a0902060037560b0a09020600051a0b0a0902060029370b0a090206
|46=>0xb0a09020600051a0b0a09020f060005110a0902500600050b0a09020f069400050b0a09020615001e05040b0a09020600050b0a2240020600050b0a5409020f0600050b0a0902d70600050b0a0902062400050b0a0902061f00050b8d0a09020f060005590b0a09020600051a110b0a0902060005040b0a0902a70600050411
|47=>0x50b0a0902060029050b0a09020600050b0a0902500600050b0a0902d20600050b0a0902ae060037050b0a09020600050b0a09020f060005110b0a09020600050b0a095302060005860b0a09020600050bb00a0902060005210b0a09020600050b0a4009020600050b0a0918020f0600cd
|_=>0
def sO:Nat→Nat→Nat
|5,0=>6
|6,0=>0x16f70b438585c2b4e15370a638515c27ce1377098384a5c244e11b708a38435c20ce0ff707c383c5c1d4e0e3706e38359819ee0c87060b82e9c166e0ac7052b8279c12ee0907044b8209c0f6e0747036b819d80c0e05970293812dc08ac03e701bb80c1c052e022700db8051c01ae0067
|7,0=>0x1b0c0d6d86a7034b81a1c0cf1c669032c819240c720629030c818240bf205e902ec817240b7205aae2cd816338b01857102b0815440a85c53302918144c0a09c4f5027281354098a04b5025281254090a047502328115b8891c43902148106b881603fb01f580f73879a03bd01d680e74071a037d01b680d74069a033d019680c74061a02fd01768
|7,1=>0x2aac15360a8b053d829ac14b60a4b051e728b4143a0a0d04fe827b413ba09cee4df826bc133e098f04bf825bc12be0950e4a1724d3924dc9170484723e411d208d90464822e41155c89b0445821ec10d6085b0425820ec1056081b040581fec0fd607db03e581eec0f56079b03c671df40eda075ee3a781d038e620721038881c040de206e2e3698
|7,2=>0x3a6c1d160e7b07358396c1c99ce3d0717738839c220e0106f8837841ba20dc106d8836931b2a0d86e6bb8359c1ab1cd49069c834a41a320d09067c833a419b20cc9065c832a419320c89063c831a418b20c49061c830a418320c0905fc82fa417b20bc905dc82ea417320b8905bc82da416b20b49059d72cac16360b0b057d82bac15b60acb055d8
|7,3=>0x49ec24d6125b0925848ec2456121b0905847ec23d611dce8e6846f4235dd1a0e8c88460ba2e9d166e8ab8451c2271d129088c8442421f5d0eb086d8432c217610ab084d8422c20f9d06d082e84134207a102d080e840341ffdcfef07ef83f439f85cfb307d183e4c1f09cf7507b373d5c1e8e0f38e79483c641e120efae77583b6c1d960ebb07558
|7,4=>0x264e1317098474beba5d612db096584aec2556129b09458
|8,0=>0x5d94aea657430b9895c7cae1a56fb2b7495b642d9216b90b5395a54ad065674eb32859542c8656330b10958442bfe55ef0aef8573c2b7a55ab2acc956242aee55670aab8551c2a6a55232a8a7540ca9e254e2ea68952fca95a549b2a45851ec28d254572a23850d4a846541129ff94fb4a7ba13cd09dd94eac2736138929bc84da426b21347299b8
|8,1=>0x6e5c370e1b752db196d44b6821b310d8f96c34b5fa1aed0d6d96b2c35725aaaed4c96a1cb4f1da672d2a9690cb4625a1f2d07867fc33de19df0ce6966f4335a199d0cc6865f432d659592ca3964dc324e19170c82963d431ca18d32c60962c4314218910c40861bcb0be1850ec20860c4303e580f0bff85fb4afb657cb0bdc95e9caf2e17870bbb8
|8,2=>0x7f04bf621fa10fc797dfc3ede1f5d2fa687cf43e5a1f1d0f8597be4bdce5ed52f6197acc3d425e8f2f40779bcbcbe1e50ef20878c43c421e110eff977b4bbb65dcb0edd876a4bb321d872ebb8759c3aae1d452e999748c3a225cff2e7787374b99a1cbeee569727439165c7b0e367717bb89e1c3f0e187707cb81e1bfd2df686f6cb7925bb90dd39
|8,3=>0x8fd4c7cde3d531e198ecc4746239311c188dc4c6be634d319d98ca4c62e6305317a88b8cc5a622c1315798a7c451a627b313588973c49a223d11168886cc41621fb10f498764439221b910d39865c430a617330b18854c42826131108f9843c41fa60ed106e8833bc17a60ad104d98224c0f22067302a9810cc066202310098800c3fe9dfe32fe98
|8,4=>0xa0cbd042680f33ff89fb4cfb667c933db99e94cf26678133b889d7cce9e273f139699c6cce1626fb137499b644d9226b9135399a54cd06667133308993ccc7a662b330c9981ccbea65e6f2ea997144b6665a4f2ca896144ae6656312a89950bca6625213287993f4c9d664dcf266892ecc956249b1245891e4c8d224591224890e4484e641712038
|8,5=>0xa5ebd2d6295b14a49a4ebd256291b14849a3e451ce68d534628a2ccd149e89514419a1cc50c6285134208
|9,0=>0xb68c5b262d8316b98b584da9e6d3f16978b47c5a1e2cff16778b37c599a6cbd16568b26cd9162c7b16358b16c58926c3916148b05cd80e2bf535f37af5c578a6bb515d19ae4c57062b7135af9ad34d67a2b2d158d9ac24d5f22ae9156b9ab14d5666aa315489aa0bd4e26a6115288a90454622a2115079a7fc53de29df14e69a6ecd356299934c48
|9,1=>0x17819bbd3ddc66ed317609bac45d3e6e8f173e9b9b45cba2e4d171d9b8ac5c326e0736fa9b7945baa2dc336d98
|10,0=>0xbf145f6a2fa517ca8be145eea2f6517aa8bd145e6a2f25178a8
|11,0=>0x17ea7
|_,_=>0
def wAt:=mkWire dB 242 248 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x20f418010b0044827050f42c3c2b1fc14690b0f42c3c0b0f018010b004287d0b0f000190b064287d050b4143d0b0f01801021f4142d050f42c3c060042c011e02c14110b0641491020f82c190b00444880b0042419000642c250a1f42c3c000642c190b1b008190b06464190b180083d060042c010b06408550b004143e0b0642c011209c143d0b0044810000642c19
|1=>0xb09c482c050f4142d06005242f4d00484190b09468030b0f5301b051142c010b1b008190b064843e060042c252b0aca43d050b4482f050f418014909cd419210042c250b0f4843e06004482c060042c01051a8287d0b0f42c3c050f4142d091f42c3c06004a40b050b42c190b00400192f384441b3711c1419051a4287d0b0f42c3c0a3342c6c0b06408190a1942c60
|2=>0xb004780b050442c190400c2c190b09444880b00424191106c4844050f418010b00444250b06418010b0042c012902c142d06004780b0504400190b0642c1905244083e000642c190511418010b004487f0b0f018012b00cdc45050642c01095a5642e5606c1401500642c010b09c1801560401411050042c3d060042c01045302c1902004143d0b06418010b005403e
|3=>0xb06425ad0b150143e060041060020f5a027050e42c3e040047803050442c19093f4843e060042c251209c143d0b0f01801020f82c19060042c010b0041009000642c19660042c57050f818010a6442c90020f818012b02cdc450506400190b00410270b06584190b5302c0102004247d050f42c3c0600400190b064440b0b0040019044002c19090047803050442c19
|4=>0x644460020f418010b005ec01112282c010906409e5290f8142d057742c92020f81801051a82c3d0b0f0107f0b0642c3c00065d03d120b818017202c14310400c2cfd210f818010b094142d0a1f42c3c0600425c11122c2c010906484190b00418010b095b8010440c2c19090042c3e0600428cd0b1b02c1902064142d021f42c3c06004441b0b0042db6470041027
|5=>0xa1f42c3c000642c191a1fc2c3d0b0f018010b004114c0b0640a1d860f018010b0242c3d06004441b371142c01340642d01051182c19060042c018406c44090b004142d091f42c3c06004d0190b00424010b0f808190400cac03290f4142d060042d010b2242c0109064681b040042c190b7f4114e0b0640801090042c3d00065f4190b18c083d000642c010b064143e
|6=>0xb00410030b0642c3e060042c3c0511418010b00648031a02444190b0041801050b42c190b004a4390b0f81801051a4146a110642c010a6b42c54050f81801058e4a43c050b4143d0b0f018010b004ac0b290f4142d120bc143d0b0fc0019060042c8a0900424191a06c2c3d00064682f040042c19051a81411040042c19091f42c3c060042c012b09c7801050442c19
|7=>0x50f42c3e0b0047a5b050442c030b0044827050f59c03040242c19093982d52400642d010600424010b064243e291a82c3d06004ac2f3711414190b0042d52090f40019060042c010409c2c19050e42c3e060042e4d5604c14010b0642c3e0a1f42c3d0b0f01801050f4146a0b0f418014909c11010b0642401120b0143d050b42c3c06005242f112242c01090644419
|8=>0x500f818010600414310400c2c190b0f400190a1f42c010b0f018012b0bc1469110642c019f02c14bd1106c2c010b180083d060042c010b548243d0b0f4180174064482e050f40019110642c01021542c01050f8843e060042c252b09cdc450506648031a02444190b004142d560401401058d4143d0b0fc18010b7b4448a0b0042419990642c93020f8001909744482e
|9=>0xb0f018010b004083d000642c19050e42c3e050b418019b02c16350b0fc18010b0642c60020f418010b0242c01000642c090b0668819290fc142d00064a4390b0f8142d06005001909004687f0b0f42c3c0b0042c190b0f80019210042419000642c25041fc2c3c0b06584190b5302c010200445870b5302c010200648030b184083d06004a40b050b42c190b0042c3d
|10=>0xb00418014909c2d51400642401110942c01050b4143d0b0f01801096442c90020f818010f1fc2c3c06004146a0b0f4142d06006a01ba70042c190a1f4143d0b0f018010400d581305004087d050f42c3c06004682f1a06c10010b06415910b240083e0600468031a06c10010b064ac27290f4142d0b0f8a43f050b42d520b545001909004ac2b1e0042c19050b4247d
|11=>0x110642c01051a42c3d0b0f02c19090f818010b00409e5290f8142d06006b419860fc00190b024143d290f0142d026b42c54050f81801050b4287d0b0f018010b064243d060042c010b0642401060042c25021f4142d0b0f01801091f42c3d0b0f018012b0acdc45050664c195604c14010b065a027050e42c3e060043c7f0b0f018012902c2c3e060042c19020f81801
|12=>0x6006b801050b82c25220042419330042c6c02064de590b00c14190b00416c6b00042c1b5409d001909004448b0b00424190b00410090b0652819560bc14010b0642c01020f418011a0946827110642c01058e4a43c050b418012b02c7801050442c199b02c16350b0fc2c3eae0f418014006424010900424190b0f800190400c2c011a0bc6803110642c010b3a86827
|13=>0x8606c2c090200414310400c2c198506414460b00429850b53008010504410030b0640801110642c01050b5582c050046827110642c011122c2c01050b414010b06408190400c2c191209c143d0600411020b06424010b0f4083e060042c890006424190b00484190b094843d060042c250400410090b066c0010b06c2c19050f800194c02c14450b004441b0b0042c25
|14=>0x2906c142d0b06414460b006101b110242c010b0f41801051fc2c3c06004083d060042c09091f42c3c060042c55050f81801020e42c3e06004146a110642c010b06400190b094114c0b06408013506c84010b0942c3e0b0fc1801a7004100b0b0642c890b00424190b944243e06004142d1106c2c0102154143e06004142d0b0f81801111b82c0102066183f060042c09
|15=>0x20642c191106c2c010400c00190b06424190b0f80019020f818010b004682f110642c01500642c270b004dc44050642c01050b400190b06444190b0042c010400c2c191e02c14110b0670801370b814190b0f818010b09c2c01090f80019090642c19051182c014c06c14450b0046809110642c01210042c25050f42c3c06004de5b0b00c14194700410270b066fc01
|16=>0x69066b801050b82c191109c2c010506414450b004681b040042c195409d001909004243d060042c01050b42c190b00446c30b06c2c010b09c10030b064680b110642c01110642c010900418010b0942c252200c24190409c00190b06424390b0f818010b0642c3e000642f195306c08010f1fc2c3c060042c3d060042c25050e42c3e060042c8a090042419330082c6c
|17=>0xb0042c892200424190b4042419090041491020f818013711c14190b0042d52400642401055042c2706004446e0b00408190b5302c01020042c3d06004243e060042c01330042c6c020641025000642c19110642c010b00410270b06468270b0f418011122824195604814010b0642c92020f81801cb0042c6f02064a41b050b414015604c14010b064780b050442c19
|18=>0x1106c2c090b006b83e050b818010a1f42c3c06004087f0b0f018010b0f018010b004bc091106c2c01021f42c3c060044409060042c011a06c2c3d000642c01040942c190006484010b094146a0b0f418010400410270b06634190b0fc0019051f42c3c06004d427210042c250b0f42c3e06004a43f050b41801210f818010b09410030b064142d0b0f01801052f4441b
|19=>0x110642c01110642c010b0942c01020f41801051f42c3c06006e4018606c2c09058d42c3f060055c03500642c27a7004100b0b0642c90020f81801590b5581b050042c93020f818010409410010b064243d060042c25059642c03050642c3d0b09c18013711014190b0040855050f818010400c2c19d20f418010b02c14cd0b1b008190b184083d06004143d050f81801
|20=>0x400642401050f418010b007483e060042c0b290f0142d060053017051142c011106c14190b0042c3e0600400190b0242c190b18c083d0511414190b0051c010409c2c19050b414120b0642c190b0f800191a02c44190b0042c190b0f00019050442c030b0642c19500042c270b5302c09020042651090f818010b15c143e060074801060042c0b370bc141905004682f
|21=>0x6004247f0b0f018011209c143d06004143d050b418011a0bc44190b0041445060042c01120bcdc01050642c190b0242c01860fc18010b0246803110642c0105244083e06004482c370041419290f8142d06004083d000642c194c02c14450b004441b0b0042419210042c252902c142d060077403d20642c0b2f02c441b0b005a419ae004142e8d0242c3f060042d52
|22=>0xb06e343d0b0fc1801e2004dc2c0506418010b06424010b0f40019090642c012902c142d0b154143e06004440b060042c015606c142d05004bc251106c2c01500f42c27060055812050042c190bc7488030906444190b00444190b004147f0b0f01801500f82c2706004bc091106c2c010b4081801090042c09020f418010b244083e06004180109ae4142e0b0042c27
|23=>0x50b418010b549001909007a02e3700c14191e00414110b06410270b0642c250b150143e060042c3e0600444250b0042419ae0f4142e06004681b0b0f400191106c14190b004680b0b0f41801120b8143d060046c030b0240819051182c018c00eb819050b82c3d060042c25560bc14010b0642c3e050b81801020f818010b00411010b0642c190b0040819e402c16c1
|24=>0x60042c3e050b41801090f42c3d060042c57050f818010b24c083e06007483d060042c0b1209cdc0105064a40b050b418011109c2c014d00484190b0942c250b0642401020f8083d06006b83e050b818010a1f42c3c060047803050442c19021fc2c3c06004d4270b40424010b004100b0b0660001050482c19021f42c3c060041801051182c010b06418010b0042c3c
|25=>0x91fc2c3c06004143d050b418010b00414110b064482f050f41801120b0143d0600444880b0042419290f8142d060042c3e06004dc45050642c018d0242c3f060042c3e060042d52090f4180109c24dc2e050641801e10642d0209004a43c050b41801091f42c3c060044427060042c01021f42c3c06004143d0b0fc18010b944243e060042c01050442c1902154143e
|26=>0x5244083e06005001909004142e0b0f818011a09c44190b006343d0b0fc1801051a444190b005301b051142c010b0f4083d0600748010b02c2c55050f81801112242c010906540190b09c0019500f42c2706004114c0b06408010b0054c1b020041411040042c19500f82c27060042c19060042c01090e42c3e060042c91020f81801050e42c3e060042c3d0b0f01801
|27=>0xb06410270b064143d0600418010b004147d0b0f01801058d42c3f06006183c060042c09090f8180106004241909004243d060042c250b0f42c27060042c57050f818011a02444190b00444190b004a43d050b418018406c2d4d02004143e0b0fc1801096142d4c02004146a110642c01050f42c3d06004147d0b0f01801290fc142d060042c3e06004843e060042c25
|28=>0xb02410250b06540010b09d001909005582f050042c6e0206410270b06414010b0642c27060040019090642c090206418010b02c143e060042c3e06005001b09004142d0b004142e06004083e060042d4f020042c890906426b9050b82c3c06005582e050042c010b09416c10b06ca40b050b484190b09414460b0042c030b0642d4c020046c030206410090b0641003
|29=>0x9064dc01050642c1902006c0090b06c24010b0954c190200414120b06414110b06418010b0242c3e060042c19020642d4d0200414010506444190b004142d05064243e060042c190b00418010b095582c050050019090042c0305066b801050b8100b0b064081902004a41b050b42c090b004441b0b00658190b00c2c19090042c3f06004142d06004a40b050b61803
|30=>0x142d0b09c2c0b050b81419060042c01020042c090b06c2c2509004083d0600415410b09c2c3d060042c270b004243e06004143e0600414110b064241909004243d0600748010b02c083e060042c3c060042c3f06005581b0500444190b004100b0b0642c190b0042c8a
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x584000014d40000000000013d000004e100000000000000000001290000046408480f5400000000000000000003a306c80ccc17a02a504aa0000000021403a806140a200000000044c0628000010801100000004000000000000000
|7,0=>0x21a4425082a10321fe83ed07c9000000003d8c79200001dc800007520e641c4837906d20d731a6833d065a000018e830d06018bc417442d905a88b1415a8000054a0a54142827504d1896412482390459889210a8000040a07f20f6800003ba07520e46000037986c300001a4c00006630c4800002f985c3
|7,1=>0x37646dd0d9a1af400006b0cd421a4434266750cd1997300006584c9218f300000000000000031866210c2218042f885e10ba997142de45b0cb5116642c6657d0ae900000000000000015b22b245550aa0951329c65290a398000286800009fa13b426e84d0c98212d32528498c91991f4236845d089a10f4
|7,2=>0x4c2897c800025c34b089511289a4d44928915120a23e347a28e8d1c1000046888c11162000000008a111220000440887890d9a18342a6845107180004148819000020243fe67f48fd19f7300007d0c0001f133dc60000f611e933ca8788c0001de43b6675d0eb09d2439c87290e399c5238286fc80001bd2
|7,3=>0x6108c1898122fe45f66bdd179a2ef45d86ba117222e045b88b6116a22d1359a8b251631ac330000afd15f080000000ae915c12b440000ac11569aa9454c6a89000029f35368a5d000000005268a3d1461a89350a8a08d3f227a400009d9139200004e22000136a00000000000134a2654
|7,4=>0xc8118e2318462880001889b0e3000000018610000
|8,0=>0x7b44f609ea9bd2379e6f30de513c737886f04ddf1bbb37706ed89d99bb0375a6ea8dd39ba437426e78dcd9b98372a6e48dc79b8c37126e18dc19b8036fa6de8dbb9b7436e26db8db59b6836cc4d8cdb01b5d36b46d5cdaa1b51369c6d2cda4934636866d00d9e9b3a366e6cd0d998b30365a6ca8d939b243
|8,1=>0x9207234e451c87390a5208e3f9c7c38f271d8e399c7038da71a8e339c6528c4717ce2e1c5a28ae7150e29144f38987124e231c43388070f4e1d1c37386870c4e171c2b38507094e111c20283a7068e0b9c1438227038e059c08380a7008dff9bfc37f26fd8df99bf037dc4fb45f51be737ca4f88def9bdc3
|8,2=>0xa9a7528ea39d443a8274f8e9d9d383a6a74c8e979d2d2a5474a0a929d223a3e7470e8c9d163a267440e869d0a3a0e7410e809cfe39f673e0e7a9cf239de73b0e749ce639c67380e6e9cda39ae7350e689cce39985324e631cc3398072f4e5d1cb7396872c4e571cab39507294e511c9f39387264e4b1c933
|8,3=>0xc087804eff1dfb3bf077d4ef91def3bda57a8ef39de43bc27778eed9dd83bac574cee81dcd3b94771cee295c23b7e76f0edc9db63b6676c0ed69daa3b4e7690ed09d9e3b367664acb95943b227638ec59d883b0a60002c11d7f3af875e4ebb1d733ae075b4eb51d673ac87584eaf1d5b3ab07554ea995503
|8,4=>0xd7a7aecb5c1eb53d647abcf561ea93d4e5a90f509e9e3d367a60f4a9e923d1e7a30f449e863d067a00f3e9e7a3cee79d0f389e6e3cd679a4b331e633cc25978f2d9e5a1cae7950f289e4e3c967920f229e423c7e78f0f1c9e363c6678c0f169e2a3c505894f111e1f3c387864f0b1e133c207834f051e073
|8,5=>0xdec7bccf781eee2dd67ba0f729ee23dbe7b74b6d1ed73da87b44f671ecb3d907b14f6196c03
|9,0=>0xeee5dd4bb997712ede5db4bb597692ece5d94bb197612ebe5d74bad97592eae5d54ba997512e9e5d34ba597492e8e5d14ba197412e7e5cf4b9d97392e6e5cd4b9997312e5e5cb4b9597292e4e5c94b9197212e3e5c74b8d97192e2e5c54b8997112e1e5c34b8597092e0e5c14b8197012dfe5bf4b7d96f92
|9,1=>0x7a12f3e5e74bcd97992f2e5e54bc997912f1e5e34bc597892f0e5e14bc197812efe5df4bbd97792
|10,0=>0xf5c3eb47d60fab1f543ea47d40fa71f4c3e947d20fa31
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x180000000402000000abc0000028f000000a2400000286000000a08000002800000009200000010700000041400000102000000400000000f00000002c40000008800000021800000084000000204000000800000000800000000c0000000280000000800000001c000000060000000140000000400000000c0000000200000000400000000
|1=>0x780980001e0240000482dc000120200000400100000c0020000200000000602400001808000002226000008098000020240000080880000202000000800800002001000005a10000012860000048340000120600000480000001084000004020000010050000040080000100000000200400000800000001a080000068000000182400000604
|2=>0x40043c0010010700040041800100100000400018001000020004000040010000000030040c000809010002004000008000000018051800060107000180210000600070001800100006000200018000000041680000100ac40004008600010021000040007000100010000400000000a00800002202600008201c00020801000080a0000020004
|3=>0x80040000200088000800210002000070008000100020000200070042c001809070006006fc0018010f0006004180018010500060001000160000000508ff4001402b50005006fc00140000000480bcc001201bf00048041800120006000480010001122b7000440adc0010a2b7000408adc00100806000402000001002bf000400abc001001bf
|4=>0x1e006fc0070000f001a0025c005801bf00160043c005801060016004100058000500150041c00500906001402408005001bf00140040c004c00000012004180042000000100200800400002000e0027c0031e2b7000c08adc003020b7000c012bc003002af000c006fc00300106000c00400003000000009000140020222400080422000200282
|5=>0x40080980100202400400800001001387004004a08010003a7004000a3c01000284004000a000100025700400082401000207004000804010000b500400023001000088004000218010000840040000880100000c0040000180100000500400001001000000002500abc009002af002080a0800801286002004a100080108600200080000800004
|6=>0x440823c011012ce004404abc0110128f00440265c01100902004400ffc011003bf004400edc011003a7004400bdc011002bf004400adc011002af004400a3c011001bf004400410011001000044002fc011000b7004400018010601070041802100106000400410841c0104028f0041002dc010400070040880980101a0b70040682c401006024
|7=>0x460005c011621a7004580adc011602af0045802fc0116000f004504abc011402bf004500adc011402b5004500abc011400bf00450029c011223bf004488adc011208a7004480adc011202af0044806fc0112019d0044802fc0112001700448003c011122b7004410adc011032870044092bc011023bf004408adc011021b700440869c011020af
|8=>0x548005c015009bf00540245c015001bf00540067c0150010200540005c01400000004d0869c01342107004c8879c013061a7004c10efc013040a7004c0c69c013021e7004c0869c013000a700491001c0120400700480841c0120202400480041c012001000048002100120002400480001c011c00bf00470005c011809bf00460267c011801bf
|9=>0xc40227c0310080400c4006fc0304000700c0024000258010500890001c0218010f00860041c02180106008600410021009bf00840241002100902008402018021008000084006fc0210010000820041802080105008200010020400030080024100200080400800200402000001006404abc01800000005e004180158019f005600418015209bf
|10=>0x400200981000222704000809810002022040008018100002040400000101000000204000000008000208014448adc0510a2b7014408adc051002b70140482dc0500a0b7014008adc05000017010448adc0410a2b7010408adc041020b7010400adc0401c024010068a5c040020260100080080400000400cc02410031403bf00c50067c03100904
|11=>0x82004288208002af082000210201004af080400afc201002af080004abc2000128408000429020001084080000abc200002840800002182000008408000001820000004054410adc151022b7054400adc140002b7044c0869c1110a2b7044408adc111021af044400adc11002237044008088101002b7040048098100120240400400981000a026
|12=>0x10680023841800086104484abc40b002af102400a9c4080008e102000230401002af100100a1840021286100004a184000060610000083c4000020010000021840000000086400afc219002af084404afc211012af084404a34211006af084400afc211002af084004a182100060008400080421000200082400afc209002af082004a182080120b
|13=>0x8044042de01101037800400a9d801020376004002bca11030af206409abc811030b72044082bc8110208f184404afc611002af1824002106080028c1820008bc601020af180400afc601002af
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x400028000000018001300000000000008000401048000000000000202020100a05000000603054440000008220003018000c000000000
|7,0=>0x808c062c00030021702024080409aa2740c000000000060062c018a94866b497030b00f1daf0dc2600000007b5e815248e0601666000291834b20181002040b0300801151652659149b41d92348040800000100200008003836afab96c023a1c1584d5f9784e065097eae0e3a8e5521e18a90200302bfc085c1e8033402c29184a4050000041400010012493000b00c
|7,1=>0x2e8100c5a0216c020502005bc9a2b398a00203804100c00578260000006560a002cc180d22ab0000405004000000908080493d5854c10006c02002a0029c0000002b62810aa0004f55cb00cf6258140c722a82cc600388040200002c8020055160f614010c008005a80c00ad0201008040056000029aa40f41f01c60005b2c01ca853009640808019604818
|7,2=>0xfe4e0100800080c000015000
|8,0=>0x2b9f2ec5d1e3714eda96a2b30cfd8515ee184334d2a37354f80588a5b4ef373d13f2337e95261322e63ba4ca0c3b46cd7238619e1f3fcfa6d993c21a1acd0d27641a4bb2c31dcad21913d3d91ba0ea50b9691b24a0fb08ad994f87e10ca0f6dd1a5f09a5c6a879744ab8cd67b665894d5528e3125b2c61d879b3bd692b1d948cc9880bfd058c9169e2872f546cf6c182
|8,1=>0x24b5054ce695e9d8d240cd9928307af9594fb83ba81715ca08c7507043da4789937ef4bec41bdf77d4a0c864d266d8cf148a4935750366697104851deabb442452b117a616ac6538bbbbdc6516998332d36ee003a85b2813026ac5aac6af217c7ea49d69316eac4988fa23645c3ac88d35334cc899c4322e77c20bf75559d1d71a4d96645cd168b14e52d37571ce167d
|8,2=>0x71376cf084e489f58632cc05b4d1035cc2b0693756e60d74ed52608286d44c027c1d1eea643a2a21965b850f0a443299ba4cae795ed0bc21326343f485ac7f3bdc9ac9769ac50f94d6b459d07833235fa823cd2034755c4340d33cafef56b
|9,0=>0x8cd8c3a0887bde75389f7bd2db10fc1bcde2fe8e5eeab6e8052f13a7b7c4aa955bdb6312876a341a89cd33e2a74bc6da684f28136319a9b6c81e89cc7d51db8e66a52a6e74444ceef96922da71e6b451a93dc6eb23cf57934e996a783b738d8
|10,0=>0xc6b35a6d4d0989b14db6b91a077
|11,0=>0x62
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 34 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_243 10 roots_243 ops++addP pm 1 dom_119 9 roots_119 ops++addP pm 2 dom_183 9 roots_183 ops++addP pm 3 dom_213 8 roots_213 ops++addP pm 4 dom_244 8 roots_244 ops++addP pm 5 dom_246 9 roots_246 ops++addP pm 6 dom_227 7 roots_227 ops++addP pm 7 dom_215 9 roots_215 ops++addP pm 8 dom_229 7 roots_229 ops++addP pm 9 dom_214 8 roots_214 ops++addP pm 10 dzo_198_1 5 roots_198 ops++addP pm 11 dom_165 4 roots_165 ops++addP pm 12 dom_198 5 roots_198 ops++addP pm 13 dzo_230_1 6 roots_230 ops++addP pm 14 dom_54 4 roots_54 ops++addP pm 15 dom_182 6 roots_182 ops++addP pm 16 dom_118 6 roots_118 ops++addP pm 17 dom_167 5 roots_167 ops++addP pm 18 dom_103 5 roots_103 ops++addP pm 19 dom_117 6 roots_117 ops++addP pm 20 dom_245 9 roots_245 ops++addP pm 21 dom_55 5 roots_55 ops++addP pm 22 dom_181 6 roots_181 ops++addP pm 23 dom_87 6 roots_87 ops++addP pm 24 dom_231 8 roots_231 ops++addP pm 25 dom_101 4 roots_101 ops++addP pm 26 dzo_246_1 7 roots_246 ops++addP pm 27 dzo_211_32 6 roots_211 ops++addP pm 28 dom_230 6 roots_230 ops++addP pm 29 dzo_215_32 7 roots_215 ops++addP pm 30 dom_151 6 roots_151 ops++addP pm 31 dzo_214_32 6 roots_214 ops++addP pm 32 dzo_214_1 6 roots_214 ops++addP pm 33 dzo_213_32 6 roots_213 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_247 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_198_1_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_230_1_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_246_1_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_211_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_215_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_214_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_214_1_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_213_32_208 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_243 10 s (0,roots_243.map (·&&&dom_243)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_247 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_243 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_247==dom_247)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_247 gM v ys):RunD true dom_247 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_247 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 53 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 53 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 267 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 11 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 267 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 340 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 84 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 340 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 85 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 85 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 12 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 12 0 = true)
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
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,10),(8,40),(8,72),(8,136),(16,17),(16,80),(16,144),(18,19),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(48,49),(48,50),(48,56),(48,112),(48,176),(64,66),(64,72),(64,80),(64,192),(65,67),(65,73),(65,81),(65,97),(65,193),(96,97),(96,98),(96,104),(96,112),(96,224),(128,130),(128,136),(128,144),(128,192),(129,131),(129,137),(129,145),(129,161),(129,193),(160,161),(160,162),(160,168),(160,176),(160,224)]
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
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)]]
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
def dzo_252_1:=0x2222222222222222222222222222222222222222222222222222222222222222
def gzo_252_1:=0x2222222222222222222222222222222022222222222222202222222222222200
def gsh_252_1:=0x1111111111111111111111111111111011111111111111101111111111111100
theorem lowS_zo_252_1_196:Lower true dzo_252_1 roots_252 gzo_252_1 7:=lower_iso_b (d1:=dom_252) (r1:=roots_252) (T1:=gsh_252_1) [(dom_252,1)] (by decide +kernel) (lower_slice_b (T:=gsh_252_1) [(0x1100110011001100110011001100110011001100110011001100110011001100,0,8),(0x1111000011110000111100001111000011110000111100001111000011110000,0,16),(0x1111111100000000111111110000000011111111000000001111111100000000,0,32)] (by decide +kernel) lowS_196)
def dzo_236_1:=0x222200002222000022220000222200002222000022220000222200002222
def gzo_236_1:=0x222200002222000022220000222000002222000022200000222200002200
def gsh_236_1:=0x111100001111000011110000111000001111000011100000111100001100
theorem lowS_zo_236_1_196:Lower true dzo_236_1 roots_236 gzo_236_1 6:=lower_iso_b (d1:=dom_236) (r1:=roots_236) (T1:=gsh_236_1) [(dom_236,1)] (by decide +kernel) (lower_slice_b (T:=gsh_236_1) [(0x110000001100000011000000110000001100000011000000110000001100,0,8),(0x111100000000000011110000000000001111000000000000111100000000,0,32)] (by decide +kernel) lowS_196)
def dzo_221_32:=0x3333333300000000333333330000000033333333000000003333333300000000
def gzo_221_32:=0x3333333300000000333333320000000033333332000000003332333200000000
def gsh_221_32:=0x33333333000000003333333200000000333333320000000033323332
theorem lowS_zo_221_32_208:Lower true dzo_221_32 roots_221 gzo_221_32 7:=lower_iso_b (d1:=dom_221) (r1:=roots_221) (T1:=gsh_221_32) [(dom_221,32)] (by decide +kernel) (lower_slice_b (T:=gsh_221_32) [(0x22222222000000002222222200000000222222220000000022222222,0,1),(0x30303030000000003030303000000000303030300000000030303030,0,4),(0x33003300000000003300330000000000330033000000000033003300,0,8)] (by decide +kernel) lowS_208)
def dzo_217_32:=0x303030300000000030303030000000003030303000000000303030300000000
def gzo_217_32:=0x303030300000000030303020000000003030302000000000302030200000000
def gsh_217_32:=0x3030303000000000303030200000000030303020000000003020302
theorem lowS_zo_217_32_208:Lower true dzo_217_32 roots_217 gzo_217_32 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_32) [(dom_217,32)] (by decide +kernel) (lower_slice_b (T:=gsh_217_32) [(0x2020202000000000202020200000000020202020000000002020202,0,1),(0x3000300000000000300030000000000030003000000000003000300,0,8)] (by decide +kernel) lowS_208)
def dzo_220_32:=0x1111111100000000111111110000000011111111000000001111111100000000
def gzo_220_32:=0x1111111100000000111111100000000011111110000000001110111000000000
def gsh_220_32:=0x11111111000000001111111000000000111111100000000011101110
theorem lowS_zo_220_32_208:Lower true dzo_220_32 roots_220 gzo_220_32 6:=lower_iso_b (d1:=dom_220) (r1:=roots_220) (T1:=gsh_220_32) [(dom_220,32)] (by decide +kernel) (lower_slice_b (T:=gsh_220_32) [(0x10101010000000001010101000000000101010100000000010101010,0,4),(0x11001100000000001100110000000000110011000000000011001100,0,8)] (by decide +kernel) lowS_208)
def dzo_220_1:=0x22222222000000002222222200000000222222220000000022222222
def gzo_220_1:=0x22222222000000002222222000000000222222200000000022222200
def gsh_220_1:=0x11111111000000001111111000000000111111100000000011111100
theorem lowS_zo_220_1_196:Lower true dzo_220_1 roots_220 gzo_220_1 6:=lower_iso_b (d1:=dom_220) (r1:=roots_220) (T1:=gsh_220_1) [(dom_220,1)] (by decide +kernel) (lower_slice_b (T:=gsh_220_1) [(0x11001100000000001100110000000000110011000000000011001100,0,8),(0x11110000000000001111000000000000111100000000000011110000,0,16)] (by decide +kernel) lowS_196)
namespace S_253
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(4,20),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,40),(8,72),(8,136),(12,13),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(24,25),(24,28),(24,56),(24,88),(24,152),(32,33),(32,36),(32,40),(48,49),(48,52),(48,56),(48,112),(48,176),(64,68),(64,72),(64,80),(64,192),(65,69),(65,73),(65,81),(65,97),(65,193),(96,97),(96,100),(96,104),(96,112),(96,224),(128,132),(128,136),(128,144),(128,192),(129,133),(129,137),(129,145),(129,161),(129,193),(160,161),(160,164),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
def xsM:=roots_253.map (·&&&dom_253)
def gM:=goal_253&&&dom_253
def NN:Nat→Nat
|7=>12
|8=>63
|9=>42
|10=>8
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x790f46d3aa688a067bd35d2314a989475b815cc61394b0e4030c7900b10d
|8,0=>0xba5f3b587f9db7e9cc879684a89b408863378f4d74a216e35e67dc664044621ed6117b60df85efa354cea53bfe5285e4f1104d0d84b88749f5f47cc04780d46fc244a9e3a50436194360ad31e1f30d182d2762be1d2b8402b56d29bcd29216292052528022f3520f971f7521c232199d8178ad17176157e013d3412b0a0df060cff60bfb20b5ea0af66097f907fd007236036ec02af80275500b94004b3
|9,0=>0xdcc75bafbb8310d7e5b879921798947799f6578e63001610fb60fdf5cd1f548a052861506e44d23d4aa9a4963246b313ce373a9d8386bf35f8632d0929eea29dfc252ec201c21b1231abe0186c813b71131de11d850ffe30e32506fe8059bd0559a020b201ee90021e
|10,0=>0x7a07a79b4e7762c4706326091206101e31b0b254
|11,0=>0x1e31b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xccccccccccccccccc0c0c0c0c0c0c0c0ccccccccccccccccc0c0c0c0c0c0c0c3333333333333333333033303330333033333333333333333330333033303330ccccccccccccccccccccccccccccccccc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c3333333333333333333333333333333333303330333033303330333033303330cccccccccccccccccc00cc00cc00cc00cccccccccccccccccc00cc00cc00cc03030303030303030303030303030303030303030303030303030303030303030cccccccccccccccccccccccccccccccccccccccccccccccc0000000000000003300330033003300330033003300330033003300330033003300330033003300cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000003333000033330000333300003333000033330000333300003333000033330000ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc33333333333333333333333333333333330033003300330033003300330033008888888888888888888888888888888888888888888888888888888888888888303030303030303030303030303030303030303030303030300030003000300cccccccccccccccc0000000000000000cccccccccccccccc0000000000000003333333333333333333333333333333300000000000000000000000000000000
|0,1=>0xcccccccccccccccccccccccccccccccccccccccccccccccc888888888888888b3333333333333333333333333333333030303030303030303000300030003000c0c0c0c0c0c0c0c0c000c000c000c000c0c0c0c0c0c0c0c0c000c000c000c00000000000000000333333333333333300000000000000003300330033003300cccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000000000000000000000000000000000033333333333333333333000033330000cccccccccccccccccccccccccccccccccccccccccccccccccc00cc00cc00cc00303030303030303030303030303030303030303030303030303030303030000cccccccccccccccccccccccccccccccccccccccccccccccccccccc00cccccc00000333300003333000033330000333300003333000033330000330000003300cccccc00cccccc00cccccc00cccccc00cccccc00cccccc00cccccc00cccccc00303030303030303030303030303030303000300030003000300030003000300cccccccccccccccccccc0000cccc0000cccccccccccccccccccc0000cccc0003333333333333333333333003333330033333333333333333333330033333300cccccccccccccccccccccccccccccccccccc0000cccc0000cccc0000cccc0003333333333333333333333333333333333333333333333333333333300000000
|0,2=>0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc0000000333333333333000033333333333300003333333333330000333333333333000000000000000000000000000000000000cccccccccccccccccccccccc00000000000000000000000000000000000000033332222333322223333222233332222cccccccccccccccc8888888888888888cccccccccccccccc88888888888888880003333000033330000333300003333000033330000333300000000000000008888cccc8888cccc8888cccc8888cccc8888cccc8888cccc888888888888888b232323232323232323232323232323232323232323232323232323232323232cccc0000cccc0000cccccccccccccccccccc0000cccc0000cccc8888cccc8889111111111111111111111111111111111111111111111110000000000000000cccccccc44444444cccccccc44444444cccccccc44444444cccccccc00000000000000000000000000000000000000000003333000033330000330000003300cccccccccccccccccccccccccccccccc8888888888888888888888888888888b3332222333322223333222233332222333322223333222233332222333322220000000000000000cccccccccccccccc0000000000000000888888888888888b333333333333333333333333333333333333333333333333330333033303330
|0,3=>0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ccccccccccccccccc8c8c8c8c8c8c8c8303030303030303030303030303030303030303030303030202020202020202cccccccc0000cccccccccccc0000cccccccccccc0000cccccccccccc00000003333333330303030333333333030303033333333303030303333333330303030000000000000000000000000000000000000000000000000ccccccccc0c0c0c33333333333333333333333333333333333333003333330033333300333333000000000000000000cccccccccccccccc0000000000000000ccc0ccc0ccc0ccc3333333333333333323232323232323233333333333333333232323232323232cccccccccccccccccccccccccccc0000cccccccccccccccccccccccccccc00000000000000000000000000000000000333333333333333333333333333300000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000000000000000330333033303330333033303330333033303330333033303330033003300330000000000000000000000000000000000ccccccccccccccccc0c0c0c0c0c0c0c33333333000000003333333300000000333333333333333333333333303030300000cccc0000cccc0000cccc000000000000cccc0000cccc0000cccc00000003333333333333333333333333333333300003333000033330000333300000000
|0,4=>0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc000088880000888b333333333333333333333333333333333333333333333333030303030303030ccccccccccccccccccccccccccccccccccccccccccccccccc8c8c8c8c8c8c8c8000000000000000333333333333333300000000000000003030303030303030cc00cc00cc00cc00cccccccccccccccccc00cc00cc00cc00ccc0ccc0ccc0ccc33333333000000003333333300000000333333333333333333333333333300000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c08080808080808080808080808080808000000000000000000000000000000000003333000033330000222200002222cccccccccccccccccccccccccccccccccccccccccccccccccccc0000cccc0003333333333333333333333333333333333333333333333333333222233332222ccccccccccccccccccccccccccccccccccccccccc0c0c0c0ccccccccc0c0c0c0000000000000000333333333333333300000000000000003333333330303030000000000000000000000000000000000000cccc0000cccc0000cccc00000003030303030303030333333333333333330303030303030303330333033303330cccccccccccccccc0000000000000000cccccccccccccccccccc8888cccc8888000000000000000000000000000000033333333333333332222222222222222
|0,5=>0xcccccccccccccccccc00cc00cc00cc0111111111111111110101010101010101111111111111111101010101010101000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc0000000000000003333333333333333333322223333222233333333333333333333222233332222cccccccccccccccccccccccccccccccccccc8888cccc8888cccc8888cccc888b3333333333333333333333333333333333333333333000033333333333300000000cccc0000cccc00008888000088880000cccc0000cccc00008888000088880330033003300330033003300330033003300000033000000330000003300004444444444444444444444444444444444440000444400004444000044440000000000000000000333322223333222200000000000000003333222233332222
|_,_=>0
def sP:Nat→Nat
|0=>0x1c1050302003861c206830200386082819d02003950c705030200d87341840a06043860a641820200386100cc01001c90608281890e5c40a06580800e1860806080800e54984140c4870c2c503282439222205031240386103c6830e1870b10341890e1860b08281890e182840608080
|1=>0x10281960200d870c2078d060438610281b0020172d0c2050302003ac0c2052b02003861029483020038610a051f02003a70c205030200395262050312012861028181001c308140d201001d1061029081001c320082050302003910c2051f06043950c645030200386102819e0200386
|2=>0xe1840a06504810e185881a28189761c308140c0800ee83041028189021ca86322c50302003860a2c50312003920c2050312003861c2c40d06040070ce440a06040070c30584140c0800e18438148c0800e1900c102818100d83861028181001c334102818100c83861028181001c319
|3=>0xe1840a07200800e18288660c0800e1840f1a0c4870c205032c040078c1840a06040440e1840a0604007261840a800c02e0e2050302a80070c2050386040070d0840a06040070c30c88140c0800f04308140c0800e88308147c0800e1843f140c0800e1840a06f80807a1c308140c080
|4=>0x162050302003930c2052b060038610281d102003d00c2050302003910c2c40a06040070c8040a06040070c205039e040070c2c20a06243860a2270302003861134503020038616205032c040070d2c40a06040070c80c88140c080941c308140c0800e1840a57240800e54984140c080
|5=>0x1c31910281890201787221840a06040070c2050302d40100e1840a06040070c2078a06240070c1440a06240800e1840a074c0800e182881e0c0800e1840a06500805a1c308140c0800e1828b140c0800e48308140c0800ee83041028181001c3087028181001c308140e901001c319
|6=>0x1028181001c3591028181001c308140ec01001c30b1028189001c3085029181001c308140c0d7001e3861028181001c308662818100bcd861028181001eb130c205030201e2f0c20503020038610281c90201e070c205031204007aa1840a0604007261840a460c080a81c8861028181
|7=>0xe1840a0604007441840a060402f0e1840a06040070c2050312040070c2c40a06040072a1840a060402e0e1840a06040070c205030200386103c503020038632205030200386161050302008070c2050312040070c2078d060402e0e1840a06240800e1840a06053000e48986
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0x14a04b7111c3c80d202d7099c1f7061c1080220008
|8,0=>0x251892624278ea23288a66218862610882220087e21f087a5de187661d187261c186e61b186a25a08662190862218085e217085a215f955a54e851a13d94d612c949211b944e10b840e0fa93ca0ea838a0da834a0ca830a0ba82cdcab828e09a924a08a820a07a81ca06a818a05a8
|9,0=>0xeba3a68e767958e327848dee7738dae3638d6e3538d2e3438cee3329caa3228c667118c226ff9bda6ed9b962dd8b562cc9b122bc8ad22ac8a9229c8a4e68b8a0e27a99ca26a898a2599
|10,0=>0xfb63e58f763d58f363c58ef9fb68
|11,0=>0x3f57
|_,_=>0
def wAt:=mkWire dB 90 254 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x601322908051001062500050c011025101902013a01162b10051629100510010a05102914011001162b100508071001101926030e010c051025020116190005100510012e1b26010c05080510011001101902010c05082b020110011005104d0c0500050c010e25140102011405140116291005082902011001100508051001
|1=>0x100510290005104d02010c05140116291005180710351401082910011005063d06011405103514016e03261d0c0510d5142602010ecd1e031405321b1025020114010e01140562015e1b0e055e030e190e05060544030c0d06a90c260201062906250201421946070601101902010c050e9906260201222e10050c0106194607
|2=>0xc0522ae06050c011e0310291405140102011405321b102502018e0d26010c058a077801141d0c05560306050c260c1d02015e470e050c01382908071001082908051001580544030c0d0619062502018029560306053e2b062502010ea90c2602010201082b100110050005140178270201141d020108191001101916011005
|3=>0x2010201140510290201561b060510291405082b10015e030e0510051029104d0c05081910011e0d140510460c011601100506050c0506460c0144070c0d10050c019c211e0114053e1b0625020102011001100514211e011405563506051401321b1601100511311a07140110250201341d26030c050605462b060110011019
|4=>0xc0d0e050201100510190c1d140510250201100110050e250201140114050c1d020106260201104d0c05160310051e0f140510050005062906011026020126010c051e0314050e010e05064d0c050e05141d462b06010201141d44010c0d06010c05221d0c01102502010e050c01142602010e25
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x11100003c81b30c905502280d404a018c048002
|8,0=>0x370db26d63699b40d9a6ca3641314d846bf35e1ae4d6c6b33581ab4d546a73521a84d3c69b34c1a54d2468f3461a24d0c68334019f4cf467733a19c4cdc66c2349998cc666032e9968cae6543289938c966483229908c7e63c31c98d8c6663031698a8c4e6243
|9,0=>0x26252f29694aca52527292948ca4251f28e946ca3251728a944ca2250f286942ca12507282940ca024ff27e93ec9f24f727a93cc9e24ef27693ac9d24e7272938c9c24df2
|10,0=>0x9c8ce066e33619a8cd04001331
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 13
def pmP:Nat→Nat
|0=>0xb057fc00002811fc000009343f00000249cfe000009257fc0000245d6f000009175b80000245d4f000009151bc000024346f000009075bc0000241c7e000009071bc000024156f000009051fc000024146f0000090410c0000205908000008081080000200e6a000006201000000074423000000322d00000005048000000141000000002002000000046f00000000e6a00000000c2000000001fc000000000080000000000
|1=>0x189159bc000624166f000128159bc0004a0456a000119151bc000464166f000118155b8000424dd6f0001093753c000424d56f000109351bc000324106f0000c9040b4000324006f0000c9000bc000225146b000089151bc000224546b000089151a0000224506f000089059bc000224166b000089053ac00022414a9000089051bc0000e0280a000038021080000a4146f000028015b8000064156f000018059bc000040034a
|2=>0x200c9041bc080224106f012889243bc040324106f010089041bc0244a6062b009089051bc0142241469004089351ac010224146f0028c9243bc00a324106f002089041bc00812410ad001089451bc004224146f001089051ac002224106f0005090d1bc001420200000050008008001400024000041801db8001060076a0002c9041bc000b24002f0001c9341bc000724126f0001a9159bc0006a4166f000189f512c000624d46f
|3=>0x2008b24126f409089d51bc804624546b200089051ac410226946b101089651ac400324906f100089353bc4000341c7f10000c06140400024956f100009251bc300020106f022809140b408232490ef
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x20028b0c24202140d281
|8,0=>0x135a387ad042496a589ca6861909d3e92d604c6db674da2e18f35e51ce4f202c9a34c9e5d507b4c2c3358caf1dc4499cac264949908ca28
|9,0=>0xd15830abc5364a2368ed73abb37685fd8d306a6fa57ed7eeea3a274511fcdbb198aba2e64
|10,0=>0xb94601223587be
|11,0=>0x27
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 42 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_252 9 roots_252 ops++addP pm 1 dom_249 9 roots_249 ops++addP pm 2 dom_244 8 roots_244 ops++addP pm 3 dom_125 9 roots_125 ops++addP pm 4 dom_229 7 roots_229 ops++addP pm 5 dom_233 8 roots_233 ops++addP pm 6 dom_245 9 roots_245 ops++addP pm 7 dom_173 6 roots_173 ops++addP pm 8 dom_181 6 roots_181 ops++addP pm 9 dom_185 6 roots_185 ops++addP pm 10 dom_213 8 roots_213 ops++addP pm 11 dom_117 6 roots_117 ops++addP pm 12 dom_237 9 roots_237 ops++addP pm 13 dom_113 4 roots_113 ops++addP pm 14 dom_61 6 roots_61 ops++addP pm 15 dom_45 5 roots_45 ops++addP pm 16 dom_157 6 roots_157 ops++addP pm 17 dom_93 6 roots_93 ops++addP pm 18 dom_221 9 roots_221 ops++addP pm 19 dom_165 4 roots_165 ops++addP pm 20 dom_101 4 roots_101 ops++addP pm 21 dom_189 9 roots_189 ops++addP pm 22 dom_241 7 roots_241 ops++addP pm 23 dom_121 6 roots_121 ops++addP pm 24 dzo_252_1 7 roots_252 ops++addP pm 25 dom_220 8 roots_220 ops++addP pm 26 dom_57 5 roots_57 ops++addP pm 27 dom_248 7 roots_248 ops++addP pm 28 dom_177 4 roots_177 ops++addP pm 29 dzo_236_1 6 roots_236 ops++addP pm 30 dzo_221_32 7 roots_221 ops++addP pm 31 dom_188 6 roots_188 ops++addP pm 32 dom_205 7 roots_205 ops++addP pm 33 dzo_217_32 6 roots_217 ops++addP pm 34 dom_236 6 roots_236 ops++addP pm 35 dom_124 6 roots_124 ops++addP pm 36 dzo_220_32 6 roots_220 ops++addP pm 37 dzo_220_1 6 roots_220 ops++addP pm 38 dom_109 6 roots_109 ops++addP pm 39 dom_217 6 roots_217 ops++addP pm 40 dom_29 4 roots_29 ops++addP pm 41 dom_184 4 roots_184 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_252_1_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_236_1_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_221_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_217_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_220_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_220_1_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_184 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 9 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffffffffffffffff0000000000000000,64),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_253==dom_253)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_253 gM v ys):RunD true dom_253 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_253 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 12 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 63 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 63 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 42 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 42 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
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
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=lower_slice_b [(0x5555555500000000555555550000000055555555000000005555555500000000,2,34)] (by decide +kernel) lowS_222
def isoMvS_191:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_iso_b isoMvS_191 (by decide +kernel) lowS_127
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,40),(8,72),(8,136),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,36),(32,40),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,68),(64,72),(64,80),(64,192),(65,67),(65,69),(65,73),(65,81),(65,97),(65,193),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,130),(128,132),(128,136),(128,144),(128,192),(129,131),(129,133),(129,137),(129,145),(129,161),(129,193),(160,161),(160,162),(160,164),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|10=>1
|11=>5
|12=>2
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|10,0=>0xbec7
|11,0=>0xd2767904577369147d6c31fd2
|12,0=>0x8fd7c792e4
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffffffff0000ffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x7943218a76943218a79432108a76543218a7c943218a7b6943218a7b943218a75943210876543210
|_=>0
def sO:Nat→Nat→Nat
|10,0=>8
|11,0=>0x2d94926a88c889
|12,0=>0x1fcb69
|13,0=>0x488
|_,_=>0
def wAt:=mkWire dB 13 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2618a669985ab985a9986418a6698a6299a661
|_=>0
def oO:Nat→Nat→Nat
|10,0=>3
|11,0=>0xb292725232
|12,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x1fff7fcff7fe7fc7f800
|_=>0
def pmB:Nat→Nat→Nat
|10,0=>1
|11,0=>0x35b5
|12,0=>0x14
|13,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 11 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_253 12 roots_253 ops++addP pm 2 dom_251 12 roots_251 ops++addP pm 3 dom_247 12 roots_247 ops++addP pm 4 dom_239 11 roots_239 ops++addP pm 5 dom_191 11 roots_191 ops++addP pm 6 dom_127 11 roots_127 ops++addP pm 7 dom_223 12 roots_223 ops++addP pm 8 dom_175 8 roots_175 ops++addP pm 9 dom_111 8 roots_111 ops++addP pm 10 dom_63 9 roots_63 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_63 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 5 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 2 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 2 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [2, 1] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [3, 8] }, { op := GateOp.or, inputs := [3, 5] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [13, 12] }, { op := GateOp.or, inputs := [12, 5] }, { op := GateOp.and, inputs := [15, 10] }, { op := GateOp.and, inputs := [11, 9] }, { op := GateOp.and, inputs := [4, 14] }, { op := GateOp.and, inputs := [6, 7] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52576_aux

theorem PEqualNP.Outside.L_meta_52576 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52576_aux.main
