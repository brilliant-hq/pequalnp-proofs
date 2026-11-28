import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52250_aux
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

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xfcfcfcfccc00cc00fcfcfcfccc00cc00fcfcfcfccc00cc00fcfcfcfccc00cc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfefefefeee00ee00fefefefeee00ee00fefefefeee00ee00fefefefeee00ee00
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

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfafafafafafaaa00fafafafafafaaa00fafafafafafaaa00fafafafafafaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfcfcfcfcfcf0cc00fcfcfcfcfcf0cc00fcfcfcfcfcf0cc00fcfcfcfcfcf0cc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfefefefefefaee00fefefefefefaee00fefefefefefaee00fefefefefefaee00
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

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xffeeffeeffeeffeeee00ee00ee00ee00ffeeffeeffeeffeeee00ee00ee00ee00
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_81 : Nat := 0x300030000000000030003
def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffeeeeffffeeeeaaaa0000aaaa0000ffffeeeeffffeeeeaaaa0000aaaa0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xffffaaaaffffaaaafafa0000fafa0000ffffaaaaffffaaaafafa0000fafa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xffffccccffffccccf0f00000f0f00000ffffccccffffccccf0f00000f0f00000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xffffeeeeffffeeeefafa0000fafa0000ffffeeeeffffeeeefafa0000fafa0000
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
def goal_92 : Nat := 0xffffff00ffffff00f0f00000f0f00000ffffff00ffffff00f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xffffffaaffffffaafafaaa00fafaaa00ffffffaaffffffaafafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xffffffccffffffccfcf0cc00fcf0cc00ffffffccffffffccfcf0cc00fcf0cc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xffffffeeffffffeefefaee00fefaee00ffffffeeffffffeefefaee00fefaee00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfafafafaaaaaaaaafafafafa00000000fafafafaaaaaaaaafafafafa00000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfcfcfcfcccccccccfcfcfcfc00000000fcfcfcfcccccccccfcfcfcfc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefeeeeeeeeefefefefe00000000fefefefeeeeeeeeefefefefe00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffaaffaaffaaffaaaaaaaaaaaa00aa00ffaaffaaffaaffaaaaaaaaaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccffccffcccccccccccc00cc00ffccffccffccffcccccccccccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeffeeffeeeeeeeeeeee00ee00ffeeffeeffeeffeeeeeeeeeeee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffaffaaffaafafafafaaa00aa00fffafffaffaaffaafafafafaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcffccffccfcfcfcfccc00cc00fffcfffcffccffccfcfcfcfccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffeffeeffeefefefefeee00ee00fffefffeffeeffeefefefefeee00ee00
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
def goal_116 : Nat := 0xfffff0f0ffff0000f0f0f0f0f0f00000fffff0f0ffff0000f0f0f0f0f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafaffffaaaafafafafafafa0000fffffafaffffaaaafafafafafafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcffffccccfcfcfcfcf0f00000fffffcfcffffccccfcfcfcfcf0f00000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefeffffeeeefefefefefafa0000fffffefeffffeeeefefefefefafa0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffffaaaaaaaaaaaaaaaa00ffffffaaffffffaaaaaaaaaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffffcccccccccccc00cc00ffffffccffffffcccccccccccc00cc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffffeeeeeeeeeeeeaaee00ffffffeeffffffeeeeeeeeeeeeaaee00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0ffffff00f0f0f0f0f0f00000fffffff0ffffff00f0f0f0f0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffaffffffaafafafafafafaaa00fffffffaffffffaafafafafafafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcffffffccfcfcfcfcfcf0cc00fffffffcffffffccfcfcfcfcfcf0cc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffeffffffeefefefefefefaee00fffffffeffffffeefefefefefefaee00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xeecceecceecceecceecceecceecceeccee00ee00ee00ee00ee00ee00ee00ee00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_142 : Nat := 0x555500000000000000000000000000005555
def goal_142 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfccc00cc00cc00cc00cc00cc00cc00cc00
def roots_142 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfefcfefcfefcfefcfefcfefcfefcfefcee00ee00ee00ee00ee00ee00ee00ee00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffccccffffccccffffccccffffccccaaaa0000aaaa0000aaaa0000aaaa0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

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

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffaa00ffffaa00ffffaa00ffffaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffccccffffccccffffccccffffcccccc00cc00cc00cc00cc00cc00cc00cc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffeeccffffeeccffffeeccffffeecceeaaee00eeaaee00eeaaee00eeaaee00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffaf0fffffaf0fffffaf0fffffaf0fafaaa00fafaaa00fafaaa00fafaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcf0cc00fcf0cc00fcf0cc00fcf0cc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffefcfffffefcfffffefcfffffefcfefaee00fefaee00fefaee00fefaee00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffccccccccffffffffcccccccceeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_164 : Nat := 0x110000001100000000000000000000001100000011
def goal_164 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_164 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0fafafafa00000000fafafafa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfefefefe00000000fefefefe00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffeecceeccffffffffeecceecceeeeeeeeee00ee00eeeeeeeeee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffaf0faf0fffffffffaf0faf0fafafafaaa00aa00fafafafaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffefcfefcfffffffffefcfefcfefefefeee00ee00fefefefeee00ee00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffffffccccffffffffffffcccccccccccc00000000cccccccc00000000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffccccffffffffffffcccceeeeeeeeaaaa0000eeeeeeeeaaaa0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f0f0f0f0f00000f0f0f0f0f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfefefefefafa0000fefefefefafa0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffeeccffffffffffffeecceeeeeeeeeeaaee00eeeeeeeeeeaaee00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffefcfffffffffffffefcfefefefefefaee00fefefefefefaee00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xeeeeeeeeeeeeeeeecccccccccccccccceeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfefefefefefefefefcfcfcfcfcfcfcfceeeeeeeeeeeeeeee0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffccffccffccffccccccccccccccccccffccffccffccffcccc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeeecceecceecceeccffeeffeeffeeffeeee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffafaf0faf0faf0faf0ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffcfffcfffcfffcfcfcfcfcfcfcfcfcffccffccffccffcccc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffefefcfefcfefcfefcffeeffeeffeeffeeee00ee00ee00ee00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffaaaaffffaaaaffff0000ffff0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffccccffffccccffffeeeeffffeeeeaaaa0000aaaa0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0ffff0000ffff0000f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffafafffffafafffff0f0fffff0f0ffffaaaaffffaaaafafa0000fafa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcffffccccffffccccf0f00000f0f00000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefffffcfcfffffcfcffffeeeeffffeeeefafa0000fafa0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffff00ffffff00ffff0000ffff0000ffffff00ffffff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffffaa00ffffaa00ffffffaaffffffaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffffccccffffccccffffffccffffffcccc00cc00cc00cc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffeeccffffeeccffffffeeffffffeeeeaaee00eeaaee00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffff0fffffff0fffff0f0fffff0f0ffffff00ffffff00f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffafffffffafffffaf0fffffaf0ffffffaaffffffaafafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcfffffcfcfffffcfcffffffccffffffccfcf0cc00fcf0cc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffffefcfffffefcffffffeeffffffeefefaee00fefaee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffccccccccffffffffcccccccccccccccccccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeffffffffcccccccceeeeeeeeeeeeeeeeeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffafafafafffffffff0f0f0f0fafafafaaaaaaaaafafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfcfcfcfcccccccccfcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefefffffffffcfcfcfcfefefefeeeeeeeeefefefefe00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffaa00aa00ffaaffaaffaaffaaaaaaaaaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffccccccccffccffccffccffcccccccccccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffeecceeccffeeffeeffeeffeeeeeeeeeeee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffff0fff0fffffffff0f0f0f0fff0fff0ff00ff00f0f0f0f000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffafffffffffaf0faf0fffafffaffaaffaafafafafaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcfffffffffcfcfcfcfffcfffcffccffccfcfcfcfccc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffffffffefcfefcfffefffeffeeffeefefefefeee00ee00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffaaaaffffffffffff0000ffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffccccffffffffffffccccffffccccffffcccccccccccc00000000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffffffffffccccffffeeeeffffeeeeeeeeeeeeaaaa0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfffffcfcffffccccfcfcfcfcf0f00000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffffffffffcfcfffffefeffffeeeefefefefefafa0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffffeeccffffffeeffffffeeeeeeeeeeeeaaee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffffffffaf0fffffffaffffffaafafafafafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffffffffcfcfffffffcffffffccfcfcfcfcfcf0cc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffffffffefcfffffffeffffffeefefefefefefaee00
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
def isoMvS_74:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_74:Lower true dom_74 roots_74 goal_74 4:=lower_iso_b isoMvS_74 (by decide +kernel) lowS_73
def isoMvS_81:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_73
def isoMvS_148:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_148:Lower true dom_148 roots_148 goal_148 4:=lower_iso_b isoMvS_148 (by decide +kernel) lowS_73
def isoMvS_164:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_164:Lower true dom_164 roots_164 goal_164 4:=lower_iso_b isoMvS_164 (by decide +kernel) lowS_73
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
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_slice_b [(0xa0a0000000000000a0a,8,9)] (by decide +kernel) lowS_74
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_slice_b [(0xc000c00000000000c000c,64,66)] (by decide +kernel) lowS_81
def isoMvS_29:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_29:Lower true dom_29 roots_29 goal_29 4:=lower_iso_b isoMvS_29 (by decide +kernel) lowS_27
def isoMvS_45:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_45:Lower true dom_45 roots_45 goal_45 4:=lower_iso_b isoMvS_45 (by decide +kernel) lowS_27
def isoMvS_46:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_46:Lower true dom_46 roots_46 goal_46 4:=lower_iso_b isoMvS_46 (by decide +kernel) lowS_27
def isoMvS_51:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=lower_iso_b isoMvS_51 (by decide +kernel) lowS_27
def isoMvS_54:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 4:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_27
def isoMvS_85:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_83
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 4:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_27
def isoMvS_89:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_75
def isoMvS_90:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_83
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 4:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_27
def isoMvS_101:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 4:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_27
def isoMvS_102:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 4:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_27
def isoMvS_106:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_83
def isoMvS_113:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_83
def isoMvS_114:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 4:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_27
def isoMvS_116:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 4:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_27
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 4:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_27
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 4:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_27
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 4:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_27
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_83
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_83
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 4:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_27
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 4:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_27
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_83
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 5:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_83
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_83
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_75
def isoMvS_195:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 4:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_27
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_83
def isoMvS_209:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 5:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_83
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_83
def isoMvS_216:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 4:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_27
def isoMvS_226:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_83
theorem lowS_31:Lower true dom_31 roots_31 goal_31 5:=lower_slice_b [(0xcccccccc,8,10)] (by decide +kernel) lowS_29
theorem lowS_47:Lower true dom_47 roots_47 goal_47 5:=lower_slice_b [(0xaaaa0000aaaa,8,9)] (by decide +kernel) lowS_46
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_slice_b [(0xcc00cc0000000000cc00cc,64,66)] (by decide +kernel) lowS_85
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
def dzo_89_4:=0x303030300000000030303030
def gzo_89_4:=0x303030200000000030302000
def gsh_89_4:=0x30303020000000003030200
theorem lowS_zo_89_4_73:Lower true dzo_89_4 roots_89 gzo_89_4 5:=lower_iso_b (d1:=dom_89) (r1:=roots_89) (T1:=gsh_89_4) [(dom_89,4)] (by decide +kernel) (lower_slice_b (T:=gsh_89_4) [(0x30300000000000003030000,0,16)] (by decide +kernel) lowS_73)
namespace S_93
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(4,20),(5,13),(5,21),(5,69),(8,9),(8,72),(12,13),(12,28),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,88),(64,65),(64,72),(64,80),(68,69),(68,76),(68,84)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_93.map (·&&&dom_93)
def gM:=goal_93&&&dom_93
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xc09ca
|5,0=>0x1e1fd
|6,0=>0x4011c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x330033000000000033003300cccccccc000000008888888b33300000000000033330000c0c0c0c000000000c0c0c0c22222222000000002222222200cc00cc000000000088008b33333330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x99a133a84688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 94 0x3fffffffffffffffffffffff
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
addP pm 0 dom_89 5 roots_89 ops++addP pm 1 dom_92 4 roots_92 ops++addP pm 2 dzo_89_4 5 roots_89 ops++addP pm 3 dom_85 5 roots_85 ops++addP pm 4 dom_29 4 roots_29 ops++addP pm 5 dom_73 4 roots_73 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_93 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_89_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_73 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_89 5 s (0,roots_89.map (·&&&dom_89)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_93 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_89 h
def symsG:List (List (Nat×Nat)):=[[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_93==dom_93)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_93 gM v ys):RunD true dom_93 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_93 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
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
def dzo_90_4:=0x505050500000000050505050
def gzo_90_4:=0x505050400000000050504000
def gsh_90_4:=0x50505040000000005050400
theorem lowS_zo_90_4_74:Lower true dzo_90_4 roots_90 gzo_90_4 5:=lower_iso_b (d1:=dom_90) (r1:=roots_90) (T1:=gsh_90_4) [(dom_90,4)] (by decide +kernel) (lower_slice_b (T:=gsh_90_4) [(0x50500000000000005050000,0,16)] (by decide +kernel) lowS_74)
namespace S_94
def pG:List (Nat×Nat):=[(2,10),(2,66),(4,20),(6,14),(6,22),(6,70),(8,10),(8,72),(12,14),(12,28),(12,76),(16,20),(16,80),(18,22),(18,26),(18,82),(24,26),(24,28),(24,88),(64,66),(64,72),(64,80),(68,70),(68,76),(68,84)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_94.map (·&&&dom_94)
def gM:=goal_94&&&dom_94
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x46ac13f102
|5,0=>0x7fa89609c039d9b
|6,0=>0x4c25d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x2aaaaaaa800000002a802a80111111110000000000000000aa88aa8800000000aa88aa8954015400000000015401540002a802a8000000000220022555500000000000055550000a0a0a0a000000000a0a0a0a1111111100000000111111112a802a800000000022002200555555550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x463204963204632084763204325043210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 95 0x7fffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x82
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x20
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0x1f6a040
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x5a
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_90 5 roots_90 ops++addP pm 1 dom_86 4 roots_86 ops++addP pm 2 dzo_90_4 5 roots_90 ops++addP pm 3 dom_92 4 roots_92 ops++addP pm 4 dom_74 4 roots_74 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_94 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_90_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_74 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_90 5 s (0,roots_90.map (·&&&dom_90)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_94 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_90 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_94==dom_94)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_94 gM v ys):RunD true dom_94 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_94 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_94 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_94 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_94 roots_94 goal_94 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_94
theorem lowS_94:Lower true dom_94 roots_94 goal_94 7:=S_94.noCircuit
theorem lowS_107:Lower true dom_107 roots_107 goal_107 6:=lower_slice_b [(0xa0a00000a0a00000a0a00000a0a,8,9)] (by decide +kernel) lowS_106
theorem lowS_115:Lower true dom_115 roots_115 goal_115 6:=lower_slice_b [(0xc000c000c000c000c000c000c000c,32,34)] (by decide +kernel) lowS_113
namespace S_118
def pG:List (Nat×Nat):=[(2,34),(2,66),(4,20),(4,36),(6,22),(6,38),(6,70),(16,20),(16,80),(18,22),(18,50),(18,82),(32,34),(32,36),(48,50),(48,52),(48,112),(64,66),(64,80),(68,70),(68,84),(68,100),(96,98),(96,100),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_118.map (·&&&dom_118)
def gM:=goal_118&&&dom_118
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x2fc5f0cf0f
|5,0=>0x93d491ec6e02a1b
|6,0=>0x93d49
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x550050005500500055005000550050a800a800a800a800a800a800a800a800000000000000015401100154011220022002200220022002200220022550055000000000055005500000000aa000000aa000000aa000000aa000140014001400140014001400140014220022002200220022002200000000550055005500550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x43250432504832504372504632543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x165418a6
|6,0=>0x1b5
|_,_=>0
def wAt:=mkWire dB 9 119 0x7fffffffffffffffffffffffffffff
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
|5,0=>9
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_116 4 roots_116 ops++addP pm 1 dom_114 4 roots_114 ops++addP pm 2 dom_54 4 roots_54 ops++addP pm 3 dom_102 4 roots_102 ops++addP pm 4 dom_86 4 roots_86 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_118 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_86 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_116 4 s (0,roots_116.map (·&&&dom_116)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_118 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_116 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_118==dom_118)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_118 gM v ys):RunD true dom_118 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_118 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_118 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_121:Lower true dom_121 roots_121 goal_121 6:=lower_slice_b [(0x3000300030003000300030003000300,1,9)] (by decide +kernel) lowS_113
theorem lowS_205:Lower true dom_205 roots_205 goal_205 6:=lower_slice_b [(0x3030000000000000303000000000000030300000000000003030,128,132),(0x3333000000000000333300000000000000000000000000000000,4,132)] (by decide +kernel) lowS_73
namespace S_213
def pG:List (Nat×Nat):=[(1,17),(1,65),(4,20),(4,132),(5,21),(5,69),(5,133),(16,17),(16,20),(16,80),(16,144),(64,65),(64,80),(68,69),(68,84),(68,196),(128,132),(128,144),(129,133),(129,145),(129,193),(192,193),(192,196),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_213.map (·&&&dom_213)
def gM:=goal_213&&&dom_213
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x798a
|4,0=>0x5f5422ff301390611b3d
|5,0=>0x8cce23969112d130e04c0c27709fec089750629702ae701291
|6,0=>0x724b85ffd7143ce0b1de
|7,0=>0x724b8
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc000000000000000c000000000000000c000000000000000c0003300220000000000330022000000000033002200000000003300220000000000000000cc008800000000000000000000000000cc008a30022000000000023002200000000002300220000000000230022000000000000000088008800000000000000000000000000cc008b30033000000000032000000000000003300330000000000320000cc00cc0000000000cc00000000000000cc00cc0000000000cc0003300000000000000300000000000000033000000000000003000000000000000000000cc00cc00000000000000000000000000cc008b30000000000000033000000000000003300000000000000330000c000c00000000000c000c00000000000c000c00000000000c000c330033000000000033003300000000000000000000000000000000cc00c00000000000cc00c00000000000cc00c00000000000cc00c33003300000000003300330000000000330000000000000030000088008800000000008800880000000000880088000000000088008b30033000000000000000000000000003300330000000000000000
|0,1=>0x3300330000000000300030000000000033003300000000003000300000000000000000cc000000000000000000000000000000cc000330033000000000033003300000000002200220000000000220022cc00000000000000cc000000000000008800000000000000880003200320000000000320032000000000032003200000000003200320000c800000000000000c800000000000000c800000000000000c80000000000000000000000000000000330030000000000033003004000000000000000400000000000000040000000000000004000330033000000000033003300000000003300330000000000000000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc000030003000000000003000000000000000300030000000000030000
|_,_=>0
def sP:Nat→Nat
|0=>0x18a1010c508086d142021b250808931420218a1b808335820218a1a80943142031433012262840431430010660bc04734c5090c560404598a12194509125404873142418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682cf15b330654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 27 214 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x15303301360315349703305317
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x51410000003100001201
|6,0=>0x817161
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0xffdd616ca2060c0
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x5100040263
|6,0=>0x7988
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_212 5 roots_212 ops++addP pm 1 dom_81 4 roots_81 ops++addP pm 2 dom_209 5 roots_209 ops++addP pm 3 dom_148 4 roots_148 ops++addP pm 4 dom_85 5 roots_85 ops++addP pm 5 dom_149 5 roots_149 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_213 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_149 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_212 5 s (0,roots_212.map (·&&&dom_212)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_213 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_212 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffffffffffff0000000000000000,64),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_213==dom_213)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_213 gM v ys):RunD true dom_213 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_213 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_213 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_213 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_213 roots_213 goal_213 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_213
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=S_213.noCircuit
def isoMvS_55:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_iso_b isoMvS_55 (by decide +kernel) lowS_47
def isoMvS_61:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 5:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_47
def isoMvS_62:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 5:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_31
def isoMvS_103:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 5:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_47
def isoMvS_109:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 7:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_94
def isoMvS_110:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 7:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_94
def isoMvS_117:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_115
def isoMvS_122:List (Nat×Nat):=[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 6:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_87
def isoMvS_124:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 5:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_31
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 5:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_31
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_87
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 7:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_118
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 7:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_94
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 7:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_94
def isoMvS_167:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_121
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 6:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_115
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 7:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_94
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 6:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_115
def isoMvS_199:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 5:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_31
def isoMvS_203:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 7:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_93
def isoMvS_206:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 7:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_94
def isoMvS_211:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 6:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_115
def isoMvS_214:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 6:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_115
def isoMvS_217:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 7:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_93
def isoMvS_218:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 6:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_115
def isoMvS_220:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 7:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_94
def isoMvS_227:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 6:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_115
def isoMvS_229:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 7:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_94
def isoMvS_230:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 7:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_93
def isoMvS_233:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 7:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_94
def isoMvS_234:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 8:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_213
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 6:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_205
def isoMvS_241:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 6:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_115
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 6:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_115
namespace S_63
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,34),(3,11),(3,19),(3,35),(4,20),(4,36),(5,13),(5,21),(5,37),(6,14),(6,22),(6,38),(7,15),(7,23),(7,39),(8,9),(8,10),(12,13),(12,14),(12,28),(12,44),(16,17),(16,20),(18,19),(18,22),(18,26),(18,50),(24,25),(24,26),(24,28),(32,33),(32,34),(32,36),(40,41),(40,42),(40,44),(48,49),(48,50),(48,52),(56,57),(56,58),(56,60)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffff
def xsM:=roots_63.map (·&&&dom_63)
def gM:=goal_63&&&dom_63
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xc6758
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ffff0000ffff0000ff00ff00ff00ff00f0f0f0f0f0f0f0f0ccccccccccccccccaaaaaaaaaaaaaaaa
|_,_=>0
def sP:Nat→Nat
|0=>0x2c688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|_,_=>0
def wAt:=mkWire dB 6 64 0xffffffffffffffff
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
addP pm 0 dom_62 5 roots_62 ops++addP pm 1 dom_31 5 roots_31 ops++addP pm 2 dom_55 5 roots_55 ops++addP pm 3 dom_47 5 roots_47 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_63 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_47 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_62 5 s (0,roots_62.map (·&&&dom_62)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_63 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_62 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_63==dom_63)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_63 gM v ys):RunD true dom_63 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_63 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_63 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_63 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_63 roots_63 goal_63 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_63
theorem lowS_63:Lower true dom_63 roots_63 goal_63 7:=S_63.noCircuit
def dzo_75_4:=0xf0f0000000000000f0f0
def gzo_75_4:=0xf0e0000000000000e000
def gsh_75_4:=0xf0e0000000000000e00
theorem lowS_zo_75_4_75:Lower true dzo_75_4 roots_75 gzo_75_4 5:=lower_iso_b (d1:=dom_75) (r1:=roots_75) (T1:=gsh_75_4) [(dom_75,4)] (by decide +kernel) (lower_slice_b (T:=gsh_75_4) [] (by decide +kernel) lowS_75)
def dzo_91_4:=0xf0f0f0f000000000f0f0f0f0
def gzo_91_4:=0xf0f0f0e000000000f0f0e000
def gsh_91_4:=0xf0f0f0e000000000f0f0e00
theorem lowS_zo_91_4_75:Lower true dzo_91_4 roots_91 gzo_91_4 6:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_4) [(dom_91,4)] (by decide +kernel) (lower_slice_b (T:=gsh_91_4) [(0xf0f0000000000000f0f0000,0,16)] (by decide +kernel) lowS_75)
namespace S_95
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,10),(2,66),(3,11),(3,19),(3,67),(4,20),(5,13),(5,21),(5,69),(6,14),(6,22),(6,70),(7,15),(7,23),(7,71),(8,9),(8,10),(8,72),(12,13),(12,14),(12,28),(12,76),(16,17),(16,20),(16,80),(18,19),(18,22),(18,26),(18,82),(24,25),(24,26),(24,28),(24,88),(64,65),(64,66),(64,72),(64,80),(68,69),(68,70),(68,76),(68,84)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_95.map (·&&&dom_95)
def gM:=goal_95&&&dom_95
def NN:Nat→Nat
|4=>3
|5=>10
|6=>17
|7=>7
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x674f144f9801dec
|5,0=>0xf7f3feecefe9624d96cf9cedb84b6c5821852383419c02fe2a
|6,0=>0xf4153d6302c9547c2218c0be3b4f33b1d89af52e700976f9fe6346962b884fe62382e723e950cded0c6f3
|7,0=>0xe1246da081bf2a182ebc4d1952a99627e58
|8,0=>0xc3264
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3300333300000000330033005555555500000000555555003333333300000000330033000f0f0000000000000f0f00000fff00ff000000000f0f0000ffffff000000000000000000ffffffff0000000000000000ffffffcc00000000ccccccccaaaaaaaa00000000aaaaaaaaffff000000000000ffff0000ffffffff00000000ff00ff00ffffffff00000000ffff0000ff00ff0000000000ff00ff00f0f0f0f000000000f0f0f0f0cccccccc00000000ccccccccffffffaa00000000aaaaaaaa
|0,1=>0xff00000000000000000000000000000000ffffff0000ff00ff0000000000ff0000ffffffff000000000f0f00000000ffff0000000000000000ff00ffff00000000ff00ff00ffff00ff00000000ffff0000f0fff0ff00000000f0f0f0f0ffffffff00000000ffffff000000ffff000000000000ff0000ff00ff0000000000000000ffffff0000000000ffffff00ffffffff00000000f0f0f0f0333333330000000033333300
|_,_=>0
def sP:Nat→Nat
|0=>0x188274a8c3b04e9a986209d2618827a24c311da930c276266628e213a64628827498713b526188f0498623bd261882e498676b12628827518613ad26189074906209d4618820498a241cc51040418820
|1=>0x30c413a4c3104e9cc8c3104e930c413a6661c427498a3104e92186209d26184ec4986209d3de186209d3220c413a4c5188ed4986209f6930c27d24c5184ec49b03104e9b986209d26
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa5055005
|5,0=>0x4563f63963362d62762161b61560f6
|6,0=>0xb87b17aa7a379c79668f78878177a77466d76676065975274b7
|7,0=>0xe77e07d97d36cc7c57bf6
|8,0=>0xee6
|_,_=>0
def wAt:=mkWire dB 30 96 0xffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x32630d1a61251a532530b92630d92730d30d3252871a562530b30b1a51e532634d1a692430d14d1a620d3253161a52871a51a630b1251a530d1a5
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1e2709a2608005894248902388c2288821884208802
|7,0=>0x261946418c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xffbfb77760553f372c22160f0c050200
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x33760a6139a432b65
|7,0=>0xe9dfdec
|8,0=>8
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_94 7 roots_94 ops++addP pm 1 dom_93 7 roots_93 ops++addP pm 2 dom_91 7 roots_91 ops++addP pm 3 dzo_75_4 5 roots_75 ops++addP pm 4 dom_75 5 roots_75 ops++addP pm 5 dom_87 6 roots_87 ops++addP pm 6 dzo_91_4 6 roots_91 ops++addP pm 7 dom_31 5 roots_31 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_95 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_75_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_91_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_31 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_94 7 s (0,roots_94.map (·&&&dom_94)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_95 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_94 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_95 gM v ys):RunD true dom_95 gM v (ori ys):=h
def Z (s:Nat):=barP dom_95 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_95 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_95 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_95 roots_95 goal_95 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_95
theorem lowS_95:Lower true dom_95 roots_95 goal_95 9:=S_95.noCircuit
theorem lowS_111:Lower true dom_111 roots_111 goal_111 8:=lower_slice_b [(0xaaaa0000aaaa0000aaaa0000aaaa,8,9)] (by decide +kernel) lowS_110
namespace S_119
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(2,34),(2,66),(3,19),(3,35),(3,67),(4,20),(4,36),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,23),(7,39),(7,71),(16,17),(16,20),(16,80),(18,19),(18,22),(18,50),(18,82),(32,33),(32,34),(32,36),(48,49),(48,50),(48,52),(48,112),(64,65),(64,66),(64,80),(68,69),(68,70),(68,84),(68,100),(96,97),(96,98),(96,100),(96,112)]
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
|4,0=>0xce7ec9aa595e44126c46256ea
|5,0=>0xe3448e0385d8193ca840c96c7930455bbe75ab19589ff572904cd5a4071d3eb1e3ead43abeb253cf
|6,0=>0xfeae0f89ecd8383cdcf2bdbbdbc114ba40cad941a0b88873f77925f76b0673eed72e6b6dff2633535d38a4f8474872e40ec93eb1e36d7e35ac63222e2c6f4281ee268281fbc91446e0d7770bd4c0b8f30b658097260371c02dda
|7,0=>0xe8d9fbe7e0b3398721ca6aedf5d38a4ec5b4930603cbe
|8,0=>0xdaa04
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00cc00ff00cc00cc00cc00cc00ccff000000ff00000000000000000000ff000000ff000000ff000000ff0000f000f000f000ff00f000f000f000f0ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00000000ff000000ff00ff00ff00ff0000ff00ff0000000000ff00ff0000000000000000ff00ff0000000000ff0000f000f000f000f000f000f000f000f0ff00aa00ff00aa00aa00aa00aa00aaff00ff00ff000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00000000ff00f000ff00f000f000f000f000f0cc00cc00cc00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa
|0,1=>0xff0000000000000000330000003300000033000000330000cc00ff00cc00ff0000000000000000cc00ff00cc00ff00cc00cc00cc00cc33003300330033003300330000000000000000ff00000000000000ff00005500550055005500550055005500000000ff000000ff0000000000000000330033000000330033003300000000ff00ff00ff00ff00ff000000ff00000000ff000000ff00ff000000ff00000000000000000000ff000000ff00000000ff000000ff000000ff000000000f000f000f000f000f000f000f0000ff000000ff000000ff000000000000ff00ff00ff000000ff00ff00000000
|0,2=>0xff000000ff000000cc000000cc0000000000000000ff00ff00ff00000f000f000f000f0000000000000000000033000000330000000000000000ff00ff00ff00ff00ff00f000ff00f0ff00ff0033000000ff00ff00330000ff00f000ff00f000ff00f000ff00f0ff00ff00ff00ff00f000f000f000f0ff00ff00ff000000000000000000000f000f000f000f000f0000000f0000ff00ff00ff00ff0000000000ff0000ff00000000000000ff000000ff0000ff000f00ff000f00ff000000ff00000f000f000f0000000f000f000f00000000cc000000cc00cc00cc00cc00ccff00ff0000000000ff00ff00ff0000
|0,3=>0xff00cc00ff00cc00ff00cc00ff00cc330033003300330000000000000000ff00ff00ff00ff00cc00cc00cc00cc0000ff0000000000ff00ff0000000000000000ff00ff0000000000000000f000f000ff00ff00f000f000f000f0ff00ff00ff00ff000f0000000f0000
|_,_=>0
def sP:Nat→Nat
|0=>0x6cb20604068b60858604520d18164b21518100818100738320d1811440c60403883460172c85951810085060404c83410122c42063c02c44460402d03460402c320d18f00a20604038834c0402ca2060452481810081811471031811440c2040
|1=>0x182163460402c858604038a20d18100ba8d18100b40d18100b2293680402c320d18100e20d18100b9c834604098b20d1810252c836418100b2233460402c420d04088b20d1a100b8083460402c83460402df20d18100b74834670100b20d180
|2=>0xb20d18100bd48346d0100b20d18101e2c83460452f33460402c83460401cb20dc4100b0c8354181008346040c0b4083460402c8346040bcb1033460402ee20d18100b216346040b483460402ec20d18f00b216368181008acd18100b214181
|3=>0x20d18100b20d18100b608d8d18100b20d18101a2c420d18100b20d18100b38858d181
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x3929b18cea6162db15589ec49621b0f586ec31615b09583ec196
|6,0=>0xb1b575aacf506a4bd09e76f34796bc99e3ef18789342de08efe67bbbc59d4ee466f335dda0ec97613aedd68ead7533a81932e92745ba11cfcc777
|7,0=>0x1a17cd3e4df18f857bf3dddee0f697
|8,0=>0x1a86
|_,_=>0
def wAt:=mkWire dB 55 120 0xffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x34b813520d883534b0d2d04b812d04d883b34b06c920b8b3610bc13934b0d2d34bcd2e34b4d2c2164d2d21e413620e4d2c34b1a2d106c83504ecd2c2cd842e78b830720b546134bcd2e
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xc00000000000000000000000000000000
|6,0=>0x1f2001d27040000000001b100000649810016200142489023880034400000c100000288821c461144000c800
|7,0=>0x291a0671986519063188611
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xf55f35bf175571d3f137135d28021014008006206105004104001101000d00c008002001000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x10020000000000000000
|6,0=>0x61c0130000218005c00b424a10b4c0028007846370020
|7,0=>0x13c463695ef5
|8,0=>0x14
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_118 7 roots_118 ops++addP pm 1 dom_102 4 roots_102 ops++addP pm 2 dom_85 5 roots_85 ops++addP pm 3 dom_83 5 roots_83 ops++addP pm 4 dom_87 6 roots_87 ops++addP pm 5 dom_55 5 roots_55 ops++addP pm 6 dom_103 5 roots_103 ops++addP pm 7 dom_51 4 roots_51 ops++addP pm 8 dom_117 6 roots_117 ops++addP pm 9 dom_115 6 roots_115 ops++addP pm 10 dom_113 5 roots_113 ops++addP pm 11 dom_101 4 roots_101 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_119 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_101 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_118 7 s (0,roots_118.map (·&&&dom_118)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_119 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_118 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
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
theorem lowS_123:Lower true dom_123 roots_123 goal_123 8:=lower_slice_b [(0xf0f0f0f000000000f0f0f0f00000000,1,33)] (by decide +kernel) lowS_91
def dzo_121_4:=0x30303030303030303030303030303030
def gzo_121_4:=0x30303030303030203030303030302000
def gsh_121_4:=0x3030303030303020303030303030200
theorem lowS_zo_121_4_73:Lower true dzo_121_4 roots_121 gzo_121_4 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_4) [(dom_121,4)] (by decide +kernel) (lower_slice_b (T:=gsh_121_4) [(0x3030000030300000303000003030000,0,16),(0x3030303000000000303030300000000,0,32)] (by decide +kernel) lowS_73)
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(4,20),(4,36),(5,13),(5,21),(5,37),(5,69),(8,9),(8,72),(12,13),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,88),(32,33),(32,36),(40,41),(40,44),(40,104),(48,49),(48,52),(48,112),(56,57),(56,60),(56,120),(64,65),(64,72),(64,80),(68,69),(68,76),(68,84),(68,100),(96,97),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|4=>5
|5=>15
|6=>37
|7=>10
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xed7f646e2d2d2ba13c5b054f5
|5,0=>0xfbe8cf4125ecf4ae303dd91c7d33d7b00d3a11917909f72dae6e90861eff31d07257bf0d130
|6,0=>0xfd71cfa6c0f8cdee8109e5696e141cdfcd3db521db0cfd91c7cf858cd339c79c3c218fbc7afba6eeb1d7fa91848e2268bb347d47053366528b3508c1439713dc6e29a61274a4231381bd1d18ecb11c1e0d8910bf9807eb3041ae01a5b
|7,0=>0xf353bc68b0c6757c4d75c2f64b324d9a2428e226774926184e
|8,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc00cc00cc00cc00cc00cc00cc00cc022222222222222220000000000000000cc88cc88cc88cc88cc00cc00cc00cc032323232323232323232323232323232cccc8888cccc8888cccc0000cccc0003333333333333333222222222222222200cc00cc00cc00cc008800880088008b3333333333333003333333333332200cccccc00cccccc00cccc8800cccc88022222222222222222222222222222222cccccccccccccccc00000000000000033333333000000003333333300000000cccc0000cccc0000cccc0000cccc00030303030303030303030303030303030444444444444444488888888888888880110011001100110022002200220022
|0,1=>0x44004400440044000000000000000323232323232323230303030303030304444444444444444000000000000000331133113311331100000000000000000000000000000000888888888888888b0303030303030301010101010101010cccccccccccccccccc88cc88cc88cc890101010101010101010101010101010cccccccccccccccc008800880088008b300330033003300220022002200220000cc00cc00cc00cc000000000000000223322332233223322222222222222220088008800880088008800880088008b3223322332233223322332233223322cccccccccccccccccc00cc00cc00cc011111111111111111100110011001100
|0,2=>0xcccccccc88888888cccccccc000000011001100110011003300330033003300c0c0c0c0c0c0c0c0c8c8c8c8c8c8c8cb03230323032303230323032303230324040404040404040c0c0c0c0c0c0c0c33113311331133113300330033003300
|_,_=>0
def sP:Nat→Nat
|0=>0x8a1951033c668510364f0861440cf08a0440c66091440cf0811030865d510308624510b3c22841c22861441c218510308a4d510308a24e1030944c510349108a1033cc4051033422840cc1891440c22801030812442c22892070861440c2040
|1=>0x3e11851033c22931440cf2866051033c22861440cf08624510b3c21851033c26dd10308a1961440e03c21851030865851033c21857c40cf7861440cf3061551030864c55440cf0865c51033c228e10344f0867440cf08615c1034910861440cf
|2=>0x1033c66051033c22861440d23c21851033c21931440cf09418510344f3061440cf30615d10308a1891650cf0861440e40861440cf19815d1033e318510344f08a1840c21891440cd0861440cf8861440d23c22851033cc2861440cf086405103
|3=>0x40cf0861440cf0861551033c219b1440d13c21851033c21857440cf08614e1033cc185
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a58c6c5e52c314989aa4762128f186cc30615309183ea196
|6,0=>0x15e7abbd41e92f4369eb4d9e60d29791b475a2ed10784bc09df8cf57773b9ddc0eda66a3335d8cec065cbacd958ea574f3a61922e8a741b9f1cecc6f7
|7,0=>0x344f9b7ca3e35f0cf806bd35cded8f657
|8,0=>0x1a96
|_,_=>0
def wAt:=mkWire dB 38 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xf16185cf151858614086421b1854f193c6821918544391850f3b185026d185c6153ca86153ce46140934f1a185423b1850615185433918506171858f281854239185021918546141859316185426f185ca3b18546140ce461518503593ca06151854f391854614
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xa3000001cc0010c00000000c40000c00
|6,0=>0xc0400bc6d2ac800a4a8198a4288a11000007c9e174400001b2648000017200152504000012244501000f134800
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0x3d7f4f1cc06f7809f77cdd748115411024050034cd1304370d01c018050100200400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xc04000c33800028080
|6,0=>0x2b04d6b1450dd657812e8bc18b8c08024400404e1d520
|7,0=>0x2dab67529e693
|8,0=>0xb
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_109 7 roots_109 ops++addP pm 1 dom_117 6 roots_117 ops++addP pm 2 dom_116 4 roots_116 ops++addP pm 3 dom_45 4 roots_45 ops++addP pm 4 dom_93 7 roots_93 ops++addP pm 5 dom_113 5 roots_113 ops++addP pm 6 dzo_121_4 6 roots_121 ops++addP pm 7 dom_121 6 roots_121 ops++addP pm 8 dom_124 5 roots_124 ops++addP pm 9 dom_61 5 roots_61 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_121_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_61 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_109 7 s (0,roots_109.map (·&&&dom_109)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_109 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 37 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 37 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 10 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_125 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_122_4:=0x50505050505050505050505050505050
def gzo_122_4:=0x50505050505050405050505050504000
def gsh_122_4:=0x5050505050505040505050505050400
theorem lowS_zo_122_4_74:Lower true dzo_122_4 roots_122 gzo_122_4 6:=lower_iso_b (d1:=dom_122) (r1:=roots_122) (T1:=gsh_122_4) [(dom_122,4)] (by decide +kernel) (lower_slice_b (T:=gsh_122_4) [(0x5050000050500000505000005050000,0,16),(0x5050505000000000505050500000000,0,32)] (by decide +kernel) lowS_74)
namespace S_126
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(4,20),(4,36),(6,14),(6,22),(6,38),(6,70),(8,10),(8,72),(12,14),(12,28),(12,44),(12,76),(16,20),(16,80),(18,22),(18,26),(18,50),(18,82),(24,26),(24,28),(24,88),(32,34),(32,36),(40,42),(40,44),(40,104),(48,50),(48,52),(48,112),(56,58),(56,60),(56,120),(64,66),(64,72),(64,80),(68,70),(68,76),(68,84),(68,100),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffff
def xsM:=roots_126.map (·&&&dom_126)
def gM:=goal_126&&&dom_126
def NN:Nat→Nat
|4=>3
|5=>5
|6=>9
|7=>3
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xea7cb1d54804247
|5,0=>0xf73466d1415207a399792f7e7
|6,0=>0xf615dd4e5fc3b7e87f277e99579cbc71e1a3997915f2b
|7,0=>0xafb698bf857e995
|8,0=>0x464f4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x2020202020202020a0a0a0a0a0a0a0a155555555111111115555555400000000000000000000000222222222222222211111111111111110000000000000000aa88aa88aa88aa88aa00aa00aa00aa0111111111111111100000000000000002222222222222222222222222222222255555555555555550000000000000000aa00aa00aa00aa00aa00aa00aa00aa0001540154015401540110011001100112aaaaaaaaaaaaaaaa22222222222222255555555000000005555555500000000aaaa0000aaaa0000aaaa0000aaaa000141414141414141414141414141414140888888888888888a22222222222222200110011001100110044004400440044
|0,1=>0x54545454545454545050505050505050
|_,_=>0
def sP:Nat→Nat
|0=>0x833892820ce24a14419c4943083388a9410678250419de941067135841ac49410671152820ce22a88311526410624990e19c494106710483114ca20d62290624990419c4509062098831140418820
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2942a805
|5,0=>0x26540c6d4ab0f6
|6,0=>0x5d6aed45a5b4477ccddd8b2b6
|7,0=>0x1c5f53e37
|8,0=>0x786
|_,_=>0
def wAt:=mkWire dB 17 127 0x7fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x4a04a24a14b14a24a14a04a16b14a34a24a14a02ab4a14a0
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x53000c80003
|6,0=>0xb2492040000
|7,0=>0x3c5c2d1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 9
def pmP:Nat→Nat
|0=>0xffe4d860608080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1041
|6,0=>0x123a42
|7,0=>0x1ff
|8,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_118 7 roots_118 ops++addP pm 1 dom_124 5 roots_124 ops++addP pm 2 dom_62 5 roots_62 ops++addP pm 3 dom_110 7 roots_110 ops++addP pm 4 dom_94 7 roots_94 ops++addP pm 5 dom_122 6 roots_122 ops++addP pm 6 dzo_122_4 6 roots_122 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_126 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_122_4_74 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_118 7 s (0,roots_118.map (·&&&dom_118)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_126 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_118 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_126==dom_126)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_126 gM v ys):RunD true dom_126 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_126 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
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
theorem lowS_207:Lower true dom_207 roots_207 goal_207 8:=lower_slice_b [(0xaaaa000000000000aaaa000000000000aaaa000000000000aaaa,8,9)] (by decide +kernel) lowS_206
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_slice_b [(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,64,66)] (by decide +kernel) lowS_213
def dzo_89_128:=0x3030303000000000303030300000000000000000000000000000000
def gzo_89_128:=0x3030302000000000303020000000000000000000000000000000000
def gsh_89_128:=0x30303020000000003030200
theorem lowS_zo_89_128_73:Lower true dzo_89_128 roots_89 gzo_89_128 5:=lower_iso_b (d1:=dom_89) (r1:=roots_89) (T1:=gsh_89_128) [(dom_89,128)] (by decide +kernel) (lower_slice_b (T:=gsh_89_128) [(0x30300000000000003030000,0,16)] (by decide +kernel) lowS_73)
def dzo_73_128:=0x303000000000000030300000000000000000000000000000000
def gzo_73_128:=0x302000000000000020000000000000000000000000000000000
def gsh_73_128:=0x3020000000000000200
theorem lowS_zo_73_128_73:Lower true dzo_73_128 roots_73 gzo_73_128 4:=lower_iso_b (d1:=dom_73) (r1:=roots_73) (T1:=gsh_73_128) [(dom_73,128)] (by decide +kernel) (lower_slice_b (T:=gsh_73_128) [] (by decide +kernel) lowS_73)
def dzo_91_128:=0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000
def gzo_91_128:=0xf0f0f0e000000000f0f0e0c00000000000000000000000000000000
def gsh_91_128:=0xf0f0f0e000000000f0f0e0c
theorem lowS_zo_91_128_73:Lower true dzo_91_128 roots_91 gzo_91_128 6:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_128) [(dom_91,128)] (by decide +kernel) (lower_slice_b (T:=gsh_91_128) [(0xc0c0c0c000000000c0c0c0c,0,2),(0xf0f0000000000000f0f0000,0,16)] (by decide +kernel) lowS_73)
def dzo_75_128:=0xf0f0000000000000f0f00000000000000000000000000000000
def gzo_75_128:=0xf0e0000000000000e0c00000000000000000000000000000000
def gsh_75_128:=0xf0e0000000000000e0c
theorem lowS_zo_75_128_73:Lower true dzo_75_128 roots_75 gzo_75_128 5:=lower_iso_b (d1:=dom_75) (r1:=roots_75) (T1:=gsh_75_128) [(dom_75,128)] (by decide +kernel) (lower_slice_b (T:=gsh_75_128) [(0xc0c0000000000000c0c,0,2)] (by decide +kernel) lowS_73)
namespace S_219
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,10),(2,66),(2,130),(3,11),(3,19),(3,67),(3,131),(8,9),(8,10),(8,72),(16,17),(16,80),(16,144),(18,19),(18,26),(18,82),(18,146),(24,25),(24,26),(24,88),(24,152),(64,65),(64,66),(64,72),(64,80),(128,130),(128,144),(129,131),(129,137),(129,145),(129,193),(136,137),(136,138),(136,152),(136,200),(192,193),(192,194),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_219.map (·&&&dom_219)
def gM:=goal_219&&&dom_219
def NN:Nat→Nat
|4=>11
|5=>96
|6=>287
|7=>130
|8=>18
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x96ab792c8a70823653775c27355f215427752f0d47fe91c63703cbb
|5,0=>0xfb974fb481f7fe2e1d59e06b8d7901d4e77c883ec4a6abdbeebc5aaaf226aa7abaa664a41fda18f698f9495ba395269912768c4558b2d78961f87d5486fb186dcc837d680f34801277fd2f7a0497585972c08720f571f3471d2c70bc66ed9c6dffa6dca66d1dc6a71964b4a64940648c162c8e5c8a657f7e56e6e56de755ed2556f35420f516e95059a4e2504b52f429024287e409243b7f53a0823866635db2334282da032d6e72c4eb2bbfb2a0cf291d826be625a9f2442322c2a21d19214b720cd21e1891e0781dc341607c14faf14a5b148251459f138be0fd880e25508bac0886207e79078ef0756e04425033fc
|6,0=>0x50ed750bcd50999507894e9394e0cd4d8724c2a54b1ad4b1954b10e4a75e4a1f94862e47e7e47c6c46fda461e4430af41e474129b40c9b3fdbf3fd503fbcf3e9fb3d3343cb733c5343c08d3b5f83b0483a9ce391ba387b53800037f78373f335fd135db235880350ce340d833863327e63236031f753196c31716313e83132430d2130b6c3034c2fd8a2fd5f2e9ca2d6e72d5982ceaa2c4eb2c30a2c0ec2bbfb2a5d12a36f29d6d2982a29828284e22849827d972794626cac2663624bb6246f82381e234bb222652146f20de52054e1e53a1dd611d0fd1a1701916a17842176a8168641673f1473a13e2c12f4d123d6115cb10273100100fd910ea0e0dc620cc460c4de0b1c50af0a0a7750a5240a4ca099f208b4c07e3b07d200772606f50066af05317051b504dc20433d0298a0289a028880256a020700203a00730005dc
|6,1=>0xbda5ebc52abbebabbb0aba1b9b7a15b5b84b402db3db4b240bb2081b1d29ae463ab7c9aa7aba99b0a6143a5adfa55dba4d85a42d0a3b7aa3aa3a36a3a2b76a24649fd029f2aa9ee6d9ec4c9ead29e98b9e77e9db479d6689bbd99acc99848295ba3958d19558993cf4930cd9237991b809130590bde8f8bb8ecd08ea818d59e8d36e8d2bb8bc818af0a8a9b38a3ee89bd8897738959086d6486657852f384038834f9822267f4c97e5ed7df307c2a37bb9e7bb057baf87b5427b4fd7ab4c7a8bb7908d78a9d77bf7779e8770e475bac7444e74056720167134271325706b16ecdb6d6a16a6f76a23e69b806998c684cd6641c6625b64f4b64c9963c3662cc961fcd60d855f21e5daef5d0b45cae25bc655b7ee5b6525aaef5977d5955e58bd5585f456067553d65529553a99534905335252bbf52539524c85248051a14515a4
|6,2=>0xfc9fefb28bfb13bf3fb8f2ebef2e7ceb1d4e9ed0e575be5757e0d29ddad9dc9acdc649da0a2d9701d87f7d433cd2de4d0bbfce81acdfa4cdcb0cd026ccbf6ca19bc982ac919ec02dbbf260beea2
|7,0=>0xd9f05d7c08d6677d0bbfc62e2c5470c2c62b7f94b6312b596eae73eac845ab1b7aa4cda9964a8824a8715a7d50a3fa0a3b56a2496a24649ead299d42999b2967169407692984920839006f8ea408dcbc8c645875748679485ea7811177e3de7deff7a7c176e12759eb7541b73748730aa71cb2719dc6c99969efe679bf6532863c366274e6244960ca95e6fa5e5475ac2b592dd590875762655c4853855537884cc1a4c6ae4b4114a6324a38e4a085478a04662a419404113c40eaf3f4d43f2c93dd0e3ce323ba8a3b05439be63934539100377cd3622d322e43165b313ab30e672fcb92dbdf2d1b32cd9529b3528534274e426b0d2591f24501244bc234f5204d51f8d81e27e1de681a17019f1f18edd184c5166c115bb4128611279a125d512365114830ebe50b8570aef30a73b09e6f099f20964806f50039bc0281301175
|7,1=>0xe040adf4fb
|8,0=>0xf9035bb08fb6419a019f814a7798d46239b60ca9508c84fd9c4c501488e44115f3f7382fd77088ca0766a06cbf
|9,0=>0x798d4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0a0f0a000000000f0a0f0a000000000f0a0f0a000000000f0a0f0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a000a00000000000000000050a050a000000000000000000000000050a050af0f0c0c000000000f0f0c0c000000000f0f0c0c000000000f0f0c0cf000f00000000000f000f00000000000f000f00000000000f000f00e0e0e0e000000000e0e0000000000000e0e0e0e000000000e0e0000f0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0af0f0f0f000000000f000f00000000000f0f0f0f000000000f000f00f0f0f0c000000000e0e0e0c000000000f0f0f0c000000000e0e0e0ca0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f000000000f0f0f0f00000000000000000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000000000000000f0a0f0a0000000000000000000000000f0a0f0ac0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c50a050a00000000050a050a00000000050a050a00000000050a050af0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000
|0,1=>0xf0f0e0e000000000f0f0e0e000000000f0f0e0e000000000f0f0e0ef0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f0000f020f02000000000f020f02000000000f020f02000000000f020f0200f000f00000000000e000e00000000000f000f00000000000e000ec0c0c0c000000000e0e0e0e000000000c0c0c0c000000000e0e0e0e0000f0f0000000000000f0f000000000000000f000000000000000af050f05000000000f050f00000000000f050f05000000000f050f005000500000000000500050000000000050005000000000005000500f0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f00f0a0f0a000000000f0a0000000000000f0a0f0a000000000f0a0000e0e0e0e000000000e000e00000000000e0e0e0e000000000e000e00f0f0f0f000000000c0c0c0c000000000f0f0f0f000000000c0c0c0ce0e0e00000000000e0e0e00000000000e0e0e00000000000e0e0e00f0f0f0f0000000000000000000000000f0f0f0f0000000000000000f0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0af0f0f00000000000a0a0a00000000000f0f0f00000000000a0a0a00
|0,2=>0x3020302000000000302030200000000030203020000000003020302f0f0f0f000000000f0f0f0f00000000000000000000000000000500f000f00000000000c000e00000000000f000f00000000000c000e0000c000f00000000000c000e00000000000c000f00000000000c000ea0a0a0a000000000a0a0a00000000000a0a0a0a000000000a0a0a00f0f0a0a000000000f0f0a00000000000f0f0a0a000000000f0f0a00303030300000000020202020000000003030303000000000202020200f000f00000000000f000e00000000000f000f00000000000f000ee0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0e00a000a00000000000a000a00000000000a000a00000000000a000af0f0f0f000000000f0f0f0f00000000000300030000000000020002f0f0500000000000f0f0500000000000f0f0500000000000f0f05005050505000000000505000000000000050505050000000005050000505050000000000050505000000000005050500000000000505050000e000e00000000000e000e00000000000e000e00000000000e000e0000000000000000f0f0f0e0000000000000000000000000f0f0f0e
|0,3=>0xf0f0f0f000000000e0e0e0e000000000f0f0f0f000000000e0e0e0ef0f0e0e000000000f0f0e00000000000f0f0e0e000000000f0f0e0000f000f00000000000c000c00000000000f000f00000000000c000c000000c000000000404040c000000000000000c000000000404040cf0a0f0a000000000f080f08000000000f0a0f0a000000000f080f08f0f0a00000000000f0f0a00000000000f0f0a00000000000f0f0f00f0f0f0f000000000d0d0d0d000000000f0f0f0f0000000000000000f0f0a0f000000000f0f0a0f000000000f0f0a0f0000000000000000f0f0f0f0000000000000f00000000000f0f0f0f0000000000000f00e0e0e0e000000000e0c0e0c000000000e0e0e0e000000000e0c0e0cf0f0f0f000000000a000a00000000000f0f0f0f000000000a000a00f000f00000000000e000e00000000000f000f00000000000e000e00a0a0a0a000000000a0a0a08000000000a0a0a0a000000000a0a0a08f0f0f0f000000000f0a0f0a000000000f0f0f0f000000000f0a0f0aa000a00000000000a000a00000000000a000a00000000000a000a0050f050f00000000050a050a00000000050f050f00000000050a050a
|0,4=>0xf0f0f0f000000000a000a00000000000f0f0f0f000000000a0a0a0a2020202000000000202020200000000020202020000000002020202500050000000000050a050a000000000500050000000000050a050a00000000000000003020302000000000000000000000000030203023000300000000000300030000000000030003000000000003000300b0a0b0a000000000b0a0b0a000000000b0a0b0a000000000b0a0b0af0c0f0c000000000f0c0f0c000000000f0c0f0c000000000f0c0f0ca0a0202000000000a0a0200000000000a0a0202000000000a0a0200f0e0f0e000000000f0e0f0e000000000f0e0f0e000000000f0e0f0ef0f0f0f000000000f0f0f0f000000000f0f0f00000000000a0a0a000000f0f0000000000000f0f0000000000000f0f0000000000000f0af0f0f0f000000000f0f0f0f000000000f0f0f0f0000000002020202f0f0000000000000f0f0f0a000000000f0f0000000000000f0f0f0a0000000000000000f000f0a0000000000000000000000000f000f0a0000000000000000f0e0f0e0000000000000000000000000f0e0f0ef0f0f0e0000000000000000000000000f0f0f0e0000000000000000
|0,5=>0x5050505000000000505050000000000050505050000000005050500f0f0f0f0000000000000f0a000000000f0f0f0f0000000000000f0af0f0f0c000000000f0f0f0c000000000f0f0f0c000000000f0f0f0c00f000f00000000000f000000000000000f000f00000000000f0000a0a0a0a000000000a080a08000000000a0a0a0a000000000a080a08f0f0f0f00000000050a050a000000000f0f0f0f00000000050a050af0f0f0f000000000f0f0f00000000000f0f0f0f000000000f0f0f005050505000000000505010000000000050505050000000005050100f0f0505000000000c0c0404000000000f0f0505000000000c0c0404f0f0f0a000000000f0f0f0a000000000f0f0f0a000000000f0f0f0a3000b0a0000000003000b0a0000000003000b0a0000000003000b0af0f0f0f0000000000050005000000000f0f0f0f00000000000000000000000000000000f020f020000000000000000000000000f020f02f0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000500f0a0f0a000000000c080c08000000000f0a0f0a000000000c080c08f0f0f0f000000000f0f0f0f000000000a000a00000000000a020a02
|0,6=>0xf0f0f0f000000000f000500000000000f0f0f0f000000000f0005000030003000000000003000000000000000300030000000000030000c0f0c0f000000000c0f0000000000000c0f0c0f000000000c0f0000f050f05000000000c040c04000000000f050f05000000000c040c040000f000000000000000f000000000000000f000000000000000f00f0f0f0f000000000f0f0f0f00000000020202020000000002020202f0f0f0f0000000000000500000000000f0f0f0f0000000000000500f0f0f0f000000000c0e0c0e000000000f0f0f0f000000000c0e0c0ef0f0f0f00000000000a000a000000000f0f0f0f00000000000a000a00f000000000000050f000000000000000f000000000000050f00000000000000000000a0a0a0a0000000000000000000000000a0a0a0a00200020000000000020002000000000002000200000000000200020000a0a0000000000000a0a0000000000000a0a0000000000000a0a0000000000000000a0a0a0a0000000000000000000000000f0a0f0af000f00000000000a000a00000000000f000f00000000000a000a00f0f0f0f000000000f0f0f0f000000000f000f00000000000a000a00
|0,7=>0xd0d0d0c000000000d0d0d0c000000000d0d0d0c000000000d0d0d0c0000000000000000f0f0f000000000000000000000000000f0f0f00f0f0f0f000000000f0f0a0a000000000f0f0f0f000000000f0f0a0aa0a0f0a000000000a0a0f0a000000000a0a0f0a000000000a0a0f0a000000000000000000a000a000000000000000000000000000a000af000f00000000000f0a0f0a000000000f000f00000000000f0a0f0af0f0000000000000f0f0e0e000000000f0f0000000000000f0f0e0ec0c0e0e000000000c0c0e0e000000000c0c0e0e000000000c0c0e0e5050505000000000505050500000000050505050000000000000000a000a00000000000a000a00000000000a000a00000000000f000f00a0a0a0a000000000a000a00000000000a0a0a0a000000000a000a00505000000000000050f0000000000000505000000000000050f0000f0f0f0f0000000002020202000000000f0f0f0f0000000002020202a0f0a0f000000000a0e0a0e000000000a0f0a0f000000000a0e0a0e0000000000000000f0f0e0e0000000000000000000000000f0f0e0e80a080a00000000080a080a00000000080a080a00000000080a080a
|0,8=>0xf000f00000000000f000f00000000000f0a0f0a000000000f0a0f0a00000000000000000000000000000000a0a0a0a000000000a0a0a0af0f0f0f000000000f000f00000000000f0f0f0f000000000f0a0f0a3030300000000000303030000000000030303000000000003030300f0f0f0f0000000003000300000000000f0f0f0f0000000003000300f0f0f0f000000000f0f0300000000000f0f0f0f000000000f0f03005050505000000000404040400000000050505050000000004040404f0f0f0f000000000f0f0c0c000000000f0f0f0f000000000f0f0c0cf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f000f003030303000000000303030300000000030303030000000003000300f0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0a505050500000000050005000000000005050505000000000500050000000000000000000000000000000000f0f0c0c000000000f0f0c0cf0f0000000000000f0f0f00000000000f0f0000000000000f0f0f0050505050000000005050505000000000505050500000000050005000000000000000000202020200000000000000000000000002020202
|0,9=>0xf050f05000000000f050f05000000000f050f050000000000000000d0d0d0d000000000d0d0c0c000000000d0d0d0d000000000d0d0c0cf000f00000000000f000f00000000000f000f000000000000000000f0a0f0a000000000f0a0f0a000000000f0a0f0a000000000a0a0a0af000500000000000f000500000000000f000500000000000f0005000000000000000000e0e0e0e0000000000000000000000000e0e0e0ec0e0c0e000000000c0e0c0e000000000c0e0c0e000000000c0e0c0ef0f0505000000000f0f0500000000000f0f0505000000000f0f0500e0c0e0c000000000e0c0e0c000000000e0c0e0c000000000e0c0e0cf0f0a0a000000000f0f0f0a000000000f0f0a0a000000000f0f0f0a50f050f00000000050f050f00000000050f050f0000000000000000f0f0505000000000f000500000000000f0f0505000000000f0005000000f0f0000000000000f000000000000000f0f0000000000000f00f0f0f0f000000000f0f0f0f0000000000000f0f0000000000000f000000f0a0000000000000f0a0000000000000f0a0000000000000f0a00f000f00000000050f050f00000000000000000000000000000000
|0,10=>0xc0c0f0f000000000c0c0e0e000000000c0c0f0f000000000c0c0e0e808080800000000080a080a000000000808080800000000080a080a0000000000000000f000f000000000000000000000000000f000f00a0a0a0a000000000f0a0f0a000000000a0a0a0a000000000f0a0f0af000f00000000000f000f00000000000f0f0f0f000000000f0a0f0a3030303000000000303000000000000030303030000000003030000f000f00000000000f020f02000000000f000f00000000000f020f02f0f0f0f000000000a0a0f0a000000000f0f0f0f000000000a0a0f0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0a0000f0f0000000000000f0f0000000000000f0f0000000000000a0ab0b0b0a000000000b0b0b0a000000000b0b0b0a000000000b0b0b0a00000000000000000000f0000000000000000000000000000000f00f0f0f0f000000000f0f0f0f00000000000000000000000000000f00f0f0f0f000000000f0f0f0a000000000f0f0f0f000000000f0f0f0af0f0c0c000000000f0f0c0c00000000000000000000000000000000f0f0f0f000000000f0f0c0c000000000f0f0f0f0000000000000000
|0,11=>0x505000000000000050000000000000005050000000000000500c0c0f0f000000000c0c0f0c000000000c0c0f0f000000000c0c0f0cf0f0f0f00000000000e000e000000000f0f0f0f00000000000e000e0050005000000000005000500000000000500050000000000000000c0c0c0c000000000c0c0c0c000000000e0e0e0e000000000e0e0e0ef0f0f0f0000000000000a0a000000000f0f0f0f0000000000000a0af0f0505000000000f0f0404000000000f0f0505000000000f0f0404d0d0d0d000000000d0d0d0d000000000d0d0d0d00000000000000001010101000000000100010000000000010101010000000001000100f000f0a000000000f000f0a000000000f000f0a000000000f000f0a00f000f00000000000a000a00000000000f000f00000000000a000af030f03000000000f030f00000000000f030f03000000000f030f0000000000000000000000000000000000f0f0f0f000000000f0a0f0af0f000f000000000f0f000f00000000000000000000000000000000f0f0f0f000000000f0f000f000000000f0f0f0f0000000000000000f050f05000000000f050f05000000000f050f05000000000f000f00
|0,12=>0x3030303000000000303030000000000030303030000000003030300f0f0f0f000000000f0f0f0f00000000000000000000000002020202f0c0f0c000000000e0c0e0c000000000f0c0f0c000000000e0c0e0cd0d0d0d000000000d000d00000000000d0d0d0d000000000d000d000000f0f0000000000000a0a0000000000000f0f0000000000000a0aa0f0a0f000000000a0f0a0a000000000a0f0a0f000000000a0f0a0a00a000a00000000000a000a00000000000a000a000000000a0a0a0a00000000000000000000e0e00000000000000000000000000000e0ef0f0f0f000000000f0f0f0f000000000002000200000000000200023000302000000000300030200000000030003020000000003000302f0f0f0f0000000000000000000000000f0f0f0f000000000f0a0f0ac0c0f0e000000000c0c0f0e000000000c0c0f0e000000000c0c0f0ef0f0f0f000000000f0f000f00000000000000000000000000000000a0a0a0a000000000f0f0f0a000000000a0a0a0a000000000f0f0f0af0f0f0f000000000f0f0f0c000000000f0f0f0f000000000f0f0f0c0000a0a0000000000000f0a0000000000000a0a0000000000000f0a
|0,13=>0x80a080a000000000000000000000000080a080af0f0f0f000000000f0f0f0f0000000000000000000000000f0a0f0af0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000f00f000f0f000000000f000f0a000000000f000f0f000000000f000f0a50f050f00000000050f050f00000000000000000000000000000000f0f0f0f00000000050f050f000000000f0f0f0f00000000000000000000000000000000000050000000000000000000000000000000500f0f0f0f000000000f000f0000000000050505050000000005000500f0f0f0f0000000000000000000000000f0f0f0f000000000f0f0c0c00f000f00000000000f000a00000000000f000f00000000000f000a0000303000000000000030000000000000003030000000000000300b0b0b0b000000000b0b0a0a000000000b0b0b0b000000000b0b0a0af0f0f0f000000000f0f0f0f000000000505050500000000050005000000a0a000000000f000f0a0000000000000a0a000000000f000f0af0a0f0a000000000f0a0f0a000000000f0a0f0a0000000000000000000000e000000000000000e000000000000000e000000000000000e
|0,14=>0xf0c0f0e000000000f0c0f0e000000000f0c0f0e000000000f0c0f0e0000302000000000000030200000000000003020000000000000302000000000000000000000000000000000000000000000000f0a0f0af0f0f0f000000000d0d0d0d00000000000000000000000000000000f0f0000000000000f0f000f0000000000000000000000000000000000000000000000000000000000000000f000f00000000000f000f00a0a0a0a000000000a0a0a0a000000000f0a0f0a000000000f0a0f0af0f0f0f000000000f0f0f0f000000000a000a00000000000a000a00a0a0f0f000000000a0a0f0a000000000a0a0f0f000000000a0a0f0a00500050000000000050000000000000005000500000000000500000000f0e0000000000000f0e0000000000000f0e0000000000000f0ef0f0f0f0000000003030300000000000f0f0f0f00000000030303000000000000000000500050000000000000000000000000005000500f0f0f0f000000000b0a0b0a000000000f0f0f0f000000000b0a0b0a000000000000000000e000e000000000000000000000000000e000e40c040c00000000040c040c00000000040c040c00000000040c040c
|0,15=>0xf0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f000000f000f00000000000f000f00000000000f000f0000000000000000a0a0a0a00000000000a000a000000000a0a0a0a00000000000a000a50505040000000005050504000000000505050400000000050505041010101000000000101000000000000010101010000000001010000f0f0000000000000f0f0500000000000f0f0000000000000f0f0500d0d0d0d000000000d0c0d0c000000000d0d0d0d000000000d0c0d0cf000f00000000000f000000000000000f000f00000000000f000000f0f0f0f0000000000000000000000000f0f0f0f000000000f000f00a000a00000000000a000f00000000000a000a00000000000a000f000000f0f0000000000000f0c0000000000000f0f0000000000000f0c30303030000000003020302000000000303030300000000030203020000000000000000f0f0f0f0000000000000000000000000f0a0f0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0a0f0a5050505000000000505040400000000050505050000000005050404f0f0f0e000000000f0f0f0e000000000f0f0f0e000000000f0f0f0e
|1,0=>0xf0f0f0f000000000f0f0f0f000000000c0c0c0c000000000c0c0c0cf0f0f0f000000000f0f0f0f000000000f000f00000000000f000f00f0f0000000000000f0f000000000000000f000000000000000f000000000000000000000000000000000000f0a0f0a000000000f0a0f0a50f050f000000000000000000000000050f050f0000000000000000f0f0000000000000f0f0000000000000f0f0f00000000000f0f0f000000500000000000000050000000000000005000000000000000500f0f0f0f0000000005000500000000000f0f0f0f0000000005000500f0f0f0f000000000f0f0f0f000000000f0a0f0a000000000f0a0f0af0f0f0f000000000f0c0f0c000000000f0f0f0f000000000f0c0f0cd0d0d0d000000000d0d0d0d0000000000000000000000000000000000000000000000000000000000000000f0f0f0f000000000f000f00f0f0a00000000000f0f0a00000000000f0f0a00000000000f0f0a000000e0e0000000000000e0e0000000000000e0e0000000000000e0e0000000000000000f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x901408030589c0400020080200090101602030942424058084612028100422108480a200202c04060287c3c0b010240a040e82004090281028020307000040586c28060002c04060d0480a040c80830120285c2c020481408020083400170b0080c000203c2a14028101e0206800180f098480a110400820050203c040e06830160a048140808038180a04018080200
|1=>0x202c0406090e008020307024050602c260609014080f010246e050202c6c0609014080f010d40a041a0080c12028106402008480a04058086612028101e02180480a0404008122f028101615010240a04058080c2e09010042d030480a04010185812028301602158480a2a0580812050203c10270a014080f0400852050602c140609014080f0a8082405020080c28
|2=>0x3118240b010188a120285c2c02030480a04078081c350202c280203110080b0500812050203c16270a0008604058080c00021081602030000841058080c0012078160203000080b0101880050203c103f01014080f018086a050203c040d090147c0b0101824050209c7a2609014080b030f024050202c2a1403014083b0589c24051d02c040600048080b0a0080c39
|3=>0x202c0406290480847040500c0502020045103014080b01018a0120202c044f0300008020083424050882c0410090140832078086a050b830101403014080b138504c000200c160227000080f0113424050202c04062600008080112812050f0101602158003c0b01018440002124102704814080f0980824050202c04480901408470400812050203c0435000101602
|4=>0x202c04062f0480a5d02020040609014080f01004001202008b4010901408030100424050b8301e2709014080f010d41a050882c04092e014080f0180862000202c4e5b09014080f0116824052c844160204814080b0116024050602cae06090140803058080c002b078160203000180b0315424050202c0406001500816058080c000203c1002048140853058080c00
|5=>0x1018d21202830080f0589c24050202c04061a81408030589c041202810100b01024c6050202cd002030480a040402c040633814080b1f8080c120282c0406330480a0405808ca2f09014080b138187a120281004090307024050202c040632000240c058081263090142e04190080c1202810c40b0101824050202c0406300482e0405808be12028101e0b138bc2405
|6=>0x28101676010180012020ec1602030480a040402c040913014081d058080c000902c04063a0480a040782c047309014080b011c80c12029c4080b0101824050202c0409380480a04059bc040609014080b01018dc1202810166d0101824052e8781602030480a590202c045f09014080f0589c04000901016023601824050202c0409030dc0a040402c040635048080b
|7=>0x1018421202a20080b1381824050202c0c8609014080b01215081202a0c080b010240c120b8781602030010411058080c120281016020320424050202c2802031cc0a04059fc0406090140802030f44c120283016140318c24053f0301602030480a7d0f010160203000080b011f0121202810f408010182405021e81602030480a790202c0406090140849059e00c12
|8=>0x202c1402030480a17060200406090141804058185e1202a58080b0101824050202c4e02130002404058080c124a8101636030480a0405a50040609014080b0101924120203c04350295816020324424050202c04060924008340101824050202c0409320480a044682c0406090140808010191812028101602048191605450101602030480a042482c0c89090142e04
|9=>0x58081212028101e080113824052c8301602030480a040182c040903014080b010184200090781602032302405410101e02030480a040101838120281016024e01800120203c046109014080b4d8080c0009010920b4d01824050203c1614010180004058080c2f00048180b0312cc61202810169901018001202020163f010180a980202c040609014080b4b8180012
|10=>0x10249c05022a41602030480a0424820040903014080b13808ce12028101602540182405058081206530480a04058080c0e1a810160252818240502020044a030480a04248204e06090143c04058080ca309288080b010182405418101e0b0101824042482c28060009008080101824050202c0406500108e080101824050202c0406000493e0405a78040609014081d
|11=>0x22c01602030480a0c058080c5c09014080b01128ca120281016af010182405021241627328480a04058080cae09014080f0589c28120285c08ac0101824050203c1602148480a045582c040609014080b098080c12028108e0b011942405218101602030480a04058080c3500010840b010182405021041602030480a17058080caa09014481e058080c1202810100b
|12=>0x32f424050202c0406092f00a040402d760609014180b01019741202810100b010ac24055c8101602030480a04058080c125c0101602032dc2405022d81002030480a040589c04b5090140808010184412028101602048bc24050202c28020309800045a02c040609014080b0101800124a811660b0101824050202c040658848080f018200406028101602472102405
|13=>0x901016020332024050202c040663848080b010198c12028118a0b0101824050202c6c02030480a0405b100406090143c04058080c12618101602031302405610101602030480ac10202c0406090143c040580856120287816020308824050202c0406600480a04058080cbf09014080f040080c120281016be0101824050203c0435090140808058080c89028101602
|14=>0x2482c4e060004808d2058080c1202810160203049a2050202c0406680480a0c5b02c040609014080b010199e120281016020333824040589c042309014080b6681824050211c160203000240405b30040609014180b0101996120281016026501824050203c1602270002404058080cc900048080b0101820120281016270a09824050200c1602270480a04058080ca0
|15=>0x30480a110f02c040902b5c080b010182404059e00409090140816058080c1202964220b0101824050202c04066b0480a170202c042b09014080b01019aa12029643c04058080c000202c04d4030480a042982c040609014080f058fc04120281016020334c24053f0101e02030480a1708820040609014ba04058500c12028101627030bc24050202c044a030002404
|16=>0x2810060b0101824052b0781602030480a04058080c5b0901408de058080c1202810160203374241702020280203014181e0589c0c1202811b80b0101824050203c100204814080b01019b4122c8101602158480a045802c040600048080b0101838120281016020336424050203c060b01018005602020040609014080b01019b01202810060b0101800052e8101627
|17=>0x58080c0e0901016027381824050202cf014030480a040182c0406000101602033982405020c81602270480a04058080ce509014080b01019c8120285c0808010240c050203c1602400480a17020080ce309014080b013880c12028101602033842405060781602048180a040782c040600048080b0338000120202c0406000497804058080cdf09014b204010183012
|18=>0x33d02405023cc1602030480a047902c040609014080b01019e212028101e03010c42405020c8060b010180a170602c4e0609014080b01018aa120281016020300024d1410781602030480af00202c04060901408ef058080c12028101e02008480a04058080cee0901408ed058080c1202810160203049d804058080c127585c3c0b010240c05023a41602048480a04
|19=>0x402c0409028101602033f024050f0101602032900004010604c00090101e02188002404058080cfb09015f404058080c1202878080b0117c24050b9f41602030480a0405be40406090142ef80101824050202c0409488480a047b82c040903014080b01024ea0502008021202810640b0101824050202c04067b0480a04058080cf509014080f0409c0412028101602
|20=>0x308480a110202c2802030480a04058080c2309015fe040402c0406090142e04040080c1202810160203049fc050211c16270101824050202c04067e8480a04058080c35028303c0b0101824050202c7e02030480a0405ab40406318480a0405be0040609015101e0202c0406090142e040789c041202810640f010c42405020201602030a40a0407820280203014080f
|21=>0xa0080c120281016780101824050202c0406808480a04058080c80090142204058080c4b0901408470782c040609014080b010240c4b09014080b01018d600090101602049382405021e81602030480a040589c0409030480a170f02c040609014080b750081206090140808058080c4e09014080b010195412029f43c04058080c120281016270101825000202c0406
|22=>0x20201602428182405120101602030480a17022b40406090140847058080c12028101602032e824050203c1602270480a040782c4e02030480a042482c280609014080b010240c180901408320402c040609014080f058081206090142e0c058080c120281016020317024050202c0406420480a04058094e0609014080f058080c1280010920b01018ca12028101e0b
|23=>0x281010020312c24050202c0406658480a04058080c4b318480a04058080c00093f8080b0a0080c00023a41602030480a04058500406130480a170202c040600048080b01018f61202c081602030480a0405a68040609014080b0101824a10202c04090338c24050202c04061a8480a047b82c040609014080b011280c1202810920b1381824050202c28020318c2405
|24=>0x58080c1202810100b010240c050202c0406488480a04058080c37090140905058080c1202810100b0a0080c050202c0406094100808010183012028101e080101824050202c0406498480a048182c040609014080f058080c12028101602033a0240405819c01202810160203000249d06010100b0101824050203c160203244240541810160203048080b010184412
|25=>0x306024050b8101e02030480a04058080c4b000481804058189612028110e08058080c1202844080b0101800122e85c080b0101824050203c16020300024050202c0406838480a040780c1602030480a048303c1602030480a11021241602030480a590f0101602030480a042482c0409030480a7d0202c0409030480a040586c040609014080f05808ca12029640808
|26=>0x202c047c030480a1e0202c4e02030480a0424820040609014080f8582c04060901408080589c040609014080b01018d4120202c040685014080b01018e012028100418130480b09058080c12028101e02188480a04058080c1800048b2170202c040609014080f058080c0009010060b010182405024181602030480a04058080d08090151004058080c120285c0802
|27=>0x2844080b0101824050202c0409030480a04058080c12800101614010182405024341602030480a170202c040609014080b568080c12028101602032382405060101e0b0101824050f01016020329024050b81016270101824050202c04060936c1602034302405020c81602030480a1f0202c040609014090b058080c12028101602030c40012020c81e0b010182405
|28=>0x4058080c1202830080b0101824050202c040600048080b010189c120281016020300024050202c0406188480a04058080c120281016020306024050203c1602030480a04058080c4b09014080b870080c12
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32502d50285023501e50195014500f500a500550005
|5,0=>0x1ac61a661a0619a6194618e61886183517d61776171616c51666160615a6154614e61486142613c61366130612a6124611e61186112610c6106610060fa60f460ee60e860e260dd50d760d160cb60c560bf60b960b360ad60a760a1609c50966090608a6084607e60786073506d60676061605b6055604f60496043603d60376
|5,1=>0x26c62666260625a6254624e62486242623c62366230622a6224621e62186212620c6206620061fa61f461ee61e861e261dc61d661d061ca61c461be61b861b26
|6,0=>0x425741e741774107409740273fb73f473ee63e773e073da63d373cc73c573be73b773b073a973a2739b7394738d7386737f73787371736a7363735d6356734f73487341733a7333732c7325731e731773107309730272fb72f472ee62e772e072d972d272cb72c562be72b772b072a972a2729b7294728e62877280727972727
|6,1=>0x5d675cf75c875c175ba75b375ac75a5759f65987591758a7583757c7575756e7567756075597553654c7545753e7537753075297523651c751755107509750274fb74f474ed74e674df74d874d174cb64c474be64b774b074a974a2749b7494748d7486748064797472746b7464745d74576451644a7444643f54387432642c6
|6,2=>0x78f77887781777a7773776c7765775e77577751674a7744673d7736772f77287721771a7713770c770576ff66f876f266eb76e476dd76d676cf76c876c176ba76b376ac76a5769e76977690768a6683767c7675766e7667766076597653664c7645763e7637763076297622761b7614760e6607760075f975f275eb75e475dd7
|6,3=>0x944793d7936792f79296922791b7915690f6908790178fb68f478ed78e768e078d978d278cb78c478bd78b678af78a878a1789a7894688d7886787f78787871786a7863785d6856784f78487842683c6835782e7827782078197812780b780477fd77f767f167ea77e377dc77d577ce77c777c077b977b277ab77a4779d77967
|6,4=>0xa177a107a097a0279fb79f479ed79e769e169da79d379cc79c579be79b869b179aa79a4699f59987991798a7983797c7975796e7967796079597952794b7
|7,0=>0xbe98be27bdc6bd57bcd8bc67bbf7bb96bb27bac6ba48b9d7b967b8f7b887b808b788b717b6a7b637b5c7b557b4d8b467b3e8b368b2e8b277b207b197b127b0b7b038afb8af47aed7ae67ade8ad68ace8ac77ac07ab97ab18aaa7aa28a9a8a937a8b8a847a7d7a758a6e7a668a5f7a587a508a497a436a3c7a357a2d8a267a1e8
|7,1=>0xdb08daa6da46d9d7d967d8f7d887d808d797d718d6a7d628d5a8d546d4e6d477d416d3b6d356d2e7d268d1f7d187d117d0a7d037cfc7cf57cee7ce77cdf8cd87cd08cc88cc17cb98cb18ca98ca18c998c918c8a7c837c7b8c747c6d7c667c5f7c587c526c4b7c447c3d7c367c2f7c296c236c1c7c148c0c8c066bff7bf87bf17
|7,2=>0xdc08db88
|8,0=>0xe3c7e366e2f7e287e217e1b6e147e0d7e067dff7df87df17deb6de47ddd7dd67dcf7dc87
|9,0=>0xe436
|_,_=>0
def wAt:=mkWire dB 271 220 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x5819010190202d078d70581805819078c705818058190f02d078110302d078780302d05899058490581a07809058190785005819078c705818058190485c05818058190202d058490312d0102e03049078090581905819090151884905818058191a81518849058180f09c0101913849078c705818058190409c0101905824190c7058180581913820010190409c0c099090150581a0302e060190304902009
|1=>0x202d09015031ad0202e059ed03023058491384b030130102d059df0300205849030490581a059390101a021d7030200f84b0312f0102e248110102d020490f02d0901505819010493584903049270150101a020190302d0101905849030490784b0581905849058490581a02187058241f82f010252481a0482d0304930815058242c81b0b849058190602d0584901011078c70581805819078c70581805819
|2=>0x5824030491384b05819090150780b05819138490302205849010c505818090150f09c01019058490202d0780b05819090150302f188020581809015011d503020058494981502022058491884905818058190302d308160582403049058fc0a0194784905a390b80b0202d030491382f01019060490121e040150401b0584906017020090202d09015020490584b02019400490a01a010490b81b0201a0b84b
|3=>0x90150598d0201a0482f030490b81b0202d0581a090151880205818092c9358160202e0784b0302d0f02f020490102d568190584b0b89c09015188490581802049020610302e03049130490302f53813048151a8151884905818032310202d0312d0102e520150f02e06017058090901501049020610302e09285060140589d010190307a0b8490202d05825020490202d0584b058fe0a019032750580005819
|4=>0x901507800058190b89e0202d0598d0201a400150a01a0307a020490118505824030491382d010190413b0584904813030490485c030490202d010490928506014020090f09e020492481a0102d0781705819012450302d520160f02e058492c8180f02d0b81b0202d0584903061058490302e0124d058490581918849058180a01b1382f0101907802058190123903017318490201a2c81802021270020101a
|5=>0x58177404918815058180118d0201a0784b058190482e030490304909015030610302e09015010c70581807802058190b8490882d030111b815358490202e0202d058490581905849030490936d18816058183e82e058190882d020190784b058190602d03049030110204906017020090118d0201a078780302d0f02d2c8180b84905849032a90204913849030220b84b058490212505809058190312d0102e
|6=>0x1011020490a019010490584b0201a0f02c020490107902049010190202d0302d0581805819030490302d030490f02e090150581a0302e0581805819090152c81b0f02d0202d0f02c02049078130302d75049030490401805849078c705818058190588f0307a07815058190784905818058190581907800058190f02e0204905819078c705818058190302d400160a01a0104949816020220584903049033a9
|7=>0x3049058190202d010110f02f020490302205849048150304909016058190304b0102d058190118d0201a13813010190a01a010490580b0201905819030490102e0202e09015030490101a3282d0304b03049010190202d020490304905817058490101a0107a0204903079020490901601019058240304902019010490307a020490584902015058490202d05802090151382d010195681a0584b1884905818
|8=>0x584901011078130302d06017020090b81b0202d058490102e02026030490201a0102e05802090150901501049033a9058170581a010490202d090150302305849020c50302c1384b0101906014020090582703049188490581875049058170312d0102e010190102d0201a010490584903015020610302e0584b0202d248190102d318490201a0101a0581901019058190580901049030490302e0302105849
|9=>0x2051010490581b0202d0202d0302d0102e090150102e01011040150584909015020190b8090202d058190c0490302e0784b058190581905809020190f02d02049030490102d0202503049011950304b0304b0581902021058490584903049078130302d358490202e05851010490584901049270160101a058490302e058490302d02022058490401705849030610302e1881505818010c7058180580009015
|10=>0x58180302e058190102e0101502019030490901601049058150202d0584b03017058190f02e02049010190202d1881605818023ab05817078490581906019020090781705819058180901505819031ad0202e0101902049058490102d058190584901019270150101a1884a058180312f0102e0581a0302e023a90581705818058190302e090150b8490202d05819090150784b0581907815058190882e02019
|11=>0x2009090150101a09015
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x8480000000201000000007881a400000000000164000014200000000000000000000004c4000040c0000000000038800000000000000000000000000000d1000000000000a30000082000000000000000000000000000001c4000000003400000000000000000c00000000000000000
|5,1=>0x10cc40300003d30e8c00000000000dcc3610000000000034200000000c882f300000000b482b200000000a0c271094823200000000000000
|6,0=>0x97225489410000000248891123c88d222c8883218800020cc82100008111fc87e11f0879300007811d8874200007131bc86d200000001b046a200000000000673198464218c461217c85e117085a21608571000055200005320000000144850100004e200004c212884910000463
|6,1=>0x3ac80000000ea1000000039cc0000000e6139080000000e31384800037c8dc33688d820000d620000d51348cd023388cc20000cb100000003248c810000c623144c323048be30000bd12ec8b9200000002e04b622cccb122bc8ad20000ab22a0ca530000a2327cc9e126cc992
|6,2=>0x50c942150093f100013d24ec939200013724d493234c092e24b0800000000004a4d281000125348c921200011f200011d246c800000011a146091620001151448d102434d0c14289082418904240880003fcc0003f48fb23e480003dc80003d480003c8cf0200000003b880000000ed1
|6,3=>0x63c98d26304000624d8810001853608c0005fcd7c300017a25e0800000000000000000000176200000005d457235bcd6d200016c100016a2000000059cd6520000000588d5f3000000000015e157455b20001592560555354c951253c94e100014c252c4000524800052054715185451
|6,4=>0x1b336c49b010001ae20001ad16a8da73000000069480000001a2368099e26709993000197200000000001952650400064899110000000
|7,0=>0x8c8a3028b8a2c28a8a282898a242888a202878a1c2868a182858a142848a102838a0c2828a082818a042808a0027f89fc27e89f827d89f427c89f117bc9ed27ac9e927a05e627909e227809de27709da27609d627509d227409ce27309ca27209c627109c227009be26f09ba26e09b62
|7,1=>0xab8aac2aa8aa82a98aa42a88aa11a7ca9d2a6ca9a1a60a962a50a922a40a8e2a30a8a2a20a862a10a822a00a7e29f0a7a29e0a7629d0a7229c0a6f19b4a6b29a86682998a642988a602978a5c2968a582958a542948a502938a4c2928a482918a442908a4028f8a3c28e8a3828d8a342
|7,2=>0xac86b02
|8,0=>0xb0c6c21b046c01afc4000af86bd1af06bb1ae86b91ae06b71ad86b51ad06b31
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0x62800010800004100000c5000023800008d000021000008000001dc00007300001c4000068000012c000044000010400004000000c400002a000008400001a000004000000c0000028000008000001c0000060000014000004000000c0000020000004000000
|1=>0x3010000a0000024100008ce0002124000840000202000080500020100007cf0001f1400074d0001bdc0006cf0001b3400050c000137c00048e0001210000448000105c0004070001014000404000100c00040200010040004000000f3c0003000000b3c000204
|2=>0x20008008001001e01c0070c7001a01c004d060013410004c0c0013010004800001191000450400113140041c50010410003807000c31c00220000080000010000003f3c000f000003b3c000ecd000392c000d04000333c000cc50003238000c8a0003110000c41
|3=>0x8813c020ecf008333c020cc7008331402040d0080a10020280008003802000400693bc01a0ef0061b1c0131c7004b34c0120d7004831c010c03004200c0106cf004141401000300400040084410020124008028002008400802000200200080060020014008004
|4=>0x5033341404cd04a83141288cd04a1334124ac70483b1c120ac7048233c1208c704283bc1040cd04011301001cd04001000880630202110080048018233c040a840101f340400df010016c04004c0100110040010010000404000000ac31c02b00700aa3140226cf
|5=>0x101331c4048cf1006014400ecf100371c400ccf10033144008cf100231c4008c510020144000c410001184000000e023143280c50c281b43000cd0c000002848400a1011020b0ef082833c2090610810000200840080152020014c07033241c04cd062a3ec1848c5
|6=>0x21202d74080110c20094248ab149228c524000105808cf1589b14522ec5148ab1c5222c5120333c480ccb120231c440edf1103b544408cf1100bd44224cd1080a00408861
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x404001504000000040800000004000004280000040600000408040d00000000040000020000042d0000001f00040000000000000200040000000400000000000000002200000004000400000000000000000200001b00000000120000000000
|6,0=>0x1000000900004200005f04000002010004420104009100028204890400640000011d005e080420370002030400000210430a0f1000011b550012238e19070018045600001066041804b0390025640065011e0428006426cf003f040400006404000000610803243904b2164a012400280004004c044d0010000410010005
|6,1=>0x193a640032640029b400377700601800000000000010000014281a04000800040000b3016300591b00000084040400180e9376040a08001064a70100020b08086269040200040101000401b50401850000008824008a014e007600101000006410040084281036020419040104007a0004010400030019003c37000001000024
|6,2=>0x110402003700ad432e00001000008f043e3021008700000076860004510c00
|7,0=>0x13458d5275cc7d51ba675b78078045484998327cab7b44cac4aac8a381c0d29b9079bf3fc113ac07a46c58ab599fbe5c5d2f5a5794ca497e4896172c7fa2bd9240d08399279c31496f8a3d4b9ab9716879c9c77035476e50465446a1ae53cdc52a037374323b6a389734316bb18c2ba9a533bb67aed3a0d16d4949af7241b8a8
|7,1=>0x16a6
|8,0=>0x959d32ca4944bcc6b6d49e8bc34fcbceb7c2
|9,0=>0x1c
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 26 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_217 7 roots_217 ops++addP pm 1 dom_209 5 roots_209 ops++addP pm 2 dom_155 7 roots_155 ops++addP pm 3 dom_202 5 roots_202 ops++addP pm 4 dom_81 4 roots_81 ops++addP pm 5 dom_73 4 roots_73 ops++addP pm 6 dom_203 7 roots_203 ops++addP pm 7 dom_91 7 roots_91 ops++addP pm 8 dom_154 4 roots_154 ops++addP pm 9 dom_90 5 roots_90 ops++addP pm 10 dom_218 6 roots_218 ops++addP pm 11 dom_211 6 roots_211 ops++addP pm 12 dom_153 4 roots_153 ops++addP pm 13 dzo_89_128 5 roots_89 ops++addP pm 14 dom_147 4 roots_147 ops++addP pm 15 dzo_73_128 4 roots_73 ops++addP pm 16 dom_216 4 roots_216 ops++addP pm 17 dzo_91_128 6 roots_91 ops++addP pm 18 dom_74 4 roots_74 ops++addP pm 19 dom_195 4 roots_195 ops++addP pm 20 dzo_75_128 5 roots_75 ops++addP pm 21 dom_139 4 roots_139 ops++addP pm 22 dom_83 5 roots_83 ops++addP pm 23 dom_27 4 roots_27 ops++addP pm 24 dom_75 5 roots_75 ops++addP pm 25 dom_89 5 roots_89 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_89_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_73_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_91_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_75_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_89 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_217 7 s (0,roots_217.map (·&&&dom_217)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_217 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_219==dom_219)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_219 gM v ys):RunD true dom_219 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_219 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_219 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_148_8:=0x1100110000000000000000000000000011001100
def gzo_148_8:=0x1100100000000000000000000000000010000000
def gsh_148_8:=0x11001000000000000000000000000000100000
theorem lowS_zo_148_8_148:Lower true dzo_148_8 roots_148 gzo_148_8 4:=lower_iso_b (d1:=dom_148) (r1:=roots_148) (T1:=gsh_148_8) [(dom_148,8)] (by decide +kernel) (lower_slice_b (T:=gsh_148_8) [] (by decide +kernel) lowS_148)
def dzo_212_8:=0x11001100000000001100110000000000110011000000000011001100
def gzo_212_8:=0x11001100000000001100100000000000110011000000000010000000
def gsh_212_8:=0x110011000000000011001000000000001100110000000000100000
theorem lowS_zo_212_8_148:Lower true dzo_212_8 roots_212 gzo_212_8 5:=lower_iso_b (d1:=dom_212) (r1:=roots_212) (T1:=gsh_212_8) [(dom_212,8)] (by decide +kernel) (lower_slice_b (T:=gsh_212_8) [(0x110011000000000000000000000000001100110000000000000000,0,64)] (by decide +kernel) lowS_148)
def dzo_213_8:=0x33003300000000003300330000000000330033000000000033003300
def gzo_213_8:=0x33003300000000003300320000000000330033000000000032002200
def gsh_213_8:=0x330033000000000033003200000000003300330000000000320022
theorem lowS_zo_213_8_148:Lower true dzo_213_8 roots_213 gzo_213_8 6:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_8) [(dom_213,8)] (by decide +kernel) (lower_slice_b (T:=gsh_213_8) [(0x220022000000000022002200000000002200220000000000220022,0,1),(0x330033000000000000000000000000003300330000000000000000,0,64)] (by decide +kernel) lowS_148)
def dzo_77_128:=0x3333000000000000333300000000000000000000000000000000
def gzo_77_128:=0x3332000000000000323000000000000000000000000000000000
def gsh_77_128:=0x33320000000000003230
theorem lowS_zo_77_128_73:Lower true dzo_77_128 roots_77 gzo_77_128 5:=lower_iso_b (d1:=dom_77) (r1:=roots_77) (T1:=gsh_77_128) [(dom_77,128)] (by decide +kernel) (lower_slice_b (T:=gsh_77_128) [(0x30300000000000003030,0,4)] (by decide +kernel) lowS_73)
def dzo_201_4:=0x3030000000000000303000000000000030300000000000003030
def gzo_201_4:=0x3030000000000000303000000000000030200000000000002000
def gsh_201_4:=0x303000000000000030300000000000003020000000000000200
theorem lowS_zo_201_4_73:Lower true dzo_201_4 roots_201 gzo_201_4 5:=lower_iso_b (d1:=dom_201) (r1:=roots_201) (T1:=gsh_201_4) [(dom_201,4)] (by decide +kernel) (lower_slice_b (T:=gsh_201_4) [(0x303000000000000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_73)
def dzo_217_4:=0x30303030000000003030303000000000303030300000000030303030
def gzo_217_4:=0x30303030000000003030303000000000303030200000000030302000
def gsh_217_4:=0x3030303000000000303030300000000030303020000000003030200
theorem lowS_zo_217_4_73:Lower true dzo_217_4 roots_217 gzo_217_4 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_4) [(dom_217,4)] (by decide +kernel) (lower_slice_b (T:=gsh_217_4) [(0x3030000000000000303000000000000030300000000000003030000,0,16),(0x3030303000000000303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_73)
def dzo_149_8:=0x3300330000000000000000000000000033003300
def gzo_149_8:=0x3300320000000000000000000000000032002200
def gsh_149_8:=0x33003200000000000000000000000000320022
theorem lowS_zo_149_8_148:Lower true dzo_149_8 roots_149 gzo_149_8 5:=lower_iso_b (d1:=dom_149) (r1:=roots_149) (T1:=gsh_149_8) [(dom_149,8)] (by decide +kernel) (lower_slice_b (T:=gsh_149_8) [(0x22002200000000000000000000000000220022,0,1)] (by decide +kernel) lowS_148)
def dzo_93_128:=0x33333333000000003333333300000000000000000000000000000000
def gzo_93_128:=0x33333332000000003333323000000000000000000000000000000000
def gsh_93_128:=0x333333320000000033333230
theorem lowS_zo_93_128_73:Lower true dzo_93_128 roots_93 gzo_93_128 6:=lower_iso_b (d1:=dom_93) (r1:=roots_93) (T1:=gsh_93_128) [(dom_93,128)] (by decide +kernel) (lower_slice_b (T:=gsh_93_128) [(0x303030300000000030303030,0,4),(0x333300000000000033330000,0,16)] (by decide +kernel) lowS_73)
namespace S_221
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(4,20),(4,132),(5,13),(5,21),(5,69),(5,133),(8,9),(8,72),(12,13),(12,28),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(24,25),(24,28),(24,88),(24,152),(64,65),(64,72),(64,80),(68,69),(68,76),(68,84),(68,196),(128,132),(128,144),(129,133),(129,137),(129,145),(129,193),(136,137),(136,140),(136,152),(136,200),(192,193),(192,196),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_221.map (·&&&dom_221)
def gM:=goal_221&&&dom_221
def NN:Nat→Nat
|5=>4
|6=>15
|7=>24
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x8d55a79da12c4351fdb2
|6,0=>0xff6bebceba829678087a7539c698fb535d927a30268de24cab1f1511b53a1b458135560870d
|7,0=>0xf5673cb636c08b8b46b7a51449b2cb8d34286af0762636694f5016e4ebd44b97e495754861934f4b309f9292f223f881a74c18fe316b350e73c0bbdc
|8,0=>0xcd723820eb7aa716683340187125d80bcff080e8
|9,0=>0x7369e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccc000000008c8c888800000000cccccccc000000008c8c888830300000000000003030000000000000303000000000000030300008c8c8888000000008c8c8888000000008c8c8888000000008c8c888b33333330000000022222222000000003333333300000000222222220ccc00cc000000000c8c0088000000000ccc00cc000000000c8c00880000000000000000000000000000000333330300000000033333030888888880000000088888888000000008888888800000000888888880330033000000000022002200000000003300330000000000220022cccccccc000000000000000000000000cccccccc000000000000000333330300000000033333030000000000000000000000000000000000000000000000000cccc8888000000000000000000000000cccc888b3330000000000003333000000000000333300000000000033330000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc030303030000000003030303000000000303030300000000030303030444444440000000044440000000000004444444400000000444400033333333000000003333333300000000000000000000000000000000
|0,1=>0xcccccc0000000000cccccc0000000000cccccc0000000000cccccc011110000000000001111000000000000111100000000000011110000cccccccc00000000cccccccc00000000cccccccc000000000000000111111110000000011111111000000001111111100000000000000000000000000000000cccc0000000000000000000000000000cccc00033333333000000000000000000000000333333330000000033330000cccc00cc00000000cccc008800000000cccc00cc00000000cccc008b3333333000000003333222200000000333333330000000033332222cccccccc00000000cccccccc00000000cccc000000000000cccc00033333030000000003333303000000000333330300000000033333030000000000000000088888888000000000000000000000000cccc888b333333300000000333333330000000030303030000000003030303000000000000000000000000000000000cccc000000000000cccc00033332222000000003333222200000000333322220000000033332222cccccccc00000000cccc000000000000cccccccc00000000cccc00033333333000000000303000000000000333333330000000003030000
|0,2=>0xcccccccc00000000cccccccc000000008888888800000000888888880000000000000001111000000000000000000000000000011110000cccccccc00000000c8c8c8c800000000cccccccc00000000c8c8c8cb3113300000000003311330000000000331133000000000033113300cc0ccc0000000000cc0ccc0000000000cc0ccc0000000000cc0ccc022222222000000003333222200000000222222220000000033332222
|_,_=>0
def sP:Nat→Nat
|0=>0x1244308c0191022470054440c224048510308c00a10308c2476051030890171022481c010308c2471951030891c049110308c0045022481c01130892070124430811c010308f2470040c234c1c010224b1c02840892071022481c61440c2040
|1=>0x891c01038c224700408920700488224700a1030891c484224701710308c2470201030891c04911030891c07c225e1c01030891dc0126c30891c01440c22470124430891c01035023091c01030891c61130c23091c06111030891c06840c2247
|2=>0x40c22470111030891c010308c2470040c225e1c07c40891c05c40c22470040c29491c01035022470044c30891c010308990701210308c1c07d11022470181030891c04851030891c07d1
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x9303180cc006
|6,0=>0x1e58e6c6c732b979caee50724b909c76e34716b899c3ee187
|7,0=>0x8fbc61e22f0a78143f19eaeef674b38d9bacd58673b1a180cb97593aadd48e9c84b323a10d07f7
|8,0=>0xab3d3de90f4269dbcd1e5af267
|9,0=>0x15d6
|_,_=>0
def wAt:=mkWire dB 38 222 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1024e0d102c4012475b25107c425107440d109dd271c04425107d21f1094425107491d080560010244032475125107531d100c41d1094725247521f109441d487c425580c409247581f10c491d0cc891d2475600102491d109441d0cc891d0cc840324751271075025387440b389440b
|1=>0x41d247442710344012404201100c43324744251c9441d1034431247521f109441d1034c0924743322474379109d603
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x80cf89c33445cca19221e6000618a20e614811802
|7,0=>0xa253ca694b29251ca29432824fc9e93b2724dc9a9332624bc9692b25249c929232
|8,0=>0xb43646c0d71ac3546a0d31
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x5f9606f24086080ffb01f9603f2407c380f8501f020373c06e580bc90071e00e0c01c100280003f20073c00e480187003040040c0080000810008000080000c000080000e0000c000100000
|1=>0x207fda99c94218273f24c0448cbc918b9218fec2ce582ffb
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>1
|6,0=>0x1818a2c80c4740487150089
|7,0=>0x6d97d646084f7248a56d2a636555e7793314
|8,0=>0x68e6a09a3a14
|9,0=>0xd
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_213 8 roots_213 ops++addP pm 1 dzo_148_8 4 roots_148 ops++addP pm 2 dom_148 4 roots_148 ops++addP pm 3 dom_93 7 roots_93 ops++addP pm 4 dzo_212_8 5 roots_212 ops++addP pm 5 dzo_213_8 6 roots_213 ops++addP pm 6 dom_217 7 roots_217 ops++addP pm 7 dom_220 7 roots_220 ops++addP pm 8 dom_157 7 roots_157 ops++addP pm 9 dom_205 6 roots_205 ops++addP pm 10 dzo_77_128 5 roots_77 ops++addP pm 11 dzo_201_4 5 roots_201 ops++addP pm 12 dzo_217_4 6 roots_217 ops++addP pm 13 dzo_149_8 5 roots_149 ops++addP pm 14 dzo_89_4 5 roots_89 ops++addP pm 15 dzo_93_128 6 roots_93 ops++addP pm 16 dom_73 4 roots_73 ops++addP pm 17 dom_89 5 roots_89 ops++addP pm 18 dom_212 5 roots_212 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_221 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_148_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_212_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_213_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_77_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_201_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_217_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_149_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_89_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_93_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_212 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_213 8 s (0,roots_213.map (·&&&dom_213)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_221 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_213 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_221==dom_221)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_221 gM v ys):RunD true dom_221 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_221 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 15 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_221 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_218_4:=0x50505050000000005050505000000000505050500000000050505050
def gzo_218_4:=0x50505050000000005050505000000000505050400000000050504000
def gsh_218_4:=0x5050505000000000505050500000000050505040000000005050400
theorem lowS_zo_218_4_74:Lower true dzo_218_4 roots_218 gzo_218_4 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_4) [(dom_218,4)] (by decide +kernel) (lower_slice_b (T:=gsh_218_4) [(0x5050000000000000505000000000000050500000000000005050000,0,16),(0x5050505000000000505050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_74)
namespace S_222
def pG:List (Nat×Nat):=[(2,10),(2,66),(2,130),(4,20),(4,132),(6,14),(6,22),(6,70),(6,134),(8,10),(8,72),(12,14),(12,28),(12,76),(12,140),(16,20),(16,80),(16,144),(18,22),(18,26),(18,82),(18,146),(24,26),(24,28),(24,88),(24,152),(64,66),(64,72),(64,80),(68,70),(68,76),(68,84),(68,196),(128,130),(128,132),(128,144),(136,138),(136,140),(136,152),(136,200),(192,194),(192,196),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_222.map (·&&&dom_222)
def gM:=goal_222&&&dom_222
def NN:Nat→Nat
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xbad5e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x2aaa8000000000002aaa8000000000002aaa8000000000002aaa800055005500000000005500550000000000550055000000000055005500a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a111111110000000011111111000000001111111100000000111111112aaaaaaa8000000000000000000000002aaaaaaa800000000000000055555555000000005555555500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>6
|_,_=>0
def wAt:=mkWire dB 6 223 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_220 7 roots_220 ops++addP pm 1 dom_158 7 roots_158 ops++addP pm 2 dom_94 7 roots_94 ops++addP pm 3 dom_206 7 roots_206 ops++addP pm 4 dom_218 6 roots_218 ops++addP pm 5 dzo_218_4 6 roots_218 ops++addP pm 6 dom_214 6 roots_214 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_222 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_218_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_214 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_220 7 s (0,roots_220.map (·&&&dom_220)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_222 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_220 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff0000ffff0000ffff0000,112),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccccccccccccccccccc,126)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_222==dom_222)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_222 gM v ys):RunD true dom_222 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_222 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_222 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_222 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_222 roots_222 goal_222 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_222
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=S_222.noCircuit
theorem lowS_235:Lower true dom_235 roots_235 goal_235 9:=lower_slice_b [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a,8,9)] (by decide +kernel) lowS_234
def dzo_109_128:=0x333300003333000033330000333300000000000000000000000000000000
def gzo_109_128:=0x333300003332000033330000323000000000000000000000000000000000
def gsh_109_128:=0x3333000033320000333300003230
theorem lowS_zo_109_128_73:Lower true dzo_109_128 roots_109 gzo_109_128 6:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_128) [(dom_109,128)] (by decide +kernel) (lower_slice_b (T:=gsh_109_128) [(0x3030000030300000303000003030,0,4),(0x3333000000000000333300000000,0,32)] (by decide +kernel) lowS_73)
def dzo_172_64:=0x111100001111000000000000000000001111000011110000000000000000
def gzo_172_64:=0x111100001110000000000000000000001110000011000000000000000000
def gsh_172_64:=0x11110000111000000000000000000000111000001100
theorem lowS_zo_172_64_164:Lower true dzo_172_64 roots_172 gzo_172_64 5:=lower_iso_b (d1:=dom_172) (r1:=roots_172) (T1:=gsh_172_64) [(dom_172,64)] (by decide +kernel) (lower_slice_b (T:=gsh_172_64) [(0x11000000110000000000000000000000110000001100,0,8)] (by decide +kernel) lowS_164)
def dzo_228_8:=0x110000001100000011000000110000001100000011000000110000001100
def gzo_228_8:=0x110000001100000011000000100000001100000011000000100000000000
def gsh_228_8:=0x1100000011000000110000001000000011000000110000001000000000
theorem lowS_zo_228_8_164:Lower true dzo_228_8 roots_228 gzo_228_8 5:=lower_iso_b (d1:=dom_228) (r1:=roots_228) (T1:=gsh_228_8) [(dom_228,8)] (by decide +kernel) (lower_slice_b (T:=gsh_228_8) [(0x1100000011000000000000000000000011000000110000000000000000,0,64)] (by decide +kernel) lowS_164)
def dzo_229_8:=0x330000003300000033000000330000003300000033000000330000003300
def gzo_229_8:=0x330000003300000033000000320000003300000033000000320000002200
def gsh_229_8:=0x3300000033000000330000003200000033000000330000003200000022
theorem lowS_zo_229_8_164:Lower true dzo_229_8 roots_229 gzo_229_8 6:=lower_iso_b (d1:=dom_229) (r1:=roots_229) (T1:=gsh_229_8) [(dom_229,8)] (by decide +kernel) (lower_slice_b (T:=gsh_229_8) [(0x2200000022000000220000002200000022000000220000002200000022,0,1),(0x3300000033000000000000000000000033000000330000000000000000,0,64)] (by decide +kernel) lowS_164)
def dzo_165_8:=0x33000000330000000000000000000000330000003300
def gzo_165_8:=0x33000000320000000000000000000000320000002200
def gsh_165_8:=0x330000003200000000000000000000003200000022
theorem lowS_zo_165_8_164:Lower true dzo_165_8 roots_165 gzo_165_8 5:=lower_iso_b (d1:=dom_165) (r1:=roots_165) (T1:=gsh_165_8) [(dom_165,8)] (by decide +kernel) (lower_slice_b (T:=gsh_165_8) [(0x220000002200000000000000000000002200000022,0,1)] (by decide +kernel) lowS_164)
def dzo_173_64:=0x333300003333000000000000000000003333000033330000000000000000
def gzo_173_64:=0x333300003332000000000000000000003332000033220000000000000000
def gsh_173_64:=0x33330000333200000000000000000000333200003322
theorem lowS_zo_173_64_164:Lower true dzo_173_64 roots_173 gzo_173_64 6:=lower_iso_b (d1:=dom_173) (r1:=roots_173) (T1:=gsh_173_64) [(dom_173,64)] (by decide +kernel) (lower_slice_b (T:=gsh_173_64) [(0x22220000222200000000000000000000222200002222,0,1),(0x33000000330000000000000000000000330000003300,0,8)] (by decide +kernel) lowS_164)
def dzo_233_4:=0x303000003030000030300000303000003030000030300000303000003030
def gzo_233_4:=0x303000003030000030300000303000003030000030200000303000002000
def gsh_233_4:=0x30300000303000003030000030300000303000003020000030300000200
theorem lowS_zo_233_4_73:Lower true dzo_233_4 roots_233 gzo_233_4 6:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_4) [(dom_233,4)] (by decide +kernel) (lower_slice_b (T:=gsh_233_4) [(0x30300000000000003030000000000000303000000000000030300000000,0,32),(0x30300000303000003030000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_73)
def dzo_105_4:=0x3030000030300000303000003030
def gzo_105_4:=0x3030000030200000303000002000
def gsh_105_4:=0x303000003020000030300000200
theorem lowS_zo_105_4_73:Lower true dzo_105_4 roots_105 gzo_105_4 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_4) [(dom_105,4)] (by decide +kernel) (lower_slice_b (T:=gsh_105_4) [(0x303000000000000030300000000,0,32)] (by decide +kernel) lowS_73)
namespace S_237
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(4,36),(4,132),(5,13),(5,37),(5,69),(5,133),(8,9),(8,72),(12,13),(12,44),(12,76),(12,140),(32,33),(32,36),(32,160),(40,41),(40,44),(40,104),(40,168),(64,65),(64,72),(68,69),(68,76),(68,100),(68,196),(96,97),(96,100),(96,104),(96,224),(128,132),(128,160),(129,133),(129,137),(129,161),(129,193),(136,137),(136,140),(136,168),(136,200),(192,193),(192,196),(192,200),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffff
def xsM:=roots_237.map (·&&&dom_237)
def gM:=goal_237&&&dom_237
def NN:Nat→Nat
|4=>1
|5=>3
|6=>9
|7=>18
|8=>10
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x30740
|5,0=>0x3fb510edc60b002
|6,0=>0xe9c8cb6137844df497923ac6633e5126c60052f903095
|7,0=>0xfb3a5df591bd1587a0954412330e332ef35227bc1ee461a98216177122ea0e8a90c29b09b2506ebd0455e04335
|8,0=>0xf0cadbd1587bc077ae52743d35a8794e2f643d291531d087fd
|9,0=>0xf0cad
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc880000cc8800000000000000000000cc880000cc8b33300003333000033330000333300003030000030300000303000003030cc880000cc880000cc880000cc880000cc880000cc880000cc880000cc8b3330000333300003333000033330000333300000000000033330000000000000000000000000000000000000000cccc0000c0c00000cccc0000c0c303000003030000030300000303000003030000000000000303000000000cc880000cc8800000000000000000000cc880000cc8800000000000000030300000303000003030000030300000303000003030000030300000303000cc000000cc0000008800000088000000cc000000cc000000880000008b33300003333000000000000000000003333000033330000000000000000cccc0000c0c00000cccc0000c0c00000000000000000000000000000000333300000000000033330000000000003333000000000000333300000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc033320000333200003030000030300000333200003322000030300000000088880000888800008888000088880000888800008888000088880000888b33300003333000033330000333300000000000000000000000000000000
|0,1=>0xcccc000000000000cccc000088880000cccc000000000000cccc0000888901000003030000010100000303000001010000030300000101000003030cccc0000cccc00000000000000000000cccc0000cccc0000cccc0000000000000000000000033330000000000000000000000000000333300000000cc000000cc000000cccc0000cc000000cc000000cc000000cccc0000cc022220000222200002222000022220000000000002222000000000000222244440000000000004444000000000000444400000000000044440000000000000002222000000000000222200000000000022220000000000002222888800000000000088880000000000008888000000000000888800000003333000022220000333300002222000033330000222200003333000022224444000088880000444400008888000044440000888800004444000088880220000002200000022000000220000333300000022000033330000002200880000008800000088000000880000008800000088000000880000008b3330000333300002222000022220000333300003333000022220000222200000000000000000000000000000000cccc000000000000cccc0000000333300003030000033330000303000003333000030300000333300003030
|0,2=>0x333300003333000033330000000000003333000033330000333300000000cccc0000cccc0000cccc0000cccc0000cc000000cc000000cc000000cc033330000333300002222000000000000333300003333000022220000000000cc00000000000000cc00000000000000cc00000000000000cc0000000330000003333000000000000000000003300000033330000000000000000cc000000cc0000008800000088000000cc000000cc000000880000008803333000033330000330000003300000033330000333300003300000033000c0c0000000000000c0c0000000000000c0c0000000000000c0c0000000000000000000000022220000222200000000000000000000222200002222
|_,_=>0
def sP:Nat→Nat
|0=>0x631801220c80611807c40c80460040c178601d1032011806c42011801032016860032151805832151801033880490141032011801032814c60044480471804043c32010043c33880403040c804900b1080471840ca0490042011c61440c2040
|1=>0x1032015c60281032011801270c80460048832011803040c80460047032011801032018060160c85c60032196060161032011801110c805318040488320118010f0c80403040c80531801220ce201180103201980103201900304343201180108
|2=>0x1032011801032011805840c80460040c8059180
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x45816c056
|6,0=>0x4e5243105c74e337163895c3ce177
|7,0=>0x192cc365e3ad21590a664f425a120c8a64141f18e906d733b181cb4c537
|8,0=>0x21cd077803be5de4eeb7723b75dacecf7
|9,0=>0x1146
|_,_=>0
def wAt:=mkWire dB 41 238 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x405044840410643010c64401106c11b101440410181121014403043c3191084d1b043410f10048010c65719044251a103c10d100520c04644230c64481046d7221011119100dc0d106c147100d9611018112597c4051010d18043410f3080401483c119346c10d346c10d346010d
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x10334cb2000831884208802
|7,0=>0xd0b22c46f2b4ab2a4a7294a32849f2749b26497254932
|8,0=>0x3e1f47c1ec7a1e4781dc761
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0x6053f8347e80238c4048aa2b11812120381abd8356b0655609fac107581f6b02af601fec03f58072b00dd6012ac0245003fb0077600dec01558002b0001c00008000080000
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x64040310422
|7,0=>0x10d52733d664cb46e75d20d
|8,0=>0x14e73abbc71e5
|9,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_233 7 roots_233 ops++addP pm 1 dom_109 7 roots_109 ops++addP pm 2 dzo_109_128 6 roots_109 ops++addP pm 3 dom_229 7 roots_229 ops++addP pm 4 dzo_77_128 5 roots_77 ops++addP pm 5 dom_173 7 roots_173 ops++addP pm 6 dzo_172_64 5 roots_172 ops++addP pm 7 dom_236 6 roots_236 ops++addP pm 8 dzo_201_4 5 roots_201 ops++addP pm 9 dzo_228_8 5 roots_228 ops++addP pm 10 dom_205 6 roots_205 ops++addP pm 11 dzo_229_8 6 roots_229 ops++addP pm 12 dzo_165_8 5 roots_165 ops++addP pm 13 dzo_173_64 6 roots_173 ops++addP pm 14 dom_164 4 roots_164 ops++addP pm 15 dom_165 5 roots_165 ops++addP pm 16 dzo_233_4 6 roots_233 ops++addP pm 17 dom_73 4 roots_73 ops++addP pm 18 dzo_105_4 5 roots_105 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_237 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_109_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_77_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_172_64_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_201_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_228_8_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_229_8_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_165_8_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_173_64_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_233_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_105_4_73 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_233 7 s (0,roots_233.map (·&&&dom_233)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_237 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_233 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124)],[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_237==dom_237)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_237 gM v ys):RunD true dom_237 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_237 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 18 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_237 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
namespace S_243
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(2,34),(2,66),(2,130),(3,19),(3,35),(3,67),(3,131),(16,17),(16,80),(16,144),(18,19),(18,50),(18,82),(18,146),(32,33),(32,34),(32,160),(48,49),(48,50),(48,112),(48,176),(64,65),(64,66),(64,80),(96,97),(96,98),(96,112),(96,224),(128,130),(128,144),(128,160),(129,131),(129,145),(129,161),(129,193),(192,193),(192,194),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_243.map (·&&&dom_243)
def gM:=goal_243&&&dom_243
def NN:Nat→Nat
|7=>3
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x7a9f6127920fc84
|8,0=>0x7a9f6
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000f000f00000000000f000f00000000000f000f00000000000f000f00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000ca000a000a000a000a000a000a000a000a000a000a000a000a000a000a000af000f000f000f000f000f000f000f000f000f000f000f0000000000000000f000f000f000f0000000000000000000f000f000f000f0000000000000000f000f000f000f000f000f000f000f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x358c8d63237b191ac688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0x398ee07
|8,0=>0x146
|_,_=>0
def wAt:=mkWire dB 8 244 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa121
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x441
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 6
def pmP:Nat→Nat
|0=>0xfff7f73ff343000
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x5a
|8,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_242 6 roots_242 ops++addP pm 1 dom_179 6 roots_179 ops++addP pm 2 dom_115 6 roots_115 ops++addP pm 3 dom_178 5 roots_178 ops++addP pm 4 dom_113 5 roots_113 ops++addP pm 5 dom_163 5 roots_163 ops++addP pm 6 dom_211 6 roots_211 ops++addP pm 7 dom_83 5 roots_83 ops++addP pm 8 dom_241 6 roots_241 ops++addP pm 9 dom_227 6 roots_227 ops++addP pm 10 dom_226 5 roots_226 ops++addP pm 11 dom_209 5 roots_209 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_243 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_209 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_242 6 s (0,roots_242.map (·&&&dom_242)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_243 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_242 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcccccccccccccccccccccccccccccccc,126)],[(0xffffffff00000000ffffffff00000000,96),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xffffffffffffffff0000000000000000,64),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_243==dom_243)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_243 gM v ys):RunD true dom_243 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_243 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_243 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_159:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_iso_b isoMvS_159 (by decide +kernel) lowS_126
def isoMvS_175:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_iso_b isoMvS_175 (by decide +kernel) lowS_125
def isoMvS_183:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 8:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_123
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_119
def isoMvS_231:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_125
def isoMvS_238:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 10:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_221
def isoMvS_246:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_219
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0e00000f0f00000e000
def gsh_107_4:=0xf0f00000f0e00000f0f00000e00
theorem lowS_zo_107_4_75:Lower true dzo_107_4 roots_107 gzo_107_4 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xf0f0000000000000f0f00000000,0,32)] (by decide +kernel) lowS_75)
def dzo_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_123_4:=0xf0f0f0f0f0f0f0e0f0f0f0f0f0f0e000
def gsh_123_4:=0xf0f0f0f0f0f0f0e0f0f0f0f0f0f0e00
theorem lowS_zo_123_4_75:Lower true dzo_123_4 roots_123 gzo_123_4 7:=lower_iso_b (d1:=dom_123) (r1:=roots_123) (T1:=gsh_123_4) [(dom_123,4)] (by decide +kernel) (lower_slice_b (T:=gsh_123_4) [(0xf0f00000f0f00000f0f00000f0f0000,0,16),(0xf0f0f0f000000000f0f0f0f00000000,0,32)] (by decide +kernel) lowS_75)
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,10),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(4,20),(4,36),(5,13),(5,21),(5,37),(5,69),(6,14),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,10),(8,72),(12,13),(12,14),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(18,19),(18,22),(18,26),(18,50),(18,82),(24,25),(24,26),(24,28),(24,88),(32,33),(32,34),(32,36),(40,41),(40,42),(40,44),(40,104),(48,49),(48,50),(48,52),(48,112),(56,57),(56,58),(56,60),(56,120),(64,65),(64,66),(64,72),(64,80),(68,69),(68,70),(68,76),(68,84),(68,100),(96,97),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|8=>1
|9=>5
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xb0a69
|9,0=>0xe6b3fd9c79d7508715435254f
|10,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfffffffffffffffff0f0f0f0f0f0f0f0fffff0f0fffff0f0fffff0f0fffff0f00000ffff0000ffff0000000000000000ffffffffffffffffffff0000ffff0000ffffffff00000000ffffffff000000000f0f0f0f0f0f0f0f0000000000000000ffffffff0f0f0f0fffffffff00000000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8543210854c3210854321078b5432108543210a895432106543210
|_=>0
def sO:Nat→Nat→Nat
|8,0=>7
|9,0=>0x2787e1783e078
|10,0=>0x2f7
|_,_=>0
def wAt:=mkWire dB 13 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc13094d50941874c2
|_=>0
def oO:Nat→Nat→Nat
|8,0=>2
|9,0=>0x61a3058a1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 7
def pmP:Nat→Nat
|0=>0x35f7fcff17c00
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>2
|9,0=>0x3512
|10,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_126 9 roots_126 ops++addP pm 1 dom_125 9 roots_125 ops++addP pm 2 dom_123 8 roots_123 ops++addP pm 3 dom_119 9 roots_119 ops++addP pm 4 dom_111 8 roots_111 ops++addP pm 5 dom_63 7 roots_63 ops++addP pm 6 dom_95 9 roots_95 ops++addP pm 7 dzo_107_4 6 roots_107 ops++addP pm 8 dzo_123_4 7 roots_123 ops++addP pm 9 dom_107 6 roots_107 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_107_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_123_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_107 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_126 9 s (0,roots_126.map (·&&&dom_126)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_126 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 5 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 5 0 = true)
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
  · simp [NN] at hi
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
def dzo_79_128:=0xffff000000000000ffff00000000000000000000000000000000
def gzo_79_128:=0xfffe000000000000fefc00000000000000000000000000000000
def gsh_79_128:=0xfffe000000000000fefc
theorem lowS_zo_79_128_73:Lower true dzo_79_128 roots_79 gzo_79_128 6:=lower_iso_b (d1:=dom_79) (r1:=roots_79) (T1:=gsh_79_128) [(dom_79,128)] (by decide +kernel) (lower_slice_b (T:=gsh_79_128) [(0xcccc000000000000cccc,0,2),(0xf0f0000000000000f0f0,0,4)] (by decide +kernel) lowS_73)
def dzo_214_8:=0x55005500000000005500550000000000550055000000000055005500
def gzo_214_8:=0x55005500000000005500540000000000550055000000000054004400
def gsh_214_8:=0x550055000000000055005400000000005500550000000000540044
theorem lowS_zo_214_8_148:Lower true dzo_214_8 roots_214 gzo_214_8 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_8) [(dom_214,8)] (by decide +kernel) (lower_slice_b (T:=gsh_214_8) [(0x440044000000000044004400000000004400440000000000440044,0,2),(0x550055000000000000000000000000005500550000000000000000,0,64)] (by decide +kernel) lowS_148)
def dzo_95_128:=0xffffffff00000000ffffffff00000000000000000000000000000000
def gzo_95_128:=0xfffffffe00000000fffffefc00000000000000000000000000000000
def gsh_95_128:=0xfffffffe00000000fffffefc
theorem lowS_zo_95_128_73:Lower true dzo_95_128 roots_95 gzo_95_128 7:=lower_iso_b (d1:=dom_95) (r1:=roots_95) (T1:=gsh_95_128) [(dom_95,128)] (by decide +kernel) (lower_slice_b (T:=gsh_95_128) [(0xcccccccc00000000cccccccc,0,2),(0xf0f0f0f000000000f0f0f0f0,0,4),(0xffff000000000000ffff0000,0,16)] (by decide +kernel) lowS_73)
def dzo_151_8:=0xff00ff00000000000000000000000000ff00ff00
def gzo_151_8:=0xff00fe00000000000000000000000000fe00ee00
def gsh_151_8:=0xff00fe00000000000000000000000000fe00ee
theorem lowS_zo_151_8_148:Lower true dzo_151_8 roots_151 gzo_151_8 6:=lower_iso_b (d1:=dom_151) (r1:=roots_151) (T1:=gsh_151_8) [(dom_151,8)] (by decide +kernel) (lower_slice_b (T:=gsh_151_8) [(0xaa00aa00000000000000000000000000aa00aa,0,1),(0xcc00cc00000000000000000000000000cc00cc,0,2)] (by decide +kernel) lowS_148)
def dzo_150_8:=0x5500550000000000000000000000000055005500
def gzo_150_8:=0x5500540000000000000000000000000054004400
def gsh_150_8:=0x55005400000000000000000000000000540044
theorem lowS_zo_150_8_148:Lower true dzo_150_8 roots_150 gzo_150_8 5:=lower_iso_b (d1:=dom_150) (r1:=roots_150) (T1:=gsh_150_8) [(dom_150,8)] (by decide +kernel) (lower_slice_b (T:=gsh_150_8) [(0x44004400000000000000000000000000440044,0,2)] (by decide +kernel) lowS_148)
def dzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00
def gzo_215_8:=0xff00ff0000000000ff00fe0000000000ff00ff0000000000fe00ee00
def gsh_215_8:=0xff00ff0000000000ff00fe0000000000ff00ff0000000000fe00ee
theorem lowS_zo_215_8_148:Lower true dzo_215_8 roots_215 gzo_215_8 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_8) [(dom_215,8)] (by decide +kernel) (lower_slice_b (T:=gsh_215_8) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,0,2),(0xff00ff00000000000000000000000000ff00ff0000000000000000,0,64)] (by decide +kernel) lowS_148)
def dzo_203_4:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0
def gzo_203_4:=0xf0f0000000000000f0f0000000000000f0e0000000000000e000
def gsh_203_4:=0xf0f0000000000000f0f0000000000000f0e0000000000000e00
theorem lowS_zo_203_4_75:Lower true dzo_203_4 roots_203 gzo_203_4 6:=lower_iso_b (d1:=dom_203) (r1:=roots_203) (T1:=gsh_203_4) [(dom_203,4)] (by decide +kernel) (lower_slice_b (T:=gsh_203_4) [(0xf0f0000000000000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_75)
namespace S_223
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,10),(2,66),(2,130),(3,11),(3,19),(3,67),(3,131),(4,20),(4,132),(5,13),(5,21),(5,69),(5,133),(6,14),(6,22),(6,70),(6,134),(7,15),(7,23),(7,71),(7,135),(8,9),(8,10),(8,72),(12,13),(12,14),(12,28),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,26),(18,82),(18,146),(24,25),(24,26),(24,28),(24,88),(24,152),(64,65),(64,66),(64,72),(64,80),(68,69),(68,70),(68,76),(68,84),(68,196),(128,130),(128,132),(128,144),(129,131),(129,133),(129,137),(129,145),(129,193),(136,137),(136,138),(136,140),(136,152),(136,200),(192,193),(192,194),(192,196),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffffffffffffffff
def xsM:=roots_223.map (·&&&dom_223)
def gM:=goal_223&&&dom_223
def NN:Nat→Nat
|5=>1
|6=>12
|7=>69
|8=>151
|9=>98
|10=>14
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x7fbcf
|6,0=>0xfe58cf7829f1879c9736bc620a5e16a11659b10c6bece66b155fd141f5d5
|7,0=>0xfeca4fdaccfb37efa8adf9da6f9b6af6490f4960f3aacec3e1e9b6ae2d54de58ddd560db3ded44c9d3be9d3857cfedfc732cc5e61c48d3c19c4be90fbd4a4bd14cbc89cb54f7ab2cda140e9fe519fdcc9f2319ac2398b6f8c4a78b5c1832af804d27fe087d1da7b04f79d6177b3d70c686cf526c25568b7c5ec9854c095284f50cbc4b9034a63246a783503e2e9d12a7932379b20e75204871e87b1e067173610b73e04433043e403e6003606
|8,0=>0xd75dbd5626d2766cf0e4c966dc930bc6588c6525c636dc3332bf534be52bbbf9cb838eb7904b6c43b6c32b31d5ae090ad60eac5f6aa3deaa3cbaa36da9f15a96c1a69d2a67f0a568ea3f0ca25c8a1e429ddb99c72e9c6b29c0a99ba889b1d79a6bd9907b971729594892031902848f8e68dd828bf708bdbd8a2db8a22889b8588004834477fc8e7e33779fcd78e8c77280764587483073793724096e35f6ccd86a01368d4467497672bb647606414363c775e8a15d7fd5d7b85ce385b9005b0c45975b579c25395e4f2fa4e2044e0c24da964d7024b3bb4add245d64459e14431643a8642e1341ade4014b3f0653778135b843462233bbe2da422cece2cbeb2b0e82a3ac24c0823729234002103c1b1521a12418a5d1704715b5114c761425e13f740f5420c4d80ba1a0b8d509899088e506e2605c7f04c190359702ac7005bc
|8,1=>0xffce2f87d1f7c36f6467f28cdf2811f0254eefe2ee273eb6d2e9b6ae87fee8637e4af3e224fe0e2fe0054df69bded84db773da856da2a3da0fa
|9,0=>0xff9fcfabeaf87e1f1b6cf1a80f0808efca2ef716eb110e8212e7662da120d9d2fd969fd6d3cd66aed518fd4b9ed1ef7cfa92cf698cb6dfc9c91c71fec4d6fc2d80bf644becb9bea4abbd72ba66eb8715b6ac9b608ab4246b3ed2b1177ab461a8185a61f2a368da256fa24b7a123f9e93d9d6319b3959a7fa98faf91395855f0802ac7ea4079181766567532a74de46fb466e05c6c23166fc9628ed61f146168f5f24f5c4fc5ad655916d58948569ae53f02518fd501d24ce6e4c2854c0a9391be3630135f03333562e12b2bad421d1020b521ddfe1ca421bd451ba5019e4415ed0104e50c2bb0c2740bbda0833706d07061a1036c1
|10,0=>0xe9ab7d6bccc48d4ae79e9f4a1946448f57a799007474a6f9056e16e6375a4e3a9281b4
|11,0=>0x1730e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffffaaaa00000000ffffaaaa00000000ffffaaaa00000000ffffaaaaffffffff00000000aaaaaaaa00000000ffffffff00000000aaaaaaaaffff000000000000ffff000000000000ffff000000000000ffff0000aaaaaaaa00000000aaaaaa0000000000aaaaaaaa00000000aaaaaa000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0000ffffffff000000000000000000000000ffffffff00000000000000000000ffff000000000000ff00000000000000ffff00000000ffffff00aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaaffffffff00000000ffff000000000000ffffffff00000000ffff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00005555000000000000550000000000000055550000000055555500ffffffff00000000ffffffff00000000000000000000000000000000
|0,1=>0x5555555500000000555555550000000055555555000000005555000000000000000000000000000000000000ffffffff00000000ffff00000000ffff0000000000000000000000000000ffff00000000ffff0000000000ff000000000000000000000000000000ff00000000ffff00000f0f0f0f000000000f0f0f0f0000000005050505000000000505000000005555000000000000555500000000000055550000000000000000ffff000000000000ffff000000000000ffff00000000000000000000ffffffff00000000ffffffff00000000ffffffff0000000000000000ffffffff00000000ffffff0000000000ffffffff00000000ffffff00ffffaaaa00000000ffffaaaa00000000ffffaaaa00000000aaaaaaaa55555555000000005555550000000000555555550000000055555500555555550000000055005500000000005555555500000000550055000f0f0f0f000000000f0f0f0f00000000050500000000000005050000ffffffff00000000ffffffff00000000ffff000000000000ffff0000ffaaffaa00000000ffaaffaa00000000ffaaffaa00000000ffaaffaaffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00
|0,2=>0xffffff0000000000ffffff0000000000ffffff0000000000ffffff00aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaa00ffff555500000000ffff555500000000ffff555500000000ffff0000ffffffff00000000ffffffff0000000000ff00ff0000000000ff000000ff00ff0000000000ff00000000000000ff00ff0000000000ff00000000ffff000000000000ffff00000000000000ff00000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0a0affffffff00000000ffffffff00000000ffffffff00000000aaaaaaaa0000000000000000ffffff00000000000000000000000000ffffff00ffffffff00000000ffffffff00000000555555550000000055550000555555550000000055550000000000005555555500000000555500000000ffff000000000000ffff000000000000ffff00000000000000000000ffff000000000000ff00000000000000ffff000000000000ff000000000000000000ffaaffaa000000000000000000000000ffaaffaaffffffff00000000ffffffff00000000ffffffff00000000ffffaaaaffffffff00000000ffffaaaa00000000ffffffff00000000ffffaaaa
|0,3=>0x55555555000000005555555500000000555500000000000055550000333333330000000033333333000000003333333300000000333333000000ffff000000000000ffff000000000000ffff000000000000aaaaffffffff00000000ffffffff00000000555500000000000055550000f0f0f0f000000000f0f0f0f000000000f0f0fffa00000000f0f0fffa0f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f00f0f0f0f000000000f0f0f0f000000000f0f0ffff00000000f0f0fff055555555000000005555555500000000555555550000000055555500ffffffff00000000ffffffff00000000ffffaaaa00000000ffffaaaa0f0f0f0f000000000f0f0f0f000000000f0f0a0a000000000f0f0a0affffffff00000000ffaaffaa00000000ffffffff00000000ffaaffaaffffffff000000000000000000000000ffffffff00000000ffff000055555555000000005500550000000000555555550000000055555500ffff000000000000ffff000000000000000000000000000000ff000000000000000000000000000000000000ffffffff00000000ff00ff00ffffcccc00000000ffffcccc00000000cccccccc00000000ccffcccc
|0,4=>0xffffffff00000000ffffffff000000000000ffaa000000000000ffaaffffffff00000000ffffffff00000000ffffffff00000000ff00ff003333333300000000333333330000000033333333000000003300330000000000000000000000000000000000ffaaffaa00000000ffaaffaaffff000000000000ffff000000000000ffffffaa00000000ffffffaa00000000000000000000000000000000555555550000000055550000000000000000000000ff000000000000000000000000000000ff0000cccccccc00000000ccffcccc00000000cccccccc00000000ccffcccc55550000000000005555000000000000555500000000000055550000ffffff0000000000ffffff0000000000ffffff000000000000000000ff00ff0000000000ff00ff0000000000ffffffff00000000ffffff000000000000000000ff00ff00000000000000000000000000ffffff000f0f0f0f000000000f0f0f0f000000000f0f0f0a000000000f0f0f0a0000ffff000000000000ffff00000000000055550000000000000000ffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaafffff0f000000000fffff0f000000000fffff0f000000000f0f0f0f0
|0,5=>0xffffffaa00000000ffffffaa00000000ffffffaa00000000ffffffaa00000000000000000000000000000000ffffffaa00000000ffffffaa00000000000000000000000000000000ffffff0000000000ffffff00ffffffff000000000000000000000000ffffffff00000000ffffff00000000000000000000000000000000000000ffaa000000000000ffaa00000000000000000000000000000000ffffffff00000000ffffaaaa000000000000000000000000000000000000000000000000ffffff00ffffffff00000000ffffffff00000000ffffff0000000000ffffff000f0f0f0f000000000f0f0f0f000000000f0f0f00000000000f0f0f0000000000000000000000000000000000ffff000000000000ffff0000ffffffff00000000ff00ff0000000000ffffffff00000000ffffff00ffff000000000000ffff000000000000ff00000000000000ff000000ffffffff00000000ffff000000000000ffffffff00000000ff000000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00000055550000000000005555000000000000550000000000000055000000ffaa000000000000ffaa000000000000ffaa000000000000ffaa
|0,6=>0xffffff0000000000ffffff0000000000ffffff0000000000ff00ff00ffffffff00000000ffff000000000000ff00ff0000000000ff000000ffffffff00000000ff00ff00000000000000ffff000000000000ff00ffff000000000000ff00000000000000ffff000000000000ff00000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000aaaaaaaa00000000aaaaaaaa00000000ffffffff00000000ffffaaaa55555555000000005555555500000000555555550000000000000000ffff000000000000ffff000000000000ffffffff00000000ffffff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000000000ffff00ff00000000ffff00ff00000000ffff00ff00000000ffff000000000000000000000000000000000000ffffffff00000000ffffff000000aaaa000000000000aaaa000000000000aaaa00000000aaaaaaaa0000ff00000000000000ff00000000000000ff0000000000ff00ff00000000ff00000000000000ff00000000000000ff000000000000000000000000000000000000ffff0000000000000000000000000000ff00ff55ff5500000000ff55ff5500000000ff55ff0000000000ff55ff00
|0,7=>0xffffffff00000000ff00ff0000000000ffff000000000000ff000000ffffffff00000000ffffffff00000000ffffffaa00000000ffffffaa00ff00ff0000000000ff00ff0000000000ff00000000000000ff000000ff00000000000000ff00000000000000ff00000000000000ff0000ccffcccc00000000ccffcccc00000000ccffcccc00000000ccffcccc000000000000000000000000000000000000ffff000000000000ff00000000000000000000ff00ff00000000000000000000000000ff00000000000000000000ffffffff000000000000000000000000ffff0000ff00ff0000000000ffffffff00000000ff00ff0000000000ffffff00ffffffff00000000ffffffff000000000000000000000000ffff00000000000000000000ffff0000000000000000000000000000ffff00000f0f0f0f000000000f0f0f0f0000000000000000000000000f0f0000ffffffff00000000ffffffff00000000ffffffff00000000ffffff00ffffffff00000000ffffffff00000000ffff000000000000ff0000005555550000000000555555000000000055555500000000005555550000000000000000000000000000000000555555000000000055555500
|0,8=>0x55555555000000005555555500000000550055000000000055005500ffffffff000000005555000000000000ffffffff00000000555500000000ffff000000000000ffff000000000000ff00000000000000ff00ff00ff0000000000ffffff0000000000ff00ff0000000000ffffff00ffffffff00000000ffffffff00000000000000000000000000ff0000ffffcccc00000000ffffcccc00000000ffffcccc00000000ccccccccffffffff0000000000ff00ff00000000ffffffff0000000000ff0000000000000000000000000000000000000000000000000000ffff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ffffff00ffffffff000000005555555500000000ffffffff000000005555000000ff00ff00000000000000000000000000ff00ff0000000000ff0000ffffffff00000000ffffffff000000000000ffff000000000000ff00aaaaaaaa00000000aaaaaaaa00000000ffffffaa00000000ffffffaaff00ff0000000000ff00ff0000000000ffffff0000000000ffffff000000000000000000000000000000000000ff00000000000000ff0000cccccccc00000000cccccccc00000000ccffcccc00000000ccffcccc
|0,9=>0xffffffff000000000000000000000000ff00ff00ffffffff00000000ffffffff0000000000ff00000000000000ff0000ffffffff00000000ffffffff00000000ffaaffaa00000000ffaaffaaffffffff0000000000ff000000000000ffffffff0000000000ff0000ff55ff0000000000ff55ff0000000000ff55ff0000000000ff55ff00
|_,_=>0
def sP:Nat→Nat
|0=>0x402060f2308000b220402060f0800200b0403021f08001e0b040302150800051d0403020600051c04030206000b0402150908000d0504021b080005040302151900050403020c1a00170504030216000b0402150f08000b0402141308000b1110020c0f000d0504020c09000b04020a09080007050403020600050403020100
|1=>0x60800050b0403020c1f00170b0402060f08000b0403022e08000b111002060f08000d050402060908002d04030206081a00050b0403020a18000504030206082a000b040206290800050b04020c0609000b040206251b08000d0504030228000b040206140f0800270b0402060f08000b0402061b0800050403020c0624000b
|2=>0x2f050402060f08000b1004020c060f000d050403022518000b043902060800200b0402062908000e0b0403021508000b110402060908000b0403023808000d050403021f080017050403020619000b100402063608000b350402060f08000b040206250908000b0402060f2b0800050403021600340b0403023308000b040330
|3=>0x3308000b1104020c0f08000b0403023f1408000b0403063e0800200b0402060908000b040206092b0800050b040206290800120b111003020c0020040302063d0800120b2204030206180b0403023c1408002f0b1002060f08000b043b02060800050b0402061b0800170b0402060908000504030206081a000b0402063a0800
|4=>0x1e0403020608000b11040302060824000b100402061308000504030206460005040302063d08000d0e050403020c0044050b0403020600120b0403021508002f050402060908000b0402064308000e0b0403020a08000504030206084200120b0403024114080d05040302260800050b0403021518001204400206080b040302
|5=>0x2063608000e0b110403020608002f120b1003020608000b04030206262508000b040302065108000b040302064f08000b040302062608000b0403064d08000d050403020c000e0b04030206250800050b0402060908004b0b0403020608000b040302064a08000d0b100403024108000b0403020a08000b0403480608002f05
|6=>0x8000b10040302063f08005e0b0403020608005c0b040302060800050b0403021508000b040302065b0800120b110403020c08000b110402060f08005a0b040302060800590b04030206080027050b04030206000b04020657080045050b0403020608000b10040302063c080055340b0403020608000b045303020608000b04
|7=>0x800680b0403020608002f0b4c0302060800660b04030206080065050b04030206080012040302060819120b100403024106080b0403026408000b6303020608002f050403020618000b0403020608620005040302061900050b040302061f08000b040302066108000b600403020608000b040302062c0800170e0b04030206
|8=>0x40302066900050b110403020618002f5403020608000b111003020c000d0b100403020c002f6c0302060800120b04030206230800200e0b040302060800050b04030206251800050b040302066b080021200b040302060800120b220403020608006a0b0403020608000e0b040302062b08000b0440020608002d0b04030206
|9=>0x60800550b0403020608002f0e050403020608000b040302067008000b6f03020608000b04030206084600050b046e03020608000b100402060f08000b040302066d0800120b0403020614080027120b040302060800120b040302060869200b040302250800120b110403020618080b0402060908000b04030247140800050b
|10=>0x800770b0403020608000b0403021508000b040206130800050b0403020a08000b0402067408000d050403020618000b04030206081a002f0b0402060f080021050b040302060800370b1004030206080017050b0403020618002f0d0403024108001e0b11040302060800730b040302060800450b0403020608000b04720302
|11=>0x40302060800050b0402060f0800050b040302062b180017120b0403020608000b040302061f08000d050403024108000b220403020618000b040302063208000b040302067d1808120b11100302060800050b040302062608000d0b0403022808000504037b0608000b040302067a08002d0b040302060869000b0403020679
|12=>0x8000b04030241140800120b35040302060800050b0403020c2500120b040302062b08000b04020c060f0800820b1003020608000b6f0403020608000b040302066b08000b040302063f18080b0403800608000e050b0403020c06000b047f03020608007e0b040302060800171e0b04030206080020050b040302061800650b
|13=>0xb0403022806080b04038a0608000b040302068908000b046e0302060800870b040302060800050b0403022806000b040302068608000b040302068508002f0b3103020608000d0e050403020608000b04030206840800120b100402060f0800050b110403020c00050b04030206610800830b040302060800050b040302062c
|14=>0x608000b8804030206080020050b04030206080005120b0403020608000b040302065008000b040302062308000e0b040302060800050b040302062b0800210b0403020608002f0512040302060800120b100403020c060005040302060824000b0403021608000b040302068b08000d05040302250800440b04030206080012
|15=>0x403020608000b10040302410608008c0b0403020608000d0b52040302060800370b0403020608005d0b0403020608002f050b040302060800120b0403020c0608000d0b040302061808000b040302064908000b040302062508000b0402060f08000b04030206140800270b040302060800051e0b0403020608000b4c040302
|16=>0x2b08002f0b110302060800120b0403020618080b040302060869000b040302068f08000b11040302061808002f040302064708002f75040302060800050b0403020618000b780403020608000b040302068e08002f0b040302410608000b52040302061808170b0403020608000b040302068d08000b111003020608000d0b10
|17=>0xb04037b0608000e050b0403020608002f050403020608000b100403020c06000b04030206180869000d0b0403020c0800120b110403020608000b040302069108001e0b040302060800120b0402060f080005040302064708000b35040302060800200b0403020608000b90040302060800050b040302410608000b04030206
|18=>0x302063c08000b040302067d08000b045403020608002f0b1003020608000b040302067108000b046c03020608000b92040302060800050b040302062508000b040302060867002f5d0b040302060800340b04030206080005040302067c08000d0b0403024108002f0b520302060800820b0403020608000b31040302060800
|19=>0x8000b4e040302060800120b100403020608002f0d0403020608000b040302063f08000b040302069308000b10040302064708000b110403020c0800050b0403020c06002f0b040302061808000b040302060819005f0b0403020608000b040302410618080b76040302060800050b11040302060800580b0403020608000b04
|20=>0x3020608000b040302061808000b110403020608000b22040302060800050b520403020608000b049403020608000b56100403020608002f120b0403020608000d050403020608000b040302068108000b04030206082400120b0403024106080b040302061808670017050b0403020608000b520403024106080b0403022806
|21=>0xb0403020608000d0b0403020608000b040302410608000b0403020c060800050b0403020608000b040302067c08002f0b0403020608000b560403020608000b10040302060800120b0403020608000b040302064708000b750403020608000b5204
|_=>0
def sO:Nat→Nat→Nat
|5,0=>6
|6,0=>0x53704c7045703e7037703070297022701b7014700d70067
|7,0=>0x24182398232722a8222821a8212820a820461fd71f581ed81e671de81d681ce81c681be81b681ae81a6819f7197818f8187818071788170816881617159815181498142713a8132812a8122811a8112810c610480fd70f580ed80e670de80d680ce80c680be80b770af80a780a070988090808970818079807180698061805a7
|7,1=>0x26882617259825182498
|8,0=>0x471946a7463745b8454744b9442943994309427941e9416840d940673fe83f683ee83e683dd93d673cd93c673bf73b783af83a8739f9397838f8387837e9375936d8365835d8355834c9344833c8334832c8325731c9313930a930282fb72f292e992e092d882d082c882c172ba72b192a982a18299829092897282727992709
|8,1=>0x67e9676866d9665865c9654864c8644863c8634862d7624961c8614860b960295fa85f285e995e095d885d085c885c085b885af95a6959e8597758f8586957e8576856f7568756085597551854985418538952f9526951e8515950d850584fd84f584ec94e484dd74d584cc94c484bc84b394aa94a2849a8491948a7482847a8
|8,2=>0x73a873197289720871977118709870186f986f276ea86e286da86d286ca86c286ba86b196a986a09698868f96878
|9,0=>0x94a89419939893099288920891889108908890088f978f098e888e088d798cf88c698be88b688ae88a6889e8896888e8885987d8875886d8865885d8854984c8844883c8834882c8823981b8813880b880387fa97f197e987e097d887d087c797be97b597ad87a5879e7796878e8785977d8775876c9763975b8753874b87429
|9,1=>0xa638a5a9a528a499a409a388a308a288a208a179a0e9a0689fe89f689ed99e589dd89d589cc99c489bc89b399ab89a3899b8993898a9982897a8972896a8962895a89528
|10,0=>0xad38acb8ac38abb8ab38aab8aa38a9b8a938a8b8a838a7b8a738a6b8
|11,0=>0xadb7
|_,_=>0
def wAt:=mkWire dB 149 224 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x50042c212f084480f121042c0104084102104064480f0b004380f050042c210b0642c690d1882c190800420011706014110b0842cb22b00414130b084380f050042c210b06430010b08418210326894010506c2c2105004841b2000434210b06414670b1802c2108004343a050042c210b06414110b08418650b18020011203c10210b00418210e03c14010b0842c19
|1=>0xb0041821040642c012103c80010506410210b004182104064842f2000434210b06420011108c2c010406410211203c2c010b0440c9a25004141b0d0e814010b0842c190b084480f0b0042c1104084480f0b004182108004141b050045c1b050442c210e03c2c6108004381b050042c21050442c600b08420013703c34010b0642c21061942c600800408c90b31c1021
|2=>0x506c2c21060042c19040845c180b1041021024942c430408414030b0442c21040642c62080040cf2040851c010b06cbc60080042c110b084842f2000414190b0841401060842c210b06514231e04414030b0845c1b0b0042c41040842c110e03c14010b08414011706014110b0842c9a25004141b0b0842c0104084141b1706c14110b0840c650b1802c0108004480f
|3=>0x4064480f0b00480030d0842c192700cbc230b044bc230b0442c215803c2d490400478110500c2c21040851c010b06cd011560842c03540842d4804004dc0f0b4141801040642c610800410210b0042c1125004141b0b084354a0b0641001500042c460406494010506c2c214e02c10610800418210b0842c1905004141b0b084380f050042c210b4c44403040649403
|4=>0x408444030b04410190b6741062080045c03050442c210b1802c01080042c010408418010619c2c600800410670b1802001080042c110b08410920b18820010b1802c2108004381b050042c21055282c210400410fd1206c2c012b00414130b0841401050442c2104084481b0b0057c030b11410195d084bc030b0445c1b050442c21121182c01040642c01060841019
|5=>0x618820010506c14190b08410190b00420010e03c2c61080042c1b1006c10210b08418620800410190b08420010b5202c110400410190608410210b0641821040842c110b10010210b0042c42040841401050642c210506c2c21080043813050042c212000434210b06444230b00410191e06414030b08414010504c2c21031942c60080042da50618820010b3144003
|6=>0xb0842c190800434620b06420011203c2c010b0448001050642c210d0042c190408414110b08420010b0642c110600410190500c2c21121042c010408478110500c2c216c0042c40040855841040842c03050042c110b085c4032f06c2c11041942c6008004bc600b0442001055202c2104004480f0b00410215610810210b00c2c011006c10212f08c2c010b0442c01
|7=>0x80045c030b10410211203c2c010b08420010504c2c210b0042c4104084381b0b18420010b0642c210600444230406420010b31c40030408448130b00420010b00410210406494010506c2c210c00418210b0642c21027c42c13121082c01040842da50618820011210c2c0104085e0111208c2c011706c2c41040840cf2470042c1b1706014110b085d80f750042c23
|8=>0x408414010b0842c19230042c420408410211203c2c010b084182104064154a0b08410015d064bc030b044ac010504c2c211006c1021060042c0111084101906084141b0b0842c010504c2c211203c2c01060855811040842c03041942c600800438130b184200108004481b0b0040a050b52c1001050042c210608448400b0041021121142c01040642c21050642c21
|9=>0xb18c2001050642c210b0042c210b11810190b10810210b18420010504c2c212000434210b0642c010b0442c210b004182104084382f050042c21061942c600800524010b10c10210506c2c210b0660823560442c030c0042c010608408650b18020017d08448130b00415480b0841001880442c630800430010b08418213f084481b0b004d013560842c031000c2c11
|10=>0x504c2c210b04410190b00420010618820015206c10010406420010b0442c1b0b0442c230b08420011208c2c01470842c1b0b04418010400420010b10410210b52810010408410190b0641021040841801750442c230b06410010b41418012f00c2c110b0442c210b00418210b06420010b10c10210506c2c211203c2c011006c10212f08c2c110500c2c211100c1019
|11=>0xb5241001470042c1b1204c2c010b52010010b04410212f06c2c110b10010210441418010506c2c210418820012f00c2c11560842c030b04c2c210b06418010b0441001560442c031000c1021027c42c13050042c210b0442c21060841021061882001060842c190b00410197c0842c130500c2c211203c2c010b0842c1b1108410190d0842c19044742c1b0b0841801
|12=>0xb04c2c110b00c10210b0042c1b0b08c10010800410191108c10190b08410015208c1001040842c030b0042c110b0842c190b52c10010b18820010b0041801041882001050442c210400418014108418010418420010b00410210b0442c191206c2c017c0042c130b06c10210608410190b08418210b04420010b18020010b1141019080041801750042c230b0841019
|13=>0xb0641801060842c21
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x350085000000001100040000000
|7,0=>0x25d093400008f422d0892220485320500001f507c1000000000007931d507141b500001a50000198c000189000017905a416080000000544144c000138c4a411cc000000000010d0000100c3e20f083930d503140b502940950000088c000079000000001a4064400000001540000114
|7,1=>0xab429d0a3427d09b4
|8,0=>0x5b0d693598d633580d5d3568d573550d513538d4b3520d453508d3f34f0d3934d8d3334c0d2d34a8d273490d213478d1b3460d153448d0f3430d093418d033400cfd33e8cf733d0cf133b8ceb33a0ce53388cdf3370cd93358cd33340ccd3328cc73310cc132f8cbb32e0cb532c8caf3
|8,1=>0x8a8e273890e213878e1b3860e153848e0f3830e093818e0338085ff37f0df937d8df337c0ded37a8de73790de13778ddb3760dd53748dcf3730dc93718dc33700dbd36e8db736d0db136b8dab36a0da53688d9f3670d993658d933640d8d3628d873610d8135f8d7b35e0d7535c8d6f3
|8,2=>0x26f39b0e693998e633980e5d3968e573950e513938e4b3920e453908e3f38f0e3938d8e3338c0e2d3
|9,0=>0xbc0aee2bb0aea2ba0ae62b90ae22b80ade2b70ada2b60ad62b50ad22b40ace2b30aca2b20ac62b10ac22b00abe2af0aba2ae0ab62ad0ab22ac0aae2ab0aaa2aa0aa62a90aa22a80a9e2a70a9a2a60a962a50a922a40a8e2a30a8a2a20a862a10a822a00a7e29f0a7a29e0a7629d0a722
|9,1=>0xcd0b322cc0b2e2cb0b2a2ca0b262c90b222c80b1e2c70b1a2c60b162c50b122c40b0e2c30b0a2c20b062c10b022c00afe2bf0afa2be0af62bd0af22
|10,0=>0xd0c7421d047401cfc73e1cf473c1cec73a1ce47381cdc7361
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x24600000020200000020000000010a0000001000000000e20000000e00000000d70000000d40000000d20000000cd0000000c60000000c000000008000000007400000004800000004000000003400000002600000002100000001800000001400000001200000001000000000b00000000a000000008000000006000000005000000004000000002000000000
|1=>0x1809f0000130080000112ff0000112f70000112df0000110ff0000110df0000102d000001011a0000100f70000090df0000050df0000040df0000030e5000002008000001ce90000018ff0000012ff0000012f70000010ff0000010f70000010df0000010d700000106e0000010200000010040000008e00000008df00000046a0000002e60000002ca0000002c6
|2=>0x506cf0000500df0000454f70000450f70000450df00004508f00004440f0000420df000041cef0000418ff0000418ef0000414df0000411ff0000410ff0000404df00004041d0000402df0000401df0000400ff00003008e0000240540000210ff0000210df0000210bd0000210740000202f40000202d40000200f0000020080000020074000020054000020040
|3=>0x1210ff0001210df0001200df0001200240001101f70001012c40001011df0001011d70001010df0001010dd0001000e00000d16df0000918df0000912df0000808840000800e00000720f70000700f50000700d70000650d70000610f70000600f70000600540000530ef0000520ff0000520df000051ccf0000510ff0000510ef0000510cf000050cff0000508ff
|4=>0x3000c000023008200022004a0002200320002200220002100ff0002100f70002100df0002001b20002001b00002001580002001120001f13df0001710f70001710f50001701f70001700f70001611df0001611d70001610df0001600f70001600d70001510ff0001509ff0001419ff0001419fb0001411f70001411df0001400f70001300df0001211f70001211df
|5=>0x41210df0041112d70041011df0041011d50041010df00410051f0041001f70041001df0041000d70040700d70040610d70040500f70040410d70040011d70040011970040010ff0040001c20040000e800400007000180145f0018010df00180105f0014912ff0014010ff0014010df001401057000c010d70004010f70004010df00040105f0003004df0003000df
|6=>0x400400ff0400000c40400000800203300df0203210df0203204df02032041f0203100df0203010df0202000ff0201912df0201411f70201210db0201200df0201200d70201000df0200200c00100454df0100414df0100410df0100050f70100010d70080200180060010ff0043100f70043011f70043011df0043010df0043009df0043005df0043000f70042012d7
|7=>0x8020010ff5000000f72020010df1020010df08040105f0500000000404211df0401610f70401600f70401411ff0401410ff0401401df0401400f70401311df0400610f70400600f70400600d7
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x40b000009040000
|7,0=>0x969032040130a00120d1c1d0f3f000a1b00000002160c43002600020004000a092700001201001e0b0800000033000f01050104040c100e000600300000073100000c0015
|8,0=>0x42b89f59deac762a6d5fed21c082eb23b9ec4bae5e55d12a6e142257c8993e78e0b2a5caa3634da27196ad869c7bb62a7745532a6b7ca62aaf4462504ca8b1689d7ea1ba77751a284170cf5edd355899d3831139372929916a341fe14e8b44947db4b39817aa4d6b48ea4297c949ab9e7a19dfd64defcd25a49a52952aed479b
|8,1=>0x4d4616322a2a5a7765ee8ae22a574f49bc22c138d97c5e
|9,0=>0xd2e9e8bb2ecc493a736fb588618fbe843b3dc6dacd922a7e603ddbe33c932a79842a885b908134b02f807ec7f02d8dc26754d54a3aa95da1cd85568e7e3a66e5dcd4bf3a725c878fbde6a0c5c37fe773894a74642a5ba7b88ccbd82ace2ed7c43a6c
|10,0=>0x2a24512a2c8e2ab73b2b2ce436d0
|11,0=>0x18
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 36 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_221 10 roots_221 ops++addP pm 1 dom_222 9 roots_222 ops++addP pm 2 dom_159 9 roots_159 ops++addP pm 3 dom_206 7 roots_206 ops++addP pm 4 dom_215 9 roots_215 ops++addP pm 5 dzo_79_128 6 roots_79 ops++addP pm 6 dom_95 9 roots_95 ops++addP pm 7 dom_219 10 roots_219 ops++addP pm 8 dzo_214_8 6 roots_214 ops++addP pm 9 dom_75 5 roots_75 ops++addP pm 10 dom_158 7 roots_158 ops++addP pm 11 dom_94 7 roots_94 ops++addP pm 12 dom_207 8 roots_207 ops++addP pm 13 dom_31 5 roots_31 ops++addP pm 14 dom_143 5 roots_143 ops++addP pm 15 dom_203 7 roots_203 ops++addP pm 16 dzo_95_128 7 roots_95 ops++addP pm 17 dzo_151_8 6 roots_151 ops++addP pm 18 dzo_150_8 5 roots_150 ops++addP pm 19 dom_74 4 roots_74 ops++addP pm 20 dzo_215_8 7 roots_215 ops++addP pm 21 dom_150 5 roots_150 ops++addP pm 22 dzo_203_4 6 roots_203 ops++addP pm 23 dzo_218_4 6 roots_218 ops++addP pm 24 dzo_91_128 6 roots_91 ops++addP pm 25 dom_205 6 roots_205 ops++addP pm 26 dom_151 6 roots_151 ops++addP pm 27 dom_199 5 roots_199 ops++addP pm 28 dom_142 4 roots_142 ops++addP pm 29 dom_214 6 roots_214 ops++addP pm 30 dom_87 6 roots_87 ops++addP pm 31 dom_155 7 roots_155 ops++addP pm 32 dzo_213_8 6 roots_213 ops++addP pm 33 dzo_77_128 5 roots_77 ops++addP pm 34 dzo_93_128 6 roots_93 ops++addP pm 35 dzo_149_8 5 roots_149 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_223 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_79_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_214_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_95_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_151_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_150_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_215_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_203_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_218_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_91_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_213_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_77_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_93_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_149_8_148 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_221 10 s (0,roots_221.map (·&&&dom_221)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_223 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_221 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_223 gM v ys):RunD true dom_223 gM v (ori ys):=h
def Z (s:Nat):=barP dom_223 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 69 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 69 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 151 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 23 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 151 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 98 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 98 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 14 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 14 0 = true)
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
def dzo_111_128:=0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000
def gzo_111_128:=0xffff0000fffe0000ffff0000fefc00000000000000000000000000000000
def gsh_111_128:=0xffff0000fffe0000ffff0000fefc
theorem lowS_zo_111_128_73:Lower true dzo_111_128 roots_111 gzo_111_128 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_128) [(dom_111,128)] (by decide +kernel) (lower_slice_b (T:=gsh_111_128) [(0xcccc0000cccc0000cccc0000cccc,0,2),(0xf0f00000f0f00000f0f00000f0f0,0,4),(0xffff000000000000ffff00000000,0,32)] (by decide +kernel) lowS_73)
def dzo_105_128:=0x30300000303000003030000030300000000000000000000000000000000
def gzo_105_128:=0x30300000302000003030000020000000000000000000000000000000000
def gsh_105_128:=0x303000003020000030300000200
theorem lowS_zo_105_128_73:Lower true dzo_105_128 roots_105 gzo_105_128 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_128) [(dom_105,128)] (by decide +kernel) (lower_slice_b (T:=gsh_105_128) [(0x303000000000000030300000000,0,32)] (by decide +kernel) lowS_73)
def dzo_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0
def gzo_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0e00000f0f00000e000
def gsh_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0e00000f0f00000e00
theorem lowS_zo_235_4_75:Lower true dzo_235_4 roots_235 gzo_235_4 7:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_4) [(dom_235,4)] (by decide +kernel) (lower_slice_b (T:=gsh_235_4) [(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f00000000,0,32),(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_75)
def dzo_175_64:=0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000
def gzo_175_64:=0xffff0000fffe00000000000000000000fffe0000ffee0000000000000000
def gsh_175_64:=0xffff0000fffe00000000000000000000fffe0000ffee
theorem lowS_zo_175_64_164:Lower true dzo_175_64 roots_175 gzo_175_64 7:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_64) [(dom_175,64)] (by decide +kernel) (lower_slice_b (T:=gsh_175_64) [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,0,1),(0xcccc0000cccc00000000000000000000cccc0000cccc,0,2),(0xff000000ff0000000000000000000000ff000000ff00,0,8)] (by decide +kernel) lowS_164)
def dzo_231_8:=0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00
def gzo_231_8:=0xff000000ff000000ff000000fe000000ff000000ff000000fe000000ee00
def gsh_231_8:=0xff000000ff000000ff000000fe000000ff000000ff000000fe000000ee
theorem lowS_zo_231_8_164:Lower true dzo_231_8 roots_231 gzo_231_8 7:=lower_iso_b (d1:=dom_231) (r1:=roots_231) (T1:=gsh_231_8) [(dom_231,8)] (by decide +kernel) (lower_slice_b (T:=gsh_231_8) [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,0,1),(0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc,0,2),(0xff000000ff0000000000000000000000ff000000ff0000000000000000,0,64)] (by decide +kernel) lowS_164)
def dzo_167_64:=0xff000000ff0000000000000000000000ff000000ff0000000000000000
def gzo_167_64:=0xff000000fe0000000000000000000000fe000000ee0000000000000000
def gsh_167_64:=0xff000000fe0000000000000000000000fe000000ee
theorem lowS_zo_167_64_164:Lower true dzo_167_64 roots_167 gzo_167_64 6:=lower_iso_b (d1:=dom_167) (r1:=roots_167) (T1:=gsh_167_64) [(dom_167,64)] (by decide +kernel) (lower_slice_b (T:=gsh_167_64) [(0xaa000000aa0000000000000000000000aa000000aa,0,1),(0xcc000000cc0000000000000000000000cc000000cc,0,2)] (by decide +kernel) lowS_164)
def dzo_167_8:=0xff000000ff0000000000000000000000ff000000ff00
def gzo_167_8:=0xff000000fe0000000000000000000000fe000000ee00
def gsh_167_8:=0xff000000fe0000000000000000000000fe000000ee
theorem lowS_zo_167_8_164:Lower true dzo_167_8 roots_167 gzo_167_8 6:=lower_iso_b (d1:=dom_167) (r1:=roots_167) (T1:=gsh_167_8) [(dom_167,8)] (by decide +kernel) (lower_slice_b (T:=gsh_167_8) [(0xaa000000aa0000000000000000000000aa000000aa,0,1),(0xcc000000cc0000000000000000000000cc000000cc,0,2)] (by decide +kernel) lowS_164)
def dzo_107_128:=0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000
def gzo_107_128:=0xf0f00000f0e00000f0f00000e0c00000000000000000000000000000000
def gsh_107_128:=0xf0f00000f0e00000f0f00000e0c
theorem lowS_zo_107_128_73:Lower true dzo_107_128 roots_107 gzo_107_128 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_128) [(dom_107,128)] (by decide +kernel) (lower_slice_b (T:=gsh_107_128) [(0xc0c00000c0c00000c0c00000c0c,0,2),(0xf0f0000000000000f0f00000000,0,32)] (by decide +kernel) lowS_73)
def dzo_230_8:=0x550000005500000055000000550000005500000055000000550000005500
def gzo_230_8:=0x550000005500000055000000540000005500000055000000540000004400
def gsh_230_8:=0x5500000055000000550000005400000055000000550000005400000044
theorem lowS_zo_230_8_164:Lower true dzo_230_8 roots_230 gzo_230_8 6:=lower_iso_b (d1:=dom_230) (r1:=roots_230) (T1:=gsh_230_8) [(dom_230,8)] (by decide +kernel) (lower_slice_b (T:=gsh_230_8) [(0x4400000044000000440000004400000044000000440000004400000044,0,2),(0x5500000055000000000000000000000055000000550000000000000000,0,64)] (by decide +kernel) lowS_164)
namespace S_239
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,10),(2,34),(2,66),(2,130),(3,11),(3,35),(3,67),(3,131),(4,36),(4,132),(5,13),(5,37),(5,69),(5,133),(6,14),(6,38),(6,70),(6,134),(7,15),(7,39),(7,71),(7,135),(8,9),(8,10),(8,72),(12,13),(12,14),(12,44),(12,76),(12,140),(32,33),(32,34),(32,36),(32,160),(40,41),(40,42),(40,44),(40,104),(40,168),(64,65),(64,66),(64,72),(68,69),(68,70),(68,76),(68,100),(68,196),(96,97),(96,98),(96,100),(96,104),(96,224),(128,130),(128,132),(128,160),(129,131),(129,133),(129,137),(129,161),(129,193),(136,137),(136,138),(136,140),(136,168),(136,200),(192,193),(192,194),(192,196),(192,200),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffffffffffffffff
def xsM:=roots_239.map (·&&&dom_239)
def gM:=goal_239&&&dom_239
def NN:Nat→Nat
|5=>7
|6=>14
|7=>41
|8=>119
|9=>100
|10=>14
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xa3dd0754fc48afa47747328842bafe2a84e
|6,0=>0xef27be8d25d7a8d6aea05ebc04801543abc42709258101e0fd19fdc13e35109380d644
|7,0=>0xf9ac7f8606f688ae30d3dcfb0d9e9cd47dccf7ebcc4f7c4036c275db1154ae12ea8373a71f1a68b4a48e59a9fb927e691b578cea88cbdf83c3b80bc878b387799173eb4723246dc0669765651704b61f42fd73e5f13bc9332b5c1da731bd000c358030f90043c
|8,0=>0xffc30ff7c2feaaefdbdcfd4a4fbaa1f9ac7f8c64f702bf527eef3b3ef073ee035ec398e6c31e45ede1ec0e0986daa3dcf0e7ce579cb20bca37bc9a8bc91f9c7d6bbe546ba8a9b897ab76a4b3a87af5edaa676a9d35a6d39a2ecca1f869f4ce9b2aa98d4f975bc966df9085f8e6748be3188f268840a83ff0830d1820d9818c07ff1d7fbdb7cf5178075772d4735ab6eead6e60a6c5db68992683ea65767632bd60b3f5e73b5ca615a9b65a6865a1585701c554d252919522c1520c450a0a4e1474c95c4ba924b39e4577a4556b453b045138409c1408c23fa7b3c6cf37e4d36844362e33564f34957311d73104a2fc492ecea2e2c72b48e2afac2adc728bee26797264af251012118720c3d1d2621c4e61bacf18892145ca140d5126ff0b35c0a4d205797036d60286c
|9,0=>0xff874fc50dfbfeef718df6a26f6695f5196ed4d8eb8d7e9c7ae564ae003adff84db399da982d6956d347dc5ec6c5a83c1783be675bca8fbbdf8ba954b897ab7b17b59e6b53f9b4131b22ceab24baab8caa6caa7f61a5ae4a11b1a0d739ef599d37a9b28b96e4c93b0b8f2cc8f1d48d42c89fc08760c8722d7ad9d765576fb156cdc36cab36952967bd26684c661c2632bd61d7f5f83e5646f5556751dda513845033d4a8aa4955946b45465ae44c0d4280940f8c3fbd23acd8397a5358fb33d793245e324592ea252c8862b7042b48e29a3528ad028661227c6221ca21bbb21ba21bacf1ae5116ed71529512bd7117cc1144210f770a6b705f60
|10,0=>0xe88e8da982cacf5bb3c099ed2806367dfda704995dbf355cff460e02b9661023701464
|11,0=>0x3ce8d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000000000000000fefe0000fefe00000000000000000000fefe0000eeeeffff0000ffff0000fcfc0000fcfc0000ffff0000ffff0000fcfc0000cccc00ff000000ff000000fc000000fc000000ff000000ff000000fc000000ccfffc0000fffc0000fffc0000fffc0000fffc0000ffcc0000fffc0000ffccffff0000ffff0000ff000000ff000000ffff0000ffff0000ff000000ff000000000000000000fffe0000fffe00000000000000000000fffe0000ffeefcfc0000fcfc0000fcfc0000fcfc0000fcfc0000cccc0000fcfc0000ccccfffe0000fffe00000000000000000000fffe0000ffee0000000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000ffff0000ffff0000fffc0000fffc0000ffff0000ffff0000fffc0000ffccff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00fefe0000fefe0000fefe0000fefe0000fefe0000eeee0000fefe0000eeeeffff0000ffff00000000000000000000ffff0000ffff0000000000000000ffff0000ffff0000ffff0000ffff00000000000000000000000000000000
|0,1=>0x55550000555500005500000055000000555500005555000055550000550000000000000000000000000000000000ffff000000000000ffff0000000000000000ffff000000000000ffff00000000000000000000000000000000f0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f0000000f00000000000000000000000000000000000000000ffff000000000000ff00fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000cccc0000fcfc0000ccfc55550000555500005555000055000000555500005555000055550000550000000000ffff000000000000ffff0000ffff000000000000ffff00000000000000000f0f0000000000000f0f00000f0f0000000000000f0f00000000fffe0000fffe0000fffe0000fffe0000fffe0000ffee0000fffe0000ffeeffff000000000000ffff0000000000000000000000000000000000000000ffff0000cccc0000ffff0000cccc0000cccc0000cccc0000cccc0000cccc0f0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000f0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f000000000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000ccccffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000
|0,2=>0x555500005555000055050000550000005555000055550000550500005500ffff000000000000ffff000000000000000000000000000000ff0000000000000000000000000000000000000000ffff0000ffff0000ff000000ff00ffff0000ffff0000ffff000000000000ffff0000ffff000000ff00000000555500005555000055550000555500005555000055550000555500005500ffff0000f0f00000ffff0000f0f00000ffff0000f0f00000ffff0000f0f0ffff0000ffff0000ffff0000ffff0000f0f00000f0f00000f0f00000f0f0ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff00f0f00000f0f00000f0f00000f0f00000f0f00000ffff0000f0f00000fff00f0f00000f0f00000f0f00000f0f00000000000000000000000000000000ffff00000f0f0000ffff00000f0f0000ffff000000000000ffff000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000ffff0000ffff0000ff000000ff000000ffff0000ffff0000ffff0000ff00
|0,3=>0xffff000000000000ffff000000000000f0f0000000000000f0f0000000000000000000ff000000ff0000000000000000000000f0000000f0aaaa0000aaaa0000aaff0000aaff0000aaaa0000aaaa0000aafa0000aafa0f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f00ffff0000f0f00000ffff0000f0f00000f0f00000f0f00000f0f00000f0f0ffff0000ffff0000ffff0000fff00000ffff0000ffff0000ffff0000fff0555500005555000055550000555000005555000055550000555500005550ffff000000000000ffff000000ff0000000000000000000000000000000000000000ffff000000000000ff00000000000000ffff000000000000ff00ffff0000aaaa0000ffff0000aaff0000aaaa0000aaaa0000aaaa0000aaaaf0f00000f0f00000f0ff0000f0ff000000000000000000000000000000000f0f00000f0f00000f0000000f0000000f0f00000f0f00000f0000000f00fafa0000fafa0000faff0000faff0000aaaa0000aaaa0000aaaa0000aaaaffff0000ffff0000ffff0000ffff00000f0f0000000000000f0f00000000ffff0000ffff0000ff0f0000ff000000ffff0000ffff0000ff0f0000ff00ffff0000ffff00000f0f000000000000ffff0000ffff00000f0f00000000
|0,4=>0xff0f0000ff000000ff0f0000ff000000ff0f0000ff000000ff0f0000ff000000000000000000ff0f0000ff0000000000000000000000ff0f0000ff00ffff0000aaaa0000ffff0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000000000000000ffff0000ff0000000000000000000000ffff0000ff00ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff000f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f0f00000f0000000000ffff000000000000ff000000ffff0000ffff0000ff000000ff00ffff0000ffff000000000000ffff0000ffff0000ffff000000000000000000ff000000ff00000000000000ff000000ff000000ff0000000000000000ffff0000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff00ffff000000000000ffff000000000000ff00000000000000ff0000000000ffff0000ffff0000ffff000000000000ffff0000ffff000000000000000000ff000000ff000000ff00000000000000ff000000ff0000000000000000333300003333000033330000333300003333000033330000333300003300ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff00ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000
|0,5=>0xff0f0000ff0f0000ff0f0000ff000000ff0f0000ff0f0000ff0f0000ff00ffff0000ff000000ffff0000ff000000ff000000ff000000ff000000ff000000000000000000ffff0000ff0000000000000000000000ff000000ff00ffff00000f0f0000ffff00000f000000ffff00000f0f0000ffff00000f00ffff0000ffff0000ffff0000000000000000000000000000000000000000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff000000ff00ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000000000000ffff0000ffff00000000000000000000ffff0000ff000000000000000000ffff0000ffff00000000000000000000f0f00000f0f0ff000000ff000000ffff0000ffff0000ff000000ff000000fff00000fff0ffff0000ffff0000ffff0000ffff0000ffff0000f0f00000ffff0000f0f0000000000000000000ff000000000000000000000000000000ff00000000ffff0000ffff0000ff000000ffff00000000000000000000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000ffff0000ff000000ffff0000ff000000ffff0000ff000000000000000000
|0,6=>0xffff0000ffff0000ffff0000ff0000000000000000000000000000000000f0f00000f0f00000f0ff0000f0ff0000f0f00000f0f00000f0f00000f0f0ffff0000ffff0000ff000000ff000000ffff000000000000ff000000000000000000000000000000000000000000ffff0000ffff0000ffff00000000ff000000ff000000ff000000ff000000ffff0000ffff0000ffff0000ff00000000000f0f0000000000000f0f00000000000000000000000000000000f0f00000ffff0000f0f00000ffff0000f0f00000f0f00000f0f00000f0f0ffff000000000000ff00000000000000ffff000000000000ff0000000000ffff0000ffff0000ffff0000ffff0000ffff000000000000ff00000000000000000000000000ffff0000ffff00000000000000000000000000000000ffff0000ff0000000000000000000000ffff0000ff000000ffff0000ff0000000000000000000000000000000000ffff0000ffff0000ffff0000ff00000000000000000000ff000000ff00000000000000000000000000000000ffff000000000000ffff000000ff0000ffff000000000000ffff00000000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ff000000ff000f0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f00000000
|0,7=>0xffff0000ffff0000ffff0000ff000000ffff000000000000ffff00000000ffff0000ffff0000ffff000000000000ffff0000ffff0000ff00000000000000000000000000000000000000000000ff00000000000000ff00000000ffff0000ffff00000000000000000000ffff0000ffff000000ff00000000ffff000000000000ffff0000ffff0000ffff000000000000ffff00000000ffff0000ff000000ffff0000ffff0000ffff0000ff000000ffff0000ff00ffff0000ffff00000f0f00000f0f0000ffff0000ffff000000000000000000ff000000ff0000000f0000000f000000ff000000ff0000000000000000ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff000000ff00ffff0000ffff0000ffff0000ffff00000f0f00000f0f00000f0000000f00000000000000000000000000000000000000000000000000ffff00000000ff000000ff000000ff000000ff000000ff000000ff00000000000000ff0000000000ffff000000000000ffff000000000000ff00000000000000ff00000000000000000000000000ffff0000000000000000000000000000ff00aaaa0000aaaa0000aaff0000aaff0000aaaa0000aaaa0000aaaa0000aaaaffff0000ffff000000ff000000000000ffff0000ffff000000ff00000000
|0,8=>0xffff0000ffff0000f0f00000f0f00000ffff0000ffff0000f0f00000f0f0ffff0000ffff0000f0f00000f0f000000000000000000000000000000000ffff000000000000ff00000000000000ffff0000ffff0000ff000000ff00ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000fff00000fff0000000000000000000ff000000000000ffff000000000000ffff000000000000000000000000ffff0000ffff00000000000000000000ffff00000000ff000000ff000000ffff0000ffff0000ff000000ff000000ffff0000ff00ffff0000ffff00000000000000000000ffff0000ffff0000ffff0000000000ff000000ff0000000000000000000000ff000000ff000000ff00000000ffff0000ffff0000ff000000ff00000000000000ffff000000000000ff00ffff000000000000ffff000000000000ffff0000ffff0000ffff0000ff00ff00000000000000ff00000000000000ffff000000000000ffff0000000000ff000000ff000000ff000000ff00000000000000000000000000000000ffff0000ffff0000ff00000000000000ffff0000ffff0000ffff00000000ffff0000ffff0000ffff0000ffff0000000000000000000000ff00000000ffff0000ffff0000ff000000ff0000000000000000000000000000000000
|0,9=>0xff00000000000000ff0000000000000000000000000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000ff000000ffff0000ff000000ffff0000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0000f0f00000f0f0ff000000ff000000ffff0000ffff0000ff000000ff000000ff000000ff0000000000ffff000000000000ffff000000000000ffff00000000000000000000000000000000ffff0000000000000000000000000000ffff00000000ff000000ff000000ffff0000ff000000ff000000ff000000ffff0000ff00f0f00000ffff0000f0f00000ffff00000000000000000000000000000000000000000000000000ff000000ff0000000000000000000000ff00000000ffff000000000000ff00000000000000ffff000000000000ffff00000000ffff0000ffff0000ffff0000ffff000000000000ffff000000000000ff0000000000f0f0000000000000f0f00000f0f00000f0f00000f0f00000f0f00f0f00000f0f00000f0f00000f0000000f0f00000f0f00000f0f00000f00ffff0000ffff0000ff0f0000ff0f0000ffff0000ffff0000ff000000ff0000000000ffff000000ff0000ffff00000000000000000000000000000000
|0,10=>0xff0f0000ff0f0000ff0f0000ff0f0000ff000000ff000000ff000000ff00ff000000ffff0000ff000000ffff0000ff000000ff000000ff000000ff000f0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00ffff0000ffff0000ffff0000ffff000000ff00000000000000ff00000000ffff0000ff000000ffff0000ff0000000000000000000000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000f0f00000f0f0f0ff0000f0ff0000f0ff0000f0ff0000f0f00000f0f00000f0f00000f0f000ff000000ff000000ff000000ff000000ff00000000000000ff00000000ffff0000fff00000ffff0000fff00000ffff0000fff00000ffff0000fff000000000fff0000000000000fff0000000000000fff0000000000000fff000000000000000000000000000000000ffff0000ff000000ffff0000ff00ff000000ffff00000000000000000000ff000000ffff0000000000000000fff00000fff00000fff00000fff00000fff00000fff00000fff00000fff0000f0000000f0000000f0000000f0000000000000000000000000000000000ff000000ff000000ff000000ff000000ff000000ff000000000000000000000000ff00000000000000ff000000ff000000ff000000ff000000ff00
|0,11=>0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ff00ffff0000ffff0000fff00000fff00000ffff0000ffff0000fff00000fff00f0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f0000ff000000ff000000f0000000f0000000ff000000ff000000f0000000f0
|_,_=>0
def sP:Nat→Nat
|0=>0xc0e010005031a0e010005031119130100180903110e1301050a030201000503070e0b0100050a09070e0100050403070e0100100903110e1701051603020701000503020d07010005090302070100100903140e1301050a090c0e000503020d0c000503020b0100050a09020100050803020700050302070600050403020100
|1=>0x10050903070e010005030f11330100050903110e32012405030f112f010005030f110e2c0005030f112b0100100903110e220124050a03070e01002a10090329110e01050327110e010005030f11190100241803110e1301050325110e0100230903110e2201000503110e1321010005030f111f0100180903110e1701050a03
|2=>0x701001003140e130105031c110e010005030f111901001d030f110e213f01001803110e17010503110e13370100414003110e130100100903110e13011526030f110e3f010005030f113d01000503110e3c01001009030f140e011005030f111901001009033b110e0105030f11390100101809030f110e0105030f11360100
|3=>0xe0100261005030f110e01000509030f114d01004c05030f110e0100240503110e4a01000549030f110e01001003110e22012405030f110e01470041450f110e010005030f110e014300050903110e1301000503290f11190100260503110e1301001809030f110e011003110e1701050903070e010005030f0e420100050302
|4=>0x55a030f110e010005030f110e2e0100050358110e01005705030f110e010005030f110e440040030f110e3f01001009030f110e01150555030f110e0100540509030f110e010005030f110e0100521005030f110e210100100509030f110e012405030f110e015000054e030f110e0100050903290f110e011d100509030f11
|5=>0xe010010033b110e016505030f110e01003a05030f110e01006405030f110e01006205030f110e01002005030f110e01001005090312110e01000561030f110e44001018030f110e01055f030f110e0100055e5d0f110e0100100503070e01001e09030f110e011d5c05030f110e0100414003290f110e01000503110e320124
|6=>0x117101001003110e13011505030f110e700005030f110e515b05030f110e01003805030f110e01006f05030f110e2101001d05036e0f110e010005036d0f110e010005030f110e3e01006b05030f110e01000509030f110e01006a0561030f110e0100050903690f110e010010030f140e012605030f110e01001d0503670f11
|7=>0x8101007f05030f110e0100260503290f110e010005037e0f110e01000509030f110e13010005030f110e7c007a05030f110e010005030f110e017800400503110e1301000577030f110e010005030f110e7601000509030f110e3f01004140030f110e010024050f110e7401000509030f110e440005030f110e72010005030f
|8=>0x22010024058c030f110e0100058b030f110e01002a05090329110e01008905030f110e010005030f110e87010005090312110e010018030f110e0105030f110e8601008505030f110e01000503070e010010050903110e13010005030f110e0100350503290f110e2101000531030f110e01008205030f110e010005030f110e
|9=>0x10050903290f110e0105030f110e920100230509030f110e01000591030f110e01002805030f110e010005030f110e0100901009030f110e2201002303110e2201001005030f110e37010005030f110e1b0100414010030f110e010005030f110e518e2605030f110e010024058d030f110e01000503110e130100050903110e
|10=>0x110e01004105030f110e01001d05030f110e3701001d0509030f110e0100974140030f110e01001d0509030f140e01002a100329110e012a1009030f110e0100050903110e1301000509033b110e010005030f110e9601000509030f110e32010005030f111901000595030f110e010005030f110e94010005090393110e0100
|11=>0x2a0509030f110e010005a00f110e010005030f110e01009f05030f110e01009d4005030f110e01008305039c0f110e0100059b030f110e0100100509030f110e01000503450f110e010005030f110e01008e05030f110e019a0005030f110e01006305030f110e01006a9805030f110e01000503690f110e0100400503290f
|12=>0x5030f110ea80100a705030f110e01004005030f110e01002405a3460f110e010005030f110e130100a505030f110e010005030f110ea6010005030f56110e010041a505030f110e010005030f110ea40005030f110e3f010005030f110e0100a205030f110e01a10005030f110e3701004140030f110e010005030f110e44
|13=>0x30f110ead0100051e09030f110e01002a050329110e01004005038f0f110e0005030f110eac01004105030f110e51010005030f110e7000050312110e010005030f110e0100ab100503110e1301004105030f110e0100ab0546030f110e01660509030f110e01001d0503aa0f110e01000575030f110e01000503a90f110e01
|14=>0x1002305030f110e0100401005030f110e01004005030f110e60010005ae030f110e01000509030f110e0100157b05030f110e01004005a3030f110e01008805030f110e010010030f110e2201005905030f110e010005030f110e210100050903290f110e01002605030f110e01000503110e2201002405030f110e44010005
|15=>0x110e01002405030f110e01009705030f140e010005030f110eb001002a10030f110e01000503110e13010005033b110e01000584030f110e010005af030f110e010005030f110e32010005030f110e010080050393110e010040030f110e9e01004105460f110e0100052d030f110e0100100503290f110e010546038f0f110e
|16=>0x5030f110e01000503680f110e010005b3030f110e01001e030f110e011d05a3038f110e01000546030f110e510110030f110e01155405030f110e01001005030f110e012405b2030f110e01000503290f110e011d1005030f110e010005030f110e53010005030f114d010005030f110e30010005030f110eb101000509030f
|17=>0xf110e010005a3030f110e010005030f110e2201000599030f110e010005030f110e0100240509030f110e010005030f110e51010005030f110e01008305030f110e0100150503290f110e0100051e030f110e010005030f110e01001d4005030f110e010010050312110e01000509030f110e22010005030f110e3401004140
|18=>0x5030f110e01002a05030f110e0100100503
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x24601e60186012600c600660006
|6,0=>0x83707c7076606f70687062605b7054704d7046703f70387031702a7
|7,0=>0x1ae81a6819e81977191618a7183717d6177617071688160815a6152814a8142813a8133712c7125711d8116710f7107810070f880f170e980e270db70d470cc80c570bd80b670ae80a860a170998091808a7
|8,0=>0x3ac83a3939a9393738b8383837c7375736e7367735f8357834e9346833e8336832e8325931d8314930e630592fd82f762ef82e782df82d782cf82c692be82b772af82a782a072988290828792807278827082697261825a7252824a8242823992318228921f9217820f820691fd91f491ec81e391dc71d481cd71c581be71b68
|8,1=>0x56a95619558955085497540953885308528851f951875108508850084f794ef84e694de84d684ce84c594be74b594ad84a4949d7494948c8485747c9474846c8463945b8453844b8445643d8435842f6426941e8415940d840583fd83f583ec93e483db93d473cc83c483bc83b48
|9,0=>0x776876d9764975c8753974b8742973a8732872a8722871997118709870186f986f096e886e086d886cf96c876c176b986b186a896a08697968f8687867f8677866f8666965e8656864e8646863e8635962e7626861e8616860e860685ff75f695ef75e785df85d695ce85c685bd95b585ad85a5859d8595858d8585857c95739
|9,1=>0x893888a98828879987188698862785a8852884b7843883b8833882b8823881b8814780c880487fb97f387ec77e487dc87d577ce77c687be87b687ae87a7779f8797878f8787877e9
|10,0=>0x90388fb88f388eb88e388db88d388cb88c388bb88b388ab88a3889b8
|11,0=>0x90b7
|_,_=>0
def wAt:=mkWire dB 180 240 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xf008143f05014403f05004803b1e094140303014603f1e1d41403050081c05070344845100f014011c1143c6f100980c0505004405705000403f050041c39070344845100f01401030141c0d12114403c05004603f1015c1401050001c3912114403c050040807070e44845100f01401030141c3912114403c05004403f111541401050001c05070344845100f01401
|1=>0xf15414003a0eca82503014143d1015c14010301414000e384dc02050980c05121140c05100f014010e354d002090fc0c05220043c02050fcc43b033048805050fcb805052dc240303014a03b100940c0505004143f050043c02070344845100f01401050f40c050f0041401280f04025030141401260ec142503014405705000403f050043c6d100980c05050041491
|2=>0x500840ef050043c55050000c0512114403c05004a047100940c05050041c3912114403c05004403f050044455050003c6f100980c0505004983b0301414a60f0041405180fc78750500c140205098403f05004403f05034140505004403f050041400052983c01050940c050e3e424a6030143c01280fc4025030141401111541401030141400260ec0c05030141401
|3=>0x2a0040c05050f54c020509c0c0505005000f050141401030143c0241510140d01004053e22034143f030143c010500878010500c0c050500414250301438550301414000f0090407050352c3f1003414010915c0c0505000143f0f00814014803c0475050081518050340c010344804550500088910f008143f260ec142503014142503014403f050047875030141403
|4=>0x50f49803050940c050563424020301478250500c0c0503014403c050040d110115414001015c140105001800d400fc1405015e80c55050004845100f014010301414030500814d1090fc0c050f004140d050148801050fc3c02035b500000501414b70900c0c05590f04005050052c071003414014051014050100414a6050143c01050040c05050000d592901c3c01
|5=>0x3014140001738151a03004398d090080c0505000403f050054c050509c0c0540000140501004dc02050980c0526000142503015000f0501414020f6342402030144024030141401092980c050f005b00d4000c14052a0080c05050f42455030141400030143c7505008140111154140005008142503015a001050900c05050043c5505001059b0503404022a0940c05
|6=>0x52d42403030144845100f01401100fc0c0505004d002090fc0c050f005000f050140cc122014143f84014160f030094c010509c0c05058042400030143c01050940c05450141518030040c05100fc14017d014151b03005ec0d0566404027903c04910f0081405100fc1401091d40c0505008d001090fc0c050301414a60f0043c02050341405750381547010040455
|7=>0x52443c02092440c050f0084025030141401680081424030141401050fc0c05050fc14910f0081401050980c05100980c0505004140d0501414018f00004010f0143c02050940c05091dc0c05050088c3f052443c020f008143f092940c050f0041603090000c050f0040c05050f6280d1001c14018803c78050500c0c05100f014011e1d414030500878260500c0c05
|8=>0xf014154601004240203014a802050f6640d0501c3c750500814050f004140d050081402050980c0522008143f030141405050341402111540c0505000143d0f0041401050040c05050f40c05100fc1401030143c5505000402703014140122004143f03014983b050940c050563c240203014dc01050980c050f15c0c05050000c050f0041401260fc1425030140c05
|9=>0x50050400050340c01010080c050500a3c010f0141547010043e0d03008400f05004168d0f03414050f0080c010f034403f05005040305034168e0f034a4070f00504030503678060503c14a60f0068c020f0340d4601004142603014140d050140455050000c05050f40c570500104020503678020503c14050300a3c030f0140d99010080c05050041518030063c00
|10=>0x50fc2400030143c570500014050503c140d030042403030143c01050040c010f01414910f008140505005003f050140c75050080c050500015990100814050f03478050500c143f05004400505005000f050140c050f004142503014143f0f0080455050003d1a030041403030143c01050f414050f01678010503c140d0100678050503c403c05005040005034403f
|11=>0x10040c02050003c010500c140205014403c05004143f03014243f03014140d050141424030140d45010041403050083c050f0340c0101004140105000403d050043c02050068c050f0343c01050081475050081427030143855050008805050fd043f050340c050f0088802050fc4455050023c0f0f014143d05004403f050043c5505000160f030080c910f0088801
|12=>0x143d050043c0d050fc14070f0080c05
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x5000000000000000000000
|6,0=>0xcd02e50a54000095020500001b5000017404d00e50254054
|7,0=>0xca331ccc342fd0bb42dd0b342bd0ab429d0a52288c9e426cc974250c904231088421108221f907a41d907241b906a419cc63417d05b4160c54414104c4124c45410503e30ecc374
|8,0=>0x628d873610d8135f8d7b35e0d7535c8d6f35b0d693598d633580d5d3568d573550d513538d4b3520d453508d3f34f0d3934d8d3334c0d2d34a8d273490d213478d1b3460d153448d0f3430d093418d033400cfd33e8cf733d0cf133b8ceb33a0ce53388cdf3370cd93358cd33340ccd3
|8,1=>0x22e38ace283894e22387ce1c3864e16384ce103834e0a381ce043804dfe37ecdf837d4df237bcdec37a4de6378cde03774dda37609d53748dcf3730dc93718dc33700dbd36e8db736d0db136b8dab36a0da53688d9f3670d993658d933640d8d3
|9,0=>0xabcaad2aacaa92a9caa52a8caa12a7ca9d2a6ca992a5ca952a4ca912a3ca8d2a2ca892a1ca852a0ca8129fca7d29eca7929dca7529cca7129bca6d29aca69299ca65298ca61297ca5d296ca59295ca55294ca51293ca4d292ca49291ca45290ca4128fca3d28eca3928dca3528cca312
|9,1=>0xbdcaf52bccaf12bbcaed2bacae92b9cae52b8cae12b7cadd2b6cad92b5cad52b4cad12b3cacd2b2cac92b1cac52b0cac12afcabd2aecab92adcab52accab12
|10,0=>0xc187051c107031c087011c006ff1bf86fd1bf06fb1be86f91
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x4e97000004c97000003607000002002000001e97000001e87000000ea7000000e97000000c12000000a97000000a200000008920000006a70000006070000006010000004820000004220000004020000004000000002010000002000000001010000000f300000008200000004400000004200000000a000000006000000005000000003000000002000000000
|1=>0x28627000022697000022297000018e270000180f7000010ea700001089200000c6a700000c4a700000b60700000a61700000a237000009eb7000009e870000096a7000009627000009422000008eb7000008e97000008e27000008bf70000088920000086b70000086a70000086870000086270000084020000082a70000080f7000008080000008000000006617
|2=>0x8806a30008086b70008080860008080060004aaeb70004a0eb700042a6b700042a6a700042a6170004286a70004206b700040a627000402082000402002000302e870002196370002096a7000209023000208e370002086b70002086a7000202c83000200ea70001896b70000886a70000886a3000088697000088687000040001000030802000028eb70000286b7
|3=>0x2010627002009607002008ea70020086b70020086a7002008627002000e27002000627001b89637001a88687001a88607001a08687001a006170019086370019006370018806a7001880697001880637001809e87001808687001802c060018024820018010060018008860018004240018004060013086b7001208eb70010026a70008886b70008886a7000888687
|4=>0x42186870042116370042106a70042098a30042098a20042086b70042086a7004208687004200607004018e37004009022003a08607003a006270038806270038006270033206b70032286870032096a7003120687003008ea70029aa687002889607002888e270028886a7002420ea70024006a700232ae87002209627002122687002089607002022687002020687
|5=>0xa00be3700a0086b700a00863700a000002009a806370084086b70083096b7008281637008201617008108eb70080896b700802a6b700800b63700800a6b700800a6a700800a63700800a2370080024020080020020080016170072006270070086270063206870062196070062086270060096270051886170048886870046306b7004309607004308e37004219607
|6=>0x80298ae87800009eb74039ba68740213a687402120687203b306b7203b206872021306b72008a26b7103209e271013096270820006270492006a7048881637046218687042008687041a816370402024230402006a704008a6a70400100220400086a70200086a70200086a601400868700a40863700a3226b700a020687
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x4000000000000
|6,0=>0x1040a0001090007000105030601
|7,0=>0x10d021a3d3b4323201121011d0104011c0b0c1e22160b1415390b010b0c0b0123100c0d360c01010b
|8,0=>0x952f69374010af244dbcc328a0261051adc9b72825549bac685fcaa63f013e28086e45291a29502317196a8228277a4a29ae2991703484c05366284771d03544883c2c5c869649a5c74b521f4e27187a80a27a4c39461b8d4b2b28836b7caa29297347572d6f42285d0f72940e2a9cc467b328ba924c47
|9,0=>0x2ea8a96d27b82881bb2d41b281562e27c58a859d3038d5beb02828cfbd7f26a4659e40d6b1dadb8e997dd962c2b576a3982661c19a408b33776c297dbfd2aba7d35e87648fc890b4b9d85ad1275963cb9f7528cd288c3189d493a1293a4878c674585b4f
|10,0=>0xccb6d77e321397ce792855297b60
|11,0=>0x12
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 36 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_238 10 roots_238 ops++addP pm 1 dom_231 9 roots_231 ops++addP pm 2 dom_175 9 roots_175 ops++addP pm 3 dom_230 7 roots_230 ops++addP pm 4 dzo_111_128 7 roots_111 ops++addP pm 5 dom_111 8 roots_111 ops++addP pm 6 dom_233 7 roots_233 ops++addP pm 7 dom_203 7 roots_203 ops++addP pm 8 dzo_105_128 5 roots_105 ops++addP pm 9 dom_237 10 roots_237 ops++addP pm 10 dom_235 9 roots_235 ops++addP pm 11 dom_75 5 roots_75 ops++addP pm 12 dzo_79_128 6 roots_79 ops++addP pm 13 dzo_203_4 6 roots_203 ops++addP pm 14 dom_109 7 roots_109 ops++addP pm 15 dom_207 8 roots_207 ops++addP pm 16 dom_163 5 roots_163 ops++addP pm 17 dzo_235_4 7 roots_235 ops++addP pm 18 dzo_229_8 6 roots_229 ops++addP pm 19 dzo_175_64 7 roots_175 ops++addP pm 20 dzo_75_4 5 roots_75 ops++addP pm 21 dzo_231_8 7 roots_231 ops++addP pm 22 dom_107 6 roots_107 ops++addP pm 23 dzo_167_64 6 roots_167 ops++addP pm 24 dzo_167_8 6 roots_167 ops++addP pm 25 dzo_107_4 6 roots_107 ops++addP pm 26 dom_167 6 roots_167 ops++addP pm 27 dzo_107_128 6 roots_107 ops++addP pm 28 dzo_230_8 6 roots_230 ops++addP pm 29 dom_206 7 roots_206 ops++addP pm 30 dzo_75_128 5 roots_75 ops++addP pm 31 dom_110 7 roots_110 ops++addP pm 32 dom_199 5 roots_199 ops++addP pm 33 dom_171 6 roots_171 ops++addP pm 34 dom_227 6 roots_227 ops++addP pm 35 dom_143 5 roots_143 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_239 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_111_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_105_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_79_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_203_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_235_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_229_8_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_175_64_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_75_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_231_8_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_167_64_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_167_8_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_107_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_107_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_230_8_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_75_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_143 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_238 10 s (0,roots_238.map (·&&&dom_238)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_239 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_238 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_239==dom_239)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_239 gM v ys):RunD true dom_239 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_239 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 7 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 14 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 41 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 41 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 119 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 119 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 100 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 100 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 14 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_239 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤11) (h:RunD true dom_239 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_239 roots_239 goal_239 12:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_239
theorem lowS_239:Lower true dom_239 roots_239 goal_239 12:=S_239.noCircuit
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_246
def isoMvS_191:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_iso_b isoMvS_191 (by decide +kernel) lowS_127
def isoMvS_251:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_251:Lower true dom_251 roots_251 goal_251 11:=lower_iso_b isoMvS_251 (by decide +kernel) lowS_247
def isoMvS_253:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_239
def isoMvS_254:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_223
def dzo_127_128:=0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
def gzo_127_128:=0xfffffffffffffffefffffffffffffefc00000000000000000000000000000000
def gsh_127_128:=0xfffffffffffffffefffffffffffffefc
theorem lowS_zo_127_128_73:Lower true dzo_127_128 roots_127 gzo_127_128 8:=lower_iso_b (d1:=dom_127) (r1:=roots_127) (T1:=gsh_127_128) [(dom_127,128)] (by decide +kernel) (lower_slice_b (T:=gsh_127_128) [(0xcccccccccccccccccccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0,4),(0xffff0000ffff0000ffff0000ffff0000,0,16),(0xffffffff00000000ffffffff00000000,0,32)] (by decide +kernel) lowS_73)
def dzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0f0f0f0e000
def gsh_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0f0f0f0e00
theorem lowS_zo_251_4_75:Lower true dzo_251_4 roots_251 gzo_251_4 8:=lower_iso_b (d1:=dom_251) (r1:=roots_251) (T1:=gsh_251_4) [(dom_251,4)] (by decide +kernel) (lower_slice_b (T:=gsh_251_4) [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,0,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,0,32),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_75)
def dzo_183_64:=0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000
def gzo_183_64:=0xff00ff00ff00fe000000000000000000ff00fe00ff00ee0000000000000000
def gsh_183_64:=0xff00ff00ff00fe000000000000000000ff00fe00ff00ee
theorem lowS_zo_183_64_164:Lower true dzo_183_64 roots_183 gzo_183_64 7:=lower_iso_b (d1:=dom_183) (r1:=roots_183) (T1:=gsh_183_64) [(dom_183,64)] (by decide +kernel) (lower_slice_b (T:=gsh_183_64) [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa,0,1),(0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc,0,2),(0xff000000ff0000000000000000000000ff000000ff0000,0,16)] (by decide +kernel) lowS_164)
def dzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def gzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00fe00ff00ff00ff00ff00fe00fe00fe00ee00
def gsh_247_8:=0xff00ff00ff00ff00ff00ff00ff00fe00ff00ff00ff00ff00fe00fe00fe00ee
theorem lowS_zo_247_8_180:Lower true dzo_247_8 roots_247 gzo_247_8 8:=lower_iso_b (d1:=dom_247) (r1:=roots_247) (T1:=gsh_247_8) [(dom_247,8)] (by decide +kernel) (lower_slice_b (T:=gsh_247_8) [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,0,1),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,0,2),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000,0,64)] (by decide +kernel) lowS_180)
def dzo_191_64:=0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def gzo_191_64:=0xfffffffffffffffe0000000000000000fffffffeffffffee0000000000000000
def gsh_191_64:=0xfffffffffffffffe0000000000000000fffffffeffffffee
theorem lowS_zo_191_64_164:Lower true dzo_191_64 roots_191 gzo_191_64 8:=lower_iso_b (d1:=dom_191) (r1:=roots_191) (T1:=gsh_191_64) [(dom_191,64)] (by decide +kernel) (lower_slice_b (T:=gsh_191_64) [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc0000000000000000cccccccccccccccc,0,2),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,0,8),(0xffff0000ffff00000000000000000000ffff0000ffff0000,0,16)] (by decide +kernel) lowS_164)
def dzo_183_8:=0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00
def gzo_183_8:=0xff00ff00ff00fe000000000000000000fe00fe00fe00ee00
def gsh_183_8:=0xff00ff00ff00fe000000000000000000fe00fe00fe00ee
theorem lowS_zo_183_8_180:Lower true dzo_183_8 roots_183 gzo_183_8 7:=lower_iso_b (d1:=dom_183) (r1:=roots_183) (T1:=gsh_183_8) [(dom_183,8)] (by decide +kernel) (lower_slice_b (T:=gsh_183_8) [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa,0,1),(0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc,0,2)] (by decide +kernel) lowS_180)
def dzo_123_128:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
def gzo_123_128:=0xf0f0f0f0f0f0f0e0f0f0f0f0f0f0e0c00000000000000000000000000000000
def gsh_123_128:=0xf0f0f0f0f0f0f0e0f0f0f0f0f0f0e0c
theorem lowS_zo_123_128_73:Lower true dzo_123_128 roots_123 gzo_123_128 7:=lower_iso_b (d1:=dom_123) (r1:=roots_123) (T1:=gsh_123_128) [(dom_123,128)] (by decide +kernel) (lower_slice_b (T:=gsh_123_128) [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0,2),(0xf0f00000f0f00000f0f00000f0f0000,0,16),(0xf0f0f0f000000000f0f0f0f00000000,0,32)] (by decide +kernel) lowS_73)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,10),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,72),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,28),(24,88),(24,152),(32,33),(32,34),(32,36),(32,160),(40,41),(40,42),(40,44),(40,104),(40,168),(48,49),(48,50),(48,52),(48,112),(48,176),(56,57),(56,58),(56,60),(56,120),(56,184),(64,65),(64,66),(64,72),(64,80),(68,69),(68,70),(68,76),(68,84),(68,100),(68,196),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,130),(128,132),(128,144),(128,160),(129,131),(129,133),(129,137),(129,145),(129,161),(129,193),(136,137),(136,138),(136,140),(136,152),(136,168),(136,200),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|9=>7
|10=>20
|11=>14
|12=>4
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0xdb4d4992f472dd9654f55cdba385b528857
|10,0=>0xf96e5c0fc3a4b13a1d749d636992f4918358fd82880a97a3dc70aed6c45262cd9584e6570fe4d76422dfe0f0090e57209e77
|11,0=>0x9608e770cd64df2622405618951a4a4dfa64d82e4931541ef940c7c1a3220a6c2090fc
|12,0=>0x99b3f792e4389a10c075
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ffffffff00000000ffffffff0f0f0f0fffffffff0f000f00fffffffffffffffffffffffffffffffffffffffffffffffffff0fff0fff0fff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f00aaaaaaaaaaaaaaaaaaffaaffaaffaaffaaaaaaaaaaaaaaaaaafaaafaaafaaafa000000000000000000ff00ff00ff00ff000000000000000000f000f000f000f0fffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00fff0fff0fff0fff0ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|0,1=>0xffffffffffffffff0000000000000000f0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000ff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff00ff00ff00ff00fffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000f000f000f0fffffffffffffffffffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff00000000000000000ffffffffffffffff0000000000000000fff0fff0fff0fff0ffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000000f000f000f000f000f000f000f000f000f000f000f000f0000000000000000fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00fffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff00ff00ff00ff00ffffffffffffffffff00f000f000f000f0000000000000000000000000000000000f0f0f0f0f0f0f0f0f000f000f000f00
|0,2=>0xffffffffffffffffff00ff00ff00ff00fffffffffffffffffff0fff0fff0fff0fffffffffffffffffff0fff0fff0fff0ffffffffffffffffff00ff00ff00ff00f0f0f0f0f0f0f0f0f000f000f000f00000ff00ff00ff00ff00ff00ff00ff00ff00f000f000f000f000f000f000f000f0
|_,_=>0
def sP:Nat→Nat
|0=>0x5c81c52440c22c10081c51030815c02075494c30920081c910308b0402076040c20570081c91030920560081ce24a1030810081d55130c24881ce2440c204020714910309100f1c92840c204020724a0c23410081c91033010081c61440c2040
|1=>0x20725c1030920402072440c20560081c910308d0402072448430810081d55130c20402072440c24410081ce2440c20402071891030810081c97040c26c10081dd2440c20402075094c40c24881c92840c26c10081d92440c20402075040c2481
|2=>0x1030810081e32440c20402072440c248178020725c2840c20402072440c205e0081da24a1030810081d82440c20402072531030920081d52440c24810081e22440c20402075541030810081d42531030810081c91030a00402071492840c2040
|3=>0x81c91030810081c52440c20402072440c24810081d52440c2040207509
|_=>0
def sO:Nat→Nat→Nat
|9,0=>0xd605922390d48464130009
|10,0=>0x76cb925b72d2964cb0256f2ada524a6e52348893fc9d68d926392d494648f43da
|11,0=>0x2e5368aaf555669754299cccbea4d31d989d42a6014f6a
|12,0=>0xcb4e3670937b9
|13,0=>0x19f8
|_,_=>0
def wAt:=mkWire dB 36 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x25e444a0404901101400525c8a051005a072894401240494a001452a1004905609c5012414911101400514a8401241494925280055528911040452910049050404911101490114b452a10049052c1452a10049052104a162414401384c529100490508b452a100490524b452a1004905
|1=>0x24141012444901140c9051128101281440111281012894401140490510140052444101144490524449011014901289c4011004905112410125e844a0405813140490514a0401241491110149018014a27100581114049057c94a071005c272814401
|_=>0
def oO:Nat→Nat→Nat
|9,0=>0x610a210418821022004
|10,0=>0xaa748e79cc392718e19c037a6e8db9b43626b8d59a834a688cf99c3
|11,0=>0x391702dc5b0b51682cc590b11602bc570ad1582
|12,0=>0xee3d87a8f41
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x1041ff8641dfc30467e0c033f05c59f8242cfc12067e08033f032b9f8109cfc08467e04033f01ed9f8091cfc02067e00833f0027bf8010dfc00667e00233f0007ff8003dfc001e7e000b7f00059f8001ffc0006fe00033f00019b8000ccc000626000000
|1=>0x86019fa10adfc85067e40833f
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>0xb302343101
|10,0=>0x41110a51151640f54c4dc64651b7dd
|11,0=>0x6215a089a48e7882548d7
|12,0=>0x604147
|13,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_253 12 roots_253 ops++addP pm 2 dom_251 11 roots_251 ops++addP pm 3 dom_127 11 roots_127 ops++addP pm 4 dom_247 11 roots_247 ops++addP pm 5 dom_191 11 roots_191 ops++addP pm 6 dom_243 9 roots_243 ops++addP pm 7 dzo_123_4 7 roots_123 ops++addP pm 8 dom_239 12 roots_239 ops++addP pm 9 dom_223 12 roots_223 ops++addP pm 10 dom_187 9 roots_187 ops++addP pm 11 dom_119 9 roots_119 ops++addP pm 12 dzo_127_128 8 roots_127 ops++addP pm 13 dzo_251_4 8 roots_251 ops++addP pm 14 dzo_183_64 7 roots_183 ops++addP pm 15 dom_63 7 roots_63 ops++addP pm 16 dzo_247_8 8 roots_247 ops++addP pm 17 dzo_191_64 8 roots_191 ops++addP pm 18 dom_123 8 roots_123 ops++addP pm 19 dom_183 8 roots_183 ops++addP pm 20 dom_179 6 roots_179 ops++addP pm 21 dzo_183_8 7 roots_183 ops++addP pm 22 dzo_123_128 7 roots_123 ops++addP pm 23 dom_115 6 roots_115 ops++addP pm 24 dom_51 4 roots_51 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_123_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_127_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_251_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_183_64_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_247_8_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_191_64_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_183_8_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_123_128_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_51 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 7 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 20 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 20 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 14 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 4 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 4 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 7] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [4, 9] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.or, inputs := [7, 5] }, { op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [9, 6] }, { op := GateOp.or, inputs := [2, 8] }, { op := GateOp.and, inputs := [13, 12] }, { op := GateOp.and, inputs := [6, 10] }, { op := GateOp.and, inputs := [11, 15] }, { op := GateOp.and, inputs := [14, 3] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52250_aux

theorem PEqualNP.Outside.L_meta_52250 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52250_aux.main
