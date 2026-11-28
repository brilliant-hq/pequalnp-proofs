import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52232_aux
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
def goal_27 : Nat := 0xeeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xffccffccaa00aa00ffccffccaa00aa00ffccffccaa00aa00ffccffccaa00aa00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfff0fff0aa00aa00fff0fff0aa00aa00fff0fff0aa00aa00fff0fff0aa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfffcfffcaa00aa00fffcfffcaa00aa00fffcfffcaa00aa00fffcfffcaa00aa00
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeecccceeee0000eeeecccceeee0000eeeecccceeee0000eeeecccceeee0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfcfcfccccc0000fcfcfcfccccc0000fcfcfcfccccc0000fcfcfcfccccc0000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefcfceeee0000fefefcfceeee0000fefefcfceeee0000fefefcfceeee0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaff00aaaaaa00ffaaff00aaaaaa00ffaaff00aaaaaa00ffaaff00aaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccffcccccc0000ffccffcccccc0000ffccffcccccc0000ffccffcccccc0000
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffcceeeeaa00ffeeffcceeeeaa00ffeeffcceeeeaa00ffeeffcceeeeaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafff0aaaaaa00fffafff0aaaaaa00fffafff0aaaaaa00fffafff0aaaaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcfffccccc0000fffcfffccccc0000fffcfffccccc0000fffcfffccccc0000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefffceeeeaa00fffefffceeeeaa00fffefffceeeeaa00fffefffceeeeaa00
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

def dom_81 : Nat := 0x300030000000000030003
def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_82 : Nat := 0x500050000000000050005
def goal_82 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_82 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffeeeeffffeeeeeeee0000eeee0000ffffeeeeffffeeeeeeee0000eeee0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffffafafffffafaaaaa0000aaaa0000fffffafafffffafaaaaa0000aaaa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffffcfcfffffcfccccc0000cccc0000fffffcfcfffffcfccccc0000cccc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffefefffffefeeeee0000eeee0000fffffefefffffefeeeee0000eeee0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffaaaaffffaaaaaaaaaa00aaaaaa00ffffaaaaffffaaaaaaaaaa00aaaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffeeeeffffeeeeeeeeaa00eeeeaa00ffffeeeeffffeeeeeeeeaa00eeeeaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffafafffffafaaaaaaa00aaaaaa00fffffafafffffafaaaaaaa00aaaaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffefefffffefeeeeeaa00eeeeaa00fffffefefffffefeeeeeaa00eeeeaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xeeeeeeeeeeeeeeeecccccccc00000000eeeeeeeeeeeeeeeecccccccc00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfafafafafafafafaf0f0f0f000000000fafafafafafafafaf0f0f0f000000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefefefefefefcfcfcfc00000000fefefefefefefefefcfcfcfc00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffaaffaaaaaaaaaaff00ff00aa00aa00ffaaffaaaaaaaaaaff00ff00aa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccccccccccffccffcc00000000ffccffccccccccccffccffcc00000000
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeeeeeeeeeffccffccaa00aa00ffeeffeeeeeeeeeeffccffccaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfff0fff0f0f0f0f0fff0fff000000000fff0fff0f0f0f0f0fff0fff000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffafafafafafff0fff0aa00aa00fffafffafafafafafff0fff0aa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfcfcfcfcfffcfffc00000000fffcfffcfcfcfcfcfffcfffc00000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefefefefefffcfffcaa00aa00fffefffefefefefefffcfffcaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffccccffffcccccccccccccccc0000ffffccccffffcccccccccccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffeeeeeeeecccceeee0000ffffeeeeffffeeeeeeeecccceeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffff0f0fffff0f0f0f0f0f000000000fffff0f0fffff0f0f0f0f0f000000000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafafffffafafafaf0f0aaaa0000fffffafafffffafafafaf0f0aaaa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcfffffcfcfcfcfcfccccc0000fffffcfcfffffcfcfcfcfcfccccc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefefffffefefefefcfceeee0000fffffefefffffefefefefcfceeee0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffaaaaffaaff00aaaaaa00ffffffaaffffaaaaffaaff00aaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffccccffccffcccccc0000ffffffccffffccccffccffcccccc0000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffeeeeffeeffcceeeeaa00ffffffeeffffeeeeffeeffcceeeeaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0fffff0f0fff0fff000000000fffffff0fffff0f0fff0fff000000000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffafafffafff0aaaaaa00fffffffafffffafafffafff0aaaaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcfffffcfcfffcfffccccc0000fffffffcfffffcfcfffcfffccccc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffefefffefffceeeeaa00fffffffefffffefefffefffceeeeaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_145 : Nat := 0x3000300000000000000000000000000030003
def goal_145 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_145 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaeeee0000eeee0000eeee0000eeee0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffff00ffffff00ffffff00ffffff00cccc0000cccc0000cccc0000cccc0000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffaaffffffaaffffffaaffffffaaeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffff0fffffff0fffffff0fffffff0cccc0000cccc0000cccc0000cccc0000
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffafffffffafffffffafffffffaeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfafafafafafafafafafafafafafafafaf0f0f0f000000000f0f0f0f000000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0fcfcfcfc00000000fcfcfcfc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfefefefefafafafafefefefefafafafafcfcfcfc00000000fcfcfcfc00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaff00ff00aa00aa00ff00ff00aa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffccffccff00ff00ffccffccff00ff00ffccffcc00000000ffccffcc00000000
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffeeffeeffaaffaaffeeffeeffaaffaaffccffccaa00aa00ffccffccaa00aa00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffafffafffafffafffafffafffafffafff0fff0aa00aa00fff0fff0aa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffcfffcfff0fff0fffcfffcfff0fff0fffcfffc00000000fffcfffc00000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffefffefffafffafffefffefffafffafffcfffcaa00aa00fffcfffcaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffccccffff0000ffffccccffff0000cccccccccccc0000cccccccccccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffeeeeffffaaaaffffeeeeffffaaaaeeeecccceeee0000eeeecccceeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffcfcfffff0f0fffffcfcfffff0f0fcfcfcfccccc0000fcfcfcfccccc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffefefffffafafffffefefffffafafefefcfceeee0000fefefcfceeee0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffccffffff00ffffffccffffff00ffccffcccccc0000ffccffcccccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffeeffffffaaffffffeeffffffaaffeeffcceeeeaa00ffeeffcceeeeaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffcfffffff0fffffffcfffffff0fffcfffccccc0000fffcfffccccc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffefffffffafffffffefffffffafffefffceeeeaa00fffefffceeeeaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_193 : Nat := 0x3000000000000000300000000000000030000000000000003
def goal_193 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000
def roots_193 : List Nat := [xs256.getD 0 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_196 : Nat := 0x11000000000000001100000000000000110000000000000011
def goal_196 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000
def roots_196 : List Nat := [xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfffffffffffffffffafafafafafafafafafafafafafafafa0000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfffffffffffffffffafafafafafafafafefefefefefefefe0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaaaaaaaaaaaaaaaaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffff00ff00ff00ff00cccccccccccccccc0000000000000000
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffaaffaaffaaffaaeeeeeeeeeeeeeeeeaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfffffffffffffffffff0fff0fff0fff0f0f0f0f0f0f0f0f00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffffafffafffafffafafafafafafafafaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fcfcfcfcfcfcfcfc0000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffafffafffafffafefefefefefefefeaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_208 : Nat := 0x10001000000000001000100000000000100010000000000010001
def goal_208 : Nat := 0xffffffffffffffffffff0000ffff0000ffff0000ffff00000000000000000000
def roots_208 : List Nat := [xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffffff0000ffff0000ffffccccffffcccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffeeeeffffeeeeeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffffafafffffafafffffafafffffafaaaaa0000aaaa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffafafffffafafffffefefffffefeeeee0000eeee0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffffffffffffffffffff00ffffff00ffff0000ffff00000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffffaaffffffaaffffaaaaffffaaaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffff00ffffff00ffffccccffffcccccccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffaaffffffaaffffeeeeffffeeeeeeeeaa00eeeeaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffffafffffffafffffafafffffafaaaaaaa00aaaaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffff0fffffff0fffffcfcfffffcfccccc0000cccc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffafffffffafffffefefffffefeeeeeaa00eeeeaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffffffffffcccccccc00000000cccccccccccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffeeeeeeeeaaaaaaaaeeeeeeeeeeeeeeeecccccccc00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffafafafafafafafafafafafafafafafaf0f0f0f000000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffcfcfcfcf0f0f0f0fcfcfcfcfcfcfcfcfcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffefefefefafafafafefefefefefefefefcfcfcfc00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff0000000000ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaaaaaaaaaff00ff00aa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffccffccff00ff00ffccffccccccccccffccffcc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffeeffeeffaaffaaffeeffeeeeeeeeeeffccffccaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0f0f0f0f0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffafffafffafffafffafffafafafafafff0fff0aa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffcfffcfff0fff0fffcfffcfcfcfcfcfffcfffc00000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffefffefffafffafffefffefefefefefffcfffcaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffccccffff0000ffffccccffffcccccccccccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffeeeeffffaaaaffffeeeeffffeeeeeeeecccceeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffafafffffafafffffafafffffafafafaf0f0aaaa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffcfcfffff0f0fffffcfcfffffcfcfcfcfcfccccc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffefefffffafafffffefefffffefefefefcfceeee0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffaaaaffaaff00aaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffccffffff00ffffffccffffccccffccffcccccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffeeffffffaaffffffeeffffeeeeffeeffcceeeeaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffafffffffafffffffafffffafafffafff0aaaaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffcfffffff0fffffffcfffffcfcfffcfffccccc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffefffffffafffffffefffffefefffefffceeeeaa00
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_81
def pG:List (Nat×Nat):=[(1,17),(1,65),(16,17),(16,80),(64,65),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3f
def xsM:=roots_81.map (·&&&dom_81)
def gM:=goal_81&&&dom_81
def NN:Nat→Nat
|2=>1
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|2,0=>0xea9d9
|3,0=>0xea9d9
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x30000000000000003000080008000000000008000b00030000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x924
|_=>0
def sO:Nat→Nat→Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wAt:=mkWire dB 3 82 0x3ffffffffffffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_81 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_81 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_81==dom_81)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_81 gM v ys):RunD true dom_81 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_81 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_81 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_81 gM s xsM):False:=by
  have hmin:2≤s:=by have hl:=run_len h;change 3≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_81 roots_81 goal_81 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_81
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=S_81.noCircuit
def isoMvS_82:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_82:Lower true dom_82 roots_82 goal_82 4:=lower_iso_b isoMvS_82 (by decide +kernel) lowS_81
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_81
def isoMvS_145:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_145:Lower true dom_145 roots_145 goal_145 4:=lower_iso_b isoMvS_145 (by decide +kernel) lowS_81
def isoMvS_193:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_193:Lower true dom_193 roots_193 goal_193 4:=lower_iso_b isoMvS_193 (by decide +kernel) lowS_81
def isoMvS_196:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_196:Lower true dom_196 roots_196 goal_196 4:=lower_iso_b isoMvS_196 (by decide +kernel) lowS_81
def isoMvS_208:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_208:Lower true dom_208 roots_208 goal_208 4:=lower_iso_b isoMvS_208 (by decide +kernel) lowS_81
namespace S_27
def pG:List (Nat×Nat):=[(1,9),(1,17),(2,18),(3,11),(3,19),(8,9),(10,11),(10,26),(16,17),(16,18),(24,25),(24,26)]
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
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
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
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_slice_b [(0xa000a00000000000a000a,16,17)] (by decide +kernel) lowS_82
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_slice_b [(0x3000300000000000300030,64,68)] (by decide +kernel) lowS_81
namespace S_209
def pG:List (Nat×Nat):=[(1,17),(1,65),(1,129),(16,17),(16,80),(16,144),(64,65),(64,80),(64,192),(128,129),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_209.map (·&&&dom_209)
def gM:=goal_209&&&dom_209
def NN:Nat→Nat
|3=>3
|4=>6
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x76c5d74ede03f89
|4,0=>0x594054087f3b7e0397dc38d5d27c4e
|5,0=>0x8b70744f2b21bc4
|6,0=>0x8b707
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc000c00000000000c000000000000000c000c00000000000c00030003000000000003000300000000000300000000000000030000400040000000000040004000000000004000400000000000000000000000000000000000000000000000300030000000000030000c000c00000000000c000c00000000000c000c00000000000800090001000000000001000100000000000100010000000000010000c000c000000000000000000000000000c000800000000000000020002000000000002000200000000000200020000000000020002c000c000000000000000000000000000c000c00000000000000030003000000000003000300000000000000000000000000000000c000000000000000c000000000000000c000000000000000c00030003000000000002000200000000000300030000000000020002c000c00000000000c000c0000000000080008000000000008000b0003000000000003000300000000000300030000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x36543654c3654d3654c3165c3605365b4a36543260439654385436743210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x8411004
|4,0=>0x956056d565454c5
|5,0=>0x344bd6a5
|6,0=>0x384
|_,_=>0
def wAt:=mkWire dB 14 210 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3454d464d1435515455946551
|_=>0
def oO:Nat→Nat→Nat
|3,0=>2
|4,0=>0x624200002200
|5,0=>0x9181
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xf976530
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>1
|4,0=>0x13028
|5,0=>0x136
|6,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_208 4 roots_208 ops++addP pm 1 dom_145 4 roots_145 ops++addP pm 2 dom_193 4 roots_193 ops++addP pm 3 dom_81 4 roots_81 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_209 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_145 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_81 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_208 4 s (0,roots_208.map (·&&&dom_208)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_209 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_208 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_209==dom_209)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_209 gM v ys):RunD true dom_209 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_209 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_209 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_209 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_209 roots_209 goal_209 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_209
theorem lowS_209:Lower true dom_209 roots_209 goal_209 7:=S_209.noCircuit
def isoMvS_43:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_43:Lower true dom_43 roots_43 goal_43 4:=lower_iso_b isoMvS_43 (by decide +kernel) lowS_27
def isoMvS_45:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_45:Lower true dom_45 roots_45 goal_45 4:=lower_iso_b isoMvS_45 (by decide +kernel) lowS_27
def isoMvS_51:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=lower_iso_b isoMvS_51 (by decide +kernel) lowS_27
def isoMvS_54:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 4:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_27
def isoMvS_57:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 4:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_27
def isoMvS_58:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 4:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_27
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 4:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_27
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 4:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_27
def isoMvS_86:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_85
def isoMvS_89:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_85
def isoMvS_99:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 4:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_27
def isoMvS_101:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 4:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_27
def isoMvS_105:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 4:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_27
def isoMvS_106:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 4:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_27
def isoMvS_108:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 4:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_27
def isoMvS_114:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_85
def isoMvS_116:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 4:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_27
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_85
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_85
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 4:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_27
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 4:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_27
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 4:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_27
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 5:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_85
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 4:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_27
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 4:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_27
def isoMvS_195:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_85
def isoMvS_197:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 5:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_83
def isoMvS_198:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_85
def isoMvS_201:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_83
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 4:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_27
def isoMvS_204:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 5:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_85
def isoMvS_216:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 5:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_85
def isoMvS_226:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 4:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_27
def isoMvS_228:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 5:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_85
def isoMvS_232:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 4:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_27
theorem lowS_47:Lower true dom_47 roots_47 goal_47 5:=lower_slice_b [(0xcccc0000cccc,32,34)] (by decide +kernel) lowS_45
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_slice_b [(0xaa00aa00aa00aa,16,17)] (by decide +kernel) lowS_54
namespace S_59
def pG:List (Nat×Nat):=[(1,9),(1,17),(2,18),(2,34),(3,11),(3,19),(3,35),(8,9),(8,40),(10,11),(10,26),(10,42),(16,17),(16,18),(24,25),(24,26),(24,56),(32,34),(32,40),(33,35),(33,41),(33,49),(48,49),(48,50),(48,56)]
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
|4,0=>0x1150d06449
|5,0=>0x9abd70e01a0a6f0
|6,0=>0x9abd7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0c0f0c0f0c0f0cf0f0f0f0f000f00f0f00000f0f0000f0c0f0c00000000f0f0f0f00000000f000f000f000f00c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0000e0e00000e0e
|_,_=>0
def sP:Nat→Nat
|0=>0x46321463214683217463216532143210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x165418a6
|6,0=>0x1b5
|_,_=>0
def wAt:=mkWire dB 9 60 0xfffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0xf9040
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>6
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_58 4 roots_58 ops++addP pm 1 dom_57 4 roots_57 ops++addP pm 2 dom_51 4 roots_51 ops++addP pm 3 dom_43 4 roots_43 ops++addP pm 4 dom_27 4 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_58 4 s (0,roots_58.map (·&&&dom_58)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_59 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_58 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
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
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_slice_b [(0xaa00aa0000000000aa00aa,16,17)] (by decide +kernel) lowS_86
def dzo_83_8:=0xf000f00000000000f000f00
def gzo_83_8:=0xf000e00000000000e000a00
def gsh_83_8:=0xf000e00000000000e000a
theorem lowS_zo_83_8_82:Lower true dzo_83_8 roots_83 gzo_83_8 5:=lower_iso_b (d1:=dom_83) (r1:=roots_83) (T1:=gsh_83_8) [(dom_83,8)] (by decide +kernel) (lower_slice_b (T:=gsh_83_8) [(0xa000a00000000000a000a,0,1)] (by decide +kernel) lowS_82)
namespace S_91
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,18),(2,66),(3,11),(3,19),(3,67),(8,9),(10,11),(10,26),(10,74),(16,17),(16,18),(16,80),(24,25),(24,26),(24,88),(64,65),(64,66),(64,80),(72,73),(72,74),(72,88)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_91.map (·&&&dom_91)
def gM:=goal_91&&&dom_91
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x3a2c0
|5,0=>0xfa69c
|6,0=>0x9f8ac
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f0f0000c0c0c0c000000000c0c0c0cf0f0000000000000f0f0000f000f00000000000f000f00a0a0a0a000000000a0a0a0a30303030000000003030000f0f0f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8ea1a3a84688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 92 0xfffffffffffffffffffffff
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
addP pm 0 dom_89 5 roots_89 ops++addP pm 1 dom_75 4 roots_75 ops++addP pm 2 dzo_83_8 5 roots_83 ops++addP pm 3 dom_83 5 roots_83 ops++addP pm 4 dom_82 4 roots_82 ops++addP pm 5 dom_27 4 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_91 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_83_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_89 5 s (0,roots_89.map (·&&&dom_89)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_91 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_89 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_91==dom_91)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_91 gM v ys):RunD true dom_91 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_91 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
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
theorem lowS_93:Lower true dom_93 roots_93 goal_93 6:=lower_slice_b [(0x303030300000000030303030,64,68)] (by decide +kernel) lowS_89
theorem lowS_103:Lower true dom_103 roots_103 goal_103 5:=lower_slice_b [(0xcc000000cc000000cc000000cc,32,34)] (by decide +kernel) lowS_101
def dzo_85_32:=0x330033000000000033003300000000
def gzo_85_32:=0x330032000000000032003000000000
def gsh_85_32:=0x3300320000000000320030
theorem lowS_zo_85_32_81:Lower true dzo_85_32 roots_85 gzo_85_32 5:=lower_iso_b (d1:=dom_85) (r1:=roots_85) (T1:=gsh_85_32) [(dom_85,32)] (by decide +kernel) (lower_slice_b (T:=gsh_85_32) [(0x3000300000000000300030,0,4)] (by decide +kernel) lowS_81)
namespace S_117
def pG:List (Nat×Nat):=[(1,17),(1,65),(4,36),(4,68),(5,21),(5,37),(5,69),(16,17),(16,80),(20,21),(20,52),(20,84),(32,36),(33,37),(33,49),(33,97),(48,49),(48,52),(48,112),(64,65),(64,68),(64,80),(96,97),(96,100),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_117.map (·&&&dom_117)
def gM:=goal_117&&&dom_117
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x8cddf44972
|5,0=>0xd5744a34c432d76
|6,0=>0x96c74
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc008800cc008800cc008800cc008b30033003300330022002200220022cc000000cc000000cc000000cc000000033000000330000000000000000cc000000cc0000008800000088000330033000000000033003300000000c000c000c000c000c000c000c000c2200220022002200220022002200220000cc000000cc000000880000008b30033003300330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x473204973204738204732064325043210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 118 0x3fffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1c2
|_=>0
def oO:Nat→Nat→Nat
|5,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0xfb440
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x16
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_85 5 roots_85 ops++addP pm 1 dom_116 4 roots_116 ops++addP pm 2 dzo_85_32 5 roots_85 ops++addP pm 3 dom_101 4 roots_101 ops++addP pm 4 dom_81 4 roots_81 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_117 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_85_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_81 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_85 5 s (0,roots_85.map (·&&&dom_85)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_117 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_85 h
def symsG:List (List (Nat×Nat)):=[[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_117==dom_117)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_117 gM v ys):RunD true dom_117 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_117 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
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
theorem lowS_118:Lower true dom_118 roots_118 goal_118 6:=lower_slice_b [(0x500050005000500050005000500050,32,36)] (by decide +kernel) lowS_114
namespace S_205
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(4,68),(4,132),(5,13),(5,69),(5,133),(8,9),(8,136),(12,13),(12,76),(12,140),(64,65),(64,68),(64,192),(72,73),(72,76),(72,200),(128,129),(128,132),(128,136),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_205.map (·&&&dom_205)
def gM:=goal_205&&&dom_205
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x70a42
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3300000000000000330000000000000033000000000000003300c0c0000000000000c0c0000000000000c0c0000000000000c0c2222000000000000222200000000000022220000000000002222cccc0000000000000000000000000000cccc0000000000000003333000000000000333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 206 0x3fffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_204 5 roots_204 ops++addP pm 1 dom_141 5 roots_141 ops++addP pm 2 dom_201 5 roots_201 ops++addP pm 3 dom_197 5 roots_197 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_205 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_197 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_204 5 s (0,roots_204.map (·&&&dom_204)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_205 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_204 h
def symsG:List (List (Nat×Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_205==dom_205)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_205 gM v ys):RunD true dom_205 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_205 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_205 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_211:Lower true dom_211 roots_211 goal_211 8:=lower_slice_b [(0xc000c00000000000c000c00000000000c000c00000000000c000c,16,18)] (by decide +kernel) lowS_209
def isoMvS_61:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 5:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_55
def isoMvS_62:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 5:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_47
def isoMvS_79:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_79:Lower true dom_79 roots_79 goal_79 5:=lower_iso_b isoMvS_79 (by decide +kernel) lowS_47
def isoMvS_107:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 7:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_59
def isoMvS_109:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 7:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_59
def isoMvS_110:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 5:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_103
def isoMvS_115:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_91
def isoMvS_121:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 7:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_117
def isoMvS_122:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_117
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 5:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_55
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 7:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_91
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 5:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_47
def isoMvS_167:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 5:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_55
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 7:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_117
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 6:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_118
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 5:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_103
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_117
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 7:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_59
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_59
def isoMvS_199:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 6:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_87
def isoMvS_203:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 7:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_91
def isoMvS_206:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 6:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_93
def isoMvS_213:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_211
def isoMvS_217:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 8:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_211
def isoMvS_218:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 7:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_91
def isoMvS_227:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 7:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_117
def isoMvS_229:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 7:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_91
def isoMvS_230:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 6:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_118
def isoMvS_233:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 7:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_91
def isoMvS_234:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 7:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_59
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 6:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_118
def isoMvS_242:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 7:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_91
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xf0f0f0f0f0f0f0f0,32,36)] (by decide +kernel) lowS_59
theorem lowS_95:Lower true dom_95 roots_95 goal_95 8:=lower_slice_b [(0xf0f0f0f000000000f0f0f0f0,64,68)] (by decide +kernel) lowS_91
theorem lowS_111:Lower true dom_111 roots_111 goal_111 8:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc,32,34)] (by decide +kernel) lowS_109
def dzo_87_32:=0xff00ff0000000000ff00ff00000000
def gzo_87_32:=0xff00fe0000000000fe00fc00000000
def gsh_87_32:=0xff00fe0000000000fe00fc
theorem lowS_zo_87_32_81:Lower true dzo_87_32 roots_87 gzo_87_32 6:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_32) [(dom_87,32)] (by decide +kernel) (lower_slice_b (T:=gsh_87_32) [(0xcc00cc0000000000cc00cc,0,2),(0xf000f00000000000f000f0,0,4)] (by decide +kernel) lowS_81)
namespace S_119
def pG:List (Nat×Nat):=[(1,17),(1,65),(2,18),(2,34),(2,66),(3,19),(3,35),(3,67),(4,36),(4,68),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,23),(7,39),(7,71),(16,17),(16,18),(16,80),(20,21),(20,22),(20,52),(20,84),(32,34),(32,36),(33,35),(33,37),(33,49),(33,97),(48,49),(48,50),(48,52),(48,112),(64,65),(64,66),(64,68),(64,80),(96,97),(96,98),(96,100),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_119.map (·&&&dom_119)
def gM:=goal_119&&&dom_119
def NN:Nat→Nat
|4=>5
|5=>15
|6=>37
|7=>10
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xef6d6ef4fc6ee3a6d9af54b88
|5,0=>0xef258e64eee3d8de3448d8193cb74ac9270a0069716ab614075ab19595395885540a78001ac
|6,0=>0xfeae0fd584f89ecf4031f2a2de972be6de2e6930dae64bce6cb4720b23e2b0eb3a4524a120d9cf2d9ccfd9b1e396e998bd487ed9a749c973eed716ab633535d38a5c1104f8474a36c47d7945218450703eb1e219941f8b31f0b107592
|7,0=>0xf2fd6f06f3e8d9fc2892bad6da4ab86aedf5d38a4f76c093c2
|8,0=>0xdaa04
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x550055005500550000000000000000ff00ff00ff00ff00ff00ff000000000000000000000000ff00aa00ff00aaaa00aa00aa00aa00aa00aa00aa00aaff000000ff000000ff000000ff0000fe00fe00fe00fe00fe00fc00fe00fcee00ee00ee00ee00ee00cc00ee00ccff00ff00ff00ff0000000000000000ff00cc00ff00cc00cc00cc00cc00cc5500550055005500550000005500000000ff000000ff00ff000000ff0000ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff000000ff0000f000f000f000f000f000f000f000f0cc00cc00cc00cc00cc00cc00cc00cc000055000000550055000000550000
|0,1=>0xff00ff0055005500ff00ff00000000aa000000aa000000ff000000ff0000ff00ff00ff00ff00ff00aa00ff00aaaa00aa00aa00aa00ff00aa00ff00aa0000ff000000ff0000000000000000ff00ff00ff000000ff00ff000000000000000000000000ff000000ff0000ff005500ff005500ff000000ff0000ff00aa00ff00aa00aa00aa00aa00aaff00aa00ff00aa00ff00aa00ff00aaff00ff00ff00ff00aa00aa00aa00aaff00ff00ff00ff0055000000550000aa00aa00aa00aa00aa000000aa00000000000000000000ff00ff00000000ff000000ff00000000000000000000550000005500000055000000550000
|0,2=>0xff00f000ff00f000f000f000f000f00000ff0000000000ff00ff000000000000aa000000aa00aa00aa00aa00aaff00ff000000ff00ff00ff00000000ff00000000000000ff00ff00000000000000000000000055000000550000
|_,_=>0
def sP:Nat→Nat
|0=>0x5320e58b08130810b0813142046020502040c20464440cb0892040c20571050813045830815442c20543ce2c20462042c20462042c224810314204c48b0811881030873040c20503ce34b0813042ca2481030871841420461050810040c2040
|1=>0x814c87cb08130810b78204c20474b0813083832c204c2040c204c40811c2c204c2042c21cc2042c204620464204c6c40cb08130810b0814083c40c204c4445990813081032c20553120cb08130810b08130621a2c204c20e2d90813081032c2
|2=>0x10b0813084440cb08130810b0813083ce2c204c2042c20572042e504c2242c204c2040cb0811881032c204c3ce2c204c4081162c20552042c20632122d908130888b0813081160c204c2212c204c20434b08130810b08132020460b08130810b
|3=>0x42c204c2042d90813081162c204c2042c204c21b48b08130810b0813102042c2055308
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a58c6c5d62c294d49ac47620b0ed86ca30615309543ec196
|6,0=>0x15f6acb54da98f4579f3cdde62d2a7923475e2ed10784bc09df8cf6677bba1dc2eda769bb3598ecc165d3acdd5aca674fba61d22e8b64239f5cece6f7
|7,0=>0x344f9b7ca3e39b0ef807bcbdc9ed6f656
|8,0=>0x1a96
|_,_=>0
def wAt:=mkWire dB 38 120 0xffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xb232cc4b22108cb333084b202c84c221084c452c802452c804472c80b212c84421311cb2011b4b222c8446f2c883302c8443d3088b3f2c841452c803332c84b222c8cb202c84b232c84b211114b201084c452c80b210d1cb202c84b2105343302c841452c80b21
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x28c7318400000000cc000000300000
|6,0=>0x2f2b4ab2a8691a04009880090a3184800000007c9d270400001b1001925c952000004c92144501000e20000034400
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xfb7e9ef7b9eb64a9062084610812007f5a9625811804d1103d090200700e0140400400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x218ce0000a201000
|6,0=>0x15ab0d430a7069d800010ea022b05835481463c80c808e0
|7,0=>0x34fde1f9deb17
|8,0=>0xe
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_117 7 roots_117 ops++addP pm 1 dom_101 4 roots_101 ops++addP pm 2 dom_54 4 roots_54 ops++addP pm 3 dom_115 7 roots_115 ops++addP pm 4 dom_86 5 roots_86 ops++addP pm 5 dom_118 6 roots_118 ops++addP pm 6 dom_103 5 roots_103 ops++addP pm 7 dzo_87_32 6 roots_87 ops++addP pm 8 dom_87 6 roots_87 ops++addP pm 9 dom_55 5 roots_55 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_119 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_87_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_55 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_117 7 s (0,roots_117.map (·&&&dom_117)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_119 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_117 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_119 gM v ys):RunD true dom_119 gM v (ori ys):=h
def Z (s:Nat):=barP dom_119 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 37 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 37 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 10 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 0 = true)
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
def dzo_91_32:=0xf0f0f0f000000000f0f0f0f00000000
def gzo_91_32:=0xf0f0f0e000000000f0e0f0c00000000
def gsh_91_32:=0xf0f0f0e000000000f0e0f0c
theorem lowS_zo_91_32_81:Lower true dzo_91_32 roots_91 gzo_91_32 6:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_32) [(dom_91,32)] (by decide +kernel) (lower_slice_b (T:=gsh_91_32) [(0xc0c0c0c000000000c0c0c0c,0,2),(0xf000f00000000000f000f00,0,8)] (by decide +kernel) lowS_81)
def dzo_82_8:=0x50005000000000005000500
def gzo_82_8:=0x50004000000000004000000
def gsh_82_8:=0x500040000000000040000
theorem lowS_zo_82_8_82:Lower true dzo_82_8 roots_82 gzo_82_8 4:=lower_iso_b (d1:=dom_82) (r1:=roots_82) (T1:=gsh_82_8) [(dom_82,8)] (by decide +kernel) (lower_slice_b (T:=gsh_82_8) [] (by decide +kernel) lowS_82)
def dzo_81_32:=0x30003000000000003000300000000
def gzo_81_32:=0x30002000000000002000000000000
def gsh_81_32:=0x300020000000000020000
theorem lowS_zo_81_32_81:Lower true dzo_81_32 roots_81 gzo_81_32 4:=lower_iso_b (d1:=dom_81) (r1:=roots_81) (T1:=gsh_81_32) [(dom_81,32)] (by decide +kernel) (lower_slice_b (T:=gsh_81_32) [] (by decide +kernel) lowS_81)
def dzo_115_8:=0xf000f000f000f000f000f000f000f00
def gzo_115_8:=0xf000f000f000e000f000f000e000a00
def gsh_115_8:=0xf000f000f000e000f000f000e000a
theorem lowS_zo_115_8_82:Lower true dzo_115_8 roots_115 gzo_115_8 6:=lower_iso_b (d1:=dom_115) (r1:=roots_115) (T1:=gsh_115_8) [(dom_115,8)] (by decide +kernel) (lower_slice_b (T:=gsh_115_8) [(0xa000a000a000a000a000a000a000a,0,1),(0xf000f00000000000f000f00000000,0,32)] (by decide +kernel) lowS_82)
def dzo_89_32:=0x3030303000000000303030300000000
def gzo_89_32:=0x3030302000000000302030000000000
def gsh_89_32:=0x30303020000000003020300
theorem lowS_zo_89_32_81:Lower true dzo_89_32 roots_89 gzo_89_32 5:=lower_iso_b (d1:=dom_89) (r1:=roots_89) (T1:=gsh_89_32) [(dom_89,32)] (by decide +kernel) (lower_slice_b (T:=gsh_89_32) [(0x30003000000000003000300,0,8)] (by decide +kernel) lowS_81)
def dzo_114_8:=0x5000500050005000500050005000500
def gzo_114_8:=0x5000500050004000500050004000000
def gsh_114_8:=0x50005000500040005000500040000
theorem lowS_zo_114_8_82:Lower true dzo_114_8 roots_114 gzo_114_8 5:=lower_iso_b (d1:=dom_114) (r1:=roots_114) (T1:=gsh_114_8) [(dom_114,8)] (by decide +kernel) (lower_slice_b (T:=gsh_114_8) [(0x50005000000000005000500000000,0,32)] (by decide +kernel) lowS_82)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,40),(10,11),(10,26),(10,42),(10,74),(16,17),(16,18),(16,80),(24,25),(24,26),(24,56),(24,88),(32,34),(32,40),(33,35),(33,41),(33,49),(33,97),(48,49),(48,50),(48,56),(48,112),(64,65),(64,66),(64,80),(72,73),(72,74),(72,88),(72,104),(96,97),(96,98),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|4=>2
|5=>15
|6=>56
|7=>31
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x9cb8866329
|5,0=>0xa9061a2c88989dd8f3e08a92f862cb664e356555552b8440a738c082bfca27610205d009cab
|6,0=>0xdf766ce6feccfb0cb3b0a0f6b8eed47c8786ef986a9ae68e5d67c89664e362fdb6128f606215f0c95e33f529ad5207e51c8450898506c74f3fe499bb48dfe489103f5073ee623e16738d0934bff30e312d93f29af228b5b27f7327665228d12266020f8c1e1b81a6841a5b61a2a7150591451012645104630d4f40cfc80ba470b32b03f5501c3e00a7a005d3
|7,0=>0xf5353b484b97b9491a428c0927e78759b8352e7952b124e2e04b3f447219452943dc363c2b636ae03560534e5d2dc552a9472a03929aae20fa71f1651d04819f6a0d8d1048d003cf3020580158b
|8,0=>0xf8906f62e793d0362b5b5f5a83cae432d0c07721
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f0e0e0e0e0e0e0e0ef0f0a0a0f0f0a0a0c0c08080c0c0808f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cf0f0f0f0f0f0f0f0000000000000000f0f00000f0f00000f0f00000f0f0000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f00000f0f0000e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ef0f0c0c0f0f0c0c0a0a08080a0a0808f0f0f0f000000000f0f0f0f00000000f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0af000f000f000f000f000f000f000f00e0e0e0e0e0e0e0e0e0e00000e0e0000f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c
|0,1=>0xf0f000f0f0f000f0f0f000c0f0f000cf0f0e0e0f0f0e0e0f0f0e0e0f0f0e0ef0f00000f0f00000f0f0e0e0f0f0e0e5050505050505050404040404040404f0e0f0e0f0e0f0e0f0e0f000f0e0f000000000000000000e0e0e0e0e0e0e0ef0f00000f0f00000e0e00000e0e000030303030303030302020202020202023030303030303030303030303030202c0c0c0c040404040c0c0c0c040400000000000000000000f0f0e0e0f0f0e0ec0c0c0c0c0c0c0c0c0c0c0c0c0c0808303030301010101030303030101000010001000100010001000f0001000f00f000f000a000a000f000f000a000a005050505050505050505000005050000
|0,2=>0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c00000000f0c0f0c000000000f0c0f0c3030303030303030303030303030000f0f0f0f0f0f0f0f0f000f000f000f000000303000003030000030000000300f0f0f0f0f0f00000f0f0f0f0f0f00000000e0e00000e0e00000e0e00000e0e0000f0f00000f0f00000a0a00000a0a00f000f000f000f000f000c000f000cf0f05050f0f05050f0f04040f0f040410101010101010101010000010100000000000000000000505040405050404f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0000f0f00000f0f00000e0e00000e0ef0f0f0f0f0f0f0f0f0f0f0f0f0f0a0aa0a0f0f0a0a0f0f0a0a0e0e0a0a0e0e
|0,3=>0xf0f0f0f0f0f0f0f0f0f0c0c0f0f0c0cf0f0f0f050505050f0f0f0f050500005050404050504040505040405050404f0f0e0e0f0f0e0e0000000000000000f0f0f0f0f0f0f0f0f0f0f000f0f0f005050505050505050505050005050500f000f0f0f000f0f0f000f0c0f000f0c3030303030303030303030003030300f0f0f0f0f0f0f0f0f0f0f0f0f0f0000c0c0c0c0c0c0c0c0c0c0c0c0c0c00000000000000000000f0f0f0c0f0f0f0c3030303030303030303020203030202d0d0d0d0d0d0d0d0d0d0c0c0d0d0c0cc0f0c0f0c0f0c0f0c0f0c0c0c0f0c0cf0f03030f0f03030f0f03000f0f0300a0a0a0a0a0a0a0a0f0f0f0f0f0f0a0a
|0,4=>0xf0f0f0c0f0f0f0c0f0f0f0c0f0f0f0cf0f0f0f0f0f0f0f0f0f0f0f000000000000f0f00000f0f00000f0f00000000f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0000f0f00000f0f00000c0c00000c0cf0f0f0f0f0f0f0f0f0c0f0c0f0c0f0cf0f0f0f0f0f0f0f0f0f0a0a0f0f0a0af0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a3030303030303030303000003030000f0f0f0f000f000f0f0f0f0f000f000000000000000000000000e0e00000e0ef0c0f0c000000000f0c0f0c00000000f0f0f0f0f0f0f0f0f0f0e0e0f0f0e0e00f000f000f000f000f0000000f0000f000f00000000000f000f0f00000000f0f0f0f0f0f00000a0a0a0a0a0a0000
|0,5=>0xf0f0f0f0f000f000f0f0f0f0f000f0000000000f0f0a0a000000000f0f0a0a3030303030303030300030003000300
|_,_=>0
def sP:Nat→Nat
|0=>0x87c50212205843c54502122021d1408488161060a0420e0b0828d89102c2023464488080c38212602030e0830008281082e2c20a045840b0854502122020a045040b0828108262c20a122090b0828889202c20c0e08788080c101122c20a041870b081c109101420704182840608080
|1=>0x5a2c21e0424429161018a043c48b080c50234245841408488562c2020c6448816a8202122140b080c10612a458418281061a2c20a04184a81610502122138b0898502122058414084884a2c20a0424424168c20a042480b082810910885840e2810f122108414084881610502128040b
|2=>0x7c1050212205840e084887a2c21e1408488781038a0425d0b0829c8212205841408d0012202030e0830916105021221c0b0828136102c235140848816105021221a0b082813312205841409909102c20c0e0800808c450212205b00828109102c20c0e0848d101c502122170b0828108
|3=>0x1e004881610502122238b5410502123440b082810910f45840e28136102e30a042440b082810911145871510109102c2431408488161011912205842a0c5021220541042440b082810911005840464009102c2020c244221610a8a04244041408089102c23f14083081610502122028b
|4=>0x8fc38a042440b081c52f042440b080c50212345841408488a02c24f1828109102c20a042444d162a20212205849228109102db840e28109102c20a043c4881610502342440b981038a042440b0828109112c5840e28100122020a9408488161248a0424688161060a90084881610502
|5=>0xe28109102c20a0418488173020a042440b0828109102e90414084881610502002440b461050212205ce0828109102e9040e28109102c20a0424442162810910b85843c2810612205840e2810612205841408488a22c20a0418488522c2031408009102c23b1408488161060a041840b
|6=>0x105021220584
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x154005
|5,0=>0x5e61618526131846610183a60d182e60a18226071816604180a6
|6,0=>0x779dd86745dca770ddbd66d9db066a5da2766dd956639d877601d7975c9d6b7591d5d7559d4f7521d4264edd3474b5d2674819197449d0b7411cfe63ddcf073a5ce2736dcd47335cc672fdcb872c5caa728dc9c7255c8e721dc8071e5c7271adc647
|7,0=>0x2c28aedeb56ab62a58a79e968a3a2877a01e7889c22697989e5a894de4d6919e3e88dde3078a22217869e13782e20387ee1f477b21e57
|8,0=>0xbe9ef37bb1ee66b7ded87b45eca7
|9,0=>0x3016
|_,_=>0
def wAt:=mkWire dB 83 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x5434102d143c00211e2b0c2d0e18142d12211401122d1a30162112291823122976230e0914021e2f0021122d6e240e11142d142d1425122d5e13042514190c2b1235102d0c2f1025583312291e280c2d12211436102d12211436102d0e23142d0021122d14351402122d182112290c2f12211001122d0e1812211a3016211229
|1=>0x12211421122d0e09142d122112290e25142d142d04251421102d5827042d043112299c2b082d5e1004251435102d0e11142d0021122d0c2f12210825142d1402122d142d122d0401122d1435102d042112290021122d0e27142d1411102d182312296e240e110e1a1221142d5e100425143c0021122d167a0625090b0e0b142d
|2=>0x142d122108250809122d0821082d0809142d0e0b142d5e1304250c291221142d1221080e10290c2b
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x52032000003
|6,0=>0x4d20004b24830004534324033e23c23a20003733523230003020002e22d12a30000002730000000000002430000000002220002021e21c21a21731521410001220000000000001020000e20d10b2000092072000
|7,0=>0x8b28928728528328127f27d27b27927727527327126f26d26b26926726526326125f25d25b25925725525325124f2
|8,0=>0x9319219110009018f18e18d1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x540de00a81ac01403f802806f00420de0040224004077800800e000c0060018004000a25000104a00018000000c00000044800007800000de00001ac000033000004000000660000080000007800000b000001200000200000030000005000000800000080000008000000
|1=>0x2000e24200100920520fe4004108610837860807f09000fe10a05fc210e37842106f08400be10201fc180019008003a00e80de015000c024047004806f008411401001bc01c0778034007
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x82005
|6,0=>0x8009400804d0860402411400c009344001000000060000008058208c10a08018000000a002481003080
|7,0=>0x32b2b5c97481ec7a3560c75c1b9e985ca1996d9b46a42df
|8,0=>0x89cbcecd9baa
|9,0=>0xf
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 27 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_107 7 roots_107 ops++addP pm 2 dom_59 7 roots_59 ops++addP pm 3 dom_121 7 roots_121 ops++addP pm 4 dzo_91_32 6 roots_91 ops++addP pm 5 dom_91 7 roots_91 ops++addP pm 6 dom_115 7 roots_115 ops++addP pm 7 dom_57 4 roots_57 ops++addP pm 8 dom_82 4 roots_82 ops++addP pm 9 dzo_82_8 4 roots_82 ops++addP pm 10 dom_81 4 roots_81 ops++addP pm 11 dzo_81_32 4 roots_81 ops++addP pm 12 dzo_115_8 6 roots_115 ops++addP pm 13 dom_105 4 roots_105 ops++addP pm 14 dom_106 4 roots_106 ops++addP pm 15 dzo_89_32 5 roots_89 ops++addP pm 16 dom_58 4 roots_58 ops++addP pm 17 dzo_114_8 5 roots_114 ops++addP pm 18 dom_43 4 roots_43 ops++addP pm 19 dom_89 5 roots_89 ops++addP pm 20 dom_75 4 roots_75 ops++addP pm 21 dom_27 4 roots_27 ops++addP pm 22 dzo_83_8 5 roots_83 ops++addP pm 23 dom_51 4 roots_51 ops++addP pm 24 dom_83 5 roots_83 ops++addP pm 25 dom_114 5 roots_114 ops++addP pm 26 dom_99 4 roots_99 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_91_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_82_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_81_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_115_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_89_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_114_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_83_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_99 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 7 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 56 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 56 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 31 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 31 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
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
def dzo_93_32:=0x33333333000000003333333300000000
def gzo_93_32:=0x33333332000000003332333000000000
def gsh_93_32:=0x333333320000000033323330
theorem lowS_zo_93_32_81:Lower true dzo_93_32 roots_93 gzo_93_32 6:=lower_iso_b (d1:=dom_93) (r1:=roots_93) (T1:=gsh_93_32) [(dom_93,32)] (by decide +kernel) (lower_slice_b (T:=gsh_93_32) [(0x303030300000000030303030,0,4),(0x330033000000000033003300,0,8)] (by decide +kernel) lowS_81)
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(8,9),(8,40),(12,13),(12,44),(12,76),(16,17),(16,80),(20,21),(20,52),(20,84),(24,25),(24,56),(24,88),(28,29),(28,60),(28,92),(32,36),(32,40),(33,37),(33,41),(33,49),(33,97),(48,49),(48,52),(48,56),(48,112),(64,65),(64,68),(64,80),(72,73),(72,76),(72,88),(72,104),(96,97),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|4=>3
|5=>5
|6=>9
|7=>3
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xa8b988c8e074be1
|5,0=>0xfbe8cecf4ad4b19d33d73af32
|6,0=>0xe56968e226838137d4705336649e743af3229a6118ecb
|7,0=>0xc4d75c2f648e226
|8,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x4444444400000000cccccccc000000032323232323232323030303030303030000000000000000088888888888888891111111111111110000000000000000cccc0000cccc0000cccc0000cccc00022222222222222220000000000000000cccc8888cccc8888cccc0000cccc00022222222222222222222222222222222cccccccccccccccc000000000000000000033330000333300002222000022224444444444444444888888888888888b3333333000000003333333300000000cc00cc00cc00cc00cc00cc00cc00cc030303030303030303030303030303030cccccccccccccccc88888888888888880001111000011110000222200002222
|0,1=>0x33333333222222223333333300000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8b1890722c6241d8458c483a88b188283c163120e458c4141deb189072246241c8b189ac20c41418e41890639163720e458c4151163104a458c4520c4132889188241890639062298831140418820
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2942a805
|5,0=>0x25640a698aa8f6
|6,0=>0x5d6acf41a534467aedd98b2b6
|7,0=>0x1c5f53e37
|8,0=>0x786
|_,_=>0
def wAt:=mkWire dB 17 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x41e41c41d43141e41d41d41c0ab41d41c6b141f41e41d41c
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x53118000400
|6,0=>0x590000000508000082
|7,0=>0x3c5c2d1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 9
def pmP:Nat→Nat
|0=>0x1ff9971818100
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1208
|6,0=>0x41b21c
|7,0=>0x1b6
|8,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 7 roots_121 ops++addP pm 1 dom_109 7 roots_109 ops++addP pm 2 dom_124 5 roots_124 ops++addP pm 3 dom_61 5 roots_61 ops++addP pm 4 dom_117 7 roots_117 ops++addP pm 5 dom_93 6 roots_93 ops++addP pm 6 dzo_93_32 6 roots_93 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_93_32_81 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 7 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_125==dom_125)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
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
theorem lowS_126:Lower true dom_126 roots_126 goal_126 8:=lower_slice_b [(0x50505050505050505050505050505050,32,36)] (by decide +kernel) lowS_122
def dzo_141_2:=0xcccc0000000000000000000000000000cccc
def gzo_141_2:=0xccc800000000000000000000000000008800
def gsh_141_2:=0x333200000000000000000000000000002200
theorem lowS_zo_141_2_141:Lower true dzo_141_2 roots_141 gzo_141_2 5:=lower_iso_b (d1:=dom_141) (r1:=roots_141) (T1:=gsh_141_2) [(dom_141,2)] (by decide +kernel) (lower_slice_b (T:=gsh_141_2) [] (by decide +kernel) lowS_141)
def dzo_201_2:=0xc0c0000000000000c0c0000000000000c0c0000000000000c0c
def gzo_201_2:=0xc0c0000000000000c080000000000000c0c0000000000000800
def gsh_201_2:=0x303000000000000030200000000000003030000000000000200
theorem lowS_zo_201_2_137:Lower true dzo_201_2 roots_201 gzo_201_2 5:=lower_iso_b (d1:=dom_201) (r1:=roots_201) (T1:=gsh_201_2) [(dom_201,2)] (by decide +kernel) (lower_slice_b (T:=gsh_201_2) [(0x303000000000000000000000000000003030000000000000000,0,64)] (by decide +kernel) lowS_137)
def dzo_205_2:=0xcccc000000000000cccc000000000000cccc000000000000cccc
def gzo_205_2:=0xcccc000000000000ccc8000000000000cccc0000000000008800
def gsh_205_2:=0x3333000000000000333200000000000033330000000000002200
theorem lowS_zo_205_2_141:Lower true dzo_205_2 roots_205 gzo_205_2 6:=lower_iso_b (d1:=dom_205) (r1:=roots_205) (T1:=gsh_205_2) [(dom_205,2)] (by decide +kernel) (lower_slice_b (T:=gsh_205_2) [(0x3333000000000000000000000000000033330000000000000000,0,64)] (by decide +kernel) lowS_141)
namespace S_207
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(2,66),(3,11),(3,67),(3,131),(4,68),(4,132),(5,13),(5,69),(5,133),(6,70),(6,134),(7,15),(7,71),(7,135),(8,9),(8,136),(10,11),(10,74),(10,138),(12,13),(12,76),(12,140),(14,15),(14,78),(14,142),(64,65),(64,66),(64,68),(64,192),(72,73),(72,74),(72,76),(72,200),(128,129),(128,132),(128,136),(128,192),(130,131),(130,134),(130,138),(130,194)]
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
|3,0=>0x699b0
|4,0=>0xfe4fdf6b4cf4682dba8bd2506cf3face688c78fdbc29fb94f1a5ed3a0f2b97baa8aa95825e378a536fee96ac2a694b5583d1571db48e9634ab832a4e2eb852bf622ba7913bff0e3610c5e7
|5,0=>0xf7c23f4b17f30e5f2078f1f3aef7b5ed087eba06eaffee5fdae1181e0f0fdcc9ddcacddc751d32a7cdae2cd675c7bcbc17d5bfbeabd87bbaf71baaf2ba99bb733caed3eadabaabdc6a750fa6de3a22659d0579b5a498498978b495c01922208a74d884e3879ca870c884ea783cda829488195680411729176e23b6d59b6ad9e6932167958673bd664ee65b51611fc60e325a66e57f3950ef54e5b94c1d948a6a45f7b4235e41fb2416c8410f83e37a366c134bc931989269fe260581fa881c3aa1aa611997e1686914732139bb11f340c19900b92
|6,0=>0xf9f47f8e64f4b70e771ee1f6bdb098d2339d155ecc56dcaeecc9c30c638fc54c0bead6bc183b8d16b559fb409cb2c5eb21f0af622ac046a9fada4c93a3268a13309af32921a990c69869197d8227b670706f66bd6768acb6417f61e2e60e3c5cffe5803251dfd511ef4a9d84a2844a203468a33e5ea3bc6f39e293931c317aa2a29a27f50219db1d86013cf212c72107551071b0b68a06ecc0553e
|7,0=>0xefc3bb967db1bbe982ee904c2735166f2f15bf25362072be432749e1d42c188020662c
|8,0=>0x83b1d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x707000000000000050500000000000003030000000000000000ffff000000000000fff0000000000000f0f0000000000000f0f0ffff000000000000ff00000000000000ffff000000000000ff00ffff000000000000ffff000000000000aaaa000000000000aaaaffff000000000000ffff000000000000ff00000000000000ff00f0f0000000000000f0f0000000000000f0f0000000000000f0f0ffff000000000000ffaa000000000000aaaa000000000000aaaaff00000000000000ff00000000000000ff00000000000000ff00afaf000000000000afaf000000000000abab000000000000aaaaaaaa000000000000aaaa000000000000aaaa000000000000aaaaffff0000000000000000000000000000ffff0000000000000000ffff000000000000ffff00000000000000000000000000000000fafa000000000000fafa000000000000fafa000000000000fafacccc000000000000cccc000000000000cccc000000000000ccccffff000000000000ff00000000000000aaaa000000000000aa00ffff000000000000ffff000000000000ffff0000000000000000
|0,1=>0xffff000000000000ffff000000000000bbbb000000000000aaaa555500000000000055550000000000005454000000000000545400000000000000000000000000000000ffff000000000000aaaa000000000000000000ff000000000000ffff000000000000ff00ffff000000000000ffff000000000000ffff000000000000ff00ffff000000000000ffff0000000000003333000000000000000033ff00000000000000ff00000000000033bb00000000000000aa030f000000000000000f00000000000003030000000000000000050500000000000005050000000000000101000000000000000000000000000000000000000000000000bbbb000000000000aaaaffff000000000000ffaa000000000000ff00000000000000ff00ffff0000000000000000000000000000fefe00000000000000000f0f0000000000000f0f0000000000000b0b0000000000000a0affff000000000000ffff000000000000ffff000000000000aaaaffff000000000000aaaa000000000000ffff000000000000aaaafafa000000000000fafa000000000000fafa0000000000000000
|0,2=>0xaa000000000000aaaa000000000000aaaaffff000000000000ff00000000000000000000000000000000000f0f000000000000000f0000000000000f0f0000000000000000fefe000000000000fefe000000000000fefe000000000000fefeaaaa000000000000ffff000000000000aaaa000000000000aaaaffff0000000000005555000000000000ffff00000000000000000f0f0000000000000f0f0000000000000f0f0000000000000a0a00ff00000000000000ff00000000000000aa00000000000000aa3333000000000000000000000000000033330000000000000000ffff00000000000000ff000000000000ffff00000000000000aa0f0f0000000000000f0f0000000000000f0f0000000000000f005555000000000000550000000000000055550000000000005500ffff000000000000aaaa000000000000000000000000000000000505000000000000050500000000000000000000000000000000ffff000000000000fafa000000000000f0f0000000000000f0f000000000000000000000000000000000fefe000000000000fefe
|0,3=>0xff00000000000000ff00000000000000ff00000000000000aa0000000000000000ffff000000000000000000000000000000005555000000000000555500000000000000000000000000000000bbbb000000000000aaaa000000000000bbbb000000000000aaaaffff000000000000ffff000000000000eeee000000000000eeeeafaf000000000000afaf000000000000afaf000000000000aaaaffff000000000000ff00000000000000ffff0000000000000000ffff000000000000ffff000000000000cccc000000000000cccc0f0f0000000000000f0f00000000000003030000000000000000afaf000000000000afaf000000000000aaaa000000000000aaaacdcd000000000000cdcd000000000000cccc000000000000cccc0f0f0000000000000f0f0000000000000f0f000000000000000055550000000000005555000000000000555500000000000055000000000000000000ffff0000000000000000000000000000aaaa00ff00000000000000ff00000000000000fa00000000000000faccff000000000000ccff000000000000ccee000000000000ccee
|0,4=>0xaaaa000000000000aaaa000000000000aaaa000000000000aa0000ff00000000000000ff000000000000000000000000000000005555000000000000555500000000000055550000000000000000555500000000000055550000000000001111000000000000000033ff00000000000000ff00000000000033330000000000000000000000000000000000ff000000000000000000000000000000aa05050000000000000505000000000000050500000000000000000f0f00000000000005050000000000000f0f000000000000000000aa00000000000000ff00000000000000aa00000000000000aa050500000000000005050000000000000404000000000000040400000000000000000000000000000000ffff000000000000ff00000000000000000000ff00000000000000000000000000000000fbfb000000000000fafa000000000000fbfb000000000000fafaffff00000000000000ff000000000000ffff000000000000000077770000000000005555000000000000333300000000000000000000000000000000ffff0000000000000000000000000000ff00
|0,5=>0xff000000000000000000000000000000ff00eeee000000000000eeee000000000000eeee000000000000eeeeccff000000000000ccff000000000000cccc000000000000cccc000000000000000055550000000000000000000000000000000000ff00000000000000ff00000000000000ff0000000000000000ffff000000000000ffaa000000000000ffff000000000000ffaaff00000000000000ffff000000000000ff00000000000000ff00ffff000000000000ffff000000000000fafa000000000000fafa5555000000000000555500000000000044440000000000004444dddd000000000000dddd000000000000cccc000000000000ccccffff000000000000fafa000000000000ffff000000000000fafaffff000000000000ffff000000000000fefe000000000000fefe
|_,_=>0
def sP:Nat→Nat
|0=>0x1c08300100cf0508341823a10502220421c140830536281090a2018c0a6850632142080c14c04101829708201960a10a8a04302880618a041018985082010c0a40683044820a04180801008890080c1010a1040a04240080c1478410381060034182180058a04242880e182840608080
|1=>0x1a2812f0a1040304300051a281120c10d8a04182ae10083055a104200618284100c12b0a1068a041950410083290a10403044400406086280a10506501538414083260a104020c9428414083010a1068a04452041028106008c4200c151084208300108018c0a2019f0a1068a042400d
|2=>0xc14d0806086057c205060a69e8814f060508201bb181420804e830508345020ce420806e0605083450222302080c15b841a2810600b840304d8284100da860a1040a2c182841a08300681040a04cc28410b0305088840304c82841a0c106001042c063028406083310a105300ca0284
|3=>0x41928508281068e14208061a30509145020c16208860c30508345023a182151408305082c5020c1570d140848508347020c1420814086054629d86501420a701940508201060a4020d140834208205060b042080c14d37083600a041820a0419f85083418248142080608905082050c
|4=>0x3a1420d140998508228030c1420806f0284100c6054e106c514083001a0c11108345029e1420d14083007a34182181424514083059c345020d34208061829a08205060b3020814182cb0820502223000a041a50508210820c1420814083005c2051f0c1420804182c908201060b2020d
|5=>0x14083050910683041828411441820c14208060860508345020c0020d140830508b840a041990508205060a9c24e102810c0c002880608305088868a04182849c20182221424510281060a1040a04180057a205020c16684102812b0c14208140848508207020c1420d14086060020182
|6=>0x6083050820502223028410281060a1170d102810600104020c002b408201820c0028416205060a9c208141a9850828106501420d14083240a1040a0448305083458a0418284102a9060a1040a04303057c6c40a0418284100c3054e1040a763030508205020ca82841029c0c0c14208
|7=>0x1029e060a1040a18182a708205020c14223100dc060a1068a04443041028305341068a043030508205060a9c23d1029d860a106c5140830508205020d0828410281060b5c20880281060a12b0d140830508345020c1423d100c1060a11f0804182b408216030c1425510281060a10454
|8=>0x8201820c14208140830508f8688140830508205020c1424e1028106001420814182a7096c5020c1420d1408305082055a0c1420814086060a1040a04182847a2050222180041408606501421b1a281060a1058814e030508345020c14244102ac860a1040a0418284b0205023a18284
|9=>0x814083050820502221828416205020c1420814e0305
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x4aa8905116a219440a87c50eea1c9436a86850c6a17942ca854509ea129422a8405076a0d9418a82c504ea08940ea8185026a039404a8045
|5,0=>0x426c835903b20163f6c7d58f7b1e963c6c7758ebb1d16396c7158dfb1b96366c6b58d3b1a16336c6558c7b1896306c5f58bbb17162d6c5958afb15962a6c5358a429426278c4d9898312a6248c47988c31126218c41988030fa61e8c3b987430e261b8c35986830ca6188c2f985c30b26158c299850309a6
|5,1=>0x28f6512ca0d93eb27764e2c9b1533326064b6a955927b2496486c8f591bb2316456c89590fb2196
|6,0=>0x2183c297844f06de0a3c0e680ef001dfd33f377d8ef999f033da67a6ef31de333bf7770eec5dd53ba37738ee55dc7b3896704ededdba3b6d76cced7ddac3b517696cd1599f3b377660eca9991bb1c762ccc3dd843b0175f4ebd1976bae765c2cb69d69bacc758aeaf9d5bbab16554ea8dd4e3a957
|7,0=>0x2463c8578fed1e5a393c6b78c8f175e2bb4516896d115a1f3c377
|8,0=>0x4936
|_,_=>0
def wAt:=mkWire dB 92 208 0xffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x101518170c11041610120c110a11061214191015101214190c151a1310150c120c020a110cf90a120c111419041604161a1314190c1510150c120c110a1122100c1106000a1114191a1b22110c15043104110c11146a1a1006121402061214191817141906090c112211581314190a12141914190c111a301a1b22100a111a30
|1=>0xc1204310c111a1310150b391012161710111a19101510150c1214190a1214020a1106091419061114190c111a1010150a1114020a1114190a110416701b041110320c111a1b101522110c15101104f50c120a120c1110010a111419041604310c110af50c1204110c111a121015141910150615141914190c110a1110151a10
|2=>0xc151011041114190a12101510120a1104161017101504190c110c120a1110320c111a11101504111a1210150539101222120c1522130c150c9d041604160c1122100c15141904110c1510154e1104160c1110150416
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11000000001000000000000000000
|5,0=>0x2011f10001d20000000000000001b21920000000000001810000001711611511411310000001210001020f10e10c20000000000000b1000000092081000000071052000000000041031021
|5,1=>0x2b1000000000292281271243000231000000000000000000212000000
|6,0=>0x9c19a29829719529329128f28d28b28928728528328127f27d27b27920007727527327126f26d20006b26a16826716526326216025e25c25a25915725525325124f24d24b24924724524324123f23d23b23923723523323123012e22c2
|7,0=>0xaa1a91a81a71a61a51a41a31a21a11a019f19e19d1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x2408110408260410020000928040201d300e88064402a20111008800408020000d100488024001000053002880108008000220009800440020000900020000800020000
|1=>0x4080d2aa6842342019574caaa645d122e1884442fb615f30ae98570c2ae415430a010500023a611410840020000fa607c303618174c0ba205c302a9814440a200491
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x80002000000000
|5,0=>0x5000012085800140000000021000000000000a80a800000006c300900000000d28000000800008544508000500108568000000200010200014d000002151
|6,0=>0x71f2cd1ad186c2f8f396c8aec564003dd8a253503e4d839588df5e80c47970ccbc2fb1a5da75d51eb8595295132c7
|7,0=>0x9b7ea8e26df8ca6974df7
|8,0=>0x24
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 17 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_205 7 roots_205 ops++addP pm 1 dom_198 5 roots_198 ops++addP pm 2 dom_197 5 roots_197 ops++addP pm 3 dom_201 5 roots_201 ops++addP pm 4 dzo_141_2 5 roots_141 ops++addP pm 5 dom_204 5 roots_204 ops++addP pm 6 dom_203 7 roots_203 ops++addP pm 7 dom_199 6 roots_199 ops++addP pm 8 dom_141 5 roots_141 ops++addP pm 9 dom_202 4 roots_202 ops++addP pm 10 dom_206 6 roots_206 ops++addP pm 11 dzo_201_2 5 roots_201 ops++addP pm 12 dzo_205_2 6 roots_205 ops++addP pm 13 dom_137 4 roots_137 ops++addP pm 14 dom_79 5 roots_79 ops++addP pm 15 dom_77 4 roots_77 ops++addP pm 16 dom_75 4 roots_75 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_207 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_141_2_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_201_2_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_205_2_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_75 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_205 7 s (0,roots_205.map (·&&&dom_205)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_207 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_205 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_207 gM v ys):RunD true dom_207 gM v (ori ys):=h
def Z (s:Nat):=barP dom_207 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 30 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 30 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 85 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 85 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 62 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 62 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 14 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_207 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_slice_b [(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,16,18)] (by decide +kernel) lowS_213
def dzo_137_2:=0xc0c00000000000000000000000000000c0c
def gzo_137_2:=0xc0800000000000000000000000000000800
def gsh_137_2:=0x30200000000000000000000000000000200
theorem lowS_zo_137_2_137:Lower true dzo_137_2 roots_137 gzo_137_2 4:=lower_iso_b (d1:=dom_137) (r1:=roots_137) (T1:=gsh_137_2) [(dom_137,2)] (by decide +kernel) (lower_slice_b (T:=gsh_137_2) [] (by decide +kernel) lowS_137)
def dzo_210_8:=0x5000500000000000500050000000000050005000000000005000500
def gzo_210_8:=0x5000500000000000500050000000000050004000000000004000000
def gsh_210_8:=0x50005000000000005000500000000000500040000000000040000
theorem lowS_zo_210_8_82:Lower true dzo_210_8 roots_210 gzo_210_8 5:=lower_iso_b (d1:=dom_210) (r1:=roots_210) (T1:=gsh_210_8) [(dom_210,8)] (by decide +kernel) (lower_slice_b (T:=gsh_210_8) [(0x50005000000000005000500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_211_8:=0xf000f00000000000f000f00000000000f000f00000000000f000f00
def gzo_211_8:=0xf000f00000000000f000f00000000000f000e00000000000e000a00
def gsh_211_8:=0xf000f00000000000f000f00000000000f000e00000000000e000a
theorem lowS_zo_211_8_82:Lower true dzo_211_8 roots_211 gzo_211_8 6:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_8) [(dom_211,8)] (by decide +kernel) (lower_slice_b (T:=gsh_211_8) [(0xa000a00000000000a000a00000000000a000a00000000000a000a,0,1),(0xf000f00000000000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_153_2:=0xc0c0c0c0000000000000000000000000c0c0c0c
def gzo_153_2:=0xc0c0c080000000000000000000000000c0c0800
def gsh_153_2:=0x303030200000000000000000000000003030200
theorem lowS_zo_153_2_137:Lower true dzo_153_2 roots_153 gzo_153_2 5:=lower_iso_b (d1:=dom_153) (r1:=roots_153) (T1:=gsh_153_2) [(dom_153,2)] (by decide +kernel) (lower_slice_b (T:=gsh_153_2) [(0x303000000000000000000000000000003030000,0,16)] (by decide +kernel) lowS_137)
def dzo_217_2:=0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c
def gzo_217_2:=0xc0c0c0c000000000c0c0c08000000000c0c0c0c000000000c0c0800
def gsh_217_2:=0x3030303000000000303030200000000030303030000000003030200
theorem lowS_zo_217_2_137:Lower true dzo_217_2 roots_217 gzo_217_2 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_2) [(dom_217,2)] (by decide +kernel) (lower_slice_b (T:=gsh_217_2) [(0x3030000000000000303000000000000030300000000000003030000,0,16),(0x3030303000000000000000000000000030303030000000000000000,0,64)] (by decide +kernel) lowS_137)
namespace S_219
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,18),(2,66),(3,11),(3,19),(3,67),(3,131),(8,9),(8,136),(10,11),(10,26),(10,74),(10,138),(16,17),(16,18),(16,80),(16,144),(24,25),(24,26),(24,88),(24,152),(64,65),(64,66),(64,80),(64,192),(72,73),(72,74),(72,88),(72,200),(128,129),(128,136),(128,144),(128,192),(130,131),(130,138),(130,146),(130,194)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_219.map (·&&&dom_219)
def gM:=goal_219&&&dom_219
def NN:Nat→Nat
|4=>3
|5=>12
|6=>20
|7=>13
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x7fd74527b33dcb4
|5,0=>0xf6700a88439a8466eb5462704608d3545bf3d9ac32dea2d5c71ed7d036de
|6,0=>0xc15c9688d962e7b5eab2511de4d8fd3bf253b3182e96626632247c41ea481cfb41c0f0166ff130a405cb204e39042d7017fe
|7,0=>0x9a3da72dcc4580b318202c1d22b8cc2711e1c56715d8f1370d0dee20543305001
|8,0=>0xdadac488e40af55
|9,0=>0x798d4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f000f000000000f0f000f000000000f0f000a000000000f0f000af0f0f0f000000000f0f0f0f000000000f0f0a0a000000000f0f0a0af0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0a0000f0f0000000000000f0f0000000000000f0f0000000000000000f0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f0000f000f00000000000f000f00000000000f000f00000000000f000f00c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0cf0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0af0f0f0f000000000a0a0a0a000000000f0f0000000000000a0a0000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a30f030f00000000030f000f00000000030b030b00000000030b000af0f0f0f0000000000000000000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f00000000000000000000000000000000
|0,1=>0xf0f0a0af0f0f0f000000000f000f00000000000f0f0f0f000000000f000f000000000000000000f0f0f0f0000000000000000000000000f0f0a0af0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f000000000000000000f0f0f000000000000000000000000000f0f0f0000000000000000000000000000000000f0f0f0f000000000a0a0a0a0000f0f0000000000000a0a0000000000000f0f0000000000000a0af0f0f0f000000000f0f0f0f0000000000000f0f0000000000000a0af0f0f0f000000000f0f0f0f000000000c0c0c0c000000000c0c0c0c303030300000000030300000000000003030303000000000303000000f000f00000000000f000f00000000000a000a00000000000a000af0f0f0f000000000f0f000f000000000f0f0f0f000000000f0f000af0f0f0f000000000f0f0f00000000000f0f0f0f000000000f0f0f00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f000000000000000000000000000000000000b0b0b0b000000000b0b0a0a
|0,2=>0xf0f0f0f000000000f0f0f0f000000000e0e0e0e000000000e0e0e0e50505050000000005050505000000000505050500000000000000000000f0f0000000000000f000000000000000f0f0000000000000f00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0a0ae0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0e0000000000000000f0f0a0a0000000000000000000000000f0f0a0a
|_,_=>0
def sP:Nat→Nat
|0=>0x1b2c70c100e1081cd0402442076830091070d50401081c36010042174832811035950405041c30402d120734a1081c314a2c920718a4cb1cd0094481d20c92070c50042100c100f2470c100e1081cd28420734630b20714a2481c61440c2040
|1=>0x1c60ca0447873430042070c194011e8430401070e40408c42070c10221081c30402d12070ca0442070c504024420748300b44884100b2481c32802d12071812512071830532c70c10204481c30407c42070c10047970ca3c41c30407442070c1
|2=>0x1081c30401081c60c10042073430401088430401070d50402c42070ca0402442071830401088432810042260c10231081c328100b4481c3040108
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x283129888c3e61c30cd45ac27610b06d82ac0f6
|6,0=>0x6a3b35d8cebf75cb2c9d58ca574fb261d22e8c54331fdcf2c72735b991cbae567
|7,0=>0x12e693447a22ef11684c409df6ef56773ba19c4cdb7
|8,0=>0x505e74f346
|9,0=>0x1486
|_,_=>0
def wAt:=mkWire dB 39 220 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x351040104346050c044051c3440d10044050c0440110341110c0431120941112c1c40d1c0480504055112068301381d10d100440d701c8112c043111014d03043481a10143010194d130c14701283410135104010434301101482510143050c44d01044430544d030500446110c04301
|1=>0xc0410d1c3481a0c0410110344050c0470d04047190c04a110014401103400d04048050434a0f04048051c35e1320151050044b29040440d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xf31a42503183300000009001
|6,0=>0x806001e9ba36e6d8599b125c6b08002934c68cd019e236660ca9923
|7,0=>0x5b2b255caa9532a253ca694b29251ca29432
|8,0=>0x17c6f0dd1
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x29c61f906b6fc83187e410c2f07f69f80170d400986e002d3f001653800908c0040fe001e3f000e1b80070cc003060000c3f000613800206400102000043e00020400010100004300001ff0000fc800020c0000300000140000090000038000010000000
|1=>0x2005b6f000c27500619a0138bd00841e710c2a
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xa2470c2000101
|6,0=>0x38540380548920b01b58d5440c6351
|7,0=>0x1731475f8636a565e622
|8,0=>0x1391c
|9,0=>0xf
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_217 8 roots_217 ops++addP pm 1 dom_203 7 roots_203 ops++addP pm 2 dom_155 7 roots_155 ops++addP pm 3 dzo_137_2 4 roots_137 ops++addP pm 4 dzo_82_8 4 roots_82 ops++addP pm 5 dom_218 7 roots_218 ops++addP pm 6 dom_195 5 roots_195 ops++addP pm 7 dzo_210_8 5 roots_210 ops++addP pm 8 dom_147 5 roots_147 ops++addP pm 9 dom_137 4 roots_137 ops++addP pm 10 dom_91 7 roots_91 ops++addP pm 11 dom_211 8 roots_211 ops++addP pm 12 dom_82 4 roots_82 ops++addP pm 13 dzo_211_8 6 roots_211 ops++addP pm 14 dom_27 4 roots_27 ops++addP pm 15 dzo_153_2 5 roots_153 ops++addP pm 16 dzo_217_2 6 roots_217 ops++addP pm 17 dom_89 5 roots_89 ops++addP pm 18 dom_209 7 roots_209 ops++addP pm 19 dzo_83_8 5 roots_83 ops++addP pm 20 dzo_201_2 5 roots_201 ops++addP pm 21 dom_202 4 roots_202 ops++addP pm 22 dom_216 5 roots_216 ops++addP pm 23 dom_75 4 roots_75 ops++addP pm 24 dom_154 4 roots_154 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_137_2_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_82_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_210_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_211_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_153_2_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_217_2_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_83_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_201_2_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_154 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_217 8 s (0,roots_217.map (·&&&dom_217)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_217 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_219==dom_219)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_219 gM v ys):RunD true dom_219 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_219 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 20 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 20 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 13 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 13 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
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
def dzo_205_32:=0x333300000000000033330000000000003333000000000000333300000000
def gzo_205_32:=0x333300000000000033320000000000003332000000000000333000000000
def gsh_205_32:=0x3333000000000000333200000000000033320000000000003330
theorem lowS_zo_205_32_193:Lower true dzo_205_32 roots_205 gzo_205_32 6:=lower_iso_b (d1:=dom_205) (r1:=roots_205) (T1:=gsh_205_32) [(dom_205,32)] (by decide +kernel) (lower_slice_b (T:=gsh_205_32) [(0x3030000000000000303000000000000030300000000000003030,0,4),(0x3300000000000000330000000000000033000000000000003300,0,8)] (by decide +kernel) lowS_193)
def dzo_193_32:=0x300000000000000030000000000000003000000000000000300000000
def gzo_193_32:=0x300000000000000020000000000000002000000000000000000000000
def gsh_193_32:=0x3000000000000000200000000000000020000000000000000
theorem lowS_zo_193_32_193:Lower true dzo_193_32 roots_193 gzo_193_32 4:=lower_iso_b (d1:=dom_193) (r1:=roots_193) (T1:=gsh_193_32) [(dom_193,32)] (by decide +kernel) (lower_slice_b (T:=gsh_193_32) [] (by decide +kernel) lowS_193)
def dzo_201_32:=0x30300000000000003030000000000000303000000000000030300000000
def gzo_201_32:=0x30300000000000003020000000000000302000000000000030000000000
def gsh_201_32:=0x303000000000000030200000000000003020000000000000300
theorem lowS_zo_201_32_193:Lower true dzo_201_32 roots_201 gzo_201_32 5:=lower_iso_b (d1:=dom_201) (r1:=roots_201) (T1:=gsh_201_32) [(dom_201,32)] (by decide +kernel) (lower_slice_b (T:=gsh_201_32) [(0x300000000000000030000000000000003000000000000000300,0,8)] (by decide +kernel) lowS_193)
def dzo_197_32:=0x3300000000000000330000000000000033000000000000003300000000
def gzo_197_32:=0x3300000000000000320000000000000032000000000000003000000000
def gsh_197_32:=0x33000000000000003200000000000000320000000000000030
theorem lowS_zo_197_32_193:Lower true dzo_197_32 roots_197 gzo_197_32 5:=lower_iso_b (d1:=dom_197) (r1:=roots_197) (T1:=gsh_197_32) [(dom_197,32)] (by decide +kernel) (lower_slice_b (T:=gsh_197_32) [(0x30000000000000003000000000000000300000000000000030,0,4)] (by decide +kernel) lowS_193)
namespace S_237
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(4,36),(4,68),(4,132),(5,13),(5,37),(5,69),(5,133),(8,9),(8,40),(8,136),(12,13),(12,44),(12,76),(12,140),(32,36),(32,40),(33,37),(33,41),(33,97),(33,161),(64,65),(64,68),(64,192),(72,73),(72,76),(72,104),(72,200),(96,97),(96,100),(96,104),(96,224),(128,129),(128,132),(128,136),(128,192),(160,161),(160,164),(160,168),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_237.map (·&&&dom_237)
def gM:=goal_237&&&dom_237
def NN:Nat→Nat
|4=>11
|5=>96
|6=>286
|7=>130
|8=>18
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xf7c1adb962d74f9cd9d2aeb6797ecd80fd95962533674253f716fd5
|5,0=>0xe5196dd32ddcc7dd6459d3b11cc6e5c2b8bbe9a1be7d6be73bbb5deba73db81ffb5596b4b45aeb61ab9e5a5de3a29a4a132aa0cd29e96699e0799dfe992279796795b7f928a9913658ff9f8ed3c8bc378140d7fa8f7f5867a6cb7907c773a0744e5727dc6d0ab6cd876b8256965166cc46421d63ea3629115d09759f5d59bed58682545a8543e1521eb4d4bf4c34c497654957a4902d466f141c9e4187b3faf43dcec3dcdd3cdde3ca6f382f037f20364a12fd172ec08265c5254612377b22e6a224d8213c01ea661b0b817411120d310f4a10d1e107f10f4ce0f0c20e87f09a3507a77056000523901fb10075d0039c
|6,0=>0x48c10487b946ee646a1b459884442843def43cdb4345342a8f42a7c424fe40d7640b243fa343f4953f1533df943d7373d0303cf893c8673b4f73ae803ae2439b37396df3835437f613721236c1336bbc36abd3637d35ef735aca35a3b348f53378a332d832f1131d3c31059300d32fb852e1f42d8802d3a72c75c2c0962aad42aa9e2a91f29f3029ea128ddd28b30286ad28068279c726db4264c825b8f25b4f257d124cd3244df2449c21ebd213161fffe1fa9f1f5dc1e35e1da401d0401c90e1c8d51c58f1b9da1b16419573190a0181f717ded17bf416866164651589014a3d134e61318712d0e126071254e112ce1115b103c40fd100e87f0e3240e2380dfc20db550d2ad0c9d10bbc60b3350b0340a5fb0a22209fa50950f094f009224089be077fc0715006d26055fb04b5204a72045a6037c10329302e7301dc6002bc
|6,1=>0xa91a8a8b5aa523da4d3ca2a1ea0f39a0b67a04359ef1a9de1a9cf3b9cd139cb6b9cb679c0dd9a58699837991bd968b295b0b94cda942a893a5091ec79145b909e1907c28e9858e8ad8d0e98cd9a8bee48a3a689be788d0988211879a08723186d9b85514851a283c738393983211820a081f2d80ce58028b7fa8f7f3b57e84d7d3377d1917d16d7c89779d777957878078774f676bf076a2f75e7c758e874c8a73082727dc6fdb46e4546de336dde16d78b6d0ab6c1de6b7636b22c6a6ed695a569340691ca68e38680f7674096717866e08668d065c4064a6b62a306209e610446096c60306601f8600e75fe035dad95cda75c8d65b9ff5b3145b03b5a4245a39059d5059c56599d1594a3583d2575a0555e954ace533d152ee151508504044f6e84f1d64f0e54ee734e0234dea54cc224cbd04be4f4b16f498fc4957a48fd4
|6,2=>0xfd638fc788f7b71f107deea03ee5deed918ec9cceb59ae9e18e8a86db7fed8995d6459d2d5dcdec9c1655c0fc4bd425b9b86b9a86b52b9b4eaeb4be1b1d13b15cab0a23abcfbaacb7aa548
|7,0=>0xefaabedab5e3d41e0b49def86da43ed3855d32e3d0f0dc5b8fc13f3bbaefb8c57b8986b7b40b790fb494cb47c2ac38bab32ea86b0a62e2a54a6a3c94a2f88a2cdea21d3a1cd19af9a979d095a319447a90dd38e5b38d186882118501984d4a7ebd77d86d7d6da7d50e7ca927c2937aa6178dc976f877448d7342f7228e6ecb96c63a6ba3d6a6956a61a6a57868845683a9682d86706866c73625ca620625fabc5f2435e19b5bdcd5879857681571fd565c4531bc5229c501044e6714bf664b9c84b0fe47faf456cd455fc44db7441ad43b09434534280c4138a40b313ec663eb5b3e8e73d8c73c79e369d636546362fc35b4d34335337de3378a32e8c31857318072fecb2f2e52e60f2c96e28b3026db4227bc225c72243b210911cdc418b2a18a9918381163e915de613bb0139991323c0eadd0e22c0d11d0b1290813b02073
|7,1=>0xfd962f107d
|8,0=>0xf0cadedab5e6adac30fbbad38a4c2e9a10d9427e917ab89955743d36525a5a8794e2f64664b43d2941762087fd
|9,0=>0xf0cad
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccc0000cccc0000cc000000cc00000088880000888800008800000088033330000333300002222000022220000333300003333000022220000222200000000000000000000000000000000444400004444000088880000888b33000003330000033300000333000003330000033300000333000003330cccc0000cccc0000cc000000cc000000c0c00000c0c00000c0000000c00222200002222000022220000222200002222000022220000222200002222cccc0000cccc0000cccc0000cccc0000cccc000000000000cccc0000000333200003332000033320000333200003332000033320000330000003300c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c333300003333000033330000333300002222000022220000222200002222cccc0000cccc00000000000000000000cccc0000cccc000000000000000333300000000000033330000000000003333000000000000333300000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc0323200003232000032320000323200003232000032320000323200003232cccc0000cccc00008888000088880000c0c00000c0c0000080800000808333300003333000033330000333300003333000033330000000000000000
|0,1=>0xcccc0000cccc0000cccc0000cccc0000888800008888000000000000000002200000022000000220000002200000022000000220000002200000022cccc0000cccc00000088000000880000cccc0000cccc000000880000008b33300000000000033330000030300003333000000000000333300000202cccc0000cccc0000cc000000cc000000cccc0000cccc0000cc000000cc000000000000000003232000032320000000000000000000032320000323244440000444400004400000044000000444400004444000044000000440003300000033000000330000003300000033000000330000003300000022cccc0000cccc0000cccc0000cccc0000cccc0000cccc00008888000088880000000000000000000000000000000333300003333000022220000222244440000444400008888000088880000444400004444000088880000888b33300003333000033330000333300003333000022220000333300000000cc880000cc880000cc880000cc880000cc880000cc880000cc880000cc8b23200003232000032000000320000003232000032320000320000003200cccc0000cccc0000cccc0000cccc0000000000000000000000000000000333300003333000033330000333300003300000033000000330000003300
|0,2=>0x88880000888800008888000088880000888800008888000088800000888222200002222000022220000222200002222000022220000220000002200cccc0000cccc0000cccc0000cccc000000000000000000004444000000000000000000000000000000000000000333300003333000000220000002288080000880800008808000088080000880800008808000088000000880111100001111000011110000111100001111000011110000111000001110000000000000000000c0000000c00000404000004040000040c0000040c323200003232000032320000323200003200000032000000320000003200c0c00000c0c00000c8c80000c8c80000c0c00000c0c00000c8c80000c8c8000000000000000000000000000000033330000333300000202000002020000000000000000000000000000000000cc000000cc000000880000008b33300003333000033330000333300003131000000000000313100000000cccc0000cccc0000cccc0000cccc0000c0c00000c0c00000c0c00000c0c222200002222000000000000000000002222000022220000000000000000cccc0000cccc0000cccc0000cccc0000444400004444000088880000888911100001111000011110000111100001111000011110000110000001100
|0,3=>0xc0c00000c0c00000c0c00000c0c0000080800000808000008080000080830300000303000002020000020200000303000003030000020200000202cccc0000cccc0000c8c80000c8c80000cccc0000cccc0000c8c80000c8cb33300003333000033330000333300003333000033330000330000003300cccc0000cccc0000ccc00000ccc00000c8c80000c8c80000c8c00000c8c000000000000000033330000333300000000000000000000323200003232cccc0000cccc0000c0c00000c0c00000cccc0000cccc0000c0c00000c0c330000003300000033000000330000003333000033330000330000003300c8c80000c8c80000c8c80000c8c80000c8c80000c8c8000000000000000333300003333000033330000330000003333000022220000333300002200cccc0000cccc0000cccc0000cccc0000cccc000000000000cccc0000080b33300003333000033330000333300003232000032320000323200003232c8c80000c8c80000c0c00000c0c00000c8c80000c8c80000c0c00000c8cb030000030300000303000003030000033330000333300003232000032320c0c0000040400000c0c0000040400000c0c0000040400000c0c0000000333300003333000033220000332200003333000033330000332200003322
|0,4=>0x440400004404000044040000440400004404000044040000440000004403333000033330000222200002222000033000000330000002200000022004444000044440000cccc0000cccc0000444400004444000088880000888b33300002222000033330000000000003333000022330000333300000000cccc0000cccc00004444000044440000cccc0000cccc00004400000044011110000111100000000000000000000111100001111000000000000000044440000444400004444000044440000440400004404000044000000440333300003333000033300000333000003333000033330000333000003330c8c80000c8c80000c8c80000c8c80000c8c80000c8c80000c0c00000c0c333300003333000000000000000000003032000030320000000000000000cccc000000000000cccc000000000000cccc000000000000cccc0000080b3110000331100003300000033000000331100003311000033000000330044440000444400004444000044440000440000004400000044000000440333300003333000030300000303000003232000032320000303000003030cccc0000cccc00000000000000000000c8c80000c8c8000000000000000222200002222000022220000222200002222000022220000202000002020
|0,5=>0x8080000080800000808000008080000080800000808000008080000080b333000033330000333200003332000000000000000000000000000000000c8c00000c8c000000880000008800000c8c00000c8c000000880000008800000000000000000000000000000003333000033330000333200003332cccc0000cccc00000808000008080000cccc0000cccc000008080000080800000000000000000000000000000003333000033330000332200003322cccc0000cccc0000cccc0000cccc0000080800000808000008080000080b333000033330000333300003333000033330000020200003333000002024444000044440000000000000000000044440000444400008888000088880000000000000003333000033330000000000000000000030300000303000000000000000008888000088880000000000000000000088880000888800000000000000033330000333300000000000000000000330000003300cc880000cc880000cccc0000cccc0000cc88000000000000cccc0000000333300003333000022220000222200003333000033330000202000002020cccc0000cccc0000cccc0000cccc0000888800008888000000000000888b31100003311000033110000331100003010000030100000301000003010
|0,6=>0xc0000000c0000000c0000000c000000080000000800000008000000080000000000000000000000000000000000000000000000022220000222200c8000000c8000000c8000000c8000000c8000000c8000000c8000000c803300000033000000220000002200000033000000330000002200000022cccc0000cccc00000000000000000000cc000000cc000000000000000000033000000330000003300000033000000330000003300000000000000000c0c00000c0c00000c0c00000c0c00000c0000000c0000000c0000000c0333300003333000000000000000000003333000033330000020200000202cccc0000cccc0000cccc0000cccc0000444400004444000044000000440010100000101000001010000010100000101000001010000000000000000cccc0000cccc0000cccc0000cccc000000000000000000000808000008081010000010100000101000001010000010000000100000001000000010000000000888800000000000088880000000000008888000000000000888b33300003333000033330000333300000000000022220000000000002222cccc000000000000cccc0000cccc0000888800000000000088880000888b33300003333000033330000333300003333000033330000333000003330
|0,7=>0x888800008888000088880000888a2330000223300002233000022330000223200002232000022320000223200000000000000000000000000000000cc440000cc44000000000000000303000003030000033330000333300003030000030300000333000003330cccc0000cccc0000cccc0000cccc00000000000000000000888800008888303000003030000000000000000000003030000030300000000000000000000000000000000444400004444000000000000000000004444000000000000000000000000000000000000000020200000202000002020000020244440000444400004444000044440000444400000000000044440000000222200002222000000000000000000002222000033330000000000000000cccc0000cccc00000c0c00000c0c0000cccc0000cccc000008080000080800000000000000033330000333300000000000000000000333000003330c0c80000c0c80000c0c80000c0c80000c0c80000c0c80000c0c80000c0c80000000000000000000000000000000223300002233000022220000222200cc000000cc0000000000000000000000cc000000cc000000000000000303000003232000030300000323200003030000032320000303000003232
|0,8=>0xcccc000000000000cccc000000000000cccc000000cc0000cccc000000033330000333300003333000033330000333300003333000030300000303000000000000000000000000000000000000000000000000008080000080b33300000000000033330000020200003333000000000000333300000202cccc0000cccc00000000000000000000cccc0000cccc0000c8c80000c8cb3330000333300000032000000320000333300003333000000320000003280800000808000008888000088880000808000008080000088880000888a22200002222000022220000222200003333000033330000222200002222cccc0000cccc00004444000044440000cccc0000cccc00004444000000033320000333200003332000033320000333200003332000033320000333244440000444400004444000044440000404000004040000040400000404000000003333000000000000222200000000000033330000000000002222cccc0000cccc0000cccc0000cccc000000000000cccc000000000000888b333000033330000000000000000000022220000222200000000000000000000000000000000cccc0000000000004444000000000000cccc0000000330000003300000033000000330000003311000033110000330000003300
|0,9=>0xcccc0000cccc00008888000088880000cccc00000000000088880000000333300003333000033330000333300000000000033330000000000000000cccc0000cccc0000cccc0000cccc000088880000cccc000088880000888b33300003333000033330000333300002233000022330000222200002222cccc0000cccc0000cccc0000cccc0000cc440000cc440000cc000000cc0333300003333000033330000333300000033000000330000002200000022cc880000cc880000cc000000cc000000cc880000cc880000cc000000cc033330000333300003333000033330000111100001111000000000000000000000000000000000000000000000000c8c80000c8c80000c8c80000c8c80000000333300000000000000000000000000003333000000000000000088880000cccc0000888800008888000088880000cccc000088880000888b32200003322000033220000332200003333000033330000332200003322cc440000cc440000cc440000cc440000cc440000cc440000cc000000cc0333300000303000033330000030300003333000002020000333300000202cccc0000cccc0000cccc0000cccc000000cc000000cc000000000000000000000000000000000000000000000000033000000330000000000000000
|0,10=>0x8c8c00008c8c00008888000088891110000111100001111000011110000111100001111000011110000000000000000000000000000000000000000cccc0000cccc0000cc000000cc03131000000000000313100000000000031310000000000003131000000008888000088880000000000000000000088cc000088cc000000000000000223300002233000022220000222200002233000022330000222200002222cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000c8c80000c8c911100001111000033330000333300001111000000000000333300000000cccc000044440000cccc000044440000cccc000044440000cccc0000000313100003131000031310000313100003131000031310000000000000000cccc0000cccc0000cccc0000cccc0000cc0c0000cc0c0000cc000000cc0003300000033000000330000003300000022000000220000002200000022000000000000000000000000000000000000000000000000c8c80000c8cb33300003333000022220000222200003322000033220000222200002222c4c40000c4c40000c4c00000c4c00000c4c40000c4c40000c4c00000c4c333300000000000033330000000000003300000000000000333300000000
|0,11=>0x808000008080000000000000000000008080000080b33300003333000033330000333300003330000033300000333000003330c0c00000c0c00000cccc0000cccc00008080000080800000888800008888000000000000000333300003333000000000000000000003322000033228c8c00008c8c000088880000888800008c8c00008c8c00008888000088880220000002200000022000000220000333300003333000000220000002288880000888800008888000088880000888800008888000000000000000110000001100000011000000110000001100000011000000330000003300c0cc0000c0cc0000c0cc0000c0cc0000c0cc0000c0cc0000c0c00000c0c10100000101000003030000030300000101000001010000030300000303000cc000000cc000000cc000000cc000000c0000000c0000000c0000000c333300003333000000330000003300003333000033330000003000000030cccc0000cccc00000000000000000000cccc0000000000000000000000033330000333300002222000022220000333300002222000022220000222244440000444400004444000044440000444400004444000000000000000330000003300000033330000333300003300000033000000333000003330
|0,12=>0xc0c00000c0c000008080000080b333000033330000333300000000000033330000333300003333000000000000000000000000cccc0000cccc0000000000000000000088880000888800000000000000000000000000000003333000033330000000000000000c0c00000c0c00000c0c00000c0c00000c8c80000c8c80000c8c80000c8ca22200002222000033330000333300002222000022220000323200003232cc0c0000cc0c0000cc000000cc000000cc0c0000cc0c0000cc000000cc000000000000000000000000000000000333300003333000000000000222200000000cccc000000000000cccc000000000000cccc000000000000888b333000033330000333300003333000003030000030300000300000003008888000088880000cccc0000cccc00008888000088880000cccc0000888b33300000000000033330000000000003333000033330000333300002222cccc0000cccc00004444000044440000c0c00000c0c0000040400000404333300003333000033320000333200003333000033330000333200003332c4c40000c4c40000c4c40000c4c40000c4c40000c4c40000c0c00000c0c333300003333000030320000303200003333000033330000303200003032
|0,13=>0xccc0000000000000ccc0000000000000ccc0000000000000ccc00000000333300003333000033330000333300003330000000000000333000000000cccc0000cccc0000cccc0000cccc0000008800000088000000880000008800000003330000000000000333000000000000033300000000000003330cccc0000cccc0000cccc0000cccc00000c0c00000c0c00000000000000022220000222200003333000033330000222200000000000033330000000000cc000000cc000000c8000000c8000000cc000000cc000000c8000000cb3330000333300003333000033330000333300000033000033330000000080800000808000008080000080800000808000008080000088880000888b03000000000000030300000000000003131000000000000313100000000cccc0000cccc00000000000000000000cc880000cc8800000000000000033000000330000003333000033330000330000000000000033330000000000440000004400000000000000000000004400000044000000000000000000000000000000033320000333200000000000000000000333200003332cccc0000cccc0000cccc0000cccc0000cc440000cc44000000000000000232300002323000023230000232300002323000023230000222200002222
|0,14=>0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c0000000333300000000000033330000000000003131000000000000313100000000cc0c0000cc0c0000cc0c0000cc0c0000cc0c0000cc0c0000cc000000cc0000300000003000000020000000200000003000000030000000200000002cccc0000cccc00000000000000000000cccc0000cccc000088880000888b30000003300000033000000330000003333000033330000332200003322cccc0000cccc0000cccc000000000000cccc000088880000cccc0000000030300000303000000000000000000000303000003030000020200000202cccc000000000000cccc000000000000cccc000008080000cccc000008080330000003300000033000000330000003200000032000000320000003288880000cccc000088880000cccc000088880000cccc00008888000088891110000111100000000000000000000111100003333000000000000000000440000004400000044000000440000004000000040000000400000004333300003333000033330000333300003322000033220000332200003322cccc0000cccc0000cccc0000cccc00008c8c00008c8c000088880000888802300000023000000220000002200000023000000230000002200000022
|0,15=>0xcccc0000cccc0000cccc0000cccc00004444000000000000cccc000000000000000000000000000000000000000333200003332000033320000333200cc000000cc000000cc000000cc000000cc000000cc000000c0000000c3333000033330000333300003333000033330000333300003333000022220000000000000000cc000000cc0000004400000044000000cc000000cc033330000333300003333000033330000333300002222000033330000222200cc000000cc000000cc000000cc000000cc00000088000000cc00000088011000000110000001100000011000000110000001100000000000000008888000088880000cccc0000cccc00008888000088880000cc880000cc8b31100003311000000000000000000003311000033110000000000000000000000000000000000000000000000000c0c00000c0c00000c0000000c0030300000303000003030000030300000303000003030000020200000202cc0c0000cc0c0000cc080000cc080000cc0c0000cc0c0000cc080000cc0b3330000020200003333000002020000333300000202000033330000020200000000000000004444000044440000000000000000000044000000440333300003333000033330000333300003333000033330000333300000000
|1,0=>0xcccc0000cccc0000000000000000000044440000444400000000000000033330000003300003333000000000000333300000033000033330000000000000000cccc000000000000cccc0000000000008888000000000000888911100001111000033330000333300000000000000000000000000000000c8c80000c8c80000c0c00000c0c00000c8c80000c8c80000c0c00000c0c0000000000000000000000000000000011110000111100000000000000004400000044000000cc000000cc0000004400000044000000cc000000cc0000000000000000000000000000000003333000000000000333300000000cc00000000000000cc000000cc000000cc00000000000000cc000000cc0303000003030000030300000303000003333000033330000333000003330000000000000000000c8000000c80000000000000000000000c8000000cb3330000333300003333000022220000333300003333000033330000222200000000000000000000000000000000cccc0000cccc0000cccc0000888800000000000000000000000000000000000000033330000000000002222cccc0000cccc0000cccc0000cccc000000000000ccc0000000000000ccc111100000000000033330000000000001111000000000000333300000000
|1,1=>0x333300003030000033330000303000003333000030300000333300003030cccc000088880000cccc000000000000cccc000088880000cccc0000000333300003300000033330000330000003333000033000000333300003300
|_,_=>0
def sP:Nat→Nat
|0=>0x130141203038284a05018904607050140803038842a11048400607100140803038383e040181c0c1d000101810010180a1c0181c1405088243610038381404018680e19088100e0a0c01422040181c2e150882406070b0541203038541a140181c1c0d0204c0e0f000101812070440810038381e090181c1c0d02030160a000240602008140808038180a04018080200
|1=>0x801c14050200c0e06028dc6c03038280a111a80c0e0a0284408031a01c1c000480c660a028440803038381a1f0200c0e0e0684412031901c14050200c14310284412300801c14050200c0e2f0284412100181c5c050480c0e0a1681412030382858050200c0e2b028440803038a80a110200c142902844121003828320502030500a0284412031388c14050480c0e0a
|2=>0x28440803038288c110206c200707018080c0d8081c112280c0e0a028441203038383e042201c860508810064205000080c0182882110200c04400284408031401c0c050200c0e0e1f8000803038382c1f0200c0e061f00008031e88c14000204c780703014121b0181c2c0a0200c760a0284408031d01c14110200c720a1b8441203038382c220200c2407070441238
|3=>0xd81c0c000200c04562a84408132a01c0c052980c0e0a028440803011480a110480c0e0a28814080c280280a110200c0e4f028440803038541a1102030240a028441203038289c050200c0e0e268449803038280a110486c20070512812030385814050200c0e4b250440810038281e050200c0e490284408480188c14000200c0e0a008000803038b80a110200c8e0a
|4=>0x200c0e0a3081422043000c0e0a02844120303858be050200c0e0a02978080c051740a110200c0e0e03000085c0181c1405020c0060703000080303818b6000496806070501412030385422040181c1c590002406070705422140181c1c1f2c00c460705014080303838ae110200c0e0e108440803038582a110206c0e0a2704408030385c1c1f0200c0e0e078440813
|5=>0x1f01422090188c0e0e05014080303818da05088101807051b00a110206c0e0a35844080303838146a0881006070506400110206c0e0a3481422040181c146802844080303828ce05088109003010280a11020400607070180a040181c140533044080c018081c05088100607051940a110200c04390500022040181c146402844081b0181c2c0a088100607051880005
|6=>0x284408740181c14050881006070516c00110200ce6070301422040181ce40a0284408030101c3205088101803010180a110200c0e0e031c42204018e40e060500008031a01c1c050882436030383814110200c0e0e0f824261b038280a110200ce00a000142209098400e0a028100607051bc0a110480c0e0e1104408032381c1405088100602039b80a110200c040e
|7=>0x10e4fe050881006073f0280a110200c6807050000a040181c0c5f0001408031d08c0e0a0881060030382800110484006070501494040181c14053e844087c0181c14050881078030382894110200c0e0e0f844080303828f60002810060203828821102030200a029e822040181c14790284408480801c1405088100607071e00a110480c0e0a029d822040181c1475
|8=>0x284408030383904110200c7a070500022040181c148a028440803038191205088100607440280a110480c0e0a438142204430400e0a028440803038187c050881006070702800110200c0e200001422090181c1419028440803038290a0002810063d118280a110200c0e0e0302800040181c14830284408030901c140508a0406070501422044000c0e0a028440803
|9=>0x284408030382934050881006420501422094c81c14050881036030382930110200c0e16030280a041e00c0e0a0284408034b81c1c050881006074a8180a110225006070501422044980c0e0a028452403038280a110480c0e0a2d81422040800c0e0a02a44080c038283a0508a3c06070501422040181c148d028451803038280a110200d16070501422040181ca00a
|10=>0x4840060705015200401a8c0e0a02844080303a8814050881006a1038280a115000c0e0a02844080c018290a050881006070702922110200c0e2e000142204018e4460a000100607050fc00050200c0e0a4f81422040181c1400410246003038280a110206c20070512822040181d3a0a02844080303a70140508810061a118280a110226c06070501422040600c680a
|11=>0x606c040a02844080303abc1405088100607052b80a110200c74070504408135681c14050880c48070501422040181c1405558440803038289c05088240607050143e04018f40e7f02844080303aa814000881006a9038280a110206c06072b02822090181c1c0a028455003038280a115381006070501422040181c14055304408a50181c1405088101807052900a11
|12=>0x2844080c01a5c14050881006b7038280a110203020020501422040600c460a000140803038183c000281036030385c14110480c0e0a36014220901ad81405088100607052d00a110200c4e070301422040600c14003d044081b0188c0e0a0001090030382800110200c0e170708822040d8400e0605014120303ac81405088103603038296211022c00607050142204
|13=>0x108c1c050881070030383814110200c0e0a618142204098e00e0a0284408c20181c14050881006c1038280a110200c0e0e0b028000401b000e0a02844081b038288605088240607052fc0a110200c040a1f01422040188c0e0a2084408be018081405088100607052f40a11022f006070501422040181d760a000440803038283a00088100607052e80a11022e00e0a
|14=>0x38280a110200c0e0a02b4422040181da00a02844120303828f2050881006470501422040181c14cf028459c040181c14cd088100607051b198110200d962305014220401b280e0a0284408c90801c14050881006020383800110200c0e15088100607053200a110200c0e0a6381422040181c14c6028458a040181c140508b100803038280a110200c0e0e0a8440803
|15=>0xb0280a09018d0460705014060705370000508810180305015b61104b6806070501422090200c0e16050141203038382c0a028100607053640a116c00c0e0a02844080303829ae050880dac070501422040181c14056a8441203038283a050881006075d9fc0a110216806070501422d40181c140508810060705001a6110200c0e2e02844080303828ba0508811a403
|16=>0x88100607728280a110486c06070512822090181c140572044080303829c605088106007051b00a110200c0e17050142209710400607050140803010e40c05088100602470280a110206c06070302800040181c140f02844080303b841405088100607053800a110200c460a3681422de0181c14050200c0e062a8000a040181c14cd4b044080303829ba00028240607
|17=>0x200c14ef0001422140181c140508810060203bac0a110200c0e162f81422037708c0e0a02844080c050780a7a088243610038280a047680c0e0a0284412a80181c14050881006072181494110200c0e0a7601422040181dd60a0004408ea0181c140508ba406070501422040181c14e8028441203038293e0508b7806070501422e70188c0e0a02844080303829cc05
|18=>0x501422090181c14057b04408031c8290a050880c0e0e053700a110200c0e0a7a81422040181c14f4028440803038284005088100628038280a11023cc06070501422090181c1c5f02845e403038280005088100607050f800110211020070501422040181c1459000140803398e41405088100607053c40a11020f00607100142204098f00e0a028442803038280a1f
|19=>0x50143e048300c0e0a0284408030382a0a050881006070b97c0a118181006070501422040181c15020284412031381c14050880c0e0a8081422ff0181c140508811fc03038280a110200c0e0e03000080303829fa0508bf00803038280a110200c0e170b0280a047d81c1405088100e0a7c81422040181c14057c044081b0181c4005088107803038b80a11023dc0607
|20=>0x88120e070501422df0181c1405088242603038280a110206c0607050000a1102030060a029e822042400c0e0a0284408130181c14053d044080303828d2050881006390382800110200c72230501422090188c0e0a0281006070501504110200c0eaa0501422040181c14bf0284408030d01c14050881006070705844110206c06020383822090181caa4a088100607
|21=>0x1a08c0e0a0284408036581c1405088100607052900a110200c0e0e0b0280a11020f006070501422048481c1405088240607050780a110200c0e0a420142204018080e0e02844080c0181c1400028440803038381484028440803038283c053d044080303a2014050881006070702800110206c0623038280a110200c0e0a001c42308018080e0a028440803038283a05
|22=>0x8c100803038280a110200c0e0a3101422040181c14770284608040181c1c0a028440803380280a11020400639038280a110480c0e0e0501422040181c1c7f0284408300d80c0e0a0284412040181c1c0a028441203038280a71088117c031181c140508811c4100181c1405088100602038180a110200c4607051e00a110200c0e160501422040d80c0e0a250440803
|23=>0x1422fa0200c0e0a02844080c0181c1c0a0284408034701c1400028440803038280af6088240607051540a110200c0e0a3d81422040800c0e060501408100181c1c0a0284408033981c1405088101803010280a110200c0e0e2f81422040181c2e0a0001422040d8400e0a02844080303828da05088100607030280a7a088100602038280005088103603038381405
|24=>0x1c2c140508810060705000f4110200c0e0a6681422040181d2a0a0284408030381814052504408480d80c0e0a028440803038280b0a0881006070517c0005088100634038181405088100607050f80a11022f806070501422040181c14630001422040181c144302844080303838143e028440803038290a05088100607051e00a110203020070501422f00200c0e0a
|25=>0x181c14050881006072a92822040181c150d02844120303828ee0508810060705016180401a380e0a0284408031381c140508810781b0181c140508c200607070280a110204c0607050000a110200c0e170501422040181c2e0e05014220401a5c0e0a028459c040181c0c0a0284406ac038280a110200c0e0a1f8142204018e40e0a3f81422040181c0c0a02c282204
|26=>0x8c4406070501422040181c14054884620040181c1400028440803038280b0f0881036030382998110200c0e06050000a040986c0e0a0284408030383814000284408030383844118700c0e0a028440607053700a110204c0639038280a1102040060705014f4110200c0e0a02b6c22090181c1405598440803038280a6b088243603038280a110200c0e0a001282300
|27=>0x88100607050152c116701006070501422040600c0e0a0284408100181c1405088103603038280a110480c0e0a0284412040181c140508810060705014f4110200c0e0a2a81422040181c14050f8440803038280a1f0480c0e0a0288822040181c1c0a0284408300181c14050881060030383814050881036030101c1405088100607050780acc088102003038280a4a
|28=>0x803038280a110200c0e0a02844080303838140508c480803038280a110204c06070501422040181c140002844080303828be050881006070501444110200c0e0a3f81423080181c1405
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32502d50285023501e50195014500f500a500550005
|5,0=>0x1ae61a861a2619c61966190618a6184617e61786172616c61666161515b61565150614a6144613e61386132612c61266120611a6114610e6108610260fc60f660f060ea60e460de60d860d260cc60c660c060ba60b460ae60a860a2609c60966090608a6084607e60786072606c60666061505b6055604f60496043603d60376
|5,1=>0x26c62666260625a6254624e62486242623d52376231622c52266220621a6214620e6208620261fc61f661f061ea61e461de61d861d261cc61c661c061ba61b46
|6,0=>0x424741d7416740f7409640273fb73f473ed73e673df73d873d173ca73c373bc73b663af73a873a1739a7393738c7385737e7377737073697362735b7354734d7346733f73387333532c7325731f63187312630b730472fd72f672ef72e872e262db72d472cd72c672bf72b872b172aa72a3729c7295728e72877280727972727
|6,1=>0x5d965d275cb75c565be75b775b075a975a2759c6595758e7587758075797572756b7564755e6557755075497543653c7535752f65287521751a7513750c750574fe74f774f164eb64e474dd74d674cf74c874c174ba74b464ad74a6749f74996492748c6485747e74786471746a7463745c7455744e7447744074397432742b7
|6,2=>0x790778a6783777c7775776e77677761675a7753774c7745773e77377730772b5724771d7716770f7708770266fb76f476ed76e676df76d876d176ca76c376bc76b576ae76a776a076997692768b7684767e6677767076697662765b7654764d7647664076397632762b7624761d7616760f7608760175fa75f375ec75e665df7
|6,3=>0x945793e7937793079297922791b7914790d7906790068f978f368ec78e578de78d778d168ca78c378bc78b578ae78a778a1689a7893788d6886787f78787871786a7863785c7855784e7847784078397832782b7824781d78185811780a780377fd67f677ef77e877e177da77d377cc77c667bf77b967b277ab77a4779d77976
|6,4=>0xa107a097a0369fd69f679ef79e879e179da79d379cd69c769c079ba69b379ac79a5799f69996992798b7984797d7976796f79687961795a7953794c7
|7,0=>0xbdf7bd87bd17bca7bc28bbb7bb47bad7ba58b9e7b977b8f8b878b7f8b787b717b6a7b628b5c6b548b4d7b467b3e8b368b2f7b278b1f8b187b108b097b027afa8af37aec7ae48add7ad76ad07ac97ac27aba8ab28aaa8aa37a9c7a948a8d7a867a7f7a796a736a6c7a648a5d7a567a4e8a477a407a397a336a2c7a257a1e7a177
|7,1=>0xdad7da67d9f7d978d8f8d878d7f8d796d727d6a8d637d5c7d557d4e7d468d406d3a6d346d2c8d248d1d7d167d0f7d087d017cfb6cf56cee7ce77ce16cda7cd37ccb8cc47cbc8cb57cad8ca67c9e8c986c917c898c818c7b6c747c6d7c667c5e8c568c4f7c478c3f8c387c317c298c227c1a8c137c0c7c057bfd8bf67bee8be68
|7,2=>0xdba7db46
|8,0=>0xe366e2f7e287e217e1a7e137e0c7e057dff6df87df17dea7de37ddc7dd66dcf7dc87dc17
|9,0=>0xe3c6
|_,_=>0
def wAt:=mkWire dB 275 238 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x708b05014050150708b0501505014050150207d11045050140708b050140501505014050150d818028450708b050140501508038028290b88b05014050150d81801815018e5028450381511838050150181502829038290204511045050140501501040038291c8290381508015010000100003829050450707f05015050140b08b05014050150d829018150708b050140501502845028790182a0382905045
|1=>0x483b05015018450d81d018153b8160482b2f8150382a038790182a0d82b01815038290504505045050450204505015050151104505014020450398d0202a0184502045018290504505015020450501405003028450282905015020450100f038290183a028290181508014018450d82b01815018450d82b018150d81d028290382903815070470501502845318450284502955028450282a018390282902045
|2=>0x4b02905045020160500202845020fd0381a050450297d0382a480450801601845028790182a02241080164702a1c82a038150281805045028290383905015368150100f051eb038160100d0382902955028450282a1e02b018011182b0101503829028450501542045050150d8080220b028180504503815010451a0171182901839050150282b0204508015110450501405015028450282a1a0140104503816
|3=>0x2845118171a017038290d847560450217f0382a218160802b080380282911045020450501411817038452a8150282a020450488b0204505014050022f802028450181a05045080160d82b0224308016018451182b038451e0280180103845028450381505045048380501503014050450981501829018454f0294b0450101703829038190504503a09028180504501889020450282825045050160282901047
|4=>0xd845018150483b0501503ae505000028450281a050451182a03845019e9038160708b05014050150708b0501405015028470384501829028472402907047050151c82a028291a0141182906045051e903816028790182a01ae7050000104703829039a902845028450284507045050150183a028290388b020450501402ad51180f039550282a028450181506015028450181d0501405015052cd048140002b
|5=>0x2001048890204505014029fd05047021e31182a0181502045018450488b0501405015029b90500302845022090281804838050156f845020300181d021e11182a02045050160282902045050450d81805045018150100f03845038296f8450203005045028450282a028450704705015020320181d3d04503816070470501505015022453884501816020ff0381a05045028790182a049c702045018161e028
|6=>0x504538829018161c82a0381501017038290501405015018150282903829050160282a0204505045028450d8470d80a018158204705015020320181d800450208b0501443047050450284505015070450501501a0b028187d00f0201905045028451e02b0d845020320d88f038450104003829018f9050150217d0382a0383a0501501929050162f845028450182a038150d845028450207d11045050147801f
|7=>0x1182a03845070470501505016018151182903845039fd050470181a0504507047050150d845018150188b028280182a020450203a050150282903829028450181d050150182a0381666029028470284505015038450181502845018160382902047028790182a01a5b02016020300181d02045018290284501815038160181d0d81d0181503816018290801f0184502845038150384503815020450384502818
|8=>0x1182a03845018450380d020010284502019050450501503801028450287b0182a0282a020452a8450282a050450184502829038790182a0380d038290382a02829050010284501845018150100f038290504503816028450382905015018150203905015318450202a0482b02045050150398d0202a0184503815020450501505015050470d829018150501502045018161180d0384508029018450504503829
|9=>0x5014050160282a0201a050450482b0204511046050141c84503815039550282a0d8450181505015020470284501829070450501505015010470382905045020150217f0382a0381a0504503815050470281b05045038890501402845038160281a05045052590201605045050160d81d018150281b05045028450382a03819050450383a05015060450181d028450202a0802b018450383a050151182b03845
|10=>0x50470204702016020150181d01845018150204502045038160282a110450501411045050140204505014050150d829018150282903829018150182a02847050160184502089050143884501816028450200d3f8160504702847018150504502845018290181502845050150501405015021c501816020320181d038150182903816018453d0450381604814020450801401845020450181502845050160208b
|11=>0x50150201d01829028450382a05014
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x25200002230808000000000000001d300001940000000000000005c800000000000548141000000000001310000000000011200000000404000034c0a300000000208000000000000000000000000000000000000000000000014c0000104022000800000000000000000
|5,1=>0x433000041200000000f500000e8c36400000000ccc00000003120c042f100000000000000000000000002c300002a209cc000
|6,0=>0x26489722548941244c000240400023c400023488b222480000000881214c83220488011f887b3000079200000001dc875200007321c480001c046f11b486a31a44672190c631180c00017885d116c859215c85430000522144400013c84e1000000013084b1000000012484720000461
|6,1=>0x3e0cf623d08f1300000000000ef23b0ce933a04e620000e4238c40000000e2137ccdd20000db2360cd713548d323448d0133880003308000328800031ccc433088c110000c012f4c0002ec8b832d88b332c48af22b84ac200000002a4ca722948a3200000002848000278c9c200009b1
|6,2=>0x13e3000000000000004f0939300013720001352000133200013030000000000000000012d300012c14ac52924a04000498800000012514905222484400000011f2474800046c919245c8000458515144c9112438d0c24288000420905340c80004048ff23f8400000000003f08fb1
|6,3=>0x640800063898c2628988261880006145841604d7f25f0d7a200017820001753000173200017215bcc0005b480005ac968359880000001642000000058c400058856110000000578c00000015b35649563000155154c800054494f200014d25304000524c000518c00051080000001413
|6,4=>0x6dc9b436c4daf26b85ac20001aa200000006a09a536905a130001a0167c59d2668d99165c80000000000000196165080000001922
|7,0=>0x8cca3128bca2d28b062a28a0a262890a222880a1e2870a1a2860a162850a131844a0f2834a0b2824a081818a042808a0027f89fc27e89f827d89f427c89f027b89ec27a89e827989e5178c9e1277c9dd276c9d9275c9d5274c9d1273c9cd272c9c9271c9c5270c9c126fc9bd26ec9b92
|7,1=>0xabcaae1ab0aab1aa4aa72a94aa32a84a9f2a74a9b2a64a972a54a932a44a8f2a34a8b2a24a872a14a832a04a7f29f4a7b29e4a7729d4a7329c4a6f29b4a6b29a86682998a642988a602978a5c2968a582958a542948a502938a4c2928a482918a442908a4028f8a3c28e8a3828dc6352
|7,2=>0xaccab12
|8,0=>0x2c51b106c31b086c11b006bf1af86bd1af06bb1ae86b91ae06b71ad86b51
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0x408000100000022000008200001e400007500001c400007000001680000520000130000041000010000003000000b0000025000007400001a0000060000011000004000000c0000028000008000001c0000060000014000004000000c0000020000004000000
|1=>0x20600008100002020000805000200c000802000200000079f0001e6c00071f0001c6c000713000164c00050f00014380005020001200000407000101000040200010040004000000e7c00031f0000c0c00028000008080002000000630000113000043800010b
|2=>0x8020002004000800c0020020007c7c001d1f000746c001d13000657c0019160004c08001300000440000100e0004008000f9f0003c7c000f1b0003c5c000e800003874000d1f000344c000d0e0003430000c820003048000c1100030080009120002208000819
|3=>0x420180106120041208010193004020800d59b003546c00a8310024c00009102002365c008d1f002345c00891f002245c008913002200c008400002005800501f001201c004200001065c004001001000000281100080c00020280008080002015000804400200a
|4=>0x18c44c06301a018126806011b018000004df130136c5c04d7530134c4c04991f011c44c04613f010e46c04351b010d44c041f170106c5c04191f010645c04055b010066c038817009847c020498008000001891f006244c0148070043218010c820043028010c02
|5=>0x9000081189170423d7c108f530421408108373041345c1007370401c7c10051f040101c10015f040017410004004000dc10000003c046c0e0913032247c0c0d59030056c0b00120242048088d1d022245c08693f02080d4080c180202048080418020006006603b
|6=>0x8504c5d0010123001204c00083241345490451720195f480613f201164c8041172009c5c80071f200000442613f10880c4414117104001c408803101c45c404807101045c4004011000200309102093544c245513
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x2c0002000021000223000002000002080800000000000000020002020000000002000306000000001900300000000002000000020800000004000000020000040002020000020000000000000000000000000002002602120000000000
|6,0=>0x321609470000000b2c21b00100149b000063420b00026b04027f02391e0002000b006f310b1c00043a000b03023e0102b06a00003a020102000060002c020004022c530a1f002a00040001020d000008382c01651f5d00bf000002020001180004040d2908029e6331000101050201a300025e00021100001a2400000b6e0063
|6,1=>0x1000202022d2d000808470252010001009f001f00632c0002001fb46800000b0000a1001d04000017000061b343002f1ec3020b001e02006d00270002000056000e00000000027e001e002b005c002800000000003600082a3d63003a008767cd01640000020200020b0b5f102a0b022001020001030200250b631500000208
|6,2=>0x20c484c6301005300005121638200b27b021f130b00000000080b000009
|7,0=>0x5a49aba10f453f5b86d84fa782ac8036966c0f66858d7293834a4f97c04ecaceaabc0e7c7bd076b6692e414fc8339046a571b5d6b9ccbb9c3cc536a0c2981bc94d59379d0dcfd34b7daed23b07a4977ac17779625881a2558ecb88d1c449a8d7ce8b43af4d919ad5b154447380628ab83457b492a978a6408984c6c77574b7d4
|7,1=>0x504f
|8,0=>0x49bdd98cbe364f35ba8f99949cad9597704f
|9,0=>0x22
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 26 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_233 7 roots_233 ops++addP pm 1 dom_109 7 roots_109 ops++addP pm 2 dom_169 5 roots_169 ops++addP pm 3 dom_228 5 roots_228 ops++addP pm 4 dom_229 7 roots_229 ops++addP pm 5 dom_193 4 roots_193 ops++addP pm 6 dom_196 4 roots_196 ops++addP pm 7 dom_108 4 roots_108 ops++addP pm 8 dom_205 7 roots_205 ops++addP pm 9 dom_204 5 roots_204 ops++addP pm 10 dom_236 6 roots_236 ops++addP pm 11 dom_173 6 roots_173 ops++addP pm 12 dzo_205_32 6 roots_205 ops++addP pm 13 dzo_193_32 4 roots_193 ops++addP pm 14 dzo_201_32 5 roots_201 ops++addP pm 15 dom_141 5 roots_141 ops++addP pm 16 dom_45 4 roots_45 ops++addP pm 17 dom_101 4 roots_101 ops++addP pm 18 dzo_197_32 5 roots_197 ops++addP pm 19 dom_165 4 roots_165 ops++addP pm 20 dom_137 4 roots_137 ops++addP pm 21 dom_77 4 roots_77 ops++addP pm 22 dom_105 4 roots_105 ops++addP pm 23 dom_232 4 roots_232 ops++addP pm 24 dom_197 5 roots_197 ops++addP pm 25 dom_201 5 roots_201 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_237 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_205_32_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_193_32_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_201_32_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_197_32_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_201 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_233 7 s (0,roots_233.map (·&&&dom_233)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_237 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_233 h
def symsG:List (List (Nat×Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_237==dom_237)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_237 gM v ys):RunD true dom_237 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_237 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
namespace S_238
def pG:List (Nat×Nat):=[(2,34),(2,66),(4,36),(4,68),(4,132),(6,38),(6,70),(6,134),(8,40),(8,136),(10,42),(10,74),(10,138),(12,44),(12,76),(12,140),(14,46),(14,78),(14,142),(32,34),(32,36),(32,40),(64,66),(64,68),(64,192),(72,74),(72,76),(72,104),(72,200),(96,98),(96,100),(96,104),(96,224),(128,132),(128,136),(128,192),(130,134),(130,138),(130,162),(130,194),(160,162),(160,164),(160,168),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_238.map (·&&&dom_238)
def gM:=goal_238&&&dom_238
def NN:Nat→Nat
|4=>5
|5=>16
|6=>36
|7=>9
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xace8caaf2fa317b4fa9c0a7e9
|5,0=>0xf61cedc348d212ec841da802b9492484ed374d3e645ed62db64b03f44fdb392d52d4101dbdd16a1a
|6,0=>0xf37fae9ae9bb5abb9bc6b1706a7c83a7b3ba5010a2f2397ac49640a9463c93c6a92e659268a921cd8a4e9833bd78ee5672f5645ed5a52a4f456429cc3effa3cb3c3c2a230ec0260dc1b470195501655f1006a0eb4d0c68e08039
|7,0=>0x8c5978c03780e15647545ee893cb3c3708c354383155e
|8,0=>0x1305b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaa0000aaaa0000aaaa0000aaaa0000000000000000444400004444000044440000444400004444000044440000444400000002a8000002a8000002a8000002a8000002a8000002aaa80002a8000002a80555500005555000000000000000000005555000055550000000000000000aaaa0000aaaa0000aaaa0000aaaa00000000000000000000000000000000000000000000000155540001555400015554000155540001555400000002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80000000555500000000000055550000000000005555000000000000555500000000aaaa0000aaaa0000a0a00000a0a00000a0a00000a0a00000a0a00000a0a111100001111000011110000111100001111000011110000111100001111000000002aaa8000000000002aaa8000000000002aaa8000000000000000555500005555000055550000000000005555000055550000555500000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa0000000154000001540000015400000154000001540000015400000154000001540282800002828000028280000282800002828000028280000282800002828555500005555000044440000444400004444000044440000444400004444
|0,1=>0xaaaa0000000000000000015400000154000001540000015400000154000001540000000000000002aaa8000000000002aaa80002aaa80000000000000000000000000000000111100001111000011110000111100000000000000000000000000000000aaaa000022220000aaaa000022220000aaaa000000000000aaaa0000000000000001555400000000000155540000000000000000000000000000000222200002aaa8000222200002aaa80002222000022220000222200002222555500005555000055000000550000005500000055000000550000005500aaaa0000aaaa00000000000000000000aaaa0000000000000000000000000000000000000000000000000000000155540001555400015554000000000000000000000002aaa80002aaa8000000000000000000000000000000055550000555500005555000000000000555500000000000055550000000000aa00000000000000aa000000aa000000aa00000000000000aa00000000141400001414000014140000141400001414000014140000141400000002aaa80002aaa80002aaa80002aaa80002aaa80002aaa8000000000000000555500005555000000000000000000000000000000000000000000000000
|0,2=>0xaaaa0000aaaa000000000000aaaa0000aaaa0000aaaa0000000000000000000000000000000000000000000000004444000044440000000000000002aaa8000000000002aaa80002aaa80002aaa8000000000002aaa80000000000000000000000055550000555500000000000000000000550000005500aaaa0000aaaa00002222000022220000aaaa0000aaaa00000000000000000000000155540000000000000000000000000001555400000000000000000000000000000002aaa80002aaa800000000000000000002aaa80000000555500005555000055550000555500005555000055550000550000005500aaaa0000aaaa00008888000088880000aaaa0000aaaa00008888000088895554000155540001555400015554000111100001111000011110000111100000000000000002a8000002a8000002a8000002a8000002a8000002a8055550000555500005500000055000000555500005555000055000000550000000000000000000000000000000000aaaa0000aaaa0000000000000000015400000154000000000000000000000154000001540000000000000002a8000002a8000002aaa80002aaa80000000000000000000000000000000111100001111000011110000000000001111000011110000111100000000
|0,3=>0x88880000888800000000000000000000888800008888000000000000000005500000055000000550000005500000055000000000000005500000000aaaa0000aaaa000000aa000000aa0000aaaa0000aaaa00000000000000015554000155540001555400000000000000000000000000000000000000000000000000000002aaa8000000000002aaa8000000000002aaa80000000444400004444000044440000444400005555000055550000444400004444
|_,_=>0
def sP:Nat→Nat
|0=>0x18c2c808164c2c80871910c860118c1030811902480811901020465cb10808718b58808119520204615050204630b20204644f20119330b20219230b2020463c808138c2c320204030834118c2c40c21c62880811892021c62021c61440c2040
|1=>0x811ab30b0c808118c8c860118c2c80811aa2d52021c630b50204630b22908118c2c8a0204630b20206798c2c894118c2c808119130b2240811912c80811a354808118c2e120204645020206030b20204631f2c808118c78b20204630b75b081
|2=>0x30b2020463222c80819c630b2020463232c40c204630b24808118c2c32011b430b10808118b4080811b330b20204630bcb108118c2d420204630b20207018c2c80811af30b2020463052c808118cb8bb4808118c2c80ac04630b20204644c708
|3=>0x20204630b20204630b40808118cd4b0c808118c2c808118ca8b20206618c2c8081191
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x3929b18ccc6062d315189cc4862130f186cc30615a89583ec196
|6,0=>0xb13d6dea8f4d7a33cfde72d32795bc91e3af16787bc21e02efa779bbb59ccee066d334dd98ec575fb2e1d62eab6523a79930c917453a0dcfac776
|7,0=>0x1a17cd3e4df18f857bf3dddee0f697
|8,0=>0x1a86
|_,_=>0
def wAt:=mkWire dB 54 239 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x30b063220b483218b4c2d08c86312cc833120b430b20b4b30210cc2c68c4c2e30bc2412cc084130b0333090cb302cc4c2e2cca22e30b0c2d106c8310cc887118b866920b914330b0c2d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xc0000000
|6,0=>0x1f2749c10000068800001910000060400000005c552000004c92100000408003c4d2304a2208710000014832
|7,0=>0x291a0671986519063188611
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xeb5eadce5c6d73d53d4f54ed43d2001040c10c004003002402102001a01900c009008002001000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x10000000000000008000
|6,0=>0x6b9480012002c0060000418070a01008de62902c00021
|7,0=>0x15c4e598db14
|8,0=>0x17
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_234 7 roots_234 ops++addP pm 1 dom_170 4 roots_170 ops++addP pm 2 dom_230 6 roots_230 ops++addP pm 3 dom_174 5 roots_174 ops++addP pm 4 dom_110 5 roots_110 ops++addP pm 5 dom_206 6 roots_206 ops++addP pm 6 dom_198 5 roots_198 ops++addP pm 7 dom_204 5 roots_204 ops++addP pm 8 dom_166 4 roots_166 ops++addP pm 9 dom_108 4 roots_108 ops++addP pm 10 dom_236 6 roots_236 ops++addP pm 11 dom_228 5 roots_228 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_238 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_228 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_234 7 s (0,roots_234.map (·&&&dom_234)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_238 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_234 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_238==dom_238)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_238 gM v ys):RunD true dom_238 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_238 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
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
def dzo_211_32:=0xf000f00000000000f000f00000000000f000f00000000000f000f00000000
def gzo_211_32:=0xf000f00000000000f000e00000000000f000e00000000000e000c00000000
def gsh_211_32:=0xf000f00000000000f000e00000000000f000e00000000000e000c
theorem lowS_zo_211_32_209:Lower true dzo_211_32 roots_211 gzo_211_32 8:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_32) [(dom_211,32)] (by decide +kernel) (lower_slice_b (T:=gsh_211_32) [(0xc000c00000000000c000c00000000000c000c00000000000c000c,0,2)] (by decide +kernel) lowS_209)
namespace S_243
def pG:List (Nat×Nat):=[(1,17),(1,65),(1,129),(2,18),(2,34),(2,66),(3,19),(3,35),(3,67),(3,131),(16,17),(16,18),(16,80),(16,144),(32,34),(33,35),(33,49),(33,97),(33,161),(48,49),(48,50),(48,112),(48,176),(64,65),(64,66),(64,80),(64,192),(96,97),(96,98),(96,112),(96,224),(128,129),(128,144),(128,192),(130,131),(130,146),(130,162),(130,194),(160,161),(160,162),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_243.map (·&&&dom_243)
def gM:=goal_243&&&dom_243
def NN:Nat→Nat
|4=>3
|5=>15
|6=>35
|7=>15
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xb5552653661812b
|5,0=>0xcdbe484e367ea9d5a530492483f8e33765933c4b2975026184240ef2225d1b019111a700e87
|6,0=>0xf2c0fd91d09b7d298c929363b92e8f88033807727ab687004e6e26e6179c605385f9135e2545a5304e8544ce5c4c22f4242341ca441b973c3c63b3433931c3125b30e2c284e51f693125730f8c40eee00bce50af8d017d8
|7,0=>0x76ef16e5916b8395a65f58ef84939c3757035c4f10b080d9880ae610599d02a060161400966
|8,0=>0xbbc9817c560fc84
|9,0=>0x7a9f6
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000f000f000f000f000f000f000f000f000f000f000000000000000000000000000000000000000000000000f000a000f000a000f000a000f000af000a000f000a000f000a000f000a000f000a000f000a000f000a000f000a0000000000000000f000f000f000f0000000000000000000f0000000f0000f000f000f000f0000000000000000000f000f000f000f0000000000000000f000f000f000f000e000e000e000e000f000c000f000c000e000c000e000ca000a000a000a000a000a000a000a000a000a000a000a000a000a000a000af000f000f000f000f000f000f000f00000000000000000000000000000000f000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000f000f000f000f000a000a000a000a000f000f000f000f000a000a000a000af000a000f000a000f000a000f000a000f000a000f000a0000000000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000f000f000f000f000f0000000f0000000f000f000f000f000f0000000f0000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000cf000f000f000f000f000f000f000f000a000a000a000a000a000a000a000af000f000f000f000a000a000a000a000f0000000f0000000a0000000a0000
|0,1=>0xf0000000f0000000f0000000f0000000f0000000f0000000a0000000a000000000000000000000000000000000000f0000000f0000000a0000000a5000500050005000500050005000500050000000500000005000000050000f000f000f000f000f000f000f000f000f000a000f000a000f000a000f000a5000500050005000500050005000500050005000500050005000000050000f0000000f0000000f0000000f0000000f000f000f000f000f000a000f000a0000000000000000f000a000f000a0000000000000000000f000a000f000af000f000f000f000f000a000f000a00000000000000000000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f0000000f000000000000000000000000000000000000f000f000f000f000f0000000f0000a000a000a000a000a000a000a000a000a000a000a000a000a0000000a000000000000000000000000000000000000f000f000f000f000f000a000f000af000f000f000f000f000a000f000a000f000f000f000f000f000a000f000a5000500050005000500000005000000050005000500050005000000050000f000f000f000f000f000f000f000f000f000f000f000f000a000a000a000af0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000
|0,2=>0xf0000000f0000000a0000000a0000000f0000000f0000000a0000000a5000500050005000500050005000500050005000500050000000000000000a000a000a000a000a000a000a000a000f000f000f000f000f000a000f000af000f000f000f000f000f000f000f000f000f000f000f000f000a000f000af000f000f000f000f000f000f000f0000000000000000000f000a000f000a0000000000000000000000000000000050005000500050005000000050000
|_,_=>0
def sP:Nat→Nat
|0=>0x24b2040c708124b1100892d81174021892045900952c44020402c44d00813c45100892c43470912c44c70893c41c22523c43430813c43430912040c22402043470863c440a24b2044022403c438308620434c0812c40ca2481070861440c2040
|1=>0x40225e2c81034021922045100892c43830892c811008974f2c40d00892d81135100892c43430893c811008624b6047030892c81074021812c44d00922c811c40224f2c45d008124b10d58224b2044026cf2c811a40224b2046500812c810d302
|2=>0x2c811008124f2c41d00893cb1100892e42044cd40224b2044024492c812340224b2045d00952c81140d00892c40c70893c440225b2c811008900b2044021922c812240224b2048500892c811008980b20440225f2c810d1c224f2c43470812c4
|3=>0x1100892c810340224b2044020492c81100893cb2045c340224b2043470892c811008994b2044022522c81034020492c81074021892c81100911892c811740224b2040c70892c8103590089
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x18d8bac57628b12d88ac3f61cb0cd85ac27610b06d82ac0f6
|6,0=>0x54de98f4579fb4e1e62f2a791bc71e2af0e783bc059f4ef3776b399dbeed8768bb29d86ebc75abab9d4eea074cba49d16e8473eb9d9ce0c697
|7,0=>0x706374fb37d63e923391948c6be19efd1777b83da5ec315a7
|8,0=>0x75dfa0fc97
|9,0=>0x1de6
|_,_=>0
def wAt:=mkWire dB 38 244 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x4b49212505021248432740b53230c9502d348d02524790214c8032540b432540b5320406414124843270c9502d40149210c8502d0c8cb415c9d03d2068b252cd90252c790212d053200c9502d1cb50211c60b25408432540b412d248432540b4b413c94b211870b25408461c2c95021
|1=>0x102d2484b210c8502d25050214068b250c9d02d40b49212c950212064b250c8502d4084b410c8d02d2c849214084b2124f8b212cd502504b49210c8d02d4c8c32540b502d4084b211c60b2540853274064b250c1d02d2485046
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x798d20002c8490001021881980000000c00000
|6,0=>0x1408004d394600239c4300000209be3000ecc003926c6d09912f35a40015929200098d21222404788e11a23045c4a1922
|7,0=>0x1b8b616a2d0598b21622c0578ae15a2b0558aa1522
|8,0=>0x1c8788f01
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x9ff9bd99f87879b59724c2411df1bf1bb19f1970bf09708b08908308108004902001e01801401000c008006004002000
|1=>0xd9fd97c93
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x2060011802810c0007000
|6,0=>0x400e4c050b0003cc01500534209018010201808410204610a504
|7,0=>0x206d751225c89a45e85d65f
|8,0=>0x1459d
|9,0=>0x14
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_211 8 roots_211 ops++addP pm 1 dom_227 7 roots_227 ops++addP pm 2 dom_179 7 roots_179 ops++addP pm 3 dom_242 7 roots_242 ops++addP pm 4 dom_115 7 roots_115 ops++addP pm 5 dom_114 5 roots_114 ops++addP pm 6 dom_178 4 roots_178 ops++addP pm 7 dzo_211_32 8 roots_211 ops++addP pm 8 dom_209 7 roots_209 ops++addP pm 9 dom_226 4 roots_226 ops++addP pm 10 dom_99 4 roots_99 ops++addP pm 11 dom_51 4 roots_51 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_243 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_211_32_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_51 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_211 8 s (0,roots_211.map (·&&&dom_211)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_243 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_211 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_243==dom_243)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_243 gM v ys):RunD true dom_243 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_243 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 35 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
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
def isoMvS_159:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_159:Lower true dom_159 roots_159 goal_159 8:=lower_iso_b isoMvS_159 (by decide +kernel) lowS_95
def isoMvS_175:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_175:Lower true dom_175 roots_175 goal_175 8:=lower_iso_b isoMvS_175 (by decide +kernel) lowS_126
def isoMvS_183:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 9:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_125
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 10:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_123
def isoMvS_190:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 8:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_111
def isoMvS_222:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_207
def isoMvS_231:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_119
def isoMvS_235:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_235:Lower true dom_235 roots_235 goal_235 10:=lower_iso_b isoMvS_235 (by decide +kernel) lowS_123
def isoMvS_245:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 10:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_243
def isoMvS_246:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_237
def isoMvS_249:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_243
def isoMvS_250:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_123
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,32,36)] (by decide +kernel) lowS_123
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_slice_b [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,64,68)] (by decide +kernel) lowS_219
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,32,34)] (by decide +kernel) lowS_237
def dzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
def gzo_215_32:=0xff00ff0000000000ff00fe0000000000ff00fe0000000000fe00fc00000000
def gsh_215_32:=0xff00ff0000000000ff00fe0000000000ff00fe0000000000fe00fc
theorem lowS_zo_215_32_209:Lower true dzo_215_32 roots_215 gzo_215_32 9:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_32) [(dom_215,32)] (by decide +kernel) (lower_slice_b (T:=gsh_215_32) [(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,0,2),(0xf000f00000000000f000f00000000000f000f00000000000f000f0,0,4)] (by decide +kernel) lowS_209)
namespace S_247
def pG:List (Nat×Nat):=[(1,17),(1,65),(1,129),(2,18),(2,34),(2,66),(3,19),(3,35),(3,67),(3,131),(4,36),(4,68),(4,132),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,23),(7,39),(7,71),(7,135),(16,17),(16,18),(16,80),(16,144),(20,21),(20,22),(20,52),(20,84),(20,148),(32,34),(32,36),(33,35),(33,37),(33,49),(33,97),(33,161),(48,49),(48,50),(48,52),(48,112),(48,176),(64,65),(64,66),(64,68),(64,80),(64,192),(96,97),(96,98),(96,100),(96,112),(96,224),(128,129),(128,132),(128,144),(128,192),(130,131),(130,134),(130,146),(130,162),(130,194),(160,161),(160,162),(160,164),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_247.map (·&&&dom_247)
def gM:=goal_247&&&dom_247
def NN:Nat→Nat
|6=>7
|7=>18
|8=>18
|9=>11
|10=>4
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x8f4988754d7a62c702a86c28b4371a33511
|7,0=>0xf5415eeb62ea35ccaeadc8887c68e2c53d9c4e38be805bc74eb66d9b056dae5fcad5c5952ab750fe0a2810561e
|8,0=>0xef9e9c3e92a619b887e6785dd6f4c94ba4f43972419cd395683783936802317c42d42f2ceb6286b00acab04c36
|9,0=>0xf2e8cc6b3abed16b18ed88c4385d966f2da5d0ec30b15026a7019af
|10,0=>0xc7335931bf7fd216aad4
|11,0=>0x3ef7d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x5500550055005500000000000000000055000000550000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff00000000000000000000000000000000000055005500550055005500000055000000005500000055000000550000005500000055000000550000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00000000000000000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000000000000000000000000000000000ff00ff00ff00ff00ff000000ff0000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00000000000000000000ff00ff00ff00ff000000000000000000ff000000ff0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc55005500550055005500550055005500550055005500550055000000550000
|0,1=>0xff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff000000000000000000000000ff00ff00000000000000000000000000ff00ff00000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x718a20b107334831040e344831040e334820814831483105862ac8208106590410290658c41640e6290620b20669441620e62082a7c0cd10548499a41054f314620b0e65882a424c510408398a418820
|1=>0x334831058e335641040871a241882c71a2b1882c71a252082c818ab2082c419a41040871a2410408719a520c4161a2510590398ab10588399a41040f719a52082041a2208107718820815041a241040f
|2=>0x1058871a24105907188310588718820b10771a252082c438cb2082c820cb20820438c41040871a2b10590336220b107719b120c41638cd2ac820b1066c4820810e334a41058834441620ee344ab10588
|3=>0x18820b10e99041621d22082c438d12082c438cb2082c43a6b2082c438cd89041621d259041621c66ac820b10e32c8310588719a4
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0xa9c46e1c70ab839c0ee007
|7,0=>0x16f0af853c27e12f08f843c1fe0f0e7083441820b2e51824c1060730318
|8,0=>0x29514379e3cce65532198c4c4221110087c43be5cf0df86bc33e18f0bf8
|9,0=>0x69a33b3958c64e0e6f71738b5c58e2b53528
|10,0=>0xe2bef9f6d1ae8
|11,0=>0x1cc7
|_,_=>0
def wAt:=mkWire dB 20 248 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x6936bb5a12390235a12398bb8b94116936b38b94117026b38114390236b38b94118bb6938b94115a35a12396b36a38b941103b5a12398bb6a38b94116b36bb5a123903b6b35a12395a34396bb6a38114396938bb8b94117026b381103b6b35a1
|1=>0x8bb4114392396b35a12396b35a12392214392396938b94116a38b94116bb5a12396b38b94118bb8b94116938b94117464117116a35a12396b35a12396a38b94115a34117114398bb4116bb5a12396b35a12396b38b94115a36bb5a12394398bb
|2=>0x3213234112393212398b94113232395a12395a32395a12394394115a3239813439
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x33000000000003000000
|7,0=>0x4244023c43933633242e42a42642331f41c31841441040e20a4064
|8,0=>0x7937637337036d36a36736436135e35b35835535234f34c3493463
|9,0=>0x9028e28c28a28828628428228027e27c2
|10,0=>0x951941931921
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 12
def pmP:Nat→Nat
|0=>0x2ff8fe077fd3f44cff1fc3f0ec2f04c0901c060140400c0200400
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x100000800
|7,0=>0x223042328ca118503188c1
|8,0=>0x1ce73df24aa0c59e0c64dce
|9,0=>0x3a2da51ce73a2e
|10,0=>0x735ce
|11,0=>0xe
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_246 10 roots_246 ops++addP pm 1 dom_231 9 roots_231 ops++addP pm 2 dom_183 9 roots_183 ops++addP pm 3 dom_243 10 roots_243 ops++addP pm 4 dom_119 9 roots_119 ops++addP pm 5 dom_245 10 roots_245 ops++addP pm 6 dom_215 9 roots_215 ops++addP pm 7 dzo_215_32 9 roots_215 ops++addP pm 8 dom_167 5 roots_167 ops++addP pm 9 dom_103 5 roots_103 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_247 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_215_32_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_103 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_246 10 s (0,roots_246.map (·&&&dom_246)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_247 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_246 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff0000ffff0000ffff0000,112),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_247==dom_247)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_247 gM v ys):RunD true dom_247 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_247 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 18 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 18 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 11 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 4 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_247 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(16,17),(16,18),(16,80),(16,144),(24,25),(24,26),(24,56),(24,88),(24,152),(32,34),(32,40),(33,35),(33,41),(33,49),(33,97),(33,161),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,66),(64,80),(64,192),(72,73),(72,74),(72,88),(72,104),(72,200),(96,97),(96,98),(96,104),(96,112),(96,224),(128,129),(128,136),(128,144),(128,192),(130,131),(130,138),(130,146),(130,162),(130,194),(160,161),(160,162),(160,168),(160,176),(160,224)]
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
|0=>0xfc0
|_=>0
def pmB:Nat→Nat→Nat
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_187 10 roots_187 ops++addP pm 2 dom_249 10 roots_249 ops++addP pm 3 dom_243 10 roots_243 ops++addP pm 4 dom_235 10 roots_235 ops++addP pm 5 dom_219 10 roots_219 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_219 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
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
def isoMvS_191:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_iso_b isoMvS_191 (by decide +kernel) lowS_127
def isoMvS_253:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_247
def isoMvS_254:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 11:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_239
def dzo_173_2:=0xcccc0000cccc00000000000000000000cccc0000cccc
def gzo_173_2:=0xcccc0000ccc800000000000000000000cccc00008800
def gsh_173_2:=0x33330000333200000000000000000000333300002200
theorem lowS_zo_173_2_141:Lower true dzo_173_2 roots_173 gzo_173_2 6:=lower_iso_b (d1:=dom_173) (r1:=roots_173) (T1:=gsh_173_2) [(dom_173,2)] (by decide +kernel) (lower_slice_b (T:=gsh_173_2) [(0x33330000000000000000000000000000333300000000,0,32)] (by decide +kernel) lowS_141)
def dzo_118_8:=0x55005500550055005500550055005500
def gzo_118_8:=0x55005500550054005500550044000000
def gsh_118_8:=0x550055005500540055005500440000
theorem lowS_zo_118_8_86:Lower true dzo_118_8 roots_118 gzo_118_8 6:=lower_iso_b (d1:=dom_118) (r1:=roots_118) (T1:=gsh_118_8) [(dom_118,8)] (by decide +kernel) (lower_slice_b (T:=gsh_118_8) [(0x550055000000000055005500000000,0,32)] (by decide +kernel) lowS_86)
def dzo_222_32:=0x5555555500000000555555550000000055555555000000005555555500000000
def gzo_222_32:=0x5555555500000000555555540000000055555554000000005554555400000000
def gsh_222_32:=0x55555555000000005555555400000000555555540000000055545554
theorem lowS_zo_222_32_208:Lower true dzo_222_32 roots_222 gzo_222_32 7:=lower_iso_b (d1:=dom_222) (r1:=roots_222) (T1:=gsh_222_32) [(dom_222,32)] (by decide +kernel) (lower_slice_b (T:=gsh_222_32) [(0x44444444000000004444444400000000444444440000000044444444,0,2),(0x50505050000000005050505000000000505050500000000050505050,0,4),(0x55005500000000005500550000000000550055000000000055005500,0,8)] (by decide +kernel) lowS_208)
def dzo_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000
def gzo_219_32:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0e000000000f0e0f0c00000000
def gsh_219_32:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0e000000000f0e0f0c
theorem lowS_zo_219_32_209:Lower true dzo_219_32 roots_219 gzo_219_32 9:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_32) [(dom_219,32)] (by decide +kernel) (lower_slice_b (T:=gsh_219_32) [(0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c,0,2),(0xf000f00000000000f000f00000000000f000f00000000000f000f00,0,8)] (by decide +kernel) lowS_209)
def dzo_159_32:=0xffffffff000000000000000000000000ffffffff00000000
def gzo_159_32:=0xfffffffe000000000000000000000000fffefffc00000000
def gsh_159_32:=0xfffffffe000000000000000000000000fffefffc
theorem lowS_zo_159_32_145:Lower true dzo_159_32 roots_159 gzo_159_32 7:=lower_iso_b (d1:=dom_159) (r1:=roots_159) (T1:=gsh_159_32) [(dom_159,32)] (by decide +kernel) (lower_slice_b (T:=gsh_159_32) [(0xcccccccc000000000000000000000000cccccccc,0,2),(0xf0f0f0f0000000000000000000000000f0f0f0f0,0,4),(0xff00ff00000000000000000000000000ff00ff00,0,8)] (by decide +kernel) lowS_145)
def dzo_223_32:=0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def gzo_223_32:=0xffffffff00000000fffffffe00000000fffffffe00000000fffefffc00000000
def gsh_223_32:=0xffffffff00000000fffffffe00000000fffffffe00000000fffefffc
theorem lowS_zo_223_32_209:Lower true dzo_223_32 roots_223 gzo_223_32 10:=lower_iso_b (d1:=dom_223) (r1:=roots_223) (T1:=gsh_223_32) [(dom_223,32)] (by decide +kernel) (lower_slice_b (T:=gsh_223_32) [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,0,2),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,0,4),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,0,8)] (by decide +kernel) lowS_209)
def dzo_95_32:=0xffffffff00000000ffffffff00000000
def gzo_95_32:=0xfffffffe00000000fffefffc00000000
def gsh_95_32:=0xfffffffe00000000fffefffc
theorem lowS_zo_95_32_81:Lower true dzo_95_32 roots_95 gzo_95_32 7:=lower_iso_b (d1:=dom_95) (r1:=roots_95) (T1:=gsh_95_32) [(dom_95,32)] (by decide +kernel) (lower_slice_b (T:=gsh_95_32) [(0xcccccccc00000000cccccccc,0,2),(0xf0f0f0f000000000f0f0f0f0,0,4),(0xff00ff0000000000ff00ff00,0,8)] (by decide +kernel) lowS_81)
def dzo_207_32:=0xffff000000000000ffff000000000000ffff000000000000ffff00000000
def gzo_207_32:=0xffff000000000000fffe000000000000fffe000000000000fffc00000000
def gsh_207_32:=0xffff000000000000fffe000000000000fffe000000000000fffc
theorem lowS_zo_207_32_193:Lower true dzo_207_32 roots_207 gzo_207_32 7:=lower_iso_b (d1:=dom_207) (r1:=roots_207) (T1:=gsh_207_32) [(dom_207,32)] (by decide +kernel) (lower_slice_b (T:=gsh_207_32) [(0xcccc000000000000cccc000000000000cccc000000000000cccc,0,2),(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0,0,4),(0xff00000000000000ff00000000000000ff00000000000000ff00,0,8)] (by decide +kernel) lowS_193)
def dzo_221_32:=0x3333333300000000333333330000000033333333000000003333333300000000
def gzo_221_32:=0x3333333300000000333333320000000033333332000000003332333000000000
def gsh_221_32:=0x33333333000000003333333200000000333333320000000033323330
theorem lowS_zo_221_32_209:Lower true dzo_221_32 roots_221 gzo_221_32 9:=lower_iso_b (d1:=dom_221) (r1:=roots_221) (T1:=gsh_221_32) [(dom_221,32)] (by decide +kernel) (lower_slice_b (T:=gsh_221_32) [(0x30303030000000003030303000000000303030300000000030303030,0,4),(0x33003300000000003300330000000000330033000000000033003300,0,8)] (by decide +kernel) lowS_209)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(3,131),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,17),(16,18),(16,80),(16,144),(20,21),(20,22),(20,52),(20,84),(20,148),(24,25),(24,26),(24,56),(24,88),(24,152),(28,29),(28,30),(28,60),(28,92),(28,156),(32,34),(32,36),(32,40),(33,35),(33,37),(33,41),(33,49),(33,97),(33,161),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,68),(64,80),(64,192),(72,73),(72,74),(72,76),(72,88),(72,104),(72,200),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,132),(128,136),(128,144),(128,192),(130,131),(130,134),(130,138),(130,146),(130,162),(130,194),(160,161),(160,162),(160,164),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|6=>5
|7=>92
|8=>367
|9=>442
|10=>184
|11=>40
|12=>6
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xe45ddd1f6e60e7c5baa73d30e
|7,0=>0xe1d8bd697ad0bf9c7a6ec7a3fc0aa0bdc90ba8eeb69fdb00c7af4b0adce7acb86abf14aab77a67eea62dfa55e09d1139877291fa98f5988ecd58c7188324b82ac77d52a7d4357aa597a2cb7804c772af758ee7277c7272c71dbd6cf146453163631621db5ffc25fa325e3b55caf05a6e859a4859757582ea55cb650b1a4ce414cbe74986544e0a427db3fe363c7f13a53039ef53945233f5d330833207c318f13024e2f4ff2e41529c3b2709c254b124c0f23ae12398e225e32247320be21f5f31e84a1ccb51933d16576157d9147a70f7ef0c6d90abf707e3004f32047f1028fe0087700705
|8,0=>0x3901c38cd83897a37f9d37b2036763365ae3619f35e4735e27357c1354ee3511d33b8233af5327f13277032508315ad30b37303772fbd52fafc2f5962f4d42f49a2f48f2f0412ebd42eb6b2e2b12df3b2d6a42cd0f2cbb12c3c92c3142b8cf2a2a429d9b29c67293af28b8727f0f27d4127a592719826db726810262d225700253a0250252483723a4a234da22e952252021b9f216c120ee6209c9208fb20826204d0202271f4f31e8bb1e3621e2081e1381d2531c9d51c6681b61f19fec197571973c191d018f6e17fe617ce9175691740916f7516ccd152171426a13c851315c12f9f12e2f12786119a411288101050fbc70ecaf0eb240e2340e0c10d8780ca280c72c0c6660c2140b0d10ac9f0abe60a70b0a46b0a1af0941d07bc50735f06c1506857064de05edb050cf040d5026dc022af01c7c00f9e00d390083c007eb
|8,1=>0x7fb537d4857ab6b7aa597a4aa7a18679b4a79863787eb7804a7802b77a4d7768e763d576240755ee74eb2742d873683727ba71860706096e50f6d5616cba56cb7f6c7d06be806bdc56ba276b6ad6b13f6999d683a86762e6701465ab264b3a643cd637c6633f062e7662c32628fc6150761491609466063b5f0125e36e5d20d5cc5e5ca875c1225be4e5a53659298573855707b5683c5635955a31550a254ea954a385410c53d6253a9852fd65277b5274b5247b51a945170d4fc854fabb4f77b4f3aa4f14a4e5574e50d4dbf94ce2b4b9a74acb449f9549a714955e4898247a2a478de474ee4741e46e8e46ced46681461114546244f974466e4401243dca420da4185d40f3e40c2d406d13fe0e3f4833f25b3f0383f0143efb63e93d3db4f3d8513d7573d72d3d2233c6273c3db3b9733b8e43acdf3a8b2397ae39240390eb
|8,2=>0xfc136fbc76fa3e2f30c5e5a86e1fd9e1cbde1702df404dd0aedae0dd6903d4b2cd491bd0bf9cee07cbc95cb45fc9d5dc6341c5469c49dac4656c0ceebfc4ab9a6cb6c02b6796b55feb5342b450eb2a7db1d38b1522b1092b0e49afdcfaf2b9af278ae9adae856ae6a3ae47fad60cad215ac301ac168abb30ab579a8deea83c2a478fa3f29a359ca257aa1c0ca159ea0d009e9b49e1ed9d32e9c8019ac109971d98d8097b8896dc796004951b4945cc93ade91ebe91d5a90d28908da8f8e68f8628ea9c8e1b08e1098d8b88d4c08d4288ba9a8b9808ab448a2a7893a38936c891e48894a87981875ac87538873408708986ffd86b0085d7085769852a9847af844c0844208395f82d0782c8582643823d58110e80cc7
|9,0=>0x2d28f2cd202c7122c60b2bc282b6cb2b4ee2b17b2b1272af2f2ac832a14b28e1528a122866e2772927563273f126716264332558a251d8251d424f5224a682358b2270a224e220ba6208e420773205911feb71f8d61f6621f1601eed01ed181de001d8a01d44d1d24d1cd0e1c9001c4071c2e01c0b81bec81bc581b9681b5a31aeb81a9ac1a4cf19f4a19976198a718d32178a516bb8163e415c8a14df7144ac143931415d13c531378f1254b122b011419113e610446101350fdbf0fd6f0f9ee0f7f00f2b50ef250eda10ecdf0ec970ebe20e9610e8550e73c0dd4e0db840d8c00cf210c75f0c0a80be0d0b8ce0b7ad0b7040b63a0b2de0afdd0ae430a78d0a41409ed5092cb0908308f3b08ae9084dc0837d082e407c0407b89076e506c0306bf805bec03ac3031f10303c02c7b02469023cb022130157f006230045f00396
|9,1=>0x633b063329630a161e3261cb85f6515efb25ede35e54c5e4835d8465d61a5d5f65ca5c5c68b5c16d5c0905bb3a5ba395b0445a81c5a5d55a37e5925c58fca58f3e58c455717a566c555ce054a5054847542e753db25358652e4e52bad52b1b5233a51b915104d5038d4fd724f9574f4ba4f3aa4f0054efa04ea7b4e2214dff34de4c4d2a34d23a4d2084ce2b4ba6c4b5834b39a4b2014aefa4adf44ab0c48cd94889f4869c481b0480f647ba147b784732a46e8d46bed46a0645eaa4586f456084515944a5a4479b4465742fac42f7e42ae0428544177640e6b40a6d407f34042e3fee53f8ad3f2db3f0b43ed2b3e6623df2e3cd813bed33aee539b3639abb3995238b6c3847638376379a43650d364c23483333d853368d33445333513205831d59307403023d2fa8b2f3982f2072e96e2e56e2dece2dca22dbbf2db032d4fa
|9,2=>0xa71e7a67a7a6625a63dda5ed4a52ada4b0ba4892a3662a355fa31aba279aa23c8a223fa0ae5a030ca02739f0be9e64e9dfee9d82c9c33f9b3cc9b2579ab2b9a9cc9a46d9852e9838f97eaa9645794a0f945a2944b9942c5940a392bbc92ac092a368e21b8d7398d61a8c8778bb2a8a5c38a3318a313894718920388f7b87423872cb8708386f9486c0c86a9985918850828505d842e4842058409383e5f83c818388082a988291f8263281e98813b17f9107f5607ebf87e99a7e4d27e4407e1517db5d7cd317c19a79e177945f7917278231765697524d74f4373eac73d60723d071b3071ad571850707536fe5e6f3ab6eecf6ee5f6e84c6d88d6d1b26b8f96b2176a9e36a65069b8169b50696d469174690946903368c3e67e3e67cdb67b6367a1d679a867968670496698366547663116622f6511164f8a64a8d642b563db4
|9,3=>0xfd8a6f80f3f36e6eebe4eb88fe8a19e6bb9e3e91e2f30df07fde589d8825d7356d4ad7d2ab4d17ebd0732ce892cb36ccaf2dc7d04c6ab6c5401c2e68c2ac8c1a7fbfc4abe088bc730bbe11bb440baec9b9f17b87bab7517b734ab7255b6af7b5ddeb5bb2b4bbfb2f83b2e70b1ec3b1507b0574afbf8aea85ac78aac30dabc4aab926ab5cea9a3ea9346a8a49a7fa2a794d
|10,0=>0x87dab877c08723f8607181ad68049f800dd7f1fb7ec0f7c4527296b7145d70cf470457703586a3a9698f368443681576560c622d860bb9603e45f4165cee85bc635ae4259e90595705945c5904a5433753c8250f284f63a4d8344d1904aa744a52149765485ed47f7c47b2047780475f8466bd45ef3451cb44f43443174310f42a3a418a440bcd407fd3fdcd3e9b03d89f3ce9b3bddb3bd953bd053b94c3b5fa3b26637c4c3740d3715b350ec339cb33760318303171030ef02fa462f25a2ce062a0af2995828f9c28c5528a122887126e78264a126012259e2240c9211b420e7520da71f8d41f4e51eb3e1e6001dba31d3401d17b1ca521c1b71b9b81b3c419f041785f1402d13ada105bf0fcd50f48d0eb430e3760c3270bec70b8360aa470a9cc0a30f0952f07cd705bdd055cb04d13041e40362102f3702ee101bb2010d7
|10,1=>0xf00afed5cfeb5e0e7013e58b6e40d3dcd05dc52adbcf6d84afd6871d4defd204dd0447cf923ce7d2ce670c80dbc67a7c2f08c0e0bbf57ebf52abd0a2bca7eba309b91bdb8910b83d1b69d8ae8e7ac9d6ab912aa914aa74faa6f1a913fa8215a6021a40e99e21b9b6469917c97d5896a8590b5d902118e3558e2298df388dd188dcca8c41d8b4e6894b688981
|11,0=>0xf2f5ce47c6df0a7d8230b9ae8a4628a26f09b4f2902838c96d8c95c8aa247e9c3795636f88661ee65cbf9573fd4a1f347d6c44cc4433cd4306d31fd22f4092d4d12b4a528a2e26abf23d151fb181e1d6188461845711a1d092f707de907b3604b7601f4c
|12,0=>0xc33a3a4c5b792e42da102bad80eef7
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000f0f050505050505050505050f0f00000000ffffffffffffffffffff0000ffff0000aaaaaaaaaaaaaaaaaaaa0000aaaa0000ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa3333333333333333333333333333000033333333333333333333333333330000ffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffffffffffffffaaaaaaaaaaaaaaaaffff0000ffff0000aaaa0000aaaa00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000050505050505050500000f0f00000f0f05050f0f00000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000
|0,1=>0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff00000000000000000000555555555555555500000000000000005555555555550000ffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaffffffffffffffffffffffffaaaaaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa333333333333333333333333333333333333333333333333333333333333000000000000000000000000000000000000ffffffffffffffffffffaaaaffffaaaa5555555555555555555555555555555555555555555555555555555555550000ffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00ff00ff00aa00aaffffffffffffffffffffffffffffffff00000000000000000000000000000000
|0,2=>0x555555555555555555555555555555555555555555555555555500005555000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00000000000000000000ffff0000aaaa55555555555555555555ffff0000aaaa0000000000000000ffffffffffffffff0000000000000000ffffffffffff00005555555555555555555555555555555555550000555500005555000055550000fffffffffffffffffffff0f0fffff0f0fafafafafafafafafafaf0f0fafaf0f0ffffffffffffffffffffffffffffffffffffffffffffaaaaffffffffffffaaaa00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00ff00ff00ff00aaffffffffffffffffffffaaaaffffaaaaffffffffffffffffffffaaaaffffaaaa0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaaffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaa0000555500005555000055550000555500005555000055550000555500000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ffffffffffffffffaaaaaaaaaaaaaaaaffffffffffff0000aaaaaaaaaaaa0000ffffffffffffffffffffffffaaaaaaaaffff0000ffff0000ffff0000aaaa0000
|0,3=>0xffffffffffffffffffffaaaaffffaaaaffffffffffff0000ffffaaaaffff000000000000000000000000000000000000ffffffffffffffffffffffffffffaaaa0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa00000000000000000000ffff0000ffff55555555555555555555ffff00000000ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000aaaa0000ffff0000ffff0000ffff0000aaaa0000ffff0000ffff0000ffff0000aaaa55555555555555555555555555555555000055550000555500005555000000005555555555555555555500005555000055555555555555555555000055550000ffffffffffffffffffffffffffffaaaaffffffffffffffffffffffffffffaaaa3333333333333333333333333333222233333333333333333333333333332222ffff0000ffff0000ffff5555ffff5555ffff0000ffff0000ffff5555000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffaaaaffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ffff5555ffff5555ffff5555ffff5555ffff5555ffff5555ffff5555ffff000055555555555555555555555555555555555555555555555555555555000000000000000000000000ffff5555ffff55550000000000000000ffff5555ffff0000
|0,4=>0xffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffaaaa00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa000000000000000055555555555555550000ffff0000ffff5555ffff00000000555555555555555555555555555555555555555555555555000000000000000055555555555555555555555555555555555555555555000055555555555500000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000000000000000555500005555ffffffffffffffffffffffffffffaaaa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a00000000000000000000000000000000ffffffffffffffffaaaaaaaaaaaaaaaa0000ffff0000ffff0000aaaa0000aaaa0000ffff0000ffff0000aaaa0000aaaa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000fffffffffffffffffafafafafafafafafffff0f0fffff0f0fafaf0f0fafaf0f0000000000000000000000000000000000000ffff0000ffff0000ffff0000aaaa0000000000000000ffffffffffffffff0000000000000000ffffaaaaffffaaaa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0affffffffffffffffeeeeeeeeeeeeeeeeffffccccffffcccceeeecccceeeecccc
|0,5=>0x55550000555500000000000000000000555500000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000aaaaaaaaaaaaaaaaaaaaffffaaaaffffaaaaaaaaaaaaaaaaaaaaffffaaaaaaaaffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffaaaa555555550000000055555555555555555555555500000000555555555555000033333333333333333333333333333333333333333333333333333333333322220000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaaffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffaaaaffffaaaa00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00aaffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000000000000000000000000000000000005555555555555555555555550000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaffffaaaa00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000aa00000000000000000000000000000000ffffffffffffffffffffffffaaaaaaaa
|0,6=>0xffffffff00000000ffffaaaa00000000ffffffff00000000ffffaaaa333333333333111133333333333311113333333333331111333333333333000000000000ffffffff00000000ffffffff00000000ffffaaaa00000000ffffaaaaffffffff55555555ffffffff55555555ffffffff55555555ffffffff555500000000ffff000055550000ffff000055550000ffff000055550000ffff0000000000ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00aa00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff000000aa0000000000000000000000000000000000005555000055550000555500000000ffff0000ffff0000ffff0000ffff0000ffff5555ffff5555ffff5555ffff0000ffffffffffffffff5555555555555555ffffffffffffffff55550000555500000f0f0f0f0f0f0f0f0f0f0f0f050505050f0f0f0f0f0f0f0f0f0f0f0f050500000f0f0f0f0f0f05050f0f0f0f0f0f05050f0f0f0f0f0f05050f0f0f0f0f0f0000ffffffffffffffff0000555500005555ffffffffffffffff000055550000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffaaaaffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000aaaa00000000000000000000000000000000ffffffff0000ffffffffffff0000aaaa
|0,7=>0xffffffffffffffff5555555555555555ffffffffffffffff55555555555500000000ffff0000ffff00005555000055550000ffff0000ffff000055550000000000ff00ff00aa00aa00ff00ff00ff00ff00ff00ff00aa00aa00ff00ff00ff00aa0000000000000000ffffffff555555550000000000000000ffffffff55550000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffaaaaffffaaaa3333333333330000333333333333000033333333333333333333333333332222000000000000000000000000000000000000ffff0000ffff0000ffff00000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffaaaaffffaaaaffffaaaaaaaa0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000a0affff0000ffff0000ffff5555ffff5555ffff0000ffff0000ffff5555ffff00000000000000000000ffffffffffffffff0000000000000000ffff0000ffff00000f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f00000a0affffffffffffffff0000ffff0000ffffffffffffffffffff0000aaaa0000aaaa0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000aaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaa00000000ffffffff00000000ffffffff00000000ffffffff00000000aaaaaaaa
|0,8=>0x5555555555555555555500005555000033333333000000003333333300000000333333331111111133333333111100005555555500005555555555550000555555555555000055555555555500000000ffff0000ffff0000ffff0000ffffffffaaaa0000aaaa0000aaaa0000aaaaaaaa0000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000ffffccccffffccccffffccccffffffffeeeecccceeeecccceeeecccceeeeeeeeffff5555ffff5555ffff5555ffff5555ffff5555ffff5555ffff0000ffff0000ffffffffffffffffffaaffaaffaaffaaffffff00ffffff00ffaaff00ffaaff0000ff00ff0000000000ff00ff000000ff00ff00ff0000000000ff00ff000000aa3333333322222222333333332222222233333333333333333333333333332222000000000000000055555555555555550000000000000000555555550000000000000000000000000000ffff0000ffff00000000000000000000ffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffaaaa33333333000000003333333300000000333333333333333333333333333322220f0f0f0f000005050f0f0f0f000005050f0f0f0f000005050f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f050505050f0f0f0f05050000
|0,9=>0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffaaaaffffffffffffffffffffffffffffffff5555555555555555555555550000000055555555555555555555555500000000555555555555555555555555000000000000ffff0000ffff0000ffff0000ffff00005555000055550000555500000000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffffffffffffffffffff0000aaaaaaaaaaaaaaaaaaaaaaaaaaaa00000f0f0f0f050505050f0f0f0f050505050f0f0f0f050505050f0f0f0f05050000000000000000000055555555555555550000000000000000555500005555000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff000000aaffffffffffffffffffffffffffffffff0000ffff0000ffff0000aaaa0000aaaaaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffaaaa33333333333333333333333311111111333333333333333333333333111100000000000000000000ffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f00000a0a00000000000000000000ffff0000ffff00000000000000000000aaaa0000aaaaffffffff00000000ffffffff00000000ffffffff55555555ffffffff55550000
|0,10=>0xffffffff00000000ffff000000000000ffffffff00000000ffff0000ffffffffffffffffffffffffffffffff00000000ffffffff00000000ffff0000ffffffff00000000ffffffffffffffffffffffff00000000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffffffffffffffffffffaaaaffffffffffffffff5555555555555555ffffffffffffffff55555555000000005555555555555555555555555555555555555555000000005555555500000000ffff0000ffffffffffff0000ffffffffffff0000ffffaaaaffff0000ffffaaaa00000000ffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa0000000000000000ffff0000ffffffff0000000000000000ffff0000ffffaaaaffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffaaaaffffffffffffffffffffffff55555555ffffffffffffffffffffffff55550000ffff0000ffffffffffff0000ffffaaaaffff0000ffffffffffff0000ffffaaaa00000000ffffffff00000000aaaaaaaa00000000ffffffff00000000aaaaaaaa00000000000000000000000000000000ffff0000ffffffffffff0000ffffaaaaffffffffffffffffffff0000ffff0000ffffffff00000000ffff000000000000ffffffffffffffffffffaaaaffffaaaaffffffffaaaaaaaaffffaaaaaaaaaaaa
|0,11=>0xffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaaffffaaaaffffffffffffffff00000000ffffffffffffffffffffffff00000000ffff0000ffffffffffff0000ffffffffffffffffffffffffffff0000ffffffffffffaaaaffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ffffaaaa00000000ffffffff00000000ffffffff00000000ffffffff0000000000000000ffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffaaaaffffffffffffffffffffffff00000000ffff0000ffff0000ffff000000000000ffffffffffffffffffffaaaaffffaaaaffffffff00000000ffffaaaa00000000ffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffaaaa0000555500005555000055550000000000005555000055550000555500000000ffffffffffffffffffffffffffffffff00005555000055550000555500000000ffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000aaaa000000000000000000000000000000000000ffff0000ffff0000aaaa0000aaaaffffffffffffffff00000000ffffffffffffffffffffffff00000000aaaaaaaaffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ffffaaaaffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaffffaaaa
|0,12=>0xffffffffffffffffffffffffffffffff00000000ffffffff00000000aaaaaaaa0000ffff0000ffff0000ffff0000ffff000000000000ffff000000000000aaaaffffffffffffffffffffff00ffffff00ffaaffaaffaaffaaffaaff00ffaaff00ffffffffffffffffffffffffffffffff55555555555555555555000055550000ffffffffffffffffffffffffffffffffffffffff55555555ffffffff55550000000000000000ffff000000000000ffff000000000000ffff000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffaaaaffffaaaaffffffff00000000aaaaaaaa00000000ffffffff0000ffffaaaaaaaa0000aaaaffffffffffffffffffffffff00000000ffffaaaaffffaaaaffffaaaa00000000aaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffaaaaaaaaaaaaffffaaaaffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaa00000000ffffffff000000005555555500000000ffffffff0000000055550000ffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffaaaa0000000000000000ffffffffffffffff0000000000000000ffffffffaaaaaaaaffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffaaaa00000000ffffffff00000000ffffffff00000000ffff000000000000ffff0000
|0,13=>0x5555555555555555555555555555000055555555555555555555555555550000ffffffffffffffffffffffffffffffff555555555555555555555555555500000000000000000000ffffffffffffffff0000000000000000ffffffff00000000ffffaaaaffffaaaaffffffffffffffffffffaaaaffffaaaaffffffffffffaaaaaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaffffaaaaffffaaaaffffaaaaaaaa00000000000000000000000000000000aaaaffffaaaaffffaaaaffffaaaaaaaaffffffffffff5555ffffffffffff5555ffffffffffff5555ffffffffffff0000ffffffffffffffffffffffffffffffffffff5555ffff5555ffff5555ffff0000ffffffffffffffffffff5555ffff5555ffffffffffffffffffff5555ffff0000ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff00000000000000000000000055555555000000000000ffff000000005555ffff00000000aaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000aaaaffffffffffffffffffffffffffff0000ffffffffaaaaaaaaffffffffaaaa00000000ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000ffffffffffffffffaaaaffffaaaaffffffffffffffffffffaaaaffffaaaaaaaa
|0,14=>0xffffffff00000000ffffffff00000000ffffffff0000ffffffffffff0000aaaa0000000000000000000000000000000000000000ffffffff00000000ffffaaaaffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffff00005555000055550000555555555555555555550000555500005555555555550000ffffffff00000000ffffffffffffffffffffffff00000000ffffffffaaaaaaaa00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00aa00aaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaa0000aaaaaaaaffffffffaaaa0000ffff0000aaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaffffaaaaffffaaaaffff0000000000000000aaaaaaaa00000000ffffffff00000000aaaaaaaa00000000ffffaaaaffffffffffffffffffffffffaaaaaaaaffffffffffff0000ffffffffaaaa000000000000000000000000000000000000ffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffffff0000000000000000ffffffffffffffffffffffffffffaaaa00000000ffffffff00000000ffffffff00000000555555550000000055550000aaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaffffaaaaffffaaaa
|0,15=>0xaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaaffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaaaaa00000000ffff555500000000ffff555500000000ffff555500000000ffff0000ff00ff00ffffffffff00ff00ffffff00ff00ff00ffffffffff00ff00ffffff0000000000000000000000ffff0000000055555555000000005555ffff00000000aaaaaaaaffffffffaaaaaaaaffffaaaaaaaaaaaaffffffffaaaaaaaaffffaaaaffffffff0000ffffffffffff0000ffffffffffff0000aaaaffffffff0000aaaa00ff00ff000000ff00ff00ff000000ff00ff00ff000000aa00ff00ff000000aaffff0000ffff0000ffff000000000000ffff5555ffff5555ffff555500000000ffffffff00000000ffffffff55555555ffffffff00000000ffffffff55550000ffffffff55555555ffffffff55555555ffffffff55555555ffffffff000000000f0f0f0f050505050f0f0f0f050505050f0f0f0f050505050f0f0f0f000000000000ffff0000ffff000000000000ffff0000ffff0000ffff000000000000aaaa0000555500005555000055550000555500005555000055550000000000000000ffffffff00005555ffffffff00005555ffffffff00005555ffffffff0000000000000000000000000000000000000000ffffffffffffffffffff0000ffff0000
|1,0=>0xaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaffffffffaaaaaaaaffff5555ffff5555ffff5555ffff5555ffff5555ffff0000ffff5555ffff0000ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff000000000000000000000000ffffffffffffaaaa0000000000000000ffffffffffffaaaaaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaffffaaaaaaaaffffffff00000000ffffffff00000000ffffffffffffffffffffffffffff0000ffffffffffffaaaaffffffffffffaaaaffffffffffffaaaa0000000000000000ffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffff0000ffffffff00000000ffffffff0000ffffaaaaaaaa00000000aaaaaaaa0000aaaaffffffff00000000ffffffff0000ffffffffffff00000000ffffffff0000aaaa000000000000000000000000000000005555555555555555555555555555000000000000000000000000ffff0000ffff00000000000000000000ffff0000aaaaffffffff55555555ffffffff55555555ffffffff55550000ffffffff55550000000000000000000000000000000000000000000000000000ffffffffffffaaaaffff0000ffff0000aaaa0000aaaa0000ffff0000ffffffffaaaa0000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000ffffffff00000000ffffaaaa
|1,1=>0xffffffff00000000ffffffff00000000ffffffffffffffffffffffffaaaaaaaaccccccccffffffffccccccccffffffffcccccccceeeeeeeecccccccceeeeeeee
|_,_=>0
def sP:Nat→Nat
|0=>0x600c161109818380d0600c0411000181a040600c302408018380d0200c040700018121f020300621000181a20020300618058181a1f0600c300b088180a040600c161e00018360d02030061808018120d020303017080182c0502030061509818120d0600c2411080180a04018081e000302408030701c000606810180b040280c090200c1007000180a04018080200
|1=>0x2030060b040184e1f02030040a00018600502030060b00018080c018bc4c13080181a1f0600c2402170180a0c0182c1011098180a040600c302d080b00c090c8101803058181a0406008560a0008c0c05020a80602000181219020300621080181a1f0600c042800018320502030060b10818120d02030061e0808c0c0902030060e000184e2002030060b098184e1f
|2=>0x20308002080880c1f020300618070180a04018081c07000181a040600c2424080187e1f020300602000f80c040600c043d098181a1f0600c2402088180a040600c043c000181a1f0200c2402038181a1f0600c042e000183e040600c2424098181a040600c3039080183e04018087007000184e1f020301636098186a0502030060b00018380502030061e000500c0d
|3=>0x20308e0a080181a1f020300436000180a040182c0e460001812190200c164509818120d0200c304108018121f0200c30070008c0c0502110060200018120d02030240a080182c420203006021e818120d0600c1611000181a1f02030060b0f01812190200c16070981812040600c244309818120d0200c160700018840502030061508018121f0200c1641098cc0c0d
|4=>0x600c3028000184e0502030163600018121902030161709818380d02030064b000182c040600c5e3d0981812190200c30450801832040600c300b2501832050200c300b228184e040600c1643099240c050203006020981838050203006210001832050600c300b088180a040180890130801812190200c3007080184e1f02030160a09818380d02030040a00018120d
|5=>0x2030300a080180a04018081007000180a0c018089c13080180a040600c044d000184e1f0200c040700018121f02030061e000180a04018601645000181219020303017080183e040600c3024000f80c42028101803010181a040600c2402218181a1f02030040a26018120d0600c302e080181a040600c1624000d00c040600c043d0808c0c09020300608000183805
|6=>0x310832040600c043d0808c0c0d020300602158000c1c02830060214000261d030243e040600c24130309c080c018084c13080183e050600c044e098400c050600c24022884c20060283006022884c204f03014080c0182c0413278180a040600c300b098184e040600c0443098407c061387c080c0180826061381408030101c0010198181a040600c042b000181219
|7=>0x1884068060e014080c018080006138701a040600c241003064080c01860044a080180a040600c165b098400c0d0281018022d04c2014030700a040600c3000030240a0c018485c130808c0c050203006182c8000c580283006022b84c20220307c080c018087000030640a0401860044508018121f02030060b2a84c4a0604834080c01860200604864080c0182ca813
|8=>0x10f426100307c0a0406008b413080180a040600c5e6209840c0060281018030580826060281018032e8602610110181a1f020300612010183e050600c16021704c46061387c080c0180800060481018030c0e80010030640a040600c3015080187e1f020300602098406e060687c080c01808003e030700a040600c041303014080c01860163a000181a05020300612
|9=>0x30140803011902610110181a1f020300602260f80c050203006120104c28060b014080c018082606290101803178f426100309c321f020300618058182c420c814080c018083a0604834080c01848200606814080c01808c610030640a040602c04170981812040600c100003014180301144001308018a4050200c0441098400c1f020300602120002633030101803
|10=>0x182c26060c814080c018601654030141803011a42610118180a040600c0408000183867020300602098400c1f02810060220800261d030343e040600c300b030240a04018480e13080180a04018080e590004c0c0d0281006120110420060281006023319426100a018121f020300612098180a0c01808a23d098400c050200c1602228002606138140803011202610
|11=>0x2030046e098400c0d0f8101803011b400060687c080c018084210030340a0c01860042e080a40c1c068101803010000c520203006021304c2006048141803090442610030241a0c0182c2213080181a040600c046b098400c090c81018030c1502006028101803058540013031080a0c01808d4130801884040600c043d0801838050600c046a09840a00604814080c
|12=>0x98186405020300618098404a060487c080c0184826060f8101803011ac26100307c0a0c018601611098180a0c0182c0411099c80c190203006021204c2006068101803388082610031482c0502030062f09818121f02030060b3804c4a060b014080c0180826061387c080c0182cde13030241a0406060141003034080c018084800080b00c0d0f8101803058080c05
|13=>0x600c3013080180a0401808ee1308018ec0d0203006020984046060487c080c018482606029d418030580822130a018120d020300612080180a0401808e873098400c1f020300602130002606068101803090084c101f0180a040600c0400098dc0c0502030062f0984046060b014080c0180826060283006023504c20060b014080c0182c5e130e8184e1f02030060b
|14=>0x8018380502030065b098400c0d0f81018021b04c2014030343e040600c300b03014080c0182c481308018121f020300678098400c090681006022284c20060c81408030110426100307c080c018601c06138141803010b82610031ec0a0406008f413080182c420281018030101832050203030020b8400c050200c24023b84c20060f814080c019e01613030244004
|15=>0x2304c200604834080c018542610030701a04060081413080183e050200c16022284c0c42028101803011e42006290141803010a02610280184e050203006020013c0c050203006120104c0c0d02810180b0102800060f814080c018083c00030700a0c018082200098880c090f81018030c0000c050203006181204c207c030640a040600c0410030140803010bc0e13
|16=>0x20300602080183e0502030060b0a84c0c050200c30022404c20060e014080c018842610030140803058089013080940c09068101803090400c090681018030c1c020060681418030c02c2210030243e04018088a13080183e040600c16022504c0c1902810180b01028260604834080c01028001019818120d02030061208018a4050200c0448098400c050600c1611
|17=>0x21014080c01808003403014080c01860041003070080c018bc7a13080180a040602c04170004c0c050200c04770004c203403014080c01860161003014080c018bcda1308018121f0203006150984028061387c080c0182c26060e01408030110426100307c0a0c018085000098500c1c068101803010000c190203006021304c2023030241a040600c24101a018a405
|18=>0x4084c2033030241a040600c8e10030340a04018600445080180a040180900130801832050203006020f0400c0d0f8100602038009e060281018030100026060281006023b8f4261003014080c018088613080183e040600c047e0984068060f814080c018080006028100602179142610110183205020300618058180a040600c0462098400c050600c047d098400c16
|19=>0xe034080c01808000606814080c018602a10031080a040600c046f08018a4050600c042e098400c1c0203006021304c201403014080c0182c1013030101803178f42610298188405020300602080cc0c270f81018030584c0c0d020300618011282033030701a040600c0400030580a040600c0484098180a040600c300b2a0000c050203030024104c2006028100602
|20=>0x30241a04060082e13080183e0502030060b3f84c0c1f0281006120101c26060e0641a040600c300b300180a040600c040009818320502030060b2584c0c1f0283006021700026060e034080c0192c2610030640a04018089013081400c090281018030904c0c190281018180102820060c8141803010a026100e8188405020300602080182c1c0281018031784c4606
|21=>0x98400c2702810180b1b04c200621014080c01808d010030243e04060082e13080180a200203006120104c0c093381018030584c20060687c080c01808de00030343e0c0182c0411098a40c0d0f8101803010000c320281018030904c20060487c080c019fc2610030241a040600c3085080184e42028101803178400c090c81018032584c20060b014080c01808e013
|22=>0xf81018030c0000c190283006021704c20060283006024384c2006068140803090080e100309c080c018087400080184e050600c044e0984028060687c080c01848040629014180301044261003014080c012182610030640a040600c16310981884050600c0428098400c0d028101803058c40006138701a040600c1600030700a0c01860501308018a4050200c0407
|23=>0x90082033030343e040600c240203034080c0180876130801812050200c16070004c0c040600c043d2a04c2006028300612010a0261003014080301120261028018120d020300618080183e040600c24022504c34060c814080c0186016060281018021785c261003014080c4500826100307c0a040600c30310001912050200c0464098400c0544030060b098184e1c
|24=>0x600c3c130814c0c0502030062f0984052060281018031784c20060e0141803010b82610280184e0502030060b098180a040602c048e098400c5221014080c018bc2025031080a040600c04100307c0a040600c161e098184e0502030045a098400c890281018023704c200602810180309234261003014080c018083c0008018a40d0f81018030c02c6806028101803
|25=>0x203006180a84c2029030701a040600c30100309c3819020300618080b00c090f8101803010000c0502030060b0a84c2033030343e040600c044c031080a040600c302f080182c050203006023104c0c0502030062f3784c20060681018030110c26100303440040600c3002080dc0c270f8101803010000c1f028101803010840023030343e040600c2402030243e04
|26=>0x600c040e000940c0d0f8101803010000c050200c0492098400c520283006022704c201d030701a040600c301003014082a0180800060281018030592c001303014080c0c02c6c13080184e0502030060231840280604834080c0182c0006028100602240002610030580a040600c0454098180a04060081491098400c0902030060e000740c0502030062f098400c05
|27=>0x30241a040600c160003014080c012502610031080a0c018082213080880c090f81018034984c0c1c0283006180884c201d0309c0a040600c160003014080c010bc1413080b00c190281018030580844061387c080c0180800060481408030c01c00100309c0a040600c166f000180a040600c300b2184c0c0d02810180301078201d0302432040600c3010118180a04
|28=>0x400c0d020300618058e82023030243e040600c30000301418030c02c22001a018380d020300602082540c1f028101803010000c160c8101803010f426060e014080c01860da000319c3e040600c1602098d00c0d028101803010400c30028101803010002022030700a040600c3000030340a04060086c00080183805020300678098400c050203016022d04c2023
|29=>0x281018022d04c200621014080c018bc205303014080c018082610030141803011a4e613080180a040600c3002318404a060281018031784c2006068101803058200c0d0281018024104c20060c81418030113826100301418030125d2c13080180a040600c300b250000c1c0281006022284c20220307c080c018081c130309c0a040602c1413080186a05020300602
|30=>0x580800060f81408030c0080e00030340a0406048040a0801812040600c2426098400c1c0281018033f84c2006028108803010000c0d02810060b0101c00060283006022704c20060f81018033880800130301418030c008a2130801812050200c2441098400c050600c16022884c200619014080c0182c0013280181a05020300602000680c090681018030c0400c19
|31=>0x4d818080c018087a00098400c1f02810180301078261011018121f020300618098400c190f814080c0105c261003014080c01809341308018a40d0f81018030c0082029030580a040600c04130307c0a0401809321308018a41621014080c018080c0d0281006024c84c2006028300602270002610030140803010ac0e00098f80c050203006180584c6806028101803
|32=>0x600c163109840d8060c814080c0180826100309c0a040600c300b000180a040600ce2020004c200651014080c018082610030340a040600c0470000400c090203006121e84c2033030241a040600c3010032800a040600c0413081400c270281018030104c20060c814080c01a7c0413080180a040600c049c098400c0d02810180b010282610030343e040600c044c
|33=>0x80500c0d02810180305808000653014080c0180826100d0180a040600c16020004d4a060281018030104c202503014080c018087a13080183e050203006023404c20060c814080c01808e013080180a040600c3031098400c05020300612058c426101b8184e0502030060b098400c05020300602070000c050200c1602038002606210641a05020300602080180a04
|34=>0x20300602098180a040600c045b098404606028101803010f426100307c080c0182c043d098500c1902810180305808260621014080c01808001056018f605020300602098400c1c028101803011b40013030343e040600c2402000500c1c0681018030104c2006028101803011f826101101838050203006020004c0c050203006120c0c426100329c0a040600c0413
|35=>0x28101803090602606028101803058089400098196205020300602098400c5202810180301188261003014080c01860043b098400c42028101803090080010308180a040600c0400098400c05020300612010e82610110180a040600c042f0984046060487c080c01808001303014080c01ac01602098400c050600c1602088002606028101803058095c13030581a1f
|36=>0x600c041303014080c018084213080183e050203006024b04c0c090c81018030584c0c52028101803011502610308180a040600c043d098400c05020300618011882610030241a040600c16001a0183e05020300602098400c0502030060b0118826102b018121f02030060b098181a05020300417098403a060c814080c01860041003014080c01974041308018381f
|37=>0x600c04b5098400c1f0281018020b84c205c031080a040600c0413080180a040186004410984066060c814080c0182c041319818120d020300602000400c050200c240b0110426105a0180a040600c0473098400c0502030060b0109826102e0183805020300602098400c1c028101803011c0261019818380d020300602098400c050200c16022084c205e030580a04
|38=>0x480180a040600c0413080a40c0502030060b0100026060487c080c01860000653014080c018080013080dc0c160281018030104c20060e014080c018bc2610118181a0502030060b01000660604864080c018082610030580a040600c3002000183e050203006025b84c20060281006120c0088213080180a040600c30021304c20220307c0a040600c0493098180a04
|39=>0x2030060b011e426060e1081a040600c04102e0180a040600c0413080197005020300602098400c050200c3002038002022030343e040600c0400118181219020300602098400c1c0281018032584c2006210340a040600c04100d018120d02030060209840d8060281018030104c20060681018030c0087a1011818320502030060b0104c460604834080c018080010
|40=>0x118180a040600c042b0004c6e0629014080c018082610031482c0502030060b0104c0c050203006bf012f826105e8180a040600c041308018121f0203006023c84c20065e014080c018082610032e80a040600c04130801836050203006020984034060f814080c0182c0413118183e050203006180100034060281018030c0080010031480a040600c0413080183e05
|41=>0x681018030c0400c19028101803011882610030343e040600c046f098400c0502030061801128001003014080c018098813080186405020300602098400c0502030060b230000c1f02830060b010442629030343e040600c0413080184e050203006026184c200604864080c0182c00130d018121f0203006020984182060281018030104c2006028101803090bc2610
|42=>0x186004100331c0a040600c16020984044060687c080c0182c041303014080c0186004be080180a040600d7ec60104c200613814080c0c0086c1308018121902030061808018a4190203006021e84c20060e014180305808501308018380d020300612010400c190281018030c02c0c270e034080c0182c261003034080c01808101003014080c01b141602098400c1c
|43=>0x2830060b010a0261003014080c01860046f0004046060c814080c0186004100d0181a05020300618010403a0604814080c018482610030340a040600cba02098400c27028101803058000cc90281018030584c2006138703e040600c3013080b00c1f028101803010000c050203006026404c20060281018030109026101f0184e050203006020984066060c814080c
|44=>0x133826102f0182c0d0281018030104c0c0566830060209840660613814080c018080010031480a040600c046d0984196060281018030104c2006048641a040600c1613030240a040600c165509840440629014080c018082610110183e05020300602099300c050203006121884c2006028101803013282610030700a040600c0462098412a060281018030104c2006
|45=>0x98400a040600c04d5098400c050203006026984c20060f8101803090087a13031482c190281018030104da405020300602098400c0d0203006021d04c20ac03014080c0180826100e8180a040600c0498098400c050203006d00c0082610030700a040600c0454098400c050203006021d84c200629070080c018087a13080740c1f0281018030c02c2606028101803
|46=>0x600c04130801974050203006d40104c20370309c3e040600c0413080680c270281018030104c20060f814080c018084213080a40c1c0281018030100026061387c080c01860040003024321f02030060b098180a040600c0462098406e060c814080c018082610118184e05020300602000400c090c81018030c000200606814080c01a7c0413080180a040600c048d
|47=>0x9841b8060281018030104c20060281006022084c2006290101803010f42610160183205020300602080b00c090f81018030104c20060281018036d00826106c819120502030060209840d80606814080c01808261003014080c018084800098400cd80281018030104c202c0307c0a040600c1602098180a040600c0443098400c270281018030117c26100335c0a04
|48=>0x528180a040600c0466098400c420281018030580800060281054030104c200670014080c018602610031482c1c0281018030104cd8060f814080c018082610030700a040600c300b000500c090681018030584c200602810180301378261003014080c018480426098400c0902030060e098400c050200c24022084c20060281018030109826100307c0a040600d3e02
|49=>0x600c300b0a0183e050203006180584c2806028101803058082672710180a040600c0413083480c05020300602098417a062c014080c0180826100309c1a040600c043d098400c090203006181d04c20060281018030138426100307c080c018087a00098182c1c028101803058082606028300612058085c13081700c1f0281018030104c20060c814080c0182c5e13
|50=>0x63814080c018082610030701a1f02030061808018120502030060b3804c2006290580a040600c0413110184e1f02030060209841ca05020300602098400c19028101803011b426100a0180a7502030060b0104ca60613814080c0180826100309c0a040600c166f098400c090c834080c01860200602810180301188001308019781f0281018030104c20060c8340a04
|51=>0x80180a040600c04260004c20060687c080c018089613080180a040600dce02098400c050203006027304c201d0309c0a040600c1613080180a04018088200098400c190f814080c0186016060b014080c018601613160183205020300602000404a0604814080c018482610030240a040600c3070098400c520b014080c0184804130309c8405020300618010400c1c
|52=>0x3014080c0182c8c13080180a040600c300e080680c520281018030104c2006068101803010f40010748181a1f02030060200018127502030060b0981838050600c0428098406606028101803012442610118180a040600c04590004c0c090c87c080c018602006138340a040600c160003014080c01809d013080dc0c050203006120104c2006028100612011040013
|53=>0x600c040009b940c05020300602098400c050600c0428098400c050203006027704c200658814080c018096413080180a0c018601611098412a060f814080c018082610030700a040600c306d09840440621014080c01808261011018380502030061809841d2060c814080c018bc26100a0181a05020300618058400c050203006027604c20060283006027504c2014
|54=>0x98400c1c0203006021e84c200602810180309008da13080740c1f0281018030900826f103014080c018082610198181a05020300618058400c097801018030c0400c050203006780104c200629034080c018087a13080b00c1906814080c01808200654834080c018082610198180a040600c042f09841de060281018030104c20060281018030c1640006290580a04
|55=>0x30708405020300602000a40c050203006180584c2006138583e040600c04130302432040600c0454098400c1f02810180305808aa13030140803013d026100305832050203006020994c0c520281018030104c202c03014080c01808001011018121f02030060b098184e1f020300602000183e050203006022184c20060c814080c0182c0454098180a040600c04f3
|56=>0x1784c20290307c0a040600c0400098183e040600c044a0004c0c05020300618010e80010030640a04018080e13080180a040600c04c3098400cf70281018030104c200604834080c0102826107b0180a040600c300209840a6060281018030c008261003014080c01860166f098400c5221014080c018600410298180a040600c1602098400c520f8101803010f42610
|57=>0x18080006028101803583e80413080184e050203006181784c2056030708405020300602080180a0c01809f013080f80c05020300602098400c160e014080c018082633030343e040600c0400030141803090085c13080180a04060600436098403a0606814080c01848041003014080c018081000030141803010b82610128184e0502030060209841d206028101803
|58=>0x30580a040600c24020981838050600c0411098400c5204834080c0182c261003034080c0180894000801832050203006180115020050203006027d84c201d030343e040600c3002080180a040600c16023404c20060c834080c018087a130801838050203006023c84c20060281088030104c2022030243e040600c0400098b00c0d0281018030104046060687c080c
|59=>0x104c20060283006021700026100307c0a040600c16023804c0cc70f814080c0180826107f0180a040600c041308018321f0203006021e84c200604834080c018bc26100e8180a040600c3059098400c050203006027e84c2033030580a040600c0413080500c520281018030104c2053030640a040600c0413080180afc0600c1602098400c0d028101803011bc0010
|60=>0x28101803058096e13080183e0502030060b2584e04060281018030104c2006028300612010442610030243e040600c5e13080180a040600c0501098403406028101803090082610280180a040600c300b098180a040600c045f098400c520487c080c018602610128183e050203006120104c0c050600c240217000261003014080c0180a0013080d00c0502030060b
|61=>0x31481a05020300618058400c2702810180301210261003034080c018087a13080182c190f814080c018082623031480a040600c0413080180a040600c0504098400c160281018030900800134d818080c01860043d09840f8060281018030104c20220307c0a040600c30020026c0c040600c16021e84c2006028101803090089413080183e050203006780104c2006
|62=>0x203006120104c0c090c81018030904c20065207c080c018082610830181a05020300602098400c0d028101803011cc20060281018030580a0a13084080c050203006020004c200621014080c0186004100307c080c018087a1308018381906810180305808265303014080c018082610030343e040600c300b128181a05020300612010400c0d0281018030c008e010
|63=>0x9840b8060281018030580826100309c1a040600c043a098400c090281006020384c20060281018030104e121003148380502030062f098400c098401018030104c20060281018030141c261003024080c0182026102b018841f028101803010400c050203016020504c205303014080c018080013080500c1c0281018030c04c20060281018030c008a800080184e1f
|64=>0x203006120104c210a03014080c018082610128180a040600c24020004c200613814080c0182c261003014080c01808aa13080940c050203006020004c202c0307c0a040600c0413081580c1c0281018030104c20060f814080c01809261311018121f020300602098400c05020300618011c820060481408030101c0013080184e0d0f81018030584c0c05020308002
|65=>0x5b04c20060281018030c0090a13080184e1f0203006180104c20c203014080c01808261003014080c01028261003014080c01809be13080181a050203006024884c2006028101803010e82610031483205020300602098400c0d0f8101803010006e0613814080c01808261003014080c018086213080500c0d0281018030104c2006028101803010bc0013080184e05
|66=>0x203006021784c2006028101803010c400130801838050203006180584c20060f814080c018480413030343e040600c1602099780c090281018030c04c2014030240a040600c1613080180a040600e1602098400c520e014080c018082610030580a040600c041308018a40d028101803058082610768180a040600c04130840c0c05020300602098400c05020300602
|67=>0x3d814080c0180826100307c0a040600c042f098400c050203006021c0002006028101803012ac2610031480a040600c0413080180a040600c24023804c2006028101803011c02610031483e050203006180104c20060e07c0a040600c0400098180ab90203006020984136060281018030580800130314832050203006020004c200621014080c0182c0413080181a05
|68=>0x28101803011302006290641a0502030060209840ac060e07c0a040600c0413080dc0c2706814080c018082610748181a1f020300602098400c1f028101803090080013118181205020300602098400c0d02810180309008203703014080c018600413080184e0d0281018030584c20f503014080c0180826100307c0a040600c044b0984218060281018030104c2006
|69=>0x98400c050203006182c84c209b03014080c018600400080199205020300602098400c520c87c0a040600c0413080500c0502030060b010002606068101803010ac2610031480a040600c0400098400c050203006028684c20060687c080c018600410030240a040600c1600098180a040600c04700004c20e303014080c018080013080181a0502030040a098400c0d
|70=>0x121426100309c3e040600c04130801832050203006120104c2023030240a040600c04000984044060281018030c008261003014080c0182c046d098400d0e0281018030104c20060281018037f8082610030340a040600c2402000400c1f0281018030128c26100e8180a040600c3002000400c0d02810180323808200654814080c018082610030340a040600c0484
|71=>0x180826100e8181a050203006180104066060687c080c018082610030700a040600c2402098400c090281018030c0002006028101803010202610033741205020300602098400c5206814080c018082610118180a040600c16020004c0c520e07c0a040600c0413080181a050203006025404c20060e1080a040600c0413081580c090281018030584c2006028101803
|72=>0x3014080c018600400081780c050203006022304c20060281018030123c2610878180a040600c0413080740c270281018030104c20060487c080c0182c26060f814080c018093a13080dc0c05020300602098400c27028101803011bc2610110183205020300602098400c050203006024b04c205003014080c0180826100a0183e0502030060b0104c0c520f814080c
|73=>0x11bc261003014080c880082610032900a040600c0413080180a040600da802098400c1f028101803011502610148180a040600c1602098400c050203006025984c2006028101803090087a13080180a040600c046d098400c050203006021e84c20f903014080c018082610030340a040600c04540984044060f814080c018600413081780c0d0281018030c0082023
|74=>0x600c042b0004c0c1f0281018030c00800060281018030133c26100301542040600c0413080181219020300602098400c0d0281018030580800330309c0a040600c04130826c0c050203006120c00826100d0183205020300602098400c0502030060209bc8201d03014080c01860161308018841f0281018030104c209b03014080c018481602098400c05020300618
|75=>0x203006180104c202503014080c018481602098404a0602810180305808261003014080c01860049809840bc06138340a040600c04130801812190203006020004c201a03014080c01808261003014080c018099813083a40c190281018030104c209b03014080c018092613080180a04018080e130801812050203006120c04c200604814080c018481613080180a04
|76=>0x281018030103826104d8180a040600c04132604222060281018030104c20060c87c0a040600c160209818380d0f81018030104c2006028101803012b82610030240a040600d2613083a40c19028101803010002610030641a0502030060b0104c0c050200c04070004c200613814080c018080010128180a040600c24180104c20060e014080c0182c0400098940c05
|77=>0x203006021c04c2006049d4080c018082610030243e040600c301308018321f0281018030c0082006290700a040600c1602098400c1906814080c018600410030241a040600c161308018120502030060209aec209b03014080c0191c04130808c0c190281018030104c20370309c0a040600c300209840280606814080c0182c0413080cc0c190281018030104c2006
|78=>0x9841c6060281018030104c2006028101803012a02610030700a040600c160209840bc0604814080c018082610033740a040600c0413080cc0c0d0281018030104c20060281018030128c26102f0181a050203006020984046060281018030100026100309c0a040600c0413080180a040600c042b098400c050203006026884c2006028101803058091613081780c05
|79=>0x203006020993020060f814080c0186004130801832050203006020004c200606814080c0182c0413080180a040600c0493098400c190281018030104c200606814080c0180800102b0183e05020300602098400c050203006022c84c20060f814080c01808001303014080c018483002098400c0502030061205808261003014080c018601613080180a040600c048b
|80=>0x104c20060f814080c0182c04130a0180a040600c04130826c0c050203006020004c200604814080c018080013080181205020300618098400c090281018030584c20060281018030104d76100e8180a040600c3002098400c1c0f814080c0180826104d8180a040600c3002098413606028101803058082610110180a040600c0413080180a040600c8e02098400c05
|81=>0x3014080c0180826104d8180a040600c0413080181205020300602098400c050203006020004c20060281018030c008261003014080c0182c0413081580c05020300602098404606028101803
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0x1c70055c00e7001dc0007
|7,0=>0x86e02138082e0203807ee01f3807ae01e38076e01d38072e01c3806ee01b3806ae01a38066e01938062e0183805ee0173805ae01638056e01538052e0143804ee0133804ae01238046e01138042e0103803ee00f3803ae00e38036e00d38032e00c3802ee00b3802ae00a38026e00938022e0083801ee0073801ae00638016e00538012e0043800ee0033800ae00238
|7,1=>0xbee02f380bae02e380b6e02d380b2e02c380aee02b380aae02a380a6e029380a2e0283809ee0273809ae02638096e02538092e0243808ee0233808ae02238
|8,0=>0x14da452d91492451b9144a45099140244f8813be44e69137644d49132e44c2912e644b09129e44a07125e448e91216447c911ce446a9118644589113e4446910f64434910ae44229106644109101e43fe90fd643ec90f8e43da90f4643c890efe43b690eb643a490e6e439290e26438090dde436e90d96435c90d4e434a90d06433980cc2432790c7a431590c3243039
|8,1=>0x1db6476491d6e475291d26474091ce5c73091c9e471f81c5a470d91c1246fb91bce06ea91b8646d891b3e46c691af646b491aae46a291a66469181a22467f919da466d91992465b9194a4649919024637918ba46259187246148182e4602917ea05f1917a245df9175a45cd9171245bb916ca45a99168245979163e0586915f64574915b205639156a455191522453f9
|8,2=>0x26a649a09265e498e92616497d825d2496b9258e095a9254a0949925024937924ba49259247249139242a4902823e648f09239e48de9235648cc9230e48ba922c648a89227e4896922364884921ee4872921a648609215e484e92116483c920ce482a9208648189203e480691ff647f491fae47e291f6647d091f1e47be91ed647ac91e8e479a91e46478891dfe47769
|8,3=>0x2f8a4bd992f424bc882efe4bb692eb64ba492e720b9392e2a4b8372dea4b7192da60b6092d5e4b4e92d164b3c92cd20b2b92c8a4b1992c424b0792bfa4af592bb24ae392b6a4ad192b224abf92ada4aad92a924a9b92a4a4a8992a024a77929ba4a65929724a539292a4a41928e24a2f9289a4a1d928524a0b9280a49f9927c249e79277a49d59273249c4826ee49b29
|8,4=>0x38724e139382a4e01937e24df08379e4dde937564dcc9370e4dba936c64da89367e4d96936364d84935ee4d72935aa0d61935624d51735224d3f934da4d2d934924d1b9344a4d0b7340a4cf9933c24ce79337a4cd5933324cc3932ea4cb1932a24c9f9325a4c8d932124c7b931ca4c69931824c579313a4c45930f24c33930aa4c21930624c0f9301a4bfd92fd24beb9
|8,5=>0xfbc93ece4faa93e864f9893e3e4f8693df64f7493dae4f6293d664f5273d264f4183ce24f2f93c9a4f1d93c524f0b93c0a4ef993bc60ee893b7e4ed693b364ec673af64eb493aae4ea293a664e9093a1e4e7e939d64e6c939920e5b9394a4e49939024e37938ba4e259
|9,0=>0x487e5216948329203947e691efa479a51dca474a91c8a46fa91b4a46aa91a0a465a918d94612517b945ca5168a457e5155a45325142a44e2912f94496911c9444a9108a43fe50f5a43b250e2a436650cfa431690bba42ca50a8a427a9096842365083a41ea5070a419e505da4152504aa41065038940be5025a406e901294022900083fda8feca3f8a8fd8a3f3e4fc5a
|9,1=>0x52025476a51b29462a5162944f95116943c950ce542a950829416a5032940394fe693f094f9e53de94f5653cc94f0a93b994ec253a6a4e76539494e2a9380a4dde536da4d96135ba4d46934894cfa9334a4cae5321a4c5e930da4c0e92fa94bc652e7a4b7a52d4a4b2a92c0a4ada92aca4a8a9298a4a3a9285949f25273949aa526284962924ea4912923c848ca9228a
|9,2=>0x5b6a96d285b2656c095ada96aca5a8a969995a3e9685a59f25672a59aa1660a595a964d95912563aa58c29626a587656149582a9601957e255eea579295daa574295c6a56fa15b5956ae95a29566655909561a957ca55ca9568a557e5555a552e9543854e6952fa549a551e85452950c8540a94fa853c294e6a537294d39532a54c2852e654afa5296949c9524a94899
|9,3=>0x64da992ca648a99199643e9905a63f258f2a63a298df9635a58cca630a98b9962c258a7962769893a62269880961da986d96196185c9614a9848a60fe5835a60b25822a606a18119602257fea5fd657ed85f9257db95f4697c895efa97b4a5eaa97a195e5e978e95e12977b95dc69767a5d769753a5d26974095cde572e95c92971aa5c465707a5bfa56f685bb656e49
|9,4=>0x6e469b87a6dfa5b7596dae9b61a6d625b4ea6d1a1b3d96cce9b29a6c825b16a6c365b0586bee9af296baa1ae196b5e9ace96b129abaa6ac29aa6a6a729a92a6a265a81869de9a6f869969a5c9694e5a4b8690a5a38a68ba9a25968725a139682699ffa67d699eba678a59d99673e99c6966f659b4966aa99a0a665a998ca660a9978a65be5965a65725952a652a1940a
|9,5=>0x77aa9de0a775e5dcda77125dbaa76c65da7a76769d93a762a5d80a75de5d6e975929d5b975469d49874fe9d35a74ae9d21a74661d0fa741a5cfd973ce9ce9a737e9cd78733a5cc5972f25cb3972aa5ca0a72621c908721a9c7d971ce9c6a971829c579713a5c45970f25c32a70a29c1ea70529c0aa70029bf796fb69be496f6a9bd0a6f221bbf96ed69bac96e8e5b9b8
|9,6=>0x803ea00697ffa1ff4a7faa9fe197f625fcea7f165fbc97ed21faaa7e865f97a7e369f83a7dea5f7197da25f5ea7d565f4ba7d069f3897cbe5f25a7c725f1487c2a9f00a7bda9eeca7b8e5ed9a7b3e9ec697af29eb2a7aa65e9fa7a569e8ba7a069e77a79ba5e65979725e539792a5e40a78de5e2e978929e1aa78429e07977f69df49
|10,0=>0x89e6626eb898ee258b893aa244a88eaa2319889ea21da8852620aa880661f8987baa1e59877261d398726a1c0986d6e1aba868a6198a8636e183a85e6a16fa8596a15c9854e6149a84fea136984b2a12398462e10f9841a60fd983cea0e9a838260d88833e60c5a82f260b2a82aa20a0a825e608da820ea079a81c26065b8172605398126a03fa80d6a02c9808aa0199
|10,1=>0x938a64d8a933aa4c5992eea4b2992a664a09925aa48bb9206a477a91b6a4649916e6451a9126243fa90da642ca908aa419990426406a8ff2a3f2a8fa2a3dea8f5663cc98f0aa3b8a8ebaa3a3b8e66a38fa8e16a37c98dce6369a8d7ae354a8d2aa34198ce2632ea8c92a31aa8c46630898bfaa2f598baea2e298b5ee2cda8b1262baa8ac662a898a7e6295a8a2ea2829
|10,2=>0x9c0ea6f9a9bc266e799b76a6d2b9b22a6bf99ad6a6aba9a86a696b9a2ee681a99e2666ea9996665ba9946a648998fe6634b98aaa62199862660db980ea5f9a97bae5e4a976aa5cfb9716a5bc996ce65a9a967ea59789636a583a95ea6571995a2655f9955a654d9950ea538b94baa5259946ea511a941ae4fca93d224eb9
|11,0=>0xa1f668749a1ae6861aa15ea84e9a116683c9a0caa828aa07aa814aa02e680299fe667efa9f96a7dba9f4a67c999f0267b6a9eb667a499e6aa790a9e1e677e99dd6676c99d8aa758a9d3e6745a9cf26732a9ca2a71f99c5a670d9
|12,0=>0xa2ce68aa9a28668989a23e68869
|13,0=>0x28bc8
|_,_=>0
def wAt:=mkWire dB 274 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 18
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x14813030710107d028410d06303065068410284d0104d028090682c03001010410804d0284d0a013010350284d0302d058150a0130302d010410109a128170284d030490c0410104d118330581503001010410804d02809110600104d02841010410284d0e87c028410104d0284d0a0130d0630306501041028010804d0e87005815010410284d0104d0d00f03065068410284d0104d0a0130302d0584d01041
|1=>0x110600104d028410a0130302d0584d010410100111833030010804d028411281303049010010984111827010010300109841010ee1d0410e817030610104d1b80f0309d028610104d1a00b030710107d028410302d0f860010410104d0284d02841010351980f030350284d1904f028c51180b030010984112813030490c0410104d0a0130f8600302d028410104d03001060390682c010410804d0284d0804d
|2=>0xf84d02841128330284d030490c0410104d1183303001098410300109841060210f860028410104d010011980f030350804d0284d0a0130302d098410307d028411183303001028010804d0e87f030610c0410104d1183303001098410284112833030490584d01041030350284d018210f860028410104d058340284d02841010410104d118330682c03001010410284d12827030490c0410104d0984102885
|3=>0xc0410e87f030610104d0284d12813030490c0410104d030010804d0f860028090284103001098410104d14813030710107d028411b80f0309d028610104d0d00f030650f84d028410d033030650f84d028410d033030650f84d028411f0170309d028610104d068410284d0a0130302d1183303001028010804d010351980f030350284d1980f030350107d028411b80f0309d02841068090804d0d03303065
|4=>0x2841030610c0410104d12817030490c041028610104d29813031490c07d0104d2801512843030490584d280150e843030610104d1b87f0309d028610104d1b8430309d028610104d0484d1183303001010150804d0f80b030350284d028411980f03035068410284d0f8601183302841030010104d1183303001028610104d0307d028410d0330306501041028010804d0d00f030650f84d028410300109841
|5=>0x584d0103505815010410284d2e00b031090e04f0282d010412980f0314905835010410302d0104d05815098410104112813030490c0410104d058170104103001098410104d0804d010360307d0284d028410d033030650f84d0284102809028412b02f010410304d0284d030490c041028090104d0104101015030660f84d02841290172904f0f84d028410f80b0284d030010804d0284114813030710107d
|6=>0x804d030352901705835010410284d2980f031490c07d0104d30843030f50284a0584d0117d2f09f03041028610104d0584d0284d010410307d0284112813030490584d0104102841030010284109841028610104d0e817098410d00b030650f84d0284102885110600307d0104d028410309d02841068090804d0284d29843031490e04d0107d028410804d0e81703061010410104d1484f030710107d02841
|7=>0x118330300112833030490c0410104d028410302d0584d02809010410d0330306501041028010804d010020284d0307d0804d028412984303149090150c0410104d290430682d0284d010410f84d0c0150104d02841290432904f0f84d028410c041028090284d030610104d2f84d2f09f068090284d030410d00f030650f84d02841098410f86002809028410104d30813030f50901701001118270101503001
|8=>0xc0410104d0804d0284d030710107d028410284912817030490c0410104d0a0130302d0584d010410284d0a01336017030bd01066068410284d028090104d030660f84d0284103065028010804d12843030490584d010410104d030660f84d028410f8600284103001098410104d029a12b0730304d0107d02841128330284103049010010984102841010410284d0104d118330300101001098410282e01041
|9=>0x30610c0150104d028c5030490c0410280903049010010804d0284136017030bd010660f84d02841028020804d0a0130302d1182702801030010804d0112903065068410304a010150584d0104102841138430c041028610104d010410309e02841028610104d010150104d1980f030350284d1182703001010150804d1104f01041030720284d0f8090804d02841110600104d0284d02841128130284d03049
|10=>0xd0330306506841010150284d0682c010410104d0284d028410d00f030650f84d02841011e52b07f028410304d010150e87c028410104d0297d2f09f068090284d0304102841010010300102809098410a0130302d0f84f028410284d0302d0584d028090104112817030490100109841030490c0410104d29843031490c809028010804d2900b13841028610104d29043048010280909841290430682d0284d
|11=>0x302d03065068410284d0282d010411980f030350d03301041030650f84d02841030610104d010411980f110630104d0307d028410a0130302d0581501041028090104d0307d0804d0284112827030490c041028090104d3604f030bd0c80b0f84d028412e00b031090e04f0107d02841028411b80f0309d010350284d0104d0284d0302d010410284112827030490584d0280901041011e52b07f028410304d
|12=>0x302d05815010410284d29817031490c8090f84d028410284d010010300102809098412984f031490e04d0107d02841030650f84d0284129833031490f8610284129833031490682d0284d028090284d030490c0410104d0304a0284d0c041028090104d0284d0a0130d033030650f84d0101502841030650f84d068411980f030350284d1980f030350804d0101501001030350804d0284d028620104d0a013
|13=>0x30650f84d02841028410284d11833030010804d28015128430304901001029fe2584d1100b0307d028411484f030710107d028410307d0f84d02841290430c809028012984f031490f861028410104d290172900b0107d02841010410d00f03065028010804d30833030f509017010011484f030710282d010410d00b030650f84d02841010350284d0302d01041028410804d14813030710107d0284109841
|14=>0x68410284d2904f0f861028410104d290432900b0107d0284105815030010284d098410104103065068410284d29817031490e04d0107d028410f8600302d02841010410104d0e04f0e04d0107d028410303502841068090284d01041030650684109841030350284d0107d02841030660104d01041028010804d4180f03059138430286101015030350284d0c0430104d0d03303065068410284d0104d0a84f
|15=>0x101502841029552b02f010410304d0309e02841068090804d0284d0a0130284d030710284d0f8090804d028412584d1100b0307d02841010150284d2f0630104d030412900b2904f028610104d0307d028410d00f0306506841010150284d2584d1100b0307d02841118330300101001098410684105815010410284d30843030f50901701001098410307d0284102841128130304901001098411980f03035
|16=>0x804d0284d1d0410309d01035118330300109841010150e8430284d030610104d03001098410104d01041030650f84d0284101a3105a2f2b017010410304d1180b0284101041020210c07c0104d028410f8090c0150104d02841118330300101001098410584d0284d0302d010410284103001098411180b0284d0282d068090284d0104114813030710107d028411b80f0309d028610104d0d00f030650f84d
|17=>0x309d0284109841028610104d110600104d0804d0284103001028410284d0100109841110630307d0104d028410c80b031490c8090f84d0284101066030710f84d0107d02841030610104d4800f0323d058360284d0e04f0282d0584d01041110630307d0104d028413080b030f5090170c0410104d0a84f0d00b03065028010804d010410104d0284d028410584d1484f030710282d01041028410100103035
|18=>0x309d028610104d2f84d2f09f03041028610104d098410284d0302d028090104129833031490c8090280109841028090682c0284d010412900b0f861028410104d2980b031490f861028410104d0284d0104d030710107d028410f84d0c0150f809028410104d1104f010152980b031490682d0284d010410100202841030350804d0284d2904f0f861028411f0171b8430309d010350284d0e87c028410104d
|19=>0x284d0307d028410584f02809010410282d0a0130302d01041010410984103061028610104d0307d0284109841028610104d11833030010804d010410309e09841028610104d0e87f028410d06303065068410284d0104d06841028090284d030610104d0682c03001010410804d0284d03049028410284d010010984105815010410284d030610104d060390682c010410804d0284d0307105815010411b80f
|20=>0xe81701041028090284103001098410104d098410104d0a0130302d010411484f030710107d02841160091104f0307d0284129017290430f84d02841030720104d0804d0107d02841029552b02f010410304d2984f0314905835010410284d1904f028c51180b03001098410307d0107d028410804d1b80f0309d010350284d011a12b0730304d0107d028412980f031490682d0284d0280903001010410804d
|21=>0x30f50284a0c04112833030490c0410104d30813030f50284a0584d028c51180b030010984103049010010104d0306506841010150284d031490c2610c07e0104d028412f84d2f09f03041028610104d03049010010c80b028010804d0f860010410104d0284d028414180f0305913843010350104d0104111817030010804d0682c0284d010410307d02841068091980f030350284d1191b02862030010104d
|22=>0x9841110630307d0104d02841028090104d028410d00f030650f84d028411982c03035010410284d0c07d0104d02841290430e04d0107d0284136033030bd010660f84d36033030bd010660684129813031490901501001118330107e03001028411b8430309d028610104d030710282d010411980f01001030350804d12817030490c0410104d09841060210f860028410104d0112911817030010804d30813
|23=>0x98412904f01065068410284d1280b030490584d01041030bd0c80b0f84d02841010410c015098410104d0112911817030010804d5204302a8d030620104d0284d0304a0100109841090170c041028090104d01015030350284d0104d508092f0340284d030410e84303061028610104d01151030660f84d0284102a7a4e8412b00b0304d010411980f030350284d0284d010020804d02841030150901701001
|24=>0x284d02aae5504d2f00b030410804d0307d0107d028411280b030490c0410104d5484f02aa10302e010410284d0302d0984101041029c10304a0c0410104d0306501041028010804d031991584d0107e0284109017030490c0410104d2b0730304d0107d02841028010304a01001098411280b030490c0410104d1280b030490584d01041010410309d028610104d0682c010410804d0284d010411183303001
|25=>0x98410e8170c041030610104d0c80b0f84d0307d0284101015030010804d0284105abd03036010410284d0804d0a0130302d010410104157841030360284d0284113843010350284d5680b031d50f84f0284103001090170100109841090170584d0104102841028010302d09841010412904f090150100109841031ed0291d0c0430104d030720804d0107d02841028410284d01001098410302d0581501041
|26=>0xf84d02841030f5090170c0410104d0314a0f861028410104d0284d0984102809010411484f030710107d028410314a0682d0284d01041010410304d01015028410d00f03065068410284d0280103061098410104d012112f0370284d030410c0410f809028410104d0104111817030010804d02ac95404d0302e0104113841028610104d1d0410e817030610104d2904f090150100109841030f50901701001
|27=>0xd00f030650f84d02841031090e04f0107d0284112833030490c0410104d03035068410284d01041030350804d010150284d12833030490584d01041031cd2c84d0282e0104112817030490584d01041031090e04f0107d02841058150304a0584d01041030350284d0107d0284112833030490584d010410304113843028610104d110600307d0104d02841598410f862028410104d02801098410280901041
|28=>0x104103001028010804d0284d03001010150804d0323d05836010410284d030710581509841010410284101015098410104d029c10304a0100109841138430309d028610104d0f809010660f84d0284103001010410804d0284d0303506841010150284d138430c015098410104d3684d030720107d0284112833030490c0410104d12817030490c0410104d0584f010410307d028415b0412b027028090304d
|29=>0x1041030650f84d028410284103001098410104d0104d03065028010804d0c2610c07e0104d02841010412b07f028410304d0284d0e04f0107d02841031090e04f0107d028412f09c03041028610104d1183303001098410104d0284d0307d0804d028410280103001010150804d1480b030710107d028412904f05835010410284d0306506841010150284d030bd0c80b0f84d028410284d0284a0c0410104d
|30=>0x104d028410a0130302d010410284d030710107d02841378410309e028610104d02801098410280901041030650f84d0101502841610150a04f0302d01041010010c80b028010804d0107e030010804d02841138410309d028610104d290430682d0284d010416004d0307e028410316102a4d0584f01041010152b07f028410304d0fa8d03062028410104d04aed0300202809098415c8092b07c028410304d
|31=>0x28411b80f0309d028610104d0101502801098410104d290170c8090f84d0284114813030710282d010410584d05815010410284d0104102801098410104d0282d068090284d010410f8600104d0284d0284105a2d2b017010410304d0284d0104d0107d028410314a0c8090f84d028410309e010350284d028411181703001098410104d0319a1584d0107e02841028c51180b0300109841010410c01709841
|32=>0x98410104d0280103001098410104d03065068410284d0104d030610c041028090104d012112f0370284d030410104109841028610104d0123d05836010410284d0f8090c0150104d028411104f0307d0804d028410c3030307e0104d02841118270300102809098411b8430309d028610104d03035068410284d0104d2b07005815010410304d0284d010410307d028416004d0307e0104d02841013010307e
|33=>0x107d0284102841010410104d02b3e51841030620104d0304113843010350284d0203905834010410284d03035068090804d0284d0107d02841033311c041010360284d0104106841010150284d010152b02f010410304d0e04d0107d028410307d010020804d028411180b030010100109841030f6090170c0410104d0314a0e04d0107d02841160091104f0307d0284114813030710282d010410309e0c015
|34=>0x10350284d0300109841028610104d0280101015098410104d0115103066068410284d6b00b031c9028020804d030230f860028410104d02b52012ed03002098410284a010010804d02841290430c8090f84d02841030390682c0284d010411b8170309d010350284d031ed0291d0c0430104d0c07e03061028410104d0c3450104d2f01703041030660f84d0107d028411d0410e817030610104d290170e04d
|35=>0x3225029310100209841030bd01066068410284d118270300102809098410fa75028412b00b0304d1104f010410307d028410e87f03061028410104d2f09f028610104d06aa92f00b0284d03041012ed0300209841028410309d028610104d0103503065068410284d110600307d0104d028410804d030710107d02841098410c0150104d02841010410f84d01015028410314a13841028610104d068410309d
|36=>0x290430e04d0107d02841030bd010660f84d028410104d0581509841010410284d0302d02809010416f8411980b030350284d12817030490c0410104d028090682c0284d0104112833030490c0410104d12817030490c0410104d01151030660f84d028416e825028092f04f0304112833030490c0410104d290170e04d0107d028411104f0f84d0307d02841028091104f0307d028416d8430122d2b0170304d
|37=>0x28020302d09841010417204d718430302502809030390682c0284d010410316102a4d0584f010412901713841010350284d0e81703061028090104d033321c041010360284d02841090170100109841290430e04d0282d0104112813030490584d01041031090e04f0107d02841010410c80b0f84d02841031991584d0107e028410e04f058150984101041060390682c0284d01041012610c07e0104d02841
|38=>0x104d2904f13841028610104d2b0700107d028410284d0f809028410104d010150304a0584d010411384113843028610104d0307d02841028610104d030210f860028410104d0f84d030720107d028410302d010410f84f028410314913841028610104d0309e01041028610104d02809068410284d0104d0314a0c809028010804d0fa8d03062028410104d01041068410284d0104d0302d02841010410104d
|39=>0x284101041068090804d0284d06aab2f00b0284d030410309d0c041028610104d12833030490100109841128170304901001098411100b0307d0284d028412b0af0f80b028410304d03382011d50f84f028410104103061028610104d128330304901001098410f84d02841010410104d1384302861010410104d0d04f03065028010804d01015030490c0410104d0304a0c041028090104d29043090150c041
|40=>0x104d0107d028410e04f0307d0107d028410307d0107d028410c80b0f84d028410302d0284d010410104d7680b6e8152f04f03041758130324d0584f010410c0170302d010410104d0104d05834010410284d0c809030650f84d028410284d09017010010984109841030090284d0284101015010410f84f0284114813030710107d028410583703035010410284d030010581709841010410104d0f84d01015
|41=>0x1041030350284d0104d0104d06843010150284d011e52b07f028410304d2901705835010410284d0d04f03065068410284d02aa10302e0284d010410c80b06841030350284d032cd0f862028410104d0104d058170984101041290430c809028010804d030210f860028410104d14813030710107d028410305a13843028610104d5404d0302e010410104d0a0130302d01041160091104f0307d0284103072
|42=>0x104d1384302841028610104d01015030660f84d02841028412b02f010410304d7a8330313101002098410684113843010350284d0314913841028610104d0d04f03065028010804d01015010410307d028410284109841028610104d0e87f03061028410104d01041030660f84d0284102aca5404d0302e01041290170e04d0107d028410584d030720282d010410c041030610104d033c9048020280909841
|43=>0x104d0c80b030090f84d02841030710f8090804d0284111817030010804d028410e81703061098410104d1183303001028010804d378410309e028610104d2b16705817010410304d028091980f030350284d032610c07e0104d02841031490f861028410104d010410309e028610104d2904f0f861028410104d031490682d0284d01041290170c07d0104d028410e04f0804d0107d02841030710282d01041
|44=>0xf860028410104d010150307d0804d028410d04f03065068410284d0284d030010804d02841012bd030360284d2900b13841028610104d0e04f0107d028417c813031650282e010411b8430309d028610104d290430e04d0107d0284102841030350804d0284d12813030490c0410104d1b80f0309d028610104d0284d0c041030610104d098410f860028410104d12813030490c0410104d030490c04102861
|45=>0x104d032260293101002098410303513843010350284d0302d0682d0284d01041031490c8090f84d02841022bd03036010410284d0309e068090804d0284d138430c041028610104d058150a0130302d010410682d0284d010410284d11817030010804d0104d030660f84d028410303b0682c0284d01041028410284d0104d2b07305815010410304d2901701065068410284d0107d2b07f028410304d06021
|46=>0x1015028410c3470104d2f01703041030650280101001098410e84303061010410104d2f09f03041028610104d0f861028410104d03049010010804d028411281303049010010984103326013c1068430284d1484f030710282d0104112813030490100109841028410304a0584d010412b0700304d0107d02841033fd011c9028020804d29017010650f84d028410106606841010150284d0282e0306101041
|47=>0x2f0370284d030412901705835010410284d29043010650f84d02841048010300102809098410a0370302d0284d0104129043090150100109841030150284a0c0410104d8184f030ad0107e028410104d0804d028410284a0584d030150104111817030010100109841011e52b07f028410304d3684d030720282d010411100b010410307d02841718030302502809098410584d0a0130302d01041010660f84d
|48=>0x104d03066028010804d0c0410c0150104d028410280901001028010804d02a8d03062028410104d032450682e0284d010414884d0682e0284d010411982f03035010410284d718030302502809098412904f0f861028410104d290170c07d0104d028410684105815010410284d0314913841028610104d010410104d0284d028410284d030490c0410104d0284d0304a0c0410104d05835010410284d06809
|49=>0x284102802098410104d1183303001028090984102841068090284d01041018210f860028410104d031090e04f0282d010411b8170309d010350284d11833030010280909841718000302502809098412900b0e04d0107d0284102aed03002010150804d05abf03036010410284d0f86002809028410104d0e04f0304d0107d02841010411980f030350284d031490c809028010804d0302d0282d010410104d
|50=>0x104d028410a04f0302d010411980f030350284d1980b030350284d0682e0284d010410e817030610104d0c8090f84d028410284d0804d028410309d028610104d1180b03001098410302d0284d010410c80b028010804d0c041028610104d033c1068430284d03049010010984101041028610104d2b02f010410304d0304901001098411104f0307d028410304d0107d02841028410584f010410307d01015
|51=>0xf861028410104d0f8090804d028412b07c028410304d0301509841010410c809028010804d0e04f0282d0104101066068410284d1180b03001098410282d010410104d010010804d02841010410284d0284103041028090104d0302d0280901041013452f017030410e04d0107d0284113843028610104d0682d0284d010416e8152f04f03041030ad0107e028412b027028090304d2f0630104d030410c015
|52=>0x98411980f030350284d010020804d0284d01065068410284d0304d0107d028410309d010350284d030090284d02841010010804d02841030010280909841010010804d0284d0309d028610104d068090284d010410313101002098411100b0307d028417184f03025010150291d0c0430104d010660f84d028410680b0804d0284d5504d2f00b0304113841028610104d0304a0c0410104d0304a0c0410104d
|53=>0x104d02841030720282d0104102aa92f00b03041011c9028020804d0284d010010984103062028410104d03061098410104d0284d0c0430104d02aa10302e010412f0370284d030410282e010410104d03015098410104d013c1068430284d010650f84d028410302d09841010410107e0284d028410c809028010804d6884d2f017030410104d0284d028410984102809010410304a01001098410302502809
|54=>0xf84d0307d0284123041028620104d0e843030610104d0302d01041028410c07d0104d028410284d030610104d030350284d028410282d0584d0104101015098410104d0f860028410104d028092f04f0304105835010410284d0300109841010410e04d0107d028410302e0284d010410e04f0107d0284101015010410304d2f0630104d0304102841028610104d01001028010804d0300102809098410307d
|55=>0x104102a8d030620104d012ed0300209841030660f84d02841030710282d010410f862028410104d090170c0410104d030720107d02841090170c0410104d031650282e0104103066068410284d0307d0104d028410104d0284d0304103001098410104d0c0170104d0304105836010410284d6e8092f04f0304103061028610104d010410101502841028412b00b0304d0309d028610104d0309e028610104d
|56=>0xf84d028411c041010360284d030090f84d028410584f03015010411183303001098410c041028090104d0584d02809010410f80b0804d028410104d0804d0284151841030620104d2f0340284d030410f84d0101502841010410804d0284d06809030350284d030150c0410104d030650f84d0284104802028090984103061010410104d0e04f0107d028410584d03015010410309e028610104d01aa10302e
|57=>0x302d0284d0104106841030350284d0682c0284d010410301501002098410311d0c0430104d010410f84d028410107d0284d0284157841030360284d0584f028090104103009028010804d068410284d0104111833030010984109841028610104d030490c0410104d058150984101041030490c0410104d030490584d01041030490584d010410c07e0104d02841068090284d0304102809028010804d03065
|58=>0x10410104d2b0170304d03025028090302e010410282d0104101015030412f04f03041030350284d030620104d0284d030410300109841028610104d0107e028412f017030412b017010410304d0680b0284d030410f84f010150284102809028410104d0f84d0104d028410e04d0282d01041068410284d0104d0284d0280901041030020280909841030150c0430104d03001028010804d0309d028610104d
|59=>0x301502809098410104d010410304d030010984101041028410302d0104109841030150280909841028090104d02809010410300209841030610104d0107d02841030150104d03015010410307d028410c0430104d0100209841028410104d028010804d0284d010410584f010410f84d028410804d0284d028410304d0282e010410804d028410c0410104d0584d01041
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0xcf40cb40c7400000c2500000be40b950b630b060ac400000a840a620a2409e409b300000965090608b50865082407d50000079400000754070506c4067500000634000005f4059605540505000004c404750000000000000416000003c5000003750316000002d40294023601f401a50155013200e50095004500000004
|7,1=>0x116411150000000010d410b210651024100200000fc400000f750f5200000ef60eb40e740e34000000000df400000db40d74000000000d34
|8,0=>0x1fe41fa400001f5500001f05000000001eb51e651e2400001de41da41d551d051cc41c751c3400001bf41ba51b6400001b241ad51a851a3519e519c21984193518e5189518450000180417b500001765172416d516941645000015f515b41565151514c51484143513f413c3137513340000000012f412b41274123411f411a5
|8,1=>0x2ce52c952c452c042bb500002b650000000000002b2400002ae42aa400002a552a0529c4297500002934290328b5287428340000280327d327a327552705000026c4268426530000260525c42575252524e424c200002475243423e523952345230422e222952245221300000000000021e321950000214520f520a520642024
|8,2=>0x39923945000038f538b4000038653815000037d4378537440000000036f536b400003683000000003653360535c43575353434f4000034b434650000341533c53375332532d532a332640000322431d531853162311530f230b43083303500002ff42fc32f842f35000000002f1200002ef22eb42e742e252dd52d8500002d35
|8,3=>0x43830000000000004335431242c50000427542520000420541c4000000004184000000004135000000004112000040f240b440740000403400003fe500003fa43f553f323ee500003ea43e553e143df200003da53d643d243ce43c953c723c250000000000003be400003ba43b643b153ae3000000003a953a4500003a0439b5
|8,4=>0x512350d5508550444ff5000000004fa54f644f15000000004ec54e934e454e224dd54d854d354ce5000000004c954c454c224bd54b854b354af4000000004aa54a644a1549c549754952490548b54883000000004844480447b54774472546e4469546450000462245e4000045a4456400000000451544c54484443543e543b3
|8,5=>0x5a945a5400005a1459d4599459545923000058e458a40000585500000000581457d457945754571456f256a50000000056550000560555b5556555240000000054d5000054855444540453e253955345530452c45284523551f451a55155
|9,0=>0x6a646a2469e469a46964692468e468b36874683467f467b46774673466f466b46674663465f465b46574653464f464b46474643463f463b46374633462f462b46274623461f461b46174613460f460b4607460345ff45fb45f745f345ef45eb45e745e345df45db45d745d345cf45cb45c745c345bf45bb45b835b445b045ad3
|9,1=>0x7a3479f479b479747943790478c478847844780477c477847744770476c476847644760475c475847544750474c474847444740473c473847344730472c472847244720471c471847144710470c47084704470046fc46f846f446f046ec46e846e446e046dc46d846d446d046cc46c846c446c046be26ba46b646b246ae46aa4
|9,2=>0x89e489a48964892488e488a48864882487e487b38774873486f486b486928654861485d485a38564852484e484a48464842483e483a48364832482e482a48264822481e481a48164812480e480a4806480247ff37fb47f747f347ef47eb47e747e347df47db47d747d347cf47cb47c747c347bf47bb47b747b347af47ab47a74
|9,3=>0x99c499849944990498c498849844980497c497849744970496c496849644960495c495849544950494c494849444940493c493849344930492c492849244920491c491849144910490c49084904490048fc48f848f448f048ec48e848e538e148de38da48d648d248ce48ca48c648c248be48ba48b648b248ae48aa48a648a24
|9,4=>0xa974a934a8f4a8b4a874a843a804a7c4a784a744a704a6c4a684a644a604a5c4a584a544a504a4c4a493a454a414a3d4a394a363a333a2f4a2b4a274a234a1f4a1b4a174a134a0f4a0b4a074a0349ff49fb49f749f349ef49eb49e749e349df49db49d749d349cf49cb49c749c349bf49bb49b839b449b049ac49a849a449a04
|9,5=>0xb934b8f4b8b4b874b834b7f4b7b4b774b734b6f4b6b4b674b634b5f4b5c3b584b544b504b4d3b494b454b414b3d4b394b354b314b2e3b2a4b273b234b1f4b1b4b174b134b0f4b0b4b074b034aff4afb4af74af34aef4aeb4ae74ae34adf4adb4ad74ad34acf4acb4ac74ac34abf4abb4ab74ab34aaf4aab4aa74aa34a9f4a9b4
|9,6=>0xc784c744c704c6c4c684c644c604c5c4c584c544c504c4c4c484c444c404c3c4c384c344c304c2c4c284c244c204c1c4c184c144c104c0c4c084c044c013bfd4bf94bf54bf14bed4be94be54be14bde3bda4bd64bd24bce4bca4bc64bc24bbe4bba4bb64bb24bae4bab3ba74ba34b9f4b9b4b974
|10,0=>0xd393d363d333d303d2d3d2a3d273d243d213d1e3d1b3d183d153d123d0f3d0c3d093d063d033d003cfd3cfa3cf73cf43cf13cee3ceb3ce83ce53ce23cdf3cdc3cd93cd63cd33cd03ccd3cca3cc73cc43cc13cbe3cbb3cb83cb53cb23caf3cac3ca93ca63ca33ca03c9d3c9a3c973c943c913c8e3c8b3c883c853c823c7f3c7c3
|10,1=>0xdf93df63df33df03ded3dea3de73de43de13dde3ddb3dd83dd53dd23dcf3dcc3dc93dc63dc33dc03dbd3dba3db73db43db13dae3dab3da83da53da23d9f3d9c3d993d963d933d903d8d3d8a3d873d843d813d7e3d7b3d783d753d723d6f3d6c3d693d663d633d603d5d3d5a3d573d543d513d4e3d4b3d483d453d423d3f3d3c3
|10,2=>0xea13e9e3e9b3e983e953e923e8f3e8c3e893e863e833e803e7d3e7a3e773e743e713e6e3e6b3e683e653e623e5f3e5c3e593e563e533e503e4d3e4a3e473e443e413e3e3e3b3e383e353e323e2f3e2c3e293e263e233e203e1d3e1a3e173e143e113e0e3e0b3e083e053e023dff3dfc3
|11,0=>0xef22ef02eee2eec2eea2ee82ee62ee42ee22ee02ede2edc2eda2ed82ed62ed42ed22ed02ece2ecc2eca2ec82ec62ec42ec22ec02ebe2ebc2eba2eb82eb62eb42eb22eb02eae2eac2eaa2ea82ea62ea42
|12,0=>0xef91ef81ef71ef61ef51ef41
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 16
def pmP:Nat→Nat
|0=>0x1a4000000000344000000000600000000000b200000000016200000000028800000000050000000000092000000000120000000000208000000000408000000000800000000000e40000000001880000000003000000000005000000000008400000000010400000000020000000000032000000000060000000000084000000000100000000000120000000000220000000000400000000000400000000000600000000000600000000000800000000000800000000000
|1=>0x816e0000000102d4000000020488000000040320000000080620000000100a00000000201100000000401800000000802a0000000100280000000200280000000400200000000712000000000e1400000000107c0000000020500000000040200000000063d400000000c540000000010c800000000218000000000414000000000810000000001002000000002000000000002020000000004000000000006020000000002040000000003a0000000000710000000000d8
|2=>0x281fe0000000503f40000000a07c8000000140f700000002816a0000000420e00000000807e800000010050000000020020000000040028000000040280000000078f700000000e1fe00000001c3dc0000000384f8000000068ff00000000d16a0000000183fc0000000307b8000000060b500000000b1ee0000000143fc0000000287b8000000050f50000000091fe0000000123f40000000247b8000000042f70000000081fe0000000103dc0000000207a8000000040d2
|3=>0x8802a000000104008000000208000000000400800000000800a20000001000480000002000100000004000000000004810a000000084100000000100708000000200c40000000401280000000802080000001004000000002004300000004008000000005e3f40000000bc7b8000000178b700000002e1fe00000005c3dc0000000b07b8000000160f500000002c16a0000000563fc0000000a87f8000000150f70000000291fe0000000523dc0000000a47a8000000148b5
|4=>0x30806200000060020c000000a001d0000001400120000002081ee000000410228000000820050000001010020000002001040000004000c000000080010000000100010000000200010000000400000000000600610000000a00f2000000140086000000280100000000480080000000840910000001080a20000002100c40000004200a80000008401300000010802400000020014c0000004002180000008004100000010002600000020004800000040008800000080010
|5=>0x1000084000002000020000002380580000004600a40000008c01400000011102900000022105800000044080600000088018c000001100280000002100620000004200a400000084010c0000010402000000020205200000040403400000080804c0000010080800000020040700000040080600000080014c000001000210000002000410000004000800000008000ec0000010000c8000002000120000004000200000006000000000008000e800000100004000000200000
|6=>0x202000000000400002000000800000000000e0001000000188014c0000030041c000000600403000000c0004600000180006c0000030000c00000058005c000000b00078000001400000000002410128000004820190000009000fa00000120017000000221024800000440019000000840016000001040144000002080258000004080010000008040f70000010081440000020101900000040202880000080404a00000100808a0000020100c400000402005000000801000
|7=>0x800c1ee0000100183d40000200307880000400609f00000800b1fe0000100160fc0000200287f8000040050f700000800a1e20000100123fc0000200247b8000040040ff0000080081fa0000100103dc000020020788000040010380000080001fa0000100003c0000020000640000040000c00000080001200000100000000000100207b800002000022000004000040000004c00040000008a005800000114007000000220000000000410000000000808059000001010072
|8=>0x2000f1ee00004001c754000080034ea8000100060f700002000a1ee0000400123dc0000800207b8000100000ff00000830000600001005e3f40000200bc7b8000040170ff00000802d1fe0000100583fc0000200b07b8000040158ff00000802b1ee0000100543fc0000200a87b80000401503f0000080291ee00001004828000002008c0000000401009800000800f1fe00001001e3f400002003c7b80000400787700000800e1fe00001001a3fc0000200347b8000040060ff
|9=>0x10000800400020000624c00040000c298000800010220001000010440002000002c80004000004800008000008a00010000010400020000020000040000028000080000043000100000084000200000098000400000118000800000220001000000400002000000480004000000800008000000600010000000400020000000400020400000000040001000000080000000000088000200000110000180000220000100000400081ee0000700483dc0000c0010728000100460f7
|10=>0x1008081ee000201010018000402000030000802058d70001004081ae00020081000c000400a387b8000801458f700010028a1ee0002004503dc0004008247b8000801040f70001002001240002002103dc000400420098000800440f700010008012400020010014c000400200090000800148ff0001000281ee0002000422e80004000307b8000800050ff00010000a1ee0002000123fc0004000247b8000800040ff0001000081ee00020001009800040002009800080004007
|11=>0x1080040c60002100041e80004200001d8000840000120001050081ee0002088103dc0004104207b8000820040f700010380f0ac00020411635c0004082085f8000810040b30001020000060002031523dc0004062347b800080c448ff0001018811ec0002030143dc0004058307b800080a160e700010120e1ee00020241a3dc0004048307d0000809060f70001010081fe0002020103dc00040400029800080800043000100c8f12c00020141e2580004022307b8000804200b6
|12=>0x2040000800004080000c00008000207b80010000002000020000002000031001818c0006040b0738000c08148770001800081ce00030001038c000600020018000c000087f00014500a1ee0002830103dc0005040207b8000a04040f70001400481ee0002800103dc000421830718000841450f70001081c20760002102943fc0004204b07b8000840850ff0001080ac1ee0002101503dc000420290590000840160f700010800a1fe0002100143dc0004200207b8000840020a3
|13=>0x50000804c000a0000e2c800140001c39000280000082000500000024000902000368001204000680002408000320004800000000008020043c80010040004d00020080009200040100008400080060020c001000c002d8002000200940004000401200008000400080010000201880020000100000040000010000080000018400100000011800200000022000400000020000800000008000d00000400001820000100003020081ee0006000103dc0009000207b800102000060
|14=>0x21018081ee0042020103dc0084000207b8010200040f70020400000400040080103dc008010000100010000040f70020000000240040000000400040000109b8008000000f700080000426e0010000003dc0016040a07b8002850a103b0005083281ee000a106103fc001420c207b8002808140ff0005010281ee000a020403c80014005287b8002800248f70005000201e4000a0001c3dc0014000347b8002800060f700050000a1ee000a000123dc0014000207b800280004032
|15=>0x400000211620800000403f41000000047e8200000000810300000291f60408000123dc0800002a43a8100000468d502000008c1ee040000116354080000224688100000148ff02000000f1ee0400000103dc0800000207980c0000048b30044080081ee0088100102f40110200205e0022000050f70040080081ee0080000503dc0100000207b8020000040f60023000000600046000000800088000207b8011000000500022000000600042920103dc008500000180010810040f7
|16=>0x10000802d1fe20001005a3dc4000200b07f8800040160f71000080201622000100401c44000200207b88000400207110000002c1622000000482c4400000000088600040108b80c000002f1fe18000000004420040003c7b8400040078f708000002f1ee10000001e3fc20000003c7b8400000068b508000000c1ee1000000163d42000000287b8400000040f708000000616210000000a2c4200000000108200040148ff04000002d1fe0800000563fc1000000a47f8200000108b5
|17=>0x3c00000221f060001004a1c0c000200247b9800000118a0300000000042500010042240a0002003c7f9400000040f728000000002248001000a0e09000000981c1000840050ff2001000000844000100543fc80002002c7f9000040040f72000080021e24000100001e48000000287b9000000040f72000000020f230001005e3dc6000200905c0c00000060ff18000000010228001004c2c05000000a87b8a00000118b81400000000422002000000484000200b87f8800040170f7
|18=>0x104000001e3cd000000060799e00040008f8
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x181d000000342705c06014000240002c05000340500d01800000060000603400000060000603414000190000602c0508c090002609c06024050000b0900207409008000240002419024290000d000140100d0bc00024550000000023000190000b0d0000341402c1400802094170080b00009
|8,0=>0x74ac045d605c0043000000000180066c790000a0e806294002900905402008000180d018af0400001806024000300203ded24db70001c6980b2cd2a0242505c0801800000003780800040054190a00905009000ab00017000001c801008000a8060480a01851050002f80302400018076a00b310e22000f1d401394a02a0222801d024ab02487000a90199e2c00801839050090040900000018760348e03485
|8,1=>0x140000000274a12200002ca3001f00ac00000093740029400000a1000d33b0140000d00010000e7070252d00023525035280001715c093ac194a01949c0037406000020509a018000000129c00008842849e0001c0180020c0b000064841400000160a800006000000500705017050710008036000064aa0043a4a80601800018af03025040a1018056a400034060500b0000037c003a8c0050560652d00136
|8,2=>0x202400024140506f05000024a4001d3000002b806024060bcdf0ec000003500007010fa02400000cf000130340d38c367d4712c8060599c0283005011054060d8000008205012001272fc0503c7d02c7a100b10000025dd54a01d038ad05000000fc008072cc204a4071c006000000500223c020f1ac01004000df01800008c0000004bc10424016a409
|9,0=>0x828c74d21249143791e57689b228d122e3878c5d50c42479cb0e1943c43d50cfd0f09950c731ad38591fd344863f93c0c8d63349b7a92c46c816c43357896581ab6c91a50d43105131e1424b9022ed2e531eb270c80b4d57712b36a072e8e053cc1691f86885e50dc01a0cc13173058542a8e90613d760d950c8c50dbf3a1a756d3e23cff4761856d513e4b9760130b9ce3c8e1888e93b9126f1b66b90a50e3c
|9,1=>0x35cc303d124dde6454db3299d50d5d8b97550c617fc332f06765468750417f09f18cb83a4a63d11f50d3c48d190799a6e9d8568c2340e96e1e54cce97648f315c72cd14449431ecd24513b50c3f3a44f854415d1434b8dc1f1d87f07e67530904862494344da04accb571434dd237e8130f03b049e141c3e0b199109da240864e9b4639263c1148545a1b9153b4f8399104b81f351433a46c7e4b58cd1322d23
|9,2=>0x313a50e1b1649150d654b07f7c413831fb8d98d0203f261d786939749b56596867e2b4ddf250e00735f37b012149f2319432d16c3912250c427b92e0dc218dc8988c601d0f30219e4661750197731147980848dfe2540950d173e49b8ed7f7754e50d0489d437c94376df62f41654c14534b848df22dcf8504f7540667d1313391441d816a8332d9b9109430492045446600af06a058bd374401206db310494
|9,3=>0xc510111b05f51850dfc77442129307a0772ac134191677532105a46944816d0850d0f2bc0c8e9353c6164fddc819bb50cc96eca279d7c661a1908ef51dad5d8c88d4af0cd436bdf7
|10,0=>0x5e14b72049835438215f605ca6096b51cf26498318d5650e346120968d728958c73e1314c4959e3d5aa24606015196643a2a5a5475157b82e1052d593e1dd7884b71a3089971436287790d14149525ef4023e5298b61a0f511057263150dd163e2d871015ec42845438fe0326dc58a6018716d8086d42d485c1df8062c9019150d5464e32641e95e4f57821c4458a5e98187239549633ed54585d15310b73053
|10,1=>0x5558117c6588614880f6511c3611d05bd893c9c450e1e811a211d8587d1c40d7780d6e589551917e87543865877091983a0e1a86b688f244902621bd6244d562016f9477a5dd
|11,0=>0x50c6250dc41384a11d4355e0170dc250c4913464870f5115113fd4b114698360d12d5450d4380544599cd50d815a0f917166
|12,0=>0x704431344911543
|13,0=>0x42
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 10 (j%128);fld (pmP (k/32)) 47 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_253 12 roots_253 ops++addP pm 1 dom_223 11 roots_223 ops++addP pm 2 dom_247 12 roots_247 ops++addP pm 3 dom_238 9 roots_238 ops++addP pm 4 dom_254 11 roots_254 ops++addP pm 5 dom_239 11 roots_239 ops++addP pm 6 dom_127 11 roots_127 ops++addP pm 7 dom_191 11 roots_191 ops++addP pm 8 dom_250 10 roots_250 ops++addP pm 9 dom_109 7 roots_109 ops++addP pm 10 dzo_173_2 6 roots_173 ops++addP pm 11 dom_126 8 roots_126 ops++addP pm 12 dom_190 8 roots_190 ops++addP pm 13 dom_63 8 roots_63 ops++addP pm 14 dom_251 12 roots_251 ops++addP pm 15 dzo_118_8 6 roots_118 ops++addP pm 16 dom_111 8 roots_111 ops++addP pm 17 dom_206 6 roots_206 ops++addP pm 18 dom_222 9 roots_222 ops++addP pm 19 dom_141 5 roots_141 ops++addP pm 20 dom_159 8 roots_159 ops++addP pm 21 dom_27 4 roots_27 ops++addP pm 22 dom_86 5 roots_86 ops++addP pm 23 dom_95 8 roots_95 ops++addP pm 24 dom_158 5 roots_158 ops++addP pm 25 dzo_222_32 7 roots_222 ops++addP pm 26 dom_175 8 roots_175 ops++addP pm 27 dom_235 10 roots_235 ops++addP pm 28 dzo_219_32 9 roots_219 ops++addP pm 29 dzo_159_32 7 roots_159 ops++addP pm 30 dom_79 5 roots_79 ops++addP pm 31 dzo_223_32 10 roots_223 ops++addP pm 32 dzo_95_32 7 roots_95 ops++addP pm 33 dom_207 9 roots_207 ops++addP pm 34 dom_186 7 roots_186 ops++addP pm 35 dom_171 7 roots_171 ops++addP pm 36 dzo_207_32 7 roots_207 ops++addP pm 37 dzo_221_32 9 roots_221 ops++addP pm 38 dom_182 7 roots_182 ops++addP pm 39 dom_231 9 roots_231 ops++addP pm 40 dzo_215_32 9 roots_215 ops++addP pm 41 dom_110 5 roots_110 ops++addP pm 42 dom_62 5 roots_62 ops++addP pm 43 dom_47 5 roots_47 ops++addP pm 44 dom_174 5 roots_174 ops++addP pm 45 dom_118 6 roots_118 ops++addP pm 46 dom_183 9 roots_183 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_173_2_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_118_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_222_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_219_32_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_159_32_145 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_223_32_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_95_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_207_32_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_221_32_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_215_32_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_183 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_253 12 s (0,roots_253.map (·&&&dom_253)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_253 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 92 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 92 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 367 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 111 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 367 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 256 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_256 : ∀ i, 256 ≤ i → i < 384 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_384 : ∀ i, 384 ≤ i → i < 442 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 58 384 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 442 → Z 9 i = true := (range_split (range_split z9_0 z9_128) (range_split z9_256 z9_384))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 184 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 56 128 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 184 → Z 10 i = true := (range_split z10_0 z10_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 40 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 40 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 6 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 6 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [7, 0] }, { op := GateOp.or, inputs := [4, 0] }, { op := GateOp.or, inputs := [9, 2] }, { op := GateOp.or, inputs := [7, 6] }, { op := GateOp.or, inputs := [6, 4] }, { op := GateOp.or, inputs := [3, 1] }, { op := GateOp.or, inputs := [2, 13] }, { op := GateOp.or, inputs := [1, 8] }, { op := GateOp.and, inputs := [10, 11] }, { op := GateOp.and, inputs := [12, 15] }, { op := GateOp.and, inputs := [5, 14] }, { op := GateOp.and, inputs := [3, 8] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52232_aux

theorem PEqualNP.Outside.L_meta_52232 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52232_aux.main
