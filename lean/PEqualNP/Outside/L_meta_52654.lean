import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52654_aux
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
def goal_27 : Nat := 0xffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_41 : Nat := 0x30300000303
def goal_41 : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_41 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfffafffaaa00aa00fffafffaaa00aa00fffafffaaa00aa00fffafffaaa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

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
def goal_57 : Nat := 0xffaaffaaffaaaa00ffaaffaaffaaaa00ffaaffaaffaaaa00ffaaffaaffaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccff00ffcc0000ffccff00ffcc0000ffccff00ffcc0000ffccff00ffcc0000
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffaaffeeaa00ffeeffaaffeeaa00ffeeffaaffeeaa00ffeeffaaffeeaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_60 : Nat := 0x1111111111111111
def goal_60 : Nat := 0xfff0fff0ff000000fff0fff0ff000000fff0fff0ff000000fff0fff0ff000000
def roots_60 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafffaffaaaa00fffafffaffaaaa00fffafffaffaaaa00fffafffaffaaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcfff0ffcc0000fffcfff0ffcc0000fffcfff0ffcc0000fffcfff0ffcc0000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefffaffeeaa00fffefffaffeeaa00fffefffaffeeaa00fffefffaffeeaa00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffeeffeeffeeffeeaa00aa00aa00aa00ffeeffeeffeeffeeaa00aa00aa00aa00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

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

def dom_88 : Nat := 0x10101010000000001010101
def goal_88 : Nat := 0xffffff00ffffff00ff000000ff000000ffffff00ffffff00ff000000ff000000
def roots_88 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffffaaffffffaaffaaaa00ffaaaa00ffffffaaffffffaaffaaaa00ffaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffffccffffffccffcc0000ffcc0000ffffffccffffffccffcc0000ffcc0000
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffeeffffffeeffeeaa00ffeeaa00ffffffeeffffffeeffeeaa00ffeeaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffffafffffffaffaaaa00ffaaaa00fffffffafffffffaffaaaa00ffaaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffffefffffffeffeeaa00ffeeaa00fffffffefffffffeffeeaa00ffeeaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xeeeeeeeeeeeeeeeeaaaaaaaa00000000eeeeeeeeeeeeeeeeaaaaaaaa00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfcfcfcfcfcfcfcfcf0f0f0f000000000fcfcfcfcfcfcfcfcf0f0f0f000000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefefefefefefafafafa00000000fefefefefefefefefafafafa00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffaaffaaffaaffaaffaaffaaaa00aa00ffaaffaaffaaffaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccffccffccff00ff0000000000ffccffccffccffccff00ff0000000000
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeffeeffeeffaaffaaaa00aa00ffeeffeeffeeffeeffaaffaaaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffafffafffafffafffaaa00aa00fffafffafffafffafffafffaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfffcfffcfff0fff000000000fffcfffcfffcfffcfff0fff000000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefffefffefffafffaaa00aa00fffefffefffefffefffafffaaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffaaaaffffaaaaaaaaaaaaaaaa0000ffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffeeeeeeeeaaaaeeee0000ffffeeeeffffeeeeeeeeaaaaeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffff0f0fffff0f0f0f0f0f000000000fffff0f0fffff0f0f0f0f0f000000000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafafffffafafafafafaaaaa0000fffffafafffffafafafafafaaaaa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcfffffcfcfcfcf0f0cccc0000fffffcfcfffffcfcfcfcf0f0cccc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefefffffefefefefafaeeee0000fffffefefffffefefefefafaeeee0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffff00ffffff00ff00ff00ff000000ffffff00ffffff00ff00ff00ff000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffffaaffaaffaaffaaaa00ffffffaaffffffaaffaaffaaffaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffffccffccff00ffcc0000ffffffccffffffccffccff00ffcc0000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffffeeffeeffaaffeeaa00ffffffeeffffffeeffeeffaaffeeaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0fffffff0fff0fff0ff000000fffffff0fffffff0fff0fff0ff000000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffffafffafffaffaaaa00fffffffafffffffafffafffaffaaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcfffffffcfffcfff0ffcc0000fffffffcfffffffcfffcfff0ffcc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffffefffefffaffeeaa00fffffffefffffffefffefffaffeeaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeaa00aa00aa00aa00aa00aa00aa00aa00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_146 : Nat := 0x5000500000000000000000000000000050005
def goal_146 : Nat := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000eeee0000eeee0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffaaaa00ffaaaa00ffaaaa00ffaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffccffcc0000ffcc0000ffcc0000ffcc0000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffeeaa00ffeeaa00ffeeaa00ffeeaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffaffaaaa00ffaaaa00ffaaaa00ffaaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffefffffffefffffffefffffffeffeeaa00ffeeaa00ffeeaa00ffeeaa00
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

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffafffafffafffafffafffafffafffafffafffaaa00aa00fffafffaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcfff0fff000000000fff0fff000000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffefffefffefffefffefffefffefffefffafffaaa00aa00fffafffaaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

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
def goal_185 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffaaffaaffaaaa00ffaaffaaffaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fff0fff0ff000000fff0fff0ff000000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffafffffffafffffffafffffffafffafffaffaaaa00fffafffaffaaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfffcfff0ffcc0000fffcfff0ffcc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffefffffffefffffffefffffffefffefffaffeeaa00fffefffaffeeaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_194 : Nat := 0x5000000000000000500000000000000050000000000000005
def goal_194 : Nat := 0xffffffffffffffffcccccccccccccccccccccccccccccccc0000000000000000
def roots_194 : List Nat := [xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffffccffccffccffccffccffccffccffcc0000000000000000
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffffafffafffafffafffafffafffafffaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffefffefffefffefffefffefffefffeaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_208 : Nat := 0x10001000000000001000100000000000100010000000000010001
def goal_208 : Nat := 0xffffffffffffffffffff0000ffff0000ffff0000ffff00000000000000000000
def roots_208 : List Nat := [xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffffffccccffffccccffffccccffffcccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f00000000000000000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffffafafffffafafffffafafffffafaaaaa0000aaaa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffffcfcfffffcfccccc0000cccc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffefefffffefefffffefefffffefeeeee0000eeee0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff00ff000000ff000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaffaaaa00ffaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffffccffffffccffffffccffffffccffcc0000ffcc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffeeffffffeeffffffeeffffffeeffeeaa00ffeeaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0ff000000ff000000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffffafffffffafffffffafffffffaffaaaa00ffaaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffffcfffffffcfffffffcfffffffcffcc0000ffcc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffefffffffefffffffefffffffeffeeaa00ffeeaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaa00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffafafafafafafafafafafafafafafafafafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f000000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffefefefefefefefefefefefefefefefefafafafa00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeffaaffaaaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffafffafffafffafffafffafffafffafffafffaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffcfffcfffcfffcfffcfffcfffcfffcfff0fff000000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffefffefffefffefffefffefffefffefffafffaaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffeeeeffffeeeeeeeeaaaaeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f000000000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffafafffffafafffffafafffffafafafafafaaaaa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffffcfcfffffcfcfcfcf0f0cccc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffefefffffefefffffefefffffefefefefafaeeee0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff00ff00ff00ff000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaffaaffaaffaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffccffffffccffffffccffffffccffccff00ffcc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffeeffffffeeffffffeeffffffeeffeeffaaffeeaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0fff0fff0ff000000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffafffffffafffffffafffffffafffafffaffaaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffcfffffffcfffffffcfffffffcfffcfff0ffcc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffefffffffefffffffefffffffefffefffaffeeaa00
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
def isoMvS_41:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_41:Lower true dom_41 roots_41 goal_41 4:=lower_iso_b isoMvS_41 (by decide +kernel) lowS_25
def isoMvS_73:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_73:Lower true dom_73 roots_73 goal_73 4:=lower_iso_b isoMvS_73 (by decide +kernel) lowS_25
def isoMvS_81:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_25
def isoMvS_82:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_82:Lower true dom_82 roots_82 goal_82 4:=lower_iso_b isoMvS_82 (by decide +kernel) lowS_25
def isoMvS_88:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_88:Lower true dom_88 roots_88 goal_88 4:=lower_iso_b isoMvS_88 (by decide +kernel) lowS_25
def isoMvS_146:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_146:Lower true dom_146 roots_146 goal_146 4:=lower_iso_b isoMvS_146 (by decide +kernel) lowS_25
def isoMvS_194:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_194:Lower true dom_194 roots_194 goal_194 4:=lower_iso_b isoMvS_194 (by decide +kernel) lowS_25
def isoMvS_208:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_208:Lower true dom_208 roots_208 goal_208 4:=lower_iso_b isoMvS_208 (by decide +kernel) lowS_25
theorem lowS_27:Lower true dom_27 roots_27 goal_27 5:=lower_slice_b [(0xc0c0c0c,16,18)] (by decide +kernel) lowS_25
namespace S_51
def pG:List (Nat×Nat):=[(1,17),(1,33),(2,18),(3,19),(3,35),(16,17),(16,18),(32,33),(34,35),(34,50),(48,49),(48,50)]
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
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_slice_b [(0x303000003030000,1,17)] (by decide +kernel) lowS_41
namespace S_89
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(8,9),(8,24),(8,72),(16,17),(16,24),(16,80),(64,65),(64,72),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_89.map (·&&&dom_89)
def gM:=goal_89&&&dom_89
def NN:Nat→Nat
|3=>3
|4=>7
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x922763f74c070e9
|4,0=>0x6ebab310173021e29bbd24a8c18324114e4
|5,0=>0x61e1742a8701a8f
|6,0=>0x1a8f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c0c0c000000000c000c030303000000000003030300c080c08000000000c080c0b03030300000000030203020000c0c00000000000008080000000000000003030300404040000000000040404010101010000000001010100c000c00000000000c00080303000000000000030300008080808000000000808080b0303030000000000000000c0c0808000000000c0c080b0303030000000003030000c000c00000000000c000c030303030000000002020202
|_,_=>0
def sP:Nat→Nat
|0=>0x6154610546d15461546d1046f105e6d546c154615b4a615461594618467543210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x21022004
|4,0=>0xa952aa0536a5948a8c5
|5,0=>0xe159aaf4
|6,0=>0x3d4
|_,_=>0
def wAt:=mkWire dB 16 90 0x3ffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x5454515551145516154564551
|_=>0
def oO:Nat→Nat→Nat
|3,0=>2
|4,0=>0x62422200000000
|5,0=>0x918100
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfc7530
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>1
|4,0=>0x111000
|5,0=>0x16b
|6,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_88 4 roots_88 ops++addP pm 1 dom_73 4 roots_73 ops++addP pm 2 dom_81 4 roots_81 ops++addP pm 3 dom_25 4 roots_25 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_89 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_88 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_25 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_88 4 s (0,roots_88.map (·&&&dom_88)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_89 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_88 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_89==dom_89)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_89 gM v ys):RunD true dom_89 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_89 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_89 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_89 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_89 roots_89 goal_89 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_89
theorem lowS_89:Lower true dom_89 roots_89 goal_89 7:=S_89.noCircuit
def isoMvS_45:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_45:Lower true dom_45 roots_45 goal_45 5:=lower_iso_b isoMvS_45 (by decide +kernel) lowS_27
def isoMvS_53:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_53:Lower true dom_53 roots_53 goal_53 4:=lower_iso_b isoMvS_53 (by decide +kernel) lowS_51
def isoMvS_58:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 4:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_51
def isoMvS_60:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_60:Lower true dom_60 roots_60 goal_60 4:=lower_iso_b isoMvS_60 (by decide +kernel) lowS_51
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_27
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_57
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_27
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_27
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_57
def isoMvS_99:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 4:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_51
def isoMvS_102:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 4:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_51
def isoMvS_105:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_57
def isoMvS_106:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 4:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_51
def isoMvS_113:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_27
def isoMvS_116:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 4:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_51
def isoMvS_120:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 5:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_27
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_27
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_57
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 7:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_89
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_57
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 4:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_51
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 4:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_51
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 4:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_51
def isoMvS_195:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_57
def isoMvS_201:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 7:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_89
def isoMvS_202:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_57
def isoMvS_209:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 7:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_89
def isoMvS_210:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 7:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_89
def isoMvS_216:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 7:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_89
def isoMvS_228:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 5:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_27
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_slice_b [(0xcc00cc00cc00cc,16,18)] (by decide +kernel) lowS_53
def dzo_57_2:=0xc0c0c0c0c0c0c0c
def gzo_57_2:=0xc0c0c080c0c0800
def gsh_57_2:=0x303030203030200
theorem lowS_zo_57_2_41:Lower true dzo_57_2 roots_57 gzo_57_2 5:=lower_iso_b (d1:=dom_57) (r1:=roots_57) (T1:=gsh_57_2) [(dom_57,2)] (by decide +kernel) (lower_slice_b (T:=gsh_57_2) [(0x303000003030000,0,16)] (by decide +kernel) lowS_41)
namespace S_59
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,18),(3,11),(3,19),(3,35),(8,9),(8,24),(8,40),(10,11),(10,26),(10,42),(16,17),(16,18),(16,24),(32,33),(32,40),(34,35),(34,42),(34,50),(48,49),(48,50),(48,56)]
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
|4,0=>0x593ef
|5,0=>0xdeb7
|6,0=>0x9abd7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f00000000f0a0f0a0f0a0f0af0f00000f0f0000f000f000f000f00c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a00000000f0a0f0a
|_,_=>0
def sP:Nat→Nat
|0=>0xd1a3a568c688
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
|0=>0x65
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
addP pm 0 dom_57 5 roots_57 ops++addP pm 1 dom_58 4 roots_58 ops++addP pm 2 dzo_57_2 5 roots_57 ops++addP pm 3 dom_27 5 roots_27 ops++addP pm 4 dom_51 4 roots_51 ops++addP pm 5 dom_41 4 roots_41 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_57_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_41 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_57 5 s (0,roots_57.map (·&&&dom_57)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_59 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_57 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
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
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_slice_b [(0xaa00aa0000000000aa00aa,16,17)] (by decide +kernel) lowS_86
theorem lowS_91:Lower true dom_91 roots_91 goal_91 8:=lower_slice_b [(0xc0c0c0c000000000c0c0c0c,16,18)] (by decide +kernel) lowS_89
theorem lowS_93:Lower true dom_93 roots_93 goal_93 8:=lower_slice_b [(0x303030300000000030303030,64,68)] (by decide +kernel) lowS_89
theorem lowS_103:Lower true dom_103 roots_103 goal_103 5:=lower_slice_b [(0xaa000000aa000000aa000000aa,32,33)] (by decide +kernel) lowS_102
theorem lowS_109:Lower true dom_109 roots_109 goal_109 6:=lower_slice_b [(0x3030000030300000303000003030,32,36)] (by decide +kernel) lowS_105
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_slice_b [(0x300030003000300030003000300030,32,36)] (by decide +kernel) lowS_113
def dzo_86_32:=0x550055000000000055005500000000
def gzo_86_32:=0x550054000000000054005000000000
def gsh_86_32:=0x5500540000000000540050
theorem lowS_zo_86_32_82:Lower true dzo_86_32 roots_86 gzo_86_32 5:=lower_iso_b (d1:=dom_86) (r1:=roots_86) (T1:=gsh_86_32) [(dom_86,32)] (by decide +kernel) (lower_slice_b (T:=gsh_86_32) [(0x5000500000000000500050,0,4)] (by decide +kernel) lowS_82)
namespace S_118
def pG:List (Nat×Nat):=[(2,18),(2,66),(4,36),(4,68),(6,22),(6,38),(6,70),(16,18),(16,80),(20,22),(20,52),(20,84),(32,36),(34,38),(34,50),(34,98),(48,50),(48,52),(48,112),(64,66),(64,68),(64,80),(96,98),(96,100),(96,112)]
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
|4,0=>0xc8ff51ccf5
|5,0=>0xbe094abdd4526d3
|6,0=>0x93d49
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x2a8022002a8022002a8022002a8022550055005500550044004400440044aa000000aa000000aa000000aa0000440044004400440000000000000002a8000002a80000022000000220000550055000000000055005500000000a000a000a000a000a000a000a000a11001100110011001100110011001100002a8000002a8000002200000022550055005500550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x473204973204738204732064325043210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 119 0x7fffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x82
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
addP pm 0 dom_86 5 roots_86 ops++addP pm 1 dom_116 4 roots_116 ops++addP pm 2 dzo_86_32 5 roots_86 ops++addP pm 3 dom_82 4 roots_82 ops++addP pm 4 dom_102 4 roots_102 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_118 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_86_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_102 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_86 5 s (0,roots_86.map (·&&&dom_86)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_118 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_86 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
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
theorem lowS_211:Lower true dom_211 roots_211 goal_211 8:=lower_slice_b [(0xa000a00000000000a000a00000000000a000a00000000000a000a,16,17)] (by decide +kernel) lowS_210
namespace S_217
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(8,9),(8,24),(8,72),(8,136),(16,17),(16,24),(16,80),(16,144),(64,65),(64,72),(64,80),(64,192),(128,129),(128,136),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffff
def xsM:=roots_217.map (·&&&dom_217)
def gM:=goal_217&&&dom_217
def NN:Nat→Nat
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x6e056
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3030000000000000303000000000000030300000000000003030000c000c00000000000c000c00000000000c000c00000000000c000c02020202000000000202020200000000020202020000000002020202c0c0c0c0000000000000000000000000c0c0c0c0000000000000003030303000000000303030300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>5
|_,_=>0
def wAt:=mkWire dB 5 218 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
|8,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_216 7 roots_216 ops++addP pm 1 dom_153 7 roots_153 ops++addP pm 2 dom_209 7 roots_209 ops++addP pm 3 dom_201 7 roots_201 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_217 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_201 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_216 7 s (0,roots_216.map (·&&&dom_216)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_217 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_216 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_217==dom_217)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_217 gM v ys):RunD true dom_217 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_217 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_217 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 4=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_217 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_217 roots_217 goal_217 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_217
theorem lowS_217:Lower true dom_217 roots_217 goal_217 9:=S_217.noCircuit
def isoMvS_61:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 7:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_59
def isoMvS_62:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 5:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_55
def isoMvS_107:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 7:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_59
def isoMvS_110:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 5:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_103
def isoMvS_115:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_59
def isoMvS_121:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 8:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_91
def isoMvS_122:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_59
def isoMvS_124:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 6:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_117
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 8:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_91
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 8:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_93
def isoMvS_167:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 5:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_103
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 6:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_109
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 5:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_103
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_59
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 6:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_117
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 7:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_118
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 6:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_117
def isoMvS_203:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_91
def isoMvS_205:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 8:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_91
def isoMvS_213:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_91
def isoMvS_214:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 8:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_91
def isoMvS_218:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 8:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_211
def isoMvS_227:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 7:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_59
def isoMvS_229:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 6:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_109
def isoMvS_230:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 7:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_59
def isoMvS_233:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_91
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 6:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_109
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 8:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_93
def isoMvS_244:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 7:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_59
def isoMvS_248:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 8:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_93
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xcccccccccccccccc,16,18)] (by decide +kernel) lowS_61
theorem lowS_95:Lower true dom_95 roots_95 goal_95 9:=lower_slice_b [(0xcccccccc00000000cccccccc,16,18)] (by decide +kernel) lowS_93
theorem lowS_111:Lower true dom_111 roots_111 goal_111 8:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f0,32,36)] (by decide +kernel) lowS_107
def dzo_87_32:=0xff00ff0000000000ff00ff00000000
def gzo_87_32:=0xff00fe0000000000fe00fa00000000
def gsh_87_32:=0xff00fe0000000000fe00fa
theorem lowS_zo_87_32_82:Lower true dzo_87_32 roots_87 gzo_87_32 6:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_32) [(dom_87,32)] (by decide +kernel) (lower_slice_b (T:=gsh_87_32) [(0xaa00aa0000000000aa00aa,0,1),(0xf000f00000000000f000f0,0,4)] (by decide +kernel) lowS_82)
namespace S_119
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(2,18),(2,66),(3,19),(3,35),(3,67),(4,36),(4,68),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,23),(7,39),(7,71),(16,17),(16,18),(16,80),(20,21),(20,22),(20,52),(20,84),(32,33),(32,36),(34,35),(34,38),(34,50),(34,98),(48,49),(48,50),(48,52),(48,112),(64,65),(64,66),(64,68),(64,80),(96,97),(96,98),(96,100),(96,112)]
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
|4,0=>0x97c8f8c9da4303f2a218036b2
|5,0=>0xf9d61f3e8df29f6e3448d8193bdc09a7bc38f24b8c0c5770d95ab1958855203ba0ea4b0408e
|6,0=>0xfeae0fd584f90d2f89ecf56aff33b3f3273f1f1ced19eec5c7dc98ddae64c7cebc67edc325bbce6cb67edb3ab4b23e2aaa688f24b8bd488280d73eed6335360a1d5d38a4f8474521843e673eb1e3267c219941845911bd10e08e0d777
|7,0=>0xf2fd6e8d9fc2892be7e06aedf5d38a4ec5b49306093c203cbe
|8,0=>0xdaa04
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00cc00ff00cc00cc00cc00cc00ccff00ff00ff00ff0033000000330000330033003300330000000000000000ff000000ff00000000000000000000ff00aa00ff00aa00aa00aa00aa00aa3300330033003300330000003300000000ff000000ff00ff000000ff0000ff00ff00ff00ff00ff000000ff0000f000f000f000f000f000f000f000f0aa00aa00aa00aa00aa00aa00aa00aa000033000000330033000000330000ff00ff0000000000ff00ff00000000ff000000ff000000ff000000ff0000fe00fe00fe00fe00fe00fa00fe00faee00ee00ee00ee00ee00aa00ee00aaff00ff00ff00ff0000000000000000
|0,1=>0xcc00cc00cc00cc00ff00cc00ff00ccff00000000000000ff00ff00000000000000000000000033000000330000ff00ff00ff000000ff00ff000000000000cc000000cc00cc00cc00cc00cc0000000000000000ff00cc00ff00ccff003300ff003300ff000000ff00003300000033000000330000003300000000000000000000ff000000ff00000000ff000000ff0000000000000000ff00ff00ff00ff00ff00ff00000000ff00cc00ff00cc00ff00cc00ff00ccff00ff00ff00ff00cc00cc00cc00cccc00cc00cc00cc00cc000000cc00000000000000000000ff00ff00000000cc00cc00cc00cc00cc00cc00cc00cc
|0,2=>0xff00f000ff00f000f000f000f000f00000ff0000000000ff00ff00000000cc000000cc000000ff000000ff0000ff00ff00ff00ff00ff00cc00ff00ccff00ff000000ff00ff00ff00000000ff00ff0033003300ff00ff00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1c62801031c66003440c76c60156831d018464719800420719834420740b1091d01950c718a0045081d31840c718a0040c70404431c62801082474061081cf1840c718e3442031c100420718a3042072ca1091c62842471851081c61440c2040
|1=>0x210c74060200c74060047c31d01807831d018011a0c74060040c718a0152031d01801142074060040c73c60045c74065840c74067401080c74060042074063112031d01801031d21807031d01805431d01980150d71d01801145c7406004203
|2=>0x1031d01803440c74d01805431d01801031d01980040c740b0040e54060040c74062809031d01801031d018e0046431d01801038c74060042031d018d5540c74060042031d34061220c74060110d71d01801081d01980042031d21801140c74c6
|3=>0x40c74060040d71d01801031d01805910c74060045031d01801031d01803042031d0180
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a58c6c5d62c294d49ac47620b0f146cc30615a89583ec196
|6,0=>0x15f6acb549e98d4579f3cdde60f297913c6de28f0d7833bfddf2cf36763b999beed96693b2dd8acbf65c3ac5d56ca474f3261922e8a741b9f1ceae6f6
|7,0=>0x344f9b7cab639f0ef807bcbdc9ed8d657
|8,0=>0x1a96
|_,_=>0
def wAt:=mkWire dB 38 120 0xffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3030c084030d043000c0500240044010d0c6310c007310c004330c003370c044010c04301116430210d5002116c302210c3010c050310c003030c083010c00301210030110c430010043030c050330c0030118c43005d643030c0830148648400c050310c04300
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x28c7300061000330000000c0000000
|6,0=>0x2f2b4800ac800002a1a46819c400002610000090a2200202001e2001d16c992000005c9615092244400404f1000d2
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xf5fd3cc301b7e158120277ddb75d09421044090034cd13043407c1c018050100200400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x410050180320060
|6,0=>0x19c0120035a52819418d4b0240171718056cf3a44c10810
|7,0=>0x35b95f7a94e37
|8,0=>0xb
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_118 7 roots_118 ops++addP pm 1 dom_117 6 roots_117 ops++addP pm 2 dom_53 4 roots_53 ops++addP pm 3 dom_85 5 roots_85 ops++addP pm 4 dom_115 7 roots_115 ops++addP pm 5 dom_102 4 roots_102 ops++addP pm 6 dzo_87_32 6 roots_87 ops++addP pm 7 dom_87 6 roots_87 ops++addP pm 8 dom_55 5 roots_55 ops++addP pm 9 dom_103 5 roots_103 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_119 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_87_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_103 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_118 7 s (0,roots_118.map (·&&&dom_118)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_119 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_118 h
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
def dzo_41_2:=0xc0c00000c0c
def gzo_41_2:=0xc0800000800
def gsh_41_2:=0x30200000200
theorem lowS_zo_41_2_41:Lower true dzo_41_2 roots_41 gzo_41_2 4:=lower_iso_b (d1:=dom_41) (r1:=roots_41) (T1:=gsh_41_2) [(dom_41,2)] (by decide +kernel) (lower_slice_b (T:=gsh_41_2) [] (by decide +kernel) lowS_41)
def dzo_82_32:=0x50005000000000005000500000000
def gzo_82_32:=0x50004000000000004000000000000
def gsh_82_32:=0x500040000000000040000
theorem lowS_zo_82_32_82:Lower true dzo_82_32 roots_82 gzo_82_32 4:=lower_iso_b (d1:=dom_82) (r1:=roots_82) (T1:=gsh_82_32) [(dom_82,32)] (by decide +kernel) (lower_slice_b (T:=gsh_82_32) [] (by decide +kernel) lowS_82)
def dzo_121_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_121_2:=0xc0c0c0c0c0c0c0c0c0c0c080c0c0800
def gsh_121_2:=0x3030303030303030303030203030200
theorem lowS_zo_121_2_41:Lower true dzo_121_2 roots_121 gzo_121_2 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_2) [(dom_121,2)] (by decide +kernel) (lower_slice_b (T:=gsh_121_2) [(0x3030000030300000303000003030000,0,16),(0x3030303030303030000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_91_32:=0xf0f0f0f000000000f0f0f0f00000000
def gzo_91_32:=0xf0f0f0e000000000f0e0f0a00000000
def gsh_91_32:=0xf0f0f0e000000000f0e0f0a
theorem lowS_zo_91_32_82:Lower true dzo_91_32 roots_91 gzo_91_32 6:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_32) [(dom_91,32)] (by decide +kernel) (lower_slice_b (T:=gsh_91_32) [(0xa0a0a0a000000000a0a0a0a,0,1),(0xf000f00000000000f000f00,0,8)] (by decide +kernel) lowS_82)
def dzo_90_32:=0x5050505000000000505050500000000
def gzo_90_32:=0x5050504000000000504050000000000
def gsh_90_32:=0x50505040000000005040500
theorem lowS_zo_90_32_82:Lower true dzo_90_32 roots_90 gzo_90_32 5:=lower_iso_b (d1:=dom_90) (r1:=roots_90) (T1:=gsh_90_32) [(dom_90,32)] (by decide +kernel) (lower_slice_b (T:=gsh_90_32) [(0x50005000000000005000500,0,8)] (by decide +kernel) lowS_82)
def dzo_105_2:=0xc0c00000c0c00000c0c00000c0c
def gzo_105_2:=0xc0c00000c0c00000c0800000800
def gsh_105_2:=0x303000003030000030200000200
theorem lowS_zo_105_2_41:Lower true dzo_105_2 roots_105 gzo_105_2 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_2) [(dom_105,2)] (by decide +kernel) (lower_slice_b (T:=gsh_105_2) [(0x303000003030000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_83_32:=0xf000f00000000000f000f00000000
def gzo_83_32:=0xf000e00000000000e000a00000000
def gsh_83_32:=0xf000e00000000000e000a
theorem lowS_zo_83_32_82:Lower true dzo_83_32 roots_83 gzo_83_32 5:=lower_iso_b (d1:=dom_83) (r1:=roots_83) (T1:=gsh_83_32) [(dom_83,32)] (by decide +kernel) (lower_slice_b (T:=gsh_83_32) [(0xa000a00000000000a000a,0,1)] (by decide +kernel) lowS_82)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,18),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,24),(8,40),(8,72),(10,11),(10,26),(10,42),(10,74),(16,17),(16,18),(16,24),(16,80),(32,33),(32,40),(34,35),(34,42),(34,50),(34,98),(48,49),(48,50),(48,56),(48,112),(64,65),(64,66),(64,72),(64,80),(96,97),(96,98),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|4=>3
|5=>12
|6=>20
|7=>13
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x6996d3ae3909076
|5,0=>0xbdbaaaff718bebf7b0d948b2a318ee306f72dd012529417c3c0c79c06627
|6,0=>0x995e694367873e4679a147a784559144d532b37829f432902c1c85c148131420913a971274f0ef98049e7027ee0231801256
|7,0=>0xba0ef789af63b3d4e11a452941c1ad1649115edf14c531489e10db90fa2d0bdcd
|8,0=>0xcdd9247c680e7a1
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0a0f0f0f0a0f0f0f0a0f0f0f0af0f0f000f0f0f000f0f0f000f0f0f005050505050505050500050005000500f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a30303030f0b0f0b030300000f0b0f0af0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f00000f0f0000f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0a0a0f0f0a0a0f000a000f000a00f0f0f0f000000000f0f0f0f00000000f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0af0f0f0f0f0f0f0f0f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f000f0f0f000a0a0a000a0a0a00
|0,1=>0xf0f0f0a0f0f0f0af0f05050f0f05050f0f05000f0f0500f0f0f0f0f0f00000f0f0f0f0f0f0000e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0000000000000000f0f0f000f0f0f0000f000a000f000a000f000a000f000af0f0f0f0f0f0f0f0f0f0a0a0f0f0a0af0f0f0f0f0f0f0f0f0f0f0f00000000303030303030303030300000303000000000000f0a0f0a000000000f0a0f0af0f0f0f0f0f0f0f0f0f00000f0f0f0af0f0f0f0f0f0f0f0f0f0f000f0f0f00f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e00b000b000b000b000b000a000b000af0f0f0f0f0f0f0f0a0a0a0a0a0a0a0ab0b0b0b0b0b0b0b0b0b0a0a0b0b0a0a
|0,2=>0xf0f0f0f0f0f0f0f0f0f0f0a0f0f0f0af0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a000000f0000000f0000000a0000000a00e000e000e000e000e000e000e000ef0f00000f0f0f0a0f0f00000f0f0f0a
|_,_=>0
def sP:Nat→Nat
|0=>0x28810e0cb0512041cc18204a10c2c145a20438c4ca2043992c128860e30204a10e0c205130b29758810e1c605154c2c12881140cb05110c4c244430b2922043060402043062d02043c708128438504a20438704a34c2ca2481071850440c2040
|1=>0x2c128810e30b70a20430b04a34874c2dc28810f30b04a2040cc2dc20430b04a00812430b04a2043062ca5c81073232c128430b04a88810c18205110c2d184880c2c12881033060812047cc2c128811e30b04a21d6432c128860c2dc4446cc181
|2=>0x10c2c128810c18b04a20430b05128810c2dc28810c4cb28810c2ca8481073062c128810e30b05128810330b05120430b29720438c18128810f38c
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x283129888c3e61c30cd45ac27610b06d82ac0f6
|6,0=>0x6a3b35d8cebf75c3ac9958ca664fba61d22e8a742a9f9ceee70734b98d8b8e566
|7,0=>0x12e6943482231111785b411df90f57773ba19c2edb6
|8,0=>0x505e74f346
|9,0=>0x1486
|_,_=>0
def wAt:=mkWire dB 37 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3914c2d28847073084a2d20c462128b4b292c84a212dc8a2104a4c591068a2d28b4f2318c4a2d30d4a0a2c84c112034c2920a442104a4a2d20e8c2d3084b292c38c292cc46052ca480d28c442130b482d20c4a2d3884b311814b292c84a2144e0a2130b4c2118c4b290c20a3120b4831
|1=>0x28b4a2104a460528b4b7204a4c2128b4c2d2884c2920a411e3084b312ca4a392cc4b3104a4a0a2c8443104a463128b4a3104a4e4430b4a21
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x810001c42900007300010c09801
|6,0=>0x806f4dd1b73000d0d89ae35a2a8d39a4342678c001c23445cca9123
|7,0=>0x5b2b255caa9532a253ca694b29251ca29432
|8,0=>0x17c6f0dd1
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x407d5820002c084ffe0427bb0213918101ef008024003f7fb0043808009eec004e760023ba000b918003e8c0017460008880003d58001e28000e460006000002400000e00000410000108000054800028000011000008200004000001f8000012000000
|1=>0x8353ddb003e8d801740800fa122139d90054ac630d161007a3
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40020200a004303
|6,0=>0x3c764b01151714605e60815011a261
|7,0=>0x1d59f3a26e495c8279a3
|8,0=>0x124d5
|9,0=>0xd
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 8 roots_121 ops++addP pm 1 dom_59 7 roots_59 ops++addP pm 2 dom_113 5 roots_113 ops++addP pm 3 dzo_41_2 4 roots_41 ops++addP pm 4 dom_120 5 roots_120 ops++addP pm 5 dom_91 8 roots_91 ops++addP pm 6 dzo_57_2 5 roots_57 ops++addP pm 7 dzo_82_32 4 roots_82 ops++addP pm 8 dom_122 7 roots_122 ops++addP pm 9 dom_115 7 roots_115 ops++addP pm 10 dom_107 7 roots_107 ops++addP pm 11 dom_82 4 roots_82 ops++addP pm 12 dom_58 4 roots_58 ops++addP pm 13 dzo_121_2 6 roots_121 ops++addP pm 14 dom_89 7 roots_89 ops++addP pm 15 dzo_91_32 6 roots_91 ops++addP pm 16 dom_27 5 roots_27 ops++addP pm 17 dzo_90_32 5 roots_90 ops++addP pm 18 dzo_105_2 5 roots_105 ops++addP pm 19 dom_41 4 roots_41 ops++addP pm 20 dom_51 4 roots_51 ops++addP pm 21 dzo_83_32 5 roots_83 ops++addP pm 22 dom_106 4 roots_106 ops++addP pm 23 dom_99 4 roots_99 ops++addP pm 24 dom_75 5 roots_75 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_41_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_57_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_82_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_121_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_91_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_90_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_105_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_83_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_75 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 8 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 20 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 20 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 13 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 13 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
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
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=lower_slice_b [(0x30303030303030303030303030303030,32,36)] (by decide +kernel) lowS_121
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=lower_slice_b [(0xcccc000000000000cccc000000000000cccc000000000000cccc,64,66)] (by decide +kernel) lowS_205
namespace S_219
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,18),(2,66),(2,130),(3,11),(3,19),(3,67),(3,131),(8,9),(8,24),(8,72),(8,136),(10,11),(10,26),(10,74),(10,138),(16,17),(16,18),(16,24),(16,80),(16,144),(64,65),(64,66),(64,72),(64,80),(64,192),(128,129),(128,130),(128,136),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffff
def xsM:=roots_219.map (·&&&dom_219)
def gM:=goal_219&&&dom_219
def NN:Nat→Nat
|4=>3
|5=>69
|6=>145
|7=>86
|8=>22
|9=>4
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x3ebb5309b90ae99
|5,0=>0xcac5ac7651ae6ba9a2a98ef8780fbd7e67f7db7b7b501771b66e01c677f6672155ac0058ee052a7952a62508224f3ac4f36d4e5b04d68f4391842b2140dbd3ebfc3e43c3d1d63cd053c9053617e35ab5359d5357ef33ca83315f32edc304462fa062988c2515723217202891f4c71d6b81d5b71c5081bfd81b84f18d1917ca716c261639d146f50fe960f91c0f66a0c70d0bef50b97409a20092fb08bbe082d8068f9066b4050d50391c015eb
|6,0=>0x665196603b6390b62704626236186f5d78e5cf6c5c2aa5922255b3c545bf531f552d7e5224f5188b5053b4f0ad4e8844a28249cad473184720046cf546ccc461b045d16429eb40d1e3f6023d9ac3d24d3c9053ba1b3b0b73afa436593363e73597d337d53318232a492fd722f76b2eeef2eb952d7252d6592bfce2bc8a289a2280f4278f926ebe265d9252ec24eeb24825235cf22dd52120320c8a20bc5206f21ed7d1ad4d1a3891a1ae19bb718e1f186821845117b881753e16ed216ed016cc715ee815c041594914777137ee132f912301122d91212611f5411cbb11c89119df1169810ba7103190fdc20fb460f6c50f5c80eef90e9760e29e0df390ced90c4230b9150b2e8076760757507426073fe072f707056061ac05ec2059460590b0527c050260488d0409e03c43038f00381c036de02a42028e302285013a8008d5
|6,1=>0xce16dc7651a78a2a640a9da819aeac9909f889af7fdde7f8027dc817ae8a771b6750287455a6af9c69920
|7,0=>0xcac29c323a9668292cf186d3e7a31b75ad57182a6f8cb6f49667c8167a2f641b160476604735eab25e3d8593145806356a2b53bf553a505140351159505d14feed4de714db714cede4ccf64c7594af29472cc4457141a4e40df33f8603e9243bf253b31839bab37b0d34b943352f32a49307352f7c72f3de2dc992dac22cb452c13c2c0282b2ab2b20a2673c260af22c0522aa12207b21b9c1d7ef1d1401c0f01a8be19bb8178c416916148d8130a40f0e60c7780b3fd0a77e09cc60926e08f8e066000613a05cb2042d7042890364a0226c013cc010e1
|8,0=>0xbef506e784587d2553a953788504004ba1545317318202f1952b8cc29b351c567134a0128610ebe50eaf90cb2d0b8570aef30500104e6c
|9,0=>0xa019f2fd770af55088ca
|10,0=>0x798d4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f000000000f000f00000000000f0f0000000000000f000000f0f0f0f000000000f000f00000000000f0f0f0f000000000f000f00f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000f0f0f0f0000000000000000000000000f0f0f0f0000000000000000f0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f00f0f0f0f000000000f0a0f0a000000000f0f0a0a000000000f0a0a0ac0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0cf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000000000000000000000000000000000000000000f0f0f0f000000000f0f0a0af0f0000000000000f0f0000000000000f0f0000000000000f0f00000000000000000000f0f0f0f0000000000000000000000000f0f0a0af000f00000000000f000f00000000000f000f00000000000f000f00e0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0e0000f0f0000000000000f0f0000000000000f0f0000000000000a0af0f0f0f000000000f0f0f0f00000000000000000000000000000000
|0,1=>0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0a0af0f0f00000000000f0f0f00000000000f0f0f000000000000000000f0f0f0a000000000f0f0f0a000000000f0f0f0a000000000a0a0a0af0f0f0f000000000f0f0a0a000000000f0f0f0f000000000f0f0a0af0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f0000f0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0a1010101000000000101010100000000010101010000000001010000f0f0f0f000000000f0f0f0f000000000f000f00000000000f000f00f0c0f0c000000000f0c0f0c000000000f0c0f0c000000000f0c0f0cf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f000f000000f0f0000000000000f0f0000000000000f0f0000000000000f0050505050000000005050505000000000505050500000000050505001010101000000000101010100000000010101010000000001010100f0f0a0a000000000f0f0a0a000000000f0f0a0a0000000000000000f0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0af0f0e0e000000000f0f0e0e000000000f0f0e0e000000000c0c0c0c
|0,2=>0xf0f0f0f000000000f0f0f0f000000000f0f0f00000000000f0f0f0000000000000000000000000000000000f0f0f0f000000000f0f0f00f0f0f0f000000000a0a0a0a000000000f0f0000000000000a0a0000f0f0f0f000000000e0e0e0e000000000f0f0c0c000000000e0e0c0c50105010000000005010501000000000501050100000000050105000000000000000000f0f0f0f0000000000000000000000000f0f0f00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0a00f000f00000000000f000f00000000000f000f00000000000f000af030f03000000000f030f03000000000f030f03000000000f030f000030003000000000003000300000000000300030000000000030000f0f0f0f000000000f0f0000000000000f000f00000000000f000000f0f0f0f000000000f0f0f0f000000000f0f0a0a000000000f0f0a0af0f0f0f0000000000000f0f000000000f0f0f0f0000000000000a0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0000f0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0a3030303000000000303030300000000030303030000000003030000
|0,3=>0xf0f0000000000000f0f0000000000000f0f00000000000000000000000000000000f0f0a0a0000000000000000000000000f0f0a0af0f0f0f000000000f0f0f0f0000000000000000000000000f0f0a0a000000f000000000000000f000000000000000f0000000000000000f0f0f0f000000000f0a0f0a000000000f0f0f00000000000f0a0f0030303030000000003030303000000000303030300000000030303005050505000000000505050500000000050505050000000005050000f0f0f0f000000000f0f0f00000000000f0f0f0f000000000f0f0f0000f000f00000000000f000f00000000000f000f00000000000f0000000000000000000000f000f000000000000000000000000000f0000f0f0f0f00000000000f000f000000000f0f0f0f00000000000f000000b000b00000000000b000b00000000000b000b00000000000b000af0f0000000000000f0f0000000000000f0f0f0f000000000f0f0f000000000000000000505050500000000000000000000000005050000f0f0f0f0000000005050505000000000f0f0f0f0000000005050000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f00
|0,4=>0xa0a0a0a000000000a0a0a0a000000000f0f0f0f000000000f0f0a0a00f000f00000000000f000f00000000000f000f00000000000000000000f0f0000000000000f0f0000000000000f000000000000000f0000000000000000000000000000000000f0f0f0f000000000f000f0000000000000000000000f0f00000000000000000000000000000f00b0b0b0b000000000b0b0b0b000000000b0b0b0b000000000b0b0a0a00000000000000000000000000000000f0f0f0f000000000a0a0a0a000000000000000000000000000000000000000000000000f0f0f00f0f0f0f000000000f0f0f0f0000000000000000000000000f0f0f0000f000f00000000000f000f00000000000f000000000000000f0000f000f0f000000000f000f0f000000000f000f0f000000000f000f003030303000000000303030300000000030303030000000003030202f0f0f0f000000000f0f0f0f0000000005050505000000000505000050505050000000005050000000000000505050500000000050500003030303000000000303030300000000010101010000000001010000f0f0f0f000000000f0f0000000000000a0a0a0a000000000a0a0000
|0,5=>0xf000f00000000000f000000000000000000000000000000000000f0f0f00000000000f0f0f00a0a0f0f000000000a0a0f0f000000000a0a0f0f000000000a0a0a0af000f00000000000f000f00000000000f0f0f0f000000000f0f0f000000000000000000f0f0f0f0000000000000000000000000f000f000000000000000000f0f0f0f0000000000000000000000000a0a0a0a00f000f00000000000f000000000000000f000f00000000000f0000f0f0f0f000000000f0f0f0f00000000000f000f00000000000f000000000000000000000000000000000000f0f0f0f000000000f0f00000000f0f0000000000000a0a0000000000000f0f0000000000000a0af0f0f0f000000000f0f0f0f0000000000000f0f0000000000000a0a00005050000000000000505000000000000050500000000000000000000000000000000f0f0f0f0000000000000000000000000f0f000000000000000000000000f0f00000000000000000000000000000a0a000000000000000000000000000000000000000000000000f0f0a0a0000000000000000000000000000000050505050000000005050000
|_,_=>0
def sP:Nat→Nat
|0=>0xe2c02a0a5c7870014129502c0054e3d30b006c6172c3c38c1a9440f3890283041cd8506091800a0cd21401c88506645803e18283042cd8310740063630182166c182022c0050668c8b0018205062078c2e607951630b961e54585065098b00301901e2c509101c3040a0c1040608080
|1=>0x6645805e5c79516002881ea0580362418800147b4160028234a05800a607a60e2c28f40d05806630b8f1600509102c00a4a207870a0c11a620110304045800c14182422ce1b180c10760b82971e2c31b0a0c1075e6cb981e1d7052e6078b226c19916017052e5878b360d60f00141ab
|2=>0x66458036301825288283562c01176205800a0c7ba16017852e505803814199160179b2e3c385065100b000c439022c038185cb0f169021b0608011440d0a0161910506085ae0a207b716a81881e5401b180c129346cc081e782971a3da8044141a1322ce040a0c1005ea8d971e008a2
|3=>0x6c2831e98580700c40f2a2c00c0a0c129422c283106a00060bc2971e2c01c48141821601c1b0a5c787002910c2e3c5800a0c41a42fde850608580441418f742c01c3630188422c2831085c87166c683103ca800a9c1ab16018052e3c5803e14128160028328e85800a9c7b71600f85
|4=>0x2c601881e14b961e545805e8828d103c00506214b9160111b0a34c081e302831f1058008141881e1c00a1858c081e2c288343d40b006c2831e645805e6c603103c3ae18141881e2cd850620a0b00702831f105807028298103c38a443440f00282831ee85800a0c7c1160028310687b1
|5=>0x6207871688d85060908b5414698103c03054141881e002971a3df800c6c283042c00c0a5cb0f164511b0608580360c40f8c1c2a7063c5803e141820e2c0381430b8f16002831e81b8b00bcd97303c5805414b03103c0052e6079516002a7063d00b0014bc51e2c00c0a0c421722cd8c
|6=>0x1e54580363018852687af146c6881e00d852e3e58b00442050620d003e1418f882c01f181418216012050620d07226c18f402c0051a9440f004511b0620d003e70283042c00507287871600522366040f1670d8506210875c6c603103c59c3630182160089b062248048141820e2e385
|7=>0x180c40f9ce11052e3c5805e1440f6e2c0300a0c40f1600d85060a4800a6018f401c5850620e8b0014b8f9a1c5850620d391600298063dd0b006c297983c00436301881e01204360c40f008828310505806014b8d1e2c02a0a5c78b00882831e985800c88283103c59b185cc0f16c0188
|8=>0xbcd8d30207801414b8f16f004f0a0c421160121b060908b00e170c062078b220c40f022c0040a0c10b00bcd960620780180d2881e2c283583c58044141a11e8059b06207ad001418f87045800a207a816008a2063d00b006c297303c38a365840f00e02831050580486c188523c01b
|9=>0x42ea00234c188422ce05063d00b00bd5052e3c580226c188421c8a20621c8b0028d96103c3803630698103dc052e5878b006c603043c39b18581881ec028310505803630188523d10530207b716c11052e3c580145840f2a2c0052c0c41416002830548580486c18834840510a0c10b
|10=>0x841c02f0a5cc0f160111b0a0c10f16008a2060838b00c02971e2c011440c10b007c28310e45800a0c7ba0e2c005063d30b001418f40985805c14c03103c5a408141883400f85063d00b0088283943c5803630188523c385063dd0b001418f6e985805e1418f402c0220a5cc0f1644283
|11=>0x5c14683103c5801414b18103c5801814b981e2d2050620d0b0120283103c38b0070d85062108b0088605300c40f16906050608580146c1881e1c00aae0c40f160111b0a0c41a1e00d83103e30b0014b981e1c59b0a0c4491e00283103ea8b00e0283103c380386c283103c3800a0c40f
|12=>0x6c28310a4d0f00bc605062078716282db103c5803e6c283103c5802214188b42c00506207d81600298062078b7e141881e2de000a0c129342c01f0a0c4211e2c02e36141881e2c00506207cb16011052e0c787160121b062108f1600205062078b003028d06207873614b180620780
|13=>0xa5c78b0014b831e2df800a0c40fac1c02f44141881e2c0223614c03103c5910a0c40f175005c0a0c40f160088c062108b3630188423c58a440c40f16002831e805801814b18062078b3888283103c58060141881e2c01b0a0c40f722c0220a341881e00d852e6078b0088d85063d00b
|14=>0xe2c00a0a5840f1600d85062148f001418f401c58060141881e1c5803814188523c580226c188422c005060948b00141881edc58044141881ee45800830283103c58036301821e2c0385e141881e2c02408141881e2c05e0a5c78b00141a5103c5803e88283103c5800a0c45d1e2c02f
|15=>0x14146881e2c005062078b9c01105062078b0014182422c01b180c40f0e882831e8058044141821e2c0300a341881e2c00a0a5840f0e2c00506207b70e2c03e0a0c10b007c28310a478b006c283048458060bc283103c5803614698103c005300c40fbe2c0110a0c429342c00a440c40f
|16=>0x1e2c0052e3478b00141881f345800a0c40f16fc00506207d6160028310a47871601f05062078b00bc505062078b00141821e1c58014141881e1c58044141881e1c5800a0c4291e2c005062108f0e2dc05062078b0070d85062078b003028d062078b006c28d06207804814188423c580
|17=>0x5062078b00141881e1c5800a601881e2c005060878b0028283103c5803630188
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa400550005
|5,0=>0x17c61775171616c51666160615a6155514f61496143613d61376131612b6125611f611a5114610e6108610260fc60f660f060eb50e650e060da60d460ce60c950c450be60b860b260ac60a660a0609a6094608e60886083507d60776071606b60656060505a6054604e60486042603d50376031602b6025601f60196013600e5
|5,1=>0x19a6194618e618861826
|6,0=>0x34c6345733f63387331732a7323731c7315730e7308630262fb72f472ed72e672e062d972d362cc72c662c062b972b272ab72a4729d7296728f72896282727b7274726d7266725f72587251724a7243723c7235722e7227722072197213620c720661ff71f871f171ea71e461dd71d671cf71c871c261bc61b571ae71a771a07
|6,1=>0x4f664ef74e874e264db74d474ce64c774c164bb64b474ae64a774a074997492748c6485747f64787471746a7463745c7455744f64487442643c6435742f64287422641b7415640f6408740173fb63f473ed73e673e063d973d363cd63c673bf73b963b273ab73a4739d7397639073897383637c7375736e73677360735973527
|6,2=>0x5677561655b6554754d7547654075397532752b7524751d751765107509750364fc7
|7,0=>0x73c8734872d7725871d871767107708870176fb66f476ed76e586dd86d586ce76c866c176ba76b466ac86a4869d7695868e7687767f8677866f8668766086597652764b7644763d7635862d8626761e8616860f7608760085f885f085ea65e375db85d385cb85c475bd75b675ae85a775a1659a7593758c7584857d7576756e8
|7,1=>0x7df67d877d177c987c187b987b367ab87a4779c8795778d8785877d8776776f7768776087588751774b67447
|8,0=>0x87d7877687078697862785a8853784b8844783c8834882d7826781f7817880f8808780087f977f277eb77e56
|9,0=>0x8987891788b68847
|10,0=>0x89f6
|_,_=>0
def wAt:=mkWire dB 96 220 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x16010a2d0601061516c934320a01363d002d0015103d3803301506010a2d100d5a2134301615163d00151e9e068144230a1d44230a1d1601061d160100151615100d0a01366016150601062d222d22011e211e1544231e010a1d16013c3d141c0a2d0a0d002d38030a5a0a012421221c0a3d002d1e391a30001516010615062d
|1=>0xe2b0a0d16011e213e0f0aa51e1d16011e824423443d0a1d16011e1d160100151615103d06b518680a011e2d1e1530150601002d0a2d100d1a011a150621160d482f442336010a2d0a0134011e211e2d141c16010a2d0601061516d918370a01006d0a2d16be0a1d16011e391834062d1615001506151c3d1a30160d00153660
|2=>0x6023141d1601110e01091e6e161516c93432163d0a01445f100d006d16150a5a1a010a35062d422d0a011e211e01368416151e011e2d06215e2d14010615103d220116451e15100d002d066d0a2d0a0d100d163100151e2d1e010a1e16017c01222f1e211e15440d0a1d16011e011e6d1615443f0a1d16012c171a01062d14f1
|3=>0x44230a1d1601100d06fd0a1e1601443f16310a01302d000d16152c1706211a01062d062d063116310015443f1e1d0a1d16010601006d0a2d3e23443d16313e2f443d0a1d002d302d0a01060106153e0f34310a011e824423006d16150a2d160106310a016003440d16310015603f440d006d142d0a0d002d182d0a01062d0615
|4=>0xa011601103d9001141f0a0d160136011e21003d16155e2f30150601602f0a59061d002d0621062d0a1e002d103d00721e6d0a2d1a010621160d00151e15103d006d0a2d0a2d180f0a01160144230a1d1601103d443d0a1d160100150621142d0615440f0a1d160130150621000d0a2d5e2f302d0a61060106212c17302d0601
|5=>0x61d1601001500691e2d14010a2d062d061536620621000d169200451e153e230aa51e1d160118691e21163d0015220116011e151e2d44231e15006d1615160d306c000d0a2d36010a2d1e2d1e15103d00711e6d16151e8144230a1d36010a2d06011e01363d0a2d00e2066d0a2d363d16150015103d34030a2d1e2d1e15183d
|6=>0x5e2d1401061514f1141e0a0d16011615103d006a1e2d442306010a1d16013c3d141c0a0d1601100d1601301706013e3f3431163d0a01602336610a2d1a030a2d0621062d482f1e31001516921e310015603f440d0a1d16011835160d0015100d16be06310a01445f0a1d160138031e6d006d1615060100151615100d0a5a0a59
|7=>0x42151e211e0170031a15160d3e170e45002d1e151692103d1e310a011615302d30150601306c0015000d16155a213430163d00154423006d0a2d18681e2d1615001501091e6e16153e0f0aa51e1d160144230a1d16011601000d1615100d061d0a2d0a0d002d0a2d422d0a851e01061e160100151615100d066d006d1615600f
|8=>0x6310a0116010a2d1e011e15443f0a1d1601061d0a0d002d06011615160d00151a0106211a15062d160100151615103d0015302d000d0a2d603f0a59061d1601422d1e0100151615440f006d0a2d440d0a1d16010a5a1a01062d36861e21003d1615421516151e010e460a3d1601103d0a2d0a6106011f41426e003d16151615
|9=>0x103d006d16150a3d1e210a1d160136610621000d16150a3d0a1d1601103d3e3f0aa51e1d16016023440d0a1d445f0a1d1601100d44230a1d16016003306d000d0a2d482f1e310a0144230a1d16011e8144230a1d16011e1d16010015161560230a59061d1601440f0a1d16010621006d000d0a2d1e011e1516320015100d16be
|10=>0x1e310a010a01062d002d302d000d0a2d70031a15062d302d060106150a0106210601163d1e310a01141f0a0d363d0a2d1e01060116310a01103d1e310a010a2d0a0d002d0615006e16151e2d006d0a2d180f001516151601062106011615006a1e2dac010a6a1e2d142d0a0d002d002d1e6d0a2d363f0a2d002d062130150601
|11=>0x15302d06011e6d006d16150a59061d1601443f006d16151631160d0a010621000d16154423006d16150a2d00691e2d180d0a011601302f06150601443d006d1615422f1e011e150165066e161506010a1e1601141e0a0d160134011e211e2d36850a2d1e017003066d1615306f000d161506210a1d16010a2d0a851e011692
|12=>0x1e1d1601440f0a1d1601443f0a1d160116921e310a0100151615103d142d1401061516921e310a01140306210615306c000d1615443d0a1d16011efd0a1e16010621140106150a1e1601100d002d34171e2d063116310a01000d006d1615221e1601075d006e16150a011e011e151e01001516150a0d0a1d160144230a1d1601
|13=>0xa1d16011e211e0116010015161544230a1d16010a1d1601103d1a31160d0a01061d0a0d1601440f0a1d1601103d16461e150aa51e1d1601003d1615103d5e2d140106151615062d060136630a2d1e1500691e2d0a0d0a1d16011a01062d06150a2d1e1d002d44230a1d1601440d0a1d160134010a691e2d0a2d1e011e15103d
|14=>0x16010601103d0615001516150621062d301706010a1e16010a6a1e2d1e1d1601222f1e15140106151601103d0a0d16010a1d16011e1d16011e011601142d06151e6d16150a01062d0a2d062d0a851e01062d0615061e1601
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x60000000
|5,0=>0x1cd46e5000069500000000000645000000018105f1170c00000000001610535140c4e200004d112c800000004650000000000000000004150f1439300000000d500000d04304000000000002b509d0000000024307d41a50590000049000000000d50304000000000000000b10000065
|5,1=>0x1f507850000000
|6,0=>0x59516145751594555152353cd4c3524d45450513d44e513544c8d2e44a9126448911e4469117344d10f4430d08441110043f4cf943d8cf333bd0eb439d0e43384cdd43650d633490ce43290c730000c433010bd32e50b542c50ad42a50a5428509d4265095424508d4228c873210c813
|6,1=>0x90900008f923a48dce3438c122c48a1224488121c4864e16384cc00083d20c3821205300020147f51fa37d91f247b91ea47991e3377d1dc37611d537451cd40001c947151c146f51b946d51b146b51a946951a2367919b3660d944644d8d4628d86460917e45ecd7745d0d7135b51694
|6,2=>0x27949d527149b526a3999263397d25c3964e55494524d4928c0009190000
|7,0=>0xce0f353cc8f2f3cb0f293c98f233c80f1d3c68f173c50f113c3cb0c3c24f063c0cf003bf4efa3bdcef43bc4eee3bacee83b94ee23b7cedc3b64ed63b4ced03b34eca3b1cec43b04ebe3aeceb83ad4eb23abceac3aa8aa73a90ea13a78e9b3a60e953a48e8f3a30e893a18e833a00e7d3
|7,1=>0xde4f763dccf703db4f6a3d9cf643d84f5e3d6cf592d58f533d40f4d3d28f473d10f413cf8f3b3
|8,0=>0xe98ba42e88ba02e78b9c2e68b982e58b942e48b902e38b8c2e28b882e18b842e08b802df8b7c2
|9,0=>0xeac7aa1ea47a81
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 14
def pmP:Nat→Nat
|0=>0x10400100000fc000800007d0007c000690006800060000580005100047000440003c000310002c0002800021000200001c000190001500011000100000c00009000080000500004000030000100000
|1=>0x100000b7d00b6400b4400afd00940008f4008200067d006740041000400003fd0037d00331002a000291002800027d0027c002440024300225002240022000211002100020400201002000014000115
|2=>0x467d0467c046740427d04015040040400003a7502b7d02b7502a7d02a750296002375023640227d02231022150214002019018f40182401820013fd01375012fd0127d011240111401104010f401004
|3=>0x402114000820265202411867d18675184301802c1607d144741407d1402c140041207d1067d1067c10031100040e27d0e0680e05d0e0440c0680c0240a07d0a040084740827d08031080200800006040
|4=>0x8027d801f480020800085467d5427d5407d540355402c5207d4c0754807d44004438114267d4245c42440424244227d42275422254220042084420084137d4136441324412fd410f440a7d40a7540a71
|5=>0xc2009c0a75c0460c02b4c0200c00699827d9807d9806898064980399802c960119027d8802084075823758220081a7581a3181a248187181864812fd810f481020808208067d8037d8037580355802fd
|6=>0xc267dc2468c22a4c227dc2275c226dc2260c2251c2225c2224c2069c2061
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x20000
|5,0=>0x92300000979001400000043000017590500000062311c34001e3400002a0000000000144e3400006800614000000016030000084a4f13000700007c59000000003f000c
|6,0=>0x950044b388a5921737ac06b5bb2f490070735e420006734d0636288c1a0567010605a7aa0010a130010965247d410622395a9301091d2e018301b1860d6e0963980754c115038a66216a6b7604bd1f019e694b8f80255b3c01420138252d9ca6492801ae0d04ab050f850e0d003ac4221206270178670a135389b05d01607e9d
|6,1=>0x8e1b9009032c2223733506b4260100bc00
|7,0=>0xc8c6cb7fab8b5f11710a5822b6c2adb8c62018777a2dbf74912b9733500b9f48a09429c505509a96c72dab192dbac746c0b785476f7550a29f7b4c3d45c9972dbeab51a98499036cc39baf52c181a86764566c7248ca
|8,0=>0x8d3b459f64b95c87a4a3c6b9b2576d82559a3e9fc871
|9,0=>0x9f453732
|10,0=>0x2d
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 20 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_217 9 roots_217 ops++addP pm 1 dom_146 4 roots_146 ops++addP pm 2 dom_155 8 roots_155 ops++addP pm 3 dom_218 8 roots_218 ops++addP pm 4 dom_210 7 roots_210 ops++addP pm 5 dom_203 8 roots_203 ops++addP pm 6 dom_91 8 roots_91 ops++addP pm 7 dom_209 7 roots_209 ops++addP pm 8 dom_195 5 roots_195 ops++addP pm 9 dom_211 8 roots_211 ops++addP pm 10 dom_216 7 roots_216 ops++addP pm 11 dom_147 5 roots_147 ops++addP pm 12 dom_83 5 roots_83 ops++addP pm 13 dom_139 5 roots_139 ops++addP pm 14 dom_202 5 roots_202 ops++addP pm 15 dom_154 5 roots_154 ops++addP pm 16 dom_90 5 roots_90 ops++addP pm 17 dom_194 4 roots_194 ops++addP pm 18 dom_75 5 roots_75 ops++addP pm 19 dom_27 5 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_217 9 s (0,roots_217.map (·&&&dom_217)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_217 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xffffffffffffffff0000000000000000,64),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_219==dom_219)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_219 gM v ys):RunD true dom_219 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_219 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 69 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 69 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 145 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 145 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 86 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 86 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 22 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 22 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 4 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_219 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_219 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_219 roots_219 goal_219 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_219
theorem lowS_219:Lower true dom_219 roots_219 goal_219 11:=S_219.noCircuit
theorem lowS_221:Lower true dom_221 roots_221 goal_221 10:=lower_slice_b [(0x30303030000000003030303000000000303030300000000030303030,64,68)] (by decide +kernel) lowS_217
theorem lowS_231:Lower true dom_231 roots_231 goal_231 8:=lower_slice_b [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,32,33)] (by decide +kernel) lowS_230
theorem lowS_237:Lower true dom_237 roots_237 goal_237 9:=lower_slice_b [(0x303000003030000030300000303000003030000030300000303000003030,32,36)] (by decide +kernel) lowS_233
def dzo_211_32:=0xf000f00000000000f000f00000000000f000f00000000000f000f00000000
def gzo_211_32:=0xf000f00000000000f000e00000000000f000e00000000000e000a00000000
def gsh_211_32:=0xf000f00000000000f000e00000000000f000e00000000000e000a
theorem lowS_zo_211_32_210:Lower true dzo_211_32 roots_211 gzo_211_32 8:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_32) [(dom_211,32)] (by decide +kernel) (lower_slice_b (T:=gsh_211_32) [(0xa000a00000000000a000a00000000000a000a00000000000a000a,0,1)] (by decide +kernel) lowS_210)
namespace S_243
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(1,129),(2,18),(2,66),(2,130),(3,19),(3,35),(3,67),(3,131),(16,17),(16,18),(16,80),(16,144),(32,33),(34,35),(34,50),(34,98),(34,162),(48,49),(48,50),(48,112),(48,176),(64,65),(64,66),(64,80),(64,192),(96,97),(96,98),(96,112),(96,224),(128,129),(128,130),(128,144),(128,192),(160,161),(160,162),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_243.map (·&&&dom_243)
def gM:=goal_243&&&dom_243
def NN:Nat→Nat
|6=>4
|7=>4
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x98c926d6412889a028cf
|7,0=>0x7f89776ef135c4f0599d
|8,0=>0xfc84
|9,0=>0x7a9f6
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0000000f0000000f0000000f0000000f0000000f0000000000000000f000f000f000f000f0000000f0000000f000f000f000f000f0000000f0000f000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000f000f000f000f000f000f000f000f000f000f000f000f000f0000000f0000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000cf000f00000000000f000f00000000000f000f00000000000f000f00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a3000300030003000300030003000300030003000300030003000000030000f000f000f000f000f000f000f000f000f000f000f000f0000000000000000f000f000f000f0000000000000000000f000f000f000f0000000000000000f000f000f000f000f000f000f000f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x657410657421065741b068a57410685741069574216a974265431068543106543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0x28c3983b807
|7,0=>0x60ea210b9a7
|8,0=>0x377
|9,0=>0x3e6
|_,_=>0
def wAt:=mkWire dB 12 244 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x41528410a4555244150441515411061f5244187d491061f52441
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x4998c6603
|7,0=>0x91409c4c2
|8,0=>0x141
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 9
def pmP:Nat→Nat
|0=>0x3fff5f7f9fc7f0980e01c00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x4213
|7,0=>0x5786
|8,0=>5
|9,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_241 8 roots_241 ops++addP pm 1 dzo_211_32 8 roots_211 ops++addP pm 2 dom_211 8 roots_211 ops++addP pm 3 dom_210 7 roots_210 ops++addP pm 4 dom_227 7 roots_227 ops++addP pm 5 dom_179 7 roots_179 ops++addP pm 6 dom_115 7 roots_115 ops++addP pm 7 dom_163 4 roots_163 ops++addP pm 8 dom_99 4 roots_99 ops++addP pm 9 dom_51 4 roots_51 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_243 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_211_32_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_51 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_241 8 s (0,roots_241.map (·&&&dom_241)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_243 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_241 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_243==dom_243)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_243 gM v ys):RunD true dom_243 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_243 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_243 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_214_32:=0x55005500000000005500550000000000550055000000000055005500000000
def gzo_214_32:=0x55005500000000005500540000000000550054000000000054005000000000
def gsh_214_32:=0x550055000000000055005400000000005500540000000000540050
theorem lowS_zo_214_32_210:Lower true dzo_214_32 roots_214 gzo_214_32 8:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_32) [(dom_214,32)] (by decide +kernel) (lower_slice_b (T:=gsh_214_32) [(0x500050000000000050005000000000005000500000000000500050,0,4)] (by decide +kernel) lowS_210)
namespace S_246
def pG:List (Nat×Nat):=[(2,18),(2,66),(2,130),(4,36),(4,68),(4,132),(6,22),(6,38),(6,70),(6,134),(16,18),(16,80),(16,144),(20,22),(20,52),(20,84),(20,148),(32,36),(34,38),(34,50),(34,98),(34,162),(48,50),(48,52),(48,112),(48,176),(64,66),(64,68),(64,80),(64,192),(96,98),(96,100),(96,112),(96,224),(128,130),(128,132),(128,144),(128,192),(160,162),(160,164),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_246.map (·&&&dom_246)
def gM:=goal_246&&&dom_246
def NN:Nat→Nat
|4=>3
|5=>15
|6=>35
|7=>15
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x8395b581c70b489
|5,0=>0xc53bbb3c44aa9ef60d9a5319849f8a313d2294c32325c20bc51a5e41a33a19006147bc0e971
|6,0=>0xfae18c3c90955616c0786acae6a623620495c4cb5745f564bc4ecab4d906381b932e0632af031f7a2fab82ed212c74e2aeb22a3be26bfd2362c234761fd311c829199860e9710bb25090f308880084950831605eb40373b
|7,0=>0xf40ed80cea69fc564c4b5e6d6574c84dbc344b7c3c44c355802a254297c520b4d1e70c015af
|8,0=>0xc602d6d4fd20703
|9,0=>0x3f43d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaa00aa00aa00aa00aa008800aa008800aa00aa00aa00aa00aa008800aa0089540154015401540154015401540154015400000154000001540000015400000002a8000002a8000002a8000002a8000002a8000002a800000220000002255005500550055000000000000000000550055005500550000000000000000aa00aa00aa00aa00aa00aa00aa00aa0000000000000000000000000000000154000001540000015400000154000001540000015400000154000001540002a802a802a802a802a002a002a002a002a8028002a8028002a0028002a002844004400440044004400440044004400440044004400440044004400440044aa00aa00aa00aa00aa000000aa000000aa00aa00aa00aa00aa000000aa000154015401540154015401540154015401100110011001100110011001100112a802a802a802a8022002200220022002a8000002a8000002200000022000055005500000000005500550000000000550055000000000055005500000000aa008800aa008800aa008800aa008800aa008800aa008800aa008800aa008940014001400140014001400140014001400140014001400140014001400142a802a802a802a802a8000002a80000022002200220022002200000022000055005500550055005500550055005500550055005500550000000000000000
|0,1=>0x220022002200220022002200220022002200000022000000220000002200011001540110015401100154011001540110015401100154011001100110011000000000000000000000000000000002a802a802a802a802a8022002a8022550055005500550055005500550055005500440055004400550044005500440000aa000000aa000000aa000000aa0000008800000088000000880000008954015401540154000001540000015401540154015401540000011000000110880088008800880088008800880088008800880088008800000000000000000001100000011000000110000001100000011000000110000000000000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa000000aa0001100110011001100110011001100110011001100110011001100000011000000002a8000002a8000002a8000002a8000002a8000002a8000000000000000000055000000550000004400000044000000550000005500000044000000440000000000000000aa00aa00aa00aa0000000000000000008800880088008954015401540154015401400154014001500150015001500150014001500142a802a802a802a802a802a802a802a802a802a802a802a802200220022002255005500550055004400440044004400550055005500550044004400440044
|0,2=>0x55005500550055004400440044004422002200220022002200000022000000220022002200220022000000220001540154015401540154015401540154015401540154015401540110015401100000000000000002a802a802a802a8000000000000000002a8000002a800000000000000000000000550000005500000000000000000000004400000044aa000000aa000000aa000000aa000000aa000000aa0000008800000088000000000000000000000000000000000001540154015401540154000001540000880088008800880088008800880088008800880088008800880000008800055000000550000005500550055005500550000005500000055004400550044
|_,_=>0
def sP:Nat→Nat
|0=>0x18c64b10a0883182c41ce08800428258c2c41ce0901842824065442822010040963152c40c204c2c42821940040ce0933043822013041ce09120429220c2c40ce0913040c70860043ce0863043ce08800408834c2c42892001070861440c2040
|1=>0x2c41ca09630b11728284c2c428220530b12028220c2c41c221f30b1070880152c40ce08800c10a09e20c2c428218831511d28220c2c470a08800c11728218830428221b00c10a0913192c408834c2c428221a30b10338218c1073824082c4282
|2=>0x2c42822003192c41ca09020b10328240c2c428222730b10728218830b12628220c2c40d708830b10220d00c2c41ca0a130b1024488cc2c428222130b1031c218c2c43ce08830b10e2824080042a508620c10a08890c2c40888c030b10388220c
|3=>0x10a08830b10a08800c2c40ca08830b10a09020c2c40ca08800c2c428240800b10a09120030b1171ca08830b10f28240830b10a0a820c2c41ce08830b11c28220c2c428220c54b11728220c
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x18d8bac57628b12d88ac3f61cb0cd85ac27610b06d82ac0f6
|6,0=>0x54de98f4579f3cdde60f297913c6de28f0d7833bfddf0ef17753b8ddb8ed57673b1dd80eb97593aadd48e9d74bb241d14c8373e39d5cdec696
|7,0=>0x706374fb28d5468a336f947c6be19efef778b83da5ec4f5a8
|8,0=>0x75dfa0fc97
|9,0=>0x1de6
|_,_=>0
def wAt:=mkWire dB 41 247 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2804c2d3900a2d20c483a28b4a022cc4c2d2808c2d2808c2d3cbc3312884a1920b4e3128b4a1a20b48022004c2d44ac80130b4a1a20b4a2128b482d448c63120b430230b4a2130b4a2d28c57202804c2d1c60a3120b471828c482d1c60a3120b463120b480130b4c2d0cc4a2140a4831
|1=>0xc2d288483130b4a2120c4b312004c2d1cb4a31290483140bc83128b4a310cb4a212808c2d2804c2d2008c2d28c483120c4a212078a3128c482d2804c2d291880130b57231cb502920c4e3328b4a442004c2d1cbca315c8072d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xf300030c000001261c80005208208801000
|6,0=>0x2814d3964000000009240023900088708a013e2766001c93726c2d09912f35a4ac949263466848f180036660ca9923
|7,0=>0x1b8b616a2d0598b21622c0578ae15a2b0558aa1522
|8,0=>0x1c8788f01
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x6dd6384df34d3012fd2df2cf1090ff0fb0df0d70c907f04f04d04904504104002001e018014012010008006004002000
|1=>0xcdfcd7c129ff
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x3008000185005281040
|6,0=>0x10d1400000401003c414450008728410b08409b3025405ce4d2
|7,0=>0x1161c85e6628148d07da749
|8,0=>0x14599
|9,0=>0x14
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_214 8 roots_214 ops++addP pm 1 dom_118 7 roots_118 ops++addP pm 2 dom_182 7 roots_182 ops++addP pm 3 dom_244 7 roots_244 ops++addP pm 4 dom_230 7 roots_230 ops++addP pm 5 dom_228 5 roots_228 ops++addP pm 6 dzo_214_32 8 roots_214 ops++addP pm 7 dom_210 7 roots_210 ops++addP pm 8 dom_116 4 roots_116 ops++addP pm 9 dom_180 4 roots_180 ops++addP pm 10 dom_166 4 roots_166 ops++addP pm 11 dom_102 4 roots_102 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_246 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_214_32_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_102 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_214 8 s (0,roots_214.map (·&&&dom_214)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_246 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_214 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xffffffffffffffff0000000000000000,64),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_246==dom_246)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_246 gM v ys):RunD true dom_246 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_246 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 35 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_246 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_246 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_246 roots_246 goal_246 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_246
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=S_246.noCircuit
def isoMvS_126:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_iso_b isoMvS_126 (by decide +kernel) lowS_119
def isoMvS_159:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_iso_b isoMvS_159 (by decide +kernel) lowS_95
def isoMvS_175:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_175:Lower true dom_175 roots_175 goal_175 8:=lower_iso_b isoMvS_175 (by decide +kernel) lowS_111
def isoMvS_183:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 9:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_119
def isoMvS_189:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 9:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_125
def isoMvS_190:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_119
def isoMvS_235:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112)]
theorem lowS_235:Lower true dom_235 roots_235 goal_235 10:=lower_iso_b isoMvS_235 (by decide +kernel) lowS_123
def isoMvS_238:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 8:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_231
def isoMvS_245:List (Nat×Nat):=[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 9:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_125
def isoMvS_249:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_221
def isoMvS_250:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_243
def isoMvS_252:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccccccccccccccccccc,126),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_125
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,32,36)] (by decide +kernel) lowS_123
theorem lowS_223:Lower true dom_223 roots_223 goal_223 12:=lower_slice_b [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,64,68)] (by decide +kernel) lowS_219
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,32,36)] (by decide +kernel) lowS_235
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_246
theorem lowS_251:Lower true dom_251 roots_251 goal_251 12:=lower_slice_b [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,1,33)] (by decide +kernel) lowS_219
def dzo_57_4:=0x3030303030303030
def gzo_57_4:=0x3030303030202000
def gsh_57_4:=0x303030303020200
theorem lowS_zo_57_4_25:Lower true dzo_57_4 roots_57 gzo_57_4 5:=lower_iso_b (d1:=dom_57) (r1:=roots_57) (T1:=gsh_57_4) [(dom_57,4)] (by decide +kernel) (lower_slice_b (T:=gsh_57_4) [(0x303030300000000,0,32)] (by decide +kernel) lowS_25)
def dzo_212_32:=0x11001100000000001100110000000000110011000000000011001100000000
def gzo_212_32:=0x11001100000000001100100000000000110010000000000010001000000000
def gsh_212_32:=0x110011000000000011001000000000001100100000000000100010
theorem lowS_zo_212_32_208:Lower true dzo_212_32 roots_212 gzo_212_32 5:=lower_iso_b (d1:=dom_212) (r1:=roots_212) (T1:=gsh_212_32) [(dom_212,32)] (by decide +kernel) (lower_slice_b (T:=gsh_212_32) [(0x100010000000000010001000000000001000100000000000100010,0,4)] (by decide +kernel) lowS_208)
def dzo_121_4:=0x30303030303030303030303030303030
def gzo_121_4:=0x30303030303030303030303030202000
def gsh_121_4:=0x3030303030303030303030303020200
theorem lowS_zo_121_4_25:Lower true dzo_121_4 roots_121 gzo_121_4 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_4) [(dom_121,4)] (by decide +kernel) (lower_slice_b (T:=gsh_121_4) [(0x3030303000000000303030300000000,0,32),(0x3030303030303030000000000000000,0,64)] (by decide +kernel) lowS_25)
def dzo_153_4:=0x3030303000000000000000000000000030303030
def gzo_153_4:=0x3030303000000000000000000000000030202000
def gsh_153_4:=0x303030300000000000000000000000003020200
theorem lowS_zo_153_4_25:Lower true dzo_153_4 roots_153 gzo_153_4 5:=lower_iso_b (d1:=dom_153) (r1:=roots_153) (T1:=gsh_153_4) [(dom_153,4)] (by decide +kernel) (lower_slice_b (T:=gsh_153_4) [(0x303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_25)
def dzo_213_32:=0x33003300000000003300330000000000330033000000000033003300000000
def gzo_213_32:=0x33003300000000003300320000000000330032000000000032003200000000
def gsh_213_32:=0x330033000000000033003200000000003300320000000000320032
theorem lowS_zo_213_32_208:Lower true dzo_213_32 roots_213 gzo_213_32 6:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_32) [(dom_213,32)] (by decide +kernel) (lower_slice_b (T:=gsh_213_32) [(0x220022000000000022002200000000002200220000000000220022,0,1),(0x300030000000000030003000000000003000300000000000300030,0,4)] (by decide +kernel) lowS_208)
def dzo_249_4:=0x3030303030303030303030303030303030303030303030303030303030303030
def gzo_249_4:=0x3030303030303030303030303030303030303030303030303030303030202000
def gsh_249_4:=0x303030303030303030303030303030303030303030303030303030303020200
theorem lowS_zo_249_4_25:Lower true dzo_249_4 roots_249 gzo_249_4 7:=lower_iso_b (d1:=dom_249) (r1:=roots_249) (T1:=gsh_249_4) [(dom_249,4)] (by decide +kernel) (lower_slice_b (T:=gsh_249_4) [(0x303030300000000030303030000000003030303000000000303030300000000,0,32),(0x303030303030303000000000000000003030303030303030000000000000000,0,64),(0x303030303030303030303030303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_25)
def dzo_185_4:=0x303030303030303000000000000000003030303030303030
def gzo_185_4:=0x303030303030303000000000000000003030303030202000
def gsh_185_4:=0x30303030303030300000000000000000303030303020200
theorem lowS_zo_185_4_25:Lower true dzo_185_4 roots_185 gzo_185_4 6:=lower_iso_b (d1:=dom_185) (r1:=roots_185) (T1:=gsh_185_4) [(dom_185,4)] (by decide +kernel) (lower_slice_b (T:=gsh_185_4) [(0x30303030000000000000000000000000303030300000000,0,32),(0x30303030303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_25)
def dzo_220_32:=0x1111111100000000111111110000000011111111000000001111111100000000
def gzo_220_32:=0x1111111100000000111111100000000011111110000000001110111000000000
def gsh_220_32:=0x11111111000000001111111000000000111111100000000011101110
theorem lowS_zo_220_32_208:Lower true dzo_220_32 roots_220 gzo_220_32 6:=lower_iso_b (d1:=dom_220) (r1:=roots_220) (T1:=gsh_220_32) [(dom_220,32)] (by decide +kernel) (lower_slice_b (T:=gsh_220_32) [(0x10101010000000001010101000000000101010100000000010101010,0,4),(0x11001100000000001100110000000000110011000000000011001100,0,8)] (by decide +kernel) lowS_208)
def dzo_217_4:=0x30303030000000003030303000000000303030300000000030303030
def gzo_217_4:=0x30303030000000003030303000000000303030300000000030202000
def gsh_217_4:=0x3030303000000000303030300000000030303030000000003020200
theorem lowS_zo_217_4_25:Lower true dzo_217_4 roots_217 gzo_217_4 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_4) [(dom_217,4)] (by decide +kernel) (lower_slice_b (T:=gsh_217_4) [(0x3030303000000000000000000000000030303030000000000000000,0,64),(0x3030303000000000303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_25)
def dzo_221_32:=0x3333333300000000333333330000000033333333000000003333333300000000
def gzo_221_32:=0x3333333300000000333333320000000033333332000000003332333200000000
def gsh_221_32:=0x33333333000000003333333200000000333333320000000033323332
theorem lowS_zo_221_32_208:Lower true dzo_221_32 roots_221 gzo_221_32 7:=lower_iso_b (d1:=dom_221) (r1:=roots_221) (T1:=gsh_221_32) [(dom_221,32)] (by decide +kernel) (lower_slice_b (T:=gsh_221_32) [(0x22222222000000002222222200000000222222220000000022222222,0,1),(0x30303030000000003030303000000000303030300000000030303030,0,4),(0x33003300000000003300330000000000330033000000000033003300,0,8)] (by decide +kernel) lowS_208)
namespace S_253
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,24),(8,40),(8,72),(8,136),(12,13),(12,28),(12,44),(12,76),(12,140),(16,17),(16,24),(16,80),(16,144),(20,21),(20,28),(20,52),(20,84),(20,148),(32,33),(32,36),(32,40),(48,49),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,72),(64,80),(64,192),(96,97),(96,100),(96,104),(96,112),(96,224),(128,129),(128,132),(128,136),(128,144),(128,192),(160,161),(160,164),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffff
def xsM:=roots_253.map (·&&&dom_253)
def gM:=goal_253&&&dom_253
def NN:Nat→Nat
|4=>4
|5=>69
|6=>234
|7=>282
|8=>122
|9=>27
|10=>4
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x6935f4cf752cde00170d
|5,0=>0xc4c1dbe2d5baf9a99a1a8f98e7e2307689e748707273c5c2ab55bc954c354f7fd4cf754c87f4a09d41e5d3ff2c3b2a1366ba34dfe31fcb2cde0292cf23cfe23b9221fa820e081efc31ee491da041ca311a8461a78b19a4a19a1118da818d9818c1e18942172c317044162bf161eb144c811a6e1165c108610f3980ea3e0dab00c4cf0b4fa0a7e309dd8099b5092350911908dfd06b320676c05dd004909041d003c42035f902ddb00fe500043
|6,0=>0x20fc62098a204301ef541eeb81e7411dfef1d9e91d93e1d3231ce921cac61c92c1bb9a1ba941b6a619d0319cc01986b18fa718e2e187371820f1820b17713174131679a161021570c150b214559144a413e2c13a1f12f31125d7123e911d9511b0e118af116f611404112b210c85107e810783105e210448100d50fbe60eeec0ec250e81e0e6f90e2f00ddfa0d9b80d73f0d5ef0cfa50ce6a0cb810ca8e0c75b0c6130c2520bb6a0b95f0b2a80b19a0afe50ae3f0a5c80a2880a0be09dbe09c7809b6509b410931e092c2090ec08c080833007fe107db807c96072700721b0705506c7006b3206536061b305f3a05d21057cb0524d051650501504ec804e1f0458f041bc03fa703f0e03c4203aeb039160378e036f90353d034a902b810266a021ef021c401f1401db901c8e01ac9019c80136700bc1009fc002220012e00053
|6,1=>0xc9cdfa0db89e96f8a5168a4868929a87c688652c828da80be77e5177e2207d86b7888f757d874ecb6d0516937563e8c6350c5e6965e2fd5cf9758cd2540b250c814e07f4de9c4db104d99c4c5184c2074b5a1496d746efe454fc4319b41e1740a993f7cb3ebbf3e0c83da163d6e53d3ec3cd913c1d439e6e395103929537ded3676d361e535f6d35c6e352023509e348f43416933d9433be333a9b3362832b003122f3091f308e2300732f5182f31b2d61b2d41a2d0d82cf4e2c7c22b4742adae2a42129e3829b3f296ef28e5228a662848c2831e282e5281aa277c72725e2623925ec725b74256fd2506e24307239ab232a82320d22d502278e2268321f2b2175b21651214122107f
|7,0=>0x1849e17fe817eba17d9a17c5117a07178f71789817772174be1693d1684a1652a162ab1620715cc615375150fb14fca14fb414c54148b11435e1402113de713d8f1333a12d0a12901122541214e11ea011b5b11886114761146e1106810f3810ef710d02103b81022a0fd100f8780eb1e0eab20e9140e3500dc9e0dad80d71a0d4730ce760cc540cb2e0ca1b0c5ce0c20e0ba240b9aa0b75e0b6830b1570a8200a7e90a7900a47b0a3340a2e40a0f609fea09e7c09d4309bec097c6090c208e8808d4308a5d0872d084bc07ffe07eb30734206e7606d0d06c830696b068d606838067cb066f0064a90618d05465052ab052a00514604d4f04bde04618044a0042ae0406303c7c039c50386803650031040300a02ffc02ed402e2a02b32025e5024090229101e7e01c3701b9e01b7101920017cf01645015c10125c00bc300074
|7,1=>0x66d4266b4f6461062a6361cec5f6035b1a35af0959e85596c858b2b538bd5233a516e9511904e1304bafc4a4dd4977648e7047c004727546c2946c15459a04477041cf640fb940e3640de83f35e3e5103e26d3d9863cdf23c9ff3c3043c2803a7603a245388013844837f7037b633660736587360e735bf3351773255631b693186d3178f3114a3007e2f6f32db412d1142c7472b9ff2ad352a0e8299fc2814e27fea274fb27477270b526ce026a9d266ff266a22659f25cee257f5256e724f1124eee24d4b243c0241c523b1a2382e236392325422fe522a732265f2235322194216ee2107f201692003c1fae31f8681f8611f64d1ef881eecc1eeb81ea1a1e3ed1e3c01d74c1d2381d1a51c68d1c35d1c3061bf151be781b33d1b16c1b09c1af761acf81abc11a6c01a4251a37a1a3131a00819dde1919b18cd818bd718729
|7,2=>0xeceb2cd805c63e0c4d26b8ebca71c49eebe9d1a998a6496f2e8d25c8a51685fb2849e783be7820d67e8fc7b1f3790f5774e475c4e714b86b1ce67ee967dc167994
|8,0=>0xa77a983bfa7cc7c6b83e5f8cd5d9f05bee458b2b4c0014a67347393439f8432c442f54419c4412c03ae79389d437f96351bb33e7c332e63240731926315982f94b2f6482e3752e3342d51c2c35e2b2e82ab6b2808527c6725ef7244a724139239be238e523267229482094c1e9ed1e21f1dfe01da3c1d5571c9481c8ea1bfcc1bd401bb071b667195ee195b7187c217e3a17aeb174851717616e5216d2c161a01571614f2613d2012f8812d6212716122891212f11ed411a3e119fb0fbe60f7e70f5ce0f4900e14e0df6b0df060d8a60cd780c9d10c60a0c5860c0e70bfb20a52d09b7e09476091f708c9e089a1087aa07fd007ced0768106eee0613f0597e04ea404bf20497003fdb036160326602f7102ade025140238901efa01c2f01a2f01860016bb00f8700f2200b9400a070027b
|9,0=>0xbafbba52b3628394740f4583538f2c347502f56c2d25d2b8431dbf91b12319afb1348412afe11d850ffe30e34f0af76061f5059bd0559a049470483d01ee9007760021e
|10,0=>0x7762c470632dca726091
|11,0=>0x1e31b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccccccccccccccccccccccccccc00000000000000000000000000000002222222222222222222222222222222222222222222222222222222222222222cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0003332333233323332333233323332333233323332333233323332333200000000cccccccccccccccccccccc00cccccc00cccc8888cccc8888cccc8800cccc8803322332233223322332233223322332233223322332233223322332233223322cccccccccccccccccccccccccccccccccccccccccccccccc0000000000000003333333300000000333333330000000033333333000000003333333300000000cccccccccccccccccccc8888cccc8888cccccc00cccccc00cccc8800cccc8803333333333333333330033003300330033333333333333333300330033003300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c33333333333333333333333300000000333333333333333333333333000000000000000000000000cccccccccccccccc0000000000000000cccc0000cccc0003330333033303330333033303330333033303330333033303330333033303330cccccccccccccccccccccccccccccccc88888888888888888888888888888888033002200330022003300220033002200330022003300220033002200330022
|0,1=>0xccccccccccccccccc8c8c8c8c8c8c8c8ccccccc0ccccccc0c8c8c8c0c8c8c8c00000000000000000000000000000000333333333333333333333300333333000000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cc880000cc8b333333333333333333333333333333333333333000000003333333300000000cccccccccccccccccccccccccccccccccc00cc00cc00cc00cc00cc00cc00cc032323232323232323232323232323232323232323232323232323232323232320000cccc0000cccc0000cc000000cc000000cccc0000cccc0000cc000000cc00033003300330033003300330033003300330022003300220033002200330022cccccccccccccccccccccccccccccccccccccc00cccccc00cccccc00cccccc03333333333333333222222222222222233333333333333332222222222222222cccc8888cccc8888cccc8888cccc8888cccc8888cccc8888cccc8888cccc888b333333333333333222222222222222233333300333333002222220022222200cccccccccccccccccccccccccccccccccccccccccccccccccccccccc00000003332333233323332333233323332333233323332333233323332333233323332cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc03333333333333333000000000000000033333333333333330000000000000000
|0,2=>0xcc00cc00cc00cc00cc008800cc008800cc00cc00cc00cc00cc008800cc008b3333333333333331111110011111100333333333333333311111100111111000000cccc0000cccc0000cccc0000cccc0000888800008888000088880000888800000000000000000330033003300330000000000000000003300220033002200000000000000000000000000000000cccccccccccccccccccc0000cccc0003333333333333333333333333333333333332222333322223333222233332222cccccccccccccccccccccc00cccccc00cccccccccccccccccccccc00cccccc0333333333333333333333333333333333322332233223322332233223322332200cc00cc00cc00cc00cc00cc00cc00cc00880088008800880088008800880089111110011111100111111001111110011111100111111001111110011111100cccccc00cccccc00cccccc00cccccc00cccccc00cccccc00cccccc00cccccc03333333333333333333300003333000033333333333333333333000033330000cccccccccccccccccccc8888cccc8888cccccccccccccccccccc8888cccc888b333333333333333333333333333333333330000333300003333000033330000cccccccccccccccccc88cc88cc88cc88cccccccccccccccccc88cc88cc88cc8b333333333333333333333333333333333333333333333333300330033003300
|0,3=>0xcc00cccccc00cccccc00cc88cc00cc88cc00cccccc00cccccc00cc88cc00cc8b3333333333333333333330033333300222222222222222222222200222222004400440044004400444444444444444444004400440044004444440044444403333333333333333330033003300330022222222222222222200220022002200cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cc880000cc880002222222222222222333333333333333322222222222222223333222233332222cccccc88cccccc88cccccc88cccccc88cccccc88cccccc88cccccc88cccccc8b333333333333333333333333333330033333333222222223333333322222200cccccccccccccccc0000cccc0000cccccccccccccccccccc0000cc000000cc0330033003300330033333333333333333300330033003300333333003333330044444444444444444444444444444444444444004444440044444400444444011111111111111111111110011111100111111111111111111111100111111000000cccc0000cccc0000cccc0000cccc0000cc000000cc000000cc000000cc00000333300003333000022220000222200003333000033330000222200002222cccccccccccccccccccccccccccccccccccccccccccccccccccc0000cccc0003333333333333333333322223333222233003300330033003300220033002200
|0,4=>0xcccccccccccccccccccc8888cccc88880000000000000000033003300330033000000000000000000220022002200220000000000000000cccccccccccccccc0000000000000000cc00cc00cc00cc0000000000000000033333333333333330000000000000000332233223322332200000000000000000000000000000000cccccccccccccccccc00cc00cc00cc00000000000000000333333333333333300000000000000002222222222222222cccccccccccccccc00cc008800cc0088cccccccccccccccc00cc008800cc0088000000000000000333333333333333300000000000000003333222233332222ccccccccccccccccccc0ccc0ccc0ccc0c8c8c8c8c8c8c8c8c8c0c8c0c8c0c8c3300330033003300330033003300330033333333333333333333330033333300cccccccccccccccccccccccccccccccccccccccccccccccc888888888888888b33333333333333333333333333333333333333333333333332233223322332200000000000000000000000000000000cccccccccccccccc88888888888888880001111000011110000111100001111000011000000110000001100000011000000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000888800008888000000000000000333333333333333300000000000000003333330033333300
|0,5=>0xcccccccccccccccc8888888888888888cc00cc00cc00cc00880088008800880333333333333333333333322333333223333333333333333333333223333332200cc000000cc000000cc000000cc000000cc00cc00cc00cc00cc008800cc008b333000033330000333300003333000033333333333333333333222233332222cccccccccccccccccccccccccccccccccccccc88cccccc88cccccc88cccccc8b300330033003300330033003300330033333333333333333333332233333322cccccccccccccccccccccccccccccccc00cc008800cc008800cc008800cc008a2222222222222222222222222222222333333333333333333223322332233224444444444444444440044004400440044444444444444444400440044004403333333333333333333333333333333311111111111111111100110011001100cccccccccccccccccccccccccccccccccccccccccccccccccccc8888cccc888a2223333222233332222332222223322222233332222333322223322222233220000cccc0000cccc0000cccc0000cccc0000cc880000cc880000cc880000cc8b30033333300333333003333330033333300332233003322330033223300332200000000000000000000cccc0000cccc0000000000000000000088880000888b333333333333333003300330033003333333333333333330022002200220022
|0,6=>0xcccccccccccccccccccccccccc00cc00cccccccc88888888cccccccc88008800000003300000033000000220000002200000033000000330000002200000022444444444444444444444444444444444444444444444444440044004400440000000003332333200000000333233320000000033323332000000003332333200000000000000000000000000000000cccccccccccccccccccccc88cccccc8b3223322332233223333333333333333332233223322332233333322333333220000000000000000000000000000000000cc00cc00cc00cc0088008800880088033003300330033002200220022002200330033003300330022002200220022cccc00cccccc00cccccc0088cccc0088cccc00cccccc00cccccc0088cccc008b33333333333333333333333333333333333333333333333333333003333330044444444444444444444444444444444440044004400440044004400440044022223333222233332222333322223333222233222222332222223322222233220000000000000000000000000000000000cc00cc00cc00cc00cc008800cc00880000000000000000000000000000000333333333333333300330022003300220088008800880088008800880088008800cc00cc00cc00cc00cc008800cc008b333000033330000333300003333000033333333333333333333330033333300
|0,7=>0xcc000000cc000000cc000000cc000000cc000000cc000000880000008b333333333333333000033330000333333333333333333330000222200002222cccc0000cccc00008888000088880000cccc00cccccc00cc8888008888880088000111100001111000011000000110000001111000011110000110000001100cccc00cccccc00cccccc00cccccc00cccccc0088cccc0088cccc0088cccc008a22222222222222222222222222222223333333333333333333322223333222200000000000000000000000000000000000044440000444400004400000044033333333333333333333333333333333330033333300333333003322330033228888888888888888cccccccccccccccc8888888888888888cccccc88cccccc8b300330033003300330033003300330033333333333333333322332233223322cccc4444cccc4444cccc4400cccc4400cccc4444cccc4444cccc4400cccc4403333333333333333333333333333333300003333000033330000330000003300cccc4444cccc4444cccc4444cccc4444cccc4444cccc4444cccc4400cccc44000000000000000003333222233332222000000000000000033332222333322220000000000000000000000000000000044444444444444444400440044004403333333333333333333333333333333300001111000011110000110000001100
|0,8=>0xcccccc00cccccc00cccccc00cccccc03333333333333333000000000000000033333333333333333333330033333300cccccccccccccccccccccccccccccccccccccccccccccccccccccc88cccccc8a222333322223333222233332222333322223333222233332222332222223322cccccccccccccccccccccccccccccccccccc4444cccc4444cccc4400cccc4400000000000000000111111111111111100000000000000001111110011111100000000000000000000cc000000cc0000444400004444000044cc000044cc000333333333333333333333333333333331111110011111100111111001111110044440000444400004444000044440000444444444444444444444400444444000330033003300330033003300330033003300330033003300220022002200220000000000000000cccccccccccccccc0000000000000000cccccc88cccccc8b333333333333333333333333333333300330033003300330022002200220022cccc0000cccc0000cccc0000cccc0000cccc4444cccc4444cccc4400cccc440000000000000000000000000000000003333222233332222333322223333222200000000000000000000cccc0000cccc00000000000000000000cc000000cc01100110011001100110011001100110011111111111111111111110011111100
|0,9=>0x22222222222222223333333333333333222222222222222233223322332233224444444444444444444444444444444444440000444400004444000044440003333111133331111333311113333111133331100333311003333110033331100000000000000000000000000000000000000cccc0000cccc0000cc000000cc00000000000000000000000000000000000000000000000003333330033333300
|_,_=>0
def sP:Nat→Nat
|0=>0xe08252a21050904292202200e1c230d28060504150311052708220d12201604031b050e26082524201a01082322020601080b1105160f040d02212001080d111f0e091c1e150a05100402060e1d0f080b11050e091c0d1b1a1619080d0216180904151105140f08070d0a05090d0c0601080b0a050908070605010403020100
|1=>0x206011c0d121b35100817230a050908221b1a34100822061a260904250328050e1325151b0516080a0533320908310d121b1608153102060108221b1a2e100829222805160825300501101c2b111a2610082530050e09130d1b1a26101c0d02012f10080d1b1a2e09081b0516192d1c2915280510040d020e2c0f1c252b061a
|2=>0x163e1c0d02300e100d0c1101100422061a260f083924200501040d111a3d0f080b0a05091c0d0630050e1c2524061a011c023b1b0e10043a0d021b0e0815220220161c0d2805161913251521050f1c392b1105160807060501380d111a100f080a0537320f0436150a050f040d0a05140f130d022106011c240d121b161c1524
|3=>0x4220d021b160e040d06050e420f1c0d28060516080d021b0e4110081724111a160f081e151105160f08242206111a0108400d0a0501101c252b111a0e100425030a050e0f0817152105100f082a240211160f08070d060501130d12060108292a1b05161c290d1b1a16083931060501080d0a053e09083f05013310080d1b05
|4=>0x21b160908250d4b1a160f08221105014910082522061a0e0908152202114a1013251506050e0f082211050e4909080d0a0514100f08480d111a0109080b11050e09080d11470e0908310d12060e0f040d06111a340f1c460d1105160e080d0a05453310043a0d02110e0f081522441105100839241105430f080b0d0a05100f
|5=>0x80d5211051609080d28061a01091c390d0605160f080d0a1b05511008152220110516080d111a011909082522061a160f080d022820160f0815241105500f1c4f0d0611050e1c390d0605011008310d0a060501080b1105160f08152211054e10082a0d0a4d05100815224c110510082522061a011004254811050e0f08150d
|6=>0xa05430f082524050e560f13250d21050e0f040d110516340f08252428050e0908241b1a26100f081531021101100825551b050e10040d110516180f080d020616340f080d1b0554011008390d1b0545101c230d021b0e10130d121b0e10080d120601090829151105430f080d1105165309082a241b1105161c240d12060e0f
|7=>0x823220a11050908240d0a1b0545080d124b160f08023b200e100f1c0d1b05160e190415221105451604250d211a160f1c240d061b1a0e1c3b1b11050e1004150d0206010f080d12162f100f1c0d02060e320f1c5a0d11050e1008021b0e1d100f0824020e59100f1c0d5811050110082a0d0a2005100824221b050e57082524
|8=>0x50e320815311b1105160829150206160f080d020e5d100f0825242005010e085c0d02060e0f04152202060e0f080d11051659090839031b050e101c15240211160f130d2806050e08220d0220160e1c5b0d021b0e10081e0d02200e101c1524021101101c252311050110082b0d12060e0f1c0d111a011810082524111a450f
|9=>0x822110516000908600d0a05160f040d03111a011c15241b110516080d0a055f091c0d0a0516190f08220d124d0e1004220d2806050e08152b0211160f085e0d110501091c240d281105160817151105451008242202111601043a0d0a11050f13170d021b0e10080d111a35091004150d061b05010825550a05100f1c0d061b
|10=>0x1a0e0f0839241b050e091c0d021600100f08240d121101091c2b11050e2610080d111f0e100f040d0221200e0f08230d024b0e0f1c0d11050e6210083a0d021b0e101c0d11050e611004290d02200e0f085b0d0605160f080b11050e100f08252b050e570f1c230d0a1b051008242202200e08230d0206010f083b11050e100f
|11=>0x29151b050e090415220a06050f081b050e192d10040d44111a160f08242212110e090417150a05100f1c0d0221060110042523111a160f08230d061b0501082211050e2f0908221b1a2610040d0311050e65082a24111a450f040d110564160f080d111a01371008220d0206450e0839241b0501101c0d11050e631008252420
|12=>0xf08250d061a430f08672211050110080d060516530f082515060501090825220a05160908672211050e09082530050e100f0815312111050f1c0d2811053210080d5206050e09080d061a26090f082522111a4a1008660d111a011008290d111a450f0829151b05011008290d2805160f1c4f0d02110e100817150228100f08
|13=>0x1a450108152b2111050f1c0d1130050e10082422211105011c0d021b0e3210082a240a06050f1c25152105100f130d0221060e0f130d281b1105161c2811050e1d100817230a05100f1c240d121b0e10080d0605160133080d1105163e0f082a0d121b0110080a053332100f130d020e00100f080d053518100f08153102060e
|14=>0x8242211050e561c6b0d11050e10080d0a050119091c290d111a160f040d211b1a160f082a0d0211160908390d4b05160f046a0d11050e0f08240d1206010f1c0d021b0e69101c290d110516011c392b11050e101c252a0a050110040d061b1a01040d211b051601130d21061b050e040d1206010f08152b02060e0f08242211
|15=>0xd1b05163c08242211050e6d080b0d1105160f0811050e1d100f081105542d100f081524061b0501082b110516000f040d032811050e083931110501100825152105090f08292a1105160f080d201105013208240d121b01100d0c110e100f0d1206166c0f040d121b011008250d200516010824224411050e08230d0a1b0509
|16=>0x10e10040d1105160e2f0f1c240d1b111a0e10080d44111a01100f1c1524110501100815310611050e0f1c240d0a1105160f1c0d11050e6e100f1c0d021b160e1004150d021101100f0823480d11050e0f04170d0a050e100f1c0d02110e32100f080d06050e65090825311b050e10081522061b050e1008290d12060e100f08
|17=>0xf08290d1b05010e10080d111a0171100f080d1b111a1609080d0221200e100f08170d02280e100f1c240d110545010e1c15241105160f080d11050e70100f08230d02060e0f04660d0611050e0f1c0d0a11054501106f0d11050e100f08290d02200e100f04220d0a06050e0f040d1211160f130d11050e00100f1c252a1105
|18=>0x1100f082a0d111a0109101c15240611050e0f04152202110e100f080d111a0e74100f08290d1b05160e0f081715021b0e100f08730d11050e100f08722211050110130d2811050e10080d1105640e09101c250d0a0516100f08290d0a0534100f1c670d11050e100f082523240a05100f08150d0a0605090f08290d0a060516
|19=>0xd1b11050e321008150d0a4b05100f1c0d442811050e1008310d2111050e0f130d210611050e0f08242211051601080d0311050e651004150d0a06050f04252a11050e100f1c25150a05100f080d06111a430f082b0d0a1105160f080d11056416100f08220d211b050e10080d761b050e100f08750d1b050e100f08550d111a
|20=>0xe0f08250d060516010f082422061105010e13390d11050e100f080d7811050e100f04150d1b1105160f0815220a0605100f1c251506050e100f040d21110516010f0817242011050e0f0817241105010e1008250d1b1a011008152b1105160f08250d0605010e0908240d1211160f08770d11050e100f04150d1b110501101c
|21=>0xd11050e6d1008250d4b05160e0f08230d021101100f08290d0a0501100f1c2b0d02110e10040d02281b0e100f085b0d11050e091008257a11050e100f080d211105010908480d1105010e0908290d0a050e090f080d11050e79100f08152b0611050e0f0825220a05011004220d2811050e10040d06111a010f081724110516
|22=>0x80d280605010e09082422200611050e08292211050e091c250d21050e100f08240d110516340f080d1105010e190908150d114d050110082522050e18100f087b2411050e100f085b0d110516100f08213b11050e100f08480d110516010f1c390d1b050e1008150d581105100f0825220605010e1008150d28110509100822
|23=>0xd28060516010f08150d441105100f080d1105013209082b0d2111050e0f13250d0a050e100f0829220a050e100f080d11051601190f080d02160e2f100f080d121b01101c0d0a110532100f080d11050e7c090f082422111a0110082a0d110568100f08240d06111a010f04360d11050e0f080d061a26100f080d020616010f
|24=>0x100f080d030211010e101c0d2806050e10081e1511050e100f08250d061a01100f04250311050e0f080d11050149100f080d06111a45010f08150d02114a100f08240d4b111a0e0f0825222006050e10082211050e26091008230d0a06050f04150d210611050f080d11050e49090f082a0d020e18100f081524110527100f08
|25=>0x80b11050e100f0817152211050110080d061b051601080d06110501320f08250d050e65091004250d110516010f0825244b050e0f04250d061a0e0f080d11050135100f083b11050e100f085c0d0a1105100f0825241105450e0f0415220a1105100f1c4f0d11050e100817150a1b05100f08400d0a050e100f08150d11054e
|26=>0x80d02060e34100f082a482411050e0f0825230605160e0f080d1b11050e7e100829230d0a05100f080d11050e530910082a0d1b050e1810080d111a2609100f1c390d06050e100f08310d0a06050e0f080d21110534100f081524211105160f08240d111a34100f080d11050e1d100f08242211050e6510080d11050e7d100f
|27=>0xd061b1a0e09080d11050e7f100f080d124b0e100f040d28110516010f080d0a0605010908153102110e100f08250d111a43100f080d120601100f040d021116010f080d11051653100f08251511050109101c0d211b050e10080d28061a01100f080d12060e090f04150d110545160f0425221105160e0f040d11050e18100f
|28=>0x1101100f08830d11050e100f080d02060e320f042a0d110516010f08240d02200e0f08152b02110e100f1c240d2811050e1004820d1105160f08390d0605160f08152211054510080d1105010e811008150d061105450f045e0d2111050e0f086a0d11050e100f080d11050e80100f085e0d110534100f1c29250d1b050e1008
|29=>0xf0825221b05160e10080d2011051601081105010e1d100f0823150d1105010908240d121101100f085e2211050e100f0815310a1105100f1c170d1b111a0e10080d1b050e34100f08150d280605100f040d06050e650f08290d1105450e0f08150d110584100f080d0a055f100f08220d11050e5010040d110516000f040d12
|30=>0x586100f08443b11050e100f080d4411050e100f1c0d02281b0e10080d11050e3e100f040d280605010e0f04220d02060e0f0825220a050e091008660d111a0e100f08850d11050e100f0824220a11050e09082011050e1d100f083b0611050e100f08242212110e100f1c150d281105011008240d111a430f080d0211013210
|31=>0x240d2811050e091c290d111a0e100f083111050e26100f088b0d11050e100f08390d4b050e100f1c290d1105010e10080d11050e8a100f08390d060501100f0811050e89100f0825152105100f08252306050e0f040d11050e88100f080d11050e87100f040d11050e53100f0824222111050e0f080d0a110532090f08150d11
|32=>0x100f088d0d11050e100f084411050e1d100f080b0d11050e100f080d280605450e0f08393111050e100f08240d0a1b05011008292a11050e100f13150d02110e100f080d1105163c0f0811050e1d100f1c2a0d111a011008230d06111a160f082b11050e26100f080d2111052d100f080d11058c0e100f080d0a060545160f08
|33=>0xf08220d281b11050e101c0d0a06050e100f08230d110501100f080d11050e53100f1c2b0d11050e10085b0d2811050e100f080d5211050e100f08250d11051601100f08230d11050e090f08250d061a0e100f08252406050e0f08250d4d050e100f08250d1105160e090f080d11050e49100f0811050e3332100f130d12110e
|34=>0x5010e091008220d02110e091008232211050e100f080d024d0e100f08250d20050e100f0825221105160e100f088e0d11050e100f08290d2111050e100f08232a0d11050e100f082a220d02110e100f082515110501100f080d0611050e320f04250d1105160e0f080d11050e35100f08240d2011050e0f082a0d0211010e10
|35=>0xd441105010e100f082a220d1b11050e10085b2a0d11050e100f08250d111a0e09100f08252411050e090f08660d1b11050e100f082a0d1b1105010e10080d031105010e10080d12060e100f040d0211160e0f080d2811051601100f080d11050e91100f080d111a0e19100f08900d11050e100f080d02111601100f080d2811
|36=>0xe00100f080d061105430e0f08310d0a11050e100f082a0d1105010e091008240d0211160e0f08150d0a1b05100f080d1b11051601101c0d210611050e100f08250d2805010e100f080d1105010e71100f080d1b1105160e0904250d111a0e100f080d02110e93100f080d0a0605160f080d02200e100f08920d11050e100f08
|37=>0xe100f080d9411050e100f040d12110e100f080d0a110501091004170d11050e100f080d03111a0e100f082a220d0a1105100f040d061105010e0f08390d110501100f080d12110e09100f08250d1b05010e1008153111050e100f0825231105160e100f040d110516010f080d442011050e100f08820d110516100f08221105
|38=>0x8240d200611050e0f08240d0a1105160f080d11050e69100f080d06110545010e0f04150d1b11050e100f08240d12110e100f08240d061105010e0f082b0d0a11050e100f040d200611050e0f08220d021b0e1008722211050e100f040d0a1105160f1c0d281b11050e101c152411050e100f04220d0611050e0f085e0d1105
|39=>0x10e100f1c0d021b0e100829252211050e100f08150d2011050e100f08230d1b11050e100f080d11050e32090f082422111a0e100f0825150a05100f080d1105010e19100f0815240611050e0f08150d114d050e100f040d11050e65100f08240d11050e34100f080d21110501100f08480d1105010e100f080d2111050e090f
|40=>0x220d0611050e100f080d11050e3c100f085e240d11050e100f080d211105450e100f080d20111a0e100f08240d0a11050e090f04390d11050e100f080d4c11050e100f080d4411050e100f08150d110527100f080d0a4b050e100f08234f0d11050e100f0d12110e6c100f08251511050e09100f08170d021b0e100f040d0211
|41=>0x611050e100f080d11050e32100f0829250d11050e100f080d2111050e100f08240d111a0e100f08290d11050e100f08170d1b11050e100f1c0d1b11050e1008250d0a050e100f080d111a0e09100f080d200611050e100f08240d1105160e0f080d0a110516100f1c0d02110e100f08720d11050e100f08390d11050e100f08
|42=>0x80d11050e100f080d11050e09100f080d0611050e100f080d02110e100f08250d11050e100f080d061b050e100f08242211050e100f082b0d11050e100f08252211050e100f08240d0a11050e100f080d0a11050e09100f04220d11050e100f080d1b1105160e100f080d1105430e100f130d11050e100f1c0d
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x7a0029400aa0005
|5,0=>0xc53061182fcc17860b9a85b582cec16160ae2855982a0c14a60a2304f98270c13260963049d4242c11b608ab043d8212c103607eb03dd81e2c0eb6072b037d81b2c0d36066b031d8182c0bb605ab02bd8152c0a3604eb025d8122c08b6042b01fd80f2c0736036b019d80c2c05b602ab013d8092c043601eb00dd8062c02b6012b007d8032c0136
|5,1=>0x1a760d128671832cc1906
|6,0=>0x1b038d65c6a4e34b71a238cf5c66ce32f719438c898638c315718738c1dc600e2f9717938badc5c8e2dd716b38b3dc590e2c1715d38acdc558e2a6614fb8a61c522e28a7141b89f1c4eae26e7133b8981c4b2e2527125b8911c47cc2386118b88a9c446e21c710ab8839c40ee20070fcb87c9c3d8c1e570ef3875dc3a0e1c970e1386edc368e1ad7
|6,1=>0x28db9451ca1cc5077280393e5c9e4e4ec6272b937d89b0e4d172653930dc978e4b572573929dc940e49972493922dc908e47d723b391bdc8d0e461722d3914dc898e445721f390e18862e42a7211b9071c82ae40e7203b9001c7f2e3f271f630f95c7bce3d771e838f25c784e3bb71da38eb5c74ce39f71cc38e45c714e38371be38dd5c6dce3677
|6,2=>0x36d39b4dcd98e6c5735f39addcd60e6a9735139a6dcd28e68d7343399fdccf0e67173353998dccb8e65573273991dcc80e6397319398adcc48e61d730b3983dcc10e60172fd397cdcbd8e5e572ef3975dcba0e5c972e1396edcb6ac5ae72d3b9681cb32e59272c5b9611cafae57672b7b95a1cac2e55a72a9b9531ca8ae53e729bb94c1ca52e5227
|6,3=>0xff6c7f473f6b9f99cfbee7d873e8b9f29cf86e7bc73dab9eb9cf4ee7a163cdb1e558f1ce78773c039de5cee4e76b73b239d75ceace74f73a439d05ce74e733739639c95ce3ec7187388b9c2d8e08e6fd737b39bbdcdd0e6e17
|7,0=>0x4f4c278613b309d274e54270dd37709b474d6ba696133b099584c6c261612fb097584b6c259612bb095584a6c2516127ce9377497c249e123f09178487c241e11ff08f78477c23a1d1c108d8846842325d18308ba7459422aa1146e89b8449c2235910b087d843ac21b610cb085e742b4213a108d083f741bc20be104f081f840c3a045d01308018
|7,1=>0x5ed42f4a17950bc285de32ed217590ba575cec2e56171ceb8775c03ade216e10b6975b0c2d6616a30b4985a0c2ce616630b298590c2c69d6250b0a858142bea15e50aea857142b6dd5a70acb8561c2af1d5690aac855242a72152aea8d85433a9fa14ed0a6e85334297a14ad0a4e8523428fa146d0a2e8513ba881d4310a117504c280613f309f18
|7,2=>0x6e643715db7cedb686d74369ddb3f0d9876c8436221b010d7886b8435a21ac10d5886a8435221a810d388698434a21a410d188688434221a010cf97678c33a9d9c50cda86694332dd988ecbc865abb2b6194b0c9d864b3b23a190d0c7e863b431bdd8cf0c5f862c3b14218910c40861c430c218510c21760cc304618130c0185fcc2fc617d4ebe28
|7,3=>0x7dd3becddf58efa487ce43e521f190f8487be43dd21ed90f6577aec3d561e9cef46879f43cda1e5d0f26878f43c5a1e1d0f07777fc3bde1de0eee8877043b621da10ec8876043ae21d610ea97750c3a661d24ee8a8741bb9f1dce90e6d7732c3979dcad0e4e8723bb901dc72ee318714c38861c330e118704c38061bf4edf286f5bb78e1bb8edd48
|7,4=>0x210b107e783b441ba20cd105e882b4413a208d103e881bbc0c1e052f021880cc40462013100187fcc3fc61fd30fe187ecc3f461f930fc18
|8,0=>0x94abca326509127c893a449ae64c5325a89294492a248332389917cc89e243f121789083c825e40311f898f7cc79a63bb31d588e64c70e637711b478d6bc6926339119488c64461222f7317388b5c4591e2b9115398a5c450a62733130989444482223111108884443fe61ed30ee88734437a21aef0ce9863442f6616b10ad88533c27a212b308d8
|8,1=>0x28e114679a2f4d15a289b34458a1ec50d6285b14258a0e4d055e819340489fe44fd9a7db33e499edccf4e279713c479ddccece275533a289cccce462711338089bbccdbe26cf135e99aaccd362689333b9999c4cb1e649131d798ac4c36260b12fd897ac4bb9e5cd12de896b44b36658b12bd895ac4ab6254b129c9
|9,0=>0x55322a89153c8a9a454ae6a45351a8a88cd4262a04f4fa8a79453a669c314d98a68c53226982f4b98a58c52a2694114988a48bd226290314789
|10,0=>0xab5c558e2ab8f5548
|11,0=>0x15737
|_,_=>0
def wAt:=mkWire dB 149 254 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x601040450e0f4403d451142439100f4144501114203d1110438410e0f43845220e414450d0f4403d110e434250f104383d131202025050a43c410e11434290e11444390d3c4180410114383d100f48c6c0e0f444410e054203d0d104183d011148c6c231b0384516114341905114183d0810440450e1142041060f41839111041445171604c4808094403d111043c39
|1=>0x810414292311c403d0d0f434451b0e4903d051143441240143c390d10464390d06840450d0a43845080941429110e4443d100f4403d050a444410f0e4443911014143910114383d080f43429110e4183d0e1b46c41110f414451027404470f0e434250f10434f10601044410e104383d0d11414390010454470d0e45c580d1b43c450d3c4180410114383d100f414f1
|2=>0xf1144039080f46c58110e43c450e1043c412516438410d1144439100f4144508094403d05114346d0f114c43922104343d0d0e414450d064444111104441508104343d0d0e4003d1511c34390e1044415080f434411b0e4242110114443d100f414450f104183f0a0543841101143845160f42041100e4343d081045845050e438410d11414390511440450d0e43c39
|3=>0xe0f434450d204183d111043c410e114346d1b0e41445110f4403d050a4343d110e4884508104343d0f08434450d16440210e10414390d0f414390f114943b0d11414390110434050e0f42445050e43c41250e4344508104183d060e4444105114183d0d0644415101142041220a444390d0f46c410d104343d110f414451511c3439050e420410e0f488430d0f43441
|4=>0x80f434050e0f42041050e440450f1143c39110f44459100e42041110f42025111043c41050a420410e0f440450e11404410d104383d050e48c6c151043439060e41839080f44441110542025111043c41080943c45050a4203d0e1143841290103419101144469050e4443d0d014383d0d11435a11611c40390d6845847100e48c6c240e43441240f43441112d43406
|5=>0x15104a843150f4343908104943d0d1146c3b10114443d100f4903d0f11434450d104083905114341910114443d0601044410e104383d0d0943c410a0543c39110e43c45131202025050a43c410e114204a0a0544441100e44439081042815110f43c39110e4843d0a1043845570f4183b10114383d25104203d0d1141439110f45845100e42041220e414450d0f43445
|6=>0xd1b46c39110f4144501104203d0f0e434410e104203d0d1043439101141445240e43441081044441080f404410f0e44439083c40418101143c3905114183d0d064444108104443910114343d020e41445100e420410d114203d0d014383d2311c20410d16438410f08414390f11434410e0f4203d0d10434390d104203d110f41445100e4203d0d0e420410e0f41445
|7=>0xd0e44441050e4583f0e104903f0d104cc390d1b83c450e115a4451b16840390f114355d060ec4045100f414390d0143c39080f4441508104343d0d0e4346d05114443d0d0e4343d0e0f454430d0e4202501114383d100f438cd0d1b8443d080f4a43b2411434410d6845847100e490390e11434410e11438410d0644441050e43c450e1043c41060f41839111041445
|8=>0xe0f43c390e11434450d0f404450f0e420410e0f414391011420410e1042041110f43439080f444590e0f440390810434411b104346d110f43c45050e4383d0d1144039240fc34410d0e438410d10408390511420410d1684039080f434391b0e43c45080f434250f1042025111043c41100e4343d0f0e434411011420410e1143439220e420410d0f44439080f43445
|9=>0x100e440451110404450e0f4343d060f4444125104403d0d0f43445161144039080f4a43b2411434410f0e434392a11c88390d0f4349d0111c3c39220a438450d0f4a8430d0143c39250e434450f114203d0e4b4183f11104803b110943c41240e414450d104203d05114903f0d1042041110f414450d28404450e0f4ac39240fc3441060e440450e0f4403d2a10c3405
|10=>0x250ec34450e1144045240e434410d0e418391011420410010454470d0e4a8470511488390d0f43441011143c39101151445090e4403d0d1683c390e1043c410d1142025110e4403d0f0e48c470511434590a054443d0f0e444390d168203d100e4541a1110434390d104343d0e0f414390e0f43441111041439100840c452210c343d050e44045250ec3445051143c39
|11=>0x50e44045081056c3b2a11434050f0e435100a0944439100f4350d160fc38410f10420410d0f48c3f080f454410d0e434390d1b43c451710c943d0d11418060f0e440452210c343d0511440451b0e43c45080f4a43f2510434451011414390e0f434452210c20410d0f434450010454470d0e4404501104383d050e404430f0e41445060fc4441050e4343d060f44441
|12=>0x150f434390d11434590e104b4410d018383d241149039110e434410d28804450e0f4a847220e4343d250ec1439100f4344515114203d0d0e488410d0f5783b0d21440290e11434390d1045845100e41439290ec90450d10458cf0e104346e110f434f106010383d111043439221143c390d0f44441110f4383d0e104384108104383d0d114183f1110434410d1143445
|13=>0x25104443d0d1143c45050e444410f10428150e114183f11104383d100e42041110e440450e0f4403d240f414450d1043445050e4583f0e1041429111043c39110e4403908104383d0511434a20a0f444390f1145845100e4203d1011404450e0f41439050a44439111043c41100843439160f438410e10420410d0f434452a11c543d0d0e4a43b05114341910114a843
|14=>0x101146c3b0f1143c410f6845847100e46c58110f44039110e4409d0111c3c391511c3439100e420410a05420410f0e4443911104345a0e10414451008440390d0143c390d104183d111041445240fc14450d10434411b0e43c45080f4403908104543f0d0e43429111044039110e43825100f4343d0d0e4906e0f114344116114403908104a43b290e490450d1043c21
|15=>0x100844045011143c390d0f444151011420410d204183d1110438450d1043c410d0f43510200e4183d050a4343d110e434410111434390f0e4203d0d1041439160fc38410d168384105114443d0e104343d0d1146c41110f4383d0e10435124511404410f10454410d0e414290e1143c390d1049459100e4344522104343d0d1b414390f114203d290ec94410d1144021
|16=>0xf1143441080941445100f434390601044410e104383d0d4482825110e4403d0d01438150f0e4203d050e444410d16438410d2084425100f44045160f44039110e40445050e4203d251043445080f494410d11434f306010383d1110428410d0e444390d11434451011490390d104983d250ec3445110e51447090e4403d1b0e43c21110f4144529010383d251043445
|17=>0x22114343d1b1043c450d10414450d0143c390d0f46c390f114203d1011438450e0f454410d0e434a20f0a43845080f4903f0d1043c290e114b4450d0183c39100e4383d0d114403d1510434391011414390d11444410d10434450d1146c43110f4403d0e10434450010454470d0e42025050a43c410e1142825110e4403d11014444101104383d22104343d0f0e44439
|18=>0xe0f488430d0f44045020e41445051144039081044039011143c392206840450d0f4341a1110414392509c403d0d11440390e0f4144501114383d100f414450f104343d15104343d0d0e414451b10c443d09114403d0d11438410d0f434458f104943f0d11418390d0644045150f454410d0e41445220e4343d0d0e4383d0d11440450d16840391008438410d1145c3b
|19=>0x11104583f0e104384522104343d100f434050e0f434410e1041445110e4443d0d0e4443d0e0f43841080f418391011404450e0f434450106844410f11438410f1042041050e4344505114883b0d0f44441100e444391b104443d0511435951b0ec3c454511404410e0f488390f114343d220e4343d050e4403d0d1143c410d104344517104346d110f4443d0d014383d
|20=>0xd0f43439081044039110e46c390f114203d080f434410d0e4204110114343d290e490450d10439351b10c443d081040839051143c410f0e4443908104943d0d11414392210c343d220e444390d0f4383d1011420410e0f494390d11414290f10438450f114383d0d11488410d0f434390d1143459100e4383d100e42041110943c410e104543f0d0e454470d0e4343d
|21=>0xd16838410f10414390d104343d0d0e444390d114383d0d06844411110434410d0e434391b10c443d100846c3b0f114a43b2411434410a1043c39110e4a8430d014383d1611438410f1043441060f444410d1044039110e46c5a0e104443d1110404410e0f42041110f434390d10408390511444410f0e43441110e4903f0d104183d1011420410d0f4443d051145443
|22=>0x511454430d0e494390d11440450d0f418040e0f44441240a444390d1045845160f43841060f44441050e44439100f434410810494390d114a0430f0a438450a0944439100f434390111c3c390e114183f111048c3f1510434391208c08390511434450f104343905114346d0f11414450f0e42041110543c45080f494410d0f43445060f444410d0e4443d151043439
|23=>0x403d1110414450d114443d1110434410d0f4903f0d104343d0d11444390d1044439100f420410d0f43841110f4583f0e1047041080f44045080f4345a0e10494410d11440290e11414390d10494410d114346d110f43c45080f444390d114403d050e4183d1110440390d1044039110e4203d
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0xa00000000000
|5,0=>0x4ac0000119000003ac07040ba80000000058400000000000000000000000000000000000000000000000000000000000000000000000000000001510282000009880000000000000001210000000008880c5016200000000000000000000000065000000000000000000000000288000
|5,1=>0x5a4000000002b2
|6,0=>0xf2200003b187330000000038186e200001a5432280000000000000000000c08174c00005c1000000002c205530000000029904e500000000000000000000000000000009840000000049308c6000020a83c500000000000000000000e4c00000000702000019a80000000000000000000000000019082f3
|6,1=>0x6428000000031880000c1517a82e140000000000000005a98b4116622c840000ad5000000005518000000029900000000000028544f18000134825540000000000025040000000000024c4000000011ca000000008a410aa210400007f50fa400000000000000000003e087b10f4200000000000
|6,2=>0x480c8e211b1000000008ba11612266439400000000000000086890a3000000000001073208640880000ff300003f847d98fa100003e440000f540000000000000001e283b8c7688e850000000071a80001be800000000000000000006e18da20000000000000001aaa00000000000000034146698000
|6,3=>0xb42800000000000000000000000000b31000000000000b1215d52b0a54d400015030000534c00014c129265114a09800000000000000000000004f509c2934426084ad400012740000490c9188000
|7,0=>0x42668449071a0a4000081910199ff43f687e48fb19f513e287b8c0001ea43d22795000000003c280000eea1d943ac67544e919cf339860000e42000000007110e021bc437086d100001b0435c46a90d321a2433c8669000019643248639000018a400006208000184430085f10bc980002ea85c5000016d4
|7,1=>0x540800014f8a9c35308a54d491a8e40000a29143228244fc89ecd3c1a7444e269b8d368a6c14d26998d31980004c0697112c980000000958c0002533000093d1261a49348c690911f98000000000011da238346880000000000000000001182000045e28ad113a0000446887d000021b4000086850b9a161
|7,2=>0x6ce8d8d1afa35c30000d611aa235046988d211a29b41467c6cecd9c1b3446626cb8d952327364a4c8518ea31a30000c6458aa311461a8c250000000060a8c0517ea2f945ea8bc8d788aef25d68ba0d729ae235be6b6d16c1ad445a08b34d64a2c635866b00d5f12ba456c8accd57a2ae15566aa0d5220000
|7,3=>0x82e904d207a40c30000000205880008106000000040448008ff11fc200007ea60001f8a00007dc6fa91f323e247be6f6d1eba3d437a26f351e51bc827888f04c0003bd47782ee4ddaa3b2375c8ea900003a647448e791cd9b9747268e3d1c5a38830000e14c00000007028df51bca00006ea8dc8db7236b3
|7,4=>0x44b40001120c000444488450f9000043a486c90c9217242a400000002139c234844307900000000000106cc0000000
|8,0=>0xa107418a819d0039fa73e8e7b9cf439e273b8e759ce839cc538ce701cdd39b4735ce6a1cd1399c7330a649cc639867300e5e9cba396e72d0e589cae395672a0e529ca2393e7270e4c9c9639267240e469c8a390e7210e409c7e38f671e0e3a9c7238de71b0e349c6728c87184e2f1c5b38b07154e291c4f3
|8,1=>0x2db1db33b6076b4ed51da73b487684ecf1d9b3b307654ec91d8f3b187624ec31d833b0075f4ebd1d773ae875c4eb71d6b3ad07594eb11d5f3ab87564eab1d533aa07534ea51d473a887504e9f1d3b3a7074d4e991d2f3a5874a4e931d233a407474e8d1d173a287444e871d0b3
|9,0=>0x17b4af595e92bce5794af195e12bbe5774aed95d92bae5754ae995d12b9e5734ae595c92b8e5714ae195c12b7e56f4add95b92
|10,0=>0xbe437c46f80def1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x84000000002000000000062000000001651000000029c4000000081000000002000000000060000000001400000000040000000000a000000000240000000008c000000002200000000084000000002010000000080000000001800000000058000000001200000000040000000000a000000000240000000008000000000180000000005000000000100000000002000000000040000000000e000000000040000000000
|1=>0x288800000009a01000000268000000009041000000229000000008760000000219400000008630000000214800000008410000000208c00000008220000000208000000008140000000202c000000080a0000000201400000008020000000200040000008000000000148840000004a3100000011080000000424000000010800000000410000000010100000000402000000010000000000380100000008c000000002220
|2=>0x100000000003f341000000f49840000036341000000bc904000002d269000000b4984000002c260000000a480400000208200000008080000000200000000007498c000001c00e0000006dd84000000fa61000000389c4000000de6000000036ba4000000da6100000036924000000d60000000034b28000000d26300000034984000000d24100000031980000000c26000000030904000000c20000000030100000000c020
|3=>0x48080000001200200000043c984000010f24100000436320000010d2610000043100000001080000000041e8040000105a61000004143e000001001400000040010000001000200000040000000000ad361000002a9c8400000a02f200000270938000008d3e300000234f2400000803c2000002000200000063801000001740a4000004fa41000001284000000048000000001180000000044000000001020800000040020
|4=>0x200000000004ac72900001235da4000042d629000010a0880000042020000001049d84000040f66100001035984000040d02000001004000000040022000001000800000040002000000a34f2800002850ca00000734984000018d76100000634d8c000018c3430000053490c000014ca00000005229000000148080000005160c4000012f261000004b4904000012b841000004a8c00000012a2200000049d0800000125242
|5=>0x4110000000102dae9000040b49840001029a01000040802c800010200200000407498400010143a200004034b8c000100d26100004028c000001008660000040000000000c8f761000031259840000c0f6610000302d9840000c0742100002620c840000908020000024021000000880e6100002125984000084402000002035984000080d261000020200800000808000000020179840000805e21000020100000000800200
|6=>0x841498400020ad271000082349c40002048000000081143e0000202d271000080363cc000200d2e9000080349cc0002008061000080100000002000220000080002a000020000100000602d98400018092610000512598400014494680000503498c000140d06100005000800000124d2ee00004620d04000116000000004534904000110da410000443498400010dc30100004234d840001080301000041288800001044001
|7=>0x100020040002050d22100081404888002012fa41000804bc984002012f241000804b4904002012c14000080434320002000d66100080020880002000242000080001004002000024000080000004002000000000040850e08000800508a000100b4b0800040250c00000d234984000340d2610000d020880000300d2730000a12888000028482200000a11088000028440200000a01088000028040000000910d004000240d671
|8=>0x1024248880040908220001024169840040905271001024149840040905061001024109800040854231001020b5884004081527100102028000004042d671001010b5984004042d261001010b4144004042c040001010a6144004042822000101090100004040d8710010043c884004010d2710010043488c004010800000100074884004001d0a3001000549c4004000f26100100038884004000d279001000349840040008200
|9=>0x1004138100040104a22001004120080040101d32301004034984040004d2610100003498404000084000100000108002020080610080063cd840180004000004800209000100145a2100400402180010004c800002800808000081109a41002040b6984008102d871002040b6184008102d2e3002040a218000810250f2002002b6984004214001100108036044004200d271001080169c400420052f90010242c0840040909601
|10=>0xc8040274d84800101d263160008349ac301029c3ca06000634ba8180010d2a806000234bac180002d2ea06000034ba8100020daea040000b6b0805a000d26101680000800040105d36101004170c04040104e200
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x10000000
|5,0=>0x7000001e0000000002900032001100c5c000005800000000000000000000000000000000000000000000000030b0000600000000003000000607018000000000000014000000000000000600
|6,0=>0x176000006400d3099dc0000000000a030b00c00240000058000015400000005046000930810000000c00000005800007600000723900c000d4f8000000000002c54388000000018001e2c000000a19003bc3a000000000003108c0016000004e040002c3c3c0000000000000000000d00000050c0007c3d000000000000100000048018000000001000000000623
|6,1=>0xae00000000000000003c0000000086d772400004000100054079d0460000000000000190d2732a9a80060000180600000301e5f0000008b308a94000000000e2050000000051b07800230017c1e160000c00120000000001203c3e78000012a001200000080000008190580000000a00000000001c4600
|7,0=>0x9000a8a0650b00adb000c26c96402fcad0f06154a8b35208c460050a64080000010000500418422316211aa0000001c204358000000000006e000bbe0800067468014a0005858549a078ff26001bc58517b87846031681400a80b05000006580144c41185d34058a8021c00001ede41230c14011f694c086071052c00dc800c5e1180007800b8068041e00974940094
|7,1=>0x23206402300000060002000013c0e2d4dc00078005400160967a75028e1780f5581c0a1e6a01400c90b010f80456a4400fd724a01e35552b90e0f00010000079c34960076994d00f3c925182300170c745988bc469371420583411b712c260f3c50492002cc5c4674b200000194453c10238b02c1e15b2c1e040ad041e296b0151004052e833213f015485f318126400
|7,2=>0x14c0001000420f0fc003342918ceac000001e890185000000003c0000
|8,0=>0xb2f499af836b29cd11525b8cd3494cd3653a2045221da44b02c45d68c34dbe9c6fc94c2cf48a1d51c6b0393ba14735a1459bcf69dd24cceb6c39ce0afa333e471e47d0d46d07c93dcb0968b1d06c107b193ad7434a96d2f734e09d0c7fb99bf4846cfcb25a4ba2e80d98e2de56394bbd450e658bf91c479639a7c5e8dce60f379d1063a9c8a33076a6
|9,0=>0x2f6490170410a0dd629ea9e5d3d44df702893a9729826cb6147d29a9d60da
|10,0=>0x261649097
|11,0=>0x47
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 42 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_249 10 roots_249 ops++addP pm 1 dom_241 8 roots_241 ops++addP pm 2 dom_208 4 roots_208 ops++addP pm 3 dom_248 8 roots_248 ops++addP pm 4 dom_45 5 roots_45 ops++addP pm 5 dom_237 9 roots_237 ops++addP pm 6 dom_125 9 roots_125 ops++addP pm 7 dzo_57_4 5 roots_57 ops++addP pm 8 dzo_212_32 5 roots_212 ops++addP pm 9 dom_252 9 roots_252 ops++addP pm 10 dom_228 5 roots_228 ops++addP pm 11 dom_61 7 roots_61 ops++addP pm 12 dom_221 10 roots_221 ops++addP pm 13 dom_244 7 roots_244 ops++addP pm 14 dom_189 9 roots_189 ops++addP pm 15 dom_245 9 roots_245 ops++addP pm 16 dom_93 8 roots_93 ops++addP pm 17 dom_181 6 roots_181 ops++addP pm 18 dom_124 6 roots_124 ops++addP pm 19 dom_157 8 roots_157 ops++addP pm 20 dom_188 6 roots_188 ops++addP pm 21 dzo_121_4 6 roots_121 ops++addP pm 22 dom_229 6 roots_229 ops++addP pm 23 dom_236 6 roots_236 ops++addP pm 24 dom_117 6 roots_117 ops++addP pm 25 dom_109 6 roots_109 ops++addP pm 26 dom_120 5 roots_120 ops++addP pm 27 dzo_153_4 5 roots_153 ops++addP pm 28 dzo_213_32 6 roots_213 ops++addP pm 29 dom_180 4 roots_180 ops++addP pm 30 dom_173 6 roots_173 ops++addP pm 31 dom_53 4 roots_53 ops++addP pm 32 dom_60 4 roots_60 ops++addP pm 33 dom_213 8 roots_213 ops++addP pm 34 dom_116 4 roots_116 ops++addP pm 35 dzo_249_4 7 roots_249 ops++addP pm 36 dzo_185_4 6 roots_185 ops++addP pm 37 dzo_220_32 6 roots_220 ops++addP pm 38 dzo_217_4 6 roots_217 ops++addP pm 39 dom_217 9 roots_217 ops++addP pm 40 dzo_221_32 7 roots_221 ops++addP pm 41 dom_25 4 roots_25 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_57_4_25 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_212_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_121_4_25 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_153_4_25 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_213_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_249_4_25 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_185_4_25 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_220_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_217_4_25 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_221_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_25 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_249 10 s (0,roots_249.map (·&&&dom_249)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_249 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffffffffffff0000000000000000,64),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_253==dom_253)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_253 gM v ys):RunD true dom_253 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_253 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 69 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 69 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 234 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 106 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 234 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 282 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 26 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 282 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 122 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 122 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 27 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 27 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 4 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_253 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_191:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_iso_b isoMvS_191 (by decide +kernel) lowS_127
def isoMvS_254:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 11:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_247
def dzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
def gzo_215_32:=0xff00ff0000000000ff00fe0000000000ff00fe0000000000fe00fa00000000
def gsh_215_32:=0xff00ff0000000000ff00fe0000000000ff00fe0000000000fe00fa
theorem lowS_zo_215_32_210:Lower true dzo_215_32 roots_215 gzo_215_32 9:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_32) [(dom_215,32)] (by decide +kernel) (lower_slice_b (T:=gsh_215_32) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xf000f00000000000f000f00000000000f000f00000000000f000f0,0,4)] (by decide +kernel) lowS_210)
def dzo_173_2:=0xcccc0000cccc00000000000000000000cccc0000cccc
def gzo_173_2:=0xcccc0000cccc00000000000000000000ccc800008800
def gsh_173_2:=0x33330000333300000000000000000000333200002200
theorem lowS_zo_173_2_45:Lower true dzo_173_2 roots_173 gzo_173_2 6:=lower_iso_b (d1:=dom_173) (r1:=roots_173) (T1:=gsh_173_2) [(dom_173,2)] (by decide +kernel) (lower_slice_b (T:=gsh_173_2) [(0x33330000333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_45)
def dzo_222_32:=0x5555555500000000555555550000000055555555000000005555555500000000
def gzo_222_32:=0x5555555500000000555555540000000055555554000000005554555000000000
def gsh_222_32:=0x55555555000000005555555400000000555555540000000055545550
theorem lowS_zo_222_32_210:Lower true dzo_222_32 roots_222 gzo_222_32 9:=lower_iso_b (d1:=dom_222) (r1:=roots_222) (T1:=gsh_222_32) [(dom_222,32)] (by decide +kernel) (lower_slice_b (T:=gsh_222_32) [(0x50505050000000005050505000000000505050500000000050505050,0,4),(0x55005500000000005500550000000000550055000000000055005500,0,8)] (by decide +kernel) lowS_210)
def dzo_109_2:=0xcccc0000cccc0000cccc0000cccc
def gzo_109_2:=0xcccc0000cccc0000ccc800008800
def gsh_109_2:=0x3333000033330000333200002200
theorem lowS_zo_109_2_45:Lower true dzo_109_2 roots_109 gzo_109_2 6:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_2) [(dom_109,2)] (by decide +kernel) (lower_slice_b (T:=gsh_109_2) [(0x3333000033330000000000000000,0,64)] (by decide +kernel) lowS_45)
def dzo_61_2:=0xcccccccccccccccc
def gzo_61_2:=0xccccccc8cccc8800
def gsh_61_2:=0x3333333233332200
theorem lowS_zo_61_2_45:Lower true dzo_61_2 roots_61 gzo_61_2 6:=lower_iso_b (d1:=dom_61) (r1:=roots_61) (T1:=gsh_61_2) [(dom_61,2)] (by decide +kernel) (lower_slice_b (T:=gsh_61_2) [(0x3333000033330000,0,16)] (by decide +kernel) lowS_45)
def dzo_223_32:=0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def gzo_223_32:=0xffffffff00000000fffffffe00000000fffffffe00000000fffefffa00000000
def gsh_223_32:=0xffffffff00000000fffffffe00000000fffffffe00000000fffefffa
theorem lowS_zo_223_32_210:Lower true dzo_223_32 roots_223 gzo_223_32 10:=lower_iso_b (d1:=dom_223) (r1:=roots_223) (T1:=gsh_223_32) [(dom_223,32)] (by decide +kernel) (lower_slice_b (T:=gsh_223_32) [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,0,1),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,0,4),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,0,8)] (by decide +kernel) lowS_210)
def dzo_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000
def gzo_219_32:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0e000000000f0e0f0a00000000
def gsh_219_32:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0e000000000f0e0f0a
theorem lowS_zo_219_32_210:Lower true dzo_219_32 roots_219 gzo_219_32 9:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_32) [(dom_219,32)] (by decide +kernel) (lower_slice_b (T:=gsh_219_32) [(0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a,0,1),(0xf000f00000000000f000f00000000000f000f00000000000f000f00,0,8)] (by decide +kernel) lowS_210)
def dzo_189_2:=0xcccccccccccccccc0000000000000000cccccccccccccccc
def gzo_189_2:=0xcccccccccccccccc0000000000000000ccccccc8cccc8800
def gsh_189_2:=0x333333333333333300000000000000003333333233332200
theorem lowS_zo_189_2_45:Lower true dzo_189_2 roots_189 gzo_189_2 7:=lower_iso_b (d1:=dom_189) (r1:=roots_189) (T1:=gsh_189_2) [(dom_189,2)] (by decide +kernel) (lower_slice_b (T:=gsh_189_2) [(0x333300003333000000000000000000003333000033330000,0,16),(0x333333333333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_45)
def dzo_253_2:=0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def gzo_253_2:=0xccccccccccccccccccccccccccccccccccccccccccccccccccccccc8cccc8800
def gsh_253_2:=0x3333333333333333333333333333333333333333333333333333333233332200
theorem lowS_zo_253_2_45:Lower true dzo_253_2 roots_253 gzo_253_2 8:=lower_iso_b (d1:=dom_253) (r1:=roots_253) (T1:=gsh_253_2) [(dom_253,2)] (by decide +kernel) (lower_slice_b (T:=gsh_253_2) [(0x3333000033330000333300003333000033330000333300003333000033330000,0,16),(0x3333333333333333000000000000000033333333333333330000000000000000,0,64),(0x3333333333333333333333333333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_45)
def dzo_237_2:=0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc
def gzo_237_2:=0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000ccc800008800
def gsh_237_2:=0x333300003333000033330000333300003333000033330000333200002200
theorem lowS_zo_237_2_45:Lower true dzo_237_2 roots_237 gzo_237_2 7:=lower_iso_b (d1:=dom_237) (r1:=roots_237) (T1:=gsh_237_2) [(dom_237,2)] (by decide +kernel) (lower_slice_b (T:=gsh_237_2) [(0x333300003333000000000000000000003333000033330000000000000000,0,64),(0x333300003333000033330000333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_45)
def dzo_125_2:=0xcccccccccccccccccccccccccccccccc
def gzo_125_2:=0xccccccccccccccccccccccc8cccc8800
def gsh_125_2:=0x33333333333333333333333233332200
theorem lowS_zo_125_2_45:Lower true dzo_125_2 roots_125 gzo_125_2 7:=lower_iso_b (d1:=dom_125) (r1:=roots_125) (T1:=gsh_125_2) [(dom_125,2)] (by decide +kernel) (lower_slice_b (T:=gsh_125_2) [(0x33330000333300003333000033330000,0,16),(0x33333333333333330000000000000000,0,64)] (by decide +kernel) lowS_45)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,18),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,24),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,28),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,17),(16,18),(16,24),(16,80),(16,144),(20,21),(20,22),(20,28),(20,52),(20,84),(20,148),(32,33),(32,36),(32,40),(34,35),(34,38),(34,42),(34,50),(34,98),(34,162),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,68),(64,72),(64,80),(64,192),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,130),(128,132),(128,136),(128,144),(128,192),(160,161),(160,162),(160,164),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|6=>4
|7=>41
|8=>143
|9=>254
|10=>157
|11=>40
|12=>7
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x8db554d4f32d2c60cab2
|7,0=>0xc83c6bf0809bd9f8d0048ccbb88a678099d73a466d4f86c41161a4b60d605ffc255ee150761502ff4f42544383327f331a5830ca32d74229087286aa2375f2299f1f67b1c1b318b4718afe15bf315b9814f78141fa0b48505ee905d7705b7b0488e0243f01e1d
|8,0=>0x836f68213981d7e8079b807407d69c7686c717866964a65367626b761cff60bbb600885f60f5df885c8a55bdc25b56a5a85a5a5b258265581ea564b85613354fb052baa508a84f36f4ebf54e7de4bb4d4787b474cf45f92457254538c44d56440db4335d414be3e05a3dde03d2953c7793b9c93a36837e0c37973372d136e0f3354d311b030f80303652f31c2d9022d7e12b7242aeef28b8f283aa281ed26c7224fc024f6624bda24bbb2464323aa123a4a2159020e052034e1f7771d4131c48a1c19c1bf561b1791a4a21a1e7199171973c194c4173891606214895147ac139d1136a9133601309e12f9e12f6b12cd91294e1267911e0c100a40f5400ef780d0c30c7030b7250b2010af1f0a36d0a2600928d0910e07943078770735f06de505afc05a7404e6c0467a0459503e8a03738035a701f9100953008ef0024f000c2
|8,1=>0xee7b3e7112e39ecd8a19c95e0c8fefc0f44b165aa4070a0b4199b5d95628894ce8933d84fe0
|9,0=>0x3608335c7a352d63508f3503d33ab43368d3270a31cd1318cd2f2fb2f08c2e9b82e3b02df1c2dbbf2d9082c49d2bc072b84b2af772a9e82a6a029df529c3529b35294da28a1227b38276dd26a762603c25eaf259cb24f912464323750235972227321ac9212391fbac1e7401e3b91d66b1ceab1ca631c9c41c1c91bc721ac291a1ae1a17f19f4019b4419ad918d3218721186831825f1664115e8815e4615c8a15bdc14c741464d12e77128501239c11fa911d9e11816115151071310534103e0101350fc030fa890ecdf0ea3d0e73c0e70a0e11b0df480def50d8c00d5600d3380d2d70d1a80cfd20ccb80c9e10c6250c2350c1630baba0b6850b6620a4b80a2ee09ea509d6d0977009002087de0801e07f5806de506c03063d705db805485043e5041dc037670354802d1002469023dd01b9d012c800bbf00636003500028d
|9,1=>0xe462dd9f49cf2e0cce55bdb7ebd543b5719b3e86af525a397aa2b6fa236da088ca077d9f1579ec3b9b7819946098ff39762f975ba96457933b18e42c8d1808cdd58b9ad89ce5868f48591385822853e5842e4840938341a83384830d180a6880965806bd7f1e47a86979e17797cc7957b77f4876bdd7690e74f1574e5873bbd72e086da656d6f86d63b6c34a6b8306a65069fd0696866698364f8a64e476452163dd161e4861a81606dd60517600885f0be5efb25e09e5d5f65c47659ad85914b58fca57a9956a4d561525514354d53538ec52bad4ff684f6944ef444d5534a0b2499c548cd94889f4851a475e946fb84675a4529d4517043f6b4399d42f7841b43412c540afb3ffb53f6363ed2b3cc873bee03bb943b6293ad3b39a80394d0391aa38a58388b43814c37bc737100366dc3650d364c2363d93637b
|10,0=>0x72e4f70f49704576a81268acf683876798f65bfa64c055f8735c7e75c4865c3b75bd855b39f5a659590b055fef559855433753c42539b053855534fa519e550f284c1b34aa574a52148e3448906475f84752a46f17442233fe1b3fa223e9b03dea83d89f3bdac3b8253a6893a5bb396a83929a3841637330369fd3686a35bca357d03535f33bd63344332aec325733239c3179030ef0305e82f9452f5cb2f10d2e7eb2e5912e2422d9e128f9c28a12285742670d2601225e5b257fc2331e224a32226320cdf1f5c51f0751e6001e5b61dc5f1d50f1d21f1ca521b6501a89c19be91892417e6716e58153c41408e1306e12fd50ebf90c8f50c5760c3270bec70b9450b2520ae4a0abd00a7380a1e809c8509b46095cc09306085cc077750681205c9b055cb04bb804a15039c602e5a02a63020cd010d70105d00f2500c6600023
|10,1=>0xcb3a5c79cfc5bd2c567cc16c7bce68b2b42b0d45aec44ab92dab270aa74faa1dfa60e19d02c9c32d9c10c9abfe97ebb9722196f548fc158f6928ad2585d71812aa804bc7f5677a726
|11,0=>0xf2c3fdddb2d27679bc5297a6391de1904578f53a8302e78aa276ca5736917117c707e7703a56f8866d16d6b370668d76551f5cbf951a4a4ea874833a47d6c37d3b3799a348f53345b31fd22e2232b4a5212a3146c10cf1909eab0902c07b3604b760369c
|12,0=>0xc88288fd7c792e463c1561e180c4160c075
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000fffefffefffefffefffefffefffefffefffefffefffefffefffefafafffefafaffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeaaaaffeeaaaaffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff0000000000000000000000000000000000000000ffffffffffffffffffffff00ffffff000000000000000000ffffffffffffffff0000000000000000ffffff00ffffff00ffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ff00
|0,1=>0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaaffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000ffffffffffffffffffffaaaaffffaaaa0000000000000000ffffffffffffffff0000000000000000ffffaaaaffffaaaaeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000eeee0000eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaafffefffefffefffefffefffefffefffefffefffefffefffefffefff0fffefff0ffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeff00ffeeff00ffccffccffccffccffccffccffccffccffccffccffccffccffcc0000ffcc0000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000
|0,2=>0xffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00ffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00fafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa3333333333333333333333333333333333333333333333333333222233332222ffffffffffffffffffffaaaaffffaaaaffffffffffffffffffffaaaaffffaaaaff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff00ff33ff0000000000000000000000000000000000ff33ff33ff33ff33ff33ff00ff33ff000000ff330000ff330000ff330000ff330000ff330000ff330000ff000000ff0000000000000000000000000000000000bbbbbbbbbbbbbbbbbbbbaaaabbbbaaaa0000bbbb0000bbbb0000bbbb0000bbbb0000bbbb0000bbbb0000aaaa0000aaaaffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffff00ffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff03333333333333333333333333333333333333333333333333333000033330000
|0,3=>0xffffffffffffffffffffffffffffffff0000000000000000ffffff00ffffff00ffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeecccccccccccccccc0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff00000000ffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000ffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa0000000000000000ffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaff00ff00ff00ff00000000000000000000000000000000000000000000000000ffffff00ffffff00ffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaabbbbaaaa3333333333333333333333333333333333333333333333333333330033333300ffffff00ffffff00ffffff00ffffff00ffffff00ffffff000000000000000000ffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaaaaaaaaaaaaaaaaa0000000000000000bbbbbbbbbbbbbbbb0000000000000000bbbbaaaabbbbaaaa
|0,4=>0xff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ff00ff00ff0000000000000000000000000000000000ffffaaaaffffaaaaffffaaaaffffaaaaffff5555ffff5555ffff5555ffff5555ffff5555ffff5555ffff0000ffff00001111111111111111111111111111111111110000111100001111000011110000bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaabbbbaaaabbbbaaaabbbbaaaaffffffffffffffffffffffffffffffffffffffccffffffccffffffccffffffcc00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00ff00cc00ff00cc00ff00cc00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff00005555555555555555555555555555555555555555555555550000000000000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff0000000000000000000000000000000000000000ffffff00ffffff00ffffff00ffffff00ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000ffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff0000ffff00000000555500005555000055550000555500005555000055550000000000000000ffffffff00005555ffffffff00005555ffffffff00005555ffffffff00000000
|0,5=>0x333333333333333333333333333333330033003300330033003300000033000000000000000000000000000000000000ffffffffffffffffeeeeeeeeeeeeeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffffffffffffffffccffccffccffccffffffffffffffffffccffccffccffcc0000ffff0000ffff0000ffcc0000ffcc0000ffff0000ffff0000ffcc0000ffcc0000000000000000ffffff00ffffff000000000000000000ffffff00ffffff00aaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa0000000000000000ffffffffffffffff0000000000000000ffffffff00000000fffffff0fffffff0fffffff0fffffff0fffffff0fffffff0f0f0f0f0f0f0f0f000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000000000003333003333330033333300333333003333330033333300333333000033330000ffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeee0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f000000000000000000000000ffffffffffffffff0000000000000000ffff0000ffff0000ff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffff00ffffff00
|0,6=>0xffffffffffffffffffccffccffccffccff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff00ff00ff00ff0000000000000000000000000000000000ffffffffffffffffffff0000ffff000000000000000000000000000000000000ffffffffffffffffffffffff000000000033003300330033003300330033003300330033003300330000000000000000ffffffff00330033ffffffff00330033ffffffff00330033ffffffff000000000000000000000000ffffaaaaffffaaaa0000000000000000ffffaaaaffffaaaaffffffffffffffffffffffffffffffff0000000000000000ffffaaaaffffaaaaffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000005555555555555555555555555555555555555555555555555555000055550000111111111111111111111111111111111111111111111111111100001111000000000000000000000000000000000000ffffeeeeffffeeeeffffeeeeffffeeeeffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffff00000000ffffffccffffffccffffffccffffffccffffffccffffffccffffffccffffffccffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000
|0,7=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000ffffffffffffffffffffffffffffffff5555555555555555555500005555000000000000000000000000000000000000555555555555555555550000555500001111111111111111111111111111111111111111111111110000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffccffccffccffccffffffffffffffff0000000000000000ffffffffffffffffffffff00ffffff005555555555555555555555555555555555550000555500005555000055550000ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffff00ffffff0055555555555555555555000055550000555555555555555555550000555500000033003300330033003300330033003300330000003300000033000000330000ffffffff55555555ffffffff55555555ffffffff55555555ffffffff00000000ffffffffffffffffffffeeeeffffeeeeffffffffffffffffffffeeeeffffeeee0000ffff0000ffff0000ffff0000ffff0000eeee0000eeee0000eeee0000eeee0000000000000000ffffeeeeffffeeee0000000000000000ffffeeeeffffeeeeffffffffffffffffffffffffffffffffffccffccffccffccffccffccffccffcc
|_,_=>0
def sP:Nat→Nat
|0=>0x458e06461420b0608086322c62b3aa8706326058c0458e9a3c6058c04583863030101406c386326058c045830f4e301014c3831018092814838305440c1010038d0b42200a00e1828416301014018f8904383863030116361cd19302c6022c18a13243838616284880e182840608080
|1=>0x1a04d29283c6021a74319303010d026cd0b18aceaa1c1cd151e301163a18aac0435886202c6024ac009a082c1af040439a16216020280319302c60202a8d22082c18202703182a30116361c319302c6022c7030508405830404d2d2a30116381858958087063030101546c39a525078c
|2=>0x2c1c319283c6022c38305082d78c043409a5a6058c043409c348c5a15e3408e0e1859204047070c2c992023839a2a3d0af1a04d35442d7821a04d295a2c6022c70d05082c6021a04304200c101001c30b18092b00270d04168578d021c31e32301163638d1f1620101661c305082d0af
|3=>0x18080aa381c314203012e4038305202c60202cc71a202c6022ce83863e2c40202cce070c5540c040530e0e18c101808681361c31e16301161c1c32d30546022c1c3230a3c58304047062adc10d021cd1f202010d021cd1f2abc10d021c30f06bc1010038d36160c1011c1c3182a2c602
|4=>0x180503d1c1cd0f163158d3a3830516bc60202cc7066a10a8b060808734105af18086810e1828b060809c1c19185442c18202383291808b1b1c1c335082c60202cc386082d0af1a04e07762c6022ce83861685781663839a462c60202cc7070c4058c04d12811c6968b18086ba3818c0b
|5=>0x6b01013818591580808e0cd47830404e1a163012e02807060a2d0af1a0471a282c60202a87070cd4f8f060809c0c64c10163010d0269185163010d023830f168560140383151e0d7820218f101808b1b1c1cd291630116381cd0b18ac0a01c1c3295a2c6022c70305082c6021a04d0b
|6=>0x6a7c5ac043409c0c1420b18086813818f19202c6022c3831e5a30116363839a16bc60202cc707344058858086810c4058c04e97200c7858c040550e0e18f8f58080a01c18c0c043409b0e185a15e0599c1c1c3182a2c60202a83861e3013e023830b10086b10e1880b18add200e68a8b
|7=>0x1c1c31e302c62b1a743867e2c182027071a163010166383866a885af043409c0cd4f8f5e0868138187a15e340801c1858c56b901c1c18f0c0458d8e0e1880c04d00a41c1c3233e0c10100383865230101546c707345478c045809c0c3c1820200e0e0c547835e0809c762c42c043409a
|8=>0x546c70734545a1583409c0cd4a8f060809c0c8c20c04340800e18c151e301160e18a8f42bc68134b4a8c043409c0c78c8b1808b1d1c18f0c040501b1c1c31e322c6022c3831006080801c1c305442c1820238d29283c6021a04e1a467c5ac043408e0c2c602689409c1c194951808b1b
|9=>0x1ebc6021a0431e2a3011636383861e2c602689408e0c7c18202007070c546021ab9c062a3d0af1a04e1a3e556021a04e063c6458c0458e0e0c78c8b18080a01c1858c04e972038694941630116381dd8b42b06811c194941808b1b1c1c3182a3010d026c39a202d0ac1a047063c30101
|10=>0x3818f8c04059801c1cd1e16301163a3838628301171c1c31916301163a38d1e16301161c1c335083010d020039a1e2c6022c7471a16a06020238386203010166007070cb4c0b1808b1c0c6480b1808b0e34d510b18086813818f191630101543830b18080aa1c1c3192a2c6022c70d15
|11=>0x1a0471a28406022c38386461420b18086810c7e1030404707345078c0458e0e345478c1a05e9c342c18202007073478a0b1808b0e0e18a8c04059801c1c30b42bc0a01c1c31e163159d543839a525058c0434e870c6458c0458e9c1c18a83040400e0f00a0b1808b0e0e68a8f4230681
|12=>0x202c62b1a04707344058c1a05e8e0e1968f1630116383a335160c1011c1c329163010154383862a3010d0320e1a2a2c62b1a04e070c5478c04340c7345458c1a05e9c0f19a9f160c1011c1e245162010d021c3102a2d0ac1a047445a3c58c04587070c78a0b18086ae38383051e2c602
|13=>0x163011696383862a3d08c1a04e062a2c62b1ab8e1a2a2c6021ab809c0c2c18203247070c8da8c04340801c1dd8b18ac6811c1c3101e2d0ac1a047062a3d0881a043863c2c6022c74707342c6022cb87063c4058c040550e0e18f0b1808b0e0e18a0c0434e9b1c1c33f163010d027071a
|14=>0x5c383352a3c182023838629346021a047070c88f95060808e0e18a8f180869d0270d10163010d5c0471a28546021a04e070c7c81558086811c68f8b060808e0e194941e3010d5c3830b503010138383862a3010d0200e070c1510b18086811c196942a3010d02703053e3c6021a04706
|15=>0x883c58c5635d070d38a8c04587070c3c58c0458e9c1c68a0b1808b1c1c1dd8b18086ae023832d282c6022c707064454182023839a28406021a047070c6058c0434e81381c31516301163a1c31018086810038386325478c043408e0c4058818080a00e18c0b1808681381c310163158d
|16=>0x1c1e20f163010d74ba3292a2c6021ab870628406021ab87066a1478c043408e0c7968b18080aa1c1c3222a3010d0270350160c1011c1c31f203d6021a047066a5478c043409c0c50a8c043571c0c88a8804340870c2d0cf1a04707342d0881a043863e2e7821a04707347c5880434087
|17=>0x4587070c2c6571a047078c50a8c04587070c2c60203547070c2c602a75009c8c5458c045970e0c7858c0458e9c1c1cd0b1808b2e383830b180a9965c722141e3010d741c310163013402383863c2c6022c70707762c60d03487070c5478c0459d070cb480b1808b0e0e18f0b18080a0
|18=>0x23831f06080db1c1c31f1808681003839a168440d02703863c2c6021a047070c4058c0458e8e0e68f8b1008681381c35a1eb010d023831e163011d02a87070c64a8b1808b0e0e1858c045ac8e0e185a1583408e7818f0b18080aa1c1c31516a06020238386202c62b1ab8e0eb05058c
|19=>0xce458c04587070c7968f16301161c1c3292a2c60202a87078ca4a0b18086ae1c185a818080a01c1e20b180aa16741c314203010d5c7075816301165c38d0b42bc6811c1c32d302c6022c3838646546021a0400e0e185b7043408e0f18a8b42206810e68f8b5e086811c1c30ba28560d
|20=>0x2a2010d021c35d2a30153021c31fa2b010d023831e203010d026c70734a458c043409c0e18a15180a9960e1858c0578b2e1c18a8f10b010d02194ad163010d0270329282c6021a74e070d7478c045970e0cd4f8c04340801c1c310163010d74b831e2a2c6022c38386523010d026c707
|21=>0x18080a0381e262160c402021c329163010d5c7030b06bc10100383861630101be383c62a2c6022ce83863cb4a0b1808b0e0e18f84160c1011c1c314302c6021ae83863c2c60202a8e0e0e1878b0620101381880b42300a01c1c30b1809a011c1c30f18086811cc831816301161c1e31f
|22=>0xc3c6021a7409b1c18f19202c6021a04706202c6021ae971c0c78a0b1808b0e0e1b20b1808b2e1c19c8b1808b1c1c1f18b18086811c1c31f20301014038386525058c040550e0e1880b18080aa1c1c30b5e301014038386526458c043570e342c42c04340860a8878b18086811c18588
|23=>0x4f808e0e18f195a2c6021a047062a3010d02007070c5458818080a00e68588580868138185a1180500e0e19a8b060809c0e6878b1808b01383831e180868136383863c5458c040550e0e18583040400e0e1880b06201010e19190160c1011c1c3222a3c4021a043865a2c6020280707
|24=>0x23831e282c60202a87070c2c1820200e0e0e1880b0620101381c36816301161c1c30b1808e8154383e7163010d02383c66a2d6021a0470616301015438386283c6022c70706205458c0435d2ece7c58c043408e0e19495180868136383863c5058c0458e0e0e1858c040728e0e1858c
|25=>0x4740aa3838386163010154707070c5080c04587070c8da8b060808e0e1911f162010d027224e16301161c1c329202c6021ab873b16301160238386168578d02007070c3c5a15e3408e0ca4a8b18086ae38185a1180501c1c1cd10163011602383863c6458c0434e811c18f19163010d
|26=>0x43408e343c5af18086811c1880f160c402021c30b18086ba5cf360b18ac6ba0e18a8b42300a01c1c30b18086ae1ce030f168578d027076c282c6021ae8386205458310080870c78c8b1808681383b50b06301011c1c3041e2c6021a04e063e3d7821a0471a525058c043409c0e1858c
|27=>0x82d78c04340870db45831008087342c6021a0400e0e1880b42bc6811c1c31e283010d026c7070c2c88c04047070c7ca8c040500e0e18f8f5e0868138383151630101543838628406022c707070c8c5a15e3408e0e19104163010d0270d151e3010d027031f160c1011d0c386324058c
|28=>0xe6858c0458e8e0e18a6d1808b0e0e18a0b18080aa38383862a3c6022c04e1a467c58c043408e0e18583dc0808e0e18f905e086811c1cd1e163010d0238386282c60202a87070c508151808b0e0e6918b5e3010d0238386160c40202f0386462d0af1a04e0e0e18f191e2c6021a04706
|29=>0x202c6022c04e0e0e18f8b5808681383a20f16206021a043d8168460d02383c4168560d02383861e2c18c0404e0e0c2c6021ae80bc0f60f8b18086811c1e20b06201010f10f8b58086811c1e31f2a3010d02383862a3d78c043408652b458c0458707342c602028070734e458c043408e
|30=>0x1c1c30b5e3010d0200707882f803180808e0e1910f160c1011c1c30f16bc6021a0471a16b06021a04706c42c18804047070c2f783180808e0f1858c04340e01c1c31f082c6021a04707d82c6021ae80870c3c588180868138185a1583409c1d12e8b1808b011c1c329163010d5c38386
|31=>0x238386e62c6022c04707885058c04587070c40583180808e0e18a8f18ac6811c1c30b1808b01e4383c6163010d74b8706e22c6022c047070c88a8f18086811c1c30be00c60202707063ca4a0b18086811c1c30be00c40202383863c4058c043408e0e18a8f1808681381820b1808681
|32=>0x1c1c335163010d027039a163158d02383c45a3c58c043408e0e19a9f163010d02703861e2d78c043409c1c685ac180868138383151e3010d5c0471a282c6021a047070c2c6021a0400e0e1880b103010d021c30b0630101ea383863cb458c043408e0e18815163011602383f4163010d
|33=>0x10340878c2c18804047070ddc58c043408e0e1878b42206811c1e21f162010d021e22d282c6021a047070c3c5f006301011d1078b42306811c1c30b1808681ec703863c2c6021a047070c3c58c043408e8e1949416301161c1c32d1e2c6021a04e0e0c3c5a1583408e0c8c5af1808681
|34=>0x2c04707342c62b1a04e0e0e6858c1a05e9c1c1c32d16301161c1c3233e2c6021a047070c5458c045970e0e1880b5e3010d02383869c546021a04707345058c043409c1c1c30b180868100707070c7c7ac043408e0c405881808681381c30f168460d0270706525458c043570e0f105a1
|35=>0x1c1f60b1808b011c1c30b1808b1d1c1c3041e2c6021a047070c2c6022c0473c0e18a8c04340f81c1c31f1e3010d02707063c2c6021a04e0e0e19690163010d02383863e3c4021a047070c8c5af180868138383c4442c6021a047070c88f8b10086811c1c31016301014038386da2c602
|36=>0x18086811c1c31f203010d02383863e2c6021a047430e1bc8b18086811c1c339163010d0238386203c58818086810e18f2d1e2c6021a047070c8820b18086811c1c3233e2c6021a04e0e0e1948f18086811c1c3102a2c40c04340870da458c04587070c2c6021b6408e0e1880b4230681
|37=>0x163010d02707070c2c6022c0477b0e1b68b103010d021c30b18086ba5c7035a16b010d0238386ba2c602a6047070c5058c054cb0e0e1880b423068138383861e2c42c043408e0c2fd03180808e0f1078b583010d023830b1808b1d3838386163010d023a1870c2c60202807070c78a8b
|38=>0x2a2c1880404386da2d08c1a04707893858c043408e0e194941e3010d023839a163011602383862a2c60202807070c2c1880404e070c7c81518086811c1c3151e30116023838620545a1183408e0e1858c043408e641c30b1808681f838386163010140707070c7c80c043409c1c1c339
|39=>0xe185a15e3408e0e18f8b5e086811c1c335442c6021a04707343c58c043409c1c1858c04340fe1c1c30b1808681fa38386ba546022c047070d0858c043408e0e185dce0301011c1c31fda3010d02383c62a2c6022c04707342c6022c04e0e0e18a0b1808b1c1c1c30b42306811cf0386
|40=>0x163010d74b87070c2c6022c04e0e0f1858c04357011d1858c563408e0e1858c045970e0f18a0b18086811c1c329163010d0238386163010d03e0707b02c6021a04707342d78c043408e0e185a15e3409c1c1c31f16bc10d0270707762c6021a04707344058c043408e0e18a151808b0e
|41=>0x43408e0e185af180868138383862a2c40c04340870c4058c043409c1c1c30b5e3010d023838616206021a04e070ca4a0b18086811c1c310163010d02383862a2c6022c047070c545ac18086811c1c345163010d0238386525458c043408e0e1878b1808681383a20f163010d0238386
|42=>0x3e546021a047070c2c6021a0473c0f1858c0435d011c1c36d163010d02383862a2d08c1a047070c5058c04587070c2d08c1a04e0e0e18f8b18086813838386205458c043408e0e185dc06301011c1e30b1808b011c1c35d16301160238386163010d023a3870c2d0ac1a047070c7c5ac
|43=>0x1858c043408e0f1858c043408e0e18a8b18086811c1c30b18086813838386168460d02383863e2c6021a047070c2c6022c047070c2d60c043408e0e6858c043409c1c1cd0b18086811c1c3151e3010d0238386
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0x9b8035800ec0007
|7,0=>0x14d70a3384fa026d012e80934047a022d010e8083403fa01ed00ee80734037dc1b2c0d18064c0309c17500b280554028a013500937046b021600fb00758036c019600bb005580273811a007d00368017b809e0042c01a7
|8,0=>0x1aec8d5246990344819dc8cce06570322918cc8c49c616e303817dc0bd1c5dae2e5816ec0b52459902c3915d48aca0556e2a2914d40a4a05150282813d409ca04d32260912bc893e048d223e811ac88b2444ae21d810a4882e440701fa90f9407a643c301d890e7c871a437d01b680d6c8699c33d019680c74061a02fd017680b6c859242b721547
|8,1=>0x2bb495b64acce55e82ab415364a8b053d829a494b20a49051b92894942a0a0504fa8278c93a249c104d97268c1326098124b79257c129a493ee4969246c921608f9247482364118e48b7045472264110e4875243282154108a083324109203c8ffa47eb23ed81f2c0f7247a723cb81e1c0eee076523a991d048e620721038881c0b8de246df23669
|8,2=>0x17d60bd925e482ee417520b9905c392dd496ca0b5325a092cbc963e0b0f057f8
|9,0=>0x410420621022e808940041fe20fe107e793ef49f5a0f9b27c583de49eca8f5507a193cc49e3e4f0d277e83bac9db24ec7275a93a8c9d224e7f2737839749c964e392713938549c064df306f18374c1b824db106cea36341af64d6b06ac9352b9a6e8d27068a9340c99e24cdf2666932f419564c9b0644931e418ce4c552622830cc98424c0d45fd9
|9,1=>0x523c28fe146d2a2ca5124286a94250a0995004a7e213dd49e4a4edca74a539509c194dd3a6ca1353299fa4cbc263e130d297e84bb425b652cb095c94a9ca52a52850938a497ca49e123f09169486ca41251f908f484764239211b908d484655230a117508b28454ca282513108908443ca1fa50ed086d9432c217250a5484a8421420e6506128288
|9,2=>0x63a531ae58c52c5a8628cb12618830c398618c30a2583f2c15a605d300e17f70bf1a5f44af7e57af0bcf85e3c2efa576b2baba5d1c2e6e17252b8995c04adde56db4b6495adcad4e16952b42859ccacbe964d2b1d958a4ac35d6074afa957942baa15c32ad98568c2b1e957d2ab59555d2a8e15352a92854542a0a14f50a7285354298294af2a4f8
|9,3=>0x1d330e909744439fe5cef0e6f8732d39761ca74e4b87214b8e65c612e27970ed38561c174e01a6fc4b7c21bcf2dde96ea537321b872dba96d8cb6a25b3f2d9696c7436165af92d7396b54b58a1ab6ed5296a5435065a730d3096935347a1a2b2d0d8681d33e699e12ce8866fcb35a599d0cc5965ec32d259590ca3964d4b246590f4c7e9
|10,0=>0x86d44342a18f30be985acc2b26147309a98485422220fd50759836c418ea0b3504fa8234c0f66069302b98114c066601f5005a7fec3fd25fd90fe397ed4bf465f930fc097db53eb65f456f9997c7d3e1e1efd2f74a7b5cbd8a5eb32f5187a44bcfe5e6d2f2ca79243c6e5e270f0a9780cbbde9ddd2ee5976ec3b561d992ec3975d4bacddd552ea19
|10,1=>0x993d4c7a662b330c998154be2a5df32e6996f44b56659932c3995cd4ac2654f329e994acca326509127aa938cc99ea4bd32559925d4902e46d522bb9114c862a421120798ff4c7da23dd11e4a8edcc74a639331bfa8dad46b26343719898c75461662f9317398b54c58a22b1514f98a2d44f262655128a8904445aa21b3103a87e3c3d221d730e29
|10,2=>0x142b9a114d062a821140799ffc4fde27dd33e4a9edccf4a679333c099dbcceba674b339c99c9cce2a6703337989b84cd9e66bb535589a64cd12267553319
|11,0=>0xac94d62a2b0335789ab7cd59a6abb35549aa64550e6a73552faa934d47a2a2b350c9a82453ee69e354e89a6f55356699934c2aa5ccd2c2694d549d9a49d522a690334789a37cd19e28bf14578a274d116687934348
|12,0=>0x573e2b8d35bd9adac56b26b49159b9
|13,0=>0x15d78
|_,_=>0
def wAt:=mkWire dB 127 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xe391a05443b461f44393e1d163102353c3b3c1f02711c1d3c3b16750c7102710e3902353c3b321d521f28391605501f188120371e39462f1a31461f3e1d163118390c710431203716710e3916312205200c2a1d16391a313c3b16760235167502710e39240916052e3120582a1d16391a05120922051839200c1e39161d1a31
|1=>0x1809463b461f18711c1d02710c7128390e3916050c713c371675020902710c711a051639161d02711c1d181d163902c93e700e391631183516bd0c711871203718391671181d0c711c1d443b0c711a053c3b2ab9021d02353c3b3c1f200516711c1d1a0516391e050c710e39161d2205181d200c2a1d16391a3128390c711605
|2=>0x20052a1d16391a050235521f2839161d1605463b461f18711c1d5a3b1e050c71161d180916bd0c7118711c1d2e3120582a1d16391a0524092e3120582a1d16391a050c7104311639161d18711c1d3e1d18710c713e390e3916310c7128390235281d1c1d1605681f0281203716710c7116bd180918713c1f1676167502711c1d
|3=>0x461f20312a1d163902390c711a0516710e3946373e710e39163116a2188120372a1d16393c2f3c3b20051e39161d1a05727128731c1d1605163902355a3b281d16051a31461f1e211839161d163918e128700e3916051631167118390c710e390c711631163918710e3916be18710e39161d1a310c711a313e731c1d16313c3b
|4=>0x2a311639463b16bd0c7118710e391a31461f203116711c1d1a31461f44393e1d16313c2f1a05521d28391605463b6a1d3e391631463b16bd180918710e3902390cf11a0516720e390431463716bd18711c1d16bd0c7118711c1d681f02812a1d16390c7116b91c1d0239021d3c373c3b200516710e39021d160520372a1d1639
|5=>0xe39161d1a313c3b3c1f20052a1d1639461f16bd0c7118711c1d1809181d20371e39161d101d1a31161d183916393c2f20052a1d16391a052a050c711c1d16390c710405203716711c1d28390235281d1c1d1605463b0a1d6a1f3e39163120371671340b0c711c1d02090c71161d02711c1d461f16bd18711c1d1835463b6a1d
|6=>0x1e39161d3c2f30395a3b281d1605463716bd180918711c1d3c373c3b2ab9021d1639161d1ae128701c1d1605183902c93e700e3916310239040520371e39161d16390c71181d1c1d1a31181d200c2a1d16391a313e3916310e39161d1a3120371671021d0c711c1d461f16bd5839181d04313c370c7128711c1d16053e391631
|7=>0x3c2f521d283916051a050c7116390e39161d16be18710e39161d1a311a311639161d18711c1d18390cf1181d16721c1d0c71181d3e390e391631463b461f203116711c1d3c1f20052a1d163902353c2f5a39281d1605463716bd0c71187118391671181d0c711c1d203716711c1d0239021d727128731c1d16051631181d2037
|8=>0xe3916050c713e711c1d181d1631681f0281203716711c1d1a053c2f521d2a05163904053c3b167502710e3918356c1d3e731c1d1631463716bd0c7118711c1d18713e1d3e390e3916313e39163118711c1d16be58391809181d161d021d0405203716711c1d16760235167502711c1d16d202812a1d1639462f3e711c1d1631
|9=>0x1671181d0c711c1d1676167502711c1d0c7118091c1d181d1639161d2a311c1d16391a3116be463b16bd18710e39163902355a3b1e05161d163958391809181d161d16391e050c710e39161d3c1f0235167502711c1d3c2f20052a1d1639521d0235521f28391605462f1a3120312a1d16393e1d18356a1f3e39163128390c71
|10=>0x1c1d02353c2f2ab9021d1639681f028120371e39161d462f3e7118351c1d16312870021d1c1d1639160504311639161d18711c1d16310c711c1d181d16391a053c1f200516711c1d3c1f20052a1d1639203716711c1d0239021d0c71023528390e391605181d04310cf116721c1d02353c2f521d283916053c3b2ab9021d0431
|11=>0x2a1d16391a053c1f0235167502711c1d1a0516750c7102711c1d462f463b3e3916310c7102710e39161d1a050c711881203716711c1d462f20312a1d16391c1d02355a3b281d1605521f2a052a1d16391a053e1d0c713e390e391631321d521f283916053c37727128731c1d1605521f2a051c1d16391a050c711639161d1871
|12=>0x16390e39161d16be18350c7118711c1d0c7128711c1d16054637462f2ab1181d163918091871203716711c1d04053c37167502711c1d02710c7128390e3916051a053c1f167502711c1d462f20312a1d16391a3102350d0528721c1d160504310c7116390e39161d4637462f3e711c1d1631023516750c7102711c1d16052058
|13=>0x283916051c1d16391e33161d163904050c710e39027216390e39161d1639340b0c710e393e390c1d1835163118390c393e1f1631181d2a1d043116391e050c39161d1a0528711c1d021d1605461f1e211839161d16050c711a0516711c1d443b461f44393e1d16311a31170d3e721c1d16310c7116050e39161d1a05340b0c71
|14=>0x21d163994331e0d161d1a31462f6a1d3e39163104050cf116721c1d1e391809181d161d0431161d183916390235167502711c1d0c71021d1c1d1a053c3720052a1d1639287102351c1d160516765c39021d16056c1d3e731c1d16310c71040516711c1d1671340b0c711c1d1e050e39161d1a0518350c1d3e3916313c37521d
|15=>0x1c1d16053e1d1835163916311639161d02711c1d1671021d0c711c1d0c711c1d163916052a1d181d163916311a310c711c1d16312839021d161d16051881203716711c1d16be163918710e393e1d6a1f3e391631281d1c1d163916056a1f3e39161d163103311e5b161d1a05043116390e39161d02091c1d021d16390c711c1d
|16=>0x2390405281f02351639160502710e39161d1a050c7102351c1d16050cf1021d16721c1d0235281d1c1d16051e31161d16391a310c71160516711c1d3c3b167502710e3902711c1d16391a05462f20312a1d1639521f2a051639161d20372a1d183916393c3b200516710e391e390209021d161d2a311639161d1a3117052872
|17=>0x2a1d16390c390239021d161d021d0c1d2a0516391e39021d161d1605161d6a1f3e3916313c375a39281d16053e1d1c1d163916311835a2311e3b161d1e39181d161d16310e392a311639161d021d1c1d163916053e1d183916391631043118f116721c1d18390c710e390431190d3e721c1d163118390c710e391631161d0c39
|18=>0x16711c1d02358c3b16050c1d04c93e701c1d16310c1d0235163916058437175918721c1d2c392c1d1c1d1a0516391a05021d0c1d0235167502711c1d0c71021d1c1d1a05021d2c390e391a050c390239161d1605028120372a1d163920051a0516711c1d760b0cf116721c1d1a05161d023916391e051e39161d1a0520372005
|19=>0x1839163916310c7118711c1d1e3b1809181d161d1631177206391a31462f3e711c1d1631183904310c710e39727128731c1d160502711a0516711c1d163118390c710e393e3b181d161d16313c37167502711c1d0235521f2a05163902f11a0516721c1d0431181d16721c1d3c37521d28391605188120372a1d1639021d0405
|20=>0x3e39163116711c1d0239021d20052a1d16391a053c2f521d28391605287302351c1d16051a055a391e05161d3c37521d2a0516390c1d2839021d1605188120372a1d16390c392c1d02391a0516711c1d021d16051a058c3b021d0c1d0c71180918711c1d02355a3b281d1605462f2ab1181d163918e128701c1d16050c1d1809
|21=>0x161d1a31043120372a1d1639028120372a1d1639161d3e701c1d163102355a3b281d16050c1d18391639163116592c3916391a05181d1e3b161d16313c2f20052a1d16392a050c711c1d163916052c3916391a05a61f2c39021d1a0518391639181d161d281d28390e391605027128390e39160516590235021d161d462f6a1d
|22=>0x283916053c3720052a1d16391871203716711c1d521f2839021d16050c711c1d1839181d461f44391e31161d1839203716710e390c391839160d1a3116e90e39021d0239183516be18711c1d1b86c01d2a3316390c1d0235023916391a055a39281d16051835443b3e1d16315a3b281d023916053c37200516711c1d18390e39
|23=>0x161d1a05166d167602711c1d3c372ab9021d1639183516be18711c1d2a1d1835183916391a3120312a1d16391e31161d183916391e0520371e39161d161d167602711c1d3c1f20052a1d163916711c1d0239021d287102351c1d1605ba1f021d16591a051a0528731c1d16050cc93e701c1d1631163120372a1d16393c37521d
|24=>0x1c1d16310c1d3e39181d16313c37521d2839160516050e39161d1a052a1d021d023916390d0d3e721c1d16313c2f521d2a051639287102351c1d16051b9a20072a1d16391ae128701c1d16053c1f5a39281d1605462f2ab1181d1639183920372a1d16390c711c1d1839181d20372a1d043116392a311c1d16391a310c710e39
|25=>0x1c1d16310c390235281f16052a052a1d021d16390cf11a0516721c1d16be5839181d043158391809181d161d2a051c1d021d16390431203716711c1d0c711a0516711c1d3c1f167502711c1d321d521f283916053c3728711c1d160516be183518711c1d18391a3116710e390235d21d283b16053c37167502711c1d0d0d3e72
|26=>0x239021d0405881f02390c39043120372a1d1639021d28701c1d1605161d180918711c1d0239881f16050c392a1d1835183916393c1f200516711c1d0dad06721c1d1a31443b1e310e39161d5839181d161d16310c7128390e3916053c37167502711c1d3c37200516711c1d2a1d0235163916051a316a1d3e39163118393e1d
|27=>0x1839163916be0c7118711c1d1671180918711c1d3c2f28711c1d1605200c2a1d16391a31163120372a1d16391631161d18711c1d3c372ab9021d163916051a0516711c1d16bd5839181d04311c1d443b3e1d16310c7116390e39161d3e7218351c1d16313c1f20052a1d16390c71161d18711c1d18391e39161d1a3116721c1d
|28=>0x1c1d160502350c7102711c1d02352a1f163916053c3728711c1d160516390e39161d1a050c713e711c1d163119ad06721c1d1a311671163118711c1d16750c7102711c1d3c3728711c1d160516052a1d16391a0516bd0c7118711c1d1a31183916720e3916bd180918711c1d3c1f1ee90239161d463b16bd18710e392a1f1835
|29=>0x3e1d1631881f02390c390e391839161d1c1d181d04310c3916591a052839021d16051a0516711c1d1c1d181d1631161d18390c398c3b04310c1d0c39181d04310e39161d1a31023916720e398c3b16310c1d1a3118390c390c39181d16310c1d1639163158391639181d161d281d1a05283916050c71203716711c1d0c712873
|30=>0xc39023516052a1d16391a310405161d163917522c1d1a050c1d0239021dba3b16591a051e31161d1639061d1c1d1a31521d28391605061d18391a3120052a1d163916390e39161d443b3e1d163116be18711c1d061d1a310c391e31161d1a315839181d161d0c71181d1c1d1839160d1a31b81f06391a310c1d2a331639443b
|31=>0x1639521d28391605161d02721c1d1a05283916051e050e39161d1809181d161d16bd18711c1d1c1d3e3916310c711c1d04050c391e05161d3e390e391631161d18711c1d181d0c711c1d1639021d161d0c711c1d160516be18711c1d2a1d183916391e0f161d1a315a39281d16052a1d16391a050d1d02721c1d2a5916391a05
|32=>0xc711c1d340b0c711c1d1a05281d16053e711c1d1631021d16391a05187116711c1d281f163916050c711c1d160516be18711c1d181d161d1631183916710e3904310e39161d2a05021d16390c39183904311a3118390c1dda312a1f1639161d183904310c39183916310c39281d1605061d161d1a310c390431161d0e392a07
|33=>0x443b3e1d16313e711c1d16312839161d16052a1d183916390235283b160502f116721c1d2a1d043116391a05881f0c39023502711c1d443b1e31161d1a0516721c1d16391e07161d0e39161d1631200516711c1d1e051e39161d1839161d163116bd18711c1d0c393e1d16313e1d1839163120372a1d16391a052a1f16390405
|34=>0x1c1d28731c1d16052c721c1d1a052a1f183916391c1d0239021d3e3b181d16312c3916591a052c3902351605043116711c1d1839181d161d06711c1d1a310c39181d161d023502711c1d3e721c1d163120372a1d16392ab9021d16392a1d163916313e721c1d16318a393e1f163128731c1d16051e391839161d5a391e05161d
|35=>0x16391a05175918721c1d061d06391a312a1f163916310c1d16391a051a050c711c1d02351c1d1605043116721c1d18351839163904312a1f16390c39281f16052839161d16050c711c1d1a0520372a1d163918390e391a312a1d16391631161d16391a052a1d043116393e701c1d16312abb021d1639203716711c1d16311671
|36=>0x16393e1f16312a0516390e39161d161d0c390239021d1c1d1a05021d0c1d04050c1d021d1a0516050c1d283916051e07161d8c3b0c1d0c7118711c1d180918711c1d163118711c1d0cf116721c1d0c7116711c1d0235163916055839181d04315839181d16313e1d3e3916310c710e39161d20332a1d1639ec1d2a0716391659
|37=>0xc1d16391c1d043116311a05181d0c711c1d8c390c1d161d16391639163116721c1d02390c1d2a1f163904311639023516051c1d04311c1d16312a1d163906391a311a050c1d16591a0502721c1d181d0431181d163118711c1d1839163916711c1d18711c1d18390e39283916052a1d163916391a05181d
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x7700070000
|7,0=>0x9f60996093608d600000000089408540805000007b507650000071506b606560000061405b600000592055404f6000004960436000003e503950000034502f50000029602540000020501a60000014600e6
|8,0=>0x1d551d141cc51c751c341be51b951b451af51aa51a551a0519b51965191518c51875182517d51785173516e516951654160515b51565151514c51475143413e51395134512f512a51264121511c51175113410f410a5105510050fc40f750f340ee50e950e450df50da50d550d050cb50c650c150bc50b750b340af40aa50a55
|8,1=>0x307530252fd52f852f352ef42ea52e552e142dc52d752d252ce42c952c452bf52ba52b552b052ab52a652a1529c52984293528e528952845281327c52784273526e52695264525f525a52555251424c52475242523e42395234522f522a52255220521b52174212520d52085204420041fc41f751f251ed51e851e351de51da4
|8,2=>0x351534c53475342533d53385334432f532a53255320531b53165311530c5
|9,0=>0x452444e444a44464442443e443a44364432442e442a44264422441e441a44164412440e440a4406440243fe43fa43f643f243ee43ea43e643e243de43da43d643d243ce43ca43c643c243be43ba43b643b243ae43aa43a643a2439e439a43964392438e438a43864382437e437a43764372436e436a43664362435e435a43564
|9,1=>0x552454e454a45464542453e453a45364532452e452a45264522451e451a45164512450e450a4506450244fe44fa44f644f244ee44ea44e644e244de44da44d644d244ce44ca44c644c244be44ba44b644b244ae44aa44a644a2449e449a44964492448e448a44864482447e447a44764472446e446a44664462445e445a44564
|9,2=>0x652464e464a46464642463e463a46364632462e462a46264622461e461a46164612460e460a4606460245fe45fa45f645f245ee45ea45e645e245de45da45d645d245ce45ca45c645c245be45ba45b645b245ae45aa45a645a2459e459a45964592458e458a45864582457e457a45764572456e456a45664562455e455a45564
|9,3=>0x74a47464742473e473a47364732472e472a47264722471e471a47164712470e470a4706470246fe46fa46f646f246ee46ea46e646e246de46da46d646d246ce46ca46c646c246be46ba46b646b246ae46aa46a646a2469e469a46964692468e468a46864682467e467a46764672466e466a46664662465e465a46564
|10,0=>0x80b38083805380237ff37fc37f937f637f337f037ed37ea37e737e437e137de37db37d837d537d237cf37cc37c937c637c337c037bd37ba37b737b437b137ae37ab37a837a537a2379f379c3799379637933790378d378a378737843781377e377b377837753772376f376c3769376637633760375d375a375737543751374e3
|10,1=>0x8cb38c838c538c238bf38bc38b938b638b338b038ad38aa38a738a438a1389e389b389838953892388f388c3889388638833880387d387a387738743871386e386b386838653862385f385c3859385638533850384d384a384738443841383e383b383838353832382f382c3829382638233820381d381a381738143811380e3
|10,2=>0x922391f391c3919391639133910390d390a39073904390138fe38fb38f838f538f238ef38ec38e938e638e338e038dd38da38d738d438d138ce3
|11,0=>0x9732971296f296d296b29692967296529632961295f295d295b29592957295529532951294f294d294b29492947294529432941293f293d293b29392937293529332931292f292d292b2929292729252
|12,0=>0x97b197a197919781977197619751
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 16
def pmP:Nat→Nat
|0=>0x4020200000000008017c000000000100048000000000200010000000000400000000000000461340000000000800480000000001000800000000001e23c00000000000c00800000000000c0e80000000000115f0000000000022a20000000000044280000000000082800000000000100a00000000000201200000000000402000000000000801000000000001001000000000002000000000000002000000000000003ed8000000000007d00000000000000ac0000000000000f80000000000001100000000000001600000000000001800000000000002000000000000001000000000000000
|1=>0x800201a000000010004028000000020004860000000020c195f0000000041073ba00000000800c57c000000010000110000000012010220000000023824fc00000000400488800000000800801000000000481dcf00000000090329e000000001006134000000002001610000000003c107c000000000482002000000000306174000000000580808000000000a195f00000000012000200000000020457c000000000308af8000000000600010000000000820be000000000104004000000000203ed0000000000400090000000000620120000000000c00040000000001082e800000000021001
|2=>0x400062be00000008000657c000000100008ef80000002000117f0000000400022be00000008000456c000000100008a780000002000101f00000004000203c00000008000017c0000001000002b80000001134165a0000000201020be000000024b8457c0000000410082e80000000820100d0000000100420020000000200800340000000400080080000000800000100000000f0010aa000000018206b4c000000030408af800000004801117000000008803d960000000102ce434000000020488ab800000004081fdf00000000800721a00000001000c0080000000200108400000000400185e
|3=>0x425022be0000000848045d4000000109008af80000002120105f0000000421022be0000000840041fc0000001040080f80000002048195f0000000409022be00000008100657c000000102008af80000002028105d0000000404822be0000000808045fc000000100708af8000000200c315f0000000401422be00000008028000400000010041caf80000002008315f0000000401022fe00000008020457c0000001004082f80000002006115f0000000400832be00000008010457c000000100108af80000002002105f0000000400420ba00000008008017c0000001001000080000002000395f
|4=>0x489032be00000009104617c00000012200caf80000002440185f0000000488022be0000000902c657c00000012049caf80000002409195f0000000481032be00000009020457c000000119508bf80000002320117f000000046202cfe00000008c38417c000000118308bf80000002304102000000004604005000000008c0048a8000000118008bf8000000228010570000000448022be000000088e8597c000000111408bf80000002222115f0000000443024fe00000008810417c000000110108af80000002200315f0000000440032be0000000880045fc000000110008af8000000212e115f
|5=>0xc00072be00000018000e574000000300018af80000006000115f0000000c00020fe00000014818017c000000280e0a3f00000005008195f00000008c1c22be00000011830457c00000023050caf800000044091fdf0000000841c22be00000010830c57c000000210509eb80000004202015f0000000840022be0000001009041740000002010000400000004004107f0000000800032ba0000000c078597c000000180608bf80000002908100d0000000501422fe0000000a008457c000000132008af80000002608315f00000004c0462be00000009800c57c000000130008af80000002449195f
|6=>0xc65022be00000018ca0417c0000003194082a80000006320115f0000000c64020fe00000018928457c000000312408af8000000623a175f0000000c45800ba000000188a845fc000000311408bf80000006228115f0000000c4342cbe00000018838457c000000310608af8000000620a395f0000000c41462be00000018828657c000000310508af80000006208115f0000000c40820fe00000018800457c000000308008af8000000604a1dcd0000000c094329e00000018120457c00000030200caf80000006030127f0000000c06024fa0000001803841740000003005082e80000006008115f
|7=>0x14c0822be00000029034617c000000520608af8000000a00c315f0000001401820be00000028010417c000000500008af8000000a000105d0000001200a2db400000020000df68000000400008af8000000664b195f0000000cc1632be00000019828e57c00000033050fea8000000660a115f0000000cc0072be00000019800657c00000032250ca780000006449195f0000000c88022be00000019024657c00000032041caf80000006408315f0000000c81022be00000019008455c00000032001caf80000006400315f0000000c80032be00000019000457c000000319508af8000000632a107f
|8=>0x3481832bc00000069020457c000000b90608af8000001701e165f0000002c41822be000000564d05968000000a30608af80000012920102d00000024250205e000000484a00030000000900a0b2d000000120000000000000230282cb60000004403077780000008400082f80000010800100900000021000001a000000420000004000000800000168000001000000090000002000000100000004000000040000007b0708af0000000f204385f0000001cc1860be00000039830617c000000700208af8000000b40d195f0000001681832be0000002983845780000005306182f8000000a606315f
|9=>0x8420026be000001081006f7c00000210200aaf80000042040135f000000840602abe000001080c04d7c000002100c0bbf80000042010177f000000840202eb60000010804055fc000002100808ef80000042010115f000000840103fbe00000108000ef7c00000210000fed80000042000155f0000008400026fe00000108000477c00000202048fed8000004004817df0000004c40022be000000980a8453c000001301408af80000026028104f000000492602c9600000088820411c000001101408af8000001f20e115f0000003e01822be00000079030457c000000d30708af8000001a60e115e
|10=>0xb48002bbe00000129800d57c000002520009ef8000004a00411df000000940002fb6000001188685f7c000002301009bf800000460003b5f0000008c00036be000001180004d7c00000214090baf8000004244813df000000848802abe000001091004f6c00000212048fef8000004240833df000000848103fbe00000109000f57c000002120019ef800000424003357000000848003fb6000001090006f7c00000212000aaf8000004240013db0000008480026be00000108800d57c00000211000aaf80000042130155f000000842402af6000001084804d7c00000210880aaf80000042100137f
|11=>0x90000400020000103c000e57c00002070021caf80000406400395f0000080c40072be00001018000e57c00002020000cae80000404000190900000802000200200001000008002400002000000cae8000034621a179f000006804302d3e00000d000405a7c00000a100c0bef8000014201011df000002800200d3400000239810c57c00000413041caf80000082606305f00000100800201600000200800c42c00000400010800800000800020003000000cc4342ebe00000188860597c000003100c0baf80000062010175b000000c40202abe00000188040457c0000031008032d00000060100135f
|12=>0x200c41c22fc00004018838457c000080300208bf80001006004115f0000200864020fe0000400c81045f8000080180608bf8000100300c117e0000200601822be00004008890457c000080110208bf80001002204115f0000200404022be00004008030457c000080100308af80001002004117f0000200400022fe00004008000457c000080000208af80000806300117f0000100464022fe00002008c0045fc0000401100083f8000080220010230000100404422be0000200001040040000400000083f80000800000102b00001000000204600001219800e57c000024100518af8000048040b390f
|13=>0x20a400026be00004140480557c000082381209bf80001043204157f000020860382efe00004108440457c000082100a09bf80001042010155f0000208402022be00004108040417c00008210000aaf80001042000137f0000202f65c22be0000405e4b0457c000080b99708bf0000101721e175f0000202e42c2cbc0000405c838457c000080991208af80001012928115f0000202463c26ac00004048020457c0000808c0608bf8000101032c115f0000202025022be0000401c838457c000080390608af80001007204115f0000200e21822fe0000401c09045f8000080381008bf80001006304115f
|14=>0x640b480027be000c8069000457c0004c0319008bf8000980200e117f0001200e45c22fe0002401c4a045fc000480381708bf80009004024117f00011025250205e00022008c2800ac000440100100008000880002a002b0001000c45422fe0002001848840a4000400301508bf80008006022117f0001000624020520002000a8a0008c000400000108008000800000200090000a00c00022b800008060000057c0000c0118208bf80001800224115f000020a64482abe0000414c810557c000082949c0baf80001052304155f000020a40702ebe000041480c05d6c000082900c0baf80001052010175b
|15=>0x401c200400822be40000028010457c400002900a0bef84000062100135f080000848823fbe100001091004f7c140080901008af82033012000115f0300200604022be0348002c000457c04b080981408af8096000b000115f0124600440822bc0248c008000457c041980b81008af80833012000115f0088001600062be008000080045f6c00f080900408af001e000a000115f002c200640822fe0058400c00045fc007802500209af800f001a00c115f001e001480822be0038003c010457c003a00500608af80071042104135f000c200640022be00100008010457c001982900809af80033012204115f
|16=>0x1000001188685f7e000002300d0befc000004201817df
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x601000
|7,0=>0x5711c0e0400006c020081c0000b034000085412c1b0600806c0a02c0306c300541b0141c0000b1301b0440b06c020c41b05c07
|8,0=>0x7d106385144c0146825070ae308120705624844618263d47e27c3b43c1c378364f98402cc8070344001c32c9c30c4f070212e9750e42b09183134530243e058324a01e0a17f070aa2e1035284200c1c7310b3c4dd4283c1543d099cb12126448f841d150691429061088334181c0dd6166c135bd270716b064535d9850703f6e840428283110c35c1c6ac4109061444ac5dc8c2c44a0b8f609c8602cad03c58
|8,1=>0x1af071ca2e5723dd0e0984003035140276d92c
|9,0=>0x7dcee36c387c56a37dc86258f73c9050de2790d66f9fb761691e5534b4eb7bc14550a66cd502f8207246a1e06819d2a6d4596f05b7b5c7461c37d540349a95c1a076d91509433503a074bf2f0ce28c893947554814521fc669b26ed3a7690834ca86a0b02ecb71a5295b8645f87f360873415b2507012579354af634754948a7f968588c729452708610a47c0a9675d1d957891399661ad735794c3b5bd73814
|9,1=>0x25ddd7f5387159645da50b4fa2d5551c59f08cfd10dcd114ff7b8f4754f92c8e91cdb1278ab568fc304b44247f580c61c8ec4fd021395c0b097239162a5a65b0e96d0e06dc9e27095365b013c631b9044819d2005d5385b68ce14b98875c6516dcc050b653c754051c1882f3ed21490ef68874184e1771f96605a2cc8f4751f1e94b5e11977c943f85b711d45f47c43522364662f59c525f33886124deb
|10,0=>0x3685f2051b3c86b648a11fc607c9ea368e3795576b06a199873346c17c5c3c1d25e980234f06406a365bf69d7a65cc93a0a774ce4119585f0d2651655c5a1605ad3cc824e4982fcf03198b7e95f2049b535597993c220651adc9744c5268a2591595b4ea4ccdc4dc5b3c1057419e4d1e36e5244adff511f85ede8759e7334cc16c987a57e25d31779f65157a4fce71e1e1251ae1b5474f53e48c7b4c15d4c946
|10,1=>0x151280994d6026549d25d8280465215e01bdec20dc6705991dcff22d2f631c03451e33da4
|11,0=>0x80135328841a9412048b63c771b0cd7d1b87c06a1d860260a1334972598a3359420c5f628c05587d6a93b58d934d88d2f130
|12,0=>0x1302046a1d45f6385e
|13,0=>0x5b
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 10 (j%128);fld (pmP (k/32)) 59 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_253 12 roots_253 ops++addP pm 1 dom_127 11 roots_127 ops++addP pm 2 dom_223 12 roots_223 ops++addP pm 3 dom_191 11 roots_191 ops++addP pm 4 dom_251 12 roots_251 ops++addP pm 5 dom_238 8 roots_238 ops++addP pm 6 dom_246 10 roots_246 ops++addP pm 7 dzo_215_32 9 roots_215 ops++addP pm 8 dom_247 11 roots_247 ops++addP pm 9 dom_159 9 roots_159 ops++addP pm 10 dom_95 9 roots_95 ops++addP pm 11 dom_119 9 roots_119 ops++addP pm 12 dom_239 11 roots_239 ops++addP pm 13 dom_231 8 roots_231 ops++addP pm 14 dom_228 5 roots_228 ops++addP pm 15 dom_244 7 roots_244 ops++addP pm 16 dom_55 5 roots_55 ops++addP pm 17 dom_45 5 roots_45 ops++addP pm 18 dzo_173_2 6 roots_173 ops++addP pm 19 dom_63 8 roots_63 ops++addP pm 20 dzo_222_32 9 roots_222 ops++addP pm 21 dom_126 9 roots_126 ops++addP pm 22 dom_243 10 roots_243 ops++addP pm 23 dom_230 7 roots_230 ops++addP pm 24 dom_190 9 roots_190 ops++addP pm 25 dom_175 8 roots_175 ops++addP pm 26 dom_183 9 roots_183 ops++addP pm 27 dom_62 5 roots_62 ops++addP pm 28 dzo_109_2 6 roots_109 ops++addP pm 29 dom_254 11 roots_254 ops++addP pm 30 dom_111 8 roots_111 ops++addP pm 31 dom_245 9 roots_245 ops++addP pm 32 dzo_61_2 6 roots_61 ops++addP pm 33 dom_250 10 roots_250 ops++addP pm 34 dzo_223_32 10 roots_223 ops++addP pm 35 dom_167 5 roots_167 ops++addP pm 36 dzo_219_32 9 roots_219 ops++addP pm 37 dom_235 10 roots_235 ops++addP pm 38 dom_103 5 roots_103 ops++addP pm 39 dom_174 5 roots_174 ops++addP pm 40 dom_252 9 roots_252 ops++addP pm 41 dom_237 9 roots_237 ops++addP pm 42 dom_61 7 roots_61 ops++addP pm 43 dom_110 5 roots_110 ops++addP pm 44 dzo_189_2 7 roots_189 ops++addP pm 45 dzo_253_2 8 roots_253 ops++addP pm 46 dzo_237_2 7 roots_237 ops++addP pm 47 dom_125 9 roots_125 ops++addP pm 48 dom_189 9 roots_189 ops++addP pm 49 dom_207 9 roots_207 ops++addP pm 50 dom_181 6 roots_181 ops++addP pm 51 dzo_125_2 7 roots_125 ops++addP pm 52 dom_188 6 roots_188 ops++addP pm 53 dom_236 6 roots_236 ops++addP pm 54 dom_219 11 roots_219 ops++addP pm 55 dom_221 10 roots_221 ops++addP pm 56 dom_109 6 roots_109 ops++addP pm 57 dom_124 6 roots_124 ops++addP pm 58 dom_27 5 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54|h55|h56|h57|h58
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_215_32_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_173_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_222_32_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_109_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_61_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_223_32_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_219_32_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_zo_189_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_zo_253_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_zo_237_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_zo_125_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h52;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h53;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h54;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h55;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h56;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h57;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h58;exact cpcs (by decide +kernel) lowS_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_253 12 s (0,roots_253.map (·&&&dom_253)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_253 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffffffffffff0000000000000000,64),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 41 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 41 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 143 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 15 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 143 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 254 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 126 128 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 254 → Z 9 i = true := (range_split z9_0 z9_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 157 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 29 128 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 157 → Z 10 i = true := (range_split z10_0 z10_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 40 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 40 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 3] }, { op := GateOp.or, inputs := [1, 8] }, { op := GateOp.or, inputs := [2, 4] }, { op := GateOp.or, inputs := [10, 9] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.and, inputs := [11, 12] }, { op := GateOp.or, inputs := [2, 8] }, { op := GateOp.and, inputs := [5, 14] }, { op := GateOp.and, inputs := [4, 9] }, { op := GateOp.and, inputs := [3, 0] }, { op := GateOp.and, inputs := [7, 6] }, { op := GateOp.or, inputs := [13, 15] }, { op := GateOp.or, inputs := [19, 16] }, { op := GateOp.or, inputs := [20, 17] }, { op := GateOp.or, inputs := [21, 18] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52654_aux

theorem PEqualNP.Outside.L_meta_52654 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52654_aux.main
