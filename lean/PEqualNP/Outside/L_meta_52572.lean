import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52572_aux
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

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfafafafafafafafaaa00aa00aa00aa00fafafafafafafafaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

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
def goal_89 : Nat := 0xffffaaaaffffaaaaaaaaaa00aaaaaa00ffffaaaaffffaaaaaaaaaa00aaaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffccccffffcccccc00cc00cc00cc00ffffccccffffcccccc00cc00cc00cc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffeeeeffffeeeeeeaaee00eeaaee00ffffeeeeffffeeeeeeaaee00eeaaee00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffafafffffafafafaaa00fafaaa00fffffafafffffafafafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffcfcfffffcfcfcf0cc00fcf0cc00fffffcfcfffffcfcfcf0cc00fcf0cc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffefefffffefefefaee00fefaee00fffffefefffffefefefaee00fefaee00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffaaffaaaaaaaaaaffaaffaaaa00aa00ffaaffaaaaaaaaaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccccccccccffccffcccc00cc00ffccffccccccccccffccffcccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeeeeeeeeeffeeffeeee00ee00ffeeffeeeeeeeeeeffeeffeeee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffafafafafafffafffaaa00aa00fffafffafafafafafffafffaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfcfcfcfcfffcfffccc00cc00fffcfffcfcfcfcfcfffcfffccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefefefefefffefffeee00ee00fffefffefefefefefffefffeee00ee00
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

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffaaaaffaaffaaaaaaaa00ffffffaaffffaaaaffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffccccffccffcccc00cc00ffffffccffffccccffccffcccc00cc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffeeeeffeeffeeeeaaee00ffffffeeffffeeeeffeeffeeeeaaee00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0fffff0f0fff0fff0f0f00000fffffff0fffff0f0fff0fff0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffafafffafffafafaaa00fffffffafffffafafffafffafafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcfffffcfcfffcfffcfcf0cc00fffffffcfffffcfcfffcfffcfcf0cc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffefefffefffefefaee00fffffffefffffefefffefffefefaee00
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

def dom_145 : Nat := 0x3000300000000000000000000000000030003
def goal_145 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_145 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeaaaa0000aaaa0000aaaa0000aaaa0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaafafa0000fafa0000fafa0000fafa0000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeefafa0000fafa0000fafa0000fafa0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffcccc00cc00cc00cc00cc00cc00cc00cc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeeeaaee00eeaaee00eeaaee00eeaaee00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xffffff00ffffff00ffffff00ffffff00f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xffffffaaffffffaaffffffaaffffffaafafaaa00fafaaa00fafaaa00fafaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xffffffccffffffccffffffccffffffccfcf0cc00fcf0cc00fcf0cc00fcf0cc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xffffffeeffffffeeffffffeeffffffeefefaee00fefaee00fefaee00fefaee00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_161 : Nat := 0x30000000300000000000000000000000300000003
def goal_161 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xffffffffccccccccffffffffccccccccfcfcfcfc00000000fcfcfcfc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeefefefefe00000000fefefefe00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_168 : Nat := 0x1010000010100000000000000000000010100000101
def goal_168 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_168 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffffccffccffffffffffccffccffccffcccc00cc00ffccffcccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeee00ee00ffeeffeeee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xffffffffffaaffaaffffffffffaaffaafffafffaaa00aa00fffafffaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xffffffffffccffccffffffffffccffccfffcfffccc00cc00fffcfffccc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xffffffffffeeffeeffffffffffeeffeefffefffeee00ee00fffefffeee00ee00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffffffccccffffffffffffcccccccccccc00000000cccccccc00000000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffeeeeffffffffffffeeeeeeeeeeeeaaaa0000eeeeeeeeaaaa0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xffffffffffffaaaaffffffffffffaaaafafafafafafa0000fafafafafafa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xffffffffffffccccffffffffffffccccfcfcfcfcf0f00000fcfcfcfcf0f00000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xffffffffffffeeeeffffffffffffeeeefefefefefafa0000fefefefefafa0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffffffffffff00ffffffffffffff00ff00ff0000000000ff00ff0000000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffffaaffffffffffffffaaffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffffccffffffffffffffccffccffcccc00cc00ffccffcccc00cc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffeeffffffffffffffeeffeeffeeeeaaee00ffeeffeeeeaaee00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xffffffffffffff00ffffffffffffff00fff0fff0f0f00000fff0fff0f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xffffffffffffffaaffffffffffffffaafffafffafafaaa00fffafffafafaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xffffffffffffffccffffffffffffffccfffcfffcfcf0cc00fffcfffcfcf0cc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xffffffffffffffeeffffffffffffffeefffefffefefaee00fffefffefefaee00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfefefefefefefefeeeeeeeeeeeeeeeeefefefefefefefefe0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaaaaaaaaaaaaaaaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffccffccffccffccffccffccffccffcccccccccccccccccccc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeeeeeeeeeeeeeeeeeee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffaffaaffaaffaaffaafafafafafafafafaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffcfffcfffcfffcffccffccffccffccfcfcfcfcfcfcfcfccc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffeffeeffeeffeeffeefefefefefefefefeee00ee00ee00ee00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeaaaa0000aaaa0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffff0f0fffff0f0ffff0000ffff0000fffff0f0fffff0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffafafffffafaffffaaaaffffaaaafffffafafffffafafafa0000fafa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcffffccccffffccccfffffcfcfffffcfcf0f00000f0f00000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefeffffeeeeffffeeeefffffefefffffefefafa0000fafa0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffff00ffffff00ffffff00ffffff00ffff0000ffff00000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffffaaaaffffaaaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffffffccffffffccffffccccffffcccccc00cc00cc00cc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffffeeeeffffeeeeeeaaee00eeaaee00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffff0fffffff0ffffff00ffffff00fffff0f0fffff0f0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffafffffffaffffffaaffffffaafffffafafffffafafafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcffffffccffffffccfffffcfcfffffcfcfcf0cc00fcf0cc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffeffffffeeffffffeefffffefefffffefefefaee00fefaee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffccccccccffffffffcccccccccccccccccccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffafafafaffffffffaaaaaaaafafafafafafafafafafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcffffffffccccccccfcfcfcfcfcfcfcfcfcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefeffffffffeeeeeeeefefefefefefefefefefefefe00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaaaaaaaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffffccffccffccffccccccccccffccffcccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeeeeeeeeeffeeffeeee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffff0fff0ffffffffff00ff00fff0fff0f0f0f0f0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffaffffffffffaaffaafffafffafafafafafffafffaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcffffffffffccffccfffcfffcfcfcfcfcfffcfffccc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffeffffffffffeeffeefffefffefefefefefffefffeee00ee00
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

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffff0f0ffffffffffff0000fffff0f0fffff0f0f0f0f0f0f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffafaffffffffffffaaaafffffafafffffafafafafafafafa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcffffffffffffccccfffffcfcfffffcfcfcfcfcfcf0f00000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefeffffffffffffeeeefffffefefffffefefefefefefafa0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffff00ffffffffffffff00ffffff00ffff0000ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffffffffffaaffffffaaffffaaaaffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffffffffffccffffffccffffccccffccffcccc00cc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffffffeeffffffeeffffeeeeffeeffeeeeaaee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffff0ffffffffffffff00fffffff0fffff0f0fff0fff0f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffaffffffffffffffaafffffffafffffafafffafffafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcffffffffffffffccfffffffcfffffcfcfffcfffcfcf0cc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffeffffffffffffffeefffffffefffffefefffefffefefaee00
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
def isoMvS_81:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_41
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_41
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_41
def isoMvS_138:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_138:Lower true dom_138 roots_138 goal_138 4:=lower_iso_b isoMvS_138 (by decide +kernel) lowS_41
def isoMvS_145:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_145:Lower true dom_145 roots_145 goal_145 4:=lower_iso_b isoMvS_145 (by decide +kernel) lowS_41
def isoMvS_161:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_161:Lower true dom_161 roots_161 goal_161 4:=lower_iso_b isoMvS_161 (by decide +kernel) lowS_41
def isoMvS_168:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_168:Lower true dom_168 roots_168 goal_168 4:=lower_iso_b isoMvS_168 (by decide +kernel) lowS_41
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
|0=>0x14815240925545514055248550405
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
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 4:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_27
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_45
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_43
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_45
def isoMvS_89:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_45
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 4:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_27
def isoMvS_105:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_45
def isoMvS_106:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_45
def isoMvS_113:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_45
def isoMvS_114:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 4:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_27
def isoMvS_116:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_45
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_43
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_45
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_45
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_43
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_45
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 4:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_27
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_43
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_45
def isoMvS_170:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 7:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_169
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_45
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 5:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_45
def isoMvS_201:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_45
def isoMvS_202:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_45
def isoMvS_209:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 5:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_43
def isoMvS_212:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_45
def isoMvS_216:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 4:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_27
def isoMvS_226:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_45
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
theorem lowS_107:Lower true dom_107 roots_107 goal_107 6:=lower_slice_b [(0xa0a00000a0a00000a0a00000a0a,8,9)] (by decide +kernel) lowS_106
namespace S_121
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(8,9),(8,40),(16,17),(16,80),(24,25),(24,56),(24,88),(32,33),(32,40),(48,49),(48,56),(48,112),(64,65),(64,80),(72,73),(72,88),(72,104),(96,97),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_121.map (·&&&dom_121)
def gM:=goal_121&&&dom_121
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x12653
|4,0=>0x193c809d0f00d1e00823
|5,0=>0x847868153d776ac652813a7791d8e41d19f138bf0a88d05b9d
|6,0=>0xb9efe6f9be33df731529
|7,0=>0xb9efe
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c0000080800000c0c00000808030003000200020003000300020002c0c0c000c0c0c000c0c0c000c0c0c02020200020202000202020002020200c0c0c0c080808080c0c0c0c080008030203020302030203020302030203028080808080808080800080008000800000303000003030000000200000002c0c00000c0c00000c0c00000c0c000202020202020202020202020202020200000000c0c0c08000000000c0c0c0b030303030303030000000000000000c0c0c0c000000000c0c0c0c00000003030202030302020303020203030000c000c000c000c000c000c000c000c03030303030303030202020202020202
|0,1=>0x202000002020000020200000202c0c0c0c0c0c0c0c0c000c000c000c03030303030303030302030203020302c0c0c0c0c0c0c0c0c0c0c0c00000001010101010101010101010100000000000000000000808000000000000080b030303020202020303030302020202000000008080808000000000808080b030000030302020303000003030202
|_,_=>0
def sP:Nat→Nat
|0=>0xce1310670989519c262486709883384d824867338833d82625467080c3384d420ce134c92384d120e0709883384cf20ce6710670998459c2620cea4906132087098a418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682ced9ab2f652c8d8f2986
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 25 122 0x3ffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x19130d31f90730db9931130f698
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x42312100000011000001
|6,0=>0x817161
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0x3ff6fb5b512185080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x2430051006
|6,0=>0x7a98
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_113 5 roots_113 ops++addP pm 1 dom_41 4 roots_41 ops++addP pm 2 dom_89 5 roots_89 ops++addP pm 3 dom_105 5 roots_105 ops++addP pm 4 dom_81 4 roots_81 ops++addP pm 5 dom_57 5 roots_57 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_121 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_57 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_113 5 s (0,roots_113.map (·&&&dom_113)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_121 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_113 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_121==dom_121)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_121 gM v ys):RunD true dom_121 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_121 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_121 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_121 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_121 roots_121 goal_121 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_121
theorem lowS_121:Lower true dom_121 roots_121 goal_121 8:=S_121.noCircuit
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_slice_b [(0xcc00cc00000000000000000000000000cc00cc,128,130)] (by decide +kernel) lowS_149
namespace S_155
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,129),(2,10),(2,130),(3,11),(3,19),(3,131),(8,9),(8,10),(8,136),(16,17),(16,144),(18,19),(18,26),(18,146),(24,25),(24,26),(24,152),(128,129),(128,130),(128,136),(128,144)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_155.map (·&&&dom_155)
def gM:=goal_155&&&dom_155
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x9aa9
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000000000000000000000000000f0f0000f000f000000000000000000000000000f000f00c0c0c0c0000000000000000000000000c0c0c0ca0a0a0a0000000000000000000000000a0a0a0af0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 156 0xfffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_154 5 roots_154 ops++addP pm 1 dom_153 5 roots_153 ops++addP pm 2 dom_147 5 roots_147 ops++addP pm 3 dom_139 5 roots_139 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_155 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_139 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_154 5 s (0,roots_154.map (·&&&dom_154)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_155 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_154 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_155==dom_155)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_155 gM v ys):RunD true dom_155 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_155 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_155 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_155 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_155 roots_155 goal_155 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_155
theorem lowS_155:Lower true dom_155 roots_155 goal_155 7:=S_155.noCircuit
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_slice_b [(0xa0a00000a0a000000000000000000000a0a00000a0a,8,9)] (by decide +kernel) lowS_170
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_slice_b [(0x30300000303000000000000000000000303000003030,32,36)] (by decide +kernel) lowS_169
theorem lowS_185:Lower true dom_185 roots_185 goal_185 8:=lower_slice_b [(0x30300000303000000000000000000000303000003030000,1,17)] (by decide +kernel) lowS_169
def isoMvS_87:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_iso_b isoMvS_87 (by decide +kernel) lowS_47
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 6:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_61
def isoMvS_93:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 7:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_59
def isoMvS_94:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 7:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_62
def isoMvS_109:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 6:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_61
def isoMvS_110:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_61
def isoMvS_115:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 6:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_61
def isoMvS_117:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_107
def isoMvS_118:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 6:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_61
def isoMvS_122:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_62
def isoMvS_124:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 7:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_62
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 7:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_59
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 7:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_62
def isoMvS_167:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_47
def isoMvS_174:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 8:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_173
def isoMvS_179:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_155
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 6:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_107
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 6:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_61
def isoMvS_186:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 8:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_173
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 6:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_61
def isoMvS_199:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 5:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_55
def isoMvS_203:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 6:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_107
def isoMvS_205:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 7:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_62
def isoMvS_206:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 7:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_62
def isoMvS_211:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 6:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_107
def isoMvS_213:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 7:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_155
def isoMvS_214:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 6:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_61
def isoMvS_217:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 7:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_155
def isoMvS_218:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 6:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_61
def isoMvS_220:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 7:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_62
def isoMvS_227:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 6:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_107
def isoMvS_229:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 6:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_61
def isoMvS_230:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 6:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_61
def isoMvS_233:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_173
def isoMvS_234:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 8:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_173
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 7:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_62
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 7:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_155
def isoMvS_242:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 6:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_61
def isoMvS_244:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 6:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_61
def isoMvS_248:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 7:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_62
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
|0=>0xb492ca4b2a2c34b282c38b4b2924b2b292cb0d2c34b282ca44482ca4b294424b280d1cb282ca8b292ca514a2ca0b2b2ca844b2ca43452ca03712cad1492ca0b294414b282ca43352d2c3732caca372ca4b294524b282ca51052ca0b294c144482ca44472ca0b29
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xa30009100063000000cc03000000000000000
|6,0=>0x301002f1002d2acaa1a0a62002519063184800000007c9d2001b26480000172001610000050931448f238400000d1
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xfb7e9c2b01bf620836047f5f97b52044510411003a4c93043d090200700e0140400400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xc070104228c0000000
|6,0=>0x711a9541f09018d67800dc0589500181380ccc16980007
|7,0=>0x27ad477295f77
|8,0=>0xb
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_62 7 roots_62 ops++addP pm 1 dom_54 4 roots_54 ops++addP pm 2 dom_29 4 roots_29 ops++addP pm 3 dom_59 7 roots_59 ops++addP pm 4 dom_45 5 roots_45 ops++addP pm 5 dom_61 6 roots_61 ops++addP pm 6 dzo_47_16 6 roots_47 ops++addP pm 7 dom_47 6 roots_47 ops++addP pm 8 dom_31 5 roots_31 ops++addP pm 9 dom_55 5 roots_55 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_63 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_29 _ g hchk
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
theorem lowS_111:Lower true dom_111 roots_111 goal_111 7:=lower_slice_b [(0xaaaa0000aaaa0000aaaa0000aaaa,8,9)] (by decide +kernel) lowS_110
theorem lowS_123:Lower true dom_123 roots_123 goal_123 9:=lower_slice_b [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,8,10)] (by decide +kernel) lowS_121
def dzo_118_8:=0x55005500550055005500550055005500
def gzo_118_8:=0x55005500550054005500550054004400
def gsh_118_8:=0x550055005500540055005500540044
theorem lowS_zo_118_8_84:Lower true dzo_118_8 roots_118 gzo_118_8 6:=lower_iso_b (d1:=dom_118) (r1:=roots_118) (T1:=gsh_118_8) [(dom_118,8)] (by decide +kernel) (lower_slice_b (T:=gsh_118_8) [(0x440044004400440044004400440044,0,2),(0x550055000000000055005500000000,0,32)] (by decide +kernel) lowS_84)
namespace S_126
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(4,20),(4,36),(4,68),(6,14),(6,22),(6,38),(6,70),(8,10),(8,40),(12,14),(12,28),(12,44),(12,76),(16,20),(16,80),(18,22),(18,26),(18,50),(18,82),(24,26),(24,28),(24,56),(24,88),(32,34),(32,36),(32,40),(48,50),(48,52),(48,56),(48,112),(64,66),(64,68),(64,80),(72,74),(72,76),(72,88),(72,104),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_126.map (·&&&dom_126)
def gM:=goal_126&&&dom_126
def NN:Nat→Nat
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x464f4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x2aaaaaaa800000002aaaaaaa8000000055550000555500005555000055550000aa00aa00aa00aa00aa00aa00aa00aa0141414141414141414141414141414142222222222222222222222222222222255555555555555550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>6
|_,_=>0
def wAt:=mkWire dB 6 127 0x7fffffffffffffffffffffffffffffff
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
addP pm 0 dom_124 7 roots_124 ops++addP pm 1 dom_122 7 roots_122 ops++addP pm 2 dom_62 7 roots_62 ops++addP pm 3 dom_94 7 roots_94 ops++addP pm 4 dom_118 6 roots_118 ops++addP pm 5 dzo_118_8 6 roots_118 ops++addP pm 6 dom_110 6 roots_110 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_126 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_118_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_110 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_124 7 s (0,roots_124.map (·&&&dom_124)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_126 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_124 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_126==dom_126)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_126 gM v ys):RunD true dom_126 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_126 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_126 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_139_4:=0xf0f00000000000000000000000000000f0f0
def gzo_139_4:=0xf0e00000000000000000000000000000e000
def gsh_139_4:=0xf0e00000000000000000000000000000e00
theorem lowS_zo_139_4_139:Lower true dzo_139_4 roots_139 gzo_139_4 5:=lower_iso_b (d1:=dom_139) (r1:=roots_139) (T1:=gsh_139_4) [(dom_139,4)] (by decide +kernel) (lower_slice_b (T:=gsh_139_4) [] (by decide +kernel) lowS_139)
def dzo_155_4:=0xf0f0f0f0000000000000000000000000f0f0f0f0
def gzo_155_4:=0xf0f0f0e0000000000000000000000000f0f0e000
def gsh_155_4:=0xf0f0f0e0000000000000000000000000f0f0e00
theorem lowS_zo_155_4_139:Lower true dzo_155_4 roots_155 gzo_155_4 6:=lower_iso_b (d1:=dom_155) (r1:=roots_155) (T1:=gsh_155_4) [(dom_155,4)] (by decide +kernel) (lower_slice_b (T:=gsh_155_4) [(0xf0f00000000000000000000000000000f0f0000,0,16)] (by decide +kernel) lowS_139)
namespace S_159
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,129),(2,10),(2,130),(3,11),(3,19),(3,131),(4,20),(5,13),(5,21),(5,133),(6,14),(6,22),(6,134),(7,15),(7,23),(7,135),(8,9),(8,10),(8,136),(12,13),(12,14),(12,28),(12,140),(16,17),(16,20),(16,144),(18,19),(18,22),(18,26),(18,146),(24,25),(24,26),(24,28),(24,152),(128,129),(128,130),(128,136),(128,144),(132,133),(132,134),(132,140),(132,148)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_159.map (·&&&dom_159)
def gM:=goal_159&&&dom_159
def NN:Nat→Nat
|4=>3
|5=>10
|6=>17
|7=>7
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xed5bb15afa0a7ad
|5,0=>0xfc76cc435ac062aae80ca7168a707d655c15a2743e58a3a05f
|6,0=>0xee111db8e9d5e13c57a7bedaabcdbca6343955fb91c0d805b57526851f474dd723ff0c240aa1ddd913e21
|7,0=>0xd48dfb41289fc4a95ddb867b3747785ea39
|8,0=>0x932a5
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfff00ff0000000000000000000000000f0f000033333333000000000000000000000000330033000f0f00000000000000000000000000000f0f0000ffffff000000000000000000000000000000000033003333000000000000000000000000330033003333333300000000000000000000000033333300ffffffff00000000000000000000000000000000ffffffcc000000000000000000000000ccccccccaaaaaaaa000000000000000000000000aaaaaaaaffffffff000000000000000000000000ffff0000ff00ff00000000000000000000000000ff00ff00ffff0000000000000000000000000000ffff0000ffffffff000000000000000000000000ff00ff00f0f0f0f0000000000000000000000000f0f0f0f0cccccccc000000000000000000000000ccccccccffffffaa000000000000000000000000aaaaaaaa
|0,1=>0xffffffff000000000000000000000000ffffff00f0fff0ff000000000000000000000000f0f0f0f0ffff00ff000000000000000000000000ffff00000000ffff0000000000000000000000000000ff0000000000000000000000000000000000ffffff00ffffffff0000000000000000000000000f0f000000ff00ff00000000000000000000000000000000000000ff000000000000000000000000000000000000ffff00000000000000000000000000000000ff00ffff000000000000000000000000ff00ff0000ff00ff00000000000000000000000000ff0000ffffff00000000000000000000000000ffffff00ffffffff000000000000000000000000f0f0f0f05555555500000000000000000000000055555500
|_,_=>0
def sP:Nat→Nat
|0=>0x104e99106209d24284ed4dc85104e9b106509da9250a209d24288279a485104e9610b13b92428820490a20c124284ef490a241d2429dcd498a209d8418827610a23ad24288ea4906241cc51040418820
|1=>0x214413a4c428827490b109d24288274d64428827490a209d3720ca209d24284ed4f485104e92144772485e04e9d90a209d2428827d2483288ee4e485104e920cb109d24284f84c8c5
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa5055005
|5,0=>0x4563f63963362d62762161b61560f6
|6,0=>0xb87b26ac6a579e79779078978367c77576e76776075975274b7
|7,0=>0xe77e16da7d37cc7c57bf6
|8,0=>0xee6
|_,_=>0
def wAt:=mkWire dB 30 160 0xffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2251252262152a62a520b20d2a51872a515d2a625d2a620e2a51872a59272151252a56a520b2252152152a520b2a692621520b2a52d5226924215
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1e2709a26096250922408e2308a2208621082200002
|7,0=>0x261946418c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xfff7f57d7775644d3027201816060500
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x6182272783942750b
|7,0=>0xefebddc
|8,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_158 7 roots_158 ops++addP pm 1 dzo_139_4 5 roots_139 ops++addP pm 2 dom_155 7 roots_155 ops++addP pm 3 dzo_155_4 6 roots_155 ops++addP pm 4 dom_151 6 roots_151 ops++addP pm 5 dom_157 7 roots_157 ops++addP pm 6 dom_139 5 roots_139 ops++addP pm 7 dom_31 5 roots_31 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_159 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_139_4_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_155_4_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_31 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_158 7 s (0,roots_158.map (·&&&dom_158)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_159 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_158 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_159 gM v ys):RunD true dom_159 gM v (ori ys):=h
def Z (s:Nat):=barP dom_159 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_159 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_159 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_159 roots_159 goal_159 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_159
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=S_159.noCircuit
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_slice_b [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,8,9)] (by decide +kernel) lowS_174
theorem lowS_183:Lower true dom_183 roots_183 goal_183 8:=lower_slice_b [(0xf000f000f000f0000000000000000000f000f000f000f0,16,20)] (by decide +kernel) lowS_179
def dzo_171_16:=0xf0f00000f0f000000000000000000000f0f00000f0f0000
def gzo_171_16:=0xf0f00000f0f000000000000000000000f0e00000e0a0000
def gsh_171_16:=0xf0f00000f0f000000000000000000000f0e00000e0a
theorem lowS_zo_171_16_42:Lower true dzo_171_16 roots_171 gzo_171_16 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_16) [(dom_171,16)] (by decide +kernel) (lower_slice_b (T:=gsh_171_16) [(0xa0a00000a0a000000000000000000000a0a00000a0a,0,1),(0xf0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
namespace S_187
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,10),(2,34),(2,130),(3,11),(3,19),(3,35),(3,131),(8,9),(8,10),(8,40),(8,136),(16,17),(16,144),(18,19),(18,26),(18,50),(18,146),(24,25),(24,26),(24,56),(24,152),(32,33),(32,34),(32,40),(32,160),(48,49),(48,50),(48,56),(48,176),(128,129),(128,130),(128,136),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_187.map (·&&&dom_187)
def gM:=goal_187&&&dom_187
def NN:Nat→Nat
|5=>2
|6=>8
|7=>9
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x4b53d0a8d3
|6,0=>0xd38a6ae7e488f275b9765b3ed312203045f09edb
|7,0=>0xc3cc4bf55c8852f6494852dbc3082822f9a0aba606719
|8,0=>0x6a88837c7026f6b
|9,0=>0x3dbb0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f000000000000000000000f0f0f0f0f0f000000f000f000f00000000000000000000000f000f000f000000000000f0f0f000000000000000000000000000f0f0f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00f0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0f00000f0f000000000000000000000f0f00000f0f0000f000f000f000f0000000000000000000f000f000f000f00f0f0f0f0f0f0f0000000000000000000f0f0f0f0f0f0f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0cf0f0f0f0000000000000000000000000f0f0f0f00000000f0f0f000f0f0f0000000000000000000f0f0f000f0f0f00f0f0f0f0f0f0f0f00000000000000000f000f000f000f00a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a30303030303030300000000000000000303030303000300f0f0f0f0f0f0f0f00000000000000000000000000000000
|0,1=>0xf000f000f000f0000000000000000000f000f00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x524c2020a93080520cc2030aa498407946930805524c2801872a9261016550cc201526138072a869309855244102cea1984552441020e9308072906611caa4882028cc26818520cc2020e3308a418820
|1=>0x5524c201543498407952610165
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x65006
|6,0=>0x3773162b62561f61871260b7
|7,0=>0x7566f66876175a75284b74563e7
|8,0=>0x8878267b7
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 17 188 0xfffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x4815152a55a92a552548128d4812a948149e28149d2812a54817a751528148128d4812812a548161b28d4815a949528152528148161b49d4812175254a928d4815a92812a5481
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0x6095348cf330ca21cc43
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0x1af3d71e38e5e0feb6f3b39d5e6ae3479a38d1827eb2f793ac3de070020008001e000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x20
|6,0=>0x12d2540cc4
|7,0=>0x7851f28b5d3
|8,0=>0x31cb
|9,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_186 8 roots_186 ops++addP pm 1 dom_59 7 roots_59 ops++addP pm 2 dom_139 5 roots_139 ops++addP pm 3 dom_163 5 roots_163 ops++addP pm 4 dom_147 5 roots_147 ops++addP pm 5 dom_185 8 roots_185 ops++addP pm 6 dom_155 7 roots_155 ops++addP pm 7 dom_179 7 roots_179 ops++addP pm 8 dzo_43_16 5 roots_43 ops++addP pm 9 dom_51 4 roots_51 ops++addP pm 10 dzo_171_16 6 roots_171 ops++addP pm 11 dom_171 8 roots_171 ops++addP pm 12 dom_27 4 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_187 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_43_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_171_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_186 8 s (0,roots_186.map (·&&&dom_186)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_187 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_186 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_187==dom_187)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_187 gM v ys):RunD true dom_187 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_187 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_187 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_189:Lower true dom_189 roots_189 goal_189 9:=lower_slice_b [(0x303030303030303000000000000000003030303030303030,16,20)] (by decide +kernel) lowS_185
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_slice_b [(0x505050505050505000000000000000005050505050505050,16,20)] (by decide +kernel) lowS_186
theorem lowS_207:Lower true dom_207 roots_207 goal_207 8:=lower_slice_b [(0xaaaa000000000000aaaa000000000000aaaa000000000000aaaa,8,9)] (by decide +kernel) lowS_206
namespace S_219
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,10),(2,66),(2,130),(3,11),(3,19),(3,67),(3,131),(8,9),(8,10),(8,136),(16,17),(16,80),(16,144),(18,19),(18,26),(18,82),(18,146),(24,25),(24,26),(24,88),(24,152),(64,65),(64,66),(64,80),(72,73),(72,74),(72,88),(72,200),(128,129),(128,130),(128,136),(128,144),(192,193),(192,194),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_219.map (·&&&dom_219)
def gM:=goal_219&&&dom_219
def NN:Nat→Nat
|5=>3
|6=>5
|7=>4
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x64e8810b45094e6
|6,0=>0xfbd3eca7818ad691a91e04e6c
|7,0=>0xdadac60ca90af55088ca
|8,0=>0x798d4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f00f0e0f0e000000000f0e0f0e000000000f0e0f0e000000000f0e0f0ef0a0f0a000000000f0a0f0a000000000f0a0f0a000000000f0a0f0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0af0f0f0f0000000000000000000000000f0f0f0f00000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000a0af0f0f0f000000000f0f0f0f00000000000000000000000000000000f0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0ac0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0cf0f0000000000000f0f0000000000000f0f0000000000000f0f0000f000f00000000000f000f00000000000f000f00000000000f000f00f0f0f0f000000000f0f0f0f000000000e0e0e0e000000000e0e0e0ee0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0ea0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x5461a854671a85c461a85421a8e5461a85421085d421a85c42a8546b1085427a846190854270543210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x2d832806
|6,0=>0x2b648e798bb916
|7,0=>0x8aef9dc3317
|8,0=>0x4c6
|_,_=>0
def wAt:=mkWire dB 15 220 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x6141585546a16158541585a846161585
|_=>0
def oO:Nat→Nat→Nat
|5,0=>1
|6,0=>0x7261423112
|7,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x9807f57e57b53f5018006000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>1
|6,0=>0x353d
|7,0=>0x6f3
|8,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_217 7 roots_217 ops++addP pm 1 dom_89 5 roots_89 ops++addP pm 2 dom_83 5 roots_83 ops++addP pm 3 dom_209 5 roots_209 ops++addP pm 4 dom_211 6 roots_211 ops++addP pm 5 dom_155 7 roots_155 ops++addP pm 6 dom_91 6 roots_91 ops++addP pm 7 dom_218 6 roots_218 ops++addP pm 8 dom_202 5 roots_202 ops++addP pm 9 dom_203 6 roots_203 ops++addP pm 10 dom_216 4 roots_216 ops++addP pm 11 dom_154 5 roots_154 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_154 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_217 7 s (0,roots_217.map (·&&&dom_217)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_217 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_219==dom_219)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_219 gM v ys):RunD true dom_219 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_219 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_219 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_84_8:=0x110011000000000011001100
def gzo_84_8:=0x110010000000000010000000
def gsh_84_8:=0x1100100000000000100000
theorem lowS_zo_84_8_84:Lower true dzo_84_8 roots_84 gzo_84_8 4:=lower_iso_b (d1:=dom_84) (r1:=roots_84) (T1:=gsh_84_8) [(dom_84,8)] (by decide +kernel) (lower_slice_b (T:=gsh_84_8) [] (by decide +kernel) lowS_84)
def dzo_201_4:=0x3030000000000000303000000000000030300000000000003030
def gzo_201_4:=0x3030000000000000302000000000000030300000000000002000
def gsh_201_4:=0x303000000000000030200000000000003030000000000000200
theorem lowS_zo_201_4_137:Lower true dzo_201_4 roots_201 gzo_201_4 5:=lower_iso_b (d1:=dom_201) (r1:=roots_201) (T1:=gsh_201_4) [(dom_201,4)] (by decide +kernel) (lower_slice_b (T:=gsh_201_4) [(0x303000000000000000000000000000003030000000000000000,0,64)] (by decide +kernel) lowS_137)
def dzo_212_8:=0x11001100000000001100110000000000110011000000000011001100
def gzo_212_8:=0x11001100000000001100110000000000110010000000000010000000
def gsh_212_8:=0x110011000000000011001100000000001100100000000000100000
theorem lowS_zo_212_8_84:Lower true dzo_212_8 roots_212 gzo_212_8 5:=lower_iso_b (d1:=dom_212) (r1:=roots_212) (T1:=gsh_212_8) [(dom_212,8)] (by decide +kernel) (lower_slice_b (T:=gsh_212_8) [(0x110011000000000011001100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_137_4:=0x303000000000000000000000000000003030
def gzo_137_4:=0x302000000000000000000000000000002000
def gsh_137_4:=0x30200000000000000000000000000000200
theorem lowS_zo_137_4_137:Lower true dzo_137_4 roots_137 gzo_137_4 4:=lower_iso_b (d1:=dom_137) (r1:=roots_137) (T1:=gsh_137_4) [(dom_137,4)] (by decide +kernel) (lower_slice_b (T:=gsh_137_4) [] (by decide +kernel) lowS_137)
def dzo_217_4:=0x30303030000000003030303000000000303030300000000030303030
def gzo_217_4:=0x30303030000000003030302000000000303030300000000030302000
def gsh_217_4:=0x3030303000000000303030200000000030303030000000003030200
theorem lowS_zo_217_4_137:Lower true dzo_217_4 roots_217 gzo_217_4 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_4) [(dom_217,4)] (by decide +kernel) (lower_slice_b (T:=gsh_217_4) [(0x3030000000000000303000000000000030300000000000003030000,0,16),(0x3030303000000000000000000000000030303030000000000000000,0,64)] (by decide +kernel) lowS_137)
def dzo_153_4:=0x3030303000000000000000000000000030303030
def gzo_153_4:=0x3030302000000000000000000000000030302000
def gsh_153_4:=0x303030200000000000000000000000003030200
theorem lowS_zo_153_4_137:Lower true dzo_153_4 roots_153 gzo_153_4 5:=lower_iso_b (d1:=dom_153) (r1:=roots_153) (T1:=gsh_153_4) [(dom_153,4)] (by decide +kernel) (lower_slice_b (T:=gsh_153_4) [(0x303000000000000000000000000000003030000,0,16)] (by decide +kernel) lowS_137)
def dzo_213_8:=0x33003300000000003300330000000000330033000000000033003300
def gzo_213_8:=0x33003300000000003300330000000000330032000000000032002200
def gsh_213_8:=0x330033000000000033003300000000003300320000000000320022
theorem lowS_zo_213_8_84:Lower true dzo_213_8 roots_213 gzo_213_8 6:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_8) [(dom_213,8)] (by decide +kernel) (lower_slice_b (T:=gsh_213_8) [(0x220022000000000022002200000000002200220000000000220022,0,1),(0x330033000000000033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_85_8:=0x330033000000000033003300
def gzo_85_8:=0x330032000000000032002200
def gsh_85_8:=0x3300320000000000320022
theorem lowS_zo_85_8_84:Lower true dzo_85_8 roots_85 gzo_85_8 5:=lower_iso_b (d1:=dom_85) (r1:=roots_85) (T1:=gsh_85_8) [(dom_85,8)] (by decide +kernel) (lower_slice_b (T:=gsh_85_8) [(0x2200220000000000220022,0,1)] (by decide +kernel) lowS_84)
namespace S_221
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(4,20),(4,68),(5,13),(5,21),(5,69),(5,133),(8,9),(8,136),(12,13),(12,28),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(24,25),(24,28),(24,88),(24,152),(64,65),(64,68),(64,80),(72,73),(72,76),(72,88),(72,200),(128,129),(128,136),(128,144),(132,133),(132,140),(132,148),(132,196),(192,193),(192,196),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_221.map (·&&&dom_221)
def gM:=goal_221&&&dom_221
def NN:Nat→Nat
|4=>7
|5=>18
|6=>46
|7=>36
|8=>12
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x9f7488bce87ad3c646cd5d2b33cf5b0f030
|5,0=>0xf2facc73757b7ea6898e64b88628754ff4a4ef384af0546cb43b6c736c5d352ca293e1215441eb56160da0668a
|6,0=>0xeb33ebe0efa3417a33e99a0cd991de96d0490775905bb903d59035788ab38713f8087a7de9572b326e88d69f89698fb64c8163eb0628e45e4755ccc2565615224d5100e504c74ad8d4a9b644a303d2f73a88c39548390893732f36f653668c34906321e12bfec26fa719fcc1136c0fbfc0bc4c
|7,0=>0xfcc3df606ed5265afd2da5144a2afe9bfd498e01969ec8877a7c816773ec76be27528074d916d1386c65d52f64525b44ebd44c424495b739b7034f4b3260330a052bb7f2b50d292f22660223f88199741596e0dd2f0877c06f7c
|8,0=>0xf8f3fef4f0eb7939f6c497e297369e401873ab6a1670b125d80bcff02ed9
|9,0=>0x7369e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccc00000000cccc000000000000cccccccc00000000cccc00000330033000000000033003300000000002200220000000000220022cccccccc000000000000000000000000cccccccc00000000000000033333333000000003333333300000000333300000000000033330000cccccccc000000008888888800000000cccccccc000000008888888b3332222000000003333222200000000333322220000000000000000cccccccc00000000cccccc0000000000cccccccc00000000cccc88033333300000000003333330000000000333322000000000033332200c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c22222222000000002222222200000000222222220000000022222222cccccccc00000000cccccccc000000000000000000000000000000033330000000000003333000000000000333300000000000033330000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc032323232000000003232222200000000323232320000000032322222cccccccc00000000cccccccc0000000088888888000000008888888b3333333000000003333333300000000333333330000000000000000
|0,1=>0xcccc000000000000cccc000000000000cccc00000000000000033330000000000003333000000000000333333330000000033332222cccccc0000000000cccccc0000000000cccccc0000000000cccccc0333333330000000033333333000000000000333300000000000022220000000000000000cccccccc000000000000000000000000cccc00003030303000000000303000000000000030303030000000003030000cccccccc00000000cccccccc00000000cccccccc000000008888888b03030300000000030300000000000003030303000000000303000000000000000000000cccccc00000000000000000000000000cccc88033333333000000003333333300000000333333330000000033330000cc00cc0000000000cc00cc00000000008800880000000000880088000000000000000000000000000000000333322220000000033332222c8c8c8c800000000c8c8c8c800000000c8c8c8c800000000c8c8c8cb3332222000000003333222200000000333322220000000033332222cccccccc000000008888888800000000cccc000000000000888800000330033000000000033003300000000003200320000000000320022
|0,2=>0xcccccccc00000000cccccccc00000000c8c8c8c800000000c8c8c8cb333333300000000333333330000000033333333000000003333222200000000000000000000000000000000cccccccc00000000cccc888b33333330000000033333333000000000000000000000000333322224444444400000000444444440000000044444444000000004444000232323230000000023232222000000002323232300000000232322228888cccc000000008888cccc000000008888cccc000000008888888b3333333000000003333333300000000333322220000000033332222000044440000000000004444000000000000444400000000000000000000000000000000000000000000000000000000000000033332222000000000000000044444444000000000000000000000000444400033333333000000003030303000000000333333330000000030303030cc88cc8800000000cc88cc8800000000cc88cc8800000000cc88cc880003333000000000000222200000000000033330000000000002222cccccccc00000000cccc888800000000cccccccc00000000cccc88880000000000000003333222200000000000000000000000033332222
|0,3=>0xccc0ccc000000000ccc0ccc000000000ccc0ccc000000000ccc0ccc33333333000000003333333300000000330033000000000033003300cccccccc00000000cccccccc00000000c0c0c0c000000000c0c0c0c11111111000000001111111100000000111100000000000011110000ccccc0c000000000ccccc0c000000000ccccc0c000000000ccccc0c000000000000000033333300000000000000000000000000333333000000cc00000000000000cc00000000000000cc00000000000000cc011111111000000001111111100000000111111110000000000000000404040400000000040404040000000004040404000000000404040400000000000000000000000000000000323232320000000032323232
|_,_=>0
def sP:Nat→Nat
|0=>0x1c644048f0c70402481c63451031cb28549b0c704d10655a34548c0c72c01031c134a2041c600d10308134548c0c764d1036011802171c63454960c704d20718035250c0d33520c744010240d14f0c704a10238d14c0c72ca2481c60040c2040
|1=>0x3c40c764614f1031c118020718d1521031d93458440c71801440c71a20058040c72c61440d81801440c704635f4840c704035e1031c634511b0c704634c1031cb1807524cd14c1031d918d1031c670d1525040d334510668e3454831d1345103
|2=>0x1e918d1684840d33451031c634a1528040c72c51031c63671523031cb3454941031c13661031c63458601031c61440c71a53451034cb0052041c63451241c638d1440d364b34548c0c704d1031cb19f1440d80463454840c72c01448c319a345
|3=>0xc403458040c718d1440c668d1523c31c63451034f018d1440ef1c634574c1c63455840c718d1440c72c6005b840c718d16d1031c63451031c644d16c1031c63453c41c638d15d4872cd1440c71ab345103a8634548f0c704d1526c31c6345103
|4=>0xa0c1031c6345d440c70463451031d91803457441cb18d1521031c600d1441b1ccd14f1031c118d1741031c63453c40c718014c1031cb18d1521034cd1441cb1b334511b0c718d1440c718dc853040c70463440e41c118d1684840c718d1440c6
|5=>0xc718d1448c31c63451031c63453040c718d1441c6ccd144e031c63451031c118d1440f71c63451034c6345d448c31c63457444c634558c1031c6345a040c718d1528040c718d1440c71b63451071953457441b134548c0c718d1440d3180345
|6=>0x40c718d1440c71803454840c718d15d1031c6345139
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x1e5065414503d40a50154005
|5,0=>0x22188261f187661c186a619185e61618526131846610183a60d182e60a54236
|6,0=>0x6fddb876c5daa768dd9d6659d906625d8275edd7475b5d66757dd587545d4a750dd3c74d993064a5d2274719157439d077401cf973c9ced5399cdf7361cd1732d8c472f5cb672bdca8728d49c7255c8e7
|7,0=>0xafa2b86ac22a97a8629a7a51a8e6a1de8079e227089a22617966253692e24478f5e3588bda287885e1a784de0b880e1fc77d5def67a1de17769dd46735dc67
|8,0=>0xc41f097c09efb7bd1eee6b9dee16b69ed37b31ec66
|9,0=>0x3176
|_,_=>0
def wAt:=mkWire dB 58 222 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1008535185473c10d473e10d460114d4615115430418541351854f1910d4b1318d61372c44f1c14d44351008d15106440d1c64b1518d4b1318752171064c2c18d441518544550c1061548005354800d15544410c18546152c5463518544550c1061530d4415544410c34546151854615
|1=>0x1cd461548544191c6cd1548dc6111cf843518444354c5c7191c1461510344153c5443518d45354804c2c18d441548dc30618544190c44635586c6691cf84351854c3710544021c64419480041934552371845217106523748d4535187463511543041854306185461d18d44151064615
|2=>0xd1510643110c7431910543130c546151c547191074319103471930d4415101461548dc611306c4150c10615187831110644151c64d15306441510746151804d150c446351064d151c6c31310d461574dc31114d443518d441510647190c4c63530dc4151808d151054615
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11001
|5,0=>0x1a30001911631420000000001220f30e10c20b1083062024000
|6,0=>0x6910006636516326035f15c35b15925815625335120000004f20004d20004a34734524324033e23b30003923723613333122f22d22b22832620000000000002332122011d3
|7,0=>0xb02ae2ac2aa2a82a62a42a22a029e29c29a29829629429229028e28c28a28828628428228027e27c27a27827627427227026e26c26a2
|8,0=>0xbc1bb1ba1b91b81000b71b61b51b41b31b21
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x21d0000432400074680009bd000122800022e400044480008240001040000204000040200008010000f4200006b40000980000110000012000002040000400000069000008000000c40000088000010000001400000240000040000004000000600000080000008000000
|1=>0x2002620326bb006487480916e90102bf2012d5e4024afc804211900421d600843a40100358015ef90023df200453f400834c800fd69001bdd200377a4006bfc800d6e9000bdd20014ba4002040800280500050020007ba4000df480016e900029de0004fa400087580010e9
|2=>0x401d6e9411a5d240c53ac412020840404305221d608501040e0d7681916f903035da0604ba40c03d8814088c0202ff20405be40803508100191
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x102
|5,0=>0xe001038100000090a086820a04600
|6,0=>0xd801c406b12aa42142044e06000050050018361644994062008d08d47982e9cf811000016683c80a
|7,0=>0x94d22433309bb282ba04d70ccd2124f1f1a56963b98b31fa34ca8eac5b224ba
|8,0=>0x7a91e50967a3229cee7af
|9,0=>0x20
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 27 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_220 7 roots_220 ops++addP pm 1 dom_145 4 roots_145 ops++addP pm 2 dom_137 4 roots_137 ops++addP pm 3 dom_157 7 roots_157 ops++addP pm 4 dzo_84_8 4 roots_84 ops++addP pm 5 dom_93 7 roots_93 ops++addP pm 6 dom_217 7 roots_217 ops++addP pm 7 dom_205 7 roots_205 ops++addP pm 8 dom_84 4 roots_84 ops++addP pm 9 dzo_201_4 5 roots_201 ops++addP pm 10 dzo_212_8 5 roots_212 ops++addP pm 11 dzo_137_4 4 roots_137 ops++addP pm 12 dom_213 7 roots_213 ops++addP pm 13 dom_156 4 roots_156 ops++addP pm 14 dzo_217_4 6 roots_217 ops++addP pm 15 dzo_153_4 5 roots_153 ops++addP pm 16 dzo_213_8 6 roots_213 ops++addP pm 17 dom_81 4 roots_81 ops++addP pm 18 dom_29 4 roots_29 ops++addP pm 19 dzo_85_8 5 roots_85 ops++addP pm 20 dom_77 4 roots_77 ops++addP pm 21 dom_212 5 roots_212 ops++addP pm 22 dom_153 5 roots_153 ops++addP pm 23 dom_201 5 roots_201 ops++addP pm 24 dom_85 5 roots_85 ops++addP pm 25 dom_89 5 roots_89 ops++addP pm 26 dom_209 5 roots_209 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_221 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_145 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_84_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_201_4_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_212_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_137_4_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_217_4_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_153_4_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_213_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_85_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_209 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_220 7 s (0,roots_220.map (·&&&dom_220)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_221 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_220 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_221==dom_221)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_221 gM v ys):RunD true dom_221 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_221 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 46 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
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
theorem lowS_235:Lower true dom_235 roots_235 goal_235 9:=lower_slice_b [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a,8,9)] (by decide +kernel) lowS_234
namespace S_246
def pG:List (Nat×Nat):=[(2,34),(2,66),(2,130),(4,20),(4,36),(4,68),(6,22),(6,38),(6,70),(6,134),(16,20),(16,80),(16,144),(18,22),(18,50),(18,82),(18,146),(32,34),(32,36),(32,160),(48,50),(48,52),(48,112),(48,176),(64,66),(64,68),(64,80),(96,98),(96,100),(96,112),(96,224),(128,130),(128,144),(128,160),(132,134),(132,148),(132,164),(132,196),(192,194),(192,196),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_246.map (·&&&dom_246)
def gM:=goal_246&&&dom_246
def NN:Nat→Nat
|7=>3
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x3f43d207031122d
|8,0=>0x3f43d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaa00aa00aa00aa008800880088008800aa00aa00aa00aa008800880088008954015400000000015401540000000001540154000000000154015400000002a8000002a8000002a8000002a8000002a8000002a8000002a8000002a800054005400540054005400540054005400540054005400540054005400540054a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a110011001100110011001100110011001100110011001100110011001100112a802a802a802a8000000000000000002a802a802a802a800000000000000055005500550055005500550055005500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x35688d5a2357d11ac688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0x398ee07
|8,0=>0x146
|_,_=>0
def wAt:=mkWire dB 8 247 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x294d
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x441
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 6
def pmP:Nat→Nat
|0=>0xfff7bf3ff329000
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x5a
|8,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_244 6 roots_244 ops++addP pm 1 dom_118 6 roots_118 ops++addP pm 2 dom_116 5 roots_116 ops++addP pm 3 dom_242 6 roots_242 ops++addP pm 4 dom_178 5 roots_178 ops++addP pm 5 dom_182 6 roots_182 ops++addP pm 6 dom_226 5 roots_226 ops++addP pm 7 dom_212 5 roots_212 ops++addP pm 8 dom_230 6 roots_230 ops++addP pm 9 dom_214 6 roots_214 ops++addP pm 10 dom_166 5 roots_166 ops++addP pm 11 dom_86 5 roots_86 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_246 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_86 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_244 6 s (0,roots_244.map (·&&&dom_244)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_246 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_244 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcccccccccccccccccccccccccccccccc,126)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffffffffffffffff0000000000000000,64),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_246==dom_246)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_246 gM v ys):RunD true dom_246 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_246 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_246 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_246 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_246 roots_246 goal_246 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_246
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=S_246.noCircuit
namespace S_249
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(8,9),(8,40),(8,136),(16,17),(16,80),(16,144),(24,25),(24,56),(24,88),(24,152),(32,33),(32,40),(32,160),(48,49),(48,56),(48,112),(48,176),(64,65),(64,80),(72,73),(72,88),(72,104),(72,200),(96,97),(96,104),(96,112),(96,224),(128,129),(128,136),(128,144),(128,160),(192,193),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_249.map (·&&&dom_249)
def gM:=goal_249&&&dom_249
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x8c72
|7,0=>0xa32f1661252bbac25e6824b3a
|8,0=>0xb3f6f262dc
|9,0=>0x2c020
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3020302000000000302030200000000030203020000000003020302c0c0c0c0c080c080c0c0c0c0c080c080c0c0c0c0c080c080c0c0c0c0c080c0b00030003000300030003000300030003000300030003000300030003000300c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c0000000202020202020202020202020202020202020202020202020202020202020202c0c0c0c0c000c000c0c0c0c0c000c000c0c0c0c0c000c000c0c0c0c0c000c0303030302020202030303030202020203030303020202020303030302020202c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c000302030203020302030203020302030203020302030203020302030203020302c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c000000000000000303030303030303030303030303030300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x738610573861047386107386a1047328109738610947386105732610543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d5736067
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 250 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1e17649f8661976521765217661d865e1865d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x1fff45fe7eff5f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x24876
|8,0=>0x53
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_233 8 roots_233 ops++addP pm 1 dom_121 8 roots_121 ops++addP pm 2 dom_185 8 roots_185 ops++addP pm 3 dom_241 7 roots_241 ops++addP pm 4 dom_217 7 roots_217 ops++addP pm 5 dom_248 7 roots_248 ops++addP pm 6 dom_240 4 roots_240 ops++addP pm 7 dom_216 4 roots_216 ops++addP pm 8 dom_209 5 roots_209 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_249 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_209 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_233 8 s (0,roots_233.map (·&&&dom_233)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_249 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_233 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_249==dom_249)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_249 gM v ys):RunD true dom_249 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_249 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_249 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_95:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_95:Lower true dom_95 roots_95 goal_95 9:=lower_iso_b isoMvS_95 (by decide +kernel) lowS_63
def isoMvS_119:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_119:Lower true dom_119 roots_119 goal_119 7:=lower_iso_b isoMvS_119 (by decide +kernel) lowS_111
def isoMvS_125:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=lower_iso_b isoMvS_125 (by decide +kernel) lowS_123
def isoMvS_215:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 8:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_183
def isoMvS_222:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_126
def isoMvS_231:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 7:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_111
def isoMvS_237:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xcccccccccccccccccccccccccccccccc,126),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 9:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_190
def isoMvS_238:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xcccccccccccccccccccccccccccccccc,126)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_190
def isoMvS_243:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_219
def isoMvS_245:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 9:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_219
def isoMvS_250:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccccccccccccccccccc,126)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 9:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_190
def isoMvS_252:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccccccccccccccccccc,126)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_126
def dzo_119_8:=0xff00ff00ff00ff00ff00ff00ff00ff00
def gzo_119_8:=0xff00ff00ff00fe00ff00ff00fe00ee00
def gsh_119_8:=0xff00ff00ff00fe00ff00ff00fe00ee
theorem lowS_zo_119_8_84:Lower true dzo_119_8 roots_119 gzo_119_8 7:=lower_iso_b (d1:=dom_119) (r1:=roots_119) (T1:=gsh_119_8) [(dom_119,8)] (by decide +kernel) (lower_slice_b (T:=gsh_119_8) [(0xaa00aa00aa00aa00aa00aa00aa00aa,0,1),(0xcc00cc00cc00cc00cc00cc00cc00cc,0,2),(0xff00ff0000000000ff00ff00000000,0,32)] (by decide +kernel) lowS_84)
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,10),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(4,20),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(6,14),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,10),(8,40),(12,13),(12,14),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(18,19),(18,22),(18,26),(18,50),(18,82),(24,25),(24,26),(24,28),(24,56),(24,88),(32,33),(32,34),(32,36),(32,40),(48,49),(48,50),(48,52),(48,56),(48,112),(64,65),(64,66),(64,68),(64,80),(72,73),(72,74),(72,76),(72,88),(72,104),(96,97),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|7=>1
|8=>2
|9=>3
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x289ae
|8,0=>0x3eae91040e
|9,0=>0xf69ede4ea81a2c0
|10,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffff00ffffff00ffffff00ffffff00ff000000ff000000ff000000ff00000000ff000000ff000000ff000000ff00000000ff000000ff000000ff000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ffff0000ffff0000ffff0000ffff0000ffffffff00000000ffffffff00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00ffff0000ffff0000ffff0000ffff00ffffffffffffffff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x56743205b67432056743290567a43205ba43205432980543210
|_=>0
def sO:Nat→Nat→Nat
|7,0=>6
|8,0=>0x35c67
|9,0=>0x24872148
|10,0=>0x2c7
|_,_=>0
def wAt:=mkWire dB 12 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x675da6719c6759e76a61679da
|_=>0
def oO:Nat→Nat→Nat
|7,0=>3
|8,0=>0x5232
|9,0=>0x918171
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xffbf7f1f00
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>1
|8,0=>0x1a
|9,0=>0xa2
|10,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_126 9 roots_126 ops++addP pm 1 dom_63 9 roots_63 ops++addP pm 2 dom_125 9 roots_125 ops++addP pm 3 dom_123 9 roots_123 ops++addP pm 4 dom_95 9 roots_95 ops++addP pm 5 dom_119 7 roots_119 ops++addP pm 6 dom_111 7 roots_111 ops++addP pm 7 dzo_119_8 7 roots_119 ops
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
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_119_8_84 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_126 9 s (0,roots_126.map (·&&&dom_126)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_126 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
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
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_slice_b [(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,16,20)] (by decide +kernel) lowS_187
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_slice_b [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,8,10)] (by decide +kernel) lowS_221
theorem lowS_239:Lower true dom_239 roots_239 goal_239 10:=lower_slice_b [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,8,9)] (by decide +kernel) lowS_238
namespace S_247
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(1,129),(2,34),(2,66),(2,130),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(4,68),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,23),(7,39),(7,71),(7,135),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,50),(18,82),(18,146),(32,33),(32,34),(32,36),(32,160),(48,49),(48,50),(48,52),(48,112),(48,176),(64,65),(64,66),(64,68),(64,80),(96,97),(96,98),(96,100),(96,112),(96,224),(128,129),(128,130),(128,144),(128,160),(132,133),(132,134),(132,148),(132,164),(132,196),(192,193),(192,194),(192,196),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7ffffffffffffffff
def xsM:=roots_247.map (·&&&dom_247)
def gM:=goal_247&&&dom_247
def NN:Nat→Nat
|5=>1
|6=>8
|7=>32
|8=>35
|9=>8
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xb9e09
|6,0=>0xfe62efc485d3645a86099e11d82f487af6651ebf
|7,0=>0xe0799dbed1c9ab1b3ec6b11fcad1e4ad018ab17b9a1eb8c91d89ac48168d73d8771748711816d6506d61e6725c662664c6a545f3e378393315523806216a11863a166880d8cb0ce810ab29039450368b
|8,0=>0xf1bdfe031ab3098b18ed96c6490afe8884485d968218f707c66f2da6e7c66aad46a3cb6713a641cf5e70b5d0ec55a5c52c03403353d5633d517376a93273c30b15299a62592e1aa1d14cc7129460f5380a87002040019af
|9,0=>0xb47c39ac027fd216aad45fda35fce3343e907a19
|10,0=>0x3ef7d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff00ff000000ff00ff00ff00000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000000000000f000f000f000f0000000000000000000f000f000f000f000f000f000f0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000033003300330033003300330033003300330033003300330033003300330000ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000000000000000
|0,1=>0xff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff000000ff00000000000000000000ff00ff00ff0000000000000000000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff0000000000000000ff00000000000000ff00000000000000ff00000000000000ff0000cc00cc00ff00cc00cc00cc00ff00cc00cc00cc00ff00cc00cc00cc00ff00cc0000000000000000ff000000ff0000000000000000000000ff000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000003300330033003300330033003300330033003300330033003300330000000000000000ff00ff0000000000ff00ff00000000000000000000000000ff000000000000ff00ff0000000000ff00ff00000000000000000000000000000000ff000000ff00ff00ff000000ff00ff00ff000000ff000000ff000000ff00005500550055005500550055005500550055005500550055005500550055000000000000ff00ff00ff000000ff00ff000000000000000000ff000000ff0000
|0,2=>0xff000000ff00000000000000000000000000000000f000f000f000f000f000ff00f000ff00f000f000f000f000f000f000f000f0000000000000000000000000ff00ff00000000000000000000000000ff00000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff000000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000ff00aa00ff00aa00ff00aa00ff00aa00aa00aa00aa00aa00aa00aa00aa00aaff000000ff000000ff000000ff0000000000000000000000000000000000000000ff000000ff000000ff000000ff00ff000000ff000000ff000000ff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff00000000000000000000ff00000000000000ff00000000000000ff0000000000000000ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00000000000000000000ff00ff00ff00ff000000000000000000ff000000ff0000
|0,3=>0xff00000000000000ff0000000000ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00000000000000ff00000000000000000000ff00ff00ff00ff00000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff000000ff0000ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff0000000000000000ff00cc00ff00cc00ff00cc00ff00cc00cc00cc00cc00cc00cc00cc00cc00ccff00000000000000ff00000000000000ff000000ff000000ff000000ff000000000000000000000000000000000000ff000000ff000000ff000000ff00000000ff000000ff000000ff000000ff00000000000000000000000000000000ff00ff0000000000ff00ff00ff000000ff00ff0000000000ff00ff00ff0000ff00ff00ff000000ff00ff00ff000000ff00ff0000000000ff00ff00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4719b2890c20471962890c154718a1036011c61495c30811932890c154c1c614a1090c204c2890c20541c61522430811c62890c24471852500c20463ca0c204738d1440c204c2840c20470052430810062890812c718a2430481c61440c2040
|1=>0x2890c20471a82890c204718d2840c204c1ca1030a71ca9430811cd5890c204718d1490c204c18a24308190718a2430811e318f2890c204c1ca2430811c018528980308118a2600c204c1a22890c204718a84980308118a7c90c205e18a7490c2
|2=>0x3862b30c2047c8d2842430811c62890d804718a2430811c6bf12890c204718a1090c206b1c6c090c20471962890c204c1c62842430813072894030811c6289b8204718a243081b471ac2890c204718a2430551c62849430811cd103081ac71aa
|3=>0x29f2430813062842430811f92842430811c6e0d2890c204719c2890c204718a2770c204718a243081d8718a2600c204718d2890c204c1c62890c29c719a29f2430811c614a2570c204629f2430811c64ca243d411c6289d030811c62890c2047
|4=>0x7c90c204718a1090c204718a2430811c698a2430811c6c8a2570c204718a2430811c6e4a2570c204719314a1090c20471bb2430811c62a11090c204718a1030811e6a4a2430811c634acc30811c62a12430811c63452430811c62890c207a1c6
|5=>0x2890c20471852890c204718a24308130718a
|_=>0
def sO:Nat→Nat→Nat
|5,0=>6
|6,0=>0xddc3070a5c22706dc147035c067
|7,0=>0x4ba127747e1178441d0974060f983c60e9838d8dd63560cd83160bd82d60ad829609d825608d821607d81d606d8199c5e815a04e811a03e8
|8,0=>0x24898fe63878be6287882218884220888021f887c21e8877e5d7873e1c786fe1b696bdda6967a1959639d8685fa17775ba567757e157853a54774fa5368
|9,0=>0xa2628189e627189a626189662518
|10,0=>0x2917
|_,_=>0
def wAt:=mkWire dB 60 248 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1c649190ef5f1a1c9560b1da4a19126c91824646251cf4636289691929f47252464a251c641992460919126c9182464a251da4a1934c8a25346ca2534c041f2464719107c9192a04919807441f24647252869c191cd960b1da4a192464265289960b28c46251c653252868a251894719
|1=>0x2464a9b1890919246091929f472528946267c6472528947291994a261c64725246471a272491a18d4a251cd8a255c647261f2491a107c9192894719066491828647251c9872928687250a649184c98a1a24c8719246c91a28946250994a267c68725297472610ac6252a6462428c4719
|2=>0x28747191c94919246091a1c9871a2868726
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x3000000000000
|7,0=>0x3b30000003833533413132e32b32832532230000002021e21d11b21831621331120000f20c3093000072052000032
|8,0=>0x8027f17d27c17a27827627427227026e26c26a26826626426226025e25c25a25825625425225024e24c24a24824624424224023e2
|9,0=>0x891881871861851841831821
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x14284fb112844010603eb0bac242090423e080c1fb07ac1c106bc1ab03fc0fb02ac0a1020007001680500138028003800a00200020004000
|1=>0x97ae1eb546141847fd1bb43ecdeb23ec7eb1bec5fb17ac5ab
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x5000000
|7,0=>0x100004e0cb30494e2880020880d50977000c6480087002
|8,0=>0x1f1e0614a626694e48a2aa742284998945db616a1aec7a86e15a4
|9,0=>0x3e34e28a241e
|10,0=>0xd
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 14 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_246 9 roots_246 ops++addP pm 1 dom_183 8 roots_183 ops++addP pm 2 dom_151 6 roots_151 ops++addP pm 3 dom_215 8 roots_215 ops++addP pm 4 dom_87 6 roots_87 ops++addP pm 5 dom_245 9 roots_245 ops++addP pm 6 dom_167 6 roots_167 ops++addP pm 7 dom_243 9 roots_243 ops++addP pm 8 dom_231 7 roots_231 ops++addP pm 9 dom_55 5 roots_55 ops++addP pm 10 dom_119 7 roots_119 ops++addP pm 11 dom_230 6 roots_230 ops++addP pm 12 dom_199 5 roots_199 ops++addP pm 13 dom_229 6 roots_229 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_247 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_229 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_246 9 s (0,roots_246.map (·&&&dom_246)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_247 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_246 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_247==dom_247)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_247 gM v ys):RunD true dom_247 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_247 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 32 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 35 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 8 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_247 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_186_64:=0x505050505050505000000000000000005050505050505050000000000000000
def gzo_186_64:=0x505050505050504000000000000000005050504050504040000000000000000
def gsh_186_64:=0x50505050505050400000000000000000505050405050404
theorem lowS_zo_186_64_168:Lower true dzo_186_64 roots_186 gzo_186_64 6:=lower_iso_b (d1:=dom_186) (r1:=roots_186) (T1:=gsh_186_64) [(dom_186,64)] (by decide +kernel) (lower_slice_b (T:=gsh_186_64) [(0x40404040404040400000000000000000404040404040404,0,2),(0x50500000505000000000000000000000505000005050000,0,16)] (by decide +kernel) lowS_168)
def dzo_185_64:=0x303030303030303000000000000000003030303030303030000000000000000
def gzo_185_64:=0x303030303030302000000000000000003030302030302020000000000000000
def gsh_185_64:=0x30303030303030200000000000000000303030203030202
theorem lowS_zo_185_64_168:Lower true dzo_185_64 roots_185 gzo_185_64 6:=lower_iso_b (d1:=dom_185) (r1:=roots_185) (T1:=gsh_185_64) [(dom_185,64)] (by decide +kernel) (lower_slice_b (T:=gsh_185_64) [(0x20202020202020200000000000000000202020202020202,0,1),(0x30300000303000000000000000000000303000003030000,0,16)] (by decide +kernel) lowS_168)
def dzo_171_64:=0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000
def gzo_171_64:=0xf0f00000f0e000000000000000000000f0e00000e0e0000000000000000
def gsh_171_64:=0xf0f00000f0e000000000000000000000f0e00000e0e
theorem lowS_zo_171_64_168:Lower true dzo_171_64 roots_171 gzo_171_64 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_64) [(dom_171,64)] (by decide +kernel) (lower_slice_b (T:=gsh_171_64) [(0xa0a00000a0a000000000000000000000a0a00000a0a,0,1),(0xc0c00000c0c000000000000000000000c0c00000c0c,0,2)] (by decide +kernel) lowS_168)
def dzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def gzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000e0a0000
def gsh_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000e0a
theorem lowS_zo_235_16_42:Lower true dzo_235_16 roots_235 gzo_235_16 7:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_16) [(dom_235,16)] (by decide +kernel) (lower_slice_b (T:=gsh_235_16) [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000,0,64),(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_187_64:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000
def gzo_187_64:=0xf0f0f0f0f0f0f0e00000000000000000f0f0f0e0f0f0e0e0000000000000000
def gsh_187_64:=0xf0f0f0f0f0f0f0e00000000000000000f0f0f0e0f0f0e0e
theorem lowS_zo_187_64_168:Lower true dzo_187_64 roots_187 gzo_187_64 7:=lower_iso_b (d1:=dom_187) (r1:=roots_187) (T1:=gsh_187_64) [(dom_187,64)] (by decide +kernel) (lower_slice_b (T:=gsh_187_64) [(0xa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a,0,1),(0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c,0,2),(0xf0f00000f0f000000000000000000000f0f00000f0f0000,0,16)] (by decide +kernel) lowS_168)
def dzo_184_64:=0x101010101010101000000000000000001010101010101010000000000000000
def gzo_184_64:=0x101010101010100000000000000000001010100010100000000000000000000
def gsh_184_64:=0x10101010101010000000000000000000101010001010000
theorem lowS_zo_184_64_168:Lower true dzo_184_64 roots_184 gzo_184_64 5:=lower_iso_b (d1:=dom_184) (r1:=roots_184) (T1:=gsh_184_64) [(dom_184,64)] (by decide +kernel) (lower_slice_b (T:=gsh_184_64) [(0x10100000101000000000000000000000101000001010000,0,16)] (by decide +kernel) lowS_168)
def dzo_107_16:=0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16:=0xf0f00000f0f00000f0e00000e0a0000
def gsh_107_16:=0xf0f00000f0f00000f0e00000e0a
theorem lowS_zo_107_16_42:Lower true dzo_107_16 roots_107 gzo_107_16 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_16) [(dom_107,16)] (by decide +kernel) (lower_slice_b (T:=gsh_107_16) [(0xa0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_234_16:=0x505000005050000050500000505000005050000050500000505000005050000
def gzo_234_16:=0x505000005050000050500000505000005050000050500000504000004000000
def gsh_234_16:=0x50500000505000005050000050500000505000005050000050400000400
theorem lowS_zo_234_16_42:Lower true dzo_234_16 roots_234 gzo_234_16 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_16) [(dom_234,16)] (by decide +kernel) (lower_slice_b (T:=gsh_234_16) [(0x50500000505000000000000000000000505000005050000000000000000,0,64),(0x50500000505000005050000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,10),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,10),(8,40),(8,136),(16,17),(16,80),(16,144),(18,19),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,160),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,66),(64,80),(72,73),(72,74),(72,88),(72,104),(72,200),(96,97),(96,98),(96,104),(96,112),(96,224),(128,129),(128,130),(128,136),(128,144),(128,160),(192,193),(192,194),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|5=>11
|6=>97
|7=>173
|8=>123
|9=>51
|10=>8
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xbaee1a99979e43b8ff1f81f6152fef3b2f41e84e10cc60cdb7083fb
|6,0=>0xf711be898fe3023e1b4ce1431d85e0d64b6c6f75bff52b9a10b531ab2c72adfb2ad0a1a7f79a732ba56e7a35bda26038e0ac8df7389bb08591f82e4c823fd7caec7b6c479bd2799cd78ddd73e0172d8e6ffb16fad86e8716e4626b53669acf68e3468b6e652096343661e595ed405ed205db395bb8a5afba59fa05961c581cd56944562e85314452f854f4eb4ec274cf974ad2b4a54648a56477a6455bf451493e7813e0763d4fa393003669e35e5e3333b308cd2efde2dce7280022659b2452923a4c1e42c1d123196d1194c0177ad1656b1621414c011414d1325f115c4115a9106160e4700ddfb0b88207bf30651a025bd
|7,0=>0x8d07687a4e879c48588482c5e8288e820e28190580b347e0dc7d8917d4097cd0e7b2867af6d76bd2754b57412a7148e70cbf6e9bd6cf566c87c6add768b1168367667a965875630146213761eed5f0115dede5c9eb5bece5b1145a5b75a17d58acf586c45849456f88551fe544fb5412052d5851c5251a14514cf4f2474ed734da374c3ee4c3d349783493754929a4703845f0a440ae41e4e3f3d33f3c73d2ef3828b37c8b3521633dd531f452ff962f0b72cb592c94b2b4582aee42ae6029b0c2926e2847e26ed3264dd2601924d7222b8d22a732257d213122112620d211f4b01e00e1db3e1cc651c9761b3b519b2c1808817ecc17cae16ebe144281439a1325f12ea71280a11cd4115f7110f6104d01007a0fcce0fc630df500d3e70cdc40bb5d0a5dc09a3307ef307e2f06aa4066f8028a8024f5011c600c1f007dc003cb
|7,1=>0xf9f02f6d4cf14aaee5aaee147eb1eae9783e8159e2887dbf9ed9753d9238d44c2d316bd1a35cf2d6cb5a0ca704c8ed6c4df6c49dac3aeac35e8bf1edbc46cb9d2cb84d1b315eaf68cae713ab89ba928ca5721a3ea0a3998a212e9cc839b3fa9aed09a0e299b4a96bc796a40967ba92a54
|8,0=>0xfe13ffa017ed0bfdbb63d15e4ca1e3c8e30c4b10c05f3bf5eebc72fb8233b7b38b5830b532bb3fd5b1464af9bfabae9aa217a5c01a579e9cd179b0ae9939b94dc89261f8fa9788f698867787c01863ac80d347e84a7cc787c35f7be7778580783a27517e7491572d8b700406f5fe6ccb06adc06a9646a7806a49867a7c679836777566b5165d0e640986374062ef260fe95fb9c5d89d5bb4b561df558dc54eee5308b5284d5025e4f9664f1c4408e33e14d3d9523c1ab386b9382b437806376f435882357d0335153209d312512fdd22fb6b2f57a2ebe62e36b2d55f2cf932cbcc2a91d26014252ae245ad22b862210921f4d21680214391fbcc1e20e1b8101b1351a34519382178db13ebe134d012f45129741245311d941107f101880f2ec0ac0509b7f071df063ca05127040a6040190201d
|9,0=>0xfc1abf0a9ee8f3ce4868d4598d08b8c8954c3432c11d6bf69bb9674b7668b61feb5c01b33aaa7ada9d1df97a1e8e7548d67789763883548071f7877c74084705fa6ca956a995638125c4c35b41852705509f24d79e4985e3fa133cbc137255347c729d8f27ecc257701c20b19d7d19a0c175210ea4905c1003c5a0385d02ce3
|10,0=>0xaeeae840fe77ec86c0fe548364acc83ecf23e1f9
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ec0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0ef0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0ea0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e00f000f000e000e000f000f000e000e000f000f000e000e000f000f000e000ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000
|0,1=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0af0f0f0f000000000f0f0f0f000000000f0f0f0f0f0e0f0e0f0f0f0f0f0e0f0ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0ef000f000f000f000f000f000f000f000f000f000e000e000f000f000e000e0000000000000000000000000000000000f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0ef000f000f0f0f0f0f000f000f0f0f0f0f000f000f0e0f0e0f000f000f0e0f0e00000000000000000000000000000000f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f000f0000000000f0a0f0a000000000f0a0f0a000000000f0a0f0a000000000f0a0f0a00000000f0f0f0f000000000f0f0f0f000000000e0e0e0e000000000e0e0e0ef0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00
|0,2=>0xf0f0f0f000000000f0f0f0f000000000f0e0f0e000000000f0e0f0e0000000000f000f00000000000f000f00000000000e000e00000000000e000ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0e0f0e000000000f0e0f0e00f000f000f000f000f000f000f000f000f000f00000000000f000f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a00000000000000000000000000000000f0f0f0f0f0e0f0e0f0f0f0f0f0e0f0e00000000000000000000000000000000f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0f0e0f0e0f0f0f0f0f0e0f0e0f0f0f0f0f0e0f0e0f0f0f0f0f0e0f0ee0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0f0f0f0f0f0e0f0e0f0f0f0f0f0e0f0ef0f0f0f000000000f0f0f0f000000000f0e0f0e000000000f0e0f0e0000000000f000f000f000f000f000f000f000f000e000e000e000e000e000e000e000e00000000f0f0f0f000000000f0f0f0f000000000f000f00000000000f000f0000000000f0e0f0e000000000f0e0f0e000000000f0e0f0e000000000f0e0f0e00000000000000000000000000000000f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e00f000f000f000f000f000f000f000f000f000f000e000e000f000f000e000e
|0,3=>0x101010101010101010101010101010101010101000000000101010100000000b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0a0a0a0a0b0b0b0b0a0a0a0a00f000f000a000a000f000f000a000a000f000f000a000a000f000f000a000a00000000000000000000000000000000f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af000f000f000f000f000f000f000f000f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0e0f0f0f0f0f0e0f0ef0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f000000f000f000f0000000f000f000f0000000f000f000f0000000f000f000f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0a0f0a000000000f0a0f0a0000000000000000000000000000000000000000f0a0f0a000000000f0a0f0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0aa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0000000000000000000000000000000000f000f000e000e000f000f000e000e0000000000000000000000000000000000000000f0e0f0e000000000f0e0f0e0000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000a0a00000a0a
|0,4=>0xf000f000f0000000f000f000f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f0f0f0f0f0000000000f0f0f0f000000000f0f0f0f000000000f0a0f0a000000000f0a0f0a0000000000000000000000000000000000f000f000a000a000f000f000a000af0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f00000f0f000f0f0f0000f0f00000f0f00000f0f00000f0f00000f0f0f0f0f0f0f000f0f0f0f0f0f0f0000f000f000f000f000f000f000f000f000f000f000a000a000f000f000a000af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0e0e0e0e0f0e0f0e0e0e0e101010101000100010101010100010001010101010001000101010101000100b0b0b0b0b0a0b0a0b0b0b0b0b0a0b0a0b0b0b0b0b0a0b0a0b0b0b0b0b0a0b0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f00303030303030303030303030303030303030303030303030303030303000300a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0a0a0a0a0f0a0f0a0a0a0af0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f0000000000000000000000000000000000f0f0f0f0f0f0f000f0f0f0f0f0f0f00
|0,5=>0xf0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f000000000000f0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f00f0f0f0f0f0f0f0f00000f0f00000f000f0f0f0f0f0f0f0f00000f0f00000f000000000000f000f00000000000f000f00000000000f000000000000000f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f000f0f0f0000000000f0f0f0f000000000f0f0f0f000000000f0f0f00000000000f0f0f0000000000f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f000f000f000f0f0f000000f0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0000000f0000000000f0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f00f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f00000000000f0f0f0000f000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000
|0,6=>0x505050505000500050505050500050005050505050005000505050505000500f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f000050505050505050505050505050505050505050500000000050505050000000000000000000000000000000000000000f0f0f000f0f0f000f0f0f000f0f0f00
|_,_=>0
def sP:Nat→Nat
|0=>0x1610f901e28f121610a8f1474284203c60a1a709042a3c504203ca1314442842008301001421a043c3001a202190c28892086080f1444b12081c10a1a5c2071828b08081c60a24103952628492081c78008547942628692081c1001a202071800584060808a12202070c002840608080
|1=>0x782842a0878a1a2c2071e30512085480f2629105080ca8f14342840e3c6000a1038f1890505081ca862628284063d00a22142151e3118a12482071e288a20a10f901e2868b08847861434904423c51112142071e18005085410f2828d85080ca8f142c210041808a0a10786402889e
|2=>0xe3c511101420720300120a103950428f05084010f00582840e0830a501421504185270a1080f0c009040e4098a221130f0c945111a5c2101e3050816110900c2868808541061424904203c012161080f4a28284203c6230058404203c60a4448284203c0080a1039518282842008794
|3=>0x1420210041960a5014210041801e44142151e28685080c10f0014203043d20a3c344040e288890a1080f5600688084010600344040e180113c2c2151e2950508407860034e042a3c51216103951e2828406087a50034404523c5112c48210043c5281610a8f0c28b12081c78a2234e04
|4=>0x81c30a22a02842a3c60a0a1018f0200885080c1011444688088430a22791050840780241080f62288a20a1080f00242901c19800084010f0cbc005080c7ae1444492080c7001a482191e288880a101950428584203c61314482101eb45111a2c203043c5120a10390040040b087c80f
|5=>0x203c30a2234e12080c70a22142151e1928a2234404200830a22d1105084078a102c2072a185161010386144598508407802e14207203050d241038f0044692081c10a22a0284203c6000a103820c9400d101038c1445505084078c142c2841e3100a161018f0228885084078c6428488
|6=>0x142101ed45112414207203c0111a142191e185111614207200830a241420720085110a1080f0cb4511101080f0cb051150142101e180113c142101c300280a108020c2889e1a202101e288921610f83203851216108021e28685080c10f1444405087c80f144468808407860044226
|7=>0x1e1978a221421f2a4010f1478584203c51166142101c18016241080f144469c084078a226c2842a4078614344040e1851112482031c288880a101951e288a8161080f0c2889e0a1080f00442841e1900a2278584203860a0a10190043c005081c7864a28896241080e1828485080c706
|8=>0x63860a0a1018f48288ba0a1080f0c288a81a142031e2889e44142101e2888570407066e00284203c320144422620087861444b85081c8061445105084078a223428406386000a1080f6c288850840786622889b08407862628885080c70c482890b085480f1479105084070c1410802
|9=>0x1c18509101080f0c2889c2414215203c5121610f901c28f1c0a1080f144440b080c80f14442842a087864a28284203df0a2210a901e1978a2214210043de8a2234584063c511361420720185116888284203830a76142101e2888d241148e1445a120a1080f1444685080c7802234584
|10=>0x681421f203c5110a10395041851d0a1080f0c288a20a10f901c18505084070c7a00b12080c70a22103a6203c30a230028420383001a702031c288920a110901e2888d0a10a821e185050884a901e3051e1610f901c1851e242c2151c185040e407865e2889b0a108021e1800d3848215
|11=>0x2c142101e305220a101951c1850b0a103901e3050b08407bd1444284201a18022142151e1918a22a0284203c60a22142101f085110a108021e192800a1080f7a0088b084070c7a28405084032514442840e083251444d85083c3201444284063c08a2234404203c60a2248584065470a
|12=>0x2c202101e185116878284203c5110a108020c8c5110a1080f8a2888d1610a8f0c29a05084078a22cc284203c51110142072a185110a101901e4c5110a10390041800d161038f0c288a224142101c180090a1018f14446bc084078a223428420087860014210043c324145c284203c60a
|13=>0x84072b0c00284203e48a22785842a3830a1a6c2101e18511101420720180113c482842a3860a1a702151c18505086080f0c288890b202101c1801c0a10a901e2840508a480f1444692081c78a22205842a4078615042b820383000a1080f0cb85110a1080f0c8c0110a108471e18511
|14=>0x14791050840706006c284343c30a228828420383003c48284203c0110a10a901e1898a1a142101eac0111a1421f063c5113c4828420386003c142032a3c5112414219203c5110a103951e3051e0a101951c3050b0a10190043c51e44142151c1854a0a1080e0c00f120a10a8f1444485
|15=>0x2214203043d28a22202840e4060a225828420087861478284200878a2234284203c6000a1080f18905270a1080f0c288c11610a8e0c2868520383300044485084078600142101e3118a2288905084078a223490406380110a1018f4a28885081c80f1800685085478c1488905084070c
|16=>0x80c80e0c0088508407bd14442842a3831414442840e401061445405081c80f0c2888d0a10a8f0c288a224142101c18511241420320380111a14210043c30a227890b08407061444685085470c0c2868b08547061434e12084070614442cb08407061444284200878600a8284203c30a
|17=>0xd3c5110a1080e181920a8215c101c185113620284203c30a2270585084078a22342840e3c30a2338284203830a22142101c1a68a22142101e19f8a22785840640706144449208407061444405085480f0c288850840706982888b0a1080f18282840e40786004490b080c80e1444f05
|18=>0x462888508407066e0089e1a142101e2888d0a10f8e0c28885084070628008b438142101c185111a142101e180110a114901e2889e0a10a8e0c28888161080f0c28885084078648288850840706a2288a81a142101e185111a482101c30511721480e0d405111a142101c303000a1080e
|19=>0x2a407061458904203830a22342b808407060078905084070c144428442407861444284203d5802234904203c511101420720185113c142101c1801194142101c18511161080e0cdc51138142101e288850840706b02889c241420320385110a12b101c185110a1080e0d508850840786
|20=>0x203c51176142101c1851116169042a3830a0a1080f0c4c5110a103901e305110ae080e0d4c5116848284203830a223428406383002248284524070a22142031c1920a2279105084070614442843e0c80f1444585080c80e182848508407060088284203830a22142101c19b0a2248584
|21=>0x80c80e144428420386141444692080c70a2234284203c60a2270905085480e0c28284203c6003c70284203830a22e42b820383000a1080e0d705113c48284203c5110a11090043c30a23042842a3830a2224284203c30a22142101c1ad002234584063830a221480e0cc00111614203
|22=>0xa1080e0c288920a1080e1800585085480f0c28284065478a225c284203c30a2258284203c30a2235e04203830a22142032a3860a2c142101c3030a3c142101c305110a1080e84185111614210043c30a2414210043c51182142101c180110a11095203c30a2214210043c3131444e05
|23=>0xc01080e0c2889e0a1080e0c288850840706be28892161080e0c2888508407868c2888d0a1080e56180111a1640420383002310284203830022702842a4070614142101c1ae913c142101e288920a103901e288a80a1080f0c288920a1080f0045a1e0a1080e0c288b40a1080e0c288b3
|24=>0x1c3030a24142101c305110a1080e0cf451182142101c18511c42c284203830a222c2842a407061458284203830a22142101c1ab8a22142101c1b08a227090508407061444585a41080e0c2888d0a1018e0c28885087ca901c185110a1080f18288b90ae080e0c28885080c80e0c00885
|25=>0x1c185110a108021e185111a142151c185110a1080e0d4c5110a1080e561801172142101c180110a1080e0d785110b202101c1801138142101c1851124142101e2889e1a142101c185110b482151c185110a114901c18511b6142101c1801116142101e18511c4142101c185111614210
|26=>0x144448508407061444685701080e0c28885701080e0c0068508407861445c85a4407061444284203836314442840e407861444284203c300223428420386061444905080c80e144428420386060034284203830023046850840706144428420383241444f120a1080e0c2888b0a10190
|27=>0x142101c1851124142101c185110ae02101c185110a1080f0c2888d0a1080e0c28885084070c0c28885084070600442842a407061445c850840706
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x3c60366030602a6024601e60186012600c600660006
|6,0=>0x1f871f171ea71e371dc71d571ce71c771c071ba61b371ad61a6719f71987191718a7183717c7175716e7167716071597152714b7144713d7136712f71296122711b7114710d710670ff70f870f170ea70e370dc70d570ce70c770c070b970b270ab70a4709d7096708f70887081707a7073706c7065705e70577050704970427
|6,1=>0x2dc72d572ce72c862c172ba72b372ac72a5729e7297729072897282727b7274726d7266725f72587251724b6244723d7236723062297222721b7214720d720671ff7
|7,0=>0x4bf84b784b074a884a084997492748a8483747c7475746d8465845d8456744e8446843e843774307429742184198412740b740383fb83f383ec73e573de73d773cf83c873c173b983b183aa73a3739c7395738d8386737f737873708368836083588350834883408339733183298321831a7312830a830282fb72f382eb82e38
|7,1=>0x6a7769f86987690868886808678867086688661765a7653764c7644863c8635762d8625861e7617760f8607860075f975f185e985e275db75d385cb85c475bc85b575ae75a6859e8596858f758785807578857175698561855a7553754b8544753d7535852d8525851d8515850d850584fd84f584ed84e674de84d684ce84c77
|7,2=>0x7ff87f787ef87e787df87d877d177c987c277ba87b377ab87a3879c7795778e7787777f8777876f876877608758875087488740873887308729772187198711870a770286fa86f376ec76e486dc86d486cd76c586bd86b676ae8
|8,0=>0xa0389fb89f389eb89e299da89d379cc79c489bc89b489ac89a5799d8994998c8985797d8975896d8965895d8954994c8945793d8935892d8925891c9914890c890488fc88f488ec88e398db88d388cb88c388bb88b298aa88a198998892788a888288799872786a886288599851884898408837982e9826881f7816980e88077
|8,1=>0xbd98bd09bc79bbf8bb78bb07ba97ba18b998b927b899b818b798b727b6a8b637b5b8b538b4b8b447b3c8b348b2c8b248b1c8b148b0b9b029afa8af28aeb7ae38ada9ad46acb9ac47abc8ab48aab9aa38a9b8a938a8b8a847a7c8a748a6c8a648a5c8a548a4b9a438a3b8a338a2a9a228a1a8a137a0b8
|9,0=>0xd768d6d9d667d5e8d568d4e8d468d3f7d369d2e8d277d1f8d169d0e8d059cfc9cf48cec8ce48cdc8cd48ccc8cc48cbc8cb57cac9ca48c9c8c948c8c8c848c7c8c748c6c8c648c5b9c538c4b8c438c3b8c329c299c218c189c117c098c018bf98bf18be98be18
|10,0=>0xdb48dac8da57d9d8d958d8e7d868d7e8
|11,0=>0xdbc7
|_,_=>0
def wAt:=mkWire dB 100 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1c191a470a410a190a19200a1a4520151c1920490a191c1914450a41203d0c451c190a5620450a1e203d1a470a410e45203d1c1920091e451c1914451a471e451c1906170a091e451c190a0d1c19064520191c19204524410a191c19204524450a191445206c0a091e451c190a5520451a4520151c1914450c450a3d203d1c19
|1=>0x1a190a410a3d203d1c191c191a470a410c0114451c1914450a3d203d1c191c190a451a190a412045504714450a4116191c1920450a451c1914451e451c1906470a3d1c192a1520451a3d20151c191a450a411c1914450c450a3d203d1c19203d0a191e451c191a190a411a450a411a3d0a411c1914450e45203d1c191c191445
|2=>0x20192a191c19204520150a3d14451c190a8420091e451c19201924450a410a1942432a3d1c1920451c191c191a4520150a41203d14451c191c190c4514451a3d0a411c190c450a3d203d1c191a3d0a411c1920091e451c190a862009144520191a470a410a191c191c191c191c190a1d203d1c193c470a4114451c192a172045
|3=>0xa45201914451e451c1942430e45203d1c19202d0a450c450a1914451a47201520191c19160e20190a450a19203d14451c190e47203d1c191c190a19203d1e451c1946450a1e203d1c1916430a4514451a3d0a411c191a1914450a410c450a1d203d1c190a3d1a1920151c19064520190a450a190a451e451c191e451c192015
|4=>0x1c190a5620450c4520190a191c1920450a453c4724410a190a8620091c192a1920451e451c191c191a1920150a45144512191a470a410a191a4520151c1916190a4520151c19163d1c190a450a410a3d203d1c1920191a470a410a1920190a3d1c1920451a3d20151c1914451a190a411c19206e0a091e451c190c451a192015
|5=>0xa3d1c193c473c4524410a1920f11c1924470a190a410a19064720191c1914452015201920190a4520150c451c192a17201920451a3d0a413c471a190a411c197243081508451445206e0a091e450a8420091e451c1910470a3d1c193c471a190a411c19201914450a410c451c192845061720190e2f203d0a450a0a0a091e45
|6=>0xa1920091e451c190a411c191c190c45204506450a4506152019204524410a1942170e451c190a0914451e451c19204524450a191a4720151c1924450a19204520310a450c450a1920491c1924450a190a3d20191c190a45200a1e451c190cfd163f1c190a450a862a3d1c1920451e451c1924430a1920190a4520151c191045
|7=>0x1c1924431c190a191445204a0a450c450a19200a1e451c19200a1e451c19206e0a091e451c19201920220a3d1c1920150a3d0c451c1920190a1920450a451c192a1920452045203d1e451c1932150e47203d06453c4706152019244314450c450a191a450a192015201942140e451c1982471a110a411445201924450a410a19
|8=>0x20190a0a1e451c19203d14451e451c190a451c193c47144524411c191a472015201920151c1924470a190a4114451e451c192a1720450c4510470a3d1c190c451a450a411c193c47061520190c45203d1c190a451c190a4524430a19883b1a010a4114450a1e203d1c190c451a3d0a411c191c190cb1202e0a45200a14451e45
|9=>0xa190a3120450a410c45204d0a0a1e451c191a470a41144516191c1920450a450a3d1c1906472019203d1c190a410a191c19204514451a110a410845204e0a0a1e451c1914450a1e203d16430a451a4520151a190a411c190a1e203d1c190d191a3f0a411c190a411c190a4520453c451a190a411c191c1912191a470a411c19
|10=>0xa411c190c0114451c190645201520190c45144524410a191c192045061520190a190e47203d1c192045203d0c451c190a0d20450c45201920190a451e451c193c471a190a41144512111a470a411c19204524410a191a470a410c01144538431c1916190a450a451a190a412045163d0a451c1914450a3d203d1c1920452441
|11=>0x1c190a411c190c4514451c192a170c4520450a451a110a41204508ae0a410c01144514451c191a470a410c450a1e203d1c191c193c4724410a190a410a19201914452019200a1e451c19203d1c190c4514450c4520450a411c193c4724410a1914453c4724410a19206c3c470a0d201914451c19144524410a190a0a1e451c19
|12=>0x1c190a450a1920191445061520191c1924430a19204506172019203d1e451c190a1d203d1c1920450a411c193c4724410a190a19201914450a411e451c190a4524410a1920450a410c450a450a41204524450a410a1908b1202e0a4514451e451c1950471a3d0a41200a20191e451c190c450a3d203d1c191a450a411a190a41
|13=>0x1c190a452a171c192045a645a41708411a3d0a411c190a410c450a1908157043084514450a410c452ae60a1120452a170c4520451a110a41084510450a3d1c191c1916190a45203d0a411c191ae10a4108453e172a192045163f1c190a450a45061520191a470a410a190a3d1c1920452a4a0a1920451c190c450a45203d1445
|14=>0xa1920091e451c191c190c0114451c190a410a190a3d203d1c190a0d2019144512111a470a4120e608150a451c1916190a45b2170855204524450a192019215d70170845aa29085620450a1e203d1c191445724308151a190a411c190645201520190a0e2019144516190a4514450a411c191c19064720191a190a4120450a3d
|15=>0x2015201908ae0c01144520191c190a4520f124470a190a45084120450a0a1e451c19203d0c451c190845a41708413c4524410a191445201520190a19064720192a17201920453c4724410a191c19064520190a450c45201914451a470a413c4724410a192845061720190a1920450a451a450a410a190a410845144524410c45
|16=>0x24410c450a190cb1202e0a450a451e451c190a191e451c191a110a4114452a3d1c1920450a0a1e451c190a310c45201906170c4520190a19201520191c190a410c4524450a1920451c190c451445244524410a190815084514451ae20a4108451c1924410a1920091e451c191a110a4120451c191a470a41b6430a0114450a45
|17=>0xa190a451a3f0a411c190a410c0114450a41080114451a010a411445204516190a45bc291a130a411a190a411c190a19203d1c191a3d0a411c191c190a19144524410a191a310a410c4512191a470a4114450c450a191c190a45204520191c19204510470a3d1c191a450a411c1924470a410a1920450c4520191a450a410c45
|18=>0xa41708410c011445081514451a130a410801144516190a450a191c191a190a4108412045064720190a0114451c190a45082d0a450c450a450c450a1924430a1972410815082d0a450a4520450a55204570170845161b0a4524450a1920110a45201520192a1920450c451c190845081520191445a447084124410a19082e0a45
|19=>0xa1908451c190a410c451445204508151a470a410a410845084514450a411c19084108151a1b0a41203d1c1914451c190a410c4520190a190c4514450a4114451a110a410a56204524410a1920190a451e451c190a412045
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x2080000062000000000000051000a00000000000
|6,0=>0x218c428882310041ed43b287510e281b1435106550c82184c2f185c20b2615c82b0851509a812c8249046308a200000000000084610441e283a200000e08000037100000d481a0800000000bd4169000000000ac8149000004c608cc10901e30366000000001740268000007a0000000002940000000
|6,1=>0x15422a080000000148828c44f28000134800000000000000000004b980000000250c000000000000000491000011aa23044588000000022840000891
|7,0=>0x31286150c0a17e32f485d90b9200002dc85a90b3200002c845810ae215932aa8548ca7214a428c850cc9fa13b426e84d0c98992d42528495090a11d42346459089210e4216641d081a0ff41f683dd079a0ef41d6839d07218e311be836d06c90d541a28338c6520c7318682fd05e18b8416882c105620ab1
|7,1=>0x4d08998931225e44b6696492b925434a26935124a2454482890051e2238446c48ccd17a22b444e8894910a21d44346859109220e4416681d101a1ff43f687dd0fa19f133da87a50f2a1e143bc67690eb99d3439e872d0e419c4438086f10dd11b7336686c0cd699a9434c66908d0219c433086510c8998d4
|7,2=>0x30c36108c1118112ff35f68bdd00002f345de8bad173a2e345be8b6d16ba2d345a06b311658ac745868b00d5e22b845688ac115622a845488a8114e9a99452a8a45146a289450c6a0913f9a7b44ee89d0d38226c4
|8,0=>0x7966f20de29bc2377e6ef0ddc9bb637666ec0dd69baa374e6e90dd09b9e37366e60dca9b92371e6e30dc5138737086e04dbf1b7b36f06dd4db91b6f36d86da4db31b6336c06d74dad1b5736a86d44da71b4b36906d14da11b3f36786ce4d9b1b3336606cb4d951b2736486c84d8f1b1b36306c54d891b0f3
|8,1=>0x11ece3c1c7538e471bce361c6938cc718ce301c5e28b67160e2a9c52389e7130e249c4638867100e1e9c3a386e70d0e189c2e385670a0e129c22383e7070e0c9c1638267040e069c0a380e7010e009bfe37f66fe0dfa9bf237de6fb0df49be637c66f80dee9bda37ae6f50de89bce3
|9,0=>0x1388a7014de29b85368a6c14d629a85348a6814ce29985328a6414c629885308a6014be297852e8a5c14b6296852c8a5814ae295852a8a5414a629485288a50149e29385268a4c149629285248a48148e29185228a44148629085208a40147e2
|10,0=>0x9d633a86748ce819ce33986728ce41
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 15
def pmP:Nat→Nat
|0=>0x2010000000008020000000020000000000050000000000102c00000000408000000000c08000000003000000000008000000000015800000000045800000000110000000000428000000001080000000004000000000008100000000020000000000052000000000140000000000280000000000840000000001e0000000000640000000001800000000004800000000010000000000028000000000080000000000180000000000400000000000800000000000
|1=>0x802400000002008c000000080214000000200800000000500400000001080b0000000410a00000001040800000004000000000008100000000020068000000080100000000200200000000800600000002001000000008000000000015460000000045180000000114200000000450000000001046000000004100000000010000000000030200000000054e000000001518000000002420000000009000000000020480000000081000000000202800000000808
|2=>0x8844680000020511a000000807460000002019180000008044540000020101d0000006154e40000015043900000048042000000115139000000450640000001080000000004154e40000010451000000040c0800000010112b0000004040840000010091e00000040244800000100908000000402038000001008090000004020200000010020000000040050000000100110000000400120000000315380000000c14e00000002018400000008060000000020108
|3=>0xf444e4000003c5139000000f064ac000003c153b000000f044ec0000038153a000000d044e4000003211bd000000c454e40000031113f000000c444ec00000311139000000c264a80000030593b000000c154e40000030513f000000c144e40000030511a000000c064ec0000030153b000000c054e4000003011b9000000c044f40000030113b000000c044e40000030111b000000c04464000002d003e000000b204ec000002855390000009040e400000221199
|4=>0x1c040e40000060553b0000016500e40000058513a0000016144e4000005811390000014454f4000005111390000014154e4000005055290000014114840000050451800000141144000000504508000001410460000005020210000014054e400000500039000001400000000004445390000010444e80000041113900000102406c0000040513c0000010114a4000004045180000010114200000040410000000100140000000400100000000f454e4000003d113b
|5=>0x40c044e4000102410390000408044e4000100411390000302044040000370113d00000d80448400002301139000004c044e400000b0901a000002400478000008001020000020000500000080000a00000200001000000800002000001f444f4000007c5539000001f044fc0000074113d000001d040e40000071113d000001c154fc0000070553d000001c154ec00000705539000001c144f40000070153f000001c044fc0000070113d000001c044ec00000701139
|6=>0x2000064cc0008000053c00020000102000040b0113b0001004044cc0004010103b0000c48044e40002070113d0000814404f4000203151bb000080c544f40002030593f000080c044f40002030113b000080c044e4000201151b90000804444e4000201104390000804144e4000201000840000800644ac000200151390000800500e40002001103a0000800404f00002000513a00008000202400019341139000060d044e400012301139000044c044e40001070113d
|7=>0x281c044f4000a050113d000281404484000a0501029000280c044f4000a010103a0002804014f4000a0004405000240c044f40008050513d0002014044a800080414025000200cc54e400080311d3f000200c444fc0008031113d000200c144f400080301933000200c054f40008030113f000200c044f4000803011390002008c54ec000801315390002004c14e4000801305080002004544f4000801105080002004410a40008010553d0002000c146000080011529
|8=>0xc0005084b003000042128004020f044640080064003900200080000000400000000000902c2406c0024070133b00090140082c00240408218000880c045ec0022010084f00088000252000200800002000801c2406c0020031913b000800c264ac0020030913b00080006040800200008016000800020024001c080011000070000000400180000810000400c04444001001000000004000000600010000000800040000000800100000000000302c064cc000a070113f
|9=>0x2010083c1139440244c044e51008130113d400061d044f500018341139400041c044f500010301139400000c044e480008343119120020c044f4410083c1119086040d044e42180020010c0402c88044f41009230113d0400c8c044f410019341139040048c044e41001030113904002dd044e410003601139020020c044e40700034313b010000f244ec040003c892b010000f064ec03000343139
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40001000000002040000000
|6,0=>0x3c010040000038083000040000000000002200000180000000003a00058080400000080002000445203008245002040b02e390101008010c00404080907402110b800000003008181d0000400020007404000001c0200000dc020f0681860040200000140e0003400000880000
|7,0=>0x44ac578492a40d604108968d26032808432218a35162725879b6fa410284cbb1b064cc4c3d3380c058236964f81f9cc90102c3f46661700383e322320c67086eac070c9202d04a5b2505910041e9752c0f4e3d18d1a890b97d0612810b89d2f15212ca6f0b0483a17a41ea44822d914150c18a0e873ec2df88e370d468020911d601846044363b6f85566b232b918a02
|7,1=>0x48098203c24323202eb90927e1a2b4d140c6c71520a044f168823c554294a18cb4a08d091c16144be958202058e322c6c8705
|8,0=>0x28e3f2e9839e629e87460f8423c28102fb6a372008f6abf92eea771b64f1426ba0aca83b391005761ccd4f13932863af6991c0d72d36c417acc4d94d9a946b395566737be5fd374345648a48cab940d974afdc33392c3988a9681f87cad3925e02d25c45d32bd57add9ebd853ca22bf353b126985a9ade3237124cd8cd87c59b0912c93924d77fb99d521
|9,0=>0x2826b3651ca1450e3daa8e27f562e9a2a6779b5b0c2904a9812f799b1512b37ce9d939781dcd7289c3edff3475bce58a56a9d57e7e94a99eeed
|10,0=>0x35cd0d0a23a1e5a6c1
|11,0=>0x67
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 46 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_249 10 roots_249 ops++addP pm 1 dom_248 7 roots_248 ops++addP pm 2 dom_83 5 roots_83 ops++addP pm 3 dom_243 9 roots_243 ops++addP pm 4 dom_219 9 roots_219 ops++addP pm 5 dom_234 8 roots_234 ops++addP pm 6 dom_113 5 roots_113 ops++addP pm 7 dom_114 4 roots_114 ops++addP pm 8 dom_123 9 roots_123 ops++addP pm 9 dom_209 5 roots_209 ops++addP pm 10 dom_218 6 roots_218 ops++addP pm 11 dom_121 8 roots_121 ops++addP pm 12 dom_187 10 roots_187 ops++addP pm 13 dom_186 8 roots_186 ops++addP pm 14 dom_242 6 roots_242 ops++addP pm 15 dom_241 7 roots_241 ops++addP pm 16 dom_122 7 roots_122 ops++addP pm 17 dom_90 4 roots_90 ops++addP pm 18 dom_59 7 roots_59 ops++addP pm 19 dzo_186_64 6 roots_186 ops++addP pm 20 dom_250 9 roots_250 ops++addP pm 21 dom_235 9 roots_235 ops++addP pm 22 dom_211 6 roots_211 ops++addP pm 23 dom_217 7 roots_217 ops++addP pm 24 dom_203 6 roots_203 ops++addP pm 25 dom_227 6 roots_227 ops++addP pm 26 dzo_185_64 6 roots_185 ops++addP pm 27 dzo_171_64 6 roots_171 ops++addP pm 28 dzo_235_16 7 roots_235 ops++addP pm 29 dom_115 6 roots_115 ops++addP pm 30 dom_216 4 roots_216 ops++addP pm 31 dom_91 6 roots_91 ops++addP pm 32 dom_89 5 roots_89 ops++addP pm 33 dom_240 4 roots_240 ops++addP pm 34 dom_81 4 roots_81 ops++addP pm 35 dom_171 8 roots_171 ops++addP pm 36 dzo_187_64 7 roots_187 ops++addP pm 37 dom_42 4 roots_42 ops++addP pm 38 dzo_184_64 5 roots_184 ops++addP pm 39 dzo_171_16 6 roots_171 ops++addP pm 40 dzo_107_16 6 roots_107 ops++addP pm 41 dom_43 5 roots_43 ops++addP pm 42 dom_147 5 roots_147 ops++addP pm 43 dzo_234_16 6 roots_234 ops++addP pm 44 dom_107 6 roots_107 ops++addP pm 45 dom_155 7 roots_155 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_186_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_185_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_171_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_235_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_187_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_184_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_zo_171_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_107_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_zo_234_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_155 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_249 10 s (0,roots_249.map (·&&&dom_249)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_249 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 11 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 97 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 97 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 173 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 45 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 173 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 123 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 123 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 51 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 51 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_251 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_233_4:=0x303000003030000030300000303000003030000030300000303000003030
def gzo_233_4:=0x303000003030000030300000302000003030000030300000303000002000
def gsh_233_4:=0x30300000303000003030000030200000303000003030000030300000200
theorem lowS_zo_233_4_137:Lower true dzo_233_4 roots_233 gzo_233_4 6:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_4) [(dom_233,4)] (by decide +kernel) (lower_slice_b (T:=gsh_233_4) [(0x30300000000000003030000000000000303000000000000030300000000,0,32),(0x30300000303000000000000000000000303000003030000000000000000,0,64)] (by decide +kernel) lowS_137)
def dzo_244_8:=0x1100110011001100110011001100110011001100110011001100110011001100
def gzo_244_8:=0x1100110011001100110011001100110011001100110010001100110010000000
def gsh_244_8:=0x11001100110011001100110011001100110011001100100011001100100000
theorem lowS_zo_244_8_84:Lower true dzo_244_8 roots_244 gzo_244_8 6:=lower_iso_b (d1:=dom_244) (r1:=roots_244) (T1:=gsh_244_8) [(dom_244,8)] (by decide +kernel) (lower_slice_b (T:=gsh_244_8) [(0x11001100000000001100110000000000110011000000000011001100000000,0,32),(0x11001100110011001100110011001100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_116_8:=0x11001100110011001100110011001100
def gzo_116_8:=0x11001100110010001100110010000000
def gsh_116_8:=0x110011001100100011001100100000
theorem lowS_zo_116_8_84:Lower true dzo_116_8 roots_116 gzo_116_8 5:=lower_iso_b (d1:=dom_116) (r1:=roots_116) (T1:=gsh_116_8) [(dom_116,8)] (by decide +kernel) (lower_slice_b (T:=gsh_116_8) [(0x110011000000000011001100000000,0,32)] (by decide +kernel) lowS_84)
def dzo_249_4:=0x3030303030303030303030303030303030303030303030303030303030303030
def gzo_249_4:=0x3030303030303030303030303030302030303030303030303030303030302000
def gsh_249_4:=0x303030303030303030303030303030203030303030303030303030303030200
theorem lowS_zo_249_4_137:Lower true dzo_249_4 roots_249 gzo_249_4 7:=lower_iso_b (d1:=dom_249) (r1:=roots_249) (T1:=gsh_249_4) [(dom_249,4)] (by decide +kernel) (lower_slice_b (T:=gsh_249_4) [(0x303000003030000030300000303000003030000030300000303000003030000,0,16),(0x303030300000000030303030000000003030303000000000303030300000000,0,32),(0x303030303030303000000000000000003030303030303030000000000000000,0,64)] (by decide +kernel) lowS_137)
def dzo_189_64:=0x3333333333333333000000000000000033333333333333330000000000000000
def gzo_189_64:=0x3333333333333332000000000000000033333332333332320000000000000000
def gsh_189_64:=0x333333333333333200000000000000003333333233333232
theorem lowS_zo_189_64_168:Lower true dzo_189_64 roots_189 gzo_189_64 7:=lower_iso_b (d1:=dom_189) (r1:=roots_189) (T1:=gsh_189_64) [(dom_189,64)] (by decide +kernel) (lower_slice_b (T:=gsh_189_64) [(0x222222222222222200000000000000002222222222222222,0,1),(0x303030303030303000000000000000003030303030303030,0,4),(0x333300003333000000000000000000003333000033330000,0,16)] (by decide +kernel) lowS_168)
def dzo_185_4:=0x303030303030303000000000000000003030303030303030
def gzo_185_4:=0x303030303030302000000000000000003030303030302000
def gsh_185_4:=0x30303030303030200000000000000000303030303030200
theorem lowS_zo_185_4_137:Lower true dzo_185_4 roots_185 gzo_185_4 6:=lower_iso_b (d1:=dom_185) (r1:=roots_185) (T1:=gsh_185_4) [(dom_185,4)] (by decide +kernel) (lower_slice_b (T:=gsh_185_4) [(0x30300000303000000000000000000000303000003030000,0,16),(0x30303030000000000000000000000000303030300000000,0,32)] (by decide +kernel) lowS_137)
def dzo_117_8:=0x33003300330033003300330033003300
def gzo_117_8:=0x33003300330032003300330032002200
def gsh_117_8:=0x330033003300320033003300320022
theorem lowS_zo_117_8_84:Lower true dzo_117_8 roots_117 gzo_117_8 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_8) [(dom_117,8)] (by decide +kernel) (lower_slice_b (T:=gsh_117_8) [(0x220022002200220022002200220022,0,1),(0x330033000000000033003300000000,0,32)] (by decide +kernel) lowS_84)
def dzo_188_64:=0x1111111111111111000000000000000011111111111111110000000000000000
def gzo_188_64:=0x1111111111111110000000000000000011111110111110100000000000000000
def gsh_188_64:=0x111111111111111000000000000000001111111011111010
theorem lowS_zo_188_64_168:Lower true dzo_188_64 roots_188 gzo_188_64 6:=lower_iso_b (d1:=dom_188) (r1:=roots_188) (T1:=gsh_188_64) [(dom_188,64)] (by decide +kernel) (lower_slice_b (T:=gsh_188_64) [(0x101010101010101000000000000000001010101010101010,0,4),(0x111100001111000000000000000000001111000011110000,0,16)] (by decide +kernel) lowS_168)
namespace S_253
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(4,20),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,40),(8,136),(12,13),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(24,25),(24,28),(24,56),(24,88),(24,152),(32,33),(32,36),(32,40),(32,160),(48,49),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,80),(72,73),(72,76),(72,88),(72,104),(72,200),(96,97),(96,100),(96,104),(96,112),(96,224),(128,129),(128,136),(128,144),(128,160),(132,133),(132,140),(132,148),(132,164),(132,196),(192,193),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
def xsM:=roots_253.map (·&&&dom_253)
def gM:=goal_253&&&dom_253
def NN:Nat→Nat
|6=>1
|7=>3
|8=>15
|9=>55
|10=>10
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x2ae1a
|7,0=>0xf5216b56f262f89
|8,0=>0xed861ebca8dcfcac56e8bda04bb6dfae4098e40f7ee147c7f23758f2d385225831c94812616
|9,0=>0xfd857fab0cf8c91f6bfaf5ff2f0769ee25ce9fb3e80b0dcc75dca12d7506d5c2cd5839d26d1d1c10ce4e7cb64eca9edc86c8bf670b4c5a9ceee9b3f899fe998dd694f6b948088880387ee787b13798947882b6d0916609f6578e610fb5cd1f56aa453b734740f3ce3738f2c309182f56c2d25d2c6412bf48164c9134840af7606fe8061f5020b200776
|10,0=>0xdfc1bdebf9d74d6d4dbeacee47a07a7762c6ec8e4706326091
|11,0=>0x1e31b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc8b333333333333333333333333333333322222222222222222222222222222222cccccccccccccccccccccccccccccccccccccccccccccccc0000000000000003333333333333333323232323232323233333333333333333232323232323232ccccc8c8ccccc8c8ccccc8c8ccccc8c8ccccc8c8ccccc8c8ccccc8c8ccccc8cb333333333333333000000000000000033333333333333330000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c3333333333333333333333333333333333003300330033003300330033003300888888888888888888888888888888888888888888888888888888888888888b3333333000000003333333300000000333333330000000033333333000000000000000000000000ccccc8c8ccccc8c80000000000000000ccccc8c8ccccc8cb333000033330000333300003333000033330000333300003333000033330000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc032323232323232323232323232323232323232323232323232323232323232324444444444444444444444444444444444004400440044004400440044004403333333333333333333333333333333300000000000000000000000000000000
|0,1=>0xcccccccccccccccccc00cc00cc00cc00033003300330033003300330033003300330033003300330000000000000000cccccccccccccccccccccccccccccccccccc8888cccc8888cccc8888cccc888b33333333333333333333333333333333322332233223322332233223322332200000000000000000000000000000000cccccccccccccccc888888888888888800000000000000000000000000000003333330033333300333333003333330000000000000000000000000000000000cc88cc88cc88cc88cc88cc88cc88cc8b33333333333333333223322332233223333333333333333332233223322332200cc00cc00cc00cc00cc00cc00cc00cc00cc000000cc000000cc000000cc0001111111111111111111111111111111111110000111100001111000011110000cccccc88cccccc88cccccc88cccccc88cccccc88cccccc88cccccc88cccccc8b333330033333300333333003333330033333300333333003333330033333300cccccccccccccccccc00cc00cc00cc00cccccccccccccccccc00cc00cc00cc03333222233332222333322223333222233332222333322223333222233332222cccccccccccccccccccccccccccccccccccc0000cccc0000cccc0000cccc0003333333333333333222222222222222233333333333333332222222222222222
|0,2=>0x332200003322000033220000332200003322000033220000332200003322ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8cccb33333333333333333333333333333333333333333333333330033003300330044444400444444004444440044444400444444004444440044444400444444000000000000000003333333333333333000000000000000033003300330033000000000000000000cc88cc88cc88cc880000000000000000cc88cc88cc88cc8b33333333333333333333333333333333232323232323232323232323232323200cc00cc00cc00cc008800880088008800cc00cc00cc00cc00880088008800891111111111111111100110011001100111111111111111111001100110011000000cccc0000cccc0000cccc0000cccc0000cc000000cc000000cc000000cc033333333333333333333333333333333333333333333333322222222222222224444444444444444444444444444444444444444444444440000000000000003333333333333333333333333333333333333300333333003333330033333300
|_,_=>0
def sP:Nat→Nat
|0=>0x5120c22801840c204a00648420308a0061130c24001921080c938a19244308a0064910c938a19110f0c938a1843c824e2862c42030872801842030902801843c324e34a1851030870062c40c204a00610330204a0061442030870061440c2040
|1=>0xc91ca00610f0c91cd2801847032472801842032501ca00610325b1ca0066840c91ca00610f4c91ca0061190c91ca0061180c91ca0065043c91ca0061032475ca00610308734a00610324758a0065440c91ca0061080cc0872801840c240d006
|2=>0xc91ca0064840c938a00610324794a00610324790a0061032478ca0061032621ca0061032472a100681110324728019210308a0064440c21ca00611f0c91ca0061130c91cd00610324729e0064440c938728610f2091ca0065110c91ca006744
|3=>0x24728018b1030872801840c91e92801844c30872801840e82472801840c91c12801840c240a0061270c91ca0061039821ca0064842032472801844c32501c01a01032472801941030872801840cc08728019244324728019410824728019110f
|4=>0x3872801840c21ca0064840c91ca00610324734a0061080c91ca0061130c91ca0065040c91ca0061080c21ca00610f0c938a0061032501cd00610324e1cd2867511032472801840c91ec28018420324e1ca194483247280184ac3087280184a83
|5=>0x61032472801843c32472801840c94072801911032472801840c9
|_=>0
def sO:Nat→Nat→Nat
|6,0=>7
|7,0=>0x17803e0078
|8,0=>0x889205c7a71cdc6b8191c5c8155c4e711a03f70da42e809a01f7
|9,0=>0x24588f623588b62249872214883220487f21f487b21e487721d48735dc586f61b496b21a48672194863218485ee57385ae163856e153852e14294edd3384ae123846e113842e10383ee0f293aa0e193660d183260c182e60b182a60a182660918
|10,0=>0xa5228c8a1227c89d5e6d899625d895624d8
|11,0=>0x29c7
|_,_=>0
def wAt:=mkWire dB 45 254 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc7510f1004a01247511f100520d10742290c0491d2474729280440d107491d247481f0c04301107491d24747290ca441d0c04701100441d247470110744011c0431d10047010c743010c04409247491d1ca43010c74a011c04b2b102491d247481f0c0491d207c3012cac301102491d
|1=>0xc047290ca510d100440d2474229247441d100440d0c0431d100441d1c043421ca531f0ca44220c04e291c04736280510d100441d247440124753030ca4a010ca43362804701100431d0c0440d100511d100431d28043391c047290c050031ca5403103431d0ca4f030c7531d0ca440d
|2=>0x31d1ca44011c0491d1074a010c043291034301247431d1c047292804a011c0511d100443e0c743011c0440d107430924748290c04409247541f1034329247482b0c0481f0c047292474f2b0c74201247441d
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x73043004
|8,0=>0x3433132e32b32832532231f31c31931631331030d30a3
|9,0=>0xa32a129f29d29b29929729529329128f28d28b28928728528328127f27d27b27927727527327126f26d26b26926726526326125f25d25b25925725525325124f24d24b24924724524324123f23d23b2392372
|10,0=>0xae1ad1ac1ab1aa1a91a81a71a61a51
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x10869ec0042187b000c203c0003058fb0008210f80009fe7b0002679ec00099b3a0002379ec0008da7b000227dec00089a7b0002079ec00081a7b0001fe9ec00079a7b0001be9ec00069a7b0001869ec0003197b0000865ec0001787b0000461ec00009a7b0000161ec00001f7b0000079ec0000187b0000003000000003000000003800000000
|1=>0x840de1ec2003197b0800c61ec2002787b0800869ec2002197b0800861ec2000187b071007dcc14001f7b0500069ec10401e7b040227dec10079a7b0400079ec10001a7b0210869ec0840187b0110069ec04061a7b0100069ec02c8de7b00b0161ec02489e7b0090869ec0242187b0090061ec01c2587b00689e1ec00c25a7b0020161f400481e7b
|2=>0x20020587f6020b69ed80009a7b4100869ed00021a7b2710079ec8a42197b2230961ec8842197b2210061ec84401a7b10289e1ec34001f3a0d00079ec240e9a7b0903861ec24061a7b
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x4182
|8,0=>0x752112c691187efa20636a9ba1
|9,0=>0x5db1e90f989521144501d3d01452d11993f0879c7a2218c4f389ca8f0453c9b197ba0b01f4b66a132c56d56ab7725cb2
|10,0=>0x1825702c3895c4a60d
|11,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 34 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_249 10 roots_249 ops++addP pm 1 dom_173 8 roots_173 ops++addP pm 2 dom_233 8 roots_233 ops++addP pm 3 dom_237 9 roots_237 ops++addP pm 4 dom_245 9 roots_245 ops++addP pm 5 dom_252 9 roots_252 ops++addP pm 6 dom_189 9 roots_189 ops++addP pm 7 dom_185 8 roots_185 ops++addP pm 8 dom_124 7 roots_124 ops++addP pm 9 dzo_245_8 7 roots_245 ops++addP pm 10 dom_116 5 roots_116 ops++addP pm 11 dom_221 10 roots_221 ops++addP pm 12 dom_125 9 roots_125 ops++addP pm 13 dzo_233_4 6 roots_233 ops++addP pm 14 dom_248 7 roots_248 ops++addP pm 15 dzo_244_8 6 roots_244 ops++addP pm 16 dom_236 7 roots_236 ops++addP pm 17 dzo_116_8 5 roots_116 ops++addP pm 18 dom_229 6 roots_229 ops++addP pm 19 dom_117 6 roots_117 ops++addP pm 20 dom_184 5 roots_184 ops++addP pm 21 dzo_249_4 7 roots_249 ops++addP pm 22 dzo_189_64 7 roots_189 ops++addP pm 23 dzo_185_4 6 roots_185 ops++addP pm 24 dom_121 8 roots_121 ops++addP pm 25 dom_188 6 roots_188 ops++addP pm 26 dzo_117_8 6 roots_117 ops++addP pm 27 dom_61 6 roots_61 ops++addP pm 28 dom_244 6 roots_244 ops++addP pm 29 dom_109 6 roots_109 ops++addP pm 30 dom_241 7 roots_241 ops++addP pm 31 dzo_188_64 6 roots_188 ops++addP pm 32 dom_181 6 roots_181 ops++addP pm 33 dom_168 4 roots_168 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_245_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_233_4_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_244_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_116_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_249_4_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_189_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_185_4_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_117_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_188_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_168 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_249 10 s (0,roots_249.map (·&&&dom_249)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_249 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_253 gM v ys):RunD true dom_253 gM v (ori ys):=h
def Z (s:Nat):=barP dom_253 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 15 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 55 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 55 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 10 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_253 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_246_8:=0x5500550055005500550055005500550055005500550055005500550055005500
def gzo_246_8:=0x5500550055005500550055005500550055005500550054005500550054004400
def gsh_246_8:=0x55005500550055005500550055005500550055005500540055005500540044
theorem lowS_zo_246_8_84:Lower true dzo_246_8 roots_246 gzo_246_8 7:=lower_iso_b (d1:=dom_246) (r1:=roots_246) (T1:=gsh_246_8) [(dom_246,8)] (by decide +kernel) (lower_slice_b (T:=gsh_246_8) [(0x44004400440044004400440044004400440044004400440044004400440044,0,2),(0x55005500000000005500550000000000550055000000000055005500000000,0,32),(0x55005500550055005500550055005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_214_8:=0x55005500000000005500550000000000550055000000000055005500
def gzo_214_8:=0x55005500000000005500550000000000550054000000000054004400
def gsh_214_8:=0x550055000000000055005500000000005500540000000000540044
theorem lowS_zo_214_8_84:Lower true dzo_214_8 roots_214 gzo_214_8 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_8) [(dom_214,8)] (by decide +kernel) (lower_slice_b (T:=gsh_214_8) [(0x440044000000000044004400000000004400440000000000440044,0,2),(0x550055000000000055005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_218_4:=0x50505050000000005050505000000000505050500000000050505050
def gzo_218_4:=0x50505050000000005050504000000000505050500000000050504000
def gsh_218_4:=0x5050505000000000505050400000000050505050000000005050400
theorem lowS_zo_218_4_138:Lower true dzo_218_4 roots_218 gzo_218_4 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_4) [(dom_218,4)] (by decide +kernel) (lower_slice_b (T:=gsh_218_4) [(0x5050000000000000505000000000000050500000000000005050000,0,16),(0x5050505000000000000000000000000050505050000000000000000,0,64)] (by decide +kernel) lowS_138)
def dzo_250_4:=0x5050505050505050505050505050505050505050505050505050505050505050
def gzo_250_4:=0x5050505050505050505050505050504050505050505050505050505050504000
def gsh_250_4:=0x505050505050505050505050505050405050505050505050505050505050400
theorem lowS_zo_250_4_138:Lower true dzo_250_4 roots_250 gzo_250_4 7:=lower_iso_b (d1:=dom_250) (r1:=roots_250) (T1:=gsh_250_4) [(dom_250,4)] (by decide +kernel) (lower_slice_b (T:=gsh_250_4) [(0x505000005050000050500000505000005050000050500000505000005050000,0,16),(0x505050500000000050505050000000005050505000000000505050500000000,0,32),(0x505050505050505000000000000000005050505050505050000000000000000,0,64)] (by decide +kernel) lowS_138)
def dzo_86_8:=0x550055000000000055005500
def gzo_86_8:=0x550054000000000054004400
def gsh_86_8:=0x5500540000000000540044
theorem lowS_zo_86_8_84:Lower true dzo_86_8 roots_86 gzo_86_8 5:=lower_iso_b (d1:=dom_86) (r1:=roots_86) (T1:=gsh_86_8) [(dom_86,8)] (by decide +kernel) (lower_slice_b (T:=gsh_86_8) [(0x4400440000000000440044,0,2)] (by decide +kernel) lowS_84)
def dzo_190_64:=0x5555555555555555000000000000000055555555555555550000000000000000
def gzo_190_64:=0x5555555555555554000000000000000055555554555554540000000000000000
def gsh_190_64:=0x555555555555555400000000000000005555555455555454
theorem lowS_zo_190_64_168:Lower true dzo_190_64 roots_190 gzo_190_64 7:=lower_iso_b (d1:=dom_190) (r1:=roots_190) (T1:=gsh_190_64) [(dom_190,64)] (by decide +kernel) (lower_slice_b (T:=gsh_190_64) [(0x444444444444444400000000000000004444444444444444,0,2),(0x505050505050505000000000000000005050505050505050,0,4),(0x555500005555000000000000000000005555000055550000,0,16)] (by decide +kernel) lowS_168)
def dzo_238_16:=0x5555000055550000555500005555000055550000555500005555000055550000
def gzo_238_16:=0x5555000055550000555500005555000055550000555500005554000054500000
def gsh_238_16:=0x555500005555000055550000555500005555000055550000555400005450
theorem lowS_zo_238_16_42:Lower true dzo_238_16 roots_238 gzo_238_16 7:=lower_iso_b (d1:=dom_238) (r1:=roots_238) (T1:=gsh_238_16) [(dom_238,16)] (by decide +kernel) (lower_slice_b (T:=gsh_238_16) [(0x505000005050000050500000505000005050000050500000505000005050,0,4),(0x555500005555000000000000000000005555000055550000000000000000,0,64),(0x555500005555000055550000555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_110_16:=0x55550000555500005555000055550000
def gzo_110_16:=0x55550000555500005554000054500000
def gsh_110_16:=0x5555000055550000555400005450
theorem lowS_zo_110_16_42:Lower true dzo_110_16 roots_110 gzo_110_16 6:=lower_iso_b (d1:=dom_110) (r1:=roots_110) (T1:=gsh_110_16) [(dom_110,16)] (by decide +kernel) (lower_slice_b (T:=gsh_110_16) [(0x5050000050500000505000005050,0,4),(0x5555000055550000000000000000,0,64)] (by decide +kernel) lowS_42)
namespace S_254
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(2,130),(4,20),(4,36),(4,68),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,136),(12,14),(12,28),(12,44),(12,76),(12,140),(16,20),(16,80),(16,144),(18,22),(18,26),(18,50),(18,82),(18,146),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,36),(32,40),(32,160),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,68),(64,80),(72,74),(72,76),(72,88),(72,104),(72,200),(96,98),(96,100),(96,104),(96,112),(96,224),(128,130),(128,136),(128,144),(128,160),(132,134),(132,140),(132,148),(132,164),(132,196),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1fffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|7=>2
|8=>15
|9=>27
|10=>6
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x91b7354a1c
|8,0=>0xf9a24e93255eec7475d2365a3316452350221e231faa216e1d15d6a159920db45077a703b90
|9,0=>0xc4ede60eff56f0c54eb64c611489e83937a2dd962d0b624df720f5720ef4205401c12a188e1172e916d83138e812cc211bb8109bc0fd6c0ed650b30004cad04c9003069
|10,0=>0xba90f4ae32420a2371a01a4340a6d4
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x22222222222222222222222222222222222222222020202022222222202020215555555554015401555555555401540155555555540154015555555554015402a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a111111111111111111111111111111111111111111111111111111110000000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa008800895555555555555555555555555555555555555554000000015555555400000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000000000000000000000000000004444444444444444444444444444444444444444444444444444444444444444aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa000000015555555511111111555555551111111155555555111111115555555511111112aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000005555000055550000555500005555000055550000555500005555000055550000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa014141414141414141414141414141414141414141414141414141414141414142aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa22222222222222222222222222222225555555555555555000000000000000055555555555555550000000000000000
|0,1=>0xaaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a15555555555555555555555555555555555555555515151515555555551515152aaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaaaaaaaaaaaaaaaaaa800000000000000055555555000000005555555500000000550055000000000055005500aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa8955555555555555555555555555555555540154015401540154015401540154000000000000000000000000000000000000000002aaaaaaa80000000222222225555555555554444555555555555444455555555555544445555555555554444aaaaaaaaaaaaaaaa8888888888888888aaaaaaaaaaaaaaaa88888888888888880000000155555554000000011111111000000001555555540000000111111112aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000000000000001111111111111111111111111111111111110000111100001111000011110000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaa0000aaaa0000aaaa00015555555444444445555555544444444555555554444400015555555444440002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa82828282828282828282828282828285555555555555555555555555555555555555555505050505555555550505050
|0,2=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00aaaaaa00aaaaaa00aaaaaa000154015401540154015401540154015401540000015400000154000001540000888888888888888888008800880088008888888888888888880088008800880555555555555000055555555555500005555555555550000555555555555000000000000000000000000000000000000aaaaaaaaaaaaaaaaaa00aa00aa00aa015551555155515551555155515551555155515551555155515551555155515552aaaaaaaaaa22aa22aaaaaaaaaa22aa22aaaaaaaaaa22aa22aaaaaaaaaa22aa21111111110101010111111111010101011111111101010101111111110101010aaaaaaaaaaaaaaaaaa00aa00aa00aa00aaaaaaaaaaaaaaaaaa00aa00aa00aa000001555400015554000155540001555400015400000154000001540000015402aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa855554444555544445555444455554444555544445555444455554444555544440a080a080a080a080a080a080a080a080a080a080a080a080a080a080a080a080154015401540154015401540154015401540154011001100154015401100112aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa22222222aaaaaaaa22222225500550055005500550055005500550055005500440044005500550044004400
|0,3=>0x5555550055555500555555005555550055555500555555005555550055555500
|_,_=>0
def sP:Nat→Nat
|0=>0x888802471200880097871030880097440c221c0091c46da0810071030886402581d30c22002471030885952521c40c22002462840d10880062840c20401c40c220f0093861033420091c40c220c0091851030880091c40882c02461440c2040
|1=>0x20024712b0c220024e1c494220024712a0c22002691c40c2200247103088a0025d1c49c308824e1c46c220025d1c46830880091c40c22260093874c40c220024a1c468308801f1c49432002479046830880091c40c221c0091c40c22230091c4
|2=>0x24711a0c2200247c040c22002471033422002471030812002462840c22002451c40c2200247bc40c220025d1c40c221524a1c40c25c80098471030880091c40c222e00940710308800919d1030880091c40c222d009b071030812002479130c2
|3=>0x71030880091c40c220025f1c40c2200
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xee007
|8,0=>0x1edce8e6c8324175cab04d822c0f606b02e713407a02d00e8
|9,0=>0x55e29f14789fc4da65d12688f445a21d10597ec3d61db0e586ec35619b0c585e4ad21572a384dc24a5150828
|10,0=>0x30ef7f8bbc5be2cf15f8
|11,0=>0x18e7
|_,_=>0
def wAt:=mkWire dB 49 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x7446a0c949110c743251c94309087490d1085a1f0c95b0b0c8610f1c148258430705209417d1c248251da8325007480d0c9482529788011c9461124447211d78801009541d4c8c42524749091c84825247481d408ca091c948090c7481d148c0291c94a01247481d2804825247481d
|1=>0x8743250c44221209491d20740291c944690c9402500748011c94705209530f1094a091c9401d20767230c04711248491110867270c0420d0c7433508843192075f23087430100743210c74325
|_=>0
def oO:Nat→Nat→Nat
|7,0=>4
|8,0=>0xb8d59a834a688cf99c332658c999031a628c39843
|9,0=>0x194b19612be574ad9592ae554a995129e534a594928e514a194127e4f49d93926e4d4999312
|10,0=>0x6b1d43a4740e71
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x618076cc5002000764c50010007fc9500100076cd50010003f894000988766dd00082076455000700364dd000600245dd000400364d50002807ecb7000280765bf000200765b7000200364d70001c8e441d000188764dd000121f6415000108766dd000100766950000a076455000080241ff000020f645500001f96c11000008764f70000027ec85000002764d5000001764150000007fe950000007649500000016405000000001ff00000000000
|1=>0x80018076cc542611076c8540500077c854010007ecdd4010003ecf52000e0f641d200020764552000207641510011e76c9510002477c1509100277cc5088080766c506018076cd504000276cd7020022f6c1502000476c9501c008660c101410076485
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>1
|8,0=>0x60d96c45a15de44e28948b
|9,0=>0x105074d869fb089268258cfa6b562b6fc2e327768
|10,0=>0xaa73114d
|11,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 44 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_252 9 roots_252 ops++addP pm 1 dzo_188_64 6 roots_188 ops++addP pm 2 dom_190 9 roots_190 ops++addP pm 3 dom_94 7 roots_94 ops++addP pm 4 dom_186 8 roots_186 ops++addP pm 5 dom_158 7 roots_158 ops++addP pm 6 dzo_212_8 5 roots_212 ops++addP pm 7 dom_174 8 roots_174 ops++addP pm 8 dom_62 7 roots_62 ops++addP pm 9 dom_124 7 roots_124 ops++addP pm 10 dom_250 9 roots_250 ops++addP pm 11 dzo_246_8 7 roots_246 ops++addP pm 12 dom_116 5 roots_116 ops++addP pm 13 dom_238 9 roots_238 ops++addP pm 14 dom_222 9 roots_222 ops++addP pm 15 dzo_214_8 6 roots_214 ops++addP pm 16 dom_246 9 roots_246 ops++addP pm 17 dom_126 9 roots_126 ops++addP pm 18 dom_234 8 roots_234 ops++addP pm 19 dzo_218_4 6 roots_218 ops++addP pm 20 dom_248 7 roots_248 ops++addP pm 21 dzo_244_8 6 roots_244 ops++addP pm 22 dom_212 5 roots_212 ops++addP pm 23 dom_220 7 roots_220 ops++addP pm 24 dom_214 6 roots_214 ops++addP pm 25 dzo_250_4 7 roots_250 ops++addP pm 26 dom_122 7 roots_122 ops++addP pm 27 dzo_86_8 5 roots_86 ops++addP pm 28 dzo_116_8 5 roots_116 ops++addP pm 29 dzo_190_64 7 roots_190 ops++addP pm 30 dom_188 6 roots_188 ops++addP pm 31 dom_84 4 roots_84 ops++addP pm 32 dom_118 6 roots_118 ops++addP pm 33 dom_110 6 roots_110 ops++addP pm 34 dzo_238_16 7 roots_238 ops++addP pm 35 dom_206 7 roots_206 ops++addP pm 36 dom_236 7 roots_236 ops++addP pm 37 dzo_118_8 6 roots_118 ops++addP pm 38 dom_182 6 roots_182 ops++addP pm 39 dzo_110_16 6 roots_110 ops++addP pm 40 dom_244 6 roots_244 ops++addP pm 41 dom_218 6 roots_218 ops++addP pm 42 dom_86 5 roots_86 ops++addP pm 43 dom_230 6 roots_230 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_188_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_212_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_246_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_214_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_218_4_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_244_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_250_4_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_86_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_116_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_190_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_238_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_118_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_zo_110_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_230 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 9 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcccccccccccccccccccccccccccccccc,126)],[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccccccccccccccccccc,126)],[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 15 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 27 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 27 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 6 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 6 0 = true)
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
def dzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def gzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fe00ff00ff00fe00ee00
def gsh_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fe00ff00ff00fe00ee
theorem lowS_zo_247_8_84:Lower true dzo_247_8 roots_247 gzo_247_8 8:=lower_iso_b (d1:=dom_247) (r1:=roots_247) (T1:=gsh_247_8) [(dom_247,8)] (by decide +kernel) (lower_slice_b (T:=gsh_247_8) [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,0,1),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,0,2),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000,0,32),(0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00
def gzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00ee00
def gsh_215_8:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00ee
theorem lowS_zo_215_8_84:Lower true dzo_215_8 roots_215 gzo_215_8 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_8) [(dom_215,8)] (by decide +kernel) (lower_slice_b (T:=gsh_215_8) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,0,2),(0xff00ff0000000000ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_175_16:=0xffff0000ffff00000000000000000000ffff0000ffff0000
def gzo_175_16:=0xffff0000ffff00000000000000000000fffe0000fefa0000
def gsh_175_16:=0xffff0000ffff00000000000000000000fffe0000fefa
theorem lowS_zo_175_16_42:Lower true dzo_175_16 roots_175 gzo_175_16 7:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_16) [(dom_175,16)] (by decide +kernel) (lower_slice_b (T:=gsh_175_16) [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0,0,4),(0xffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_171_4:=0xf0f00000f0f000000000000000000000f0f00000f0f0
def gzo_171_4:=0xf0f00000f0e000000000000000000000f0f00000e000
def gsh_171_4:=0xf0f00000f0e000000000000000000000f0f00000e00
theorem lowS_zo_171_4_139:Lower true dzo_171_4 roots_171 gzo_171_4 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_4) [(dom_171,4)] (by decide +kernel) (lower_slice_b (T:=gsh_171_4) [(0xf0f00000000000000000000000000000f0f00000000,0,32)] (by decide +kernel) lowS_139)
def dzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def gzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000fffe0000fefa0000
def gsh_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000fffe0000fefa
theorem lowS_zo_239_16_42:Lower true dzo_239_16 roots_239 gzo_239_16 8:=lower_iso_b (d1:=dom_239) (r1:=roots_239) (T1:=gsh_239_16) [(dom_239,16)] (by decide +kernel) (lower_slice_b (T:=gsh_239_16) [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,0,1),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,0,64),(0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_191_64:=0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def gzo_191_64:=0xfffffffffffffffe0000000000000000fffffffefffffefe0000000000000000
def gsh_191_64:=0xfffffffffffffffe0000000000000000fffffffefffffefe
theorem lowS_zo_191_64_168:Lower true dzo_191_64 roots_191 gzo_191_64 8:=lower_iso_b (d1:=dom_191) (r1:=roots_191) (T1:=gsh_191_64) [(dom_191,64)] (by decide +kernel) (lower_slice_b (T:=gsh_191_64) [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc0000000000000000cccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,0,4),(0xffff0000ffff00000000000000000000ffff0000ffff0000,0,16)] (by decide +kernel) lowS_168)
def dzo_203_4:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0
def gzo_203_4:=0xf0f0000000000000f0e0000000000000f0f0000000000000e000
def gsh_203_4:=0xf0f0000000000000f0e0000000000000f0f0000000000000e00
theorem lowS_zo_203_4_139:Lower true dzo_203_4 roots_203 gzo_203_4 6:=lower_iso_b (d1:=dom_203) (r1:=roots_203) (T1:=gsh_203_4) [(dom_203,4)] (by decide +kernel) (lower_slice_b (T:=gsh_203_4) [(0xf0f00000000000000000000000000000f0f0000000000000000,0,64)] (by decide +kernel) lowS_139)
def dzo_175_64:=0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000
def gzo_175_64:=0xffff0000fffe00000000000000000000fffe0000fefe0000000000000000
def gsh_175_64:=0xffff0000fffe00000000000000000000fffe0000fefe
theorem lowS_zo_175_64_168:Lower true dzo_175_64 roots_175 gzo_175_64 7:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_64) [(dom_175,64)] (by decide +kernel) (lower_slice_b (T:=gsh_175_64) [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,0,1),(0xcccc0000cccc00000000000000000000cccc0000cccc,0,2),(0xf0f00000f0f000000000000000000000f0f00000f0f0,0,4)] (by decide +kernel) lowS_168)
def dzo_87_8:=0xff00ff0000000000ff00ff00
def gzo_87_8:=0xff00fe0000000000fe00ee00
def gsh_87_8:=0xff00fe0000000000fe00ee
theorem lowS_zo_87_8_84:Lower true dzo_87_8 roots_87 gzo_87_8 6:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_8) [(dom_87,8)] (by decide +kernel) (lower_slice_b (T:=gsh_87_8) [(0xaa00aa0000000000aa00aa,0,1),(0xcc00cc0000000000cc00cc,0,2)] (by decide +kernel) lowS_84)
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000ffff0000fffe0000fefa0000
def gsh_111_16:=0xffff0000ffff0000fffe0000fefa
theorem lowS_zo_111_16_42:Lower true dzo_111_16 roots_111 gzo_111_16 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xaaaa0000aaaa0000aaaa0000aaaa,0,1),(0xf0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff0000000000000000,0,64)] (by decide +kernel) lowS_42)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,10),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,40),(8,136),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,36),(32,40),(32,160),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,68),(64,80),(72,73),(72,74),(72,76),(72,88),(72,104),(72,200),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,130),(128,136),(128,144),(128,160),(132,133),(132,134),(132,140),(132,148),(132,164),(132,196),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|8=>16
|9=>186
|10=>338
|11=>118
|12=>14
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xf6504e8371e5d7ce59cde1c1ec38f1a814a8b64d751a17489770ff8570094fefc441223a2a524920
|9,0=>0xa2f03a2a64a16f8a01439f72c9cbc49bc4c99c24990b29649f93d25939e59347192d05916d8909d28ff5c8fba78ec6f8ded08d2bb8c9a28bcae8a85889da38996788a038257780b517eb147d9a67d5a37b05f7a9e17a299786ac7856c774f576aa074f8574bd6748b073e837279971e1c70e276e4206cb356c9cf6c5176c02a6be076b4186af20652696300f62ad25e12c5cbe959d47573a056f5f56972564a055fcd5589151fdc4f2804ef694e1ca4ca754c2c14c1fe4bfe74b4fd4ab5446b7b4659e421d33f7f03d6893d11d3caa23bcf337cc33776c3467f33adf31b292f8ad2f7672d44c2cff32a98b29b7528f8028e1f288e127bb726c0a25fe825976238711f0cc1d971197c418dd7155ff1490a137e3134b612dad12af9124a11224611d520a877098700906f0799107914070870519803d7b0200700b4500841006a9
|9,1=>0xff436fdd0bfd8ddfbb1cfb341fa471f9d69f5d07f57fbf10f2ef87beef8beaf02e8073e6347e3cb8e3b30d93a0d8d19d7bc7d6f3ed4de4d4204d2181d1cb9d14dbcf027cef19c9299c36e5c13bac0b53c09aabf6c5bf2c3bf11bbd81dbd4e2bbd4bb932cb8a80b788db47aeb3d94b26a3b1e92b001fae9e1ac61cac26da7f09a6e48a5fb1a58a4a413ca38dfa373aa340f
|10,0=>0x5a4ec5a39a58a75583a853e5053baa53855532ea50fa64f7654f2a34e0204d7cd4aef64a8014a613478e3477f04759f461994592a439954391942ca641fca4174b4113c410aa40dbf40705402d8401094008f3ee0c3dea83d3913cdeb3ccfe3c6af3c0fe3b8253b4763aa4e39419392803897c3837b3820937405371ad360f73572d34d883413e339973364a32db432a913215631c94318e52f2142efd52ec022ea6d2e43c2babe2b52f2985c26900267e824926241782387e2331e2285f21ce7202971fe931f6d01ed2b1eb1f1e49e1dc5f1d9861cab51b8f818b70187ed17cf6165c415e1015c6313b0f12a05121261118010eac1031a0fec90f7660dbe10d0e20d0870be020b9450b8c70b6350b2520af790a4fd09fc408f2108ebb07c28079ef077b707775076a906d6702f540210101c3f016a3009af0097c008b700355
|10,1=>0xc4a87c3f60c23f2c1800c0026bf254bea0ebe551bcdc4bb72db7e1ab7931b7362b6b97b5fd8b40abb3b16b3563b158ab0d45b0996af916adec0add82ad9d3ab270aa914aa51aa78d3a777aa5a91a5688a4f15a4cc5a2367a1d56a1a7aa0e76a0ad79f4339e8379d31b9d1189c8189c5a59c1349b6849b6729a35899fb79950c9950696ec29693395ca094750935c5913f29077b90211900808fc018fa488e6568e4858e17a8c6148c4838adb98a8998a1f0896a987dca87bba86dab84e65848348428083de6838de836828344a825c680c047e7a17cb2d7b9917b5077b27479ba4799eb7826277def76f5c76c7d716c66fdb46f00d6de256dd896d8816cd326c8516c7096c6016c4986bff96928e6910368f076809767b486719c66f8d6629b65b75654c464ec864b6f636d861c9c60d2b6077d604c4603715ce5c5cd975b22a
|10,2=>0xffc94fd40ffc874fc81dfbc1dfaf1ffa340f997bf94b9f8f5df8e45f7ef6f6f7bf698af661af5389f4fdaf45baf3e8ef37a7f2237f204cf1e62f129af091def600ef2a9eefb7eeefaeed15ee881ee388eddb7ed5e3ed4aaeca60ebe07eace5ea7f4e8599e7e2ae7951e7422e718ae51dee4c0ce3820e0f36e0be9e0778dfe27df395dc1c8dbe44dbb13d8f88d87d1d8467d744dd719dd6b83d4a4bd45cdd3549d1fe0d1dcdcf896cf52bcf14bcee02ce55ccda86cd769cb895c9fe9c86ffc8426c6c55c6207c616bc5e58c587d
|11,0=>0xfd2f7fba7ef9668f8e3af8a8bf814bf7879f7308f5d69f331cf329af2f5cecb32ec5eae469ae178ddf14edd90fdc6c3db393d919bd8230d6d2ed0d9dcf279ce015cb2c7ca9ceca69cc7aa2c6a49c55a4c5004c487ac4484c3e3fc1b85c1893c0d64bc505b6b15b2e99b08a3abe2fa763da55a4a4cc5a4803a3abea36dca369ca32d8a26869c8c79c7b4962ee9608e8ffae8b9e48809e8713286ee67e9c37e31a7c2427895e76ca56e3d66bd976b3706afc166f0c66b74642dc64123616d65a18058c9958893584c157fb95631b53cdc51a4a4ea874c8e34ba7e47d6c44cc4433cd406ce3799a37581348f5343e1322b631fd22bfee2b8302777422db02193d1f2b11d986157d314d98130ba0eb2a0d8be0c8b809e0809463092f707c2805d8e055e9017a400a6c
|12,0=>0xfff0bf4b96eb432dd9d2c33a399b3f9892d943438fd7c79d1f792e461e180eef70c075
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffffffffffffffffffff00ff00ffff0000ffff0000ffff0000ff000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|0,1=>0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffffffffff0000ffffffffffff0000ff00ff00ff000000ff00ff00ff0000000000000000000000000000000000ffff0000000000000000000000000000ff0000000000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0fff00000000000000000ffff0000ffff00000000000000000000ffff0000ffff0000ffffffffff00ff00ffffffffffffff00ffffffffff00ff00ffffffffffffff00ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffff0000ffff0000ffffffffffffffffffffffffffffff0000000000000000000000000000000000ffffffffff00ff00ffffffffff00ff00ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff00000f0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000
|0,2=>0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00000000000000000000000000000000000000ffff0000ff000000ffff0000ff00ffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffff00ffffff000000000000000000ffffffffffffffff0000000000000000ff00ff00ff00ff0000000000ffff000000000000ffffffff00000000ffff000000000000ffffff00ffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00ffffffffffff0000ffffffffffff0000ffffffffffff0000ff00ff00ff0000005555555555555555555555555555555555555555555555555555555555555500ffffffffffffffffff00ff00ff00ff00ffff0000ffff0000ff000000ff000000333333333333333333333333333333333333333333333333333333333333330000000000ffffffffffff0000ffffffff00000000ff00ff00ffff0000ffffff00ffffffffff00ff000000ffff0000ff00ffffffffff00ff000000ffff0000ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffff0000ff00ff00ff000000ffffffffffff0000ff00ff00ff000000
|0,3=>0xffffffff00000000ffffffff00000000ffffffff00000000ffff0000ff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffff00ffff0000ffff0000ffff0000ffff0000ffffffffffffff00ffffffffffffff000000000000000000ffff0000ffff00000000000000000000ffffffffffffff0000000000ff00ff0000000000ffffff0000000000ff00ff0000000000ffffff00ff00ff00ff00ff00ffffff00ffffff00ff00ff00ff00ff00ffffff00ffffff00ffffffffffffffffffffffffffffffff00000000ff00ff0000000000ffffff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffffffffffffffff00000000ffffffffffff000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00ff0000ffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ffffff00ffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00ffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffffffff00ffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff000000000000000000000000000000000000000000ffffffff00000000ffffff00
|0,4=>0xccccccccccccccccccccccccccccccccccccccccccffccccccccccccccffccccffff0000ffffffffffff0000ffffffffffff0000ffffff00ffff0000ffffff00ffffffffffffffffffffffffffffffffffffffffffff0000ff00ff00ff000000ffffffffffffffff00000000ffffffffffffffffffffffff00000000ff00ff000000ffff0000ffff000000000000ffff0000ffff0000ffff000000000000ff00ffffffff0000ffffffffffff0000ffffffffffff0000ff00ffffffff0000ff000000ffff0000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff00ffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ff00ffffffffffffffffffffffffffffffff00000000ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff000000ffff0000ffff0000ffff0000ffff000000000000ffff000000000000ff00333333333333333333333333333333333333333333333333333333333300330000000000ffffffff00000000ffffffff000000000000000000000000ffff0000ffffffffffffffffffffffffffffffff0000000000000000ffff0000ffff0000ff00ff00ffffffffff00ff00ffffffffff00ff00ff00ff00ff00ff00ffffff000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000
|0,5=>0xffffffffffffffff0000000000000000ffff0000ffff0000ff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffff00ffffff00ffffffffff00ff00ffffffffff00ff00ffff0000ff000000ffff0000ff000000ffffffffffffffffffffffffff00ff00ffffffffffffffffffff0000ff0000000000000000000000ffffffffffffffff0000000000000000ffffffffff00ff00ffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffff0000000000000000000000000000000000ffffffffffffffffff00ff00ff00ff000000000000000000ffffffffff00ff000000000000000000ffffffffff00ff00ffff0000ffff0000ffffffffffffff00ffff0000ffff0000ffffffffffffff00ffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00ffff0000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff0000000000ffff0000ffff0000ffff0000ffff00ffff0000ffff0000ffff0000ffff000000000000ff00ff0000000000ff00ff00000000000000000000000000ff0000ffffffffffffffffffffffffffff0000ffffffffffffffffff00ff00ff000000ffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff0000000000000000000000000000000000000000000000ff00000000000000ff0000
|0,6=>0xffffff00ffffff00ffffff00ffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000ffffffffffffffff0000ffff0000ffffffffffffff00ff000000ffff0000ff000000000000000000ffff0000ffff0000ffffffffff00ff00ffffffffffffff00000000000000000000000000000000000000ffff0000ffff0000ff000000ff00ffffffff00000000ffffffff00000000ffffffff0000ffffffffffff0000ff00ffffffffffff00000000000000000000ffffffffffff000000ff00ff00ff0000ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffff00ffffffffffffffff00ff00ff00ff0000ffffffffffffffff00ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000ffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff0000ffffffffffffffffffffffffff00ff00ffffffffffff0000ffffffffff000000ffffffff00000000ffffffffffff0000ffffffff00000000ffffffffffff000000000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00000000000000ffff000000000000ffff000000000000ffff000000000000ff00000000000000ffff000000000000ffff000000000000ff00000000000000ff00
|0,7=>0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ffffff00ffffff0000000000ffffffff00000000ffffffff00000000ff00ff0000000000ffffff000000000000000000ffffffffffffffff0000000000000000ffffff00ffffff0000000000000000000000ffff0000ffff00000000000000000000ffff0000ff00ffffffffffffffff000000000000ffffffffffffffffffff000000000000ff00ffffffffff00ff000000000000000000ffffffffff00ff000000ffff0000ff000000000000000000ffffffffff00ff000000000000000000ffff0000ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff0000000000000000000000ffff0000ffff00000000000000000000ff000000ff00f0f0f0f0f0f0f0f0f0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0fff0f0f0fff0000000000000000000000000ffffffff000000000000000000000000ffff0000ff00ff00ff00ff00ff00ff00ffffffffff00ff00ff00ff00ff00ff00ffffff00ffffffffffffffffffffffffffffffff0000000000000000ffffffffffff00000000000000000000ffffffffffff00000000000000000000ffffffffffff000000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00ff00ff0000
|0,8=>0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ff00ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00000000000000000000000000000000000000000000000000ffffffffffffff00ffffffff00000000ffffffffffffffffffffffff00000000ffffffffffff000000ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff0000ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff000000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff0000ffffffffffffffff0000000000ff00ffffff0000ffff00000000000000ff0000ffffffffffffffffffffffffffffffff00000000ffffff0000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffff000000000000000000ffffffffffffffff000000000000000000000000ffffff0000000000000000000000ffff0000ff0000000000000000000000ffff0000ff00ffffffffffffffffffffffffffffffff00000000000000000000ffff0000ff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000000000000000000000ffff0000ffff0000ffffffffffffff00
|0,9=>0xffffffffffff0000ffffffffffff00000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000ffffffffffffffffff00ff00ff00ff00ffffffffffff0000ff00ff00ff000000ffffffffffffffff0000000000000000ffffffffffffffff0000ffff0000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff0000ffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00000000000000000000ffffff00ffffff000000000000000000ffffff00ffffff0000000000000000000000000000000000000000000000000000000000ffffff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000ff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ff00ffffffffffffffff0000ffff0000ff00ffffffffffffffff0000ffff0000ff00ffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ff000000000000000000000000000000000000000000000000000000ffff0000ff00ffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffffff00000000000000000000000000000000000000ffff0000ffff0000ffff0000ff00
|0,10=>0xffffffffffffffffffffffffffff0000ff00ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff000000ff0000ffffffff00ff00ffffffffff00ff00ffffffffff00000000ffffffff00ff0000ffffffffffffffffffffffffffffffff0000ffff0000ff000000ffff0000ff00000000000000000000000000ffffffff000000000000000000000000ff00ff00ffff0000ffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffff00ffffffffffffffff0000ffff0000ffffff00ff00ff00ff000000ff000000ff00ffffffffffffffffffffffff0000ffffffffffffff00ff00ffffffff0000ff00000000000000000000000000000000000000000000000000ffffffffff00ff00ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff0000000000ffffffffffffffffffffffffffffffff0000000000000000ffffff00ffffff0000000000ffffffff00000000ffffffff000000000000000000000000ffffff00ffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffff000000000000000000ffffffffffffffff0000000000000000ffffffffffffff00ffffffffffffffff0000000000000000ffffffffffffffffffffffffffff0000
|0,11=>0xffffffff000000000000ffff00000000ff00ff00000000000000ff00ffffffff00000000ffffffff0000ffffffffffff00000000ffffffff0000ff00ffffffffff00ff00ffffffffff00ff000000000000000000ffff0000ff000000ffffffffffffffffffffffffffffffffffffffffff00ff000000ffff0000ff00000000000000000000000000000000000000000000000000ffffff00ffffff0000000000ffffffff00000000ffffffff00000000ffffff0000000000ffffff0000000000000000000000000000000000ffffffffff00ff000000ffff0000ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffff0000ff0000000f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000ffffffffffffffff00000000ffffffffffffffffffffffff00000000ffff0000ffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00ffffff000000ffff0000ffff0000ff000000ff000000ffff0000ffff0000ff000000ff00ffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ff000000000000000000ffff0000ffffffff0000000000000000ffff0000ffffff0000000000ffffffff00000000ffffffff00000000ffff000000000000ffff0000ffffffff00000000ff00ff0000000000ffffffff0000ffffff00ff000000ff00
|0,12=>0xffffffffffffffff0000000000000000ffffffffffffffff00ff00ff00ff0000ffffffffff00ff00ffffffffffffffffffffffffff00ff00ffffffffffffff000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff0000ffffffff00000000ffffffffffffffffffffffff00000000ffffffffff00ff00ffffffffffff0000ffffffffffffffffffffffffffff0000ffffffffffffff000000000000000000000000000000000000000000ff00ff0000000000ffffff00ffff0000ffff0000ffff0000ffff00000000000000ff00000000000000ff0000ffffccccffffccccffffccccffffccccccccccccccffccccccccccccccffcccc000000000000000000000000ffffffff000000000000000000000000ffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000ffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00000000ff000000ff000000ff000000ff0000ffff0000ffff0000ffff0000ffff00ff00ff00ffffffffff00ff00ffffffffff00ff00ffffff00ff00ff00ffffff000000000000000000ff00ff00ffffffff0000000000000000ff00ff00ffffff0000000000000000000000000000000000ffffffffffffff00ffffffffffffff00ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ff000000ff00
|0,13=>0xffff000000000000ffff000000000000ff00000000000000ff00000000000000000000000000000000000000ff00ff00ff00ff00ffffff00ffffff000000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff00ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ff00ffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000000000000000000000000000000ff00ff00000000000000000000000000ff000000000000ff00ff0000000000ffffffff00000000ff00ff0000000000ffffff000000000000ff00000000000000ff00000000000000ff00000000000000ff0000ccccccccccffccccccccccccccffccccccccccccccffccccccccccccccffccccffffffff00ff00ffffffffff00ff00ffffffffff00ff0000ffffffff00ff0000ffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00000000000000000000ffffffffffffffff0000000000000000ffffffffffff0000000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff0000000000000000000000000000ffffff00000000000000000000000000ffffff00ffffffffffffffffffffffffffffffff000000000000000000000000ffffff000000000000000000000000000000000000ff00ff00ff000000ff00ff00ff0000
|0,14=>0xffffffff0000ffffffffffff0000ffffff00ff000000ff00ff00ff000000ff00ffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffff00ffffffffffff0000ffffffffffff0000ffffffffff000000ffffffffff000000ff00ff00ff00ff00ffffffffffffff00ff00ff00ff00ff00ffffffffffffff000000000000000000000000000000000000000000ffff000000000000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffff00ff00ff00ffffff00ffffffff00000000ffffffff00000000ffffffffffffffffffffffffff00ff000000000000000000ffffffffffffff000000000000000000ffffffffffffff00ffffffffffffffffffffffffffffffff00ff000000ff000000ff000000ff000000000000ffffffff00000000ffffffff0000000000ff00000000000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000ffffffff00ff0000ffffffff00ff0000ffffffff00ff0000ffffffff00ff0000ffffffff00000000ffffffff00000000ffffffffffffff00ffffffffffffff000000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000ff00ff00ffffff00ff00ff00ffffff00ff00ff00ffffff00ff00ff00ffffff00
|0,15=>0xffffffffffff0000ffffffffffffffffffffffffffffffff00000000ffff000000000000ffff0000ffffffff0000ffffffffffff0000ff00ffffffff0000ffffffffffff0000ff00000000000000000000ff00ff00ff00ff000000000000000000ff000000ff0000ffffffffffffffff0000000000000000ffffffffffffffffffffffffff00ff000000000000000000000000000000000000000000ffffff0000000000ffffff00ffffff00ffffff00ffffff00ffffff000000ff000000ff000000ff000000ff0000000000000000000000000000000000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ffffff00ffffff00ffffff00ffffff00ffffffffffffffffffffffffffffffff0000000000ff00000000000000ff0000ffffffffffffffffffffffffffffffff0000000000000000ffffffffff00ff00000000000000ffff000000000000ff00000000000000ffff000000000000ff00ffffffffffffffff0000000000000000ffffffffffffffffffffff00ffffff00ffffffff00000000ffffffffffffff00ffffffff00000000ffffffffffffff0000000000000000000000000000000000ffffffffffffffffffffff00ffffff00ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff000000
|1,0=>0xffffffffffffffff00000000ffffff00ffffffffffffffff00000000ffffff00ffffffffff00ff00ffffffffff00ff000000ffff0000ff000000ffff0000ff00ffff000000000000ffff000000000000ffff000000ff0000ffff000000ff00000000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff0000000000ffffffff00000000ffffff0000000000ffffffff00000000ffffff0000000000000000000000000000000000ff00ff00ffffff00ff00ff00ffffff0000000000000000000000000000000000ffffffffffffffffffffffffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffff00ffffffffffffff00ffff0000ffffffffffff0000ffffff00ffff0000ffffffffffff0000ffffff0000ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00000000000000ff0000ffffffffffffffffffffffffffffffff00ff00ff00ff000000ff00ff00ff00000000000000000000000000000000000000ff000000ff000000ff000000ff0000ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ff000000ff00000000000000000000ff00ff00ff0000000000000000000000ff00ff00ff0000ffffffff00000000ffffffff00000000ffffffffffff0000ffffffffffff0000ff00ffffff00ffffff00ffffff00ffffff000000ff000000ff000000ff000000
|1,1=>0xffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff000000ff0000ffffffffffffffffffffffffffffffffffffffff00ff0000ffffffff00ff0000ffffffff00000000ffffffff00000000ffffffff00ff0000ffffffff00ff000000000000ff00ff0000000000ff00ff0000000000ffffff0000000000ffffff000000000000000000000000000000000000000000ffffffff00000000ff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffffffff00ffffffffffffff00ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffff00ffffff00ffffffffffffffffffffffffffffffffff00ff00ffffff00ff00ff00ffffff0000000000000000000000000000000000ffffffffffffffffffffffffff00ff00ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffffffffffffffffffffffffffffffffffff0000ff000000ffff0000ff000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8004207030a01405020001007030280a2700800101e130280a040487c1006130280a040487c4206130280a04000200e06050104a01000844807030280a040005c0e16050140823008843c200501408000b8783a0a0281002080381834050200400180b81c2c0a028100208038180a04090040008038180a040780400080382c0c0a028101208038180a04018080200
|1=>0x501408000401c0c0a028107201000dc1007030280a04010040008038181405020d40200040d00e06050140801000cc0e19030280a040d804002103818400a02810000c0b81c32160501408010b81c0c1d050140801190200e06050140801000200e06050140830008001007030280a041700400080382c0c0a0281002000401c0c0a028105a09008200e0605014082a
|2=>0x981c0c0a02810120803818144f0200400212701c0c0a0281002000401c0c4d050140801000cc2607030280a040d804000c0b84c0e160501408010401c0c0a028109601001201007030280a04008001007030280a04228040008038181404220040008039040c0a0281002000401c0c0a028108001000200e3e030280a0400800780803818140502004001f1c01c4406
|3=>0x320200e06050140801000201a07030280a0423024c617038580c0a0281002080381814050218402001081c0c0a02810c00100084105e0381814050200010072e018140502004005a0401c0c0a0281002000f8840e59030280a040015c100d030280a04008001006050140854008001007030280a0429804000803818a40a0281002001c020a207030280a04008002808
|4=>0x281036010005c0e1605014087700884103a038581405020007008038180a04018040008038580c750281002000401ce606050140801000200e0605014087000800106f038280a04370041007030280a043680400080f080140502004006c0401c0c0a028100200350200e06050140801000200e0605014086900800d008038181405020240008038181405021940200
|5=>0x206c02000401cba06050140809008200e06050140882008001007030140881008010008038181405020040008038181405021f802000b81c3216030280a040d80442083e81c0c0a02810000c038642c0a028103601000200e0605014087c008001007030280a043d8040008038181405021e802000401cf206050140801000e01007030280a043c004000c038640c0a
|6=>0x4900400081201c0c0a028100200488200e060501408010007c420d1101814050200030080385814050200400080381814050224002000b84c0e16030280a040d8051c0803818140502004000c0981c2c0a028103601002301007030280a04008001007030280a044500400080381814050222012000401c0c0a028110e01000200e06050140884008001813038181405
|7=>0x41bc0c0a028109201042940e06050140801000200e060501408a3008014208038181405020040008038180a044f0040008038193a0a0281002000401c0c0a028113801000200e06050140899008001007030981405020241007030280a044b804000803a540c0a028100200040781a220501408090f8201a22030280a04048200e06050140893008001007030280a04
|8=>0x3700400085901c0c0a0281002000401c0cb0050140801000200e0605014081c008001007032bc14050200400ad0401c0c0a0281002000401c0c0a02810ce09000201a07030280a045600410070b0280a041d80400080f07414050200400085501c0c0a028100200540200e060501408010008410070309814050200042080f0340c0a0281012a60401c0c0a028100200
|9=>0x302808440080042085d81c0c0a0281000080385814050208c02001081c0c0a028117401000e00e06050140862008001007030280a045c804000803ae00c0a0281002000f8843c22050140800070201a07030280a0404820a207030280a040080010070b0180a045b804000803ad40c0a0281002001e8200e0605014080900acc1007030280a04008003e21030280a04
|10=>0x30741405020040021041fc0e06050140800608200e06050140809008841007030280a04600001007030280a045f80400080f098140502004001f040184c0a0281002005f0200e06050140801000200ebd030280a040080018080681cbe060501408090401c0c0a0281178010007c7007030280a0401004000803818ea05020040021038642c0605014081b000e01007
|11=>0x281002000401c0c0a0281194010007c2e1e0b0280a04008200e06140280a04008001007030299004008001007030280a043c00400080381814050231c0200628200e06050140801000201a060501408850480410070301408030080018080801cbe06050140800040280a04371240200040781405023100200108214807030280a04000200ec2030280a04008004207
|12=>0x38a40c0a02810008d040340c0a0281012016a8200e06050140801000200e060501408d3008001007030280a046880400080381814050233c0200670200e060501408010007c420d030280a04048841007030280a04570001007030280a046680400cb0401c0c0a028100200608201a07030280a04008541007030280a040080022080381814050200400180b81c0c0a
|13=>0x20002e081d01c2c0a0281002d41c0200e060501408000b81c0c0a028104601000840e19030280a040d800100d030280a04330240221043780e060501408004685c0e160501408010401c0c0a028112809000301007030140881008001007030280a046e00400080381814050236c02000401c0c0a02811b401000200e060501408d900800100d03029ae04008003e21
|14=>0x3818140502004000806b800c0a0281002000401c0c0a02811be01000201a0711018140502024c61703818140502004002f1c0200e06050140801000200e06050140886008001056038181405022c40200040781a060501408b100800103a03858140502004009f0401c440605014080100060180803818140502004001f1081c2c06050140801000206298038181405
|15=>0x501408010007c4207030280a040480010070b0181405023000200720201a06050140801000200e060501408ba00800107d0381814050200400e30401c0c0a0281002000f81c0c0a028116201000200e29030280a04478040008038a40c0a028109201000201a072f818140502024101e0b0280a047080400080681c0c0a028113601000200e060501408e2008011a08
|16=>0x40340e22030280a04003041007030280a04008001808080340e06050140801000205807030ac1405020040021040780e16050140801000201a07030280a044280400081601c0c0a0281002000f8200c0a0281168010007c1056030280a04008011a080385814050200400080f058aa0a028100200040340ec3030280a04008001007030280a042180400083f81c2c06
|17=>0x28100200040c40e06050140809001a01808038181405020040008038181405023980200040400e5f030280a04000200e060501408dd008002e08038642c06050140801060200e190b0280a04008002e08038181405022d002000401c0c1d050140801000200e0605014088f008001007030280a0424804008d0401c0c0a02810120100084100d0397c0c0a028100021
|18=>0x21b802000f8201a0605014086e008014008038181405020040008068181405023600200040181405021b9c201003902e07030280a04008003e21038880c0a0281000084c01c44060501408000f81c0c0a028110a01000203c06050140849008001007750181405020040008038181405021880200748200e06050140801000201a0605014088500801d00c0401c0c0a
|19=>0x3010072f81814050200400087701c0c0a0281002000f8780c0a028110a01000300e0605014081b00801da080381814050200400170404c0e16030280a040083010130385814050200400080381814050219812010007c1007030280a044d804001f0b8780c0a028100200040782c0a028109201003b01007030280a04008001056038280a043700400080f0341405
|20=>0x501408960080010070309814050200400080f0340c0a028101201040340e060501408e2008001007030280a0428004001f1c01c0c0a0281002000401c4406158280a0400234100d0381814050200400080f034440a0281002000f8201a22030280a04008004208038181405021b802001b8e01007030280a04008001007618181405022c402000401c0cef050140801
|21=>0x30280a04008004207030280a040d8040008038181405022ac0200108203c07110280a0400020ac060501408e10080042081d01c0c0a02810000803bc00c0a0281002002d8200e0605014080100030100703029ae04008002e070b01814050206c02080381814050225002000601c2c0a028103601000201a07030280a045d00400360401c0c0a0281002001c0200e06
|22=>0x23d002000f85c0e16030280a0400821e607030280a04008001007030280a041f804000c7201c0c0a02810020010820ac07030280a040080042080f0340c0a0281002000f8340c0a0281162010007c10070301408b700800c608038580c0a028100200041580c5505014080100234100d030280a04008001808039080c0a028100200790200e0605014080100021e207
|23=>0x20040008038581405021dc0200040340c0a02810cc0100020de070b0181405020043e087b818140502004000e040340e06050140801000201a06050140849008003e17038880c0a0281002000401c0c0a02811ec01000501007030280a04048041007030280a045a02400380401c0c0a028100401003d41007030280a040080010bb038181405020040008038181405
|24=>0x501408010008410070c8580c0a02810008d0b81c0c0a02810020004078aa0a0281002000b8203c070b0280a04008203c060501408f9008001807030280a044280400083f81c0c0a0281002000401c0c0a028105a01000200e060501408d2008003e080f088140502004001f0b81814050239402000401c0c0a028118001000601007030280a04008003e210f0181405
|25=>0x30280a04008001056068181405023840200448200e06028116e0100021f006050140885008002e081d01c0c0a0281002004681c0c0a028110a01000200e060501408770480400080f01c2c2b050140801000200e190b01814050206c02001983010070c81814050200400085201c0c0a028100200060201a072f81814050200400082b01814050212402006b0200e06
|26=>0x404c0e16030280a040d8040033060202607030280a04008002e07030280a04330040008038181405020ec02000401c0c0a02811f801003ec1007030280a040080010070b0181405022a40200108201a07030280a04048200e06050140846048014e08038181405020040008038181405023e802000605c0e19030280a04008006608038642c06050140801000bc1007
|27=>0x8001007030280a048180400cc0401c0c0a0281002000401c0c0a028120401001281007030280a0400800101e4c01c440a02810009a040780c0a028100200808203c06050140801000200e060501408ae00801d0080381814050200400080681a000a028100200340200e06050140801003fc1007030280a0400800101e030280a047f00400fd0401c0c0a028100200
|28=>0x30280a04118040008038581405021b802000441c0e06050140801000200e16030280a043b0040008038181405024180200448200e16030280a04008001007030280a048280400080381814050232402000401c0c0a028108e010007c100605014090400800104e03818140502004000c0b84c0e06050140801000cc1013038580c0a028100200040340e06050140877
|29=>0x30280a040480042084c01c0c0a0281000d6040340e060501408010007c100d030280a040480442080f2600e060501408000401c0c0a0281216010023410f8030280a040080010078501814050200400210401c5206050140800848200e060501408010007c420d030280a0400800100d038181405020b40200840200e06050140801000200e06050140860008001007
|30=>0x28121c01000203c07110280a04048003e08038880c0a0281012000401c0c0a028118c01000dc1007030280a04008013408038181405021b802000401e1a0605014080100020ac07030ac1405020040008038181405021d002000401c0c0a6b8100200388200e16030280a040080010560381814050200400080381814050243002000f820de06050140801002241007
|31=>0x7280400081601c2c06050140801000200e16030280a047380544080381814050200400720401c0c0a0281002000401e2006050140801000200e06050140888008013408038880c0a0281002000401c0c0a028121e0100020fa070b0181405020040008038181405022580200040780e290501408010007c10071481814050200400086f01c0c0a0281002000401c0c0a
|32=>0x4d01c0c0a028116201000203c07158280a040080010070c81814050206c02000f8200e06158280a040080010070b01814050223c02000401cba06050140801000200f13030280a0400800180803b801405020040021040780e06050140809000203c6f03858140502004101e038181405022c40200890200e060501408010005c0e06050140877008013408030280a04
|33=>0x30280a0470804000803818400a028100200198200e19030280a04008002e084c01c0c0a0281002000401c0c0a02810d601003501007030280a04008001007030280a045b004000803b802c0a028100200060201a07030280a0404804101e030280a045880400080381814050200802000401c0c0a028109801000e01007110181405020004208038181405021240200
|34=>0x202400087701c2c0605014080100084106f0381814050200400080981c0c0a028103601000200ec3030280a0400800b0080681c0c0a0281002000401c0c0a02810ce010007c101e0b0280a04008001007898181405023f802000a0200e19030280a04008013e080f0181405020040008038181405022a402000401c0c0a028113601000200e060501408ac00800106f
|35=>0x510201a07030280a040080010070b0280a04428040008030280a04821240200040780c0a02811d601000cc1013038181405020040017040c40e060501408010008410072f818140502000ae080381814050200400088a01c0c0a028100200041780e0605014080100030101003818140502004000e0401c0c0a028101200108200e59030280a04000301013038181405
|36=>0x30280a040080134080681814050239402001c0203c07030280a04008001007030280a048b80400080f01c1405021b802004d0200e0605014089b008003e08038181405021b802000401c0c0a02810ec01000200e06028116e01000200e060501409160080042070b01814050206c0200041bc1a07030280a040085010130381814050200401150401c0c0a028100200
|37=>0x30280a04008201a072e818140502004001f0401814050239c02000401c0c0a028110601000200e22030280a045880400210401c84060501408000401c0c0a028110a0900800101e03964140502004001f0401cb206050140801000200e29030ac14050200116080381814050200400330381814050206c02008c8200e06050140801000302e070b0280a0400c601007
|38=>0x50140801002341007030280a04008003e0806818140502004008d040780e060501408010007c10060501408e500800101e030280a04708040008030280a0472ac402000f8200c0a02810dc0100021ee070b0280a04008001007030280a048d0040008038181405023400200040340e06050140846008007a080381814050200400082b1bc0e0605014080104078de0d
|39=>0xb81c0c0a0281002000401c0c0a028120801000200e190b01814050200400080381814050219802000401c0c0a0281092010003010070c818140502004000c0401c0c0a0281012010005c1007110181405020040008038580c2b0501408010005c1007030280a04728040021040780e060501408010005c10070b01814050200418080385814050200400170404c0e06
|40=>0x281002004487c1007030280a040080010100381814050200400080981c0c0a028101200108201a07030280a040080010078881814050200400080981c2c06050140801000201a060501408e100800106f03818140502004000c040340e06050140801000203c6f0381814050200400080681c0c0a028101201070200e0605014080100030101303818140502004001f
|41=>0xf8200e06050140801000302e07030280a04008006608038580c0a028100200070200e22030280a04008001007030280a043b804001f1081c0c0a0281002000f821f006050140801000200e16030280a040d8040033060200e06050140801000213007030280a0400800101e4c01c0c0a0281002000401c5206050140801000200e22030280a04048001056038580c0a
|42=>0x73804000c0401c0c0a02811b001000200e2911018140502004000c0401df006050140801002681007030280a04008020208038181405020040008080340e06050140801000200e060501408fe00800101e038181405020240200040c40e0605014080100020621e0381814050200400080f01c2c0a0281002000f8200e16030280a04008001007030ac140502004008d
|43=>0x38181405022d00200041580e06050140801000203c0d030280a04008001031038880c0a028100200468301007030280a040080010070b018aa0a028100200318200e0605014080100020ac1e0381814050200400080397c0c0a0281002000401c2c060501408e100800101e0681c0c0a0281002000401cb206050140801000200e0605014086e008001007030280a04
|44=>0x501408490080010077001814050200400210401c3206050140800040340e0605014086e0080042080381814050202400140401c0c0a0281002000401c0c0a0281162010007c101e0381814050200400330401c0c0a028100200108200e16030280a040080134080681c0c0a0281002000401c0c0a028103601000200e42030280a0400800b008038181405020040008
|45=>0x401c0c0a02811d6010005c101e0381814050200400082b0340e060501408010007c1007030280a04048040008068181405023940200040340e5f030280a04008003e080f01814050200400080681c44060501408010027c1007030280a040080010070b0181405024100200720200e060501408010003818080381814050200400080381814050211802000401c2c06
|46=>0x30280a0400800103a03818140502004001f040340e06050140801000203cf8030280a0400800100d038181405022c40200043dc0e060501408010005c10070c81814050200400380401c0c0a028100200448200e06050140801000200e060501408d8008004208038880c0a028100008038181405022140200040780e0605014088500801341f0401c0c0a028100200
|47=>0x30280a040080010071101814050200400080681c0c0a0281002000401c0c0a02811ca01000202607030280a040080010070c8181405020040008038181405020240200040780e06050140801000841007030280a040080010070b01814050200400710401c0c0a0281002000401c0c55050140801000200e290b01814050200400080f01c440a0281002000f8200e22
|48=>0x200e06050140801000301007030280a04008001007030280a0470804000803be00c0a0281002000b8200e060501408010007c1007
|_=>0
def sO:Nat→Nat→Nat
|8,0=>0x3b401ba00cee05f802bc013e008f003f801c380c5c0530021800cc0046001300009
|9,0=>0x159d0aaa454322989147c8a1684f7427381354898644b1224f9123488fa046b222d81124886e442522099100487de43dd21e590ee4874e439521c190dc486be434d219e80cac86324305417990b8c05a242bf2155a0a64850e427521319094c0482422f210e9082c83f241e720e9a0704835e419b40c5805e482d2015720a2904cc8242410f207e9
|9,1=>0x278c93a249bf24d69266c9312497904b39255492864931248f9243491f648e9246b92314916648a12447921f490d6485b0424920dc904a4813240091fc40fbe47cd23dd91eac0f32478723ba91d940ea64741239881c7c8e1a46fb237491b5c8d8a46b3235091a350cf64667432a9190c8c62461f2306917e50bce45d522e2816cc8b42458d42bd9
|9,2=>0xdeb26ec9371c9b6a4da326c8936041ade4d5d26a5934e49a4e4d152682833cc99c24ccf265e932ac99324c87263b8319498a64c4126179307498164bf925f392f5c178a4bb505d192e4496fe4b6d25ae82d2516720b29058b92c1495e64ae1256792af495564a9b0544929dc94ca4a51451f928ad14360a0744fa9
|10,0=>0x4a74a5165279293394954a4865231290f94834a3f291e728e9a4704a35e519d28c4a45d522c2914f289e944aca22e91034877a4374a18ed0b3484fa422d20f25067282a9410ca062501d480593fdd1fca4fd147df93eb49f364f8927bb93d8d1e9e8f3d279593c5d1e0a4ef3277093b3c9d7a4eab274ba3a149ce28e5d4725938dd1c468e0f46fe9
|10,1=>0x5d0cae5e971d2b8595be4adce56d52b6195ac4ad3a96894b3b95994aca2963f2b16958652c0e55f52af195744ab7e55ad2acd95624aaee55652aa995504aa5e551b4a84953d529c654d12a5ea52aca93254872a39a5184a89a94394a12a504527fe53eb49ec94f1ca76a53a329c7a4ded26ce935349a094cbca63a530b297c94b9525a652c129579
|10,2=>0x6facb7b25bc72dda96e8cb7225b7f2db696d6cb6925b372d9296c4cb6025aeb6d6ab6b0cb5625a9f2d46969e534ce5a552d21968c4b43a9a076cfa96785339e59bd2cd4a665cb306996f4cacb650db262591b6c84963dcb1c698d12c60862bcb13a588b2c3c9619cb0aa58432c189607cb01a57fb2bf495f5caf8a57b32bcfa5e34aef297672baa9
|10,3=>0x823cc0fa606b302ba8114c062a01f300697fecbfce9fd52fe197ec4bf3e5f8d2fbca7d9cbea69f412f9797c6d3e125ef72f7297b453d7e5ead2f4ca7a1cbce69e612f28878f53c565e192f03977d4bbc65dcf4ede976a53b2e5d852eb997584ba9e5d3d2e94a745cba0a5cf32e709733cb9769ca92e4aa720cb8e25c5f2e26970ecb84e9c116dfea
|10,4=>0x94ecca5265173283893d4c9c2a4cd525d992a4c92aa48152379917c489a643952139904d480263ed51ed98f24c76e63a351c7a8df4c6d6635931a398ccd4642630f317da8b9d45a6a2bf515698a65450e62753130a893544766229310b98814c3e661e130e6a86e5434e619530c1985c4c2baa14b309c9849cc22a6101507798374c192a0b55050a
|10,5=>0x2689333b99994cca666413316a986ccc1265f732f1a9744cb7e65ab52cc996154ae6655f52a69
|11,0=>0xad155662ab1f35869abecd5ceaad3555faaab4d5366a87553a9a985549e6a3b55149a855540669ef54ee9a725536aa9a334c89a5fcd2d6a95754a29a4c5523e690d347caa39551a668c13456aa26cd10ea87534319a13d5076a829340b9a00d4fe267df33e5a9ee4cf4e679353bfa9dad4eaea7435397a9c74ce1666f7537299b4ccd7ea6ad334d9
|11,1=>0x2f4137979bc6d5e126ef557719bb3d5d7a6ea9574b9ba0d5ce26e5f37269b8ecdc526e155700ab7bcdbb6adc756d9ab684db1aad7b36b3ab554da82ad2f368dab424d9eaace336689b2f559566c9936439b1cd58c26c4d561cab09cd82a6c0335f89af7cd79a6bb955d2aae4556fe6b6b55ac9
|12,0=>0x303d38159c064e00e6ff537f19bf44df7e6fad37cd9be24deee6f6537a99
|13,0=>0x18278
|_,_=>0
def wAt:=mkWire dB 283 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x8010688803801030050401d00801068880380103005068880380104005030050401d0881706041038250080104019040050c86d038070405a030010400103001060670401903807040050f88803819030050401d0f858040010401d0381903001050710986e038050405a0300103001060650401903807040010a82b0a04d0380506003040190882b060410382500801040190703406005038010080104019
|1=>0x38071c01b1c01d0b805040011b01b0b86503807040010986d038050405a03001038070405a04059030010f88804005030050401d03807040010401903001040010f8580401d03001198650b81903807040010b8c60981903805040011781f040a50b005030010703410819038010400500801060370380104019040b2038ad0b007030010f8a40401d040050b00503001088130604103825008010401903819
|2=>0x400100801038050600304019029411981e04059030010386d040050405a03001100010f888030050401d038050405a040590300104019040010380503001039320d8050405a0300125005041250385a030010391e230010408a0300517817040a50b005030010310d0410a0c8010380706042038250080104019030fd0404209801038051e8070a01d06003040190b80504001030050401d1d801040ea0c819
|3=>0x30010604d04019008010380533801330050f81b0401d04099068880380103005038010408a0080103005040650300103807040010398a040a60b00503001040050386e0405a03001040052f81906807038012e8050603403801040192d81d1980704059030010401d110030300504005038012c01d06007040192b1570385903858030010610a0c80104019038070e8050f8580401d03001038091c01b0b805
|4=>0x30010617f0680703801040190617c0680703801040191b81b1c01d0b80504001038071982306001040190601f04001040190300104005030010c819038071b82b1c01d0b80504001051d90985a0380503001031d11083603801040053901b388010f8070401d0681b0f0030380103819198670b81903807040010f88803819030050401d0a065038070600304019041ad0688a03801030050f8af0b0070401d
|5=>0x3001468270601d00801040194581b0417d0680703801008014481b1081d040052c03606007038010401943007428010407a038190380519823060010401906034038010080104019418010604f04019038053402b1087903819040052b8032c01d0600704019041fe1d0010c81903807040010405a0380703001040052b0070385903001040190405a03807030011984f040590380503001300050386e0405a
|6=>0x40194d8054d01b0b81d04001008010688803801030050ba62040010f00703819032591c01f0b80504001008010300503801038190300503801008010401d4a0013b8050601f04019060430382500801040190c86d038070405a030012b8012c01d06007040190380104005030050401d06065040190380703001070371081903801040050405a0400103805030010423d038a60b005030010405a0401903805
|7=>0x380700801330050f81b0401d3b8010601f038010401903001040ea0c819038070f8580401d038190300103aad0d8070405a03001042a50c85a038070300104005068880380103005008010380103819040055381d0602700801040192b003038590385a030011c078108010381904005042924c0010f00703819510070603503801040195002b4f8050f8030401d4d0880f801030050401d168050603703801
|8=>0x4005178231c0190b805040010610b0c8010401903807060400382500801040190381904005030050401d06005038010080104019038091c01b0b80504001030014482b1081d04005032d95880504036038010a01d0080106003040190bad10388a03005040010401d040050681b03801270070386d0405a03001112c70403603801030050986e038050405a03001448580404d0380503001042b92101b0c801
|9=>0x4005468030601d008010401924805040050385a030010c86e038070405a03001038190688803801030050401d068880380103005041d90985a0380503001061080c801040190380706807038010080104019118010606704019038070401d1c01b0b80504001051d90985a0380503001038070405a0400503001178171c0190b80504001378070f0030381904005030010606704019038070415a0f00103819
|10=>0x40010b8ea0c8190380704001040010401d03819030010f8a403025008010401d02b250a01e06003040191b81b0f825008010401d041f62b0070385903001043190801b098010380503801008010407a038191b82b0f825008010401d040190680506807038012b01f031b90681b038010f157038190385803001040054c0010f0070381961807032c50403603801040050f8580401d03001210190c80103807
|11=>0x380102b610601e03801040190401d040050b00503001008010601d03801040196b005041b90681b038016a01b4d0070b81d04001690011087a0381904005680050f85b0401d030010617d0680703801040190400503801008010401d2101b0c80103807040054485b0404d03805030016601d040ad0b00703001468030601d03801040190a04d03805060030401906041038250080104019060650401903807
|12=>0x3807030050f8030401d060650401903807030010401d04005188070f0050381904001030010c819038071b8071c01d0b805040010400106067040190380703807040050405a030010f81b03801008010401d040051d0030c8190380703001040010407903819008013b8050601f040193402b0604d04019038056e8051981f0405903001440014481b1081d040050617e0680703801040190417a2f81906807
|13=>0x385a0300104395038010381b0415a03859030012b0070385903001041bd0f0030381904036038010401d038a60b005030010385a0b00503001008010680703801038190401e030014d01b0403503801041ba0681b03801063610601e0401903385038010401e0386c0405a030010380100801030050406503807040011c0190b80504001428010407a03819068190403603801038190403603801030010c819
|14=>0x388a03005040010f8580401d03001038a60b005030010b15703858030010601d0080104019068070380104005030050380104005468030407903819068050380104019038ad0b007030010300103819040050407a0380103819038ad0b007030010388a030050401d038590401d030010601d0401903001038190385803001032c504036038010410a0c801038070c859038070300104005008010401d24805
|15=>0x38190401d0681b038014f8050f8030401d0601e03801040190401e0681b0380104001043950381b04005030050401d1880703889030050407a0401d038192b01f0f00103819033ad0b81e04001040a60b005030010416511003030050407a0380103819468070601d040190388900801030050604d04019038050439e728010381b0680506807038011981f0405903001030010380704001040190380703001
|16=>0x11001030050601d038010401903005038010381903801030050401d040050681b038011c01d0b80504001032c504036038010b3870401e03001068070380104019038a50b005030010401d0407a03819198230600104019041550385803001040010380503001040190380503001008010f81b0401d4d01b0f8010401d0401d0381904001038190385a03001388190f8070401d031b90681b038010681b03801
|17=>0x42610f00703819188030f00503819040050405a030010d8070405a0300103005038190400506819038010401e0c81903807040051981c040590300119807040590300102b610601e040190405a04001030013b8050601f040190405a04019030010415a06819038010b86503807040011c01f0b805040010688803801030050381903801008010603603801040191981e040590300104025008010401d14807
|18=>0x40052b01f068190380104001030050401d6c0010601e040190080106003040190388a00801030051c01b0b805040012c00106007040194c0030f007038190f88a030050401d040010401d03001378050f00303819040420980103805043610601e040190f00103819040050380103819040050401d04036038014482b0f8050401d0406503807030010385903858030010601d03801040190c8010401903807
|19=>0x680703801038590385a03001041b90681b038010300103807040050400104079038190381903858030010400103819030010f3e30380303819468230601d040191d0010c819038070603703801040191087a038190400503819030050401d040010401d0381b248050385a03001040e90c819038070401d0381904005030010601f04019038010f81b0401d2b00303859030010401d7c019038031081903801
|20=>0x40ea0c81903807370070681b038010a00506003040190c85a03807030010380100801040050408a00801030050602700801040190b87a0381904001040190380704001038070405903001040a50b0050300106819038010401e4482b1081d040050407a03803038190c81903807040010407a04079038190601f00801040190b00703819030010405a03807030010600104019038074c0010f0070381904019
|21=>0x30010386d0405a030010380504019040010380504059030010601f03801040195a0010388a03005040ad0b007030010f88b030050401d041250385a030010f0070300503819040350380103819043e103803038192101b0c8010380746807040790381906b97038010381b1087903819040050f827008010401d70801038190401e042d10388a030050405a0380503001038050600104019040010f81b0401d
|22=>0x681b0380103801008010401d0f0070381904005040c60f005038190601d040190380370003033850401e040050b00503001448031081d040050401d03801040050603703801040194f8190f8030401d0386e0405a030010606704019038072b01b0385903001039190408a030050985a0380503001033fa708010401e0404d0380503001330010f81b0401d0a01e0600304019230010408a030050385b0401d
|23=>0x2b00703859030011c01f0b80504001038190b0050300103025008010401d1d0030c81903807063e304019038030381900801030050401d00801030050801b09801038050f825008010401d0681b04035038010386f0405a030010b007038590300110836038010400502b610601e04019030010f8070401d0b4110385b030010701f10819040050401d0f003038190f805008010401d0f0070381904005041b9
|24=>0x38010b0070381903001038070405a030010b0070401d03001038a60b005030010603403801040190b3850401e03001033610601e04019008010381904005030010f00303819040360380103819070031081904005040010601f0401904035038010381b038ad0b00703001820010385b03001060350380104019388010f8070401d888010601c040194481b1081d040050f801030050401d428050407a03819
|25=>0x381903001033f9708010401e038070600304019038190f8030401d0c85a03807030014d01b0b81d040013b8010601f040190f003038190401e0f888030050401d0b8190380704001040010f007038190688a03801030054d0070b81d04001588050403603801033850401e030010380100801040190403603801038191c01b0b805040010d8050405a03001040250080103005040050385a030010403504036
|26=>0x63e104019038030603503801040190407a03819030010385b0385a03001038190b81e040010405903805030010981903805040010680703801040052c01d06007040190396511003030052f81906807038010382500801040190408900801030051100303005040050401900801038050985903805030010f0030381904005038050405a03001032c50403603801060070380104019330050f81b0401d0401d
|27=>0x4005008010407a0381911003030050381911003030050401d0b0070b005030010417d06807038010405a04059030010439d728010381b040010401903001044110385b0300104035038010381b108010381904005043de7c01903803038190681b038014d01b0b81d040010401d0681b038010985a03805030014482b1081d040050b88a03005040010405a04005030010f0030380103819038050600304019
|28=>0x40010b007030010381b0400103819040050400103001040190300103805040010407903819038010401d04079038190401d0381b038190401e04036038010381b0401d0681b03801034110385b03001370050681b038010f85b0401d03001038010408a030050a01d06003040190f0010f00303819038010f003038190603403801040190401d728010381b0604f04019038050403603801030050c80103807
|29=>0x300104089030050601f040190401d04005038030401d0405a0300106001040190f007038190f007038190b00503001008010300503859030010f8050401d0980103805008010380503801040050601c040190380503001038010401e0f0030381903801040190f003038190380100801108190400504019038050401d040010385b0300103807030010f81b0401d0385a030010401903807008010401903005
|30=>0x30010c8010380706007040190388a030050385903001038010381903889030050601d04019038580300104065038070f0010381906807038010401e03001038010381911003030050681b03801728010381b0601e04019110010300504019038030b81d04001043e1038030680503801708010401e00801038190f005038190f0050381903819030010401d030010b007030010f8190401d040190400104059
|31=>0x40010b805040011081d040050601e0401903005040050407a038190407a038190f8010401d0b81e0400103819040010681903801008010401d038010381b06807038010401d0381903801030050f8030401d0385b03001043950381b06005040190408a030050385a03001033850401e03807040050681b038010080104005060030401904036038010401d038190405903001040050300104035038010405a
|32=>0x40190401e03803040010401d03005038010381b0380503807008010381904005030010f8070401d03858030010b005030010300503819030050401d0c81903807038010401d038030381904036038017c0190380303807
|_=>0
def oO:Nat→Nat→Nat
|8,0=>0x465041503c50375032502d50285023501e50195014500f500a5005500050000
|9,0=>0x1474143413f413b41374133412f412b41274123411f411b41174113410f410b4107410340ff40fb40f740f340ef40eb40e740e340df40db40d740d340cf40cb40c740c340bf40bb40b740b340af40ab40a740a3409f409b40974093408f408b40874083407f407b40774073406f406b40674063405f405b40574053404f404b4
|9,1=>0x2474243423f423b42374233422f422b42274223421f421b42174213420f420b4207420341ff41fb41f741f341ef41eb41e741e341df41db41d741d341cf41cb41c741c341bf41bb41b741b341af41ab41a741a3419f419b41974193418f418b41874183417f417b41774173416f416b41674163415f415b41574153414f414b4
|9,2=>0x32f432b43274323431f431b43174313430f430b4307430342ff42fb42f742f342ef42eb42e742e342df42db42d742d342cf42cb42c742c342bf42bb42b742b342af42ab42a742a3429f429b42974293428f428b42874283427f427b42774273426f426b42674263425f425b42574253424f424b4
|10,0=>0x3f033ed33ea33e733e433e133de33db33d833d533d233cf33cc33c933c633c333c033bd33ba33b733b433b133ae33ab33a833a533a2339f339c3399339633933390338d338a338733843381337e337b337833753372336f336c3369336633633360335d335a335733543351334e334b334833453342333f333c3339333633333
|10,1=>0x4b034ad34aa34a734a434a1349e349b349834953492348f348c3489348634833480347d347a347734743471346e346b346834653462345f345c3459345634533450344d344a344734443441343e343b343834353432342f342c3429342634233420341d341a341734143411340e340b34083405340233ff33fc33f933f633f33
|10,2=>0x570356d356a356735643561355e355b355835553552354f354c3549354635433540353d353a353735343531352e352b352835253522351f351c3519351635133510350d350a35073504350134fe34fb34f834f534f234ef34ec34e934e634e334e034dd34da34d734d434d134ce34cb34c834c534c234bf34bc34b934b634b33
|10,3=>0x630362d362a362736243621361e361b361836153612360f360c360936063603360035fd35fa35f735f435f135ee35eb35e835e535e235df35dc35d935d635d335d035cd35ca35c735c435c135be35bb35b835b535b235af35ac35a935a635a335a0359d359a359735943591358e358b358835853582357f357c3579357635733
|10,4=>0x6f036ed36ea36e736e436e136de36db36d836d536d236cf36cc36c936c636c336c036bd36ba36b736b436b136ae36ab36a836a536a2369f369c3699369636933690368d368a368736843681367e367b367836753672366f366c3669366636633660365d365a365736543651364e364b364836453642363f363c3639363636333
|10,5=>0x72637233720371d371a371737143711370e370b37083705370236ff36fc36f936f636f33
|11,0=>0x7a727a527a327a1279f279d279b27992797279527932791278f278d278b27892787278527832781277f277d277b27792777277527732771276f276d276b27692767276527632761275f275d275b27592757275527532751274f274d274b27492747274527432741273f273d273b27392737273527332731272f272d272b27292
|11,1=>0x8132811280f280d280b2809280728052803280127ff27fd27fb27f927f727f527f327f127ef27ed27eb27e927e727e527e327e127df27dd27db27d927d727d527d327d127cf27cd27cb27c927c727c527c327c127bf27bd27bb27b927b727b527b327b127af27ad27ab27a92
|12,0=>0x82218211820181f181e181d181c181b181a181918181817181618151
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 16
def pmP:Nat→Nat
|0=>0x21d9c0000008647000000217fc00000085f7000000215fc00000085770000002159c0000008547000000209040000008103000000195dc0000004d43000000115fc00000045770000000e79c0000002577000000081500000001d77000000074cc0000001577000000035dc00000005f70000000179c000000057f000000015dc0000000567000000010900000000357000000007fc0000000064000000000040000000000
|1=>0x1115fc0000040f77000001015fc0000040577000000bdd9c000002ef77000000adddc000002b767000000acd9c000002a567000000a1ddc0000028577000000a159c00000101020000003f51c000000e543000000335dc000000c7e700000031d9c000000c5670000002dddc000000b57f0000002d5dc000000b567000000295dc000000a5670000002559c0000008f77000000237dc0000008d7f000000235dc0000008777
|2=>0x42959c000010957f000004215fc0000108567000004017fc000010056f0000032159c00000c0577000002277dc0000088df7000002235dc000008877700000221d9c00000885770000022159c00000805770000020159c00000800a100000200184000006ad77000001a15dc0000064d770000013d5dc000004cd77000001295dc0000049567000001235dc000004857f000001215dc0000048567000001211e00000048068
|3=>0x100575c000040057700000f21ddc000038057f00000da15dc000032c76700000b215fc00002c1f7700000b015fc0000289f7700000a277dc0000289d7700000a255dc000028877700000a21d9c00002885f700000a215dc000028856700000a017dc00002805e7000009215fc00002485770000092159c000020a5770000082559c00002085770000082159c00001c8577000006015fc000014c57700000521ddc00001287e7
|4=>0x800d79c0002003567000080095dc0002002567000080091d00002002464000080015dc000180857700001a2d5dc0000681d77000018235dc0000608577000018035dc000048a577000012215dc000044f577000011215dc000044457f0000110d5fc00004405770000102d5dc000040a577000010255dc0000409567000010237dc0000408d77000010215fc0000408577000010195dc00004045770000100d5fc0000402577
|5=>0x101215dc0004044f77000101135dc000404477700010109fdc000404157f000101055bc0004040df7000101035fc0004040d7700010101ddc00040405f7000101015dc000400957f000100235fc0004008d77000100217dc00040085770001002159c0004003df70001000d5dc00020815670000812159c000202b7770000803d59c000200e5670000802d5dc000200a5770000802959c000200a464000080215dc0002008567
|6=>0x119055dc0004443d77000111097dc000440b577000110255fc000440857700010c215dc00042c9d7700010b075dc00042c057700010a215dc0004263777000108ad5dc0004180d7f00010421ddc0004108660000104215fc0004108577000103037fc00040c0d7f000103015fc0004088d77000102215dc0004084d7f000101835dc0004060777000101315fc000404b577000101255fc0004048dff000101237dc000404857f
|7=>0x411215dc00104035d70004100d5dc00104005770004012b5dc0010049577000401035fc00100285f7000400a15dc001000f577000400335dc0010008d770004000f59c0010000df700030421dfc000c04877f000280add9c000862b57700020e21ddc000822b577000200b159c000802b567000200a1d9c000800c56700020021d9c00080085770002002159c00080000500001900959c00060035770001800d59c000468bd77
|8=>0x1202b5d9c004806cd77001201395dc004804c577001201295dc0048048577001200b1f9c004802b7670010082159c004014c77700100421dfc004010857f001003215dc00400485770010002959c0040008d770010002159c0040000577000840215dc002000857700060031c9c0014600df700050b275dc0014289577000501135dc0014020d770005000f7dc0014003d7700041a215dc0010641d77000418097dc001044a5f7
|9=>0x4005a15dc010014c57f004004215fc0100068d77004000b35dc010002c567004000a979c01000287e7004000a159c010000c577004000297fc010000a567004000255fc0100008d77004000215fc0100003d6700200a255dc0080008577002000015dc005840857700160133fdc005204857700140133ddc0050049577001401215dc005002877700140039ddc00500085770014002014000482ad567001207b15dc0048168777
|10=>0x100002559c0400008d7f010000215dc0400008567010000097dc04000025e70080002159c0158068f77005601a1ddc014812c5770052001178c0144027d77005008adddc014002f577005000b1f9c014000b577005000215dc01400080c0004411255dc0110068df7004400ab5dc01080297770041098dddc01041c057f004101ab7dc0104067d77004101115dc0104040577004008ad5dc0100223567004008237dc010016a57f
|11=>0x10108255dc040410057f010103015dc0404040d77010101015dc0404008d7f0100820579c04020095770100802559c0402008777010080215dc0402008567010080015dc0400409577010010215fc04000895f7010002255dc04000894e0010002247dc04000890e40100022159c04000825f7010002057dc04000815e7010002055dc0400081567010002053c004000810f4010001215dc040000e567010000297dc040000a577
|12=>0x204002d5dc0810008df7020140335dc0804408d77020103235dc08040285f702010033ddc0804008d77020100215dc080200b577020018215dc080040b5f7020010295dc08000485770200002d7dc080000b577020000237dc0800008567014000295fc044a0085770110002159c041204ad77010480395dc041200b577010480015dc041004ed770104002b5dc0410002d77010400037dc0406009577010180215fc04044085ff
|13=>0x84010a95dc210002a5770840002d5dc2010208777080018215dc2000228577080008255dc200010b577080000395dc2000000100040800215dc102000847704020031fdc0c120085770301003b5dc0c0200a577030080255dc0c002885770300002b7dc0c0000ad77030000255dc0914040df70245000379c0904040d77024008297dc090000a5f7021401215dc0850028577021000215dc0814040d770204022b5dc0810048f77
|14=>0x2010800c7e780160031fdd2000289577440740335dd0818008577420100335dd0800008d77404200295dd0040008d7740060431fdd001800cd7721520031f9c8108208567201202b159c8048048577201003215dc804002857720000ab559c8000288567200008a159c404800c7e70a4018295dc280460957708560039fdc211060e5770841102d5dc210060a777
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>0x180c86e040a0042c0318844020d008043c00
|9,0=>0x4202053552806aa87a136d21e6ed1b204c195006811100c1fde6a04ccd9785171c9086258610ca2261aa1084d463648a207211281c6902908046a21b9c0e272694ca30d210313446016394019293909b6d406ceeae621b6c0f30038cc34e58b8d0c18388a85d052ae4ecb02804086465396a92644eb809ac626ac820cc5c32d44fdb61e0989c2fb488c206812c38a242
|9,1=>0x1fd0b050547c822b964e78e13020cd2e1d1e0bf1273084cabe0989f161832b95267e5653e5aad23995770d0bae510e813bd51c6754a66840b569408050a72601fc6
|10,0=>0x9376ad72c7beb776ce3a1268ab7cee1052d73bbff72a65054ae2830d57e5e9fe5aa966f9ec8d16a630d4add4caa4b1e7dd12d09cf2296f2a83561b789171aa713ed86ba66752ba1b10c79d99c5586851c76e9ce95d80dbc7575bb3be04328c11d98b568434318f657caa0d042ba96fc0840ca6ec22c84a206b11caa1e0925a178e61d0d481e5cfc9b2d96fda5a5b0cee
|10,1=>0x29214e7256e3279c70af5d4557f2286ba747df8a64e39ac3f0a553abb657ecd0d296352ec28a7990accc74b6be486f52a841df597ad6d0a90a02adf5d437b1a08686c21521c2d8d5d25d265b0772e10c087d606a0f448f29456e119fa67c8b9c5a7051e29b6c825c075d0901701514a9bb2a3c82e19a854ea89c8dc92e8d37c6e8c569540a0f70be22d0f21bdd303453
|10,2=>0x36d214c50433f37b71be7c2a94a803fe050e78ef225e445680d5eb8684596a59397dacdd4eda2921afb9452d76e19a8e44f746b76c7e7472dc709498d3274a0a85286a30fa6d7210436a8012f4b15421f6913451c6712c2c4277142b
|11,0=>0x421a1c50c988c582519e94050bba01a75a2b82c10d69d7fa00db03447b108a443c919ebd1412678b49e5dcc5a2c4c14e0f4a234cfd11d874bc02d8844b02b8673d989ce306fcf085a21bde50da79fd65d3366cb4488a44811a7ad08fa68e1d396eab4440620d0683b9537f10c3cd2963c340710ec8a0719cddc39b7ad59839095b360aa92
|12,0=>0x9e1a0d02442330d06834070f8685806
|13,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 42 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_253 12 roots_253 ops++addP pm 2 dom_223 11 roots_223 ops++addP pm 3 dom_111 7 roots_111 ops++addP pm 4 dom_239 10 roots_239 ops++addP pm 5 dom_191 11 roots_191 ops++addP pm 6 dom_247 11 roots_247 ops++addP pm 7 dom_95 9 roots_95 ops++addP pm 8 dom_251 12 roots_251 ops++addP pm 9 dom_63 9 roots_63 ops++addP pm 10 dom_127 11 roots_127 ops++addP pm 11 dom_207 8 roots_207 ops++addP pm 12 dzo_247_8 8 roots_247 ops++addP pm 13 dzo_215_8 7 roots_215 ops++addP pm 14 dom_159 9 roots_159 ops++addP pm 15 dom_175 9 roots_175 ops++addP pm 16 dzo_190_64 7 roots_190 ops++addP pm 17 dom_183 8 roots_183 ops++addP pm 18 dzo_175_16 7 roots_175 ops++addP pm 19 dom_215 8 roots_215 ops++addP pm 20 dom_47 6 roots_47 ops++addP pm 21 dzo_119_8 7 roots_119 ops++addP pm 22 dom_231 7 roots_231 ops++addP pm 23 dzo_171_4 6 roots_171 ops++addP pm 24 dzo_235_16 7 roots_235 ops++addP pm 25 dom_119 7 roots_119 ops++addP pm 26 dzo_239_16 8 roots_239 ops++addP pm 27 dzo_191_64 8 roots_191 ops++addP pm 28 dzo_47_16 6 roots_47 ops++addP pm 29 dzo_203_4 6 roots_203 ops++addP pm 30 dzo_175_64 7 roots_175 ops++addP pm 31 dom_237 9 roots_237 ops++addP pm 32 dzo_87_8 6 roots_87 ops++addP pm 33 dzo_245_8 7 roots_245 ops++addP pm 34 dom_87 6 roots_87 ops++addP pm 35 dzo_111_16 7 roots_111 ops++addP pm 36 dzo_187_64 7 roots_187 ops++addP pm 37 dom_167 6 roots_167 ops++addP pm 38 dzo_189_64 7 roots_189 ops++addP pm 39 dom_151 6 roots_151 ops++addP pm 40 dom_139 5 roots_139 ops++addP pm 41 dom_31 5 roots_31 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_247_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_215_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_190_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_175_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_119_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_171_4_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_235_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_239_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_191_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_203_4_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_175_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_87_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_245_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_111_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_187_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_189_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_31 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 186 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 58 128 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 186 → Z 9 i = true := (range_split z9_0 z9_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 256 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_256 : ∀ i, 256 ≤ i → i < 338 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 82 256 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 338 → Z 10 i = true := (range_split z10_0 (range_split z10_128 z10_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 118 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 118 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 14 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 14 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [7, 2] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.or, inputs := [1, 0] }, { op := GateOp.or, inputs := [6, 9] }, { op := GateOp.or, inputs := [2, 11] }, { op := GateOp.or, inputs := [5, 11] }, { op := GateOp.or, inputs := [12, 0] }, { op := GateOp.and, inputs := [10, 13] }, { op := GateOp.and, inputs := [8, 14] }, { op := GateOp.and, inputs := [15, 4] }, { op := GateOp.and, inputs := [3, 7] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52572_aux

theorem PEqualNP.Outside.L_meta_52572 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52572_aux.main
