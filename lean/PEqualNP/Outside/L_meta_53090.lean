import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_53090_aux
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
def dom_15 : Nat := 0xffff
def goal_15 : Nat := 0xeea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0
def roots_15 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_21 : Nat := 0x330033
def goal_21 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_21 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_23 : Nat := 0xff00ff
def goal_23 : Nat := 0xfefea0a0fefea0a0fefea0a0fefea0a0fefea0a0fefea0a0fefea0a0fefea0a0
def roots_23 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfafaaaa0fafaaaa0fafaaaa0fafaaaa0fafaaaa0fafaaaa0fafaaaa0fafaaaa0
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_30 : Nat := 0x55555555
def goal_30 : Nat := 0xfcfccc00fcfccc00fcfccc00fcfccc00fcfccc00fcfccc00fcfccc00fcfccc00
def roots_30 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfefeeea0fefeeea0fefeeea0fefeeea0fefeeea0fefeeea0fefeeea0fefeeea0
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_37 : Nat := 0x3300000033
def goal_37 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0
def roots_37 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_39 : Nat := 0xff000000ff
def goal_39 : Nat := 0xfefefefea0a0a0a0fefefefea0a0a0a0fefefefea0a0a0a0fefefefea0a0a0a0
def roots_39 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

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
def goal_45 : Nat := 0xfffafffaaaa0aaa0fffafffaaaa0aaa0fffafffaaaa0aaa0fffafffaaaa0aaa0
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xfffcfffccc00cc00fffcfffccc00cc00fffcfffccc00cc00fffcfffccc00cc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfffefffeeea0eea0fffefffeeea0eea0fffefffeeea0eea0fffefffeeea0eea0
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafafafafafaa0a0fafafafafafaa0a0fafafafafafaa0a0fafafafafafaa0a0
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefefefefea0a0fefefefefefea0a0fefefefefefea0a0fefefefefefea0a0
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccffcccccccc00ffccffcccccccc00ffccffcccccccc00ffccffcccccccc00
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffeeeeeeee00ffeeffeeeeeeee00ffeeffeeeeeeee00ffeeffeeeeeeee00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_60 : Nat := 0x1111111111111111
def goal_60 : Nat := 0xfff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000
def roots_60 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafffafafaaaa0fffafffafafaaaa0fffafffafafaaaa0fffafffafafaaaa0
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcfffcfcfccc00fffcfffcfcfccc00fffcfffcfcfccc00fffcfffcfcfccc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefffefefeeea0fffefffefefeeea0fffefffefefeeea0fffefffefefeeea0
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_69 : Nat := 0x330000000000000033
def goal_69 : Nat := 0xfafafafafafafafaa0a0a0a0a0a0a0a0fafafafafafafafaa0a0a0a0a0a0a0a0
def roots_69 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0]

def dom_71 : Nat := 0xff00000000000000ff
def goal_71 : Nat := 0xfefefefefefefefea0a0a0a0a0a0a0a0fefefefefefefefea0a0a0a0a0a0a0a0
def roots_71 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffeeffeeffeeffeeee00ee00ee00ee00ffeeffeeffeeffeeee00ee00ee00ee00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfffafffafffafffaaaa0aaa0aaa0aaa0fffafffafffafffaaaa0aaa0aaa0aaa0
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_78 : Nat := 0x55550000000000005555
def goal_78 : Nat := 0xfffcfffcfffcfffccc00cc00cc00cc00fffcfffcfffcfffccc00cc00cc00cc00
def roots_78 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfffefffefffefffeeea0eea0eea0eea0fffefffefffefffeeea0eea0eea0eea0
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfafafafafafafafafafaa0a0fafaa0a0fafafafafafafafafafaa0a0fafaa0a0
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfefefefefefefefefefea0a0fefea0a0fefefefefefefefefefea0a0fefea0a0
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffeeffeeffeeffeeeeeeee00eeeeee00ffeeffeeffeeffeeeeeeee00eeeeee00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfff0fff0fff0fff0f0f00000f0f00000fff0fff0fff0fff0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffafffafffafffafafaaaa0fafaaaa0fffafffafffafffafafaaaa0fafaaaa0
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffcfffcfffcfffcfcfccc00fcfccc00fffcfffcfffcfffcfcfccc00fcfccc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffefffefffefffefefeeea0fefeeea0fffefffefffefffefefeeea0fefeeea0
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_97 : Nat := 0x3000000030000000300000003
def goal_97 : Nat := 0xffffffffaaaaaaaaaaaaaaaa00000000ffffffffaaaaaaaaaaaaaaaa00000000
def roots_97 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_100 : Nat := 0x11000000110000001100000011
def goal_100 : Nat := 0xfffffffff0f0f0f0f0f0f0f000000000fffffffff0f0f0f0f0f0f0f000000000
def roots_100 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfffffffffafafafafafafafaa0a0a0a0fffffffffafafafafafafafaa0a0a0a0
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfffffffffefefefefefefefea0a0a0a0fffffffffefefefefefefefea0a0a0a0
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_104 : Nat := 0x101000001010000010100000101
def goal_104 : Nat := 0xffffffffff00ff00ff00ff0000000000ffffffffff00ff00ff00ff0000000000
def roots_104 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffffaaffaaffaaffaaaa00aa00ffffffffffaaffaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffffccffccffccffcccc00cc00ffffffffffccffccffccffcccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffffeeffeeffeeffeeee00ee00ffffffffffeeffeeffeeffeeee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfffffffffff0fff0fff0fff000000000fffffffffff0fff0fff0fff000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffffffffffafffafffafffaaaa0aaa0fffffffffffafffafffafffaaaa0aaa0
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffffffffffcfffcfffcfffccc00cc00fffffffffffcfffcfffcfffccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffffffffffefffefffefffeeea0eea0fffffffffffefffefffefffeeea0eea0
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffeeeeeeeeeeeeeeeeeeee0000ffffffffeeeeeeeeeeeeeeeeeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffffffff0f0f0f0f0f0f0f0f0f00000fffffffff0f0f0f0f0f0f0f0f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffafafafafafafafafafaa0a0fffffffffafafafafafafafafafaa0a0
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffcfcfcfcfcfcfcfcfcfc0000fffffffffcfcfcfcfcfcfcfcfcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffefefefefefefefefefea0a0fffffffffefefefefefefefefefea0a0
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffaaffaaffaaffaaaaaaaa00ffffffffffaaffaaffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffccffccffccffcccccccc00ffffffffffccffccffccffcccccccc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffeeffeeffeeffeeeeeeee00ffffffffffeeffeeffeeffeeeeeeee00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffffffff0fff0fff0fff0f0f00000fffffffffff0fff0fff0fff0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffafffafffafffafafaaaa0fffffffffffafffafffafffafafaaaa0
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffcfffcfffcfffcfcfccc00fffffffffffcfffcfffcfffcfcfccc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffefffefffefffefefeeea0fffffffffffefffefffefffefefeeea0
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
def goal_141 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeeea0eea0eea0eea0eea0eea0eea0eea0
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaafafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xffffccccffffccccffffccccffffccccfcfc0000fcfc0000fcfc0000fcfc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeefefea0a0fefea0a0fefea0a0fefea0a0
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffcccccccc00cccccc00cccccc00cccccc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeeeeeee00eeeeee00eeeeee00eeeeee00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xffffff00ffffff00ffffff00ffffff00f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xffffffaaffffffaaffffffaaffffffaafafaaaa0fafaaaa0fafaaaa0fafaaaa0
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xffffffccffffffccffffffccffffffccfcfccc00fcfccc00fcfccc00fcfccc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xffffffeeffffffeeffffffeeffffffeefefeeea0fefeeea0fefeeea0fefeeea0
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaafafafafaa0a0a0a0fafafafaa0a0a0a0
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xffffffffccccccccffffffffccccccccfcfcfcfc00000000fcfcfcfc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeefefefefea0a0a0a0fefefefea0a0a0a0
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffffccffccffffffffffccffccffccffcccc00cc00ffccffcccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeee00ee00ffeeffeeee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xffffffffff00ff00ffffffffff00ff00fff0fff000000000fff0fff000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xffffffffffaaffaaffffffffffaaffaafffafffaaaa0aaa0fffafffaaaa0aaa0
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xffffffffffccffccffffffffffccffccfffcfffccc00cc00fffcfffccc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xffffffffffeeffeeffffffffffeeffeefffefffeeea0eea0fffefffeeea0eea0
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffffaaaaffffffffffffaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffeeeeffffffffffffeeeeeeeeeeeeeeee0000eeeeeeeeeeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xffffffffffffaaaaffffffffffffaaaafafafafafafaa0a0fafafafafafaa0a0
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xffffffffffffccccffffffffffffccccfcfcfcfcfcfc0000fcfcfcfcfcfc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xffffffffffffeeeeffffffffffffeeeefefefefefefea0a0fefefefefefea0a0
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffffffffffff00ffffffffffffff00ff00ff0000000000ff00ff0000000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffffaaffffffffffffffaaffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffffccffffffffffffffccffccffcccccccc00ffccffcccccccc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffeeffffffffffffffeeffeeffeeeeeeee00ffeeffeeeeeeee00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xffffffffffffff00ffffffffffffff00fff0fff0f0f00000fff0fff0f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xffffffffffffffaaffffffffffffffaafffafffafafaaaa0fffafffafafaaaa0
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xffffffffffffffccffffffffffffffccfffcfffcfcfccc00fffcfffcfcfccc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xffffffffffffffeeffffffffffffffeefffefffefefeeea0fffefffefefeeea0
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaafafafafafafafafaa0a0a0a0a0a0a0a0
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xffffffffffffffffccccccccccccccccfcfcfcfcfcfcfcfc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeefefefefefefefefea0a0a0a0a0a0a0a0
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xffffffffffffffffff00ff00ff00ff00fff0fff0fff0fff00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xffffffffffffffffffaaffaaffaaffaafffafffafffafffaaaa0aaa0aaa0aaa0
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xffffffffffffffffffccffccffccffccfffcfffcfffcfffccc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xffffffffffffffffffeeffeeffeeffeefffefffefffefffeeea0eea0eea0eea0
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffeeeeffffeeeeeeeeeeeeeeeeeeeeeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xffffffffffffffffffffccccffffccccfcfcfcfcfcfcfcfcfcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xffffffffffffffffffffeeeeffffeeeefefefefefefefefefefea0a0fefea0a0
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffffffffffffffffffff00ffffff00ff00ff00ff00ff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffffccffffffccffccffccffccffcccccccc00cccccc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffeeffffffeeffeeffeeffeeffeeeeeeee00eeeeee00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xffffffffffffffffffffff00ffffff00fff0fff0fff0fff0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xffffffffffffffffffffffccffffffccfffcfffcfffcfffcfcfccc00fcfccc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xffffffffffffffffffffffeeffffffeefffefffefffefffefefeeea0fefeeea0
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xffffffffffffffffffffffff00000000fffffffff0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xffffffffffffffffffffffffaaaaaaaafffffffffafafafafafafafaa0a0a0a0
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xffffffffffffffffffffffffeeeeeeeefffffffffefefefefefefefea0a0a0a0
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffffffffffff00ff00ffffffffff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffffccffccffffffffffccffccffccffcccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffeeffeeffffffffffeeffeeffeeffeeee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xffffffffffffffffffffffffff00ff00fffffffffff0fff0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xffffffffffffffffffffffffffaaffaafffffffffffafffafffafffaaaa0aaa0
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xffffffffffffffffffffffffffccffccfffffffffffcfffcfffcfffccc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xffffffffffffffffffffffffffeeffeefffffffffffefffefffefffeeea0eea0
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffffffccccffffffffcccccccccccccccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffffffeeeeffffffffeeeeeeeeeeeeeeeeeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xffffffffffffffffffffffffffff0000fffffffff0f0f0f0f0f0f0f0f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xffffffffffffffffffffffffffffccccfffffffffcfcfcfcfcfcfcfcfcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xffffffffffffffffffffffffffffeeeefffffffffefefefefefefefefefea0a0
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffffffffffffffffffff00ffffffffff00ff00ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffffffccffffffffffccffccffccffcccccccc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffffeeffffffffffeeffeeffeeffeeeeeeee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xffffffffffffffffffffffffffffff00fffffffffff0fff0fff0fff0f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xffffffffffffffffffffffffffffffaafffffffffffafffafffafffafafaaaa0
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xffffffffffffffffffffffffffffffccfffffffffffcfffcfffcfffcfcfccc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xffffffffffffffffffffffffffffffeefffffffffffefffefffefffefefeeea0
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_21
def pG:List (Nat×Nat):=[(1,5),(1,17),(4,5),(4,20),(16,17),(16,20)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3f
def xsM:=roots_21.map (·&&&dom_21)
def gM:=goal_21&&&dom_21
def NN:Nat→Nat
|2=>1
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|2,0=>0xd83d3
|3,0=>0xd83d3
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x330000c000c220022
|_,_=>0
def sP:Nat→Nat
|0=>0x924
|_=>0
def sO:Nat→Nat→Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wAt:=mkWire dB 3 22 0x3fffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_21 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_21 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_21==dom_21)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_21 gM v ys):RunD true dom_21 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_21 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_21 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_21 gM s xsM):False:=by
  have hmin:2≤s:=by have hl:=run_len h;change 3≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_21 roots_21 goal_21 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_21
theorem lowS_21:Lower true dom_21 roots_21 goal_21 4:=S_21.noCircuit
def isoMvS_37:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_37:Lower true dom_37 roots_37 goal_37 4:=lower_iso_b isoMvS_37 (by decide +kernel) lowS_21
def isoMvS_41:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_41:Lower true dom_41 roots_41 goal_41 4:=lower_iso_b isoMvS_41 (by decide +kernel) lowS_21
def isoMvS_42:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_42:Lower true dom_42 roots_42 goal_42 4:=lower_iso_b isoMvS_42 (by decide +kernel) lowS_21
def isoMvS_69:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_69:Lower true dom_69 roots_69 goal_69 4:=lower_iso_b isoMvS_69 (by decide +kernel) lowS_21
def isoMvS_97:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_97:Lower true dom_97 roots_97 goal_97 4:=lower_iso_b isoMvS_97 (by decide +kernel) lowS_21
def isoMvS_100:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_100:Lower true dom_100 roots_100 goal_100 4:=lower_iso_b isoMvS_100 (by decide +kernel) lowS_21
def isoMvS_104:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_104:Lower true dom_104 roots_104 goal_104 4:=lower_iso_b isoMvS_104 (by decide +kernel) lowS_21
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_21
def isoMvS_138:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_138:Lower true dom_138 roots_138 goal_138 4:=lower_iso_b isoMvS_138 (by decide +kernel) lowS_21
namespace S_15
def pG:List (Nat×Nat):=[(1,5),(1,9),(2,10),(3,7),(3,11),(4,5),(6,7),(6,14),(8,9),(8,10),(12,13),(12,14)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_15.map (·&&&dom_15)
def gM:=goal_15&&&dom_15
def NN:Nat→Nat
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x3d209
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00f0f0ccccaaaa
|_,_=>0
def sP:Nat→Nat
|0=>0xe4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|_,_=>0
def wAt:=mkWire dB 4 16 0xffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_15 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_15 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_15==dom_15)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_15 gM v ys):RunD true dom_15 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_15 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_15 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_15 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_15 roots_15 goal_15 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_15
theorem lowS_15:Lower true dom_15 roots_15 goal_15 4:=S_15.noCircuit
theorem lowS_23:Lower true dom_23 roots_23 goal_23 5:=lower_slice_b [(0xcc00cc,16,18)] (by decide +kernel) lowS_21
theorem lowS_43:Lower true dom_43 roots_43 goal_43 5:=lower_slice_b [(0xa0a00000a0a,8,9)] (by decide +kernel) lowS_42
namespace S_101
def pG:List (Nat×Nat):=[(1,5),(1,33),(1,65),(4,5),(4,36),(4,68),(32,33),(32,36),(32,96),(64,65),(64,68),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_101.map (·&&&dom_101)
def gM:=goal_101&&&dom_101
def NN:Nat→Nat
|3=>3
|4=>8
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x4b39d4241c2d8fb
|4,0=>0x6e072446d041ec83cb2e377251c8ea1343c05b27
|5,0=>0x774c23bd7a224c3
|6,0=>0x774c2
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc000000c0000000cc000000c00000000330000000000000030440000004400000040000000433000000330000003300000030440000004400000044000000003000000030000000200000002cc000000cc000000cc000000000000000000000003300000032cc00000000000000c8000000022000000220000002200000022c0000000c0000000c0000000c33000000330000000000000000cc00000000000000cc000000032000000320000003200000032cc000000cc000000c0000000c33000000330000002200000022
|_,_=>0
def sP:Nat→Nat
|0=>0x35643564f356431564356e4356d4c3564356b432504356a43216493506835675643210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x21022004
|4,0=>0x5eaa952aa0536a5948a8c5
|5,0=>0xf91cab45
|6,0=>0x424
|_,_=>0
def wAt:=mkWire dB 16 102 0x3fffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x355516459554595464d164551
|_=>0
def oO:Nat→Nat→Nat
|3,0=>2
|4,0=>0x62004222
|5,0=>0x9181
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfb96530
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>1
|4,0=>0x614
|5,0=>0x176
|6,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_100 4 roots_100 ops++addP pm 1 dom_97 4 roots_97 ops++addP pm 2 dom_37 4 roots_37 ops++addP pm 3 dom_69 4 roots_69 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_101 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_100 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_37 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_69 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_100 4 s (0,roots_100.map (·&&&dom_100)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_101 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_100 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_101==dom_101)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_101 gM v ys):RunD true dom_101 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_101 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_101 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_101 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_101 roots_101 goal_101 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_101
theorem lowS_101:Lower true dom_101 roots_101 goal_101 7:=S_101.noCircuit
def isoMvS_29:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_29:Lower true dom_29 roots_29 goal_29 5:=lower_iso_b isoMvS_29 (by decide +kernel) lowS_23
def isoMvS_30:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_30:Lower true dom_30 roots_30 goal_30 4:=lower_iso_b isoMvS_30 (by decide +kernel) lowS_15
def isoMvS_39:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_39:Lower true dom_39 roots_39 goal_39 5:=lower_iso_b isoMvS_39 (by decide +kernel) lowS_23
def isoMvS_45:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_45:Lower true dom_45 roots_45 goal_45 5:=lower_iso_b isoMvS_45 (by decide +kernel) lowS_43
def isoMvS_46:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_46:Lower true dom_46 roots_46 goal_46 5:=lower_iso_b isoMvS_46 (by decide +kernel) lowS_23
def isoMvS_53:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_53:Lower true dom_53 roots_53 goal_53 5:=lower_iso_b isoMvS_53 (by decide +kernel) lowS_43
def isoMvS_57:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_23
def isoMvS_58:List (Nat×Nat):=[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 5:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_23
def isoMvS_60:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_60:Lower true dom_60 roots_60 goal_60 4:=lower_iso_b isoMvS_60 (by decide +kernel) lowS_15
def isoMvS_71:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_71:Lower true dom_71 roots_71 goal_71 5:=lower_iso_b isoMvS_71 (by decide +kernel) lowS_23
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_43
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 5:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_43
def isoMvS_78:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_78:Lower true dom_78 roots_78 goal_78 5:=lower_iso_b isoMvS_78 (by decide +kernel) lowS_23
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_43
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 4:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_15
def isoMvS_105:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 7:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_101
def isoMvS_106:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 7:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_101
def isoMvS_108:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 5:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_43
def isoMvS_116:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_23
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_43
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_23
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_43
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_23
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_43
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_43
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 4:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_15
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 5:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_43
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_23
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 7:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_101
def isoMvS_172:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 5:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_23
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_43
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 5:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_23
def isoMvS_197:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 5:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_43
def isoMvS_198:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_23
def isoMvS_201:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 7:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_101
def isoMvS_204:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 5:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_23
def isoMvS_216:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 5:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_23
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 7:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_101
def isoMvS_228:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 5:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_43
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 7:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_101
theorem lowS_31:Lower true dom_31 roots_31 goal_31 6:=lower_slice_b [(0xcccccccc,8,10)] (by decide +kernel) lowS_29
namespace S_47
def pG:List (Nat×Nat):=[(1,5),(1,9),(1,33),(2,10),(2,34),(3,7),(3,11),(3,35),(4,5),(4,36),(6,7),(6,14),(6,38),(8,9),(8,10),(8,40),(12,13),(12,14),(12,44),(32,33),(32,34),(32,36),(32,40)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_47.map (·&&&dom_47)
def gM:=goal_47&&&dom_47
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xa2a89
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff00000000ff000000ff00f0f00000f0f0cccc0000ccccaaaa0000aaaa
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 48 0xffffffffffff
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
addP pm 0 dom_46 5 roots_46 ops++addP pm 1 dom_45 5 roots_45 ops++addP pm 2 dom_43 5 roots_43 ops++addP pm 3 dom_39 5 roots_39 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_47 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_39 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_46 5 s (0,roots_46.map (·&&&dom_46)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_47 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_46 h
def symsG:List (List (Nat×Nat)):=[[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_47==dom_47)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_47 gM v ys):RunD true dom_47 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_47 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_47 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_47 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_47 roots_47 goal_47 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_47
theorem lowS_47:Lower true dom_47 roots_47 goal_47 7:=S_47.noCircuit
theorem lowS_55:Lower true dom_55 roots_55 goal_55 6:=lower_slice_b [(0xcc00cc00cc00cc,16,18)] (by decide +kernel) lowS_53
theorem lowS_103:Lower true dom_103 roots_103 goal_103 8:=lower_slice_b [(0xcc000000cc000000cc000000cc,32,34)] (by decide +kernel) lowS_101
theorem lowS_107:Lower true dom_107 roots_107 goal_107 8:=lower_slice_b [(0xa0a00000a0a00000a0a00000a0a,8,9)] (by decide +kernel) lowS_106
theorem lowS_121:Lower true dom_121 roots_121 goal_121 8:=lower_slice_b [(0x3030000030300000303000003030000,1,17)] (by decide +kernel) lowS_105
def dzo_108_16:=0x11110000111100001111000011110000
def gzo_108_16:=0x11110000111000001110000010100000
def gsh_108_16:=0x1111000011100000111000001010
theorem lowS_zo_108_16_104:Lower true dzo_108_16 roots_108 gzo_108_16 5:=lower_iso_b (d1:=dom_108) (r1:=roots_108) (T1:=gsh_108_16) [(dom_108,16)] (by decide +kernel) (lower_slice_b (T:=gsh_108_16) [(0x1010000010100000101000001010,0,4)] (by decide +kernel) lowS_104)
namespace S_124
def pG:List (Nat×Nat):=[(4,20),(4,36),(4,68),(8,40),(8,72),(12,28),(12,44),(12,76),(16,20),(24,28),(24,56),(24,88),(32,36),(32,40),(32,96),(48,52),(48,56),(48,112),(64,68),(64,72),(64,96),(80,84),(80,88),(80,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_124.map (·&&&dom_124)
def gM:=goal_124&&&dom_124
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xe606a
|5,0=>0xeeefd
|6,0=>0x4f73
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x444444444444444444444444000000022002200220022002200220022002201111111100000000111111110000000088880000888800008888000088880004040404040404040404040404040404002200220022002200220022000000011111111111111110000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8ea1a3a84688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 125 0x1fffffffffffffffffffffffffffffff
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
addP pm 0 dom_116 5 roots_116 ops++addP pm 1 dom_92 4 roots_92 ops++addP pm 2 dzo_108_16 5 roots_108 ops++addP pm 3 dom_108 5 roots_108 ops++addP pm 4 dom_104 4 roots_104 ops++addP pm 5 dom_60 4 roots_60 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_124 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_108_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_60 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_116 5 s (0,roots_116.map (·&&&dom_116)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_124 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_116 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_124==dom_124)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_124 gM v ys):RunD true dom_124 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_124 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_124 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_124 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_124 roots_124 goal_124 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_124
theorem lowS_124:Lower true dom_124 roots_124 goal_124 7:=S_124.noCircuit
theorem lowS_155:Lower true dom_155 roots_155 goal_155 6:=lower_slice_b [(0xa0a0a0a0000000000000000000000000a0a0a0a,8,9)] (by decide +kernel) lowS_154
namespace S_233
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(8,9),(8,40),(8,72),(8,136),(32,33),(32,40),(32,96),(32,160),(64,65),(64,72),(64,96),(64,192),(128,129),(128,136),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffff
def xsM:=roots_233.map (·&&&dom_233)
def gM:=goal_233&&&dom_233
def NN:Nat→Nat
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x80eb7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x30300000000000003030000000000000303000000000000030300000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c020200000202000002020000020200000202000002020000020200000202c0c00000c0c000000000000000000000c0c00000c0c00000000000000030300000303000003030000030300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>5
|_,_=>0
def wAt:=mkWire dB 5 234 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_232 7 roots_232 ops++addP pm 1 dom_169 7 roots_169 ops++addP pm 2 dom_225 7 roots_225 ops++addP pm 3 dom_201 7 roots_201 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_233 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_201 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_232 7 s (0,roots_232.map (·&&&dom_232)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_233 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_232 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xffffffff00000000ffffffff00000000,96)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_233==dom_233)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_233 gM v ys):RunD true dom_233 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_233 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_233 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_233 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_233 roots_233 goal_233 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_233
theorem lowS_233:Lower true dom_233 roots_233 goal_233 9:=S_233.noCircuit
def isoMvS_59:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_59:Lower true dom_59 roots_59 goal_59 6:=lower_iso_b isoMvS_59 (by decide +kernel) lowS_55
def isoMvS_61:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 7:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_47
def isoMvS_62:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 6:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_31
def isoMvS_79:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_79:Lower true dom_79 roots_79 goal_79 7:=lower_iso_b isoMvS_79 (by decide +kernel) lowS_47
def isoMvS_87:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_iso_b isoMvS_87 (by decide +kernel) lowS_55
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 6:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_55
def isoMvS_93:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 7:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_47
def isoMvS_94:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 6:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_31
def isoMvS_109:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 8:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_107
def isoMvS_110:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 8:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_103
def isoMvS_115:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 6:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_55
def isoMvS_117:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 8:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_103
def isoMvS_118:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 6:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_55
def isoMvS_122:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 8:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_121
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 7:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_124
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 7:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_47
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 7:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_47
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 7:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_124
def isoMvS_167:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 7:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_47
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_107
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_103
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 8:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_121
def isoMvS_179:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 6:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_155
def isoMvS_181:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 6:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_155
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 6:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_55
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 8:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_103
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 8:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_103
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 6:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_31
def isoMvS_199:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 7:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_47
def isoMvS_203:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_107
def isoMvS_205:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 8:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_103
def isoMvS_206:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 8:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_121
def isoMvS_211:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 6:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_155
def isoMvS_214:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 6:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_55
def isoMvS_220:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 6:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_31
def isoMvS_229:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 8:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_107
def isoMvS_234:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 9:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_233
def isoMvS_236:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 8:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_103
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 8:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_103
def isoMvS_244:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 6:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_55
def isoMvS_248:List (Nat×Nat):=[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 8:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_121
namespace S_63
def pG:List (Nat×Nat):=[(1,5),(1,9),(1,17),(1,33),(2,10),(2,18),(2,34),(3,7),(3,11),(3,19),(3,35),(4,5),(4,20),(4,36),(6,7),(6,14),(6,22),(6,38),(8,9),(8,10),(8,40),(12,13),(12,14),(12,28),(12,44),(16,17),(16,18),(16,20),(24,25),(24,26),(24,28),(24,56),(32,33),(32,34),(32,36),(32,40),(48,49),(48,50),(48,52),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_63.map (·&&&dom_63)
def gM:=goal_63&&&dom_63
def NN:Nat→Nat
|5=>3
|6=>5
|7=>4
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xa725c4e21f4c8ee
|6,0=>0xc029aa84844d9a93ed612184e
|7,0=>0xb93537adc377e251fb9e
|8,0=>0xc6758
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfff0fff0fff0fff0ffffffffeeeeeeeefffffffffffff0f0ffaaffaaffaaffaaffffffffaaaaaaaaccccccccccccccccaaaaaaaaaaaaaaaa0f0f0f0f0f0f0a0affff0000ffff0000ffffffffffffaaaaffffffffffff0000ffffffff00000000ff00ff00ff00ff00f0f0f0f0f0f0f0f0eeeeeeeeeeeeeeee
|_,_=>0
def sP:Nat→Nat
|0=>0x36219836b2198432198a36219836e2198d362108c43219843210836b2104a21984a210432987543210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x31433006
|6,0=>0x2a746e758bb116
|7,0=>0x8aefd9c3b17
|8,0=>0x4c6
|_,_=>0
def wAt:=mkWire dB 15 64 0xffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa1634e1216616366163661284e16358d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>1
|6,0=>0x8171523212
|7,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x9f5cf2d0407001f587ec00c000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>1
|6,0=>0x4ad6
|7,0=>0x7db
|8,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_61 7 roots_61 ops++addP pm 1 dom_58 5 roots_58 ops++addP pm 2 dom_46 5 roots_46 ops++addP pm 3 dom_55 6 roots_55 ops++addP pm 4 dom_60 4 roots_60 ops++addP pm 5 dom_59 6 roots_59 ops++addP pm 6 dom_62 6 roots_62 ops++addP pm 7 dom_47 7 roots_47 ops++addP pm 8 dom_23 5 roots_23 ops++addP pm 9 dom_31 6 roots_31 ops++addP pm 10 dom_29 5 roots_29 ops++addP pm 11 dom_43 5 roots_43 ops++addP pm 12 dom_15 4 roots_15 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_63 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_23 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_15 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_61 7 s (0,roots_61.map (·&&&dom_61)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_63 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_61 h
def symsG:List (List (Nat×Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_63==dom_63)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_63 gM v ys):RunD true dom_63 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_63 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_63 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
namespace S_111
def pG:List (Nat×Nat):=[(1,5),(1,9),(1,33),(1,65),(2,10),(2,34),(2,66),(3,7),(3,11),(3,35),(3,67),(4,5),(4,36),(4,68),(6,7),(6,14),(6,38),(6,70),(8,9),(8,10),(8,40),(8,72),(12,13),(12,14),(12,44),(12,76),(32,33),(32,34),(32,36),(32,40),(32,96),(64,65),(64,66),(64,68),(64,72),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffff
def xsM:=roots_111.map (·&&&dom_111)
def gM:=goal_111&&&dom_111
def NN:Nat→Nat
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x93226
|9,0=>0x4f37e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff0000ffff0000ffff00000000ffff000000000000ffff00000000ff000000ff000000ff000000ff00f0f00000f0f00000f0f00000f0f0cccc0000cccc0000cccc0000ccccaaaa0000aaaa0000aaaa0000aaaaffff0000ffff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x58d11ac688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>7
|9,0=>0x76
|_,_=>0
def wAt:=mkWire dB 7 112 0xffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa1
|_=>0
def oO:Nat→Nat→Nat
|8,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 5
def pmP:Nat→Nat
|0=>0xfc0
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>1
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_110 8 roots_110 ops++addP pm 1 dom_109 8 roots_109 ops++addP pm 2 dom_107 8 roots_107 ops++addP pm 3 dom_103 8 roots_103 ops++addP pm 4 dom_79 7 roots_79 ops++addP pm 5 dom_47 7 roots_47 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_111 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_47 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_110 8 s (0,roots_110.map (·&&&dom_110)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_111 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_110 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_111==dom_111)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_111 gM v ys):RunD true dom_111 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_111 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_111 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_111 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_111 roots_111 goal_111 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_111
theorem lowS_111:Lower true dom_111 roots_111 goal_111 10:=S_111.noCircuit
theorem lowS_119:Lower true dom_119 roots_119 goal_119 9:=lower_slice_b [(0xcc00cc00cc00cc00cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_117
theorem lowS_123:Lower true dom_123 roots_123 goal_123 9:=lower_slice_b [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,8,9)] (by decide +kernel) lowS_122
def dzo_109_16:=0x33330000333300003333000033330000
def gzo_109_16:=0x33330000333200003332000032320000
def gsh_109_16:=0x3333000033320000333200003232
theorem lowS_zo_109_16_104:Lower true dzo_109_16 roots_109 gzo_109_16 6:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_16) [(dom_109,16)] (by decide +kernel) (lower_slice_b (T:=gsh_109_16) [(0x2222000022220000222200002222,0,1),(0x3030000030300000303000003030,0,4)] (by decide +kernel) lowS_104)
namespace S_125
def pG:List (Nat×Nat):=[(1,5),(1,9),(1,17),(1,33),(1,65),(4,5),(4,20),(4,36),(4,68),(8,9),(8,40),(8,72),(12,13),(12,28),(12,44),(12,76),(16,17),(16,20),(24,25),(24,28),(24,56),(24,88),(32,33),(32,36),(32,40),(32,96),(48,49),(48,52),(48,56),(48,112),(64,65),(64,68),(64,72),(64,96),(80,81),(80,84),(80,88),(80,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|5=>2
|6=>8
|7=>9
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x59fc442901
|6,0=>0xd2990bef0a73b4656002326f61fb640405d0401c
|7,0=>0xfc16eca6a8c9bfd7ca295fceb5d3c55ab7e4e09f4168a
|8,0=>0x74b3a397270f7ba
|9,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccc00000000888888880000000333333330000000033330000cccccccccccc0000cccccccccccc00033333333333333333333333322222222cccccccccccccccccccccccc000000033330000333300003333000033330000cccccccccccccccc00000000000000033333333333333333333333333330000cccccccc88888888cccccccc8888888b3003300330033003300330033003300cccccccc00000000cccccccc000000033333333333333333333000033330000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c33333333333333332222222222222222888888888888888888888888888888880330033003300330033003300220022
|_,_=>0
def sP:Nat→Nat
|0=>0xa6319856319c5a631975463197ba631975a63295a631f9c75a63195463215631e97ba632c5a31095a310956321edc7631975463287631975a310987632543210
|1=>0x5a6319b5a631954631975
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x65006
|6,0=>0x3863172b62561e71861260b7
|7,0=>0x7566e76776075975274a84463e6
|8,0=>0x8878267b7
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 16 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x165a9455546a579455516a5594551945525c6579455196a554aa559465155e51571b7945519552a95697945551465a96e959455c6de5196e959455
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0x5cd5248cf330c9318c42
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 10
def pmP:Nat→Nat
|0=>0x19f3cc965ce3e71734b9a440ff67db3bd9dccaf655b1af87cc2e6100038803c004000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40
|6,0=>0x79068730e1
|7,0=>0xaa2e5134da9
|8,0=>0x3d30
|9,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 8 roots_121 ops++addP pm 1 dom_124 7 roots_124 ops++addP pm 2 dom_77 5 roots_77 ops++addP pm 3 dom_45 5 roots_45 ops++addP pm 4 dom_61 7 roots_61 ops++addP pm 5 dom_109 8 roots_109 ops++addP pm 6 dom_93 7 roots_93 ops++addP pm 7 dom_60 4 roots_60 ops++addP pm 8 dom_117 8 roots_117 ops++addP pm 9 dzo_108_16 5 roots_108 ops++addP pm 10 dzo_109_16 6 roots_109 ops++addP pm 11 dom_29 5 roots_29 ops++addP pm 12 dom_92 4 roots_92 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_108_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_109_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_92 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 8 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_125==dom_125)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
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
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_slice_b [(0x50505050505050505050505050505050,16,20)] (by decide +kernel) lowS_122
def dzo_155_4:=0xf0f0f0f0000000000000000000000000f0f0f0f0
def gzo_155_4:=0xf0f0f0e0000000000000000000000000f0f0e0a0
def gsh_155_4:=0xf0f0f0e0000000000000000000000000f0f0e0a
theorem lowS_zo_155_4_138:Lower true dzo_155_4 roots_155 gzo_155_4 6:=lower_iso_b (d1:=dom_155) (r1:=roots_155) (T1:=gsh_155_4) [(dom_155,4)] (by decide +kernel) (lower_slice_b (T:=gsh_155_4) [(0xa0a0a0a0000000000000000000000000a0a0a0a,0,1),(0xf0f00000000000000000000000000000f0f0000,0,16)] (by decide +kernel) lowS_138)
namespace S_159
def pG:List (Nat×Nat):=[(1,5),(1,9),(1,17),(1,129),(2,10),(2,18),(2,130),(3,7),(3,11),(3,19),(3,131),(4,5),(4,20),(6,7),(6,14),(6,22),(6,134),(8,9),(8,10),(8,136),(12,13),(12,14),(12,28),(12,140),(16,17),(16,18),(16,20),(16,144),(24,25),(24,26),(24,28),(24,152),(128,129),(128,130),(128,136),(128,144),(132,133),(132,134),(132,140),(132,148)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_159.map (·&&&dom_159)
def gM:=goal_159&&&dom_159
def NN:Nat→Nat
|7=>2
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xb4128a773d
|8,0=>0x932a5
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000f0f0f0f0ffff0000000000000000000000000000ffff0000ff00ff00000000000000000000000000ff00ff0000000000000000000000000000000000f0f0f0f0cccccccc000000000000000000000000ccccccccaaaaaaaa000000000000000000000000aaaaaaaaffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2cc88b3a22c688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xcc06
|8,0=>0xc6
|_,_=>0
def wAt:=mkWire dB 8 160 0xffffffffffffffffffffffffffffffffffffffff
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
|0=>0xfefcf80
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>6
|8,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_158 7 roots_158 ops++addP pm 1 dom_157 7 roots_157 ops++addP pm 2 dom_155 6 roots_155 ops++addP pm 3 dom_151 7 roots_151 ops++addP pm 4 dom_143 7 roots_143 ops++addP pm 5 dom_31 6 roots_31 ops++addP pm 6 dzo_155_4 6 roots_155 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_159 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_155_4_138 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_158 7 s (0,roots_158.map (·&&&dom_158)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_159 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_158 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_159==dom_159)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_159 gM v ys):RunD true dom_159 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_159 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_159 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_183:Lower true dom_183 roots_183 goal_183 8:=lower_slice_b [(0xff000000ff0000000000000000000000ff000000ff0000,1,17)] (by decide +kernel) lowS_167
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_slice_b [(0xa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a,8,9)] (by decide +kernel) lowS_186
namespace S_189
def pG:List (Nat×Nat):=[(1,5),(1,9),(1,17),(1,33),(1,129),(4,5),(4,20),(4,36),(8,9),(8,40),(8,136),(12,13),(12,28),(12,44),(12,140),(16,17),(16,20),(16,144),(24,25),(24,28),(24,56),(24,152),(32,33),(32,36),(32,40),(32,160),(48,49),(48,52),(48,56),(48,176),(128,129),(128,136),(128,144),(128,160),(132,133),(132,140),(132,148),(132,164)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_189.map (·&&&dom_189)
def gM:=goal_189&&&dom_189
def NN:Nat→Nat
|4=>21
|5=>61
|6=>70
|7=>45
|8=>10
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xcea6fc42519505b78650728cf718f9690b3669d74d2e4458a53c40e3a7a836e5d3111a2e1082177b205c91809a0d7220bd2107813
|5,0=>0xe3007e11a3d9be4d1224cfd64cfb1ace42acc7c4caa4ac485abfc61b9419aca4fa406c9e8a99ca779335c8c2f7875a484ee1843c982982808207cdf47917c64c7c645d963ba961cfb5988f5762c52eb04dcab49ebc47d9c3a609382153357e2f6d02e75e2e5522e3292ce242bdb21d7611be271a0bd17b6515aeb13f5911ec80ee210c24c0a2c9085c70757205c38047fe0367c02e6502c7d
|6,0=>0xf2b4aec370e8262e2197e0cd7d9682d1918cffdecd367cc9d4c573ebede8b686ea8120a7c2e9facc9a34693b6c88848887e37e1947a1867608075df57529372f1e715e470ab16fc596a2d76847262e1b5db015d9145af23582ec54e9947afb47a7345d0d42a19423d53f9e73c7c13c0f73a30a38d6e376de3702733a4c2bcec2b4b72af6c27b862624c1b78c1729c152b312c59128d51261e10ac20ad5f0a7c1090eb057ed030be016160152a0037e
|7,0=>0xf4ae8ead9fc17ceb2a4bad97baa0e3a809aa58bea4cb495d048f52a8dbf08af7984dc3816ac7def979a127879c754c07369e61be9593b65894d57b2350dd7508394e54e4dceb4b6e9471163e479343e93399c2896821c7d2152217ec117c3311cdc116e710c9a0e023097ec04e600112a
|8,0=>0xead9fcf2a19dd359db9b8014067cf56463160ce360ace0daa1
|9,0=>0x3abd3
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccccccc00000000000000000000c8c8c8c8c8c8000332233223322332200000000000000003322332233203320cccccccc888888880000000000000000cccccccc8888888b33333333333333300000000000000003030303030303030cccccccccccccccc0000000000000000888888888080808333322223333222200000000000000003333222233332020cccccccccccc00000000000000000000cccccccccccc000333333330000000000000000000000003333333300000000cc88cc88cc88cc880000000000000000cc88cc88cc88cc8b03030303030303000000000000000003030303030303030cccccccccccccccc0000000000000000888888888888880333333332222222200000000000000003333333322202220cccc0000cccc00000000000000000000cccc0000cccc000330033003300330000000000000000003300330033003300cccccccccccccccc0000000000000000c8c8c8c8c8c8c8cb33333333333333300000000000000000000000000000000
|0,1=>0xcccccccccccccccc0000000000000000cccccccccccc000000000003333333300000000000000000000000033332222000000000000000000000000000000000c0c0c0c0c0c080b3333333333333330000000000000000222022202220222044444444444444440000000000000000444444444040404333333330000222200000000000000003333333300002222cccccccccccccccc0000000000000000cccccccc8888888803300330033003300000000000000000033003300220022cccccccccccccccc0000000000000000cccccccc0000888b33322223333222200000000000000003333222033332220c8c8c8c8c8c8c8c80000000000000000c8c8c8c8c8c8c0c333333330000333300000000000000003333333300002222cccccccccccccccc0000000000000000cccccccc000000033333333333322220000000000000000303030303030202088888888888888880000000000000000888888888888888b33333333333333300000000000000002222222222222222
|0,2=>0xcccccccc888888880000000000000000cccccccc8888000333333330000000000000000000000003333333302020202cccccccccccccccc0000000000000000080808080808080911111111111111100000000000000001111111111110000cccccccc00cc00880000000000000000cccccccc00cc008803300330033003300000000000000000033003300330022cc00cc00cc00cc880000000000000000cc00cc00cc00cc8800000003300330000000000000000000000000033003300cccccccccccccccc0000000000000000000000000000888830303030303030200000000000000000303030303030302cc88cc88cc88cc880000000000000000cc88cc88cc88cc0000000003333332200000000000000000000000033333322cccccccccccccccc0000000000000000ccccccccc0c0c0c222222222222222200000000000000002222222220202020cccccccccccccccc00000000000000000c0c0c0c0c0c080800033330000333300000000000000000000303200003032
|0,3=>0xcccccccc000000000000000000000000ccc8ccc83030303030300000000000000000000030303030303020200000000cc00cc88000000000000000000000000cc00cc8b33333333333333300000000000000003330333033303330000000000000000000000000000000000c0c0c0c0808080b3333333333333330000000000000000333333333333222288888888888888880000000000000000888888888888000333333333333330000000000000000003333333333333300c8c8c8c8c8c8c8c00000000000000000c8c8c8c8c8c8c8c003300330033002200000000000000000033003300330022cccccccc000000880000000000000000cccccccc0000008a22222222222222200000000000000002220222022202220000000000000cc880000000000000000000000000000cc8b3333333000033220000000000000000333333330000332200000000000088880000000000000000000000000000888911111111111110000000000000000001111111111111100
|0,4=>0x88880000000000000000000000000000000222222222222222200000000cc88cc88000000000000000000000000cc88cc8a2222222332233220000000000000000222222223322332200000000000000880000000000000000000000000000008b3333333333333330000000000000000333233323332333200000000cccccccc00000000000000000000000088888888000333300003333000000000000000000003333000032320000000000000000000000000000000008080808080808083030303030302020000000000000000030303030303020200000000000000000000000000000000cccccccccccc888b3333333000000000000000000000000333333330000222200000000000000000000000000000000cc00cc00cc00cc0000033330000333300000000000000000000323200003232cccccccccccc88880000000000000000cccccccccccc888a22222222222220000000000000000002222222222222200
|0,5=>0x4400440044004400000000000000000044004400440044033333333333333330000000000000000332233223322332200000000000000000000000000000000cc88cc88cc88cc8b33333333333333300000000000000003300330033003300cccccccccccccccc0000000000000000ccccccccccccc0c002200220022002200000000000000000022002200220022cccccccccccccccc0000000000000000008800880088008b33333333300330000000000000000003333333333003300cccccccccccccccc0000000000000000ccccccccc8c8c8c800000002222222200000000000000000000000022222222cccccccccccccccc0000000000000000000000008888888a2002200220022000000000000000000220022002200220044884488448844880000000000000000448844884488448b3333333332233220000000000000000333333333322332200cc00cc00cc00cc000000000000000000c800c800c800c911111111111111100000000000000001110111011101110
|0,6=>0x33003300332233220000000000000000330033003322332288888888888888880000000000000000cc88cc88cc88cc8b3332200333322000000000000000000333322003333220044cc44cc00000000000000000000000044cc44cc000000000330033002200220000000000000000003300330022002288888888888888880000000000000000008800880088008b3333333002200220000000000000000333333330022002200000000000000000000000000000000cccccccc8888888800000000000000000000000000000000000000022222222cccccccc000000000000000000000000cccccccc8888888800000000000000000000000000000000022002200220022000000000000cccc0000000000000000000000000000888b33333333333333300000000000000002200220022002200cccccccccccc00880000000000000000cccccccccccc008b33333333333000000000000000000003333333333332222
|_,_=>0
def sP:Nat→Nat
|0=>0x4188a40020182184110910088a1002010c228001f100891112086113c2498222744030e30e09043081b10581010024d0218404991844c092e08611105810c20246822a0049404308892608911100c70c20246820c146821e3000d06386001a0c10c162050202004880e182840608080
|1=>0x24402227400910086106220182028800d260c10118246820cc00095e08311002498202308ae260c10c2234403043168910086115a244021845608060861138255820c4400910188aa002548622a000910086114e244022298009041889e00244250c440231a0c10100251820244009
|2=>0x1e30880100a18c23084970418880126410c23044020d0000304308bf002440222f800904188bd0024a020c440080608610682410c22ec03a122010c22244020c41cb8123438600244026e440090c45b280025a820c440091a0808c00205021844008061c634001018218440096408311
|3=>0x184448804188c000244020c4658070246820c44008072810c220040304308c912646820c440091a0832c002010c232000946086102224682184088d260c10c8e7c48d041880926086118e2498223180091a08610123431130022892608311126410c20444990c44c0013101062200402
|4=>0x1234106220040304308d000646880608611827c4020c440091a0861100244020c4678082244022318019100c311300048d041a7001a0c3820d340090e083119a00403050c6118e246820c40880100c311300048804188b300349830430889041a61100246820c40019100c10c2224982
|5=>0x60864700244021846380b0341870c4400806086114402c0d061c300ae2018218440451220106220040304308d5100c10c226c00806f010122004030e1a9801220106229c0231a0c10c22004d21a0831100201821846880124c10622c4008061881130004a3043088012214820c4401f
|6=>0x2200688060808c00244020230880100c101195800804308c201804880418880100c3c3184448d041ad00100c35300201deba0831182249820c440091a1c106220048d0e08300100c3ddb818889340831100341820c46680100c143023088904188cd016c4880430880100c10c2364688
|7=>0x1220106236800807783820c4400806086102220186bf68008061c10620440080608311cc0328806083110020187041880012203820c44008061c106ac02c0d060831100201878618880100c106239000d260c106204469306083101220106238c008061c36270244070c440611220106
|8=>0x7b8106220040304188e232201820c4088070244020c4400807781062200403da0831100236020c4400304188eb0020187b8188801a4c1820c44008060a18c22644030418880124c106220040304188ea00201820c47480100c10c231c068100c1062203388060831100201820c42d00
|9=>0x201820c40880100c10623580080608311a8004880418880100c106236800806083119a004030e0831100201870d5001f122010622004880430880100c101184400910083119c00403bc0831022004030e083119a0068806083102200688060831000244020c40880100c1062158008
|10=>0x100c10622004030e08311004c4030418880100c106237c008060a1862202c080608311
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x6450bea16942aa8505096a119420a83c506ea0c9416a8285046a07940ca814501ea029402a8005
|5,0=>0x1cf6392c70d8deb1b76362c6ad8d2b1a05334c6518c731886304c5f18bb317062d6a5958afb15962a6c5358a3b1416276c4d5897b1296246c47588bb1116216c41587fb0f961e6c3b5873b0e161b6c355867b0c96186c2f585bb0b16156c29584fb0996126c235843b08160f6c1d5837b0696
|6,0=>0x6eeedc1db4bb6366b8ed599a8334b5688ecf5d9b3b306652ec8d98e3b15761ecc21d8132fb75e8ebb5d733ae065b2eb49d6632c5757ceae1958baaa7546ea71d4aba8e7510ca05d3d3a7374d8e995d2fb25874a2e929d22323d746ce8bdd143a226436e855907b2096406c7f94fbb9f073d2e789cee31d57
|6,1=>0x1cf3b986722ee315c2bb7e7
|7,0=>0x4d6799ef325a613cbc696af2b9e53449e892d123de443c8178f4f1d1a36446578bcf15de28b44b6888f0f5e1bb4307854d08de0e3c15781cf01de003bf977e30fad9f2b3dd87acef3dde43bc17774eecddd63ba57
|8,0=>0x28dbd147a1af419e7fbcf879e2f3a9e7234dd7
|9,0=>0x5226
|_,_=>0
def wAt:=mkWire dB 111 190 0x3fffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x42300450621222126450c0110010c01062100217044120906212221040518450c0110420c01220106212221100d220122010019220118460c0106212645120418450c01124626450c01124278442025100d22013e44062104451209062110cd121e04454644104518450c01100d3e4718450019222146440c01264512462027
|1=>0x15922230c0146471821043118450c010f530445044400c512462221062122210406184512460621320b1041182106210c0104c512460621222178471809003500192221124506210019062122210d061245062122010046062122210e230445100d0e23044518460c01062100452221320b1041220122210c01100106215045
|2=>0x18450c011339220306210c0104450403044606212221bf6904470446001d0e0304451245062100210445062122210445062122210e030445622112460621a42304352221040318450c01101e0621044512310c0101690c01044618460c01100d18460c0104210445464418210c01222104210445100518450c01010612450621
|3=>0x4031041220106210021043622218646040318460c01b421044600362221044622010621044604450c0122010447044604452201264610019c2122030445220106210445222304450421222104450403b8460401100110452201100110452201a8010445044404451209136906210446104518450c01100d18450c010c010606
|4=>0x4451001044704030421220122230444062104460e2304450569044604450444120106210c01062118450c0122030621044122010e2304451045220110452201100d22011046220105592223a80104441041220112090621044122018645040307510444a822044404010445002122210c01
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x44011000000000200000000000000000000000000000
|5,0=>0xa084c4000128888c0000000000000000211000078c0001d10d9000000000000006843220000b18508244000000000022200000000001c6000000034414600000002440000000000204000000000000000000000000000a60000000104000000
|6,0=>0x629b08d822be35d9ae0d6a6b23579ab0d526a63521284d3c69b34c1a589266912471a309126863419a00cfa67b23c19d4ce647213811b88d846a23399948c646122f19708b260002b19544a4650226992c8906453000108c7e63c31c98d8c6660001908bcc5862a2
|6,1=>0x1a66d03000334d964c83
|7,0=>0x12d29594a4a4e5252919484a3e51d28d9464a2e5152899444a1e50d2859424a0e50528194049fe4fd27d93e49ee4f527993c49de4ed2760ba89d04e627213889c04de26e13689b04d62
|8,0=>0x27033719b0cd46683331990cc466032f1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 13
def pmP:Nat→Nat
|0=>0x32be00614c00c20000d000014820025dc004ab8009000011000021f00043b80085c0010a20020000020000021800040000045c00088000100000110000110000200000260000480000600000800000800000a00001000001000000
|1=>0x110680201dc03c2b80785300f0a201e114034ab80685700d0a601815c03009005a5900b2ae01616402c2a80585300924a0121d40242b8048100084000100400142d8028570050a600a0000102b80204900402400802001001001d57
|2=>0x20c20e41815c8248a9048752090ae412040820a9900857201048400044700800209df0412fe05e14c098888109010202020400440800080f84501f00003a10c06c2e80d8550190ea03211405c0000a04a0130aa026000048008088de
|3=>0x4029578002210004090040010c8552190204221dc8441a106117
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x82000010000000000000000
|5,0=>0x2c28018180000000381002400210000000008200064868000007800000480001030000100000044000000000000003000010000
|6,0=>0x162e007b3cd204159b9b12f9e8341ae04d66b244b563050ca8a3615396973a7828b4248c12a814e657e48c809e057aa468ad13005a8dd7d4c700cc2a057
|7,0=>0x3878c101f68ce2b5c7919c75af30e886de93b75714e2356dbb2b7626398525e4b5b6e6396d7a531
|8,0=>0x1e95789d4485af0cbd
|9,0=>0x13
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_185 8 roots_185 ops++addP pm 1 dom_149 5 roots_149 ops++addP pm 2 dom_21 4 roots_21 ops++addP pm 3 dom_57 5 roots_57 ops++addP pm 4 dom_157 7 roots_157 ops++addP pm 5 dom_29 5 roots_29 ops++addP pm 6 dom_173 8 roots_173 ops++addP pm 7 dom_153 5 roots_153 ops++addP pm 8 dom_141 5 roots_141 ops++addP pm 9 dom_184 5 roots_184 ops++addP pm 10 dom_45 5 roots_45 ops++addP pm 11 dom_61 7 roots_61 ops++addP pm 12 dom_53 5 roots_53 ops++addP pm 13 dom_181 6 roots_181 ops++addP pm 14 dom_188 6 roots_188 ops++addP pm 15 dom_60 4 roots_60 ops++addP pm 16 dom_172 5 roots_172 ops++addP pm 17 dom_169 7 roots_169 ops++addP pm 18 dom_137 4 roots_137 ops++addP pm 19 dom_41 4 roots_41 ops++addP pm 20 dom_156 4 roots_156 ops++addP pm 21 dom_177 5 roots_177 ops++addP pm 22 dom_165 5 roots_165 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_189 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_165 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_185 8 s (0,roots_185.map (·&&&dom_185)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_189 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_185 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_189==dom_189)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_189 gM v ys):RunD true dom_189 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_189 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 21 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 61 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 61 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 70 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 70 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 45 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_189 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_235:Lower true dom_235 roots_235 goal_235 10:=lower_slice_b [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a,8,9)] (by decide +kernel) lowS_234
namespace S_237
def pG:List (Nat×Nat):=[(1,5),(1,9),(1,33),(1,65),(1,129),(4,5),(4,36),(4,68),(8,9),(8,40),(8,72),(8,136),(12,13),(12,44),(12,76),(12,140),(32,33),(32,36),(32,40),(32,96),(32,160),(64,65),(64,68),(64,72),(64,96),(64,192),(128,129),(128,136),(128,160),(128,192),(132,133),(132,140),(132,164),(132,196)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffff
def xsM:=roots_237.map (·&&&dom_237)
def gM:=goal_237&&&dom_237
def NN:Nat→Nat
|4=>3
|5=>62
|6=>145
|7=>87
|8=>20
|9=>3
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x6037c2ceb828d23
|5,0=>0x861127dd2e7b1987a63f6b6e8673c966dd95fae75e5d446dfd3b2f43866b37bfc36eb4331c332c86318932dbbd2a0612665b2595b243ad23e1e233b9211402037d201c1200321fbee1f1101cea41c84e1bee41a41b157f01570c12b9312adf1229e110a20ed390e49d0d1eb0cd680ca1f0c8df0b6dc0b2590b0ac08c90072d206f2b05c3405a15044ee040da0390301ee200dc800abe0075d00559
|6,0=>0x51a04515b04fddc4e3b84dbe04d5754d4864c01d4a4c249dfa4890447d7647d5147a2646dfd43c05432274183e3e50e3e30b3c5d73c5143ba2f3a69039e9138a4c38901382b6380ab37b9335a673577335629355c334d5e33c3d31c6b3180530682300e02fce12fa542d2542c1f42be842bd072aaf42a3d329f072907c285cc273e526e142565124ceb23e22239fe23123222a421de92170c1f8301ecb51daf21cecb1c6911c1ca1b05a1a49819eda19e221963f1949d18f86181b11739616e12161ee15c6615a4c159f21502c132a813039125f811849108cd106180fcf90f8cb0f42c0ee490e0710d9cd0c8dd0bfd90be090bc510b3850af610af080ab680a9cb09a1d099de09643077ce0732d06db005e1405abe0590205886052be04ef704e5b04bf204620041350313a02c4c022da01f300135e01028009880075d004c8
|6,1=>0xcdec9b60119b5c8968127bfed75a14714026e3466bb986b6e8668d16614b646da5e0a85b5805aa9153a36
|7,0=>0xd6188cdec9c219b7e70667409657d564b926421164023609a25d65a5d40b59228515ef50c0a4f06f4e3964d759498fc485c9483f343cce431b542a7c3fbf83faa23f7e63d6713b0433ae2439bcd3779a365b735ded34b48303952d89b2c0a62a574297ee27404273d52723b251cb244df2420c2305820f4520a4e1fd701e5831e22d1cc361b35c19a3e17f1f17ded17c89175941755c14fef14bf51486c1472213ed8139871204611af411674106460fa5d0e5050c70508c64070990648e05e42049d403f3902da202c4a022f901e2c010f600ff300d4100275
|8,0=>0x866bd625ca487c747faf455fc431a04138a40c9040b31318072948726db42376c2265521aa22030e1a7a11445a12af6014cf
|9,0=>0x743d343d292584d
|10,0=>0xf0cad
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccc000088880000cc00000088000000cccc000088880000cc000000880333300003333000033330000000000003333000033330000333300000000cc880000cc880000cc880000cc880000cc880000cc880000cc880000cc8b33300003333000033330000333300003333000022220000330000002200cccc0000cccc0000cccc0000cccc0000000000000000000000000000000333300003300000022220000220000003333000033000000222200002200cccc0000cc000000cccc0000cc000000cccc0000cc000000cccc0000cc0333300003333000022220000222200003333000033330000222200002222cccc000000000000cccc000000000000cccc000000000000cccc000000033000000330000003300000033000000330000003300000033000000330088880000888800008888000088880000888800008888000088880000888b33300003333000000000000000000003333000033330000000000000000cccc000088880000cccc000088880000cccc000088880000cccc0000888b33300003333000033000000330000003333000033330000330000003300c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c333300003333000033330000333300003333000033000000222200002200
|0,1=>0xc0000000c0000000c000000080000000c0000000c0000000c0000000800000000000000000000000000000003303000033030000330300003302cccc0000cccc0000cccc0000cccc0000cccc000088880000cccc0000888800000003333000000000000333300000000000033330000000000002222cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc000000033030000330300003303000033020000330300003303000033030000330200cc000000cc000000cc00000088000000cc000000cc000000cc0000008b33300003333000033330000222200003333000033330000333300002222cccc0000cccc0000cccc0000cccc0000cccc000000000000cccc0000000030300000303000003030000020200000303000003030000030300000202cccc0000cccc0000cccc0000cccc0000cccc0000cccc000000000000000003300000033000000330000003300000033000000330000003300000022cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000888800000000000000033330000333300000000000000000000333300002222cccc0000cccc0000cccc0000cccc0000c0c00000c0c00000c0c00000c0c111100001111000011110000111100001111000011110000111100000000
|0,2=>0xcc000000000000008800000000000000cc000000000000008b33300000033000033330000002200003333000000330000333300000022cccc0000cccc0000cccc0000cc880000cccc0000cccc0000cccc0000cc891110000111100001111000011000000111100001111000011110000110000000000cccc000000000000cc88000000000000cccc000000000000cc8800000000000000000000000000000003333000033330000333300003322cccc0000cccc0000cc880000cc880000cccc0000cccc0000cc880000cc8b33300003333000033330000333300002222000022220000222200002222000000000000000000000000000000000c0c00000c0c00000c0c0000080b333000033330000333300003333000033330000333300002222000022220000000000000000cccc0000cc8800000000000000000000cccc0000cc8b33300003322000033330000332200003333000033220000333300003322cccc0000cccc0000cccc0000cc000000cccc0000cccc0000cccc0000cc0333300003330000032320000323000003333000033300000323200003230cc880000cc880000cc88000000000000cc880000cc880000cc880000000333000003330000033300000333000003330000033300000333000003330
|0,3=>0xcc00000088000000cc00000088000000cc00000088000000cc0000008b333000033330000003300000022000033330000333300000033000000220c0c00000c0c0000000c0000000800000c0c00000c0c0000000c00000008000000000000000333300003333000000000000000000003333000000000000000044440000000000004444000000000000444400000000000000000000000111100000000000011000000000000001111000000000000110000cc000000cc0000008800000088000000cc000000cc00000088000000883030000000300000303000000020000030300000003000003030000000200000000000000000000000000000000cccc0000cccc0000cccc0000888b33300003232000033300000323000003333000032320000333000003230cccc0000cccc0000cccc0000cccc00000c0c00000c0c00000c0c00000808000000000000000000000000000000003030000030300000303000003020c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c000008080330000003300000033000000330000000300000003000000030000000288880000cccc000088880000cccc000088880000cccc000088880000888b33300002222000033330000222200003333000022220000000000000000
|0,4=>0xcc88000000000000cc88000000000000cc88000000000000cc8830300000303000003030000030200000303000003030000030300000302cccc0000cccc00008888000088880000cccc00000000000088880000000111100001111000011000000110000001111000011110000110000001100000000000000000000000000cccc0000000000000000000000000000888800000000000000033330000333300000000000000000000222200002222cccc000000000000cccc0000cccc0000cccc000000000000cccc0000888800000000000000033220000332200000000000000000000332200003322cccc000000000000cccc0000cc880000cccc000000000000cccc0000cc8b3330000333300003333000000000000222200002222000022220000000000000000cccc0000000000008888000000000000cccc000000000000888b3330000111100003333000011110000333300001111000033330000000044440000444400004444000000000000444400004444000044440000000333300003333000033330000333300001111000011110000111100000000cccc0000cccc0000cccc0000cccc0000cc880000cc880000cc880000000000000000000000000000000000000003333000033330000333300000000
|0,5=>0xcccc0000cccc00000000000000000000cccc0000cccc0000cccc0000888800000000000000033330000330000000000000000000000333300003300cccc0000cccc0000cccc0000cccc000000000000cccc00000000000088891110000110000001111000011000000111100001100000011110000110000cc000000cc000000cc00000000000000cc000000cc000000cc000000000000000000000001111000011110000000000000000000011110000000000000000cccc000000000000cc00000000000000cccc000000000000cc0222200003333000022220000332200002222000033330000222200003322004400000044000000440000000000000044000000440000004400000001111000011110000111100001111000011110000000000001111000000000000000000000000000000000000000000000000cccc000000000000888b3330000333300000000000033220000333300003333000000000000332200000000000000000000000000000000444400004444000044440000000222200002222000022220000222200003333000033330000333300002222cc000000cccc0000cc000000cc880000cc000000cccc0000cc000000cc8800000000000000033330000222200000000000000000000333300002222
|0,6=>0x11110000111100001111000011110000111100001111000000000000000000000000cccc000000000000cccc000000000000cccc000000000000000000000000000000000000000000000003333000022220000333300002222
|_,_=>0
def sP:Nat→Nat
|0=>0xa7c20b0e194054e101862220e040e341082c2d2870214c8b488c3a0102c7064414589420440b0e78305081cd053e105930e44294081c6853e10583365c311101cf06101421d0c4429c0848d870c442873414c841660b860a58a870214a04164c38622402120e188901c346010608080
|1=>0x562c1970c1538412b9005082c18e0c453031c81482160d00556105831c188a610483862214aa51c1d00516903a058105a50e8068816b43853e1058e0c45305380c31150702180e1942708383110a7020602b15841638386222082a0e81485083830c02149070c44428301c69f082c483
|2=>0x1c5c3052c105870ad590416a83860ad02070acca04166038622402070c15984161c29664105980e34116161c6810010c073c182845a1d005082cd870c444100e184054e5438d18042070a58a04164c9070c442830e188b1083830150c018e0c4532854243a00a103a90a7c20b4a18085
|3=>0x2438b86021459d1c1808816b438602b020b06383014ca05870c05410082ce830e188880860187403420b30383a004145874015d04164c3860a5820b120d48110105870c15c04161c3260acc20b301c6862c105b7065c3010a103b60c1420b120c3052c105930e188a80a103810a5020b
|4=>0x81d48602b020b0f043010a103860a9c20b0700301102c3860af9e84160cd8e0c0440b1c1c30110b058378180a8081c3080a9c20b365c386022140702a0294082c9920e1808516dc3860a9c20b061c301621059d061c301105448e1a0440b546038602142180e188a60a10483520420b
|5=>0x3145c90e18885081c30110b020b300cb8602a02032e180a62a12387401420b066c70622142170c042c608dc3860220295361808538105870c4544508383a0523428b3a383010a556830e80284166c386022080b061c3056a105838818085082ce8e0c442843a3830110a05870c442c2
|6=>0x2e180a60a1018e0c45404460d005082ce921c18085161cd060a1058e0e1888596103a01a1558416dc3860a5820b0e806c5082ce870c45305088c3a0042028b3a383015014a830e188ca086c3862214804065c301201058e0c0443f161c3056a5820b066c30150103a90c14b04161c682
|7=>0xa103860acca84160c7200c2058740082ac082d2091c18088160c7201a105a3120d005082c4980214c84166038d040458e0c042cd1694487040428b1c1d005982d287401420b301c311501018740a41041674d870c0440b241c30110145870404299082d20e0c0440b063948d0c04598
|8=>0x10a0aaa481c3010a10b86029829c08b43a00a105ad0e80405082c4d0401420b0e08085142c9170e180852a603010aac20b0e180a808c0382022278b363838602214180e19416082d68740a428416603a01a105830e188a65010c070c167041694487401420b061c30566105aa1c1c301
|9=>0x82cb870c442d508603860a9c20b1c1c3059c1058e2e188880a1d005a8105891c80405160c7290c0440b6e7438602142074015584174838602a020b0e804055610598061d0020a2c18e0c04804164cc070c442842e1c30150402090f44085082cc170c04428084c3860acc20b3a1c301
|10=>0xc042d62a101870c05308082c3820c042c316607070c14b0416901870c04404160c3860214c841660386022140416607070c44284164c386021420b5a1c08532105ad541c3010a10c032e180852a6039a0c1420b300c3862214a870c14b1f082c4981a04404169038d040440b0e182b3
|11=>0x301c10602145890e34088082c3860360284161c3010a40a84161c6860216b841648b870c0428416603820c04405160c3860299404160c7020c0428b3a6c386021420b48383010a1059b0e180880a2d2071a18088082c3a00c16284160c386029820b30383860214a8b301c3015010587
|12=>0xba105870c20296082c3a05234284164cb870c04284161d005b81059d0e180852a128170c04284166c7070c0540508603a00c1420b3a1c30110a020b301d006101420b365c38622142070c042da082c1860216d84168c1820c04284169048e0c042841638386222028b0e180880b6820b
|13=>0x21420b460c706021420b301d486021420b0e180859a1058e0c042dc082c483401420b061c682021058e2e180880a2c3860214c8416749070c04284161c301101708bbe1c3010a1059d0e180a80a5425e0e80284161c3052c105870c0443f082c3a0042028b2660386021420b0e18085
|14=>0x638301102d68e0e18085082c487040440516243a91a04284164c7070c04284161d0290a105870c444052a9038d040428416601870c04295161c3010a4020b36383862214224061c1010a105986e1c3010a105890c042c3082e2070c04284161c3010b5c20b4824386022020b2674386
|15=>0xe180880a545870c45405081c311101420b801c3010a1059b1c1c3010a105830e083010a10598061c3010a105832e18085082cb870c04295081c68202205930e18085082c1970c05404301c3052c105870c0429c082c4874020284166c38602a0295081c3011014e04163838d0c0440b
|16=>0x386021420b1c1c3010a105970e18085082c386221420b481c3010a1059d0e18085082d1870418085082cc070c04284161c3010b5820b06383010a1058752083010a1058e0e083010a2cb870c04405082c3860216284161c3010b3c20b
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x8500440004
|5,0=>0x173616d61676161615b6155614f614a5144613e61386132612d51276121611b61165110610a610460fe60f860f260ed50e760e160db60d560cf60c960c360bd60b760b160ab60a5609f60996093608e50886082607c60766070606a6064605e60595054504f50496043603d60376031602b6025601f60196013600d6
|6,0=>0x31d73176310730a630372fd62f762f072e972e272dc62d572cf62c872c172bb62b472ae62a772a072997292728c6285727f62787272626c6266625f72587251724b6244723d7236722f72287221721a7214620d7206720061f971f361ec71e571de71d771d071c971c361bc71b571af61a871a1719a7194618d7186718061797
|6,1=>0x4c974c364bc74b574ae74a774a074997492748b7484747d7476746f74696462745c6456644f74487442643c6435742e74277421641a7413740c740573fe73f773f163ea73e373dd63d673cf73c963c363bc73b663b063aa63a3739c7395738e73886381737a7374636e63677361635a7353734c7346633f73387331732b63247
|6,2=>0x53c7535752e7527752075197512750b750474fe64f774f074e974e364dd64d764d07
|7,0=>0x713770c770486fc86f486ec86e576de76d866d176ca76c376bb86b476ad76a5869f66996692768c6684867d7676766f76678661665a7653764b8644763c8634862d7626761f7617860f8608760085f975f275eb75e385db85d385cb85c385bc75b485ad75a6759e8597759075888581757a7572856b7563855b8553854b85438
|7,1=>0x7b967b277ac67a5779e7797778f87878780777a6772876b7763875b8755674f6747873f8738773177298721871a7
|8,0=>0x8497842783a8833782c7825781d8816780e8807780077f977f367ec77e577dd87d587cd87c677bf7
|9,0=>0x85d785678506
|10,0=>0x8646
|_,_=>0
def wAt:=mkWire dB 99 238 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x12210e190a114c1f0e2108153617081d163d040c08190a1d06110e150e9a30070e21081908150a25082502190e19081d022912200e1908150a110e191a380a19081d30830e210a111605261b2e210e2d0a112e110815022d0e2d166a2c193007101d300706110a1d163d0e1106080a1d08190a190e151629081912200e190a11
|1=>0x40c08190a1d0c1d300706110e150e9908a10a2d261b2e210e2d0a110e2d30071c150e1130071c15081d16290a1912200e19081512bd12220e190a113617163d06080a1d08190a190e1106540a1d082d0a2d022d50110a2d081d0ebd12220a112a150a1d081d022d082d0c05041508190e151605102d0a1d0a110e1102665a1b
|2=>0xa115a2f30191c150e11101d022d102d0a1110190e150e19081508762e150e2d2e150e110e2d0a115a1712210e190a110e1150110a2d261750390a2d0e11022d062d08150e1506110e1502190a1902191c150819081d0219040f08190a1d30071c150e1110190e1908155c07721d101b081530071c150e11302f06110e15023d
|3=>0x501d0a2d0e11170d0a3a022d0e110a094617041d081916851a380a190e1130470e21022d0a110a111c2f0a1d081d7e11061b0e151c2d0e110e15081546171c190e11085e0a2d0e2d0e152c2f3007101d0815085d0a110e2d261b50390e1126132e210e2d0a11302f1c150e110aed2a0f082d0a1d062d082d0e150c150e110e19
|4=>0x22d941d50130a2d5a1712210e190a11080d0a2d0e2d0e152a15082d0a1d901d1a1302190a1916050a1d1c2d081d0e2d50380a2d081d302f101d0a112a1d0e9a2a15082d022d101f0a2d08150e11083502190a19082d501d0a2d081d0c05301906110e1536171c2d0e112c2d30070611761d2a0f082d0a1d081d022d062d0e15
|5=>0xe15022d0a2d0a1d02191c19081d3a13062d0e1530071c150e11503b022d0a2d0ea6083502190a19302f1c150e110c150e22021908150ea108a1022d0a2d0a110e09021908190e11501d0a2d50130e15022d0a2d0a6e022d1c2d081d0a6e2e110e2d061b0a110a1d081d30071c150e11085d0a2d0e2d0e150a19101f08190a11
|6=>0xe1908150c050a1d0a19081d021912110e190a1d301b1c150e110e210a1908190815105c0e110e2d0a11481312150e19021904170819081d0892021906190e1516150e21022d0a110c05041508190e152e152e110e2d0a1126132e210e2d0a115a1b040d08190a1d06190815081d0a1d1a110a19081d101d102d0e2d0a110e11
|7=>0xe190e15122008190e190a113a130a5d0e2d0ea61019101d081506540a1d082d0a2d0e360a19081908151c2d0a2d081d300706110e150ea50219101908150c150e2102190815022d08a116150e1530191c150e110219089212150e1926072a0d082d5a2f1a390a1926072a0d0a1d02190a110a1d081d02194617041d08191215
|8=>0xc050e190e1110190a1d0a110e11302f062d06110e150219521f10190a110b4d503a0a2d0e11521f021910190a110219080d08190a1d0a6e1c2d081d302d0e210a110a6e2e110e2d0cbd12220e190a11101d0a110e2d26072e210e2d0a110a111611501d0a2d4c1f102d0815021912210e190a11021912210e190a110c050613
|9=>0x6190e150815301b06110e150a2d101d0815022d1c150e11514d503a0a2d0e115a1b12210e190a115a2f12210e190a11082d06110e152c1930071c150e11082d022d06110e1530071c150e110e19101d0a110e3508190a190a1126072e210e2d0a1130470e210a115a0730191c150a110e11022d0e2d0c059e111a1f0a190a11
|10=>0x2e230e2d1c150819081d0a190e190a11b215041f081936172a1d082d1a3a0e1108762e150e2d0819101d081550110a2d0e15081d08190a1d2e152e110e2d06190a1d081d2e110e2d0a1108151a1d0a190e2202190a112a15082d0a1d1c15082d081d0a390a2d0e110a5e0e2d082d102d0e1508151c170819081d30071c150e11
|11=>0xe1930071c150e11061b0e1508150c0508190815302d1c150e118a2d101f0a113007101d0815083502190a192e210e2d0a110c0512170e19062d082d0a1d06130e2d0a1d1c2d0a2d0e110e2102190a110ea1161508150c05101d08152e11022d0e2d2e230e2d0a111c1b0a1d081d041d08190a1d12150e190e11022d0a110e11
|12=>0x1c2d0e11022d1c2d0e1106190c110e15302f1c150e110e191c170e11c41d2a17082d1a3a0a190e1112150e190a113a11062d0e150a1d1c19081d1019101d08152e200e2d0a110e1112170e190a1d02190e190a1d08190a190e110e2d0815301b1c150e113a13062d0e152a1f082d0815c011062f0e15501d082d0a2d12130219
|13=>0xe110c110e1506110e150e2d0a1d082d0e2d0a19081908152e210e2d0a110e150a2d0e2d30071c150e114c1f102d081502190e190a110e55082d0a2d4c1f102d0a110a190a110e110a110a1d081d30191c150e1108190e190a110e191a110a1950390a2d0e110219101908150815022d082d0c111a1d0a19080d082d0a1d3617
|14=>0xe110e2d022d06190e15062d0e15041d08191c150e112e170e2d0a1d081d041508190819081d0e2d0a11101f0a111a1f0a1916110a11022d0a2d022d0a111c2f0e111c2d
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x198006
|5,0=>0x1acc665000062418440001714000000000015d453400000000000000140c4b511d00001094000000000000003d50f040000e8800000003910000345000032200000000c442d4000029409141f500001c305d400004d00f4000000000000c30000000
|6,0=>0x53cd4b4520d44400014044f113844d113134b51294495122347911a4459112443910b3420d0444010fd33e50f543c50ed43a50e633890df336d0d74350cd133350ca33190c332fd0bb42dd0b342c0cac42a10a5328509d4265095424508e322cc8740000843204c7d41e507631c906e4
|6,1=>0x8d523148b52294895222387ce1c3861215384520d400020a381920247f91fa47dcdf347bd1eb47a0de537851dd47651d637491cf3730dc937151c146f8dba46d91b336bd1ab46a0da4468119c4661194464118c4621185360517d45e517635ccd7035b11693595161457515a35591524
|6,2=>0x27049b12684994e61497525a395ce53493d0000930e49391524148f52394
|7,0=>0xcbcf2c3ca4f263c8cf203c74f1a3c5cf143c44f0e3c2cf083c14f023bfcefc3be4ef63bccef03bb4eea3b9cee43b84ede3b6ced83b54ed23b3cecc3b24ec63b0cec03af8abb3ae0eb53ac8eb02ab4eaa3a9cea43a84e9e3a6ce983a54e923a3ce8c3a24e863a0ce8039f4e7a39dce743
|7,1=>0x3743dc4f6e3dacf683d94f623d7cf5c3d64f563d4cf503d34f4a3d1cf443d04f3e3cecf383cd4f323
|8,0=>0xe74b9b2e64b972e54b932e44b8f2e34b8b2e24b872e14b832e04b7f2df4b7b2de4b772
|9,0=>0x3a11e8079f1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 14
def pmP:Nat→Nat
|0=>0x3050003030003000002d00002c0000289000280000231000209000200000180000138000110000109000100000080000050000040000038000035000030000028000021000020000011000010000009000008000005000003000001000000
|1=>0x4008004000003b38003318002b39002210002200002019002010001b39001b19001b18001000000f79000f39000b79000b39000b38000ad0000a100009000008100008090008080008010008000005800004500004100003c0000338000310
|2=>0x1020901010001003900c39800ab39008fb9008f99008f80008f39008f19008d89008b99008b59008b39008790008780008599008500008390008219008180008100004f79004bb9004b39004a100048090048000047980043980043390042c8
|3=>0x40b79040b3904028004020903033902a339028b39028800028020024718022b39020f79020f59020f19020e50020b3902080002075002071002055902055002005002001001a339019318013b39013b19012230012200011b18010b39010310
|4=>0x68231068229068211064b39064110061110061010060f19060b19060131052b3905231005230905223905223005131805020004cb0804a239049328049100048f09048800048339048020044b39044398041b39040f39040f19040bd9040bc0
|5=>0xa22300a21300a1318098b39098339098330098320098310098130098129089118088100083318082339082210082110081b3908001908001007033906ca10069b39069230068b39068b31068b19068b11068b09068b01068a11068910068339
|6=>0x924f79489b39481b39444b79443b392003311043b80f00090d03390d03190c23390c03390a2b39
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x302
|5,0=>0x81e00050e001f0000004c1900000000334039001c00000000050e003e00000e000c00330000100b00130d5d000409002306000000260000
|6,0=>0x13407649a23450f09890551001b35aeb5b2150154926a26178c22016006161136adb467b0779e975e3c348e63200709b68f2c5cb34e0a163a01901db1254224698d286c00c3c607a51b626b726f0185634f386a0607434b4101c72ea40171378a2a24060101074bc50146934a55017d07508b993d3f8f1400086f210b05272b
|6,1=>0x5052778099b0887ba290044167662bd91
|7,0=>0x952f5aa72faf6e2daca85fc2941a65c9b8a12fccb7a57b3070b712be187ec1cb68982f51535251af2f88c8297ea7667cca595671aa58a949317bbfb79c06a0c43b6d064d9f807a20bb73b98481a2a682807b9db996a3ab
|8,0=>0xbc5ac0a831799575837e617f488670745ba75732
|9,0=>0x703147
|10,0=>0x2f
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 24 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_233 9 roots_233 ops++addP pm 1 dom_69 4 roots_69 ops++addP pm 2 dom_37 4 roots_37 ops++addP pm 3 dom_101 7 roots_101 ops++addP pm 4 dom_236 8 roots_236 ops++addP pm 5 dom_229 8 roots_229 ops++addP pm 6 dom_45 5 roots_45 ops++addP pm 7 dom_108 5 roots_108 ops++addP pm 8 dom_173 8 roots_173 ops++addP pm 9 dom_205 8 roots_205 ops++addP pm 10 dom_77 5 roots_77 ops++addP pm 11 dom_109 8 roots_109 ops++addP pm 12 dom_225 7 roots_225 ops++addP pm 13 dom_165 5 roots_165 ops++addP pm 14 dom_105 7 roots_105 ops++addP pm 15 dom_204 5 roots_204 ops++addP pm 16 dom_228 5 roots_228 ops++addP pm 17 dom_141 5 roots_141 ops++addP pm 18 dom_172 5 roots_172 ops++addP pm 19 dom_197 5 roots_197 ops++addP pm 20 dom_169 7 roots_169 ops++addP pm 21 dom_100 4 roots_100 ops++addP pm 22 dom_232 7 roots_232 ops++addP pm 23 dom_201 7 roots_201 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_237 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_37 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_100 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_201 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_233 9 s (0,roots_233.map (·&&&dom_233)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_237 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_233 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_237==dom_237)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_237 gM v ys):RunD true dom_237 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_237 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 62 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 62 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 145 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 145 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 87 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 87 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 20 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 20 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 3 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_237 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_237 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_237 roots_237 goal_237 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_237
theorem lowS_237:Lower true dom_237 roots_237 goal_237 11:=S_237.noCircuit
theorem lowS_238:Lower true dom_238 roots_238 goal_238 10:=lower_slice_b [(0x505000005050000050500000505000005050000050500000505000005050,32,36)] (by decide +kernel) lowS_234
def isoMvS_95:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_95:Lower true dom_95 roots_95 goal_95 9:=lower_iso_b isoMvS_95 (by decide +kernel) lowS_63
def isoMvS_175:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_175:Lower true dom_175 roots_175 goal_175 10:=lower_iso_b isoMvS_175 (by decide +kernel) lowS_125
def isoMvS_190:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_126
def isoMvS_207:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_207:Lower true dom_207 roots_207 goal_207 10:=lower_iso_b isoMvS_207 (by decide +kernel) lowS_125
def isoMvS_215:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 8:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_183
def isoMvS_219:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_219:Lower true dom_219 roots_219 goal_219 9:=lower_iso_b isoMvS_219 (by decide +kernel) lowS_187
def isoMvS_222:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_126
def isoMvS_231:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 10:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_111
def isoMvS_243:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_187
def isoMvS_246:List (Nat×Nat):=[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_119
def isoMvS_250:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_238
def isoMvS_252:List (Nat×Nat):=[(0xcccccccccccccccccccccccccccccccc,126)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_126
def dzo_107_16:=0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16:=0xf0f00000f0e00000f0e00000e0e0000
def gsh_107_16:=0xf0f00000f0e00000f0e00000e0e
theorem lowS_zo_107_16_104:Lower true dzo_107_16 roots_107 gzo_107_16 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_16) [(dom_107,16)] (by decide +kernel) (lower_slice_b (T:=gsh_107_16) [(0xa0a00000a0a00000a0a00000a0a,0,1),(0xc0c00000c0c00000c0c00000c0c,0,2)] (by decide +kernel) lowS_104)
def dzo_110_16:=0x55550000555500005555000055550000
def gzo_110_16:=0x55550000555400005554000054540000
def gsh_110_16:=0x5555000055540000555400005454
theorem lowS_zo_110_16_104:Lower true dzo_110_16 roots_110 gzo_110_16 6:=lower_iso_b (d1:=dom_110) (r1:=roots_110) (T1:=gsh_110_16) [(dom_110,16)] (by decide +kernel) (lower_slice_b (T:=gsh_110_16) [(0x4444000044440000444400004444,0,2),(0x5050000050500000505000005050,0,4)] (by decide +kernel) lowS_104)
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000fffe0000fffe0000fefe0000
def gsh_111_16:=0xffff0000fffe0000fffe0000fefe
theorem lowS_zo_111_16_104:Lower true dzo_111_16 roots_111 gzo_111_16 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xaaaa0000aaaa0000aaaa0000aaaa,0,1),(0xcccc0000cccc0000cccc0000cccc,0,2),(0xf0f00000f0f00000f0f00000f0f0,0,4)] (by decide +kernel) lowS_104)
namespace S_127
def pG:List (Nat×Nat):=[(1,5),(1,9),(1,17),(1,33),(1,65),(2,10),(2,18),(2,34),(2,66),(3,7),(3,11),(3,19),(3,35),(3,67),(4,5),(4,20),(4,36),(4,68),(6,7),(6,14),(6,22),(6,38),(6,70),(8,9),(8,10),(8,40),(8,72),(12,13),(12,14),(12,28),(12,44),(12,76),(16,17),(16,18),(16,20),(24,25),(24,26),(24,28),(24,56),(24,88),(32,33),(32,34),(32,36),(32,40),(32,96),(48,49),(48,50),(48,52),(48,56),(48,112),(64,65),(64,66),(64,68),(64,72),(64,96),(80,81),(80,82),(80,84),(80,88),(80,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|5=>21
|6=>139
|7=>268
|8=>197
|9=>63
|10=>8
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xba009aaeada24229fe038b64b863dc8020573a6471c2471a637151e6f20368d6b621a55d9044a5be49ae3353ee307fc1d807075f2
|6,0=>0xb819db729cb1b90b1947b1260b084eae8f5aae6eaad2fa8dd5a39e5a174ca16e39fa3598cc19461d931018cf948bdfe86e0784509834bd81ae1804c17daaf7c1217c09d7a53f77fb875c9d73696733ad7107770da36ed3e6e3b16a3036923065c3162244603d15f8cc5ef105d8c55b30a58f915765056f4a552bd54f7e54922541a352ecb523e550e0c4e6814c9dd4c1db4b4664b0024a86f4a7054a6ea49d0849b4847bd14786f439bd4326742cd740e5d3fc0f3f9eb3f0b73e6673ba1e3ae3239892392713926b3658130d09306272ed9c2eb782d7f42d68e2c6a52abab2a8ff29e9c2800826dc82611421dc921940216d020ef7200ec1fcbe1f6251e4d01c6d01b8321b5451b47a1ae1a1722216ec815163149c4142541359c10a0c100400e00e0cac80c6200c3b10bf280bbc60b9620ae940a2fa09d5907d140654103d8d
|6,1=>0xef40ce89b6e0542dac54d8d58d4397d41fecfadec45ebbc7b0b9758
|7,0=>0x490a3481ac47e6047cfd473dc4700945b8e44a3f42b1c424b8422a9418a740f9c40e7440e0340bcb3d8ef3d01b3cfa63c5c23ba053b1df3ae19392b23872d370cf368843674d3627635b903555833ecf33bcc33937338df31cf931c07313583123130a2e301312fd3a2fbd02fb102f5742e9d12d2cb2cd9b2ca7d2c6982bd682b9362a6f02a2ef2886328515283da26e2d260bf25976259072563b254172533c2409323f51236212316a22d152144a1f3531e1711d2751c2ef1c24c1bb3b1b7731b5ec1acee1a437196521605315a321589915260152551472a14100135b3130ba12666120d11192e10a79107f31032b0f13d0e1e60dce70dc090d7670cdab0aaf30aada0a82709c3a083e708205079cc077f50736c07135063ff05ee705d64058c5050200447a0414103e7403a48033490316e02f3b0212b017ef017330127a
|7,1=>0xd5f69d5e12d3f13d3a99d3483d1ef6d1af2ced92cc918cb352ca05ec8972c72eac71a6c637dc5406bf72abdc2eb7cfab76d9b72e8b58a6b4496b3d73b1bbbb1908ada40a81e6a49a4a18d0a16e3a04b59ef0d9ded19dc869d4ca9c8e79c5c39b2f59afc3994c99921d93a2e908768ee758e5458e3b58e3ac8e0a48da248c0518b1e88a54f8a1508941189095866ce83a81837ef831398281c8269d823af8228780ee07dda97dc9a7c2207a6d47a04979bfd7987d78ed8772aa770b5763f574fb474ab472ce9729c0726c86eb806de5f6dcdc6d04f6b2656a2706a13d69f3569c4c691a668a1f66c0665efa636f262cf861ee25ff6b5fc095fa2b5dd4b5d3995c41b5bd575aa0f5a1c2586d65817c56c7056a015599054654538605347750a4b507a24fa3f4e4a74e3e14d7e34d6494b2d94ad164a88d49c4349bf14999049572
|7,2=>0xf65cbf3f27f3689f3001f2e27f138eed8efe8eb9e216ede3f4d9384d6078
|8,0=>0x6db096ba4c683f767cb365b7d659e3654db637d5636736250461c4c614a9607155f82a5f6295d1145ca0e5959758efc57a8b563e15583253e8c53a3b536da5343f516bc50a71508e6508d7502cb4ed884ea1b4e41c4df8b4c9fe4c2d94b4824a093498eb47f6a4790e44f7b44d46415b5408af3f1c73de9a3cbd73c4733c42d3c0203929e384ff37a1f3546b353cb339863360d3351732fd932802327d12fb512ef9e2c6c32c4102bed32a46b2a1322a12d2a0bb2854827ad027960274d725d2a252652514524b24241c423e062220d21fd421c8521c5b212e81f7e61f24e1e2811e1591e0fe1c00f1b81d1a79a1a7971a04d189d917513170cb16f3c15dfd14a1013d2f13b14124841158d111a0103150f3070ec9f0e4660dfb60d6770c83d09ed70997d0904d087cc081cd066c50601705ad403d5703b9d033d2031ce02941
|8,1=>0xfffc2f87a2f767fe98a0e8b9ae851be6ca6e3527e23f8e08c0dfb74da49ed7ac4d607fd31ded1decd0498cf629cf447cdc40cc65dc474bb3e6ab0dd6b0d7eae60cacbd2abd39aa7fba79d4a78a3a65b0a643ea5d98a59a7a496ba3f98a3423a24eaa09e89e64298eef96d5495dbb913da90fe98fd688fa488aa6289bd3887ef8797a87860866968589b847f882eef8259a809ef803177f9347ef827ec497d0277811c7619c75afb736c86e221
|9,0=>0xeaa72d7c1cd7251d30f7d07fbcb115c6e0bb172dae6bc9ef6b98d8996ffb90c1a8c18080b067f8697cc3675028732a5721876c53969a565d1ec56fb45377851f1c4f2c04c96b4426d43f713d5ff3cb5b3c55e3c2ee3a902375e833bb7291b828ca226efc26280232c122f9c224dc21e04215431f4731df2b1b6f51b4f01914a17b870fa530f8b00f0720b3ce0a10406d1406ca6052120325102368013a2
|10,0=>0xce280b81c7761fa581863b65b2fbbe2537d063e4
|11,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffaaaaaaaaffffffffaaaaaaaaffeeffeeffeeffeeffeeffeeffeeffeeffffffff00000000ffffffff00000000ffffffffffffffffaaaaaaaaaaaaaaaa00ff00ff00ff00ff00ff00ff00ee00eeffffffffffffffffffffffffffff0000ffffffffeeeeeeeeffffffffeeeeeeeeffaaffaaffaaffaaffaaffaaffaaffaaff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffffffffff00000000ffff0000ffff0000ffff0000ffff0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee00ff00ff00ee00ee00ff00ff00ee00ee00ff00ff00ff00ff00aa00aa00aa00aa
|0,1=>0xffffffffffffffffffffffffff00ff0000000000ffffffff00000000eeeeeeee0000000000000000ffffffffff00ff00ffff00ffffff00ffffff00ffffff0000ffffffffffffffff0000000000000000ffffffffffff0000ffffffffffff0000ffffffffffaaffaaffffffffffaaffaaffffffffffffffffffffffffaaaaaaaaffffffffffffffffff00ff00ff00ff0000ff00ff00ff00ff00ee00ee00ee00eeccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffff00ff00ffffffffff00ff00ffffffffffffffffffff0000ffff00000000000000000000ffffffffffaaffaa00000000ffffffff00000000ffaaffaa
|0,2=>0xffffffffaaaaaaaa00000000ffffffff00000000ffff0000ff00ff00ff00ff00ff00ff00ee00ee00fffffffffffffffffff0fff0fff0fff0fffffffffffffffff0f0f0f0f0f0f0f000000000ffffffff00000000fff0fff0ffffffffffffffffffffffffeeeeeeeeffffffffffeeffeeffffffffffeeffeeaaaaaaaaaaaaaaaaffffffffffaaffaaff00ff00ff00ff00ffffffffffeeffeeffffffffffffffffffaaffaaffaaffaa00000000ffffffff00000000ffeeffeeffffffffffffffffffeeffeeffeeffee00000000ffffffff00000000ff00ff0000ff00ff00aa00aa00ff00ff00aa00aa0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0a
|0,3=>0x11111111111111111100110011001100bbbbbbbbbbbbbbbbbbaabbaabbaabbaafffffffffff0fff0fffffffffff0fff0fff0fff0fff0fff0fff0fff0fff0fff000ff00ff00ff00ff00ff00ff00ff0000eeeeeeeeffffffffeeeeeeeeffeeffee00ff00ff00ff00ff00ff00ff00f000f0ffffffffffffffff00ff00ff00ee00eeffffaaffffffaaffffffaaffffffaaaa0000000000000000fffffffffff0fff0fffffffff0f0f0f0fffffffff0f0f0f000ff00ff00ff00ff00ff00ff000000000000000000000000ffffffffffff0000ffffffffffffffffffffffffffaaffaa0000000000ff00ff0000000000ee00eeffffffffffffaaaaffffffffffffaaaa
|0,4=>0xbbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaaffffffff00000000ffffffffffaaffaaffffffffffffffffffffffffffffff003333333333333333333333333333330000ff00ff00f000f000ff00ff00f000f00000000000000000ffffffffeeeeeeeeff00ff00ffffffffff00ff00ffeeffeefffff0fffffff0fffffff0fffffff0f000ff00ff00ff00ff00f000f000f000f011111111111111111111111100000000ffff1111ffff1111ffff1111ffff00000000000000000000ffaaffaaffaaffaafffffffffffffffffffffffff0f0f0f000000000ffaaffaa00000000ffaaffaaeeeeeeeeeeeeeeeeffffffffffeeffeefffffffffffffffffffffffffff0fff0
|0,5=>0xffff0f0fffff0f0fffff0f00ffff0f00aaffaaffaaffaaffaaffaaffaaaaaaaa00ff00ff00ff00ff00ff00ff00aa00aafffffffffffff0f0fffffffffffff0f00000000000ff00ff0000000000aa00aaffffffff00ff00ffffffffff00aa00aaffffffffffffffffffffffffffffaaaa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0affffffffffffffffffffffffffeeffeeff00ff00ff00ff00ffffffffffaaffaa0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000fff0fff000000000fff0fff0000000000000000000000000ffaaffaaffffffffffffffffffffaaaaffffaaaaeeffeeffeeffeeffeeffeeffeeeeeeeef0f0f0f0f0f0f0f0fffffffffff0fff0
|0,6=>0xfff0fff0ffffffff00ff00ffffffffff00f000f000000000ffffffff00000000aaaaaaaaff00ff00ffffffffff00ff00ffaaffaa000000000000000000ff00ff00f000f0ffffffffffffffff00000000ffaaffaa0000000000000000fff0fff0fff0fff0ffffffff00000000fffffffffff0fff011111111110011001111111111001100ff00ff00ff00ff00fffffffffff0fff0fffffffffffffffffffffffffffff0f055555555555555555555555500000000ffff5555ffff5555ffff5555ffff0000f0f0f0f0fffffffff0f0f0f0fff0fff00000000000000000fffffffff0f0f0f00f0f0f0f0f0f0f0f0f000f000f000f00
|0,7=>0xffffffffffffffffffffff00ffffff00555555555555555555005500550055000f0f0f0f0f000f000f0f0f0f0f000f0000000000ffffffff00000000f0f0f0f00f0f0f0f0f0f0f0f0f0f0f0f00000000ffff0f0fffff0f0fffff0f0fffff0000f0fff0fff0fff0fff0fff0fff0f0f0f0
|_,_=>0
def sP:Nat→Nat
|0=>0x2a30f8f083818634244032c6cf8908201863a2490e0650e8f243818212703830c507841c5c19e3a24908060879c0e0c3021424c070618d0f1c5c1863464c1706085111e1c182263c90e06184850820196262490806188840e0c110143c707061850d060860b142440706182840608080
|1=>0x81c186048540d085c1862868c0f105c1954e3490706084980a103830c3c6921c1c1864c3420706086130894182206cd070608a24364c284460c114261420e0618a1922142070608785080c10b36684032a3110d080c1212c6cd09101c1863644785081c1821a703952880d9a323cb83
|2=>0x362948d0e0c10c22342250e0c10a1a383830430d0f461c182366878e0e0c31b323421706181135e10703046c8981a1038304a06842e0c10c3464c070608d8d101c18604b8d095a0c114364c692100c3022660907060860a0eac19528a850d1c1c186284c2841c0c10c52342082e0c105
|3=>0x81c1822c284850e0c3143a3c9070608d0f2e1c186044c2844a201821a104170608f090a10417060888d081c18218684a30e0ca1b1a48186045058f08383833c6c684100c1313614684100c1163a3490806087840e0c124364c7920e0c3023434417061810a1e143830c0981a0e0c122
|4=>0x3634907061812164446840e0c11a6cd43ab2a5050f4a1c1951834e0706086331e38383046c68e0e0c3145c3c2170e0c11e14244070608d9a643c383046c7920e0ca8c204c6921c0c31432446920e0c1111e34907060948d0838b832828c0d0e0c30226249070618a0f081c182626c785
|5=>0x2e0c11d12483830450c0d0838b83043420e2e0ca1e343471706086091a1041706189a9085c182284cc124a0ca94323c2842e0c10d6e70383046cd080e0c1103634e07061811434347170618a1a223c383046c535581d59528283832a30a1012142070650b131a48703043050d0608a0b
|6=>0x1e1c1822c6ce89082018236d82070654a2a3e3c20706181133010b830430d0706e811436d86840654a393214207061811a1a201822c6d405081c182184c7841c0c31b1e3420e2e0c31930342170608f8d082018604342080609c1b3a3490e0608a280a103830c505191e1c182364cc04
|7=>0xe0c3191a483830c08e8908381943628787065463b26104030440d891a104032c6cd07060881b34d5e1528e4d8a6a1d59528ecd191e5c182367c6841c0c10c26242170618a1d1e10703046cd090e0ca163634203045059b3e3420e0618a1f12103830c5098f085c186044c2844a0c11a
|8=>0x2e1c1827a1423c2e0ca941a1038304f8da91e142070608d931e10b832a3079c0e0ca9436f4284581c19528683832a30a221e1420e0e0c11b14243830c504840e0c314683ce07065460a1e1c18604642844a1c1821e1420e0e0c30f081c18604d0684100c10b36442070654a101214208
|9=>0xe0ca941a10b832a321191e34217065461d1a49e032a5028d081c182006a0350e0ca9436683ab0654a2a36686a30e0c114366868e0e0c31437046840e0c11436d86840eac195284c6920e0c10c7ad86920e0ca9432142082e0ca9466243830450d8a1a20383046c5051a1c182183c284
|10=>0x166da85081ca948e362870608a1b343e2070654d8d081c1822890d9a1a383830430d931a483830c08a0d08201951888d350e0ca94726c48d08203830c6c5051a1c18604506921c1c186281422c0e0ca945464785081c182364c2844a0ca9452342170e0c11430349250e0ca943460797
|11=>0x28686970e0c302284c284580ca943e3c2080654d93303c2080654d8a121c182286cc0d085c383043641c0e0ca943668c0f0e0c11b263492c560ca94303c684105c1951a4870706086181a107070608d8d08383832878d890a107070650d89081c18228d0d9a1a5c383043148d080c114
|12=>0x60861922342170654a0f1a111870608da91a483830c08a0f1a107070618d8f1a49287065461930342070608d9a323cb832a50d8d09243830450d8d081c18228c4d851a103830450b091a484070608d9d1a48383045098f08944032a6cd0f4a1c19536246845a0c114364c2844a0ca8c
|13=>0x96286a50e0ca8c28606842e1c182184c692100c11b66347070608a1b1a10b870608a1e66d5e072a50db51a496075654a090a10b870608a0d241c195185081a4a1c1952840d8d08392970608d991a112870608d9a100ca94446c984100ca94206cd070654a10369c6840e0c11b9434207
|14=>0xe54a0d081c1829e6c985085c1822864284101c18237386840e0c11b1a104030404d9a1e943832a30d991a10b83046c28d0838b830451eb51a483ab2a50d0d4a20383046da8508f0b952868687065261b1a2038304b8d931a104030c08db50a116072a50998081c182186c6920eaca94
|15=>0x2a51d98081c1952840d8a1a383830450d9a0e0ca94546c535781ca943674684100c11b263c207061811b1e103832a31a0f1a10b8706181501a483832a5140d085c182286c28d089438304683832a30a1036d9a85081c1952829a875654a0930142070608d891a111870650db50a1163c
|16=>0x6cd46840eaca9434f03832a5151b643c6840e0c11b1e11287065481b261420806546431a11e1528e4db21a483832a30a181a4840706546431a496070654a0d0820b830c086840e0e882286c6920e0c142362948d0e0c114366478d241c1823628787065460d080c302282cd8a1a1d583
|17=>0xe0ca8c206c98d0838186286cc911a10383046c684101c182206cf8d081c18218286880e0ca8c6c3423c2e0ca94223c6840e0c11b34a04870608a1b6c3422c0e0ca9414606870608d935e104032a6c48d085c3830c50e8f081c1823668687060801b64646840e0c11b32142250e0ca94
|18=>0x2c6c6920eaca94a8da18d081c195284c6842e0c10c7ad86842e0ca941a703830450d931a107030430d8d08f019528e4da91a116830450d9f1a103830c08a0d081c18228e0d8d081c1860484d8d081c182a66cc8f0a103832a3098da448383046c9981e10b832a506844620b83046c784
|19=>0x43198f101c1953669aac0e54a1b1e14225101c19564342080e0c11b263c2250654dca1a104070608d931a10b830c08a0f0a103830c08d09101c18237586840e0c11b26602250654a1b1a107170618a32081c1952840d8d08b019528e4d931a487030450d8a6a1ca94aa6cd0d0e0c114
|20=>0x36242840e0c31434d9a870654a1b4e349070654a051a10407061813d6a142170654a0a0a343952960d9a6ab1e072a50d931a484032a30e8d0838182286cf8d08201823664885081c19528142070654621ae342070608a1b34d5e172a50d911e142070654a1d12103830450d8d0838b83
|21=>0x2888d911a112870654a0d080c114166cc0d0820b832a6a1b5781ca943668c8f0e0c11b50142070608a1b14f5a870654a1b80d86840e0ca941a10383056cdda1a10383046c98f241c19518686882e0ca8c143c287065460f1a103830458d8a6a143ab2a5098d0894403046cd0d4a1c182
|22=>0x28a8da91a104070608d9a1e1c186046c6840e0c114166ee1a0e0ca94446c6920e0ca8c42d423c0e54a2a3634207060881b80342032a51c9b6a3423c2a51c9b1e34907061810a1a1c18218446840e0ca8c2834217060a11b323c6842e0c11b1a103830431a091a103832858db0341c195
|23=>0x578d933010b832a5088d08203832a32c8a0a34383046d98f0e0c11b1e142250e0cab21a10383046c6b7381c195286c9af081c18236684070654a103634207060ae9b64606840e0c11b3234207061811b5e3420e0e0c11b3e3420e0608a1b343d2880e0ca9b12349070618a3508b0395
|24=>0x36369120e0c11b1a103832a30a221a103e20654a1b5e342080e0ca9b1a1c18228b8d911a104070654a1b3e342080654a1bc23423c0e54a1b6c342070654a1b1b7c3832a50d8d08b4182286da8508b03ab2a5148d0838383286c28d0820b83047c7840e0ca8c0a34203045059b1a10383
|25=>0xe0ca94370c684781ca94364cc0f081c195286c6e30e0ca94366078d085c3832a5268d241c195286c6bc0e0ca945c6c6840e0c1148c6e0351a103832a50d8d081d5832a5151b32142070654a1b263493c0654a1b6c3423c0e0ca9436343ab0654a2e2634225100ca9436686a50e0ca94
|26=>0x100ca9b343c383046cc0d241c195185098d081c182186cd0d4a1c1951850dbd6c342070654a1b1a10b832a52a1b6a349075654a661a103832a50d9a1ab03832a50d8f1a122070654d9a323c3832a50db51a103832a51c9b1a103832a52d9bca2828d0e0ca9437686840e0ca94367c784
|27=>0xeac195283c6844a1c19536342070654614684c6920e0c11436342230e0c114363420e0e0c314362828d0e0c11436746920e0ca9430342250e0ca94364c7842e0ca94363c6920e0ca8c343563c0e0ca94366078d081c1823674684780ca9436342070608a6736d4692781ca94364c784
|28=>0x2a5259b1a112870654a1036342170e0c10c263422c560ca9436686880e0c11b1a104032a5111b60686970e0ca9436342070654a10363420e0e0c10c36342070608a01362868706546141a10b832a5211b323c6842e0ca94364c6920eac195284c6840e0c302286cc8d081c182362828d
|29=>0x3434407065461b6a3422c0eaca9436342070654614206c50d0e0ca94766c985081c19518506842e1c186045148d081c1860450d8f1a11287065461b0a3423c0eaca9426142170654a3d6a142070654a1b3a342070608a1b1a487070608a1b1a483832a51d9b1e142080e0ca9b0a10383
|30=>0xb8686970e0ca9436c86844a1c195286c28d081c18218349080e0ca8c64342070654a1b1a103832a5359b30342080e0ca9b1a103832a5351bd0342070654a1b26bc2070654a1b7a342170654a1b1a103832a52e9b64606840e0ca9437286840e0c11436684870608a1b1a103ab2a5259b
|31=>0x101c195290c684581c195286f70d081c195286c98d0894195286d4091a103830450d8d0820b83046cd0dd21c195286c28d081c186045178d081c182363426c0e0ca9436342232e1c182286ec8a0a343832a50dbd1a11e170654a1b1a112880e0c11b7a3422c0e0ca9436cc7870654a1b
|32=>0x608a1b14344070654a1b1414687065461480342070654a1b7ad46920e0ca943669abc0e54a1b1a103830400d8d241c195292cd8d381c195286c28d0820b832a506840e0ca94de6c6840e0cade286d98d101c195286d90d081c1951850d981a10407065461b3e3423c0654a1b0a34225
|33=>0x286da8d08b1e072a50d9a1a5c3832a30a131a10b830450d8d081d5952950db51a11e172a50d991e142070654a1b6a3422c0e54a1b324c6840e0c11b803423c0e0ca9436342070654a393634207e00ca9436146840e0ca940029a870654a1b2634907065461412342080e0c11b3e34207
|34=>0x286cc0d081c18236646844a1c195286c6f10e0ca94369c6840e0ca94370218d081c195286e1b51a11e072a50d991e342070608d8d0838b830450d851a104070608d931a104032a30d9a1a1c182186c684881c18236a46840e0c11436606842e1c19528d42842e1c1952900684581c195
|35=>0x1a1c182286c5181a1c195286c78d08944070654d9a1a1c1952800d8d081c18228d0d851a11e170654a0f1a103830c08d9a7ad43832a50d8d241c1952908dbd0a11e070654a1b1e342170e0ca8c34352880e0ca94370c6840e0ca94726cd0d0e0c302286c98d2420195286de85081c195
|36=>0xe0ca94366498d081c195286d81a1a1c195286c5431a1c195286d90d08203832a50d980a342070608d851a10b870608a290a342070608a1b1e1420706546051a107070608a1b1a103832a5299b12342070618a1b1435e070654a1b6a142075654a1a86d43832a50d8d081c1951884d8a
|37=>0x654a1b6a142070654a1b323c6840e0ca943614684101c195286c6840e0ca948e6cd0d0e0ca8c286c684881c195286c98f081c195286cd0d781c195286e18d081d5832a50d8d081c1952950d8d081c19529ccd8f0a103832a50d931a104032a50d8d0e0ca945c6cd0d0e0c1143628692
|38=>0x654a1b1a1163c0e0ca9436746840e0ca94363423c2e0ca94363c6840e0ca8c36342070654a21363422c0e0ca9436606840e0ca8c286da8d081d595286c6844a1c195286c98d241c195286c5051a1c195286c78d081c182363490706546141a103832a53a1b30342070654a1bb868687
|39=>0x1a103832a53a9b3e342070654a1b0a3423c0e0ca9436d4684781ca9436146840e0c11436349080e0ca94366028d081c195286c684585c3832a50d8d08203832a30db51a483832a50d8d085c3830450d8d0820383046c48d081c182286e18d081c195286cc8d08203832a50d931a103ab
|40=>0x363423c0e0ca9436342070608a1b34343832a50d851a10b870654a2f1a103832a50d8a1a1c195286deb51a103832a50d8d081c19528d0d8d081c19529c8d8d081c1952990d9a6a1c195286c6f6241c195286e1851a103832a50d931a103832a30a1b1a107070608a1b26342170654a1b
|41=>0x6840e0ca9436342080e0ca9436d46840e0ca9436146840e0ca9436342170e0ca9436342070654614
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x786039301b180ccc060602d30151809cc0486021300f1806cc030601530091803cc018600930031800cc0006
|6,0=>0x119b88b1c44ae21e710bb8841c412e20270fdb87d1c3dcc1e770f038765c3a4e1cb70e2386f5c36ce1af70d4386898336e19470c6b8619c2fee17870b8b85a9c2c6e15c70aab8539c28ee140709cb84c9c256e124708eb8459c21ee1087080b83e9c1e6e0ec70733037dc1b0e0d170653830dc178e0b570573829dc142c09a7049b8231c10ae07e7
|6,1=>0x1f7b8fa1c7c2e3da71ea30f35c78ce3bf71dc38ec5c754e3a371ce38e55c71ce38771c0b0de9c6e6e36c71b2b8d79c6aee35071a4b8d09c676e3347196b8c99c63ee3187188b8c29c606e2fd617b38bbdc5d0e2e1716d38b4dc598e2c5715f38addc560e2a9715138a6dc528e28d7143389fdc4f0e27171353898dc4bac2567127b8921c482e23a7
|6,2=>0x10e98866e42d6213b1081c832e4127205b9011c7fae3f67
|7,0=>0x30f3985a0c1ee60782ffc17de0be0e5e972f0c1769cba6e5cb82e2396f20b6905ad72d2c16760b2b058d82c3395fa0aeee57072b4b95860ab3055182a53950a0a7505328295b948e0a37051472864141209f904f57276c1399c9bee4d78267c131e097f04b78257c12a1c94104988248b9229c906e47c723a411b5c8cb045e722bb913e0890e4408
|7,1=>0x402c1ff60feb07ed83f339f7dcfb0e7d083e4b9f060f74e7b283d5b9e8e0f37079563c6c1e160efb077673b7b9d9e0ec0e75973a8c1d29ce85073a839941cadce48e71d738ac1c39ce0d06ff737bc1bbe0dd0e6e0836c41b45cd9306c1835cc1ac60d5306a1834d39a4a0d16e684733eb99d60cdb0665832ec19560c9b0645831ec18d60c5b06258
|7,2=>0x4f83a7a213c109d974e8c27261384e9bb74da3a6b2134ae99d84cac2636130ce97e84bbba5be12d0e96084acba54612930941849cc24c612530922748d4244a12150902847d423ca11d508e2846dba351d19908c4845e422d2115ae8a6744f4225dd120e8888440421e210e10868843042165d0a308498420c20e61064e82a8411ba06e1027080d6
|7,3=>0x5e93af2a1786ebbb85da3aeb217490b9c85ca42e32170aeb7d85bac2db9d6cd0b5e85abbad3e1690eb40859c42cc5d656cb23858e3ac52161aeb05857ec2bd615dceae7756fc2b61d5a10ac8856042ae5d564eaab75523aa75d52b0a8e7543429fdd4f0ea708534ba98614b30a518524c2909d4750a337515c2891d4390a157506c281613fce9f77
|7,4=>0x6153b08a18350c1376063b01217faebf675f742f9a17c0cbd97
|8,0=>0x7163b8921c372e1387054b80ddbf70df386f5c378e1bb70dd386e5c3711db772db386d63b68e5b370d9386c5c360e1af8ed7666b74359a1abb2d5496a643515da7b0d358696c34961a392d148685cb40e19f70cf386754b38dd9b52cd286654330a19732cb0965443282192f2c907643cb1fe18f0ec7086344318218b2ec5096244310218710c317
|8,1=>0x81b440ba204d101e880acc03260090ffb97f94bfaa1fc50fd997e93bf2a1f850fbb77d9c3eaa5f432f9897c843e1e5f00ef7797b74bd9ddec0ef5887a843d221e810f38879843ca21e410f179787c3c21de010ef88777cbb9a5dbd0ed6876743b165d792eb48756bba925d390e94874643a121cf90e7397363b98e5cb8ee548725cb90e1c770e338
|8,2=>0x91cbc8c264511220890c44845e413120188fd3c7ca23d331e188ecc4746239311c188dcc46c26351119f98cb4c63a230d117e88bbbc5ba62cef15f88ab4c536628b113d889ac44b6224cf11f788bc443e220f10fe987acc3b621cb10dd886ac4332618910bc8859cc2ae2147109b884a3c2322109107c883a441b220c9105b982a3c135e08b103e7
|8,3=>0x1262892ccc946249312409
|9,0=>0x518628b314527a24cd106287314318a153d08a283334109a044500227f113f089f3ccf7e27af13cf89e34cef6676b13ad89d2c4e79e72d138e89c2ccdf266e7336b89b1c4d6e26a7134b89a14ccea2665132a899144c6de628f30c898244bf225e912eb99714cb6a25a512ca896144aea256332a98950c4a662523128a7941bc9ee24e5326a8
|10,0=>0xa4fc525e291f14878a3fc51de28e0f4697
|11,0=>0x14a77
|_,_=>0
def wAt:=mkWire dB 119 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1a19046d2a511e1f046d2a5126090e352a51361d363d1a510835086d3a512a51364e0e35046d04352a510a513635086d1a961a8e08351c6d0e092a511a6d2a513666286d1a110e511a5e0e6d0e3d1a5108350e6d1a5d0e6d1a5d0e6d0a511a09046d0a111a6d2a510e091a51046d2a5108351e6d0e3d28352a5108352a512a51
|1=>0x521f0c352a5136110e51364e0e352a51086d0e351a11046d2a510e6d36090a1136352a512a511a5e0e6d34512a510a11286d1a6d2a5136390e092a511a5108351a111a51046d0e092a512a51363e0e092a511a390e092a512a511e6d0e3d1a5108352437086d521c126d0e352a51086d2a5136111a3136510e35583708351a6d
|2=>0x2a510ead0a11066d1a6d06351a962435086d36510e350e092a510a110e311a6d1a51286d08d1286d0a1f1a6d2a51366a2a511a5108350a1136352a51362504352a510a11046d2a510a511a6d2a512a511a09046d0a111a6d2a512a51364e086d28350e350e6d1a51046d2a5108351a6d2a51106d0e511a1a2a510c1d046d2a51
|3=>0x1a6d2a5118350e35286d08352a511c350e092a512a5136091a510e092a511e6d2a510e3d28351a5d0e6d086d364e1c350e092a512a51346d0e3d1a5108351a1d1a312a51286d0e6d086d364e363d1a510e092a5108350e6d2a511a19046d2a5118350e313651086d2a510e6d0e3d283508d10a1f1a6d08d10a1f1a11046d0e09
|4=>0x46d0a11043536352a5108d10a1f1a6d1a51286d28350a11046d1a6d2a51106d2a5110350e511a6d0a1f36351a09046d2a510e512a510a111a6d1a51286d1a114a37106d0e512a51141f0a11066d1a6d06350e3d28350e6d2a510835266d0e352a51364e0e35266d0e350a1d1a6d2a511a1d2a51106d1a6d0e51364e0e350a1d
|5=>0x46d2a510835806f5835561d066d286d0e352a51086d086d36f6260d0e351a2136350e51346f1a092a5108350e51346d2a510835286d0a111a6d2a511a510e6d1a6d2a51363578350e0d28fd2e0b2a510e6d0a0936352a51286d0e6d28350e3508d128350a1f3635786d363578350e0d1a5e0835286d0e6d28350e0936352a51
|6=>0x286d0e6d861f6a6d1a110e51046d04352a51046d0a111a6d2a510e0936092a51086d5837561d066d1a6d2a510e3d28350e35106d1a6d0e51362504352a5118350e313651086d1a11363d1a510e6d286d10370e510e6d0e6d0e3d2835266f0e0d36110e351a6d2a510e32286d1a1106355837561d08350e19046d2a5108350e09
|7=>0x1a312a51286d0e6d08d10a1f1a6d2a51363d1a5108350e353611561d066d363d1a510e6d0e092a513651086d0a511a6d2a510c37046d2a5136350a1f36352a510835286d0e6d521f0a091a6d2a510eae066d1a6d063509190a0b1a6d2a5136220e511a5108351a8e1c6d0e0936510e092a510835046d0e352a51086d2e370e51
|8=>0x2a5128350e313651086d1e6d2a510e3d28350e6d0e3d1a5108353c1d0c37046d261a0e35046d0c1f046d2a510e5104352a51086d086d2a51364e0e351a51106d0e510e3536210e511a510835521c126d2a510e350e31286d0e6d046d2a51083536352e0d1a1d0e6d0e51266d28350e350e511e6d28350e350a11043536352a51
|9=>0x2a51346f08350c37046d2a51346f1a110e0d063506353611561d066d0e6d2a514a370e31086d1a111a962e510e6d2e510e6d0e092a511a212a51106d0e511a110e511a5e0e6d1a96106d0e511a9636210e5108353a512a51364e0e35286d126f04352a51366626510e351a511c6d0e092a510c3536092a51086d1a51046d0e09
|10=>0x1b11106f0e510e51121f04352a511a5108350e31286d0e6d10350e512a511a6d3611066d6a1d06351a112a51106d0e511a6d0e6d0e0d06359a572e691a110e6d0e512a512437086d0e510e35046d2a510635561d3635066d2a511a3136510e35086d360d6a1f063524350e313651086d1a312a51286d0e6d0e510e352a51086d
|11=>0x1a490e0d086d06350e512a51364e0e351a510e35046d2a510a1f1a6d1a51286d36092a511a510e6d36113a0d364e0e351c350e092a512a51106d1a6d0e511a9608350e317a6f6a1d06350a11066d1a6d063504352a510a5136351c6d0e092a511a6d786d0e0d29190a0b1a6d2a511a6d2a511a1d0e6d36352a5110350e512a51
|12=>0x36f66a1d063508351ab2786d1a962e510e6d36511a6d0e510e356a6d06353651086d1a310e513651086d56353611561d066d046d2a510e510e6d0a1f1a6d36112a5110370e510a090a112a512a51086d0e3d28350a111a6d1a51286d521f0c352a51141f0a113635066d1a9618350e31286d0a111a6d2a5108351ab22e0d0e6d
|13=>0x86d1e6d0e6d28350e510e6d1a960e31286d2a512a51366626510e351a962a51106d0e51286d0a1d1a6d2a51346d36510e51083578350e0d326f2a510e3d2835121d1a092a510835806f1ab12e0d0e6d0a112a510a511a6d0e511e6f28350e352a511a512a51364e0e352a5108350e32286d2a5126510e351a21106d1a6d0e51
|14=>0x801f1ab12e0d0e6d0e090e352a51086d140f0a111a6d06350e1a046d0835360d086d78370e0d806f861d6a6d06352a510e35286d0e6d7a6f260d0e3508d10a1f1a6d2a5136510e350e092a51801f1ab1786d0e0d521c0a1d1a6d026d121f04352a511e1f2835046d2a512a510a221a6d0e510e3d3635365128352a510e352451
|15=>0x10350e510e3e3635365128350e0d06351a110e6d326f0e3d2835364e0e350e092a51286d0e6d366a0e511a5108351a11786d0e0d0635106d1a6d0e512e510e6d28350e350e51126f04352a510e352a511a51046d1a6d2a510e511a092a5108355e1d2a51363e2835181d1a3136510e35046d0e6d0e092a511a951a962e510e6d
|16=>0x86d28350e350e6d36510e5108350a111a6d1a51286d28350c1f046d2a510a11066d1a6d06351a1d2a51106d0e512e510e6d2a5108351a6d046d04352a517a6f1a116a1d086d3a51364e0e35046d2a511a6d0e510e6d6a1d0635b20f14510a111a6d1a111a0d786d0e0d1a1d0e513651086d364e0e350e510a1d1a6d2a51326f
|17=>0x835646f4a350e31286d1a222a510e510e6d2a510e6d0e3d2835286d0a1f1a6d2a510e1a046d2a511a5e0e6d34510835646f1a952e510e6d521f0a091a6d2a510a5136350e510e6d0e0d6a6d1a1106352a510e3d1a5108351c350e092a51346d1a116a1d063536f636f5260d0e3526322a5136510e352a5100350e32286d3651
|18=>0x301f0a511a6d2a512a511a31286d26510e352a510e092a51363e28350a1d1a6d36210e511a510835360904352a51086d1ab2786d0e0d0a092a511a6d0e511a51046d2a510835521f0a091a6d1a5e1a110e6d1e1f1a513651086d786d0e0d4a37106d0e512a51801f861d6a6d06356a6d0635283536092a51086d286d346d2a51
|19=>0xe3509812e0f0e6d521c0a091a6d2a510ead066d1a6d06350a091a6d2a512a5136350e510e6d0a1d1a6d1a51286d521f0a091a6d2a5128d10a1f1a6d2a511e6d0e6d28350e35326f10350e512a5114510a111a6d2a51366a1a5108352835106d1a6d0e513e510a1d1a6d2a5108d10a1f1a6d2a511e6f28350e351a9636210835
|20=>0xa531a6d363d1a510e6d264936110e350e0d2437086d0a0b1a6d2a517a6d6a1d06355837561d066d103536350e510e0d36110e3536f678350e0d066d2437086d106d0e510e3536210e51083524512a51086d2e37286d0e6d440d1a5e0e6d363e0e5128352a512437086d326f10350e51266d0e510e356a6f0e0d063536f6260d
|21=>0x260b2a510e350e0d086d06350e5128350e352a511a5108351a313651086d2a5136510e3508350e31286d36f6260d0e350e6d78370e0d066d086d06350f856a6f0635561d0835066d36220e5128350e3d1a510835861f6a6d0635263236510e35140d0a111a6d00350e32286d266d28350e350e0d6a6d06351e6d28350e350991
|22=>0x2a51121f04352a511a493651086d10370e510e6d0e6d0e3d2835066d36110e350e35046d2a5110350e512a510a113635066d36210e512835286d0a1f1a6d0e352a51086d1c6d0e092a51046d0e092a510a111a6d2a51086d364e0e3518350e31286d0e6d28350e351a513651086d1a11786d0e0d2a51363d28350e0d364e0e35
|23=>0xe31286d141f346d08351a6d36510e35361d046d2a510c35046d2a5128350e31286d0e0d3635066d1a6d1a1d0e6d6a1d1a6d06352a51364e0e350e092a51086d141f2435086d36350e5128356a1f1a6d06351a962e510e6d2a51286d0e6d0e35561d066d2a510e5108350e511a5e0e6d0e6d345108351a962e510e6d286d0e09
|24=>0x78350e0d2a51106d0e511af1786d0e0d366a1a510835340d1a110e6d2e510e6d286d1a6d2a510e513651086d0a211a6d0e512ed61a0d0e6d1a310e51286d370910370e51d235786f0e0d1e6f28350e35260d361d0e35301f1a31286d1a31286d126f04352a511a092a510835360d6a1f063536510e5108350635561d066d4a37
|25=>0x6a1f086d063508d10a1f1a6d36350e510e6d0af21a6d0e0d28d10a1f1a6d366a0e5108354a350e31286d1a310e51286d0e0d1a5d0e6d106d1a6d0e515635561d066d1b1d561f066d106d0e510e35121d04352a512a510e510e6d0835786f0e0d046d1a6d2a512a51363e2835da1d1a32286d2e092a510e6d14510a111a6d361d
|26=>0xe0d0835286d0e6d2a511a1d0e6d066d78370e0d0e6d0e0d06351a6d0e3d2835786d0e0d06352a5126510e351ab1786d0e0d861f6a6d063506d10a1f1a6d36350e32286d0a111a6d06351a1d3651086d0e5104352a510a1d1a6d2a511a490e51086d286d0a111a6d861d6a6d06356a1d086d06351a110e0d06352a510e32286d
|27=>0xe6d36210e510835861f6a6d0635046d2a5108351a1d0e51086d6a1d1a6d06350a511a6d2a51106d10350e5109c90a0f1a6d3a51364e0e356a6d06356a6d0e0d06352a510e3d28350e6d0e092a512a511a6d0e51286d0e510e352a51286d08352a51106f0e510a091a6d2a511835286d0e6d0e6d1a6d06352e0d0e6d1a0d786d
|28=>0xa511a6d0e6d1a6d2a510a091a6d2a511a6d1a51286d0e091a6d2a510a221a6d0e51046d04352a510e0d346d0835066d1a6d06356a6d1a110635286d0e3e2835346d2a5108350a110a511a6d36210e51283508350e32286d0a1f1a6d2a510e0d1a6d0e6d2835046d2a511a116a1d06351a220e51086d363578350e0d2835286d
|29=>0xe6d1a31286d066d06352e510e6d36110e350a111a6d28352a513651086d260f0e351a31286d340d08351a6d06350e3d28351a6d0e51561f066d286d0835106f0e5128350e350e0d08355635066d78370e0d5637066d363528350e510e352437086d2a5108352435086d26510e35345108350a110a0d1a6d0a211a6d0e512a51
|30=>0x8356a1d06350a1f1a6d0a0f1a6d0a531a6d1a110635241d086d0a0d1a6d36510e350e092a511a1d0e6d2e530e6d1a5d0e6d1a6d0e0d0e0d06351a6d2a510e51086d0a511a6d2e0d0e6d0e51286d086d06352a510e6d0e512a5104352a516a6d063510350e51360d0e35786d0e0d364e0e350e0d0e6d1a51286d0e3e28352e0d
|31=>0xe5106351a6d0e6d286d0e0d2a5108351a6d0e6d363e2835346d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x142000004880000000000000000000000018c01d40128000002200000008000000000000000000
|6,0=>0x2884000000013e626944c88000130224d4472889510a82104418800010061f88000000000001e5400007630e481b9035206910000195030285b50b4215cc000054309ea13482590483086a1048000040107a60e8c1b9833405ca0a54140800004e20948111820203e200000d28000000000000000164
|6,1=>0x48500000000238a00008ba9125220443c48690000000042c88491081206a000080900001fe43ed07d080001f2200007b18f511e283b5075900001d24398c70a8dc51b4436080000d441a62340c6620c8418a600006190bf400002e945c10000166a0000000000000002b9454a8a54000000005190000
|6,2=>0x4ed40001365262a4b5096092a2000000009321251
|7,0=>0x444887910d2217342868411062208440888010fe21f933ea87c50f719ea43ce6790cf189e123ba87650eaa1d1439a8728ce321c2437c86eccdba1b3435e86b0cd421a4434266750cca195432466390c52188230a66050bea00002f285d50b8a16e32d485990b1215e42b6655d0aa1950429885210a221404
|7,1=>0x61e6c2d183a30436008bf117c22f445e08bb117422e535c28b78d6d9ad745a68b40d669ac9458a8b0515ea2b9456a8ac51580aac45508a91150229c45308a51148228c45108a11140227d34f469d9139227024da69a5132a26144ba8968d2b2252449c892cd23a243447e88ed11ba233446068b4d151a264
|7,2=>0x7ca8f88c0003de47b48f609ea23d047988f211e223c047788ee11da23b1375a8ea51d2a3a2373c8e691cb239517264e3d1c5a38747068dfd1be1b7a26ee6dd85b9236e46d48d991b2136046b88d611aa2350469e2d2d1a3a34436808cf4d9d1800066e6ccd198932f26568c9d191a321263a8c68d8b23124
|7,3=>0x994931ce61a4c0397892e4e5b1cb2496052b125424a53942927524d1c9739269244a46a489490e520d23fa47b48ee91cd237a46c38d09191230245c48b091512289c4d48929115220a43d487290d5218a42d48529095210a41e383490592099c0f4816901d202940147fc6fe900003f647e66fc49f6a3e94
|7,4=>0x9f093d12789ced49d29395270a4dd49b4735926924ce4
|8,0=>0xb7276d8ed99db03b5a76a8ed39da43b427678ecd9d983b2a7648ec79d8c3b127618ec19d803afa75e8ebb9d743ae275b8eb59d683aca7588eaf9d5c3ab27558ea99d503a9a7528ea39d443a8274f8e9d9d383a6a74c8e979d2c3a527498e919d203a3a7468e8b9d143a227438e859d083a0a7408e7f9cfc3
|8,1=>0xcee79d0f389e6e3cd679a0f329e623cbe7970f2c9e563ca67940f269e4a3c8e7910f209e3e3c7678e0f1a9e323c6058b4f151e273c487884f0f1e1b3c307854f091e102c1a7828f039e043c0277f8efd9df83bea77c8ef79dec3bd27798ef19de03bba7768eeb9dd43ba27738ee59dc83b8a7708edf9dbc3
|8,2=>0xe6a7cc8f979f2c3e527c98f919f203e3a7c68f8b9f143e227c38f859f083e0a7c08f7f9efc3df27bd8f799ef03dda7ba8f739ee43dc45b7cf6e1ed93dac7b4cf681ecd3d947b1cf621ec22d7e7af0f5c9eb63d667ac0f569eaa3d4e7a90f509e9e3d367a60f4a9e923d1e7a30f449e863d067a00f3e9e7a3
|8,3=>0x7443e827cf8f9d9f383
|9,0=>0x1f0cbe097bf2f7a5eecbdc97b72f6a5eccbd897af2f5a5eacbd497a72f4a5e8cbd0979f2f3a5e6cbcc97972f2a5e4cbc8978f2f1a5e2cbc497872f0a5e0cbc0977f2efa5decbbc97772eea5dccbb8976f2eda5dacbb497672eca5d8cbb0975f2eba5d6cbac97572eaa5d4cba8974f2e9a5d2cba497472
|10,0=>0xf983f2c7e50fc91f903f1c7e30fc51
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 15
def pmP:Nat→Nat
|0=>0x9000000000008800000000008000000000006200000000005800000000005000000000004a00000000004800000000004300000000004100000000004000000000003600000000003100000000003000000000002800000000002400000000002200000000002100000000002000000000001e00000000001800000000001400000000001000000000000c00000000000a000000000008000000000006000000000004000000000003000000000002000000000001000000000000
|1=>0x200100000000103800000000102400000000102000000000100000000000082400000000082000000000081200000000081000000000080c0000000008080000000008040000000008020000000008000000000004280000000004200000000004180000000004080000000004010000000004000000000003150000000002240000000002080000000002040000000002000000000001b8000000000198000000000190000000000138000000000120000000000100000000000095
|2=>0x1022400000001020000000001002800000001001c00000001001800000001000200000001000000000000e48900000000e0d800000000e09800000000c0f800000000c06800000000a13000000000a0e800000000848800000000813000000000812000000000808800000000802800000000800800000000604200000000408800000000402400000000300000000000283e00000000280e000000002800000000002400000000002198000000002068000000002030000000002028
|3=>0x1040020000001040000000001020390000001000300000001000280000001000080000001000010000001000000000000c04150000000a85390000000825990000000824b900000005021c00000005000000000004001800000004000000000002a13800000002a13000000002a128000000028138000000028130000000028128000000028028000000028020000000022419000000022128000000022000000000020028000000020020000000020002000000020000000000010804
|4=>0x80e4f900000080c4a900000080a4b900000080853a0000008085220000008084f800000080843a0000008065bb000000806539000000804c3500000080453900000080452c0000008044ba0000008025b90000008024190000008020210000008005b80000008004b80000007c2c040000007c243500000040a4a900000040682400000038243500000024002c000000200020000000200004000000200002000000200000000000120002000000120000000000104018000000104008
|5=>0x90247b00000090247900000090243d00000090243b00000090243900000090203d00000090053c0000009004bc00000090047900000090043c00000090041900000090027c00000090003300000090001b000000830c1d00000083061d00000082a53900000082a52900000082a52300000082a4bb00000082a4ab00000082853100000082852b00000082843a00000082653b00000082642c0000008225390000008224b90000008205b900000082053a00000081223e000000810538
|6=>0x92243f00000092243b000000922439000000912e1c00000091263d00000091253d00000090e4fd00000090e4f900000090e4bf00000090e4bb00000090e43f00000090c4fd00000090c4f900000090a63d00000090a53900000090a4b900000090a43f00000090a43900000090a03c00000090863800000090653b0000009064bb00000090643f00000090643d00000090643b00000090643900000090253f00000090253d00000090253c0000009025390000009024bd0000009024b9
|7=>0x4d8643b00000490243900000410000800000400243900000290203100000200482000000200201000000200200000000200002200000200000c000002000008000002000004000002000000000001802000000001800000000000d8a4b3000000d8643f000000d8643b000000d0e4f9000000d0e43e000000d0243d000000d02439000000c80020000000b02c3400000098243900000094203300000093261d00000092a63f00000092a53d00000092a53900000092643b00000092253f
|8=>0x40000090000040000018000040000010000040000002000038d02439000038582439000030d0243900003098243900003058243900002418041100002090243b00001cd8643b00001898643900001890643b00001890643900001890443900001890243900001890043900001850042900001800403800001092443b00001092043b00001090643b00001090243900001018043900001000401800000cd8643b000008902439000008020028000008020020000004d8e4bb000004d8e43b
|9=>0x409025bd0000409025bb0000409025b900004090253b0000409024bb00004090243f00004090243d00004090243b00004090243900004090242900004082643b0000408264110000408264090000408224bb00004082243400004080e43b00004080c50300004080a53b00004080a43b0000408025bb0000408025b10000408024b900004080053c00004080049c0000405004290000401000000000400284830000400021b80000400021980000400020b8000040002002000040000110
|10=>0x10091253c00010090a63800010090853900010090243b00010082a43c00010082a43900010082243900010080a53900010058a4b900010050842e0001001c0c3d00008093343d000080922e1d000080912e1d000080906c35000080902c3d00008003320d000080000826000068d0243b00005890041b00005010003800005000001000004890243b000041002429000040d0243b000040d0242900004092643f00004092643b00004092443b00004092243b00004090a43b0000409027bf
|11=>0x400000020000400000010000300bc243d00028290643d000282806027000282004830000280b02c35000200b1243d000200b0243d00020080243500020080242d00020021000c000200000806000180d42c35000180742c35000140d0a43b000140d0243f00014080253c00014080253900014000a52b00014000a4ab000100d5263d000100d0a4b9000100d0a439000100d025390001009c2c3d0001009aa53900010098a43d00010098a43900010098253d0001009824bd00010098243d
|12=>0x450100018000450000018000440900439000440000010000430d0043900043092041b0004289a243900042098243900041092043b00041090243900041090043900041082440300040892243b00040892243900040892043900040892042300040890443b00040890043900040882042b0004085004290004081200300004081200280004080a043900040802003800040802003000040800002000040092443b00040092243b00040092043900040090643b000400902439000400120028
|13=>0x14001082028010120d82439010120d02039010120582039010100dc243d0101005ca43d01010058a43901010058243901010040a4390100305804390100205824390100005c243d0080401004290080001000000040409825b90040409005b90040009824b90040009804bd002300bd242d002180552e1d00210055063d001240210028001040200008001000000010001000000000000800000000000460d0043900045090243900045090043b000450900439000450100038000450100030
|14=>0xa08000d80020800008d02439410120d02039218000982439218000100028200450982439190120d02439100430982439100100d0a53908002090243b040120800039030001d4243d030001400018024001c82420024001c80420014001982439
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40001000000000000000702c1600010000400000000000
|6,0=>0x18000017800f41f0200808000001008024d80008000213076000100012022d82c08001382416514209c000a013d4221f16000640b00190c200080000015001902206000000800000080000030380400011045c08111640400068c80000000c0000504125e202000187871010342a0905811080526184005903034121e1884ce400108ec785a0e8005a0038000001f
|6,1=>0x23400013b848b204000002402
|7,0=>0x1bbf42c295aeda520c4a8db67a84e1963b1a100370cb35e09173753523cbd9e286538aeb0a6349d0d3214adc291ac1e06853298c56123398d22bbbb4807afa2d9a4371f2411472889b1bcec87340db21342b231347869c089dab14818b286adbd698e63a920e646519f8248ad640886ad7a84494ae1249d3262410f0e3a73cd5a3b2044ed1d893ce2cae7257e1f0ce5c
|7,1=>0x5b9111c655a060705d141aee37f7b555f1b2458356c03035cb743f50091280d79005f69e836c3511e01b35996bacbba9cee29d75d126a40ea94e9c3db051318faaf4d9a8ea196074c493c2aaaba0cd2dad5c101b817008aa2c45c6005517e3e97cf2f31a3e47cc39270c9460110084c4d536dc1223d4805e12b014a2bc1a20df9040027cbc0d1c2a04562f4afbdc4b57
|7,2=>0x5de280ca299a4174580ff075ca9
|8,0=>0x53e058ce790956866e3dc115faa70662a2c16753f85a0719f35fcb0e3578ebf8427d8581956897c19bbdf61d58c419b7930a9de8d98fa267e736adea62146d7262ac4a5dfaedb777dca96474d23cfe0aaf4bdbea95277d188532b4e2db39d9d66e7d6176b3cdba1c1c6e1199496c502cee7b3a6b102bd70adcd7532507809669697ce3759788a46ea49d7229ae5577c6
|8,1=>0x11425b5dc37b6b2858579dac4a269dddc04d96364616a1cab3e81586e4059adba36a1062b3703c327ee562cbac8dabe27e160fc456a858ecbc8f23403faed8d2d8bdc2f145dc401799fe434a32fe
|9,0=>0x38581bed23198ec78c72625416dd09bd44c165993676b64da3196fb12ef119ed272537c234181926c43dc5477fb06d1386c732133d65c12c6c29de6223818232a78eab06fa7dc0
|10,0=>0x614218ede676057ae7
|11,0=>0xbb
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 48 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_125 10 roots_125 ops++addP pm 1 dom_23 5 roots_23 ops++addP pm 2 dom_124 7 roots_124 ops++addP pm 3 dom_119 9 roots_119 ops++addP pm 4 dom_63 9 roots_63 ops++addP pm 5 dom_95 9 roots_95 ops++addP pm 6 dom_30 4 roots_30 ops++addP pm 7 dom_94 6 roots_94 ops++addP pm 8 dom_118 6 roots_118 ops++addP pm 9 dom_117 8 roots_117 ops++addP pm 10 dom_122 8 roots_122 ops++addP pm 11 dom_61 7 roots_61 ops++addP pm 12 dom_53 5 roots_53 ops++addP pm 13 dom_126 9 roots_126 ops++addP pm 14 dom_31 6 roots_31 ops++addP pm 15 dom_62 6 roots_62 ops++addP pm 16 dom_116 5 roots_116 ops++addP pm 17 dom_55 6 roots_55 ops++addP pm 18 dzo_108_16 5 roots_108 ops++addP pm 19 dom_79 7 roots_79 ops++addP pm 20 dom_123 9 roots_123 ops++addP pm 21 dom_93 7 roots_93 ops++addP pm 22 dom_47 7 roots_47 ops++addP pm 23 dom_111 10 roots_111 ops++addP pm 24 dom_110 8 roots_110 ops++addP pm 25 dom_29 5 roots_29 ops++addP pm 26 dom_15 4 roots_15 ops++addP pm 27 dom_59 6 roots_59 ops++addP pm 28 dom_91 6 roots_91 ops++addP pm 29 dzo_107_16 6 roots_107 ops++addP pm 30 dom_87 6 roots_87 ops++addP pm 31 dom_60 4 roots_60 ops++addP pm 32 dzo_110_16 6 roots_110 ops++addP pm 33 dom_92 4 roots_92 ops++addP pm 34 dom_115 6 roots_115 ops++addP pm 35 dom_21 4 roots_21 ops++addP pm 36 dom_85 5 roots_85 ops++addP pm 37 dom_101 7 roots_101 ops++addP pm 38 dom_78 5 roots_78 ops++addP pm 39 dom_107 8 roots_107 ops++addP pm 40 dzo_111_16 7 roots_111 ops++addP pm 41 dom_46 5 roots_46 ops++addP pm 42 dzo_109_16 6 roots_109 ops++addP pm 43 dom_39 5 roots_39 ops++addP pm 44 dom_103 8 roots_103 ops++addP pm 45 dom_75 5 roots_75 ops++addP pm 46 dom_71 5 roots_71 ops++addP pm 47 dom_43 5 roots_43 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_23 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_108_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_15 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_107_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_110_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_111_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_zo_109_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_39 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_71 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_43 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_125 10 s (0,roots_125.map (·&&&dom_125)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_125 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 21 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 139 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 11 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 139 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 268 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 268 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 197 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 69 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 197 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 63 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 63 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
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
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_slice_b [(0xcccccccccccccccc0000000000000000cccccccccccccccc,8,10)] (by decide +kernel) lowS_189
theorem lowS_239:Lower true dom_239 roots_239 goal_239 12:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,8,10)] (by decide +kernel) lowS_237
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_slice_b [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000,1,17)] (by decide +kernel) lowS_231
theorem lowS_251:Lower true dom_251 roots_251 goal_251 11:=lower_slice_b [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,8,9)] (by decide +kernel) lowS_250
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_slice_b [(0x3333000033330000333300003333000033330000333300003333000033330000,1,17)] (by decide +kernel) lowS_237
def dzo_154_4:=0x5050505000000000000000000000000050505050
def gzo_154_4:=0x5050504000000000000000000000000050504000
def gsh_154_4:=0x505050400000000000000000000000005050400
theorem lowS_zo_154_4_138:Lower true dzo_154_4 roots_154 gzo_154_4 5:=lower_iso_b (d1:=dom_154) (r1:=roots_154) (T1:=gsh_154_4) [(dom_154,4)] (by decide +kernel) (lower_slice_b (T:=gsh_154_4) [(0x505000000000000000000000000000005050000,0,16)] (by decide +kernel) lowS_138)
def dzo_186_4:=0x505050505050505000000000000000005050505050505050
def gzo_186_4:=0x505050505050504000000000000000005050505050504000
def gsh_186_4:=0x50505050505050400000000000000000505050505050400
theorem lowS_zo_186_4_138:Lower true dzo_186_4 roots_186 gzo_186_4 6:=lower_iso_b (d1:=dom_186) (r1:=roots_186) (T1:=gsh_186_4) [(dom_186,4)] (by decide +kernel) (lower_slice_b (T:=gsh_186_4) [(0x50500000505000000000000000000000505000005050000,0,16),(0x50505050000000000000000000000000505050500000000,0,32)] (by decide +kernel) lowS_138)
def dzo_236_16:=0x1111000011110000111100001111000011110000111100001111000011110000
def gzo_236_16:=0x1111000011110000111100001111000011110000111000001110000010100000
def gsh_236_16:=0x111100001111000011110000111100001111000011100000111000001010
theorem lowS_zo_236_16_104:Lower true dzo_236_16 roots_236 gzo_236_16 6:=lower_iso_b (d1:=dom_236) (r1:=roots_236) (T1:=gsh_236_16) [(dom_236,16)] (by decide +kernel) (lower_slice_b (T:=gsh_236_16) [(0x101000001010000010100000101000001010000010100000101000001010,0,4),(0x111100001111000011110000111100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_104)
def dzo_234_16:=0x505000005050000050500000505000005050000050500000505000005050000
def gzo_234_16:=0x505000005050000050500000505000005050000050400000504000004040000
def gsh_234_16:=0x50500000505000005050000050500000505000005040000050400000404
theorem lowS_zo_234_16_104:Lower true dzo_234_16 roots_234 gzo_234_16 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_16) [(dom_234,16)] (by decide +kernel) (lower_slice_b (T:=gsh_234_16) [(0x40400000404000004040000040400000404000004040000040400000404,0,2),(0x50500000505000005050000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_104)
def dzo_218_4:=0x50505050000000005050505000000000505050500000000050505050
def gzo_218_4:=0x50505050000000005050504000000000505050500000000050504000
def gsh_218_4:=0x5050505000000000505050400000000050505050000000005050400
theorem lowS_zo_218_4_138:Lower true dzo_218_4 roots_218 gzo_218_4 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_4) [(dom_218,4)] (by decide +kernel) (lower_slice_b (T:=gsh_218_4) [(0x5050000000000000505000000000000050500000000000005050000,0,16),(0x5050505000000000000000000000000050505050000000000000000,0,64)] (by decide +kernel) lowS_138)
def dzo_238_16:=0x5555000055550000555500005555000055550000555500005555000055550000
def gzo_238_16:=0x5555000055550000555500005555000055550000555400005554000054540000
def gsh_238_16:=0x555500005555000055550000555500005555000055540000555400005454
theorem lowS_zo_238_16_104:Lower true dzo_238_16 roots_238 gzo_238_16 7:=lower_iso_b (d1:=dom_238) (r1:=roots_238) (T1:=gsh_238_16) [(dom_238,16)] (by decide +kernel) (lower_slice_b (T:=gsh_238_16) [(0x444400004444000044440000444400004444000044440000444400004444,0,2),(0x505000005050000050500000505000005050000050500000505000005050,0,4),(0x555500005555000055550000555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_104)
def dzo_232_16:=0x101000001010000010100000101000001010000010100000101000001010000
def gzo_232_16:=0x101000001010000010100000101000001010000010000000100000000000000
def gsh_232_16:=0x10100000101000001010000010100000101000001000000010000000000
theorem lowS_zo_232_16_104:Lower true dzo_232_16 roots_232 gzo_232_16 5:=lower_iso_b (d1:=dom_232) (r1:=roots_232) (T1:=gsh_232_16) [(dom_232,16)] (by decide +kernel) (lower_slice_b (T:=gsh_232_16) [(0x10100000101000001010000010100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_104)
def dzo_250_4:=0x5050505050505050505050505050505050505050505050505050505050505050
def gzo_250_4:=0x5050505050505050505050505050504050505050505050505050505050504000
def gsh_250_4:=0x505050505050505050505050505050405050505050505050505050505050400
theorem lowS_zo_250_4_138:Lower true dzo_250_4 roots_250 gzo_250_4 7:=lower_iso_b (d1:=dom_250) (r1:=roots_250) (T1:=gsh_250_4) [(dom_250,4)] (by decide +kernel) (lower_slice_b (T:=gsh_250_4) [(0x505000005050000050500000505000005050000050500000505000005050000,0,16),(0x505050500000000050505050000000005050505000000000505050500000000,0,32),(0x505050505050505000000000000000005050505050505050000000000000000,0,64)] (by decide +kernel) lowS_138)
def dzo_170_4:=0x50500000505000000000000000000000505000005050
def gzo_170_4:=0x50500000504000000000000000000000505000004000
def gsh_170_4:=0x5050000050400000000000000000000050500000400
theorem lowS_zo_170_4_138:Lower true dzo_170_4 roots_170 gzo_170_4 5:=lower_iso_b (d1:=dom_170) (r1:=roots_170) (T1:=gsh_170_4) [(dom_170,4)] (by decide +kernel) (lower_slice_b (T:=gsh_170_4) [(0x5050000000000000000000000000000050500000000,0,32)] (by decide +kernel) lowS_138)
def dzo_234_4:=0x505000005050000050500000505000005050000050500000505000005050
def gzo_234_4:=0x505000005050000050500000504000005050000050500000505000004000
def gsh_234_4:=0x50500000505000005050000050400000505000005050000050500000400
theorem lowS_zo_234_4_138:Lower true dzo_234_4 roots_234 gzo_234_4 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_4) [(dom_234,4)] (by decide +kernel) (lower_slice_b (T:=gsh_234_4) [(0x50500000000000005050000000000000505000000000000050500000000,0,32),(0x50500000505000000000000000000000505000005050000000000000000,0,64)] (by decide +kernel) lowS_138)
namespace S_254
def pG:List (Nat×Nat):=[(2,10),(2,18),(2,34),(2,66),(2,130),(4,20),(4,36),(4,68),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(8,136),(12,14),(12,28),(12,44),(12,76),(12,140),(16,18),(16,20),(16,144),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,36),(32,40),(32,96),(32,160),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,68),(64,72),(64,96),(64,192),(80,82),(80,84),(80,88),(80,112),(80,208),(128,130),(128,136),(128,144),(128,160),(128,192),(132,134),(132,140),(132,148),(132,164),(132,196)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|4=>4
|5=>69
|6=>235
|7=>289
|8=>124
|9=>27
|10=>4
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xa7f9558274366642fac1
|5,0=>0xa7f959a6809846f75c6d70be35ec34582744fb0a46df54684b4534344f3341a4a409963c238371913351a2e12f2cf0f2a6bd2a51d28e53280a4272c724ad022b9220ca71faa61f9ed1f7761e68a1b4891b1211a9e81a62118e6a18a1a1836b1692a158f0150e2148b712e5f128d1123b5112221061c10244101db1004d0eb640e3800e2450cd500bafe0a8960a4b9090af073e806dab06ce2063ba0558d04efe049c803ed802c3002725021f1
|6,0=>0x20c952096c1fcf41fc1c1e98d1e4d71df6e1dd311d69b1d5481d2711d07d1ce001c9a51c6d41c6bb1c4901c3451bcf81b1ff1ad4219f2419d2319baf195401917018b181878c184e617a9216e5a16cc01688316632163c715d91155b51496d145cc13bd313aad13122129131214a119a1117151165d115f01113710c6510665101380ff310fbcb0f01c0eb6d0ea3c0e6780dced0d4050d1340cbc00c6970c6100c4220b8780b4a10af9a0a00009ef509c770974308ecd08d4c08c9508b7207a6407670076340761e07445073e80730a071690710b06b730682d05d10059ea0589e058540544404fff04eba04e4a048f20441403dea03c6503a960376f0372a0343d02c6c02a810296402678025410245c024230217401fc301f4301f3401dc401cc801b4c019650147e0125901221010f4010aa00d1300a4c008c900849001ec
|6,1=>0xe1669d6607d2e1aa9c8691b738512e835d97fbee7630e6fc0f6e2726a86a69d1e6646e65fb7617ac5e0ec5781456e9156343556fd5331752c0b526c45128150c835073f4d9cf4b20c49d404975a4957048c07475e3473154710c45e57457e6450ae44f3344e51448a74363e434be412954113640abf40ab3408a63ed483e8a33e8263e6633dd2a3d8ff3d79b3d37a3d0df3a1723a05f39e0c39313366503624c35c4435994353b033ec132dd132bac3221031d3a317523108630c6130be430a52307d6300fa2fb4d2fa5f2efde2ee922e2102dfd62d2ef2c2ee2b4442af6b2ac45289212860d271f4271ae2663a259292528e2491b2465b2448523a1623a0322a7d228cd219c1212ed21001
|7,0=>0x16df916a3916760166c1160eb15fd215ca81522c14eb614e8b149a4147ed144a714235140fb13f65138281370e134861329112a71128ae11a8f10e6d10c9d10a92105dd0fef40fc0e0f4c00f1f80f1dd0ece10e99a0e84d0e4ba0e14c0dee00d9f90d74e0d5640d2600ce520c93f0c8d70c8200c5b80c2640bd290bb930b9d00b7940b1bd0a9470a66c0a5270a4ab0a2f109f2709c3e09a8109734094fd094e90806a07c3207bac0779806ed706db406226060b905f9805cf705b7e05ac00578a056d50567f0566505531054fc054b705444051cb05071050500501804f9004c600490b04566040ab0409403dcd03d7103ae5030ef0303102f9002f6802d9602a89027a00248b02470023fa02371020e00205901ede01ed301d7f0193c018270179c017860149900db700ab500a6f009cb009c00048000382002e40022e00071
|7,1=>0x5fa7e5c3835bcf65b8155af315928e5862a537c3529315289c508f1507204c57d4b7894a8204a6c94a025489d34795e45fcc457324563f4557843ea043e4c4386742f334121b4110b400643ef483ef333edac3ec5d3ec2c3e9043e2b83e12d3cdfa3ccd93b57339fb1398b838c6e36eed36b01354ca350a834d9e333293204d3159230625303853033e2fa312f3112eb4c2e6f82e6652e5f92e14b2cd902c0de2b6582b5702ab142a94528f4c28a72283e5277a7275e426b0426a9a2629f2604325e8825a48258ed2461f23dc12366f22ca322c8122a7e22890220be21a722086a1feb21fc4c1fbce1fa1d1f07b1ec501ea1c1e96f1e54e1df0f1dedc1d5a21d3e61d1df1d1861d0fa1c9e91c88b1c8521c7821c4de1c20c1b6f71ab561a9fb1a5231a12e1a04b19e16199d81926d1925b18f4918663184be183d517f3f179b5
|7,2=>0xd6607d1492c814ac14a6badfab579aa81c4a4fe5a40e89cfa2961db9400291b738c9fe8999c879cc86a5a82cd3800ec7fa467e9d27869e7746f748b7745706e7696ce726c83f69ea468314646e06343160788
|8,0=>0xb579a9a67d92694824bb73a1859b8e577f555ecb516954da174c35946f6b46b2b46a2f45e44438734336842e993dbbe3d0743c7c73a18c380773800d365a33569234f493405031ce4316452fbc62e89d2d15f2cb622bc4b2b4142b1f22ad4d2a1a12994128e88277bd266e1265e32609325b7a2588a2463523c1f2271821e2321d6e21c1d215fd20ada2078f1f36b1eb361eb2b1e0f11d0d81c7671bfc81bec41b62a1b44219ace18cd1184ad1841917eed174e916a971651916049148ef138ec13170128d81284912764114e2114ce0f63a0efbf0ee160df500d2540c8ee0c2ef0b8910b87c0b8210a3270a000091d208e47087ee077a7070dd06ceb061f90551d054cd05479051b7048760434b03dae03b90035130344402fec02df002b46029a001d5401a3a016ba0141100b1b005f000528003d9
|9,0=>0xda1eab6f2692a016a30c56d80541094c6114b7ea489e847e4a389b333030315472d42d2d0b6172e9138e8131db12cc211bb80f44b0ed6508448055f50551504c9002793
|10,0=>0x420a2389322224d0a6d4
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a84444444444444444444444444444444444004400440044004400440044004402aaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaaaaaaaaaaaaaaaaaaaaaaaaaa80005555555555555555555555555555555554545454545454545454545454545454a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a15555555555555555555555555555555511111111111111111111111111111112aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80005555555555555555555555550000000055555555555555555555555500000000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa000000000000000155555554000000015555555400000001555555540000000155555554000000022222222222222222222222222222222222222222222222222222222222222225555555555555555555555555555555500000000000000000000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaa000000015401540154015401540154015401540154015401540154015401540154015402aaaaaaaaaaaaaaaaaaaaaaaaaaa80002a2a2a2a2a2a2a2a2a2a2a2a2a2a00005555555555555555444444444444444455555555555555554444444444444444
|0,1=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a1115511551155115511551155115511551155115511111111115511551111111002a802a802a802a8022002200220022002a802a802a802a80220022002200225555555555555555111111111111111155555555555555551100110011001100aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa00015555555554015401555555555401540155555555540154015555555554015402aaaaaaaaaaaaaaaaaaaaaaaa22222222aaaaaaaaaaaaaaaaaaaaaaaa22222225555555555555555550055005500550055555555555555555500550055005500aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa895555555555555555555555555555555554015401540154015401540154015402aaaaaaaa22222222aaaaaaaa22222222aaaaaaaa22222222aaaaaaaa22222225555555555555555554455445544554455555555550055005544554455005500aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000155555555551155115555555555115511555555555511551154015401540154000000000000000002aaaaaaaaa802a8000000000000000002aaaaaaaaa802a805555555555555555555500005555000055555555555555555555000055550000
|0,2=>0x8888888888888888aaaaaaaaaa88aa895555555555555555551155115511551155555555555555555511551155115512aaaaaaaaaaaaaaaaaa22aa22aa22aa22aaaaaaa800000002aa22aa2000000005555555544444444555555554444444455555555444444445500550044004400aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000001555555555555555555555555555555555511551155115511551155115511551002a802a80220022002a802a80220022002a802a80220022002a802a80220022005500550055005500550055005500550055005500550055000000000000000000000000aaaaaaaa00000000aa00aa0000000000aaaaaaaa00000000aa00aa000000000000000000000000000000000155555555551155115555555555115512aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa802a802aaaaaaaaa802a80555555555555555555555555555555555555555544444444555555554444444400000000aaaaaaaa00000000aa88aa8800000000aaaaaaaa00000000aa88aa895555555555115511555555555511551155555555551155115555555555115512aaaaaaaaaa22aa22aaaaaaaaaa22aa22aaaaaaaaaa22aa200000000000000000000000000000000000000000000000055445544554455445544554455445544
|0,3=>0x88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88888888888888891111111111111111555555555511551111111111111111115555555555115510000000000000000000000000000000000000000000000002aaaaaaaaaa22aa20055005500550055005500550055005500550055000000000055005500000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00880088015555555555555555111111111111111155555555540154011111111110011002aaaaaaaaaaaaaaaaaaaa2222aaaa2222aaaaaaaaaaaaa802aaaa2222aaaa200555555555555555555555555555555550000000055555555000000005500550000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa008800880000000000000001555555555555555400000000000000015555555554015402aaaaaaaaaaaaaaaaaaaaaaaaa802a802aaaaaaaaaaaaaaaaaaaaaaaaa802a805555555555555555000000000000000055555555555555555544554455445544aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00aa00aa00aa015555555555555555555555115555551155555555555400015555551155540002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2222222222222221111111111111111111111111111111111111111111111111100110011001100
|0,4=>0xaaaaaaaa000000000000000000000000aaaaaaaaaa88aa8800000000000000000000000000000000000000015555555400000001111111108888888888888888888888888888888888888888888888880000000000000000000000000000000555555555555555500000000000000005555555544444444aaaaaaaa00000000aaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaaaa88aa895555555444444445555555544444444555555554440044015555555444004402aaaaaaaaaaaaaaa802a802a802a802aaaaaaaaaaaaaaaaa802a802a800000005511551155115511551155115511551155115511551155115500550055005500aaaaaaaaaaaaaaaaaaaaaaaaaa88aa88aaaaaaaaaaaaaaaaaaaaaaaaaa88aa8844444444444444444444444444444444444444444400440044444444440044000000000000000002aaaaaaaaaa22aa200000000000000002aaaaaaaaaa22aa25555555500000000555555550000000055555555555555555555555544444444222222222222222222222222222222222222222200000000222222220000000155555555555555555555555555555554000000000000000155555555111111100000000000000002aaaaaaaa222222200000000000000002aaaaaaaa22222225555555544444444555555554444444455555555444444440000000000000000
|0,5=>0xaaaaaaaa22222222aaaaaaaa22222222aaaaaaaa22222222aaaaaaaa000000001414141414141414141414141414000014141414141414141414141414140002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa22aa22aaaaaaaaaa22aa25511551155115511551155115511551155115511550055005511551155005500aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88aa88aa88aa8955555555555555555555555555555554015401540154015401100110011001108888888888888888888888888888888800000000888888880000000088008800055005500550055005500550055005500550055005500550055005500000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa888888895555555555555555555555555555555555555555555555555555555554015402aaaaaaaaaaaaaaaa2222222222222222aaaaaaa800000002222222200000000000000005555555500000000444444440000000055555555000000004444444400aa00aa00aa00aa00aa00aa00aa00aa00aa00aa0088008800aa00aa008800880000000001540154000000000110011000000000015401540000000001100112a802a802aaaaaaaaa802a802aaaaaaaaa802a802aaaaaaaaa802a802a802a800000000055555555000000005555555500000000555555550000000000000000
|0,6=>0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaaaaaaaaaa8888888955555555555555555555555555555555555555555555555401540154011001108888888888888888888888888888888888888888888888888888888888008800000000011111111000000001111111100000000111111110000000000000000aaaaaaaaaaaa8888aaaaaaaaaaaa8888aaaaaaaaaaaa8888aaaa0000aaaa000000440044004400440044004400440044004400440000000000440044000000000002aaa80002aaa80002aaa80002aaa80002a2a00002a2a00002a2a00002a2a0000000000000000000000000000000055555555444444445555555544444444aaaaaaaa00aa00aaaaaaaaaa00880088aaaaaaaa00aa00aaaaaaaaaa00880088000000000000000000000000000000015555555555555555111111111111111000000002a802a80000000002a802a80000000002aaaaaaa800000002aa22aa2444444445555555544444444554455444444444455555555444444445544554400000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aa00aa004444444444444444444444444444444444444444444444444444444400000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa22222222aaaaaaaa22222222aa22aa20000000000000000000000000000000055555555555555555544554455445544
|0,7=>0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa000000008888888954015401555555555401540155115511540154015555555554015401551155100000000000000002aa22aa22aa22aa200000000000000002aa22aa22aa22aa25500550055005500555555555555555555005500550055005555555555005500aa00aa00aa00aa00aa22aa22aa22aa22aa00aa0000000000aa22aa220000000155555555555555555555555555555401555555555555555555555555555554002828282828282828282828282828280028282828282828282828282828282800000000055115511000000005511551100000000551155110000000055005500aaaaaaaaaaaaaaaa0022002200220022aaaaaaaaaaaaaaaa00220022000000000000000000000000015401540154015400000000000000000154015400000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800005050505050505050505050505050505050505050505050505050505050500000000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaa000000015555555555555554444444444444444555555555555555544444444400000002aaaaaaaaaaaaaaa8888888888888888aaaaaaaaaaaaaaaa88888888888008800000000000000000000000000000000000000000000000005555555544444444
|0,8=>0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aa88aa895555555555555555555555544444444555555555555555555555555444004402aaaaaaaaaaaaaaaaaaaaaaaaaaaa2222aaaaaaaaaaaaaaaaaaaaaaaaaaaa2220000000055555555000000005555555500000000550055000000000055005500aaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000a8a8aaaaaaaa0000a8a95401540154015401540154015401540154015401555555555401540155115512a802a802a802a802aaaaaaaaaaaaaaaaa802a802a802a802aaaaaaaaaa22aa200000000000000000000000000000000005500550055005500550055004400440000000000000000220022002200220000000000aa00aa0022002200aa00aa01555555555555555401540154011001115555555555555554015401540110011002a802a802a802a802a802a802a8022002a802a802a802a802a802a802a80220000000000000000000000000000000000000000000000000055005500440044000000002222222200000000222222220000000022222222000000002200220000000000000000000154015401100110000000000000000001540154011001122222222222222222aaaaaaaaaaaaaaaa2222222222222222aaaaaaaa22222225500550055005500555555555544554455005500550055005555555555445544
|0,9=>0xaa88aa88000000000000000000000000aa88aa884444444444004400444444444400440044444444440044004444444444004400008800880088008800880088008800880088008800880088000000000000000000000000000000011111111111111110000000000000000111111110000000000000000000000000000000000000000aaaaaaaaaaaaaaaaaa00aa00aa00aa0155555554000000015555555555555555555555540000000155555555540154000000000000000002aaaaaaaaaaaaaaa80000000000000002a802a802a802a805500550055005500550055005500550055555555555555555544554455445544aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88aa880154015401540154015401540110011001540154015401540154015401100112aaaaaaa802a802aaaaaaaaa802a802aaaaaaaaa802a802aaaaaaaaa802200225555555555555555550055005500550055555555555555555555555555445544
|_,_=>0
def sP:Nat→Nat
|0=>0xa1b2417180b132b0609180f0e1a2b09020c001a15102a0b1303090b0029281b0f0e270704260809181f050809120b05041b2524171f07110310170b0a1b160b0523130310020b05211a0610201f0006090b1e1d131a08090f1c041b1518160f131a1909180c040d1517160b131509140b130809120b0a1103100f0e03020100
|1=>0xb0a071b020f003804350309170b3106100f003704222b09181f05361510020b0a251509180b313503092a0b0015080934021f0610020b0a2119030933020f0632021f0507250809170b311b03020f300715092d020b132f0610021f051b03020f002808092d160b05111510020c041b022c0f0704190310020c00080914020b
|2=>0x8092e0b0a08090b3f2904220309330b000309120b05070609201f0027351509020c13251510020f133e0310160b051b2615020c071b1517181f130809020b0a3a3d0610021f05150914020b131a092c0f07041b0317330b003506090f0e1319030917181f1909020f3c131b0620181f001b153b0f07041509180b3a04063902
|3=>0x2b061033021f051a0309330b00050d4515020b05040d2403020b05131b2417160b07080309020f05281b242b020b000444060917180b04250809170b0a071109160b0543071a1509330b00041a4209160b05071509140b13060201051308090b0a29281b1924020f130d15020c131a4109201f070809120b0a0d1516020f1325
|4=>0x490415031017160b07190609020c13110310020f050408030948020b051a0809171f0513470309020b0a0706092e160f31070809180b0546041906090f37070424060918160b00190310020f0004360609021f0513260809021f0507350609020c05131a1910170b00041a06090f1c07040d0633021f05130610021f052913
|5=>0x350309170b0a071b2417020b13070809120b05042b0609020f0e07060920181f00260609181f0507350609160b31051a4c09170b07041b160b0a0527074b0609021f0507250610170b0004220609330b00040609120b050704251509180b0a07251510020b00041b0317160b00074a0610020b0513250809180f05040609020f
|6=>0x4060914020b0a07470609160b051315080918160b0a251510020f0704152b092e020b044a0809180b0504080309020f0e07061017331f05130609020b053a1306092a0b0527131b2418160b05071a0309330f05071b1915021f05131b03021f054e071a2410020b0004220809021f05131a0610160b054d1906092a020b13
|7=>0x609170b31070609021f0552130310021f052907080309020b051c0309020b0029131a0309180b054d0d0616020f0513060951020f0004351509160b05130d03021f0005030609180f0e071b03180b050e070d15021f000406092a180b05501a0309020c000706092d160b05074f0609021f05071a1509160b0013060912020b
|8=>0xf000415080916020b310d0617160b000422150309160f070d1516020b0004560610021f0513360610020f050415080917330b044103092a020b071509020b55130d15020b31130415060934021f07060918020c5404150609021f1d131a1509160f13070610020b0053041a08090b050e13222b09021f0507410309020c0725
|9=>0x918160b31150309020b5a072b06092e020b0a22150809180f0441030917021f071a10160b0543070609020f5907040610020b1e05131509020b0a5807220309181f05071a5709170b0704450309020b0a071a1909160b0a071a4109160b0a07150809021f31130809020b31053c08060917160b31152b0918020f041b061816
|10=>0xd2415020f07041b2615020f0704150309021f1d071b2418020b00041106090f0e0704190309020b052815080917160b131b2524170b07041a06102a0b000408095c180b05040803092e020b0a0306093b1f050745190609020f0406090b050e27131b152a020b13070d1516020f07041a2b090b050e071a08095b0b05041506
|11=>0x610507041b2d020b0507040609180b0546131a0310170b0513061060020b000a152b0917160b071a1510170b1304155f09020f0704110610160f05041a5f09180b0504250809020f05130d0302055e130d2417020b07040609020b0a3a070d0616020b000a1a1510021f00045d0610020b05131b1517021f13070d15020b0a13
|12=>0x131b020b640a07040609020f0063041b03020f4607041b020b000563044a0609180b05131a24092e0b07041a09180b056204350609201f0507190309020f13060933020c0013350309020f05131b4515020b00041b2403020b00130d06020c05130632020b0507040809021f0529131b241517160b071a0309020f00131b020b
|13=>0x617181f00040309120b05072506092e0b0a0706090b3f290704670609020b0a131b020b660527041b0617180b3104060917330b54041b020b056507041a1510020b0a13150310021f00570610020f00041b032e021f05071b062a180b00040610020f0e13111509020c07041b0620180b00042b09021f0529071503092e020b
|14=>0x1d060960020b3007670309020b0a07060933020b0a541a0809180c05041509020b0058041b6818020b000406095c180b0513350309020b000a1a1909181f05041b682e020b07041a2b10021f051308030918160f0506090f0037070408090b052928043d0610020b05041906093b0f07041b1924020f07041b0318021f00051b
|15=>0x93b0b0507041b1518160f07040d06020f0e070406090b0537070403090b052907283506092a0b0513561509020b00040609020f6d0704060918160b056c0809020b0a40060201050704251509020f13071a2409020b0013351509160b00044a0610020f0704066b020b0a070809020b056a131a15020c690704080309020b0a
|16=>0x554040809021f052907042b0609020b051d046f0609020b05130403060948020b05071a0609171f051307150610021f00041a1509021f0513070609020b056e070406093b0b000507040609180b0546070457030609021f05071b5d24020b0507041a0310170b050704060920021f0007060918160f000457060917160b0706
|17=>0x609020c07042b030609020b000a060916020b0572070609020b057107041509020b0a3c071b2403020b000704060916020f3100071a15092e0b000704670309020b050704250609180f0507040d06020c05070419030918020b05041a0610020b0a051322190609180b05041b0618020b310504030610021f0005060933020b
|18=>0xb0704410309020f070415730917020b0704080309020b051d040609120b0507040609021f0554130d0620020b0507040609020b000538041a4109170b070422080917020b000422150309021f0507220310020b0507044a0809020b050704350309020f0507040609020c050750030609021f0546071b065b020b0507041915
|19=>0x610020b3105131509020b0576070406092a020b050750150310020b0513250609170b4607040809020b0a053c07251509020b4607040d06020574070408060917160b0a070d062a020b0507041b0618021f000504190309020f0704220609021f0513071b2503180b05070415080916020b0a07060918020b056c041a190917
|20=>0x2b060917020b00040610020b00053c0436060916020b05131b1518020b0513040d060200055e040609020b057707041a241509160b050715060918160b0a0715061016020b00040610020b053013041b2b03020b0a050722060917180b000408060920021f050708060918160f0504360609020b0a05074a0609180b05070403
|21=>0x809020b00041b15020f130704061017020b0a130309020b056313070610020f0e0704060917021f0507500d060205790704350609020b000a04111509160b0507040609020b057807041503092e020b0704066b020b05070403060918020f0513560609020b0a0507250610020b05130d0617021f0507040609020f05380704
|22=>0x40609020b053707040d0617020b0004670609020b0a070419060918020b0a04250809180b05040610020f053c070406097b020b0507040609020b0005580415061016020f070424150610020b00041a1510020b0a0704240809020b00041a09020b0543130708030917020b00041a09170b052307040609020b052313042215
|23=>0x610020f07041a0309330b050706730917020b0a0706097e020b0a07040d06021f051322150809020f07041a15097d0b07047c0609170b05070403060917330b0507220610020b0a0704190610020b31050415060917330b070403060917180b00041b0618020f000424080918020b050415030918020b00042209020b052307
|24=>0x4061033020b3105041b0616020b05074d22260609021f050722150609180f07041a0609180b310504351509170b07040609020b0a0576071b06020b000a13800609021f0507040609020f055807041a0809021f000504250609020b0a4607150609021f311307150610020b0a13060918020b057f041a06020c056907042415
|25=>0x3105130306092e020b0a07360609020b0513040609020b050e07500d0633020b0513041a0609181f0005040609020b05830704061016020b3105060917160b5407041906102e020b05040809020b05400424061017020b07040609021f05820704061017020b3100041a06095b0b05070481060917020b07041b191517020b07
|26=>0x6020b058507040609020b0584070425030609170b0a071b03020b054e07040d06020f051304060920180b0004110309021f050745150809020b05040609020b3105270424080309020b05131509020b053c1307221a0609160b0a0715060917160b1307251909020b050704110609160b0a05072406090b053707040610021f
|27=>0x3020b0513070310020b052907041a06090f0e07040d03020b0005041a2b09170b05070406090b05870704060917181f000419060917020b13044f0609020b050704060916020f00130609021f05860704061017160b051325030610021f0507350609160b000504360610020b05040609021f0005270457190609020f07040d
|28=>0x4890609020b0507041a0809181f05041a0609180b0a05131a191509170b07042b03060918021f051508092e020b04030609020b051d13060917180b0550040609020b058807045d030609021f05071509020b054907041a0610021f051342060917020b07041a09020b05620704350609160f0507040806092a180b05041b25
|29=>0x350309020b0513560609020b0005041a0809170b0a070403060918160b000515060918160b00042b030609020f00041509020f3c070457060918020b05040609020b0a052713240609020b00131a0309170b0a070d06020b000a04680809020b00048b06020c05070406098a020b05070415080916020b0004352409020b0507
|30=>0x609200b0507048d0d06020f07041a0609180c050704190609021f05131a0809020c050704060934021f0507220609180b0a07040609020c0013150809020b0a130610020b058c13560609021f051307220809020b0a070406090b0529072804360609020f050704152b09020b3107041b1517020b13070408060917020b6604
|31=>0x20b00130609020b313007045d260609020b05072b060917021f0507351509020f07042406093b0b0507040609020b058f07041b2215020f07042b0609020c050703060933020b0005110609160f0507041b020b05631307040309020b0507400d0617020b0513048e0609020b0507043506092a0b0507041a4109020f070435
|32=>0xb0537130704060917160b3113071506092a020b130706090b053707045706090b05370704910609020b050704060912020b0507041b033316020b0507900609020b050704220609330b050704110609200b05070406730916020f05071a0610160f05070422250609020b0a0724060917160b07261a0609021f050724150609
|33=>0x50704470609020b000507041b68020b050704060994020b050704080609020f00040609020b000a131a0610021f0507040609020f053c070406093b0b0507045706093b0b050704930609020b0507041a0309180b0513150309020b0013570609020b050704220610021f0507040609020b0a92070406092d020b0507040609
|34=>0x60902950b050724150609020f07042b0609020b310507041b0617020b051307041b2415020b05070408060918020f0504060918020b0a05131b15020f0704152b09020b050704030609020b051d0704350609020b05130422060917020b000704220609020b0a070408060916020f050704060916020b05074d1a0809020b0a
|35=>0x27070403060917020b00070422150609020b0007041b06020b6605070426150609020b0507040d15020b050704960609020b05070406092e020b3105070424060917020b0704080609020b0a0513110609170b0507041a0609020c050704111509020b0507040609020b056207040609020b002907041a0609180b0a05070403
|36=>0x53007041a1509160b05070445060917020b0507040609020b057207042b0609020b0a050725030609021f0507060917180b0a070406091733180b0507040609020b055a070424060918020b050704060918020b31000504250609180b050704060997020f05070406092e021f00050704152b09020b051307040609020b0a05
|37=>0x6092e020b0005041b03020b0513070609020b05079904030610020b0005041a0609170b0513070457030609020b050704190609021f0507040806092e17020b050403060918020b05130609020b053807040609020b050740040609020b0005980704060917020b540704030610021f0507080609020b31000504060933020b
|38=>0x507040609020b055807040806092a020b0507041a0609020f00070422250609020b050704030610020f0507041a0610170b05070441060916020b050704060917021f000704080609020c050704220609020b051307040609020b055413040d0602055e070403061016020b05070609160b059a070424030609020b05130708
|39=>0x704060917160b0a07150309020b0513071a0609181f05070447220609020b05070406092e020b0513040609020b054e07041a0609020b0a051307150609021f0007041a0309021f05070609020b05300704060917020b31130704190609020f070403060917021f0507080609020b051d04220610020b050704350609020f
|40=>0x1509170b07042b060916020b050722150609160b0507041b063316020b050704190609021f00050704150609020b0a1307080609020f05130457240609020b0507047a0d06020b0507040609020b0a540704350609160b0507040609021f05270704060917020b0a13072415060917020b0704110610020b050415060916020b
|41=>0x916020b0507040609020b053c070403060916020b0507080609021f050704030609021f05070609020b050750040609020b058c0704060918021f050704570609020b0507045d1a0609020b050704750d06020b0507040609020b059b07045d240609020b0507040d06020f050704560609020b050704060917160b0513071a
|42=>0x5130704060920020b0507040609020c050704030609020b000507040610021f050704240609020b05070403060917020b050704350609020b050704060916020f05070425030609020b05070406093316020b050704150809020b050704220609020b05070408060918020b0504030609020f0507041a0609170b0507040806
|43=>0x609020b050704060916020b0507040609021f050704030609020b0507040609020b0a050704080609020b0a0507041a0609180b050704030609020b0513070609020b31
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x7280254008a0004
|5,0=>0xc63061d4302c17b60bab05bd82d2c16360aeb055d82a2c14b60a2b04fd8272c1336096b049d8242c11b608ab043d8212c103607eb03dd81e2c0eb6072b037d81b2c0d36066b031d8182c0bb605ab02bd8152c0a3604eb025d8122c08b6042b01fd80f2c0736036b019d80c2c05b602ab013d8092c043601eb00dd8062c02b6012b007d8032c0136
|5,1=>0x1a850d1a8675832ec1925
|6,0=>0x1b138d6dc6a8e34d71a338cfdc670e331719538c8dc638e315718738c1dc600e2f9717938bb185cae2df616c38b45c594e2c3715e38ad5c55ce2a7715038a65c524e28b7142389f5c4ece2706134b8989c4b6e2547126b8919c47ee2387118b88a9c446e21c710ab8839c40ee20070fcb87c9c3d6e1e470ef3075dc3a0e1c970e1386edc368e1ad7
|6,1=>0x28f3945dca20e5097281393edc9e8e4ed72733937dc9b0e4d172653930dc978e4b572573929dc940e49972493922dc908e47d723b391bdc8d0e461722d3914dc898e445721fb10e1c862e42a7211b9071c82ae40e7203b900587f4e3f371f638f95c7bce3d771e838f25c784e3bc61dab8eb9c750c3a171cd38e4dc718e38571bf38dddc6e0e3697
|6,2=>0x36c39b45cd94e6c3735e39ad98d5ee6a87350b9a6d8d28e68d7343399fdccf0e67173353998dccb8e65573273991dcc82c63a7319b98b1cc4ae61f630c39845cc14e60372fe397d5cbdce5e772f039765cba4e5cb72e2396f5cb6ce5b062d4b9689cb36e59472c6b9619cb00c57972b9395adcac8e55d72ab3953dca90e541729d394cdca58e5257
|6,3=>0x2005cff4e7f373f639f95cfbce7d773e839f25cf84e7bc63db31ebdcf50e7a173cd39e518f1ae78673bfb9de1cee2e76a73b1b9d71ceaae74e73a3b9d01ce72e7327395b9c91ce3ae7167387b9c21ce02e6fa737a31bb5cdcce6df7
|7,0=>0x4f8c27a613c4e9da84e94272a1386e9bb84d9c26ae1348e99c84ca426321309097d74bb3a5ba12cd095f74ac3a54212910941749cc24c612530921848cc2449d2150902847d423ca11d508e2846dba34e119708c3845dc22ce1158e8a4844e4225211190885743ec21d610db0865842ec2156109ce846841f420da105d0826840f4205a101ee8087
|7,1=>0x5f1c2f7597ab0bce75e342efa176d0bae85d342e7a172eeb8f85c3c2dfe16ef0b7075b442d8216b2eb5185a4c2d0616730b318594c2c89d6350b12858542c0a15f50af375763ab9215baead585673ab1a157d0ab6855742a9dd53f0a9785483aa2215010a788538429a214c10a597528c292614830a398518c28a614430a198508c2826140309f98
|7,2=>0x6eabb739db8d0dbe86dbbb6be1b50eda086cc43645db130d8186bcc35c61ad30d6186ad3b54dda98ed44869e434d21a590d24868e434521a190d04867ebb3d619db0ce5866ec3356199b0cc6765f432da195eeca7864fc325e191f0c87863fc31de18df0c67862fc315e18a0ec488620bb0e618630c298610c30661824ec0a860142fea17e6ebeb8
|7,3=>0x7dfbbede1f5f0fa787d03be621f210f8887c0bbde61ee4ef6a87b1bbd6e1ea8ef4c87a333cfdde70ef30879443c821e310f10878443c021df2eef18774c3b861db30ed187653bb0a1d750eb377563ba95dd3cee977747c3a1e1cff0e7787383b9a21cc10e588728bb9261c830e398718c38a61c44ee1a87094382a1c050dfa86f9437addbc8eddc8
|7,4=>0x10c0785c442c22152f0a2784d4424a21151082883d441ca20d51063782dc414e20971043881dc40ce20571023880dc404e2018f00487fe43fd21fd90fe487eebbf561f9b0fc67
|8,0=>0x967ccb1e257d32b6895744a9a253b329589473ca1664f932748935cc98e24b712538925c490a6475123199144c8822431120f99034c7f663e931eb98f1c476a63a6f1cb88e14c6ea236511aa88d14466a2325118a88c0cc5e622e3116898afcc55e229f114788a0b44e622613128888fcc45e221d3106887ecc3d261daf0e5886f3c35de19f10c78
|8,1=>0xa5d452c6695314a18a4c4d245e91314818a3d3d1ca28d334609a2bcd13e288f143e9a1b450ba284d141e8a0b45036680cf3fd99fb3cfba27cd13dd99eac4f36278933bc89dabceb62749339d79cac4e36270b137d89bac4db266c9135b99a9c4d2e2685333a899944ca66643131a798944c2a260332f89978bcba625c312d89
|9,0=>0x56566b1b15858abe4d5d22adaf5649aaebd5562a9935448a9e454ce6a5535228a8d4544a2a1515028a7ccd3c629d314e18a6d3d34a299514c28
|10,0=>0xadac56b9eb4d159e8
|11,0=>0x15bd7
|_,_=>0
def wAt:=mkWire dB 156 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x80941c1904064081504154182502044141909064140d03074181141044541f0506434300b0a42421070641c110504454110b0542419150741815070641411024041411060744c5406054101d33150940006184081d061340011160541009070644c152e03014110b0442419020340c1504064884c0b0542419050641009040743430070542c2909084181d060441411
|1=>0x25000681102064105518044081d0b054102d020645c11020542009060740901060744c5406054101d0b0445c13070240815070546019020742c150302418110907414210b0a4101504074181d08174081506074142d0200400110507454110b0541019090740019070540819090740019070542025021341c110b044181d090742c11130644c090704420252207c101d
|2=>0x60541c190402418150b0444c1504074241902044142d15024141906054141d080941c19000301419050741c110604420251605c081107034282d0604410151507c181504054381d1605c0811040740819060441c15080942c110607418150705420250b044181d2e0305c1d020540069020641c15090746811020644c190e0645817020440815130241c11090742c11
|3=>0x6094081105064b80c18054081d13064241d0407408190506534191305c101d050b45819020441811070442c3609084181d250005819020442c1117034081504064241907044242106074181504054142d080941c1905064101509064080d030541019024340c170406418150b054202506074a81d020a410151d0440802070544c19020740855060542c15131541c11
|4=>0x90744c19070442c15020442c150906410551507418150b044241906044081d0507418250b0441c09070541811024044c54050641c11130542419040742c11090741019060541c15160542419020442c1504074241d1605c0811030541c110604420150b0541c190a0b4141d050444c09070442c1506184081d060940c1506044141d0b0a42421070641c11050441055
|5=>0x631400112505c0c09060442819090641411090742c11050745c13020542c1502044081d050742029040541c19090640811050b4081d060545815040240c6102074101905044181d13150181504074343008094181d0b0a414110940414111315014190704410191d064080205074181d02074282d04054081d430240c1706044681d0206418010b044141d0b0440819
|6=>0x60441015020381019050641c15090640c150406408110b05400110507400090507408191d064000b0705468110b054081908094181d0b0a4141102064101d09074141102154541d02074181509064001105074141d06044241d0b0440856050642c11700744c56050641c11024d44c17040740815040b40819070441c1506054241d0b0441c110b0440819050655c08
|7=>0x6044544e06054101d1507414090206414190b05410191507c1815020541019024044c54050641c11040742c110006c1c1527044601b02074541f05024081905064181d170640815060442c111502414190709468150206438191605c08111a0742c15020642c29050444c1b070442c112505c0c09040645c4d02054101d0a0b4101506054141d030741811074340c17
|8=>0x50741c253305c4c09040740c1d040642419050445c1905024081d05074102d060745c130205408110b054941f0302418110e0645817020441019090744c15040740c63020741811090741419060441c112505c0c090406494171a0440819750bc341109084181d020441015020541c19090642c1102074141d0604420150b0541c191a054102d020640c0909064081d
|9=>0x704424190b054140904074241d05044cc1b130241c111605c241d020442c150b0444c1b02054101d7a0bc083509084181d1a0740819094044c5406054101d0b0540c61020741811090745819020441c110b0442025020541c1904274601b020740c1d09074080e06044941f16064081109064181502074101d070542c3609084181d150440811050641419070940811
|10=>0x307c10191a054081909074241d040040019070541811070240815070541c150b054081d0906410154706c881d150241419071b42419020541c151d064000b07054181d03024081d060440c7702008141d06044ac0b080441c190b054241d020441419050741c25050641c25020642819070641c1504054b81b170740815062e86015020741c15070645409050641419
|11=>0x1706408150b0440855050b4081d0605400111a074140902064141918038081d060441015050741c110906409051507c18150b0449417030241811060542c1113054101d05064101d0907414113106c00110507424320a0b41015090742c1505064581d04024081904064081502544001b070542025070442c11060740855060542c15070645c1f05024081905065cc09
|12=>0x2207c540906054140d04074101907064681502064101507154681f020644c1507044241d0b045581f131a40819070442025060744c09040742c11040041c2502044141d02044000909074001907054181d131501815040745411090741815070940011020541c152a074082904055cc150307c1019050242419150741815090744c1513024101d1305c2419070448813
|13=>0x60740829050441825070440c0906044241d0215814190b05408191605c081109084181105074181d06134095703000141d060442c1107024081507054142d070540811070440811070940815040742c11090740c0906044941f1a044081909074601b0b044081d080542c150607414090302418110704420250b054181d1704c1c09020541c15060442c111a07c0819
|14=>0x5074601b02074541106054141d040741015020540819040642421070641c1504054141d07064541305065a419090c82c29040541c1506074081105064681d02064181d0b044081902074541d050240819050641c0d040b4081d060441c19170740815060541019020542c1104064f01d02038101909074102d020641c1141044541f06054ac170307410190b0540821
|15=>0xb054541f0206414190d05420250b054181d02074282d020641015080541c110b044181d06074282d020641015040b4801d1704c0815070547c15070442c1106054101504074181d07044241d1606c08112507c5819020441815061344c1504074181509064081504074186104064081d0407418cd18044081d0b054141d0307418110b054080e040641419310640011
|16=>0x160740811060442c150307c1811020442c1502064241d051a468110206414110204454110205418150422868150b044541106054101d13054cc1713024101d2204c88111502418150205420110b044181d0802418150b0541c19150241815090642c150b0a41015080441c190b054681f0206424193306c4c09151301419060441c11040742025020541c19160540811
|17=>0x70640819040540069020641c150906454130506409990004c141d070542c15060741c150704414110b0440819090740c0b040642c1557020901d0a064141106024101902074101d050741419060441c11150241815090742c111902c201507064b80c170740815040655c0b063144c15020544c15070455c0b24074281905044901d0a06414113102c281d040542419
|18=>0x607408151a07c08190a0b408190405418151a07c08192b05c2011070640856060541c1502064081d05044581f0204418110b054541105064184d13054101d090640815040742419150441419020742c1506074101502074101d0605424190b0541419080441c1902008141d06044601902074101d1706408150705414111502418150607408110b0544c17020441c11
|19=>0x305c1019040542011070642c1103024181102054081d0405460110207408151d044000b050740c1502074181100044081d050740c090207418110b0546013020742c1100024141d050644c190704410151806c081d040640815070541c151502418150906400130507488131502414191b07414190906654191607c081100044000905074541102054181504054101d
|20=>0x6074241d0204418111a05c0819020441c1103054101906074000905074101d0406424191317c081504074181105074241d020640815040741c91030541019080542c11060745c1d02054181d04064081d040749c111806c081d13150141907044000e04064001b020541c1506044241d0b044181d00044141d3305c4c09070440811020641419072285c19020541d0d
|21=>0x20641c110705414190b044102d0206410193305c4c09070444c1502054101d080542c15060742c110205410190002c141d06074681502064241d080242c1506074ac0b080441c1906074082905044142d020641c15041a46815020641811090742c1502054081909074541f0204414190b044081507054181d0b0a4141117064081504074101d0006c1c150b0d82421
|22=>0x2054181503074081106044540902044141916074081109064102d000641c1504074181504054101d0b054181d0a0641411020d424210607410150006c1c15020440821060742c111806c081d05044081504074541102054181509074681f020641c15020441419050240811050441419060441c110b044081902074540905064601502074101d03008141d060441015
|23=>0x90742c110a064141102054101902084181d020442c15030241811160740811050641c1915024181502074181d040642c1502064081502044181d0302c18110204418110b044181d060442c111306c1c111606c0811020742c112407428190504428690206410150d044242106074205e02054181d0a0641411080942c15060740c61020741811020540811070441809
|24=>0x20442c1106044141106074141102064081d07044181113054101d1704c08150b0a41411050741811
|_=>0
def oO:Nat→Nat→Nat
|4,0=>7
|5,0=>0x798000000000000000000000000000000000000000000000000000003a2000000000000000000000001c1000000000d10000032200000c08162000000000a88000028200000000000000004c400000000000000009080000000000000000000000000006a8000000003040000000000001d40000000
|5,1=>0x56c00001328242
|6,0=>0x112622044298000100a1f4c00007c10f261e04000000000001dc43a9073200001b940000695000019c800000000000000000000000000000000000000c86000031885e50000000000005b30ae8000000005610a2a0000000000009a800002428000086a000020903d4070a00001a20000000000000000313
|6,1=>0x66a0000194600006398c61184800000000000000000000000bf300002f845e88b94000000000000b81000000005a20b04000000000000000156a2a840000000000000000000a8214e2289450880000000278c4e889c1000000000000975000000004928000000023cc0000000000000004618000
|6,2=>0x494c000000000004814000000023a6461400000000000000000000000000000000011710000000089290d5214600008321015000000007ea000000003e8c000000000003e447aa000000003c8c7798ea5000039cc0000e611c6638846ea8d94000000006c08000000000006a200001a2600000000000
|6,3=>0x5b0c00016750000000000016522c46000000015d52b0a00000000000000054d400000002a420000a79800029680000a50947328a4508c00013d527640000000000000004d9498a92d4250a00000000000
|7,0=>0x440600010e221930000858d09220e40000829103220333fe80000fe19f843e887cc4f909ee43d480000f399e343c067710ec99d633a6673d0e5a1c8338a6708cdf9800037686dd0d9a1b0335a66a8cd32000034486790cd999740000650c000190431a66250c2a181400005f8cbd980002f065dc4b9a16f4
|7,1=>0x59a6b25162a2c1457c600015d9ab740000acd157a2ae10000aa900002a64546600014fa00005368a60d4a2291351e4a2d000000005106a14d40a27d44f289d8d39226e44d489a08000000000009911318a6034b8896112a9a5414a26938d2522464000090cc00023f447688dd119a22f445a48a8d139a234
|7,2=>0x6d28d95000000006c280001aea35940000d551a91b4f300000001a6180006908d111a0233d30000ce5000033630000cd45999000065e8000195a000064e8c98400032246422c7518ca31630000c491879b0c36108c111809afd45f28be057a22f135da8ba8c0002e915cc6b8916f22db35b06b54d68a2d01
|7,3=>0x82080002069c0a380c9009000040027f880001fc23f447e08fb11f4200007c88f811ee2000000000001ec9bd547a280001e6a3ca3000000000003c647848efcdde93b9476a8ec51d6a3a940000e951d19000073e80001cda39747268e485c88800071e4e30dc4238537046dfcdbe937946ec6dc91b7236d1
|7,4=>0x46440000000230245c4000116122a9c51489c712cc00044748887104c00043d40000000000043a386c90c9217242b38507091210241c4830800000004144
|8,0=>0xa487484e8f1d1b3a307454e8995103a1a7428e839d043a0273f8e7d9cf839ea73c8e779cec39d27398e719ce039ba7368e6b9cd439a27338e659cc8398a7308e5f9cbc397272d8e599cb0395a72a8e539ca439427278e4d9c98392a7248e479c8c39127218e419c8038fa71e8e3b9c7438e271b8e359c683
|8,1=>0xbaa7748ee79dcc3b94571cee21dc13b7c76ecedc1db53b6476bced61daa2b4e7690ed09d9e3b367660eca9d923b1e7630ec49d872b087604ebf1d7b3af075d4eb91d6f3ad875a4eb31d633ac07574ead1d573aa87544ea71d4b3a907514ea11d3f3a7874e4e9b1d333a6074b4e951d273
|9,0=>0x1830b0516082c0c5810b0116002bfc57f0afd15f82bec57d0af915f02bdc57b0af515e82bcc5790af115e02bbc5770aed15d82
|10,0=>0xc2238407078e0e1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x200000000000018b100000000018100000000001200000000000108000000000010000000000000a100000000000a000000000000921000000000087000000000008500000000000830000000000082000000000008100000000000800000000000060000000000004410000000000410000000000040000000000002800000000000210000000000020000000000001c1000000000008000000000000400000000000030000000000002100000000000200000000000010000000000000e00000000000010000000000000
|1=>0x129310000000012921000000001283000000000128210000000012131000000001200000000000118210000000011000000000001089000000000108200000000010410000000001006100000000100300000000010020000000001001000000000100000000000008e2200000000070000000000006c300000000004800000000000443000000000044000000000004020000000000400000000000030100000000002981000000000281000000000028000000000002440000000000220000000000020200000000002010
|2=>0x4263a0000000042440000000004213b00000000420000000000040060000000004002000000000400100000000040000000000003af21000000003a931000000003a82e000000003880c0000000032f390000000032c2300000000280000000000022603000000001b3b1000000001abb1000000001a931000000001710100000000169b00000000015820000000001581000000000149500000000014820000000001480000000000144100000000014030000000001383000000000129f100000000129710000000012963
|3=>0x1129310000000110910000000010e93100000001059b10000000104000000000010200000000001009300000000100100000000010001000000000d296100000000c01c100000000b9a1000000000b2c4100000000a6c510000000092ba900000000929e1000000009293100000000902a00000000090040000000009000000000000848200000000080800000000008005000000000800100000000080000000000005681000000000529b100000000529a10000000052931000000005133800000000509c10000000042d33
|4=>0x400800000000040002000000004000000000000372931000000035793100000003529510000000352931000000035192100000003508300000000350030000000034281000000003420100000000331931000000031793100000003128100000000310931000000030204000000002509310000000250830000000023bb31000000023291100000002139510000000201bb80000000201800000000020002000000002000000000000186971000000018693100000001400a0000000014003000000001400200000000116931
|5=>0x200001000000020000000000001838e0000000008bae370000000832e2b00000007041410000000608330000000060080000000006000300000000600020000000051e931000000051693100000004d292100000004b28010000000498b280000000492933000000049293100000004908a0000000048080000000004800100000000454150000000045292100000004508600000000450161000000044441200000004421e100000004404200000000440010000000043ab31000000041a93100000004129390000000412931
|6=>0x6032c610000004032e3f000000402aa0300000024c00000000002418b00000000241293100000021109310000002110000000000210e93100000020929710000002080870000000205abb1000000205a9210000002050a80000000204210000000020411b100000020408b00000002040020000000203ac210000002032d31000000201ab8000000020183000000002013b390000002012d330000002012bb900000020129610000002012931000000201283000000020109b1000000200220000000020009210000002000050
|7=>0x400bad1100000400028100000040000001000004000000000000201009300000010050320000000a08613800000086300310000008613131000000861293100000086031a10000008432131000000841a93100000084169310000008400800000000825691100000082008000000008186931000000811697100000080a6c110000008034091000000802253900000080204100000008016939000000801693100000080161b100000080129b100000080121100000008010000000000800081000000080008000000008000030
|8=>0x821028100000082011b3a00000806810010000080493131000008021b3310000080213bb900000802139b1000008021393100000802131b1000008020319100000802019a100000801069710000080082971000008001b931000008001ab3100000800139b1000008001393900000800129310000080011bb900000800100100000080010000000008000287100000800008000000080000020000004241292100000420a6c11000004209297100000420928400000042090c00000004208285000000420820100000042012931
|9=>0x20205298100002020523390000202052328000020205093100002000400b00000200012000000020000102000001400020000000100512151000010051211800001004569510000100452d3300001004529710000100452050000010045086000001000529790000100052328000010000405000001000040100000100004001000008a00613800000880969310000088091121000008809003000000880900200000088082820000008808080000000821108a00000082110810000008211019100000821029310000082102911
|10=>0xc001004032837200000061b9311801004832833040080001a938040000001a939020000005293b01003400129310100340000020010004001082001000004929e101000004929a101000004921b1010000041293101000004008a00100000013931010000001293100c000001a908002080309ab38001900083082f0004000098b200002804030e2b0001c04832e370001006030c310001004072c330000c05830023000080583ae2a0000805032023000080101abb80000242010000
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>2
|5,0=>0x2a000421000024000000000000000000000000000000014000000000000001a000000e001400034080000050000d0000000000680000000003400000000000000002400000680000000180000
|6,0=>0x3406001800060282d0000000000000003000a0b06c00000142800000b80300000000060af80000000000008143e83400000c0b06700000002f00001ba00000b80000000003e00088a00800350a4001a1803000000019c10070689800780001c0000000000000000001a000200050ca05000001f10000001a6100000005f8006200188010c9f538002600000000003
|6,1=>0xc00210000000080880000612a8000000000d000005f0003e0018800b0040382c00680d80000000008432120b80000000000c0000001440000023a4000000000000000000001a00001a2e20f8013cbd00000b200000e00000000a03a000000c0850000b0001a020a81e1f000003400000002400020000000
|7,0=>0xfaf1047c088003f3a001263c1a0000401460f801ea00090448a5e03a9800008587d2e5f3938dd46ba201c0000000f034117c090222808a784f4800290003584d3d2e7e0404409030880164ef002e28448000667a045b00006d097a757c3e6d800229841a503e0411525c230672b406009ba9580d80f81286000a8500657000100005181199a190004408fc018a0f32b
|7,1=>0x588003f0855090000831002943265819f600a59d5d600000002236158022c1100000006e9b00c0ea85d37e7f4c000dc0e00278019eac912f8ce003d844e8030187c10b70fb90a4281f1f400007c801d8e0000ec313800001e2005dc817287002a4008f000a00e007f8000a008607001065f0c4c80e0040460039d8481c7a4086a2a112007c001c789b4e6030188e529d
|7,2=>0x3f000023adc000843e4c021a4003e018c001270000000031d09556772dbf6584744800005d
|8,0=>0xab4bab88096b7a9cee4dd452b28691d8e355ad31a2f1142cc9163376ace373990b142cd3ad8fdab3e5ab0d391aa692d922529a4cccd7a08f60f477a22a6323581bd984aa0352491c8718c22d951c124af046d42a6f38a49a0043813de1f1f574288896642468ae77f4d4e090aca3a9b3c1cb9a615416cd21b13abd4989174b26896840f220c0c563b5918a1
|9,0=>0x10a30af829feb0da2b4cd6919743da54654cc41429272a81e44e511bdcf12
|10,0=>0x739354041
|11,0=>0x3f
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 52 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_206 8 roots_206 ops++addP pm 2 dom_138 4 roots_138 ops++addP pm 3 dom_248 8 roots_248 ops++addP pm 4 dom_246 9 roots_246 ops++addP pm 5 dom_190 9 roots_190 ops++addP pm 6 dom_124 7 roots_124 ops++addP pm 7 dom_158 7 roots_158 ops++addP pm 8 dom_238 10 roots_238 ops++addP pm 9 dzo_154_4 5 roots_154 ops++addP pm 10 dzo_108_16 5 roots_108 ops++addP pm 11 dom_252 9 roots_252 ops++addP pm 12 dom_150 5 roots_150 ops++addP pm 13 dom_126 9 roots_126 ops++addP pm 14 dom_116 5 roots_116 ops++addP pm 15 dom_122 8 roots_122 ops++addP pm 16 dom_222 9 roots_222 ops++addP pm 17 dom_174 8 roots_174 ops++addP pm 18 dom_220 6 roots_220 ops++addP pm 19 dom_62 6 roots_62 ops++addP pm 20 dom_244 6 roots_244 ops++addP pm 21 dom_214 6 roots_214 ops++addP pm 22 dom_94 6 roots_94 ops++addP pm 23 dzo_110_16 6 roots_110 ops++addP pm 24 dzo_186_4 6 roots_186 ops++addP pm 25 dom_188 6 roots_188 ops++addP pm 26 dzo_236_16 6 roots_236 ops++addP pm 27 dom_118 6 roots_118 ops++addP pm 28 dom_58 5 roots_58 ops++addP pm 29 dom_186 8 roots_186 ops++addP pm 30 dom_60 4 roots_60 ops++addP pm 31 dom_182 6 roots_182 ops++addP pm 32 dom_92 4 roots_92 ops++addP pm 33 dom_156 4 roots_156 ops++addP pm 34 dzo_234_16 6 roots_234 ops++addP pm 35 dzo_218_4 6 roots_218 ops++addP pm 36 dzo_238_16 7 roots_238 ops++addP pm 37 dzo_232_16 5 roots_232 ops++addP pm 38 dom_216 5 roots_216 ops++addP pm 39 dom_204 5 roots_204 ops++addP pm 40 dom_172 5 roots_172 ops++addP pm 41 dzo_250_4 7 roots_250 ops++addP pm 42 dzo_170_4 5 roots_170 ops++addP pm 43 dzo_234_4 6 roots_234 ops++addP pm 44 dom_30 4 roots_30 ops++addP pm 45 dom_234 9 roots_234 ops++addP pm 46 dom_104 4 roots_104 ops++addP pm 47 dom_198 5 roots_198 ops++addP pm 48 dom_166 5 roots_166 ops++addP pm 49 dom_242 8 roots_242 ops++addP pm 50 dom_78 5 roots_78 ops++addP pm 51 dom_46 5 roots_46 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_154_4_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_108_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_110_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_186_4_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_236_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_234_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_218_4_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_238_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_232_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_zo_250_4_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_zo_170_4_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_zo_234_4_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_46 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xcccccccccccccccccccccccccccccccc,126)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccccccccccccccccccccccccccccccc,126)],[(0xffffffffffffffff0000000000000000,64),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffffffff00000000ffffffff00000000,96),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 69 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 69 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 235 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 107 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 235 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 289 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 33 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 289 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 124 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 124 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 27 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 27 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 4 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 4 0 = true)
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
def isoMvS_223:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_iso_b isoMvS_223 (by decide +kernel) lowS_191
def dzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def gzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0e00000f0e00000e0e0000
def gsh_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0e00000f0e00000e0e
theorem lowS_zo_235_16_104:Lower true dzo_235_16 roots_235 gzo_235_16 7:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_16) [(dom_235,16)] (by decide +kernel) (lower_slice_b (T:=gsh_235_16) [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a,0,1),(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c,0,2),(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_104)
def dzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
def gzo_219_4:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0f000000000f0f0e0a0
def gsh_219_4:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0f000000000f0f0e0a
theorem lowS_zo_219_4_138:Lower true dzo_219_4 roots_219 gzo_219_4 7:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_4) [(dom_219,4)] (by decide +kernel) (lower_slice_b (T:=gsh_219_4) [(0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a,0,1),(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000,0,16),(0xf0f0f0f0000000000000000000000000f0f0f0f0000000000000000,0,64)] (by decide +kernel) lowS_138)
def dzo_187_4:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0
def gzo_187_4:=0xf0f0f0f0f0f0f0e00000000000000000f0f0f0f0f0f0e0a0
def gsh_187_4:=0xf0f0f0f0f0f0f0e00000000000000000f0f0f0f0f0f0e0a
theorem lowS_zo_187_4_138:Lower true dzo_187_4 roots_187 gzo_187_4 7:=lower_iso_b (d1:=dom_187) (r1:=roots_187) (T1:=gsh_187_4) [(dom_187,4)] (by decide +kernel) (lower_slice_b (T:=gsh_187_4) [(0xa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0000,0,16),(0xf0f0f0f0000000000000000000000000f0f0f0f00000000,0,32)] (by decide +kernel) lowS_138)
def dzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def gzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000fffe0000fffe0000fefe0000
def gsh_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000fffe0000fffe0000fefe
theorem lowS_zo_239_16_104:Lower true dzo_239_16 roots_239 gzo_239_16 8:=lower_iso_b (d1:=dom_239) (r1:=roots_239) (T1:=gsh_239_16) [(dom_239,16)] (by decide +kernel) (lower_slice_b (T:=gsh_239_16) [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,0,1),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,0,2),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_104)
namespace S_255
def pG:List (Nat×Nat):=[(1,5),(1,9),(1,17),(1,33),(1,65),(1,129),(2,10),(2,18),(2,34),(2,66),(2,130),(3,7),(3,11),(3,19),(3,35),(3,67),(3,131),(4,5),(4,20),(4,36),(4,68),(6,7),(6,14),(6,22),(6,38),(6,70),(6,134),(8,9),(8,10),(8,40),(8,72),(8,136),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,18),(16,20),(16,144),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,36),(32,40),(32,96),(32,160),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,68),(64,72),(64,96),(64,192),(80,81),(80,82),(80,84),(80,88),(80,112),(80,208),(128,129),(128,130),(128,136),(128,144),(128,160),(128,192),(132,133),(132,134),(132,140),(132,148),(132,164),(132,196)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|9=>10
|10=>28
|11=>19
|12=>5
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0xcccabcc533b37187f84b6980554b8439dc63265e174c00e907
|10,0=>0xe0b5be03e3dd4c1cf591ccd75cc8dec60bdc4f35bcdb7b677695c0a727116a4c361e72617d25b461484b33ce2438ec334a1233e54327281ed001d99b1a51e0ea0705c7d03461
|11,0=>0xfb047e3441e0c25bd5f9ab1aaa763d96f2d9580172f53727db502ee4aaed49315388e635d8f34b122bfee06fa0064bf
|12,0=>0x9e29199b3f4b32f389a10eef7
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00fffffffffff0fff0fffffffffff0fff0fffffffffff0fff0fffffffffff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000fffffffffff0fff00000000000000000fffffffffff0fff0ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffff00000000000000000000000000000000
|0,1=>0xff00ff00ff00ff00ff00ff00f000f000ff00ff00ff00ff00ff00ff00f000f0fffffffffffffffffffffffffff0fff0fffffffffffffffffffffffffff0fff0fffffffffffffffffffffffff0f0f0f0fffffffffffffffffffffffff0f0f0f0ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f00ffff0f0fffff0f00ffff0f0fffff0f00ffff0f0fffff0f00ffff0f0fffff0f00f0f0f0f0fffffffff0f0f0f0fff0fff0f0f0f0f0fffffffff0f0f0f0fff0fff0fffffffffffffffffffffffffffff0f0fffffffffffffffffffffffffffff0f0ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000fffffffffffffffffff0fff0fff0fff0fffffffffffffffffff0fff0fff0fff00000000000000000ffffffffff00ff000000000000000000ffffffffff00ff00f0f0f0f0f0f0f0f0fffffffffff0fff0f0f0f0f0f0f0f0f0fffffffffff0fff000000000ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00
|0,2=>0xf0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f00
|_,_=>0
def sP:Nat→Nat
|0=>0x8148801758610308120034624a30308101018510f0c20404462843c20480113843c20480163843c204058e28408120044e5440812004c61440c20402cd24c0c204044a0c205220044e28c0812002cd2443c204038d24a3020401c61440c2040
|1=>0x1d1892840812004465440c204801018928f0812001852843c204040d2443c308101c18928308120019a10308120038625510204800624464308120044628c0c20480185861030812001c62440c204800b1893030812002cd2440c2048011103
|2=>0x812002d018910308120040624a0c204801018910f0c204801c1891030812004463040c20480111843c308120038d2443c204038d24a1020480141892830812005862840c20480163840c20480103493030810062440c205f2007862440c2048
|3=>0x2840c204800d18910308120058610308120034624a10308120038d2440c204801d1891030812003862443c204801418910308120040624c0c204801034910308120018510f0c20401852840c20480062440c206020038624a102048006255103
|4=>0x1891030812001851030812001893040c204800e189103081200189
|_=>0
def sO:Nat→Nat→Nat
|9,0=>0x121c4080e203080a2020806201080220008
|10,0=>0x4f213394aa521946611184224ff93da4ed93924dc834e4ca930a0b992c24a7927a495923248391ee07291a6460915e44f8
|11,0=>0x1e8877a9d597325c396ea5b196a25a0865e58e961657c95ca969957e95695365449
|12,0=>0x214882e60297e65f09
|13,0=>0x21c8
|_,_=>0
def wAt:=mkWire dB 33 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x204500d10648194034419246463210856111854921206440d10846110c84921203440d24649190c6432144849190c64321146460d103492118348291034919209540d21084191884811403441918c8811103491920443191034919403432120644191034319188442120b86291034921
|1=>0x2044919203491918843210c6462110343191034842106461510349210c6484524644212064419744cd0d188465530344211034d0d188482910349190c8440d106432110349210c848191065021103441925b500f106460d30344214834632108481110349195834615248482e4034419
|2=>0x92110843191034621185492110346210c6481934346210c843192108419184442120644190c849211034921303c4211034319303442140344191034419203441918c4421
|_=>0
def oO:Nat→Nat→Nat
|9,0=>0x2442041c41841441040c4084044004
|10,0=>0x7937637337036d36a36736436135e35b35835535234f34c34934634334033d33a33733433132e32b3283
|11,0=>0xa029e29c29a29829629429229028e28c28a28828628428228027e27c2
|12,0=>0xa61a51a41a31a21
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x781f7000580ff000127ff000122ff000121ff000120ff000106ff000104ff0000d0d70000a0ff000082ff000080ff000080df00003bff000032ff000029ff000021ff00001bff000012ff000010ff00000fff00000eff00000bff00000aff000009ff000008ff000004ff000003ff000002ff000001ff000000ff00000000
|1=>0x801029ff404026ff320380ff108000ff0f0180ff00c000ff008104ff0080b0ff00803aff008030ff00801eff00801cff008018ff008014ff008013ff008012ff008004ff004027ff00201bff002013ff001126ff00102bff001000ff000907ff0008a2ff0007a1f7000783f7000782ff
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>0x8a17573999122d3
|10,0=>0x4093607f09769a7463cf1e2a159de5a296392b471b
|11,0=>0x1e207ecf32ebd656b13ab6ccb0d5a
|12,0=>0x14ac20c6
|13,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 32 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_253 12 roots_253 ops++addP pm 2 dom_127 12 roots_127 ops++addP pm 3 dom_239 12 roots_239 ops++addP pm 4 dom_251 11 roots_251 ops++addP pm 5 dom_191 11 roots_191 ops++addP pm 6 dom_247 11 roots_247 ops++addP pm 7 dom_223 11 roots_223 ops++addP pm 8 dom_219 9 roots_219 ops++addP pm 9 dom_243 9 roots_243 ops++addP pm 10 dom_183 8 roots_183 ops++addP pm 11 dom_159 9 roots_159 ops++addP pm 12 dom_215 8 roots_215 ops++addP pm 13 dom_187 9 roots_187 ops++addP pm 14 dom_235 10 roots_235 ops++addP pm 15 dom_175 10 roots_175 ops++addP pm 16 dom_207 10 roots_207 ops++addP pm 17 dzo_235_16 7 roots_235 ops++addP pm 18 dom_143 7 roots_143 ops++addP pm 19 dom_231 10 roots_231 ops++addP pm 20 dzo_219_4 7 roots_219 ops++addP pm 21 dom_211 6 roots_211 ops++addP pm 22 dzo_187_4 7 roots_187 ops++addP pm 23 dom_151 7 roots_151 ops++addP pm 24 dom_203 8 roots_203 ops++addP pm 25 dzo_239_16 8 roots_239 ops++addP pm 26 dom_139 5 roots_139 ops++addP pm 27 dom_171 8 roots_171 ops++addP pm 28 dom_199 7 roots_199 ops++addP pm 29 dom_167 7 roots_167 ops++addP pm 30 dom_179 6 roots_179 ops++addP pm 31 dom_155 6 roots_155 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_235_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_219_4_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_187_4_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_239_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_155 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 10 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 28 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 28 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 19 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 19 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 5 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 5 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [7, 8] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.or, inputs := [2, 9] }, { op := GateOp.or, inputs := [4, 10] }, { op := GateOp.and, inputs := [11, 12] }, { op := GateOp.or, inputs := [9, 10] }, { op := GateOp.and, inputs := [3, 14] }, { op := GateOp.and, inputs := [7, 8] }, { op := GateOp.and, inputs := [6, 5] }, { op := GateOp.and, inputs := [2, 0] }, { op := GateOp.or, inputs := [13, 15] }, { op := GateOp.or, inputs := [19, 16] }, { op := GateOp.or, inputs := [20, 17] }, { op := GateOp.or, inputs := [21, 18] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_53090_aux

theorem PEqualNP.Outside.L_meta_53090 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_53090_aux.main
