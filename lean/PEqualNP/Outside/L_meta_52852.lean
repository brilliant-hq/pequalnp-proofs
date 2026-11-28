import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52852_aux
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

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xffffffffeeeeeeeeaaaaaaaa00000000ffffffffeeeeeeeeaaaaaaaa00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xffffffffaaaaaaaafafafafa00000000ffffffffaaaaaaaafafafafa00000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xffffffffccccccccf0f0f0f000000000ffffffffccccccccf0f0f0f000000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xffffffffeeeeeeeefafafafa00000000ffffffffeeeeeeeefafafafa00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffffaaffaaffaaffaaaa00aa00ffffffffffaaffaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffffeeffeeffaaffaaaa00aa00ffffffffffeeffeeffaaffaaaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xffffffffffaaffaafffafffaaa00aa00ffffffffffaaffaafffafffaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffffffffffaaaaaaaaaaaaaaaa0000ffffffffffffaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffffffcccccccc0000cccc0000ffffffffffffcccccccc0000cccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffffffeeeeeeeeaaaaeeee0000ffffffffffffeeeeeeeeaaaaeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xffffffffffff0000f0f0f0f000000000ffffffffffff0000f0f0f0f000000000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xffffffffffffaaaafafafafaaaaa0000ffffffffffffaaaafafafafaaaaa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xffffffffffffccccfcfcf0f0cccc0000ffffffffffffccccfcfcf0f0cccc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xffffffffffffeeeefefefafaeeee0000ffffffffffffeeeefefefafaeeee0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffffffffffff00ff00ff00ff000000ffffffffffffff00ff00ff00ff000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffffffaaffaaffaaffaaaa00ffffffffffffffaaffaaffaaffaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffffffccffccff00ffcc0000ffffffffffffffccffccff00ffcc0000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffffffeeffeeffaaffeeaa00ffffffffffffffeeffeeffaaffeeaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xffffffffffffff00fff0fff0ff000000ffffffffffffff00fff0fff0ff000000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xffffffffffffffaafffafffaffaaaa00ffffffffffffffaafffafffaffaaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xffffffffffffffeefffefffaffeeaa00ffffffffffffffeefffefffaffeeaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeaa00aa00aa00aa00aa00aa00aa00aa00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffefffefffefffefffefffefffefffeaa00aa00aa00aa00aa00aa00aa00aa00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_146 : Nat := 0x5000500000000000000000000000000050005
def goal_146 : Nat := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000eeee0000eeee0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfccccc0000cccc0000cccc0000cccc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefeeeee0000eeee0000eeee0000eeee0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffaaaa00ffaaaa00ffaaaa00ffaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffccffcc0000ffcc0000ffcc0000ffcc0000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffeeaa00ffeeaa00ffeeaa00ffeeaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfffffff0fffffff0fffffff0fffffff0ff000000ff000000ff000000ff000000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffaffaaaa00ffaaaa00ffaaaa00ffaaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffffcfffffffcfffffffcfffffffcffcc0000ffcc0000ffcc0000ffcc0000
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffefffffffefffffffefffffffeffeeaa00ffeeaa00ffeeaa00ffeeaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeaaaaaaaa00000000aaaaaaaa00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_164 : Nat := 0x110000001100000000000000000000001100000011
def goal_164 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_164 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcf0f0f0f000000000f0f0f0f000000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffefefefefffffffffefefefefafafafa00000000fafafafa00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffffccffccffffffffffccffccff00ff0000000000ff00ff0000000000
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffafffafffaaa00aa00fffafffaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfff0fff000000000fff0fff000000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffefffefffffffffffefffefffafffaaa00aa00fffafffaaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffffffccccffffffffffffcccccccc0000cccc0000cccc0000cccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffeeeeffffffffffffeeeeeeeeaaaaeeee0000eeeeaaaaeeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f0f0f000000000f0f0f0f000000000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffffffafafffffffffffffafafafafafaaaaa0000fafafafaaaaa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfcfcf0f0cccc0000fcfcf0f0cccc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffefefffffffffffffefefefefafaeeee0000fefefafaeeee0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffffccffffffffffffffccffccff00ffcc0000ffccff00ffcc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffeeffffffffffffffeeffeeffaaffeeaa00ffeeffaaffeeaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0fff0fff0ff000000fff0fff0ff000000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffffafffffffffffffffafffafffaffaaaa00fffafffaffaaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffffcfffffffffffffffcfffcfff0ffcc0000fffcfff0ffcc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffefffffffffffffffefffefffaffeeaa00fffefffaffeeaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_194 : Nat := 0x5000000000000000500000000000000050000000000000005
def goal_194 : Nat := 0xffffffffffffffffcccccccccccccccccccccccccccccccc0000000000000000
def roots_194 : List Nat := [xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfccccccccccccccccc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfffffffffffffffffefefefefefefefeeeeeeeeeeeeeeeee0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffffccffccffccffccffccffccffccffcc0000000000000000
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffffffccccffffccccffffccccffffcccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffffafafffffafaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffffffcfcfffffcfcffffccccffffcccccccc0000cccc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffefefffffefeffffeeeeffffeeeeeeee0000eeee0000
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

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffffafffffffaffffffaaffffffaaffaaaa00ffaaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffefffffffeffffffeeffffffeeffeeaa00ffeeaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffffffffffeeeeeeeeffffffffeeeeeeeeaaaaaaaa00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffffffffffff0f0f0f0ffffffff00000000f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffffffffffafafafaffffffffaaaaaaaafafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffffffffffcfcfcfcffffffffccccccccf0f0f0f000000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffffffffffefefefeffffffffeeeeeeeefafafafa00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffeeffeeffffffffffeeffeeffaaffaaaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffffffffffafffaffffffffffaaffaafffafffaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffefffeffffffffffeeffeefffafffaaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffffffffffaaaaffffffffffffaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffffffccccffffffffffffcccccccc0000cccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffffffeeeeffffffffffffeeeeeeeeaaaaeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffffffffffff0f0ffffffffffff0000f0f0f0f000000000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffffffafaffffffffffffaaaafafafafaaaaa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffffffcfcffffffffffffccccfcfcf0f0cccc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffffffefeffffffffffffeeeefefefafaeeee0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffffffaaffffffffffffffaaffaaffaaffaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffffeeffffffffffffffeeffeeffaaffeeaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffffffffffff0ffffffffffffff00fff0fff0ff000000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffffffaffffffffffffffaafffafffaffaaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffffffcffffffffffffffccfffcfff0ffcc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffffffeffffffffffffffeefffefffaffeeaa00
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
def isoMvS_164:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_164:Lower true dom_164 roots_164 goal_164 4:=lower_iso_b isoMvS_164 (by decide +kernel) lowS_25
def isoMvS_194:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_194:Lower true dom_194 roots_194 goal_194 4:=lower_iso_b isoMvS_194 (by decide +kernel) lowS_25
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
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_57
def isoMvS_99:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_27
def isoMvS_101:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 5:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_27
def isoMvS_102:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 4:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_51
def isoMvS_105:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 7:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_89
def isoMvS_113:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_57
def isoMvS_114:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_27
def isoMvS_116:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 4:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_51
def isoMvS_120:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 5:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_57
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_27
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_27
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_57
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_27
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 7:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_89
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_57
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_27
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_27
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_27
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_27
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_27
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_27
def isoMvS_195:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_57
def isoMvS_198:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_27
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
def isoMvS_228:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 5:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_57
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
theorem lowS_91:Lower true dom_91 roots_91 goal_91 8:=lower_slice_b [(0xc0c0c0c000000000c0c0c0c,16,18)] (by decide +kernel) lowS_89
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_slice_b [(0xcc000000cc000000cc000000cc,64,66)] (by decide +kernel) lowS_101
theorem lowS_107:Lower true dom_107 roots_107 goal_107 8:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c,64,66)] (by decide +kernel) lowS_105
namespace S_115
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(2,18),(2,66),(3,19),(3,35),(3,67),(16,17),(16,18),(16,80),(32,33),(32,96),(34,35),(34,50),(34,98),(48,49),(48,50),(48,112),(64,65),(64,66),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_115.map (·&&&dom_115)
def gM:=goal_115&&&dom_115
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x88c8c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f00000000000f000f00000000f0000000f0000000f0000000f0000c000c000c000c000c000c000c000ca000a000a000a000a000a000a000af000f000f000f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 116 0xfffffffffffffffffffffffffffff
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
addP pm 0 dom_114 5 roots_114 ops++addP pm 1 dom_113 5 roots_113 ops++addP pm 2 dom_99 5 roots_99 ops++addP pm 3 dom_83 5 roots_83 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_115 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_83 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_114 5 s (0,roots_114.map (·&&&dom_114)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_115 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_114 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_115==dom_115)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_115 gM v ys):RunD true dom_115 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_115 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_115 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_114_4:=0x500050005000500050005000500050
def gzo_114_4:=0x500050005000400050005000400000
def gsh_114_4:=0x50005000500040005000500040000
theorem lowS_zo_114_4_82:Lower true dzo_114_4 roots_114 gzo_114_4 5:=lower_iso_b (d1:=dom_114) (r1:=roots_114) (T1:=gsh_114_4) [(dom_114,4)] (by decide +kernel) (lower_slice_b (T:=gsh_114_4) [(0x50005000000000005000500000000,0,32)] (by decide +kernel) lowS_82)
namespace S_118
def pG:List (Nat×Nat):=[(2,18),(2,66),(4,36),(6,22),(6,38),(6,70),(16,18),(16,80),(20,22),(20,52),(20,84),(32,36),(32,96),(34,38),(34,50),(34,98),(48,50),(48,52),(48,112),(64,66),(64,80),(64,96),(68,70),(68,84),(68,100)]
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
|0=>0xf9c80
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x16
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_114 5 roots_114 ops++addP pm 1 dzo_114_4 5 roots_114 ops++addP pm 2 dom_116 4 roots_116 ops++addP pm 3 dom_102 4 roots_102 ops++addP pm 4 dom_82 4 roots_82 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_118 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_114_4_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_82 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_114 5 s (0,roots_114.map (·&&&dom_114)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_118 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_114 h
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
theorem lowS_121:Lower true dom_121 roots_121 goal_121 8:=lower_slice_b [(0x3030000030300000303000003030000,1,17)] (by decide +kernel) lowS_105
theorem lowS_143:Lower true dom_143 roots_143 goal_143 6:=lower_slice_b [(0xcccc0000000000000000000000000000cccc,128,130)] (by decide +kernel) lowS_141
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_slice_b [(0xaa00aa00000000000000000000000000aa00aa,16,17)] (by decide +kernel) lowS_150
namespace S_182
def pG:List (Nat×Nat):=[(2,18),(2,130),(4,36),(4,132),(6,22),(6,38),(6,134),(16,18),(16,144),(20,22),(20,52),(20,148),(32,36),(32,160),(34,38),(34,50),(34,162),(48,50),(48,52),(48,176),(128,130),(128,132),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_182.map (·&&&dom_182)
def gM:=goal_182&&&dom_182
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x4eb1b
|4,0=>0x6c6031d05e04aed00ea0
|5,0=>0xac2248edac589a056c942e77127be82786c0cbb607bf705c44
|6,0=>0xd5c3922bde0f59e02507
|7,0=>0xd5c39
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa000a000a000a0000000000000000000a000a000000015401540154000000000000000000000154015401540002a802a802a802a8000000000000000002a8000002a8000000005000000050000000000000000000000000000000000000000000000000000000000000000aa00a000aa00a00000000140015400000000000000000000000001400142a802a800000000000000000000000002a802a800000005500550055005500000000000000000050005000500050aa00a000aa00a000000000000000000000000000000001400140014001400000000000000000014001400140014000000002a802a800000000000000000000000002a80285500550055005500000000000000000000000000000000aa00aa00aa00aa000000000000000000aa00aa000000015400000154000000000000000000000154000001540002a802a802a8028000000000000000000280028002800284400440044004400000000000000000044004400440044
|0,1=>0x500050005000500000000000000000000000000000000aa00a000aa00a0000000000000000000aa00a000aa00a1540154015401540000000000000000011001100110011088008800880088000000000000000000000000000000055005500550000000000000000000000000000000000000a000a000a000a0000000000000000000a0000000a00000000000154015400000000000000000000000001400142a8000002a802a8000000000000000002a8000002a80005500550055005500000000000000000055005500550000
|_,_=>0
def sP:Nat→Nat
|0=>0x2446011223008911804c26e230089688c022446b12a911804a244604c82302444c44601209118041a440791c969804488c02312b118041180a2244101122400e2300a418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682cf15b330654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 25 183 0x7fffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x31230911171049271119b491111
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x510000413112010000
|6,0=>0x817161
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0x3ff7be6e60a183080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x2600135400
|6,0=>0x79a8
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_180 5 roots_180 ops++addP pm 1 dom_164 4 roots_164 ops++addP pm 2 dom_146 4 roots_146 ops++addP pm 3 dom_150 5 roots_150 ops++addP pm 4 dom_178 5 roots_178 ops++addP pm 5 dom_166 5 roots_166 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_182 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_166 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_180 5 s (0,roots_180.map (·&&&dom_180)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_182 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_180 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_182==dom_182)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_182 gM v ys):RunD true dom_182 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_182 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_182 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_182 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_182 roots_182 goal_182 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_182
theorem lowS_182:Lower true dom_182 roots_182 goal_182 8:=S_182.noCircuit
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
def isoMvS_109:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 8:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_107
def isoMvS_117:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 7:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_59
def isoMvS_122:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_115
def isoMvS_124:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 7:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_59
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 8:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_91
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 8:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_107
def isoMvS_158:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 6:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_151
def isoMvS_167:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_151
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_107
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_91
def isoMvS_174:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_151
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_115
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 7:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_115
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_115
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 7:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_115
def isoMvS_199:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 6:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_151
def isoMvS_203:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_91
def isoMvS_211:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 8:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_121
def isoMvS_213:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_107
def isoMvS_214:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 8:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_107
def isoMvS_218:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 8:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_121
def isoMvS_227:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 8:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_91
def isoMvS_229:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 8:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_91
def isoMvS_230:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 7:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_115
def isoMvS_233:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 9:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_217
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 8:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_121
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 8:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_91
def isoMvS_244:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 7:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_115
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xcccccccccccccccc,16,18)] (by decide +kernel) lowS_61
def dzo_83_4:=0xf000f00000000000f000f0
def gzo_83_4:=0xf000e00000000000e00000
def gsh_83_4:=0xf000e00000000000e0000
theorem lowS_zo_83_4_83:Lower true dzo_83_4 roots_83 gzo_83_4 5:=lower_iso_b (d1:=dom_83) (r1:=roots_83) (T1:=gsh_83_4) [(dom_83,4)] (by decide +kernel) (lower_slice_b (T:=gsh_83_4) [] (by decide +kernel) lowS_83)
def dzo_115_4:=0xf000f000f000f000f000f000f000f0
def gzo_115_4:=0xf000f000f000e000f000f000e00000
def gsh_115_4:=0xf000f000f000e000f000f000e0000
theorem lowS_zo_115_4_83:Lower true dzo_115_4 roots_115 gzo_115_4 6:=lower_iso_b (d1:=dom_115) (r1:=roots_115) (T1:=gsh_115_4) [(dom_115,4)] (by decide +kernel) (lower_slice_b (T:=gsh_115_4) [(0xf000f00000000000f000f00000000,0,32)] (by decide +kernel) lowS_83)
namespace S_119
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(2,18),(2,66),(3,19),(3,35),(3,67),(4,36),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,23),(7,39),(7,71),(16,17),(16,18),(16,80),(20,21),(20,22),(20,52),(20,84),(32,33),(32,36),(32,96),(34,35),(34,38),(34,50),(34,98),(48,49),(48,50),(48,52),(48,112),(64,65),(64,66),(64,80),(64,96),(68,69),(68,70),(68,84),(68,100)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_119.map (·&&&dom_119)
def gM:=goal_119&&&dom_119
def NN:Nat→Nat
|4=>3
|5=>10
|6=>17
|7=>7
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xc2d9e2ef8d2d72f
|5,0=>0xe0385de436a5dbe9f2cb8dd538152777a2d4a62516b9600b45
|6,0=>0xff912de44bd8383cec84b1c91a0b888f24b873f780f09764ec73efd4872e3875a361f73222e11bd10b8f3
|7,0=>0xf1577e8d9fd6a4184cb0721ca5d38a4c2fe
|8,0=>0xdaa04
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3300000033003300330000003300003300330033003300330033003300000f00ff000000ff000f000f00000000ff00ff00ff00000000000000000000ff00ff00ff00ff00f000f000f000f0330033003300330033000000330000ff00ff00ff00ff0000000000000000ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff000000ff0000ff00ff00ff00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff00ff00ff00000000ff000000ff000000ff000000ff0000f000f000f000f000f000f000f000f0cc00cc00cc00cc00cc00cc00cc00ccff00ff00ff00aa00aa00aa00aa00aa
|0,1=>0xff000000ff000000ff0000000000000000ff00ff0000000000ff000000000000ff00ff0000000000000000ff000000ff00ff00ff000000ff00000000000000000000ff00ff00ff0000f000ff00f000ff00f000f000f000f0ff00ff00ff00ff000f000f00000000ff00ff00ff00ff00ff00ff00ff00000000ff000000ff0000000000000000ff00ff000000ff00ff00ff00000000ff00ff00ff000000ff00ff00ff0000000000000000ff00000000000000005500550055005500550055005500000f000f00000000000f000f00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x96e941c612c13640c412a688188254cd07104a940c412a58838c4552503104a9920620c528188204a06554128188af4a0622b92418825620612b528188c54a0e2095881acaa4a0e208107118a418820
|1=>0x40c412a5030960940c412a6a8188254ec88188254cd03104a941c62095281ac254a0612c13540c412f52818825e25071ac254a343104a99906209528188aa4e503104a940f012a503
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa5055005
|5,0=>0x4563f63963362d62762161b61560f6
|6,0=>0xb87b17aa7a379c79578f68878267c67576e76776075975274b7
|7,0=>0xe86e17da7d37cc7c57bf6
|8,0=>0xee6
|_,_=>0
def wAt:=mkWire dB 30 120 0xffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x40b1a642642540d1a51251a640b41e1a51a51251ed42640d4253871a59a740d1551a682540b1a540b20d4254551a640d1a59a440d3871a59a640d
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1e2001c2689825894248902388c2288821884208802
|7,0=>0x261946418c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xffbfb77771443f37321c1b1811060200
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0xa0421634bb2547924
|7,0=>0xcdee9df
|8,0=>8
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_118 7 roots_118 ops++addP pm 1 dom_117 7 roots_117 ops++addP pm 2 dom_103 6 roots_103 ops++addP pm 3 dzo_83_4 5 roots_83 ops++addP pm 4 dom_115 7 roots_115 ops++addP pm 5 dom_83 5 roots_83 ops++addP pm 6 dzo_115_4 6 roots_115 ops++addP pm 7 dom_55 5 roots_55 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_119 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_83_4_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_115_4_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_55 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_118 7 s (0,roots_118.map (·&&&dom_118)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_119 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_118 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_119 gM v ys):RunD true dom_119 gM v (ori ys):=h
def Z (s:Nat):=barP dom_119 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
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
def dzo_121_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_121_2:=0xc0c0c0c0c0c0c0c0c0c0c080c0c0800
def gsh_121_2:=0x3030303030303030303030203030200
theorem lowS_zo_121_2_41:Lower true dzo_121_2 roots_121 gzo_121_2 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_2) [(dom_121,2)] (by decide +kernel) (lower_slice_b (T:=gsh_121_2) [(0x3030000030300000303000003030000,0,16),(0x3030303030303030000000000000000,0,64)] (by decide +kernel) lowS_41)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,18),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,24),(8,40),(8,72),(10,11),(10,26),(10,42),(10,74),(16,17),(16,18),(16,24),(16,80),(32,33),(32,40),(32,96),(34,35),(34,42),(34,50),(34,98),(48,49),(48,50),(48,56),(48,112),(64,65),(64,66),(64,72),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|5=>2
|6=>8
|7=>9
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x4a89a318ee
|6,0=>0xa770d84f486a0554ac724559144d5343d5318c74
|7,0=>0xba0efb0e7685320789af6a42d2c9172b0d9284ad1489e
|8,0=>0xcdd9247c680e7a1
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x5050505050505050500050005000500f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a00e000e000e000e000e000e000e000ee0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ef0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c00000000f0f0f0f000000000f0a0f0af0a0f0a0f0a0f0a0f0a0f0a0f0a0f0ac0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf000f000f000f000f000f000f000f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f0000f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0ef0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a
|_,_=>0
def sP:Nat→Nat
|0=>0x37c65432765431780643e78654376d543e7806543918654317c6543b16543786f53e786a53786a537806a543be1654391804370d54317c04321653b16a543210
|1=>0x437865439786543780654
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x56005
|6,0=>0x3773162a72371d61761160b6
|7,0=>0x7566e76776165985274b74563e7
|8,0=>0x8878177b6
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 16 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1d9656197c61975595955d97ca19705957559d756197561d619d5955d94ea557653a704597561d765d56571f6561975595866617559d985d975595
|_=>0
def oO:Nat→Nat→Nat
|5,0=>4
|6,0=>0x609534c90334ca31cc43
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 10
def pmP:Nat→Nat
|0=>0x1dcf9f5cf827971eb8e5bf69bb6dcb4eda768bbc3cb0f5872c2920e0040010003c000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>1
|6,0=>0x194443a9c9
|7,0=>0xc8cd728368f
|8,0=>0x1d0b
|9,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 8 roots_121 ops++addP pm 1 dom_59 7 roots_59 ops++addP pm 2 dom_113 5 roots_113 ops++addP pm 3 dom_107 8 roots_107 ops++addP pm 4 dom_120 5 roots_120 ops++addP pm 5 dom_114 5 roots_114 ops++addP pm 6 dom_122 7 roots_122 ops++addP pm 7 dom_91 8 roots_91 ops++addP pm 8 dom_115 7 roots_115 ops++addP pm 9 dom_58 4 roots_58 ops++addP pm 10 dzo_57_2 5 roots_57 ops++addP pm 11 dzo_121_2 6 roots_121 ops++addP pm 12 dom_51 4 roots_51 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_57_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_121_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_51 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 8 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_123 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_121_4:=0x30303030303030303030303030303030
def gzo_121_4:=0x30303030303030203030303030202000
def gsh_121_4:=0x3030303030303020303030303020200
theorem lowS_zo_121_4_89:Lower true dzo_121_4 roots_121 gzo_121_4 8:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_4) [(dom_121,4)] (by decide +kernel) (lower_slice_b (T:=gsh_121_4) [(0x3030303000000000303030300000000,0,32)] (by decide +kernel) lowS_89)
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(4,36),(5,13),(5,21),(5,37),(5,69),(8,9),(8,24),(8,40),(8,72),(12,13),(12,28),(12,44),(12,76),(16,17),(16,24),(16,80),(20,21),(20,28),(20,52),(20,84),(32,33),(32,36),(32,40),(32,96),(48,49),(48,52),(48,56),(48,112),(64,65),(64,72),(64,80),(64,96),(68,69),(68,76),(68,84),(68,100)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|6=>4
|7=>4
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xfc5bb79e4471ff261eff
|7,0=>0x4169b1099d0bf9801a5b
|8,0=>0x77492
|9,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc88cc88cc88cc8b33333333333333333223322332233220000cccc0000cccc0000cc880000cc8b3333333333333330000000000000000cc00cc00cc00cc00cc00cc00cc00cc022222222222222222222222222222222cccccccc00000000cccccccc000000033330000333300003333000033330000cc88cc88cc88cc88cc88cc88cc88cc8b3333333333333333300330033003300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c33333333333333332222222222222222
|_,_=>0
def sP:Nat→Nat
|0=>0x547168543716854b716854a71068543216854a71685a716985716985371698543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0x26e35833806
|7,0=>0x60ea210b9a7
|8,0=>0x377
|9,0=>0x3e6
|_,_=>0
def wAt:=mkWire dB 12 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x19d38d9d075a1785d93859d4a8e16752a3859d4a8e1675a1785d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x4998c6603
|7,0=>0x91409c4c2
|8,0=>0x141
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 9
def pmP:Nat→Nat
|0=>0x3ffe7dff3fc7f1140d01c00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x1324
|7,0=>0x5768
|8,0=>5
|9,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 8 roots_121 ops++addP pm 1 dom_109 8 roots_109 ops++addP pm 2 dzo_121_4 8 roots_121 ops++addP pm 3 dom_124 7 roots_124 ops++addP pm 4 dom_117 7 roots_117 ops++addP pm 5 dom_61 7 roots_61 ops++addP pm 6 dom_89 7 roots_89 ops++addP pm 7 dom_116 4 roots_116 ops++addP pm 8 dom_53 4 roots_53 ops++addP pm 9 dom_60 4 roots_60 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_121_4_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_60 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 8 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_125==dom_125)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_125 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_slice_b [(0xcccccccc000000000000000000000000cccccccc,16,18)] (by decide +kernel) lowS_157
theorem lowS_183:Lower true dom_183 roots_183 goal_183 9:=lower_slice_b [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_182
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_slice_b [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,16,17)] (by decide +kernel) lowS_214
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
|0,0=>0xf0f0f0f000000000f000f00000000000f0f0000000000000f000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000f0f0f0f000000000f000f00000000000f0f0f0f000000000f000f00f0f0f0f0000000000000000000000000f0f0f0f0000000000000000f0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f00f0f0f0f000000000f0a0f0a000000000f0f0a0a000000000f0a0a0ac0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0cf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000000000000000000000000000000000000000000f0f0f0f000000000f0f0a0af0f0000000000000f0f0000000000000f0f0000000000000f0f00000000000000000000f0f0f0f0000000000000000000000000f0f0a0af000f00000000000f000f00000000000f000f00000000000f000f00e0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0e0000f0f0000000000000f0f0000000000000f0f0000000000000a0af0f0f0f000000000f0f0f0f00000000000000000000000000000000
|0,1=>0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0a0af0f0f00000000000f0f0f00000000000f0f0f000000000000000000f0f0f0a000000000f0f0f0a000000000f0f0f0a000000000a0a0a0af0f0f0f000000000f0f0a0a000000000f0f0f0f000000000f0f0a0af0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f0000f0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0a1010101000000000101010100000000010101010000000001010000f0f0f0f000000000f0f0f0f000000000f000f00000000000f000f00f0c0f0c000000000f0c0f0c000000000f0c0f0c000000000f0c0f0cf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f000f000000f0f0000000000000f0f0000000000000f0f0000000000000f0050505050000000005050505000000000505050500000000050505001010101000000000101010100000000010101010000000001010100f0f0a0a000000000f0f0a0a000000000f0f0a0a0000000000000000f0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0af0f0e0e000000000f0f0e0e000000000f0f0e0e000000000c0c0c0c
|0,2=>0xf0f0f0f000000000f0f0f0f000000000f0f0f00000000000f0f0f0000000000000000000000000000000000f0f0f0f000000000f0f0f00f0f0f0f000000000a0a0a0a000000000f0f0000000000000a0a0000f0f0f0f000000000e0e0e0e000000000f0f0c0c000000000e0e0c0c50105010000000005010501000000000501050100000000050105000000000000000000f0f0f0f0000000000000000000000000f0f0f00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0a00f000f00000000000f000f00000000000f000f00000000000f000af030f03000000000f030f03000000000f030f03000000000f030f000030003000000000003000300000000000300030000000000030000f0f0f0f000000000f0f0000000000000f000f00000000000f000000f0f0f0f000000000f0f0f0f000000000f0f0a0a000000000f0f0a0af0f0f0f0000000000000f0f000000000f0f0f0f0000000000000a0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0000f0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0a3030303000000000303030300000000030303030000000003030000
|0,3=>0xf0f0000000000000f0f0000000000000f0f00000000000000000000000000000000f0f0a0a0000000000000000000000000f0f0a0af0f0f0f000000000f0f0f0f0000000000000000000000000f0f0a0a000000f000000000000000f000000000000000f0000000000000000f0f0f0f000000000f0a0f0a000000000f0f0f00000000000f0a0f0030303030000000003030303000000000303030300000000030303005050505000000000505050500000000050505050000000005050000f0f0f0f000000000f0f0f00000000000f0f0f0f000000000f0f0f0000f000f00000000000f000f00000000000f000f00000000000f0000000000000000000000f000f000000000000000000000000000f0000f0f0f0f00000000000f000f000000000f0f0f0f00000000000f000000b000b00000000000b000b00000000000b000b00000000000b000af0f0000000000000f0f0000000000000f0f0f0f000000000f0f0f000000000000000000505050500000000000000000000000005050000f0f0f0f0000000005050505000000000f0f0f0f0000000005050000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f00
|0,4=>0xa0a0a0a000000000a0a0a0a000000000f0f0f0f000000000f0f0a0a00f000f00000000000f000f00000000000f000f00000000000000000000f0f0000000000000f0f0000000000000f000000000000000f0000000000000000000000000000000000f0f0f0f000000000f000f0000000000000000000000f0f00000000000000000000000000000f00b0b0b0b000000000b0b0b0b000000000b0b0b0b000000000b0b0a0a00000000000000000000000000000000f0f0f0f000000000a0a0a0a000000000000000000000000000000000000000000000000f0f0f00f0f0f0f000000000f0f0f0f0000000000000000000000000f0f0f0000f000f00000000000f000f00000000000f000000000000000f0000f000f0f000000000f000f0f000000000f000f0f000000000f000f003030303000000000303030300000000030303030000000003030202f0f0f0f000000000f0f0f0f0000000005050505000000000505000050505050000000005050000000000000505050500000000050500003030303000000000303030300000000010101010000000001010000f0f0f0f000000000f0f0000000000000a0a0a0a000000000a0a0000
|0,5=>0xf000f00000000000f000000000000000000000000000000000000f0f0f00000000000f0f0f00a0a0f0f000000000a0a0f0f000000000a0a0f0f000000000a0a0a0af000f00000000000f000f00000000000f0f0f0f000000000f0f0f000000000000000000f0f0f0f0000000000000000000000000f000f000000000000000000f0f0f0f0000000000000000000000000a0a0a0a00f000f00000000000f000000000000000f000f00000000000f0000f0f0f0f000000000f0f0f0f00000000000f000f00000000000f000000000000000000000000000000000000f0f0f0f000000000f0f00000000f0f0000000000000a0a0000000000000f0f0000000000000a0af0f0f0f000000000f0f0f0f0000000000000f0f0000000000000a0a00005050000000000000505000000000000050500000000000000000000000000000000f0f0f0f0000000000000000000000000f0f000000000000000000000000f0f00000000000000000000000000000a0a000000000000000000000000000000000000000000000000f0f0a0a0000000000000000000000000000000050505050000000005050000
|_,_=>0
def sP:Nat→Nat
|0=>0xe2c02a0a5c7070014129502c0054e3930b006c6972c3838d189440e3890283041cd8506091800a0cd21401c88506645803e18283042cd8310740063634182166c182022c0050668c8b0018205062070d2e607151634b961c54585065098b00341901c2c509101c3040a0c1040608080
|1=>0x6645805e5c71516002881ca058036241880014734160028234a05800a607260e2c28e40d05806634b8e1600509102c00a4a207070a0c11a620110304045800c14182422ce1b1a0c10760b82971c2c31b0a0c1075e6cb981c1d7052e6070b226c19916017052e5870b360d60e00141ab
|2=>0x66458036341825288283562c01176205800a0c73a16017852e505803814199160179b2e38385065100b000c439022c0381a5cb0e169021b0608011440d0a0161910506085ae0a2073716a81881c5401b1a0c129346cc081c782971839a8044141a1322ce040a0c1005ea8d971c008a2
|3=>0x6c2831c98580700c40e2a2c00d0a0c129422c283106a00060bc2971c2c01c48141821601c1b0a5c707002910d2e385800a0c41a42fde850608580441418e742c01c3634188422c2831085c87166c6031038a800a9c1ab16018052e385803e14128160028328e85800a9c7371600f85
|4=>0x2c601881c14b961c545805e8828c103800506214b9160111b0a30c081c342831d1058008141881c1c00a1a58c081c2c288343940b006c2831c645805e6c68310383ae1a141881c2cd850620a0b00702831d105807028298103838a443040e00282831ce85800a0c74116002831068731
|5=>0x6207071688d85060908b5414618103803054141881c002971839f800c6c283042c00d0a5cb0e164511b0608580360c40e8c1c2a706385803e141820e2c0381434b8e16002831c81b8b00bcd9730385805414b0310380052e6071516002a7063900b0014bc51c2c00d0a0c421722cd8d
|6=>0x1c545803634188526872f146c6081c00d852e3a58b00442050620d003e1418e882c01f1a1418216012050620d07226c18e402c005189440e004511b0620d003e70283042c00507287071600522366040e1670d8506210875c6c683103859c3634182160089b062248048141820e2e385
|7=>0x1a0c40e9ce11052e385805e1440e6e2c0300a0c40e1600d85060a4800a6018e401c5850620e8b0014b8e9a1c5850620d3916002980639d0b006c297983800436341881c01204360c40e008828310505806014b8c1c2c02a0a5c70b00882831c985800c88283103859b1a5cc0e16c0188
|8=>0xbcd8c30207001414b8e16f004f0a0c421160121b060908b00e170d062070b220c40e022c0040a0c10b00bcd9606207001a0d2881c2c283583858044141a11c8059b062072d001418e87045800a2072816008a2063900b006c297303838a365840e00e02831050580486c188523801b
|9=>0x42ea00234c188422ce05063900b00bd5052e38580226c188421c8a20621c8b0028d96103838036346181039c052e5870b006c683043839b1a581881cc0283105058036341885239105302073716c11052e38580145840e2a2c0052c0c41416002830548580486c18834840510a0c10b
|10=>0x841c02f0a5cc0e160111b0a0c10e16008a2060838b00c02971c2c011440c10b007c28310e45800a0c73a0e2c005063930b001418e40985805c14c0310385a408141883400f85063900b00882839438580363418852383850639d0b001418e6e985805e1418e402c0220a5cc0e1644283
|11=>0x5c1460310385801414b1810385801a14b981c2d2050620d0b0120283103838b0070d85062108b0088685300c40e16906850608580146c1881c1c00aae0c40e160111b0a0c41a1c00d83103a30b0014b981c1c59b0a0c4491c00283103aa8b00e02831038380386c28310383800a0c40e
|12=>0x6c28310a4d0e00bc685062070716282db10385803e6c28310385802214188b42c00506207581600298062070b7e141881c2de000a0c129342c01f0a0c4211c2c02e36141881c2c005062074b16011052e0c707160121b062108e1600205062070b003428c06207073614b180620700
|13=>0xa5c70b0014b831c2df800a0c40eac1c02f44141881c2c0223614c0310385910a0c40e175005c0a0c40e160088d062108b3634188423858a440c40e16002831c805801a14b18062070b3888283103858060141881c2c01b0a0c40e722c0220a301881c00d852e6070b0088d85063900b
|14=>0xe2c00a0a5840e1600d85062148e001418e401c58060141881c1c58038141885238580226c188422c005060948b00141881cdc58044141881ce45800834283103858036341821c2c0385e141881c2c02408141881c2c05e0a5c70b00141a510385803e8828310385800a0c45d1c2c02f
|15=>0x14146081c2c005062070b9c01105062070b0014182422c01b1a0c40e0e882831c8058044141821c2c0300a301881c2c00a0a5840e0e2c00506207370e2c03e0a0c10b007c28310a470b006c283048458060bc283103858036146181038005300c40ebe2c0110a0c429342c00a440c40e
|16=>0x1c2c0052e3070b00141881d345800a0c40e16fc0050620756160028310a47071601f05062070b00bc505062070b00141821c1c58014141881c1c58044141881c1c5800a0c4291c2c005062108e0e2dc05062070b0070d85062070b003428c062070b006c28c062070048141884238580
|17=>0x5062070b00141881c1c5800a601881c2c005060870b002828310385803634188
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
|0=>0x16010a2d0601061516c934360a0136391039002d00153803301506210a2d06015a213434161500151c2d1c9e068144230a1d44230a1d16010621061d160100151615062d306c0015161506011039222d00451c1544230e1516011c013c39141c0a2d002d061538030a5a104900150e44002d1c15160106151e391a300a01062d
|1=>0xe2b002d06153e0f44390a1d1601103910e6443b44390a1d16011c1d103916010015161506b51a680a011c151c2d16151401062116010615062118011815062d482f44230a1d16011039001500691c2d141c16010a2d0601061516d91a330015006d161516be0a1d16011c3d0a2d1a300a01062d06151e391a300a01062d3660
|2=>0x60235e2d1401110e01091c6e161516c9343616390a01445f006d1615100d0a5a18010a31062d0a01422d1c011039368416151c2d1c0106215e2d140106151039220116451c15002d066d0a2d100d06210615163500151c2d1c010a1e16017c011039222f1c15440d0a1d1601363916151c01443b0e1516010a5a1801062d14f1
|3=>0x44230a1d160106fd0a1e1601100d443b16350a01302d161506010a5a061d1601100d062d1a2d06350015443b0e151c1d160136010a2d06013e231a691c2d3e2f0e4516011c150a0d0015302d06013e0f1a690a011c824423006d161506350a01002d0a2d60031a310a01062d603b366106011629002d0615062d0a0d0a1d002d
|4=>0xa011601103990010e2a160106151c2136010a2d1c0116be301506015e2f5e2d14010615062d0a1e002d100d38031c6d0a2d1039180106210a01062d1c15006d0a2d103906360a01002d0a2d44230a1d160144390a1d1601103900150621142d0615440f0a1d16010a2d0621301506015e2f302d0a6106012c170621302d0601
|5=>0x61d1601001500691c2d14010a2d062d0615366206210601169200451c153e233801222d1c151a691c210a011c2d220116011c151c2d4423360116151c15160d3660161506010a391c2d006d0a2d00711c6d161510391c8144230a1d36010a2d060136390a2d1c017003066d0a2d0a011c6d0a2d10390a3934030a2d1c2d1a39
|6=>0x63516350a0114f1141e0a0d160116151039006a1c2d442306010a1d16013c390e28002d0615100d1601301706013e3b1a690a011c2d602336610a2d1615100d1803062d482f1c350a0116921c350015603b440d0a1d160170011815062d100d5e2f14010615445f0a1d1601380336011c6d16150a010621161506010a5a0a59
|7=>0x42151c01103970031815062d3e170e45002d1c1516921c350a0110391615302d30150601306c0015161506015a211a680a011c2d442336010a2d0a2d1a680a011c2d01091c6e16153e0f3801222d1c1544230a1d16011601000d1615100d061d0a2d002d06150a2d422d0a851c01061e160100151615100d3601066d1615440f
|8=>0x1401061516010a2d1c011c15443b0a1d1601061d0a0d002d060116150015062d180106211815062d1039160100151615180116150015062d603b7001142d06151c1d160100151615440f006d1615440d0a1d16010a5a1801062d36861c210a2d1c01421516151c010e460a39160110390a2d0a6106011d41426e003916151615
|9=>0x6d161510391c210a390a1d1601440d0a1d1601100d0a390a1d16011039443b44390a1d16016023440d0a1d445f0a1d1601100d44230a1d160160032c15302d0601482f22011c1544230a1d16011c8144230a1d16011c1d16010015161560237001142d0615440f0a1d16010621000d006d16151c011a2f00151c15100d5e2f
|10=>0x22011c150a01062d002d0a2d302d060170031815062d302d060106150a010601100d22011c2d1c150e2a061536390a2d1c01060116350a011c350a0110390a2d002d061536031615061536010a2d1c2d16150636001506011601100d34030a2d1c2dac0134171c2d1601142d061516011c6d1615363b0a2d002d062130150601
|11=>0x15302d060136011c6d16157001142d0615443b006d16151a2d0a01062d06210a2d06014423006d161534010a2d1c2d1a0d0a011601302f0615060136850a2d1c01422f1c011c150165066e161506010a1e16010e2b1601061534011c2d103936850a2d1c017003066d161536620a2d060106210a1d16010a2d0a851c01482f
|12=>0x16011039440f0a1d1601443b0a1d160116921c350a01001516151039142d14010615482f22011c15100d1403061536600a2d060144390a1d16011cfd0a1e16010621140106150a1e1601100d002d34171c2d063516350a0136010a2d0601221e1601075d006e16150a011c011c151c01001516150a0d0a1d160144230a1d1601
|13=>0xa1d16011c01103916010015161544230a1d16010a1d160110392c151801062d061d0a0d1601440f0a1d1601103916461c150aa51c1d16010039161510395e2d140106151615062d060136630a2d1c1500691c2d0a0d0a1d16011801062d06150a2d1c1d002d44230a1d1601440d0a1d160134010a691c2d0a2d1c011c151c1d
|14=>0x1601060110390615001516150621062d301706010a1e16010a6a1c2d1c1d1601222f1c1514010615160110390a0d16010a1d16011c1d16011c011601142d06151c6d16150a01062d0a2d062d0a851c01062d0615061e1601
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
|0=>0x40b00405004040040100400003900021500210002000018500180001080010500101001000008000040000350003000028000200001b000180001500011000100000d0000500004000030000100000
|1=>0x80000471c0451c0419c04004040000315c03110031000253d0215c021300203402030020100200001538014380115c011000102800d1900c09005400052500511005100050000445004400041800410
|2=>0x141841021010105100100c71d0c71c0c51d0a57d0a55d0a51d0955d0953d0871d0859d0857d0853d0851d0851c083880815c0811d0811c081140811008109081080810008014080100800c0800508001
|3=>0x4039d402103831d3811d2953d2951d2879d2851d283882829d2819d280052351d2153d2151d211282053d205382050520415202982020820088200281c59d1c51d1c51c1831d18310181901459d1431c
|4=>0x8031d801808017c801007811d6c51d6c01c6851d680006411064008630056051d6051160400600505c71d5871d5831d58310503154a55d4a53d4951d4819d4800042538425304215c4151d4150d40405
|5=>0xe0109c8109c4108c151dc0554c0400b0205a053da04009859d9851d9819d981909818898185901988c51d8a55d8855d8853d8851d880008351d8351083505831188310d8215c82100811008053d8043d
|6=>0xec51dec108e851de8519e8109e8001e0550e051de0511e0510e0508e040d
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x20000
|5,0=>0x41c0000045f000a00000033000014173f00000015270f3a000b3a00001f00000000000a6c3a00001a0010310000004206000003386d0900430000291700000000300044
|6,0=>0x7f0034b997a2941459a740b1ba233700655e5a3200405e68403d25934a3f7501403fa4a50048a02801043c202a35401b2d187e01044c220183019e85115c04168b4371c7050691690c6b766007bd0d019d4d3995811d192e0132012c1d4faaa3372501b71107a83f45841211002bc01b494024016275080970909f3e016a869c
|6,1=>0x964b9904064e1b1c5e3b40b31e0100bb00
|7,0=>0xc9c8cb80a8925b136608731bb0c2a9b4c80e467d614fc6639a218c517841ab58ad8726c13f788e9bc44fa8474fbec457bfb284365d6478a1ab67742f56c58c4fbca86ea68a8d0677c38fb86fc782ae755272777c58ca
|8,0=>0x985556ab52b65389afacc8b6b57b79887a8e54abc966
|9,0=>0xab565950
|10,0=>0x4f
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 20 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_217 9 roots_217 ops++addP pm 1 dom_146 4 roots_146 ops++addP pm 2 dom_210 7 roots_210 ops++addP pm 3 dom_91 8 roots_91 ops++addP pm 4 dom_155 8 roots_155 ops++addP pm 5 dom_195 5 roots_195 ops++addP pm 6 dom_209 7 roots_209 ops++addP pm 7 dom_154 5 roots_154 ops++addP pm 8 dom_203 8 roots_203 ops++addP pm 9 dom_202 5 roots_202 ops++addP pm 10 dom_211 8 roots_211 ops++addP pm 11 dom_194 4 roots_194 ops++addP pm 12 dom_147 5 roots_147 ops++addP pm 13 dom_83 5 roots_83 ops++addP pm 14 dom_216 7 roots_216 ops++addP pm 15 dom_218 8 roots_218 ops++addP pm 16 dom_90 5 roots_90 ops++addP pm 17 dom_139 5 roots_139 ops++addP pm 18 dom_75 5 roots_75 ops++addP pm 19 dom_27 5 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_139 _ g hchk
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
theorem lowS_221:Lower true dom_221 roots_221 goal_221 10:=lower_slice_b [(0x30303030000000003030303000000000303030300000000030303030,128,132)] (by decide +kernel) lowS_217
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_slice_b [(0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc,64,66)] (by decide +kernel) lowS_229
theorem lowS_235:Lower true dom_235 roots_235 goal_235 10:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c,64,66)] (by decide +kernel) lowS_233
namespace S_243
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(1,129),(2,18),(2,66),(2,130),(3,19),(3,35),(3,67),(3,131),(16,17),(16,18),(16,80),(16,144),(32,33),(32,96),(32,160),(34,35),(34,50),(34,98),(34,162),(48,49),(48,50),(48,112),(48,176),(64,65),(64,66),(64,80),(64,96),(64,192),(128,129),(128,130),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffff
def xsM:=roots_243.map (·&&&dom_243)
def gM:=goal_243&&&dom_243
def NN:Nat→Nat
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xfc84
|9,0=>0x7a9f6
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f00000000000f000f00000000000f000f00000000000f000f00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000ca000a000a000a000a000a000a000a000a000a000a000a000a000a000a000af000f000f000f000f000f000f000f000f000f000f000f0000000000000000f000f000f000f0000000000000000000f000f000f000f0000000000000000f000f000f000f000f000f000f000f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x6b191ac688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>7
|9,0=>0x76
|_,_=>0
def wAt:=mkWire dB 7 244 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x21
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
addP pm 0 dom_242 8 roots_242 ops++addP pm 1 dom_179 7 roots_179 ops++addP pm 2 dom_115 7 roots_115 ops++addP pm 3 dom_241 8 roots_241 ops++addP pm 4 dom_227 8 roots_227 ops++addP pm 5 dom_211 8 roots_211 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_243 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_211 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_242 8 s (0,roots_242.map (·&&&dom_242)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_243 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_242 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffffffffffff0000000000000000,64),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_243==dom_243)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_243 gM v ys):RunD true dom_243 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_243 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
  · simp [NN] at hi
  · simp [NN] at hi
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
namespace S_246
def pG:List (Nat×Nat):=[(2,18),(2,66),(2,130),(4,36),(4,132),(6,22),(6,38),(6,70),(6,134),(16,18),(16,80),(16,144),(20,22),(20,52),(20,84),(20,148),(32,36),(32,96),(32,160),(34,38),(34,50),(34,98),(34,162),(48,50),(48,52),(48,112),(48,176),(64,66),(64,80),(64,96),(64,192),(68,70),(68,84),(68,100),(68,196),(128,130),(128,132),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_246.map (·&&&dom_246)
def gM:=goal_246&&&dom_246
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x90f3
|7,0=>0xc35e7a86594c5b844b7c3df2f
|8,0=>0xbdea86d4fd
|9,0=>0x3f43d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x1540154015401540154015401540154015401100154011001540110015401100002a8000002a8000002a8000002a8000002200000022000000220000002244004400440044004400440044004400440044004400440044004400440044aa000000aa000000aa000000aa000000aa000000aa000000aa000000aa000154015401540154015401540154015400000000000000000000000000000002a802a80000000002a802a80000000002a802a80000000002a802a8000000055004400550044005500440055004400550044005500440055004400550044aa00aa00aa00aa00aa00aa00aa00aa00aa000000aa000000aa000000aa000140014001400140014001400140014001400140014001400140014001400142a802a802a802a802a802a802a802a8022002200220022002200220022002255005500550055000000000000000000550055005500550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x572806537280654728065a372806537218054328065a728065728906543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x2286dd4735c67
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 247 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1d9784e176619765e1764e17645f86619785d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x1ffe66fe7eff5f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x76485
|8,0=>0x32
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_242 8 roots_242 ops++addP pm 1 dom_182 8 roots_182 ops++addP pm 2 dom_244 7 roots_244 ops++addP pm 3 dom_230 7 roots_230 ops++addP pm 4 dom_118 7 roots_118 ops++addP pm 5 dom_214 8 roots_214 ops++addP pm 6 dom_228 5 roots_228 ops++addP pm 7 dom_102 4 roots_102 ops++addP pm 8 dom_116 4 roots_116 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_246 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_116 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_242 8 s (0,roots_242.map (·&&&dom_242)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_246 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_242 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_246==dom_246)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_246 gM v ys):RunD true dom_246 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_246 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_246 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_slice_b [(0x303000003030000030300000303000003030000030300000303000003030000,1,17)] (by decide +kernel) lowS_233
def isoMvS_175:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_iso_b isoMvS_175 (by decide +kernel) lowS_159
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 10:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_123
def isoMvS_189:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 10:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_123
def isoMvS_190:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_183
def isoMvS_237:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 10:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_235
def isoMvS_245:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 10:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_123
def isoMvS_252:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccccccccccccccccccc,126),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 10:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_123
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xcccccccccccccccccccccccccccccccc,16,18)] (by decide +kernel) lowS_125
def dzo_27_4:=0xf0f0f0f0
def gzo_27_4:=0xf0e0a000
def gsh_27_4:=0xf0e0a00
theorem lowS_zo_27_4_27:Lower true dzo_27_4 roots_27 gzo_27_4 5:=lower_iso_b (d1:=dom_27) (r1:=roots_27) (T1:=gsh_27_4) [(dom_27,4)] (by decide +kernel) (lower_slice_b (T:=gsh_27_4) [] (by decide +kernel) lowS_27)
def dzo_45_2:=0xcccc0000cccc
def gzo_45_2:=0xccc800008800
def gsh_45_2:=0x333200002200
theorem lowS_zo_45_2_45:Lower true dzo_45_2 roots_45 gzo_45_2 5:=lower_iso_b (d1:=dom_45) (r1:=roots_45) (T1:=gsh_45_2) [(dom_45,2)] (by decide +kernel) (lower_slice_b (T:=gsh_45_2) [] (by decide +kernel) lowS_45)
def dzo_155_4:=0xf0f0f0f0000000000000000000000000f0f0f0f0
def gzo_155_4:=0xf0f0f0f0000000000000000000000000f0e0a000
def gsh_155_4:=0xf0f0f0f0000000000000000000000000f0e0a00
theorem lowS_zo_155_4_27:Lower true dzo_155_4 roots_155 gzo_155_4 6:=lower_iso_b (d1:=dom_155) (r1:=roots_155) (T1:=gsh_155_4) [(dom_155,4)] (by decide +kernel) (lower_slice_b (T:=gsh_155_4) [(0xf0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_27)
def dzo_173_2:=0xcccc0000cccc00000000000000000000cccc0000cccc
def gzo_173_2:=0xcccc0000cccc00000000000000000000ccc800008800
def gsh_173_2:=0x33330000333300000000000000000000333200002200
theorem lowS_zo_173_2_45:Lower true dzo_173_2 roots_173 gzo_173_2 6:=lower_iso_b (d1:=dom_173) (r1:=roots_173) (T1:=gsh_173_2) [(dom_173,2)] (by decide +kernel) (lower_slice_b (T:=gsh_173_2) [(0x33330000333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_45)
def dzo_59_4:=0xf0f0f0f0f0f0f0f0
def gzo_59_4:=0xf0f0f0f0f0e0a000
def gsh_59_4:=0xf0f0f0f0f0e0a00
theorem lowS_zo_59_4_27:Lower true dzo_59_4 roots_59 gzo_59_4 6:=lower_iso_b (d1:=dom_59) (r1:=roots_59) (T1:=gsh_59_4) [(dom_59,4)] (by decide +kernel) (lower_slice_b (T:=gsh_59_4) [(0xf0f0f0f00000000,0,32)] (by decide +kernel) lowS_27)
def dzo_61_2:=0xcccccccccccccccc
def gzo_61_2:=0xccccccc8cccc8800
def gsh_61_2:=0x3333333233332200
theorem lowS_zo_61_2_45:Lower true dzo_61_2 roots_61 gzo_61_2 6:=lower_iso_b (d1:=dom_61) (r1:=roots_61) (T1:=gsh_61_2) [(dom_61,2)] (by decide +kernel) (lower_slice_b (T:=gsh_61_2) [(0x3333000033330000,0,16)] (by decide +kernel) lowS_45)
def dzo_187_4:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0
def gzo_187_4:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0e0a000
def gsh_187_4:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0e0a00
theorem lowS_zo_187_4_27:Lower true dzo_187_4 roots_187 gzo_187_4 7:=lower_iso_b (d1:=dom_187) (r1:=roots_187) (T1:=gsh_187_4) [(dom_187,4)] (by decide +kernel) (lower_slice_b (T:=gsh_187_4) [(0xf0f0f0f0000000000000000000000000f0f0f0f00000000,0,32),(0xf0f0f0f0f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_27)
def dzo_189_2:=0xcccccccccccccccc0000000000000000cccccccccccccccc
def gzo_189_2:=0xcccccccccccccccc0000000000000000ccccccc8cccc8800
def gsh_189_2:=0x333333333333333300000000000000003333333233332200
theorem lowS_zo_189_2_45:Lower true dzo_189_2 roots_189 gzo_189_2 7:=lower_iso_b (d1:=dom_189) (r1:=roots_189) (T1:=gsh_189_2) [(dom_189,2)] (by decide +kernel) (lower_slice_b (T:=gsh_189_2) [(0x333300003333000000000000000000003333000033330000,0,16),(0x333333333333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_45)
namespace S_191
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,18),(2,130),(3,11),(3,19),(3,35),(3,131),(4,36),(4,132),(5,13),(5,21),(5,37),(5,133),(6,22),(6,38),(6,134),(7,15),(7,23),(7,39),(7,135),(8,9),(8,24),(8,40),(8,136),(10,11),(10,26),(10,42),(10,138),(12,13),(12,28),(12,44),(12,140),(14,15),(14,30),(14,46),(14,142),(16,17),(16,18),(16,24),(16,144),(20,21),(20,22),(20,28),(20,52),(20,148),(32,33),(32,36),(32,40),(32,160),(34,35),(34,38),(34,42),(34,50),(34,162),(48,49),(48,50),(48,52),(48,56),(48,176),(128,129),(128,130),(128,132),(128,136),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffffff
def xsM:=roots_191.map (·&&&dom_191)
def gM:=goal_191&&&dom_191
def NN:Nat→Nat
|4=>7
|5=>33
|6=>178
|7=>349
|8=>218
|9=>53
|10=>7
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x7511f53c655071416c3d141820ceff07155
|5,0=>0x9f1907b2d966ee35e6435acbc4d6f14cf6649c954683546805462cc4497131db330a1a2aef72749c230da22ea720e482063f202091ca871aa9015bf4129050d71c0c9310ba490b0dc05f4605efd029fc00999
|6,0=>0x45346450af43d93429a6428fa41f164056d404f53e1f33d3293ba3e3a0dd3977f38ede37fd236f1934d1e34a2033c5d32d3131c0b306672f5e02f17a2e81f2e0822c9e52c9092c38e2c20f2c1242a433297c828c7427a6d2776b26d7e257c32516224da724831239062300222e79227de2219d214a41ff0b1f4d11f4881e7551d81c1d52a1cbf21c4431a7271a0d219cf9198bf181f017f6e1798c16bc9164031522714e9e14e25142eb13b3d134621319611fcd11b40119ac114921123410eed1092710781101810fd8f0fab60f4f90f47d0f4310f1350efb90df690de720dc820dc590d4790cf2a0cab50b28a0af560aee60ae5d0a09809e6709c48096f1091b2090ea08a340828807fc207db607c7f078da077a20637a0530104f1c04e3a047ed046c903c0f03356025e1020b301c860129d00ab0006730049b0027b00116
|6,1=>0xcdb4bba955af36fabd54a4df1a17169f7459c6a292322919a08f2408a4008706d867d58138c80caa7e9597bd797388b734f271fd96ca206b94d68dad65b2f642956417660fd85d8295ae065a9c45921e5862957b0f55ccf53c6d52f534fb1a4f8f24f8b54f3a34dc5b4ca804c0ac4a8554a7f2484e7484df46c9846608
|7,0=>0x1dd001d94a1d42b1bb601b3181b11e1b0021ab671a6081a42c1a41919fd219b4a199dc194ac189dd183b1182021779c171b016c8016a6a16975164a915f2115eb715c6c1560e1523c14d7514b6c149941401313ff613cc813a711351912bb612557120cd1202711ad911492112bf10d8e10bcf0ff190fe340f1b30f1b20f1940ef290ed450ec850e9710dfc80d9120d6cd0c8fb0bb540b7640b57e0b3100afcc0ae5d0a6870a5a509fc309e3d09c8309a820961208e4208ac90897a0890208793086480832507fbd07e2b079c2078a6076c907659075a20704106cea06af206ae306adf062710546e05425053d00530104c1a04ba404a0e049a7047d8045430414d037b6037a2036f90346502ea902d7c02815026eb026a4025d9024bc021ae020db0204701c8f019d801977018ff0141200f8500c9b00c5d00a0300735005f8
|7,1=>0x4ef894e6704e37e4e0434d4c74d1d74afcf4a67e4a29b4a23749c2149b4b491fe4916c48483463e945d9d45735456864513d447fb447b743e0a439834383b42ed042dfc42d144286f417d7417c8410654106440f5640eac40d234051a3ffd33fb6b3e9603e9133e8793d9d63b6e03b6c63aac03a8ee3a26e3a19c394bc393503849937f6c37dbb37a7a37726376b9375cd373d93738e36c563622636169351fb350993503634870346603460d3446f343d633b5e339a13323432ef63196231940315ca314e1312873106130717304662faab2f9252f6e12f5a52f0d72e7d02cab72ca502c7cf2c62a2b7702b21c2a6d72956f2946e28f55285c62847528414283d527d37279812762b275832707926d5a2562623fa9239f323876228c022656221b72205521c10217c020f3e20d4420921204f3203291f4371eceb1e1a81de62
|7,2=>0xe2721e0424d8c7bd4acdd378fcd500c90e4b815ab64ceb5cefb2928ae6ababbd5a9c2ea8e68a8337a6640a226fa17779fd409f3549f1639eeff9c6e79b6a89b4399ac0496f50958d790ab68fc358a5a78946a88322867ec86650864ff85bbd8585a837648117580caa7e5407cb3a7b2e379ba27876976ec575cb4737e272954715d270d0270aaa707c0704156fbf86c6426c62f6a2756a0706a01c6987268e9d67a7f65eb665993649ff61d2861ae260f1360ef8603415f41f5ee445e9b95d6065d4d65b7335ac26597c257afc57af6574c05736155b99556a552d10528fb5280151ac0517cb50ed9
|8,0=>0x3fba93f0d43e1d33d9d63c0723ba1d3b99b3b7423a3993851c3700133aa4339a1332d3329843279b313c330f262fbce2f8362f2e32f06e2e7772e20f2d9c72cc582c16f2b7792b04c2aa7f29ca4291b028ffb27a3c276d02759a2636f25aeb25865256ae24fa324a04246b12317d22b8d2243122361211a7203dc202281fee01fe7b1ef071df761dcba1d6241d42b1cffc1c6361c0761b4c11a98116b031676815d8815c6c15b2e159e31523c14e4c140ae136ad1367e131af12dab12d401276d11f0b11d3f111c410fae1068c105c90fa8a0f0c70ef5c0e9d50e5280e4a60d32e0c9dd0c65c0c5370c1810bc780b09b0ab1f0a43109a82092e50906408cca085e607b3b076c906fea06ebc06855064a40634605c91053d00534c04c1a044f004407039b80372503498032d90270c01ef4014170134500dcc008e7005cb00182
|8,1=>0xe3b2fd9414c6919c1415b2641b07d3ac8bd9f94d9f67c9b4399ac0498c3296ce5958d792d30927ab91df38cce589bfb89a0a7dcf97ca817c3487c3197aabe7a80d7959c7907e76ff476f4d73e8d734c07302370fec6e6ac6bb606b1c66ab186a52d69eb1692c468ab06898167a78674ae6379b631f6620386082d5f6945ebd75c8aa5c25d5b5145b1d45a97b5a5ab5a48957af656f2054ee551ba8516cf50a9c4fc0f4e3304df394d3394d24a4c2714b4e149cc649a9a4897b484d547bf2473ca46d7a4624745934455914513d4383e42deb4213b417c8415f2415674135b40abd
|9,0=>0xfab72e0b7dd1836b8713aac2da2d9796ce58d84078e3b708596f9746d62b626e55ee57582b7541ae513564f9644eb564c9ff4b0d44abfc4a1fd4264e418283a95a396b5389962fb852eb272d22a2ab0e29bc82746a272992534e1f7e51ed161b0941a804188501260e0ff790e38a0d4c40b94f092e508ce60712a0443603961037c701d3b
|10,0=>0xc502bc4e91b84b6644614a2491deb511d8d
|11,0=>0x2bff1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfff0fff0fff0fff00000000000000000fff0fff000000000ffffffffffffffff0000000000000000ffffffff00000000fff0fff0fff0fff00000000000000000fff0fff0fff0fff0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ffffffffffffffff00000000000000000000000000000000ffffffffffff00000000000000000000ffffffffffff0000ffffffffffffffff0000000000000000ffffff00ffffff00fffafffafffafffa0000000000000000fffafffaaaaaaaaaffffffffffffffff0000000000000000ff00ff00ff00ff00cccccccccccccccc0000000000000000ccccccccccccccccffffffff000000000000000000000000ffffffff00000000ffff0000ffff00000000000000000000ffff0000ffff0000ffeeffeeffeeffee0000000000000000ffeeff00ffeeff00ffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0a0a0a0a
|0,1=>0xeeeeeeeeeeeeeeee0000000000000000eeee0000eeee0000ffffffffffffffff0000000000000000ffffffffaaaaaaaafafafafafafafafa0000000000000000fafafafafafafafa333300003333333300000000000000003333000033332222ffffffffffffffff0000000000000000ffffffffff00ff00ffffffffffffffff0000000000000000ffff0000ffff0000ffccffccffccffcc0000000000000000ffccffccffccffccffffffffffffeeee0000000000000000ffeeffeeffeeeeeeffffffffffffffff0000000000000000ffffaaaaffffaaaaffffffffffffff000000000000000000ffaaffaaffaaff00eeeeeeeeeeeeeeee0000000000000000eeeeeeeeeeeeeeeefffffffffffffafa0000000000000000fffafffafffafafaffffff00ffffff000000000000000000ffffff00ffffff00ffffffffffffaaaa0000000000000000ffaaffaaffaaaaaa0f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa
|0,2=>0xf0f0f0f0fffffff00000000000000000f0f0f0f0fffffff0ffffffffffffcccc0000000000000000ffccffccffccccccfafafafafafafafa0000000000000000fafafafa00000000ffccffccffccffcc0000000000000000ffccffccffcc0000ffffffffff00ff000000000000000000ffffffffff00ff0000330033003300330000000000000000003300ff003300aaffffaaaaffffaaaa0000000000000000ffffaaaaffffaaaafffffffffffffff00000000000000000fffafffafffafff0eeeeeeeeeeeeeeee0000000000000000eeeeeeeeeeee00000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0000ffffffffffff00000000000000000000aaaaaaaaaaaa0000000000000000ffff0000000000000000555500005555aaaaffffffffaaaaaaaa0000000000000000ffffffffaaaaaaaafafafafa323232320000000000000000fafafafa32320000333333333333333300000000000000003333000033330000ffffffffffff00000000000000000000ff00ff00ff000000
|0,3=>0xffff0000000000000000000000000000ff00ffffffffffff000000000000000000000000000000000000ffffffffffffffaa0000000000000000ffaaffaaffaaffaaffffffffffffff000000000000000000ff00ff00ff00ff00ffffffffffffffaa0000000000000000aaaaaaaaaaaaaaaaffffffffffffff0000000000000000000000000000000000ffffffffffffff000000000000000000ffffffffffffff00ffffffffffffff000000000000000000ffff0000ffff000000000000000000000000000000000000ffffffffffffff0000ff00ff00ff00ff000000000000000000ff00ff00ff0000000000000000ffcc000000000000000000cc00cc00ccffcc00000000ffffffff000000000000000000000000ffffaaaa050505050505050500000000000000000505050505050000ffffffffffffffff0000000000000000ffffffffffff0000333300003333333300000000000000003333000033333300333333333333333300000000000000003333330033333300
|0,4=>0x55550000000000000000aaaaaaaaaaaaaaaa333333333333333300000000000000003333333333330000000000005555555500000000000000000000aaaa0000aaaaff33ff33ff33ff330000000000000000ff33ff00ff33ff0000ff00ff00330033000000000000000000ff00ff0033000000330003003300030000000000000000003300030033000000000000ffffff00000000000000000000000000ffffff00ffffffff0000ffff0000000000000000ffffffff0000ff0055555555555555550000000000000000555555555555550000000000000000000000000000000000ffffffffffffaaaaffffffffffffaaaa00000000000000000000000000000000ffffffffffffaaaa0000000000000000ffffffffffffaaaaffffffffffffffaa0000000000000000ff00ff00ff00ff00000f000f000f000f0000000000000000000f000f000f000033333333333333330000000000000000333333333333222200ff00ff00ff00ff000000000000000000ff00ff00ff00aa
|0,5=>0xffffffffffffaaaa0000000000000000ffff0000ffff0000ffffffffff00ff0000000000000000000000000000000000ffffffffffaaffaa0000000000000000aaaaaaaaaaaaaaaa0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f000000ffff0000ffff00000000000000000000ffff0000ff00ffffffffffffffff0000000000000000ffffffffffffaaaaffffffff555555550000000000000000ffffffff55550000ccccffffccccffcc0000000000000000ccccffffccccffccffffffffffffff000000000000000000ffffffff00000000ffffffffff00ff000000000000000000ffff0000ff000000ffffffffffffffff00000000000000005555555555550000fff0fff0333033300000000000000000fff0fff033300000ffffffff333333330000000000000000ffffffff33330000ffccffccffccffcc0000000000000000ffcc0000ffcc0000ffeeffeeffeeffee0000000000000000ffeeaaaaffeeaaaa00000000ffffffff000000000000000000000000ff00ff00
|0,6=>0x3333333333333333000000000000000033333333333333000000ffff0000ffff00000000000000000000ffff0000aaaa333333333333333300000000000000003333ffff3333ff00ffffffff000000000000000000000000ffffaaaaffffaaaafffffffffffff0f00000000000000000fff0fff0fff0f0f0fff0fff0fff0fff00000000000000000fff0fff0fff00000555555555555550000000000000000005500550055005500bbbbbbbbbbbbbbbb0000000000000000bbbbaaaabbbbaaaabbbbbbbbbbbbbbbb0000000000000000bbbbbbbbbbbbaaaa0000ffff0000ff0000000000000000000000ffff0000ff00333333333333333300000000000000003333222233332222fffffffffffffafa0000000000000000f0f0f0f0f0f0f0f0bbbbababbbbbabab0000000000000000bbbbababbbbbaaaa00000000ffffffff000000000000000000000000ffffff00000000000000ffff0000000000000000000000000000aaaaffffffffaaaaaaaa00000000000000000000000000000000
|0,7=>0x333333033333330300000000000000003333330333333300afafafafafafafaf0000000000000000afafafafaaaaaaaa0f0f0f0f00000f0f00000000000000000f0f0f0f00000a0a00ff00af00ff00af000000000000000000ff00af00ff00aa0f0f0f0f0303030300000000000000000f0f0f0f03030000fffafffafffafffa0000000000000000fffafffaff00ff00fffffffffffffff00000000000000000f0f0f0f0f0f0f0f0fffffffffffff0f00000000000000000fafafafafafaf0f0ffffffff000055550000000000000000ffffffffaaaaaaaa0f0f0f0f0b0b0b0b00000000000000000f0f0f0f0b0b0a0a0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0a0aff33ff33ff33ff330000000000000000ff33ff33ff33ff00000f000f000f000f0000000000000000000f000f000f000a000000000000ffff00000000000000000000000000000000ffff0000ffffffff0000000000000000ffff0000ffff000000000000555555550000000000000000ffffaaaaffffaaaa
|0,8=>0xffffffff00000000000000000000000000000000fafafafafafafafa0000000000000000fafafafafafa0000ffff0000ffffffff0000000000000000ffff0000ffffaaaa00000000ffffffff000000000000000000000000aaaaaaaa00000000000000000000000000000000ffffffffaaaaaaaa00000000000055550000000000000000ffffffffffffaaaa0033003300330033000000000000000000330033003300003333333333333333000000000000000011111111111100000f0f0f0f0f0f0f0f00000000000000000505050505050000ffffffffffffffcc0000000000000000ccccccccccccccccafafafafafafafaf0000000000000000afafafafafafaaaa0000ffff0000ffff00000000000000000000aaaa0000aaaa555555555555555500000000000000005555555555550000ffffffffffffeeee0000000000000000ccccccccccccccccffffffffffffffff0000000000000000ffffffffffffff00ff0fff0fff0fff0f0000000000000000ff0fff0fff00ff00
|0,9=>0xffffffffffffffff000000000000000000ff00ff00ff00000000ffff0000ffff00000000000000000000ffff000000000000000000000000000000000000000000000000ffffaaaaffffffff000000000000000000000000ffffffffffffaaaaffffaaaaffffaaaa0000000000000000ffffaaaa00000000ffffffffffffaaaa0000000000000000ffffffff00000000ffffffffffffffff00000000000000000000ffff0000ff00000000005555555500000000000000000000000000000000ff00ff00ff00ffff0000000000000000ff00ff00ff00ff00ffff00ffffff00ff0000000000000000ffff00ffffff000000ff00ff00ff00ff000000000000000000ff00ff000000003333003333330033000000000000000033330033333300000000ffff0000ffff000000000000000000000000000000000000ffff0000ffff00000000000000000000ff000000ff00aaaaaaaaffffffff0000000000000000aaaaaaaaaaaaaaaaffff0000ffffffff0000000000000000ffff0000ffffff00
|0,10=>0xafafafaf000000000000000000000000aaaaaaaaffff0f0fffff0f0f0000000000000000ffff0f0fffff000011111111111111110000000000000000111111111111000000000000000000ff00000000000000000000000000000000ffff0000ffff00ff0000000000000000ffff0000ffff0000ffffffffbbbbbbbb0000000000000000ffffffffbbbbaaaaffffffffffffaaaa0000000000000000aaaaaaaaaaaaaaaa00000000ffffaaaa000000000000000000000000ffffaaaafffffffffafafafa0000000000000000f0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00ffffffff555555550000000000000000ffffffff0000000000000000000000000000000000000000ffffffffff00ff0000000000000000000000000000000000ffffffffffff0000ffffaaaaffffaaaa00000000000000000000000000000000000000000000000000000000000000000000ffff0000aaaa0000000000000000000000000000000000ff00ff00ff0000
|0,11=>0xffffff00ffffffff0000000000000000ffffff00ffffff00ff00ff00ffffffff0000000000000000ff00ff00ff00ff00555555555555555500000000000000005555555500000000ffff5555ffff55550000000000000000ffff5555ffff0000333311113333111100000000000000003333111133330000ffff0000ffff00000000000000000000ffffffffff00ff0000005555000055550000000000000000aaaaaaaaaaaaaaaa0000000000ff00ff00000000000000000000000000000000333300003333003300000000000000003333000033330000ffffafafffffafaf0000000000000000ffffafafffffaaaaffffffff0000ffff0000000000000000ffffffff00000000555505055555050500000000000000005555050555550000ffffffaaffffffaa0000000000000000ff00ff00ff00ff00ffffffff000000ff0000000000000000ffffffff00000000000000ff000000ff00000000000000000000000000000000ffffffffffff00ff0000000000000000ffffffffffff0000
|0,12=>0xf0f0f0f0000000f00000000000000000f0f0f0f00000000ff0fff0fff0fff0f0000000000000000ff0fff0fff0fff00333300003333333300000000000000003333000033330000bbbbaaaabbbbbbbb0000000000000000bbbbaaaabbbbaaaa0f0f0f0f00000f0f00000000000000000f0f0f0f00000000ffffffffffffcccc0000000000000000cccccccccccccccc00000000ffffffff000000000000000000000000ffff0000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0fffffafa555555555555000000000000000000005555555555550000f0f0f0f0fffffafa0000000000000000f0f0f0f0fffffafa00ff00ff00ff0000000000000000000000ff00ff00ff00000f0f0f0f0f0f0f0f0000000000000000000f000f000f0000ffffffffffff00000000000000000000ff00ff00ff00ff00000000ff000000ff0000000000000000000000ff000000000000afaf0000afaf00000000000000000000afaf0000aaaaffffffff0000ffff0000000000000000ffffffff0000aaaa
|0,13=>0xaaaaaaaaaaaaaaaa0000000000000000ffffffffffff0000aaaaaaaaaaaaffff0000000000000000aaaaaaaaaaaaaaaa00ff00ff00ff00aa000000000000000000aa00aa00aa00aaffffffff003300330000000000000000ffffffff000000000033003300330033000000000000000000000000000000000f0f0f0f0003000300000000000000000f0f0f0f00000000ffffffffffffffff00000000000000000000ffff0000aaaaff00ff00ff00ff000000000000000000ffffffffffffff00000000000000555500000000000000000000000000000000000f000f000f000f00000000000000000000000000000000ffffff0fffffff0f0000000000000000ffffff00ffffff00ff0fff0fff0fff0f0000000000000000ff00ff00ff00ff00000000000000000000000000000000005555555555550000333303033333030300000000000000003333030333330000000055550000555500000000000000000000555500000000aaaaffffaaaaffff0000000000000000aaaaffffaaaaaaaa
|0,14=>0xffff5555ffff55550000000000000000ffff0000ffff00005555555555555555000000000000000000000000000000003333111133331111000000000000000033330000333300000000000000ff00000000000000000000ffff0000ffff0000fffffffffffff0f00000000000000000f0f0f0f0f0f0f0f0ffffffffaaaaffff0000000000000000ffffffffaaaaaaaaaaaaffffaaaaffff0000000000000000aaaaaaaaaaaaaaaaffff0000ffff55550000000000000000ffff0000ffff000000ff00ff00ff00ff00000000000000000000000000000000ff00ff00ff0000000000000000000000ffffffffffff0000ffff0000aaaa00000000000000000000ffffffffaaaaaaaaffffffffffaaffaa0000000000000000ff00ff00ff00ff00000055550000555500000000000000000000000000000000ffffffff000055550000000000000000ffffffff00000000ffffffffff00ffff0000000000000000ffffffffff00ff00cccccccc888888880000000000000000ccccffff8888aaaa
|0,15=>0xffffffff00ff00ff0000000000000000ffffffff00000000050505050505050500000000000000000000000000000000afafafafafafafaf0000000000000000aaaaaaaaaaaaaaaa111111111111111100000000000000001111000011110000ffffffff0000555500000000000000000000000000000000aaaaaaaaaaaaffff00000000000000000000000000000000aaaaaaaaaaaaaaaa0000000000000000ffffffffffffaaaaffff0000ffff00000000000000000000ffffffffffffaaaa0000ff000000ffff00000000000000000000ff000000ff00000000000000ff000000000000000000ff00ff00ff00ff00ffff00ffffff00ff0000000000000000ffff0000ffff0000000000000000000000000000000000000000ffff0000ff0000000000000000000000000000000000ffffff00ffffff00ffffff00ffffff0000000000000000000000000000000000ffffffffffffffff0000000000000000fafafafafafafafa0000ffff0000ffff00000000000000000000fafa0000fafa
|1,0=>0x111111111111111100000000000000000000000000000000ffffffffeeeeeeee0000000000000000ffffffffeeeeeeee00000000000000000000000000000000ffffaaaaffffaaaafffffffffff0fff00000000000000000fffffffffff0fff0ff00ffffff00ffff0000000000000000ff00ff00ff00ff00ffffffffffff55550000000000000000ffffffffffff0000ff00ff00ffffffff0000000000000000ff00ff00ffffff00ffffffffffccffcc0000000000000000cccccccccccccccc
|_,_=>0
def sP:Nat→Nat
|0=>0x58b40a010705c2c0c028400813160404c0a15868240c02828080306040540a020a450160282808030589c0226020681a1203014461a0b0300a04058740a2405038060d090180a230182c442105038262002840221e0200c040c00810100d09014140e0182c3a010e06c3419090301c130c048180e0b85818150704c2812028382612028441208038180a04018080200
|1=>0x5814660a07010060b0609c0204018340c10188285603090181805050ac3412030300a090181c0c050d86832200604008030781820300700c240b02844081a068b80c101580c281202828081a030bc20210700c1a2e03040361a068800a100200c5806080443c290b0300a0a020685016028401c1a0902c18050700c50160284008290589c220a020203212060281217
|2=>0xf010064306014200e01818780c028406404018180a10210101012058300a0a0200c18102090014041480c1815200281c031e0300a1002020320c080fc140e018f4780c02840120e0182c18051d810340d030800a1019010520b0a8441404098e00c0c0284008030c048160c0501034030581402331b810060c028406c040181818101a8283c03058740a34050c84603
|3=>0x60407e0e01848160c02810060b06014024f190102606060409c0902068161d00884120e040640c0c08010060b06014024d1908c060b02804221b0200c1a10180281c04098b0181005010060b060148e0a0200c980c0812c143715838060d028408c040182c181500810060b08044940a020680c0c080849248020681a06028400803068180a47051183c040182c3a05
|4=>0x508cb203058740a0a0700c165808044142b0d080180508028725701818180508010060b0611c600a020e00c0c028400803058740a012a810065405840420a0700c2406058300a0e018640c1008940080305840820005010064c058404c0a1594c060d08084140401830204e20028080328818181e0182c181512828080306840605005010060b08138660a0700c3206
|5=>0x3201420040181420112002808030598c201105038060d0301420620200c16270809814230d02c18050098464230182c1801108102e5f058300a012401010190604014040400c0c0c0297408290d02c0a01130241c290581402110200c16101097014230d02c18050089408130c830205b05010101910030200a020683206060407e390700c0c05080443c040182c0a33
|6=>0x1a02890040d0640c0c080e41c031e0300a100200c160c081b414043600c161d028040803358640c10050241c130c840220a1580cd40508028081a0c818400c080385203059900a100700c780c02840d2040182cd0100882808030599c201105038340b100300a100700c0c0c2c04008130181818051d8243c17058740a0a0200c16103280014090181c160505038060b
|7=>0x200c1615009d414040b80c162d0280408033a02c202605010060508100e60a04820320c081881439021c40c0c028401c03058302a011a118080b06014206e11868160c028940803030300a3b0204c240c0282812230182c0a330508c080305814660a22038340b0601402040182c20411302808700182c180500810060b081bcb80a0200c1610108cc140b06014206e
|8=>0x59a0207b050c8082905814022615838063c0601420040b80c16153a82846033d0141409158340a102d82864041482c18270508c081a218300a100705c160c028404a2b0700c0c0c08084081a059e00a01080241c03059e40a10018300a101b18814440700c860c02840460e0190c180508024085203030200e0182cf00500840ee040182c180500810060b08084ec0a
|9=>0x604014320200c5806060401c04018340c1018024ac0606014200401a0016103f8280803029f8207c05010520305854ea0a1901026190809814040d02c0a01081f4080302840227c050245671030300a101c81006060601476040d0b8160c080102619060407e0a19010060d030409c2b02068780c02840460e0182c180132838060b1001420110200c160c138040803
|10=>0x9868160c430401204018b00c0c080380612058300a0a0200c160542a0c14090705c161d0280412570181818050802408130c8404c0a0200c16153ea101432020a4160c02804080305814fc8305110081a0583104100200c1a12030141409020a4160c1382812040190c1805008c808030681820210700c160c028ed02040182c18051d86c262006014200a240102619
|11=>0x5024ac0b06014200a070101003068180a1019010060b06041120a11a34060b06014200a23010060b0601420720200c160c00840380a04838520b06054140945868160c02840140e0182c18050811412040b82c1810108280808018641847050c80803058300a3b45010060b0601420040182c208921028080b06014202405010060b082210e0a0200c1627080441404
|12=>0x8250145a0200c160c0808414321180c160c08138141e0200c160c0a80526040182c0a1008a48140e0182c18050084068091180c160c02a4414040980c167902840140e020a4340b06014020e0181816200601420040182c1810188285603058300a101f8281204058300a10370280813388181805080ac081a058300a101d024080305a380a1005024081a2602c1810
|13=>0x80286404098680c0c0284064040182c1805080e81c040182c182708028081a058801805080243c230182c3a050508c060b06014029e04810067405830200a4e038060b06014200a0701006190303020924d00c160c02840140e018f0180508010060b06014209905024360306814200a22010060b06015220a04810269706014200a19010520b06014020a0200c160c
|14=>0x601402090204c0c0c02840e4090d80c160c0284014040182c0a01081d414040d00c1805081001404019ac160508029460409818180508028081a0182c0a10198283c040182c180500a88881e0200c161d028286404018b0160c0802864040182c18103782902040400c320c080280803058302021508290203058300a10310280803058300a104f828121b018340c05
|15=>0x1b8ac1c03058300a1040810060b028404c0a1180c162d0282890040d018160c0284008030302c18052382808290d02c18050811408030581420a62d8280803058302036448280803058310c1005010066b0302c0a10050c85603058142026051114a03058300a1005010060b060148e0a1c8ac1c03030300a100204c340b028404c0a04838260b02840220a22038060b
|16=>0x98181805080fc14040d00c16050084022040182c180500a0c14480200c320c0824814390182c180508188140e0182c181500a3064230182c0a10088280838030300a101580c0c0c02840c40a19010060d0301420320200c1a0b080841444070a4060b06014021b0200c160c080c014230700c160c02a0c140e0182d4e0508024461a058300a010f010060b06040820a
|17=>0x5038080305830204105078080305830204e0506c08030c81820a6050ac0803058300a3b050e46404018181805080243c0b06014206e05038060b060155210190100606058300a1055010060b06040420a0200c160c02aa41404018f4160c02aa414090200c0c0c02840742b2980c160c0808414040182c18101814014040d02c180500aa0140902068161d080841404
|18=>0x2840b60a022d8060b029f8200a020a4060b06015520a04ad4060b0601402100200c1a0602840b60a1b8c80803058300a100200c1605082d0220a020a4060b06208200a02069660c0284160040982c1805080286409020a4160c028040803058740a011282872040182c0a10130281c0305814fc105782808ae0186416100882808030583020ad0502408ab058300a10
|19=>0x84064040182c204e0882808170182c1805418281c040400c3206060401204018341610270281c04019d0160c080280813100300a10050111a03058740a01050c8460305830202105010060b0601402b902020060b02840220a04810060b32014200a0200c0e0b02828120e058300a10370280803058303e010200c161d02804c20a15810060b060416e0a0200c160c
|20=>0x6040820a07010060b0e81402840700c160508044cc0a29810064c05830200a24010260606014200a11810060b0601402450486c061903030200a1902408130c830200a022fc060d5f014200a022f0060b06041760a5d0100606058300a10020e0060606014201e0182c0a100023014810200c160c0291c140409818400c0284014040182c0a103a828120e0b82c1805
|21=>0x6818203005024460b06014206e05024080305830208905011200305830203105010060b0284022c105038060b028042011460e40803058310c10050e40803058300a470503808290182c0a0108918081a0182c1805080c84603058740a0a0486c340b06014200a22010060b06040820a0495c060b06014200a22010060b060140245600102e0b06014200a11810060b
|22=>0x87808170182c3a0505010060b028413ec405010060b081384c0a40810060b028414c0a0200c320b0809814040182c0a7e08304142b0700c0c05080446e040182c180508028880e0d02c18050802808290182c18054182812230182c1810270285603058300a103102808030330c160c0284008134b02c18050802808292f82c18050802812045f82c1805080280803
|23=>0x601402040d00c1a0608084122b0182c0a101302916040182c18101082808030583198100511846040182c180500810060b028410e0a19010060b06004204e0200c16150832c14040d02c18ca0803806060601420660200c161d0280592040182d9005080281c1a058300a1063828081a05b180a1005024080305830206f050103403030300a101b0c81c041482c1805
|24=>0x980c320c0802808ae0182c20d20882808290182c18056802864040182c18680802864040182c18670802808030581420cf05010340b06014205b0508c060b02840008c05025480306814200a0200d9c0b02840144411838060b0e81414b00200c160c028401404018640c0c0816c14320200c18050810014440200c160c08194140e0204c061908044144423010060b
|25=>0x4878520b06014020a19010060b0280420112208c081a058740a0a6c010060606014200a40810060b06014200a5181026190604014040400c160c081bc14043880c1a060284072b50182c18050802808080182c1805080e8640e0204c320c080288c040182c18050835d0204018340c050802808d501835a805080280803058302a0169828642b0182c1805080286e04
|26=>0x58404226050241c03058300a101d010060617814200a04838520b06014020a0700c160c02804206115810060b060148e0a0200c320b08368141b018340a1028028720e018181805080280813018180a10088281c03058740a01460258003058300a1005024060b16814200a02020061906040c40a190103403068180a1007010520b06014028402068060b0601420d9
|27=>0x205c160c02840dc0a04810100b06040600a22038060b02840220a15810060d02840b60a04838060d0301420440200c160c02b7814320182c1805080d014040182c1805080fc14230200c160c02b78143702020060b0601420040404c320c08248142b0200c0c0c080c014040182c180554b7414040182c18270802902040980c320c08028080305814207d420280803
|28=>0x1d82808030581420112d8289004018340c0508028460e0182c1810108281204018300a102002808290182c1810208286404018181805080d81c0401818160c080c0120e0d02c1805008406e090700c160c028400803058300a0122824081a068180a102d010060b0601420450700c16050831c220a1c8241c03030300a100200c16050820c4c0a048ac060b028414c0a
|29=>0x5831c010108283c04018300a102002812233882c1805080283604098680c0c02840080309018160c028281c130181818050814008030902c180505038060b06014203f050100656030300a101583806060601420920200c0c0c02974b4460200c160c0284008135582c18050802864df0200c160c028400803030f018050802980040d02c18050802812040182c1805
|30=>0x5010060b06014021039204080306014203605010060b060142083050e408031e0300a10050241c0305814021008838080305830d010050102e03058302a8c050c80829058300a83050780803058302a84050100606058300a104f81026030c840220a1b810060b0601420b10200c1a0608084140e0182c400c02840140e0200c160c008409c32020a4160c028040803
|31=>0x80286e0401818160c0284008130c8302092050102e0b060142025050c81204018340c05080105203058302ad1051100803218300a1005025c429058300a10050e408ab058300a10050e40803060142036051680803058142075050c80803058409c26050c808030c82c20260506c060b0284022500506c060b06014203f050243608058300a10053840803058300a10
|32=>0x828812040182c1805080288a440200c160c0284014720200dc80c02840140401a0016050804414320200c160c02841060a190240803058740a1005010060b02841061105010060b08348220a221181c03058300a100200c16101084414040182c18051d82812040182c204e13028880e0182c1805081147204018181805081c812041482c18054182872570182c1805
|33=>0x506c0803068180a1005038080801818160c02840360e0182c180508140141e11810060b0e8141409020681a0b02840149a0182c180508029ca040182c1805080280803058300a104c82872090700c160c02840141b0200c1a050802812040182c181027028120e0d02c18050802856040d00c0c0c0284056040d00c160c0808414230200c160c02a4414040d02c1805
|34=>0x1a001605080280803058740a910502436030302c18050802864090204c160c0284014044680c160c02841180a0200c1a0602840a00a220240803058300a01050e40803058300a10052b0121b0182c18050802836040182c1805080281c0414868160c0284014235280c160c028401404018340a1028028460e0182c180500810060b06014209f053980803058300a10
|35=>0x50102603030300a10478240803058740a0105010060b0601402106982808130182c18050802874040182c2a10088288c090200c160c0284014440700c160c02840141e02068060b06014200a1180c160c02805180a6e010061905830200a75010060b06015d21005011d003058300a10052c808130182c1805080280803030300a10248284603058300a104f0281c04
|36=>0x823c08ec058300a1005010060b028414c0a5a810060b0601402100200cac0b06014200a220385203058300a100503808290182c1815050c808030302c18050822c081a0182c18050802812230d02c1805080280803058300aa905010060b75814200a0700c160c028418e0a04810060b06014200a6b810060b63014200a2d0c80803058300a1005024060b0601420bd
|37=>0x182c18106682888230200c161d02829021b0200c160c0284014040d00c160c0084042390204c060606014200a0204c340606014200a0200c160c083b4140401818160c02840b60a0200c160c02840143a07010060b060409c0a0200c0c0b028414c0a0200c320b060413c0a22010521a058300a1005010060b06014205b0528c0803058740a10050102e03058300a01
|38=>0x8140141e0200c160c02840dc0a2b810060b06014200a15810060b06014200a56038060b0601420500528c0813058300a1005010060b0e81420f0050c81c040982c1805080283604018640c0c0802812040d064160c08028120e0182c18050839c6e040980c160c0284014390200c160c0284014b10f010060b02840220a0204c060b06040600a0200c160c0f8401404
|39=>0x58300a10050380803058300a103702812041482c18050082946040182c180500840143202068060b06014021022010060b06014200a22810340b060140210423000803058300a010802872040181818050802864040182c18150802812040182c18050820c14040d00c161d02804120e0182c0a1008828721b0200c160c0284014040182c18050834c1404018640c0c
|40=>0x4f01006060601420f22d0240803058300a10051108c040182c1805080280803068180a1049810060d03014208f190101003058300a10052c00803058300a1005038080305830202105010060b0601420f40506c56040182c0a105302808f3018641810050101013058300a104902864090200c160c02841dc810204c060b06014200a04810060b060140210390dc0803
|41=>0x182c18050820c14c00200c160c02840140902020260b06014200a02020160c02841240a408100606058300a1005010060b0601420f70501006f606014200a0200c980b0604014040d00c160c02840a00a11810060b06014206e052040803058300a10050254803058300a10050241c03058300a01080105203058300a91050c85603058300a1005010060b060140210
|42=>0x282808030302c1805080fc140e0200c1a06028400803058300a101f8283c040182c18050821014044b00c160c0284014040182c180508029f4040d02c18050812414b50200c160c0a8401409020a4160c0284014e311810060b06040420a7c810060b06014200a04810e20b06014200a0205c060b060042065053e00803058300a100502408034b82c1805080281c04
|43=>0x182c18050818414811c810060b06014200a0200c160c0284014fb0200c162006014200a0205c060b06040ca0a070105203058300a01050ad6a03058300a10050103403068180a10050c808030581420260511064040182c180508028080305814021008828b40e0200c160c02840140409868320c080283c041480c160c0280414230700c16050804414091180c161d
|44=>0x182c1805008400803058300a100535c08290182c180508344143211838060b06014200a0200c16a70284014040182c190008028081a0182c1805083d014040182c18050834414097f80c160c0284014040182c3a057e82864090200c160c08138140e0200c320b0804414040182c18107e028080305830204e05010060605880180508028a6040182c1810108281204
|45=>0x200c160c0284014040182c180500840e50204810060b06014200a19010060b06014200a0200c160c02841060a0700c160c028407c230182c180508230143204810060b060140210048781c03058300a10050c81c040182c181027028640e0200c320b0604014040182c18055484014320200c160c02804200a0200e020b06014200a048ac060b06014200a39038081a
|46=>0x50ac0803058300a100524c08170182c180500840140401864160c08029260401864160c080291e090200c320b0604014040182c18050802962320200c160508044142b0200c0c0c02841240a04838060b060140210050380803058300a010821008034b82c18050802836040400c160c0284014040183606050802808bf0980c160c0284014320200c160c02841dce1
|47=>0x182c1805080280803068180a10050102e290182c1805080280803058300a010823c1c040182c18050839e0c040182c1815080281c0401864160c0802809050182c18050802a0804018341605080281c040d00c160c0284014040182c1805082f4140401818160c02840a00a11838060b06014200a0200c160c02840a00a020203403058300a100506c0803058300a10
|48=>0x50240803058300a10053b872040182c18050802856040181818050802946040182c180508028640e0200c160c0284014040182de21d0284014040d00c160c02804200a07010060b0601402101c8102603058300a1005010060b06014200a2f01026030c830200a0200c160c028401472190240803058300a1005010060b0601420490503808030581420110508c081a
|49=>0x58300a10050f8120e0182c18050802812040182c180508028e4b50200c160c0284014090200c160c02804200a02068061905830200a19010060b06014200a220240803058300a1005010060b02840220a0200c160c0a8401507048ac060b06014200a0200c160c02841920a15810060b06014200a5c011de03058300a1005010060b06015d21005010060b0601420c5
|50=>0x200c160c0284014040182c1805080291e090200c160c0284014040182c180508029dc040d00c160c0284014040183416050802808130182c1805080280803058300a01080280803
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x794032a0145007a8029400aa0005
|5,0=>0xe1606e2835981a0c0ca6062302f98170c0b26056302998140c09a604a302398110c082603e301d980e0c06a60323017980b0c0526026a811d8082c03b601ab00bd8052c0236
|6,0=>0x14db8a51c51ae286713fb89e1c4e2e26a7131b8971c4acc24f712438905c474e233711638895c43ce21951093882dc408e1fd70fbb07c1c3d2e1e270edb8751c39ae1c670dfb86e1c362e1aa70d1b8671c32ae18e70c3b8601c2f2e17270b5b8591c2bae15670a830525c284e13b709a384b5c24ce11f708c38445c214e103707e383d5c1dce0e77
|6,1=>0x229b9131c88ae43e721bb90c1c852e422720db9055881ce407720038fe5c7e4e3eb71f238f75c7ace3cf71e438f098778c3b661d7b8ea1c742e39a71c9b8e31c70ae37e71bbb8dc1c6d2e36271adb8d51c69cc34771a038ce5c664e32b719238c79862ee3107184b8c0d85fac2f67177b8ba1c5c2e2da7169b8b31c58ae2be715bb8ac1c552e2a27
|6,2=>0xb56e5a472ceb9659cb1ee58872c0b95e9cae6e56c72b2b9579caaee55072a4b9509ca76e5347296b9499ca3ee51872893142dca08e4fd727b393bdc9d2c4e2726db9351c99ae4c6725fb92e1c962e4ab625239275c92ce48f72443920988f6e4747236b9199c8c2a45a7
|7,0=>0x3ce39e520f19078483beb9dd60edb076583aec1d59ce9d0746839f41cda0e5d0726838f41c5a0e1d0706837f41bda0ddd06e6836fb9b5e0da0e6c8836041ae20d62e6ab6351c1a71cd29068c8342419f5cceb066d8332c19760cab064d8322c18f60c6b062e73134187a0c2ee60f8303c17fe0bf0e5f082f4417820bb105d082e4b97060b74e5b28
|7,1=>0x4c64261212f9097484b64259212b9095484a642512127cc93684974249a123d091684874241dd1ff08f78477c239e11bf08d78467c2321d18108b88458ba2a6114308998448c2226110308798438c21a610c3085984293a12a1088c83c841aba0b6104b081d840ac203d9010e80083fc41fc20fd4c7e283ed41f4a0f9507c283ddb9ece0f5707a38
|7,2=>0x5bfc2dde16df0b6875b042d65d6a30b4a75a142cea16650b2a859142c6a16250b0a858142bedd5e70aeb8571c2b6e15a70acb8561c2aee15670aac755242a7215290a8c8542429f214e90a6c85324297214a90a4c8522428f214690a2c8512ba876142b0a0d85033a7fa13ed09ee84f34277a13ad09cf74e3c26fe1370e9b084d442689933509946
|7,3=>0x6b63b5921ab90d5486a6bb519da7d0d368697bb49e1a40ed188688434221a010cf88678433a219c10cd88668bb3261984ecba8659432aa19450c9a86494322a19050c7a8639431aa18c50c5a8629bb12e18870c3c761abb0b6184b0c1d860ac3036180b0bfd85fb3afba17cd0bdf75ebc2f41d7910bc175ddb2ed1d75aeba675cf42e5dd71f0b878
|7,4=>0x7afc3d5e1e9f0f47879fc3cde1e5f0f28779043c65de230f0987813bbea1de50eea877143b6a1da50ecb7761c3af1dd690eae675343a7a1d2d0e8e8743439fa1ced0e6e87334397a1cad0e4e8723438fa1c6d0e2f77143b8821c310e108704438021bf10df086f4437821bb2edd186e4c37061b730db186d4c36861b330d9276c54360a1af6ed738
|7,5=>0x1043881e3c0d2205af026780f4405a201d100687ff43fda1fdeefe787efc3f5e1f9f0fc787dfc3ede1f5f0fa787cfc3e5e1f1f0f8787bfc3dde1edf0f678
|8,0=>0x927c491e247d32368917bc8a1e441121799083c81e63ff11f788f7c479a63bb31d678e6cc716237931b488d64468e6337119298c54460a22f5117378b54c58662b1315088a3cc4fa626d112e8892cc476222cf10f7883c43fe21ef10ee9872cc37621ab10ce7863442fa216b30ae78534427a212d108d9842c41f9e0eb306c9832bc17620a9304b9
|8,1=>0xa2fbd161e89f34478a1fc50de285d34277a0f4d0566819340399fdc4fca67d513e199ec4cf3e678f13be99db44eba274b339e79cb44e36670b137d89ba4cdb226c7335b89a9c4d2e2685333a899944caa26433318998844c222602f2fa797944ba665c312d8996844b25e58132b8895844aa2254112979947c4a1e24fd327779383c9a224c112579
|8,2=>0xb34cd9826cb2f6527b24cd9062c7316327b14cd8862c34f6137b054d80a2bf335f09af4457822bb115cf9ae3c56fe2b6f15ae9ad3456766b2cf58d9ac2c55f9eaeb356e7ab3455766aab154d8aa2c54f62a69352c8a92454722a27350b8a814d3e669e314e89a704535e699f14c87a60bd2e2695f34a78a4fc525e291f14878a3fc51e1e8df34669
|8,3=>0x2e8b173c9b99cdcaa6e4517199b893dc266e0316f98b78c5ba26dc116d88b68bdb262d8136b79b574da966d3b16949b4645a0e6cf536728
|9,0=>0x18fa8c79463a671c318d89c6846322317f38b87c58462a2314118979c47c621e30ff18769c374619a30bd18559c26c6112707918339c15c6091f03918139c05c600e2ff537f37bf54df8a2fb517d28be545f0a2f7517b19bd4c5e826f3117908bc3cddfe2eed376d9bb2c5d762eab174d8
|10,0=>0x64c6325319218c8cc6449f21519028
|11,0=>0x19397
|_,_=>0
def wAt:=mkWire dB 264 192 0xffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x808104818018190200d020291c818098110182d0582902029080f1058f90482801811048180602d058290801502029018e91c8280204d0700d020291905401839020290284108029100410202d0481805829078410181107034058290602d02029018050181107074080290604102029058950204104804018290200d08029020050587d0d05408029028410182901811018190803d07034058290602d02029
|1=>0x18410282d04818058290482d2d0430f00d07041020291186a018290582901959158680202d01829048070181110041048180202905829081490d064058290282d0182902841048040802902029100410481801811058291901701839020290200d01819020290282d05829070330700d020290401701819020190582919064058150182d01839020290181a1182905915220280188d098110182d0183902029
|2=>0x58290484101811058150182d0200d02029190340202d018390602d02029048180282d05829061150202922028020a51e043058f90482801811020290481801811020290582902999018ae0202d0200d080310180502005080290803d07034018110602d020290202906115220280188d02041080290d0110d017018292f805080290198111828020410817901819158280202d0582919033080290d01101829
|3=>0x1839020291c818058291580d0202d020292d0330b8110d04101829058b50707402041060410202919054018410206902841018290591501829220280188d020290d0170582901829048040188d0200d0d064058290282d018290480401805070740802906041020290200d040130d02d01829019c90482a0482d0200d0204104804018290200d08029080e91c8281580d0202d058290182d10041048180200d
|4=>0x182940843040110d02d01829080e91c828048290482d0204d0582919064048290282d020291004104818058290180506041020290181108029049c90482a0200d08029059152202804841080e91c8281580d0202d020291906405829020690282d01829058290200d158680202d01829018060482a058291001504818018290200d058290b81702029018050802904818080291905402069028410182919033
|5=>0x1c8280204d0802902029018410182904818020290582948017019410201a058290486e01811158292d00f22029048410200d058290182d01a3d0202a018291c828018ad19074048290604105885018110d017018290200d158680202d0182905831020290181905829028da1902f02069018294681701a31020060184102029018110284101829018111182b02041220281180d0204102029018110d0410d017
|6=>0x4818018290200d0582908031018111182902041080290700f0204102029059391901704829022751483b01841020290181a020290282d058290226d148380184102029058f90482801811020290702d018110602d020291180d082611182a020410482a0200d0d011018294b01701a550702f020290b8110d0410d01701829190170206901829020050182a0284108029070330205e01805080291182a060e9
|7=>0x52029018111582b0202d2d03304805018112d02f0205d0d04101829100310481801811058290482b0200d0620e19043020690182902005148280184108029080310188d118290204119064020690282d01829408171902d020690182905815040110d02d0182902189040130d02d01829500290481b0200d0582905831020190181105829058290d0110182d018291c828048290482d19054028410183902029
|8=>0x200d0182902041080292d0170f00d07041020291c82b1580d0202d1902d190330183902029070740204106041020290181a40843048190200d0182922028020a501841028da1902f0206901829028e91c8280204d0182d100310481801811190330183902029022611180d1182a02041408431902d0206901829058291580d0202d020291903302069018290182d0200d020290202914811018410802905829
|9=>0x482d0200d0202d020850d0170182914813018410d017018290200d060410481a0200d05829018290703308029020290802919043020690182902249058150181a05829040130204d098290182d02006020290284108029070330700d020290582901979158280202d02022018190582905829018390602d020290602d0d017018290202904017020190181905829190430700d0202906181118280204102029
|10=>0x8031048040181108029021fa0804507033020290282d070330202902a0e19043020690182901ab11c82a0482d0200d2d017018790704102029070411901701839020290282d0d8330201905829080e91c828018ad0202d05829048290482d0200d0200d0f00f0704102029080f9048280181102029049c90482a0200d29841020850d01701829220041180d020410802905aa5080f9048280200d058291c828
|11=>0x182900a8b148280184108029018190703305829020290611522028048410803d070340602d020290f00f0181107041020290d054080290284101829080310480601811080295581701ae11582a019f90804507033020290811522028020a508029058310186e02019058291c82b048290482d0200d570430184507033020290291522028020a505a891482801841018295900d022c50982a08029048290200d
|12=>0x1af90602d05a3d0202a5e01701af507043020290da4f0182a020190582901979158280202d020060f0330200508029408431902d02069018290182d048180200d058292d03319041018390202901805020290181108029070331901701839020292d0430b8110d0410182901819020290282d058290602d1901704829059391901701839020290182d048180200d058290604101a3102006080290d01702069
|13=>0x20a5099c90482a0200d0182d058310401701819058291182902041028da1902f04829019410201a05829019fa080450703302029070330200608029018412d02b0205d0d04101829020410183906041020290200d0702d0182902029020e91c8280482d018112d01701879118290604102029018060802905885020850d017018290181a0802922028020410581502019018110582905815048290200d0182d
|14=>0x48430181101829062a1020a601841408171c8290482d1902f020690182901839020290184108029080310180502005080290627e628290482f0181119017190330d8330d80d0702d0202919033020690282d0182908045070330202907033020290202d05829048410200d2d0430205d148290184119017048290181102041408130186d158290202d031cb0482a0200d01b090983a0182d020290191522028
|15=>0x20410202904ab11c82a0482d0200d058150186e02019058292d02f1904102069018290182d0282d07033020292202b1180d020410d017018290602d058291903304829018110202d0d017083353881701a3d0202a2202b0188d0204106156638290484301811190170206901829028415a8330224d0182a028f9048280200d01829020291580f0202d058290206a018290604108029062751483b0184102029
|16=>0x21c90482a0482d01811098291c8280204d058150182d018390202904011018190602d0582901b5105b590682a0602d518290482b01811058151c82b0204d0182d57017018450703302029083451483a01841020290d011080850d017018290813919017020690182959033022c50982a0182d018290d80f0702d020290f0330f013118290204105831018111582b0202d05899190330183902029060411180d
|17=>0x201a0582902029098110182d058290182d070330582902029020060802906041020290218504806018110802907074018110604102029040130d02d0282d0182902069018290602d058290202901806508291186b0204101829018410200501811080290703301839020291180d01829058295182d0482b0200d1cac5098110982a0182d058150482b0200d0182d040110d02d0182901a3d0202a0602d05829
|18=>0x602d020290181105829081c90482a048410200d2d0131904101839020290835d2202a0188d020414082b040110d02d018290400f098290182d0202d04017018190582905aa6080f9048280200d190540206902841018290581502021098290182d0d01719033020291c8280181105829061250204e0182d01841020290181108029048060181108029408430186d158296e0330236d0c82a0282d0214105831
|19=>0x1580d0202d01806080e91c8280482d0200d0602d022490181a05829020290d01702041018292d02f22029048412d0170205d148291902f020690182902029040170181905829018290202901811080290482d01811220281180d02041080290200d018290602d058290703305829190431903301839020290d83301811158290202d0f00f0200501805080290200d040170d02d01829048410602d158290202d
|20=>0x20290602d0d01705829018290481802029018110582908029190170183902029018390202901841080292d02f0f00d0704102029019c90482a01811020410182d01829020190582910041048180200d058290201a0182d10041048180200d058290481a02029018110582905829158680202d018290202d020290181a0582908179158280202d05829220292202b020a50184101ab11c82a0204d0182d1c818
|21=>0x1902f048290482d0200d2d0331904101839020291901719033018390202919033020690282d018290d8130702d07033020290481a02019058290200d02019018190582915ab11c82a018ad0202d1282a048040200d1902f1902d020690182919043518290482b0200d02029080850d0170182902841018050200608029190430d0110182902841020050180608029500290481b0200d058290282d070330182d
|22=>0x200d059811182802041058450703302029190430206901829048290200d0604107033190430183902029570170184507033020292202b0188d02041070330d017080e91c8280204d0182d1903319017048290482a0482d0200d048290200d4082b048190200d058290282d0400f098290182d04804018050200d0802904829058290200d0602d020a5018410200d0238d1482a0184101ae11580d1582a0202d
|23=>0x201a05829020290204108029628290482f0200d04b9f0582a0200d020190602d058290202901819058290d8130702d02029060411182902041018290200d0602d02289148280184111a4f020410182a33029018ae0202d020290482d018110702d0602d0202919017048290200d0200d0202901829018290202d058290202d0d01701829082611182a0204114828018410182922028048410200d0482a04841
|24=>0x200d1180d02041020290704101829020290200602041080290236d0c82a0282d023a50824d0182a01a611182a02041022c50982a0182d098130182d058290700f0204102029058450703302029060410823d0202a020190181105829048290200d0182d01a3102006080290201a0602d0582908029048410200d0204d0182d020190181105829520291582b0202d020290184101829022611182a0204105831
|25=>0x80290197b158280202d0d8330702d02029080290224d0182a158680202d01829148110184102029018410284102029058290206901829018291182b02041020410200d01829080f9048280200d060f904828018110484301811020292202a04841062a1020a6018411904102069018290200d07043020290202a0182d05829080290200d06041048070200d1c8280204d0182d0703302841020292202b04841
|26=>0x582a020291c82b0204d0182d098110982a0182d07041070330202904017098290182d0d05402841018293881701a3d0202a080310188d020410d80d0702d02029080290d01701829098110182d05829018290182d058297781701bb90802a0186e02019058291c8280204d0182d1901701839020290d83302019058290282d0183a020291481101841018290d80f0702d020290482b0200d060410202a01805
|27=>0x200d08029020690182922028020a5018410182901806080290221101806080291580d0202d0582902069028410182919043048290200d0182906041080290200d0703302029018ad158290202d048070200d080290201a0282d058290f00f0704102029023c9098280182d1c82a018ad020290201a058290482b0200d0182d01bc60e829060410182d0183902029020190282d058290200d0282d018290200d
|28=>0x18410823d0202a0700d0202d02029080290183a02029098280182d0582922029048410200d2202b020a501841058290182a0602d0202a0602d05829020690d02d01829023d501b9d0582a0d01702029018291586b0202d018290d833158290202d0282d0982b0182d0400f098290182d048290802a0200d02021098290182d0482a0200d080291c82b0204d0182d0187a07041020290181101841080290482b
|29=>0x1829028410224d0182a1482a0200d018410d0170204101829518410482b0200d019c90482a0200d0b817018050802901a2d1182b02041059c90482a0200d1904301839020290221101806080290200d098290182d01a490181a05829048190200d0582901afa05a3d0202a058fb048280200d058850d01701829018290201a058290187a11829020411902d0206901829018111582b0202d020290181108029
|30=>0x204d0182d5402a020a601841048180200d058290b8170d041018290202901841080290202d0224d0182a018290602d0582919033018390202904829048410200d0703308029020290187907041020290182d0282d01829020050184108029070330204102029020410200d060410481a0200d05829058290602d02029019420201a0582902005018060802901a550702f020296382a048430200d098130182d
|31=>0x183902029080f9048280200d08029020690182905b250206a018290482a018110202d0802902029018292202a020a5018411483a020290700d020410202906181118280204102979158280202d1586b0202d018291483a0184102029018110239d0582a083f90e82a0604119017048290200d0282d07033020290d0570284101829190170206901829048180200d05829020850d0170182904806080291c829
|32=>0x202a0282d018110282d0982a0182d0700d07033020290181a0202d05829020290181108029020290180608029059c90482a0200d02019018190582905a4d0182a0602d09a3d0182d0202a0802a02069018295a82d0224d0182a0482a0200d0802904bb90802a0200d518290482b0200d1904302069018290482801811020290f0131182902041048290200d080290181107041020291901701839020290282d
|33=>0x202d058290482b0200d01839020290e82906041080290182908029020290204d0182d158280202d0182d0282d0482a0200d048290200d0204e0182d070330202902041018290602d0582914829018410202a080290582a0202902055028410282d020291482b01841020350602d020290182907043020290201a0582902041020290201a058290d02d018290702d020290202d0182a01805080290182a0282d
|34=>0x202a0200d0802a018290602d0182d08029048280200d01811020290482a0200d0224d0182a0200d080290282d018290206901829048410200d07033020290a82a02841018110202d0206a018291582a0202d01bb90802a0824d0182a0482f0200d0802a0200d0204d0182d
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x70000
|5,0=>0x1960000000000000000000000000000000000000000000000000000000000000136000000000000000000000000000000d60000000000000000007600000000
|6,0=>0x7c3000007b1077407520000000000000000070506e2000006a4000000000000000000000655062300000000000005d5000005a3000005550000052304e4049500000000000000000000000004810000000004440422040203c400000000037500000325000002f302d202a30000000000000000000002820235000001f4
|6,1=>0xeb50e7400000e340e210000000000000e110dc50db10000000000000d65000000000d240ce4000000000c950c450bf5000000000bd200000000000000000000000000000000000000000b940b450b130ad40a85000000000a620a15000009c50000097509250000000000000000091108e3089500000845080407f100000000
|6,2=>0x13b41374000000000000000000001361132412e400001295000000000000126300000000000000001224000011d50000000000001185000011350000000000000000112100001102000010b500000000000010741061101500000fe30f950f540f050000
|7,0=>0x20f420b420832053201420011fc41f931f541f141ef21eb41e741e341df41db41d7400001d341cf41cb41c741c431c041bc41b841b441b131ad41a941a541a14000019d4199419721952191418d418a3186418511823181117e317a417731734170316c416841653162315e415a4156415240000000014f314b41474143413f4
|7,1=>0x2e442e1300002dd42da32d912d542d142cd42ca32c642c332c032bc400002b842b532b142ad42a942a542a1429d429942954291428e328a42864282427e427a4000027822744271326d426942654261425d425a32564253324f424c324b124742443240423c423842353231422d422c1229322540000221421d421a321732134
|7,2=>0x3b043ac43a843a623a2439e439b3397400003952391438d438943863382437f337b437743752372336f336b43683000000003671363435f435b4000035740000000035433504000034c434b134833444340433c433843353331432d432943254321431d431943154311430e330a4306430242ff32fb42f742f432f042ec42e84
|7,3=>0x490448c448934863482447e447a44764472446e446a446644624460245c445844553453244f444b444744443440443c4439343540000431442d4000042a34264422441e441a44164412440e440a4406440243fe43fa43f643f2400003ee43eb33e743e343e213de43db33d743d433d043cc43c843c443c043be23ba43b733b43
|7,4=>0x552454e454b35474543453f4000053b45374533452f4000052b45274523451f451d251945154511450d450945054501400004fe34fd14f9400004f544f144ee34eb34e834e444e044de24da44d6400004d514d414d044cc44c844c444c314c034bc44b844b4400004b044ac44a934a544a1449d44994000049724943
|7,5=>0x5af45ab45a835a625a2459f3000059c359a200005964592458e458a4000058825844580457c457845744570456c456935654561455e355a45564
|8,0=>0x66d366a366736643661365e365b3659265636533650364d364a364826453642363f363c3639363636333630362d362a362736243621361e361b361836153612360f360d260a36073604360135fe35fb35f835f535f235ef35ec35e935e635e335e035dd35da35d735d435d135ce35cb35c835c535c235bf35bc35b935b635b33
|8,1=>0x72b372837253722371f371c3719371637133710370d370a37073704370136ff26fc36f936f636f336f036ed36ea36e736e436e136de36db36d836d536d326d036cd36ca36c736c436c136be36bb36b836b536b236af36ac36a936a636a336a0369d369a369736943691368e368b368836853682367f367c36793676367336703
|8,2=>0x7ea27e737e437e137de37db37d837d537d237cf37cc37c937c637c337c127be37bb37b837b537b237af37ac37a937a637a337a0379d379a379737943791378e378b378837853782377f377c3779377637733770376d376a376737643761375e375b375837553752374f374c3749374637433740373d373a373737343731372e3
|8,3=>0x83738343831382e382b382838253822381f381c3819381638133810380d380a38073804380137fe37fb37f837f537f237ef37ec3
|9,0=>0x8a228a0289e289c289a28982896289428922890288e288c288a28882886288428822880287e287c287a28782876287428722870286e286c286a28682866286428622860285e285c285a28582856285428522850284e284c284a28482846284428422840283e283c283a2
|10,0=>0x8aa18a918a818a718a618a518a41
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 16
def pmP:Nat→Nat
|0=>0x4000000000001940000000000aa000000000051000000000022800000000011000000000008200000000003500000000001a00000000000c4000000000060000000000026000000000012800000000009000000000004000000000001b00000000000b800000000005800000000002a0000000000140000000000098000000000048000000000022000000000010000000000003800000000001800000000000a0000000000040000000000018000000000008000000000002000000000000
|1=>0x26280000000012000000000008e6000000000471000000000222800000000110c0000000008820000000004260000000002100000000001058000000000820000000000405000000000201000000000100400000000080000000000032000000000010800000000008000000000003ca0000000001650000000000a3800000000051400000000024a000000000120000000000088800000000044000000000020c0000000001040000000000810000000000404000000000200000000000084
|2=>0xa6a800000000515c0000000028aa000000001451000000000a10000000000505400000000282000000000140000000000090000000000045dc000000002240000000001096000000000841000000000415c00000000208a000000001020000000000808000000000400800000000200200000000100000000000042b8000000002010000000000e600000000006550000000003100000000001800000000000aa80000000005250000000002910000000001484000000000a40000000000500
|3=>0x10a88000000008518000000004260000000002125000000001090000000000845c00000000422c000000002103000000001080800000000840000000000418a0000000020c400000000104d80000000082400000000040e6000000002057000000001018000000000808000000000402e000000002015000000001009000000000804000000000400c0000000020050000000010010000000008004000000004000000000001725000000000b6b800000000595c000000002b6c000000001577
|4=>0x1b6b800000000d95c000000006bee0000000035f5000000001abb800000000d4dc0000000069ee0000000034d7000000001a3b800000000d15c000000006424000000003137000000001899000000000c4800000000061ee0000000030d700000000182b000000000c144000000006040000000003014000000001800000000000a54c000000004dee0000000026570000000012da800000000915c00000000448a000000002230000000001108000000000880000000000434a000000002180
|5=>0x49db8000000024cdc00000001256200000000929500000000494800000000246d40000000121200000000087970000000043638000000021ad4000000010d0a00000000863700000000430000000000216dc000000010a22000000008494000000004242000000002100000000001076c00000000830400000000415b800000002085800000001036e0000000081a300000000404000000000200800000000100060000000080020000000022020000000011000000000008040000000003737
|6=>0x2126a80000001000000000000409ae00000002000000000000983a800000004915c0000000242a8000000010051000000008020800000004000000000001c08800000000b6d7000000005b5b800000002da5c000000016bee00000000b5b7000000005aab800000002d15c0000000165ae00000000a39700000000516b8000000028a5800000001450e00000000a257000000005080000000002820000000001402600000000a002000000004b4800000000257dc000000012b2c000000009495
|7=>0x1001a6b800000800915c0000040029ce00000200144700000100025a000000800125000000400090200000200009600000100004080000080000d4000004000028000002000010000000800000000000200c26c000000816aae00000040b45700000020582b800000102955c00000081402600000040a00300000020500080000010200040000008062ae0000004030d700000020122b800000100895c0000008004000000004000130000002000010000000e08058000000086aee000000043457
|8=>0x4200109000002002d15c0000100160ae00000800a25500000400502b800002000d35c0000100068ee00000800345700000400196b800002000c84800001000610800000800265700000400122b800002000895c0000100041ae0000080020a700000400104b00000200082480000100040ae00000800204500000400010000000200002040000100000280000080000120000040000080000020000018000010000000000007801499000003811a6b800000802d15c000004010cae000002008245
|9=>0x2400007b800010c0002100000840500a60000420234d700002101126b800010800531c0000800468ee000040022677000020010378800010006c9dc0000800341e60000400190530000200088698000100029adc0000800069ee0000400034d7000020001a2b800010000c31c0000800040820000400001060000100002008000080000104000040000002000020000000000008005a2b8000040020008000020000aae00001000004600000420192b800002100995c000010804428000008402212
|10=>0x80001009000040000515c00020000200000009000a7d7000048001a6b800024000d15c000100817aae00008040b457000040201a2b800020100b55c0001008016ac00008000bb57000040004a2a800020000f35c0001000078ae000080003757000040001b8b800020000d6dc0001000068ac0000800030510000400017ab800020000b35c00010000400000008000144600004000000200001880899dc0000c0014d26000060001297000024808a7b80001200401cc0000900069ae000048003477
|11=>0x200005a2b80010000210440008000068ae0004000014f70002000008000001000001b5c000800000cae000400000502000200000033800100000008400080000002600040000000000010800122b800052404d15c0002900320a60001480134f70000a0809a3b80004a00002400002108060ae0001080000c5000080809a2b8000401028114000200016202000100007c57000080001aab800040000d3dc0002000068ae00010000301200008000127b800040000915c0002000044660001000020e7
|12=>0x40100122b800200800125800100400088e0008010014c7000400005aab800200002515400100000a88e000800003457000400000a2b80020000050480010000008aa000800000400000400000103000200000029800100000002200049000355700024000522b8001200000d5c00080c00006000040202267700020100132b8001008005b5c000804002c2400040200141200020100096a8001008004000000804000c2000040200060200020100027b800100800035c000804000040000402000000
|13=>0x40000001a2b8100000000110040000014aee020000003457008080201022804020100f55c0100000040e600600000000000208400162b801020002f55c00810000e96c004080007457002040001a2b801014000d55c008000007bae004000003d57002000001e6b800848104d1dc0042400368ee002120013477001020809a7b800810008d15c0040400568ae00200001b051001000009a3b8008000001440003000000824000c0000b457000600000a7b800210408d15c0010800468ae000802003457
|14=>0x24040020248ae804090006457402040001a2ba00020000985c8000800048ae202040063457101020011a2b880012000915c20000001488e080100002457
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x200
|5,0=>0x80000000000000000000000000000000000008000000000000000028000000000180000
|6,0=>0x20dc00670880000000892c220000000120000005160000120520700000980000000000000000000000011b0262011000002a868000f001cc7e0000000002e1889c00271a87c000000020001f023cc00000000036de0002000000000000e201000000036000ca0001800620403000000000000001f000006e286b19400001680088000aca0ca000000000006e0100008
|6,1=>0x2080000000000008410080000c0000000c4000000000100040800000002002180000000001f0039400d50000000330fc9000310a8060800
|7,0=>0x1a9b8001c130c20e01191038276598f4013e131141206094191a8306270f61a2b1f0d549001414a82d31080c01cc8fac4e39aa87000423b7e00042bb5e061f3288c0005479b8dc4f344818e20c38b82e37049c4ca091c05e8e0515800022984b305e06643eb040801d7cba87004fc9e65189d37c310a08549743b2c0147e328263a6e0429638e42500000aec7058bf26
|7,1=>0xdc880ae65a65b09e4fce035ba0b5465012f51f604cc2caa88ae28b3b2a8001e13800dd08048c9463447025f34296e345307028001d86d41bc2348bd8e8805cdec6e7a39260f010805783c0a28951fc112e00130643533248cc403c3641008008d4a6000007c13370c000d400000c74a0034c15e9095609c266eaf3dc686b1da965201768200ce6baa8b2a22043c81973
|7,2=>0x12b9615f70940400116310019b76355c800982526804360512428100f0910432290007c0d9123018cc8a0036d26435b8000976879aeba6d27c36c9c0009dd4e7b0893c016e2d82080c6622a498529a0005d0b029c802a50f822664d0080064017508cf925150014c82
|8,0=>0xd75c8f4d1dac4e2bba75aecea49430daf2415c17b359e91d7181a9a2231116806258dd607370d95b7aa45e2c4e9dd624fb4c6076a71f786ce1c96a74c6958489ce16286a068e3d84c83342d014d384c608e28eef56d9c8c5d3b2c4629ed9da96499c797460e83a287b27236bc2932236360bf6deff4427ae0ed884f26c964bc4e4343a7afe3ac57e338c458dff096abd
|8,1=>0x28b6430e59360fd65a58566302e9a0884ee7586fb55ab5366477211649618ad9c1bc13a6121a15e6bf8f503871810514b27b1e5448eb6645ad55deb2f89d5192babb2e4d129677d6ef14d442fafcfe3ead33eecb5216ce86abd84b2868918f2ecbbe5943b89
|9,0=>0x9b4fa81329edb353172fad4519f1967661109e914613cd3e266d31224b55936d273cc205a7bfe8235c8d8df792d04c595ff6578c6a33a4a8ec29696
|10,0=>0x259109667369ce96
|11,0=>0x86
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 49 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_189 10 roots_189 ops++addP pm 1 dom_159 9 roots_159 ops++addP pm 2 dom_187 10 roots_187 ops++addP pm 3 dom_146 4 roots_146 ops++addP pm 4 dom_175 9 roots_175 ops++addP pm 5 dzo_27_4 5 roots_27 ops++addP pm 6 dom_182 8 roots_182 ops++addP pm 7 dom_27 5 roots_27 ops++addP pm 8 dzo_45_2 5 roots_45 ops++addP pm 9 dom_143 6 roots_143 ops++addP pm 10 dom_190 9 roots_190 ops++addP pm 11 dom_181 7 roots_181 ops++addP pm 12 dom_63 8 roots_63 ops++addP pm 13 dom_183 9 roots_183 ops++addP pm 14 dom_157 8 roots_157 ops++addP pm 15 dom_45 5 roots_45 ops++addP pm 16 dom_179 7 roots_179 ops++addP pm 17 dom_186 7 roots_186 ops++addP pm 18 dom_59 7 roots_59 ops++addP pm 19 dom_164 4 roots_164 ops++addP pm 20 dom_180 5 roots_180 ops++addP pm 21 dom_53 4 roots_53 ops++addP pm 22 dom_167 6 roots_167 ops++addP pm 23 dom_178 5 roots_178 ops++addP pm 24 dom_155 8 roots_155 ops++addP pm 25 dom_158 6 roots_158 ops++addP pm 26 dom_154 5 roots_154 ops++addP pm 27 dom_151 6 roots_151 ops++addP pm 28 dom_188 7 roots_188 ops++addP pm 29 dom_171 8 roots_171 ops++addP pm 30 dzo_155_4 6 roots_155 ops++addP pm 31 dzo_173_2 6 roots_173 ops++addP pm 32 dom_55 5 roots_55 ops++addP pm 33 dom_60 4 roots_60 ops++addP pm 34 dom_174 6 roots_174 ops++addP pm 35 dom_62 5 roots_62 ops++addP pm 36 dom_58 4 roots_58 ops++addP pm 37 dzo_59_4 6 roots_59 ops++addP pm 38 dzo_61_2 6 roots_61 ops++addP pm 39 dom_163 5 roots_163 ops++addP pm 40 dom_173 8 roots_173 ops++addP pm 41 dom_61 7 roots_61 ops++addP pm 42 dom_156 5 roots_156 ops++addP pm 43 dom_150 5 roots_150 ops++addP pm 44 dom_166 5 roots_166 ops++addP pm 45 dzo_187_4 7 roots_187 ops++addP pm 46 dom_170 5 roots_170 ops++addP pm 47 dzo_189_2 7 roots_189 ops++addP pm 48 dom_147 5 roots_147 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_191 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_27_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_45_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_155_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_173_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_59_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_61_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_zo_187_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_zo_189_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_147 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_189 10 s (0,roots_189.map (·&&&dom_189)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_191 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_189 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_191==dom_191)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_191 gM v ys):RunD true dom_191 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_191 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 33 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 33 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 178 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 50 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 178 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 349 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 93 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 349 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 218 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 90 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 218 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 53 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 53 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 7 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_191 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_223:Lower true dom_223 roots_223 goal_223 12:=lower_slice_b [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,128,132)] (by decide +kernel) lowS_219
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,64,66)] (by decide +kernel) lowS_237
def dzo_211_4:=0xf000f00000000000f000f00000000000f000f00000000000f000f0
def gzo_211_4:=0xf000f00000000000f000f00000000000f000e00000000000e00000
def gsh_211_4:=0xf000f00000000000f000f00000000000f000e00000000000e0000
theorem lowS_zo_211_4_83:Lower true dzo_211_4 roots_211 gzo_211_4 6:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_4) [(dom_211,4)] (by decide +kernel) (lower_slice_b (T:=gsh_211_4) [(0xf000f00000000000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_83)
def dzo_243_4:=0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0
def gzo_243_4:=0xf000f000f000f000f000f000f000f000f000f000f000e000f000f000e00000
def gsh_243_4:=0xf000f000f000f000f000f000f000f000f000f000f000e000f000f000e0000
theorem lowS_zo_243_4_83:Lower true dzo_243_4 roots_243 gzo_243_4 7:=lower_iso_b (d1:=dom_243) (r1:=roots_243) (T1:=gsh_243_4) [(dom_243,4)] (by decide +kernel) (lower_slice_b (T:=gsh_243_4) [(0xf000f00000000000f000f00000000000f000f00000000000f000f00000000,0,32),(0xf000f000f000f000f000f000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_83)
namespace S_247
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(1,129),(2,18),(2,66),(2,130),(3,19),(3,35),(3,67),(3,131),(4,36),(4,132),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,23),(7,39),(7,71),(7,135),(16,17),(16,18),(16,80),(16,144),(20,21),(20,22),(20,52),(20,84),(20,148),(32,33),(32,36),(32,96),(32,160),(34,35),(34,38),(34,50),(34,98),(34,162),(48,49),(48,50),(48,52),(48,112),(48,176),(64,65),(64,66),(64,80),(64,96),(64,192),(68,69),(68,70),(68,84),(68,100),(68,196),(128,129),(128,130),(128,132),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffff
def xsM:=roots_247.map (·&&&dom_247)
def gM:=goal_247&&&dom_247
def NN:Nat→Nat
|4=>7
|5=>36
|6=>148
|7=>330
|8=>209
|9=>53
|10=>7
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xf1b91c2e89b109d92f4f7d6f9576831eab7
|5,0=>0xf1c33ecb5be7bf6e37b5d7ca7bc4ecb9d67b9ba3b93e9b6daab113f99dd38c4c38595684b737d79b75a075f3ce5e36450ce646838407563b191368e92d8812ceec27d9026d1419d82199881802b16dc5159ec0c8b109a390078c
|6,0=>0xdb550da41dd9542d6812d121bcd65acc23acb13ac98cbc3d98c26c2bf981bd70bbd5bab9e09b4a09b42bab3206b1c7bacd64a9acea98cea9250a436ba2da09f93f9f80d9f5989e07b9bc549b0be99e759965595f979594993daf926d490cea8e5b38d2318c5658bc81884c98748d859f882ea68252881f537fee97e0e77be9d76ab375aa975770755967367072d8a725d9724b26e3836d74c6bf9b69de869d296993469395687a66762b658646428d64267639695ff7b5f4705bb885b0d65ad705abfd5460751ebf5002c4eac44e72d4ccce4c24d4bc3949b12468da45dc43f4393cd7f39db93988a39841375b03698b339c432b2f323ce2f2192cdd3299082850d257ae206f61f4a51eeba1ec2e1e9cb1e3ac1dc4a1be821ae2e19e24180cd15f4715a8e1321211570103970d4900c9530b9a609411093cb089e902e6602257
|6,1=>0xfe62efb65dfb233fa777f9d00f9453f253ef077af0382ed931ea215ea073e9b75e91dae3857e116ae0433deb2bdba62db76d
|7,0=>0x676cd6767d671ba66cf766b6c6697465a6c6594d654d2641fd62138610b760e035dda35d8ca5d60a5bdbc5b53e5ad8e5a2b35989c584f15803d57e515774454a5e53a83528a25278f526cf5242551ebf503cf501af4f99b4f33b4ecc94ec9b4ccfc4c71a4c0954b1e14af61494fb49473492ed491454857b45b414544743b824316b4295341c50407d6401a6400043f3d23ef113eb983e0db3df973dc8d3a30a374cd356e9350da35092324d4318e531506308c9305612ed162e9a32dcaa2d71a2c7f02c7be2bb0f2b9012a1852903728ee528d29285af26bb02490c2274c1febe1f0a81cf921c2c31bf111ac6c19b1d1825a1751f1678f13a541350c133ba124d311ab60f5aa0d5d90cd190cc040ca520c3f90ba480b86b0b0a20a22c08cb508624085780849c07bbf068cd062fd058e604a0a03cd903cc701e5f00ee600196
|7,1=>0xc8ca6c8b7dc8b4ec7d2fc7705c686cc41c9c3122c2e3fc24b3c1162bf864bec42bd040bb9a8bb7d0bad94ba31ab9488b92fdb857cb8464b7613b7504b6f78b1889afc0eaf32faec38ade00adb44ad12daccc3abb1aab24caa678a8609a8515a8511a6304a5a92a5731a49c5a3cf0a3a40a347fa2a68a19f29ffe99ece99e9c29e11d9da7f9cff79c5039a7349a1eb9937b98cd897b41971e896df095f8f9537992e1692c6391b8191acc901c68f88f8e6138e4938dc8f8dbe28d7038cc0e8c7948acb48aa0c886758859e880ae87bbb87091852cd8457d844a784209840b782f488299b82039814ed7fe347f0bf7ed947e5087e1897da167c87f7bc8a7ad657a3f1763947609f75edd7563875130750ff74ffe74b12741f873e7471dd2715f2711427098c6ec226dd866dac16d6506cdec6c3ed6bedf692bb68c15686d767f8c
|7,2=>0xff670fe62efe5b4fd621fc1f9fc0effbc6efb7fcfb65cfb153faf9ffa8adf9da2f9000f8f71f826ef7d1cf64baf5a08f46abf3e7bf3b9df1febf14a6f1491ee864ed6d2eb41ceaf53eac38ea95eea2eaea0b1e7600e656be4fc1e4edee34c8e1981e120ce0bfddff8adebcddd767da162d9455d90acd8294d7c90d76b1d7671d61cfd48afd4497d4173d3c8ed3c17d28d5d2057d16abd15dbd12bdcfc91cf275cf237cec44ce4bbce2f6cd52ccc860cc7d5c9925c96b4c9506
|8,0=>0xa2fc09ecf79b8189a1eb9a13997f53978079591490b298fb0b8f07c8c91d8c769887e68800487ab786713834598130b812cf80a3d808fd800b77fcee7ddfa7dcf47bb2f7b2837a8bc78cb5744da73d877359971fa371748711816ed206e51b6d6506c9896ba126ab4468ded67b016770e6725c6707d6427863e3863c846348062da56119e5eafb5c8825a7ff57d5d5504552d9651aa8507574e8f74c87149c6147a42475f5475c3470e94688c4644c45f3e459e842e47429c44232c41bde419cd4156d3f2f73e4b43d6d63c8fc3c85b3c1653bb823af113a2c039ebf3792934df53439b31b1a3179530f862fcab2ed802d7872c7802a24f28ccb284aa244ba2285e224ed216a11fbff1ec641eade1a76619b33188061703c16c39169af133aa10d040fa310ba890ab290a7df0914306a6001faf019ec01629012a6010f2001d7
|8,1=>0xfec45fe828fd097fcf10fbb3afa248f911bf7f3df7f3cf6d07f638af5e70f58fdf4899f2783f1e68edfdceda4bed1d4ed017ebf80ebd6ceb970ead01eab95e95cde832ce805ae785de75fbe69c7e1004dfb10dfa1ddde15dd285dc582daf8fd94cad85bfd7917d7650d6718d5e95d4026d317ed0fedcfe20cfa0ccd50dcce06c9ab1c92d5c85dcc77dcc5d42c5bbec365bc2ee1c0e5bc0429bb51bbb12ababd3b87fcb6bf5b577bb3ec6b226ab2158b1b61b13c8ad481ace62acca7abf6cab17ba9ec7a84dda619ba4a28
|9,0=>0xf5a42e9229e39e1e1a1be031adb0c8d8de6d6743d6298d18a2d132bccf5dcbb71c6b3ac1903b2322b18edaf571ac82aa63bba3d7c968ac9646c93ea090afe8c79a896fc8794985d968218f7b98c7297d6fb856f2da6a3cb6713a669cf5d0ec55a5c4b95848c35403353c86e36c1734a6b30b151bc0119e910ac8f0634402040019af002d0
|10,0=>0xff591f9dd7b47c39ac027fd216aad410d17
|11,0=>0x3ef7d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff00ff00ff00f000f000f000f000ff00ff0000000000f000f000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff00fa00fa00fa00fa00ff00ff00aa00aa00fa00fa00aa00aacc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000ff00ff00ff00ff00f000f000f000f000ff00ff00ff00ff00f000f000f000f0ff00ff00ff00cc00ff00ff00ff00cc00ff00ff00ff00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa
|0,1=>0xf000f00030003000f000f00030003000f000f00030003000f000f000300000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000000000000000ff00000000000000ff00000000000000ff00ff000000ff0000110011001100110011001100110011001100110011001100110011001100000500050005000500050005000500050005000500050005000500050005000005000500050005000500050005000500050005005500550005000500550000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000000000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff000000003300000033003300330000003300330033000000330033003300000033000033003300330033003300330033003300330033003300330033000000330000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff00000f000f000f000f000f000f000f000f000f000f00000000000f000f00000000ff00ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa00aa00aa00aa00aaff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
|0,2=>0xf000f000f000f000f000f000f000f000f000f00ff00ff000f000f00ff0000ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00000f000f0000000f000f000f0000000f000f000f0000000f000f000f000000000f000f000f000f000f000f000f000f000f000f000f0000000f000f000f0000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00f000f000f000f000ff00ff00ff000000f000f000f00000000000000000ff00000000000000f000000000000000ff00f000f000f000f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00ff00ff0000000000000000ff00000000000000ff00000000000000ff0000000000000000ff00ff00ff00f000ff00ff00ff00f000ff00ff00ff00f000f000f000f000f05500550055005500550055005500550055005500550055005500550055000033003300330033003300330033003300330033003300330033003300330000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff000000000000000000000f000f000f000f0000000000000000000f000f000f0000
|0,3=>0xff00ff000000ff000000ff00000000000000000000000000000000ff000f00ff000f000000000000000000ff000f00ff0000ff00ff00ff00ff00ff000000ff000000ff00ff0000000000ff0000000000005500550011001100550055001100110055005500110011005500550011000055005500550055005500050055000500550055005500550055000500550000000000000000ff00000000000000ff00000000000000ff00ff00ff000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0000ff00ff00ff00ff000f000f000f000f00ff00ff00ff00ff000f000f000f000000000000ff00ff0000000000ff00000000000000ff00ff0000000000ff0000f000f000ff00ff00f000f000ff00f000f000f000ff00ff00f000f000ff00f000000000000000000000ff000000ff0000000000ff00ff0000000000000000ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00000f000f000f000f000f000f000f000f000f000f000f000f000f000f0000000033003300330033003300030033000300330033003300330033000300330000ff00ff00ff00ff000f000f000f000f00ff00ff00ff00ff000f000f0000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000000000
|0,4=>0xf000f000f000f000f000f000f000f000f000f000ff00ff00f000f000ff00f000000000ff00ff00000000000f000f0000000000ff00ff00000000000000000000ff000000ff0000000f0000000f000000ff000000ff0000000f0000000000000000000000000000ff000000ff0000000000000000000000ff00000000ff000000ff000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff0000000033000000330000003300000033000000330000003300000000000000000000ff000000ff000000ff000000ff000000ff000000ff00000000000000000000000033003300000000003300330000000000330033000000000033000000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00000000ff000f00ff000f00ff000f00ff000f00ff000f00ff000000ff000f00ff00000000000000000000ff00ff00ff00ff000000000000000000ff000000ff00000f000f00000000000f000f000f000f000f000f00000000000f000f000f0000ff00ff00ff00ff00ff00ff0000000000ff000000ff000000ff000000000000ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff0000
|0,5=>0xff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff00000000ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff00000000ff00ff0033003300ff00ff0033003300ff00ff0033003300ff00ff0033000000000000000000000000000000000000ff00ff00ff000000ff00ff00ff00000000000000000000ff00ff00ff0000000000000000000000ff00ff00ff00000f000f000f000f000f000f000f000f0000000000000000000f000f000f0000f000f000f000f000f0000000f0000000f000f000ff00ff00f0000000ff0000ff00ff00ff00ff00ff000f00ff000f00ff00ff00ff00ff00ff000f00ff0000ff00ff0000000000ff00ff0000000000ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff0000000000ff0000000000000000000000000000ff00ff00000000000000000000000000ff0000000000000000000000000000000000000000000000000000ff00ff00ff0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ff00ff00ff0000000000000000000000000000000000000000ff000000ff000000ff00000000ff000000ff000000ff000000ff000000ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000000000000000ff00ff0000000000ff0000
|0,6=>0xff00ff00ff00ff00ff00ff00f000f000ff00ff00ff00ff00ff00ff00f000f0ff00ff00ff00ff00ff00f000ff00f000ff00ff00ff00ff00ff00f000ff00f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000f000f000f00000ff000000ff000000ff000000ff000000ff000000ff000000f0000000f000000000000000000000000000000000ff00ff00ff00ff00ff000000ff00000000000000000000ff00ff00ff00ff000000000000000000ff00ff0000000000000000000000000f000f000f000f0000000000000000000f000f000000000000ff000000ff000000ff000000ff000000ff00000000000000ff00000000ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x200831118248070c14b08160400c1c401062214708160400a1a403181430b100400a8c084c581003071316188842008015181018b0c4450e262c0800a5818b0c4428e20188921438802005428d06080800a384020c446900e5028e26188921c2010100101820c444880e182840608080
|1=>0x18587101600a051c20106005c69b041800c08401010030688041888c1c4010100146901e00a052c0c58622344100e18284062c080145818b020028e26180122e5840b0c4460e102c311141098b0c4460d100808018101820c00b8e262c3110a341820c4428d2068c8a182440f0c00284
|2=>0x834802008860e20180124e1530d20083000a5818b0c002a51c4120600287131618017080c5860028b89201c30a185818b0c002971a40100441460d202d1a214310962018020183880b005450c1c403002428b8d262c3111834800287c50c3c40586007060d262c0800a305860074e0a
|3=>0x62c08014388020c002a51240786001469000c988a1834802005580c1a403005e2860e20083000a5d7162008300183418600b428a423498600b028d20a83000a58690040110c1a405a3342860d20083110a3158e20180120a5882a0c0060d102c080143108d20180200a348290c0028c
|4=>0x1834806466450c08d08020c0060d06083000a5c20d200801418588020c0128c1a0c82a0c002892c40300403069000c890a183480b008850c1cd08020c0028d20011331430690168ca0a18108020c0128c2c0c82a0c0060e1a401002814f0d161801d18108020c00b8c1a40323582860d
|5=>0x1450e262c3000a5c4bd16180051c4058622286900c0100518348070c147101604005143480b785050c2cd08020c0060d2019db1143048406083000ae880b0c0050c1a40323722861e1a403007030683041801d0a341b60c0028d262c3110a3068304180054a3480b0c002b52c40386
|6=>0x2c388020c006900c8c90a183480b0c002bf1af880600c46212c4150600306900400a3018586900c0100c1c205860028b8d2000a3314306900cec90a1834d8b0c0050c084c586005c616202c311181080b020050c42349860048296202c0800a30688161888a183898b0c002a51c41206
|7=>0xc00bc008348020c002101600a8a18344101e180052c405802a1460d262c080190080b0c00e0a425880600b02c01a4010600147101600a8514349830c01985123898600482a11a4150600146834818005143418b0c4450d061802d14306831604005145840b0c00b8c1a400225828640
|8=>0x1c201060014b10161888518588020c00e0c121010600746092c41506003068320180200a58690041918c1a40014582860e202c3110a28210041801c1904683041800508348020c8c60d20080800a30f0d2018031185880b005450c1a40106461460e200830038146900089c8a185818b
|9=>0x1a0c8020c002b01a0c58600145251a40586462860d20080150a306900c8d98a183480028e450c1a0c58622145212c4030024144c216180058078690161800908201060030693061802c0b0068b0c00e8a123482a0c002892c083003a30690008890a18344020c00b8c08405862228609
|10=>0x10c50c1a4c586005c6091ad058600286090840300242861e1a0c80b0c00296684058600286091c4c5860014690160400a18348060048e8a18846930c0160a18242031618005143480600e428a18a06900c01c8a183482a0c0050c565871016180051a0c586007428a1c349900c00905
|11=>0x1a4030070286211a40300722860d7c4030024286401a4c80b0c0028e264058600158211a4c18b0c002c01a0c80b0c005093c3498b0c0062e1a40300862860e1a4058044286041a403007228609203c300143020d260c586001448d202c02214315c01c405860028690481800a1834806
|12=>0x923070d262c3000b255961a0c586001508d201803114315a11a405860014683202c32314315c01a4058600146901600a0a6030683041800592348020c00297183480b005240a1900693062c3001484b0e202c3000a586900c01c8a183498b0c023854224b10161800513188020c00609
|13=>0x50e0a18341b60c0050c08348020c00e8c1a405802a2860d062c014152862b803418b0c00509084010600146411a403005a2860d20083003a1460d20d83000a3140d201801214320161c40586002868320a8300143200d1040586002869004180054a30216200830060306900c0198a
|14=>0x2c3880600482ab123880b0c0028d0640300581450d201c30a18246831600a0a1834410161918a1900690161800514a200d202c300143868820083000a35a100418005183880b0c005251884f16202c300183498316180056034990161918a18246900c0100a18acb0e2008300183480b
|15=>0xc0060d102c014152862b202c30038286091a4c300582860d202c02214306900400a0518ac690161918a181080600cc530190020d202c3001484f0d202c3000a2421620083001900b0d202c3000a3498b005054a1858690041801d18786900c0090a1825e8b0c0050c123880600c450c
|16=>0x2018038143048d102c0141430b100c0198a6030b101e1800c5610690041800c5040586007050c50348020c0028c123498b005050c1a40586461450c503480b0c8c50c8084690161800a1c40586007028a4224b10041800c4234986004850c1a4210b0c0028e684058600286041a20802
|17=>0xa349900c01985183418b0c00525192c693161800a18348240c0028a181080b0c00e0a183498b0c0029718acb0d0608300183480b0c4450c5010690041800c823418b0c0028a42246900418005083480b0c8c50c2c40586007028c123480600e450c1a40581001450c425880b0c0028d
|18=>0x28b891c4c30024286282c348020c006211a41506002860d20180319a28609084c58600146161a40586462862b123418b0c0028d262c3003a14621202c3003828609084030066286211a40586462860d20180333a2860d262c3000a9460d202c300149460d062c3003a2860d203c300
|19=>0xc0198a183498b0c00e8a183484f0c0050c1ad08020c0180c425880600b050c125880600cc50c1a4c586002928c1a205860028b8c1a0c80b008850c1a0c580282a48c1ad080b005450c123840b0c0028a1c40300622a70c2c40586007050c1210586007450c8024710161800a1c40586
|20=>0x563480600cc50c1a0c80600e050ca23418b0c0050c121040b0c0050c1278b10161800c125840b0c0028c3c34990161800c1a20586007450c8058690041800c1c40586009c28d104010600c060d102c30014946092c2c3003a2861e1a4c18b0c0060d20180201430b1016180171834410
|21=>0x1834410160110a183440b005054918344100400a0518a06900c0198a183480b005428a1904690041800518ac68b0c00e8a1834990160110a183480600b4549183498b00505491878b0e202c3001834806004a68a1878688202c30018ac710161800542581901618005423480600b028a
|22=>0xc02b0a2c348020c02a8c2c3880b0c002c9563480b008850c3c3480b0c0028c5078690161800c130480b0c0050c1a403005a2861e1c3480b0c002c0123418b0c0050d062c300145c6c520180311431096200830018a068b0c00e8a194c690161800518a0690161800a18acf0d202c300
|23=>0x4234586007450c1a0c806008050c1a40106007028c3c10690161800c1b6080600c450c1a40580441450c503480b008850ca8348020c0028c42348020c002a11c3498b0c0028d20180391430496062c3000a388020c002b08038690161800aae3880b0c0050c422469316180051c3480b
|24=>0xa286211a40580442860e202c30038286091a41506002860e1a40586462861e2c3480b0c00609202c30038286261a40300b42860d2164300242860d062c3006e1448d202c323143020d202c022143130d202c3000a282100418030182418b0c00e0a1858190161800560ac6831618005
|25=>0x1a0c8020c002ae2c40586002860d10403005828609262c30038286161a0c58600164892c40300582860d8a4c30024286091c40106001509e1a4c58600306d820180121431096064010600304c2161800a1858690160110a18588020c0180cb8588020c0060d260c300582860d202c311
|26=>0x1a0c8020c0028d0640300722860d264058601786411a4c586001460d202c01514c065d1a40580282860d2018012a028609102c30038286091a2010600146211a40300702865b1c40300242860e202c3000a28bc11a0c58600286091c2c3003a2862b1c4c80b0c002a12c403002428604
|27=>0x2928c1c3480b005028a2c40586001528c823498b0c0050c12581820c006281a403005828604202c300145c62b1a40580282860d20083008e14b1016180052e3108d20180120a287100c0090514c048420083001834806016850c563480600b050c1a41e8b0c0028e202c3000a292a1
|28=>0x202c0141430b10161800a4a3108d20180201430b0d202c0140a307100c00927143048d06083000a58690161806018344100c01c8a1834190161805f1438690041800592349900c01c8a1904688161800a188469316180051cd080b0c0028a503480b005050c0840300242980c0840586
|29=>0x1a40586462860d064030066145041a40106012462b1a4030072286091a2c3003a2860d201802d0a28616202c300c214f0d201802c143048e20180120a2958e20180121430234202c30014306831618005145cf0d20180201430b0e10405860014b34202c3000a3158d260c586001420d
|30=>0x1c40586002980c123440b0c0050c5058690161800a1810690041800c2c3419016180055084690161800a18349901618005603108e1a40586001452b2c3418b0c0050c1a201901600a0a18a020d202c30014310891a40586001452b423480b0c0050c1a40586017850c423480b005050c
|31=>0x18850c123480b0c005251884f0d202c300143108d064030058286402c3480b0c0050c4c3480b0c0050c1a2080b0c0053018587100c0090a18ac48e202c30014306b4202c30014c060d0640586007050c08586900c0198a18349900c0090a1834413202c01414310841a405860028604
|32=>0xc0198a18ac48d202c3000a32d8e202c3001430693202c30098286212c40586002860d1040586007050c1210710161800a18344101600a05143070d202c3003a2860d262c3000b246411a40586001450c1a4c80b0c00e0a18386900c00905143418b0c005491834842161800a1834806
|33=>0x2018012143108d202c3000a2970d202c3001430b0d06401060030710161800514c0690161805214306906c1800a183480f0c0050c1a4c586002a48c123480600b050c2c3480b0c02a8a18348020c0180c0834806004850c1a40586014050c1234403161800a188448d20083001430690
|34=>0x1970b10161800a183880b0c0138a18a070d202c300143258d202c30014314091a405860028604202c30014c06091a2098b0c0050c2c40586001580c8c348020c006091b90586002860d202c300381450c1a20586002a48ca83480b0c0028a18ac48d062c300143068820083000a3108d
|35=>0x16180521430690161800a4a3048d102c3000a2862b2c348020c0060e1a4c80b0c002841a0c80b0c0028a8024690161800a18106900418005183480b0c00517183419004180051238806004850c123880b0c0028a563880b0c0050c4258190161800a196c683161800a185880b0c00530
|36=>0x563480b0c0028c138c80b0c0050c125818b0c0050c1a40300624850c1c3480600c450c4224693161800a183480b0c02385143480b0c01385187870d202c3001430484202c3001430688062c30015246211a0c80b0c0028a125880b0c0028c1a40586007450c1278690161800a1834190
|37=>0xc019851430b0d202c3000b246511a40586002860d062c3006e2860d202c014143048d062c3000a2958d062c3001430688262c300152460e1a4058600145491a40586017c50c1a40300582860d202c3006e146211a4010600286042c348020c006211c3498b0c0050c1ad080b0c0050c
|38=>0x662860d20f458600286211a0c8020c0050c803480b0c0050c1c40586002980ca63480b0c0050c1a40586015850cb8348020c0050c1a4c18b0c002ab1c4c80b0c0050c083480600cc50c12388020c0050c1a0c80b0c0028a60a0690161800a18348020c002b01810690161800a9230690
|39=>0x1904690161800a9230683161800515246901618005145c62b1a4c80b0c0028c423498b0c0050c1a4030062286091a40106001460d0640580282860d8a4030024286098c40586002860d20083008e2861e1a40586002860d064030058286161c4058600150891a4030058286161a40300
|40=>0x18386932018012143020d2640586001460d104058028286411a4058600286571a405860028616202c300c22860d264058028286090840586001450c5634983161800a183480b0c00e85143069016180551430690161800514946042c40586002980c12341820c0050c5034190161800a
|41=>0x183480b0c0300a18246c4161800a1824b10041800cb83498b0c0050c2c3480b0c00e8a18a0688202c300143069016180610a28f0d064058600286091c4c586002860e1a2080b0c0028a1ad080b0c0028a18a0693202c30014315961c4058600286041a40586007450c5634410161800a
|42=>0x18a0690161800514315961a40586001460d262c3008e28621125880b0c0050c1a40106001648c1a40586007050c8034990161800a1810688202c3001430b0e20083001884693062c300143142b1a4058600286541a40586002860d202c0140a286161a2080b0c0028c1210b10161800a
|43=>0x2862b2c3480b0c0050c083480b0c0028a1834190161800514348020c0028c083480600cc28a18ae00d202c30014306900418065143070d202c300a02860e1a40106001448d262c3000a30690161804c14310961c40586002862b083480b0c0050c423480600b050c4234410161800a
|44=>0x1618005188448d202c3001432d8d202c300143020e1a40586002860d211058600286091a40586001450c5624690161800a183480b0c0308a1838693202c3001430683200830014306e720083001430690161800514c060d202c30015246042c3480b0c0050c2c348020c006091a4c586
|45=>0x2860d219810600286041a4058600286161a40586001460e1a40300242860e1a40586001450d202c3006e2862b1a40586002860d202c3000a2a48c1a40586009c50c2c3880b0c0050c1a2080b0c0050c125880b0c0050c1a4c18b0c0050cd0348020c0050c4238690161800a1834990
|46=>0x16180471430688202c3000a286161a0c80b0c0050c4234190161800a183480b0c005301970690161800a1834806004850c5634990161800a1838690041800a1824710161800a1824690041800a1834413202c30014306e4202c30014306e3202c3001430688064058600286211a40586
|47=>0x1a40586002860e1a4058600286091a4058600286161a40586002860d202c3000a2860d2640586002860d0640586002860d2008300143048d062c300143230d202c3001430690
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x794032a0145007a8029400aa0005
|5,0=>0x79303b181ccc0e0606d30351819ea0c96061b02f5816ec0b16055b0295813ec0996049b0235810ec081603db01d940e0c06a60323017980b0c0526026a811d8082c03b601ab00bd8052c0236
|6,0=>0x15338a7dc532c2927145b8a11c4fea2787138b89a9c4c6e25c712ab8939c48ee240711cb88c9c456e224710eb8859c41ee2087100b87ed83e8e1ee60f3b8781c3b2e1d270e5b8711c37ae1b760d8386a5c344e19b70cab0639c30ee18070bcb85c9c2d6e16470af3056182a2e14b60a2384f5c26ce12f709438485c236c1147086b8419c1fee0f87
|6,1=>0x22f3915dc8a0e4497221390edc868e42d72133907dc830e41172053900dc7fac3f671f7b8fa1c7c2e3db61ea38f35c78ce3bf71dc38ec5c754e3a371ceb0e59c71ee38871c0b8de9c6e6e36c71b2b8d79c6aee35071a4b8d09c676e3347196b8c9d8640e319718938c2dc608e2fd717b38bc185d4c2e3716f28b5dc5a0e2c9716138aedc568e2ad7
|6,2=>0x274b9389c9b6e4d47266b9319c980c4b97259392adc948e49d724b3923dc910e481723d391cdc8d8e4657
|7,0=>0x36ec1b560d9b06c5835ec1ad9cd5d06a6834f41a5a0d1d0686833f419da0cdd0666832f4195a0c9d0646831fb98de0c5f0627830fc185e0c20e6088300b97e60be305e982f0c17660ba305c982e0c16e60b6305a982d13966a0b25058a82c1b95f1caeae56d82b2c15760aab054e72a3b94fe0a6f052f8293c147e0a30e51082844140209f104f08
|7,1=>0x467c231e1180e8b88458422a2114108988448422221102e87a7439421aa10c8c85c842a421321089083c841a420b21049081c840a42035d00b07fd83fac1fb60fcb07de73ebb9f3e0f8f07bf83dbc1ebe0f4f079f83cbc1e3e0f10e78083bcb9dc60ed3076363adc1d4e0e970743839dc1cce0e570723838dc1c4e0e170703837dc1bd1cdd906e57
|7,2=>0x563c2afe156f0aaf8553c2a7e152f0a90754442a0214f10a7085344298214b10a5085244290214710a317514c288614330a1185053a80dd3f709f384f63a79213b909d484e642712137909b484d6426921339099484c64261212fae97584b6c259612bb095584a6c2516127b09358496c2496123b09158486c241611fec8f78477c239e11bf08d78
|7,3=>0x65d432ca19550ca3764dc3251d91aec85863ec31d618db0c65862ec3156189b0c45861ec30d9d85d0c26860f4305dd81f0c0786003afe217e10be885f042f6217a10bc885e042ee5d7630baa75d1bae71d7290b8c85c242df216e90b6c85b242d7216a90b4c85a2bacf6166b0b2e759342c7dd62f0b0f8583c2bfe15ef0aef8573c2b7e15af0acf8
|7,4=>0x75943aaa1d450e9a874943a2a1d050e7a8739439aa1cc50e5a8729bb92e1c870e3b8719c38ae1c470e1c770a438321c090dfc86fa437b21bc90ddd76eac37361b8b0dbe76db436ba1b4d0d9f76cc3b6421b12ed8186bcc35c61ad30d6186acc35461a930d41869cc34c61a530d21868cc34461a130d01867cc33c619d30ce1866cc334619930cc27
|7,5=>0x1e010ef97778c3ba61dc30ed98768c3b29dd850eba8
|8,0=>0x88e4444e62153102887d443ca21d510e2886d4434a2196f0c4785e442d2215730a4784e4425221173082983dbc1ca60d51061982cc4142608f303e981acc0b62049301b9809c402e20070ffc77f9cbfaa5fc32fd897e843f1e5f7f0fb697d6cbe925f372f9387c54be065ef12f7087b3cbd81deb10f4f97a34bcf65e692f2b97914bc665e212f088
|8,1=>0x99644c92263733138985c4c0a65f512f19974c4b8625b4f2d2896544b06657132b08954bca862533129189444ca0224f1127089344498224b1124f9923c48fe246d322e8912cc8726429120c8901cc7ea63e511e998f0c476623a131c798dfc46de2360f1a888d044662231f318788bfc45de22df116698af44556629b1144989e444d5e25b11249
|8,2=>0xaa1cd4ea6a66f52a9a90cd4662a2315089a7fcd3de29df14e87a704535e699d34c68a5ecd2d6295934a39a4d4d2466911347f9a3b4d1b668cb145d8a2ac5136288b143c9a19cd0aa684514199a084d02227ff33f699f744f9667b933d489e6bcf16277b13b589d6c4e96273b139589c73ce1666fb137589b64cd9226b9135489a644d12267af3349
|8,3=>0x15d39ae54d70a2b7335b27ad54568a2b3335909ac4455fe6aed356d9ab2c55726aa9154c8
|9,0=>0x178a8bc145dea2ee337689bafcdd5e2e9f17487b9fcdcde2e5f17278b8f4dc5a2e1d17059b7ec5bd62ddb16e58b6ec5b562d9b16c58b5e4dad22d5916a48b4e45a522d1916839b3dc59ca6cd516619b2cc59426c8f363f8b1b4d8ba2c4d161d9b0ac58326c0af5fd8afa4d7ae6bc715dc7
|10,0=>0x5f062f7317b18bd4c5e862f3317927
|11,0=>0x17c97
|_,_=>0
def wAt:=mkWire dB 105 248 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x121414311a311a411e011c081a3116291a4112311a411c2f12141a412029005d12141a4114310c5d202912141431101b1a3120151431005d1a2912141a4120311431201514311e011c081a311629201514311c081a3116291a411e0114311c081a3116291a41005d2029121414311a311a411a41201514311e011c081a311629
|1=>0x1431101b1a152015143142081a291a0d16291629121414310c5d12141a412031143114311c081a3116291a411214143116291a412c0e20312016422f1a0d2031143142081a0d203116292c411c2f1a2942081c411a291a3116290c5d201512141a4112311a41501b08411a15143112171a4114311a31165d12141a4114312029
|2=>0x1a151431202912142031005d12141a4114310c5d1214203114311a29005d12141a4114311c2f1c411a31005d201512141a41143112141a4114311c4c1a3120291a31005d12141a41143114311e011c081a3116291a1516291a412031143116dd143120311a4e2029005d2029121414311a291e011c081a311629162912141a41
|3=>0x1a2914311a411a15162920151431422f1a0d203114311431420816291231162912141431005d12141a411a151a4116291a31201514311a29005d121414311a4108431a151431005d121414311a312016500308411a1514311a2912141a41203114311c0816291a312015143120290c5d12141a411431422f12311a412031082f
|4=>0x1a411431209512161a4114311c2f1c291a311a41422b1a0d2031202914311a311a410c5d12141a411431422f12311a411a151a4120311431502f1a212015502f422912311a4142081a0d203116291a312c411a29143108431a151431202920311a161629143112161a411431005d1214203114311c411c2f1a311a412c0c2031
|5=>0x12311a411a412c3316291a295829422f1231422912311a418a2b1c2f1a3156331a4d202920291a1614311a0d2031202950331a210629203112311a411b11062b2031501b1c4d1a31202908411a1514311c081a3116291a41203120291a151431501b4229123156331a4d2029165d12141a4114315c2f1b11062b203120291214
|6=>0x202956332c411a2942081a0d1629263156331a4d2029162912161a41143108372c3116291a2920161a3120312c411a291c4124291c2f1a311229143112311a4150031a21062956332c411a292031201616291431162912141a411431101b2015143156331a4d20291c411a311a291431502f56312c411a0e2029203114311431
|7=>0x2015143120c11a161629143112121c291a311a41422b12311a411a16202920311431500356311a4d3c2f422b12312c411a291a31162916dd20311a4e2029162908431a151431681b20c11a1614312052101b0629203156331a4d202916291a411a1514311b2520161431162908431a15143116dd14311a4e20291c2f1c4d1a31
|8=>0x1a151431422b12311a411a412c3116291a2956332c411a292052101b2631202916292c311a291c2f422b1c411a311a411c4c1a3120291a4124291c2f1a311c2f1a311a291431122914311a41422f1a0d203114311e011c081a311629101b1a410629203150031a212015143150331a21201514315033422912311a4116291a31
|9=>0x12311a411215143116291a411a41101b2631202950031a2120155003422912311a415033422912311a411a222015143116291a291a411c2f1c411a312c0c20311a2914311a151629201514312052101b20151431503756312c411a292029422f12311a41501b422912311a411629101b20151431082f1a161a15143150330841
|10=>0x8411a151431202912141a411431203116292c411a29005d12141a411431162908411a15143120161629143112311a41500308411a1514311a2220151431502f422912310c5d12141a41143114311a2912311a415829422f12311a411a41101b20151431082f08372c311a291c081a291a3116292c3116292c411a2950374229
|11=>0x1a411a3120291a41563116292c411a29203124291c2f1a3120291a411a151431500356312c4112291a41143108431a1514311a0d1a2206292031082f2c311a411a295003422912311a4112161a41143150431a210629203114311c081a311629082f20291a15143120721a220629203121311c4f1a312029165d12141a415037
|12=>0x1a4114312015082f1a151431504356311a4d202917411c4e1a31202920c11a1616291431422f12311a411a41082f2c311a2912221a4126312029201512141a411431501b1a210629101b10430629203120c11a1614311a411a31201514311ac624291c2f1a31503756312c411a291a4108431a15143112291a41121414311a31
|13=>0x422b1a0d2031122914311a311a411a291a0d2031422f12311a415829422f1a0d21492c0f20311a2920151a411a15143112311a411a4120151a291431502b56311a4d2029201508431a151431563316292c411a291a312c431a29143116291a16201514312015121614312c311a29422b1a0d20313c2f422b12311a411a291214
|14=>0x24291c2f1a311c411a291a3116295043422912311a41a82912171a4114311d411c4e1a312029502b56312c411a291a21201514311043101b201514311629101b20151431082f08411a151431681b20c11a1614311b252016162914312c4108432c311a29501b56311a4d101b104326312029422b1c411a3124291c2f1a310629
|15=>0x143116291a411c4114311a312029502f422912311a411a291a412031143116291a311a16143150331c4d1a3120291b411c4e1a312029143112311a41a0311c4e1a31202920161a311a291431502b1a2120151431502b422912311a411a9512161a411431822f1b2520161431422b1c411a3112291a4112141a41203114312049
|16=>0x56312c411a295037422912311a41b631122b1a41143120311a4e2029500342291231501b08411a151431a83112171a4114311ac11a1616291431062920311a16203112291a41203114315043422912311a413c2f422b1a0d1a22162920151431422b1c411c291a3120c524291c2f1a31501b1a212015501b422912311a411231
|17=>0x1a292016422f1a2912311a4120491c2f1a31202914311a3116291a41422b12311a4120c524291c2f1a311a291a0d203116292c0c20311a411a29501b56312c4108372c3116291a291a29123316291a41422f1a0d20312029005d12141a411431501b422912311a4150371c4d1a31202942081629123150031c4d1a312029502b
|18=>0x1c4c1a312029121614311a41143120311629502f1a21062998291c4f1a31202920161a51101b201514311a411a22201514312015143116291a415829422f12311a41122b1c2f1a41121414311a311a4108431c291a311a411a311a4d20291c411c2f1a31203116291a1514311b552c0e20311a290629422f1a0d203126312029
|19=>0x201616291431502f56311a4d1a0d2029203114311a161a21101b201514311c2f08371c291a3112161a151431101b1a312015143112161a41143120311a2916291a41422f422912311a4112141a411a15143116291a0e203114311a2912141a4114311c2f1c411a311c2f1a1614311c291a3116291a414c2fb631122b1a411431
|20=>0x5043422912311a41822f1b2520161c431a311a291431422b12311a411c2f1a4d202912141a4120311431422b12311a411a291a31201514311a161a4d2029203114311a15101b201514311a7608432c311a2912311a411a29101b2015143116291a4120311431aa292c0e20311a29502f1a2120151431a4312c0f20311a291a31
|21=>0x101b263120291c411c291a3108371c291a31263120291a4156312c411a291c291a31162920311a291431422912311a4120291a1614311c411a31143120312c411a29101b0629203108411a151431143112311a41122912311a41c2291c431a311a0d101b062920315003422912311a412031082f1a151431162920161a151431
|22=>0x1a311a41101b2015143108431c291a312029201614311b25201614311a22263120291c2f1a3114311043062920312c0c20311a29c62f1c2b1a3112161431422b12311a41422f1a0d203156332c411a29b631122b1a411a16201514311c2f1a311a2912291a311a4120c11a1614311a2206292031082f2c311a291c2f1a312029
|23=>0x1c2f1a31143112311a411b11062b20311a29203116291a311a1614312c0f20311a2916dd1a4e20291c081a311629104326312029422f12311a412c0e20311a16162914311c2f1c291a311c4e1a3120291a4106292031162912311a41082f1a151431143112291a411a31122b1a411c4f1a311a2912311a411a22201514311c29
|24=>0x16291c2f1a311a4114311a311a411a4d1a3120291a0d20311a292031122b1a4108372c311a291a2912331a412c431a311a291c4d1a312029c6411c2b1a31422912311a411a161a1514311a41263120291a161a2914312c3316291a291a41263320291a222015143120162015143112171a41203112291a411629201514311c41
|25=>0x24291c2f1a3124291c2f1a31202912311a411a0e203114312c431a291431422b1c411a312c311a411a291043062920311a0d203114311a411a29143108431a151431422b12311a412c0f1a291b26201614311a412015143116292c411a2914311a3120291a1520311431563312291a4116291a15143112141a41143114312031
|26=>0x1a411a161629143120161a151431082f1a15143120161a2914318c412c331a2920311a4e2029101b201514311a41203114311a4d203120291043263120291a31201614314e312c431a29422f12311a4114311a4e20291a0d203116292c3116291a291c411a31202920c11a1614312c411a2914311a411c2b1a3120311a411a29
|27=>0x629203120491c2f1a312c331a411a291a0e20311629422b12311a41422f1a0d20311a311a291431422f12311a41082f2c311a291c4c1a3120291a0d2031162956332c411a2908371c291a31b82912331a416e311a4e2029123316291a412029203114311a311a4d2029082f1a1514311a3116291a411a162031143142291231
|28=>0x20291a151431101b201514311b25201614311b91263320291a291c431a31101b263120291a411a15143120311a4d202908431a1514312c0e20311a2912161a41143108372c311a291a41203116291a21062920311b252016143120162031143112141a41143114311a4d2029202912311a4124291c2f1a31143116291a41101b
|29=>0x202956312c411a2912171a411431101b2015143120151a2914312c311a411a298e291a0e20311a41062b20311a2916291a41202912331a4108432c311a291a212015143114311c431a31422b1a0d20311a3120291a411a312015143120c11a16143156311a4d20291a312c411a2908431a15143126311a4d20291c2f1a312029
|30=>0x16291431082f1a15143156332c411a29219a043116291c4e1a31202914311a311629143120291a411c4f1a3120291c411a311a292c312c411a29422f12311a411a0d062920311a21201514312c411a2914311a0e203120291a2912311a412016162914311a222015143156331a4d20291a15201514311a291a3116291a0d2031
|31=>0x1a2914311c2f1a311a3114311a4e20292c411a29201614312c431a291a311a29201514311a411a29203120291a0916291c411a312029143112311a41122b1a411c291a31062b20311a41143112291a411c431a311a31202920311629200916291a161431201614312c311a2916291a2920291a412c411a291a15143120311431
|32=>0x1a311a411a29143120292031162920311a412c331a291a0e20312015143120311a291a0d20311a16143112331a411c2f1a311a4d20291a3116291a311a4116291a4126312029263320291c2b1a310629203112311a41043116291a151431
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x70000
|5,0=>0x1f60196000000000000000000000000000000000000000000000136000000d600000000000000000000000000760000000000000000000000000000
|6,0=>0x8c508840000000008350000000007f407b40000000000000000000000000000000000000774000000000743000006f5000006a5000000000000066406420631060305b50000000000000583053504f404d200000494000004720461041503c50000037500000000000003520000032302d500000000029400000254
|6,1=>0xd9400000d810d440000000000000000000000000cf5000000000ca500000c5500000c23000000000be40bd100000bc10b7500000b34000000000000000000000000000000000000000000000000000000000ae500000ab300000a740a610a5100000a0509b5000009650000000000000000091500000000
|6,2=>0x106410330fe500000f950f5400000f14000000000ee30ea40e550e1400000dd4
|7,0=>0x1d541d231ce41cb31c741c341bf41bc31b931b541b141ad400001ab21a831a441a0419d319a300001964192418f318c318841853181417e317a417731743171316e316c216841644162215f315b415831544150414d314a31464142413e413a413641333000012f412b4000012831244121311d4119411541123111110d410a3
|7,1=>0x2b942b542b142ad42ac12a842a442a1329e329a42964292428e428a42864282427e427a42764273326f426b426832653262325e4000025a42564252424e424a424640000242423e423b323742343230422d322942254221421d421a32164212420e420a4206420241fe41fa41f641f331ef41ec31e931e5400001e141dd41d94
|7,2=>0x38e438b3000038743843381337d43794376337330000370336c436843662362435e435a43564352434e434b334923463342433e433a43364332432e432b33274323431f431c331843153311430d43094305430322ff42fc32f842f712f432f042ed32ea32e732e342df42db400002d8300002d442d042cc42c842c442c132bd4
|7,3=>0x46f346b446744634460345c445844544450444c444844453441443d4439443630000432442f342b442744234421241f241b441744143410440c440844053401400003fd43f943f543f143ed43e943e543e233de400003da400003d643d243ce43ca43c733c523c143bd43b943b543b143ad43a943a633a2439e439a439643924
|7,4=>0x52f3000052b452835244523151f451b4517451525114000050d45094505450144fd44fa300004f644f514f144ed44ea34e644e3300004df44db44d7400004d344cf44cc34c934c544c1400004bd44ba34b734b434b044af100004ab400004a744a3449f449c3498400004944491348e348a448644824480247e247a447644724
|7,5=>0x54c4548454445404000053c45393535453230000
|8,0=>0x60936072604360135fe35fb35f835f535f235ef35ec35e935e635e335e125de35db35d835d535d235cf35cc35c935c725c435c135be35bb35b835b535b235af35ac35a935a635a335a1259e359b359835953592358f358c3589358635833580357d357a357735743571356e356b356835653562355f355c35593556355335503
|8,1=>0x6c836c536c236bf36bc36b936b636b336b036ad36aa36a736a436a1369e369b369836953692368f368c3689368636833680367d367a367736743671366e366b366836653662365f365c365a265736543651364e364b364836453642363f363c3639363636333630362d362a362736243621361e361b361836153612360f360c3
|8,2=>0x78837853782377f377c3779377637733770376d376a376737643761375e375b375837553752374f374c3749374637433740373d373a373737343731372e372b372837253722371f371c3719371637133710370d370a37073704370136fe36fb36f836f536f236ef36ec36e936e636e336e036dd36da36d736d436d136ce36cb3
|8,3=>0x7bb37b837b537b237af37ac37a937a637a337a0379d379a379737943791378e378b3
|9,0=>0x826282428222820281e281c281a28182816281428122810280e280c280a2808280628042802280027fe27fc27fa27f827f627f427f227f027ee27ec27ea27e827e627e427e227e027de27dc27da27d827d627d427d227d027ce27cc27ca27c827c627c427c227c027be2
|10,0=>0x82e182d182c182b182a182918281
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 16
def pmP:Nat→Nat
|0=>0x2ae000004000000068000000c700000186000003000000048000000810000010000000188000002b00000053000000a200000140000002380000045000000880000010c00000200000001e0000002c000000480000008800000100000000e000000180000002800000040000000600000008000000080000000
|1=>0x10880000210c000040b0000081400001022000020400000402000008000000080a0000100c0000200000003800000068600000c00000016a0000028400000500000009c8000013300000256000004a8000009440000121800002420000048200000900000010a000002110000042000000810000010080000200
|2=>0x240800004800000088a000010540000208e00004110000082000001004000020000000395c000072a80000c57000016ae00002c50000054880000a76000014ae00002954000052880000a440000143c0000285c000050a80000a140000142200002814000050200000a0000001200000021c8000043300000854
|3=>0x422860008391c00105ab80020b55000416280008295c001048000020802000410000008080400100698002001600040028000800480010008000200060004000a00080000000f00f00010a1f000118ae00006d5c0000d6b80001a57000034a6000066000000c2200001810000030000000501000009aa00001300
|4=>0x403488008061500100c28802018500040308800806104010096880201254004024a000804850010082a002010110040200200802d5c01005aa80200b14004014ae008024000100400002002010040008e008001100100002002000000010000000104804002010000040003000436ae00086b5c0010d2b80021817
|5=>0x200232804004550080084801000b57020014ae04000f50080018001000280020004040400014c0800009010000100200000a04000000040000000714a0e00c410080180395c01107ab80220b570044168800882c50011058800220b04004414280088254c01104a3802209140044100000806b5c0100d6200201a57
|6=>0x24014ae0480095c090008181021257020414ae04082848081040b010208070204100c04080858081010a010202070204040c04080008081000081001bd70200378804006d5c0800da801001b4402003608040069500800cc2010019440200300804004f5008009aa010013530200268e04004c50080092001001200
|7=>0x8481eae10807b5c2100f2b84201c57084034ae1080694c2100c2b8420184008401cae1080341c210062b84200c17084012ae10007f5c2000fc384001c17080034ae1000694c2000d0b8400195708001eae1000395c20005eb84000ad7080014ae1000285c2000100840002000800000008000104091042b81200b57
|8=>0x104034ae2080690c4100c2188201254104014a62020395c402072b88020a471004140e200208504000d2988001853100025a62000295c400050a0800080710001000200008504000100080001501000020c200001404000003052004170a08362e14007f5c2800deb850016970a001eae1400395c280060b85000ad7
|9=>0x19010395f024072bc4081ed788003daf0410395e080072bc0000e5749001cae9000395d200052b94000a572000142e4000000c6100f2b8c080e5712041cae2408295c4810521890202161200148e2400091c414050988241004
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x400
|5,0=>0x2c060000000000000000000000000020003000000000000000b0000000000000000
|6,0=>0x2000ae0d000000000000003e0000018003b0008000001115c0017170001000000000000000000000000000000001040020000803c17001d85a003680000000003c0000000000208000016000000e41a00000000000000000000020000008000a8005400000003a4395c40370000000381b8806a0006801621e4307c004b0000000350018c8400000200023
|6,1=>0x408118000a888000400000082005010000d
|7,0=>0x12a8ca01c2bb1c1a710209586e5052515c3f0086c46200700568664292800156900446273f00126016026ceeb702214f86533a38606c1d00842013a1d072322401008af001281e4d3c10d140d44cae544302004449a00435468522811460088128104363065c2607a0101a0446c3d8a0510034241a2b26008432491cfa0731178007f27000405a17838aaaa2c15e1c43
|7,1=>0x1900cba9104485ec44128341204090240a0d00370080d10c74110d5300408730c01c400e0041182276ec5012095c8240048000840210232e070bc113c402210d80404d138210472000810006f1a01002a5600bc000402854407202804e6de03020083228a480405108185e5f1188808b3012d5f009078e0d4590db8c088a041e512012d034003200014d6391d0145e01
|7,2=>0x1a282fc2800052f2001a571c000780d6b1b9540d110d474008082404058b01000c4593892604118c800f31b08c010812978c8f91200094435e8100a880004c000a39098703c0003d465e4a8240408878c1c8f0
|8,0=>0x7dbca224f8d431df1147b6c9ebc56362228f742060cfd62c49586a704b5f6cd6fb7d74a06a315244f6501224d656a0530a79494e64ec352b184bc8da49be75348463cda8dbd4fad592881532783b3976f78aa3e58568c3a411287e9e9b4c9742a0d4046702d42d315c5e383c774889eed023157c7b29c2df4ab8489538e66b8c532db5b3f1be2988b1948d308b2c9869
|8,1=>0x97554b83b343e9a19e40828b066a46db32324f48055fccd1f14db6d94faed78ff3e8f0288230a0dad242daa01e3d2e279b7123d209b69854a5976524ec0d170a9193d48ce73ba9b72d494089f0050321f64f5f93e26533d3adb6a4
|9,0=>0xbc47aee4cdf67448a6e7564ccd4eb6d9e8d0db674bd408f779a0f4ac8923d40db4936e6ad03d338a6a25d94d586940cc66d1289281ee7d5647d7730
|10,0=>0x1a0a68f279e97656
|11,0=>0x4f
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 31 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_246 10 roots_246 ops++addP pm 1 dom_245 10 roots_245 ops++addP pm 2 dom_231 9 roots_231 ops++addP pm 3 dom_146 4 roots_146 ops++addP pm 4 dom_215 9 roots_215 ops++addP pm 5 dom_198 5 roots_198 ops++addP pm 6 dom_243 10 roots_243 ops++addP pm 7 dzo_83_4 5 roots_83 ops++addP pm 8 dom_199 6 roots_199 ops++addP pm 9 dom_183 9 roots_183 ops++addP pm 10 dom_179 7 roots_179 ops++addP pm 11 dom_119 9 roots_119 ops++addP pm 12 dom_83 5 roots_83 ops++addP pm 13 dom_214 8 roots_214 ops++addP pm 14 dom_242 8 roots_242 ops++addP pm 15 dom_51 4 roots_51 ops++addP pm 16 dom_178 5 roots_178 ops++addP pm 17 dom_167 6 roots_167 ops++addP pm 18 dom_227 8 roots_227 ops++addP pm 19 dom_211 8 roots_211 ops++addP pm 20 dom_210 7 roots_210 ops++addP pm 21 dom_151 6 roots_151 ops++addP pm 22 dom_147 5 roots_147 ops++addP pm 23 dom_115 7 roots_115 ops++addP pm 24 dom_103 6 roots_103 ops++addP pm 25 dom_213 8 roots_213 ops++addP pm 26 dzo_211_4 6 roots_211 ops++addP pm 27 dom_55 5 roots_55 ops++addP pm 28 dom_163 5 roots_163 ops++addP pm 29 dzo_243_4 7 roots_243 ops++addP pm 30 dzo_115_4 6 roots_115 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_247 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_83_4_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_211_4_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_243_4_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_115_4_83 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_246 10 s (0,roots_246.map (·&&&dom_246)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_247 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_246 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_247 gM v ys):RunD true dom_247 gM v (ori ys):=h
def Z (s:Nat):=barP dom_247 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 36 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 148 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 20 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 148 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 330 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 74 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 330 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 209 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 81 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 209 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 53 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 53 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 7 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_247 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_251:Lower true dom_251 roots_251 goal_251 12:=lower_slice_b [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,1,33)] (by decide +kernel) lowS_219
namespace S_253
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(4,36),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,24),(8,40),(8,72),(8,136),(12,13),(12,28),(12,44),(12,76),(12,140),(16,17),(16,24),(16,80),(16,144),(20,21),(20,28),(20,52),(20,84),(20,148),(32,33),(32,36),(32,40),(32,96),(32,160),(48,49),(48,52),(48,56),(48,112),(48,176),(64,65),(64,72),(64,80),(64,96),(64,192),(68,69),(68,76),(68,84),(68,100),(68,196),(128,129),(128,132),(128,136),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffffffffffff
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
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_189 10 roots_189 ops++addP pm 2 dom_249 10 roots_249 ops++addP pm 3 dom_245 10 roots_245 ops++addP pm 4 dom_237 10 roots_237 ops++addP pm 5 dom_221 10 roots_221 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_221 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
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
def isoMvS_254:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_247
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,18),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,36),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,24),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,28),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,17),(16,18),(16,24),(16,80),(16,144),(20,21),(20,22),(20,28),(20,52),(20,84),(20,148),(32,33),(32,36),(32,40),(32,96),(32,160),(34,35),(34,38),(34,42),(34,50),(34,98),(34,162),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,72),(64,80),(64,96),(64,192),(68,69),(68,70),(68,76),(68,84),(68,100),(68,196),(128,129),(128,130),(128,132),(128,136),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|12=>1
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|12,0=>0x9892d
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x86543210876543210
|_=>0
def sO:Nat→Nat→Nat
|12,0=>9
|13,0=>0x98
|_,_=>0
def wAt:=mkWire dB 9 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x181
|_=>0
def oO:Nat→Nat→Nat
|12,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0xff00
|_=>0
def pmB:Nat→Nat→Nat
|12,0=>1
|13,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_191 12 roots_191 ops++addP pm 2 dom_253 12 roots_253 ops++addP pm 3 dom_251 12 roots_251 ops++addP pm 4 dom_247 12 roots_247 ops++addP pm 5 dom_239 11 roots_239 ops++addP pm 6 dom_127 11 roots_127 ops++addP pm 7 dom_223 12 roots_223 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_223 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 1 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 1 0 = true)
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
  · simp [NN] at hi
  · simp [NN] at hi
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [6, 7] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.or, inputs := [7, 5] }, { op := GateOp.or, inputs := [6, 2] }, { op := GateOp.or, inputs := [9, 3] }, { op := GateOp.or, inputs := [8, 0] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [4, 8] }, { op := GateOp.and, inputs := [11, 10] }, { op := GateOp.and, inputs := [12, 13] }, { op := GateOp.and, inputs := [15, 14] }, { op := GateOp.and, inputs := [3, 9] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52852_aux

theorem PEqualNP.Outside.L_meta_52852 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52852_aux.main
