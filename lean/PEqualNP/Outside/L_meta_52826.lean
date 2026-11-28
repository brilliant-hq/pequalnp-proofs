import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52826_aux
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
def dom_21 : Nat := 0x330033
def goal_21 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_21 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_23 : Nat := 0xff00ff
def goal_23 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_23 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfefaeca0fefaeca0fefaeca0fefaeca0fefaeca0fefaeca0fefaeca0fefaeca0
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_39 : Nat := 0xff000000ff
def goal_39 : Nat := 0xeeeeeeeea0a0a0a0eeeeeeeea0a0a0a0eeeeeeeea0a0a0a0eeeeeeeea0a0a0a0
def roots_39 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_42 : Nat := 0x50500000505
def goal_42 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00
def roots_42 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xffeeffeecc00cc00ffeeffeecc00cc00ffeeffeecc00cc00ffeeffeecc00cc00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xffaaffaaa0a0a0a0ffaaffaaa0a0a0a0ffaaffaaa0a0a0a0ffaaffaaa0a0a0a0
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xffeeffeeeca0eca0ffeeffeeeca0eca0ffeeffeeeca0eca0ffeeffeeeca0eca0
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafaaaaafafaa0a0fafaaaaafafaa0a0fafaaaaafafaa0a0fafaaaaafafaa0a0
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefeeeeefafaa0a0fefeeeeefafaa0a0fefeeeeefafaa0a0fefeeeeefafaa0a0
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffeeeeaacc00ffeeffeeeeaacc00ffeeffeeeeaacc00ffeeffeeeeaacc00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffaffaafafaa0a0fffaffaafafaa0a0fffaffaafafaa0a0fffaffaafafaa0a0
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffeffeefefaeca0fffeffeefefaeca0fffeffeefefaeca0fffeffeefefaeca0
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_71 : Nat := 0xff00000000000000ff
def goal_71 : Nat := 0xeeeeeeeeeeeeeeeea0a0a0a0a0a0a0a0eeeeeeeeeeeeeeeea0a0a0a0a0a0a0a0
def roots_71 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0]

def dom_74 : Nat := 0x5050000000000000505
def goal_74 : Nat := 0xffccffccffccffcccc00cc00cc00cc00ffccffccffccffcccc00cc00cc00cc00
def roots_74 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffeeffeeffeeffeecc00cc00cc00cc00ffeeffeeffeeffeecc00cc00cc00cc00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xffaaffaaffaaffaaa0a0a0a0a0a0a0a0ffaaffaaffaaffaaa0a0a0a0a0a0a0a0
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xffeeffeeffeeffeeeca0eca0eca0eca0ffeeffeeffeeffeeeca0eca0eca0eca0
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfafaaaaafafaaaaafafaa0a0fafaa0a0fafaaaaafafaaaaafafaa0a0fafaa0a0
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfefeeeeefefeeeeefafaa0a0fafaa0a0fefeeeeefefeeeeefafaa0a0fafaa0a0
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffeffeefffeffeefefaeca0fefaeca0fffeffeefffeffeefefaeca0fefaeca0
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_97 : Nat := 0x3000000030000000300000003
def goal_97 : Nat := 0xffffffffaaaaaaaaaaaaaaaa00000000ffffffffaaaaaaaaaaaaaaaa00000000
def roots_97 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_98 : Nat := 0x5000000050000000500000005
def goal_98 : Nat := 0xffffffffcccccccccccccccc00000000ffffffffcccccccccccccccc00000000
def roots_98 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xffffffffeeeeeeeeeeeeeeee00000000ffffffffeeeeeeeeeeeeeeee00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xffffffffaaaaaaaaaaaaaaaaa0a0a0a0ffffffffaaaaaaaaaaaaaaaaa0a0a0a0
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xffffffffcccccccccccccccc00000000ffffffffcccccccccccccccc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xffffffffeeeeeeeeeeeeeeeea0a0a0a0ffffffffeeeeeeeeeeeeeeeea0a0a0a0
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_104 : Nat := 0x101000001010000010100000101
def goal_104 : Nat := 0xffffffffff00ff00ff00ff0000000000ffffffffff00ff00ff00ff0000000000
def roots_104 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffffaaffaaffaaffaa00000000ffffffffffaaffaaffaaffaa00000000
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffffccffccffccffcccc00cc00ffffffffffccffccffccffcccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffffeeffeeffeeffeecc00cc00ffffffffffeeffeeffeeffeecc00cc00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xffffffffffaaffaaffaaffaaa0a0a0a0ffffffffffaaffaaffaaffaaa0a0a0a0
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xffffffffffccffccffccffcccc00cc00ffffffffffccffccffccffcccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xffffffffffeeffeeffeeffeeeca0eca0ffffffffffeeffeeffeeffeeeca0eca0
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffffffaaaaaaaaaaaaaaaaaaaa0000ffffffffaaaaaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffcccccccccccccccc00000000ffffffffcccccccccccccccc00000000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffeeeeeeeeeeeeeeeeaaaa0000ffffffffeeeeeeeeeeeeeeeeaaaa0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffafaaaaafafaaaaafafaa0a0fffffffffafaaaaafafaaaaafafaa0a0
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffcfcccccfcfcccccf0f00000fffffffffcfcccccfcfcccccf0f00000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffefeeeeefefeeeeefafaa0a0fffffffffefeeeeefefeeeeefafaa0a0
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffccffccffccffcccc00cc00ffffffffffccffccffccffcccc00cc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffeeffeeffeeffeeeeaacc00ffffffffffeeffeeffeeffeeeeaacc00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffaffaafffaffaafafaa0a0fffffffffffaffaafffaffaafafaa0a0
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffcffccfffcffccfcf0cc00fffffffffffcffccfffcffccfcf0cc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffeffeefffeffeefefaeca0fffffffffffeffeefffeffeefefaeca0
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_135 : Nat := 0xff000000000000000000000000000000ff
def goal_135 : Nat := 0xfefefefefefefefefefefefefefefefea0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def roots_135 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 7 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeecc00cc00cc00cc00cc00cc00cc00cc00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_142 : Nat := 0x555500000000000000000000000000005555
def goal_142 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffccc00cc00cc00cc00cc00cc00cc00cc00
def roots_142 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffefffefffefffefffefffefffefffeeca0eca0eca0eca0eca0eca0eca0eca0
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_145 : Nat := 0x3000300000000000000000000000000030003
def goal_145 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_145 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeaaaa0000aaaa0000aaaa0000aaaa0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafafafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcf0f00000f0f00000f0f00000f0f00000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefefafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffcccc00cc00cc00cc00cc00cc00cc00cc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeeeaacc00eeaacc00eeaacc00eeaacc00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfffffff0fffffff0fffffff0fffffff0f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffafafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfcf0cc00fcf0cc00fcf0cc00fcf0cc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffefffffffefffffffefffffffefefaeca0fefaeca0fefaeca0fefaeca0
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_161 : Nat := 0x30000000300000000000000000000000300000003
def goal_161 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfffffffffafafafafffffffffafafafaaaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfccccccccc00000000cccccccc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffefefefefffffffffefefefeeeeeeeeea0a0a0a0eeeeeeeea0a0a0a0
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaa00000000ffaaffaa00000000
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffffccffccffffffffffccffccffccffcccc00cc00ffccffcccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeecc00cc00ffeeffeecc00cc00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfffffffffff0fff0fffffffffff0fff0ff00ff0000000000ff00ff0000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffaffaaffaaa0a0a0a0ffaaffaaa0a0a0a0
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffffcfffcfffffffffffcfffcffccffcccc00cc00ffccffcccc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffefffefffffffffffefffeffeeffeeeca0eca0ffeeffeeeca0eca0
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
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffffffafafffffffffffffafafafaaaaafafaa0a0fafaaaaafafaa0a0
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfcfcccccf0f00000fcfcccccf0f00000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffefefffffffffffffefefefeeeeefafaa0a0fefeeeeefafaa0a0
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffffffffffff00ffffffffffffff00ff00ff0000000000ff00ff0000000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffffaaffffffffffffffaaffaaffaaaaaa0000ffaaffaaaaaa0000
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffffccffffffffffffffccffccffcccc00cc00ffccffcccc00cc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffeeffffffffffffffeeffeeffeeeeaacc00ffeeffeeeeaacc00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0fff0ff00f0f00000fff0ff00f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffffafffffffffffffffafffaffaafafaa0a0fffaffaafafaa0a0
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffffcfffffffffffffffcfffcffccfcf0cc00fffcffccfcf0cc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffefffffffffffffffefffeffeefefaeca0fffeffeefefaeca0
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_193 : Nat := 0x3000000000000000300000000000000030000000000000003
def goal_193 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000
def roots_193 : List Nat := [xs256.getD 0 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfffffffffffffffffafafafafafafafaaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfffffffffffffffffefefefefefefefeeeeeeeeeeeeeeeeea0a0a0a0a0a0a0a0
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaa0000000000000000
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffffccffccffccffccffccffccffccffcccc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeecc00cc00cc00cc00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffffaaaaffffaaaaaaaaaaaaaaaaaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffffffff0f0fffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffffafafffffafafafaaaaafafaaaaafafaa0a0fafaa0a0
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffffcfffffffcfffcffccfffcffccfcf0cc00fcf0cc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffefffffffefffeffeefffeffeefefaeca0fefaeca0
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffffffffffffffffffccccccccffffffffcccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffffffffffff0f0f0f0ffffffff000000000000000000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffffffffffafafafaffffffffaaaaaaaaaaaaaaaaa0a0a0a0
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffffffffffcfcfcfcffffffffcccccccccccccccc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffffffffffefefefeffffffffeeeeeeeeeeeeeeeea0a0a0a0
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffffffffffff00ff00ffffffffff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffffffaaffaaffaaffaa00000000
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffffccffccffffffffffccffccffccffcccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffeeffeeffffffffffeeffeeffeeffeecc00cc00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffffffffffafffaffffffffffaaffaaffaaffaaa0a0a0a0
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffffffffffcfffcffffffffffccffccffccffcccc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffefffeffffffffffeeffeeffeeffeeeca0eca0
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffffffffffffffffffff0000ffffffff000000000000000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffffffffffaaaaffffffffaaaaaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffffffccccffffffffcccccccccccccccc00000000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffffffeeeeffffffffeeeeeeeeeeeeeeeeaaaa0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffffffffffff0f0fffffffff0f00000f0f00000f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffffffafafffffffffafaaaaafafaaaaafafaa0a0
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffffffcfcfffffffffcfcccccfcfcccccf0f00000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffffffefefffffffffefeeeeefefeeeeefafaa0a0
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffffffaaffffffffffaaffaaffaaffaaaaaa0000
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffffffccffffffffffccffccffccffcccc00cc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffffeeffffffffffeeffeeffeeffeeeeaacc00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffffffffffff0fffffffffff0ff00fff0ff00f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffffffafffffffffffaffaafffaffaafafaa0a0
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffffffcfffffffffffcffccfffcffccfcf0cc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffffffefffffffffffeffeefffeffeefefaeca0
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
def isoMvS_42:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_42:Lower true dom_42 roots_42 goal_42 4:=lower_iso_b isoMvS_42 (by decide +kernel) lowS_21
def isoMvS_74:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_74:Lower true dom_74 roots_74 goal_74 4:=lower_iso_b isoMvS_74 (by decide +kernel) lowS_21
def isoMvS_97:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_97:Lower true dom_97 roots_97 goal_97 4:=lower_iso_b isoMvS_97 (by decide +kernel) lowS_21
def isoMvS_98:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_98:Lower true dom_98 roots_98 goal_98 4:=lower_iso_b isoMvS_98 (by decide +kernel) lowS_21
def isoMvS_104:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_104:Lower true dom_104 roots_104 goal_104 4:=lower_iso_b isoMvS_104 (by decide +kernel) lowS_21
def isoMvS_145:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_145:Lower true dom_145 roots_145 goal_145 4:=lower_iso_b isoMvS_145 (by decide +kernel) lowS_21
def isoMvS_161:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_161:Lower true dom_161 roots_161 goal_161 4:=lower_iso_b isoMvS_161 (by decide +kernel) lowS_21
def isoMvS_193:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_193:Lower true dom_193 roots_193 goal_193 4:=lower_iso_b isoMvS_193 (by decide +kernel) lowS_21
namespace S_39
def pG:List (Nat×Nat):=[(1,5),(1,33),(2,34),(3,7),(3,35),(4,5),(6,7),(6,38),(32,33),(32,34),(36,37),(36,38)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_39.map (·&&&dom_39)
def gM:=goal_39&&&dom_39
def NN:Nat→Nat
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x9b080
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00000000f0000000f0cc000000ccaa000000aa
|_,_=>0
def sP:Nat→Nat
|0=>0xe4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|_,_=>0
def wAt:=mkWire dB 4 40 0xffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_39 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_39 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_39==dom_39)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_39 gM v ys):RunD true dom_39 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_39 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_39 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_39 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_39 roots_39 goal_39 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_39
theorem lowS_39:Lower true dom_39 roots_39 goal_39 4:=S_39.noCircuit
theorem lowS_43:Lower true dom_43 roots_43 goal_43 5:=lower_slice_b [(0xa0a00000a0a,32,33)] (by decide +kernel) lowS_42
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_slice_b [(0xa0000000a0000000a0000000a,32,33)] (by decide +kernel) lowS_98
namespace S_106
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(8,10),(8,40),(8,72),(32,34),(32,40),(32,96),(64,66),(64,72),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_106.map (·&&&dom_106)
def gM:=goal_106&&&dom_106
def NN:Nat→Nat
|3=>3
|4=>7
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x25a8e15ae407a8e
|4,0=>0x71a6b39bad26d910e2a2098a008ad707995
|5,0=>0x9f91c1b19f04f10
|6,0=>0x9f91c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x282800002828000028280000000505000004040000050500000404a0a00000a0800000a0a00000a080000000141400000000000010108080000080800000808000000050500000000000005040000000020200000202000002020000020101000001010000010100000101280000002800000028000000280505000005050000000000000000a0a0000000000000a0a0000000141000001410000014100000141282800002828000028000000280505000005050000040400000404
|_,_=>0
def sP:Nat→Nat
|0=>0x35643564d356431564d350632504d3156c3254b3564356a435694856435743210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x21022004
|4,0=>0xa952aa0536a5948a8c5
|5,0=>0xe51a2af5
|6,0=>0x3d4
|_,_=>0
def wAt:=mkWire dB 14 107 0x7ffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x345514650d65591345513655964551
|_=>0
def oO:Nat→Nat→Nat
|3,0=>2
|4,0=>0x82624222000000
|5,0=>0xb1a1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfa76530
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>1
|4,0=>0xab600
|5,0=>0x136
|6,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_104 4 roots_104 ops++addP pm 1 dom_98 4 roots_98 ops++addP pm 2 dom_74 4 roots_74 ops++addP pm 3 dom_42 4 roots_42 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_106 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_42 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_104 4 s (0,roots_104.map (·&&&dom_104)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_106 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_104 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_106==dom_106)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_106 gM v ys):RunD true dom_106 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_106 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_106 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_106 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_106 roots_106 goal_106 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_106
theorem lowS_106:Lower true dom_106 roots_106 goal_106 7:=S_106.noCircuit
def isoMvS_45:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_45:Lower true dom_45 roots_45 goal_45 4:=lower_iso_b isoMvS_45 (by decide +kernel) lowS_39
def isoMvS_53:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_53:Lower true dom_53 roots_53 goal_53 5:=lower_iso_b isoMvS_53 (by decide +kernel) lowS_43
def isoMvS_71:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_71:Lower true dom_71 roots_71 goal_71 4:=lower_iso_b isoMvS_71 (by decide +kernel) lowS_39
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_43
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 4:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_39
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_43
def isoMvS_101:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 5:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_43
def isoMvS_105:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_99
def isoMvS_113:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_43
def isoMvS_135:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_135:Lower true dom_135 roots_135 goal_135 5:=lower_iso_b isoMvS_135 (by decide +kernel) lowS_43
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_43
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 5:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_43
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_43
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 7:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_106
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_43
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_43
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_43
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_43
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_99
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 5:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_99
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_43
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 5:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_99
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 7:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_106
def isoMvS_172:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 5:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_43
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_99
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_43
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_43
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 5:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_43
def isoMvS_195:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_99
def isoMvS_197:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 5:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_99
def isoMvS_201:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_99
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 7:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_106
def isoMvS_209:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 5:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_99
def isoMvS_212:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_43
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 7:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_106
def isoMvS_226:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 7:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_106
def isoMvS_228:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 5:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_43
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 7:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_106
def isoMvS_240:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_240:Lower true dom_240 roots_240 goal_240 5:=lower_iso_b isoMvS_240 (by decide +kernel) lowS_43
theorem lowS_31:Lower true dom_31 roots_31 goal_31 6:=lower_slice_b [(0xcccccccc,8,10),(0xff00ff00,2,10)] (by decide +kernel) lowS_21
def dzo_43_4:=0xf0f00000f0f0
def gzo_43_4:=0xf0e00000e0a0
def gsh_43_4:=0xf0e00000e0a
theorem lowS_zo_43_4_42:Lower true dzo_43_4 roots_43 gzo_43_4 5:=lower_iso_b (d1:=dom_43) (r1:=roots_43) (T1:=gsh_43_4) [(dom_43,4)] (by decide +kernel) (lower_slice_b (T:=gsh_43_4) [(0xa0a00000a0a,0,1)] (by decide +kernel) lowS_42)
namespace S_47
def pG:List (Nat×Nat):=[(1,5),(1,33),(2,10),(2,34),(3,7),(3,11),(3,35),(4,5),(6,7),(6,14),(6,38),(8,10),(8,40),(9,11),(9,13),(9,41),(12,13),(12,14),(12,44),(32,33),(32,34),(32,40),(36,37),(36,38),(36,44)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_47.map (·&&&dom_47)
def gM:=goal_47&&&dom_47
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xc22ea2ed5e
|5,0=>0xb24b5b141727eef
|6,0=>0xa2a89
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff0000ff00ffcc0000ffcc333300000000cccc0000cccc00ff000000ccffff00000000ff000000ff00f0f00000f0f0cccc0000cc00aaaa0000aaaa
|_,_=>0
def sP:Nat→Nat
|0=>0x432609432604832604326074260543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 48 0xffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x11b
|_=>0
def oO:Nat→Nat→Nat
|5,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0x1f69040
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x53
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_43 5 roots_43 ops++addP pm 1 dom_39 4 roots_39 ops++addP pm 2 dom_45 4 roots_45 ops++addP pm 3 dzo_43_4 5 roots_43 ops++addP pm 4 dom_42 4 roots_42 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_47 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_39 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_43_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_42 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_43 5 s (0,roots_43.map (·&&&dom_43)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_47 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_43 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_47==dom_47)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_47 gM v ys):RunD true dom_47 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_47 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_47 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_99_4:=0xf0000000f0000000f0000000f0
def gzo_99_4:=0xf0000000e0000000e0000000a0
def gsh_99_4:=0xf0000000e0000000e0000000a
theorem lowS_zo_99_4_98:Lower true dzo_99_4 roots_99 gzo_99_4 5:=lower_iso_b (d1:=dom_99) (r1:=roots_99) (T1:=gsh_99_4) [(dom_99,4)] (by decide +kernel) (lower_slice_b (T:=gsh_99_4) [(0xa0000000a0000000a0000000a,0,1)] (by decide +kernel) lowS_98)
namespace S_103
def pG:List (Nat×Nat):=[(1,5),(1,33),(1,65),(2,34),(2,66),(3,7),(3,35),(3,67),(4,5),(6,7),(6,38),(6,70),(32,33),(32,34),(32,96),(36,37),(36,38),(36,100),(64,65),(64,66),(64,96),(68,69),(68,70),(68,100)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_103.map (·&&&dom_103)
def gM:=goal_103&&&dom_103
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xa7530
|5,0=>0xca4ac
|6,0=>0xc6a65
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff000000ff000000ff00000000cc000000cc000000cc000000ccff00000000000000ff00000000f0000000f0000000f0000000f0aa000000aa000000aa000000aa33000000330000003300000000ff000000ff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8ea1a3a84688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 104 0xffffffffffffffffffffffffff
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
addP pm 0 dom_101 5 roots_101 ops++addP pm 1 dom_71 4 roots_71 ops++addP pm 2 dzo_99_4 5 roots_99 ops++addP pm 3 dom_99 5 roots_99 ops++addP pm 4 dom_98 4 roots_98 ops++addP pm 5 dom_39 4 roots_39 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_103 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_71 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_99_4_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_39 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_101 5 s (0,roots_101.map (·&&&dom_101)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_103 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_101 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_103==dom_103)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_103 gM v ys):RunD true dom_103 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_103 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_103 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_103 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_103 roots_103 goal_103 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_103
theorem lowS_103:Lower true dom_103 roots_103 goal_103 7:=S_103.noCircuit
theorem lowS_107:Lower true dom_107 roots_107 goal_107 8:=lower_slice_b [(0xa0a00000a0a00000a0a00000a0a,32,33)] (by decide +kernel) lowS_106
namespace S_117
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,65),(4,5),(4,20),(16,17),(16,20),(32,33),(32,96),(36,37),(36,52),(36,100),(48,49),(48,52),(48,112),(64,65),(64,96),(68,69),(68,84),(68,100),(80,81),(80,84),(80,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_117.map (·&&&dom_117)
def gM:=goal_117&&&dom_117
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x25b
|4,0=>0x1fade1f7cf1c9cf07483
|5,0=>0xbb29d4ce643fe443eb96335f42d60b216c814c27125910433a
|6,0=>0x96c744cec54ab101cc1b
|7,0=>0x96c74
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc00cc00cc00cc00c000c000c000c220022002200220020002000200020cc00cc00cc00cc000000880000008b30033003300000033003300330000cc00cc0088008800cc00cc0088008a200220022000000220022002200000000000000000000cc00cc00c800cb30000003300000033000000330000cc00cc00cc00cc00880088008800030003000300030003000300030003088008800880088008800880088008800030000000320000003000000032cc00cc0000000000cc00cc0000000330022003300220033002200330022c800c800c800c000c800c800c800c330033003300330000000000000000
|0,1=>0x20002000200020002000200020002cc00cc00c000c000cc00cc00c000c33003300320032003300330032003200000000000088000000000000008b300330033003300220022002200220c000c000c000c00080008000800080000000330033000000000022002244004400440044004000400040004000000002200220000000000220022
|_,_=>0
def sP:Nat→Nat
|0=>0xd06280683140343cc500d062e00b1a0c50586831403418b5020d42c803418b3020c590068316205a0c580068315c01a0c568183118a05a0ca0246831468314e33148018820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682ced9b2b0654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 25 118 0x3fffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x30129b28db95a0f2817942a32a1
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x51003200000000211101
|6,0=>0x817161
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0x3ff6fb5b512306080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x4030002615
|6,0=>0x7a98
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_113 5 roots_113 ops++addP pm 1 dom_21 4 roots_21 ops++addP pm 2 dom_85 5 roots_85 ops++addP pm 3 dom_53 5 roots_53 ops++addP pm 4 dom_97 4 roots_97 ops++addP pm 5 dom_101 5 roots_101 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_117 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_101 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_113 5 s (0,roots_113.map (·&&&dom_113)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_117 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_113 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_117==dom_117)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_117 gM v ys):RunD true dom_117 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_117 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_117 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_117 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_117 roots_117 goal_117 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_117
theorem lowS_117:Lower true dom_117 roots_117 goal_117 8:=S_117.noCircuit
theorem lowS_151:Lower true dom_151 roots_151 goal_151 8:=lower_slice_b [(0xcc00cc00000000000000000000000000cc00cc,128,130)] (by decide +kernel) lowS_149
namespace S_167
def pG:List (Nat×Nat):=[(1,5),(1,33),(1,129),(2,34),(2,130),(3,7),(3,35),(3,131),(4,5),(4,132),(6,7),(6,38),(6,134),(32,33),(32,34),(32,160),(36,37),(36,38),(36,164),(128,129),(128,130),(128,132),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_167.map (·&&&dom_167)
def gM:=goal_167&&&dom_167
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xa9bfa
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff000000000000000000000000000000ff00000000f0000000f00000000000000000000000f0000000f0cc000000cc0000000000000000000000cc000000ccaa000000aa0000000000000000000000aa000000aaff000000ff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 168 0xffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_166 5 roots_166 ops++addP pm 1 dom_165 5 roots_165 ops++addP pm 2 dom_163 5 roots_163 ops++addP pm 3 dom_135 5 roots_135 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_167 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_135 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_166 5 s (0,roots_166.map (·&&&dom_166)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_167 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_166 h
def symsG:List (List (Nat×Nat)):=[[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_167==dom_167)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_167 gM v ys):RunD true dom_167 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_167 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_167 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_167 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_167 roots_167 goal_167 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_167
theorem lowS_167:Lower true dom_167 roots_167 goal_167 7:=S_167.noCircuit
theorem lowS_227:Lower true dom_227 roots_227 goal_227 8:=lower_slice_b [(0xa0000000a0000000a0000000a0000000a0000000a0000000a0000000a,32,33)] (by decide +kernel) lowS_226
namespace S_234
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(2,130),(8,10),(8,40),(8,72),(8,136),(32,34),(32,40),(32,96),(32,160),(64,66),(64,72),(64,96),(64,192),(128,130),(128,136),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffff
def xsM:=roots_234.map (·&&&dom_234)
def gM:=goal_234&&&dom_234
def NN:Nat→Nat
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x83d77
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x50500000000000005050000000000000505000000000000050500000000a0000000a0000000a0000000a0000000a0000000a0000000a0000000a0101000001010000010100000101000001010000010100000101000001012828000028280000000000000000000028280000282800000000000000050500000505000005050000050500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>5
|_,_=>0
def wAt:=mkWire dB 5 235 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_232 7 roots_232 ops++addP pm 1 dom_170 7 roots_170 ops++addP pm 2 dom_226 7 roots_226 ops++addP pm 3 dom_202 7 roots_202 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_234 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_202 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_232 7 s (0,roots_232.map (·&&&dom_232)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_234 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_232 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xffffffff00000000ffffffff00000000,96)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_234==dom_234)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_234 gM v ys):RunD true dom_234 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_234 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_234 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_234 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_234 roots_234 goal_234 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_234
theorem lowS_234:Lower true dom_234 roots_234 goal_234 9:=S_234.noCircuit
def isoMvS_55:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_55:Lower true dom_55 roots_55 goal_55 7:=lower_iso_b isoMvS_55 (by decide +kernel) lowS_47
def isoMvS_59:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_59:Lower true dom_59 roots_59 goal_59 7:=lower_iso_b isoMvS_59 (by decide +kernel) lowS_47
def isoMvS_61:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 7:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_47
def isoMvS_62:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 6:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_31
def isoMvS_79:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_79:Lower true dom_79 roots_79 goal_79 7:=lower_iso_b isoMvS_79 (by decide +kernel) lowS_47
def isoMvS_87:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_87:Lower true dom_87 roots_87 goal_87 7:=lower_iso_b isoMvS_87 (by decide +kernel) lowS_47
def isoMvS_109:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 7:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_103
def isoMvS_115:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_103
def isoMvS_118:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 6:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_31
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 8:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_117
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 8:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_117
def isoMvS_157:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 8:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_151
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 8:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_117
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_107
def isoMvS_173:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 7:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_167
def isoMvS_174:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 8:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_151
def isoMvS_179:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_167
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 8:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_107
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 8:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_117
def isoMvS_185:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 7:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_167
def isoMvS_186:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 8:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_151
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 8:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_117
def isoMvS_199:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 7:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_167
def isoMvS_203:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_107
def isoMvS_213:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_107
def isoMvS_229:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 8:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_107
def isoMvS_230:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 8:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_151
def isoMvS_233:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_227
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 8:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_107
def isoMvS_242:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 8:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_151
def isoMvS_244:List (Nat×Nat):=[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 8:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_117
def dzo_29_2:=0xcccccccc
def gzo_29_2:=0xccc8cc80
def gsh_29_2:=0x33323320
theorem lowS_zo_29_2_21:Lower true dzo_29_2 roots_29 gzo_29_2 5:=lower_iso_b (d1:=dom_29) (r1:=roots_29) (T1:=gsh_29_2) [(dom_29,2)] (by decide +kernel) (lower_slice_b (T:=gsh_29_2) [(0x33003300,0,8)] (by decide +kernel) lowS_21)
def dzo_58_4:=0x5050505050505050
def gzo_58_4:=0x5050504050504000
def gsh_58_4:=0x505050405050400
theorem lowS_zo_58_4_42:Lower true dzo_58_4 roots_58 gzo_58_4 5:=lower_iso_b (d1:=dom_58) (r1:=roots_58) (T1:=gsh_58_4) [(dom_58,4)] (by decide +kernel) (lower_slice_b (T:=gsh_58_4) [(0x505000005050000,0,16)] (by decide +kernel) lowS_42)
def dzo_23_8:=0xff00ff00
def gzo_23_8:=0xfe00ec00
def gsh_23_8:=0xfe00ec
theorem lowS_zo_23_8_21:Lower true dzo_23_8 roots_23 gzo_23_8 5:=lower_iso_b (d1:=dom_23) (r1:=roots_23) (T1:=gsh_23_8) [(dom_23,8)] (by decide +kernel) (lower_slice_b (T:=gsh_23_8) [(0xcc00cc,0,2)] (by decide +kernel) lowS_21)
def dzo_46_16:=0x5555000055550000
def gzo_46_16:=0x5554000054500000
def gsh_46_16:=0x555400005450
theorem lowS_zo_46_16_42:Lower true dzo_46_16 roots_46 gzo_46_16 5:=lower_iso_b (d1:=dom_46) (r1:=roots_46) (T1:=gsh_46_16) [(dom_46,16)] (by decide +kernel) (lower_slice_b (T:=gsh_46_16) [(0x505000005050,0,4)] (by decide +kernel) lowS_42)
def dzo_61_2:=0xcccccccccccccccc
def gzo_61_2:=0xccccccccccc8cc80
def gsh_61_2:=0x3333333333323320
theorem lowS_zo_61_2_21:Lower true dzo_61_2 roots_61 gzo_61_2 6:=lower_iso_b (d1:=dom_61) (r1:=roots_61) (T1:=gsh_61_2) [(dom_61,2)] (by decide +kernel) (lower_slice_b (T:=gsh_61_2) [(0x3300330033003300,0,8),(0x3333333300000000,0,32)] (by decide +kernel) lowS_21)
def dzo_59_4:=0xf0f0f0f0f0f0f0f0
def gzo_59_4:=0xf0f0f0e0f0f0e0a0
def gsh_59_4:=0xf0f0f0e0f0f0e0a
theorem lowS_zo_59_4_42:Lower true dzo_59_4 roots_59 gzo_59_4 6:=lower_iso_b (d1:=dom_59) (r1:=roots_59) (T1:=gsh_59_4) [(dom_59,4)] (by decide +kernel) (lower_slice_b (T:=gsh_59_4) [(0xa0a0a0a0a0a0a0a,0,1),(0xf0f00000f0f0000,0,16)] (by decide +kernel) lowS_42)
def dzo_55_8:=0xff00ff00ff00ff00
def gzo_55_8:=0xff00ff00fe00ec00
def gsh_55_8:=0xff00ff00fe00ec
theorem lowS_zo_55_8_21:Lower true dzo_55_8 roots_55 gzo_55_8 6:=lower_iso_b (d1:=dom_55) (r1:=roots_55) (T1:=gsh_55_8) [(dom_55,8)] (by decide +kernel) (lower_slice_b (T:=gsh_55_8) [(0xcc00cc00cc00cc,0,2),(0xff00ff00000000,0,32)] (by decide +kernel) lowS_21)
def dzo_53_2:=0xcc00cc00cc00cc
def gzo_53_2:=0xcc00cc00c80080
def gsh_53_2:=0x33003300320020
theorem lowS_zo_53_2_21:Lower true dzo_53_2 roots_53 gzo_53_2 5:=lower_iso_b (d1:=dom_53) (r1:=roots_53) (T1:=gsh_53_2) [(dom_53,2)] (by decide +kernel) (lower_slice_b (T:=gsh_53_2) [(0x33003300000000,0,32)] (by decide +kernel) lowS_21)
def dzo_47_16:=0xffff0000ffff0000
def gzo_47_16:=0xfffe0000fefa0000
def gsh_47_16:=0xfffe0000fefa
theorem lowS_zo_47_16_42:Lower true dzo_47_16 roots_47 gzo_47_16 6:=lower_iso_b (d1:=dom_47) (r1:=roots_47) (T1:=gsh_47_16) [(dom_47,16)] (by decide +kernel) (lower_slice_b (T:=gsh_47_16) [(0xaaaa0000aaaa,0,1),(0xf0f00000f0f0,0,4)] (by decide +kernel) lowS_42)
namespace S_63
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(2,10),(2,34),(3,7),(3,11),(3,19),(3,35),(4,5),(4,20),(6,7),(6,14),(6,22),(6,38),(8,10),(8,40),(9,11),(9,13),(9,25),(9,41),(12,13),(12,14),(12,28),(12,44),(16,17),(16,20),(18,19),(18,22),(18,26),(18,50),(24,25),(24,26),(24,28),(24,56),(32,33),(32,34),(32,40),(36,37),(36,38),(36,44),(36,52),(48,49),(48,50),(48,52),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffff
def xsM:=roots_63.map (·&&&dom_63)
def gM:=goal_63&&&dom_63
def NN:Nat→Nat
|4=>1
|5=>3
|6=>9
|7=>18
|8=>10
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x24144
|5,0=>0x599851452c096a5
|6,0=>0xd2f45854614db562f857218781aef60caea092100454d
|7,0=>0xb25dc77e25754825c1184525d43ea83eafb359ee2f6af2efb618f7712b0f0ed460e2b20d32f0ba3e0412e028d7
|8,0=>0xc6758a964ea1d5077e2558d29450684017b29ed41fb9e0dd24
|9,0=>0xc6758
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff00cc00cc000000aaaa0000aaaaffffffffff00ff00fffff0f0fffff0f0f0f0a0a0f0f0a0a0f0f0f0f0f0f0f0f0cccccccccc00cc000000fafa0000fafaff00ff00ff00ff0033333333330033000f0f0a0a0f0f0a0affffffff00000000ffff0000ffff0000fff0ffa0fcf0eca0ccccccccccccccccaaaaaaaaaaaaaaaa
|0,1=>0xcceecceecceeccee55550000ffff00002222222222222222dd00dd00dd00dd0000ff00ff00000000f0fff0fff0f0f0f0aaaaaaaa00000000ffffffffaaaaaaaaffccffccffccffcc00ffaaff0000aaaa555555550000000000000000aaaaaaaa55555555aaaaaaaa0a0a0a0a0a0a0a0afafafafafafafafaffffffffcccccccc
|0,2=>0xeeeeeeeeeeeeeeeefff0fff0fff0fff0ffffffff0000aaaaaa00aa00aaaaaaaafafafafaf0f0f0f0ffffaaaaffffaaaa00aa00aa00aa00aa
|_,_=>0
def sP:Nat→Nat
|0=>0x3443031ca0401031ca7c010728101e10329c0401072810081033ca0401031da2810180c72814c45c72810081031d12890040c72810160c72814c40c72801921031d12801840cf28100e10c0c72890040c72c90041ca2402040c70061440c2040
|1=>0x6040c72810040c72810191031d12810040d71ca0401031ca0406c40e51ca0401031ca0407580c72816581031ca04010c0d71ca0403440c744a0401035c728100e9040c72810040c72810230c72815541031e20401031ca0406ce1210c728101b
|2=>0x1031ca0401031ca0401031ca0405040c72a6040
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x45816c056
|6,0=>0x4d62338fdc70e335163895c3ce177
|7,0=>0x192cc275d42ca1550a374e3a59920c8884041e20e4c6c63331818b4c537
|8,0=>0x21cd077803be5de4eeb7723b75dacecf7
|9,0=>0x1146
|_,_=>0
def wAt:=mkWire dB 39 64 0xffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x40204044011000a011c147122874102100440010043291c1441d28043021c144390c0806f1c484031008a6500403021c4841f0c04a0d1c441811c083670040777040834628047400444a6d1c4986710044000d18a0104d071155444031008d071c44d0710743021d0011104d0711
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x103388c2000931c85208c02
|7,0=>0xd0b31c4af2b4ab2a4a7294a32849f2749b26497254932
|8,0=>0x3e1f47c1ec7a1e4781dc761
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0x112051812ea3050390fa66174952e892dd120aa20f7c41bf882df0d0281155c0d3f812ff024fe0497c092a81250022ae0341403a0802ff004fe0097c00a0800ff000aa00010000080000
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x808804108a2
|7,0=>0x10d54d27c3e2ce7aae3757a
|8,0=>0x1b0b421995f74
|9,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_61 7 roots_61 ops++addP pm 1 dzo_29_2 5 roots_29 ops++addP pm 2 dom_59 7 roots_59 ops++addP pm 3 dzo_58_4 5 roots_58 ops++addP pm 4 dom_55 7 roots_55 ops++addP pm 5 dzo_23_8 5 roots_23 ops++addP pm 6 dom_47 7 roots_47 ops++addP pm 7 dzo_46_16 5 roots_46 ops++addP pm 8 dzo_61_2 6 roots_61 ops++addP pm 9 dom_62 6 roots_62 ops++addP pm 10 dom_53 5 roots_53 ops++addP pm 11 dzo_59_4 6 roots_59 ops++addP pm 12 dom_31 6 roots_31 ops++addP pm 13 dom_42 4 roots_42 ops++addP pm 14 dzo_55_8 6 roots_55 ops++addP pm 15 dzo_53_2 5 roots_53 ops++addP pm 16 dzo_43_4 5 roots_43 ops++addP pm 17 dzo_47_16 6 roots_47 ops++addP pm 18 dom_43 5 roots_43 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_63 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_29_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_58_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_23_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_46_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_61_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_59_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_55_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_53_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_43_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_43 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_61 7 s (0,roots_61.map (·&&&dom_61)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_63 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_61 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_63==dom_63)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_63 gM v ys):RunD true dom_63 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_63 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 18 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_63 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_63 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_63 roots_63 goal_63 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_63
theorem lowS_63:Lower true dom_63 roots_63 goal_63 10:=S_63.noCircuit
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0e00000f0e00000e0a0
def gsh_107_4:=0xf0f00000f0e00000f0e00000e0a
theorem lowS_zo_107_4_106:Lower true dzo_107_4 roots_107 gzo_107_4 8:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xa0a00000a0a00000a0a00000a0a,0,1)] (by decide +kernel) lowS_106)
namespace S_111
def pG:List (Nat×Nat):=[(1,5),(1,33),(1,65),(2,10),(2,34),(2,66),(3,7),(3,11),(3,35),(3,67),(4,5),(6,7),(6,14),(6,38),(6,70),(8,10),(8,40),(8,72),(9,11),(9,13),(9,41),(9,73),(12,13),(12,14),(12,44),(12,76),(32,33),(32,34),(32,40),(32,96),(36,37),(36,38),(36,44),(36,100),(64,65),(64,66),(64,72),(64,96),(68,69),(68,70),(68,76),(68,100)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_111.map (·&&&dom_111)
def gM:=goal_111&&&dom_111
def NN:Nat→Nat
|4=>3
|5=>15
|6=>35
|7=>15
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xe53c48f45212ddc
|5,0=>0xfda0adafe9867de84e0374f0f6a8136a7cf4ef374de3c4654d3424729cf81b18608a010622c
|6,0=>0xca686c3d92aac74a2b2d9d74e89ae5867de74bbb73a4d6ab3468c226385160c755bcc05b0aa59b505972d5859754cee4837f41a5329e6c29bbb26cef242d7218ca1f91d1a9531a29718bd115c4310dab070fa06032042c0
|7,0=>0xb99b7a3cb2a089996c6d62b4f5edaa52dc551506222bb1fd1d11c0f11278107dd0d65e0cbc3
|8,0=>0xcdd67932264e8e3
|9,0=>0x4f37e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff0000ff000000ffff0000ff00ffff0000ffff0000000000000000ffff0000ffff0000ffff0000ff00ffff000000000000ffff00000000ffff0000ffff0000cccc0000ccccffcc0000ffcc0000ffcc0000ffccffff0000cccc0000ff000000cc00ffff0000cccc0000ffff0000ccccffff0000ffff0000ff000000ff00ffff0000ff000000cccc0000cc00aaaa0000aaaa0000aaaa0000aaaaffff0000ffff0000ffff00000000ffff0000eeee0000ffaa0000eeaaff000000ff000000ff000000ff00f0f00000f0f00000f0f00000f0f0cccc0000cccc0000cccc0000cccc
|0,1=>0xcccc0000cccc0000ffff0000ffcc000000000000000000ff000000cc00000000ffff000000000000ffcc00ff000000ff000000ff000000ccffff000033330000ffff0000330000000000ffff000000000000ff00ff000000ff000000ff000000cc00333300003333000033330000000033330000330000003333000033003333000033330000333300003300cccc0000cccc0000cccc0000cc0000ff000000ff000000ff00000000ffff0000ffff0000ffff0000cccc00000000ffff000000000000cccc00ff000000cc000000ff000000ccffff0000ffff0000ffcc0000ffcc
|0,2=>0xffff0000ff0000ff000000ff000000cc000000ccffff0000ffcc0000ffff0000ffcc0033000000330000003300000000ffff0000ffff0000ffff0000ffccccff0000ccff0000ccff0000cccc
|_,_=>0
def sP:Nat→Nat
|0=>0x14e4cc08115838c28204548e10204015738f20704b14c28904538c08115638c0551543840890401480812c550f4c704014c28704548f21004538808118538810a1c11440812c544811008114c0c204038d30a04b1442890452070461440c2040
|1=>0x4015c38c6412c014e7cc08100538c08100578e30205514e4cc28204538830204560e10c40204014830a1c114e30204015d38c04b00570e3cc1c12c014f4c204014e30204b15139b30204014e30204b00568430a0812c510c641005388310081
|2=>0x10c28204014e8cc0810053a320c08100539330204014e4c830204014e10c0811563881070810052040812c530204016238810204560e84c08100538c08115638c08100570e30206000538c08904014e30a1c12c520204015438d30205514e4cc
|3=>0x30204014e30a08100538430204014e20c08100538830708100538810204014e20c0812c538430204015438f20204014e94c08100538c08100550e4c430204014e30204016438c28204b14e
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x18d8bac57628b12d88ac3f61cb0cd85ac27610b06d82ac0f6
|6,0=>0x54de98f4669fbce1e62f2b6923c75e2cf10684bc09df6ef4776bb99dc0cd97693b2dd88ebd75b3abdd50ea174d3a4dd18e8573f39ddce0e697
|7,0=>0x706374fb37d5c691f3af967c7461df00f788b8bda62c4f5a8
|8,0=>0x75dfa0fc97
|9,0=>0x1de6
|_,_=>0
def wAt:=mkWire dB 38 112 0xffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc42013824039102ce3120e40314c20b313400f3908c4c2d00e530320e403128e420140cca39080530b2cc483900c422200c470308e473308e4c394c2040130e4e290804401100cc3930b80393c0c2312070e0900c481c08e403130b4e011c042392cf00393024c3908b40393ce4231
|1=>0x20130e403108e403130e403100e4031102cc3930240313cec231102cc391004c392c2c03900e420130e420128c4201202403120e403120e4031340c40930e403930e403110acc39080440338c4d033ce4231102cc392070239
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x7980000030c000a20002082984100008800002
|6,0=>0x13cc004c39271c800443001089f9bc3744001c136200000199b125c6b08002934e4001292324247c8f09b332458ca1122
|7,0=>0x1b8b616a2d0598b21622c0578ae15a2b0558aa1522
|8,0=>0x1c8788f01
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x7f6fcdbeb7b5f6bcd3fa7d4f69cd289d33606044887f0d614c288430821001d0220400600901001001001000
|1=>0xdffb6f3dc9c
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x180008003001142001004
|6,0=>0xc01634500b0045d81000c400054344100a1000c704408e0520c7
|7,0=>0x969e3e285751c7508e07d3
|8,0=>0x195db
|9,0=>0x17
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 11 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_107 8 roots_107 ops++addP pm 1 dom_79 7 roots_79 ops++addP pm 2 dom_101 5 roots_101 ops++addP pm 3 dom_103 7 roots_103 ops++addP pm 4 dom_109 7 roots_109 ops++addP pm 5 dom_47 7 roots_47 ops++addP pm 6 dzo_107_4 8 roots_107 ops++addP pm 7 dom_77 4 roots_77 ops++addP pm 8 dom_45 4 roots_45 ops++addP pm 9 dom_106 7 roots_106 ops++addP pm 10 dom_71 4 roots_71 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_111 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_107_4_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_71 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_107 8 s (0,roots_107.map (·&&&dom_107)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_111 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_107 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_111==dom_111)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_111 gM v ys):RunD true dom_111 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_111 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 35 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_111 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_21_2:=0xcc00cc
def gzo_21_2:=0xc80080
def gsh_21_2:=0x320020
theorem lowS_zo_21_2_21:Lower true dzo_21_2 roots_21 gzo_21_2 4:=lower_iso_b (d1:=dom_21) (r1:=roots_21) (T1:=gsh_21_2) [(dom_21,2)] (by decide +kernel) (lower_slice_b (T:=gsh_21_2) [] (by decide +kernel) lowS_21)
def dzo_117_2:=0xcc00cc00cc00cc00cc00cc00cc00cc
def gzo_117_2:=0xcc00cc00cc00cc00cc00cc00c80080
def gsh_117_2:=0x330033003300330033003300320020
theorem lowS_zo_117_2_21:Lower true dzo_117_2 roots_117 gzo_117_2 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_2) [(dom_117,2)] (by decide +kernel) (lower_slice_b (T:=gsh_117_2) [(0x330033000000000033003300000000,0,32),(0x330033003300330000000000000000,0,64)] (by decide +kernel) lowS_21)
def dzo_103_16:=0xff000000ff000000ff000000ff0000
def gzo_103_16:=0xff000000fe000000fe000000fa0000
def gsh_103_16:=0xff000000fe000000fe000000fa
theorem lowS_zo_103_16_98:Lower true dzo_103_16 roots_103 gzo_103_16 6:=lower_iso_b (d1:=dom_103) (r1:=roots_103) (T1:=gsh_103_16) [(dom_103,16)] (by decide +kernel) (lower_slice_b (T:=gsh_103_16) [(0xaa000000aa000000aa000000aa,0,1),(0xf0000000f0000000f0000000f0,0,4)] (by decide +kernel) lowS_98)
def dzo_85_2:=0xcc00cc0000000000cc00cc
def gzo_85_2:=0xcc00cc0000000000c80080
def gsh_85_2:=0x3300330000000000320020
theorem lowS_zo_85_2_21:Lower true dzo_85_2 roots_85 gzo_85_2 5:=lower_iso_b (d1:=dom_85) (r1:=roots_85) (T1:=gsh_85_2) [(dom_85,2)] (by decide +kernel) (lower_slice_b (T:=gsh_85_2) [(0x3300330000000000000000,0,64)] (by decide +kernel) lowS_21)
def dzo_114_4:=0x500050005000500050005000500050
def gzo_114_4:=0x500050005000400050004000500000
def gsh_114_4:=0x50005000500040005000400050000
theorem lowS_zo_114_4_98:Lower true dzo_114_4 roots_114 gzo_114_4 5:=lower_iso_b (d1:=dom_114) (r1:=roots_114) (T1:=gsh_114_4) [(dom_114,4)] (by decide +kernel) (lower_slice_b (T:=gsh_114_4) [(0x50000000500000005000000050000,0,16)] (by decide +kernel) lowS_98)
def dzo_102_16:=0x550000005500000055000000550000
def gzo_102_16:=0x550000005400000054000000500000
def gsh_102_16:=0x55000000540000005400000050
theorem lowS_zo_102_16_98:Lower true dzo_102_16 roots_102 gzo_102_16 5:=lower_iso_b (d1:=dom_102) (r1:=roots_102) (T1:=gsh_102_16) [(dom_102,16)] (by decide +kernel) (lower_slice_b (T:=gsh_102_16) [(0x50000000500000005000000050,0,4)] (by decide +kernel) lowS_98)
def dzo_115_4:=0xf000f000f000f000f000f000f000f0
def gzo_115_4:=0xf000f000f000e000f000e000f000a0
def gsh_115_4:=0xf000f000f000e000f000e000f000a
theorem lowS_zo_115_4_98:Lower true dzo_115_4 roots_115 gzo_115_4 6:=lower_iso_b (d1:=dom_115) (r1:=roots_115) (T1:=gsh_115_4) [(dom_115,4)] (by decide +kernel) (lower_slice_b (T:=gsh_115_4) [(0xa000a000a000a000a000a000a000a,0,1),(0xf0000000f0000000f0000000f0000,0,16)] (by decide +kernel) lowS_98)
namespace S_119
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,65),(2,34),(2,66),(3,7),(3,19),(3,35),(3,67),(4,5),(4,20),(6,7),(6,22),(6,38),(6,70),(16,17),(16,20),(18,19),(18,22),(18,50),(18,82),(32,33),(32,34),(32,96),(36,37),(36,38),(36,52),(36,100),(48,49),(48,50),(48,52),(48,112),(64,65),(64,66),(64,96),(68,69),(68,70),(68,84),(68,100),(80,81),(80,82),(80,84),(80,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_119.map (·&&&dom_119)
def gM:=goal_119&&&dom_119
def NN:Nat→Nat
|5=>4
|6=>15
|7=>24
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x7b72e6884d559580fceb
|6,0=>0xee19cc80e665a31623615c120486fc4634937d1c3618b266941affb1940b1584b09b5009962
|7,0=>0xe6e92cb580c2654ba857b09fda00819a99f956348aef678d4e6f73054f3c52a16445da39d502cc4024f2a1f161181df162fe0781104d9b0371c02440
|8,0=>0xf06f3c5484a4ab884cb05d38a47c932e83b1fc0f
|9,0=>0xdaa04
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff00aa00aa00ff00ff00aa00aaff00ff00ff00ff00aa00aa00aa00aaff00ff00ff00ff00ff00ff000000000a000a000a000a000a000a000a000afa000000fa000000fa000000fa00000000000000000000ff00ff00aa00aacc00cc00cc00cc00cc00cc00cc00cc00000000ff00ff0000000000aa00aa3300330033003300330033000000000f000a000f000a000f000a000f000aff00ff0000000000ff00ff00000000ff000000ff000000ff000000ff0000f000f000f000f000f000f000f000f0aa00aa00aa00aa00aa00aa00aa00aa3b003b003b003b003b003b000a000aff00ff00ff00ff0000000000000000
|0,1=>0xaa00aa00aa00aacc00cc00cc00cc00ee00ee00ee00eeff00ff00f000f000ff00ff00f000f00000000000000000ff00ff00f000f0ff00f000ff00f000ff00f000ff00f0bb00bb00bb00bb00bb00bb00aa00aaff00ff000a000a00ff00ff000a000aff00ff00ff00ff00ff00ff000a000a00000000ff00ff00000000000000aa0000aa000000aa000000aa000000aaff00ff00ff00ff000000aa000000aaf000a000f000a000f000a000f000a0ff00ff00ff00ff00ff00ff00aa00aaff00aa00ff00aa00ff00aa00ff00aafa00fa00fa00fa00fa00fa00fa00fa0000fa000000fa000000fa000000fa
|0,2=>0xff00ff00ff00ff00ff000000ff0000ce00ce00ce00ce00ce00ce00ce00ce000000000000000000000000aa00aaff00ff00ff00ff0000000000aa00aaff00ff000000aa00ff00ff000000aaff00ff00ff00ff00ff00ff00f000f0ee00ee00ee00ee00ee00ee00ee00ee00000000aa00aa0000000000aa00aa
|_,_=>0
def sP:Nat→Nat
|0=>0x56c40c21c01440da0803c40c90880181440c90803c40c93880051032425c034510324254f28d1032423cd10324e34511424201328510324215210308700d1432424003cd10324e08510308730014b0c21c02840c90881440871801440c2040
|1=>0x86000d15210324200510324e08800d1440c908c0051032429003456c40c90808c51032420052c324200f1440e108088510324200510908600510384e00f3440c90804cf1440c90801440c93a000510378201c1440c90801440c21c04c5103242
|2=>0x51032420054840c908015b10324200510324e0803451032420059c40c90801440c90960051038420051032428003c510324e0051032422001440e60803c510324e0801440c90a5005103
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x9303180cc006
|6,0=>0x1e1ce4c6b7323975cace4f7243909876e34716b899c3ee187
|7,0=>0x8fbc61e24d0a881bbf59eb0ed872c379dad0cf764b309d76eb5657b2a1d41099749b231d0cc7f7
|8,0=>0xab3d3de90f4179d3ccde5ad267
|9,0=>0x15d6
|_,_=>0
def wAt:=mkWire dB 40 120 0xffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x85c40d140561510291100c242152424d0d140520f10242012424015085403d085450a080497d080c0760c54d2714045390804d2714045014c5c03d0855901305430a385c009580440a3c0c2150804015085520c14044093c0c03d0854d27140511314043090804015085430a349c501
|1=>0x409103420114044011028909085c509080453a08049310c285090804d0a14042172424501102453a080430a1406001
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x849009d33466080016228444c718b312418c19803
|7,0=>0xa253ca694b29251ca29432824fc9e93b2724dc9a9332624bc9692b25249c929232
|8,0=>0xb43646c0d71ac3546a0d31
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0xab2a0b4740f8f81d5703a3e074740e8b81c5b038b207064068e8073500aae01454022f8045300836010680209002040032200400002180020000300004c000880010000080000c000100000
|1=>0x42d958402a87cfcaece9019118e7e27cfc368b86d15
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0x32060870043572c92853cc
|7,0=>0x5998cf6e690e45b9d579d85e8984188a051c
|8,0=>0x9686937d589a
|9,0=>0x12
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_117 8 roots_117 ops++addP pm 1 dzo_21_2 4 roots_21 ops++addP pm 2 dom_115 7 roots_115 ops++addP pm 3 dom_118 6 roots_118 ops++addP pm 4 dom_87 7 roots_87 ops++addP pm 5 dzo_117_2 6 roots_117 ops++addP pm 6 dom_21 4 roots_21 ops++addP pm 7 dzo_103_16 6 roots_103 ops++addP pm 8 dom_103 7 roots_103 ops++addP pm 9 dzo_85_2 5 roots_85 ops++addP pm 10 dom_55 7 roots_55 ops++addP pm 11 dzo_114_4 5 roots_114 ops++addP pm 12 dzo_102_16 5 roots_102 ops++addP pm 13 dzo_115_4 6 roots_115 ops++addP pm 14 dzo_99_4 5 roots_99 ops++addP pm 15 dzo_53_2 5 roots_53 ops++addP pm 16 dom_98 4 roots_98 ops++addP pm 17 dom_85 5 roots_85 ops++addP pm 18 dom_99 5 roots_99 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_119 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_21_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_117_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_103_16_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_85_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_114_4_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_102_16_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_115_4_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_99_4_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_53_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_99 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_117 8 s (0,roots_117.map (·&&&dom_117)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_119 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_117 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_119==dom_119)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_119 gM v ys):RunD true dom_119 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_119 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 15 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_119 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_119 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_119 roots_119 goal_119 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_119
theorem lowS_119:Lower true dom_119 roots_119 goal_119 10:=S_119.noCircuit
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_slice_b [(0x50505050505050505050505050505050,16,20),(0x55550000555500005555000055550000,4,20)] (by decide +kernel) lowS_106
namespace S_159
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,129),(2,10),(2,130),(3,7),(3,11),(3,19),(3,131),(4,5),(4,20),(4,132),(6,7),(6,14),(6,22),(6,134),(8,10),(8,136),(9,11),(9,13),(9,25),(9,137),(12,13),(12,14),(12,28),(12,140),(16,17),(16,20),(16,144),(18,19),(18,22),(18,26),(18,146),(24,25),(24,26),(24,28),(24,152),(128,129),(128,130),(128,132),(128,136),(128,144)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_159.map (·&&&dom_159)
def gM:=goal_159&&&dom_159
def NN:Nat→Nat
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0x932a5
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff0000000000000000000000000000ffff0000ff00ff00000000000000000000000000ff00ff00f0f0f0f0000000000000000000000000f0f0f0f0cccccccc000000000000000000000000ccccccccaaaaaaaa000000000000000000000000aaaaaaaaffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c688
|_=>0
def sO:Nat→Nat→Nat
|9,0=>6
|_,_=>0
def wAt:=mkWire dB 6 160 0xffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0x3e0
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_158 8 roots_158 ops++addP pm 1 dom_157 8 roots_157 ops++addP pm 2 dom_155 8 roots_155 ops++addP pm 3 dom_151 8 roots_151 ops++addP pm 4 dom_143 8 roots_143 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_159 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_143 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_158 8 s (0,roots_158.map (·&&&dom_158)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_159 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_158 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_159==dom_159)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_159 gM v ys):RunD true dom_159 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_159 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_159 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_159 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_159 roots_159 goal_159 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_159
theorem lowS_159:Lower true dom_159 roots_159 goal_159 10:=S_159.noCircuit
namespace S_175
def pG:List (Nat×Nat):=[(1,5),(1,33),(1,129),(2,10),(2,34),(2,130),(3,7),(3,11),(3,35),(3,131),(4,5),(4,132),(6,7),(6,14),(6,38),(6,134),(8,10),(8,40),(8,136),(9,11),(9,13),(9,41),(9,137),(12,13),(12,14),(12,44),(12,140),(32,33),(32,34),(32,40),(32,160),(36,37),(36,38),(36,44),(36,164),(128,129),(128,130),(128,132),(128,136),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_175.map (·&&&dom_175)
def gM:=goal_175&&&dom_175
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xe62a2
|7,0=>0xc1b61b216d447d518b360c3a9
|8,0=>0xc13be0e69b
|9,0=>0x3e74a
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff0000ffff00000000000000000000ffcc0000ffcc00ff000000ff0000000000000000000000cc000000ccff000000ff0000000000000000000000ff000000ff00cccc0000cccc00000000000000000000cccc0000ccccffff0000ffff00000000000000000000000000000000ffff0000000000000000000000000000ffff00000000ffcc0000ffcc00000000000000000000ffcc0000ffccffff0000ffff00000000000000000000ff000000ff00f0f00000f0f000000000000000000000f0f00000f0f0ffff0000ffff00000000000000000000cccc0000ccccaaaa0000aaaa00000000000000000000aaaa0000aaaa
|_,_=>0
def sP:Nat→Nat
|0=>0x582706582170654827065a8270653821705a82170654821065827096543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d4835c67
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 176 0xffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1d9875198761976605765d9876067661d865d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfff1b7f3f7fafc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x77aa
|8,0=>0x14
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_174 8 roots_174 ops++addP pm 1 dom_173 7 roots_173 ops++addP pm 2 dom_167 7 roots_167 ops++addP pm 3 dom_47 7 roots_47 ops++addP pm 4 dom_143 8 roots_143 ops++addP pm 5 dom_171 8 roots_171 ops++addP pm 6 dom_39 4 roots_39 ops++addP pm 7 dom_45 4 roots_45 ops++addP pm 8 dom_165 5 roots_165 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_175 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_39 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_165 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_174 8 s (0,roots_174.map (·&&&dom_174)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_175 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_174 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_175==dom_175)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_175 gM v ys):RunD true dom_175 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_175 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_175 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_175 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_175 roots_175 goal_175 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_175
theorem lowS_175:Lower true dom_175 roots_175 goal_175 10:=S_175.noCircuit
def dzo_227_4:=0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0
def gzo_227_4:=0xf0000000f0000000f0000000f0000000f0000000e0000000e0000000a0
def gsh_227_4:=0xf0000000f0000000f0000000f0000000f0000000e0000000e0000000a
theorem lowS_zo_227_4_98:Lower true dzo_227_4 roots_227 gzo_227_4 6:=lower_iso_b (d1:=dom_227) (r1:=roots_227) (T1:=gsh_227_4) [(dom_227,4)] (by decide +kernel) (lower_slice_b (T:=gsh_227_4) [(0xa0000000a0000000a0000000a0000000a0000000a0000000a0000000a,0,1),(0xf0000000f0000000f0000000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_98)
namespace S_231
def pG:List (Nat×Nat):=[(1,5),(1,33),(1,65),(1,129),(2,34),(2,66),(2,130),(3,7),(3,35),(3,67),(3,131),(4,5),(4,132),(6,7),(6,38),(6,70),(6,134),(32,33),(32,34),(32,96),(32,160),(36,37),(36,38),(36,100),(36,164),(64,65),(64,66),(64,96),(64,192),(68,69),(68,70),(68,100),(68,196),(128,129),(128,130),(128,132),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_231.map (·&&&dom_231)
def gM:=goal_231&&&dom_231
def NN:Nat→Nat
|5=>2
|6=>8
|7=>9
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xa29464cf0b
|6,0=>0xf51f7e6d8fc3b364886b273fb24f08185a10461b
|7,0=>0xf2d04cd1f4bed8c9d76083a9a7a27675ada5518e4fd95
|8,0=>0xe576f8cb884aeef
|9,0=>0x9aff0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff000000ff0000000000000000000000ff00000000ff000000ff000000f0000000f0000000ff000000ff000000f0000000f000000000ff00000000000000f000000000000000ff00000000000000f0ff000000ff000000ff000000ff000000ff000000ff000000ff00000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0ff00000000000000ff00000000000000ff00000000000000ff00000000ff000000ff000000ff000000f0000000ff000000ff000000ff000000f0cc000000cc000000cc000000cc000000cc000000cc000000cc000000ccff000000ff000000ff000000ff000000ff000000ff0000000000000000ff000000f0000000ff000000f0000000ff000000f0000000ff000000f0ff000000ff000000ff000000ff000000ff00000000000000ff00000000aa000000aa000000aa000000aa000000aa000000aa000000aa000000aa3300000033000000330000003300000033000000330000003300000000ff000000ff0000000000000000000000ff000000ff0000000000000000ff000000ff000000ff000000ff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xe7310547310c9a7310c9a73610973d10897310b4a731049a73619fa731059736109a32109a32610547361973d60c9a32105c47310847310b4a73684736543210
|1=>0x9a7310b9a73109a736109
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x65006
|6,0=>0x3863172b62561e71771160b6
|7,0=>0x7566e76686065a65374c74573e7
|8,0=>0x8878177b6
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 16 232 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x24510685a964196441964419ea85ba645196419044114a419a441c7e591071f96441a96411067aa165910505a9641906e91944119641ba44119641
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0x5cd5248cf3348a31cc43
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 10
def pmP:Nat→Nat
|0=>0x13f39e84bce1e6ef776bb3dd9be8fb46d937c7e62f30f986401e6080038804001e000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x20
|6,0=>0x189eb21947
|7,0=>0x10a4d8d4c90e
|8,0=>0x1e2c
|9,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_230 8 roots_230 ops++addP pm 1 dom_103 7 roots_103 ops++addP pm 2 dom_195 5 roots_195 ops++addP pm 3 dom_163 5 roots_163 ops++addP pm 4 dom_167 7 roots_167 ops++addP pm 5 dom_227 8 roots_227 ops++addP pm 6 dom_199 7 roots_199 ops++addP pm 7 dom_229 8 roots_229 ops++addP pm 8 dom_135 5 roots_135 ops++addP pm 9 dom_71 4 roots_71 ops++addP pm 10 dzo_99_4 5 roots_99 ops++addP pm 11 dzo_227_4 6 roots_227 ops++addP pm 12 dom_39 4 roots_39 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_231 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_135 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_71 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_99_4_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_227_4_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_39 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_230 8 s (0,roots_230.map (·&&&dom_230)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_231 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_230 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_231==dom_231)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_231 gM v ys):RunD true dom_231 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_231 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_231 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_231 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_231 roots_231 goal_231 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_231
theorem lowS_231:Lower true dom_231 roots_231 goal_231 10:=S_231.noCircuit
namespace S_235
def pG:List (Nat×Nat):=[(1,33),(1,65),(1,129),(2,10),(2,34),(2,66),(2,130),(3,11),(3,35),(3,67),(3,131),(8,10),(8,40),(8,72),(8,136),(9,11),(9,41),(9,73),(9,137),(32,33),(32,34),(32,40),(32,96),(32,160),(64,65),(64,66),(64,72),(64,96),(64,192),(128,129),(128,130),(128,136),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffff
def xsM:=roots_235.map (·&&&dom_235)
def gM:=goal_235&&&dom_235
def NN:Nat→Nat
|4=>4
|5=>68
|6=>157
|7=>95
|8=>26
|9=>4
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x411912a584287be06929
|5,0=>0xbdff79199f909128ebd88a5fc836117ad6c7a6db78115761a2747667377d710bd70afc686af5a5805538e551cc54f1553a0b4f0b04ee5b4e92f4e45a4d83d458a63e6233e5bf3bbbc3b48c3a9d03530330a6c2dcc52ceb42aaee270ce257ea23cb323712222c4210711fa981ec381cbf71ca9a1baed1b2ef19fd019fa018469166e4165f114361122dc120b811a790fbda0cfb20a2ed0943707d04070e706c80058cb046e20192200968
|6,0=>0x63cd25d76f5c9f65b5b359f0d5865d58616574595551054eca509f94f9af4d8db4c66d49a5346bed46b5d4679145c47455e44504944de544a8e443734342140eef40ce63f7d33ed5b3b59f3b1713ab293a00336dc535a60346de33d983388f32aeb32ac33260831c61305f52fcfb2fa542fa4d2e3492e0a32de092db362d9c12c8282bbfc2a2162999329821295d028fb9288522799b2766626eaf22db0224a12221721a1d2028c1fcba1fabf1f5271d7a71d23a1ca171be7b1b4b51b3361b0141abe019cc51965e19508191cd18918184211823716ef6168ad15d1a1565114bbb14924143b0143221372b1328a12ec8119f0118d41010a0fb960f97e0d86d0c0d60b8eb0b5dd0abca0a8ff0a8320a74b0a52f0944b08486082a407e230745a07012067330663c05bab05b5d053e404c4c047fa0408a0312602582024fe0172f
|6,1=>0xe7ae6e1b71bdff7b9728b8082b4ae3b1f9c9ba3295d4b909128dcff8a99d839fc8361180f0b7e8897d69c7ba207b5c575499745f471a976e87d69c47682f868114668e8662b7645a3
|7,0=>0xf9cc4f3d4fba59db82b2a82a29cef695bda8fc65834b5818db811e47b96671d517052b6fcce6f4fe6e09d6186e5d76f5cbce5b95459f9e5978d577fa5696e541c84bbbc4b78049e14481ce454a944714441b84209640a463fa1b37bd635dc93477c344133368732dc6329a932828327743241b30f343086a3006b2d2592cff02915a2874827e0226913258792412c23e8322c7b1f8da1f7421d7f11d50f1984818c0f16c561688915c4e1416113a7212318121a70f9810e2190de7b0d3e70d22f0c5ba0c4410b3d20b3630a75309bb2098520924d08827080b307e00056b3055be04728044370372e00ffe0065a
|8,0=>0xfa065be4269d8e695f7b6eda3618c95ff13552f84a6894365038f8b3891e38690303302dbb82b0dc27a6d2787221abc18f9f12e87108330f1c20e79c0979904e7b
|9,0=>0x5f7022ff10040d9019d0
|10,0=>0xfffda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000c0c00000f0f00000c0c00000f0f00000c0c0000000000000000f0f00000c0c00000f0f00000c0c00000f0f00000c0c00000f0f00000c0cf0f00000f0c00000f0f00000f0c00000f0f00000f0c00000f0000000f00f0f00000f0f00000f0f00000f0f00000c0c00000c0c00000c0c00000c0cc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0cf0f00000f0f00000f0f0000000000000f0000000f0000000f0000000000f0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f00000000f0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00f0000000f0000000f0000000f0000000f0000000f0000000f0000000f00f0f00000f0f00000f0f00000f0f00000000000000000000000000000000f0f00000f0f000000000000000000000f0f00000f0f0000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f00f0f00000f0f00000f0f00000c0c00000f0c00000f0c00000f0c00000c0ca0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0af0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000
|0,1=>0xf0f00000f0f00000c0c00000c0c00000f0f00000f0f00000c0c00000c0cf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f000000001010000010100000101000001010000010100000101000001010000000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000cf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000c0c00000c0cf0f00000f0f00000f0f00000f0f0000000000000f0f0000000000000f00f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0af0f00000f0f00000f0000000f0000000f0f00000f0f00000f0000000f0000000000f0f0000000000000f0f0000000000000f0f0000000000000f00f0500000f0500000f0500000f0500000f0500000f0500000f0500000f0030100000301000003010000030100000301000003010000030100000300f0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f0000000000000000f0f0000000000000f0f0000000000000f0f0000000000000c0c00000000000000000000000000000000f0f00000f0f00000f0f00000c0c0000000000000000f0f00000f0f000000000000000000000f0f00000c0ce0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e
|0,2=>0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000c0cf0f00000f0f00000f0f00000f0f00000f0f00000c0c00000f0f00000c0cf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f0010100000101000001010000010100000101000001010000010100000100f0f00000f0f00000f0f0000000000000c0c00000c0c00000c0c00000000303000003030000030300000303000003030000030300000303000003000000000000000000000000000000000000f0000000f0000000f00000000f0f00000f0f00000f0f00000f0f0000000f0000000f0000000f0000000000000000000000000000000000000000f0f00000f0f00000f0f00000f0000f0000000f0000000f0000000f0000000f0000000f0000000f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f000050000000500000005000000050000000500000005000000050000000050500000505000005050000050500000505000005050000050500000000d0d00000d0d00000d0d00000d0d00000d0d00000d0d00000d0d00000c0cf0f00000f0f00000f0f00000f0000000f0f00000f0f00000f0f00000f00f0f00000f0f00000f0f00000c0c00000f0f00000f0f00000f0f00000c0c
|0,3=>0xf0f00000f0f000003030000030300000f0f00000f0f0000030300000000505000005050000010100000101000005050000050500000101000000000000000000000000f0f00000f0f000000000000000000000f0f0000000000000000000000000000000000000000f0f00000c0c00000f0f00000c0c00000000f0f0000000000000f0f0000000000000f0f000000000000000000000000f0f0000000000000f000000000000000f0f0000000000000f0000000000000000003030000030300000000000000000000030300000000f0f00000f0f0000000000000f0f00000f0f00000f0f0000000000000c0cf0f00000f0f00000f0f00000f0000000f0c00000f0c00000f0c00000f0000000000303000000000000030300000000000003030000000000000000f0f0000030300000f0f0000030300000f0f0000030300000f0f0000000050500000505000005050000050500000505000005050000050500000500f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f0f00000f000000000000000000f0f00000f0f000000000000000000000f0f00000f0030300000303000003030000030300000303000003030000030300000000f0f00000f0f00000f0f00000a0a00000e0e00000e0e00000e0e00000a0a
|0,4=>0xf0f0000000000000f00f0f0000000000000f0f0000000000000f0f00000f0f00000f0f00000f00f0f00000f0f00000c0c00000c0c00000f0f0000000000000c0c00000000000000000000000000000000f0f00000000000000000000000000000c0c000000000000000000000000000000000000000000000000f0f00000f00000000000000000000f0000000f00000000000000000000000f00000000f0f00000f0f0000000f0000000f00000f0f00000f0f0000000f0000000000000000f0f0000000000000c0c0000000000000f0f0000000000000c0cf0f00000f0f00000f0f00000f0f0000000000000f0f0000000000000c0c00000000000000000000000000000000f0f00000f0f00000f0f00000000f0000000f0000000f0f00000f0f00000f0000000f0000000f0f00000f00c0c00000f0f00000c0c00000f0f00000c0c00000f0f00000c0c00000c0c50500000505000005050000050500000505000005050000050500000404f0f00000e0e00000f0f00000e0e00000f0f00000e0e00000a0a00000a0a00f0000000f0000000f0000000f0000000f0000000f000000000000000030300000303000003030000030300000303000000000000030300000000
|0,5=>0xf0f0000000000000c0c00f0000000f0000000f0000000f0000000f000000000000000f0000000000000000000000000000000000000000f0f00000f0f00000c0c00000c0cf0f0000000000000f0f0000000000000f0f00000f0f00000f0f00000c0c303000003030000030300000000000003030000030300000303000000000000000000000000f0f00000c0c000000000000000000000f0f00000c0cc0c00000c0c00000c0c00000c0c00000f0f00000f0f00000f0f00000c0c00000000000000000000000000000000f0f00000f0000000f0f00000f000000000000000000f0f00000f00000000000000000000000f0f00000f00f0f00000f0f00000f0f00000f0f000000000000000000000f0f00000f0000f0000000f0000000f000000000000000f0000000f0000000f000000000000000000000000f0f00000f0f000000000000000000000f0000000f00f0f0000000f00000f0f0000000f00000f0f0000000f00000f0f000000005050000000500000505000000050000050500000005000005050000000000000000f0f0000000000000f0f0000000000000c0c0000000000000c0c000000000000000000000000f0f00000000000000000000000000000f00
|_,_=>0
def sP:Nat→Nat
|0=>0x2e143271210c8b009420b4814309081ca850c5020718742840e88e850c84494322c00e3c1ce850c8021038143090e40f930c78207187428e0840e050c503902600294086459a0a0cc8b2e1430932605970c488840e2c0842c1ca850c5068b0214907204c292221039012346010608080
|1=>0x62190140e40f80081d80b000cf18168c3212864c0b0080a07206c291081c81f0cbc9040e402a0125039000b82073a14321322cb850c85384322c009286568816103aa58143143028581281cfab0294219541431112103900c78218102d18e281ce850c4838b024c28432205a80a24c8b
|2=>0x20143113c103900c103950a18f19165c2864250c8b00782072a1432e22243900c1168b48143042c2d3050c1040b4814309081c8380c39b810a18381624c28628083810a1038c3a1430404600861cd43900a1820768a828642cc21916009040e40d85065040b461590432b45862210381
|3=>0x218207168ce850cbc9040e2c0856610c0b020108928205810a24a072030289085838b0a199040e2c0800c804940e2c080086040b02ec1945a2c0800acc184322c00512516980e2c084102c0ba00bc207206c286081c5b40a182074654286081c0aa0a190140e400040e8d5050cbc207
|4=>0x3e04292081c8050c9c4940e2c0852810390367c28e081c5c30a182071708286125038b030420716fdf050c50219302c0047a6440b0a0cf0b0298286405039b1604291081c5810019994086058100b8f040e7c08678243900a1990432205850c0ca07168c28666782191614311081cf8b
|5=>0xe7c6011c2439b3e043038c605810c24a190e2c009081c81b3e181840e055050c3838c024c2865c243900a19989281c5810085384102c0854a0c2191614320081c5c30a190140e7c581000ca0b02982868a10c8b0a182072110286281039036002b3121c581000ca2d302c0851c5039b
|6=>0xe402861cd438b021432708b438b02149040e6c5810a3820702c42863c50218102c09e086040b0284a2d0e2c085081c8470a18909081c581002438b030003c121cf810ccd9040e2c0805e242072014304362c09c0a190a7281c5810ab84940e40286661038b681430312b4c0b0218494
|7=>0xe2c086241039f160401e1210c88161422d0e2d1850c7848432605865e103903e143331250c8b0a18207207dc850c1038c02147cb08645800a197090e7c086401038162143046e2c0850c10c0716064861210381541433312645850c94484322c2865e1038b86143037a645850cb8884
|8=>0x102c08540b8207201430e121c0b10a1819e28605810c1038c9a042a0081c5a30a184945a1c5815e1038162143033c605810c1168b02982865c442073e04309082c09c0a18207142c080081c5ab020100e281c8050c1040b02982864a842191614309081c5817018a07182c0930a95904
|9=>0xa18f042c1c5850cbc2071604286081c85100147090e2d1850c2420716d028608645d00a18894081c8050cbc207168c286126038b025c3113c1038b021819e12645850cc8f040e2c0865c4448716043043e2c09c0a1a7140e2c0850c0c20716d02866610cad1614304322cd050c0cf14
|10=>0xa1819e5a2c0850c7820702a8286121038b481432f081c8050c10b07168c2869610c8b0a1979e081c8050c38f090e30085081c5a36214304322dd000d142181604286081c5b13a14325081c0aa0a182160e2c286081c5d20a184840e2e1850c242072130286420ca1916143033c64580
|11=>0xc1038b0354006081c8480a18219a82c28642cc2071604286067838b0214333062438b021432e221038b021430908b438b0218a0430205810a1038b481431e081c5a40a1820716d02861c7838b461431e081c5b40a1819e322c2863c1038c168c29e081c6016214f043260586081c0aa
|12=>0xa187040e300800acca04322c286061168b02143040e2c0851e19984322c2864a1040716042861250c07160432f081c5810014321061038b020032012103900a182080e2c0a90a182180e2c0970a197840e7c5810a182073e2c0b90a1ab040e2c0850c782190e2c0050c0cf140e2c085
|13=>0x1604286b41038c021432e1c1039f0214320081c58100187040e6c6010a1ac840e2c0850c382073604286b010c0b0214321121038b02003205c1038b0214309081c5816214320081c81f0a187040e400050c10cad102c2864210c98161432508b438b0214314081ea0b021500e281c581
|14=>0x121038b0330286b81038b02143090864c0b0c38a0716040051cf438b0214314081c80b0016304321c5850c11e87202c2863c1168716042865eb8207160428622502071604286281c581b61430908b44071604358121c5810a188840e305810a19914081c5810a1823d0e305810ac8207
|15=>0xa19794081c5810a197840e2c0850c1038b02e42861c7848716042863c24207202c2863c10c87161432f3c1038b021430312645850c784840e305810a0ca08160428432605800c804840e300850c2420736305810cb8a040e2c0800a80f040e2c0850c2420716068050c1038b0324286
|16=>0x2143040e2c0858218207168c2863c1038b4614309281c5810078207182c085081c581a01430e121cf810c24207168c2863c24207168c286081c581be143040e2c0b10a18494321c5850c7820716058850ccca04302c0850c8020720143040e2c0ca0a1871e0e2c0800a18207362c093
|17=>0xc103d41604286401038b0214321121038b021430308645850c116871604286061038b0200286420c2071604286081cd8b0200286081cd9f1604286081c581bc143040e406050c24a0716042865c382071604286b01038b02143040e7c6010a182190e2c0050c0ca071604286061040b
|18=>0x1038b0214304321c5850c104071604286281038b02143040e305810a18f040e2c0850c103dd1604286121038c16042863c24207160428608f438b021430e121c5810a184840e40585
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xd5008500440004
|5,0=>0x183617d61776172516c61675161615b6155614f61496143613e51386133512d61285122611c61166110610a610460fe60f860f350ed60e760e160db60d560cf60c960c360bd60b760b160ac50a750a1609b6095608f60896083607d60776071606b6065605f60596053604d60476041603b6035602f60296023601d601760125
|5,1=>0x19a6194618e61895
|6,0=>0x346633f73396333632c7325731e731773107309730272fc62f572ef62e962e272db72d472ce62c772c072b972b272ab72a4729e62986291728b6284727d7277627072697262725c6256624f72496243623c7235722e72277220721a6213720c720571fe71f771f071ea61e371dd61d671cf71c871c261bb71b471ad71a761a07
|6,1=>0x4f774f074ea64e374dc74d664cf74c874c174ba74b374ac74a5749e7497749074897483647c7475746e74677461645a7454644d7447644074397432742c6426641f74187411740a740373fc73f573ee73e773e073d973d273cb73c563be73b863b173ab63a4739d7397639073897383637c7375736e7367736073597353634c7
|6,2=>0x5b965b275ac65a5759e75986591758a7584657e6577757075697563655c7556654f75487541753b6534752d75267520651a6513750c750574fe7
|7,0=>0x78f8787878077788771776b6764775d7756774f774877408738873087297721871a7712870a870376fc76f576ed86e676de86d776d076c976c186b986b186aa76a3769c7695768d8686767e8677767076697662765c6654864d7645863d8636762e8626861e8616860f760785ff85f875f265ec65e485dd75d585cd85c675bf7
|7,1=>0x87068697863685c7855784f6848784088397832782b7823881b8815680e780687fe87f687ef77e877e087d887d177c987c367bb87b567af67a7879f87978
|8,0=>0x92b7924791c8914890d790678ff78f878f178e988e368dc78d488cc88c488bc88b578af68a878a088997892788b7884787d78767
|9,0=>0x9476940793979327
|10,0=>0x94d6
|_,_=>0
def wAt:=mkWire dB 96 236 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa210a110e190e050a1d12200e190a110c110a2d0c111230161908150e054a2f4219121d08153c0728150c11521910260a11421b0e99029a3c1f281508192c2f0e8d3c0712193c4308010a190e050e2508190a1912190a111219081536130e3d0819003816110c1516190e3d0815003816110a190a19162912200e110e190a11
|1=>0x16050a1908193ee5287f161508190e250a110e050a1908190aba082d0ead123016190815142d12200e190a110c11162912200e150e1908156c11003b0a1906150c0d0e110e050e193c0728150c11081916053e11161556050c15123016190a113c07121908150e05081930110a1d1605087d3e190a2d0c1508191605122d421b
|2=>0x3c0728150c1128150e05281d0c115e173e5116150c113c07281508190c810c82122d0a1106190e110e150c15121d0e190815161916050a110c110e8d3c0712194a173c1d00110a190819122d0c15081500130e190e150c150e010e110a190c150c0d0e110e0530190e1508190c1d0a1930130a1d1605086d002d0a191c151611
|3=>0x8193e1916150c111605401b122d0815421b121d0a110c1116053e1916155e0700390a19023d003816110c150c11001f08150c150b01282f081908190c150e150e050e190e05281708193c1f12190a110819087d3e190a2d5e173c2d00110c150e15281d081916510a511615081908150c3a16111605661708210e190e050e11
|4=>0xa111615161908190a113e190a2d1611081d121b0e1508150a190e050a110c1108153e19161516054a2f06010a19361318150c2d282d16050a110c110e51081908150c15421b121d081542190a0d0e1108193e110a2d3c1f28150c117a1d0a520c110e05762d160500130a190c111605002d0c15081510110e190a1930190e15
|5=>0x16050aba282d08196c11003b16110a19421b301130190e15401b087d3e190a2d5e2f003916110a1928150e1508190e1512190e1908150819301130190e159019087e16151605401b122d08150c15282f0a110c1108150c3a161516116617281d081940191605122d0a11421b121d0815282d16050a110c110e1130190e150815
|6=>0xace0acd281d0819401b3e1116150e190e05121908150e150e051219081540193e1116150e05281d0a110c111c00161116190a190e0506030e110a111615282d08193c2f122d121908150ead123016190815941530520e150c114a2f3c1d12190c0d0a110e110e053c1d0e05121908155e074019122d0815081d0e0528170819
|7=>0xc1116050a391c19082d3c2f12190a110e1528150c11287c1619161508190e010a190a110c1116c53c2f28150819081d28150e1508193c1f001d00110c150aba282d08195e1f3c2d121912200e1908150c150c15123016190a1116051c1516110c114a1f10250e190a1142190e05121d08159815182716190a11086e18150c2d
|8=>0x287f1615081908320a191619160516113c0712190a114a073c1d12190e0510270e190a115c171605282d0c113c07281508195a1330190e155e173c2d00110a19081d0e05121908150ace281d28150c110aba282d0c115e1f287d0819093d30530e150c114a0706010a19101508210e190e050ce90e0530130a1d0e190e112815
|9=>0x3c07121908153c2d08010a1916053c072815081906030e050e110c153c2d08010a190c2516190a113c2f281508190c150e0530130a1d0f2928630e1508193c2f281508194a2f4219121d08153c0728150819034e0905001f0a195e073c2d121916051232161908190a0d0e110e050e0508010e110a190e8d3c07281508193ee5
|10=>0x10170c1d061506190e1112190e110a1106190e110a115c17282d0819001d08150c150e190e1508193c6708010a190e053c6708010a194a074219121d08153c07281508193c1d2815081908010e050e110c153c07281508193c2f121908150e1508010c150e054a2f4219121d0815081d001d00110c154a2f3c1d281508190e8e
|11=>0x1d0a190c1110170c1d0c111c15082d161116190a190e5108190e050e010e110a19003816110c150e05281d081910250e190a110e150c110a113c2d00110c1506150e110c151605122d0a1110260a1108b630190a1d287d16150819287f0819ae190617081d0e0500110c1528150e110c11121f0c150815087e161516050e05
|12=>0x122f0c110a1110150e190815061b0e110a115c17181116196617281d08192817161908196617281d08190a3a161916111c19082d16153e1116150c150a31161116198c2d121b08151611002d0c150e15061b081d121d0c1508150a391c19082d3c2f1219081516053e111615160516110c1510150e190e0508610e150e0508b5
|13=>0x3c2d281508190e050e110a111619121908150e190e110c110c150e150e05122d161908150a3116190a11282d0a190819122d1219081510270e190b79281f08191232161909750c7e161508150e150e050c1516110c11082d2817081916050a1908190c260a110e05160528170819001d00110c155c15282d08190aba282d0819
|14=>0x8190a190a110c1112191619081510270e190a110a11161516113c07121908153c0712190815287e161508193c2f281508190e050a110c113c2f281508190e510e1508191c151611160530520e150819080116110a19086e002d0a193c2d281508194019122d0815287f16150819161112190a1116051219081508010a190e05
|15=>0xe050c1d08191619281508190c7e161516190815121908152817081916110a111605081510170e19122d0815121d0815081d0e05001d0a190e110a190a0d081d002d0a193e190a2d281f0819161916050a110c111c191611061b081d161516190a190e050e110c11081d0e19001f0a193c07281508193c072815
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x198006
|5,0=>0x794000000000007450000731000000000000001b940001a54000191461300005d4000059400000001550505134c49411500000000414000000010043c400003750c942d500002a3000000009cc00009842150750000068c1640508000000012200001110000000000000000000c5
|5,1=>0x7d5
|6,0=>0x57515a3559152453cd4b40001483511000050113c44e113444c112c44a4d26348911e446cd1830001153448d0e442910644090ff33f0cf843d4cf143b8cea43990e3337d0db4360cd443410cd33250c543050bd42e50b542c8cae42a90a7328d0a032710984251091323508a32190824
|6,1=>0x90523d48e523548c8e2e48a92273890e2048712184854e12383920b381d20347fd1fb47e0df537c500007b51e947951e14778ddb375d1d3473d1cb471d1c34700dbc46e4db540001b146b8daa40001a6468cd9f466d197464d1903631188461118045f117845d117045b116935951614
|6,2=>0x2a84a94ea14a78e9b3a5d2943a44e8d4a252854a0527d49e527639c926f39b0e6939952614978e5a495ce534940e4d39252454
|7,0=>0xd94f632d80f5e2d6cf583d54f523d3cf4c3d24f463d0cf403cf4f3a3cdcf343cc4f2e3cacf283c94f223c7cf1c3c64f163c4cf103c34f0a3c1cf043c04efe3becef83bd4ef23bbceec3ba4ee63b8cee03b74eda3b60ad53b48ed02b34eca3b1cec43b04ebe3aeceb83ad4eb23abceac3
|7,1=>0x3c23efcfbc3ee4fb63eccfb03eb4faa3e9cfa43e84f9e3e6cf983e54f923e3cf8c3e24f863e0cf803df4f7a3ddcf743dc4f6e3dacf683
|8,0=>0xfdcbf52fccbf12fbcbed2facbe92f9cbe52f8cbe12f7cbdd2f6cbd92f5cbd52f4cbd12f3cbcd2f2cbc92f1cbc52
|9,0=>0xff07fb1fe87f91
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 14
def pmP:Nat→Nat
|0=>0x461004600044000428004250040d00408004010040000200001600012000100000c9000c800081000800006800060000500004d0004800041000400002800021000200001800005000030000100000
|1=>0x20080200001de901de801ce9014400100800ee900e0100de900cf900ce900ce800cc800c2800c01008c000881008510084100821008200080900801008000069800650004cd004c0004880048300480
|2=>0xcc4808ef908ee908e4808cf908ce908c7808c6908c6808a1808881088000800004ec904cf904ce904cd904841046c00464004600040d8040500400003de903c690390803440034280300802dc802d48
|3=>0x20ce9208412004018ef918ce914ce914cc913ce913c49134281306812de911de911c691100810ef910ee910ed910de910ce910ad9108c11086110821106d810698102d81002010018100080ce480cce9
|4=>0x6004050cc950c69509685010844ec944cf944cd9444d04445844450440d8440d042de942d484204041ce941c4941c2940de940ce94004030c6922de92204021dc921d4821ce9214602140020de920de8
|5=>0x92c6990de990d2890ce9905409010890080900208cc4888ce984ee984e09846c0846488460882d4081d4881ce980ec980ce980cd9808d980881806c0806008008062ce962c6962861624606206860068
|6=>0xd0de9d0ce9d0cc9d0c69d0861d0829d0560d04e9d04c0d0489d0461d0429d00c8d0081d0049c8ce9c0ec9c0148c00c9c0080c0020a2c69a2c61a1de9a1ce9a1c41a1c21a1460a1428a1408a040094811
|7=>0xd80c8
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x203
|5,0=>0x560028000000450016000000001a001b000b530019000d0000042f053f0a00002500003e7d00696a100005000013003e2808002744530000530048000000000021
|6,0=>0x6285f2008804d548a01ba01a70f09051d41d519a6b84f00a328da014b089d9e260629098a0162ce009b28c2005217b401240608857e28af4c10010110cbdb0e5904aa6bc14e0071b100a1c09477364a050c61c44228006364365a95c587495739490f328d0191b0b81118c1235c3a0715100f01c671b70818678e9f8290c92c
|6,1=>0x33142b0f01bd0fcc9c061e010d582a3c55b901400601102a31080843bb
|7,0=>0x34d8dedd7f70d8d13534bed2c45eacd7932d34acd6e0df2e73d3c7926597b31208ac083574cfadd06db61f304d79a272a883ab3452b26e966c98467522cd5e5d88472c89669ac8a4388668bf37767c05a0a90f3bd9d4895b811cdcc3b3a4ca
|8,0=>0xde357ad8ac6f7b7f70783da58f789999ac60bcb53b518cae848b
|9,0=>0x367fac50
|10,0=>0x34
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 20 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_234 9 roots_234 ops++addP pm 1 dom_193 4 roots_193 ops++addP pm 2 dom_97 4 roots_97 ops++addP pm 3 dom_107 8 roots_107 ops++addP pm 4 dom_169 5 roots_169 ops++addP pm 5 dom_227 8 roots_227 ops++addP pm 6 dom_203 8 roots_203 ops++addP pm 7 dom_233 8 roots_233 ops++addP pm 8 dom_226 7 roots_226 ops++addP pm 9 dom_201 5 roots_201 ops++addP pm 10 dom_171 8 roots_171 ops++addP pm 11 dom_225 7 roots_225 ops++addP pm 12 dom_195 5 roots_195 ops++addP pm 13 dom_163 5 roots_163 ops++addP pm 14 dom_105 5 roots_105 ops++addP pm 15 dom_232 7 roots_232 ops++addP pm 16 dom_139 5 roots_139 ops++addP pm 17 dom_99 5 roots_99 ops++addP pm 18 dom_43 5 roots_43 ops++addP pm 19 dom_75 5 roots_75 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_235 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_75 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_234 9 s (0,roots_234.map (·&&&dom_234)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_235 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_234 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xffffffff00000000ffffffff00000000,96)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_235==dom_235)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_235 gM v ys):RunD true dom_235 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_235 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 68 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 68 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 157 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 29 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 157 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 95 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 95 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 26 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 26 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 4 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_235 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_235 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_235 roots_235 goal_235 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_235
theorem lowS_235:Lower true dom_235 roots_235 goal_235 11:=S_235.noCircuit
theorem lowS_238:Lower true dom_238 roots_238 goal_238 10:=lower_slice_b [(0x505000005050000050500000505000005050000050500000505000005050,128,132)] (by decide +kernel) lowS_234
namespace S_245
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,65),(1,129),(4,5),(4,20),(4,132),(16,17),(16,20),(16,144),(32,33),(32,96),(32,160),(36,37),(36,52),(36,100),(36,164),(48,49),(48,52),(48,112),(48,176),(64,65),(64,96),(64,192),(68,69),(68,84),(68,100),(68,196),(80,81),(80,84),(80,112),(80,208),(128,129),(128,132),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_245.map (·&&&dom_245)
def gM:=goal_245&&&dom_245
def NN:Nat→Nat
|4=>12
|5=>45
|6=>161
|7=>122
|8=>28
|9=>6
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x73566673474ea3a2bda21f4271c8101bfaf1a6ec1962a142ed054e501046
|5,0=>0x774a36ec94678bb5f8e3568c552086504024c6ff4905346f3f45326420703f2963efb43e5093e30238ab936aa6341bd33b012e8512c5722c13e27403244ec235a01cafd1bc181a5fe1870f178f21723c14f681490913f7d103460e3ba0cfac0b4460a8c10809d078e3040930160c01578
|6,0=>0x3a8d33a8653a38e39378378c03756e37496366f13466133703332ec32df8321c831e89304682f8072e8942ca372c62f2c4812ae292aa302a88e2a28929dce29dc1299ce298b32951928e6327e91275f126bb324ca02491a244ec243362401823f36233092328e22c0121ab3215012124020fbc20de52013f1e38e1d2af1cad91c7351be3a1ad691ad2519db71960d1941818a4b1881a183e71833c172651706c16c5f15f3b15e0415abd157b614db41498013a98130cc128511127510ac3100250ffde0fe830f99a0f85d0f6400f2fe0edbb0e3540db9d0d1b90cc0f0c6af0c6270bc8f0b9c10b84f0b3740ae7c0a4f70a4810a0e609e2009d2509c4409960097d8096790941308c0a08b4e081ae0784d073f7073340722106b4a064e5064120626205fd505f200498e043f60304e02af80239202363021a901c9d002950014c
|6,1=>0x9e6799129583aef73b9c724c7678476079f604f25fe495a8c45a2d05972858d4e57c4957935571d65682554fb8500954d35e4c6ff4be864bb964af434977e4754f466d644373429a4402063f4423eedd3abd4
|7,0=>0x9b2a27f4ea76ab67353d700717003f6f7696ed2369e696995b67e8566c6b60a155ff1f5e9a2589c156c5254a28539cc4ff2b4d81b4b5544aec1482564449e4100a40dde40a3e402873ddfe3bfb43b6a33b5f43b4513a9423a40e39b4834ca133b52337bb304c5302df2dd592c86b2c62f2c3602b6be2a5132a4af2a35a2a2c72a0fc28ddb2764e267ad25d152531e24e3923b43231a422f70210bb20cae2068b202b41efdd1e9721db471cfd61cfc51ad301a5821a3fb1a2861915317da4160481584215127150f114bdd12d7c110c310fa410d4b104910f4920ee610e3fa0deb50da530d5f10cd5b0c11b0b36f0afce0af740a53509dc1097d808c02087ac07dc8076580669305a8e03df6038ec0377c0344402e6f029bb0265b024d701c3001bc601a390186801051009ac00904006bf
|8,0=>0x6aeef5a6524c2644c05e4ac084188c4126940c0a38e6d3731f3362331ca12abaa269d3234181ddd81d3bf1a52b18800170a114b000b58b0ad740ad4802f1002879020c201a11
|9,0=>0xbf1f18283359b17356de2cd2a07d37
|10,0=>0xbf1f1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc000000033003300330000003300330033000000220022002200000022002200220000cc00cc00cc00cc000000000000000000cc00cc00cc00cc00000000000000033003300330000003300330033000000330033003300000033003300330000cc00cc00cc00cc00cc00cc00cc00cc000000000000000000000000000000033003300330033003300330033003300330022003300220033002200330022c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c22002200220022002200220022002200220022002200220022002200220022cc00cc00cc00cc00cc00cc00cc000000cc00cc00cc00cc00880088008800033003300330033003300330030003000330033002200220033003300200020cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00000000000000033003300330033003300330033003300330033000000000033003300000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc00032003200320032003200320032003200320032003200320032003200320032cc00cc00cc00cc00cc00cc00cc00cc0088008800880088008800880088008b3003300330033003300330030003000330033003300330022002200200020
|0,1=>0xcc00cc00cc00cc00c000c000c000c000cc00cc00cc00cc00c000c000c000c33003300330033003300330033003300330033002200220033003300220022cc00cc00cc00c000cc00cc00cc00c000c800c800c800c000c800c800c800c33003300220022003300330022002200330033002200220033003300220022cc00cc00cc00cc00cc00cc00cc00cc00cc000000cc000000cc000000cc00033003300300030003300330030003000220022002000200022002200200020cc00cc00c000c000cc00cc00c000c000cc00cc00c000c000cc00cc00c000c33003300330033003300330033003300320032003200320032003200320032cc00cc00cc00cc00cc000000cc0000008800880088008800880000008800033003300330033003300000033000000330033003300330033000000330000cc008800cc008800cc008800cc008800cc008800cc008800cc008800cc008b3003300330033003300300033003000320032003200320032003000320030cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc008800880088008b3003300330033003300300033003000330022003300220033002000330020cc00cc00cc00cc00cc00cc00cc00cc00c000c000c000c000c000c000c000c33003300330033002200220022002200330033003300330022002200220022
|0,2=>0x4400440044004400440044004400440044004400440044004000400040004030000000300030003000000030003000300000003000200030000000300020000000000000000cc00cc000c000c000000000000000000cc00cc0008000b300220033002200330022003300220033002200330022000000000000000000000000000000000000cc000000cc0044000000440000004400880044008b30033003300330003000300030003003300330033003300020002000200020c000c000c000c000c000c000c000c000800080008000800080008000800080000000330033000000000003000300000000003300330000000000020002000000000c000c00000000000c000c0000000000080008000000000008000800000000000000033003300030003000000000000000000330033000300020c000c000c000c000c000c000c000c000c0008000c0008000c0008000c0008000330000003300000033000000330000003300000033000000320000003200000000cc00cc0000000000cc00cc0000000000cc00cc000000000088008b300330033003000330033003300300033002200330020003300220033002000000000000000000000000000000000cc00cc00cc00cc00c800c800c800c83000300030003000300030003000300030003000300030002000200020002
|0,3=>0xcc000000cc000000cc000000cc0000008800000088000000880000008800000003300330000000000000033000000000033003300000000000000220c0000000c0000000c000c000c000c000c0000000c0000000c0008000c000800000003300330000000000330033000000000033003300000000003300220000000000000000cc00cc00cc00cc000000000000000000cc00cc00c800c800033000000330000003300000033000000320000003200000032000000320400040004000400040004000400040000000000000000008800880088008b3003300000033003300330000003300330033000000220033003300000022cc000000cc00cc00cc000000cc00cc00cc000000cc008800cc000000cc008b300330033003300330033003300000033003300220022003300330022000000000000000000000000000000000000cc00cc00cc00cc00cc008800cc00880000000000000003300330033003300000000000000000033002200330022cc00cc00cc00cc00c000c000c000c000880088008800880080008000800080000000000000000330033003300330000000000000000003200320032003200000000000000000c000c000c000c000000000000000000080008000800083000300030003000300030003000300030003000300030003000200030002
|0,4=>0xcc00cc00cc008800cc00cc00cc008800cc00cc00cc008800cc00cc00cc00880000000000000000000000000000000330033003300220033003300330022cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00c800c800cc00cc00c800c80000000000000000000000000000000330033003200320033003300320032cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00c000c000cc00cc00c000c11001100110011001100110011001100110011001000100011001100100010cc00cc000c000c00cc00cc000c000c00cc00cc0008000800cc00cc00080008000330000003300000033000000330000003300000022000000330000002244004400440044004400440044004400440044004400440044000000440003300330033003300330033003300330033003300330033003000300030003088008800880088008800880088008800cc00cc00cc00cc00cc008800cc00880000000000000003300330033003300000000000000000033003300220022000000000000000000000000cc00cc000000000000000000000000008800880000000000000000000330000003300000000000000000000002200000022cc00cc00c800c800cc00cc00c800c800cc00cc00c800c800cc00cc00c800cb3003300330033000000330000003300330033003300330000002200000022
|0,5=>0xcc00880000000000cc00880000000000cc00880000000000cc008b3003300030003003300330003000300330033000300020033003300030002cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc008800cc0088300030003000300030003000300030003000300030002000300030003000200000000cc00cc0000000000cc00cc0000000000cc00cc0000000000c800c80000000330033000000000033003300000000003300220000000000330022cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00c800c800c800cb000300033003300300030003300330030003000320032003000300032003200000000cc00cc0000000000cc00cc0000000000c800c80000000000c800c80000000000000001100110011001100000000000000000011000000110000cc00cc00cc00cc004400440044004400cc00cc00cc00cc00440000004400000000000000000000000000000000000000033000000220000003300000022cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc008800cc00cc00cc008830003000300030003000300030003000300030002000200030003000200020000cc000000cc000000cc000000cc000000cc000000c8000000cc000000c80000000330033000000000033003300000000002200220000000000220022
|0,6=>0xcc00cc00cc00cc00cc008800cc008800cc00cc00cc00cc00cc008800cc008800000000000000003000300030003000000000000000000030003000200028800880088008800cc00cc00cc00cc008800880088008800c800c800c800cb3003300330033003300330033003300330033003300330033000000330000c800c800c800c800c800c800c800c800c800c800c800c8000000000000000330022003300220033002200330022003300220000000000330022000000000000000000000000cc00cc00cc00cc0000000000000000008800880088008b30000003300000033003300330033003300000033000000330022003300220000000000000000cc00cc00cc00cc000000000000000000cc00cc00cc008b300330033003300320032003200320033003300330033003200320032003200000000c800c80000000000c800c80000000000c800c80000000000c800c80000000030003000000000003000300000000000300030000000000020002000000000000000000000000000000000c000c00080008000c000c0008000b00030003000300030003000300030003300330032003200330033003200320000cc000000cc000000cc000000cc000000cc000000cc00000088000000891001100110011001100110011001100110011001100000011001100110000
|0,7=>0x4400440044000000440044004400011001100110011001100110011001100110011001100110000000000000000c400c400c400c400c400c400c400c400c400c400c400c400c000c000c000c00000000000000000000000000000000030003000300030002000200020002440044004400440040004000400040004400440044004400400040004000433003300330033003300330033003300110011001100110010001000100010cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc000000cc00cc00cc000000003000000030000000300000003000000020000000200000002000000020000000000000000cc00cc000000cc000000000000000000cc00cc0000008800030000000330000003000000033000000300000003200000030000000328c008c008c008c008c008c008c008c008c008c008c008c00880088008800880000000330033000000000033003300000000003000300000000000300030000000000000cc00000000000000cc0000000000000088000000000000008b00030003000300033003300330033003000300030003000320032003200320000c0000000c0000000cc000000cc000000c0000000c0000000c8000000cb3003300220022003300330022002200300030002000200030003000200020
|0,8=>0xcc00cc00cc000000cc00cc00cc00031003100310031003100310031003100310031003000300031003100300030440044004400440044004400440044004400440000000000440044000000000000000000000000000000000000000320032003200320032003200320032cc00cc00cc00cc00cc00cc00cc00cc000c000c00080008000c000c00080008000330000002200000033000000220000003300000022000000330000002200000000000000000000000000000000cc00cc00cc00cc0088008800880088300030002000200030003000200020003000300020002000300030002000200000000440044000000000044004400000000004000400000000000400040000000011001100000000001100110000000000110000000000000011000000000000000000000000000000000000cc008800cc008800cc008800cc00880000000000000000000000000000000330033003000300033003300300030cc00cc00cc00cc00cc00cc00cc00cc0000000000cc00880000000000cc00880000000000000000000000000000000330033003300330033000000330000440044004000400044004400400040004400440040004000440044004000403000300030003000300030003000300030003000000000003000300000000
|0,9=>0xcc00cc0000000000cc00cc0000000000cc00000000000000cc00011001100110011001100110011001100100010001000100010001000100010
|_,_=>0
def sP:Nat→Nat
|0=>0x9082b0d0b0f1b09101706031101080d0403090807031808280d0b1c031101270d0f0a1d080d0b0f15140d0b260f0308250b090824230d0b1e2209080d0b0f032108200d0f1218100b1e1b090807040a1d080d0f151401050f0a1408051c1b09010704031808000f1514130b0f12111001040a09080706030201050403020100
|1=>0x81a0d0f0310012505360a09080d0b0f2218080d0b0f35340309080f15090117050f0321320908060309100b0f033208200b0f03111001310f120910010b0f0a090817050f150913170b0f0308300d0b0f2202010d0b0f0321092f0d040301082e0d1c040301250d1e15090e0d0b2d0f031101080f151d010d0b0f1609012c0f
|2=>0x910010f1b090108170d2d0f030908290b0f450309010d0b1e44030908430b41190f0311010d0f0a09080e0d0b0f150908420d0b413b0f0309080b2d0f0302080b09083a230d0b0a09083e0d0b0f0310013d0b2d0f0302010b0308303c0d0b1c030901000b0f0908240d0b3b0f09083a0b0f030901390d383709080d0b1e0311
|3=>0xd0b0f03091008550b530f0309080d0b0f1108293a0d0b0f03021a0d0b0f09083a500d0b190f0308520d0b4b1c031109010d040f0908510d0b1c1b030901500d4e1c040309080d4c0f031809080d0f030201200d0b0f031109014a0d19490309080d0b0f030910330b0f150901480d0b0f0a0309470d0b0f031d080d0b0f0346
|4=>0x1101080d5e0f0308250d0b0f030910013f050f0318091001050f1b0308300d0b0f0910013a0d0b0f0a03085c0d0b4b0f0309014a0d4b1c03094a0d0b380f0a09080d0b0415030901500d4f0f0308250d0b031109085b0d0b4f0309085a0d0b1c0309011a0d0b0f031f08200d0b1c035809080d0b0f031808310d0b4103090857
|5=>0x309010d0f151b0913010d0f68030913080b0f036621090805671c0f0309080b0f03661f11010d0f1509170d0b0f031101650d0c041509010d03090823640d0b620f0311080d0b0f1b0908610d0b0f0309100129051c0f0309600d0b0f5909083a0d0b0f1b09015f0d0f030208310d0b1603090823050b0c1c1b09010d490f03
|6=>0xd1e0f0308250d0b0a030908230d0b1e0309085a0d0b1c030901270d0b440f0309086e0b0f0308255a0d0b0f031f1308200b1e0f0908510d0b0f036d09100d0b6c030908230d0b0f156c1609010d0f03211f11080d4c0f030211080d1c44030908500b3b190f0309080b0f031f086b0b380f1509010d0b0f031f1008200b0f6a
|7=>0x670f150309080b0f0366091001050f6f6c0309010d1c0309010e0d0b0f161b091301080f6803090108050f150908480d0b0f0309082a310b03090820230d0b0f0308300d0b4f0f0309600d0b0f35151b09080d0f150309600d0b0f030908000b06030901080d0b0f681609080d0b0f031808200d0b040309081a0d0f1b09080e
|8=>0x9085a0d0b0f1509013f050d190f18083a0d0b0f156c09470d0b0f03660211010d0f6f15030901054c0f030901080d0f6c030910010f030201740d19031108570d0b0f0302462f0d0b0f030908730d0b0f16030910470b0f090108710d0b534e0f0309080d0f03090831050b0f151608250d0b4f670f0309080b0f030970010d
|9=>0x270d0f03321f11080b0f34030910010b0f0908760d0b0c1e1509010d0b0f580908760d0b0f0901083a050d1e44030908500b0f6f1b0910010d0f156c1b09010d0f150901730d0b0c1e0a09080d0b410f0311010d0f03592109080d0f030209750d0b190f02083a0d0b0f035908200d0b0c0f0a08250d0b0f03210910010d0c0a
|10=>0x35808290d0b0f031d01080d0b0f03091308310b0f03661110010d0f5d340309080b0f035808270d0b030901083c0d0b4d0f0908510d0b1c030901730d0b0f0366092f0d0b5d0309083c0d0b0f031f11130108770f0309080b191c0308520d0b1e0309081a0d0b670c0f0309080b0f037208290d0b0f0908240d0b0f03110108
|11=>0xd0b0f03090108740d0f03720901080d0b0f03090108800d0f1603091301080b0f03180208290d0b1c030908800d0b0f0309087f0d0b0f037d09080d0b0f031109087c0d0b0f5d150309080d0b0f032109080d0b0f034609082f0d0b0f0309087a0d0b790f030901080d0f5d0308250d0b0309082a280d0b0f150825780d0b0f
|12=>0x8500d0b0f0a6c0309080d0b0f03181f01080d0b1c0f0a0309010d0b0f1603091310080b0f03090869420d0b0f150308250d0b0f03091008690b0f6f1b09080d0b530f0309080d0b0f0a340309080d0b0f0a09083f0d0b0f030908540d0b530c0f0309080d0b0f03020901050d380f0309080d0b0f031f1110080b0f68030908
|13=>0xd0b0f03020908570d0b0f03321109080d0b0f030901085a0d0b0f161b0901080d0f1509013f0d0b41190f0309010d0b0f030908830d0b0f5d1b0309080d0b411c0f0309010d0b0f6f03091008050b0f158209080d0b0f0309083f420d0b0f031108810d0b414b0f0309080d0b0f031f090108050c1e040309080d0b0f035809
|14=>0x690d0b0f0901083a0d0b0f0311091301080d0f031109082f0d0b0f450309080d0b0f0309010869050f030901880d0b190f0302010d0b0f0346110901080d1c0f030908870d0b0f03661f0908050b0f030908860d0b0f851609080d0b0f0302461f080d0b0f6f030910010d0b4104030209080d0b4b0f0302080d0b841c030908
|15=>0xb0f03024608050d0b0f5d6f0309080d0b4d0f031809080d0b040f03090108290d0f030908730d0b4c0f030209080d0b1c0f1b0309010d1e1c440f0309080b0c0f030908730d0b0f036611080d0b0f0309088b0d0b040f030901083f0d0f03090847050d0b0f03180108290d0b0f0309018a0d0b0f16030989080b0f03020901
|16=>0x4b1c031109080d0b0f03460910080b4f0f0a0309080d0b0f6f030913080d0b0f030908693f0d0b0f03180908690d0b0f0309082a290d0b0f0366020908050b190309088d0d0b190f0318080d0b0f038c1f080d0b0f03090108420d0b0f03090108610d0b0f03181f11080d0b0c1e0309080d0b0f6c16030910080b0f0308250d
|17=>0x30901087f0d0b0c04030901080d0f030970080d0b0f0366091008050b0f6f160309010d0b1e440f0309080b0f03590209080d0b0f0a151609080d0b0f340309080d0b4d0f030901080d0b1e0f0a0309080d0b0f031108650d0b0f03180908500d0b0f1b09085f0d0b410f0309010d0b0f0a030108250d0b0f030901081a0d0b
|18=>0x1109080d0b1e0f030901080d0b0f030908900d0b8f0f0309080d0b0f030910010d0b0f0309085f0d0b0f03091008050b0c1c0309080d0b0f030908810d0b0f0309083f0d0b0f031809080d0b0c0f1b09080d0b0f151b09010d0f156c1b09080d0b0f03596609080d0b190f0309084a0d0b0f038e09080d0b0f030908170d0b0f
|19=>0x9080d0b0f03090108690d0b4f1c0f0309080d0b0f03090108050d0f6c1b0309080d0b0f03180209080d0b0f030908880d0b190f0302080d0b0f0a150309080d0b4b040f0309080d0b0f034609080d0b0f030908910d0b411c0f0309080d0b0c0f030901080d0b0f6c160309080d0b0f0309080d7e0b0f036609080d0b1c0f03
|20=>0xf0309080d0b0f0309080d0b0f160309080d0b0f031109080d0b0f030910080d0b0f030901080d0b0f0302
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x375032502d50285023501e50195014500f500a500550005
|5,0=>0x13f61396133612d61276121611b6115610f6109610360fd60f760f160eb60e560df60d960d450ce60c860c260bc60b660b060aa60a4609e60986092608c60866081507b60765070606b5065605f60596054504e60486042603c6
|6,0=>0x2f572ee72e772e072d972d362cd62c762c072b972b272ab72a4729d7297629072897283627c7275726e7267726072597252724b7244723d7236722f72287221721a7213720c720571fe71f771f071e971e361dc71d571ce71c771c071b971b271ab71a4719d7197619071897183617d6176716f71687161715a7153714c71457
|6,1=>0x4ac64a5749e7497749074897482747b7474746d7466745f74587451744b6445643e7437743074297422741b7414740d7406740063f973f273eb73e473dd73d673cf73c873c173bb63b473ad73a673a063997392738b7385637f63787371736a7363735c7355734e7347734073397332732b7324731d731673106309730272fc6
|6,2=>0x58f75887581757a7573756c7565755e7557755075497542753b7534752d7527652075197512750b750564fe74f774f074ea64e374dc74d574ce74c774c074b974b27
|7,0=>0x76e8766875f77587751774a7742873a8732872b7724771c8714870c870576fe76f686ee86e686df76d876d086c976c186b986b186aa76a2869b7693868c7684867c8674866c8664865c8654864d7646763f7638763086297622761a8613760c760575fe75f775ef85e875e085d885d175ca75c375bb85b385ac75a4859d75967
|7,1=>0x927691f8917890f8908790178f988f278eb78e388db88d478cc88c488bd78b588ad88a6789e889778907888888088788871786988618859885188498841883a7833782c7824881c8814880d780587ff67f787ef87e787df87d877d087c977c187b987b277ab77a3879b8793878c7785777d87767
|8,0=>0x9f489ec89e579dd89d589ce79c779bf89b789b079a979a189998991898a7983797b8973896c7965795e7957795079497942793b7934792d7
|9,0=>0xa1f6a187a117a0a7a0379fc7
|10,0=>0xa256
|_,_=>0
def wAt:=mkWire dB 146 246 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xf0b4040d080b43004030842c210308424390c0102c210d03454140d0b45804080d40c2d030d42c210f0b434390c0100c3d080b4a83f0d294202d0b0840c05090e43004030f4202d09174580403084340d080b40c6919010202d0d0847c04080b43004030b4202d0f0b43004080b458040d0b4202d0d1a464040f0b4202d091745804030842c210f0b438350c010202d
|1=>0x80b44435080b4242d0d0845804030b40c350b0845807030d5103f0d1e8043d080b46421090f42c21030143004030f4202d033482837150b5003f3f0d4202d0f0846835190102c2119010242d080b4242a01034202d0d0b45c3d16010202d1a0346404090143c25080b43ccd080d47c04090d4202d080b4342d16010202d16010202d03084680d19010202d09084242a
|2=>0xd094202d3209c603701094202d0f024603f020b43559101b80c2d1b544706f030b43c2103188602711084242d090846404090f4202d4d09c6405090f4202d080f4443d090b40d364b08424110f0180c2d4f0bc0c710f085342f180f404250913804350b0852c23110f4242d0f2746406090f4202d080d47c04090d4202d031e83c050b084346d030b424390c0100c3d
|3=>0x4f0b4700d031880425080b4543f0b0840c21030b4607f090d4082d130fc14210d034342d080f40c2d0b0840427090a8040d080b434210d0b4040f080b434210d0b40425080b574270a0d46c211803c24050d0842c215309c283d01034202d4b08c24110f0b52c23090443c2d0f3f4202d010fc0c210f5991821110d4283f150b43c5519010202d090f43c215909c7c05
|4=>0xd0347c210d095042f0f02424211e0fc347a1c0b5343719014202d0d094140809084342d0103c402d0d08454100b0840c210f0b40435080b40c2d03085a40d080b5982f0910434210d5393c2d1c0347c21090d4202d030845804030d42c21090b43c0a090842c210f0b4202d030843c4e010d4202d096347047090b43c215d03c28351b0840c2d09018202d0d0b43421
|5=>0x5303d3c2d150f434c51f0183425080b4302d030f5bc2f150d40c210a0f4542d0d1a46404090f4202d330f47c04090d4202d034245806030d4202d5909c603501094202d0f0b46404090f4202d0c0100c2d0f0342c210a09c0c05080b44c3f010d4202d0a0fc3c0501034202d19018202d090f4347a010f4202d1309c3405080b5340f1e094202d10118242d080b4582d
|6=>0x30b4242d0b084083509084342d0d1540c214d0bc6405090f4582d080b40c350d08424210b0843c46090b44421090b5182309054342d160b40c350372825a5010dc202d4e0b53c2f031c47c4e0508434250d0b428270d034542d03084202d1c110242d0f084354e0a0f4542d080b424410d084342d160b45821030d42c210c0103c21030f4202d030b43405080b40437
|7=>0x10fc202d0f0140c210b0854025010fc202d03188342d01094202d1e0fc347a010f4202d100340c2d0d0846c35080b40c2d030843006030f4202d030143c05080b46421090b4243d0b085982d660bc24410502c342d03188243d020b424215909c7c05090d4202d030f4242a01034202d660bc24410d084283f01034202d0d0b4040f090f40c6201094202d6c08c346d
|8=>0x90e43004030f4202d1f0183405080b42441090b434210a0d4283701034202d095094025010fc202d5d0fc5805030d5340f19014243d080b43cfe030182c211f0b424355d0fc5805030d4202d0d014242d080b4e0370f3f4040f080b4702d0f08464040f014243d080b54c370c014202d0901825a5010dc202d190183c25080b44421090b42837010342c215803d4025
|9=>0xf3f4040f080b4242d090d43421690340437080b4202d110fc242d096940437080b42c21090483c2d0d0140c35080b46027020b424210f08424120f0b43007030f4202d7e09414230d0b440470d0842835150b40c21660bc24410d085182309054342d7b0b47c23090d4302d030f4202d090a8040d080b434a50109c202d03258242a150b40c2127094a43f0109c202d
|10=>0x91c43c210310434210d0b40c21160bc0c350103c202d090b46423090f46421190b4243d0d0b43425080b410210f0343c2d010fc202d1b084346d030b42405090d4202d030143c210b0840c35100b43421010dc202d090a8542d030844c37100b434210d1540c2d030843005030f4202d0a0dc040d080b4040d0103c202d1c1bc0c2d0f0843005080b42c2109084342d
|11=>0x30d4342d010dc202d091c83c210b084202d0f0942421080b44435090b47046090b47c210d094342d1c1b80c2d0f084542f0d0340c211f0b43425090840c410d0842c21020f43c2d090843c45090b42421190bc243d0f084603f020b42421180dc4421090b4283f01034202d030b40c350b084200d0103c202d19084243d080b42d7d150fc0c216c084346d030b42c21
|12=>0x90a8040d080b4242109054342d6f0b40c410d084603d01094202d0f0b40427080b43006030f4202d410bc3c09090840c2d0f0842c210d1e8702d0f0843006080b43409090b42421880b424720f0840c060f0b4202d6c08c0c150d0b4a4250109c202d080b40c720f084402f030d434210908404370b084600f01094202d090b40435080b51823110d4242d82084582f
|13=>0x80b43c0a090b424210f018202d030b4543f03084202d091c43c210a09c040d080b46404090f4202d080f4443d090b47c2d090d43421150f4542d030840c41100b43421030180437080b40437080b40427080b4342d020d42421090f410230f0b4082d0f0942421090d4082f090845806030d4202d1303c0435080b4243511084242d0f0143c0d080b42035160b40c35
|14=>0xb0843c5603084342d0d0840c3d0f0846423090f4040f080b40425080b40c3d030b4202d030b40c21030846c35030b5982d1f08424354b08c642d090f426350408c3c2d160100c35080b43007030f43c2d030f42c211c110242d0f08424410d084342d160840c350b084347a010f4202d660b4083509084340d150b40c210a0dc040d080b46405090f4202d03014043d
|15=>0x30d4242d0d084202d090840437080b4700d0f084342d080b46c35030b4082d0908424720f0843c2509084542d0308424110f0b47c2d090d46c3f030b424710f0840c3d080b4582d030d414230d0b424410d084242d0f084043d080b44423090b4302f030f43421
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x54c12303cc000030c000021004400000040000000
|5,0=>0x6430000000000060400000000000000174c594158c515000000000004c500004b10000483114c000105000000003d40e8c0000d9033300002e50000295098c25108141b50000000060c000
|6,0=>0x4951232480d1d3468d16444910f3430d08441110043f88fb33dd0f433c10ed33b04e933950e14378cda43590d33340cce23308000324cc633090be40000ba42dccb432c10ac42a100002910a13278c9c2264c96324cc9032310884214c8321fd07b41dd00001d487141b8c6a419cc000
|6,1=>0x77d1dc37689d647491ce472cdc837189c246fcdbb46e0db536c51ad46ac9a830001a6268919f366d19740001934640d8c46211844604d8015f4d79400000005dc97435c896e45a9166458915e45691573550d504534d4a30001473510d42200013f34f493a34dcd3434c112f14b49294
|6,2=>0x24b3920e44490123c48e4e3638c922e48ace274890e22287921b385d215284520e3829000081ce052808dfe47ecdf837d11f047b4de94798de33
|7,0=>0xc14f023bfcefc3be4ef63bccef12bb8eeb3ba0ee53b88edf3b70ed93b58ed33b40ecd3b28ec73b10ec13af8ebb3ae0eb62acceb03ab4eaa3aa0aa53a88e9f3a70e9a2a5ce943a44e8e3a2ce883a14e832a00e7d39e8e7739d0e7139b8e6b39a0e653988e5f3974a5a395ce543944e4e3
|7,1=>0xeb8fab3ea0fa53e88f9f3e74b9a3e5cf943e44f8e3e2cf883e14f823dfcf7c3de8b773dd0f713db8f6b3da0f653d88f5f3d74b5b2d60f553d48f4f3d30f493d18f433d00f3d3ce8f373cd0f313cb8f2b3ca0f253c8cb203c74f1a3c5cf143c44f0e3c2cf083
|8,0=>0xf9cbe52f8cbe12f7cbdd2f6cbd92f5cbd52f4cbd12f3cbcd2f2cbc92f1cbc52f0cbc12efcbbd2eecbb92edcbb52eccbb12
|9,0=>0x3ed1fb07eb1fa87e91
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x1000001dc000388000610000c00001440002800004a00008a000110000210000410000800000cc000140000260000400000580000a800014000024000044000080000090000100000180000280000400000600000800000800000
|1=>0x540000a0c001410002800004c2000904001188002300004400008100010100020100040000050800090000107000202000400000708000e000016e0002c4000528000a10001400002580004880009000010c00021000041800081
|2=>0x640800c804018528022f70043ee008004010000012f70022ee0045c4008420010800020020040000077b800eb7001d4e002bdc005508008870010400020040037b800600000946001004001fb8002ff0005ee000bd4001688002a1
|3=>0x2480c0483dc08b7b8112f70205ee0400800800080c2ff011d4e023a8004650808af7010840020bdc0417780823501010c020100031fb80617700c2a2018184030008052f700a0ee010bdc020bb8040410065ee00cbd401978803221
|4=>0x822c21044d8208988403f70806ee100bfc2017b8402290802401000a0200100320b706200c0c0bdc1815b82249704216e082adc10540820801040dee081bcc103788206230409820812dc102590204910408c6080bdc10020820000
|5=>0x10845221013c420048802f71005de2009244011288008410008820001c2417f84826f0904d21208a42403484802008c0ae1141d82217b8442f30885e211090c2211184407708808611008c220018422f70840ee104fdc208bb841170
|6=>0x4000044001e2400ac4601338a0af7141502282884504508a08871105ee220a144414088824511014a210bfc42137884249
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x20402000200020400020000
|5,0=>0x20000001300000000043402030000002c0007000204000900000a04000946004c0014022e033800000400
|6,0=>0x9e01010a0319950b01244ab37301c8ae0908000134011b34001e01b32825b88001050000014b01cf3a21035b910402052f1300160401008c0f3153139852132bc60411019650af7f1314203b01d090012793590c40aa1f3719692f020f0013011a140035010106649b00146909017a016e5a17715401cebe3f00015f97210100
|6,1=>0xd00981a52516b00503012279010bb72d130d1fa50031334839551f345e73cb7926
|7,0=>0x8bca106a5c4e017e43b17561b688433026a83286a1871e6bc112293c1836b2a4ad9a4dc5a963c942c0100e1d43568f601fb4582a8da78f743babc4ba4eb9679bc001b18251bf769d6c571d3a848e479f496fa0754f33651cbb5d153eaa85c31f897077433d835823cd43784367aaa3c6a6a37bbc13b643bd4494
|8,0=>0x427dbcccac589c8a6dc282a27bccbcb56862667b7249c77c4543ad92
|9,0=>0x414e66724399
|10,0=>0x43
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_244 8 roots_244 ops++addP pm 1 dom_225 7 roots_225 ops++addP pm 2 dom_149 7 roots_149 ops++addP pm 3 dom_177 5 roots_177 ops++addP pm 4 dom_213 8 roots_213 ops++addP pm 5 dom_117 8 roots_117 ops++addP pm 6 dom_241 8 roots_241 ops++addP pm 7 dom_229 8 roots_229 ops++addP pm 8 dom_209 5 roots_209 ops++addP pm 9 dom_181 8 roots_181 ops++addP pm 10 dom_228 5 roots_228 ops++addP pm 11 dom_165 5 roots_165 ops++addP pm 12 dom_212 5 roots_212 ops++addP pm 13 dom_85 5 roots_85 ops++addP pm 14 dom_113 5 roots_113 ops++addP pm 15 dom_180 5 roots_180 ops++addP pm 16 dom_197 5 roots_197 ops++addP pm 17 dom_101 5 roots_101 ops++addP pm 18 dom_240 5 roots_240 ops++addP pm 19 dom_53 5 roots_53 ops++addP pm 20 dom_193 4 roots_193 ops++addP pm 21 dom_145 4 roots_145 ops++addP pm 22 dom_161 4 roots_161 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_245 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_145 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_161 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_244 8 s (0,roots_244.map (·&&&dom_244)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_245 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_244 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_245==dom_245)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_245 gM v ys):RunD true dom_245 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_245 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 12 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 45 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 161 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 33 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 161 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 122 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 122 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 28 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 28 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 6 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_245 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_245 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_245 roots_245 goal_245 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_245
theorem lowS_245:Lower true dom_245 roots_245 goal_245 11:=S_245.noCircuit
def isoMvS_95:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_95:Lower true dom_95 roots_95 goal_95 10:=lower_iso_b isoMvS_95 (by decide +kernel) lowS_63
def isoMvS_123:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_123:Lower true dom_123 roots_123 goal_123 10:=lower_iso_b isoMvS_123 (by decide +kernel) lowS_111
def isoMvS_125:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_125:Lower true dom_125 roots_125 goal_125 10:=lower_iso_b isoMvS_125 (by decide +kernel) lowS_119
def isoMvS_183:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 10:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_175
def isoMvS_187:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 10:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_175
def isoMvS_189:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 10:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_175
def isoMvS_190:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 10:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_159
def isoMvS_222:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 10:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_159
def isoMvS_237:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 10:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_231
def isoMvS_243:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 10:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_231
def isoMvS_246:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_159
def isoMvS_249:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_231
def isoMvS_250:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_238
def isoMvS_252:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 10:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_159
namespace S_127
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,65),(2,10),(2,34),(2,66),(3,7),(3,11),(3,19),(3,35),(3,67),(4,5),(4,20),(6,7),(6,14),(6,22),(6,38),(6,70),(8,10),(8,40),(8,72),(9,11),(9,13),(9,25),(9,41),(9,73),(12,13),(12,14),(12,28),(12,44),(12,76),(16,17),(16,20),(18,19),(18,22),(18,26),(18,50),(18,82),(24,25),(24,26),(24,28),(24,56),(24,88),(32,33),(32,34),(32,40),(32,96),(36,37),(36,38),(36,44),(36,52),(36,100),(48,49),(48,50),(48,52),(48,56),(48,112),(64,65),(64,66),(64,72),(64,96),(68,69),(68,70),(68,76),(68,84),(68,100),(80,81),(80,82),(80,84),(80,88),(80,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|11,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ac688
|_=>0
def sO:Nat→Nat→Nat
|11,0=>7
|_,_=>0
def wAt:=mkWire dB 7 128 0xffffffffffffffffffffffffffffffff
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
addP pm 0 dom_125 10 roots_125 ops++addP pm 1 dom_63 10 roots_63 ops++addP pm 2 dom_123 10 roots_123 ops++addP pm 3 dom_119 10 roots_119 ops++addP pm 4 dom_111 10 roots_111 ops++addP pm 5 dom_95 10 roots_95 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_95 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_125 10 s (0,roots_125.map (·&&&dom_125)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_125 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_127 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_189_2:=0xcccccccccccccccc0000000000000000cccccccccccccccc
def gzo_189_2:=0xcccccccccccccccc0000000000000000ccccccccccc8cc80
def gsh_189_2:=0x333333333333333300000000000000003333333333323320
theorem lowS_zo_189_2_21:Lower true dzo_189_2 roots_189 gzo_189_2 7:=lower_iso_b (d1:=dom_189) (r1:=roots_189) (T1:=gsh_189_2) [(dom_189,2)] (by decide +kernel) (lower_slice_b (T:=gsh_189_2) [(0x330033003300330000000000000000003300330033003300,0,8),(0x333333330000000000000000000000003333333300000000,0,32),(0x333333333333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
def dzo_187_4:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0
def gzo_187_4:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0e0f0f0e0a0
def gsh_187_4:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0e0f0f0e0a
theorem lowS_zo_187_4_42:Lower true dzo_187_4 roots_187 gzo_187_4 7:=lower_iso_b (d1:=dom_187) (r1:=roots_187) (T1:=gsh_187_4) [(dom_187,4)] (by decide +kernel) (lower_slice_b (T:=gsh_187_4) [(0xa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0000,0,16),(0xf0f0f0f0f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_175_16:=0xffff0000ffff00000000000000000000ffff0000ffff0000
def gzo_175_16:=0xffff0000ffff00000000000000000000fffe0000fefa0000
def gsh_175_16:=0xffff0000ffff00000000000000000000fffe0000fefa
theorem lowS_zo_175_16_42:Lower true dzo_175_16 roots_175 gzo_175_16 7:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_16) [(dom_175,16)] (by decide +kernel) (lower_slice_b (T:=gsh_175_16) [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0,0,4),(0xffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_43_16:=0xf0f00000f0f0000
def gzo_43_16:=0xf0e00000e0a0000
def gsh_43_16:=0xf0e00000e0a
theorem lowS_zo_43_16_42:Lower true dzo_43_16 roots_43 gzo_43_16 5:=lower_iso_b (d1:=dom_43) (r1:=roots_43) (T1:=gsh_43_16) [(dom_43,16)] (by decide +kernel) (lower_slice_b (T:=gsh_43_16) [(0xa0a00000a0a,0,1)] (by decide +kernel) lowS_42)
def dzo_183_8:=0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00
def gzo_183_8:=0xff00ff00ff00ff000000000000000000ff00ff00fe00ec00
def gsh_183_8:=0xff00ff00ff00ff000000000000000000ff00ff00fe00ec
theorem lowS_zo_183_8_21:Lower true dzo_183_8 roots_183 gzo_183_8 7:=lower_iso_b (d1:=dom_183) (r1:=roots_183) (T1:=gsh_183_8) [(dom_183,8)] (by decide +kernel) (lower_slice_b (T:=gsh_183_8) [(0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc,0,2),(0xff00ff00000000000000000000000000ff00ff00000000,0,32),(0xff00ff00ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
def dzo_174_16:=0x555500005555000000000000000000005555000055550000
def gzo_174_16:=0x555500005555000000000000000000005554000054500000
def gsh_174_16:=0x55550000555500000000000000000000555400005450
theorem lowS_zo_174_16_42:Lower true dzo_174_16 roots_174 gzo_174_16 6:=lower_iso_b (d1:=dom_174) (r1:=roots_174) (T1:=gsh_174_16) [(dom_174,16)] (by decide +kernel) (lower_slice_b (T:=gsh_174_16) [(0x50500000505000000000000000000000505000005050,0,4),(0x55550000555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_186_4:=0x505050505050505000000000000000005050505050505050
def gzo_186_4:=0x505050505050505000000000000000005050504050504000
def gsh_186_4:=0x50505050505050500000000000000000505050405050400
theorem lowS_zo_186_4_42:Lower true dzo_186_4 roots_186 gzo_186_4 6:=lower_iso_b (d1:=dom_186) (r1:=roots_186) (T1:=gsh_186_4) [(dom_186,4)] (by decide +kernel) (lower_slice_b (T:=gsh_186_4) [(0x50500000505000000000000000000000505000005050000,0,16),(0x50505050505050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_171_16:=0xf0f00000f0f000000000000000000000f0f00000f0f0000
def gzo_171_16:=0xf0f00000f0f000000000000000000000f0e00000e0a0000
def gsh_171_16:=0xf0f00000f0f000000000000000000000f0e00000e0a
theorem lowS_zo_171_16_42:Lower true dzo_171_16 roots_171 gzo_171_16 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_16) [(dom_171,16)] (by decide +kernel) (lower_slice_b (T:=gsh_171_16) [(0xa0a00000a0a000000000000000000000a0a00000a0a,0,1),(0xf0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_170_4:=0x50500000505000000000000000000000505000005050
def gzo_170_4:=0x50500000505000000000000000000000504000004000
def gsh_170_4:=0x5050000050500000000000000000000050400000400
theorem lowS_zo_170_4_42:Lower true dzo_170_4 roots_170 gzo_170_4 5:=lower_iso_b (d1:=dom_170) (r1:=roots_170) (T1:=gsh_170_4) [(dom_170,4)] (by decide +kernel) (lower_slice_b (T:=gsh_170_4) [(0x5050000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_181_2:=0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc
def gzo_181_2:=0xcc00cc00cc00cc000000000000000000cc00cc00c80080
def gsh_181_2:=0x3300330033003300000000000000000033003300320020
theorem lowS_zo_181_2_21:Lower true dzo_181_2 roots_181 gzo_181_2 6:=lower_iso_b (d1:=dom_181) (r1:=roots_181) (T1:=gsh_181_2) [(dom_181,2)] (by decide +kernel) (lower_slice_b (T:=gsh_181_2) [(0x3300330000000000000000000000000033003300000000,0,32),(0x3300330033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
def dzo_170_16:=0x50500000505000000000000000000000505000005050000
def gzo_170_16:=0x50500000505000000000000000000000504000004000000
def gsh_170_16:=0x5050000050500000000000000000000050400000400
theorem lowS_zo_170_16_42:Lower true dzo_170_16 roots_170 gzo_170_16 5:=lower_iso_b (d1:=dom_170) (r1:=roots_170) (T1:=gsh_170_16) [(dom_170,16)] (by decide +kernel) (lower_slice_b (T:=gsh_170_16) [(0x5050000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_157_2:=0xcccccccc000000000000000000000000cccccccc
def gzo_157_2:=0xcccccccc000000000000000000000000ccc8cc80
def gsh_157_2:=0x3333333300000000000000000000000033323320
theorem lowS_zo_157_2_21:Lower true dzo_157_2 roots_157 gzo_157_2 6:=lower_iso_b (d1:=dom_157) (r1:=roots_157) (T1:=gsh_157_2) [(dom_157,2)] (by decide +kernel) (lower_slice_b (T:=gsh_157_2) [(0x3300330000000000000000000000000033003300,0,8),(0x3333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
def dzo_151_8:=0xff00ff00000000000000000000000000ff00ff00
def gzo_151_8:=0xff00ff00000000000000000000000000fe00ec00
def gsh_151_8:=0xff00ff00000000000000000000000000fe00ec
theorem lowS_zo_151_8_21:Lower true dzo_151_8 roots_151 gzo_151_8 6:=lower_iso_b (d1:=dom_151) (r1:=roots_151) (T1:=gsh_151_8) [(dom_151,8)] (by decide +kernel) (lower_slice_b (T:=gsh_151_8) [(0xcc00cc00000000000000000000000000cc00cc,0,2),(0xff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
def dzo_171_4:=0xf0f00000f0f000000000000000000000f0f00000f0f0
def gzo_171_4:=0xf0f00000f0f000000000000000000000f0e00000e0a0
def gsh_171_4:=0xf0f00000f0f000000000000000000000f0e00000e0a
theorem lowS_zo_171_4_42:Lower true dzo_171_4 roots_171 gzo_171_4 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_4) [(dom_171,4)] (by decide +kernel) (lower_slice_b (T:=gsh_171_4) [(0xa0a00000a0a000000000000000000000a0a00000a0a,0,1),(0xf0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_149_8:=0x3300330000000000000000000000000033003300
def gzo_149_8:=0x3300330000000000000000000000000032002000
def gsh_149_8:=0x33003300000000000000000000000000320020
theorem lowS_zo_149_8_21:Lower true dzo_149_8 roots_149 gzo_149_8 5:=lower_iso_b (d1:=dom_149) (r1:=roots_149) (T1:=gsh_149_8) [(dom_149,8)] (by decide +kernel) (lower_slice_b (T:=gsh_149_8) [(0x33003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
def dzo_53_8:=0x3300330033003300
def gzo_53_8:=0x3300330032002000
def gsh_53_8:=0x33003300320020
theorem lowS_zo_53_8_21:Lower true dzo_53_8 roots_53 gzo_53_8 5:=lower_iso_b (d1:=dom_53) (r1:=roots_53) (T1:=gsh_53_8) [(dom_53,8)] (by decide +kernel) (lower_slice_b (T:=gsh_53_8) [(0x33003300000000,0,32)] (by decide +kernel) lowS_21)
def dzo_181_8:=0x330033003300330000000000000000003300330033003300
def gzo_181_8:=0x330033003300330000000000000000003300330032002000
def gsh_181_8:=0x3300330033003300000000000000000033003300320020
theorem lowS_zo_181_8_21:Lower true dzo_181_8 roots_181 gzo_181_8 6:=lower_iso_b (d1:=dom_181) (r1:=roots_181) (T1:=gsh_181_8) [(dom_181,8)] (by decide +kernel) (lower_slice_b (T:=gsh_181_8) [(0x3300330000000000000000000000000033003300000000,0,32),(0x3300330033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
def dzo_149_2:=0xcc00cc00000000000000000000000000cc00cc
def gzo_149_2:=0xcc00cc00000000000000000000000000c80080
def gsh_149_2:=0x33003300000000000000000000000000320020
theorem lowS_zo_149_2_21:Lower true dzo_149_2 roots_149 gzo_149_2 5:=lower_iso_b (d1:=dom_149) (r1:=roots_149) (T1:=gsh_149_2) [(dom_149,2)] (by decide +kernel) (lower_slice_b (T:=gsh_149_2) [(0x33003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
namespace S_191
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,129),(2,10),(2,34),(2,130),(3,7),(3,11),(3,19),(3,35),(3,131),(4,5),(4,20),(4,132),(6,7),(6,14),(6,22),(6,38),(6,134),(8,10),(8,40),(8,136),(9,11),(9,13),(9,25),(9,41),(9,137),(12,13),(12,14),(12,28),(12,44),(12,140),(16,17),(16,20),(16,144),(18,19),(18,22),(18,26),(18,50),(18,146),(24,25),(24,26),(24,28),(24,56),(24,152),(32,33),(32,34),(32,40),(32,160),(36,37),(36,38),(36,44),(36,52),(36,164),(48,49),(48,50),(48,52),(48,56),(48,176),(128,129),(128,130),(128,132),(128,136),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
def xsM:=roots_191.map (·&&&dom_191)
def gM:=goal_191&&&dom_191
def NN:Nat→Nat
|6=>14
|7=>113
|8=>312
|9=>268
|10=>64
|11=>8
|12=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x52a1c331e331870263e5249121fe051df851c2551895e0dc380a46c03fcc02790003e4
|7,0=>0xb1842aec47901308ccc28c8867e7577bc5d6ed896c8ac6a811692e955934519cf505fa4ea784cad04c93549d85488f8436133d4e73cd263b61f3afe73aa5438ef3373b535147347633374c2d1f12cdb42c6432aff42a6e629f4629710295ad2898a263642507823d7d23bbe237d12329e22a1a2210620a80200681ff411f7c21f66f1d6c11c0db1bbff1b6c01a2c117f4317ec617e851767b167b415e7d15a821538f1537814b92134e4134a91324e1323612700118d3115d210791103ba100220f3ab0e7f40dd9d0daa70d01f0ce360ca4d0c9e20c36d0bd0b0bcd2098d90988c095dc091a208d90083d607cfe0728d0719f06c7d0657b063a105bfc059e30583f0428103bd902cb7029d2026ca01d6a00f2800b6a0038f00325
|8,0=>0x1204311e9911b54117b51178d111a710c9c10b46109b91085f108401078410380102180f9f10f5d20f3750f1b30f0f00edc40eca90ec250e9cb0e8d50e8800e7bc0e5870e2380e14f0d5690d4cc0d1970d0820cbe30c9e30c5700c26d0c1390c0ea0bb160ba1c0ba0b0b8fb0b8a00b6880b5b10b2ef0b2d00b19b0b05b0ae030abe90abe20a9ca0a8710a63609f6809e5e09e3d09dc40955c08c7c08b3f08a5b086f5080dd07f6607e5b07dc607d2707c7907c3f07add079b10738d071bd0719f070af0704206fb806e7506bde06af406aea06adf06aaa06909065c005dfd0593c05842057b5057a70545a0503904e5904b4f047ef047e004579044d5042980413703f9b03f9803dc5039e3038dc0367b0362f02d6102cfc02cf202ba1024d20207e0207301e8501b24019ea017e3015930104d00fa800b5a008bb0051e000fa
|8,1=>0x4822d47a0f474cd469234518d41d284180541116402093f9723ef753e7903e4b93da153d7793d3a03bc813b7fb3ac1439c0939819394343711336d40355483509934c5d346913413b32caf31e54312982fe4e2fdc22fcdb2fc122ea782bdb32ab452a9f52a38d2a2d22a2472988a290d728fbf28db92849926f9d268ef262f72561c2547d2530c2520e2515f24d41246e624612245ce23ec623921236ea235532325722ec822e6222abb219c221805215aa2142c2121c210602082c2009b1fba41fb6c1fae01f6f71f29d1e2b71dbdb1d7c41d08c1cebb1cd8b1cb691c3dc1bcd71bbc71baa71b9711b6fc1b5d31b4381b1741ab351aaa219e9519d641948419461187ec17dc617dbd173db16fe2169e5165b91611315c6d154fd14ccf1460f14603145b9142f6142bc135b21341912f5f12945127c01274512626125bb1227f
|8,2=>0xf5dc6b01e5a6d60949168aca58a7508991084e417aee07ac5d79881770ef70fdf6cc246882e6717866a2e6629463f506359d62577602bb5fd925d5015b9a05a14959e47595cc584d6581d4575f0572995611f55b3e552385517153d8653012527ca519ae51377505c74fde94e39f4d0fb4c1124c0304bfda4b0564ae784ad974ad9649c5e48f6e48ab3485ba
|9,0=>0x1e40a1e34d1e2d71d42b1cdec1c9a01c3d21beaf1b23e1ae7b1ae491a1ec1a16319c4a1989f191ea18e9918e2818e0a188ab1845b17f6217ca9179f617548164a61633915ce615a9f154f814e2114395142731385b135a0134b51321a12dab11fa811e761184a10fee1080d103ec0fa8a0fa270f5910f3c10f2510efbb0e4a60e21f0df240dead0ddaf0d9ee0d3790d2f90d1240d1130c6930c4460bc2e0bb750b6d30b56b0b4cf0af800aa9f0a8280a3e509e37098b50940d093f1093f0092d40905a0900108c7008b6d08af708ac208a120818507ead07ea707d4c07cf207b3b07b110710a06ef906a35069af0686806559065550647505a3a0563d053d70527b04dab04c8704be90497b04773047590473b0452f0451d040a703d9f03d38038fc037dc02d7a024b90229401f2c017640137c011e90113800f8800c170024e
|9,1=>0x9ca9f94db794b59921148e74d8d2bf86c25825c381ce5804ed7f3e27d1ce7b89872764727136f7706ec4e6da896d77d6a1b6695ef63bbe637d860dec596b25955458eb657d2655f4b55cb954c32510ac4f1a94d2a54bae44bab54b4fe49e4c48fc048d47483dc465b243c1841b774157440ad63f8573f5273f08f3d9123d1ea3b8e83ae463a28839c6f39775395db3920d38e6d38cad389c038156371423702b365583570034a1c347b034512344ed3425633efd33eee333db328ea31f5d310ba30b213094f305dc304a0301e82fd032f8362f2e32e61d2e2bd2e1782ddf82d2152c6552c5c82b04c2a3672a19329bdd29762283f62831627f9127cf727913278d32768f2737f26f8a2683d2676725df02431f242bf241f624064236ae2266d2252c2205021903216192115d2102f20e0220b84204201fc091f9421f5111e75c
|9,2=>0xcf899c01aeb8c51b821eb59f3af408a9ed7a9292a3937a34c2a1838a0f3d
|10,0=>0xd81599f3969d6d792de58fc728c5488bbbf8aec38745c86bc383e59752b36d62b693c866ec563b195d6fc5d1775bb4259113585f154aaf537854eb564b4234a59d4a1604264e40a5d3eeaf3a2cb353c032c49329652eb272db9f2d0882ab0e2852826f642437c23c6923a591e0d11d1541c0521ae4714e35147f11260e0e38a0be8c0b94f092e508eca0712a0430f0415303c510363c0303e0292c017ff00b91
|11,0=>0xf269e41059320cd2eaa62bff1266a61deb511d8d
|12,0=>0x2bff1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffff0000000000000000ff00ff00ff00ff000000faff0000faff00000000000000000000faff0000fafaffffffffffffffff0000000000000000cccccccccccccccc515151515151515100000000000000005151515150505050f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0ffffffffffffffff0000000000000000ffffaaaaffffaaaaffffffffffffffff0000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaaffffffffffffffff00000000000000000000000000000000ffffffffaaaaaaaa0000000000000000ffffffffaaaaaaaaffffffffffffffff0000000000000000ffffffff00000000ffff0000ffff00000000000000000000ffff0000ffff0000ffffffffffffffff0000000000000000ffaaffaaffaaffaaff00ff00ff00ff000000000000000000ff00ff00ff00ff00cccccccccccccccc0000000000000000cccccccccccccccc0f0f0f0f0f0f0f0f00000000000000000f0f0a0a0f0f0a0a
|0,1=>0xfffffffff0f0f0f00000000000000000fffffffff0f0f0f0ffffffffffffffff0000000000000000ffffffffff00ff00fffffffffafafafa0000000000000000fffffffffafafafa33333333333333330000000000000000333333333300330000ff00ff00ff00ff000000000000000000ff00ff00cc00cc0000ffff0000ffff00000000000000000000ffff0000fafa3333333333333333000000000000000033333333332233220f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0a0affffffffff00ff000000000000000000ffffffffff00ff00ffaaffaaffaaffaa0000000000000000ffaaffaaffaaffaaffffffffffffffff0000000000000000ffffffffeeeeeeeeffffffffcccccccc0000000000000000ffffffffccccccccfafafafafafafafa0000000000000000fafafafafafafafaffffffffffffffff0000000000000000f0f0f0f0f0f0f0f000ff00ff00ff00ff000000000000000000ff00ff00ee00eeffffffff000000000000000000000000ffffffff00000000
|0,2=>0xffccffccffccffcc0000000000000000ffccffccffccffcc0000ffff0000ffff00000000000000000000aaaa0000aaaaffffffffccccffff0000000000000000ffffffffcccceeeeffffffffffffffff0000000000000000ffffffffffffaaaaffffaaaaffffaaaa0000000000000000ffffaaaaffffaaaa00ff00ff00ff00ff000000000000000000ff00ff000000000f0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0a00000000ffcfffcf000000000000000000000000ffceffceffffffffffffffff0000000000000000fffffffffffff0f0ffffffffffffffff0000000000000000ffffffffffff0000555555555555555500000000000000005555555555555050ffffffffffffffff0000000000000000fafafafafafafafa0000ffff0000ffff00000000000000000000fafa0000fafaffffffffffffffff0000000000000000ffff0000ffff000000000000ffccffff000000000000000000000000ffccffee00ff00ff00cf00cf000000000000000000ff00ff00ce00ce
|0,3=>0xcfcfcfcfcfcfcfcf0000000000000000cececececececece00000000cfcfcfcf000000000000000000000000cecececeffffffffffffffff0000000000000000ffffffffaaaaaaaa00000000ffffffff000000000000000000000000aaaaaaaaf0fff0fff0fff0ff0000000000000000f0fff0fff0f0f0f0fffff3f3fffff3f30000000000000000fffff3f3fffff0f0ffffaaffffffaaff0000000000000000ffffaaeeffffaaee00ff00ff00ff00ff000000000000000000cc00cc00cc00cc0f0f0a0f0f0f0a0f00000000000000000f0f0a0e0f0f0a0ebbbbbbbbbbbbbbbb0000000000000000bbbbbbbbaaaaaaaaffff3333ffff33330000000000000000ffff3333ffff0000333333333333333300000000000000003333333300000000555511115555111100000000000000005555111155550000ffffffffffffff000000000000000000ffffffffffffff00ffffffffffffff000000000000000000f0f0f0f0f0f0f000ffccffffffccffff0000000000000000ffccffeeffccffee
|0,4=>0x333333333311331100000000000000003333333333103310fefefefefefefefe0000000000000000fefefefefefefefefefefefefefefefe0000000000000000fefefefe000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0000ffffffffffffffff0000000000000000ffffffffffaaffaa555551515555515100000000000000005555515155555050330033333300333300000000000000003300332233003322fffffffffcfcfcfc0000000000000000fffffffffcfcfcfc0000ffff0000fcfc00000000000000000000ffff0000fcfcffffffaaffffffaa0000000000000000ffffffaaffffffaaffffffaaffffffaa0000000000000000ffffffaa0000000055555555555555550000000000000000555555550000000000000000ffffffff000000000000000000000000ffaaffaa555555555555555500000000000000005555555550505050ffff00ffffff00ff0000000000000000ffff00ffffff0000555500555555005500000000000000005555005555550000
|0,5=>0x333333330000333300000000000000003333333300002222000000000000000000000000000000000000000055505550fff0fff0fff0fff00000000000000000fff0fff0fff0fff0ffffffffffffffff0000000000000000000000005550555000ff00ff000f000f000000000000000000ff00ff000a000affffffff0000ffff0000000000000000ffffffff0000aaaa0000fbfb0000fbfb00000000000000000000fbfb0000fafa555555555555555500000000000000005555555555550000ff0fff0fff0fff0f0000000000000000ff0aff0aff0aff0aeeeeeeeeeeeeeeee0000000000000000eeeeeeeeeeeeeeeeffffffffffffffff0000000000000000ffffffffccccccccffffffffffff00000000000000000000ffffffffffff00000000ffff0000ffff00000000000000000000ffff0000aaaaffffffffffffffff0000000000000000fffffffff0f0f0f0ffffffffff55ff550000000000000000ffffffffff50ff50555555555555555500000000000000005050505050505050
|0,6=>0x333333333333333300000000000000003322332233223322fffcfffcfffcfffc0000000000000000fffcfffcfffcfffcfffcfffcfffcfffc0000000000000000aaa8aaa8aaa8aaa8ffffffffff0fff0f0000000000000000ffffffffff0aff0affffffff0f0f0f0f0000000000000000ffffffff0a0a0a0a333333333303330300000000000000003333333333023302ffffffffffffffff0000000000000000ffeeffeeffeeffee00000000ffffffff000000000000000000000000ffeeffee0000f0ff0000f0ff00000000000000000000f0ff0000f0f0fffffffffffff0f00000000000000000fffffffffffff0f0fffff0f0fffff0f00000000000000000fffff0f0fffff0f000ff00ff00ff00f0000000000000000000ff00ff00ff00f0ffffffffffffffff0000000000000000fffffffffafafafaffffffffeeeeeeee0000000000000000ffffffffeeeeeeeeffffffffeeeeeeee0000000000000000f0f0f0f0e0e0e0e0ffffffffffffaaaa0000000000000000ffffffffffffaaaa
|0,7=>0xfffffffffffffff00000000000000000fffffffffffffff0fffffffcfffffffc0000000000000000fffffffcfffffffcfbfbfbfbfbfbfbfb0000000000000000fbfbfbfbfafafafa333333333300333300000000000000003333333333003322ffffccccffffcccc0000000000000000ffffccccffffccccffffccccffffcccc0000000000000000ffffcccc000000000000ffff0000ffff00000000000000000000ffff0000fefeffffffffffaaffaa0000000000000000ffffffffffaaffaa0000ffff0000ffaa00000000000000000000ffff0000ffaa0000ffff0000eeee00000000000000000000ffff0000eeeeff00ffffff00ffff0000000000000000ff00ffaaff00ffaaffffff00ffffff000000000000000000ffffff00ffffff00ffffff00ffffff000000000000000000f0f0f000f0f0f000505550555055505500000000000000005055505550505050ffffffffffffffff0000000000000000eeeeeeeeeeeeeeee00ff00ff00ff00ff000000000000000000ff00ff00aa00aa
|0,8=>0xfffffcfcfffffcfc0000000000000000fffffcfcfffffcfc00000000fffffcfc000000000000000000000000fffffcfc00000000bbbbbbbb000000000000000000000000aaaaaaaaaaffaaffaaffaaff0000000000000000aaffaaffaaaaaaaa00000000aaffaaff000000000000000000000000aaaaaaaafcfcfc00fcfcfc000000000000000000fcfcfc00fcfcfc005555555555555555000000000000000055555555555554540f0f0f0f0f0f0f0f00000000000000000f0f0f0e0f0f0f0efffffffffffff0f00000000000000000ff00ff00ff00f000ffffffffffffeeee0000000000000000ffffffffffffeeeefcfcfcfcfcfcfcfc0000000000000000fcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc0000000000000000fc00fc00fc00fc00ffffffeeffffffee0000000000000000ffffffeeffffffeefffafffafffafffa0000000000000000fffafffafffafffa00000000fffafffa000000000000000000000000fffafffa555555555555555500000000000000005500550055005500
|0,9=>0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00ffff0f0fffff0f0f0000000000000000ffff0f0fffff0f00ffff5555ffff55550000000000000000ffff4444ffff444455555555555555550000000000000000444444444444444400000000ffff5555000000000000000000000000ffff444411111111111111110000000000000000111111111010101000ff00ff00ff00ff000000000000000000ff00f000ff00f0ffffffffffffffff0000000000000000fffff0f0fffff0f0ccffccffccffccff0000000000000000ccffccfcccffccfc00ff00ff00fa00fa000000000000000000ff00ff00fa00faffffffffffffffff000000000000000000ff00ff00fa00faf0f0f0f0ffffffff0000000000000000f0f0f0f0fff0fff000000000ffffffff000000000000000000000000ff00ff000000f0f00000ffff00000000000000000000f0f00000fff0fffff0fffffff0ff0000000000000000fffff0fffffff0f00000fffc0000fffc00000000000000000000fffc0000fffc
|0,10=>0xccccffffccccffff0000000000000000cccceeeecccceeee000000000f0f0f0f0000000000000000000000000f0f0000ff00ff00ff0fff0f0000000000000000ff00ff00ff0fff00ff0fff0fff0fff0f0000000000000000ff0fff00ff0fff000f0f0f0f0f0f0f0f00000000000000000f0f00000f0f000000000000ff0fff0f000000000000000000000000ff0fff000000ffee0000ffee00000000000000000000ffee0000ffee0f0e0f0e0f0e0f0e00000000000000000f0e0f0e0f0e0f0effeeffeeffeeffee0000000000000000ffeeffeeffeeffeeffffffffffffffff00000000000000000f0e0f0e0f0e0f0e0000ffff0000ffff00000000000000000000ffff0000f0f0aaffaaffaaffaaff0000000000000000aaffaaaaaaffaaaa00ff00ff00ff00ff000000000000000000ff000000ff0000ffffffffaaffaaff0000000000000000ffffffffaaffaaaaffffffffffffffaa0000000000000000ffffffffffffffaaffffff00ffffff000000000000000000aaaaaa00aaaaaa00
|0,11=>0xffffeeeeffffeeee0000000000000000ffffeeeeffffeeeeffffeeeeffffeeee0000000000000000ff00ee00ff00ee00ffffffffffffffff00000000000000000000fffc0000fffc55505550555055500000000000000000555055505550555000000000fffffff0000000000000000000000000fffffff0fffffff0fffffff00000000000000000fffffff0fffffff0ffffffffffffffff000000000000000000000000fffffff05555555505050505000000000000000055555555000000000000ffff0000ffff00000000000000000000ffff00000000f5f5f5f5f5f5f5f50000000000000000f5f5f5f5f0f0f0f0ffffffffffaaffaa0000000000000000ffff0000ffaa0000aaffaaffaaffaaff0000000000000000aaeeaaeeaaeeaaee0000aaff0000aaff00000000000000000000aaee0000aaee0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0c0c0c0cafafafafafafafaf0000000000000000afafafafaeaeaeaefffffffffffffcfc0000000000000000fffffffffffffcfc
|0,12=>0xffffccccffffcccc0000000000000000f0f0c0c0f0f0c0c0000055550000555500000000000000000000555500000000ff00ff55ff00ff550000000000000000ff00ff55ff00ff00333333223333332200000000000000003333332233333322ffffffffffffffff0000000000000000555055505550555000000000ffffffff0000000000000000000000005550555000000000ffffffff000000000000000000000000f0f0f0f00000000000ff00ff00000000000000000000000000ff00f0333333333333333300000000000000003300330033003300fffff3f3fffff3f30000000000000000fffff3f0fffff3f00f0f0f0f0f0f0f0f00000000000000000c0c0c0c0c0c0c0cafafafafafafafaf0000000000000000aeaeaeaeaeaeaeae0000ffff0000ffff00000000000000000000ffaa0000ffaaffffffff0000ffff0000000000000000ffffffff0000ffaa000000005555550000000000000000000000000055555500333333333333333300000000000000003333222233332222
|0,13=>0xfff0fff0fff0fff00000000000000000fff00000fff00000000000000000000000000000000000000000ffff0000fcfcffffccccffffcccc0000000000000000aaaa8888aaaa8888ffffffffffffcccc0000000000000000ffffffffaaaa888800000000000000000000000000000000555555555550555000ff00ee00ff00ee000000000000000000ff00ee00ff00eeffffffffffffffff000000000000000000ff00ee00ff00ee0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0a0a0a0a003300330033003300000000000000000030003000300030ffff0033ffff00330000000000000000ffff0030ffff0030333333333232323200000000000000003333333332323232ffff00ffffff00ff0000000000000000ffff00ccffff00cc0f0f000f0f0f000f00000000000000000f0f000c0f0f000c333333333333333300000000000000003333333332323232fffffffffff0fff00000000000000000fffffffffff0fff0555555555550555000000000000000005555555555505550
|0,14=>0xff0fff0fff0fff0f0000000000000000ff0eff0eff0eff0e00000000ffffffff000000000000000000000000ccccccccfafafafaffffffff0000000000000000fafafafafefefefe0000ffff0000ffff00000000000000000000ffcc0000ffccffffffffffffffff0000000000000000ffccffccffccffccaaaaffffaaaaffff0000000000000000aaaaffeeaaaaffee000000003333333300000000000000000000000033330000aaaaaaaabbbbbbbb0000000000000000aaaaaaaabbbbaaaa0f0f0f0f0f0a0f0a00000000000000000f0f0f0f0f0a0f0a003300330033003300000000000000000022002200220022f0f3f0f3f0f3f0f30000000000000000f0f2f0f2f0f2f0f200000000ffffffff000000000000000000000000ffff00000000fcfc0000fcfc00000000000000000000fcfc0000fcfc555555555555555500000000000000005555444455554444ffffffffffffffff0000000000000000ffffccccffffcccc005500550055005500000000000000000055004400550044
|0,15=>0xf0f0f0f0f0a0f0a0000aaff0000aaff00000000000000000000aaff0000aaaaaaaaaaaaffffffff0000000000000000aaaaaaaaffaaffaa0a0a0a0a0f0f0f0f00000000000000000a0a0a0a0f0a0f0affffffffffffffff0000000000000000fefefefefefefefe0000ffff0000ffff00000000000000000000fefe0000fefe0000ffff0000ffff00000000000000000000ffff0000ffaaffffffffffffcccc0000000000000000ffffffffffffcccc555455545554555400000000000000005554555455545554ff55ff55ff55ff550000000000000000ff55ff55ff00ff003311331133113311000000000000000033113311330033000f0f03030f0f030300000000000000000f0f03030f0f0000ffffffffffffffff0000000000000000fffffffffff0fff0ffffffffffffffff0000000000000000fff0fff0fff0fff03333333333333333000000000000000033333333333033300f0f0f0f0f0f0f0f00000000000000000e0e0e0e0e0e0e0e
|1,0=>0xcc00ff00cc00ff000000000000000000cc00ee00cc00ee00ff00ff000000ff000000000000000000ff00ff000000aa00000000ffffffff000000000000000000000000ffffaaaaccccccccffffffff0000000000000000ccccccccffffeeeeffffccccffffcccc0000000000000000ff00cc00ff00cc00ffffeeeeffffeeee0000000000000000ffaaeeaaffaaeeaaffffccccffffcccc0000000000000000ffaacc88ffaacc8800000000ffffffff000000000000000000000000fffff0f0ccccccccffffffff0000000000000000ccccccccfffffcfcffff0000ffffffff0000000000000000ffff0000ffffff0055550000555555550000000000000000555500005555550000000000ffffeeee000000000000000000000000ffffeeeeffffffff0000ffff0000000000000000ffffffff0000ff000000ffff0000ffff00000000000000000000ff000000ff00fffffffff0f0ffff0000000000000000fffffffff0f0fff00f0f0f0f0f0f0f0000000000000000000f0f0f0f0f0f0f00
|1,1=>0xffffff00ffffff000000000000000000ffffff00aaaaaa00000000003333333300000000000000000000000032323232aaaaaaaaffffffff0000000000000000aaaaaaaafafafafaeeeeeeeeffffffff0000000000000000eeeeeeeefefefefeffffffffffffffff0000000000000000ffffffeeffffffee00000000ffffffaa000000000000000000000000ffffffaaffffffffffffffff000000000000000000000000ffffffaa00000f0f00000f0f000000000000000000000f0c00000f0c00ff00fc00ff00fc000000000000000000ff00fc00ff00fcffff00ffffff00ff0000000000000000ffff00ffffff00aafff0fff0fff0fff00000000000000000aaa0aaa0aaa0aaa00000000000000000000000000000000000000000555544440f0f0c0c0f0f0c0c00000000000000000f0f0c0c0f0f0c0cffffffffffffffff000000000000000000000000fcfcfcfc00000000fcfcfcfc000000000000000000000000fcfcfcfc0000ffff0000ffff0000000000000000000000000000fcfc
|1,2=>0xffffffffcfcfcfcf0000000000000000ffffffffcececece333333333333333300000000000000002222222222222222fff0ccc0fff0ccc00000000000000000fff0ccc0fff0ccc000000000ffffffff000000000000000000000000eeeeeeee0000bbbb0000bbbb00000000000000000000bbbb0000aaaa0000000000ff00ff00000000000000000000000000f000f0ffff0000ffff00ff0000000000000000ffff0000ffff00f0fffffcfcfffffcfc0000000000000000fffffcfcf0f0f0f0003300330033003300000000000000000033000000330000aabbaabbaabbaabb0000000000000000aabbaaaaaabbaaaa333333333333333300000000000000003333333322222222ffffbbbbffffbbbb0000000000000000ffffbbbbffffaaaa00ff00ff00ff00ff000000000000000000ee00ee00ee00eefffffffffffafffa0000000000000000fffffffffffafffaffffffffffffffff0000000000000000fcfcfcfcfcfcfcfc000000005555555500000000000000000000000054545454
|1,3=>0xffff0000000000000000000000000000aaaaff00ff00ff00ffff0000000000000000ff00ff00ff00ffaaffffffccffffffcc0000000000000000ffffffccffffffccffffffccffffffcc0000000000000000aaaaaa88aaaaaa88fff0fff0fff0fff00000000000000000fff0fff0aaa0aaa000000000000000000000000000000000fffffffffffffcfc000000000000000000000000000000005554555455545554ffff3333ffff33330000000000000000ffff3333ffff2222000000005555555500000000000000000000000055550000ccccccccdddddddd0000000000000000ccccccccddddcccc00ff00ff00ff00ff000000000000000000f000f000f000f00f0f0f0f0e0e0e0e00000000000000000f0f0f0f0e0e0e0e0000000000000000000000000000000000ff00ff00ff00f0000000000303030300000000000000000000000002020202000000330000003300000000000000000000002200000022ffffffff0f0f0f0f0000000000000000ffffffff0c0c0c0c
|1,4=>0xfff0fff0000000000000000000000000fff0fff0f0f0fffff0f0ffff0000000000000000f0f0fffff0f0f0f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f000000000f0f0f000f0f0f0000000000000000000f0f0f000f0f0f00ffffffffffffffff00000000000000000f0f0f000f0f0f0000000000000000000000000000000000fffffff0fffffff00f0f0f0f0f0f0f0f00000000000000000f0e0f0e0f0e0f0effcfffcfffcfffcf0000000000000000ffceffceffceffceffffffffffffffff0000000000000000fffffffcfffffffcffffffffffffffff0000000000000000fff0ccc0fff0ccc0ffffffffffffffff0000000000000000ffffffffffffffaaffffffffffffffff00000000000000000000000055555500555555555555555500000000000000005555000055550000ffddffddffddffdd0000000000000000ffddffccffddffccffeeffeeffeeffee0000000000000000f0e0f0e0f0e0f0e000000f0f00000f0f000000000000000000000f0f00000f00
|1,5=>0xf0f0f0f0ffffffff0000000000000000f0f0f0f0fffff0f003030303030303030000000000000000020202020202020200000000000000000000000000000000ffffff00ffffff00cccccccccccccccc0000000000000000ffffffccffffffcc00000000000000000000000000000000fffffffffff0fff000000000ffffffff000000000000000000000000ffffccccffffffffffffffff0000000000000000ffffffccffffffcc00ff00ff00ff00ff000000000000000000aa00aa00aa00aaf0fff0fff0fff0ff0000000000000000f0faf0faf0faf0faffffffffffffffff0000000000000000fffffcfcfffffcfc00ff00ff00ff00ff000000000000000000ff00ff00f000f000ff00ff00ff00ff000000000000000000ff00cc00ff00ccff33ff33ff33ff330000000000000000ff22ff22ff22ff221111111111111111000000000000000011001100110011000000ffff0000ffff00000000000000000000cccc0000cccc545454545454545400000000000000005454545454545454
|1,6=>0x111011101110111000000000000000001110111011101110555544445555444400000000000000005555444455554444000000003333333300000000000000000000000030303030000000000000000000000000000000000000fff00000fff0333333003333330000000000000000003333330033333300ffff0000fffffff00000000000000000ffff0000fffffff0ffffffff555555550000000000000000ffffffff444444445555555555555555000000000000000055555555444444440f0f0f0f0f0f0f0f00000000000000000f000f000f000f00ffff0f0fffff0f0f0000000000000000ffff0f00ffff0f0000000000ffffff00000000000000000000000000ffffff00333333333333333300000000000000003333000033330000ffffffff333333330000000000000000ffffffff3333000000ff00ff00ff00ff000000000000000000ff00ff00ff000000000000000000000000000000000000fffffffffafafafafcfcfcfcfcfcfcfc0000000000000000fcfc0000fcfc0000
|1,7=>0xaaaaaaaafffafffa0000000000000000aaaaaaaafffafffaaaaaaaaaaaaaaaaa0000000000000000ffffeeeeffffeeee000000000f0f0f0f0000000000000000000000000c0c0c0cffffffffffffffff0000000000000000ffffeeeeffffeeeeffffffff0f0f0f0f0000000000000000ffffffff0f0f0000000f000f000f000f0000000000000000000c000c000c000c00000000000000000000000000000000ffffccccffffcccc000f000c000f000c0000000000000000000f000c000f000c55555555555555550000000000000000545454545454545400000f0f00000f0f000000000000000000000c0c00000c0c00000000000000000000000000000000fcfcfcfcfcfcfcfc000000003333333300000000000000000000000022222222ffffffffffffffff0000000000000000545454545454545400000000000000000000000000000000fff0fff0fff0fff00000ffff0000ffff00000000000000000000ffff0000ff00f3f3f3f3f3f3f3f30000000000000000f3f3f0f0f3f3f0f0
|1,8=>0xaaaaffffaaaaffff0000000000000000aaaaffffaaaaaaaa00000f0f00000f0f000000000000000000000f0f00000000ff00ff00ffffffff0000000000000000ff00ff00ffaaffaabbbbbbaabbbbbbaa0000000000000000bbbbbbaabbbbbbaa333333333333333300000000000000003030303030303030bbbbbbbbbbbbbbbb0000000000000000babababababababa0000000000000000000000000000000000000000ffffff00333033303330333000000000000000003330333033303330ccccccccffffffff0000000000000000ccccccccffffcccccfcfcfcfcfcfcfcf0000000000000000cfcfcccccfcfcccc00ff00cc00ff00cc000000000000000000ff00cc00ff00ccf0fff0fcf0fff0fc0000000000000000f0fff0fcf0fff0fcffffffffffffffff0000000000000000ffffff00ffffff000f0f0f0f0f0f0f0f00000000000000000f0f0f000f0f0f000000fff00000fff000000000000000000000fff00000fff0000000005555555500000000000000000000000050505050
|1,9=>0xdddddddddddddddd0000000000000000ddddddddcccccccc11111111111111110000000000000000111111110000000000000000000000000000000000000000fffffffffffff0f0
|_,_=>0
def sP:Nat→Nat
|0=>0x110081601048203c100200802080c01c2e050204c1601048a80c050200c040b008a4080209004120814040080b0089436070a0140802058344a170280c16010408c44020580410210384008120082040070e814080205824381005804101b0d01c20040102032180385c0a040b00412000801026120082422050803c1601040380c0502008160d060180a04018080200
|1=>0x411c2045020081601048f420040100488000381844040102c020921840080205820841c0381420040102c0209200f4080205804103e038f4080b00820223c0385c0a0a0200c1601040180a04078ec160104014203a02008160d040400802008206e0708010040b008d866070b814040b00824102303014080205804660708088040b1880410040102c02081081c5a10
|2=>0x1048ac010489820040580412080d8740a040102c1a081a1500a2b0102c1a081a0180a3502008160104840080b0082022530385c0a040102c0209210400802058209e0708010040b06820180708010044d058341017028101e0b0082098140801004121f824101002008240b048203210020081601250d00e10110081601041240e1f02810041300824540502008160d
|3=>0x3010040b040700e1f1e810040b040700e0401048160104820d005080101e0b00820ce10110082401041904c10158081601048d0c6100202c02080881c20040102cc20104980aa0502008160104840440205804105f038f420040102c02082e0f420040115802180384008020900412082d96820220102cac0104840040b008d81059038400802058046c58038400857
|4=>0xd81c3e1011008e6010402808020580410680385ca43d0203c16010401420040782c0208391b02004010480208038180a04010901671008400816011c40200038500a0a020081656048180a02058041223080081601041c04607080100401041bc000731014080205804122e31040040b00824460708010041200820da10020081609041a80e4b080100401040000e26
|5=>0x14080205824101c1e0500a2b02008167104840fc22010480208080081601041640e100200816083e0b80e543d008160d04040040b00820f2070b84008030082000070a84056220102c020902810040b00824ee0508010040b009280e1015888040b00824e00502008160d041d8202b2083c16010401ca8051580816080e01c2e05021d4160104820cc050202c0208
|6=>0x580412100200802084401d0c101100816010481408024382c02080b814080f05804105843014080205804121002175080d0404106220102c020933014080205834103408010041200825023202810160104200202b0202c02090881cfe1011008240104050202b1100816710489c20040102c101c03898a41402008160d04040080b00820222e038142004011580209
|7=>0x2008160d040d00e3d08104080205804100702810040b008211a0708010040b008212a0703040e8220102c02092584044040102c02090404008020580410920384122040782c020803840080f05834109008010040b008945407080880412008211c0502008160d1b0211a050203c16010422c2e050200816011281c207b2ea28100708010040b00a240e1015888d202
|8=>0x42a40e100203c1601042040e10020081601042980e3d08010041205958020908010040b0082054a503a8820040102c020803a8420040102c02090384044020580410a00f81808020900412104f010040b008200e1402810040b00820b00708010040b00821360708010040b00821340708010040b4b80410070a04008020902ce20904014200a020081671008202065
|9=>0x820ce0708010040b0082166072a8400802058d810070284008020583402082c05020040102d5e090401c20040102c02b10401d60050200816010401c0c100200c0424058040e101100816af008200e10022b4040b008200e5429010040b0082068070808808020580412083781420040102cac01048b8d610020081656008240e10020081601042a80e1002008160d
|10=>0x38f4200401808240b00820c41002008240b00824f01005010040b008240e6b08010040b0082570070b84008020082410000384008020582410190385c0a040982c02081501c20040115802090001c3e3d0200816560081c0c040102c02095b8142004012d8160104840080f058041090039ac200401048020803840040b008203407080116a0205804100708010040b
|11=>0x8200e100203c1601043040e100200816010416054072a040040b0082180070f81408020583410342a040445d0104802080801004be05804100708010040b008217a070808808160102ce2010481420040782c02085e04008020580410b9038142004018081601040b87a10020081601220a40e6b0801006020580410071301808020595802071605c0a040102c0208
|12=>0x8010047d0580410070f07c0a040102c02090405c20020902c02081181c20040102c02096601c20040104c7601040a80e10020081601043280e10020090a010482192100200c0412059c4020808010040b00821900708088ea020580412080831808020580410070801006020082000070304008020580588071e8102c020580478073001408020580412c208010040b
|13=>0x820be0708010040b00825aa07028400802058041040039480c0502008160d0082020040102c02086981ca8050200816710082020040102c02086901cf0050203c160104014202b0200c040b0082420040782c02086801c3e10020099e010401c202b020bc1e0b0682020040100410bc6481d60101100816010401c20046680816010401c0a103281016010406c0e05
|14=>0x102cac010387c0a040104c02081501db8100200816010401c20040102c02086d81c0c050200816012c01c20040102c02086c81c20040102c02086c1c00e550284008020982c0209081140802058041007082e8080f058340208083580802058041007081d0080f4282c1a080284008021202c020922050200a0200816710401c20040180816af008200e5a08010040b
|15=>0x401c20040102cac0104b900a1002008160d0438c2e1002058480b008240e10020081601043800e1e08010040b00821b007081d1be0b008200e103a0882c0b00824aa0602810040b008243e10022b004010401c2e10110081601040b80e5203010040b0082054070b8140803058041010020081601041c80e10020081601043780e1508010040b00821b0071e8401404
|16=>0x580410070801004ed058041007080d40802058046c0803ac020040102c1a0803840080205805d4080384072040102c020803840080205805d008038180a350200816010401c2e10020084801040a40e10020081601040d0a60702008160104820d007080101e0b00821ce0708010041305804126f0385c0a040784c160104150963d0200816010401c2004013941601
|17=>0x8203e06020090a56039480c040102c024403840040b0680410fa03840ca041783c160d040405e020902c02081181c3e053a0101e0b008207a10020081601043e40ef802810040b0682020040782c02087b81c9610020081601040a40e100200816087a81c20040102c02081a3d00e100200816087881ccc5502810040b008200e1708028080200820000708011de02
|18=>0x8480816010401c28100200816af0401c20040102e0e010401c20040102c02088281c20040102c0208198d00e1002008160104c100f0108010040b008200e100200816011281c20040782c02088001c20040102c02087f81c7a1002058040b008a40e26080ac040b00820680708010040b0082054fe0389c0a100203c040b0082020040102c02087e01c3e050203c0413
|19=>0x1e840080205804111403814202b02008160d040d02004178084801040a40e10230101e0b068041006080100401048000e100203c040b068222610020081601044400e170801006130580412070b84008020082000070284008020580412ce08010040b00824110f0384008020580412088701c20040102e18010401c3e050200816560682020048500816010401c2004
|20=>0x82240070847c080205804100708010040b008223c0702810040b00824104302810040b2b004123c1e84056040102ce20103840080205c7002080384014041780802080001c211b0200816010401c20040102c02088c81c20040102c02088c01c2004538081601048b80e1002008160d0445c0e3d0845808020580410071e84008020595802d8038400816058062a07
|21=>0x80105e02008200007084a0080205804100708010600205804102e038500a650200816081a01c20040102c03260401c7a100200816080e01c2004010481601048224a1729014080f05804101402810040b2b0242124020081601040d00e1005010040b00822460791040080f05804100702810060205804103c3584008020980412071e840080209848020908010040b
|22=>0x102d5e010401c20042e83d0a0d040400802058041131038180a7b02008160104cc020040102cac08038f408020580412089601e5e6b08010040b008200e0508118080205804122602840560205804120602810040b008265c10024b404850401c0c050200c040b00824200a020081601044b00e0508194080205834103408010040b008225607084a40802058041007
|23=>0x9c81c4e1702810040b008200e109c010040b008200e1d02810040b00820540708010040b9b00410070f8180802008226a07081d0f616059580e1002008160104cd00e10020081601044cc0e0508010040b00824882e08010040b0082264071e84008020902c02092204174220104802080802808690102c02080385c0a040580412081501408020583402081e0400875
|24=>0x8010041200824100602810060205804a81e29010040b008200e1f0301004122b0040e3d08010160104820220708010040b0082278071e84014040102c02440384044040104802088892020040102c109c038180a040102c1a081a010040b009107807081f8080f0580410071e840093b0102c02080381420350200816010482274100200816010401c20040102c0208
|25=>0x58041007080102c0205abc020903840080205d0402080381420020580412081184056020580412e408010047d0580410070a84008021202c0208038500a6502008160d0404008020580412a9038400802058041140038547a040102c02081e01c0a1015810040b00824543d020081601041c0780708010048405834103d020081601044b00e10024f8040b008200e48
|26=>0x404008020580411140387c0a040102cac01048428e040102c0208039ac20040104802090404009460102c020803d1420040102c0208038f420040580410110384008020900410f70384008020580411440398c2a100200816010401c0a040102c0209220f020220102c02088001c0a101d010040b008200e2708010040b0082054070808808a70102c0209080128402
|27=>0x21741601042000e10158105e020580412070852808020580410071e8400802059580209038180a740200816010401c7a040102c02441e01c20045383c160d0404008020580411490384009480102c020803840e87b2ea1410070b81456040102c0209080ac0802058041270038982e520200816010401c0c05020081601048a8a81f11008240104014208f02008160d
|28=>0x38f420040180816010401cc4100200816010481c20040102c0208a901c2004012141608a881c0a10020081601045400e1011010040b008229e07290400802058041034038400802a702c020803840080205958111103840e8047902c020803840f6042e80824010401c0c040102c0208a681c20220102c02085b81c20040102c0208a581c200401808260b008240e10
|29=>0x384008020595802091481c20040102c028c040a80e2602840080205834020808010041205804115503840080205804107003840080205804115403840082f0782c1a080284008020982c020902840080205804104c038f420040102c02089701c28100200816084e01c20460200816010481c3e103d888040b008200e10021d4040b008205c0708012a602058041208
|30=>0x40a40e10ae010040b008200f5b08010040b008200e10020081601045680e10ac8880802058041007081ec080f0102c1a08160f40a100200816010401c2004018081671008200e1002009280b008200e100229c1e0b008200e100200aae0b008200e10ab010040b008200e0602810040b008242a100200816010401c0c103a088040b008200e1708010040b008241029
|31=>0x580411620384008027d82c1a010401ec2100200816010401c20047905816010401c7a05080101e0205804105408118040b008200e100200ac00b008200e06080102c020902c020708010055f0580410071e840f6040102c02080385c20220200816010482020040102c0208af01c2022020081656008243e060200824010401c0a1020810040b008200e10020082401
|32=>0x8200e54031ec040b008200e1002008260b008218e07080101e0b00822ca07b1840080205804100708011d6020982c1a010401c3e103d810040b068200e1002008167100822b0073104008020902c0208039980a040102c0208038142004012d816010401c3e103d8100412008200e54081ec040b068200e10020580485058041207028400802059c40208130400802
|33=>0x820ee070f8400802008226a07080ac080205804109303842d4040102c020803da420040102c02080395008020580410440392c7a100200816010401c3c10158101e02058041007081d0f61605804100708010040b00822d0070304008020580410a30389820042e80816010401c0c040102c02091e01c21660200816010401c20040102c02360401c3c1015810040b
|34=>0x401c20040102cac01043900e10158081601048b80e10110105e020580412080b84008020982c020903840080205804116d039540c050200816010401cc0101100816010401c20220200802080001c20040102c0208b601c200407808260b068041010020bc040b008241029039540a1002008260b008200e100203c1601045ac0e1002008167100820780708010040b
|35=>0xb900816010401c20040102c0208b881c0a1002008160d040d0a810020081601043140e100203c1601045300e100200ae00b008200e1002008160104822d6071e840080205958020729040080205958020803840080205804116f03840080205834116e03840e87b0782c020803840080205805fa080385020040102ce2080387c0a0401004114d03840e804014841601
|36=>0x424c0e10020090a1200824100608010040b008245207080102c029082c02080385c20040102c02081481c3e060200816560081c3c10328101e0205804100708010ba02ba8041007084f4080f0580410070823c080f0102c0208038780a10020081601048200c10020081671008240e1002008160104822e80708010040b00822e6070f040ca040102c0208039502004
|37=>0x8240e100102c02090408c0e104c088082f0102c020803b44200401048020803840e8040182c0208038400802058041090038427a040102c02090401c7a1002008480b008200e1002008160d00822ee0708010040b00822ec070304044040102c02092a1480a040102c02080384008020580410810384008020580412089601c20040102c02087801c2065020081601
|38=>0x102c02080387c0a040102c02090404008690102c02090401c20040102c0208be81c217c0200816010401c7a05020081601040f00f7b08010040b008200e3d08010040b00820a60708010040b00822f407080100424059c402080384008020580410c10384008020580410dd0395021790102c02080384008020580411780384008020580412089281c3e1002058040b
|39=>0x80101e020580411820381420040102cac0d0415020020580411810387420040102c0209038400802058041180038406a040102c020803840ca040102c02081c01c28050200816560401ccc1002008160d008200e1041810040b008200e540800816010450c0e10020081601bf8200e10020bc040b0082052072d0400802058041208038c820040782c020803842fc04
|40=>0x8231007030400802059c4020743040080205804100708010040bc3804100708010040b00821ee0708010040bc3004100708010040b00822e807081d008160595802070801005840580410070b8f40a040102c0208038400802058041208a68c820040102c02090401da21011010040b008200e26080081601042dc0e05081d0080205804120808010040b008224607
|41=>0x401c20040b03c16560081c20043480816010401c2004c680816010401c20040102c038c0401c2002058041023038400802058071408038500a040102c1a0808010040b0082150070801004b605804104403840080205804118903840080205804112c038400802058041100038980a101580816010401cc60508010040b008200e10024b4040b008200e1011010040b
|42=>0x3e4020040102c020803878200405804102a038401404178081601048200e0508010040b00e3c10070f84008024295810071e84008020580488070b84056040782c0208038180a040102cac010381420040102c0208c701c281011010040b2b0200e0608012e4020580410072a840080b0082036071e840080205804102a0384014040102cac010481c208f02008160d
|43=>0x2810040b0082078070f81408020580410b70381820e10200816010401c20040102cac086381c2065020bc1e0b008200e103a0102c0b008240e0508010040b00824112e0284008030102c0209040f420040102ce201048200e1002058040b388040e10020081601043980e103f010040b008200e1708194080f058041007080ac082f0782c0208038400802058041191
|44=>0x20081601044200e1015811d60205804100708010040b00e3c10070f84008021200410070808808160102cac010384008020595803580381820040102c02099701c7a0508010040b00821b00708010040bc900410070a0400802059581207131480a100200816010401c20040102cac01048f00e1f0801004122b0041007080101e02059581a08081d0085d428041007
|45=>0x20081601048200e10020bc04120580410072a040080205834020803840e8040102c02090401c20040102cac0d0401c281002008240b008200e100200aea0b008200e10020081601046200e1002008481205804100708010040b0082410e402840080205804124408088082f01048160104040ca047580816010401c0a10020081601048205410020081601043b00e10
|46=>0x81ec08020580410070826008020902c0208039480a100200816010401c200441174040b008200e1047810040b008200e10020081601040e00e100200816710680410070a040080205958100708010041205804120808010040b0082088070301408020580410070284008020982c02080384306220200816010401c3c100200816010401c20040102c02082801c200a
|47=>0x401c20040102c0209040f00e100200816010428c0e0508010040b0082410103a088040b008200e10020081601048225c07081d0f602058041007030400802059580207082fc0802058041007084f4e8040102c02080384008020580411650395020040121416010401c20040121416560401c0c1011010040b008200e100229c040b008200e100200a420b008200e06
|48=>0x8200e10158105e020580410070b84056040102c02080384008020580410e40384008160102cac0103840440401048160104040082f0102c02090401c20041783c16010401c207402008160d008200e1f08010040b2b004100708010040b008225c0708010060205804100708010040b2b004120702840080205804102a0385c20040782c0208039502004010481601
|49=>0x15810040b008200e100203c040b008200e100200816010401c20040b00816010401c20740200816010401c20040102c02090401c7a100200816010401c20040102c02081501c20980200816010401c2065020bc040b008200e100200a42850580410071e81420040102c02080381420040102cac010401c2e050200816010401cc4100200816010401c2074020090a0b
|50=>0x8010040b008200e0608010040b008200e1032810040b008200e10
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0xb6e0547026b8119c07ee0387018b80a9c046e01c700ab8039c00ee0007
|7,0=>0x127c091e047f02387118408a2044102188108b8826040301f980f8c07a603c301da70e94072a0386e1bb80d9c06ae0347019b80c9c062e0307017b80b9c05ae02c7015b80a9c052e0288e13c809ab84b6024b011d808ac0436020b00fe707bb83be01cf00df806bc033e018f00bf805bc02be0150e0a0804c402420112e082703d401ca00d500628
|7,1=>0x3bf81dc38ec20752e3a181cd38e4a0718c38571bec0dd9c6dee36871b040d65c6a6c34c71a240cf5c66ce32e8193b8c7e062f030f8183c0bfe05ef02ef817438b85c5b302d3616638b12057902b57156c0a96053ce296814740a1a04fd02777137c099e04bf02578
|8,0=>0x2ea417320b8905bb92d9c16ae0b45259992c8496220aff257692b7415964ab9255392a5c150a4a7505328295b948e0a37051382863941209f904f482764138e49b524d2826541306497304b182544927e492d248d9242c11f608eb046d82324916e48a7044b8222390f5c86b042c9212410720829040b920148fe647e123e881f040f62079f23c78
|8,1=>0x3f2c9f760fa927cd73e339efa0f6d07ad93d249e75cf2b078d83c249dee4ee5276a83b141d6a0ea5074993a049ce20e610728839041c5e4e1d2705937e49bd20dd726e2936d41b4a0d9506c3735d49aca0d5506a2834d41a4a0d150681933c499be4ccd265e832ac99360c8b063c931a418b20c49061c830a418320c0ae5fd82fac17b24bc905dc8
|8,2=>0x4fbca7ba53cb29dd84eac2736138b09bc94da426b21347299a94c94262a1305097a84b9425aa12c5095994a8c25261284e93a8499424a65241291794874a41a11fd08f77477c239e11bf08d6946742316517ce8b68456ca299d13b28967446ca21250f908748435ca18e10b708538425c210a50732830941442082102f280f840349ffa0fed07ee8
|8,3=>0x60342ffa17eb2bed85f24af7217a90bcd75e2c2ef617692bac85d1cae71d7272b8b85c1c2dea56e6eb6b85b1c2d6e16a52b4995a0c2ce616630b2a759142c6656212b08858042be215e10ae7956f4ab5a159d0ac5955ec2ad9d55b2aa4954e42a5215190a84853e429d214d90a64852e4294e54970a42951d428ca14550a21950cc2842540f2a007
|8,4=>0x6e74371ddb7f0db786d83b6a21b3f2d9696c74361ddaff0d7786b7c359e1abf0d5786a7c351e1a7f0d3786974b49a1a3d0d1596864b41219f90cf39675c338e19b8ecd48665cb30e19770cb386554b28659312c917644c320618f30c727634cb18618b12c508623cb0fe186f0c2f86143b082182f2c0e9
|9,0=>0x7f543f8a1fb32fd187e4c3f025f710faf97d34be7a1f2d0f8e87c2cbdf61eeb0f6d87b2c3d725ea90f4aa7a0cbce61e630f298790c3c69de250f09977fd3bda5ddb2ee4976dcbb4e1d970ec4775e43ace5d552ea2874d43a465d112e7f973b4b9ba1ccd0e5e872acb9325c872e3b8719c38ae1c452e1a87094382a1c032df986f84b7a21bbf2dd69
|9,1=>0x9064480e63f531f288f54478663b311d188e44c702236f31af88d3c467e232f118f88c3c45fa62eb316d88b24c56e62a7114a98a1444ea22651129988fd4456a21b1104987e443d221d730e3886dc434e219530c0a85c442c2214f309e984b4423a210d107d983ac41b260c9105c882954126608130379817c409a603b301588064c0121ff72ff29
|9,2=>0xa15c508a683334118a044d00227ef33ef89f3c4f7e27af13cf89e34cefa276b33ad89d2c4e762729338b99c1c4dee26e7136a99b144d6a26a3334989a04cce2265f3327898fc4c5e261f1306997eccbd625d752e3896dc4b4e259532c1995c4cac22551129f994bc4a3a650d127d993ac49b264c7325a992944922a48112388917cc89a643b32149
|9,3=>0xb234d8f2ac69162c8b11558666c2136088b00457e22bdf35e69aef457566b9b15c49addcd6c6ab5315a18accc56426b0f357f8abbc55be2acb555c9aaa455322a87353b8a994d4a66a4135188a87cd41a69fd14f68a774539a29bd14d77a67c5321e98114b79a57c529e293f14969a46cd21628f934748a364519228b914548a2645112287914339
|9,4=>0xb5645a922d3736929b44cda062cf316709b34459822caf364f8
|10,0=>0xc654630a317518b19c544e27e712d388e8c43461f670e9386b9c31c616e30a7184a9c21460e6706138288c1046062301f38078bff4dfd66fdb17e58beec5f526f9917c48bde45ece6f5717a29bcd45e466f1317818bbc4ddbe6ecd375d9baac5d362e89373c8b9a45cb22e49171b9b894dc2a2e0516f99b784db9e6dbd36d68b66cdb162d7b16b49
|11,0=>0xc84c640631f318f18c753e38a31b518d28
|12,0=>0x19117
|_,_=>0
def wAt:=mkWire dB 403 192 0xffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x10410404101016008161c82f158e1020210680b0081d020d1008160801d12013058250401d1a823020d1028070801d190480201d0581d0b81101041080c2178b902026010050401d020261602f028ad020210480904041058260801d0401d0409e1302d020150081d0801d12013048090482d0401d0407d0f0070802d010150502f0801d020250401d0581d0a80b048510401d008410582a04809020250401d
|1=>0x20d102807040410801d0104129023009460b941080090404a0581d0081d27014098050801d058211302f08009020150101d0801d058262580701841010250581d0401d0402d0802d010160401d0801d240130a02d0081d0801d008410401d23014158090801d020210502f08025020250201d0184320823020a9010160801d048411f843008a5058260401d1e8430a80b1e805080250801d04809048110401d
|2=>0x502f048110401d0087a02811010150801d0f00704015010150801d0581d081a617825010050401d1d813010163300b328410201d0581d0202d0280704011020150801d0a80b1e805080250401d3104803005040410581d03011080210401d008150801d2f01d1e9760301d058091602f1e811040150801d058260202602015008160801d00821058262a80b00815020150801d0f8210802d00816020210401d
|3=>0xf007010150801d0801d010b9048130401d05951020412a80b008150801d0201d0802d3a048010110581d081a617825010050282108009058150101d0801d040ee0101604805040410801d058250401d0502f04811008250401d020250801d040050401d0084112013040410801d058250401d0815904005020260801d0401d08159008211201305825049b80581d0401d1782d01005009b235809080a505826
|4=>0x401d0f007010150801d0281108005058150081d0801d0502f0801d020250087a080260401d0101500825080050401d0801d020210581d17995010050201d05811021f6058d9040d1008160801d0081d020413d814008110801d0502f04809048110401d0201d04011048510401d008410801d3c0130405d0401d010411d023328d1008160202d020211e80b080250201d0401d0081d310130a0210801d00841
|5=>0x3880904011008250201d0401d0201d0a0ad040110401d008410801d3303c0101d08195058111302308009020150101d0801d0801d0a0ad040110401d008410081d0102d4283c058050101d158bd008090201d0401d020210f8110802d008160081d0801d41043098090581d0401d05821078230b8110101d0801d010410a80b04011048510401d008410581d0b9950201d05811010410084104011008250201d
|6=>0x581100841008250581d0401d02025008250801d0401d0202d2a807080350081d020a90280b040150801d1b043040d1008160801d4b01d0e80b0804d058210401d0201d010110404101841010250201d0401d0225205a4d0803e0101d0081d370131782d0101d008090823e0581d328050201d058111b0430801d460430101d040a9010160801d010410409e32815058110801d05809020053a2140580502009
|7=>0x401d00821080a5058260401d082b2012ad1102f0201d0081d53813040bd010050101d0820a09809058215401d5382f040bd0100504005080250581d0401d0280b29013058150801d082910428d1100b0201d0b8ad040110401d010410201d3a024020090401d0401d04041058410581d0227d0f02f0b81d010410084113023020150801d4e84302271068230081d0090a0414a058150801d00a654c00b3281d
|8=>0x809080a51202f040490581d318130284d0801d058213c08803009040410201d1d813058a9010160801d5a013040e10680b0081d00815040d1008160801d0081d13023020150801d008b9048130401d00841042c92a82f0a01d008410a195058110801d008410480908021058250401d008b905013040890201d012b90f88a058410201d0280708011058150801d01807010250201d0401d04005020260801d
|9=>0x401d0482f1e823080250401d01025080a5058260401d0400508089040410201d08009028ad0801d0202104841010250581d0401d0581d040510401d008410300908021020250401d35823080a5058260401d0502f048110401d01041258070485d0401d01041010410280b0801d05821008210502f020250401d08025040050802d0401d0401d02813040410801d0401d05911040160801d370131782d0101d
|10=>0x202d010250502f020250401d043150682f080210081d080f104009080260401d0401d080ad0801d020210830d01813010250401d0101d031d202009080210101613023020150801d02041050071581d020210802d008160081d0801d020410201d058090581d5f83c0101d15805020214801d370131782d0100504009008250201d0401d0101d041760102d0801d5d81d082ea328090581102026010250801d
|11=>0x581d0081d0101d0080902021041760804a058090581d0a1950201d058110084101339028af0801d020212a80b05811008150801d1b02d040d1008160801d0802d0401d010150801d0800902092040490581d23007158090401d020210402d058a9010160801d0832e5e01d2e823058090401d0804a058050581d04805010250581d0401d0ba623281d0202d01041010b9020260201d0401d32b1d0083e0101d
|12=>0x328090202d0235d1784a0581d01005010110101d0082d0081d040160801d058250401d04805048110401d00841008b904813010250401d080b9020260401d0e807098410401d0582120823020a9010160801d08021058150081d0801d05b52020e10680b0081d2b01d08011040050801d318070284d0801d058210b8210101d0801d0104102021010250801d0401d688230b82d0101d010410802d3d84800811
|13=>0x588a058410201d0800905013040890201d058150280b040410801d078210101d0801d010411d823058a9010160801d2408b0201d0a02d008411e82f080250401d0082108025020250401d058410280b0801d05821083753d824020050401d688270b82d0401d010410404113023020150801d6d01d5f80b15805020211e80b1e82f040150801d058210401d008150801d23014158090801d020210101d0081d
|14=>0x482d0401d01041008161e813040150801d081a617825010050401d3c02f08059010210101d0402d01807010250401d058210101d0801d01041080111e809080250401d05b9917826010050401d0401d00821110430201d0081d428130082d0801d05825040090401d010410138a70823068110081d010151e82f040150801d020092e8880102d0201d0401d0201d0101101021080210401d008150801d012ad
|15=>0x401d0a0110081d0801d00841370231782d0101d008090482f0401d00bda01111040160801d1a82f020d1008160801d7980779041090090581d3284105811008150801d010410502f1581d02021013c13882f008250401d09bb90402d080360081d040d1020d1008160801d0a1950081d0202d00841043b1758131781d00809158e1020210680b0081d043a50a08a0201d00841020d102807040410801d1202f
|16=>0x101d0409e2a049020410581d1902f0b8110101d010413c04b03009040410581d0802504009058260401d02015028070801d0202102232040a9010160801d1302d020150101d0801d05bf60424d0803e0101d0101d0802d0801d05821080210802d0082d008210401608021058150801d023ee098350081d058210202d0081d0101d008090100502092040490581d0101d0801d0101105841258131e80908025
|17=>0x81d0244a8881d428430082d0402d048090401d010410502f048110401d010410401d028af0801d020215780b008b9020260401d2d00b080b9020260401d00c35050431581d020210081d0802d040050801d0442d3d83c020050101d019ec0b01d020050102100841008b9020260401d00c21082623281d0202d830230224d0803e0101d040d6020d1008160801d082fe158050401d0202105c0d0840907813
|18=>0x202104841008250401d8e80504325090430581d0502f1581d0100502021050bd1581d01005020218d01d0811a158090202132bae1781d010050202d0115904005020260401d0081d4780b328050202d021c11e80b080250401d1e82f02821040050801d010212e824058090401d0301d02021008160081d0801d1202f0981d00809058210101d0081d15809020210502f08021020250401d3d82f0101d00811
|19=>0x801d008410449d1788a0201d008090087a04015010150801d1e807080250581d0401d08009058150101d0801d0801d040050401d00841008160801d048113880b008250401d0b84d058210101d0104108026010250801d0401d05821080a5058260401d0402d080250581d0401d03486080210682d0081d1e9d00301d0200908021120530482d0401d008410801d01843010250401d04005048430401d0801d
|20=>0x401d08021020050801d0401d04005083150682f0081d0802538843008250401d080a5058260401d0401d158090801d0202104011020150401d0801d0801d04807080210401d058052e9ec020050580908021010250801d0401d0202538843008250401d0202d008160081d0801d020da040d1008160801d024a90b84a0581d010410502f1581d0100502021059e93d814008110801d020260401d0081605811
|21=>0x401d098410280b0801d0582100cdd0308a040410201d0900b04041058410581d020050400902009008213102f040510401d008413303f0101d081950202d04016020260801d0401d0a0a60482f0401d008411e823080250581d0401d0581d328090201d058111782501005020250401d08009010160401d0801d1e843040150081d0801d008b9010b9020260401d058090101d0082d0081d178ba0202601005
|22=>0x801d0403d080210101d0280908011058150801d0082104041058410581d0a80b1e805080250401d9e8240401d17811008091e82308025020250401d428430201d058050581d068230a02d0081d0084108021008160081d0801d1e84304015040160801d328bd0202d0101d008090301d020d1008160401d0801d5801f0a1950581100841370270401d1782d008090104132815058110801d024951e80708025
|23=>0x8b904009020260401d538480581d040bd01005120130801d058250401d110430201d0401d02021058d9040d1008160801d048510482d0401d008410202d0081d0801d00841538130401d040bd008090f1970b81d0202d010411e8431e805080250401d02021010160401d0801d1e80b08025080260401d0081d4283c058050101d0802538843008250401d014fd04953080110401d0581d0a02d0401d00841
|24=>0x328050202d1e9ee0301d02005080210801d040050802d0401d32bad1781d010050202d0581d080a5058260401d9681d2e9ec02005058090f0ad028090801d020210a80b1e805080250401d041ba0581d1782d010056081d031d202009080211e82d1e805080250401d08026028230801d0401d0201d1902f0b81101041328d1008160202d0801d010160801d0401d0201d040bd0080917d0d008090408a0201d
|25=>0x201da601d3a02f01011048090401d058210403e0102d0101d010050401d020215d01f328090202d04005080250401d0801d01011040411e84304015040160801d178210081d0101d008093482f0b035010210081d178a505826010050401d02005058090200905805080090401d0801d02021020211e80b080250401d010410282d020150801d08021010160401d0801d020410581d058410201d0081d0801d
|26=>0x101d008090401d0801d058211302f020150801d04807080250401d068230081d00841158090401d0202102005058410201d010b9020260401d014b9008260401d04841010250401d040510401d008412b03e008210101d068130082d0081d042160082d0801d0201d2e8430102d02807058150801d05add020160801d082160082d00821020090782d0101d0581d0102d008110282f040410801d1301311041
|27=>0xd753a01f020096881f0b82d0104170843110050201d178890201d010050101d008110081d1e811040150801d04809008250401d05a4d0803e0101d2b009008210101d05d61010260401d02485090050581d080210801d0401d048510401d008410201d01011040410482f0401d0104104005058260401d040a9010160801d020150081d0801d0114a090410581d1e80b080250401d01386068110081d0081d
|28=>0x202d05911040160801d02005058410581d0081d02005020410401d0580501021040350081d0801d1300b020150801d098350081d058210e81f0804d058210583d010210101d040150101d0801d158090801102021428880082d0201d01021040410581d05b91110430201d0301d02005080210201d0401d0104142826058050401d008210201d0401d04041058410581d020a9010160801d1202f040490581d
|29=>0x2e8430102d08271068230081d08011040160801d1e809080250401d078410101d020210101102005010212a8230a01d008411100b040410201d2a01d0102d0204108021080260401d0259d0782f0101d040d1008160801d028090801d0202102041008110404105821078070101d0101d3a0430101108591110070201d0402d068090081d0081d00811058410480b008250401d03005040410581d0801d08195
|30=>0x424d0803e0101d048050401d0084105841058160801d020090682d0081d00821110430201d048130401d02021010050201d0401d0402d0401d010410a04a0581d0084104041008150801d04151020410201d0582a040890201d2e88b0102d0201d0101d0081d0582105826010050401d028050801d058213a007010110101d04843008250401d3c0130405d010410104a058410581d040110803e0101d0253d
|31=>0x821078410101d058110102d4281f0082d178110101d008090101d328050202d0401d010150801d04041008250401d048530401d00841a801d42823058050b81d0202d01041020412e81f0102d0f0130b81d01041008160081d0801d05836080110081d3a02f010110101d05d91110070201d3a007020090401d02821040050801d0282d040050801d2b17605809008210081d3d823020050101d0200902005
|32=>0x80250401d040090802d0401d12013058250401d010051102d0201d0107d058410581d0b01d0101101021370131782d010050401d178110080908025058250401d044860682d0081d328360081d0202d080210201d0401d08011058150801d0820a098090582138843008250401d3882f008250401d058110803e0101d058050581d0401d0482f080210401d0682d010210081d0482f0401d01041080210802d
|33=>0x81d081950202d158bd01005020210408a020410201d0453d2e8430102d05826010050401d080b9020260401d0b8110101d01041bc8213d81f020050801d0802d0401d17825010050401d0f8360802d0081d70821068110081d1e843040150801d082ad1102f0201d1e813040150801d2e836058090081d00825058250401d031d202009080213d824020050401d020413d81f008112e9ee02005058091e807
|34=>0x802100b91110430201d041ba1782d0100500aad1102f0201d048530401d0084104009020090082105e153d80b02005028210801d01041058160401d0801d0b8110401d010410201d0b82d0104102813020150801d020090801d0401d3880b008250401dc182f078110101d040050081d0801d021760102d02041098410401d058210304a040410581d020d1008160801d010360081d0202d008210801d00841
|35=>0xa01d008410280b040150801d00821020250401d0081d328050202d04009008210101d0b035010210081d010f1080260401d045ad3a00702009120130981d058210462d090070581d0081d0801d008415382f040bd0100505911040160801d3a017010110801d081c6008250401d1902f0b81101041028110801d020210284d0801d058212e9ec02005058090201d2e8070580904035080210081d031ed02005
|36=>0x401d0101101021008260801d0401d010250801d0401d04841008250401d04035010210081d17826010050401d3a21505805020090101d0202d010410101d00809020210295b040050801d3301f081950202d01016010150801d01005020250401d042dd020160801d0802d0082d0082104015040160801d020210101d0104108021040050801d328160202d0801d0201d0400500841080212e81f058092a80b
|37=>0x801d758131781d00809082623281d0202d1781d0100502021042dd020160801d04049058410581d0201d008210102100821010260401d04807080210401d1e82f040150801d00911040160801d040050401d0084102811058150801d00821080260401d04005058410581d0081d008210101d0580902009058051e843040150801d05841020160801d08021068110081d0083e008210101d0202d0101d00809
|38=>0x682d0081d0200508021090110581d058150801d2e82105809328050202d0680b0081d068210081d04005008410581d0401d040160801d040410801d0801d05821110090201d0b81d010410404a0581d020250401d0581d01005080110081d020090401d008210081d0581d008414281f058052e80705809040490581d0808a0201d0401d028230801d0401d0201d0581d010051781d010050202d010160401d
|39=>0x801d010410405100841058050200901005020210800902021110430201d00821010210581d0201d010050401d0101d00809020090081d0802d00821008260401d010250401d008210401d010160801d0101d01041020410581d080260401d1100b0201d0801d0401d020090201d008260401d0200502009080210082115805020213a005020093a043010110082d020410082d00821040410201d040bd01005
|40=>0x80210202d020210101d01021020090401d080250401d010160801d3281d0202d010050202d4281d05805040150801d040050801d
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x15501140000000000d40000000000940045000000000004
|7,0=>0xe050dc40d750d25000000000cd50c940c450c040bd30b940b540b050ae20a950a540a2309d5098500000944090408f108e1000008b3089208540823081107c5000007a207550000070506b506a1065500000000060505b5056505330512000004d40485044403f503d203c103750343031302d402850235022101f3000001a5
|7,1=>0x19650000191518f218a518551805000017b500001765171516c51675162515d51585153514e51495144513f513c3137500001343130412b512651215000011c500001184113510e510a41055100500000fd30f940f450ef50ec30e750e520000
|8,0=>0x2974293428f428b42874283427f427b42774273426f426b42674263425f425b42574253424f424b42474243423f423b42374233422f422b42274223421f421b42174213420f420b4207420341ff41fb41f741f341ef41eb41e741e341df41db41d741d341cf41cb41c741c341bf41bb41b741b341af41ab41a741a3419f419b4
|8,1=>0x3954391438d438943854381437d437943754371436d436943663362435e435a43564352434e434a43464342433e433a43364332432e432a43273323431f431b43174313430f430b4307430342ff42fb42f742f342ef42eb42e742e342df42db42d742d342cf42cb42c742c342bf42bb42b742b342af42ab42a742a3429f429b4
|8,2=>0x493148f448b44874483447f447b44774473446f446b44674463445f445b44574453444f444b44474443443f443b44374433442f442b44274423441f441b44174413440f440b4407440343ff43fb43f743f523f143ed43e943e543e143dd43d943d543d143cd43c943c543c143bd43b943b543b143ad43a943a543a1439d43994
|8,3=>0x58b45874583457f457b45774573456f456b45674563455f455b45574553454f454b45474543453f453b453745334530352c452845244520451c451845144510450c45084504450224fe44fa44f644f244ee44ea44e824e444e044dc44d844d444d044cc44c844c444c044bc44b844b444b044ac44a844a444a0449c449844944
|8,4=>0x6664662465e465a46564652464e464a46464642463e463a46364632462e462a46264622461e461a46164612460e460a46082604460045fc45f845f445f045ec45e845e445e045dc45d845d445d045cc45c845c445c045bc45b845b445b045ac45a845a445a0459c459845944593158f4
|9,0=>0x72737243721371e371b371837153712370f370c370937063703370036fd36fa36f736f436f136ee36eb36e836e536e236df36dc36d936d636d336d036cd36ca36c736c436c136be36bb36b836b536b236af36ac36a936a636a336a0369d369a369736943691368e368b368836853682367f367c3679367636733670366d366a3
|9,1=>0x7e737e437e137de37db37d837d537d237cf37cc37c937c637c337c037bd37ba37b737b437b137ae37ab37a837a537a2379f379c3799379637933790378d378a378737843781377e377b377837753772376f376c3769376637633760375d375a375737543751374e374b374837453742373f373c3739373637333730372d372a3
|9,2=>0x8a738a438a1389e389b389838953892388f388c3889388638833880387d387a387738743871386e386b386838653862385f385c3859385638533850384d384a384738443841383e383b383838353832382f382c3829382638233820381d381a381738143811380e380b38083805380237ff37fc37f937f637f337f037ed37ea3
|9,3=>0x96739643961395e395b395839553952394f394c3949394639433940393d393a393739343931392e392b392839253922391f391c3919391639133910390d390a39073904390138fe38fb38f838f538f238ef38ec38e938e638e338e038dd38da38d738d438d138ce38cb38c838c538c238bf38bc38b938b638b338b038ad38aa3
|9,4=>0x98b398839853982397f397c3979397639733970396d396a3
|10,0=>0xa0c2a0a2a082a062a042a022a0029fe29fc29fa29f829f629f429f229f029ee29ec29ea29e829e629e429e229e029de29dc29da29d829d629d429d229d029ce29cc29ca29c829c629c429c229c029be29bc29ba29b829b629b429b229b029ae29ac29aa29a829a629a429a229a0299e299c299a29982996299429922990298e2
|11,0=>0xa141a131a121a1110000a101a0f1a0e1
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 16
def pmP:Nat→Nat
|0=>0x2808000000000000000024490000000000000000240300000000000000002049000000000000000020180000000000000000201000000000000000002009000000000000000020000000000000000000185100000000000000001809000000000000000018010000000000000000144900000000000000000200000000000000000001040000000000000000010100000000000000000080000000000000000000680000000000000000005e0000000000000000005000000000000000000041000000000000000000400000000000000000003000000000000000000028000000000000000000200000000000000000001800000000000000000011000000000000000000100000000000000000000800000000000000000006000000000000000000020000000000000000000100000000000000000000
|1=>0x862790000000000000008404000000000000000082100000000000000000820790000000000000008206900000000000000082050000000000000000808b90000000000000008081900000000000000080180000000000000000801380000000000000008010500000000000000080101000000000000000800680000000000000008003100000000000000080010000000000000000800010000000000000006a2710000000000000005523900000000000000050060000000000000000400000000000000000002200e0000000000000001a2f900000000000000010000000000000000000084780000000000000000800000000000000000007f0100000000000000004f390000000000000000407800000000000000004041000000000000000040390000000000000000400000000000000000002853
|2=>0x10a03100000000000000100000000000000000000f8240000000000000000ea270000000000000000da2f9000000000000000da235000000000000000d6279000000000000000ca279000000000000000c8278000000000000000aa2f9000000000000000aa279000000000000000a22790000000000000009a279000000000000000922790000000000000008e2790000000000000008bf790000000000000008b8790000000000000008b2f90000000000000008b2790000000000000008af790000000000000008aa7b0000000000000008aa790000000000000008a8f90000000000000008a6790000000000000008a3790000000000000008a2fd0000000000000008a2f90000000000000008a27d0000000000000008a2790000000000000008a0790000000000000008727d0000000000000008627d
|3=>0x801029000000000000008010090000000000000080100100000000000000800460000000000000008002200000000000000080004100000000000000800040000000000000008000200000000000000080000000000000000000500000000000000000004a7279000000000000004a3f7d000000000000004a2f7d0000000000000048a2500000000000000048727b0000000000000048227b0000000000000048210100000000000000422f1b0000000000000042271900000000000000403f350000000000000040300100000000000000402440000000000000004000000000000000000038a2790000000000000029b2790000000000000028a2f90000000000000028000900000000000000280008000000000000002108a9000000000000002086400000000000000018a2790000000000000018a079
|4=>0x400800000000000000004004001000000000000040000000000000000000308020100000000000000d0c45900000000000000c8f27900000000000000c8ef7900000000000000c8ee7900000000000000c8e47900000000000000c8e27900000000000000c87d7900000000000000c87d7100000000000000c04d0900000000000000ad227900000000000000a92ff900000000000000a83f7900000000000000a82f7900000000000000a04f3900000000000000893ff90000000000000088b2f90000000000000088a2f90000000000000088a27900000000000000883ff900000000000000883f7900000000000000882ff9000000000000008118b900000000000000808660000000000000008080680000000000000080373100000000000000802fb9000000000000008018f0000000000000008014e9
|5=>0x20c890190000000000002008812000000000000020000080000000000000180080420000000000001008a2790000000000001008a2190000000000001000800a00000000000008c8f67900000000000008c8e6790000000000000810a0010000000000000810802100000000000008101459000000000000080aac7d000000000000080aa2790000000000000808bc790000000000000808a67b0000000000000808a6790000000000000808a279000000000000080200500000000000000800600800000000000008005c490000000000000800404100000000000004c8f3790000000000000448a31b0000000000000448001000000000000004480001000000000000040aa279000000000000040a210c0000000000000408a27b0000000000000408a0790000000000000408601000000000000004010230
|6=>0x20000a218000000000001c00d82400000000000014008a258000000000001208000b1000000000001208000a9000000000001200862790000000000012008001d000000000001200040b1000000000001200040a90000000000012000200c000000000001040880120000000000010088b2b90000000000010088a2f9000000000001000d92810000000000010008b2790000000000010008a2790000000000010000a0580000000000010000200a0000000000010000000400000000000048c0d4590000000000004808a6790000000000004800600000000000000040d8e479000000000000409010610000000000004088b6f90000000000004088a6f90000000000004018b259000000000000400d42780000000000004008b2f90000000000004008a67d0000000000004008a2f900000000000024c8e279
|7=>0x100000823800000000000a0008a2790000000000080008a27900000000000800000000000000000005000ca2b500000000000400a8a2f9000000000004008927f9000000000004002da2f9000000000004002cb2f90000000000040028a2f900000000000400288a390000000000040028808000000000000400282f790000000000040021004900000000000400208008000000000004001492f9000000000004000ca2790000000000040008a2790000000000040008827800000000000400088230000000000003001082280000000000026012a2080000000000024818a2790000000000024001827900000000000208009859000000000002009082790000000000020018a07900000000000200108859000000000002001020420000000000020008a279000000000002000880590000000000020000a230
|8=>0x10000020000000000000100000024610000000000810008a2060000000000804002a2590000000000802018a258000000000080084aa27b000000000080040aa27b000000000080004ab27f000000000080004aa27f0000000000800010b259000000000080000a8213000000000080000a227b0000000000800008a270000000000080000862790000000000800000a2590000000000800000621b0000000000420010a60c0000000000204018a2790000000000202009a279000000000020001000000000000000136018a2790000000000114008a0580000000000112408b279000000000011000aa811000000000011000820010000000000100408a879000000000010002882790000000000100008a8790000000000100008a27900000000001000088278000000000010000880310000000000100000a230
|9=>0x82040088278000000000820000ba27000000000080020ada279000000000800202da261000000000800040040010000000008000088a279000000000800000da3790000000008000008a279000000000700000ca279000000000682000fa279000000000580080aa6790000000005000008a2790000000004202008a279000000000420000800000000000004000048b6790000000004000048a27d000000000400004020080000000004000010a2590000000004000008a2790000000004000002a65900000000040000000201000000000300008ca2f90000000002044014867900000000020100988278000000000200401862790000000002000088a67900000000020000258279000000000200000da27900000000020000000200000000000102008ca2790000000001000088af79000000000100000a0001
|10=>0x40000801022000000000400000a97279000000004000004a627b000000004000000ca2790000000040000009a279000000004000000000000000000020024808b6790000000020004808a2590000000020000008a279000000002000000102d9000000001f0200048279000000001602000d8269000000001084000ea2fd000000001080040fa279000000001080040aa279000000001080000fa2fd000000001080000f2279000000001080000a227900000000100403082779000000001004010ca2fd000000001002001000600000000010000a072021000000001000060fa2790000000010000408a3790000000010000408a279000000001000030820790000000010000018a2790000000010000008aa790000000010000008a279000000001000000883000000000010000000087100000000100000000200
|11=>0x200200008e3790000000200102408b3790000000200100448a31d0000000200012408e1790000000200012408e07900000002000004c8c119000000020000020ca2790000000200000008a27d0000000200000008a279000000011001000ca2310000000110010008a3790000000108102008b3f90000000100110048b3190000000100102008b2b90000000100012008b2790000000100010008b3790000000100010008b2790000000100010008a3f90000000100010008a37b00000001000000c8e27900000001000000c8e1790000000100000008b1790000000100000008a27900000000c00000801221000000008004002cb2f9000000008000000803010000000040800402220b000000004080000a227b000000004001208962790000000040004058627b0000000040004042264300000000400008a10269
|12=>0x1400000008227900000010000104082cb100000010000104081c19000000100000000a2c3d0000000b003120c8e37900000009001100c8a2790000000804815008a27b000000080011040820790000000800050008a2790000000800010008a2790000000420000008a2790000000410000014a2710000000402020018a6f90000000402000008a2790000000400040008a6790000000400040008a2790000000400024098a2f90000000400024018b6790000000400024018b2790000000400024008b2f90000000400004098a2f9000000040000010ca2790000000400000088a2790000000400000048b27d00000004000000400400000000040000003482790000000400000018a4790000000400000008a279000000040000000192790000000300000008a01c0000000240a00008a3790000000208202088a379
|13=>0x20000000080010000000200000000252219000002000000000db2f9000002000000000ca2790000020000000008a27900000110000008182c790000011000000008223b00000100000008100c59000000c00000040891090000008400000008ae790000008100010408a9790000008010100000006000000080100104088121000000800010000020420000008000020818a0790000008000010408b3790000008000010408a9f90000008000010008b3790000008000000819acf90000008000000818bc7900000080000008008459000000800000008881280000008000000040a4480000008000000018a279000000800000000899090000004000000040a0100000002100000008a279000000204000002d2079000000200080000fa270000000200000000ca2790000002000000008a27900000018100000082239
|14=>0x400002060d8e0790000040000200008224000000400000240c8e6790000040000010008a2790000040000000009a67900000400000000080040000002200104008ca279000002200000080d2079000002200000001da079000002200000000da2f9000002200000000ca27900000204800000b8b2f9000002040200408cb2f9000002040200408ca2f90000020400000008a279000002010000008ca2790000020040000088e279000002002a00008d8278000002000820200da379000002000801000db3790000020008000088b3790000020008000008b2790000020002002008a2790000020002000088a2f90000020000100088a2790000020000040088a279000002000000408d82f9000002000000208d82790000020000002009a279000002000000008da2f90000020000000088b37900000200000000882779
|15=>0x8090011000aa2790000080200102408a27d0000080200100408a37d0000080100110048b279000008001880000ea279000008001804000ca3790000080008300008a3790000080000803008a37b000008000080200aa27b0000080000110008a2790000080000001008a3790000080000000048a3790000080000000048a27900000800000000402009000008000000000aa2190000080000000008a2790000080000000000802000000800000000000001000006200200001da679000006000820400da2790000060000010088a2790000040808114088a2790000040804010048a2790000040804000008a2790000040800000008a27900000402000100c8a07900000400200040d8e6790000040008000008a2790000040007020008a6790000040004002048a2790000040002200089827800000400002160184058
|16=>0x200810010018a2790000200800010018a0790000200404024018a27b000020040002001822790000200400000008a0790000200004132018a2580000200000800018a25a0000200000202018a2790000200000040008a2790000200000000008a27900001c000080404aa258000018000080000aa2790000108000000008a27900001002003120482379000010004000040aa27b000010002000000aa2790000100020000008a2790000100004400048a279000010000080004ab27d000010000080000a627b0000100000420008a2790000100000020802a2590000100000001048a3790000100000000048b3790000100000000048af790000100000000048a279000010000000000aa2790000100000000008a27900000c0820000008a27900000c0004800008a27900000c0000a0001aa2790000080918901008a279
|17=>0x100200000000da270000100004080000aa27b0001000040800002224a0001000020026008a279000100001080000fa279000100001080000aa27900010000101900180060000100001000020fa2790001000010000008a279000100000080000aa27b00010000000b0018a07900010000000000c8e07900010000000000ada2790001000000000080004800010000000000210270000100000000000aa2790001000000000009a2790001000000000008a079000080000000008830790000400100800008a2790000400040000048327900004000400000082300000040004000000803010000240804112008a279000024080120000aa27900002408000000c8e2790000240000090018a2790000240000090008a27900002400000000082279000022240202001da2790000220008224018a27900002100000000082079
|18=>0x4040000000009a679000400200800000fa279000400200000080ba279000400200000000fa2f90004000009000008a279000400000180000aa2fd0002202005020018a2790002080100911048a37d0002080001000008a279000208000100000020200002080000801048a37d000208000000000120210002040804010008a2790002002003000008a67d000200200200001da67d000200200000000da2fd000200200000000ca2790002000101000008a2fd00020000110000092ff90002000005000008a279000200000100000b2ffd000200000100000a2f79000200000100000921a50002000001000008aef900020000010000002020000200000000104aa27d000200000000000928b40001080004130018a279000104000200000da27900010400002040c8e079000102202a00000da2790001020020026009a279
|19=>0x80000000080040a0100080000000080040a0080046080000000008a2790040000000100009a23100260c200200001da279002500002a02000aa2790024082002000008a279002008002402000ba2700020040002000008a2790020000002000008a2790010000208100408a2f90010000208040008a2790010000000100088823900080080200008c8a079000800800000080080280008000020020008a2790006082000001009a2790006080108900008a2fd0006080000800008a2fd0006002001040008a27900042c0006820008a279000428200f82000ca279000420280100000ca279000418000480001aa279000418000080000aa27d0004100024820808a27d000410000480001aa27d000410000081000aa079000408200980000ca2fd000408020080000ba235000408000990000aa279000408000180000ba279
|20=>0x800100002a020008a2798000002009000008a2794000200800800008a279200002a00000080da079100020080000000ca279100000040000000ca279085000000004010ca2790800082000001008a279080000091011020822790400180004000048a2790400000020020008a279040000000000000080000200000000000088a079020000000000000870d90200000000000008207b0100000020801008a27901000000000000000200008100000008000080280080000020020008a279
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x24040000001400000030300000004
|7,0=>0x174003ac2c0981a55400270003fc72358ec551000350f4543137c6509c330001001c643800a0013c000045991d010a6348002742b0350a09c1c17800210183d0b4000000c40517c0104c0102c0c430ea278270a0a000001020691dc000451f00405084d70007601800558ce0a40c00000328de6081504800334791f4b9178fc06811008bd33c31568130001f
|8,0=>0x2f1a54ae029615e3750708d1755e1748daa2b13a654bf6846a57d789e06168dab3c6561e0e8364c8685c4389182911c4fd524b90240e329c56138e7c2a9843991e2ed0855d9c60c6c5f9697c5ee414c48684385a494b20407c164bd726981e3c0d505c1da1019678c72a49b170e188c4355da16f8db18d573b5a9404d00f9200e4812ec5a829842013284cba7d98e55cdc5a5892ecf26a82d0d425811738a557
|8,1=>0x161909fdbb06cd03166361a0f0e04a2ae445091023a474d84a7042a1fc7b5f57c241371d0be09047185a04e14003cd0a147a588fa27def4446e39cb1745f43b86d20836229b440e0455c328fc6f1f1306fc222d6626753e6ec0e6e57a951f2229c54e25b3d4fd810309cde767d1b6101f4ec349fa04561d3331d88ed4b8543d4f42fa0a8676a1b8c5b2611bb0d0575dda1340d82d837519162b51a8a858351e1
|8,2=>0x25150160ee9a8a829c3a1050b73938318583924c8122d651f02149386681a1cfb3ba4510db86c04818a335d9575a0a11ad2420d034a60d7798c1f84369d284942e2611361cd7
|9,0=>0x64a3e789811650d8062495c8c62d344e661814f87767b34d065d4b01855e425987a25d50560980918b10e2968956cc08ad659b95c3462814227146115d0b2851eb529ec935d48f0c9885cd949c284a8f9c2651d5fe9dd88895cb5b5d95b98d368e5a2e8371e8a979b792e1054db64884d3bdfc08049449638720693d4f2bde6240677f5ea4124a1d0f715643499e949e2672268964b866a032cd355228822608
|9,1=>0x2201473cf67808763e5c9ac99909cc15a3a9548f1cc86940ef9a636545bca020c6cd6b7489a4648c8d0f64c5a4105af9065a68a079f6206a092628977cdc6a417b9c92d94dbd741eba35973be6da44712ddf86659b8266c991c24cd591857f8bcfa9028c5c60e5104f7de7432d4d76dd5255965aa5f6b5f04e180791c0309ba8e61d99e8e7e9ac75c535c1df82cf96463064c4f9444b30e3d78dfb9e95d234f3
|9,2=>0x6b89687e38101793f9495b0e993a48
|10,0=>0x1343f8d6378889a22c7059e7951ca3770468794353a6f30521918450fd148604c770437d84c7e44e9d6007c1c94a96f531ed72a3579666a48527586661496134ae7fd64181b5515c37d45b1a2764b5b1
|11,0=>0x1362e288540ec447c042
|12,0=>0x3c
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 10 (j%128);fld (pmP (k/32)) 80 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_190 10 roots_190 ops++addP pm 1 dom_151 8 roots_151 ops++addP pm 2 dom_182 8 roots_182 ops++addP pm 3 dom_159 10 roots_159 ops++addP pm 4 dom_63 10 roots_63 ops++addP pm 5 dom_189 10 roots_189 ops++addP pm 6 dom_187 10 roots_187 ops++addP pm 7 dom_188 8 roots_188 ops++addP pm 8 dzo_46_16 5 roots_46 ops++addP pm 9 dom_149 7 roots_149 ops++addP pm 10 dzo_58_4 5 roots_58 ops++addP pm 11 dom_62 6 roots_62 ops++addP pm 12 dom_158 8 roots_158 ops++addP pm 13 dom_183 10 roots_183 ops++addP pm 14 dom_31 6 roots_31 ops++addP pm 15 dom_170 7 roots_170 ops++addP pm 16 dom_61 7 roots_61 ops++addP pm 17 dom_55 7 roots_55 ops++addP pm 18 dzo_189_2 7 roots_189 ops++addP pm 19 dom_175 10 roots_175 ops++addP pm 20 dom_59 7 roots_59 ops++addP pm 21 dom_157 8 roots_157 ops++addP pm 22 dzo_23_8 5 roots_23 ops++addP pm 23 dzo_29_2 5 roots_29 ops++addP pm 24 dom_180 5 roots_180 ops++addP pm 25 dom_53 5 roots_53 ops++addP pm 26 dom_174 8 roots_174 ops++addP pm 27 dom_186 8 roots_186 ops++addP pm 28 dzo_55_8 6 roots_55 ops++addP pm 29 dom_143 8 roots_143 ops++addP pm 30 dom_155 8 roots_155 ops++addP pm 31 dom_153 5 roots_153 ops++addP pm 32 dom_47 7 roots_47 ops++addP pm 33 dzo_187_4 7 roots_187 ops++addP pm 34 dzo_61_2 6 roots_61 ops++addP pm 35 dom_43 5 roots_43 ops++addP pm 36 dzo_175_16 7 roots_175 ops++addP pm 37 dzo_43_16 5 roots_43 ops++addP pm 38 dom_178 5 roots_178 ops++addP pm 39 dzo_183_8 7 roots_183 ops++addP pm 40 dzo_53_2 5 roots_53 ops++addP pm 41 dom_185 7 roots_185 ops++addP pm 42 dom_179 7 roots_179 ops++addP pm 43 dom_173 7 roots_173 ops++addP pm 44 dom_181 8 roots_181 ops++addP pm 45 dzo_59_4 6 roots_59 ops++addP pm 46 dom_21 4 roots_21 ops++addP pm 47 dom_156 5 roots_156 ops++addP pm 48 dzo_174_16 6 roots_174 ops++addP pm 49 dzo_47_16 6 roots_47 ops++addP pm 50 dzo_186_4 6 roots_186 ops++addP pm 51 dzo_171_16 6 roots_171 ops++addP pm 52 dzo_170_4 5 roots_170 ops++addP pm 53 dzo_181_2 6 roots_181 ops++addP pm 54 dom_142 5 roots_142 ops++addP pm 55 dom_42 4 roots_42 ops++addP pm 56 dzo_170_16 5 roots_170 ops++addP pm 57 dzo_157_2 6 roots_157 ops++addP pm 58 dzo_43_4 5 roots_43 ops++addP pm 59 dom_167 7 roots_167 ops++addP pm 60 dzo_151_8 6 roots_151 ops++addP pm 61 dzo_171_4 6 roots_171 ops++addP pm 62 dom_150 5 roots_150 ops++addP pm 63 dzo_149_8 5 roots_149 ops++addP pm 64 dom_171 8 roots_171 ops++addP pm 65 dzo_53_8 5 roots_53 ops++addP pm 66 dzo_181_8 6 roots_181 ops++addP pm 67 dom_154 5 roots_154 ops++addP pm 68 dom_172 5 roots_172 ops++addP pm 69 dom_161 4 roots_161 ops++addP pm 70 dom_166 5 roots_166 ops++addP pm 71 dom_139 5 roots_139 ops++addP pm 72 dom_147 5 roots_147 ops++addP pm 73 dzo_149_2 5 roots_149 ops++addP pm 74 dom_163 5 roots_163 ops++addP pm 75 dom_165 5 roots_165 ops++addP pm 76 dom_177 5 roots_177 ops++addP pm 77 dom_184 5 roots_184 ops++addP pm 78 dom_135 5 roots_135 ops++addP pm 79 dom_169 5 roots_169 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_191 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54|h55|h56|h57|h58|h59|h60|h61|h62|h63|h64|h65|h66|h67|h68|h69|h70|h71|h72|h73|h74|h75|h76|h77|h78|h79
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_46_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_58_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_189_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_23_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_29_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_55_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_187_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_61_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_175_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_43_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_zo_183_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_53_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_zo_59_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_zo_174_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_zo_186_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_zo_171_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h52;exact cpcs (by decide +kernel) lowS_zo_170_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h53;exact cpcs (by decide +kernel) lowS_zo_181_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h54;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h55;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h56;exact cpcs (by decide +kernel) lowS_zo_170_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h57;exact cpcs (by decide +kernel) lowS_zo_157_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h58;exact cpcs (by decide +kernel) lowS_zo_43_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h59;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h60;exact cpcs (by decide +kernel) lowS_zo_151_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h61;exact cpcs (by decide +kernel) lowS_zo_171_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h62;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h63;exact cpcs (by decide +kernel) lowS_zo_149_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h64;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h65;exact cpcs (by decide +kernel) lowS_zo_53_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h66;exact cpcs (by decide +kernel) lowS_zo_181_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h67;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h68;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h69;exact cpcs (by decide +kernel) lowS_161 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h70;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h71;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h72;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h73;exact cpcs (by decide +kernel) lowS_zo_149_2_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h74;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h75;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h76;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h77;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h78;exact cpcs (by decide +kernel) lowS_135 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h79;exact cpcs (by decide +kernel) lowS_169 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_190 10 s (0,roots_190.map (·&&&dom_190)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_191 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_190 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_191==dom_191)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_191 gM v ys):RunD true dom_191 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_191 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 14 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 113 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 113 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 312 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 56 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 312 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 256 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_256 : ∀ i, 256 ≤ i → i < 268 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 256 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 268 → Z 9 i = true := (range_split z9_0 (range_split z9_128 z9_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 64 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 8 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 1 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 1 0 = true)
theorem checked (s:Nat) (hs:s≤12):∀ i<NN s,bar dom_191 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 7 6=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤12) (h:RunD true dom_191 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_191 roots_191 goal_191 13:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_191
theorem lowS_191:Lower true dom_191 roots_191 goal_191 13:=S_191.noCircuit
theorem lowS_239:Lower true dom_239 roots_239 goal_239 12:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,1,5)] (by decide +kernel) lowS_235
theorem lowS_247:Lower true dom_247 roots_247 goal_247 12:=lower_slice_b [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,32,34)] (by decide +kernel) lowS_245
namespace S_254
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(2,130),(4,20),(4,132),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(8,136),(12,14),(12,28),(12,44),(12,76),(12,140),(16,20),(16,144),(18,22),(18,26),(18,50),(18,82),(18,146),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,40),(32,96),(32,160),(36,38),(36,44),(36,52),(36,100),(36,164),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,72),(64,96),(64,192),(68,70),(68,76),(68,84),(68,100),(68,196),(80,82),(80,84),(80,88),(80,112),(80,208),(128,130),(128,132),(128,136),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x15555555400000001555555540000000155555554000000015555555400000002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80005500550055005500550055005500550055005500550055005500550055005500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a11111111111111111111111111111111111111111111111111111111111111112aaaaaaaaaaaaaaa80000000000000002aaaaaaaaaaaaaaa80000000000000005555555555555555555555555555555500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ac688
|_=>0
def sO:Nat→Nat→Nat
|11,0=>7
|_,_=>0
def wAt:=mkWire dB 7 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_190 10 roots_190 ops++addP pm 2 dom_250 10 roots_250 ops++addP pm 3 dom_246 10 roots_246 ops++addP pm 4 dom_238 10 roots_238 ops++addP pm 5 dom_222 10 roots_222 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_222 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
  · simp [NN] at hi
  · simp [NN] at hi
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
theorem lowS_223:Lower true dom_223 roots_223 goal_223 13:=lower_iso_b isoMvS_223 (by decide +kernel) lowS_191
def isoMvS_251:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_251:Lower true dom_251 roots_251 goal_251 12:=lower_iso_b isoMvS_251 (by decide +kernel) lowS_239
def isoMvS_253:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_247
def dzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def gzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0e00000f0e00000e0a0000
def gsh_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0e00000f0e00000e0a
theorem lowS_zo_235_16_106:Lower true dzo_235_16 roots_235 gzo_235_16 9:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_16) [(dom_235,16)] (by decide +kernel) (lower_slice_b (T:=gsh_235_16) [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_106)
def dzo_250_4:=0x5050505050505050505050505050505050505050505050505050505050505050
def gzo_250_4:=0x5050505050505050505050505050505050505050505050405050504050504000
def gsh_250_4:=0x505050505050505050505050505050505050505050505040505050405050400
theorem lowS_zo_250_4_106:Lower true dzo_250_4 roots_250 gzo_250_4 9:=lower_iso_b (d1:=dom_250) (r1:=roots_250) (T1:=gsh_250_4) [(dom_250,4)] (by decide +kernel) (lower_slice_b (T:=gsh_250_4) [(0x505000005050000050500000505000005050000050500000505000005050000,0,16),(0x505050505050505050505050505050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_106)
def dzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def gzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000fffe0000fffe0000fefa0000
def gsh_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000fffe0000fffe0000fefa
theorem lowS_zo_239_16_106:Lower true dzo_239_16 roots_239 gzo_239_16 10:=lower_iso_b (d1:=dom_239) (r1:=roots_239) (T1:=gsh_239_16) [(dom_239,16)] (by decide +kernel) (lower_slice_b (T:=gsh_239_16) [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,0,1),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_106)
def dzo_238_16:=0x5555000055550000555500005555000055550000555500005555000055550000
def gzo_238_16:=0x5555000055550000555500005555000055550000555400005554000054500000
def gsh_238_16:=0x555500005555000055550000555500005555000055540000555400005450
theorem lowS_zo_238_16_106:Lower true dzo_238_16 roots_238 gzo_238_16 9:=lower_iso_b (d1:=dom_238) (r1:=roots_238) (T1:=gsh_238_16) [(dom_238,16)] (by decide +kernel) (lower_slice_b (T:=gsh_238_16) [(0x505000005050000050500000505000005050000050500000505000005050,0,4),(0x555500005555000055550000555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_106)
def dzo_110_16:=0x55550000555500005555000055550000
def gzo_110_16:=0x55550000555400005554000054500000
def gsh_110_16:=0x5555000055540000555400005450
theorem lowS_zo_110_16_106:Lower true dzo_110_16 roots_110 gzo_110_16 8:=lower_iso_b (d1:=dom_110) (r1:=roots_110) (T1:=gsh_110_16) [(dom_110,16)] (by decide +kernel) (lower_slice_b (T:=gsh_110_16) [(0x5050000050500000505000005050,0,4)] (by decide +kernel) lowS_106)
def dzo_122_4:=0x50505050505050505050505050505050
def gzo_122_4:=0x50505050505050405050504050504000
def gsh_122_4:=0x5050505050505040505050405050400
theorem lowS_zo_122_4_106:Lower true dzo_122_4 roots_122 gzo_122_4 8:=lower_iso_b (d1:=dom_122) (r1:=roots_122) (T1:=gsh_122_4) [(dom_122,4)] (by decide +kernel) (lower_slice_b (T:=gsh_122_4) [(0x5050000050500000505000005050000,0,16)] (by decide +kernel) lowS_106)
def dzo_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_123_4:=0xf0f0f0f0f0f0f0e0f0f0f0e0f0f0e0a0
def gsh_123_4:=0xf0f0f0f0f0f0f0e0f0f0f0e0f0f0e0a
theorem lowS_zo_123_4_106:Lower true dzo_123_4 roots_123 gzo_123_4 9:=lower_iso_b (d1:=dom_123) (r1:=roots_123) (T1:=gsh_123_4) [(dom_123,4)] (by decide +kernel) (lower_slice_b (T:=gsh_123_4) [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0,1),(0xf0f00000f0f00000f0f00000f0f0000,0,16)] (by decide +kernel) lowS_106)
def dzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0e0f0f0e0a0
def gsh_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0e0f0f0e0a
theorem lowS_zo_251_4_106:Lower true dzo_251_4 roots_251 gzo_251_4 10:=lower_iso_b (d1:=dom_251) (r1:=roots_251) (T1:=gsh_251_4) [(dom_251,4)] (by decide +kernel) (lower_slice_b (T:=gsh_251_4) [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0,1),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,0,16),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_106)
namespace S_255
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,65),(1,129),(2,10),(2,34),(2,66),(2,130),(3,7),(3,11),(3,19),(3,35),(3,67),(3,131),(4,5),(4,20),(4,132),(6,7),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(8,136),(9,11),(9,13),(9,25),(9,41),(9,73),(9,137),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,144),(18,19),(18,22),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,96),(32,160),(36,37),(36,38),(36,44),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,72),(64,96),(64,192),(68,69),(68,70),(68,76),(68,84),(68,100),(68,196),(80,81),(80,82),(80,84),(80,88),(80,112),(80,208),(128,129),(128,130),(128,132),(128,136),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|11=>4
|12=>17
|13=>6
|14=>1
|_=>0
def HT:Nat→Nat→Nat
|11,0=>0x698f33348e07bf00394d
|12,0=>0xa48037b3695849750bdf4ef024306d41ef9362c531f2d254f220e731aefa1a50f196cb182600dc0e0d608
|13,0=>0x9892d7d8d45146d2bad8177bc0c075
|14,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaaff00ffffff00ffffff00ffffff00ffffff00ffaaff00ffaaff00ffaaff00ffaaffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0affffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|0,1=>0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fffafffafffafffafffafffafffafffafffafffafffafffafffafffafffafffaffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff003333333333333333333333333333333322222222222222222222222222222222ffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffffffffffffffffffffffffffffffccccccccccccccccccccccccccccccccfffffffffffffffffffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
|_,_=>0
def sP:Nat→Nat
|0=>0x1cc54ae23080e6c952418407360b54906101cc5a2488184e62a483b840761ac54906101cc5ad083080e62a66440c203c8c54ac6101cc582483080ef61524404e66952418407618a959101398a418820
|1=>0x398a920c203b0c54906101cc5aa483080e62a564184073152440c20398bc4906101cd82a483080fb6152418407316a9220203a8c54906101cc54cc83080e62a56440407315241b82039b5849061
|_=>0
def sO:Nat→Nat→Nat
|11,0=>0x1a8119089008
|12,0=>0xb59ac9a399a99198897f97696d963a5a951947a3e934a2b9229
|13,0=>0xeb9e29d99d09c79be9
|14,0=>0xf48
|_,_=>0
def wAt:=mkWire dB 29 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x30148d20d18149128130131548d18132118158120d18120d3221812a528120120d4d928d48d28148118122218130128d48d48122118131120d8a520130130d1812b932218118130120d527321181
|_=>0
def oO:Nat→Nat→Nat
|11,0=>0x24c630cc03
|12,0=>0x2c2a8a8298a4288a02789c2689825894248902388c2
|13,0=>0xcc721c4701bc6e1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0x504e03bfdd0c01dfe80200cff3008067f88080bbfc200699fe08232cff0411867f8100373fc06c019fe02500cff0100067f80213f3fc00e059fe00232cff0011167f8004033fc001199fe0006bcff0000f67f8000433fc000119fe00003cff00000e7f8000033fc00000ffe00000000
|_=>0
def pmB:Nat→Nat→Nat
|11,0=>0x40ce1
|12,0=>0x126ba8c2467a85969bd2b9
|13,0=>0xaa32f0f
|14,0=>2
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 33 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_223 13 roots_223 ops++addP pm 1 dom_191 13 roots_191 ops++addP pm 2 dom_127 12 roots_127 ops++addP pm 3 dom_251 12 roots_251 ops++addP pm 4 dom_254 12 roots_254 ops++addP pm 5 dom_253 12 roots_253 ops++addP pm 6 dom_247 12 roots_247 ops++addP pm 7 dom_239 12 roots_239 ops++addP pm 8 dzo_235_16 9 roots_235 ops++addP pm 9 dzo_250_4 9 roots_250 ops++addP pm 10 dom_245 11 roots_245 ops++addP pm 11 dom_235 11 roots_235 ops++addP pm 12 dzo_239_16 10 roots_239 ops++addP pm 13 dom_126 9 roots_126 ops++addP pm 14 dzo_238_16 9 roots_238 ops++addP pm 15 dom_111 10 roots_111 ops++addP pm 16 dom_252 10 roots_252 ops++addP pm 17 dzo_110_16 8 roots_110 ops++addP pm 18 dom_238 10 roots_238 ops++addP pm 19 dom_246 10 roots_246 ops++addP pm 20 dom_250 10 roots_250 ops++addP pm 21 dzo_122_4 8 roots_122 ops++addP pm 22 dzo_123_4 9 roots_123 ops++addP pm 23 dom_106 7 roots_106 ops++addP pm 24 dom_243 10 roots_243 ops++addP pm 25 dom_119 10 roots_119 ops++addP pm 26 dom_231 10 roots_231 ops++addP pm 27 dom_125 10 roots_125 ops++addP pm 28 dom_237 10 roots_237 ops++addP pm 29 dom_123 10 roots_123 ops++addP pm 30 dzo_251_4 10 roots_251 ops++addP pm 31 dom_249 10 roots_249 ops++addP pm 32 dom_242 8 roots_242 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_235_16_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_250_4_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_239_16_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_238_16_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_110_16_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_122_4_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_123_4_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_251_4_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_242 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_223 13 s (0,roots_223.map (·&&&dom_223)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_223 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 4 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 17 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z13 : ∀ i, 0 ≤ i → i < 6 → Z 13 i = true := span_ok (by decide +kernel : span (Z 13) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z14 : ∀ i, 0 ≤ i → i < 1 → Z 14 i = true := span_ok (by decide +kernel : span (Z 14) 1 0 = true)
theorem checked (s:Nat) (hs:s≤14):∀ i<NN s,bar dom_255 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
  · exact z12 i (Nat.zero_le i) hi
  · exact z13 i (Nat.zero_le i) hi
  · exact z14 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 8 7=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤14) (h:RunD true dom_255 gM s xsM):False:=by
  have hmin:7≤s:=by have hl:=run_len h;change 8≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_255 roots_255 goal_255 15:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_255
theorem lowS_255:Lower true dom_255 roots_255 goal_255 15:=S_255.noCircuit
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
    (hhas : ∃ g ∈ gates, isNotGate g = true) : 16 ≤ gates.length := by
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [7, 6] }, { op := GateOp.or, inputs := [0, 7] }, { op := GateOp.or, inputs := [3, 1] }, { op := GateOp.or, inputs := [10, 0] }, { op := GateOp.or, inputs := [5, 8] }, { op := GateOp.or, inputs := [4, 9] }, { op := GateOp.or, inputs := [6, 4] }, { op := GateOp.and, inputs := [9, 14] }, { op := GateOp.and, inputs := [5, 8] }, { op := GateOp.and, inputs := [3, 1] }, { op := GateOp.and, inputs := [11, 12] }, { op := GateOp.and, inputs := [2, 13] }, { op := GateOp.or, inputs := [15, 16] }, { op := GateOp.or, inputs := [20, 17] }, { op := GateOp.or, inputs := [21, 18] }, { op := GateOp.or, inputs := [22, 19] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 23⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  have hwit : (execN witGates xs256).getD 23 0 &&& mask256 = goal_255 &&& mask256 := by decide +kernel
  intro x
  have hlt : natOfBits8 x < 256 := natOfBits8_lt x
  have hpt : pt8 (natOfBits8 x) = x := pt8_natOfBits8 x
  generalize hr : natOfBits8 x = r at hlt hpt
  have h1 := execN_bit witGates xs256 r hlt (fun g hg => by
    have hm := wit_mono g hg
    rcases hm.1 with h | h <;> simp [h])
  have h2 := congrArg (fun l => l.getD 23 false) h1
  rw [xs256_bits ⟨r, hlt⟩, hpt] at h2
  have hgd : ((execN witGates xs256).map (·.testBit r)).getD 23 false =
      ((execN witGates xs256).getD 23 0).testBit r := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (execN witGates xs256)[23]? with | none => simp | some v => rfl
  rw [hgd] at h2
  have hbit : ((execN witGates xs256).getD 23 0).testBit r = goal_255.testBit r := by
    have hb := congrArg (fun v => v.testBit r) hwit
    simp only [Nat.testBit_and, mask256_bit, hlt, decide_true, Bool.and_true] at hb
    exact hb
  have hres := h2.symm.trans (hbit.trans (goal_eq_f ⟨r, hlt⟩))
  rw [hpt] at hres
  exact hres

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfan _h1not hev
  by_cases hhas : ∃ g ∈ gates, isNotGate g = true
  · have hfan' : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨h1, h2⟩ := hfan g hg
      refine ⟨?_, h2⟩
      rcases h1 with h1 | h1 | h1 <;> simp [h1]
    have hlb : 16 ≤ gates.length := lb_with_not gates o hfan' hev hhas
    refine ⟨witGates, 23, wit_mono, ?_, wit_eval⟩
    have hlen : witGates.length = 16 := rfl
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

end PEqualNP.Outside.L_meta_52826_aux

theorem PEqualNP.Outside.L_meta_52826 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52826_aux.main
