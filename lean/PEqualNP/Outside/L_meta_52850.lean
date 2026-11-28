import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52850_aux
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

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfffafffafffafffaaa00aa00aa00aa00fffafffafffafffaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfffefffefffefffeaa00aa00aa00aa00fffefffefffefffeaa00aa00aa00aa00
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

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffffefffefffaffeeaa00fffffffefffffffefffefffaffeeaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeaa00aa00aa00aa00aa00aa00aa00aa00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffefffefffefffefffefffefffefffeaa00aa00aa00aa00aa00aa00aa00aa00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_145 : Nat := 0x3000300000000000000000000000000030003
def goal_145 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_145 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 7 0]

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

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfffffffffafafafafffffffffafafafafafafafa00000000fafafafa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcf0f0f0f000000000f0f0f0f000000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffefefefefffffffffefefefefafafafa00000000fafafafa00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

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

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffffaaaaffffffffffffaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

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

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffffffffffff00ffffffffffffff00ff00ff00ff000000ff00ff00ff000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffffaaffffffffffffffaaffaaffaaffaaaa00ffaaffaaffaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

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

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfffffffffffffffffafafafafafafafafafafafafafafafa0000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfffffffffffffffffefefefefefefefefefefefefefefefe0000000000000000
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

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffefffffffefffffffefffffffeffeeaa00ffeeaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaa00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffffffffffafafafafafafafafafafafafafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f000000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffffffffffefefefefefefefefefefefefafafafa00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffeeffeeffeeffeeffeeffeeffaaffaaaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffefffefffefffefffefffefffafffaaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffffffffffffffffffff0000ffff0000ffff00000000000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffffffccccffffccccffffcccccccc0000cccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffffffeeeeffffeeeeffffeeeeeeeeaaaaeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffffffffffff0f0fffff0f0fffff0f0f0f0f0f000000000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffffffafafffffafafffffafafafafafaaaaa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffffffcfcfffffcfcfffffcfcfcfcf0f0cccc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffffffefefffffefefffffefefefefafaeeee0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffffffaaffffffaaffffffaaffaaffaaffaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffffeeffffffeeffffffeeffeeffaaffeeaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffffffafffffffafffffffafffafffaffaaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffffffcfffffffcfffffffcfffcfff0ffcc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffffffefffffffefffffffefffefffaffeeaa00
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
def isoMvS_145:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_145:Lower true dom_145 roots_145 goal_145 4:=lower_iso_b isoMvS_145 (by decide +kernel) lowS_25
def isoMvS_146:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_146:Lower true dom_146 roots_146 goal_146 4:=lower_iso_b isoMvS_146 (by decide +kernel) lowS_25
def isoMvS_164:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_164:Lower true dom_164 roots_164 goal_164 4:=lower_iso_b isoMvS_164 (by decide +kernel) lowS_25
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
|0=>0x5454515551455051654546551
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
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 5:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_27
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
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_27
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
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 5:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_57
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_27
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 7:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_89
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_27
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_57
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_27
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_27
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 5:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_57
def isoMvS_195:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_57
def isoMvS_197:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 5:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_57
def isoMvS_198:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_57
def isoMvS_201:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 7:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_89
def isoMvS_202:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_57
def isoMvS_209:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 7:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_89
def isoMvS_210:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 7:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_89
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_57
def isoMvS_216:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 7:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_89
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 5:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_57
def isoMvS_228:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 5:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_57
def isoMvS_240:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_240:Lower true dom_240 roots_240 goal_240 5:=lower_iso_b isoMvS_240 (by decide +kernel) lowS_27
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
theorem lowS_79:Lower true dom_79 roots_79 goal_79 6:=lower_slice_b [(0xcccc000000000000cccc,64,66)] (by decide +kernel) lowS_77
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_slice_b [(0xaa00aa0000000000aa00aa,16,17)] (by decide +kernel) lowS_86
theorem lowS_91:Lower true dom_91 roots_91 goal_91 8:=lower_slice_b [(0xc0c0c0c000000000c0c0c0c,16,18)] (by decide +kernel) lowS_89
theorem lowS_93:Lower true dom_93 roots_93 goal_93 8:=lower_slice_b [(0x303030300000000030303030,64,68)] (by decide +kernel) lowS_89
theorem lowS_103:Lower true dom_103 roots_103 goal_103 5:=lower_slice_b [(0xaa000000aa000000aa000000aa,32,33)] (by decide +kernel) lowS_102
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
namespace S_179
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,129),(2,18),(2,130),(3,19),(3,35),(3,131),(16,17),(16,18),(16,144),(32,33),(32,160),(34,35),(34,50),(34,162),(48,49),(48,50),(48,176),(128,129),(128,130),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_179.map (·&&&dom_179)
def gM:=goal_179&&&dom_179
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xc94e1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000000000000000000000000000f000f00000000f0000000f00000000000000000000000f0000000f0000c000c000c000c0000000000000000000c000c000c000ca000a000a000a0000000000000000000a000a000a000af000f000f000f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 180 0xfffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_178 5 roots_178 ops++addP pm 1 dom_177 5 roots_177 ops++addP pm 2 dom_163 5 roots_163 ops++addP pm 3 dom_147 5 roots_147 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_179 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_147 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_178 5 s (0,roots_178.map (·&&&dom_178)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_179 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_178 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_179==dom_179)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_179 gM v ys):RunD true dom_179 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_179 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_179 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
|0=>0x3123091117104926a511119b491111
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x610000513212010000
|6,0=>0x918171
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
theorem lowS_185:Lower true dom_185 roots_185 goal_185 8:=lower_slice_b [(0x30300000303000000000000000000000303000003030000,1,17)] (by decide +kernel) lowS_169
theorem lowS_199:Lower true dom_199 roots_199 goal_199 6:=lower_slice_b [(0xaa00000000000000aa00000000000000aa00000000000000aa,64,65)] (by decide +kernel) lowS_198
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
theorem lowS_229:Lower true dom_229 roots_229 goal_229 6:=lower_slice_b [(0x2200000022000000220000002200000022000000220000002200000022,32,33)] (by decide +kernel) lowS_228
def isoMvS_61:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 7:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_59
def isoMvS_62:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 5:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_55
def isoMvS_107:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 7:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_59
def isoMvS_115:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_59
def isoMvS_121:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 8:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_91
def isoMvS_122:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_59
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 6:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_79
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_87
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 8:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_91
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 8:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_93
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 6:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_87
def isoMvS_167:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_87
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_93
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_91
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_87
def isoMvS_181:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 7:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_179
def isoMvS_186:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_179
def isoMvS_188:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 7:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_179
def isoMvS_203:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_91
def isoMvS_211:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 8:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_185
def isoMvS_213:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_91
def isoMvS_214:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 8:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_91
def isoMvS_218:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 8:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_185
def isoMvS_227:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 7:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_179
def isoMvS_230:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 7:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_179
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 8:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_91
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 8:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_93
def isoMvS_244:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 7:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_179
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xcccccccccccccccc,16,18)] (by decide +kernel) lowS_61
theorem lowS_95:Lower true dom_95 roots_95 goal_95 9:=lower_slice_b [(0xcccccccc00000000cccccccc,16,18)] (by decide +kernel) lowS_93
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
|0=>0x3030c084030d043000c0500240044010d0c6310c007310c004330c003370c044010c04301116430210d5002116c302210c3010c050310c003030c083010c00301210030110c430010043030c050330c0030118c43005d643030c0830148648400c0430140c4300
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x28c7300061000330000000c0000000
|6,0=>0x2f2b4800ac800002a1a46819c400002610000090a2200202001e2001d16c992000005c9615092244400404f1000d2
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xf6fd9e7e689061082e0277ddd76d996258114045110421002a07c120400e00c0200400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40c060100218040
|6,0=>0x18b81c0035a630136109f00380151af7052ab3b8a92940c
|7,0=>0x35b9677a94e39
|8,0=>0x10
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_118 7 roots_118 ops++addP pm 1 dom_53 4 roots_53 ops++addP pm 2 dom_85 5 roots_85 ops++addP pm 3 dom_115 7 roots_115 ops++addP pm 4 dom_117 6 roots_117 ops++addP pm 5 dom_102 4 roots_102 ops++addP pm 6 dom_55 5 roots_55 ops++addP pm 7 dzo_87_32 6 roots_87 ops++addP pm 8 dom_87 6 roots_87 ops++addP pm 9 dom_103 5 roots_103 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_119 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_87_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_87 _ g hchk
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
def dzo_105_2:=0xc0c00000c0c00000c0c00000c0c
def gzo_105_2:=0xc0c00000c0c00000c0800000800
def gsh_105_2:=0x303000003030000030200000200
theorem lowS_zo_105_2_41:Lower true dzo_105_2 roots_105 gzo_105_2 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_2) [(dom_105,2)] (by decide +kernel) (lower_slice_b (T:=gsh_105_2) [(0x303000003030000000000000000,0,64)] (by decide +kernel) lowS_41)
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
|0=>0x3c84b0d28c4b290478c2144b4c212884b292c84a212884b7204a4c591068a2d28b4f232c34a3130d4a0a2c84c112034c2920a442104a4a2d20e8c2d20c4a2d2c38c292cc46052ca480d28c4b212044c2d20c4a2d20e4b3120a4b211814b2944e0a2130b432d30a4c21083082d28c4831
|1=>0x28b4a2104a460528b4b7204a4c2128b4c2d2884c2920a411e3084a2d30b4a392cc4a052cc4a0a2c8443104a4b0d28c412930a4e4430b4a21
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x810001c42900007300010c09801
|6,0=>0x806f4dd1b73000d0d89ae35a2a8d39a4342678c001c23445cca9123
|7,0=>0x5b2b255caa9532a253ca694b29251ca29432
|8,0=>0x17c6f0dd1
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x7e76f808003c015fbe00a6df0052478021b7c010db400869f0022478009d780048100014ff0008488003e400009de0004eb00026f800123c0008a200044000006f00003000000e00000500000250000110000080000018000009000004400000c000000
|1=>0xa00277d0011aa0008de8aa6df20534f90112746c01ae1004cf
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x24011200700a045
|6,0=>0x3cd54601065e20c0937c42092960e1
|7,0=>0x1d6942e26e599c8249e3
|8,0=>0x115d8
|9,0=>0xe
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 8 roots_121 ops++addP pm 1 dom_115 7 roots_115 ops++addP pm 2 dom_107 7 roots_107 ops++addP pm 3 dom_122 7 roots_122 ops++addP pm 4 dzo_41_2 4 roots_41 ops++addP pm 5 dom_82 4 roots_82 ops++addP pm 6 dzo_82_32 4 roots_82 ops++addP pm 7 dom_59 7 roots_59 ops++addP pm 8 dom_113 5 roots_113 ops++addP pm 9 dom_120 5 roots_120 ops++addP pm 10 dom_91 8 roots_91 ops++addP pm 11 dzo_57_2 5 roots_57 ops++addP pm 12 dom_41 4 roots_41 ops++addP pm 13 dzo_105_2 5 roots_105 ops++addP pm 14 dom_58 4 roots_58 ops++addP pm 15 dzo_121_2 6 roots_121 ops++addP pm 16 dom_89 7 roots_89 ops++addP pm 17 dzo_91_32 6 roots_91 ops++addP pm 18 dom_27 5 roots_27 ops++addP pm 19 dzo_90_32 5 roots_90 ops++addP pm 20 dom_51 4 roots_51 ops++addP pm 21 dzo_83_32 5 roots_83 ops++addP pm 22 dom_106 4 roots_106 ops++addP pm 23 dom_75 5 roots_75 ops++addP pm 24 dom_99 4 roots_99 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_41_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_82_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_57_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_105_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_121_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_91_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_90_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_83_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_99 _ g hchk
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
theorem lowS_183:Lower true dom_183 roots_183 goal_183 9:=lower_slice_b [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_182
def dzo_185_2:=0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c
def gzo_185_2:=0xc0c0c0c0c0c0c0c00000000000000000c0c0c080c0c0800
def gsh_185_2:=0x30303030303030300000000000000000303030203030200
theorem lowS_zo_185_2_41:Lower true dzo_185_2 roots_185 gzo_185_2 6:=lower_iso_b (d1:=dom_185) (r1:=roots_185) (T1:=gsh_185_2) [(dom_185,2)] (by decide +kernel) (lower_slice_b (T:=gsh_185_2) [(0x30300000303000000000000000000000303000003030000,0,16),(0x30303030303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
namespace S_187
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,18),(2,130),(3,11),(3,19),(3,35),(3,131),(8,9),(8,24),(8,40),(8,136),(10,11),(10,26),(10,42),(10,138),(16,17),(16,18),(16,24),(16,144),(32,33),(32,40),(32,160),(34,35),(34,42),(34,50),(34,162),(48,49),(48,50),(48,56),(48,176),(128,129),(128,130),(128,136),(128,144),(128,160)]
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
|5,0=>0x8dbf0380e2
|6,0=>0xdd4469df1a8191f8088b771ba328110f1f70263e
|7,0=>0xe0bc4d1175bf963a1eeb858f0718e9696d9103a6099a6
|8,0=>0xd51466d6aa6a888
|9,0=>0x3dbb0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x5050505050505050000000000000000050005000500050050405040504050400000000000000000504050405040504f0c0f0c0f0c0f0c00000000000000000f0c0f0c0f0c0f0cf0f0f0f0f0f0f0f00000000000000000f0a0f0a0f0a0f0af0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0f0ac0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0af0f0f0f0000000000000000000000000f0f0f0f00000000f0e0f0e0f0e0f0e00000000000000000f0e0f0e0f0e0f0ef0f0f0f0f0f0f0f00000000000000000f000f000f000f00f0f00000f0f000000000000000000000f0f00000f0f0000f000f000f000f0000000000000000000f000f000f000f00e0e0e0e0e0e0e0e00000000000000000e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0a00000000f0f0f0f0000000000000000000000000f0a0f0af0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x64a90854a9f085b6a9085c4a908549e085749085c4a29085d6908564a29856439085b6a28569e085769054a91085c432054a291085d6295c4a91085762543210
|1=>0x854a9085b4a9085d49085
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x65006
|6,0=>0x3863262c62661f71871260b7
|7,0=>0x7476d76676065a65284c64573e7
|8,0=>0x8878267b7
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 16 188 0xfffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x125a450169d0140651b0525d9e91ba525246414a50190501a95019050194501d9e91ba50194632b05252466990632246414a501b0525906e940651
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0x5cd4344ce32cc9218c42
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 10
def pmP:Nat→Nat
|0=>0xe75f3829d6ceb475a280fde7ee2758ffc7f62ef17707f81d60c9020008003c000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x20
|6,0=>0x79cc470d82
|7,0=>0xb84d0a93629
|8,0=>0x3d0b
|9,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_185 8 roots_185 ops++addP pm 1 dom_59 7 roots_59 ops++addP pm 2 dom_177 5 roots_177 ops++addP pm 3 dom_171 8 roots_171 ops++addP pm 4 dom_184 5 roots_184 ops++addP pm 5 dom_155 8 roots_155 ops++addP pm 6 dom_186 7 roots_186 ops++addP pm 7 dom_179 7 roots_179 ops++addP pm 8 dzo_57_2 5 roots_57 ops++addP pm 9 dzo_185_2 6 roots_185 ops++addP pm 10 dom_51 4 roots_51 ops++addP pm 11 dom_178 5 roots_178 ops++addP pm 12 dom_58 4 roots_58 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_187 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_57_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_185_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_58 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_185 8 s (0,roots_185.map (·&&&dom_185)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_187 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_185 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
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
|0,0=>0xf0f0f0f000000000f000f00000000000f0f0000000000000f000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f000000000f000f00000000000f0f0f0f000000000f000f00f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000f0f0f0f0000000000000000000000000f0f0f0f0000000000000000f0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f00f0f0f0f000000000f0a0f0a000000000f0f0a0a000000000f0a0a0ac0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0cf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000000000000000000000000000000000000000000f0f0f0f000000000f0f0a0af0f0000000000000f0f0000000000000f0f0000000000000f0f00000000000000000000f0f0f0f0000000000000000000000000f0f0a0af000f00000000000f000f00000000000f000f00000000000f000f00e0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0e0000f0f0000000000000f0f0000000000000f0f0000000000000a0af0f0f0f000000000f0f0f0f00000000000000000000000000000000
|0,1=>0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0a0af0f0f00000000000f0f0f00000000000f0f0f000000000000000000f0f0f0a000000000f0f0f0a000000000f0f0f0a000000000a0a0a0af0f0f0f000000000f0f0a0a000000000f0f0f0f000000000f0f0a0af0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f0000f0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0a1010101000000000101010100000000010101010000000001010000f0f0f0f000000000f0f0f0f000000000f000f00000000000f000f00f0c0f0c000000000f0c0f0c000000000f0c0f0c000000000f0c0f0cf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f000f000000f0f0000000000000f0f0000000000000f0f0000000000000f0050505050000000005050505000000000505050500000000050505001010101000000000101010100000000010101010000000001010100f0f0a0a000000000f0f0a0a000000000f0f0a0a0000000000000000f0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0af0f0e0e000000000f0f0e0e000000000f0f0e0e000000000c0c0c0c
|0,2=>0xf0f0f0f000000000f0f0f0f000000000f0f0f00000000000f0f0f0000000000000000000000000000000000f0f0f0f000000000f0f0f00f0f0f0f000000000a0a0a0a000000000f0f0000000000000a0a0000f0f0f0f000000000e0e0e0e000000000f0f0c0c000000000e0e0c0c50105010000000005010501000000000501050100000000050105000000000000000000f0f0f0f0000000000000000000000000f0f0f00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0a00f000f00000000000f000f00000000000f000f00000000000f000af030f03000000000f030f03000000000f030f03000000000f030f000030003000000000003000300000000000300030000000000030000f0f0f0f000000000f0f0000000000000f000f00000000000f000000f0f0f0f000000000f0f0f0f000000000f0f0a0a000000000f0f0a0af0f0f0f0000000000000f0f000000000f0f0f0f0000000000000a0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0000f0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0a3030303000000000303030300000000030303030000000003030000
|0,3=>0xf0f0000000000000f0f0000000000000f0f00000000000000000000000000000000f0f0a0a0000000000000000000000000f0f0a0af0f0f0f000000000f0f0f0f0000000000000000000000000f0f0a0a000000f000000000000000f000000000000000f0000000000000000f0f0f0f000000000f0a0f0a000000000f0f0f00000000000f0a0f0030303030000000003030303000000000303030300000000030303005050505000000000505050500000000050505050000000005050000f0f0f0f000000000f0f0f00000000000f0f0f0f000000000f0f0f0000f000f00000000000f000f00000000000f000f00000000000f0000000000000000000000f000f000000000000000000000000000f0000f0f0f0f00000000000f000f000000000f0f0f0f00000000000f000000b000b00000000000b000b00000000000b000b00000000000b000af0f0000000000000f0f0000000000000f0f0f0f000000000f0f0f000000000000000000505050500000000000000000000000005050000f0f0f0f0000000005050505000000000f0f0f0f0000000005050000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f00
|0,4=>0xa0a0a0a000000000a0a0a0a000000000f0f0f0f000000000f0f0a0a00f000f00000000000f000f00000000000f000f00000000000000000000f0f0000000000000f0f0000000000000f000000000000000f0000000000000000000000000000000000f0f0f0f000000000f000f0000000000000000000000f0f00000000000000000000000000000f00b0b0b0b000000000b0b0b0b000000000b0b0b0b000000000b0b0a0a00000000000000000000000000000000f0f0f0f000000000a0a0a0a000000000000000000000000000000000000000000000000f0f0f00f0f0f0f000000000f0f0f0f0000000000000000000000000f0f0f0000f000f00000000000f000f00000000000f000000000000000f0000f000f0f000000000f000f0f000000000f000f0f000000000f000f003030303000000000303030300000000030303030000000003030202f0f0f0f000000000f0f0f0f0000000005050505000000000505000050505050000000005050000000000000505050500000000050500003030303000000000303030300000000010101010000000001010000f0f0f0f000000000f0f0000000000000a0a0a0a000000000a0a0000
|0,5=>0xf000f00000000000f000000000000000000000000000000000000f0f0f00000000000f0f0f00a0a0f0f000000000a0a0f0f000000000a0a0f0f000000000a0a0a0af000f00000000000f000f00000000000f0f0f0f000000000f0f0f000000000000000000f0f0f0f0000000000000000000000000f000f000000000000000000f0f0f0f0000000000000000000000000a0a0a0a00f000f00000000000f000000000000000f000f00000000000f0000f0f0f0f000000000f0f0f0f00000000000f000f00000000000f000000000000000000000000000000000000f0f0f0f000000000f0f00000000f0f0000000000000a0a0000000000000f0f0000000000000a0af0f0f0f000000000f0f0f0f0000000000000f0f0000000000000a0a00005050000000000000505000000000000050500000000000000000000000000000000f0f0f0f0000000000000000000000000f0f000000000000000000000000f0f00000000000000000000000000000a0a000000000000000000000000000000000000000000000000f0f0a0a0000000000000000000000000000000050505050000000005050000
|_,_=>0
def sP:Nat→Nat
|0=>0xe2c02a0a5c7070014129502c0054e3930b006c6172c3838c1a9440e3890283041cd8506091800a0cd21401c88506645803e18283042cd8310740063630182166c182022c0050668c8b0018205062070c2e607151630b961c54585065098b00301901c2c509101c3040a0c1040608080
|1=>0x6645805e5c71516002881ca058036241880014734160028234a05800a607260e2c28e40d05806630b8e1600509102c00a4a207070a0c11a620110304045800c14182422ce1b180c10760b82971c2c31b0a0c1075e6cb981c1d7052e6070b226c19916017052e5870b360d60e00141ab
|2=>0x66458036301825288283562c01176205800a0c73a16017852e505803814199160179b2e38385065100b000c439022c038185cb0e169021b0608011440d0a0161910506085ae0a2073716a81881c5401b180c129346cc081c782971a39a8044141a1322ce040a0c1005ea8d971c008a2
|3=>0x6c2831c98580700c40e2a2c00c0a0c129422c283106a00060bc2971c2c01c48141821601c1b0a5c707002910c2e385800a0c41a42fde850608580441418e742c01c3630188422c2831085c87166c6831038a800a9c1ab16018052e385803e14128160028328e85800a9c7371600f85
|4=>0x2c601881c14b961c545805e8828d103800506214b9160111b0a34c081c302831d1058008141881c1c00a1858c081c2c288343940b006c2831c645805e6c60310383ae18141881c2cd850620a0b00702831d105807028298103838a443440e00282831ce85800a0c74116002831068731
|5=>0x6207071688d85060908b5414698103803054141881c002971a39f800c6c283042c00c0a5cb0e164511b0608580360c40e8c1c2a706385803e141820e2c0381430b8e16002831c81b8b00bcd9730385805414b0310380052e6071516002a7063900b0014bc51c2c00c0a0c421722cd8c
|6=>0x1c545803630188526872f146c6881c00d852e3a58b00442050620d003e1418e882c01f181418216012050620d07226c18e402c0051a9440e004511b0620d003e70283042c00507287071600522366040e1670d8506210875c6c603103859c3630182160089b062248048141820e2e385
|7=>0x180c40e9ce11052e385805e1440e6e2c0300a0c40e1600d85060a4800a6018e401c5850620e8b0014b8e9a1c5850620d3916002980639d0b006c297983800436301881c01204360c40e008828310505806014b8d1c2c02a0a5c70b00882831c985800c88283103859b185cc0e16c0188
|8=>0xbcd8d30207001414b8e16f004f0a0c421160121b060908b00e170c062070b220c40e022c0040a0c10b00bcd960620700180d2881c2c283583858044141a11c8059b062072d001418e87045800a2072816008a2063900b006c297303838a365840e00e02831050580486c188523801b
|9=>0x42ea00234c188422ce05063900b00bd5052e38580226c188421c8a20621c8b0028d96103838036306981039c052e5870b006c603043839b18581881cc0283105058036301885239105302073716c11052e38580145840e2a2c0052c0c41416002830548580486c18834840510a0c10b
|10=>0x841c02f0a5cc0e160111b0a0c10e16008a2060838b00c02971c2c011440c10b007c28310e45800a0c73a0e2c005063930b001418e40985805c14c0310385a408141883400f85063900b00882839438580363018852383850639d0b001418e6e985805e1418e402c0220a5cc0e1644283
|11=>0x5c1468310385801414b1810385801814b981c2d2050620d0b0120283103838b0070d85062108b0088605300c40e16906050608580146c1881c1c00aae0c40e160111b0a0c41a1c00d83103a30b0014b981c1c59b0a0c4491c00283103aa8b00e02831038380386c28310383800a0c40e
|12=>0x6c28310a4d0e00bc605062070716282db10385803e6c28310385802214188b42c00506207581600298062070b7e141881c2de000a0c129342c01f0a0c4211c2c02e36141881c2c005062074b16011052e0c707160121b062108e1600205062070b003028d06207073614b180620700
|13=>0xa5c70b0014b831c2df800a0c40eac1c02f44141881c2c0223614c0310385910a0c40e175005c0a0c40e160088c062108b3630188423858a440c40e16002831c805801814b18062070b3888283103858060141881c2c01b0a0c40e722c0220a341881c00d852e6070b0088d85063900b
|14=>0xe2c00a0a5840e1600d85062148e001418e401c58060141881c1c58038141885238580226c188422c005060948b00141881cdc58044141881ce45800830283103858036301821c2c0385e141881c2c02408141881c2c05e0a5c70b00141a510385803e8828310385800a0c45d1c2c02f
|15=>0x14146881c2c005062070b9c01105062070b0014182422c01b180c40e0e882831c8058044141821c2c0300a341881c2c00a0a5840e0e2c00506207370e2c03e0a0c10b007c28310a470b006c283048458060bc283103858036146981038005300c40ebe2c0110a0c429342c00a440c40e
|16=>0x1c2c0052e3470b00141881d345800a0c40e16fc0050620756160028310a47071601f05062070b00bc505062070b00141821c1c58014141881c1c58044141881c1c5800a0c4291c2c005062108e0e2dc05062070b0070d85062070b003028d062070b006c28d062070048141884238580
|17=>0x5062070b00141881c1c5800a601881c2c005060870b002828310385803630188
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
|0=>0x1601000d0615161516c9186b0a0116013639103900153803301516150601100d5a210a2d343016390a011c9e068144230a1d44230a1d1601062116150e0d16010a01062d0a01306c000d16151039222d00451c151c0144230a1d16013c391615141c0a0d160138032c1710490015221c0a39160116011e390a0d1a30160d0015
|1=>0x14f10e2b0a0d16011c213e0f221d0a3916014439440b0a1d16011039422d1c010015161506b51c15343016390a010a2d180d0a01100d16011a011a15062d100d482f4423006d16150a0134011c2d1039141c1601000d0615161516d918370015006d0a2d5e2f0a1d16011c3d0a2d1a30160d00151e390a0d1a30160d00153660
|2=>0x156023141d1601110e01091c6e161516c9343216390a0106824423006d16151a152c170035062d0a01422d1c0110391c2d426c003916155e2d0a610601100d164522011c1510390621360d0a2d002d163100150615100d1c2d0a1e1c0116017c01222f1c151039440d0a1d160136391c011615443b0a1d16012c170035062d
|3=>0x100d44230a1d160106fd0a1e100d1601443b16310a01302d060116152c1716610601100d062d063116310a011c1d443b0a1d16010601006d0a2d3e2316911c313e2f0aa51c1d002d0a01302d060106153e0f34310a011c824423006d16150a2d180d0a011601600316bd06310015603b00e1066d002d142d061506151631160d
|4=>0x18390a01103916019001141f0a0d160136010a2d1c01103916be30150601602f141d0a0d002d062d0a1e100d002d103900721c6d0a2d1a010a01062d100d1039006d1c1516150a2d180f0a01160144230a1d1601521510391c1d1601162900150615100d440f0a1d1601301516150601100d602f0a59061d002d0a5a302d0601
|5=>0xa59061d1601001500691c2d14010615062d0a2d36620601100d169200451c153e23221d0a39160118690a011c2d103918391c2d16010a011c154423006d1615160d306c000d0a2d0a39006d1c2d0a2d103900711c6d16151c8144230a1d3601000d16151c0136390a2d7003360d161536391615103900150a2d1c15006a1c2d
|6=>0x440f063116310a01901d141f0a0d1601161534031c2d1039060144230a1d16013c39141c0a0d1601100d1601301706013e3b343116390a0160235e2d0a6100360a2d062d100d16921c310015482f1c310a01603b440d0a1d16011a31160d0a01100d5e2f06310015445f0a1d16013e0344390a1d160106010015100d16150a5a
|7=>0x161542151c01103970031a15160d3e17482d00451c15169242151c0110391615302d301506010a01306c000d0a2d5a213430163900154423006d0a2d0a2d34301639001501091c6e16153e0f221d0a3916014423006d16151601000d100d161516610615000d1615422d0a2d0a851c01061e1601001516150621066d006d0a2d
|8=>0x5e2f06310015160100391c151615443b0a1d1601061d0a0d002d062d0601001516151a010a35062d100d16010015103916150e0d0a01002d0a2d603b141d0a0d1601422d1c0100151615440f006d0a2d440d0a1d16010a5a061d16011c21426f0039161516150a851c010e460a39103916010a2d0a6106011d41426e00391615
|9=>0x100d006d103916151c210a390a1d16010621141d0a0d16010a390a1d10391601443b44390a1d16016023141d0a0d445f0a1d100d160144230a1d16016003306d000d0a2d482f1c31001544230a1d16011c8144230a1d16011c1d1601001516156023141d0a0d1601440f0a1d16010621006d000d0a2d1c011c1516320015100d
|10=>0x482f1c3100150a01062d002d302d000d0a2d70030a35062d302d060106150a010601100d1c2d1c310015141f0a0d00391c6d1615060116310a0110391c310a010a2d0a0d002d0615006e1615006d1c2d0a2d16150632001516010601100d1615006a1c2dac010a6a1c2d142d0a0d002d002d1c6d0a2d363b0a2d002d0a610601
|11=>0x16010015302d0601006d1c6d1615141d0a0d1601443b006d16151631160d0a010a2d0601100d4423006d16150a2d00691c2d180d0a0116010615302f060100711c6d16151c1516861c010165066e16150a1e06011601141e0a0d160134011c2d1039482d0a851c017003066d1615306f000d161506210a1d16010a2d0a851c01
|12=>0x422d1c011039440f0a1d1601443b0a1d160116921c310a01001510391615142d14010615482f1c310015062114030615306c000d161544390a1d16011cfd0a1e16010a610601100d0a1e100d1601002d34171c2d063116310a01006d000d1615221e1601075d006e16151c151c010a011c01001516150a0d0a1d160144230a1d
|13=>0x16010a1d16011c01103916010015161544230a1d16010a1d103916011a31160d0a01061d0a0d1601440f0a1d1601222f1c1510390aa51c1d16010039103916155e2d06310015062d000d0a2d36630a2d1c1500691c2d0a0d0a1d1601061d0a0d16010a2d1c1d002d44230a1d1601141d0a0d160134010a691c2d00391c151615
|14=>0x1601060110390615001516150621062d301706010a1e16010a6a1c2d1c1d1601222f1c1514010615103916010a0d16010a1d16011c1d16011c011601066d16151c6d1615160d0a01062d0a2d0a851c01062d0615061e
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x60000000
|5,0=>0x1cd06e5000069500000000000645000000018105f1170c00000000001610535140c4e200004d112c800000004650000000000000000004150f1439300000000d500000d04304000000000002b509d0000000024307d41a50590000049000000000d50304000000000000000b10000065
|5,1=>0x1f107750000000
|6,0=>0x591160457115845511513538d4b3520d44450113c44e113444c4d2d44a5125448511d4465116344910e442cd07440d0ff43f0cf843d4cf233b90ea43990e33380cdc43610d533450cd43250c630000c332fd0bc32e10b442c10ac42a10a4428109c4261094424108c4224c86320cc803
|6,1=>0x90500008f523948d8e3338bd22b489d223487d21b4860e153848c00083920b381d204300020047f11f937d51f147b51e947951e237791db375d1d437411cc40001c847111c046f11b846d11b046b11a846911a1367519a365cd934640d8c4624d85460517d45e8d7645ccd7035b11684
|6,2=>0x27849d127049b12693995262397925b3960e54494124c4924c0009150000
|7,0=>0xcdcf343cc4f2e3cacf283c94f223c7cf1c3c64f163c4cf103c38b0b3c20f053c08eff3bf0ef93bd8ef33bc0eed3ba8ee73b90ee13b78edb3b60ed53b48ecf3b30ec93b18ec33b00ebd3ae8eb73ad0eb13ab8eab3aa4aa63a8cea03a74e9a3a5ce943a44e8e3a2ce883a14e8239fce7c3
|7,1=>0xde0f753dc8f6f3db0f693d98f633d80f5d3d68f582d54f523d3cf4c3d24f463d0cf403cf4f3a3
|8,0=>0xe94ba32e84b9f2e74b9b2e64b972e54b932e44b8f2e34b8b2e24b872e14b832e04b7f2df4b7b2
|9,0=>0xea87a91ea07a71
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 14
def pmP:Nat→Nat
|0=>0x1f4001f1001f0001a1001a00018000160001410011300110000f0000c1000b0000a0000810008000070000610005100048000410004000030000210002000011000100000800004000030000100000
|1=>0x61d8060b006010050c8050b0040c104010031a003090020510201002000011d8010c1010800100000dd400c9000c8000b00009d400880006900065000610005d4004100040000300002510021000200
|2=>0xa1f10a1d8091f108bf108b9008b10089f5087f5087d1085f5085f1083f5083f1082c1081f9081f1081f0081d808110081030809108090080840808008045080410804008010080040800108000061f1
|3=>0x403d440080400202b1f128dd128bf128bd1289f1289d1283d128390281f1280c128051261f1241f1231a0231712311022100211f12110020b80203002006118191181010d1f90c1f90c1f80a1f90a1f8
|4=>0x831d182010811f1805d480020683d168000660414d1f14c1f148dd148cc148c90485f5483f1483d148351481f9481f5481f1451f1451a045190450e1450b0421d14108040dc140d9040880405d440480
|5=>0xe0181e0021c89d1c80d4c8000c01a1c0188a81f9a81f1a81d1a8091a8000a41f1a0c41a0178a0108a0098a0020a00148e1f98e1f1889f1889d1889c1887f18879088690885f588041861f1860d1860b0
|6=>0xe81f9e81f1e81d1e81b1e8180e8141e8094e8091e8090e01a8e01a1
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x20000
|5,0=>0xb4200000b3c00170000002800001a34070000003152030400200400004c0000000000177204000037003025000000190500000a2e73160009000065340000000024000f
|6,0=>0x9f002998ae82b21a51940888bb472d00623d602700083d68084e4ab61d076b010807818400138f49010b3344662608412b359e010b1f43019c0185a610390b32a10977c01805b46a236d6e3f06b921017f382fb0a845365a0127012a45507d802d4a01991006930712a51110002cc541150848013b6b0d1669ad865e016c9b7e
|6,1=>0xaf1eb10b054f41423d0c0887460100bc00
|7,0=>0xc9c7caa393b56114630d7b4189c2958bc7221b716450be3eb84da054740e8c588d9d4bc60774abb3c850931c50bac856bf8aa5573a4074908c64675b55c4a050bd937583a4a2056fc3ac9a76c0a9926b5d796f7058c1
|8,0=>0xb759558c5d975fa78e91c797967a7caa78ab5c8cc963
|9,0=>0x8c555153
|10,0=>0x50
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 20 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_217 9 roots_217 ops++addP pm 1 dom_146 4 roots_146 ops++addP pm 2 dom_209 7 roots_209 ops++addP pm 3 dom_216 7 roots_216 ops++addP pm 4 dom_155 8 roots_155 ops++addP pm 5 dom_218 8 roots_218 ops++addP pm 6 dom_210 7 roots_210 ops++addP pm 7 dom_203 8 roots_203 ops++addP pm 8 dom_91 8 roots_91 ops++addP pm 9 dom_195 5 roots_195 ops++addP pm 10 dom_83 5 roots_83 ops++addP pm 11 dom_147 5 roots_147 ops++addP pm 12 dom_154 5 roots_154 ops++addP pm 13 dom_202 5 roots_202 ops++addP pm 14 dom_90 5 roots_90 ops++addP pm 15 dom_211 8 roots_211 ops++addP pm 16 dom_194 4 roots_194 ops++addP pm 17 dom_139 5 roots_139 ops++addP pm 18 dom_27 5 roots_27 ops++addP pm 19 dom_75 5 roots_75 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_194 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_75 _ g hchk
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
theorem lowS_231:Lower true dom_231 roots_231 goal_231 8:=lower_slice_b [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,32,33)] (by decide +kernel) lowS_230
namespace S_245
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(1,129),(4,36),(4,68),(4,132),(5,21),(5,37),(5,69),(5,133),(16,17),(16,80),(16,144),(20,21),(20,52),(20,84),(20,148),(32,33),(32,36),(32,160),(48,49),(48,52),(48,112),(48,176),(64,65),(64,68),(64,80),(64,192),(96,97),(96,100),(96,112),(96,224),(128,129),(128,132),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_245.map (·&&&dom_245)
def gM:=goal_245&&&dom_245
def NN:Nat→Nat
|4=>21
|5=>61
|6=>70
|7=>45
|8=>10
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xb9eaeb0122ab206a32278d68280f6f727196fab168791657db5f49238a2e3705033e4826c681b969189e51347c1304a0119c0051b
|5,0=>0xfe819e6d73e4c86df34fdd1b9cdc99cc913c216cb8edcb25c5abfeaa7747a42c1a19129588d93eb08eae78d2358a13b7b74b750856e3316db686d3086357c628cc5fc485079b4c9314afd04a7544a34f4a2044983848c4b446bd42dfe3e14a3c23539fbc39965396d138fba354c4343c230f182acf829b862429a229b6228531e9fc18ccd10dfa0e9720e2670c69d0bde90b69a0afc506ea1
|6,0=>0xf0ca6ea196e97d0d4772d1051cacccca1e3c87c9bfe47b799cadc10ad3b0ad342a3f65a3f4e9c869977b994e018fe2586a5c7e1f27d39f782ef74ed9733986e9a66725a66fac66c3962a5e5ee6a5835f580af573ec50ea24b5b54ae4541a82409f0404783de763d3f63a90336dff3678e33b122b6ed29efc2944128cdf285a824d2e225b820bef209ca2094c1f3f71cbc01ad4715dcf151de109d4100810f7470f0040e7cd0cd8807fd904e8d03015
|7,0=>0xfa3cdd857ad38ccccdf7c73f8c730bc71d3b8397b3e44b3ce7a7ebea1d959588b8faf980a98795b26b72e6339162660617695dfd458db557ec9558df4f0ac4c2644c05e4bfbc49d613eb7e3abae234181f9fc1f7e51edba1cc7f1a08e159f7149650ad74097a507a8706c150621702879
|8,0=>0xe84aba7ebea79219490a828337999350eeb356de2cd2a18c01
|9,0=>0xbf1f1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc00c800cc00c800cc00c800cc00c80088008800880088008800880088008b3003300330033002200220033003300330033003300330022002200220022440044004400440044004400440044004400440044004400400040004000400000000000000000000000000000000330033003300330033003300220022cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc000000033003300330033003300330033003000300030003000300030003000300030cc00cc00cc00cc000000000000000000cc00cc00cc00cc00000000000000023002300230023002300230023002300230023002300230022002200220022cc00cc00cc00cc00cc00cc00cc00cc0000000000000000000000000000000320032003200320032003200320032003200320032003200320032003200328c008c008c008c008c008c008c008c0088008800880088008800880088008b3003300330033003300330000000000330033003300330033003300000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc000330033003300330033003300320032003000300030003000300030003000308800880088008800880088008800880088008800880088008800880088008b3003300330033003300330033003300330033003300330000000000000000
|0,1=>0xcc00cc00cc00cc00cc00cc00cc008800cc000000cc000000cc000000cc00033003300330033003300330000000000320032003200320032003200000000cc00cc00cc00cc00cc00cc00cc00cc00c800c800c800c800c800c800c800cb3003300330033003300330022002200330033003300330033003300220022cc00cc00cc00cc00cc00c800cc00c800cc00cc00cc00cc00000000000000033003300330033003300330033003300220022002200220022002200220022cc00cc00cc00cc00cc00cc0088008800cc00cc00cc00cc00000000000000032003200320032003200320032003200320032003200320032003200000000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c33003300330033003300330033002200220022002200220022002200220022040004000400040004000400040004000400040004000400040004000000033003300330033002200220022002200330033003300330022002200220022cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00880088008800880003300000033000000330000003300000033000000330000002200000022cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc000000033003300330033003300330033003300330000003300000033000000330000
|0,2=>0xcc00cc00000000000000000000000000cc00033003300330033000000000033003300330033003300330000000000330000cc00cc00cc00cc000000cc000000cc00cc00cc00cc00cc000000cc000000000000000000000003300000033003300000000000000000033000000330000880088008800880088008800cc00cc008800880088008800880088008800880000000330033000000000033003300000000003300330000000000320032cc00cc00cc00cc00c800c800c800c80088008800880088008800880088008a200230022002300220023002200230022002200220022002200220022002200000000000000000000000000000000cc00cc00cc00cc00c800c800c800cb30033003300330032003200320032003300330033003300320032003200328c008c008c008c008c008c008c008c008c008c008c008c008c008c008800880000000000000000000000000000000330032003300320033003200330032cc00cc00cc00cc00cc00cc008800880000000000000000000000000000000000000000000000033000000330000000000000000000000330000003300000c000c000c000c000c000c000c000c000c000c000c000c000c000c000000000003300000033000000330000003300000033000000330000003200000032
|0,3=>0xcc00cc00cc00cc0000000000cc00cc00cc00cc00cc00cc00000000000000011001100110011001100110011001100110011001100110011001100000000440000004400000044000000440000004400000044000000440000004400000003300000033000000330000003300000032000000320000003200000032000000000000000000000000cc00cc00000000000000000000000000c800cb30032003300320033003200330032003300320033003200330032003300320c000c000c000c000c000c0000000c000c000c000c000c000c000c00000003300330033003300010001000100010033003300330033000000000000000088008800880088008c008c008c008c008800880088008800880088008800880000000000000003300330033003300000000000000000033003200330032cc00c800cc00c800cc00c800cc00c8000000000000000000000000000000000000000000000003300330033003300000000000000000033003300220022000000000000000000000000cc00cc000000000000000000000000000000003000300030003000300030003000300030003000300030003000300030000cc00cc00cc00cc00cc00c800cc00c800cc000000cc000000cc000000cc00033003300330033003300330033003300330033003300330032003200320032
|0,4=>0xcc00cc00cc00cc000000000000000000cc000000cc00033003300330033003300330033000000330033003300330033003300330000cc00cc00cc00cc000000cc000000cc00cc00cc00cc00cc00000000000000000000000330033000000000033003300000000003200320000000000320032cc00cc00cc00cc00cc00cc000000cc00cc00cc00cc00cc00cc00cc000000000003300000033000000330000003300000000000000000000000000000000cc000000cc000000cc000000cc0000000000000000000000000000000000000003300000033000000330000003300330000003300000033000000330000cc00cc00cc00cc00cc00cc00cc00cc00cc008800cc008800cc008800cc008b3003300330033002300230023002300330033003300330022002200220022000000000000000000000000cc00cc0000000000000000000000000088008b30000003300000033000000330033003300000033000000330000003300000400040004000400040004000400040000000000000000000000000000000000000000000000033003300330033000000000000000000330033003300000c000c000c000c000c000c00040004000c000c000c000c000c000c000000033003300330033003300330033000000000000000000000000000000000000
|0,5=>0xcc00cc00cc00cc00cc00cc00cc00cc00cc00c800cc00c800cc00c800cc00c81000100010001000100010001000100010000000100000001000000010000040004000400040004000400040004000400040004000400000000000000033003300330033003300330033003300000000000000000033000000330000cc000400cc000400cc000400cc000400cc000000cc000000cc000000cc000330033003300330033003300330033003300330033003300330033002200220000000000000000040004000400040000000000000000000000000000000320032003200320033003300330033003200320032003200320032003200320000000000000000000000000000cc0000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000004400440044004400440044004400440000000000000000000000000000000330033003300330011001100110011003300330033003300000000000000004400440044004400440044004400440044000000440000004400000044000330022003300220033002200330022002200220022002200220022002200220000000000000000cc00cc00cc00cc0000000000000000008800880088008b3003300330033003300000033000000330033003300330033000000330000
|0,6=>0x4400440044004400000000000000000000000000000000000220000002200000022000000220022002200220022002200220022002200000000000000000000000000000000cc000000cc000000cc000000cc0003300330033003300330033003300330033003300330033003300000033000000000000000000000000cc000000cc000000000000000000000000000000033003300330000003300330033000000330033000000000033003300000000440044004400440044004400440044004400440044004400000000000000022002200220022003300330033003300220022002200220022002200220022cc000000cc000000cc00cc00cc00cc00cc000000cc000000cc000000cc000330033003300330000003300000033000000000000000000000000000000000000cc000000cc000000cc000000cc0000008800000088000000880000008b3003300330033003300330032003200330033003300330033003300320032
|_,_=>0
def sP:Nat→Nat
|0=>0x6880a10e1019d0c503842e4c0920e4430140243843e5cd09087cb81002c18202241863c04011067409b380cc090e44186346c2032e68c840628080080cc140e108172c2420328543840c4c907224030f12101861c1c2030c3438c080c300160c5011210186101c2030c140040608080
|1=>0xe1019d0c0401c160cb9a12458860224384065cb090e101a63a0438406c03010e1019702b8384065c0ad0e101ac2e0438406195890e0c301542439106194890e44186502438b080cb9434101a70c04384069831a0e101a50224391480c31a12441861e2438b065c08946101862600384
|2=>0x822438b065c08980101973405f84065ca3e0e101863425991069c31a124433d78243830c05d890e441a60c68004065cd0946101970201191744031a121018172243910618a380e441866e2438406182890e45b030c0438406080890e448060225ab4080cb810e10186281d9840605909
|3=>0x2668087220c31a13282032e05f090e441867a243c32320b8112101975604487231c18634243840618d000e1019802243910618d096a1018634008830d18487080c3130e101868a243910c689090e122222e0438406280890e4418610243910618a0087082032e0438406500a10e10181
|4=>0xe302032e044872240186a624391205e9093810186121c8830d44487220c30100261912e049090e4418602243b522401863424890073cb8100468109e5c0879c10817022438406180800e1019728043b3080cb819a1c8830c05e090e0c30198243cb080cb81121c58406180890e10197
|5=>0x22439106180890f64883b0180890e44b812400487220c313121c584065ca010e1019702243d722e819d02243833a180cc121c8839e5c0800e452030c044870841117021c8830d4c487224018634243910618d09ac1019702fc384065c0d40e45d030c68487231c197a6243910618a00
|6=>0x286800406180890ecc2030c50391067433d121c8834c18d090e441a60c04007080cb81121d19106180de121c89726049090e2c2032e68089234081702003910618d00121c8830c044dd0e2c2032e044d5080ee17021ce0b065c0890e468102e040110618d001246d830c04487b410197
|7=>0x220ee170224391065f201121c8832e069890e471832e04487220cb81121f111200cb9a0224391065cd0113588832e500800e4418602243c32240197034c487080d117021c8832f48487220cb81c2243912120b8112441972868007c0101860224391061899a121c8df06180890e44197
|8=>0x226b1106180890f588832e4c080121c8832e68080121c8e8065c0890e448030c04487220c314121c8ba06180890e441863424391a00cb81001c584065c0890e4418602243ca220cb9a0200491d0401970224391065c0890f9c2030c04487cc0cb81121c8832e4c0890e441970227287
|9=>0xe441860224391065c0bd121c8832e500890e441973404487220cb81121ea91d25c08994441a60c04487220cb81121f591205c08992448032e04009220cbea121c8d0205c0890e441860200487220cb810026511065c0cd121c890065c0890e474032e040090e4481702f44872240197
|10=>0x220cb81121c883d25c0890e448032e04487220cb81121e491065c0890f288d0065c089
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x6450bea16942aa8505096a119420a83c506ea0c9416a8285046a07940ca814501ea029402a8005
|5,0=>0x1cf6392c70d8df29b86366a6b58d3b1a16336c6558c7b1896306c5f58bbb17162d6c5958afb15962a6c5358a3b1416276c4d5897b1296246c47588bb1116216c41587fb0f961e6c3b5873b0e161b6c355867b0c96186c2f585bb0b16156c29584fb0996126c235843b08160f6c1d5837b0696
|6,0=>0x6ecedc55b53b6376b8ed55da73b477680ece5d993b2b7648ec7998bbb116616cc11d7ebaf675deeba1d7132db75a8eb35d633abf7570eac995632a5753eca65949b28c750ae9fd93c3a7174d8a999930325974a6c931d23323f7470e8c5d15b224743cc85dd08b20a7406e7f1cfb31ef73d0e78d4ee39d57
|6,1=>0x1cfb3987722ee29dc1bb7d6
|7,0=>0x4d769a0f325e61b4bc796cd2bde543ca17934f24de45c48478faf1d9e37446688bef161e29344b788ad0f9e1bbc307852f08620d3c14681cd01de003bf977e4efaddf23bdd77ab0f39de3bbc077710ec99d633a57
|8,0=>0x28dbd147a1af419e7fbcf969e4f3ade723cdd7
|9,0=>0x5226
|_,_=>0
def wAt:=mkWire dB 108 246 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x81d2e05222512692225021d2e05061e021d1607081d22250c1e2e052127061d061c081e22252e05021d2225121d1618081d2225741c0c1e281d22250c02121d381c2225381c0619061d2e05081e22252225021d081d22254c1d0c252e0512bd2013061d081d2225021d4c1f021d2225381c22252225281d2225281d081e0c02
|1=>0x21d2e05021d121e12cd081e222522251355021e021d20072005061d02252e05121d381f08052e052007061d0325061d061c08052e0522252e053427021d0c1e2e05064e281d0225741c06192e052e05061d021d2027061d2027061d0611061d22252e05121d081e222522251329061e3a0f0c1d3a470c1d2e050929061e2225
|2=>0xc1d2e052e05021d121d381c08052225281d081d2225021d061d0625021d2e05121d22252225441d0627081d22250625061d121d021d2e05121d070d0c1e08692225021d0d592e05121e064e000502012e05121d081d222502250c0d0c1d2e053a470c1d2e05121d2027061d741f06192225061d06272e052007061d2e05061d
|3=>0x61e2e05121d021d061da01e062522252e052325061c281d02250007121d441d06270359121e2007061d0759121e441e0627061d021d021d121e121d02250c1e2e052007061d222506270325061c066a021d2127061d061c021d121d0225081922252e05021d3a0d0c1d2e050225121d021d2e05081e2225022522252e050607
|4=>0x61f061d061c061e06252e0506070225021d021e061e061f0c252e05281e0225061d061c061d121d0327061c061d06252e05121d061e121d1329061ed21d061f0601121d061d0607061d121e2e05121e0005121d121d021d0601121d061d2e052e05120506192e052e05021d0625121d081d2225
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x2200000440000000000004000000
|5,0=>0x2921318944000241111000000000000008440000000000000000000000000000000000008043c41d10d900000000000000000000000000060c0001710a18000000000089838c0000000000000000000059828410400000000000e20000000184084000
|6,0=>0x621b04d7c6bc25d8ae0c000b715a1ac895e6000570aacd524a63519a8493c60004d9a6492c6933000240d1a68a3441214d0467f33e19e4cec67513919bccda46a3339990cc265f22e1964cac654229114089a64b224191888664031e98e8c6e63431910bcc5a42b2
|6,1=>0x1a86d136793349946c73
|7,0=>0x12e29614a8a505262921488a4051e28e1468a3051628a1448a2050e2861428a105062821408a004fe27e13ec5f24f727a93cc9e24ef27693ac9d24e7272938c9c24df26e936c9b24d72
|8,0=>0x27233819b8cd866a3341998cc86623301
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 13
def pmP:Nat→Nat
|0=>0x272e004e480098b8011970022220043000080d8010000009080010400010300020200034000065800098800120000228000408000800000c0000120000200000200000200000300000400000400000400000600000800000800000
|1=>0x4830c09005010acb82111d04222a0840341080002080d04030208045c1004002001404000806467c0880000939f00c000016c4c029c100531300a32a01445c0288180501000a0000080640100c00201100400200684800c8b801801
|2=>0x14300028445c5088a8a111110e232216424428cb885113103226206000408eb88119f10223e204454320cb0640140c222e11644c22c0804519708a32411445c22808041b17083424104c1c2090104119608000a09465c1288b825115
|3=>0x3040401a511520201039044452c818a511714a22a29444c528888a5103
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x400080000008000
|5,0=>0x602280022a00000000800000000000000000002830516000000000000001c0080e000001c3400000000000e2460000002940028200
|6,0=>0x2928d31472c0ec1b9a18640044a9e4805ee836096181802062326003c9a02ce1b3e5b6951786798b4a4ca218364a8a7739e98752188a34a89fa46b48333
|7,0=>0x63aaaaee5c382ce0c58efe6c1663cdaf08fbd9996dc29d5ac54d1210bb5507140a0b172b7cf31cf
|8,0=>0x31e4c792f1cb87652a
|9,0=>0x1b
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_241 8 roots_241 ops++addP pm 1 dom_164 4 roots_164 ops++addP pm 2 dom_228 5 roots_228 ops++addP pm 3 dom_149 5 roots_149 ops++addP pm 4 dom_244 7 roots_244 ops++addP pm 5 dom_113 5 roots_113 ops++addP pm 6 dom_177 5 roots_177 ops++addP pm 7 dom_240 5 roots_240 ops++addP pm 8 dom_213 8 roots_213 ops++addP pm 9 dom_180 5 roots_180 ops++addP pm 10 dom_225 5 roots_225 ops++addP pm 11 dom_53 4 roots_53 ops++addP pm 12 dom_181 7 roots_181 ops++addP pm 13 dom_85 5 roots_85 ops++addP pm 14 dom_117 6 roots_117 ops++addP pm 15 dom_209 7 roots_209 ops++addP pm 16 dom_212 5 roots_212 ops++addP pm 17 dom_229 6 roots_229 ops++addP pm 18 dom_116 4 roots_116 ops++addP pm 19 dom_165 5 roots_165 ops++addP pm 20 dom_197 5 roots_197 ops++addP pm 21 dom_208 4 roots_208 ops++addP pm 22 dom_145 4 roots_145 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_245 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_145 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_241 8 s (0,roots_241.map (·&&&dom_241)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_245 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_241 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_245==dom_245)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_245 gM v ys):RunD true dom_245 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_245 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 21 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 61 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 61 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 70 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 70 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 45 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_245 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_245 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_245 roots_245 goal_245 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_245
theorem lowS_245:Lower true dom_245 roots_245 goal_245 10:=S_245.noCircuit
namespace S_246
def pG:List (Nat×Nat):=[(2,18),(2,66),(2,130),(4,36),(4,68),(4,132),(6,22),(6,38),(6,70),(6,134),(16,18),(16,80),(16,144),(20,22),(20,52),(20,84),(20,148),(32,36),(32,160),(34,38),(34,50),(34,98),(34,162),(48,50),(48,52),(48,112),(48,176),(64,66),(64,68),(64,80),(64,192),(96,98),(96,100),(96,112),(96,224),(128,130),(128,132),(128,144),(128,160),(128,192)]
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
|0=>0x1ffec6fe7eff5f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x76485
|8,0=>0x32
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_242 8 roots_242 ops++addP pm 1 dom_182 8 roots_182 ops++addP pm 2 dom_214 8 roots_214 ops++addP pm 3 dom_244 7 roots_244 ops++addP pm 4 dom_230 7 roots_230 ops++addP pm 5 dom_118 7 roots_118 ops++addP pm 6 dom_228 5 roots_228 ops++addP pm 7 dom_102 4 roots_102 ops++addP pm 8 dom_116 4 roots_116 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_246 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_118 _ g hchk
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
def isoMvS_159:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_iso_b isoMvS_159 (by decide +kernel) lowS_95
def isoMvS_175:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_iso_b isoMvS_175 (by decide +kernel) lowS_95
def isoMvS_189:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 10:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_187
def isoMvS_190:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_183
def isoMvS_235:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_235:Lower true dom_235 roots_235 goal_235 10:=lower_iso_b isoMvS_235 (by decide +kernel) lowS_187
def isoMvS_243:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 10:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_187
def isoMvS_249:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 11:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_219
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,32,36)] (by decide +kernel) lowS_123
def dzo_45_2:=0xcccc0000cccc
def gzo_45_2:=0xccc800008800
def gsh_45_2:=0x333200002200
theorem lowS_zo_45_2_45:Lower true dzo_45_2 roots_45 gzo_45_2 5:=lower_iso_b (d1:=dom_45) (r1:=roots_45) (T1:=gsh_45_2) [(dom_45,2)] (by decide +kernel) (lower_slice_b (T:=gsh_45_2) [] (by decide +kernel) lowS_45)
def dzo_27_4:=0xf0f0f0f0
def gzo_27_4:=0xf0e0a000
def gsh_27_4:=0xf0e0a00
theorem lowS_zo_27_4_27:Lower true dzo_27_4 roots_27 gzo_27_4 5:=lower_iso_b (d1:=dom_27) (r1:=roots_27) (T1:=gsh_27_4) [(dom_27,4)] (by decide +kernel) (lower_slice_b (T:=gsh_27_4) [] (by decide +kernel) lowS_27)
def dzo_173_2:=0xcccc0000cccc00000000000000000000cccc0000cccc
def gzo_173_2:=0xcccc0000cccc00000000000000000000ccc800008800
def gsh_173_2:=0x33330000333300000000000000000000333200002200
theorem lowS_zo_173_2_45:Lower true dzo_173_2 roots_173 gzo_173_2 6:=lower_iso_b (d1:=dom_173) (r1:=roots_173) (T1:=gsh_173_2) [(dom_173,2)] (by decide +kernel) (lower_slice_b (T:=gsh_173_2) [(0x33330000333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_45)
def dzo_155_4:=0xf0f0f0f0000000000000000000000000f0f0f0f0
def gzo_155_4:=0xf0f0f0f0000000000000000000000000f0e0a000
def gsh_155_4:=0xf0f0f0f0000000000000000000000000f0e0a00
theorem lowS_zo_155_4_27:Lower true dzo_155_4 roots_155 gzo_155_4 6:=lower_iso_b (d1:=dom_155) (r1:=roots_155) (T1:=gsh_155_4) [(dom_155,4)] (by decide +kernel) (lower_slice_b (T:=gsh_155_4) [(0xf0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_27)
def dzo_59_4:=0xf0f0f0f0f0f0f0f0
def gzo_59_4:=0xf0f0f0f0f0e0a000
def gsh_59_4:=0xf0f0f0f0f0e0a00
theorem lowS_zo_59_4_27:Lower true dzo_59_4 roots_59 gzo_59_4 6:=lower_iso_b (d1:=dom_59) (r1:=roots_59) (T1:=gsh_59_4) [(dom_59,4)] (by decide +kernel) (lower_slice_b (T:=gsh_59_4) [(0xf0f0f0f00000000,0,32)] (by decide +kernel) lowS_27)
def dzo_61_2:=0xcccccccccccccccc
def gzo_61_2:=0xccccccc8cccc8800
def gsh_61_2:=0x3333333233332200
theorem lowS_zo_61_2_45:Lower true dzo_61_2 roots_61 gzo_61_2 6:=lower_iso_b (d1:=dom_61) (r1:=roots_61) (T1:=gsh_61_2) [(dom_61,2)] (by decide +kernel) (lower_slice_b (T:=gsh_61_2) [(0x3333000033330000,0,16)] (by decide +kernel) lowS_45)
def dzo_189_2:=0xcccccccccccccccc0000000000000000cccccccccccccccc
def gzo_189_2:=0xcccccccccccccccc0000000000000000ccccccc8cccc8800
def gsh_189_2:=0x333333333333333300000000000000003333333233332200
theorem lowS_zo_189_2_45:Lower true dzo_189_2 roots_189 gzo_189_2 7:=lower_iso_b (d1:=dom_189) (r1:=roots_189) (T1:=gsh_189_2) [(dom_189,2)] (by decide +kernel) (lower_slice_b (T:=gsh_189_2) [(0x333300003333000000000000000000003333000033330000,0,16),(0x333333333333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_45)
def dzo_187_4:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0
def gzo_187_4:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0e0a000
def gsh_187_4:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0e0a00
theorem lowS_zo_187_4_27:Lower true dzo_187_4 roots_187 gzo_187_4 7:=lower_iso_b (d1:=dom_187) (r1:=roots_187) (T1:=gsh_187_4) [(dom_187,4)] (by decide +kernel) (lower_slice_b (T:=gsh_187_4) [(0xf0f0f0f0000000000000000000000000f0f0f0f00000000,0,32),(0xf0f0f0f0f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_27)
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
|6=>179
|7=>350
|8=>218
|9=>53
|10=>7
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x7511f53c655071416c3d141820ceff07155
|5,0=>0x9f1907b2d966ee35e6435acbc4d6f14cf6649c954683546805462cc4497131db330a1a2aef72749c230da22ea720e482063f202091ca871aa9015bf4129050d71c0c9310ba490b0dc05f4605efd029fc00999
|6,0=>0x450af43d9342f46429a6428fa41f164056d404f53e1f33d3293ba3e3a0dd3977f38ede37fd236f1934d1e34a2033c5d32d3131c0b306672f5e02f17a2e81f2e0822c9e52c9092c38e2c20f2c1242a433297c828c7427a6d2776b26d7e257c32516224da72483123906238762300222e79227de2219d214a41ff0b1f4d11f4881e7551d81c1d52a1cbf21c4431a7271a0d219cf9198bf181f017f6e1798c16bc9164031522714e9e14e25142eb134621319611fcd11b40119ac114921123410eed1092710781101810fd8f0fab60f4f90f47d0f4310f1350efb90df690de720dc820dc590d4790cf2a0cab50b28a0af560aee60ae5d0a09809e6709c48096f1091b2090ea08a340828807fc207db607c7f078da077a20637a0530104f1c04e3a047ed046c903c0f03356025e1020b301c860129d00ab0006730049b0027b00116
|6,1=>0xcdb4bba955af36fabd54a4df1a17169f7459c6a292322919a08f2408a4008706d867d58138c80caa7e9597bd797388b734f271fd96ca206b94d68dad65b2f642956417660fd85d8295ae065a9c45921e5862957b0f55ccf53c6d52f534fb1a4f8f24f8b54f3a34dc5b4ca804c0ac4a8554a7f2484e7484df46c984660845346
|7,0=>0x1dd001d94a1d42b1bb601b3181b11e1b0021ab671a6081a42c1a41919fd219b4a199dc194ac189dd183b1182021779c171b016c8016a6a16975164a915f2115eb715c6c1560e1523c14d7514b6c149941401313ff613cc813a711351912bb612557120cd1202711ad911492112bf10d8e10bcf0ff190fe340f1b30f1b20f1940ef290ed450ec850e9710dfc80d9120d6cd0c8fb0bb540b7640b57e0b3100afcc0ae5d0a6870a5a509fc309e3d09c8309a820961208e4208ac90897a0890208793086480832507fbd07e2b079c2078a6076c907659075a20704106cea06af206ae306adf062710546e05425053d00530104c1a04ba404a0e049a7047d8045430414d037b6037a2036f90346502ea902d7c02815026eb026a4025d9024bc021ae020db0204701c8f019d801977018ff0141200f8500c9b00c5d00a0300735005f8
|7,1=>0x4ef894e6704e37e4e0434d4c74d1d74afcf4a67e4a29b4a23749c2149b4b491fe4916c48483463e945d9d45735456864513d447fb447b743e0a439834383b42ed042dfc42d144286f417d7417c8410654106440f5640eac40d234051a3ffd33fb6b3e9603e9133e8793d9d63b6e03b6c63aac03a8ee3a26e3a19c394bc393503849937f6c37dbb37a7a37726376b9375cd373d93738e36c563622636169351fb350993503634870346603460d3446f343d633b5e339a13323432ef63196231940315ca314e1312873106130717304662faab2f9252f6e12f5a52f0d72e7d02cab72ca502c7cf2c62a2b7702b21c2a6d72956f2946e28f55285c62847528414283d527d37279812762b275832707926d5a2562623fa9239f323876228c022656221b72205521c10217c020f3e20d4420921204f3203291f4371eceb1e1a81de62
|7,2=>0xe2721e0424d8c7bd4acdd378fcd500c90e4b815ab64ceb5cefb2928ae6ababbd5a9c2ea8e68a8337a6640a226fa17779fd409f3549f1639eeff9c6e79b6a89b4399ac0496f50958d790ab68fc358a5a78946a88322867ec86650864ff85bbd8585a837648117580caa7e5407cb3a7b2e379ba27876976ec575cb4737e272954715d270d0270aaa707c0704156fbf86c6426c62f6a2756a0706a01c6987268e9d67a7f65eb665993649ff61d2861ae260f1360ef8603415f41f5ee445e9b95d6065d4d65b7335ac26597c257afc57af6574c05736155b99557ca556a552d10528fb5280151ac0517cb50ed9
|8,0=>0x3fba93f0d43e1d33d9d63c0723ba1d3b99b3b7423a3993851c3700133aa4339a1332d3329843279b313c330f262fbce2f8362f2e32f06e2e7772e20f2d9c72cc582c16f2b7792b04c2aa7f29ca4291b028ffb27a3c276d02759a2636f25aeb25865256ae24fa324a04246b12317d22b8d2243122361211a7203dc202281fee01fe7b1ef071df761dcba1d6241d42b1cffc1c6361c0761b4c11a98116b031676815d8815c6c15b2e159e31523c14e4c140ae136ad1367e131af12dab12d401276d11f0b11d3f111c410fae1068c105c90fa8a0f0c70ef5c0e9d50e5280e4a60d32e0c9dd0c65c0c5370c1810bc780b09b0ab1f0a43109a82092e50906408cca085e607b3b076c906fea06ebc06855064a40634605c91053d00534c04c1a044f004407039b80372503498032d90270c01ef4014170134500dcc008e7005cb00182
|8,1=>0xe3b2fd9414c6919c1415b2641b07d3ac8bd9f94d9f67c9b4399ac0498c3296ce5958d792d30927ab91df38cce589bfb89a0a7dcf97ca817c3487c3197aabe7a80d7959c7907e76ff476f4d73e8d734c07302370fec6e6ac6bb606b1c66ab186a52d69eb1692c468ab06898167a78674ae6379b631f6620386082d5f6945ebd75c8aa5c25d5b5145b1d45a97b5a5ab5a48957af656f2054ee551ba8516cf50a9c4fc0f4e3304df394d3394d24a4c2714b4e149cc649a9a4897b484d547bf2473ca46d7a4624745934455914513d4383e42deb4213b417c8415f2415674135b40abd
|9,0=>0xfab72e0b7dd1836b8713aac2da2d9796ce58d84078e3b708596f9746d62b626e55ee57582b7541ae513564f9644eb564c9ff4b0d44abfc4a1fd4264e418283a95a396b5389962fb852eb272d22a2ab0e29bc82746a272992534e1f7e51ed161b0941a804188501260e0ff790e38a0d4c40b94f092e508ce60712a0443603961037c701d3b
|10,0=>0xc502bc4e91b84b6644614a2491deb511d8d
|11,0=>0x2bff1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfff0fff0fff0fff00000000000000000fff0fff000000000ffffffffffffffff0000000000000000ffffffff00000000fff0fff0fff0fff00000000000000000fff0fff0fff0fff0ffffffffffffffff00000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ffffffffffff00000000000000000000ffffffffffff0000ffffffffffffffff0000000000000000ffffff00ffffff00fffafffafffafffa0000000000000000fffafffaaaaaaaaaffffffffffffffff0000000000000000ff00ff00ff00ff00cccccccccccccccc0000000000000000ccccccccccccccccffffffff000000000000000000000000ffffffff00000000ffff0000ffff00000000000000000000ffff0000ffff0000ffeeffeeffeeffee0000000000000000ffeeff00ffeeff00ffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0a0a0a0a
|0,1=>0xeeeeeeeeeeeeeeee0000000000000000eeee0000eeee0000ffffffffffffffff0000000000000000ffffffffaaaaaaaafafafafafafafafa0000000000000000fafafafafafafafa333300003333333300000000000000003333000033332222ffffffffffffffff0000000000000000ffffffffff00ff00ffffffffffffffff0000000000000000ffff0000ffff0000ffccffccffccffcc0000000000000000ffccffccffccffccffffffffffffeeee0000000000000000ffeeffeeffeeeeeeffffffffffffffff0000000000000000ffffaaaaffffaaaaffffffffffffff000000000000000000ffaaffaaffaaff00eeeeeeeeeeeeeeee0000000000000000eeeeeeeeeeeeeeeefffffffffffffafa0000000000000000fffafffafffafafaffffff00ffffff000000000000000000ffffff00ffffff00ffffffffffffaaaa0000000000000000ffaaffaaffaaaaaa0f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa
|0,2=>0xf0f0f0f0fffffff00000000000000000f0f0f0f0fffffff0ffffffffffffcccc0000000000000000ffccffccffccccccfafafafafafafafa0000000000000000fafafafa00000000ffccffccffccffcc0000000000000000ffccffccffcc0000ffffffffff00ff000000000000000000ffffffffff00ff0000330033003300330000000000000000003300ff003300aaffffaaaaffffaaaa0000000000000000ffffaaaaffffaaaafffffffffffffff00000000000000000fffafffafffafff0eeeeeeeeeeeeeeee0000000000000000eeeeeeeeeeee00000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0000ffffffffffff00000000000000000000aaaaaaaaaaaa0000000000000000ffff0000000000000000555500005555aaaaffffffffaaaaaaaa0000000000000000ffffffffaaaaaaaafafafafa323232320000000000000000fafafafa32320000333333333333333300000000000000003333000033330000ffffffffffff00000000000000000000ff00ff00ff000000
|0,3=>0xffff0000000000000000000000000000ff00ffffffffffff000000000000000000000000000000000000ffffffffffffffaa0000000000000000ffaaffaaffaaffaaffffffffffffff000000000000000000ff00ff00ff00ff00ffffffffffffffaa0000000000000000aaaaaaaaaaaaaaaaffffffffffffff0000000000000000000000000000000000ffffffffffffff000000000000000000ffffffffffffff00ffffffffffffff000000000000000000ffff0000ffff000000000000000000000000000000000000ffffffffffffff0000ff00ff00ff00ff000000000000000000ff00ff00ff0000000000000000ffcc000000000000000000cc00cc00ccffcc00000000ffffffff000000000000000000000000ffffaaaa050505050505050500000000000000000505050505050000ffffffffffffffff0000000000000000ffffffffffff0000333300003333333300000000000000003333000033333300333333333333333300000000000000003333330033333300
|0,4=>0x55550000000000000000aaaaaaaaaaaaaaaa333333333333333300000000000000003333333333330000000000005555555500000000000000000000aaaa0000aaaaff33ff33ff33ff330000000000000000ff33ff00ff33ff0000ff00ff00330033000000000000000000ff00ff0033000000330003003300030000000000000000003300030033000000000000ffffff00000000000000000000000000ffffff00ffffffff0000ffff0000000000000000ffffffff0000ff0055555555555555550000000000000000555555555555550000000000000000000000000000000000ffffffffffffaaaaffffffffffffaaaa00000000000000000000000000000000ffffffffffffaaaa0000000000000000ffffffffffffaaaaffffffffffffffaa0000000000000000ff00ff00ff00ff00000f000f000f000f0000000000000000000f000f000f000033333333333333330000000000000000333333333333222200ff00ff00ff00ff000000000000000000ff00ff00ff00aa
|0,5=>0xffffffffaaaaaaaa00000000000000000000000000000000ffffffffffffaaaa0000000000000000ffff0000ffff0000ffffffffff00ff0000000000000000000000000000000000ffffffffffaaffaa0000000000000000aaaaaaaaaaaaaaaa0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f000000ffff0000ffff00000000000000000000ffff0000ff00ffffffff555555550000000000000000ffffffff55550000ccccffffccccffcc0000000000000000ccccffffccccffccffffffffffffff000000000000000000ffffffff00000000ffffffffff00ff000000000000000000ffff0000ff000000ffffffffffffffff00000000000000005555555555550000fff0fff0333033300000000000000000fff0fff033300000ffffffff333333330000000000000000ffffffff33330000ffccffccffccffcc0000000000000000ffcc0000ffcc0000ffeeffeeffeeffee0000000000000000ffeeaaaaffeeaaaa00000000ffffffff000000000000000000000000ff00ff00
|0,6=>0x3333333333333333000000000000000033333333333333000000ffff0000ffff00000000000000000000ffff0000aaaa333333333333333300000000000000003333ffff3333ff00ffffffff000000000000000000000000ffffaaaaffffaaaafffffffffffff0f00000000000000000fff0fff0fff0f0f0fff0fff0fff0fff00000000000000000fff0fff0fff000005555555555555500000000000000000055005500550055000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0a0abbbbbbbbbbbbbbbb0000000000000000bbbbaaaabbbbaaaabbbbbbbbbbbbbbbb0000000000000000bbbbbbbbbbbbaaaa0000ffff0000ff0000000000000000000000ffff0000ff00333333333333333300000000000000003333222233332222fffffffffffffafa0000000000000000f0f0f0f0f0f0f0f0bbbbababbbbbabab0000000000000000bbbbababbbbbaaaa00000000ffffffff000000000000000000000000ffffff00000000000000ffff0000000000000000000000000000aaaa
|0,7=>0xf0f0f0f00000f0f00000000000000000f0f0f0f00000a0a00ff00af00ff00af000000000000000000ff00af00ff00aa0f0f0f0f0303030300000000000000000f0f0f0f03030000ffffffffffffffff0000000000000000ffffffffffffaaaafffafffafffafffa0000000000000000fffafffaff00ff00ffffffff0000ffff0000000000000000ffffffff0000aaaaffff0000ffffffff0000000000000000ffff0000ffffaaaafffffffffffffff00000000000000000f0f0f0f0f0f0f0f0fffffffffffff0f00000000000000000fafafafafafaf0f0ffffffff000055550000000000000000ffffffffaaaaaaaa0f0f0f0f0b0b0b0b00000000000000000f0f0f0f0b0b0a0aff33ff33ff33ff330000000000000000ff33ff33ff33ff00000f000f000f000f0000000000000000000f000f000f000a000000000000ffff00000000000000000000000000000000ffff0000ffffffff0000000000000000ffff0000ffff000000000000555555550000000000000000ffffaaaaffffaaaa
|0,8=>0xffffffff000000000000000000000000aaaaaaaa00000000000000000000000000000000ffffffffaaaaaaaa00000000000055550000000000000000ffffffffffffaaaa0033003300330033000000000000000000330033003300003333333333333333000000000000000011111111111100000f0f0f0f0f0f0f0f00000000000000000505050505050000ffffffffffffffcc0000000000000000ccccccccccccccccafafafafafafafaf0000000000000000afafafafafafaaaa0000ffff0000ffff00000000000000000000aaaa0000aaaa00000000000000000000000000000000ffffffffffff0000555555555555555500000000000000005555555555550000ffffffffffffeeee0000000000000000ccccccccccccccccffffffffffffffff0000000000000000ffffffffffffff00ff0fff0fff0fff0f0000000000000000ff0fff0fff00ff00333333033333330300000000000000003333330333333300afafafafafafafaf0000000000000000afafafafaaaaaaaa
|0,9=>0xffffaaaaffffffff000000000000000000000000ffffffffffffaaaaffffaaaaffffaaaa0000000000000000ffffaaaa00000000ffffffffffffaaaa0000000000000000ffffffff00000000ffffffffffffffff00000000000000000000ffff0000ff00000000005555555500000000000000000000000000000000ff00ff00ff00ffff0000000000000000ff00ff00ff00ff00ffff00ffffff00ff0000000000000000ffff00ffffff000000ff00ff00ff00ff000000000000000000ff00ff000000003333003333330033000000000000000033330033333300000000ffff0000ffff000000000000000000000000000000000000ffff0000ffff00000000000000000000ff000000ff00aaaaaaaaffffffff0000000000000000aaaaaaaaaaaaaaaaffff0000ffffffff0000000000000000ffff0000ffffff0000000000ffffffff00000000000000000000000000000000fafafafafafafafa0000000000000000fafafafafafa0000
|0,10=>0xffff0f0fffff0f0f0000000000000000ffff0f0fffff000011111111111111110000000000000000111111111111000000000000000000ff00000000000000000000000000000000ffff0000ffff00ff0000000000000000ffff0000ffff0000ffffffffbbbbbbbb0000000000000000ffffffffbbbbaaaaffffffffffffaaaa0000000000000000aaaaaaaaaaaaaaaa00000000ffffaaaa000000000000000000000000ffffaaaafffffffffafafafa0000000000000000f0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00ffffffff555555550000000000000000ffffffff0000000000000000000000000000000000000000ffffffffff00ff00ffffaaaaffffaaaa00000000000000000000000000000000000000000000000000000000000000000000ffff0000aaaa0000000000000000000000000000000000ff00ff00ff0000ffffffffffffffff000000000000000000ff00ff00ff00000000ffff0000ffff00000000000000000000ffff00000000
|0,11=>0xff00ff00ffffffff0000000000000000ff00ff00ff00ff00555555555555555500000000000000005555555500000000ffff5555ffff55550000000000000000ffff5555ffff0000333311113333111100000000000000003333111133330000ffff0000ffff00000000000000000000ffffffffff00ff0000005555000055550000000000000000aaaaaaaaaaaaaaaa0000000000ff00ff00000000000000000000000000000000333300003333003300000000000000003333000033330000ffffafafffffafaf0000000000000000ffffafafffffaaaaffffffff0000ffff0000000000000000ffffffff00000000555505055555050500000000000000005555050555550000ffffffaaffffffaa0000000000000000ff00ff00ff00ff00ffffffff000000ff0000000000000000ffffffff00000000000000ff000000ff00000000000000000000000000000000ffffffffffff00ff0000000000000000ffffffffffff000000000000afafafaf000000000000000000000000aaaaaaaa
|0,12=>0xf0f0f0f0000000f00000000000000000f0f0f0f00000000ff0fff0fff0fff0f0000000000000000ff0fff0fff0fff00333300003333333300000000000000003333000033330000bbbbaaaabbbbbbbb0000000000000000bbbbaaaabbbbaaaa0f0f0f0f00000f0f00000000000000000f0f0f0f00000000ffffffffffffcccc0000000000000000cccccccccccccccc00000000ffffffff000000000000000000000000ffff0000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0fffffafa555555555555000000000000000000005555555555550000f0f0f0f0fffffafa0000000000000000f0f0f0f0fffffafa00ff00ff00ff0000000000000000000000ff00ff00ff00000f0f0f0f0f0f0f0f0000000000000000000f000f000f0000ffffffffffff00000000000000000000ff00ff00ff00ff00000000ff000000ff0000000000000000000000ff000000000000afaf0000afaf00000000000000000000afaf0000aaaaffffff00ffffffff0000000000000000ffffff00ffffff00
|0,13=>0xaaaaaaaaaaaaaaaa0000000000000000ffffffffffff0000aaaaaaaaaaaaffff0000000000000000aaaaaaaaaaaaaaaa00ff00ff00ff00aa000000000000000000aa00aa00aa00aaffffffff003300330000000000000000ffffffff000000000033003300330033000000000000000000000000000000000f0f0f0f0003000300000000000000000f0f0f0f00000000ffffffffffffffff00000000000000000000ffff0000aaaaff00ff00ff00ff000000000000000000ffffffffffffff00000000000000555500000000000000000000000000000000000f000f000f000f00000000000000000000000000000000ffffff0fffffff0f0000000000000000ffffff00ffffff00ff0fff0fff0fff0f0000000000000000ff00ff00ff00ff00000000000000000000000000000000005555555555550000333303033333030300000000000000003333030333330000000055550000555500000000000000000000555500000000aaaaffffaaaaffff0000000000000000aaaaffffaaaaaaaa
|0,14=>0xffff5555ffff55550000000000000000ffff0000ffff00005555555555555555000000000000000000000000000000003333111133331111000000000000000033330000333300000000000000ff00000000000000000000ffff0000ffff0000fffffffffffff0f00000000000000000f0f0f0f0f0f0f0f0ffffffffaaaaffff0000000000000000ffffffffaaaaaaaaaaaaffffaaaaffff0000000000000000aaaaaaaaaaaaaaaaffff0000ffff55550000000000000000ffff0000ffff000000ff00ff00ff00ff00000000000000000000000000000000ff00ff00ff0000000000000000000000ffffffffffff0000ffff0000aaaa00000000000000000000ffffffffaaaaaaaaffffffffffaaffaa0000000000000000ff00ff00ff00ff00000055550000555500000000000000000000000000000000ffffffff000055550000000000000000ffffffff00000000ffffffffff00ffff0000000000000000ffffffffff00ff00cccccccc888888880000000000000000ccccffff8888aaaa
|0,15=>0x50505050505050500000000000000000000000000000000afafafafafafafaf0000000000000000aaaaaaaaaaaaaaaa555555555555555500000000000000005555000055550000111111111111111100000000000000001111000011110000ffffffff0000555500000000000000000000000000000000aaaaaaaaaaaaffff00000000000000000000000000000000aaaaaaaaaaaaaaaa0000000000000000ffffffffffffaaaaffff0000ffff00000000000000000000ffffffffffffaaaa0000ff000000ffff00000000000000000000ff000000ff00000000000000ff000000000000000000ff00ff00ff00ff00ffff00ffffff00ff0000000000000000ffff0000ffff0000000000000000000000000000000000000000ffff0000ff0000000000000000000000000000000000ffffff00ffffff00ffffff00ffffff0000000000000000000000000000000000ffffffffffffffff0000000000000000fafafafafafafafa0000ffff0000ffff00000000000000000000fafa0000fafa
|1,0=>0x111111111111111100000000000000000000000000000000ffffffffeeeeeeee0000000000000000ffffffffeeeeeeee00000000000000000000000000000000ffffaaaaffffaaaafffffffffff0fff00000000000000000fffffffffff0fff0ff00ffffff00ffff0000000000000000ff00ff00ff00ff00ffffffffffff55550000000000000000ffffffffffff0000ff00ff00ffffffff0000000000000000ff00ff00ffffff00ffffffffffccffcc0000000000000000ccccccccccccccccffffffff00ff00ff0000000000000000ffffffff00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x50b40a010705c2c0b028400813160404c0c15868240b02830080305840540c020a450160283008030509c0226020681a1203014461a0b02c0a04050740a2406038060d090180a2301828442106038262002840221e0200c040b00810100d09014180e018283a010e06c34190902c1c130c048160e0b85816150704c2812028382612028441208038180a04018080200
|1=>0x5014660c07010060a0589c0204018340c10188305603090181605060ac34120302c0a090181c0c050d86832200584008030781820300700c240a02844081a068b80c101580c281202830081a030bc20210700c1a2e03040361a068800a100200c5806080443c290b02c0a0c020685016028401c1a0902816050700c50160284008290509c220c020203212058301217
|2=>0xf010064305814200e01818780b028406404018180a102101010120502c0a0c0200c16102090018041480c1615200301c031e02c0a1002020320b080fc180e018f4780b02840120e0182816051d810340d030800a1019010520a0a8441804098e00c0b0284008030c048140b0601034030501402331b810060b028406c040181816101a8303c03050740a34060c84603
|3=>0x58407e0e01848140b02810060a05814024f190102606058409c0902068141d00884120e040640c0b08010060a05814024d1908c060a02804221b0200c1a10180301c04098b0161006010060a058148e0c0200c980b0812c183715838060d028408c0401828161500810060a08044940c020680c0b080849248020681a06028400803068180a47061183c04018283a05
|4=>0x888cb203050740a0c0700c145808044182b0d080160508030725701818160508010060a0591c600c020e00c0b028400803050740a012a810065405040420c0700c24060502c0a0e018640c1008940080305040820006010064c050404c0c1594c060d0808418040182c204e20030080328818161e01828161512830080306840605006010060a08138660c0700c3206
|5=>0x38280a0c0700c146302840080302840224006010060a31040220c0700c1a0602840c204018284e1013030461a0502c0a01300c846030502c02210205cbc0a05814024802020320b0803008080181816052e010521a05014022604838520a0280422040182820212d830461a0502c0a0112810261905840b40c0202032200584018040d0640c0b080fc720e018180a10
|6=>0x1a03090040d0640c0b080e41c031e02c0a100200c140b081b418043600c141d028040803358640c10060241c130c840220c1580cd40508030081a0c818400b0803852030518c0a100700c780b02840d204018280a103403008030519c201106010060a33040220c07068142005814200e0181816580801026030302c0a3b048782e0a0e8141804018282064000301203
|7=>0x200c1415009a018040b80c142d0280408033a028202606010060508100e60c04820320b081841839021c40c0b028401c030502c2a011a118080a05814206e11868140b0289408030302c0a3b0204c240b028301223018280a330608c080305014660c22038340a05814020401828204113030087001828160500810060a081bcb60c0200c1410108cc180a05814206e
|8=>0x148280a01130ac1c031e02c0a100205c060a0a9a01823019ec0a0c048ac1a05081681832020a4140b1383046040d10c1605080382e0a0581420253d1e4140b02840182b0700c0c0b08084081a051dc0a01080241c03051e00a100182c0a101b18418440700c860b02840460e0190c16050802408520302c200e01828ee0500840ec0401828160500810060a08084ea0c
|9=>0x302c200e0200c1a06080c012560302c0a100200d040a0820418040181500103f0300829018282a68060c808130c8404c0c02068140500840fe040181420113f030122b388181605080e408030302c0a3b020685c0a0584008130c82c203f060c8080306818204e15810343c0581420230700c140b009901c03050800a1008810060a0589c020401828ce103e8306404
|10=>0x200c5806058401c0309028160506010060a02a210a0c048382e0a0e81402092b80c0c0b02840120409864202606010060a0a9fd0e0c19010520a058140204018280a804283088040d028168408010060d090180a0c04810520a0589c18090200c860b028046404018340c1010838060a0581476830200c140b028ec36131002c0a100612008130c82c200c19010062c
|11=>0x60380808018340c05080c808030502c208c0608cf2030502c0a100611808030502c0a1039010060a05804201c060241c290502c2a0c04a38340a05814200c0700c140b028408a090205c140b0808418040400c320b2383064040182816051da3408030502c0a100200c14104610818040502c0a1012030080305041168a06010060a13840220c0204c340a05a242009
|12=>0x5840420c1908c060a058409c0c0f010060a0585402950200c140508045280c0700c140b0280420340488c060a05815260c0204c060a3c014200c07010521a0502c0a010700c0c0a1002c0a100200c140b080c4182b018281605080fc1809020281605081b81804099c40c0b0284056040d0281605080e812040182920050803012040d130140b0803012560502c0a10
|13=>0x581420320200c140b02840740e0200c140b1384018040d028400b02840121e1180c141d0283046030502c0a015002408033a0281610062781c030502c0a100603808030c81816104a270060a05814200c0700c780b0284008030502c0a104d830121b018340a100611008030502c0a930602408134c82c0a10060c808290502c0a0106010060a058412c0c3e010060a
|14=>0x581420720486c060a05814200c0200c140500840d00c02068060b02840800c0200cd60a0284018860204c0c0b0284018040d00c1405080cc181e0200c140b0280548440f010060a0e81418320200c580a0584018320200c140b081bc188302020061905840180401828161010a8c18830182816050818418040182816050828418090d80c1a060284018320204c3406
|15=>0x820c08030501420260608c060a168141848020680c0a05814200401818140b0291c180414868140b028408a04018280a105396818040182816101b230180401828168908030080335818140508030642b018280a101303088a60182816050803008030502c0a47060e4560e01818160508010261a050142026060241c13050142011061101c030502c0a01048102606
|16=>0x2068060a0280420110200c140b028050a0c24010061905841280c1c80c140b02840c20c0700c140b0a8051e321180c14050804418041c0181605080ac0606058142061060c80803068180a1019010060d05040420c2203852030502c0a010d810060a05840600c11838060a058150a0c0700c14a80284012230d02816050087808030502c2041060dc560e018281605
|17=>0x208303c04018281610270303604018640c105383056040182816051d83072320200c0c0b02840121e0502c0a10370301c030502c0aaa080c80803030281605082ac08030502c202106010060a05815540c0200c7a0a05815540c04810060605814203a1594c060a05840420c0200c140b080c0a00c02068140b02805520c04810340a0e840420c0204c0c0b028407e0c
|18=>0x501500100601052030502c0aaa060256c030502c0a0108010060d03014205a060dc640401828160508010060a028416a110601052030502d08100601034b40581420b10204c140b02840183204810520a058140204018283a050089418390200c140508098180e018280a80082c018045780c320a080441804018281610570301204560281605080301c04018281610
|19=>0x2704418040b80c140b02a14180e0202006190302c20090200c1a0a08138180e0200ce80a058401804098801605080300879018283a050083064230182816101083008030502c0a015d01010030501420110602408030518c0a10060100607050141809070281605081b8180401828161f00810060a0e8140260060ac08030502c20b806010060a05814205a060116e03
|20=>0x50740a0143838060a0284022650614c08032602816100612008130302c0a100608c08030502c0a012282436030c8181610060c8120409864161006011800306afc0a10060117a030502c20bc062ec08030302816050801070030302c0a100f00c1405080011e0c41810060a058148e0c0204c0c2005814200c0200c1405081a018090705c140b0280420320200c1410
|21=>0x502c0a10370301204018281610460300892018281610188300803050142011608301c0305014021008a3c7204018281689080307204018281605238301c041480c1405008448c040d00c140b028406423018283a0506024361a0502c0a100611008030502c204106024ae030502c0a100611008030502c0a01229e808170502c0a100608c08030502c2041060380803
|22=>0x283008030501420a1620300803050409c260620c08030501420a7060100619050404c0c0200c140540041820c1583806060284022370200c140b02840184407068140b0284018041480c140b02a1418091180c140b08138182b01828160508184180401819860a05814200409a60140b02840180414978140b02840180902300140b028401804018340c10180301223
|23=>0x304042091580c140508098188e0200c140b0808418040182816cc080308c230200c140b02804080305014208a060c808030502c021027010060a0a841960c02068140b650401c030302c0a1032810060a0e81402c90200c14c802840180e0d02816050831c18040d0298c0508030120401828161037830081a018181605080d8640e020a4140b028043c040b80c141d
|24=>0x5780c14106904418041480c140b02b4018320200c140b3384018320200c140b330401804018280a1067830081a0502c0a102d03046030501420004783012a5018340a100601006ce05014200c2208c1c03050740a0c58810060a05814200c0200c320605840b40c19010060b02840800c22010060a05840c80c0701026030c840220c2211808030502c0a0102068060d
|25=>0x60c808030501402100891046040d0283a050636008030302c0a100620c08030502c0a100621808130c82c200c02020060a05840de0c021c4060d0301420395b00c140b0284018040400c140b0284074320701026190584018460200c140b02841ae830200c1a060284018046a80c1ad402840180401828161500b4c18321580c140b0284018370204c0619058401804
|26=>0x18281605080e80803030bc0a10060241c290502c0a0106038060a058140210300ac08030502c0a4706010061905041b40c0d80c1a050814018390700c0c0b0284018040980c0c0508044180e018283a0500a3c127a018281605080301203050b40a100601010030c82c2061060c8081a018340c050803808290502c0a014381034030502c0a106c8243c290502c0a01
|27=>0x61101c03050142011060ac080306814205a060241c03068180a1022010060a05815bc0c1900c140b02840680c0200c140b028407e0c11810060a05815bc0c1b81010030502c0a1002020261905841280c3d00c140b02840c00c15810060605840600c0200c140b02aa9ba0c0200c140b1384018830204c0619058401804018280a103fa1c180401828202113030120e
|28=>0x284018230700c140b0808418090200c16050810018041480c140b0810418320200c0c0b028406c0e0200c0c0a05840600907068140b02804203704838060a0581420040182816050091412040d0340c05081f008030502c0a1022838060a028418e11060e4120e01818160508010060a028410a260602456030501420a7060102e0a05814206e0602408080502c2030
|29=>0x119c4140b02840181b0204c3406058142004018480c0a05814180e0980c0c0b02840a00401848140b028301c030502c0a101f83008032b0181605080ac1c030302c0a104a010060605814b87c23010060a05814200409ab0140b0284018326f810060a05814200401818780b02840187a02068140b0284018090200c140b028ec1804018280a100896818480200c1a06
|30=>0x1b03008030502c0a10428307204018f0160508030120e018280a01080441c04018281667080300817018281615478306404148281605428303c04018281615438300803030281605082840813018642011060dc08030502c0a1059010060d03040420c0700c142005814200c07010060a05804204e19010520a0581402040182816e008084181e0200c1605081001809
|31=>0x4a03008170502c0a101283064090200c1a060284008290182816156883088040190c16050803012e21482816050803072045602816050803072040182c0a101b030f804018280a1034030640401828204e1303064040186414101303036030501420112803036030502c0a101f830121b04028160508031c2040182816050803008030502c0a01081c906040182c0a10
|32=>0x5814200c3901006e405814200c0200d040a02840220c19010060a058142085060c81204018283a0508030080305014208508830080305041a411061108c0e01828160508010060a08084220c0200c140b028ec18090200c14102709818440700c140b028408a390200c0c0b02840e409020a4140b02a1418392b80c140b0284018370200c0c0a058142004098641610
|33=>0x5814201b0700c140b02840a00c0f08c0803050740a0c04810340d05014200c4e00c140b0284018e50200c140b0284018040182816050826c183904838060a05814200c0d810060d0284018090200c140b08138180907068140b02840182b02068060605814202b02068060a05840420c11810060a05815260c02068140b0284148090200c140b02840184522010060a
|34=>0x1818140b02840183204810260a05814200c021e4060a05814208f06010060d030142050061101204018281605008307204018281605080315a090d80c140b02840181b0200c140b02840180e020a4340a05814200c11a98060a05814200c0200c1a050814018230700c140b0280408030502c0a1050831cc04018281605080303604018340c05080301c040400c0c0a
|35=>0x83008030502c0a010834c18040980c140b02840183a0200c141508044184604810060a05814200c22038060a05814200c0f01034030502c0a100608c060a05814028f0637008030c8281610063a808030502c0ae90803008e80182816050803166040980c140b02840180401818160508124182301828160508280180e0200d040a028401804018283a0549830121b
|36=>0x62d808030502c0a010801006560502c0a10061101c29018281605080301c041480c140b0a830640401818140b028411c040d00c140b02840180911868140b028401804018281605550300803053ac0a1006038060a0581420c70602408030502c0a100635c0803053180a10061f064040182816050803012030502c0a105f0300813018181605082441204018283a05
|37=>0xd810060a05814200c02068060a0580420211c81026030302c0a1006010261a0302c0a1006010060a05841da0c0200c0c0a05814205a06010060a05814200c1d03808030502c204e0601006060501420a70601006190502c20a00611008290d02816050803008030502c0a102d0310c04018283a050803008170182816050084122047602816050803008030501420a7
|38=>0x502c0a10060ac08030502c0a10062b41c030502c0a10280310c04098281605080300803050740a1078030640e0204c140b02840181b0200c320605840180902068320a0584018090700c140b02841ce370204c060a05814200c1c810060a05814200c5907808030501420110601026030502c203006010060a0587c200c0200c140b08334184411810060a0e8141883
|39=>0x20a4140b0280418860200c140b02804200c1901034030502c0a010811008030502c0a1006114081a0502c0a010821cf4040182816050084018390200c0c0b0284018320200c140b0a84018090200c140b028410a0c02068060a0e81402090700c14050804418390d810060a05814200c0200c140b02841a60c0200c320605840a00c0f010060a05814206e0615c0803
|40=>0x803088460200c140b028401804018340c05082540803068180a10488c80808018281605080316204018281605080301c040182816101083008030502c0a107a030362b0200c14050829c18047980c320b08030080809828160508250183204810060a0581420ee4181026030502c0a100602408030502c0a01081c86e04018281605080301c04018281605081b81809
|41=>0x481010130502c0a1006010100a0581420940620c08030302816050803008030502c0a107b83008037b02c0a1006010064c0502c200c02068060a0581420500608c08030502c0a103703106040182816050803012a501828160508030120e01828160500840082901828160549830642b0182816050803008030502c0a010828008030302c0a10791f01204018281605
|42=>0x30142004018281605080fc181e0200c140b028410e0c02260060a05814200c0200c140b0284018fa02068140b02840920c5b010060a05854200c04810520a05814200c7188c08030502c2021063e408030502c0a100602408710502c0a10060102e030502c021032031f00401828160508030120401a64140b02840180e0200c140b028410a0c3d010060a05814200c
|43=>0x6010060a05814200c7d810060a1002c0a10060102e030502c20640603808290182816050083056b601828160508030081a018340c05080306404018280a101303088320200c140b028401804018280a0108044187c07010060a05814200c0204c341905840181e020a4060a05814020c11838060a02840220c0488c060a0e814180401818140b028407e0c07010060d
|44=>0x1480c140b02841a20c1908c1c030502c0a1006010060a54014200c0200c140b8084018040d00c140b02841e80c0200c140b02841a20c04c00060a05814200c0200c141d02bf8183204810060a058409c0c07010061905040220c0200c140b083f0180401828161027030080303028400b0284018530200c140b0808418090200c140b02840c00c418e408030502c0a10
|45=>0x8182408030502c0a10060c808030502c0a1006010060a05814208506038060a05814203e1180c140b028411e0c1902408030502c0a01080243c0e01828160508030640e0200c140b0813818320701006190502c200c0200c140b02aa8200c19010060a0581402100601007020502c0a100602456030502c0a10061c81c040d00c140b02804200401828160508031ae04
|46=>0x2804200c0200c320a0584018950200c320a0584018910481006190502c200c0200c140b0284018b219010060a02840220c158100606058142094060241c030502c0a01080301c04018281605008410e0401a64140b02840181b02020060a05814200c0200c1b040284018046004c060a05814200c19010060a0581420ee70810060a05814200c0200c140b028042072
|47=>0x1480c140b02840180401828160500841220e0200c140b02841cf070200c140b0a840180e0200c320a0584018048300c140b0284019050200c1a0a02840180e02068060a05814200c0200c140b028417c0c0200c0c0a0581420500608c1c030502c0a1006010060a05814205006010101a018281605080303604018281605080305604018281605080312a040b80c140b
|48=>0x2840182b0200c0c0b0284018860200c140b02840183207010060a05814200c0200c14f10e814200c02068060a0581402100603808030502c0a01080e408130182816050803008030502c0a1006174081301864161006010060a05814200c390c812040182816050803008030502c0a10248301c04018280a100883046040d00c140b028401804018340c05080300817
|49=>0x200c140b0284018725b010060a05814200c04810060a0581402100601034030c8281610060c808030502c0a1006110120401828160508030080305014201106010060a05854200c8402456030502c0a1006010060a0581420c9060ac08030502c0a10062e408ef0182816050803008030502c0ae90803008030502c0a1062830120401828160508031dc390200c140b
|50=>0x10060a05814200c0200c140b02840189104810060a05814200c0200c140b0284018ee02068060a05814200c0200c1a0a0284018040980c140b028401804018281605008401804018281605080307c090700c140b028401809
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x794032a0145007a8029400aa0005
|5,0=>0xe1606e2835981a0c0ca6062302f98170c0b26056302998140c09a604a302398110c082603e301d980e0c06a60323017980b0c0526026a811d8082c03b601ab00bd8052c0236
|6,0=>0x14db8a51c51ae286713fb89e1c4e2e26a7131b8971c4acc24f712438905c474e233711638895c43ce21951093882dc408e1fd70fbb07c1c3d2e1e270edb8751c39ae1c670dfb86e1c362e1aa70d1b8671c32ae18e70c3b8601c2f2e17270b5b8591c2bae15670a830525c284e13b709a384b5c24ce11f708c38445c214e103707e383d5c1dce0e77
|6,1=>0x229b9131c88ae43e721bb90c1c852e422720db9055881ce407720038fe5c7e4e3eb71f238f75c7ace3cf71e438f098778c3b661d7b8ea1c742e39a71c9b8e31c70ae37e71bbb8dc1c6d2e36271adb8d51c69cc34771a038ce5c664e32b719238c75c62ec3107184b8c09c5f8c2f66177b8ba1c5c2e2da7169b8b31c58ae2be715bb8ac1c552e2a27
|6,2=>0x16c9cb56e5a472ceb9659cb1ee58872c0b95e9cae6e56c72b2b9579caaee55072a4b9509ca76e5347296b9499ca3ee51962893942dca08e4fd727b393c189d2e4e2726db9351c99ae4c6725fb92e1c964c4ab725239275c92ce48f7244b1209c8f6e4747236b91a148c2e45a7
|7,0=>0x3d1b9e6e0f27078b83c239df20ee9076c83b241d75ceab074d83a2c1cf60e6b072d8392c1c760e2b070d8382c1bf60deb06ed837339b7a0daee6cf8363c1afe0d70e6b2635541a8dcd3706938345c1a11ccf906748336419920cb906548326419120c7906357316c18960c3ce61683074181a0bfee5f782f7c179e0bbf05d782e8397220b82e5b98
|7,1=>0x4c9c262e1307097b84b9c25ae12c7095b84a9c252e128ac93d849ac24b6124b091d848ac2439d20d08fe847b423ba11cd08de846b4233dd18f08bf845c3a2c2115108a0844c4224211110880843c421c210d10860842cba1461096c843841e3a0d210590824840e42059901ee80783ffc1fde0fe2c7e983f0c1f660fa307c983e139eea0f6507aa8
|7,2=>0x5c342dfa16ed0b6f75b3c2d81d6b10b5175a4c2d0616730b318594c2c8616330b118584c2c09d5f50af2857542b8a15b50ad2856542b0a15750ab37555c2a8e15370a938545c2a0e14f70a738535c298e14b70a538525c290e14770a3385163a89214390a148506ba81613fb09f584f6c279613bb09d674e74271a137ee9b784d7c26a59343099b6
|7,3=>0x6b9bb5ae1ac70d5b86aa3b535da8b0d3d869b3b4ba1a4eed1f868bc343e1a0f0cff867bc33be19cf0cdf866c3b3421992ecc1865cc32c619530ca1864cc324619130c81863cc31c618d30c61862d3b14a18950c43761e3b0d218590c24860e4305218190c0485febafd617db0be675ef42f5dd79f0bc875e132eedd768ebad75d2c2e79d72d0b8e8
|7,4=>0x7b343d7a1ead0f4e87a343cfa1e6eef2f87943bc821e310f117784c3c061df30ef18774c3b861db4eed28765bbb0e1d7aceb58756c3a961d3b0e958746c3a161cfb0e758736c39961cbb0e558726c39161c7cee377717c389e1c3f0e178707c381e1bff0df786f7c37a1dbc10dd886e8437221b810db886d8436a21b410d9976c8c36261b04ed7a8
|7,5=>0x20a5104b7821c40f1e06af02d8812c4076202b100d8802c3ff9dfed0fee87f343f7a1fad0fce87e343efa1f6d0fae87d343e7a1f2d0f8e87c343dfa1eed0f6e8
|8,0=>0x92f4495a249b3245891f3c8dde45f1226990fbc85a641d120688ff447d663d931e578ee4c752239731c388ddc46ca635511a198ccc46462313118278bccc5c262cf315f88ab4c536628b113d889a4c4b2224af11e788b4443a220d10fd987a4c3b221c910dd786ac4336218930bd785ac42b6214b109c984a44235e109307b983a3c1b220c7305a9
|8,1=>0xa373d19de8bd34568a274511a287b34367a16cd092683734129a054500667f313f099f3ccf7a67ad13cd99e2c4ef6276933ad79d2c4e726729138c89c1ccdee26e5336a89b144d6a26a3334989a0c4ce626613327998fc4c5e2620f3097980c4be265e112e7996fc4b61e59f32c7895fc4ade255f12a6994f44a5a251b3286793fbc9de24df12669
|8,2=>0xb3c4d9be6cd0f6617b2c4d9422c9116417b1c4d8c22c52f6227b0ccd8462c1135ff9afbc57be2bcf15de9aeb4573a2b8d15bd9adac56b26b4af59c9aca45635eb09357d7abac55b26ac9155c8aaa455322a87353b8a99c54ae2a45351a8a88cd4226a0114f79a77c539a69bd14d77a683d31e697d34b68a574529a293d14968a474521de8fd34759
|8,3=>0x2ea9174b9ba14dce66e6317289b90bdc626e2117088b8045bde6ddf16e78b703db622d9f36c69b5ecdad26d5916a39b4dc5a4a6d1336818
|9,0=>0x19098c80c63e271e118e79c6fc635e319d38c77c5fc62de315f18a69c4f4625a311d18859c3ec61d630db18649c2e4614e709718429c1d460cdf05718229c0d4604a301338027bfccdfc62fd317e18becc5f462f9317c09bdc45ebe6f4f179f8bcb4de3a2f0b377c9bba45db22ec9175c8
|10,0=>0x6502327119308c9446485f23319118
|11,0=>0x19487
|_,_=>0
def wAt:=mkWire dB 265 192 0xffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x808101819048180200d1c8180482902031018110503102031080f1050f904830018110481805829050310801502031018e91c8300204d0483101811080311905402841018390203110041048180202905031050310803d07034018110203105829070740200d02031018050803105841020411282904804018310200d080310507d0d0540183102005080310284101819050310803d07034018110203105829
|1=>0x5031080311902f0206901831018410282904818050311580d1186a018310503101959158680183102029048070181110041048180203105031081490d064050310183102829028410480408031100410481802031018110503119017048310181101819028290203101811050310700d0702f0203102019040170181905031190640700d0203101829028290181a1183105115220300188d048290483101811
|2=>0x18291004104818018110182905031048410200d0200d0501502031018290202919034058290483101811048180503102829059150203122030020a502031080f2050f90483001811048180200d02031029951580f02029050310200d020050180508031058410803d070340181102031058290203105915220300188d02041080310d0170206901831018050197d11830020410803101819081751583002029
|3=>0x1905402841048310200d1902f048310200d050e9020311c830018ad020293e02f0b811018050803102041050b5070740203105841018411905402841048310200d0511501831220300188d05031020310d01701831048040188d0d064050310200d01831028290480407074020310180508031058410200d040130181905031019c904829048320200d0204104804018310200d08031080e9050311c8300204d
|4=>0x188d020410d0170200d0d0410183141843040110181905031080e9048311c830048290204d19064028290483105031020311004104818050310200d0203101805080310584143031048330200d05115080312203004841080e9020311c830018ad02029050311906402829048310200d050310200d1586801831020290180604832050311001504818018310200d05031020310b81701805080310481808031
|5=>0x205e018050803111832058e91c8300204d0184102031018310803104818020310503149017019410201a050310216a0186e158313e00f048050200d080310503101a450203201829018311c830018ad19074058410483101811050850d017018310200d15868018310202902031018190503105829028da1902b048310200d3c81701a3d0200601841020310181102841118330200d01831020410203122030
|6=>0x48291905402841018390203104818018310200d050310802d11831018110204102041080310183a020310513919017048310227d1483b0203101841028290181a020310503102275148380203101841050f902031048300181107029018110203105829082691180d1183202041048320200d048310200d4c01701a5d0702b020310d017118690183102041190170483101811018320200508031028410702f
|7=>0x4841020310181108031050310200d5283115833020293e02f04805018113e02b1186901831020411002d048180181105031048330181105a16190430206901831020051483001841080310802d118310188d020411906402829048310200d4181719029048310200d040110d029018310282904011040130181905031510310481b0200d050310200d0201905031058290d011018310182905031048311c830
|8=>0x20310597d02031118300204102041018310200d080313e0170f00d02005080311c833018ad020291902f190290483101811070740204102031058410181a41843048190200d0183122030020a501841028da1902b048310200d028e91c8300204d018291002d04818018111902f0483101811022691180d118320204141843048190200d05031020311580d02029050311902f0206901831018110203101829
|9=>0x80f9048300200d050311c830048290200d02085020290d017018311481301841018110d01701831058410481a0200d050310702f01831020310803119043048310200d0803102829022510181a0503104013098310204d01829020310200608031028410700d0702f02031019751583002029050310401301819050310700d0503102031058290d017018310582902031020190401701819050311904301839
|10=>0x22c909832048310200d080310480405841018110803102202080450702f02031028290702f0203102a1619043048310200d01ab51c832048290200d3e017148390203101841190170183907041020310d82f020190503102829080e91c830018ad0202904829048310200d050310200d0f00f020050803102031080f9048300181143031048330200d11885020410d017018310811522030020a501841052a9
|11=>0x20060803105841020690d0170183100a9314830018410803109831018290702f020310591522030048410803d0703402031058290f00f0181107041020310d0540803101831028410802d0480601811080315601701ae51583201a01080450702f020310811522030020a5080310d80f0201905031058294183319029048310200d57843018450702f020310291522030020a5018310529114830018415980d
|12=>0x28290182902829048310200d01afd0582905245020325e81701af907043020310da570201901832019751583002029050310f02f0223d020060803141843048190200d05031048180181101829050313e02f04805018110803101805020310181108031190170702f018390203119043020690d0410183102031018190503102829058291901704831051391901701839020310481801811018290503101a3d
|13=>0x983a02031018290191522030020a501a65051c9048320200d0502d0401701819050311183102041028da1902b04831019410201a0503101a02080450702f020310702f0200608031018413e0331186901831020410204105841048310181102019018310200d05031020e91c83004829018113e01711869018310203101806080310584102085050850d017018310181a0803122030020410200d0201905031
|14=>0x183105a7d1483b020310184104843018110183105aa5020a6018414181704819050311902b0206901831018390203101841080310200501805080310584105a86628310482b01811190171902f0d82f0d80d02019050311902f02829048310200d080450702f0203105031020290702f02031020a5018413e0431483902031018410204119017048310200d41813158690183102029031cb048320200d01b09
|15=>0x1902f04831018110188d02041020310584104ab51c832048290200d0d80f0201905031028293e02b19041048310200d050150702f0203101829220331180d02041050310d0170183105829020291902f04831018110d017083353881701a4502032220330188d020410595663831048430181119017048310200d5b02f022550183202841028f901831048300200d020311580f020290503105841080310206a
|16=>0x50310503101a450203205829021c9048290483201811098311c8300204d0700d0203101829028290401101819050310582901b51053590683205829430310483301811050151c8330204d0182957817018450702f02031083451483a02031018410d011080850d017018310813919017048310200d5982f022c909832018294180f1586901831020290f02f0f01311831020410181105829158330202905099
|17=>0x236d0c832028290502d021410201a05031018ad02031020290503105031018290702f0203105841020060203108031021810480601811080310707401811020310584102829040130181905031020690582901831050310180602031518311186b0183102041020050181101841080310702f01839020310188d018310503143029048330200d09b090983a02031018290182902829048330200d0401101819
|18=>0x20290503101811020310582904841081c9048320200d0205e020690d041018310835d220320188d02041418330401101819050310400f09831018290218104806018110803102029040170181905031052aa080f9048300200d1905402841048310200d0704d0203101829028291902f0d017020311c8300181105925098130182905031020310181101841080310480601811080314184315869018316e02f
|19=>0x1c8181580d0202901806080e91c830048290200d022510181a050310582902031020410d017018313e02b04805080313e01714839020311902b048310200d020310401701819050310200d02031018310803104829018110803122030020a50184105829018310200d050310702f050311902f190430483101811018110d82f15831020293e00f0b81101805080310200d040170181905031018410582915831
|20=>0x702f020310d0170582901831050310481802031018110503108031190170183902031048310181101841080313e02b0f00d020050803102041019c9048320200d0183102019018290503110041048180200d05031018290201a10041048180200d05031020310481a018110503105031158680183102029020310181a0202905031081751583002029050313e033048050200d0803101ab51c8320204d01829
|21=>0x2029048291902b048310200d3e02f048050181108031190171902f04831018111902f02829048310200d0702f0d81307029020310216a02019050310181902019018110503115ab51c832018ad0202912832048040200d1902b19029048310200d1904343031048330200d02031080850d017018310180502006080310284119043048310200d01806020050803102841510310481b0200d050310282901829
|22=>0x48320200d0517d1183002041050450702f0203119043048310200d0584104831018110702f19043018390203157817018450702f020312203314811018410702f0d017080e91c8300204d018291902f190170483104832048290200d048310200d41833048190200d05031028290400f098310182901805048040200d0803105829048310181105031020a5018410200d0238d1483201841018ad01ae515832
|23=>0x201a0503105829020310204108031628310482b0200d04b9f0200d050320201905031058290181902031050310d8130702902031118310204105841018310200d0582902291148300184111a57018320204132831018ae0202904829020310181107029020310582919017048310200d0183102031018110183102029050310d017018310202908269118320204101831148300184122030048410200d04841
|24=>0x48410200d1481102031018410200501831080310200602041080310236d0c83202829023a5082550183201a691183202041022c90983201829098130182905031020410183a02031050450702f0203105841082450203202019018110503101829048310200d01a3d02006080310201a0503105829048410200d080310204d01829020190181105031528311583302029018310203101841022691183202041
|25=>0x2032080310197715830020290d82f0201905031022550183208031158680183102029148110203101841020310184102841048310200d050310183111833020410200d0183102041080f9048300200d058f90483001811048430203101811220320484105aa5020a60184119041048310200d0200d0704302031020320182905031058410181108031048070200d1c8300204d01829028410702f0203122033
|26=>0x200d02031050321c8330204d018290981109832018290702f07041020310401709831018290d05401831028413881701a45020320188d02041058410d80d02019050310d01701831080310981101829050310183101829050317781701bb9080320186e02019050311c8300204d018291901701839020310d82f0201905031028290183a020311481101831018410d80f020190503105841048330181101805
|27=>0x48330200d0d011018310803122030020a5018410180601831080310221d01806080311580d020290503102841048310200d19043048310200d0584101831080310702f020310181115831018ad02029048070200d080310201a05031028290f00f0200508031023c909830018291c832018ad0201a020310503101829048330200d01bc60e831058410183902031018290201905031028290200d0183102829
|28=>0x8031082450203201841020290483101811080310183a02031098300182905031048050200d0803122033020a501841018320503105829020320503105829020690d02901831023d501b9d05032020310d017018311586b01831020290d82f15831020290282909833018290400f098310182908032048310200d098390203101829048320200d080311c8330204d018290187a0704102031018110184108031
|29=>0x204e01829022550183202841018111483201841020410d0170183143041048330200d019c9048320200d0b817018050803101a391183302041051c9048320200d1904301839020310221d0180608031098310200d0182901a510181a05031048190200d0503101afe0524502032050fb048300200d050850d017018310201a01831050310187a1183102041048190200d050310181115833020290203101811
|30=>0x1c8310204d0182954832020a601841048180200d050310b81701805080310203101841080310225501832020290582901831050311902f048310181104841048310200d080310702f02031148390203101841018290183102829020050184108031020410702f020310181102041058410481a0200d050310503102031058290481a0200d0503102005018060803101a5d0702b0203163832048430200d01831
|31=>0x28290183902031080f9048300200d048310200d08031053250206a0183102029048320181102031018310803122032020a5018411483a020310204101839020310597d11830020410297515830020291586b01831020291483a0203101841018110239d05032083fd0e8320584119017048310200d0702f020310282902bf60d0430183119017048310200d048180200d05031020850d017018310480608031
|32=>0x28290203202829018110282909832018290702f01839020310181a0202905031020310181108031018060203108031051c9048320200d02019018190503105255018320582909a45020320182908032048310200d15a550183202029048320200d0803104bb90200d0803243031048330200d19043048310200d0203104830018110f0131183102041048310200d08031018110704102031190170183902031
|33=>0x18290202905031048330200d01839020310e83105841018310803102031080310204d0182915830020290182902829048320200d048310200d0204e018290702f02031018310204105031058291483101841020320803102031050320205502841020310282914833018410203505829020310183107043020310201a0503102031020410201a050310d0290183102019050310183202029018050803101832
|34=>0x20320200d0803201831058290182908031048300200d0203101811048320200d02255018320200d080310183102829048310200d048410200d0702f020310a8320284101811020290206a01831158320202901bb90803208255018320482b0200d0200d080320204d
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x70000
|5,0=>0x1960000000000000000000000000000000000000000000000000000000000000136000000000000000000000000000000d60000000000000000007600000000
|6,0=>0x773000007610742000000000000000006f506d200000694000000000000000000000645061300000000000005c500000593000005450000051304d4048500000000000000000000000004710000000004340421040203c400000000037500000325000002f302d202a30000000000000000000002820235000001f4
|6,1=>0xe24000000000de40dd10000000000000dc10d750d610000000000000d15000000000cd40c94000000000c450bf50ba5000000000b8200000000000000000000000000000000000000000b440af50ac30a840a350000000000000a1209c5000009750000092508d5000000000000000008c108930845000007f507b407a10000
|6,2=>0x1364132400000000000000000000131112d41294000012450000000000001213000000000000000011d4000011850000000000001135000010e5000000000000000010d1000010b200001065000000000000102410110fc500000f930f450f040eb500000e65
|7,0=>0x20a42064203320031fc41fb11f741f431f041ec41ea21e641e241de41da41d641d2400001ce41ca41c641c241bf31bb41b741b341af41ac31a841a441a0419c40000198419441922190218c4188418531814180117d317c117931754172316e416b316741634160315d315941554151414d40000000014a31464142413e413a4
|7,1=>0x2df42dc300002d842d532d412d042cc42c842c532c142be32bb32b7400002b342b032ac42a842a442a0429c429842944290428c428932854281427d4279427540000273226f426c326842644260425c425842553251424e324a424732461242423f323b423742334230322c42284227122432204000021c421842153212320e4
|7,2=>0x3ab43a743a343a1239d43994396339240000390238c438843844381337d437a337643724370236d336a33664363300000000362135e435a43564000035240000000034f334b4000034743461343333f433b433743334330332c432843244320431c431843144310430c43093305430142fd42fa32f642f242ef32eb42e742e34
|7,3=>0x48b448744843481347d447944754471446d446944654461445d445b245744534450344e244a44464442443f343b4437443434304000042c4428400004253421441d441944154411440d44094405440143fd43f943f543f143ed400003e943e633e243de43dd13d943d633d243cf33cb43c743c343bf43bb43b923b543b233af3
|7,4=>0x551454d454a35464542453e4000053a45364532452e4000052a45264522451e451c251845144510450c450845044500400004fd34fc14f8400004f444f044ed34ea34e734e344df44dd24d944d5400004d414d314cf44cb44c744c344c214bf34bb44b744b3400004af44ab44a834a444a0449c4498449440000492248f3
|7,5=>0x5ae45aa45a735a525a1459e3000059b3599200005954591458d4589400005872583457f457b45774573456f456b456835644560455d3559455540000
|8,0=>0x66c3669366636633660365d365a365826553652364f364c3649364726443641363e363b363836353632362f362c3629362636233620361d361a361736143611360e360c260936063603360035fd35fa35f735f435f135ee35eb35e835e535e235df35dc35d935d635d335d035cd35ca35c735c435c135be35bb35b835b535b23
|8,1=>0x72a372737243721371e371b371837153712370f370c370937063703370036fe26fb36f836f536f236ef36ec36e936e636e336e036dd36da36d736d436d226cf36cc36c936c636c336c036bd36ba36b736b436b136ae36ab36a836a536a2369f369c3699369636933690368d368a368736843681367e367b367836753672366f3
|8,2=>0x7e927e637e337e037dd37da37d737d437d137ce37cb37c837c537c237c027bd37ba37b737b437b137ae37ab37a837a537a2379f379c3799379637933790378d378a378737843781377e377b377837753772376f376c3769376637633760375d375a375737543751374e374b374837453742373f373c3739373637333730372d3
|8,3=>0x83638333830382d382a382738243821381e381b381838153812380f380c380938063803380037fd37fa37f737f437f137ee37eb3
|9,0=>0x8a1289f289d289b28992897289528932891288f288d288b28892887288528832881287f287d287b28792877287528732871286f286d286b28692867286528632861285f285d285b28592857285528532851284f284d284b28492847284528432841283f283d283b28392
|10,0=>0x8a918a818a718a618a518a418a31
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 16
def pmP:Nat→Nat
|0=>0x4000000000001c40000000000d200000000006100000000002a80000000001440000000000a000000000004500000000002080000000000f0000000000062000000000028000000000012000000000008400000000004000000000001d00000000000e000000000006400000000003000000000001500000000000a000000000004400000000002000000000000f00000000000680000000000300000000000120000000000080000000000028000000000010000000000002000000000000
|1=>0x51800000000028000000000011a20000000008d000000000044780000000022100000000010e200000000082000000000040800000000020000000000009fa00000000044500000000022080000000010000000000007a000000000028d000000000144000000000088000000000041200000000020800000000009800000000004800000000001fa0000000000dd00000000004e800000000026000000000012a0000000000910000000000460000000000220000000000108000000000081
|2=>0x107e80000000083740000000041a200000000201800000000100a0000000008030000000004008000000002000000000000c40000000000535000000000250000000000122500000000086c000000000431400000000213a00000000109c000000000844800000000420400000000210000000000107400000000082c8000000004144000000002040000000001018000000000808000000000402000000000200a0000000010040000000008008000000004000000000001500000000000a34
|3=>0x2d1e0000000014bf400000000946a000000004a0400000000247e80000000123740000000090ea00000000481c0000000024040000000010bf40000000081fa0000000040dc000000002062800000001025000000000810000000000407d00000000203a80000000101940000000080ba00000000405100000000201a800000001009000000000804000000000400800000000200200000000100040000000080000000000028dd00000000144e000000000a2300000000050020000000022dd
|4=>0x48488000000024210000000012100000000009031000000004814000000002408400000001204000000000901100000000480000000000208000000000102000000000080cd00000000404200000000202000000000100da00000000806500000000402880000000200e000000001004000000000801800000000400a800000002005000000001002200000000801000000000400280000000200100000000100000000000068fd0000000034480000000018bf400000000c5ba0000000060fd
|5=>0x8000800000004000000000001c1fa00000000dafd000000006d5e80000000369f400000001b42a00000000d8fd000000006c7a80000000360f000000001a1fa00000000d0bd00000000684e800000003423000000001a10000000000d07d00000000682e80000000340000000000191fa00000000c8dd00000000626a80000000303f400000001810000000000c020000000006000000000002a26400000001347a000000009a1d000000004d0480000000262d4000000013122000000009851
|6=>0x20011000000010008700000008001fa0000004000d100000020004200000010002000000008000ea000000400020000000200002000000100000000000078904e00000010c87900000008441a00000004200540000002091fa0000001042fd00000008203c80000004020d000000020104200000010081c00000008040080000004003f4000000200028000000100004000000040000000000011223c0000000485fa00000002107d0000000101040000000080160000000020082000000010021
|7=>0x20450e80000010223f400000081047a000000408084000000204010000000101a37400000080c118000000404afd00000020256e8000001012af4000000809448000000404a1500000020250200000010123f40000008090fa0000004040fd00000020204600000010101f40000008080000000004022d500000020107e8000001008374000000804000000000401a9d000000200d1e80000010048400000008015ba000000400a9c00000020054c80000010029e40000008014620000004002dd
|8=>0x60306e80000030083f4000001804128000000c0208c00000060100600000030003740000018000000000008052fd00000040286e80000020123740000010085fa0000008042dd00000040097e8000002000a3400000100051200000080028100000040010080000020003f400000100001a00000080000800000028013e800000140094400000081b43a00000040d21d00000020685e80000010340c400000081957a00000040ca05000000204d0e0000001024090000000812000000000408a35
|9=>0x4000203c00002000002000001000000200000600041fd00002040306e8000102000b4400008081011a0000400844fd00002000940200001000323f40000800111fa0000400088d900002000294080001000143f40000800081fa00004000408c00002000203e80001000100000000800050a20000400000fd00002000004600000800043340000400000ba00002000001000000800687e80000400103f40000200011ea0000100000000000041c247e80000200021f400001000000000000700009c
|10=>0x8008003c80004002121e40002000110300001000052fd00008000213a80004000105e40002000081fa00010000407d00008000201600004000001d400020000004000010000000500005060082e0000282014bf40001410021fa0000a04052dd00005020087e80002800123f40001400081fa0000a00008fd00004040217e80002020103f40001008435fa0000804050fd00004020285e80002000923f40001000481fa00008000d8bd00004000217e80002000109d40001000081f80000800040c5
|11=>0x24000017e80010214203f4000800a090fa00040050485500020028201600010014003f4000800a0005000040050002400020020043e80010010001f400080061000800040010887d00020008400000010004100b000080020800000040010085d00020008000000010000321f40008000100b200040000800100020000217e80010000103f4000800008000000400001028000200000112800100000003400080000000000030000002c00008020000c00004004103f40002002010780001001000fd
|12=>0x80428c07e80040210221940020108101fa0010081048fd00080408047e80040204009340020100181fa00100041481d0008002085568004001031b7400200081157a00100018081000080008243c800400023b1f400200001c1fa00100000c8fd00080000542e8004000029134002000011d9a0010000068fd00080000262680040000123f40020000091b200100000464d00080000207e80040000040600020000001820008000002f900028000643e8001400010bf40009008020ba0004800250fd
|13=>0x6000000000002040000943f410014000a5fa08008000c9bc0400400020fe82002000103f41000c00041fa0800200058fd04001000287e82000800123f40820100081fa04100008ccfd02002040e27e8100100071bf40800800389fa0400080142fd02000000627e8100000011b140800000020480200400000fd01000000207e80400000803f40100000000a00040a08050fd00202040006880080000203340022101081fa0011080040fd00082004627e80041002193f400208001d9fa00104000664d
|14=>0x18400000804fd42080c00207ea1040200103f50020000041fa4010000000fd1400400100fe88002010002f42000000125fa1000000040fd
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x200
|5,0=>0x40000000000000000000000000000000000008000000000000000050000000000340000
|6,0=>0x46800002242800000042ca50a0000000060000004e20000365300e00000ca0000000000000000000000024684424a700000002b832000800076390000000006b0448a002284c6c000000004001b31c0000000003524000080000000000120020000000128003e00028002209068000000000000036000011a971907c0000500013800432f83e00000000000908240002
|6,1=>0x404000000000002100804000280000000880000000000800a1000000009001740000000006c008c800620000000283661000228600b540009
|7,0=>0x9a48001822404b20109127084d6fa44019422130060d4417152db05add3a1957a7c433e0029c5adad6a681a01ad0e2590cc6a56de097dc961409768ce46360f918000a3a249246712470aa37be359148d01a503e034722a7a0a2580002982dba1ae0d7033ae00202cacdea20063cce1f088f35211461085965269000c530f80d0292010b5d90d94000002ec0a1cf2c3
|7,1=>0xd30ddda1fa04b4ce67af032440751d5406c91c5cc408fa990f407126b78008f22801245a0184856153980d9b8ec2dd53059050001f71d724d0b3fb4874926ee0983341c32a4004571f8401497609480589001942413102c440492795804020084cee00000d8079e45800420000046c80013161905b73115129297b2c2a230f0b57e43890081b1ab30aaac430131817aa
|7,2=>0x1818676efd6602001c422001069c267c0019490660086814473080820884c85d30001b036a8d806882540055ac936e200026d86311cb84e672f4c35801270f93a85338026ea801124822f52194db8800359d20a1d0045a360162ccc0100048030f009193ec4250012cda
|8,0=>0xd9e88a2bcde17d07a8883cc7b021485aec99739c2b7618fd24fbb0cc1c9bb3c059d525348d719c9b9a83e9f268cdd2d8bbbbf06e851b8aee8c475a264299792fe74a829c8e0d0579c03dd0f0b5a49de202e207aef3bcc8462fbeb95f5a55fa7574ec508b5d319a531b8ea938bc194c9353fb5346d16ebc34312536732c755517e3b92a3c250230679d9dc69d5f15c304
|8,1=>0x32f305b55d6a10d8ccd7536582e576dd5c57dead37fc0d6b0689bf14a7508c024dc0229ecf5a47a6da874814708046c3abc2fe78566cb2a6bdadb6a4ccc9e7ddfb43ad8dfc758a51ad1416ec22ceca4f3f6c1119d3726429a54e4d429753c6b0e5b74c4377b
|9,0=>0xb57941d5af0debe2f587a2bacfcbd3b565baf08f201e105e3d70f71e3ad456af687629a1afb5d8909c3dc5ab90bb3dcc5a3318c2117b82a6ede9e75
|10,0=>0x1d5ba753b0d61c75
|11,0=>0x29
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 49 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_189 10 roots_189 ops++addP pm 1 dom_146 4 roots_146 ops++addP pm 2 dom_175 9 roots_175 ops++addP pm 3 dom_159 9 roots_159 ops++addP pm 4 dom_187 10 roots_187 ops++addP pm 5 dom_190 9 roots_190 ops++addP pm 6 dom_182 8 roots_182 ops++addP pm 7 dom_183 9 roots_183 ops++addP pm 8 dom_157 8 roots_157 ops++addP pm 9 dom_45 5 roots_45 ops++addP pm 10 dom_179 7 roots_179 ops++addP pm 11 dom_27 5 roots_27 ops++addP pm 12 dzo_45_2 5 roots_45 ops++addP pm 13 dom_151 6 roots_151 ops++addP pm 14 dom_63 8 roots_63 ops++addP pm 15 dzo_27_4 5 roots_27 ops++addP pm 16 dom_171 8 roots_171 ops++addP pm 17 dom_188 7 roots_188 ops++addP pm 18 dom_178 5 roots_178 ops++addP pm 19 dom_155 8 roots_155 ops++addP pm 20 dom_158 6 roots_158 ops++addP pm 21 dom_154 5 roots_154 ops++addP pm 22 dom_143 6 roots_143 ops++addP pm 23 dom_167 6 roots_167 ops++addP pm 24 dom_164 4 roots_164 ops++addP pm 25 dom_180 5 roots_180 ops++addP pm 26 dom_53 4 roots_53 ops++addP pm 27 dom_186 7 roots_186 ops++addP pm 28 dom_59 7 roots_59 ops++addP pm 29 dom_181 7 roots_181 ops++addP pm 30 dom_55 5 roots_55 ops++addP pm 31 dzo_173_2 6 roots_173 ops++addP pm 32 dom_62 5 roots_62 ops++addP pm 33 dom_58 4 roots_58 ops++addP pm 34 dom_174 6 roots_174 ops++addP pm 35 dom_166 5 roots_166 ops++addP pm 36 dzo_155_4 6 roots_155 ops++addP pm 37 dom_163 5 roots_163 ops++addP pm 38 dom_173 8 roots_173 ops++addP pm 39 dom_156 5 roots_156 ops++addP pm 40 dom_60 4 roots_60 ops++addP pm 41 dom_150 5 roots_150 ops++addP pm 42 dzo_59_4 6 roots_59 ops++addP pm 43 dzo_61_2 6 roots_61 ops++addP pm 44 dom_61 7 roots_61 ops++addP pm 45 dzo_189_2 7 roots_189 ops++addP pm 46 dom_170 5 roots_170 ops++addP pm 47 dzo_187_4 7 roots_187 ops++addP pm 48 dom_147 5 roots_147 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_191 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_45_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_27_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_173_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_155_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_zo_59_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_zo_61_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_zo_189_2_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_zo_187_4_27 _ g hchk
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 179 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 51 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 179 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 350 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 94 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 350 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
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
theorem lowS_223:Lower true dom_223 roots_223 goal_223 12:=lower_slice_b [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,64,68)] (by decide +kernel) lowS_219
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,32,36)] (by decide +kernel) lowS_235
def dzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
def gzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00fa00000000
def gsh_215_32:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00fa
theorem lowS_zo_215_32_82:Lower true dzo_215_32 roots_215 gzo_215_32 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_32) [(dom_215,32)] (by decide +kernel) (lower_slice_b (T:=gsh_215_32) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xf000f00000000000f000f00000000000f000f00000000000f000f0,0,4),(0xff00ff0000000000ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_211_32:=0xf000f00000000000f000f00000000000f000f00000000000f000f00000000
def gzo_211_32:=0xf000f00000000000f000f00000000000f000e00000000000e000a00000000
def gsh_211_32:=0xf000f00000000000f000f00000000000f000e00000000000e000a
theorem lowS_zo_211_32_82:Lower true dzo_211_32 roots_211 gzo_211_32 6:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_32) [(dom_211,32)] (by decide +kernel) (lower_slice_b (T:=gsh_211_32) [(0xa000a00000000000a000a00000000000a000a00000000000a000a,0,1),(0xf000f00000000000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
namespace S_247
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(1,129),(2,18),(2,66),(2,130),(3,19),(3,35),(3,67),(3,131),(4,36),(4,68),(4,132),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,23),(7,39),(7,71),(7,135),(16,17),(16,18),(16,80),(16,144),(20,21),(20,22),(20,52),(20,84),(20,148),(32,33),(32,36),(32,160),(34,35),(34,38),(34,50),(34,98),(34,162),(48,49),(48,50),(48,52),(48,112),(48,176),(64,65),(64,66),(64,68),(64,80),(64,192),(96,97),(96,98),(96,100),(96,112),(96,224),(128,129),(128,130),(128,132),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffff
def xsM:=roots_247.map (·&&&dom_247)
def gM:=goal_247&&&dom_247
def NN:Nat→Nat
|5=>12
|6=>69
|7=>201
|8=>215
|9=>74
|10=>11
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xf3012eec6cd7667d41a2d0593bd31285a21813418109e659966093d52715
|6,0=>0xffcbcfea13fe62efc0adfa777f4d30f2165efac4ef789ef393ed14aebeefebb7ae9fcde953bdf5f3d4119cb176bfc27be0f6bc151b84b6b48a7b402cae2fdaa6eeaa678a839ba2da0a16269ffe99bc5493daf8f07c8bc81840a3804947c43b724b2715316dd7e6d9226d21369d3566a01653b25efd95d84b5d3ef5d0b45bb805b20c5a6a1594a551ebf512a64e72d4a4803ed1632b2f1c3bf1c1671a3e9105130efa509411069ed04a88027cb
|7,0=>0x9a1eb98cd89834097d3397c7c97b4193bfa92c6391c2391b8191acc8f07c8e6138d9888859e880ae87938872358631485d9684c178473c842098299b82039818c380c14808fd805b57f0b17da167c87f7c7db7b6c776c1c750fe749c47265c715f2711816e15b6cdec6bedf6a83068c1568b55683b767e1a66b6c647a863d38634b360ff55a2fd5a2b359867597ae57d5d57cbe5754154a5e541545278f5209251ebf518fb515274dcec4d8064c71a4abff49ed647da94620a45b414544743b824119a400043f3d23e3c03e0db3b8623a262374cd3712736ebd354f734ee733ae030b152ed162d71a2c32e2b1242a18528ee52866d26bb02698a262b92490c2434b2302a22375210e21b43b18e711825a16d961678f142c513a5412e7a0f2330d5d90d5ca0ab290a22c0896d07887069ed062fd0422403cc703ab2034f200830
|7,1=>0xff670fe62efe5b4fd707fbc6ef9da2f94e5f7d1cf64baf640df558bf3ea4f3e7bf3470f2067f1491f0f0def177eec17ee864edfdcec60ceb41cead01ea2eae6e64e4694e3fd0e2c09e0bfde03c1dfa62df347dce16dc0a5d80e4d6479d61cfd5e95d5dd8d48afd4026d3c8ecfc91ce2e1cde01cc7d5cae31c8dfbc7f29c7c28c51ecbf9bdba31ab8c03b88c8b857cb6f78b6289b4cb9b43c2b26ccb267aadb44aa678a723fa347f9ffe99f0b59e11d9c7a49c2a49bf71
|8,0=>0x9bdf09b8189a1eb97f539780796f409591494d5b93574934be911f38ff548fb0b8f07c8c91d8c769899d9887e687ab785d96845608345982e26808fd800b77fcee7a8d678cb5785dd7792e7359972e7271fa371a95711816e51b6dcea6d6506d40568ded6725c640ad63c8462da560e72607ea5e5bd5c8825c66c5ad625a5e859c565829c57d5d55da65593e51b4e5148a4eb444d87b4c6a549c6148c98481f047a42475f545f3e429c4419cd40bf03d6153d60b3c8fc3c85b3bb823a2c039ebf390d637839367e63658b34df53396f31b1a317c430f8630b152fcab2ed802d42f2c7802a7fa2a29b2a24f2a134247852343c22569216a120dfd203f01fbff1f56b1ec511d69b1b1d119b33191fb17f4616c3913e8313bb111f8c0fe6f0e5b10dd010c9180ab290a5ef09b9409143076a1048eb03945036ac019ec0106d001d7
|8,1=>0xff0ddfe963fd707fc864fb0aaf9539f911bf68d3f638af60a2f5e70f4515f3547f2ebff13b8f0315edfdceda4bed1d4ec56bebf80eb970eb96fead01eab95e9752e8b2be832ce5acce539de49e9e1a1be1004dfa1dde15eddcf6dc582daf8fd7917d6718d6087d5e95d4026d317ed2f2bd0fedcfe20ceec0ce00ecd6e0cd50dcce06cad7cc9ab1c996fc5d42c5bbec3f3ac3673c365bc2ee1c0e5bbf54cbe98dbc809bc655bc46fbc34ebabd3ba242b82b6b5253b3ec6b3452b2607ad7d3ad481ad10faa921a9ec7a9500a8486a6413a619ba4a28a35f2a0648
|9,0=>0xf5a94f5a42f49fdf2e8ce9229e39e1e1a1be031adb0c8d8de6d6743d18a2cde25cdb14ccf5dc6b3ac2d7bc1903bed16bbffeb68eeb31d4b2322b18edaf571ab878a7987a63bba3d7c93ea090afe8c79a896fc88c43888448794985d9685c8e8218f7de4c7b98c744ac7311c715e1707c66f2da6713a641cf5d0ec5c631596df5754f55a5c51b184f4c848c3545a6d403353ab7b34a6b30b15300542e7732592e22d9518eb617c83179111294611ab40f5380e78e02040019af
|10,0=>0xff591fd8d6f9dd7c7335c7110b47c39ac02931bf7fd216aad4343e9
|11,0=>0x3ef7d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000003300000033000000330000003300000033000000330033000000330000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00aa00aa00aa00aaff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00cc00cc00cc00cc0f000f000f000f000f000f000f000f000f000f000f000f000f000f00000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff000000000000ff000000ff000000ff000000ff000000ff000000ff00ff000000ff0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa
|0,1=>0xf000f0000000f000f000f0000000f000f000f0000000f000f000f00000000ff00ff00ff00ff00ff00ff0000000000ff000000ff000000ff000000000000000000000000000000000000ff00ff000000ff000000ff0000000000000000000000000000000000000000000000000000000000000000ff000000ff000000000f0000000f0000000f0000000f0000000f0000000f000f000f00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff0000000000000f000f00030003000f000f00030003000f000f00030003000f000f00030000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000000000000000003300330033003300000000000000000033000000330000000033000000330000003300000033000000330000003300000000000000000000000000000000ff00ff00ff00ff000000000000000000ff000000ff00000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000ff00f000ff00f000ff00f000ff00f000ff00f000ff00f000f000f000f000f033003300330033003300330033003300330033003300330033000000330000
|0,2=>0xff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0000f000f000ff00f000f000f000ff00f000f000f000ff00f000f000f000ff00f0ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff000000ff0000ff00ff00ff00ff00ff00ff00000000000000000000000000ff00000000000055005500110011005500550011001100550055001100110055005500110000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff0000000000000000ff00000000000000ff000000000000000000ff000000ff0000ff000000ff000000ff00000000000000ff000000ff000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff00ff00000000330033003300330033003300330033003300330033003300330033003300000000ff000000ff000000ff000000ff000000ff0000000000ff00ff00ff000055005500550055005500550055005500550055005500550055005500550000ff000000ff000000ff000000ff000000ff000000ff00000000000000000000
|0,3=>0xff00ff00ff00ff000000000000000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000ff00f000ff00f000f000f000f000f000ff00f000ff00f000f000f000ff00f0ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff000000000000ff00ff0000000000ff00ff0000000000ff00ff00000000000000000000000000000000ff000000ff00ff000000000000000000ff000000ff00000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff00000000ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff000000ff00ff00000000ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff000000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff00000000ff000000ff00000000000000ff000000ff000000ff000000000000000000000000000000000000000000000000ff00ff00ff00ff000000ff000000000000ff000000ff000000ff000000ff000000000000000000ff000000ff0000ff000000ff000000ff000000ff000000ff000000ff000000ff000000000000
|0,4=>0xff000000ff000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff000000000000ff00000000000000ff00ff0000000000ff00000000000000ff0000ff000000ff000000ff00000000000000ff000000ff000000ff000000000000ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff0000ff00000000000000ff00000000000000ff00000000000000ff000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00000000000000ff000000ff00000000000000000000ff00ff00ff0000000000000000000000ff00ff00ff0000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000ff00ff00ff00ff00000000000000ff00ff000000ff0000000000000000000000000000330033000000000033003300000000003300330000000000330000000000000000000000000000000000000000ff000000ff000000ff000000000000ff000000ff000000ff000000ff000000ff000000ff00ff00ff00000000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff000000000000ff00000000000000ff00000000000000ff00000000000000ff0000ff000000ff0000000000000000000000ff000000ff00000000000000ff0000
|0,5=>0xff00ff0000000000ff00ff0000000000ff00ff00ff000000ff0000ff000000ff000000ff000000ff000000ff00000000000000ff0000000000000000ff000000ff000000ff00ff00ff000000ff000000ff0000000000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff00000000ff000000ff000000ff000000ff00ff00ff000000ff000000000000000000000000ff000000ff000000ff00000000000000ff000000ff00ff00ff000000000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000000000000000000000000000ff000000ff0000000000000000000000ff000000000000ff00000000000000ff00000000000000ff0000000000ff00ff00000000ff00ff00ff00ff000000ff0000000000ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff000000000000ff00ff00ff00ff00ff00000000000000ff00ff00ff00ff00ff000000ff000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000
|0,6=>0xff000000ff000000ff000000ff000000ff00000000000000ff00000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00ff0000ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00000000000000000000ff000000ff000000ff00ff0000000000ff000000ff000000ff00ff0000ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff00000000ff00ff0033003300ff00ff0033003300ff00ff0033003300ff00ff00330000ff00ff00ff00ff0000000000ff000000ff00ff00ff00ff0000000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00000000000000000000ff00ff0000000000ff00000000000000ff00ff0000000000ff0000000000000000000000000000000000000000000000000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00ff00ff00000000000000000000ff000000ff0000000000000000000000ff000000ff0000ff00ff00ff00ff000000ff000000ff00ff00ff00ff0000000000ff00000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000000000000000
|0,7=>0xff00000000000000ff0000f000f000f000f000f000f000f000f000f000f000ff00f000f000f000ff00f0000000000000ff00000000000000ff00000000000000ff0000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00ff0000000000000000000000000000ff000000000000000000000000000000ff0000f000f000f000f000f000f000ff00f000f000f000f000f000f000f000ff00f0ff00ff00ff00ff000000ff000000ff00ff00ff00000000000000ff000000000000000000000000000000000000000000000000ff00ff0000000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff0000ff00ff00ff00ff000000ff000000ff00ff000000ff00000000000000000000ff00ff00ff00ff00ff00ff00000000000000ff000000ff000000ff00000000ff00ff0000000000ff00ff00ff000000ff00ff0000000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00000000000000ff000000000000000000000000000000000000ff000000ff000000ff000000ff000000000000ff00ff0000000000ff00ff00000000000000000000000000ff0000
|0,8=>0xff00ff00ff000000ff00ff00ff0000ff00ff0000000000ff00ff0000000000ff00ff00ff000000ff00ff00ff00000000000000000000ff00ff00000000000000000000000000ff00ff0000000000000000000000000000000000000000ff00ff00ff00ff00ff000000ff0000ff00ff0000000000ff00ff0000000000ff00ff00ff00ff00ff00ff00ff0000000000000000000000000000ff00ff00000000000000000000000000ff0000ff00ff00ff00ff00ff000000ff000000ff00ff0000000000ff000000000000ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff0000000000ff0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000ff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x517020100161d05041c020100120a1701001b0e060a0f19020100160a170010180e06051702001016060a0c02001514060a1302001012060a0f0800070e0a09010b070605040c020800050c11001006050c020b1006050302001006050c02000d060a0f010b070e050302000d0605040c02010b0a0908000706050403020100
|1=>0x60a0c02000d0e06270a0f0208000e0a0302000d0e060a0f260201000e1a0a0f0208000e0a0901000720061a0a091101000605241702010016050a0f02080016050a03020100061a0a0902010b060a170200230e06220a0f0201000e0a170221100e060a17010b070e06050c02001020060a0f01001f160e05041702080016
|2=>0x60504171101001605041702010b160a1701002c0e060a0f2b00100e060a090f010007160a030200100e060a1701001f0e060a0f01001f0e060a17020100161d0a170200100e060a170010070e06050c11010006050c02010b06051729020100160a170228100e06050a0c11010006050f02080016050a0c02010b0605030201
|3=>0xf02010b0e050c020800060a0f0100070e201a0a0f1101000e05170201003216050a0f11010016050417020010161a0a0f02010b0e050f3102010016050a0f02010b16050a0c0208000605040c020100201a0a09020800060a092f020100162d0f020100160a170800070e060a0c1100100e060a0c020b100e06050c03020100
|4=>0x173d01000e060a173a0201001606390a0f1702010016050f171e020100160a170201000e3306051702001016060a1701002c160e06050a172a020100160a0f02010037160e360a0f0201000e060a0f0201000e33060a0f30020100160e050f110100160a0902001514060a170201210e06050f02010b160a1700102c0e06270a
|5=>0xa09170200101506420a090f0201000e050a1702080016060a0c0200100e2006050a1c0201001206050f1702010045160a172f020100160e0504170201001620420a09170201001605172a02010016270a090f020100160a44170201000e06420a0f170201000e0a0f020010410e06050f1702010016121a0a090f020100160a
|6=>0x4e0e060a0f0200100e140605172f02010016051702080016064c0a170201001606051c02010012060a17020010340e060a170201000e1206420a0c170201000e0a170100070e12060a0c1702001015060a174a020100160e0a0f170201210e060a170200100e3b060a0f0201000e47060a17020010460e061a0a170208000e06
|7=>0xb1606050c1702001016060a090200100e14060a090f0201003416480a170200100e0605175202010016060a51170201001606480a0f0200100e060a0c170201210e06420a17020100160e0a170200101516060a090f020100163b0a09170201210e06480a0f13020100160a17020010500e060a170200100e14064f17020100
|8=>0x6270a0f0201000e20480a090f020100161a0a0f0201000e200a17020121160e060a1c020100370e0605170201005616064f0a170201000e06050a0f0201001620531702010016060a171e020100160a171c0100070e060a0c0200100e14060a0f020800160e0a170200230e060a0911010016060a030201000e060a090201
|9=>0x50f170201005b0e0a0f1302010016120517020100165a060a0f310201000e0a090201003716060a17020100370e060a093002010016060a0f020100370e060a09170100071606050f02010016204f0a090201000e060a591702010016060a0c1101000e06050f170201005816570a0f020100160e0a0c02010b0e060a090208
|10=>0x16060517020100165d060a0c170201000e060a0c300201000e060a0f02010b0e390a090f020100060a0c170100070e060a09020100370e060a091713020010060a170200100e12060a3c170201000e060a0f171e020100162e0a0f020100160e0a0f170200230e060a0f0200100e120605170201005c160659170201001606
|11=>0xc170200230e060a0c030201000e060a090f02010016122d170201000e060a0c0200100e120605251702010016060a09170200230e062e0f020100160e0a1701001f0e12060a090200100e12060a170200100e06390a0c17020100060504170201001612390a0917020100060a0c020100370e060a0c1713020010062d170201
|12=>0x10016050a1711010016061a0a1702010b0e060504171c020100160a130201001206050a1702010b16060a17020023160e060a1701002c0e060a0f020100610e06390a1702010016060a1701001f0e060a0c0f2b01000e060a0f0201000e600a171302001016064c0a0f17020100160a175f0201000e06380a170201000e060a
|13=>0x6570a170201000e06690a170200100e06570a0f0201000e060a0f31020100160e0a0f0201006816050a0f02010016120517670201001606051711010016060a0f660201000e061a0a090201002006051702010b16060a0902080016060a0f02010065160a170100070e20061a0a171101000e06630a17020100160e430a0f02
|14=>0x380a170200100e06430a0f17020100160a0f020100160e6c0a0f110100160e05040c1702010016430a170200100e060a0f02010b160e0a0f170201005816050f020100161205171e02010016050a0c02010020060a171902010016060a0c0208000e060a0f1701002c0e060a0c170200100e060201006b0e060a09170201006a
|15=>0xa090f020100161a0a170200100e060a0f0208000e051702010045166d0a170201001606050a1702001016060a091302010012060a0902010b060a0c1701002c0e0605591702010016060a0f2b0100160e050c02010020060a0f170201005b0e0a17020100500e060a17020100165a060a091701002c0e060a17020010160e06
|16=>0x20100410e060a0917020100163b060a1702010072160e6d0a170201000e060a17020100700e061a17020100580e060a0c0f170200100e0605170201005816060a170201006a0e06270a170200100e060a170201210e060a0f17010007160e050c1702010016060a1701001f160e060a0f020100160e600a0c13020100120643
|17=>0x50f17020100160a17020800160e060a0f17020100500e060a1c0201000e1206480a17130201000e060a0c09170200100e060a0f17020100350e06480a0f130201000e06485e0201000e0605170201005b0e06740a0f0201000e06483e09170201000e0605172f0201000e06050a0f1702010016730a172a0201000e060a0c0f
|18=>0x500e060a090f13020100060a0f0201000e12060a0c17020100340e06434d0201000e060a171e0201000e06480a091702010016060a0917020100340e061a0a170201000e20060a17020100750e06630a170201000e06050a170201001620060a090f020100340e060a0c170201000e3b06430a710201000e0654170201000e06
|19=>0xf0201000e060a170100070e06493e170201000e060a0917020100550e060a17020100770e060a0c171302010006480a090f0201000e060a0f0201000e76060a0c17020100500e0605170201001620060a0c17020010160e060a091713020100060a090201001612060a170201000e1206570a17020100160e060a0917020100
|20=>0x60a0f020100160e200a1702010b0e060a171302010016060a1702010050160e060a6e1702010016062e0a17020100160e060a0c0201000e1206640a17020100160e064c0a170201000e060a17020100450e060a090201000e1206480a0c170201000e060a17020100790e06050f17020100580e060a17020100780e06480a0c
|21=>0x6433e170201000e06490a0f0201000e060a09170201001612060a0902010020060a174b0201000e063e17020100580e060a0f170201000e12062e17020100160e067c0a17020100160e060a0f02010041160e0a0f2b01000e064f0a170201000e060a0f171e0201000e060a177a01000e060a170201000e6c060a171101000e
|22=>0xe060a170201005816060a0c091713020100060a0c170201000e12060a0c0f0201000e1206020100587b0e06270a0f17020100160e4c0a0f170201000e060a17020100370e060a0f17020100450e060a17300201000e060a170201000e7d0605174d02010016061a0a0f17020100160e0a170201000e60064c0a17130201000e
|23=>0x800e060a177e01000e060a0f020100650e060a170200100e06480a0f020100160e430a0f0201000e060a09170201006f0e060a0c090201000e12060a170201005b0e060a0c170201000e060a172f0201000e060a17020100651606490517020100060a3c170201000e06430a170201001606483f170201000e06541702010016
|24=>0x1702010034160e0a090f02010016433e09170201000e060a0f020100680e06270a0f620201000e06050417020100160a0f17020100160e3b380a170201000e061a0a170201000e12060a17010007160e060a17020100681606050a170201001612060a1702010077160e06484d0201000e060a0c171302010016060a17020100
|25=>0x2006050a171c02010016060a0f170200100e060a174b020100160e060a172b0100160e060a0f17020100580e06390a170201000e060a0f17130201001605171e0201000e060a17020100160e6c060a17820201000e060a17110100160e060517020100750e060a17020100810e060a1702010b160e0605170201001612060a0f
|26=>0x37160e060517020100450e060a17020100830e060a1730020100160e06380a0f170201000e06570a170201000e120605170100070e06051702010068060a0f020100160e120a17020100160e6006430a091702010016060a170208000e061a0a171c0201000e06480a0f17020100160e430a0f170201000e060a0902010016
|27=>0x3c17020100160e06380a09170201000e06430a0c170201000e061a0a091702010016060a090f17020100160a0c170200100e06570a170201000e06840a170201000e060a0c0201000e200605170201006f0e060a09170200100e0605171c0201001606053f1702010006270a17130201000e06430a090f0201000e060a170201
|28=>0xe06640a170201000e06480a170201000e12060a17020010160e06050a0c1702010016060a17020100400e060a17190201000e060a17020100350e06743e170201000e06730a170201000e0605172b01000e060a0c17020100160e06380a0c170201000e06390a0f170201000e06050f171e0201000e0605177a01000e060a
|29=>0x370e060a17020100550e06050f17020100450e06270a0c170201000e060517300201000e06380a17020100160e0602010058410e060a0f17020100160e120a0f0201000e200a171c0201000e3b06270a09170201000e060a17020100500e06420a09170201000e061a0a0c170201000e062e0a170201000e06270a090f0201
|30=>0x60a1702010041160e064305170201000e060a17020100160e20060a170201007f0e06740a170201000e060517020100580e060a0f17020100340e060a09710201000e061a0a17020100160e060a0f17020100160e2e170201000e067c0a170201000e06050c17020100160605175e0201000e060a172a020100160e05170201
|31=>0x201000e060a172b01000e060a6e170201000e060a171c0201000e06480a17020100160e068617710201000e060517020100410e060a170201006f0e060a170201007b0e063e0a09170201000e06480a09170201000e060a17020100160e3b060a170201000e12060a0f620201000e061a05170201000e06480a0f170201000e
|32=>0x580e060a0f17130201000e06480a710201000e06053e170201000e060a0c170201000e060517710201000e064805170201000e0605174d0201000e060a090f0201000e060a175e0201000e06050a17710201000e060504170201000e060a17020100720e060a09170201001606490a170201000e060a172a0201000e060a1713
|33=>0xa85170201000e06860f170201000e060a170201000e2006051702010016060a171c020100160e060a3f170201000e060a0c0f170201000e06270a170201000e060a090f170201000e060a17020100680e061a0a170201000e06050a1702010016060a17020100650e06430a170201000e060a17020100160e12060a17020100
|34=>0xe063e0a17620201000e06050f170201000e06040a170201000e060a17020100340e060a0c17020100160e06050a0f170201000e06270a0f170201000e060a170201000e3b06880a170201000e06430a09170201000e0605170201007b0e06870a170201000e06483e170201000e060a0c09170201000e060a0f020100410e06
|35=>0xa170201000e063e0a170201000e060a17710201000e06480a170201000e0605170201000e060a17020100410e06050a170201000e060a17020100160e0686170201000e060a09170201000e060a0f170201000e060a17620201000e060a174d0201000e06480a0f020100
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x21300f1806cc030601530091803cc018600930031800cc0006
|6,0=>0xfdb87d583dce1e770f038765c3a4e1cb70e2386f5c36ce1af70d438685c336c19470c6b8619c2fee17870b8b85a9c2c6e15c70aab8539c28ee140709cb84c9c258c126608fb8461c222e10b6082383f981eee0f07074b8389c1b6e0d47066b8319c17ee0b87058b82a9c146e09c704ab8239c10ee080703cb81c9c0d6e064702eb8159c09ee0487
|6,1=>0x21d610b3883dc412c2027
|7,0=>0x2093902dc808e3fd71fac0fb607cb03dd81eac0f36078b03bd81dac0eb6074b039d81cac0e36070b037d81bac0db9c6cee35f81ac38d4206910340819c40cc206510320818c40c4206110300817c40bc205d102e0816c40b42059102c0815c40ac5c55302a1814cc0a4605130281813d389ca04d50262812d4094dc4970243811dc08ce045702238
|7,1=>0x300c17e60be305e982f13976a0ba505ca82e1b96ee0b6705ac72d2416720b29058c82c2415f5caeb056d82b2c157d8aaf054f82a3c14fe0a6f052f8293c147e0a2f050f8283c1401c9f104f0827441385c9b304d18264c1306097304b272554128a0936e4938245c1211c8fcc47682374119a08bd045682274111a087d04377218390a2084104197
|7,2=>0x3f5b1f91cfb907d483e641f198f7d07b683d7b9ea1cf41079883c841e220f01077883b841da20ec2e75983a8c1d29ce85073b739a39cb20e49071d738ac1c360e0ec6ff837bc1bbe0dcf06df836c39b420d9106c1735cc1ac60d54e6a3734e39a520d190684833eb99d60cdb0665832f3995a0c9d0647731fc18de0c60e6288310b98660c2306098
|7,3=>0x8308414ba086103308118404c20060ff307f18
|8,0=>0x523428f6546b0a2d8512c287254290a0b9501c27ea53e6e9eb84f14a76a13a509c994e0c26e2536109a794cfc265e131f098694beca5d612db096494aeba55612992943949d4a4ca12550921948c4a43e520f0900747cba3c611d128e0846bca33a518b28bc945aba2b6114b089c944a422321107287a9438ca1a610c308598428c2122508108388
|8,1=>0x628bb12258810c379617c309e183d2c1596073b01657fb0bf675f742f9dd7bf0bd785e74af16577b0bb585d6c2e96173ceb9685c742e1a16fd0b7685b6cad9256b72b5475a5cad0a56750b319594c2c8616330b10958442bfe55ef0aef85734ab7dd5af0acf85634aafa156b2aad85533aa7a152b2a8e7543429fdd4ef0a7075344297e54af0a4e9
|8,2=>0x7324396e5ca70e4b8721c38ee1c670e2c7711cb86a5c232e089700bb7e25bdf2de696eecb7561b9b0dc586dec36d61b5b0da586cec3659db1b2d8496bdcb5ce1ad70d6296accb5425a92ed42769d434c65a512d21768c4b43e5a0d2cfe867acb3b619c92cdc8669cb32e19870cbb86594b2aa19450c9a86494322a19050c7996393b1a658c30c589
|8,3=>0x3c91de390f14878643c121df90ef48775cbb8a5db50ed197653bb065d74eeb197544ba821d2f2e8e9743439f65ceb0e6c9
|9,0=>0x899444a6624311198888c4422620110f88878443a221c2f0d898684431e617f10b698574429a213d109688474421660fb107498364419220b91054882644112207910348815cc08e203710138805c400e1ff70ff477f643f921fb72fd387e5c3f0e1f770fb297d4cbe825f310f9087c443dfe5eed2f6e87b2cbd761eab0f4d87a24bcf21e672f2b8
|9,1=>0x230d117e88bacc5b622cb115d88aa4c52e6285313a8
|10,0=>0x477223a911cc88e2bc6f6236b11ad88d33c67a232d118e8
|11,0=>0x11e47
|_,_=>0
def wAt:=mkWire dB 137 248 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x12045c581706428390e0642839002045c591716030831716428391716038191020c5c580c01c5c59012045c580e0645c190301c70491716c5c5a012042859170645c580e0645c581a02c28590a1645c3917160381925064144b0a0e45c5a012045c191716038191c12428391716c5c5a002045c58170e428590e0645c5a1e168143c170645c191a0905c390a1643819
|1=>0x170642859171603819002042859170645c580e0643c83171605c19002045c191716038190a0e45c59012045c580a1640481170e45c580e064c0191a1705c390e0645c192e0e428811716038190c01c0081171645c580c20c5c590a0e45c580e0645c191a02c5c390a16430831716030071716428391716408811716038190a0e40081171645c580e06414a80a0e45c5b
|2=>0xe0645c1902404fc5e3e0ec28193c0ec5ced0a1683819270ec283d17064143c1706428390e0645cd6340e45c190a0e430071716438193802c2831171645c5b1a17c28590e0645cd6340e4283e170645c191a17028590e0640881171605c190a0e43819171083007090640081171605c190a0e43819002045c580e0645c19012045c590a0e45c580e0645c581a02c2859
|3=>0xe064e0030a0c43c39490f9203b0a17430070f0e45c190a1640481171603819100ec2419170e50c1b0a0945c390120428391716038191716030071716428391716c5c5a17064c0191a17028590e0645c580506c28390e0650c1b0a0945c390a0e470191716c38190e0645c390a0f45c191a20c28591716038194306c2825170e45c191706428391716838190a1645c39
|4=>0xf0e45c19050c05c590a0e438194b0e45cef0a16838190a17430070f0e45c193800c28310f0e45c193806c2831171643819100ec3007171643819170645c390a16838193800d0c190a0943c3b0a174fc5d3e0ec5c420c01c3c391706534190517028390e0642839012045c580e06428391716c5c5a0e064e01b0a0c43c3917064403b0c01c3c39170652c19173bc285a
|5=>0x17064285d170e43819170642859170645c580e064e0030a0c45c5917554f827170e45c190a0e45c580e06550390a20c5c580e064143c0a0e43819170645c420c01c3c39170640481170645c580e064e0070a0c43c39170640881170e45c580e06470491716c5c5a0e0640081170e45c580e06428390c01c5c590e0645c420c01c2419170e45c390a0f83819170643007
|6=>0x1716c28390e06414830a0e45c580e0645c1958064145f0a0e45c5a17065605a0517c28390f20c5c580e0645c191a17c28590e064685c170e438193817c28310f0e45c191a02c5c390a1645c581706428390e0645d553e09c5c390a06414830a0e45c581716408811716038190517c5c190a0e43819171680081171645c580e0645c39012045c580e0645c580a0f43819
|7=>0x380ec28310f0e45c190506c2839171689c3b3e1745c390a064e05f0a0c43c391706430070c0ec3c3917064b8390a2045c580e065345a051712c59173bc285a0e0645c19002045c580e0649c3b0a0f45c1917164680b0a16438193817d0c190a0945c390c01c303b090645c39050f028390e0645c190a2045c191716038193801c28310f0e4305f0c01c3c39170641473
|8=>0x170ece03b0a0c45c590e0655c0b0a1245c5a0e0643c391706409050a1785c1948160285d0e064303b0c01c5c590e0643c3b0a0c45c491716838190a0c43c39170643083171645c580e0645c5a170e438191706428655e0e4f85c0a0643007171245c5a0e064144b0a0e45c5a0e064e0074306428250a2045c191716038190c01c305f090645c390c01c5c49171683819
|9=>0xe0645c5a0a0e408810a0e45c580e0645c58170e428590e06400810a0e45c580e0640481170e45c580e0642826170e43819170645c581a02c28590e064285917160381964065205b0a1743819170642825170e438190220428391716038190a16400811716038191716c305f0c0ec3c391706400810a0e45c580e064e0070a0c45c593802c28310f0e45c192762c283d
|10=>0xa1780881170645c580e0645c590506c28390e0640081170645c580e06438190517c5c190a0e45c190a0e45c5a0e064143c1706428390e0645c590a0e45c581a0905c390a16438191716404811716038193802c28310f0e45c49171683819434dc145c051742839550e4f827170e428190a12458831716038190a10430070f0e45c190f20c5c19171605c19410e4285e
|11=>0x171643819170640481171603819050fc5c190a0e438190a6e470391716c38190a0e430071716438190c17c303b090645c39002045c391716038193802c28310f0e45c190520c2839171603819024145c190a178381917164283917160381958064145f17064283958168145f0a0e4e00b4306428250c01c5c491716830070a0c43c39170645c190a0945c390e065045a
|12=>0xa06534190517028390a0e43819170658819170ec3c390a1785c19170e4285a0e06504190a17838190a6e5c4391706c28aa620645c3b05064145f0a0e430070f0e45c190517c28390e065bc393e17c28193800c28310f0e45c1917064680b0a1645c490a0e45c5a0e0655c0b0a1245c5a1706520580a17438190c17c303b0f0e45c190e0645c190a0945c390a1643007
|13=>0x170e4285d0a0f85c391706428591716038190571c5c1b0a0e52419480ec285d0a0e45c580e0645c390a0f85c1917164285a0e06428251706c5c390a20c5c580e0645c190a0e43819012045c580e06428320f0e45c191716c5c5a0e0643c3b0a1745c190c01c2419170e4d0390a0f85c190f0ec285d17064f85c0a174281958064145f0a0e42989170645c3b170e4285d
|14=>0xf0e4285d17064680b050642839480ec285d0a064f827170e4281941164285e0e064303b0f0e45c19170e4285d170643d8b170645c3b0a0c83c391706428391716038190c01c5c590e064303b090645c39170e45c5a0e06458831716038190a1245c5a0e0642832090645c39170e43c3b17064305f0f0e45c190f0e4283e17064145c051742839050f05c190a0e43819
|15=>0xe0645c1902414285e3f174f83b0a064143c170642839027b4145e0a0e5045a0a1783819022045c580e0645c19171603819002045c580e064303b1716438190a0c85c590e06470391716c38190a2045c580e0645c491716838194816c285d0e064284d0f0ec5c19050fc5c190a0e4305f090645c390a1743c3917064f98b0a0645c3b17064145f0a0e4f826170e42819
|16=>0xc17c3c3917064145f0517828390a0f4381917064284d0f0ec5c191a17c14190a0e4143f1706428391a17014190a0e4284a1716838190517028390e06428590e0645c1948160285d0e0643c3b170642825170e42819480ec285d170645c39171683819170e45c580e0645cef0a16838190517c28190a0e4305f0f0e45c190a2045c580e06428711716c381917064285e
|17=>0xa0e4303b1716438197f0e4f85e0a06409fd3e1782819170642826170e430070f0e45c190e064285d170642825170e45c193e17c5c390a064305f090645c3958064145f0a0e45c491716838194d064145c0a0e438190a0985c39480ec285d0a0e45ced0a16838190a0945c390e064f83b0a17428190a20c5c580e06438190517c28390c0ec2419170e45c49171683819
|18=>0xa0e45c1941168285e0e064f824170e42819022045c580e06415c71706c2839650642826170e400811716038190a0e45c5a0e064283e0e0645c19170e438191706428190a0945c391706504390a178283d170645c3b0506c28390e0645c190a16838190a0c43c391706428591716838191a02c28590e06504390a17838190a0e45c5a0e06504590a178381905170285d
|19=>0xa1383c3b17064685c0a16438190a0c43c391706428491716838191a02c14190a0e5ec39051782839170645c5a0e06520580a17438190e0642825170e404811716038191716c28590e06438190a1745c190a0945c39170645c391716038190a0e45c5b0e06430070f0e45c19173bc285a0e06409050a17838190517c5c190a0e49c3b0a0f45c190f0ec381917064143c
|20=>0x1716838190a0c43c39170649c3b0a0f45c19050f028391706409ed051782839173b4285a0e0650c190a0945c39090642825170e45c390a1643819170e438191706430070f0e45c190a1245c5a0e0642a150906c5c39171645c580e064f85f0a06428390c01c2419170e45c5b0a0e438193e0ec28190a0e43c3b170645c190a0945c391a17c28590e064143f0a0e45c19
|21=>0x17064685c0506428390a0c45c590e064285e0517c2839170645c5a0e0645c580e0645c193e1745c390a06428320f0e45c194306c2825170e45c590a16438190a2045c580e0645c390a0f45c194816c285d0e0645c5a0e06430071716438190a0e45c590e064fc5e3e0ec28195e0e4f85c0a064d0390a0f85c190a6242819170ecf9890a0645c3b02414285e0a0e45c49
|22=>0x3e17c2819051782839170e42819170e4285d0a1683819171683819170645c3b0506428390a1745c190a17838190517428391716038193e17828190a6245c3b0517c28390a0f85c191706c5c390a16438190e0645c190a2045c580e06428711716c38191716428390e064f85c0a06428391c0645c5b0e064685f0506428393e09c5c390a064143f0a0e45c190f0e4283d
|23=>0xf0e45c190a0f45c19170e45c19410e4285e0506428390e06428390a0985c390517428391716838190517c28390f0ec5c191706c285d0a06428390f0e45c191706c28390a1742839051702839170e45c193e17028191706c28390506c283941064285e170e43819480ec285d620645c3b0f0ec5c1902414285e710e45c1b1716c38190a17438191706c283b0a1782839
|24=>0x28191706c285d0a0e4285e0a0e438190a0ec5c39170645c3b0517028390a1745c190a0645c3b0a0e45c190506c28390a0f85c191716438191706428390a0f45c190a16838194806c285d0a0945c390517828390a7145c1b0a1742819090645c390a1785c190906c5c390a0ec5c191716038190a0e438191716c38193e0ec2819
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x110820d440187c40000000000007750e861c1036200000cea18d02f28000000016902aa800000000000000051409a8000000000000000000024284350806000000003b506e80c9417202a404c8000010a81e30348059009200e4012a0000000000000000000040800000a600000000005000000000000000
|6,1=>0x945122600004628000
|7,0=>0x2b285550a8a14d429285150a0a13e327484d9099212e42548499091211f323a4000000011b222e844d087a0000216800000001074000040d07fa0fc300003e4c7b18f241de63b0c7420e531c4638446ea0d941ac634906720ca418c800006120be417482d905998af415862a105298a41142600004ea0994
|7,1=>0x44c888cd0fa21b442e884d107a20c34108000102220043f887e4cfaa1f143da87a50f391e34000077d0ee19d843a887410000000039887210e299c1437a86e50daa1b3236066b10d49800034c66890cf999b432e8650cc8218c4316261d0c1a17f42f685dd0ba1800000005c4cb6a16942ca80000b0a15d4
|7,2=>0x5f48bd917922ee45d48b9917122de45b48b591692000059e6b30d649ac545828afc95da2b740000acd157a2ab454e8a90d50229c45326a58d49228e45148a19000028334fe89f48000279400009d5138a26d44d289951311a5e44b489591292251149a89251231a42447e68ed11ba233445e88ad11508000
|7,3=>0x6308c54d88a30e36148c1918122fe4
|8,0=>0x7b06f54de91bcf37986f24de31bc337806ef4ddd1bb737686ec4dd71bab37506e94dd11b9f37386e64dcb1b9337206e34dc51b8737086e04dbf1b7b36f06dd4db91b6f36d86da4db31b6336c06d74dad1b5736a86d44da71b4b36906d14da11b3f36786ce4d9b933436626cb8d959b28364a6c88d8f9b1c3
|8,1=>0x92e7250e489c8e39167220e429c8238fe71f0e3c9c7638e671c0e369c6a38ce7190e309c5e38b67160e2a9c52389e7130e249c4638867100e1e9c3a386e70d0e189c2e385670a0e129c22383e7074a0d1c1738287044e071c0b38107014e011bff37f86fe4dfb1bf337e06fb4df51be737c86f84def1bdb3
|8,2=>0xaac754cea81d4d3a94751cea21d413a7c74ece9c1d353a6474bce961d293a4c748ce901d1d3a34745ce8a1d113a1c742ce8495063a067400e7e9cfa39ee73d0e789cee39d673a0e729ce239be7370e6c9cd639a67340e669cca398e7310e609cbe397672e0e5a9cb2395e72b0e549ca639467280e4e9c9a3
|8,3=>0x165ceca1d913b1c762cec41d853b0475fcebe1d793aec75cceb818000ada75a8eb39d643ac27578ead9d592
|9,0=>0xc305858b0a16122c205838b06160a2c105818b0216022c0057f8afe15fa2bf057d8afa15f22be057b8af615ea2bd05798af215e22bc05778aee15da2bb05758aea15d22ba05738ae615ca2b905718ae215c22b8056f8ade15ba2b7056d8ada15b22b6056b8ad615aa2b505698ad215a22b405678ace159a2
|9,1=>0x316162a2c505898b1216222c405878b0e161a2
|10,0=>0x18e071b8e361c6a38d07198e321c6238c07178e2e1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x61800030800018000008a000044800020400010000005f0000278000134000090000045000020800010000003600001a00000c800005c00002a000014000009000004000001800000a000004800002000000c0000040000018000008000002000000
|1=>0x405000202000098e0002da0001690000a680004be00025a00012c00009540004a000024f00010d0000860000428000212000108000082400041000020300010100008040004000001e60000ef800057c0001be0000cf00006580003280001900000c7
|2=>0x1000000737c0038be001adf000d2f80068600033fe00197f000c6f800633c0030be00184f00092f8004868002024000adf000544000297c0014a8000a1a00050c0002850001424000a0a0004af800237c00119e0008c8000460000217c00109e000812
|3=>0x252f80128600091be00489a00212f801096c00849a00421a00210a00108400081340040400020090010020008004002a5f001509000a17c00509e002800001160000897c0044ae002250001108000880000412400204f0010090008028004006002002
|4=>0x8104004037c0200be01000f008004003297c01843400c21800600d002a87801503400a25f00510f00288580140be0088df004401002097c0104000080df00406e802017c01009a008008004000001ab7c00d1be0062d700304d001824800c034004adf
|5=>0x1842f808633c0430be020a5f01052d808217c0394be0188df00c42f806097c0300be01609a00a52f80522680290be012a5f009501004a17c02500401225f00912b804893402440401205f00856f804297c0214340108df00842f80420280204be01021a
|6=>0xc006f818613c0c14be060a5b02456f812297c0894be041c5f020caf810617c08309e0410c9020827810297c0811be0408cf020464810217c08109e04080b02026781008680803dc04015d02006f810032c0801900400c7020060010013c080024030a5f
|7=>0x404017e0000be80005c20002008000143808ba18085f
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x1060026000a3d020400000004060a0200042f0e0000061d00000000080600000000001f28020000180220060a0600040604080a0204000000000029000600000b00000000
|7,0=>0x1412c53f9c1a0b06d9001b072a08072a1a4e061200c87212071b000033320203636d610662166c002f2c02550708c6ad8dc9df0b75052d005f0a496ea1001dd80fbe17591d15330a65400b122e1e10062b00000a1eb05d005400002a001d4b0200020a04e3710b06026633646054970c2c003e930f5188a90a252d878f00c130
|7,1=>0xe408432d301d8304e1aa0b0b1c271263dc450300020606e2402bde6b00d7a241ab020bcb02123407040d0008902b19bd0009585e8b39042e840b0466130b2d0f020711217a078700
|8,0=>0xac5239779146334fa6d4a3bf9042b3869b23a8c74e8cb39d86a342b023c3c67098999da0a339b0937f2faeb33f4642aecc7f32dadd8aa0bc4ebad647d34b5632249f8e6a453542afa33ce5b19b50c475cd355544244555963345d568a6a67c3a39a37b4e337480184e5d33547822ca4ca3ae7fb2b0b07621514e7d4eae22b0b5
|8,1=>0x42425ca354a38aa937a379703fce008839814d42977f2f463b4246a1a3a3c0cf3699a9c05a89389246253946d09d465bb5678395ac4e4c6931e6a754a082e04a7e6f5749465abba5b6c2b04846bda39e5855ca46b4db73
|9,0=>0x42b3b74eaca657b09aa1b385a6b3a346da4642423955b5d1b9d1469daca4b055aeceb39d464ea6ae4642b0ac4e46b1ceceba4642b342a6b74eb87d5355ce9d7f4eb055a3b1aed2469442
|10,0=>0xb542b11842a81818464242
|11,0=>0x18
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_246 10 roots_246 ops++addP pm 1 dom_119 9 roots_119 ops++addP pm 2 dom_243 10 roots_243 ops++addP pm 3 dom_183 9 roots_183 ops++addP pm 4 dom_215 9 roots_215 ops++addP pm 5 dom_182 8 roots_182 ops++addP pm 6 dom_245 10 roots_245 ops++addP pm 7 dom_167 6 roots_167 ops++addP pm 8 dom_230 7 roots_230 ops++addP pm 9 dzo_87_32 6 roots_87 ops++addP pm 10 dom_165 5 roots_165 ops++addP pm 11 dom_231 8 roots_231 ops++addP pm 12 dom_55 5 roots_55 ops++addP pm 13 dom_151 6 roots_151 ops++addP pm 14 dom_199 6 roots_199 ops++addP pm 15 dom_87 6 roots_87 ops++addP pm 16 dzo_215_32 7 roots_215 ops++addP pm 17 dom_227 7 roots_227 ops++addP pm 18 dom_103 5 roots_103 ops++addP pm 19 dom_197 5 roots_197 ops++addP pm 20 dom_229 6 roots_229 ops++addP pm 21 dom_213 8 roots_213 ops++addP pm 22 dom_181 7 roots_181 ops++addP pm 23 dzo_86_32 5 roots_86 ops++addP pm 24 dzo_211_32 6 roots_211 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_247 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_87_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_215_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_86_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_211_32_82 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_246 10 s (0,roots_246.map (·&&&dom_246)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_247 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_246 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_247 gM v ys):RunD true dom_247 gM v (ori ys):=h
def Z (s:Nat):=barP dom_247 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 69 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 69 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 201 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 73 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 201 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 215 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 87 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 215 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 74 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 74 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 11 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 11 0 = true)
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
theorem lowS_251:Lower true dom_251 roots_251 goal_251 12:=lower_slice_b [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,16,18)] (by decide +kernel) lowS_249
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_slice_b [(0x3030303030303030303030303030303030303030303030303030303030303030,32,36)] (by decide +kernel) lowS_249
def isoMvS_254:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_247
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,18),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,24),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,28),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,17),(16,18),(16,24),(16,80),(16,144),(20,21),(20,22),(20,28),(20,52),(20,84),(20,148),(32,33),(32,36),(32,40),(32,160),(34,35),(34,38),(34,42),(34,50),(34,98),(34,162),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,68),(64,72),(64,80),(64,192),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,130),(128,132),(128,136),(128,144),(128,160),(128,192)]
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 3] }, { op := GateOp.or, inputs := [7, 2] }, { op := GateOp.or, inputs := [4, 2] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.or, inputs := [8, 1] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.or, inputs := [13, 10] }, { op := GateOp.and, inputs := [4, 13] }, { op := GateOp.and, inputs := [11, 15] }, { op := GateOp.and, inputs := [3, 0] }, { op := GateOp.and, inputs := [14, 12] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52850_aux

theorem PEqualNP.Outside.L_meta_52850 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52850_aux.main
