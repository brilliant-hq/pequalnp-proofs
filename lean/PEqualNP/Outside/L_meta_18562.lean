import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18562

namespace PriorG11.SharedCases
abbrev Slice := Inhabited (Fin 4)

variable [sctx : Slice]

def choose {α : Type} (a b c d : α) : α :=
  match sctx.default.val with | 0 => a | 1 => b | 2 => c | _ => d

namespace Rup
abbrev qv:=Nat×Bool
abbrev q0:=List qv
def w3 (l:qv):qv:=(l.1,!l.2)
def w2 (v:Nat->Bool)(l:qv):Prop:=v l.1=l.2
def Holds (v:Nat->Bool)(c:q0):Prop:=∃l∈c,w2 v l
def ep0N (e:Nat):=[0,0,1,1,2,2,3,3,4,4,5,5,6,7].getD e 0
def ep1N (e:Nat):= choose ([3,7,4,9,5,6,7,9,7,8,6,9,8,8].getD e 0) ([8,9,4,9,5,6,7,9,7,8,6,9,8,8].getD e 0) ([8,9,3,7,5,6,7,9,7,8,6,9,8,8].getD e 0) ([8,9,3,7,4,9,7,9,7,8,6,9,8,8].getD e 0)
def epN (s e:Nat):=if s==0 then ep0N e else ep1N e
def neighN (x:Nat):= choose ([136,528,96,641,386,580,292,281,208,42].getD x 0) ([768,528,96,640,386,580,292,280,209,43].getD x 0) ([768,136,96,642,384,580,292,282,209,41].getD x 0) ([768,136,528,642,388,576,288,282,209,45].getD x 0)
def adjB (x y:Nat):=(neighN x).testBit y
def nbrsN (x:Nat):List Nat:= choose ([[3,7],[4,9],[5,6],[0,7,9],[1,7,8],[2,6,9],[2,5,8],[0,3,4,8],[4,6,7],[1,3,5]].getD x []) ([[8,9],[4,9],[5,6],[7,9],[1,7,8],[2,6,9],[2,5,8],[3,4,8],[0,4,6,7],[0,1,3,5]].getD x []) ([[8,9],[3,7],[5,6],[1,7,9],[7,8],[2,6,9],[2,5,8],[1,3,4,8],[0,4,6,7],[0,3,5]].getD x []) ([[8,9],[3,7],[4,9],[1,7,9],[2,7,8],[6,9],[5,8],[1,3,4,8],[0,4,6,7],[0,2,3,5]].getD x [])
def avoidMask (a:Nat):= choose ([28,49,56,67,74,88,134,162,194,263,270,291,298,533,593,773].getD a 0) ([15,29,43,57,75,89,135,163,195,270,298,532,592,644,704,772].getD a 0) ([23,29,51,57,83,89,133,161,193,268,290,296,534,594,644,774].getD a 0) ([39,45,51,57,71,77,83,89,165,197,294,300,594,704,770,770].getD a 0)
def qd (x y:Nat):Nat->Nat×Nat
 | 0=>(0,0)
 | i+1=>if ep0N i==x&&ep1N i==y then (i,0) else if ep1N i==x&&ep0N i==y then (i,1) else qd x y i
def edgeIdxS (x y:Nat):=qd x y 14
def inIB (I x:Nat):=I.testBit x
def capN (k I x:Nat):=if inIB I x then 1 else 2+k
def ineligNbrsN (I x:Nat):List Nat:=(nbrsN x).filter (inIB I)
def eligNbrsN (I x:Nat):List Nat:=(nbrsN x).filter (λ y=>!(inIB I y))
def pop3 (m:Nat):=(m&&&1)+((m>>>1)&&&1)+((m>>>2)&&&1)
def unsl (s:Nat):=(s / 5,s % 5)
def fLive (x j:Nat):Nat:=x*5+j
def fLab (x j c:Nat):Nat:=50+(x*5+j)*10+c
def fOpp (x j c:Nat):Nat:=550+(x*5+j)*10+c
def fRes (t x:Nat):Nat:=1050+t*10+x
def fCommon (x y:Nat):Nat:=1080+(min x y)*10+(max x y)
def fDiff (t x y:Nat):Nat:=1180+(t*10+x)*10+y
def fEqGe (t x:Nat):Nat:=1480+t*10+x
def fHm (x:Nat):Nat:=1500+x
def fRsub (t x j:Nat):Nat:=1510+(t*10+x)*5+j
def fEs (s e x:Nat):Nat:=1660+(s*14+e)*10+x
def fRa (s e x j:Nat):Nat:=1940+((s*14+e)*10+x)*5+j
def fFree (x j:Nat):Nat:=3340+x*5+j
def fEmpty (x j:Nat):Nat:=3390+x*5+j
def fGate (b a:Nat):Nat:=3440+b*14+a
def fGflip (b a:Nat):Nat:=3636+b*14+a
def fSgate (b a:Nat):Nat:=3832+(min b a)*14+(max b a)
def fLt (b a:Nat):Nat:=4028+b*14+a
def fAfter (e x j:Nat):Nat:=4224+(e*10+x)*5+j
def fHsec (e:Nat):Nat:=4924+e
def fSecp (e b a:Nat):Nat:=4938+(e*5+b)*5+a
def fAfree (e x j:Nat):Nat:=5288+(e*10+x)*5+j
def fAempty (e x j:Nat):Nat:=5988+(e*10+x)*5+j
def fStay (e:Nat):Nat:=6688+e
def fPick (e z:Nat):Nat:=6716+e*10+z
def fH0 (e z l:Nat):Nat:=6856+(e*10+z)*5+l
def fBc (a b:Nat):Nat:=7742+a*14+b
def fAvoid (x a j:Nat):Nat:=7998+(x*16+a)*5+j
def fEfh (a l:Nat):Nat:=8798+a*5+l
def fEse (a b:Nat):Nat:=9118+a*14+b
def fMesc (a z l:Nat):Nat:=10014+(a*10+z)*5+l
def fSmate (x j y l:Nat):Nat:=11230+((x*5+j)*10+y)*5+l
def fOmate (x j y l:Nat):Nat:=13730+((x*5+j)*10+y)*5+l
def fIfilt (i y a l:Nat):Nat:=16230+((i*10+y)*3+a)*5+l
def maskRes (k a x:Nat):q0:=(if 0<k&&a.testBit 0 then [(fRes 0 x,true)] else [])++(if 1<k&&a.testBit 1 then [(fRes 1 x,true)] else [])++(if 2<k&&a.testBit 2 then [(fRes 2 x,true)] else [])
def uvSlots (k I u v a b:Nat)(f:Nat->Nat->qv):q0:=(if u != a&&u != b then (List.range (capN k I u)).map (f u) else [])++(if v != a&&v != b then (List.range (capN k I v)).map (f v) else [])
def untriple (b:List Nat)(a:Nat):=let v:=b.getD a 0;(v&&&15,(v>>>4)&&&15,(v>>>8)&&&15)
abbrev unctx:=untriple
def validTriple (b:List Nat)(a:Nat):=a<b.length&&let t:=untriple b a;t.1<14&&t.2.1<10&&t.2.2<10&&!adjB t.2.1 t.2.2
def validCtx (d b:List Nat)(a:Nat):=a<b.length&&let c:=unctx b a;validTriple d c.1&&c.2.1<14&&c.2.2<10
def unmask (b:List Nat)(a:Nat):=let v:=b.getD a 0;(v&&&15,(v>>>4)&&&16383,(v>>>18)&&&1023)
def validMask (b:List Nat)(a:Nat):=a<b.length&&a<6&&let u:=unmask b a;u.1<14&&u.2.1.testBit u.1
namespace R1
abbrev P (x:Nat):qv:=(x,true)
abbrev M (x:Nat):qv:=(x,false)
abbrev G (k I:Nat)(s:Nat×Nat):Bool:=s.1<10&&s.2<capN k I s.1
abbrev C a b:=[M a,P b]
abbrev W a b:=[M a,M b]
abbrev K a b c:=[M a,M b,P c]
abbrev p2 a b c:=[M a,P b,P c]
abbrev L:=unsl
abbrev N:=List.range
abbrev B:=inIB
abbrev D:=capN
abbrev F:=fLive
abbrev E:=fOpp
abbrev O:=untriple
abbrev R:=fLab
abbrev S:=fRes
abbrev V:=ineligNbrsN
abbrev U:=ep1N
abbrev A:=ep0N
abbrev H:=fSgate
abbrev Q:=fRa
abbrev T:=unctx
abbrev X:=nbrsN
abbrev J:=fEs
abbrev z3:=fAfter
abbrev z4:=validTriple
abbrev z5:=fCommon
abbrev z6:=fAempty
abbrev z9:=uvSlots
abbrev za:=fPick
abbrev zb:=fHsec
abbrev zc:=validCtx
abbrev zd:=fSecp
abbrev ze:=fIfilt
abbrev zf:=fFree
abbrev zg:=eligNbrsN
abbrev zh:=avoidMask
end R1
section B0
open R1
def expand0 (k I g r:Nat):q0:=let c n m:=(r>>>n)&&&m;let e:=L (r&&&63);let f:=e.1;let h:=e.2;let i:=L (c 6 63);let m:=i.1;let n:=i.2;let o:=L (c 3 63);let p:=o.1;let q:=o.2;let s:=D k I;let u:=r&&&15;let v:=r&&&7;let w:=c 6 15;let z:=c 4 15;let Y:=c 3 15;let a a b c w x y z:=if g<b then if g<a then w else x else if g<c then y else z;if g<16 then a 4 8 12 (a 1 2 3 [P (F u 0)] (C (F f h) (R f h f)) (C (F f (h+1)) (F f h)) (K (F f h) (R f h w) (z5 f w))) (a 5 6 7 (M (F u (2+(c 4 7)))::maskRes k (c 7 7) u) [M (S z u)] [M (z5 u z)] (K (S v Y) (S v (c 7 15)) (z5 Y (c 7 15)))) (if g<10 then let y:=c 7 15;if g<9 then [M (fDiff v Y y),P (S v Y)] else [M (fDiff v Y y),M (S v y)] else if g<11 then [P (z5 z (c 8 15))] else [M (z5 u z),M (F u (c 11 7)),P (R u (c 8 7) z),P (R u (c 11 7) z)]++(N k).map (λ t=>P (fDiff t u z))) (a 13 14 15 ((N (s u)).map (λ j=>P (fAvoid u z j))) (C (fAvoid f w h) (F f h)) (W (fAvoid f w h) (R f h (c 10 15))) (C (S u 9) (S (u+1) 9))) else a 20 24 28 (a 17 18 19 (let b:=(c 4 1)==1;[(S u 9,b),(S (u+1) 9,b),P (fEqGe u 9)]) (K (fEqGe v (Y+1)) (S v Y) (S (v+1) Y)) (let b:=(c 7 1)==1;[M (fEqGe v (Y+1)),(S v Y,b),(S (v+1) Y,b),P (fEqGe v Y)]) [M (fHm u)]) (a 21 22 23 (W (fHm u) (F u (1+k))) (M (fHm u)::M (F u (1+(c 4 7)))::maskRes k (c 7 7) u) (C (fRsub v p q) (F p q)) (K (fRsub v p q) (S v (c 9 15)) (R p q (c 9 15)))) (a 25 26 27 (M (S v p)::P (fHm p)::((N (s p)).filter (λ j=>j != q)).map (λ j=>P (fRsub v p j))) [M (E f h f)] [M (F f h),M (R f h w),M (E f h w),P (fHm w)] (M (F f h)::M (R f h w)::P (E f h w)::(N (s w)).map (λ l=>P (fSmate f h w l)))) (a 29 30 31 (C (fSmate f h m n) (F m n)) (let d:=c 12 15;let b:=(c 17 1)==1;[M (fSmate f h m n),((if ((c 16 1)==1) then E m n d else R m n d),b),((if ((c 16 1)==1) then E f h d else R f h d),!b)]) (M (F f h)::M (E f h w)::P (R f h w)::(N (s w)).map (λ l=>P (fOmate f h w l))) (C (fOmate f h m n) (F m n)))
def expand1 (k I g r:Nat):q0:=let f n m:=(r>>>n)&&&m;let h:=L (r&&&63);let m:=h.1;let n:=h.2;let o:=L (f 6 63);let p:=o.1;let t:=o.2;let u:=L (f 5 63);let v:=u.1;let w:=u.2;let z:=r&&&15;let Y:=f 4 15;let Z:=f 1 15;let c a b c w x y z:=if g<b then if g<a then w else x else if g<c then y else z;if g<48 then c 36 40 44 (c 33 34 35 (let d:=f 12 15;let b:=(f 17 1)==1;[M (fOmate m n p t),((if ((f 16 1)==1) then E p t d else R p t d),b),((if ((f 16 1)==1) then R m n d else E m n d),!b)]) [M (F m n),M (E m n (f 6 15)),M (zf m n)] [M (F m n),M (E m n (f 6 15)),M (E m n (f 10 15))] (let d:=f 10 15;let b:=(f 14 1)==1;[M (F m n),M (E m n (f 6 15)),(R m n d,b),(E (f 6 15) 0 d,!b)])) (c 37 38 39 [M (F z (f 8 7)),M (F z (f 11 7)),M (E z (f 8 7) Y),M (E z (f 11 7) Y)] [P (E z 0 Y)] (M (E z 0 Y)::(N (D k I ((X z).getD (f 8 3) 0))).map (λ l=>P (ze z Y (f 8 3) l))) [M (E z 0 Y)]) (c 41 42 43 [M (J (f 4 1) z (epN (1-(f 4 1)) z))] (K (J 0 z Y) (J 1 z Y) (fHm Y)) [P (J (f 4 1) z (epN (f 4 1) z))] (let s:=r&&&1;let x:=f 5 15;M (J s Z x)::P (J (1-s) Z x)::(N (D k I x)).map (λ j=>P (Q s Z x j)))) (c 45 46 47 (W (Q (r&&&1) Z (f 5 15) (f 9 7)) (Q (r&&&1) Z (f 5 15) (f 12 7))) (C (Q (r&&&1) Z v w) (F v w)) (C (Q (r&&&1) Z v w) (J (r&&&1) Z v)) (W (Q (r&&&1) Z v w) (J (1-(r&&&1)) Z v))) else c 52 56 60 (c 49 50 51 (let s:=r&&&1;let y:=f 11 15;let b:=(f 16 1)==1;[M (Q s Z v w),((if ((f 15 1)==1) then E v w y else R v w y),b),((J (if ((f 15 1)==1) then 1-s else s) Z y),!b)]) [P (F m n)] [P (E m n (f 6 15))] (let a:=edgeIdxS m ((V I m).getD n 0);[P (Q a.2 a.1 m n)])) (c 53 54 55 (let a:=edgeIdxS z ((zg I z).getD 0 0);[P (Q a.2 a.1 z (V I z).length)]) (let e:=f 13 15;K (fSmate m n p t) (Q (f 12 1) e p t) (Q (f 12 1) e m n)) (let e:=f 13 15;K (fOmate m n p t) (Q (f 12 1) e p t) (Q (1-(f 12 1)) e m n)) (C (zf m n) (F m n))) (c 57 58 59 (W (zf m n) (Q (f 6 1) (f 7 15) m n)) (C (fEmpty m n) (F m n)) (W (fEmpty m n) (E m n (f 6 15))) (C (fGate z Y) (H z Y))) (if g<62 then if g<61 then [M (fGflip z Y),P (H z Y)] else [M (H z Y),P (fGate z Y),P (fGflip z Y)] else if g<63 then let q:=L (f 8 63);[M (Q (f 14 1) z q.1 q.2),M (Q (f 15 1) Y q.1 q.2),((if (f 14 1)==(f 15 1) then fGate z Y else fGflip z Y),true)] else let b:=(f 13 1)==1;[M (fGate z Y),(J (f 8 1) z (f 9 15),b),(J (f 8 1) Y (f 9 15),!b)])
def expand2 (k I _m g r:Nat):q0:=let c n m:=(r>>>n)&&&m;let d:=L (c 4 63);let f:=d.1;let h:=d.2;let i:=r&&&15;let j:=c 4 15;let n:=c 4 31;let o:=L n;let q:=o.1;let a a b c w x y z:=if g<b then if g<a then w else x else if g<c then y else z;if g<80 then a 68 72 76 (a 65 66 67 (let b:=(c 13 1)==1;[M (fGflip i j),(J (c 8 1) i (c 9 15),b),(J (1-(c 8 1)) j (c 9 15),!b)]) (W (H i j) (fLt i j)) [P (H i j),P (fLt i j),P (fLt j i)] (W (fLt i j) (fLt j i))) (a 69 70 71 (K (fLt i j) (fLt j (c 8 15)) (fLt i (c 8 15))) (C (z3 i f h) (F f h)) (W (z3 i f h) (Q (c 10 1) i f h)) (K (z3 i f h) (Q (c 10 1) (c 11 15) f h) (fLt i (c 11 15)))) (if g<74 then if g<73 then [M (fAfree i f h),P (z3 i f h)] else [M (fAfree i f h),P (zf f h)] else if g<75 then [M (z6 i f h),P (z3 i f h)] else [M (z6 i f h),P (fEmpty f h)]) (if g<78 then if g<77 then [M (zd i q o.2),P (F (A i) q)] else [M (zd i q o.2),P (F (U i) o.2)] else if g<79 then W (zd i q o.2) (Q 0 i (A i) q) else W (zd i q o.2) (Q 1 i (U i) o.2)) else a 84 88 92 (a 81 82 83 (let y:=c 9 15;let b:=(c 14 1)==1;[M (zd i q o.2),((if ((c 13 1)==1) then R (U i) o.2 y else R (A i) q y),b),((if ((c 13 1)==1) then E (A i) q y else E (U i) o.2 y),!b)]) (M (zb i)::(N (D k I (A i))).flatMap λ b=>(N (D k I (U i))).map λ e=>P (zd i b e)) (P (fStay i)::(N 10).map (λ z=>P (za i z))) []) (if g<86 then if g<85 then [M (H i j),M (fStay i),P (fStay j)] else let z:=c 8 15;[M (H i j),M (za i z),P (za j z)] else if g<87 then C (fH0 i f h) (z3 i f h) else p2 (fH0 i f h) (E f h (A i)) (E f h (U i))) (a 89 90 91 (M (za i j)::P (zb i)::(N (D k I j)).map (λ l=>P (fH0 i j l))) [] [] (let s:=L (r&&&63);C (E s.1 s.2 (c 6 15)) (F s.1 s.2))) []
def expand3 (k I:Nat)(t0 c0 x1:List Nat)(g r:Nat):q0:=let f n m:=(r>>>n)&&&m;let h:=D k I;let m:=z9 k I;let n:=O t0;let o:=T c0;let q:=r&&&15;let u:=r&&&63;let v:=f 4 15;let w:=f 6 15;let Y:=f 6 7;let Z:=f 8 3;let d a b c w x y z:=if g<b then if g<a then w else x else if g<c then y else z;if g<112 then d 100 104 108 (d 97 98 99 [] (let a:=(f 4 1)==1;let t:=n q;K (J 0 t.1 (if a then t.2.2 else t.2.1)) (J 1 t.1 (if a then t.2.1 else t.2.2)) (fBc q t.1)) (let t:=n q;[M (fBc q v),M (fStay v),P (zb t.1)]++m (A t.1) (U t.1) t.2.1 t.2.2 (λ z l=>P (z6 v z l))) []) (d 101 102 103 [] (let c:=o u;let a:=c.2.1;let b:=c.2.2;let t:=n c.1;[M (fBc c.1 a),M (za a b)]++m (A t.1) (U t.1) t.2.1 t.2.2 (λ z l=>P (z6 a z l))++[P (zb t.1)]++(if b != t.2.1&&b != t.2.2 then [P (fHm b)] else [])++(N (h b)).flatMap (λ l=>[P (fEfh u l),P (fAfree a b l)])++((N 14).filter (λ e=>e != a)).map (λ e=>P (fEse u e))) (C (fEfh u Y) (z3 (o u).2.1 (o u).2.2 Y)) (let t:=n (o u).1;W (fEfh u Y) (E (o u).2.2 Y (if ((f 9 1)==1) then t.2.2 else t.2.1)))) (d 105 106 107 (let c:=o u;p2 (fEfh u Y) (E c.2.2 Y (A (n c.1).1)) (E c.2.2 Y (U (n c.1).1))) (C (fEse u w) (fLt (o u).2.1 w)) (p2 (fEse u w) (J 0 w (o u).2.2) (J 1 w (o u).2.2)) (C (fEse u w) (fBc (o u).1 w))) (d 109 110 111 (let a:=r&&&7;let um:=unmask x1 a;let am:=um.2.1;let cm:=um.2.2;P (zb um.1)::((N 14).filter (λ e=>am.testBit e)).flatMap (λ e=>P (fStay e)::((N 10).filter (λ z=>!(cm.testBit z))).map (λ z=>P (za e z)))++((N 10).filter (λ z=>cm.testBit z)).flatMap (λ z=>(N (h z)).flatMap (λ l=>P (zf z l)::P (fMesc a z l)::((N 10).filter (λ y=>cm.testBit y)).map (λ y=>P (E z l y))))) (let a:=r&&&7;let d:=(unmask x1 a).1;let s:=L (f 3 63);p2 (fMesc a s.1 s.2) (E s.1 s.2 (A d)) (E s.1 s.2 (U d))) (let a:=r&&&7;let am:=(unmask x1 a).2.1;let s:=L (f 3 63);M (fMesc a s.1 s.2)::((N 14).filter (λ e=>!(am.testBit e))).flatMap (λ e=>[P (Q 0 e s.1 s.2),P (Q 1 e s.1 s.2)])) []) else d 116 120 124 [] (d 117 118 119 [] (let x0:=(X q).getD Z 0;C (ze q v Z (f 10 7)) (z6 (edgeIdxS q x0).1 x0 (f 10 7))) (C (ze q v Z (f 10 7)) (zf ((X q).getD Z 0) (f 10 7))) (W (ze q v Z (f 10 7)) (R ((X q).getD Z 0) (f 10 7) v))) (d 121 122 123 (C (ze q v Z (f 10 7)) (R ((X q).getD Z 0) (f 10 7) (f 13 15))) [] (W (za q v) (za q (f 8 15))) []) (d 125 126 127 [] (let s:=L u;C (R s.1 s.2 w) (F s.1 s.2)) (M (z5 q v)::(N (h q)).map (λ j=>P (R q j v))++(N (h v)).map (λ l=>P (R v l q))) (let p:=f 4 3;let a:=if p==2 then 1 else 0;let b:=if p==0 then 1 else 2;let y1:=f 6 15;let y2:=f 10 15;let j:=f 14 7;[P (fHm q),M (S a q),M (S b q),M (S a y1),P (S b y1),M (S b y2),P (S a y2),M (F q j),P (fRsub a q j),P (fRsub b q j)]++(if 2<k then [P (F q 4)] else [])))
def expandScheme (k I b:Nat)(c d e:List Nat)(a:Nat):q0:=let f:=a&&&127;let r:=a>>>7;if f<64 then if f<32 then expand0 k I f r else expand1 k I f r else if f<96 then expand2 k I b f r else expand3 k I c d e f r
def enabled0 (k I g r:Nat):Bool:=let e n m:=(r>>>n)&&&m;let f:=L (r&&&63);let h:=f.1;let m:=L (e 6 63);let n:=m.1;let o:=L (e 3 63);let p:=o.1;let q:=D k I;let s:=G k I;let u:=B I;let v:=r&&&15;let w:=r&&&7;let z:=e 6 15;let N:=e 4 15;let Y:=e 3 15;let c a b c w x y z:=if g<b then if g<a then w else x else if g<c then y else z;if g<16 then c 4 8 12 (c 1 2 3 (v<10) (s f) (h<10&&f.2+1 < q h) (s f&&z<10)) (c 5 6 7 (v<10&&!u v&&(e 4 7) < k&&(e 7 7)<(1<<<k)&&pop3 (e 7 7)==k-(e 4 7)) (v<10&&u v&&N < k) (v < N&&N<10&&(u v||u N)) (w < k&&Y < (e 7 15)&&(e 7 15)<10)) (if g<10 then w < k&&Y<10&&(e 7 15)<10&&Y != (e 7 15) else if g<11 then let b:=e 8 15;v<10&&u v&&N<10&&b<10&&N != b&&adjB v N&&adjB v b else v<10&&!u v&&N<10&&N != v&&(e 8 7) < (e 11 7)&&(e 11 7) < q v) (c 13 14 15 (v<10&&N<16&&!((zh N).testBit v)&&((zh N)&&&neighN v) != 0) (s f&&z<16) (let y:=e 10 15;s f&&z<16&&y<10&&(zh z).testBit y) (v+1 < k)) else c 20 24 28 (c 17 18 19 (v+1 < k) (w+1 < k&&Y<9) (w+1 < k&&0 < Y&&Y<9) (v<10&&u v)) (c 21 22 23 (v<10&&!u v) (v<10&&!u v&&(e 4 7) < k&&(e 7 7)<(1<<<k)&&pop3 (e 7 7)==k-(e 4 7)) (w < k&&p<10&&!u p&&o.2 < q p) (w < k&&p<10&&!u p&&o.2 < q p&&(e 9 15)<10)) (c 25 26 27 (w < k&&p<10&&!u p&&o.2 < q p) (s f) (s f&&z<10&&z != h) (s f&&z<10&&z != h&&!u z)) (if g<30 then let a:=s f&&n<10&&n != h&&!u n&&m.2 < q n;if g<29 then a else a&&(e 12 15)<10 else if g<31 then s f&&z<10&&z != h&&!u z else s f&&n<10&&n != h&&!u n&&m.2 < q n)
def enabled1 (k I m g r:Nat):Bool:=let b n m:=(r>>>n)&&&m;let c:=L (r&&&63);let f:=c.1;let h:=c.2;let l:=L (b 6 63);let n:=l.1;let o:=L (b 5 63);let p:=D k I;let s:=G k I;let t:=B I;let u:=r&&&15;let v:=b 4 15;let w:=b 6 15;let z:=b 1 15;let a a b c w x y z:=if g<b then if g<a then w else x else if g<c then y else z;if g<48 then a 36 40 44 (a 33 34 35 (s c&&n<10&&n != f&&!t n&&l.2 < p n&&(b 12 15)<10) (s c&&w<10&&w != f&&t w) (let d:=b 10 15;s c&&w<10&&w != f&&t w&&d<10&&d != w) (s c&&w<10&&w != f&&t w&&(b 10 15)<10)) (a 37 38 39 (u<10&&!t u&&v<10&&t v&&(b 8 7) < (b 11 7)&&(b 11 7) < p u) (u<10&&t u&&v<10&&adjB u v) (m==1&&u<10&&t u&&v<10&&!t v&&!adjB u v&&(b 8 3)<3&&(b 8 3)<(X u).length) (u<10&&t u&&v<10&&t v&&u != v)) (a 41 42 43 (u<14) (u<14&&v<10) (u<14) (z<14&&(b 5 15)<10)) (if g<46 then if g<45 then z<14&&(b 5 15)<10&&(b 9 7) < (b 12 7)&&(b 12 7) < p (b 5 15) else z<14&&s o else z<14&&s o) else a 52 56 60 (a 49 50 51 (z<14&&s o&&(b 11 15)<10) (f<10&&!t f&&h < ((V I f).length+(if (zg I f).isEmpty then 0 else 1))&&h < p f) (f<10&&!t f&&h < (V I f).length&&h < p f&&(V I f).getD h 10==w) (f<10&&!t f&&h<(V I f).length&&h < p f)) (a 53 54 55 (u<10&&!t u&&!(zg I u).isEmpty&&(V I u).length < p u) (s c&&n<10&&n != f&&!t n&&l.2 < p n&&(b 13 15)<14) (s c&&n<10&&n != f&&!t n&&l.2 < p n&&(b 13 15)<14) (s c)) (a 57 58 59 (s c&&(b 7 15)<14) (s c) (s c&&w<10) (u < v&&v<14)) (if g<62 then u < v&&v<14 else if g<63 then u < v&&v<14&&s (L (b 8 63)) else u < v&&v<14&&(b 9 15)<10)
def enabled2 (k I m g r:Nat):Bool:=let b n m:=(r>>>n)&&&m;let c:=L (b 4 63);let d:=D k I;let f:=G k I;let h:=r&&&15;let i:=b 4 15;let a a b c w x y z:=if g<b then if g<a then w else x else if g<c then y else z;if g<80 then a 68 72 76 (if g<66 then if g<65 then h < i&&i<14&&(b 9 15)<10 else h<14&&i<14&&h != i else h < i&&i<14) (a 69 70 71 (let e:=b 8 15;h<14&&i<14&&e<14&&h != i&&i != e&&h != e) (h<14&&f c) (h<14&&f c) (h<14&&f c&&(b 11 15)<14&&(b 11 15) != h)) (h<14&&f c) (let p:=L (b 4 31);h<14&&p.1 < d (A h)&&p.2 < d (U h)) else a 84 88 92 (a 81 82 83 (let p:=L (b 4 31);h<14&&p.1 < d (A h)&&p.2 < d (U h)&&(b 9 15)<10) (h<14) (m>0&&h<14) false) (if g<86 then let e:=m>0&&h<14&&i<14&&h != i;if g<85 then e else e&&(b 8 15)<10 else m>0&&h<14&&f c) (a 89 90 91 (m>0&&h<14&&i<10) false false (f (L (r&&&63))&&(b 6 15)<10)) false
def enabled3 (k I m _q:Nat)(t0 c0 x0:List Nat)(g r:Nat):Bool:=let b n m:=(r>>>n)&&&m;let c:=D k I;let d:=B I;let e:=zc t0 c0;let h:=z4 t0;let j:=r&&&15;let n:=b 4 15;let o:=r&&&63;let p:=b 6 7;let u:=b 6 15;let a a b c w x y z:=if g<b then if g<a then w else x else if g<c then y else z;a 104 112 120 (if g<100 then a 97 98 99 false (m>0&&h j) (m>0&&h j&&n<14) false else if g<102 then if g<101 then false else m>0&&e o else m>0&&e o&&p < c (T c0 o).2.2) (a 105 108 110 (m>0&&e o&&p < c (T c0 o).2.2) (m>0&&e o&&u<14&&u != (T c0 o).2.1) (if g<109 then m==1&&validMask x0 (r&&&7) else m==1&&validMask x0 (r&&&7)&&G k I (L (b 3 63))) (if g<111 then m==1&&validMask x0 (r&&&7)&&G k I (L (b 3 63)) else false)) (a 115 116 117 false false false (m==1&&j<10&&d j&&n<10&&!d n&&!adjB j n&&(b 8 3)<3&&(b 8 3)<(X j).length&&(b 10 7) < c ((X j).getD (b 8 3) 0))) (if g<124 then a 121 122 123 (m==1&&j<10&&d j&&n<10&&!d n&&!adjB j n&&(b 8 3)<3&&(b 8 3)<(X j).length&&(b 10 7) < c ((X j).getD (b 8 3) 0)&&(b 13 15)<10&&adjB j (b 13 15)) false (m>0&&j<14&&n < (b 8 15)&&(b 8 15)<10) false else a 125 126 127 false (G k I (L o)&&u<10) (j < n&&n<10&&!d j&&!d n) (j<10&&!d j&&let p:=b 4 3;((p==0&&1<k)||(0<p&&p<3&&2<k))&&(b 6 15)<10&&(b 10 15)<10&&(b 14 7)<c j))
end B0
def enabled (k I a c:Nat)(d e f:List Nat)(b:Nat):Bool:=let g:=b&&&127;let r:=b>>>7;if g<64 then if g<32 then enabled0 k I g r else enabled1 k I a g r else if g<96 then enabled2 k I a g r else enabled3 k I a c d e f g r
abbrev expS:=expandScheme
abbrev enS:=enabled
end Rup

end PriorG11.SharedCases
namespace PriorG11.SharedCases
abbrev CellData := Nat × Nat × Nat × Nat × List Nat × List Nat × List Nat
def CellData.budget (b : CellData) := b.1
def CellData.independentMask (b : CellData) := b.2.1
def CellData.mode (b : CellData) := b.2.2.1
def CellData.symmetry (b : CellData) := b.2.2.2.1
def CellData.pins (b : CellData) := b.2.2.2.2.1
def CellData.pairs (b : CellData) := b.2.2.2.2.2.1
def CellData.masks (b : CellData) := b.2.2.2.2.2.2

def evidence : List (List Nat × List Nat × List Nat) := [
  ⟨[],[],[]⟩,
  ⟨[0x947,0x948,0x989,0x98a,0x98b,0x98d],[0x692,0x2a2,0x2b2,0x2c2],[0x813c00d]⟩,
  ⟨[0x948],[],[]⟩,
  ⟨[0x712],[],[]⟩,
  ⟨[0x637],[],[]⟩,
  ⟨[0x613,0x713,0x983],[0x32],[]⟩,
  ⟨[0x612],[],[]⟩,
  ⟨[0x713,0x983],[0x31],[]⟩,
  ⟨[0x437,0x987],[0x71],[]⟩,
  ⟨[0x989,0x98c],[0x90,0x690,0x990,0x2a0,0x2b0,0x2c0],[]⟩,
  ⟨[0x989],[0x90],[]⟩,
  ⟨[0x989],[],[]⟩,
  ⟨[0x916],[],[]⟩,
  ⟨[0x949,0x989,0x98a,0x75b,0x75d,0x98c,0x94d],[0x90,0x691,0x2a1,0x2b1,0x2c1,0x91],[0x813c00d]⟩,
  ⟨[0x636],[],[]⟩,
  ⟨[0x986],[],[]⟩,
  ⟨[0x307],[],[]⟩,
  ⟨[0x549,0x989,0x98d],[0x690,0x91],[]⟩,
  ⟨[0x63d],[],[]⟩,
  ⟨[0x700],[],[]⟩,
  ⟨[0x212],[],[]⟩,
  ⟨[0x825],[],[]⟩,
  ⟨[0x413],[],[]⟩,
  ⟨[0x837],[],[]⟩,
  ⟨[0x825],[0x50],[]⟩,
  ⟨[0x989],[0x690,0x90],[]⟩,
  ⟨[0x413,0x837],[0x71],[]⟩,
  ⟨[0x837,0x976,0x700,0x980],[0x161,0x603],[]⟩,
  ⟨[0x700,0x941],[0x211],[]⟩,
  ⟨[0x948,0x989],[0x280,0x91,0x691,0xc1,0x5c1],[]⟩,
  ⟨[0x989,0x976,0x837,0x947],[0x690,0x161,0x72,0x273,0x90],[]⟩,
  ⟨[0x837,0x947],[0x271,0x70],[]⟩]
def cellOf (word : Nat) : CellData :=
  let parameters := evidence.getD (word/8192) ([],[],[])
  ⟨(word/1024) % 4,word % 1024,(word/4096) % 2,0,parameters⟩
def cells0 : List CellData := ([
  1,2,4,8,16,32,64,128,256,512,3,5123,5,5125,6,5126,
  1034,12,5132,1041,20,5140,1048,33,5153,1058,1064,48,5168,65,5185,1090,
  1096,1104,1154,132,5252,1184,1216,1281,1282,1284,1288,1312,5633,1540,528,5648,
  1600,1664,1792,1031,14343,1038,6158,1045,6165,1052,6172,1059,6179,1066,6186,1073,
  6193,1080,6200,1091,22595,1098,6218,1105,6225,1112,6232,1158,6278,1186,6306,1218,
  6338,1283,6403,2309,1286,6406,2314,1292,6412,1313,6433,1314,6434,1320,6440,1541,
  6661,2577,1556,6676,1601,6721,1616,6736,1668,6788,1728,6848,1793,6913,1796,6916,
  2311,7431,2318,7438,2339,7459,2346,7466,2581,7701,2641,7761,2821,7941] : List Nat).map cellOf
def cells1 : List CellData := ([
  28673,2,4,16,32,64,256,512,37891,5,46085,1041,54305,62529,1030,1034,
  1058,1090,1154,1282,1044,1284,1540,1072,1104,1552,1312,1600,1792,1031,71687,6155,
  6179,1091,71747,2179,2069,2097,2129,1038,6158,1158,6278,1286,6406,2090,2122,2314,
  1186,6306,1314,6434,2242,2580,2820,2640,2063,80911,2183,7303,2091,89131,2123,7243,
  2211,7331,3267,2318,7438,2346,7466] : List Nat).map cellOf
def cells2 : List CellData := ([
  1,2,4,8,16,32,64,128,256,512,3,95235,5,103429,6,5126,
  1033,1036,1041,5138,20,5140,1048,1057,34,5154,1064,48,5168,1089,1090,1096,
  1104,1153,1156,1184,1216,1282,1284,1288,1312,1538,1540,528,5648,1600,1664,1792,
  1031,112647,1037,6157,1043,6163,1045,6165,1046,120854,2073,1052,6172,1059,129059,1065,
  6185,1073,6193,1074,137266,1080,6200,1091,145475,1097,6217,2129,1106,6226,1112,6232,
  1157,6277,1185,6305,2241,1286,6406,1292,6412,1314,6434,2344,1542,6662,1554,6674,
  1556,6676,1602,6722,1616,6736,1668,6788,1728,6848,1794,6914,1796,6916,2071,121879,
  2077,7197,2099,154675,2105,7225,2131,7251,2137,7257,2582,7702,2642,7762,2822,7942] : List Nat).map cellOf
def cells3 : List CellData := ([
  1,2,4,8,16,32,64,128,256,512,3,5123,5125,6,160774,5129,
  1036,5137,1042,1048,168993,34,177186,5156,5160,48,5168,185409,66,5186,68,193604,
  72,5192,1104,5249,5252,1184,1216,1282,5380,1288,1312,5634,528,5648,576,5696,
  5760,1792,1031,6151,6157,1043,6163,1049,6169,1059,202787,6181,1062,6182,6185,6188,
  1073,6193,1074,6194,1080,6200,1091,211011,1093,219205,1094,227398,1097,6217,1100,235596,
  6225,2130,2136,1157,6277,1185,6305,1188,6308,6337,1220,194756,1286,6406,1292,6412,
  1314,6434,1316,6436,1320,6440,1554,6674,1602,6722,2640,1728,6848,1794,6914,2087,
  244775,2093,7213,2099,7219,2105,7225,2119,252999,2125,7245,2131,7251,2137,7257,2213,
  7333,2245,261317,2342,7462,2348,7468,2642,7762] : List Nat).map cellOf

end PriorG11.SharedCases
namespace PriorG11.Bounds
open PriorG11.SharedCases
def cellsAt (i : Fin 4) : List CellData := match i.val with
  | 0 => cells0 | 1 => cells1 | 2 => cells2 | _ => cells3

end PriorG11.Bounds

namespace PriorG11.Compressed
def strict {α : Type} (x : Nat) (use : Nat → α) : α :=
  match x with | 0 => use 0 | k+1 => use (k+1)
def tile0 : List (List Nat) :=
[[0xd001a110009090000,0xb00441000340d0027,0x500650a005b0c004f,0x3007304006f05006a,0x5007e04007a040076,0x4008d040089060083,0xf00a309009a090091,0x300bf0500ba0800b2,0x400c90300c60400c2,0x300d50400d10400cd,0x500de0300db0300d8,0x300eb0400e70400e3,0x700f30200f10300ee,0xff0300fc0200fa,0x401050201030400ff,0x5011205010d040109,0x2011e03011b040117,0x30127040123030120,0x5012e00012e04012a,0x10138020136030133,0x5014103013e050139,0x3014f060149030146,1099511627777,0x80000002010000],
[0x40005e030100000000,0x8200a00000000000,0x80c200000000002000,0x8000000800003001,0x210080000c01a112,0x4000001608d00c0,0x700b85240a009a0,0x38982a406004d00100,0x80400268000100cc,0x200134000080000000,0x9a0000400000010080,0x2000000100601000,281758578789632,0x1e0a1048026800010,0x588280134002000000,0x6009a0000800007180,0xd80002000000f06281,0x1000008844e20d004,0x165e33107004fc00,0x3319d03c03ca000080,0x42202620000400000,0x13100002000001c8d,0x80001000180ec6a212,0x8000008e388098098],
[0x1e4e1ec84c04c6000,0x790682802891000400,0x416017290002000162,0xd2400400001fd748a,0x20000000fe49a0c0,0x4000000000486806ce,0x804036038a0000,0x40301b01c500002000,0xd80e2800010000001,0x71400200000002009a,0x4000001c0510740,0xe82a83e038a0,0x7c7cc442101c500002,0xb2b1180e2d80019b9d,0x98318ed000fa4eaa44,0x2f68004efd1f256588,0x20000e9936844e2d,0x337d49bd628199980,0xcf2f5a158cf3d20010,0xb10b469365000801b0,0xe376e00004000007f7,0x700002000000000285,0x100000004020311bb,0x6018188ddb800],
[0xd0348c46edc000080,0x864376f0840001000,0x1bd800002000000c82,0x5400100332c7c79434,0x800000403d21b0dec,0x91f225c10e08448000,0x2af5074422558004e7,0x43e2e5300080040001,0x72980001080000c996,0x900080d3f4a4cf2201,0x49df897a841108b94e,0x404288885d655000,0x144634758001e000,0x241a3e800010000000,0x1f4000080000002010,0x4000001b00c120d,0xe00849068fa0,0xfc7c4f449347d00002,0x281259a3edc001ec9c,0x30e5e4000080000040,0xf368007b2755224e11,0x20015711a7249c72,0xedfc918604f47b100,0x24aeb227a3d8c20400],
[0x7494523bac0009d294,0x49b2f0840000000267,0xda000201c16943ecca,0x1f0095cca5fc2554da,0x271e653492b2759403,0x3c9a895d3afad000bb,0x68b0aac80000400000,0x556400002000002ecd,4503599627375706,0x800000020102e2ab2,0x1d00c1715590000,0xf87a8b8aac80000400,0x45e5564ac0020f9e30,0xc3a56001003e848882,0xd0009c16fe4a5a2302,0x400000272d498970c6,0xdf191ae8c6be7a0000,0xd86655f3d8000217f,0x342fd400001000000d,0xea0900280a188a46da,0x8004000085938c1a97,10960500848,0x40206c5fdb00002,0x28362fed800010000],
[0xb17f6c00030000000e,0xb708020004e0090749,0x2009e5858628dabf,0x443326f60339c,0x241a8383076800010,0xdc1c183b4000080000,0xc1da0013c0009d130,0xd00002000008a0724e,0x1013aec647847160e,0x80343e939b076ce0,0x812351d18d3a000400,0x28ecc6b35800402810,0x643200002000000000,4503599631573112,0x80002000c0683c3219,0x1c40a0889e190ca200,0x88484f2c8bf2800400,0x7a64ff00002000000,0x27f800010000804826,0x2780027a261403d3,0x4000fe140a89e993fc,0x900b8628f6c9fe0000,0x45c47d64ff88020000,0x3fb28e54001008c4a0],
[0xce8000080000000008,0x400000010081fd9,70394781165376,0x341e47f673a00002,0xfa40b39d4e0010040,0xda124000080000100,0x920000400000000052,0x2000000080410ad0,0x10941421085684900,0x1212242b424c80010,0xf921da430000080000,0x2d2193000400d150c0,0x300002000000000291,0x1000000040208b69e,0x2ef6140e845b4f1800,0xb080a2da78ea00082,0x2918d66a0013c0013b,0x6b3500002000000000,0x80001000000040208e,0x8009a41a14047359a,5100723332864,0x80411ed95c0000400,0x8f6cae00002000000,0x6570004f0002b44c04],
[0x500080015a2804147b,0x40000000004a41b2ba,0x804122d9980000,0x8040916ccc00002000,0x48b666000100000004,0x332500080013a28041,0x40000000004a49b,8813582064960,0x54030936cea00002,0x2149b675000010000,0x51b3a800008000002c,0xd510040001001703ca,0x2000000000252ad9,70508706862848,0x340b04b368b800010,0x84a59b45e10008000a,0xedacd080040001e1c0,0xb8c002000861584852,0x10006a02044d0986d8,638933847200,0x1008265bba4000080,0xa132ddd20000400000,0x6ee90031e0031d8c00,0xce0010008ec6420299],
[0x800000000094d3774,4512562619842560,0xd022136dfdc0000400,0x49b6fee940020031d8,0x830da0015973b60441,0x800000000094eb,0x40000001008279cd34,0x1500613ce69a0000,0xc0449e734d00002000,0x5039a680001000000a,0xd34000d80006a5a032,0x40003731065289c,0x76f249920a948e69b2,0x1d051d2a673c9ac002,0x93b53c041d600109f1,0xaa07429001007ab684,0x88000040000000005a,0x2000000080415b04,0xb0030ad824400,0xe5a02a56c122000010,0x6d2be0910000e80006,0x304892000400000300,0xfac00286e049920696,0x100020905192b382c],
[0x67c849535a47acd00,0x6c4adade411a900080,0x2175222c0000400284,0x911600002000000000,4503599631573178,0x80006a5c0685d488b,0x1492f0a5aea445a900,0x808a57b23295000415,0x2be92f9a80020a8a49,0xa2f56001054524c45a,0x800082a29264f715fc,0x435fff37884b0255d6,0xfa9c49c9834e4d5800,0xa504c3a9d8ac0021af,0x62d61d006c00035fce,0xea900080002a8153a,0x40942948aba31eb,0x2be024d60597605b5,0x142b32ccb08702712,0x5b166d843860100001,0x3ac24210080000b4a3,0x360000400000000043,0x2000000080419d61,0xd4b4040ceb09b00],
[0x6a02a67584d8001b0,0x18b42c26c000080000,0x361360000400000360,0xba4004005801b88c5a,0x2001420e09a2d2b09,0x600e04d969d9cf520,0x4352ddec000080,0x41a96ef60000400000,0xb77b00002000000080,0xc00400008008c0c0d4,0x8000007206a6a5bbd,0xff3a0c0b5ade40000,0x29af6f210010001,0xd9b7f000002000000,0xbf8000010000000402,0x3000800040f02886cd,0x40000000004b66dfc2,0x8041b5733a0000,0xc030dab99d00002000,0x6d5cce80001000000e,0x674002000000078069,0x40000000004b6ee,8813735785376,0x75340b0dcb99d00002],
[0xa6e5ccec00010000,0x7ae6d8000080000000,0x6c0000400000010083,0x2000001e8061bd73,4576119591908864,0xa705cdb401000,0x838ae830000080000,0x574180000400000010,0xc00002000d91f8061c,1100032650144,717625517153,0x1008392ea84000080,0x61c975420000400000,0xbaa100002000d71f00,0xc2100000001081b0e4,0x8000000000a725d50,4512643465101312,0x341cd75e20000400,0x4e6baf18820004f002,0xdac000010000000401,0x200200024c7e020745,0x40000e570243a2ed62,41581571424256,0x4020e9bb9b00002000],
[0x74ddcd80001000000f,0xe6c00008000007c01a,0x400000000053aee,8813771453280,0x950c0e0edbb9b00002,0x8976ddcdc00df005a,0xbaeed210078000008a,0x7d4000400e9d460893,0x200000000025e177,0x49910040f1bc7000,0x9206078de38440040,0x3d3c6f1f6300800000,0x7795348004053f96b0,0xc0000200000008025e,0x1f0144951c0f0f4bcc,0xa24a901597a5e66003,0x491ccbd6f332800080,0x25ed7bf7400040382d,0xc12400002000000000,4505103184699639,0xf80a24ab00607be092,5213826654232,0x8041f182760000400,0xf8c13b00002000000],
[0x9d800010000014c03,0x800000000097c6,0x4000045a0103e704ec,37329749555200,0x4020f9c15000002000,0x7ce0a8000010000000,0x54000c780510a9c080,0x63c028854f078be70,0x1442a80585f582a00,0x15443a2fbc1500031e,0x5717e60a80018f00a2,0xf70542800080390aa4,0x46000040000000004b,0x200000298041fd8c,81583809280,0x4940207fe311800010,0x3c3ff188c000800082,0xf8c4700c7c04ae74b0,0xa0000200000000025f,0x10000000402100c63,0xa24a9808080631d000,0x4d078c0318e8018f80,0x26038c7400c7c05125,0xc63a00002000000000],
[0x48001000281dc13102,0x8000000000a81631d,4512675726835712,0xb01a2098d7a0000400,0x304c6bd80020000002,0x36a800010000019014,0x8000000000982e,0x4000000100841b1b54,0x2a00620d8daa0000,0x805306c6d500002000,0x83e36a800ba0000815,0xb54000080000000008,0x4000000100841f1,0x8192ab8ae20f8daa0,0x16858307c6d5a0002,0x2e284653e000010000,0x2b29f20000800000ce,0x80000400000000044,0x2000000080421595,5911185145365504,0xae059856542000010,0x3142f2a12000080000,0xb953200004000006e0,0x900002000000000221],
[0x1000000040210dca9,0xa24ab008086e54c800,0x59078c372a64018f80,0x261d953200c7c05125,0xca9900002000000000,0x80001000000040210f,0x800000b401887e54c,0x5396401143f2a64000,0x380a62395320037c00,0x512ca990000200006b,0x54c800010000000001,0x8000000c60188a6,0x4000006d018c532a64,46366675042304,0x402117ca9900002000,0x8be54c800010000000,0xa6401fd808f4a1e060,0x8004047a51019545f2,11328377651,0x40211bce1d00002,0x608de70e800010000,0x6f3874007f8023da1c,0x3a000040000000004c,0x27e0027db40082399c]]

def tile1 : List (List Nat) :=
[[7389143823686912,0xd403a8ee70e802000,0x547f3874000080000,0x39c3a0000400000000,0xd00002000000080424,0x7f0053e5ac06121ce1,0x45ead806190e70e803,0x6d048c8b387401bf80,0x26479c3a00dfc022f5,0xce1d00002000000000,0x800010000000402124,0x800000ce01892670e,0xa06f00cc933874000,0x800a24b9c3b1802000,0x125ce2d00010001783,0x71680001000001b801,0x8000000000892e,0x4000000100849738b4,0xf00624b9c5a0000,0xd55525ce2d00002000,0x93e716c608013cbfc7,0x724080001fffe6ebac,0x40000000005caf5,8813907982624],
[0x740312ed5c900002,0xa976ae4800010000,0xc35724000080000000,0x920000400000010084,0x20000010806261ab,0xaffc8905530d5c900,0xe70964996ae4c60801,0x5cdb6eda0800047ff,0x3b82c0000400000000,0x600002000000080427,0x10000008003139dc1,729320304640,0x10084ef7058000080,0x2277b82c0000400000,0xdc16a000202b96bb83,0xd0001015cb5e03353b,0x80abdef22429eee8b,0x12d7a2054ff78ce900,0x2a83be415000403,0x143e1f900002000000,0xfc800010000000402,0x4f80165a50060a1f,0xa00040001150f87e4,0x2801005004000800],
[0x8000a2000140100020,0x200a00800100014000,0x800020004000500,0x100100000800100004,0x4020000020004140,72059793103142912,0x100004000800020080,0x8000500200000800,0x800180014020028020,0x20004000100200a00,0x5000100004020028,0x800140100280100020,0x2000504000a004000,0x800140100280100,0xa4000001900400a004,0x480000002fffe000,0x3208000000900000,0xa004010000140008,0x800280100100000880,0x1032004000400640,0x140100280100020005,0x4008001000c8000800,0x50020020000a00201,0x1400804000028100],
[0x20050020004000a20,0x1ffff00054000000c8,0x28020028144000000,0xa08001400800100,0x800004400050020080,0x2003204001400800,0x8001000c9000190020,0x140004000a00201400,0x80400a004000800,0x50020004000a20000,0x20005100000004020,0x200000021000280100,0x110000a050001000c8,0x4008000020040280,0xa10000000801000,0x100028020050020004,0x4000a00801400800,0x804000028020050020,0x20100000a20001400,0x19040000004800050,0x640040c80100020,0x1400802000028002,0x20050020004000a10,0x100011400801000028],
[0x4000800140004000,72339069023029258,0x80a004000800140020,0x4000a04000000800,0x810000028010050020,0x20004280100800000,0x5000800004004000,90074202309132320,0x2000500010a004040,0x8000140040280100,0x10002000500010a004,0x4020000140040280,0x28010010000500400a,0xa004008000140200,0x20000a01000000810,0x801064004040050020,0x140020000100100000,0x800800004000800,0x800020004000100020,0x800000802000004000,0x4000020004000100,0x100100000800800004,0x23200019002001e140,0x380a00020005000200],
[0x200028008050020004,0x8000a00401400800,0x80000004040050020,0x140800000107ff0005,0x52000002303ffc70,0x1180800280100020,0x40005000100028001,0x1000140080280100,0xc1000000080800a004,0x4000800140400008,0xa3fff004602000a,0x2000c8100050020004,90089601934305280,0x802000004010000024,0x640080000100400000,0x19004032005000000,0x640100c80140000,0x10015e000132004040,0x8070640004003200,0x100200000810032004,0xc8000800640040000,0xc80100401402800200,0x1000040008500a0004,0xfe000500020000800],
[0x800100004000800020,0x20004000102000002,0x800100004200028,9007749015797792,0x201c00800100038008,0x8070020004000e00,0xe00201c00800100038,0x38008070020004000,0xe00201c00800100,0xe0040008001c0004,0x40380100020007001,0x800100038008000020,0x1c0040000100201c00,0x88000e004000800,9011597302302720,0x200000801000004008,0x8000020004000100,0x100200000801000004,0x64008000020040000,72092778418405632,0x2000c8008000020040,0x4000108000a00800,0x800100004008000020,0x20004000a02000000],
[0x5000100028008050,9077578737385984,0x20019001000004008,0x8000020040280500,0xe00021c00800080038,0x40008001c0004000,0x14010080000280400e,0x1050040200000a0004,0x100000100200002800,0x8040050040008000a0,0x20100140100020002,0x804000004020000,0x800640004000e00800,0xff007d004032004000,0x20000020004003203,0x5000200192000050c8,0xc8020190024000280,0x3200801402800100,0xf803e8020190020004,0x10000010002001901f,0x8001000c9000028640,0x640100c80140001402,0x780400a014000800,0x1e10003c0100200],
[0x20000784000f004008,0x80001e10003c0100,0x50020000784000f004,0x5b682b2aaa004000c0,0x150828563016b05b64,0x28a8574a2a552a8515,0xa296a9545454545454,0xa4a0b095552aaa4aa,0xcc1cdcc30870e18249,0xa0015554d515e0c1d,0xa9f9e03202a02400c0,0x33f29f1fef7fb5fb3f,0xb1ea9ea7e75e6bf35f,0x13d09d01741eb5eb3e,0x3f9bf73ed3fd3fd15d,0x89c81c77c75c6dc63a,0xedbe3a3dd3fcbfc95c,0x3dc17c15c0bc01bf7b,0x83a63bbbb75b62dbbc,0xe34b4fb4d35a9da95a,0x35a3fa33a31a21a0d9,0xb32331b2fb2d32cb3f,0xb39bd9899639615334,0x3190d8ff8eaa31f33e],
[0x632ab22be31a3193d9,0x2beabbab7a979778b7,0x29ba972b7292291a9f,0xa6f26a267a7f29ea9c,0x9fea19a1535501221e,0xf5f1fa1f48146121f1,0x1732732330143141d3,0xbf29f28328126d2610,0x3d21f201d17c97c172,0xed077b93693d15c952,0xd01701500d00aff6f,0x3e89e08f8af89f0da,0x81c01201181c83c03a,0x6c801bf7a778ff3ffc,0x439618e1761b63963c,0x959f665942458c2258,0xfe07c0f07ec8aaa,0x3c0ff81fff03f00,8972564572404751,0x7e07c00003c0ff03fe,0xc0f81ff81c000e0,0x3c0e000018181fe04,0xc000000030000003,0xfa1fc5000703000000],
[0xdfcebe61f85fbdfdeb,0xf04f7d7bd7de1eebf9,0x6bd21e8ff3b696efb7,0xf1dea6b4b581abed5e,0xa1e4ff27792bc83e40,0x77ff4b37d9a0cf967c,0x18f0cf843c1fe0af00,0x7aa9d41ee4f703b574,0x75ee572ab915eab755,0xbd14e89f407a01cffe,0x2ff977b94caa745ba2,0xbca9e44e7a7cd6e607,0x809c9ae4af1ff8e1c6,0xa6f4f78bbc4d487053,0xb94dc9f93ef9fbd5de,0x275b5ad9da26cd772b,0xd256a6b533a98d456a,0x299f5b44e96b4b3e4a,0x653ff0dd06e6366573,0xc5dc2e5572a9953ca8,0xb20d905c78fe17e8bb,0x67e2d722b914c87e43,0x5819c07f4070b38d4c,0xf3fc81d00e60600303],
[0xfb1fd3fefb57d9bec5,0x977f3cbcc5dc397fc7,0x7cdb6ed680fbdf3ef,0xcacc587dc6a9d54aaa,0x1988c2def5f3afb59,0xc18759398fbe9a2a44,0x43f70ff7c3b007c1c1,0x1801f70f61fee1e007,0x50d87c180183b0fa,0xef0e8400e0fef0fb86,0x76000001704000de1,0xf00060c00002080000,0xffcf7e79f3bf8ffe77,0xd5ff6efb73db7edaf5,0xeb8c3ce0e6f7307a81,0xcc169fb403c00e3f71,0x457a2ccf667733799a,0xd3829b94c3a9fdcf2e,0x193e49ee4c52e1971,0xdf42f9b7cd3e0e0052,0xd6c3c180685d55fb48,0xdb0741a0fa86dd87de,0xaaaa529547010207a0,0xa4401000402aa554aa],
[0x18013fa68bdd7bfd78,0x4a16941cc539483104,0xd28398a441ca41882b,0x95a507314882b16942,0xc00700fc03fa595b16,0x700fe01800f00fe01f,0xb56ce14c00d8b0c34a,0xd1505414017d4e270f,0x9edfb6e41ce6295554,0xd4cb0dbfbfd7f1f2bc,0x40819c76294a4ed3a4,0xb1ac5b0285a027f91a,0xbbceefabdef7add6fc,0x6398ba2d4a71dc37f9,0xadf17c1eb4d8fc3e8f,0x71dc36cd9f2cc9f269,0x998ac2aca71afb0e9b,0xe769d6719b66c9ae67,0x4a06809fe7c9ee7a9d,0x328ba2a89a1e86a168,0x95a5293a4690a3e8ea,0xff7f70b44863311046,0x7bfffffbfffffeff,0],
[0xfffffff00000000000,0xf5feafc1fa80280003,0x3ed9f2fe17c1fabfcf,0xd4fa7f46e8bd7f9a77,0xfe9fabf2fdaf755ea9,0xe61c9f93725e7fd7f9,0x7e6fc3f82dcd79a731,0xf06e07c079073febf5,0x71b7ebfd5f83efdb83,0x34d6babf4ae752ea0d,0xfa97506743685d03a0,0x59874de9ad75a6b3d5,0x4d5fabb536a4d41a40,0xa4039f73e67aff5aeb,0x8630af55e6b7eafd4b,0xacb582afd5065ebbf5,0xbf57e6faf55e6bc56a,0xd78acb592b055f05fb,0xff5eabcd60af75eabc,0x21541ff574ae0abeba,0x6a055fab5543a8730e,0xd59a9343a8730aa148,0x77aee14bb9b53666c4,0x5acb4957fafe5fabd1],
[0xbbef2065fcbb9752da,0x25a4ac8bfd7f2f85ea,0x34158690be1374642f,0x82b05203746e4dc1b4,0x9ab340658107e0d416,0xbe77cdf9b936a6d0d9,0x398643726d0d985fa,0xdb836b6c3f87e0f01d,0x4b683f87e0e81cc0df,0xab1960ac55c3f87a63,0x5e5fc940b7d6dad65a,0xa4728d51bcdc904a85,0xf5f4be77bfe8f91da3,0x21b43485d0120142f,0x581103097d2e6f7ddf,0x4e1243e0d02f094200,0x3c3e1df873da05e160,0x1fe37ffc3ffe1c0000,0x1c5ffe2fff0fc2000,0xf0000f0ff17ffc3e00,0xd2fff87e00001e37f0,0xe2ffc5ff87c00003f,0x5f8400030fc5ff0000,0x197de3f40000236],
[0x78cc61ab27c2000600,0x601283d00280075e2f,0x4f9314b92c4450e400,0x5605454f535435053f,0xd003fc98e539464358,0x243d0f0300a8290680,0xd40d01400fd1804a1,0x4bd2d4b1204751c44d,0x143505404fd3d4c530,0x15815d5715153d4d53,0x46438c6248460358d6,0x9ff26498e61982539,0xe82f0b42a0a419030,0x45d17059128490f43c,0xd4852043501400fe3f,0x814f535434f5314bd2,0x6094e438862080e015,0xf3b91e7f3784263986,68719472871,0xfffffff40000000000,4194303,0x3fffffffffd0000000,0xf92fe43f88fda80015,0xf5d3e8bfc2ff01fbab]]

def tile2 : List (List Nat) :=
[[0x391cde77cebf3a7ce0,0x6f1d3c60f133c1ce87,0xd7be1ef57bccf22bc7,0x92e9f3a72e987bf7ef,0x84fa01e78ff12ea73a,0xf0bfa2b995e887a1de,0xdd0f81be01f7f5df0f,0xf4edd38f4e0d40379c,0xdcc1f2fdcb87515d42,0xb3292ca2b260c90731,0xcdbf0ef6ac22366cbf,0x3831e1e78f263bfb6f,0xb31d8fe7ebb3d6ce2f,0xe7e01f3e7b90473cc6,0x8078f003e100c79823,72057595674493849,0xc2fdeff9ffcefe2ff0,0xfe5bd2de46efb7f8ff,0x96afb5f46fa2fd03e7,0x9becda66833d1ad4d6,0xd03e80aac506353381,0x57907c81e90f47fa3b,0x956c8b796fca1e4ff2,0x2bc03dffef5f45b9ad],
[0xc6adf56f2be10f07f8,0x2bcd5e4aee572ab915,0x64531a9414ee076afa,0x139e9f4539a9b94caa,0x3a77d13ca9e44efa74,0x7ff3ef9f5d55ea0f50,0x9d13e837417a03d00e,0x2ff977cbaf08f457a2,0xbe873579a9cc6e607,0x92bc80e3ff943c2191,0x7e43f01f7cfaa7f26b,0xbd3de2fa3af9d40ef2,0x5370bb84dbdef577a9,0xf056a2b49568aee5ee,0x31a90d456826d13e4a,0x6967495a40d4d6a675,0x85fa3741b70db46d2d,0x7f8bf85fa2ef1770b6,0x8363c72ab954ca9e65,0x3915c8a644f22190fc,0xa07c83e01ee0f40798,0xe607202a818d4c67f,0xf81f40f207803b81d0,0xce04f01fcbfb1fd4ff],
[0x7dbbed5f66f9f81ac0,0xeeee1f7cf9e73f3979,0xfbdfcef9f7cbbe3dd4,0xeda36b44da169f53ba,0x55033eb8f5c5afcdb6,0xf1bd8d42a9f58f2aa7,0x2ee1f31f18f3c79638,0xd673b3959419c585ec,0x7f6cf967bb3c59dece,0x421043e2bef5f6aeed,0x72147698851916378b,0x9e383c2ebb56b629e9,0xff8fcf1f83e60f83c7,0xf3c7f23ff079f83f8c,0x1f0183e08f0780e0f8,0xf19f8fe0e080fc1e3c,0x80060fc4f1e0f01c1f,0x800707e323000e0e01,0xaaaa94ab52a9e0ff00,0xc0691ed6cdedb5652b,0x6c16d0aa0341580d02,0x41ad0ada1568b6da2d,9051235581717761,0xed25d247c02b01c07c],
[0xeebecbefeeebf0bede,0xd9fdb1d71c3146beac,0xd8bd99d7ad79d9bdae,0xc49c6bc50990969d49,0xadbad9b2feafa89c29,0x98b9de9cefcef8e6f9,0xd2a98c9999ec9cf9c9,0x8798998edeade6dd6d,0x94974d00cd39869859,0x8395d962bfebbebaab,0x4af48afcaf8ad0a94a,0x469fa9e6980d4ba4ab,0x4e9a1832e7dd53490f,0x51d80838850d2a9b0e,0xe0243c021b0449ecb4,0xe0000010c6d55d0343,0x8f8bababa7c7c3e3e3,0x1b3b3757575373736f,0x5552aa555442e2ff1f,0xcfcb0018002a968a55,0xe2ff7ffb97f1bf75f9,0xafa1fcefe5cf9f7cab,0xe42f1d78e3c6de2ef0,0xfbf3df7ef4f74bc8d],
[0xe95770bb6dd93f03f8,0x3fd05e80f3d79e7cea,0x7313981cb4e5972ab9,0xb5e42f1d78e7c6be2f,0x76f7b75db36f03775b,0x316adb675b27dc2ee0,0x5a3cd1c68b3447a7dd,0x36f1a9944c9ae7e73c,0xbc82e3ff1eb8f1c74e,0x1698b0c5762a314589,0x65ea2f377f1bf4df93,0x771bb4dd6af8d7bcbd,0x72c6d621b36d996cc3,0x9e8d3ae9bb4d8aa354,0x69391a02cfd67db3d5,0x9e6c14c1ecb43d10a7,0x3e7e3e41c7e7f1c071,0x3f1fcc033c6418f9c0,0x7c00e60063801cf8e0,0x1c6b8b41a50803000c,0x4ca193f679ccc816f3,0xde1fc376ee5bbcec2d,0xfc1f737a6e0810c2f8,0xd8e71b61732e4707f4],
[0x88b0efdee3b3a259ca,0xc637c6d8cf19631c5b,0xc859072063dc798ef1,0x432664bc9591f23645,0xffffbffffdc084,0xfffff800000000000,0xc017d8bf1001fc2000,0x35baaecde9bcb3a672,0x7226d4bb175e73beb7,0x9e70be67cae99cdb96,0xd2ba5549a90ceb9d53,0x37f87d0fa0ec1d5ab5,0xbe97d142c758888dc1,0xe6fcbf87ee7dbfaff5,0xbfd3f87effd9faff3f,0xff7fcff7febfcff6fe,0xfd0481088801001fff,2164663515135,0xff8000000000000000,0x40190080028001bfff,0xf7cfbc7d53ea1f0003,0x57ca3e3df0a7e43f19,0xed3768bacbea5f50f9,0x57cbfe5df2df8f5daa],
[0xe853749ba0dc86e336,0x66ca8eaf7573ab5d46,0xf0a783ecdd66db2f59,0xd05e32e7f8bbc5be23,0xf81fc0fb4228e17b4b,0x3e07c0f81f01e0781,0xaa4a951545454d351e,0xc67e68008044294a4a,0x2d02d428ad556554c,0x1420302005b416d42d,0xe0df97a73e5c787fec,0xa00fd007f22e4c78b0,0x870a10101003c0801f,0x1ffe7bf5c7e8c16284,0x87ffdefd79edd7a71e,0xcd875faf3e3b75e9cf,0xb4e6cb930e0dfb35ea,0x9d19b2e4c7837eed7a,9004863099629398,35149995048960,0x1001517feffdf800,0x93ff768360eff2f007,0x26490c001ff2ce7619,0x16499281b603903b2f],
[0x7f80ff01fe0492667,0x64e4f3fcff01fe03fc,0x926602249264c9932,0xf73cf7b80dff7fcfc0,0x3de3800e839fe3780d,0x100200038ee03c0038,0x34ed2fffe375fd3ebf,0xfe3f7fdf840f7bdbe0,0x844ff7b9f2784f0ffd,0x60007ea80056fddd10,0x6f169e1e02440077df,0x5bc5a787800fe34da9,0x9600f0f0169e2d016a,0x38001e7f00017fd05a,0x330eddb96864210003,0xc8731c86530ffdb864,0xc308e1c3c70f0f1f3,0xbd2e0c1012322c6e0c,0x349140f38d30b8df75,0x7fe1e18e18431aa51,0x90e81b1f05d0f81f00,0x6bbbe73fdf7bbfe83d,0x5ccf71edff60cdff9f,0xa9554ddf58ce71adef],
[0x75f1f0154aa54552a8,0x3eba7df003e01d1bf9,0xa7c01f746dd7c3777e,0x1bf977e3e367df00b,0xdb50052ab2133abaf8,0x782500812bada8055a,0x16499249781e0925e0,0x458b17409149492667,0xc4ca41979ca10b1621,0x1eef0c40fbbcf6019e,0xe67dcd73180311de29,0x18a4a09ece3846291d,0x644000036dddc91ce7,0x9e01f1c82000004dce,0xc0079e003cf001e787,0x79e003cf001e7800f3,0xa952a54529cf0f3c00,0xff7783104022952a54,0xe800dc005feb38de79,0x81800ba05c02100001,0x8003e81f00f0076030,0xbe37f19fc182081020,0xcbfd83ebff5dfae7d6,0x5fa27cf7e77f38f99f],
[0x9f9cf4e79f1f78ebd4,0xded27a8fd41ea074e3,0x747ba1dc0ee87a37df,0xfe683503a5fd2dea93,0xd007fe007ffe007f,0xa1a1a1a0001c00f000,0xa5555524c9ba1a1ba1,0xa0901182201400012a,0xd1fa2f43e4fc27a904,0x9fbdf77ee7d8fd1e93,0xda794727e4dc7b8c72,0xce98d2fa6bacf58eaf,0xc4588704e14da7b4b6,0x76ce593ca59a312623,0x51da1f73ae6de8b3d6,0x9b526b4527a4d48e8f,0x65449e93b27247d4ea,0x238330620bc099913a,0xae52274498911a213c,0xe1be7728e4dc938e71,0x864ec998f31d638c11,0xa3544a8853ad11a1b6,0xea245a6bfd7f2e6538,0x4fc9a51422744c8790],
[0x98d19a2342624c41bf,0x7cff9df38fd1f93d06,0xf25a7f47defbbf73ec,0x11822031d5faf17a2,0x93f47b8b6a6d3da5b9,0xdc5329e52cc7e8bd0f,0xe75cdbd3ca393f26e3,0x8d2faa2ef5dcbb173e,0x84f07d4ea9b526bfd5,0x4cc89d189311e22c43,0x8bf67aced9cb2933a6,0x768cd2389d12a24c48,0xbc4786fa694527a4d4,0x88d0daf49d939279e4,0xd7f2e784d0620bc276,0x53724e35d1ae25a8bf,0xec998f31d638cfd3f2,0xac28d510a84fd1f93c,0x134e8990721e2f45e4,0x67154430d02204111a,0x37ecc2f0aa26c861e4,0x70f03f0f81fc00fef2,0xf8781f8703c303f0e0,0xe1c0fc303f0f03f0c0],
[0x583fc2c1fc183f0d83,0x303f87c0e1e07c3818,0x3c3f03e1e0787e07a,0x702c7c06381d8f0387,0x800ffbfb400600702c,0x2beabbc7cbf55f6ff6,0x77a6defe9f93da7d5f,0xa5d57af34d6dbd79bf,0x8aab40000ec66b6576,0xdbebf4e38180a01000,0x5050500803c07c7dbf,0xca2505050550505050,0x640600006664cccccc,0x799f31e2bce01b0340,0x3bc7fef7d5fa9f4fed,0x7a7f4eec3c838ff1ee,0xcad93b4347e8ed3dd5,0xf86b0ce18c1786b6ce,0xcb595b2964ec5649cb,0x5b9f71ae2dc4bb3662,0x47a8ed15a294428351,0xa49390b512a0560a3f,0x995306604ff9e13564,0x7a07c0e81306a6cccb],
[0x389708e6a2047f8bf0,0x2ac5189b15780fe9e5,0xd42a8457eae9af31d6,0x1d42686565af55baa3,0x7c0ec99836a97d0f2,0xeffd5fa9f4fe87c6fb,0xe9fd54aa14e2e0587,0x640600102bd53a8f5,0x56c9d83b800e01b034,0xcbfe6bccf98f15e2f6,0x7b8ef14e1fc2f25649,0xdd0b8f71ae25f0bbfc,0x8b512a0550d1fa3b4a,0x70c614c1782b04e06a,0x8b9833026fe1bc3586,0x71162047f8bf652c9d,0xfd3dfa3d46a8dc5989,0xf81d07daac94927205,0xe6965aca5bf07a0d40,0x83194ea929c4b85708,0x3e07798eb15628c4d8,0x15fa91396718e09fb,0x21d42a8510a946288a,0x3e668cc99830067d0f],
[0x87e1a6551163409012,0xfbe8e8358c0abca023,0x7c3c0e1e07c3e07801,0x3f60e1c0ff0f81f860,0xc341e841f0d070d07c,0xc3f81f0e83f8506083,0xff03c381f47c0e1f03,0x87c087028e07d1c0e1,0x3e061a0f63f028f03,0xf8d8d6b8807a4001f0,0x827e5e423fc3831d16,0x3ff611f02fedec2,0x45821f0d803ff60000,0x7a3b1c8bc4a22f278b,0xff8000f808fe73190c,0xd80036000d80280007,0x1505b6000d80036000,0x74cd8f8ae87c8f8008,0x49ae82aa6c0b9f0ec9,0x4f3ad4778e7fb6f77f,0x8296670a5ebeb56fcc,0x29294a4a529494a52a,0x2e99b1f15d0f91f001,0xe935d0554d8173e1d9],
[0x89e75a8ef1cff6deef,0x5052cce14bd7d6adf9,0x252529494a529294a5,0x74e6c3e15d47cc7c00,0xe8e5fdf7f5d07c1d95,0x33deb2decc679eb50e,0xc014aad4a2ad5c0295,0x975f0007cf975f0007,0x1745c00f965e1f06ce,0x85cfe6df04c6c7cf9d,0xcf8ee007d55f67200d,0x473f000ff7af974007,0x473f000fe6c7d7bf77,0x15a6c7d7ae8f9f77,0xee006d6ae9f76575f,0xd5a6ce853657473e1f,0xc00d87de76463e0ee5,0x375e1f06de75575f05,0x5c6cd87dd6e8f9646,0x4df0ffd6e95565e1f,0xfe6cd97ae95565d1e,0xd4afe6cd97acfe04df,0xf7ae955f764ce73e04,0x5f765d073e04cee5cf],
[0x3e04cee5cff6ad97b5,0x24cee5cff6ad97bf67,0xe00ff6b7be755f6627,0xb7be755f663d072dee,0x7e7f662de4cef5aff6,0x852624cee015b6a7dd,0xbd77bf6637472de00f,0xdd7e65364cedeef5b6,0x7e7646374ce73f14a7,0x4cedf4a01d6cf4aefd,0xa015a7dd6e8f852637,0x6f8cff14bd662cedf4,0x452cff14a5cfe6cd9d,0x4cfe1f14a5c6dd6e95,0xaeefee9646ce955f76,0xbe7f673e0fed965e14,0x663d0fed9e6625d6b7,0x7d0724cee00ff7b55f,0xf5affd662de4d6b7be,0x7e672df4aefe653f6c,0xff0ee006c7de6f8dfd,0x463e06d6ae9e6f974c,0xd55d0cfe05c00d8e96,0x37afecff0ffd64df07]]

def tile3 : List (List Nat) :=
[[0x6ff7bf672ff7b7afe7,0xb6be652ef5b6be7f7f,0x2dfe76be65262deef5,0xa40b0cf4bd6cedfd66,0xa584a212720e3a0668,0x1820c3d873cda1982f,0x3608b655ba904da92d,0x800000017d4ec1afb2,0x29330a548992004c00,0xc9524080201010001,0xaa69b5ab36a59a5249,0xb5b5aa8c9ccb2d956b,0x6d35b6b516b5aad4d4,0xd5b6b55b56b4adad5b,0x995aaab36a1a5ad59a,0xaa4c4ab56d6b11315b,0xaa944b49095aba6c9d,0x1a8c931535a568a512,0x93594c956675310a56,0x20410408002500214,0x34aa615280424a2400,0x20024004401092081,0x881001e02c028020,0x1f03c06c0d01902c05],
[0x40a41402504808c100,0x28010000b81682b05,0x50280440800a00e018,0x7c0f01b0340640b01,0x582905009812824046,0xffb32b0802f05c0b41,0xc0000000000000ffff,0xa00c01400800ffffff,0x580a81001e0300580,0x202304007c0f01a032,0xff60a81482804c0941,0x500800f01602802801,0x81e0360680c81602a0,0x520a0128240460800f,0x3fffffab0802a0,0x2003ffffe800000000,0x586c14090401c0c050,0x5aed167b3596c963b1,0x301408030100401ff6,0x28d44a150502410070,0x53156a95429d4ca552,0x9fcbe3f0f7fbbdbecf,0x59acb64b1d8ac37f4f,0x5fabd3e865aed569b4],
[0x9fcbe3f0f7fbbdbecf,0x29548a35128540bf4f,0x790020b552a550a753,0x80000000ffffd609f3,0xfeffc00000007ffffe,0x1ffefff80000000f,0xa02eb61e3fc50b051f,0xa3c09c4820041ad464,0x80c320ee675bb5dc9,0x92c9786e3ff55feff5,0x48cb3d9ac067a95545,0x8d6eb353389bcf67f1,0xe8702ff2fc7dff3a,0x4783edacdd31848221,0xfd96ff616fb6d828af,0x90470c02e197777a1b,0xd0c5c51a2820510ab4,0xd1641c28087b1b1b01,0xb25f3ffbbdbeaf0032,0x8f369c5619ce32f168,0x14a65007030371b69b,0xe0f678456351642a11,0xd384c03fdfcfa7cbd1,0xeff9fc7dfe9f3fa58e],
[0xdbd8ebf5bb3dee97c7,0x64b35e375b8d26e934,0x6d259249a8340a62ed,0x2b90df6d769b3db6ff,0x75e574d2b2b94c9e5b,0xc44302206e04f06f6,0x3d4d7ac0d7e855c0d4,0x552fb17ab838e85c41,0x9555555552a965a2a5,0x84400d11108a024aaa,0x46442356881a11e228,0x5635834441ad107544,0xe90403e86b3a9f18f3,0xe10000f39c93cc312b,0xd7000017d7d7cf39fa,0x492da84a89375ad759,0x89555548a00022aaaa,0x54458f4f4768eb08ea,0x7eea8000037bedaa1f,0x6aa80aad554a55ff81,0x5b40741b27489fa95b,0x2f2010c49aa9106aed,0x22aaa554ac486df72f,0x1a856453f6ec9c36c0],
[0x18d3c632f2bf3da45a,0x73de5510c493633674,0x1f00c13f9f4014055,0xa7c9b5d7c3e5d1f3e0,0x736f817d9f8bad99bb,0x8a9937493557436551,0x45294a314a5294a52,0xf3e1f7c6cfc3e1f000,0xf3e1f610bc21f425d1,0xf9f61421f6ce142519,0x1aefc00425180421f0,0x10fd1d1e12e8b805d5,0xbc22e8bcdfc519f6,0x5d00708be17c00518,0xd6cdd5d5d1f2efc5d0,0xc9228409000d7402f9,0xb66b52a2a56592aa2,0x2152490c59214a89a5,0xf610050aa95884,0x5aad3c008f1e3c5a3c,0x25b40796e9ad7800cb,0x1e005a78e93c96433c,0xad3c00cb1e00cb3c8f,0xcb1e8f008fe9ad3c00],
[0x8f00e95ae95ae9433c,0x8f5a1ead00cb3c1e1e,0x3c96cbe978005ae9cb,0xe9b4b47896b4ad785a,0x8fb40043070025b443,0x5a3c5aad3c001e4300,0xad78963c8f1ee9cb8f,0x80881b4396e9073c5a,0xb5edda8cb9184a0419,0x54d9579d2a8d005256,0xa324d7512eaf6a9285,0xac10195a8317575a33,0xae192e22edf94292aa,0x9200f6a68021c43fd7,0x80604020015554532,0xc1d9cde9e7e5e3fdec,0x9f8daba9bdadcbc7c5,0x456175736d8b898381,0x494745435f59575553,0xd2b29272523212d4b,0xed0b09070503011b13,0xcac8c4c0dcd6cce4fc,0x82809288a4a0beb8ac,0x648c68646260746884],
[0x7d007d007fa548ecb,0xc00fdf006c01f401d0,0x1d803ec01a00fec01f,0x7b0124855a5fa00f40,0xdc7600f7db880f7d80,0x3e201efb71d99c07be,0xe3b33e2ba03df6e3b3,0x3df6e3b33e2ba03df6,0x3f7db8eccf8aed8a60,0x76c53edc7667c576c5,0xeccf8aed8a7c7667c5,0x14f15db14f3e2bb629,0x74f9fcae37a7629ddb,0x2f80bc05c0580a02c,0x1ff00017f017f017e,0x807807c03f00fe01fe,0xa28020f1863100c03,0xe05c3f038fbe9158b4,0x8a80e50af053c52e02,0x3274e5dd2bba577052,0xfcabb132ee65d89977,0x97974a70f05ce5ee5e,0x72ee95c5472e6e50d3,0xc4cbb132e16e29cbb3],
[0x8a4782f6217d88435,0xd594351408a708516,0x735da39f751cd108e5,0xd87dc59aec45974d34,0xd686c28d6256788c45,0x48e3eef0cc5defb2ac,0x420cc1d36924c94810,0x29c99a307c9ba6094a,0xb053deeab76d030ab5,0x1485144036751329c5,0xc98b8a28a422a48905,0x59adb4535953b1b2d2,0x6a6d5d369ba6d34db3,0x66abb559b66a5aba6a,0x4ecbb9b4dd36566dab,0xee6d9b66eadab66d97,0x34b8b57756969bb36c,0x2a4916c53468a6a51a,0x5094508860114428d0,0xd49c65110808421480,0xe4ca790a542a994b85,0x5623113997732ecaec,0x951c2e94b86f12f62,0xf66e5dd39ae4e52a39],
[0x8997626422dc1cbc74,0x835313c10dec437b2f,0x545850a399ab084151,0x780b8c239a94e7d17c,0x462311bf016bc6a0cd,0xb19bdfc7995555883a,0x60142400c41e46843d,0x316b7aa098a287b1b6,0x15012880c74fb392d3,0x96951969518b2a0482,0xb2d353a9a34a9b4d95,0xb73356cdd565daba94,0xb34769da6969ba6aac,0xd369aae946d96ac54e,0x23a30c5d36363b95cd,0x85184286219430d229,0xaa5848600200240288,0x229555554aaaaaaaaa,0xa7c02e86df374fa7c0,0xa7e5fe166e86df374f,0x80006b6a25fe1646cf,0x6e9f4f805a50002dad,0xdbe6e9f4f805d0dbe,0xdee9f4f804bfc2cdd],
[0x5b0000d6d44bfc2cdd,0x7767c9f005b360005b,0xdf1ba3ecfc00c31b3e,0x167751b3e7e2b2ba0d,0x7c00dc01eee01be47c,0x7cb77ba000ba06fba2,0x27e3e67d973e13e8fb,0x5dd003f8b75003e059,0xb67c599f359c037c16,0xf8f8eeb1b27f592e81,0x97c6d3e25ff8aeadd8,0x167ba9f09786cbadf1,0xd954c497fe359ae997,0xa5899a0cd04031861d,0x170d954b2ccb8b4a2,0x90002080001060000,0x8000e0a000a0a0006,0x50014070013080012,0x60019050016060015,0x4001e03001d03001c,0x7002205002007001f,0xa002a090027090024,0x70041060040080035,0x50044040043040042],
[0x5004a050048050046,0x6005002004e04004c,0x4005a070054040052,0x80062020061020060,0x1006e040068010065,0x5008005007a050074,0x40084070082030081,0x3009402008d050086,0x4009f070098030096,0x500ac0100a90300a6,0x100c40300ba0200b3,0x900f60200e20900ce,0x4012a08011e02010a,0x24a28924618000,0x9939300ec000000000,1401221,0x38d30208930f380d00,0xb006057c438b202107,0x34165564453d455140,0xd23d02cc5544824548,0x2920da595d54d23964,0x5146145131d35dc5d4,0x32c00053544448500d,0x3147c54cf18000745],
[0xdc8175053986d35850,0x44a28f5d54861c2434,0x91d5de85850c356695,0x76d64ce21975b69429,0x800893925088e01051,0x254073d45020884564,0x69c6831515575ce085,0x214541864a48503392,0xdad665a5d128f49261,0x185910d459d7190cd2,0x28b34c7b00b4135,0x8402cc18000624c300,0x30018c40e34700033,0x3cd28d641c00ca3d,0x9250d34b00c28b2860,0x2c908b3d134f007381,0x51548e9e0031cd44c,1,244889500580,0x8410f260000000000,0x40071c61c61c4,0xa2c920c2092083d800,0xc308fc30000001c024,0x811030c31041030c40],
[0x1041030c41043fd030,0x4110241030c3041003,2147084,0x870c508000040dc000,0x1506c0000051c61471,26807140114821,0x105186145429830c2,0xd0c500000000000000,3120,857843271991296,0xd7000000000000000,1301,0x38f4384000000,0xfe0000000000000000,0x1851440c71c6186150,0x518645506103187,0x500000000000000000,0x618114a2051c30516,0x620746f0604120b2,0,0xd38b28830930c211d1,0x8c38f4a1082ce38e24,0xd30d34e2cb34b38b2,13106230451],
[0xb28a4dc00000000000,0xc34d40a28b2cb24c2c,0x4934a28a28b354252c,0x30e5378929030f34b3,12,0xa50f45038a0d504000,0xc95704208331250c3c,0x892471cf44d3d13124,0x1543c534e356953172,0xf5e38d4dd1d158c5d6,0xb59b30c5c925528914,0x7458253418810d645,0x6601960a1433937d43,0x3912c359790e48d4ce,0x30ce40735a791c548f,0xcd0d48e34730f4530c,0xca4470973ca14d0cf6,0xcf5dc41be63831d33,0x25b7d740b1d8417310,0x748d24581d60d3c774,0x775351e0c3c91d061,0x8089948d40a5632523,0x1860c70861060047ca,0x40850df66080102086],
[0x31030821001020c20c,0x871000c21041047e50,0xc221fd61062031070,0x1c21c6242184082182,0x610708210018280702,0xc60a05518610008408,0x61020c30081091840,0xc4140186003824400,0x1e0c4105003083103,0x414410400010308408,0x831000c618083c4200,0xe1301c81000821861,0xc41040020082070c7,0x1840c710885b430c2,0xe1bf0071461871c618,139897349216,0x38e24b00187d000000,0x23100000000000000c,1117031318034,0x440020028934000000,0x5a0000000000000040,0x142183182144104122,0x50821c08a746006106,768],
[0x20020c00c51061a2b,0x21808b9450070061,16386,0x41451040c6105122f3,0x21408ce4500610518,131153,0xc01411420000634b0,0x1008dc440061410c2,1296,0x800000000637e00,0x408e1400030000400,0,0x10410410410a386000,0x808e60100204104204,268502032,0xc20431470e39e0000,0x18f2040430c4001080,18163553026060,0x80063d900000,0x8f9420420410400400,4467856769155,0x31851450e3ef000000,0xa430410431851430c,0xc10031400011830c19]]

def tile4 : List (List Nat) :=
[[0xc30401a44a0030430,0xc31ca043185043005,0x90c304300300114392,0xc30c3064b00030c11c,0xc32430031461c50010,0x1c71430c30c5939,0x410650b000000000,279172874244,37956,0x25120400000000,0x41001040041041000,0x1000000040000946c1,0x252000000100104,0x400000000000010400,0x40000081948c00,0x20a527000000000000,0,17872633856,0x2e52e0000000000000,0x1842c9007104188106,0xe2c624a10a96447108,0xe62438634f1083041c,0x628f3852ce1093461,41431334912],
[0x698000000001000040,0x4100104000100002,0x410009a7c000104,0xa40000000010410000,281474993487910,72068217639534592,0x804000000000000000,70368744178282,0x400009aac00010010,0x42043000001000000,0x40000000026b4,0x9ae0004004100,0,158592,0x9ae00000000000,0,2537472,0x9ae000000000000,0,40599552,0x9ae0000000000000,0,0x1020020c20a6b80000,0x9b6020c0082083081],
[0x20c108208008208000,0x2042082026ed08004,0x9c1800c20000c20c30,0xc30000020020000c0,74362338282573952,0xcac208300108008300,3332894621753,0x40027330000000,0xd40000000000000040,0x20c00000000009c,0x10000273a00000000,0x800000000400000020,281474976975311,690562021720128,0x100000008000000000,236816,0x61a7470000000000,0,136959168,0xc71a75700000000000,0x862071492071c51871,5479795825,0x20e7ce000000000000,0x20840840c40410820c],
[69423956492,0xe7fc0000000000000,0xc30c30c30c20c30c3,0x10420830c2a09c2081,0xe84a0420830c20830c,0x820c30c20840c30810,0x420420c2a1d030c30,0x8970430820830c4082,0x30c30c20030c30820a,0xc20820c2a2f4308304,0xd10000000000000c30,40,0x1001042a3440000000,0x900000000104100000,0x40001000000000028d,0xa37010000000,0x41040040041041040,0x1040000001041028e5,0xa3bc004104104,0x410000000010000410,0x1042000001028f40,0xa3e40000000000,0,0x42082042068f900],
[0xa41000000000000,0,0x810820830e904000,0xa45c000004004008,0,0x1c00c30000e9170000,0x3a54c50c60c31c3149,0x91c31430c61c30c60c,0x861891861a99f1860c,0xa7f031461861861841,0x148147245246187248,0x51891c31aa670c71c6,0xb60720924618720920,0xc71481431461c81c7a,882581181045857,0x280000000000000000,0x2041081041041041ad,0x4108106b5e08108104,0x10410810410410410,0x81042042082041adc,0x20820ab86041081041,0x108204104208208208,0x82081042082042ae88,0x820abbe0820820420],
[0x82042082082041081,69924482,0xc30ebdd00000000000,32,11509760,0x2be8000000000000,0,184156160,0x2be80000000000000,0,2946498560,0xebe800000000000000,0x821030851050c50,47303360512,0xc0e000000000000000,2,756853768192,0xe0000000000000000,44,0xb0380000000,0xe00000000000000000,704,0x81041b03800000000,16777345],
[11287,0xb05c000000000,0,180592,0xb05c0000000000,0,2889472,0xb05c00000000000,0,0x4200000102c17000,0xb06c000000000000,0,739966976,0xb06c0000000000000,0,11839471616,0xb06c00000000000000,0,189431545856,0x6c000000000000000,11,3030904733696,0x6c0000000000000000,176],
[48494475739136,1024,2823,775980331302912,0,45168,0x2c1c0000000000,0,722688,0x2c1c00000000000,0,11563008,0x2c1c000000000000,0,185008128,0x2c1c0000000000000,0x10a3493400ca2c8303,827620081664,0x2c8300000000000000,0x94092440071cf1c00,35850989600768,0xce7000000000000000,0x30e0022c030e20902,777187819520],
[0x3d0000000000000000,0x1d848d4001d33904ad,0x1c0000b851140c384,0x52870000000000021c,0x153cf38e00951536e3,0xbc2d434d30e0,0x10e0040000000001c8,0x22d63cc2833d152f30,0xbf94040f1472c,0xd22840000000000060,0x1248744e10e5b0162,0x70c2c314020e489300,0x148c1880000000030c,0x135474cd0c05b11f2d,0x84c73800124c43510,0x3521c3000000000347,0x34cf40f4442323450f,0xcb44000050a19020,0x4b24600000000000e2,0x260f3c0033270115,0xace8c41020cb509303,1099511627828,0x41041040033be00000,0xcf2010000010410400],
[64,0x1041040033c9000000,0xf48000000104104100,28,0x41041033d30000000,0x700040000041001040,207,0x41041073dc00000000,0x410410410420410800,3323,0x1082073ee040000000,0x104104100208104100,70368744230912,0x41074030410000000,0x81041040042042041,17592186897664,0x10741600100000000,0x410410400020410400,281544783595520,0xb42b041041041000,0x204104100204104100,71485654712320,0x74420420410010000,0x41001041081081041],
[17870574583808,0x345800104108100000,0x420410410000810400,4523024253952,0x467000000000000000,0xe3443401d224b24403,282382758314024,0xdb0000000000000000,0x38b30800b31028a034,9074638882603022,0x300000000000000000,0x8e28924239128c2356,0xd76800000003,0x3080000000000000,0x550b2c20cd30a275df,0x8d9d4930308031,0xcb1000000000080000,0x45728b20438f2769f2,0xdd20444b20010e,0x300000000000000000,0x503cb20324a3b74e0c,0xdf5c028a1c70004,0x1c3000000000000000,0x14cb24a0862f7ee109],
[0xe1b8010f24228301,0xc91020000000000000,0x50339130a3b8971c82,0xe4b430054062cc007,0xb08900000000000300,0x8d54e4802796f31034,0xe82c800028f3cf1003,0x3021c0000000004304,0x738a31213a5a20a2c9,0xbe0724300c38f3120c,69793222670,0x4004103b040000000,0x340000041041000002,236,0x4204103b0d00000000,0x800400010410410020,265926,0x104103b1b000000000,274945015812,60548,0x4107b230010400000,0x40040042041040042,72057594039946369,0x4103b3704104000000],
[0x800400410820410400,15538192,0x10bb46000000000000,0x104100008108100104,248856580,0x7b570010010000000,0x40040002081001040,3985113089,0x7b6804104104100000,0x810410010800410410,281538826666000,0xb7d002041001000000,0x104104004108208007,72491264376836,0x930400010410400000,0x4204200104108107b,0x40ee8c1040001,0x400000000000000000,0x872462442041c303ba,0x2441c6f030718a2491,0x24c1ca1c5184186000,0x1830c324730a27c6e,0xc60c2f33c320a1c700,0xc01820000801072482],
[0x2c30052491c82bd0e0,0x6249f5948080087006,0x424a1000001c728600,0x32862000820fdba10,0x80f7e402052860000,0x80000206283082180,0x8218520003e331ca,0x6f98061c700000008,0x880c00000002c40000,283443068929,0x2fa840000000000247,4646845850583060,0x4000004003ed000000,0xfb8020420810410820,0x41040000000040042,0x820810beee082081,0xbf8008204200000000,72602404061199,0x8100107f080000010,0x4c0000001002080001,0x41040002080fc,0x4000003f1e00008200,0x400820820000000800,0x81080000000040fca],
[0x204003f32081000000,0x104000000000000000,0x81000001fcdc,0x103f3e0000810000,2181038080,0x2081041000000fd0c0,0xe298000000000008,0x54393638c2b8014964,0xff49e99afc48230b90,0x98b908cfc48230a70,0xad7fdd22fc48c08bb0,0x4975df4928238bb002,0x46b2ee8c08a701e92,0xaa889620cc05f001ab,0xc932180c043830e0c6,0xaec400cc04b008830c,0xc00048121106741c7a,0x955135f25240400cc4,0x99a4217be95945eed7,0x13352006b5ec6ad36c,0xe81158408faaf69000,0x5cac6e646252271aae,0x93f5ffc0200cc8c005,0x5dca393fd59aabdafe],
[0xc640746398bb494275,0x109d5f5bfffa40400c,0x30c5bcb5a31d96bd62,0x200b3804e03db3abc8,0x24ccb466b5af99e777,0x4f007a444299ec4ac,0x180d6c07eb6990680c,0x251078340470f0bd02,0xd0ac4a0a280ab80f9,0x14c0556c7440207d8,0x611803eb0788038092,0x14803d703d7161002,0x429026402cd9700604,0x72552302411017800,0x900b4c3001a0440488,0xb819f805501cb524c0,0x4604d1181013080801,0x301405c00210200b0,0x908044041025a00b48,0xa005100707f80335dc,0x33b014f015eabf2006,0x83820401a0b0560170,0x2d1321a10158005007,0xa00321d0247a047805]]

def tile5 : List (List Nat) :=
[[0x6e09980a680aaf5fa0,0x2ff056a017b0058bc5,0xc5e09844e0290c0727,0xffdf40401d4ba07813,0x623b3190097b8bc07,0xf02f51d0124433542d,0x3230063c94076ad27d,0xd6500381c30471481e,0xec01280dba5705767,0x1f3043d641e0904f0,0x2016bffe8018bc5020,0x602a10a1e41f03e027,0xa80acb5d482400012,0x82f683a553cb1301e1,0x7ab5211000600ccc42,0x14a100805b11501af6,0x1090a0036121a1fc15,0x2b01f030044411f561,0x605111d18ce188010f,0x1012370804bd69000,0x5a0a62380c6f025e03,0x6eca4010030a90000f,0xc0215c1d806e03a809,0x5aeab0161429d000cd],
[0x8a85d801602861ec0f,0xebaeb57ad000a00092,0xd81ec42405a1da057,0xc1808058e001c8346c,0x1e0a03e78e102b48b7,0xf5d81500408b45f033,0xe021002300de93a00b,0x87403c419adf59862,0xb7dc1684049002c328,0x41ac541b81601e00cd,0x81faefa0005305302e,0x5060318e84f023203d,0x1dd1340ffdbaf5a020,0x15d0460103902a3170,0x415c815e422f02018,0x20120d5061180c5c07,0xde804f135c2210d68,0xcd030a982c07617001,0xd0c7aa0af5f81a0468,0xb03360e481701f5004,0x130ad0369adce00bd6,0x600390242a0b940130,0x55607f67e80014bea,0xa693321abe078780e9],
[0x606bd2faef402d0aa0,0x7424812861203ea433,0xfe81c00d6ca0062573,0xffc0fa7418ebd07d52,0x60190648c5f0eb0153,0x35e0af9125c0e12d6a,0xe0a8018750b0149829,0x2f58600b14678c418c,0x1d1c07d41f27efaa1,0xef5a80a7658046847,0xb0e000cde7c019635a,0x50a0a404f7feaee00b,0x113e361c206d0c0c0,0xb057daf480002ba2a0,0xce03c3030188e10211,0x800d67e0099c11b0d2,0xe22a3fd52415f7feae,0xc0bc205c18ea17d81a,0x1d64a0040be0c25080,0x19c3f86093bdfc201,0x48813a107a81387f17,0xa44a801acf58207c2b,0x814099f01a480f886f,0xc100d6003d6401a885],
[0x535eba007aed9d001,0x794c6839d80c0e02d,0x3ffeada00b632001bf,0xfdc01090fe02036505,0x80169b5260065a341e,0xe61190090fc21675fe,0x6d3ce0e8c5cb830280,0x8088fa3dc59ffff3f6,0x423111f00c80fd18a,0x5ffae09f58603e1b72,0xc4602501629e03f39e,0x680bd7300ad5c12020,0x501d06603c2a08c230,0xd67005a925d02a7202,0x81322601e224200793,0x6e0608ab5004700f5a,0x8082d8217ba009073c,0x4a010caf8bc805b000,0x8c484657bc06c62208,0xa2aca2f4ae68116450,0xc02e34e0fa401e0ac0,0x3a02fcbb805c00003e,0xcb9804b00123a40320,0x892dc00205634720af],
[0xab00b00163ce304731,0xd680f80844c05b2a2c,0xb6a700a406182c3a3a,0xd600dcc100440f8802,0x63723c0eb04bb2ea50,0x130910248a8691cf01,0xc519e2102c1425b040,0x80160da918230f2601,0x2f2bbe01e02a000280,0x132d806012e37000c3,0x437b00302c0a020488,0x32f3700608ac2e0e0a,0x48f00d0f85414780ac,0x1e0032888cb41e61f,0x1a9f09c194b40230c0,0x4aca1f14401810944a,0xbd005901944451941,0x580101c2b53a44020,0x1330781602ec2aa002,0x40380c005805cae386,0xc48312a0047a049c,0x2005500000b54006,0xa1f807c194320a85af,0x8a60044c4114b41e43],
[0x1d0986e1f1560121eb,0xb2f053e7088f45a01a,0xbaca80202ea0226dc4,0x1719e79d05ac31e1ed,0xe025f2820b88ae220,0x200c5082068ac52385,0x143e0d622ec624c029,0x1701020c5c04c6081c,0xc45813182e0310888,0xdc052222bb60700f10,0x6862ec0e40a780249c,0x4bc804bb28360d022c,0xaecbcae5306580132a,0xab8584e01f04706235,0x9ea02807f002a32981,0x4c7e3c48058106c23,0x9f0071032ca8cdc8a,0x80a921381b39804028,0x484010a8b9815ac2ba,0x8cc07b1a036805419c,0x458383808601b3b03,0x503ac00c60700e0308,0x200ca64bc006ba9802,0x9365808012e49001a0],
[0x651636d03e01200d81,0x6345b9acbc007d001,0x203d43987a018d40b6,0x7b80a021200f202ac3,0x17128e0f051020d94e,0x9202111026017f0b70,0xb10000280970008a84,0x4e2038a12d0020ad,0x35818d85047c19929,0x45e80c500994e0381c,0xca4bc2e8b9b80063,0x4022e37002603d01c7,0xc1a83f01629936580,0xc2e0002194304e0301,0xb191cd81882601804b,0xa7282603f920a67ee0,0xba00602ea077029524,0x4e9e37412329a3cbb6,0xf8022a7b501099782,0x284c54ec0a6c4d2a62,0xc0d18e0400a0252001,0x15a2c1bc41b4f12886,0x61e98ac604a99183f0,0x1e0396001426041],
[0x4178284764a40c8894,0x262b898c140a8e6032,0x700900481406280861,0x65aec022e9100dcdd2,0x1013c1b609810d8193,0x6b862002401409c4,0x10b292f40a16e9f601,0x5258093f5705d3d760,0x180402ca013388632,0x3f086a72948f81b3b6,0x9c51252b80a49c7055,0x100802ca009d94048,0xb1d989eda720086ce6,0x6574825c4056483996,0x2039a06708c9046602,0xc182222b03d08a0400,0x94b87164425380d507,0xc0c2058c8cc8456146,0x95ae6b92e210052402,0x3015033f40118d405a,0x4050b2655804b9ae1,0x1e39424680cb002030,0xae7b226ba804019a0,0x2c072261d73892105c],
[0x100802ce0a248428e,0x46259824480b84d6e6,0x55a894c10a8c07ec16,0x30f4379e068b72481,0x6921112665681c9a6,0x1a11952a460e63c30c,0x42f0113c8040081f50,0x211202084e500b2191,0x3f300007802b02f83,0x136d42017005830c33,0xf2c01b03ccefabe910,0x683a301287022c2c1,0xb81e97be8fa8a002d8,0x8027b605507f5ee404,0x5c03bac9609e104b8c,0x4d4c09a5202c812839,0x4d5006a0042000601,0x68c01b03bf4f93e6f0,0x1c581e28c30b78b80c,0x6a87e01e27be4f9860,0x8f0e038502365a90f8,0x24827cba501cb00902,0xf05c0a86e0d491b805,0x42000201cd4c240880],
[0x8be09004d504d55080,0x344180a5c01b032bef,0x7003c4502b00f009f7,0x1af2200c8189ef83e3,0x2813838d01930f9c9c,0x24c0580427a301006,0x4d44c1400080ec0b26,0x18053560c38000601,0xe00acac0ad3804d500,0x903d00c3e00202b858,0x1e3d803207bdead3dd,0x130fa0b162c5ce588c,0x28ac4878200dd80e0e,0x4180103dcdac01902b,0xf901e1e20a444ca78,0x256240e01cd528920,0x2a0a40a2503afad318,0x8180401cd4d004bef0,0x1b83180d9d8c052a82,0x535200278073560378,0xc81ef5ab6ad22000,0x316ae8a524df82e28e,0xa4dc05082a906934a,0x5a00c81eb02b4adda0],
[0xda52c1a0e41a4bfcae,0xbeaa40c204e8292107,0x4fb06eb0067b3a004,0xb01a02e89aaaf93807,0x907d454071302930,0x16296cc180401cd550,0x33c0920cfe03c47250,0x12c07d40018053538,0xd000535204a00fc02f,0x8a7e803602bd0adabe,0x11606896073a942317,0x19016afbd0ad8e06c,0xc2514680834103f034,0xe0523e0782220f2c14,0xfc0786941e6a2c46e0,0xd8312c143681d6f2f,0xc01cd4b003e0f1406c,0x602995fe03c3e5053a,0x4c00eb00535605f81f,0x2bcadbcc1068051acd,0x165333680f01ec0420,0xaf2b6f30e03481e2f8,0xc4e6d7c0ff8806c0e,0x1e02712831c08c5a03],
[0xbbf805804279911072,0xd880bc070703036034,0x905081006014d49003,0x581183640c6019ef81,0x901ee822780735780d,0xcd5c01c82ac0178021,0x301280aa8036080401,0x107e017c074d4ae2b4,0xd0a007036c0a538884,0x81d3c700c81eacab8a,0x62081008611298823c,0x16012c2aea20f0a04c,0xa0e80f314ac402c078,0x2d06dc28c447010ad,0xcb0627aba01ce00f95,0xd01301e9f7ad6b840f,0x4681a58903783bc41,0x81697fc201cd4011e0,0x202780cc697ac9804,0x20180535181e240fa0,0x521f003807900f207c,0x3a06aeabeac8e00053,0x8e0942622980f88ea0,0x1d60c88481b0d8432],
[0xe0a69e1eaebacafca0,0x425395b0127f71db02,0x5f04a80a90dc66ce38,0x41b58601804afd200d,0x2c2e80ecd7aacf860a,0xcf8181c0f2c040c31c,0x4735006011e0520755,0xc057846bdb90b40b67,0xd4f057a3046819b06b,0x5115900603858f0014,0x41037c18f01600300,0x2abcad2b27001b352,0x24da07931a13758036,0x87ab4af2b3d002e0,0xc4c64268a101a7872,0x8af1203c1f0a814814,0x5cbd34dc0ac31e332b,0xe09b01d0692118ab01,0x11abc0100770096052,0xd54090e480e63a0903,0xeeb4d5304f02b82640,0xa800e01c9e1e02a5ba,0xc4d45001440e681080,0x78801900c9804a89ee],
[0x2008014d5c0ae06381,0xda597805902b6006c0,0x9b70da0540a80902d9,0x4c3f01e0d96bda3806,0x320956666a84c1630,0x81d5ebda583318814a,0xda7802287431203c10,0x3b0eac1a221e81d656,0x89f81b40b8ec66a80a,0x14e40c501bdb8004c9,0x81ebd35a5809b01975,0x669800405070e01411,0x10c450240100d00066,0x685014086038d69af4,0x58506b81e17e0745af,0x2f050e1e3666805a3,0x9ab006084a0716062f,0x2c2208081e1b0f99af,0xbfc06668104221b03e,0x44008a188202c640c3,0x3969ae300c301ba6a0,0xf01b28707541783707,0xc1871468e60f87af68,0xaf98900488d07f0e13],
[0xc7024183421878f9b,0xc0a3e96666e842382c,0x6b8801b9a238181261,0xe1ebda580a2f01e1da,0xe666f818c1f9011781,0xe0e81585893d04c3eb,0x8b059e0b999b003001,0x9af412c58120509c82,0x41cb6bda3832b01856,0xebe4e63806940afc0a,0x649800e05808f80a83,0x4812c0f41041508ee1,0x6206e093a0e33e661a,0x150d605e5a6b984828,0x1f8169ae900c040864,0x3088537c1fe080c0c4,0x80b14050e20faf8780,0x2c3e06be5060141087,0x7c554a8218759c518,0x595100cc50938bb,0x37429209a221c0e044,0x4e395c0084e41be3,0x436d69aeb006b15c,0x12285c1d561e7428a9],
[0xc905a0450faf6d8470,0x2faf8d8f30420d4a04,0x37143024943892b018,0xa20f858d8ef001cdd8,0x71e1fc1cf4829e124,0x2a029c1b81620063a8,0x80dada6ba80057009c,0x29dade6bd8a1270282,0xebe1780214a04b0cf0,0xb02502a57090442da,0x2ab4d859cfaf798570,0x100604041a048c8329,0xcd41d4434023af7984,0x2c800c0388c032ec0,0xb170000ee001a96a1f,0xffffcf02a57d14e7ff,0xc6202008402c84d8bf,0xece0ab7fff9fff2135,0x6c0de6ecabaffbaff,0xa8ffeffffd24852020,0x124f90ffebd7aaafbb,0x5f42550861080800a0,0x1702861520febec50,0x75b1096db312ec8182]]

def tile6 : List (List Nat) :=
[[0x556bf2040c04e00411,0x934ac94e22dc9bd555,0xedb7fc02140220012e,0x18ed7517284faa4b2,0x62ae6db6ee008901b0,0x9400c4c2ac62826e3,0x850c4c031252958c54,0x48b17599fb1a447009,0x514613b853488f4261,0x4b6b9ece21f8042c46,0xc8326317324620d8,0x28d7089404a3311586,0xa878319571230fafc8,0x3bd8022c12a813eaf0,0x3d48062833650422d9,0x5081b032a1851213cc,0x2a594b3c5d7779153,0x105171aeb71b1e4250,0xb01871185624fc4bea,0x18c31a393aa2501142,0x8287f6b9450809001,0xd0d6bd43100703504,0xd0525f1690c85847,0xe40360fe037fe61fe2],
[0x2063e42067e415006b,0xec58205fec682063ec,0x2053e42057e448205b,0xf23d18204fec3a4fec,0xcc05007a04001e8e00,0x3bc42c203fcc342043,0xcc242033cc2037c420,0x3c40c202fcc142033,0x7ee03a746133b25,0x17a401c283a4001d36,0x3ee004013a400c0,0xa200ea0020ee0002ee,0x8290e4009090b02c10,0xa7c00e318d2a82918,0xc2362a27280141688c,0x418853a19e609c0e38,0x8e9c0806b822516209,0xa8c3c188458340096,0x5cf8440202d41a0c00,0x10a630341a1810823a,0x2187880ca209cc0020,0x16a12198088031826,0x84097c00852a694088,0xe09023e2c0a182818],
[0x282c68480c282c0324,0x35808086034443c22,0x9a4974225162086508,0x8876c0316482402a1,0xa8e40c864c3a877c,0x5029f802e65424fb5c,0xb600ff59281e81fe9,0xa555a8ad4a5fe40400,0xd852000a60355552df,0x35b65c47acffd2afd,0x83011e8801878ec74c,0x3814db58ffa2283360,0x1c7ae22836da9cffd2,0xc52896efa8c800cdb5,0x7c1f00ec6403578e08,0x1961df8740a48df63,0xdf81c81a98c2e5bf28,0x5308de3da806a6a654,0x1c0f0c8044033c061b,0xf0b8200800c51c6cd8,0x88a6d984c56e3801b6,0x18003072195318c56c,0x6801d4037c1a318347,0x250c1a318347386708],
[0x4c9696e8c60d1cb001,0x3c01074098d2040174,0x30e2450809c14c5081,0x88706a200204c86707,0x25c4b4dcc507129056,0x825314204d81c2511,0x80982030b4070903bb,0x68591306a000c23817,0x82986c4ed810706142,0x1005037e881030f081,0x84401405ee1033e601,0xdc04304c2493820296,0x36572d40384c4b783,0xa122396039f6fa7838,0x3d4805a19013c9d010,0x3c2013b5c3c00f83f,0x6804b70b91b430914a,0xc249b40268783a759d,0x7b4004f03d3487b009,0xcc1b32622ce01684b6,0x700504b63b200430b8,0x7cbf014802c7e0fa86,0x1af97f301dc67100b5,0xc217034f66fd740130],
[0x804104b5d2b004900d,0xb004700a405f29d114,0x111e4c20f80d84b51a,0x704b5128c04100198,0x4d529d4f0801e23190,0x84b502580510014500,0x42c81f164d2f700c1,0x7c600c3d2002580510,0xd22c04b006903665b1,0xe8f581b1af6ba81894,0x7e81715f6075008347,0x123ef804c80e860158,0x24312021bc04b002d0,0x4500c62039f6cd350,0x2d80fd94ec0f3021f0,0x63598b703021d0d230,0x8085c015800a05e02,0x5601480670171ea401,0x9002880a8a22048c16,0xf892629302b2795804,0xb22138089000f04b01,0x500045f01e5564c280,0xb84ce10210b0211404,0x62b1f8f8045000ea03],
[0x37016805e407ceb604,0x909300e116048c7484,0x57a0e2b1b8bc045000,0xb198b846905d8088e6,0x4f01a203e2a885e42,0x731b5263162b0e08c,0xf142b0e87004b04a84,0xb000138c86e40788e,0xfb01681242847180a4,0x43004187df8c071f8,0x74197c46f4073033b8,0x190a940341e8080138,0x1c0993ba5d4100334,0x14e201086c283dce44,0x40da01780171460044,0x1380cc1c9e92e0146,0x2e06821f402825ac0c,0xd5f8f01b93b61ae30,0xe0c06da51501480372,0xa4592c80138170128,0xb5d3240510dc1e3570,0x3a012b5a934bc03851,0x4901b8c30982900030,0x9804501e0481973f5c],
[0x703cf741500cd1b084,0x8e6a032002b4041004,0x630a40148742d4059,0x13490421240a08494,0x19dbd8b5bc090c4d8,0x7581a3200430047053,0x250d1c83012803e9ed,0xc4287f01587b024610,0x820148092a680b52,0x82380822901f5c04a0,0x450004a02c6650000,0x3a2a65480a861949d0,0x8ac4d86a011805e0,0x71040006d01781431,0x1301580f0148088f2a,0x780982780f46b40c28,0x10219595034b25834,0xc532917004d0098298,0x5811c055494a4a40b,0xc8fe98221009580430,0xd0b240f004d0583e80,0x30183b80d18a82022a,0xf00e35807e11010800,0x8f02c66408a78028b],
[0x821c31b8b0045029f1,0x17805428c01354211,0x718011d1041c346023,0xf328a121300004d001,0x89408801a7f501a67,0x180c501f05d803d8d2,0x2050e40c500b705022,0x470ab8223819c0c605,0x40440fc1d01f801e0,0x30406143d822780180,0x4380c5d00d81234390,0x4604c09ed06221878,0x13f8017c0220330394,0x6f80586e05808004ae,0x604e0120540e8130,0x900304e8004ecf8874,0x78106009b84e21a801,0x887c0ac05c0c5c0c40,0x9a00181d0418004ef6,0x3e804406e3da21e801,0xc03a0880c04184a0,0xb3e2184e100d0010,0x3606541e138030b081,0x110290218b1c5c84e0],
[0x8401a00470026805c,0x272213b6c00850085,0xedb42214806280a28,0x683a81f800c002803c,0x4bb621580070090120,0x1182e0f0f101703c09,0xa7612884d019080c8,0x580141d08e02140080,0x825404a034136882ce,0x20b86c71b80020021a,0x319039031720012a64,0x2f5b38209834208028,0xb800560143c0360058,0x30141d80340f424220,0x20b801a803e0720b87,0x381a0c0c08a00f404a,0xcf080401bf0121,0xb5003b204806410b0,0x719c09f80248ef0814,0x580bf004a8cf080c,0x203a0df80248120814,0xa401c1a488d0809002,0xc0cdc04c00c02600e1,0x4800882543c0102505],
[0x3881c405a8001021f8,0x5f00ce01af307e1198,0x211b341fb801e80120,0x23061d807601f00ec0,0x4402c40211cda1f98,0xd48ac1fe120a8138,0x80f807a00880461f98,0xf87c5007300901f00e,0x383c58db010c1b341,0xde2a839b83700d00c8,0x806f084490012a87cc,0x406690243101340109,0xd0003805031af8121e,0xb0f803a00ca3c1107c,0xf0280414441d006038,0x3361f045c0218c171,0x7c3001d02d01540508,0x981e1a80ac0844cd8,0x80ca40980fc01c3212,0xc03061f3c2cb680182,0x409a40670161225405,0x900a90024010b2c409,0xcc0d206a05972f2843,0x40e0306246867e0d40],
[0x41d7028083063e1b82,0xd207204003ca10e802,0x2d06500609407412c0,0x5e001087acb08060e,0x2c1ea8ce02900e8048,0x12405700330014133b,0x9408422a07a4a80412,0x7c027004700b312e07,0xa038cd980330c2a4,0x4500e40680b2484090,0x88c0b818040387301c,0x9003b01e331c3c4893,0x10004029878c643c4b,0xe1b31418789001580a,0x17090e143100c81383,0x2800403832c02404b0,0x7b017e03b8210006c9,0x200100001db25c5bc0,0x9abb550053009e01f,0xbc0b06200380885100,0x84629940cd50060640,0xe0083e500088836096,0x3200501780e0fc06c9,0x1341808344e05c1b0],
[0x140b40c83ec93b550,0xe07300e243850c402c,0x1a0b271206114010a,0xe02101380000760fb8,0x700e80220038058582,0xc1fc06e1f0b24293b4,0x8358c41d82a0a40782,0xe8b8074ca23c3a16,0xc028760911a03e01d0,0x80ae883c7000c7700a,0x90012036806c08c145,0x3c28875401071aee01,0x28883cb013019900a0,0x848fc0b0887a0cc1ba,0x6824729b83100e806,0xc8742831e072685a03,0x41e0b2028707607680,0xa808380072c683a415,0x1b04a80c861cbacc6,0x4818cae79bac5011ec,0x40542b401b01e190,0x8000e8a012d123b8,0xb40706020040a4088,0x180c0e16038f0a4064],
[0x101a127c4846134828,0xa028c301b08724ebac,0x2a124851d802c038e,0xb009c190400072eb28,0xbe31e1c2034200d007,0x83a6c787140129ca28,0x453a73003ba01cc0d,0xa8480c0ac0e605c100,0x71348e1009480e09c0,0xe0490004503950167c,0xe02c00a0100407604,0x4c3861077133507201,0x81c9e0642c7870e9c8,0xcc9e006891c200080b,0xa04b010c04e05c3608,0xa0c80867a05a00d017,0xd40098036064320003,0x330320c84a6e86801,0x200c28c79035400892,0x1d82d06e83200db803,0xdbe07e0378039002,0x8130ec0c81516423a,0x38a342180a2c3810e0,0x174c2ac52b0721058a],
[0xb836901f3d07d2380c,0xc0100c5602a0110001,0x2106d0580040610021,0x1ac1836423a110022c,0x201b04301e1d02d0,0x6ce2a3661e12040b1,0x59009600a38b8a1b18,0x8098667b8a1b685140,0xc0d41040a5900506b,0x2480bc127034e29802,0x41b18011100741204,0x26014c06a0c7000d0,0x20c1a834e2f8022054,0x40c1e0130380180885,0x2400cab821ae113805,0x241a880e50032a1ab8,0x107f027054402a036a,0xb8057001a2e086a401,0x4480ac11043686ae0,0x32e0b80088314028e6,0xe08f200f2023012010,0x12068e12068e123103,0x80ac03d000e1580680,0x2880a83f0242c15016],
[0xe020c068e1681e0020,0x40c852015015c0b414,0x404434f868e1484886,0x881803a802c0c1410,0x40706b00ac00c06727,0x7f8002ede06640284,0x1500ef000b866de28,0x23b066de2803983c7c,0x32138368116016c03c,0x282a112021982e0158,0x3203c0482507207900,0x2880a900a59866de18,0xd27066de2801f000c0,0x180ec05d000602e0b0,0x3582c190837c19200,0x1601805501e00405b0,0x816a1937d400df0640,0xb37c19180a78063807,0x2b01c40341505b000,0xc161b705637cb002a8,0x8130c600f000801c0d,0x37101a70150060278,0xab806f001c6dc0624,0x158218190940fa370],
[0x1371c01a82107e0b9,0xdc38060550190684e2,0x23428ce0641a0be0ce,0xc9c0ab7010011803c1,0xe01040243428ce0460,0x74b9060c0f38078383,0x7418185041821a200b,0x4172021401851000a3,0x641607900058382600,0x6480ec0e06406c0cc0,0x18815013808dd029f0,0x89c40a40e06805c0fc,0x216020607877c6c04d,0x20a299138b9374d002,0x4f0030a3c186e0643,0xd20a285c2a03c34274,0x801401480560840021,0xf017b836a74a03e044,0x2e01680c204903342,0x19617827c241381d4,0x269000a83d023c0354,0xe3504c3f04885ebc0,0x600f00080e22046022,0xf824a026dac8cc1c1d]]

def tile7 : List (List Nat) :=
[[0x12e801c0d00d00ac0,0x68084802da82690c6,0x71f80d8022740420b4,0x2c443a0c3854090260,0xb85cb10805d0036e17,0x17289c1101e077c02d,0xb00ec02b031806f940,0x432b6ef08c16402e02,0x900a0c387a064061ac,0xa4380c542218c34809,0x2a0540036e091e006,0x28070020080e261a2f,0x105dc41010889d01c0,0x8db8253077414062a1,0x207094170c82a0d91,0xe220d4a01700a4024,0x7c16d50404c8181c19,0x86b336016c8067802,0x340ac0228400a81f40,0x9002600a024b601688,0x934d8022909a01c809,0x6c038383d012190641,0x14a8440780b8158060,0xd0108e16822d80607c],
[0x18305a031018484822,0x760273c1c6132a0660,0x5400360088e058d028,0x1c3609090498640f02,0xb53a123581e80613c0,0x6605221c0a10c0f010,0x16e24364c00a73641,0x817a1608087004f8,0x1006812408d00a81f8,0x5834340781a5cd9058,0x900541b83518817a00,0x70c868720500816020,0x30781204902c1b8070,0xd3840858b01c1e4120,0x78385063206138010,0x8314815404c0920118,0xac06c0d5364083829,0x64028809f808900a02,0xa8b55c0ab8054f3e85,0x8e15a80208501002be,0xd80a403f010202078,0x1e2af856d578032128,0x57802300d806038108,0xe003543000c1c1c814],
[0xe80c301f0886419001,0x501fd0031241c0e854,0xc08106285e071000d,0x2d18b0500d81580bc0,0x840092160040882281,0x1cd60800bc0054072a,0x881ea004a00a823f8,0x502d02a081caa35810,0x10c24c0d63204f802,0x605600f2008c153594,0x2301a0540035807360,0xa07e00c320e02123c3,0x14ac3816664b20be04,0x50057e410a0c2a0f01,0x12e1682881000d601c,0x20806a0282d009824,0x8815010a06a9543912,0x81806b5ca548013601,0x136010c016c0643205,0xe0c4162d7052a53806,0x45ad77801903b1806,0x18c04c37064321634,0x230b5d100041e0139e,0xe0f0b1a12c048185],
[0x1c4838ce40c826802a,0xad700206ae00c6218,0x703061960c314603c,0x76b323d0120b03c2d8,0xc292c28c8030132ab8,0x2940c0740020182e1c,0x9206c0030001e08f0,0x80a06c000703c040,0xa9806402781a002407,0x10809806004010809,0x70007010801400064,0x701a001b0020281e00,0x64000702018a206400,0x1a000700981a2080a0,0x1e029aa01e00070008,0xb01a00070007002028,0x1e02d0020008001e02,0x81e0002d01e002028,0x1a000702c800be00c0,0xabc074608060ac0000,0xbc074000700a06c2b,0x1a2d0d206410303600,0x27a011000201980340,0x6402880cc0006407],
[0x20470328180182d2d,0xb4000703736a000759,0x700070db0208060,0xc80f4f20640003681e,0xf011000201a8000703,0x3b80000a064099014,0x7009b404f400074,0x70b817c002f0074,0x640168208060ac0003,0xc07400070007400fc0,0x420201e3a05a04010,0x400079c0440800074,0x4581c660117506060,0x20006c2f0320208074,0x12d2e0640007217000,0x4a8001e04c01a0330,0x1a823100000206c,0x8001e0391815f8102,0xb4081032a0207c00,0x2e000500001200202a,0xec062100e054001020,0x170204080ac005812,0x40a0840370004080a4,0x280120010202e0e00],
[0xa01200088816008012,0x4080a400a012000500,0x4080ac001028261a00,0x10202e000501e81600,0xb01602a812000500,0x10202e02c0c81600,0x5c2040a08c02b8d016,0x8040ac000502e102de,0x57423eb605c037020,0x101203012816030ada,0x804c192040004c3c03,0x706080a054023404c0,9031392151263488,0x540604b01100020108,0x3a012038088252020,0x119a6720b40ea00054,0x380f41ac0660005400,0x2981f605841820281,0xac00fb1d4124208081,0xe8160000102e608040,0x81201010013ea0003,0x609d01401801d81204,0x805401d02016509016,0x1604381203b8044000],
[0x1fc004010ec0449e8,0x20004403c060a08054,0xc1d01220520c025000,0x40042100052320c00,0x2048840250004032,0x5c01802000440068,0xb4160d5e044c058020,0x5d7618500041945614,0xe55d26580f48ab242c,0x8fdd4f19101422ac16,0x9cf018d002a4d109ba,0xc000983009acd65dac,0x889000102914bc84f9,0x40186c30a50e0a3d18,0x5db00da0100c084243,0xebb49d2e4238230080,0x71f2800591f00d1422,0xd003a2ec9ab8912ae2,0x90a4a5ac6120941a00,0x8521e04a364f47119,0x880d3056b4009a4d59,0x54d76141a802252593,0xca8c053a050a0d1034,0xfa640098640c110210],
[0x1ce84004c5b441b0b,0x20c45a6cd70c4acc05,0x150943274b081dc200,0x2106140615c026d56,0x6728108f0130b41ba2,0x1813071b446e52047c,0x8e5fa7180284d1cddb,0x4dcc628fa0280b17,0x3458827ac18620cf2,0x241338f207c202f44,0x45f840ce52e397c88,0x2a49e230709f0940f,0x6a241cea132a01d5e6,0x98346918ab63981b0a,0x148554008430a34fce,0x6a0c316281ac88019e,0x386478206b2c1a820c,0xaee408f04cb2f4010d,0xce01181047933c1501,0xcd5f340306932402fa,0x1c075c030504dcac14,0x115c880706aae4088e,0x2c110505dcd422084e,0x3081174dc9818259b],
[0x408d658c661c659388,0x233c0914670c144203,0x4c0a5a2d0cca0b191c,0x2904b15c330105020c,0x1c83e16622010c409,0x12c7980043802d8c21,0xb4c40300a9640926a5,0x84526c09081d040f0a,0x30ea440f318e0902c4,0x32054a03030a010e01,0x4e124a4a004e0503,0x1a7603321203010e4a,0x6c014418d001c60800,0x521d0996de01d81c0a,0x104131c4a1028562e,0xd07023e04003e9802,0x350c9c2e0b0e2088a4,0x6381e006c241a0222,0x10b09048217050012,0xc21c406a60d038209,0x394207091901090542,0x35d1c44f0290e54400,0xeccc270145d1c42703,0xbd3272395634270140],
[0x4b0268db6401346a00,0x2d8d52c5b02de41a4,0x3a4f491b62354e781d,0x10462e4c066190031,0xb4a4172a5501aa2174,0x8c524101412a590380,0xcc0170521500291a00,0x5c250e13018f81e093,0x42008048842400844a,0xc5d0299f104110070,0xdd007c42081f0001f1,0xc121a3263a07a1cd28,0x3e03c39c81a1d0f402,0x21073a43a683e3a68,0x378c18de0018c2af11,0x614b1801a02a00acda,0x4160b405c586841505,0x2e5814ce0b1c2a0543,0x10bace10a609a264,0x406481ce10bece5026,0xb03420032544d00ac,0x32a448030221506c74,0x1281200f8120b0090,0x8638bc090053c808],
[0x82ad0250226c944016,0xebed80e01200a0008,0x103401000c81e49644,0x41b011f424040901b1,0x151517171717040f01,0xf0f0f011111111113,0x709090b0b0b0b0d0f,0xe0096009605019203,0x6c0e8279c95986201,0xf02723a1ec03418c1c,0x1c2615082721e3a401,0xb00701c3840dd5c0d8,0x269b94e270381c402,0x46dc0500e806e1a36c,0xd2806c29880b80503,0x24149414140781061b,0x700966a4e401b0d066,0x680d0b40164e33405,0x2604c688ec01a858ce,0x23b0289a0c132803a0,0x199826830144094641,0xbc160b090a02a012c0,0x247c030620a402ea44,0x220b84a802480662e1],
[0xb684381c38340a290,0x8470a20f098120a219,0x80706642c11c014543,0xb4118ac82642c10400,0x8803e1226192090841,0xa83e28240841918a83,0x163472846028300188,0x68733c3c381062a0aa,0x404348a487c183110a,0x3d0260280cc019b80,0x5061c3904803108a58,0x5e0a42c012161e161,0x2080260a5e4019012,0x1888345c099fb38978,0x618217102828040cbc,0xf825c24084199c0d80,0xe1e050e8b050823208,0x6968f88b828b81871,0xa0622c10b01870683b,0xa3404222c006107c25,0x207036286870483963,0x866ccf0e3c2a0e823c,0x6196080128068808a3,0x5820044044c320383],
[0x1201120303010301e8,0x1b1d01010301010103,0x20ec0f111313151719,0x909090b0d003a0f1c,0xea01e0ee1d7a0fea,0xe239078ef0040fea,0xe21c721c7201c0e6,0xd20cd20dda000dde,0x3300ca0cd20cd200d2,0xc200c233195a000bce,0xbe0ac23118520ac200,0x9be174a0120be0009,0x8b60100b608b200,0x14360006a607aa153a,0x132a00059e27143200,0x230492122200049627,0xe24111a038a00608e,0x360503001016028220,0x1f09083a19064a00ad,0xd801c3062511821715,0xa5339a5003895acce6,0x146b98085600d67efa,0xfe740015e668f46020,0x981d244409802ba80b],
[0xd0aba80d9bf02011eb,0xe81f8003dae46bf838,0xc02bb815faa417b5da,0x381680ae90d1693a06,0x583024c02be807d7fe,0xb82080f21aec02641f,0x76be8024abc33476b,0x40b00afc1e41eb3820,0xa8015f80046b880171,0xa02bf84d81598002eb,0x440138005af40feba0,0x120cc2e401921820,0x4401a80e4c05050012,0x540392058824140500,0xe644390e3016017940,0xb8420c5816051270,0x203fa4000fee203fa4,0x840fea000fee000fee,0xc401c0e6000ee61ebb,0xe6000ee6203b842071,0x1b6a0dda0dda1b01db,0xd21a621db744001b6e,0x180d6000cd635350c,0xbce000bce0bca00ca],
[0xac6310bca0bca00,0xac6000ac60ac231,0xbe09ba00ba03155f0c,0x4a0009be0009be0009,0x2022c420590408b217,0xaa2022c408b20008b6,0x7aa07aa2b07aa2b07,0x1a84201a8403c0d68c,0x526406a200a206a220,0x9e059a059a059a2713,0x9200819602459e0005,0x49600049600049604,0x8a00038e2300608e00,0x2038e038a00038e03,0x200a04028210120282,0x5010e000286000286,0x50505051201050542,0x10501120505050505,0x50505050112120505,0x50126050505054205,0x10a088e0508d60705,0x5084403a82c010102,0x4205040e088e0216,0x2e8201245a0305008a],
[0x31064d617cad7c5e00,0xc08020201405a80c06,0x905a4b0000bbe42e32,0x160110c40a54215401,0x855794c012852942a,0xdc144a22ae60018,0x314c018052010b0231,0x2c4a01805201b80806,0x3414021105d4b13c01,0x4ea4004e0a21054521,0x744e3302900124b12c,0x983814118308013497,0x4e0a783808441bb844,0x2c0a0a8222110cc200,0x814a110c031c814884,0x1c061c810a9a6c061c,0x3434c42804020e9c41,0xe25911c5810701088,0x1c2c1b014bb10c0422,0x58d910404020e9de1,0xe1b0fc020504d87654,0x786411078ac38460d,0xd879ac2506422b20ec,0x40d000b20ec0a0b80]]

def tile8 : List (List Nat) :=
[[0x1878c83e520510764c,0x83a8f170101839a1ed,0xd188008b808e543a96,0x840bd0d40f0a2c30ca,0x28028b0d5bd0dc0f0c,0xcc01c021ca2c356f43,0x2c38d383281408b460,0x540919c0d4005011ca,0x9e88e4080550cc00e0,0x4e0c40a00873219c1,0x880501c0eac0ac2d00,0x2c0bc05860c358d02,0xe0bc24f8ee08140608,0x40b48e742e07030da3,0x29eb0298003819063b,0x4e859f40380439468,0x82081101f4f0a41419,0xe782280022c30e11e7,0x6d4228002045861431,0x33cd42080239431a32,0x787c002508c05831a,0xe782380613c4f047fc,0xf202382e022c309a37,0xb20218010239461437],
[0x37f202080502809a34,0x4d234c6419802809a,0x980149123209818807,0x629c00470a12320641,0x36c981883c50c0c01b,0x520602c133606404d2,0xd001a8278cfc007c3e,0xe036074078704d236,0x80e389c2226810807,0x72705c03418e31c681,0x864e3340939829a244,0x1ca484e322bc1280e,0x9b9828118e304dd798,0x2adc160043418e31c0,0x5a17171717171717,0x150052151500521717,0x131315005215150052,0x1300ca131313131313,0x46004200c611111111,0xf003a0f1108461108,0x3e00be0f0f003a0f0f,0x3200320032083608,0xd0836003208360032,0x82e0b082e002a0b0d],
[0x90b00ae002a00aa0b,0x900a2082600220826,0x1a0826082608260022,0x7009e07001a081e00,0x12001a081e081e07,0x81600120012050816,0x1aa614056e94050012,0x7422c56401aa0520c4,0x50800105601714501,0x4080127a40c171492,0xec000d3e004214a69c,0x51200320c32091698,0x8e0105004e01009605,0x1301181535c2010906,0x3013039681c406a7,0x1800c4c80686d51eb4,0xc0d0f81fc065d5301,0xa68d901aaf699d1851,0xc6dd0138000012c8c0,0xd503c043d01a05201,0x38428021009338c05c,0x1a394b90095202a8c8,0x8015001080a051f0f,0x2a12601601e0d1cd30],
[0x1ba412a4fa2d95a476,0x54baec800e900a8be,0xe0cd870701a0914a00,0xb900a537404400a1,0xd01605580600da694c,0x30668066a380541814,0x1c806a6365a5c0f83,0xd80e3cd90178083e,0x91a141e0cc1c381425,0x702c041808f348054,0x10cf500ec0aed6805c,0x540170bd00ac55c054,0x4c0702506d8072b000,0x14802a09300a33340,0xf8050296193a0180ba,0x2a0180cd0108054342,0xd4a4a81604412408c0,0x5053a212203b80a8e,0xaa02980d7802615800,0x42010800c12a0c5c0c,0x1080b8150220510003,0x16a2bc04502c561016,0x46786870f8061f0550,0x5a80257f802113740],
[0x20e36c046a0187214,0xc09e0004bc9e48029e,0x510009c5310140381,0x80c4851844d018a308,0x440c56244e94045414,0x6b017800850085a6c0,0x5a0a6c292829140e83,0xd434101382a038390,0x3006060fe01c028174,0x85161881e814dd8c04,0x900d10c0481a145a03,0x2870b06070355d0405,0x4c1c514b4023c0c070,0xb1c100446cb2c1c2c2,0xb1281fa9d016008300,0x6e0c8325037000165,0x198122000108006056,0x5bb1f8043800e03814,0x3801028328120167b,0x9e80004100c28a430,0x30a080cc078320508c,0xcd00b10b00440099c4,0x500d300b090000400,0x5c0085009b18d2c400],
[0x1c0e004037808b5a00,0x704e03f01569b5f18,0x35f28405307c1b8008,0x98330020ce460081b0,0x4f02124b2958384f0,0x8251c72f02f0358dc0,0x328c2f0309e1303a03,0x64d80a202004d005c,0x282302d00013b0128,0xa0f601480063420090,0x9c0bc7300f04a06a04,0xc1904301ec0256d801,0x1680210d029187c00,0x74063c1c0080e7686,0x39da7404d0041306b4,0x1c181b0194632061f0,0x138022138c4401822,0x5201700307302d400,0x56014b6c3f9851c20e,0x9e0148289d02901080,0x62622067019c6b01c8,0xd02702b16501380c,0xc0080130c61240484d,0xe1e81c67088184403],
[0x80545b2225ad864605,0x9b00440e28bd00ab10,0xb826f0671600d300b2,0x2828243b81a58819b,0xd02b4025464c03c026,0x480e184ee07544b118,0x424963e1180c7341c0,0x2863d8196204047000,0x133c51f86a06a05243,0x390184f604056b4668,0x16e3fa0c5c0680c4c1,0xe0e300340dc8740108,0x4405c0d2931012804,0x2d87898b80a048308,0xf02400805c07868263,0x2060d0398a0804d002,0x24008160a11839a3c1,0xd73101180021889ce8,0x502781c21101906,0x101b064502ccd38d88,0x18c3008dcc804c0b0b,0x3d5869f80536582d8c,0x240a3481f8121040c,0x3024080002b4e81325],
[0xb6b02203e0440b40,0x9901601b0b4b0c004,0x1601a80469c005424,0x2c0a46ca6405001f4,0x880f814385e004044c,0xc5d014d7203c1828da,0x3901fc055000ac02c3,0x70bc1c6040430900d0,0x2802b245491b00b028,0x2e80cdc1180007801,0xa82428a0160242f005,0x740260c40a8100d390,0xd012b0178012301c0,0xc0b00a1e805050b056,0x6406005b256c091e80,0x40cb418c484041001,0x310310240900a0c714,0x580918336484043005,0x2d01c0580583302428,0x4583d004c0229884e,0x60058ed9400c600d8,0xb19d80410005c0218,0x40bc01c1e818a27006,0xc2c757004800c9096e],
[0x2d14250134050d8146,0x470060b3008d30c04c,0xb1d5cd4c0b701200,0x341695920b201238d1,0x80440508c100add5c0,0x400400699842803d58,0x410e5e08824804606,0x3d012142c1583b5c60,0x410004230587022b0,0x1a010201c0d828dc20,0x5636281a52008ec110,0x500a21b830810804ea,0x30c71462b033adc005,0x1dc1840844162200c0,0x69b34811f88a0519a1,0x860041d07c28640c05,0xf1b82218530c045068,0x8e6e0d0308c0cc0d14,0x4100618700440093,0xce8129d0580428af30,0x4240885a06e0518a28,0x170004280430165714,0x61d8130620a80a09,0x6b0da6cc3009c6330d],
[0x80d0a1780f8711a048,0xd01f6b20128c22988,0x7016004882a03e8048,0xe038600556e0b008b1,0xfe0c868a5608e00c11,0x4820000ac230666512,0xe03429a3703d014560,0x52dd6c0a6054a60,0xb0a800af00520fc044,0x14960378051082ba02,0x8ac29e6c11a01200cd,0x3034009e6700404c0,0xf01c0f02962380cc4,0x1d0004f38a98299973,0x1782421007810c058,0xf02c81e18140ca6f3,0x2e920a670c8a1101c,0x784203804286c05024,0x1b8054010984f60638,0x12f0501610821402b6,0x404c5c0e37096404b0,0x480c94e9f038a0981a,0x28128128245f6e101,0xfc1494500087e07138],
[0xe0541f05b00c32b072,0x390402021bc8718a67,0xf03600c2a1f81d806,0xd0389968327809f710,0x512dea03e008519c60,0x15800054165b1a19,0x1406b6301680e28b9,0x4b1040580b0361c835,0x5407a0b83dc04415,0xf00132025800401eb4,0xb014284a4201580800,0x9111199e81a0580681,0xe528bd00ac8c405c34,0xa02615091abb550078,0x70a149e4c92a72d80a,0x24062000151c346e80,0xe1d8000e101084f02,0x31f009c3302c3d4004,0x40900d80c30cc58186,0x450034c94e3703452,0x560a3b039014370b6c,0x46016802a6d70dc048,0x5890c8245b00d0505e,0x61456ca74e8226e60],
[0x421014a3209e00854,0xa1e1ca2220009c05b0,0x52943405048620e508,0x120005152422e5b02c,0xa18305989501280d80,0x660240541380f87f01,0x6074051001209204a0,0xb04832064067260cd6,0x12801c49512ff8050,0x1ca3500ae003040c95,0x1082e0ce000507b0fa,0xe00fa1005c10804016,0x1701380904900180,0x126801203c1480b0c8,0x5050505120ee12016,0x50505050512120505,0x50505051205050512,0x50505121205120512,0x9632120096050512,0x960505050505050505,0x9605053212009600,0x50532120505050036,0x1200c6120532051205,0x9612320512320036],
[0x9605031205121205,0x120505050532050505,0x51200963212123205,0x960505050500960505,0x9605050542050500,0x361200963212051205,0x50505050505050500,0x9605051212050096,0x50505009605050505,0x41005c1e8e45fe4205,0xc701283284e040806f,0x5432638a0a40630242,0xd00482a04c80804100,0x605048308168c1004,0x4c02cb6a59b0128624,0x8bb8102900004100,0x338b02202101f81a06,0x2a028cc80010e01606,0x52472303428a18c06,0x305c28f20001030168,0x706011800421378a0,0xd0701602291d824406,0x40627405f103013823,0x244050d030108551d],
[0x30181bc4041000941b,0x98451e0c0202850946,0xd40860606a9013801,0xe270301284c287e0b,0x14405408825028a308,0x3f02012801cc270081,0x1812843e0741d07302,0x20981d049019585181,0x66e025023302015830,0x701480292c0380302,0xc4ac0e583a0250213,0x12101222e028fe0041,0x11000146401c11e83a,0x603a804fc0804c10cc,0xb2033023f02011808,0x1da9f01180099702e,0x6c080410052144401c,0x9f82960300205e027,0x50276e81c250444,0x66082642501c38446a,0xe006818e45c05c0005,0xc81280011195140213,0x4a008ca201081bc0,0x40516027fe800cd0f],
[0x580704108f0e2fc021,0x702c5a0aa060eff01,0x11a0120231062104d8,0x5d05e029804580801c,0x320620128056a8005c,0xe2403c05ff0f01280c,0x800027fd81c0605a0,0x122568ae02c08981d8,0x1c51d010800050fb0,0x844988004264378016,0x1048420060b0620004,0xf1081c05031d3ec05,0x2773772606160c2409,0x51219833d3ec05b006,0x7c0c78740c250c5150,0x809c0001185b665c4a,0x23f00813c7b00481b,0xda0616300128000012,0x70108052610c05828,0x800054192820640001,0x8780800c0084250087,0x81a0a101600201100,0x84028e41f8000fb01,0x380760000ca010802],
[0x14807db7cfd4085064,0x6833d0e80410016034,0x188ca13587e0440d81,0xc2f0506c0640750158,0x234028c603a0448c82,0x1803200a808d00004c,0xb21700c0ee00600200,0xc6006808a9c405c39,0x183c100bd805300e26,0x30d00c149828a0a048,0x45017194265062a14,0x4f0a29681f027b000,0xf601680089d1d280c8,0x280f0a2d0042104d8,0x80a2ac257180161111,0xe5150128025073803b,0x4702f04130150a205,0x80e2e149403833e3c8,0xe24016013311889638,0x4811d20208933220,0x6c070638dc0c800401,0x3600cc5f0108290fc0,0x6002d9edc07384dc1,0x4c11c122041a80be]]

def tile9 : List (List Nat) :=
[[0xcf013800a05080792f,0x6810ce6418235404ee,0x440a52500e0cf91501,0x4f201681a26108220,0x3c0b05e0714382101,0x6c3313c80490162443,0x587c02829039b0618a,0x3d008d2d00440a21,0x108183f008a86c04c,0x8251b0840fe000319,0x2121c1b602170701,0x3d008e444044126342,0x43681ec05295805400,0x98a5012821f0b01605,0x4413385810808a04,0xa7010800030ec02b13,0x83744d02a1fc0b85d8,0x1185604a01b808a80,0xca054190289205d921,0x2270514776104a4f0,0x26c2138162c320631e,0x21a0a827600004303c,0x60434302c5a071c608,0xa4009c7005c1151ca],
[0x80005400050a4a0250,0x7015800415066808a,0x809381b80040706001,0x24522ce588e02a086,0xd034a400541d84a016,0x202228802200f80,0x228d2c02847809c035,0x1e135d8c02c01b8048,0x34000027648e500d0,0x5c062102c07a011a0f,0x14606600d802d2480,0xc3c53c809ca131b48,0x143728e40430784ba0,0x28f60283141c048070,0x180a0642e501680151,0xd012124c6501e06310,0xd70614321394059007,0x49ac0a18a0e0f0451c,0x80900039404c2d9162,0xce015045e0d017830,0x823edd010801564ba4,0xc780441c4063300210,0x1e31f834041064808a,0x4d242a07a00f03411a],
[0x11d0126800c4cde400,0x801095460054119012,0x26e50138022304a004,0x1b38e89f011004050e,0x13019824300819ca79,0xc6c08003901680118,0x60c4d01f0141c068,0x7701381a8066427298,0x5e803cc60054004082,0x8ca003747e5001e150,0x110140e01c1d024c2,0x81a002000138184a27,0xf001846016028a6c1e,0x461822c08231537404,0x45c150c41e12038020,0xb090800dd01386128,0xdd0158027f00c0f01a,0x408804201822c2c470,0x35017822a81016028a,0x80c046043039e14402,0xc1462ad2016800c2d8,0xc5041501e0681231,0xc0ca13428c14720178,0xd20128038045e00209],
[0xc04c05110840780414,0xd15016002201108ec5,0x4d01c8080006012823,0x4c21e060160128340a,0x1800050b8068003740,0xa028a8320081ba2201,0x2c06600147c4d4038a,0x405901ba1f00281881,0x232dd01180212a110,0x1a82804c4d09c80a4d,0x702482001605f01440,0x8097090630cb4804,0xe83737088160e80507,0x5901c70840dda42c0e,0x2680800d201080842,0xc18caad201681228a2,0x40261413c02e05873,5066768630317184,0x903830e2900b0c0470,0x378452038f41cd870,0x78045848587150128,0x10c80c0001680ca036,0xe40a32c7a06868ac0,0xd1280c08a4340261e8],
[0xc000118309a124048,0xaa013702c81d80c140,0x63180000700541115,0x41008aad4044013c,0x1622b1d01616a03016,0x50096050505243150,0x960500960505051205,0x50505050505050500,0x50505053205051205,0x3612050505003605,0x50505051205050505,0x9600961205050512,0x50096050096050505,0x50096050096050505,0x120542050505121205,0x50505050500360096,0x51201051205051205,0x10096050505050096,0x960500960512050505,0x120505120096009600,0x50505120505121232,0x51212009612050505,0x54a12050096050096,0x260245264c00c19205],
[0x645340148c19600f8,0x238c1960d41080e10,0x21b030381005265c,0x9149800300308e644,0x10064c04b40108c1ba,0x90224f852c0a808803,0xc0f8285094c0190806,0x80a00c0424f853c08,0x31505061c014992800,0x3400502e8f852c0230,0x252c0540f0424645,0x40380642452c005023,0xa62251c0381894e01,0x2e8c62401c0e0b094,0x8e02d80a6225040318,0x1a80822250403f8b9,0x2d8a65140a0e050624,0x14283814188802100c,0x10400d85140190587c,0x150341089894580880,0xacb6141878204352c3,0x889894080141505021,0x8b98941800e0c540f0,0xb6145803c0e0c84030],
[0x1e121a96190802198,0x141801f03c202e0634,0xb1826c0a10802198b6,0x4e400b18203213a00,0x7844ed061c00180f62,0x108060f6c84ec3e0a,0x2a0c5414f1b1139848,0xf8420f19832138823,0xc01813a0061013982,0xb21813d8523808a2c6,0x61c1c29b8706420f1,0x321398190d80b022cd,0xc461c6e22004010a0,0x3f0083213e03e0586d,0x3780704c3e4004d00,0x83e0b787932802217a,0xd8070103f4f1b050c0,0xc1f823e104d403c5c0,0xa090621004378f880d,0x90420e08bd0f9318e4,0x793202270ec3ec11,0x49c713078840f9348,0xac02e0670ec3f40222,0x5d003d014c0f02a5c4],
[0x2b0420f05cee4b400,0xc0880f0102a865dc,0x201008729b9bb92a8,0xaee5c405a040ecc3cc,0x1e1c87399298004802,0xcf03cee5d401f0b008,0x4c1c103ce64b40021,0xb1973b92b800aa1976,0x33398f08183c0c4c1c,0x3c9206e012050e851,0x3b00e92203aa80ee,0xc01c0d00c3a4940049,0x9218036803a1a48404,0xea026038713058830e,0xb81c4047a1a48c0030,0x6081c390819ba920e,0x2020c3bcf40021a484,0x83846400470582a168,0x611a0047004701f801,0xf0e26071828e11b800,0x7c01f80785a464010d,0x5b01982103218384,0x300818042c029e1188,0x7c05429060adc39c01],
[0xc38c0a0e260b00a384,0x2e8016443642849ed,0x616454003700450017,0xac008da36c1e178183,0x6401380360844400a0,0xa161160178008da3,0x25a1c280a082368db8,0xd20643c01589a0190,0x68002063441e060107,0xd600fc070340642c02,0x61a82d214434032818,0x48f1c94190818d2803,0x60c01204324001308,0x280c0ba04334000849,0x1161d05c0721241ce8,0x1830784c190010c98,0xce024121982ba1241c,0x5a005a1717000810,0x5a17005a005a171717,0x151515151517005a00,0x1500d2005200520856,0x13004a00d600520856,0xca1300ce13004a0482,0xc21111111113004a00],
[0x3a0f004200421100,0x3a003a0f0f0f003a,0x320836030200b20d,0xb00aa0b002a0b0302,0x9090909002a0b00ae,0x82009a070182070826,0x20092081605050101,0xd797f87d57f1dc2701,0x6dcbb2bfb8edede1ac,0x1b3e8274fefebfb3f1,0x1b3ffa7effe0dd14c2,0x1fb4f65f20edde2cd1,0x2b28a6e9916f9452ff,0xdfc4f5ee85daccd2c1,0x3e75e35dcace1c00a5,0x338ffeafb3f61ef7ea,0x7b95afba259698c562,0x6f77effe49db6d09c5,0x5d3ecdabfeb3ea25fd,0xcf58f22ecde7be05da,0xe78853e31eff7fd4fa,0xbadba499cf92a89a82,0x3ed4e21d6ccc1bfdb6,0x2d50c77bb7aaefd5f9],
[0xeea0e70e40e27deadb,0x8fbcf55f41f16ed2eb,0x689280275c5132ddfd,0x1b55aeaa6ca0a9a592,0xbe53dcad5acc1c42bd,0x3be6acb94efd6f86ed,0x4e17deadb8d6ed24cc,0x8f48efeec5e91e71e4,0xf2f8ffbfe3fbcf98f7,0x99278af82d7c974255,0x3be0b60ac9a6f9f197,0xce48de3d59d0dcbbc4,0x1c13b20fd4f93f09e9,0x7e43e2ae04dc0d4acb,0x8edbec7eace86e70e5,0x1f8df79f5bf38f29f0,0xe7ab5c7369fecfddfa,0x9af3a93a3f9df8fe85,0xeca8c5dc10bc9b92b4,0xfe6fe19dbbd78d3cce,0xb93bff5fd6f93f38ee,0xbdb3d5acabc2eb79ad,0xfe8de79e67e53e2dde,0xef72f6af5cf4df09eb],
[0x7febfdcfbffb0f99f7,0x38a584a73a5102e5ff,0x3b8db4cad7a60a069a,0x5d0dce7caec51c07bc,0xfe5fe30e08dc8d6ed4,0xdfeafacf5cf24ed4e9,0x8d78d13c86b98a9592,0x1eb1ea9e8be67e09dd,0xaf4cf39f2af14edeed,0xffadf9af92f8af6df5,0x331cffdff4febfdefb,0x98d988181a72b6814b,0x2ad3a439f59c698592,0x2c4ec21bfcbcdb76b3,0x1d84d53d33cfbcdcc9,0xff7df26eaae5ce20dc,0x8d04c7cbdcb419fffe,0x4db5d8ad6dd4ed39d2,0x4e81e73e43e29e01dd,0x4efdeefed7ebaea9e9,0x1f8bf78f60f2cf19f0,0xf6c64912d9ff2fcefb,0xe97a92c8ec88179271,0xdae2aada8fa5ca0d9d],
[0x1c18bddb91b6cb2db0,0x7d6ad41d09cc4c94c3,0xdfabf72f21e6fe3edb,0x6cc9c73bb09ccffbfc,0x9dcad7ed55d34d0dcf,0x5e65e46e29e1de06de,0xbec6ebeeb2e8fe85e7,0xef78f5ff38efbeeded,0xfff4fe0fd8fb9fa2f8,0x36875a54f044927617,0xd8aa85d8107967546f,0x79f19cb99a94a9088c,0x4b27aecab8a56a33a1,0x8cfacbfc50c0abc4b7,0xdf2eef6ec9e9fe29d5,0xcaf9a5a9cc8a8fc1f6,0x8d41d15ce0c87bdfb6,0xddfbdd8dbddabdabd8,0x1e78e43e28e16e16e0,0xff56f2af18efded1e8,0x7f8cf8cf7af71f68f5,0xb3af275feefc2fb0fa,0x68497fb77f6f562b5a,0x1a4f9fe9a795e8f28a],
[0xabccb9db5fb13aeaab,0x4c79c57c42c35c0fbd,0x8d9dd0ccc7cbaca8c9,0xdf33f12edbea8e54e0,0x7ba3ae699affbfe2f7,0x5d5dd45d34cfcca0c3,0x8e05de8dd7dc2da7d8,0xaeacea8e8de5ce32e1,0x1f0defdef3eefeebed,0xff7cf5ff35f24f17f1,0x5fe5fd1fc8fc2fadf8,0xc7876ca54136dfffff,0xa99494c8d489b84d7f,0xbb1daffabaa6ca339c,0xbf2bd7bcbbb6ba4b3,0x9c94c7cc64c43c22c1,0x4dd5d9cd21d0ccd6ca,0x9f07eaae77e4de23de,0x8ae1953fdcf4cf28f1,0xbcdacc5cb5c95c5fba,0x3e03deddb2d9cd66d1,0x9e6ee69e59e1ee13e0,0x5eafe9fe9ae9ae8fe7,0xee0ee0edbed0ec5ec],
[0x1f86f76f6bf66f4bf1,0x3fe0fdbfd6fc6fc1fa,0xb7f27d475969749716,0xb9489048c983181880,0xfabca74a5fa0f9ed9c,0xfc06bfebf1b6eb44ae,0x8c6bc5ac52c34c2cc1,0xbe08db8d9fd3ecddc7,0x5fa3f74f0feede5de3,0x1a2c9468d3fd1fcdfc,0xdc2ac2ac2ac2abddb5,0xccf6ce9ce9cdccc3c5,0x7da7d8ed4ed35d35d1,0x3e33e1ae0de0de00de,0xde5ae5ae4de4de40e3,0xaf4df27f1af1af0dec,0x3fcdfb3f99f8cf73f5,0x16bb61d53837a22fff,0x19198ee8c58767e879,0x5a72a4ca139cd99e96,0x3b2db14aecaddabea9,0x2be3bd5ba4b91b7fb6,0xcd29cfecb5c6cc29c1,0x2e2ee09dc7da8d87d4],
[0xbf9ef76f1ef04ea5e8,0x1af4a5a8bdfe6fc5fb,0x1d78d41cc1c92c2db9,0x9e0bdf7de3dc8dadd9,0xde74e68e49e38e27e1,0x5f17ef3ee7ed1ebee9,0xdf58f55f42f34f2bf2,0x3f7df74f6bf68f62f5,0x8fc2faffa7f94f86f8,0x1193ffaff2fe9fd9fc,0x67096e65ce5404aa28,0xa85b82d80e7dc77874,0xd93a8d28c38b489987,0xb9d39a997796f95894,0xbb39b1aaf4ac2a5a9d,0x5d29cd4cbdc9ec10b6,0xaf24ee3ea9e2ed94d8,0xafabf9ff80f5df52f4,0x593e8eaff8ff4fddfb,0x1c19be1bd3b80afc9e,0xd22d14d06ceacabc5,0x4d6fd68d45d45d37d3,0xd99d99d99d8bd84d8,0xfe1edd8dd1dd1db5da]]

def tile10 : List (List Nat) :=
[[0xfeefe64e64e64e56e4,0x9f6df51f20f19f19ee,0xbfddfd6fc8f9ef90f8,0x17266bc62755237efe,0x57e57bb79179179173,0x183182681b7fb7f07e,0xf8cf8cf8ba8a589b85,0x399896e95994e9198e,0xd9e29d89c39b89ae9a,0x3b03af8a98a039f89e,0x1e96d22b6eb19b0eb0,0x6f01ef6ee1eb7eacea,0xa39a13872872f36f1,0x4d2ece2c96bd9b42ad,0x6dc6da0d7ad7ad7ad5,0x4e38e12e12dc6dc6dc,0xed0ed0ed0e84e84e8,0x6ed0ed0ed0ed0ed0ed,0x8f1cf1cef6ef6ef6ef,0xef8ef8ef8ef8ef8ef6,0x1fdafdafdafdafb4f8,0xf6a16445ea57741228,0x97367267006dd6ca6b,0xd91b8ab80d7a875174],
[0x5bd5b94b2ca5f9d797,0x2c76c63c48c1cc06be,0x2d8ed70d4dcf0ce5cc,0x8e1ce06df0de0dd0dc,0xdf7cf2df12effea2e5,0xafe4fe1fdbfd0fc5fb,0xbae59d37cfffdff2fe,0xabbdbb0baab87b74b4,0xc47c0abf4be4bd4bc,0xed7ed55d1ccd6cb0c9,0xde87e87e87e5ae04dd,0x3ee0ee0ecaea7e9de8,0x3f43f39f2ff16f06ef,0x2faffa5f7cf79f69f5,0xbfdbfd8fd5fc2fb8fb,0xdfedfe7fe7fe4fdefd,0x25724613d429d153ff,0x76fd6f46c569f67061,0x2ab49618597fb79377,0x2c36c07c07bfdb12b1,0x9c6fc66c66c5cc5cc5,0x5c95c8bc82c82c79c7,0xdcc4cbbcbbcb1ca8c9,0x2d19d10cfdcf3ce0cc],
[0x6e04d51d3ed2bd2bd2,0xeea4e91e7ee7ee75e4,0xfb86a62997ff7ff7fe,0xdd10d10cf7cdecd1c1,0x2d9cd76d43d43d36d1,0xeb3eb3e27e0ee01dc,0xdecdecdec0ec0ec0ec,0x7ee7ee7ee7edaedaec,0x1ef4ef4ef4ef4ee7ee,0xef01f01f01f01f01f0,0xbf1bf1bf0ef0ef0ef0,0x4f74f67f67f5af41f1,0xf37f000ff3ff3f81f7,0x158f57c5695564ee37,0xf6ff65f65f63060a5d,0x790e8df8c38b089d79,0xb96196195893c92091,0xd97d97d97d97496b96,0x49ab9ab9a299999097,0x1bbbb82a97a71a389b,0x9ce8cb9cb0cb0ca7c8,0x6f56e58e1fdf9d88d5,0xff5ff5ff5ff56f56f5,0xef7bf72f72f72f5ff5],
[0xc7ca7caff6fdafb4f8,0xca53a53a53a0997b91,0xcb02ae7adaac6ab2a7,0x1bdabdabdabdabb1b4,0x5be1be1be1be1be1be,0xfc1fc11c0ac0abfcbf,0xdc26c26c26c26c26c1,0x8d6bcf1c71c48c41c2,0x1df2de5de5ddedd7da,0x8f58eeceafe80e3ce2,0x4f87f7af73f6cf65f5,0xffaffa2fa2f9bf94f9,0x95f826aff2fdefc3fa,0xc7e27d37c47c175567,0xf8708418278168057f,0xc95b94c91d8b488e87,0x89db9cc9c398698096,0x1aceaa5a7fa1ea049f,0x4c74c08bf9bf9bd9ba,0xbcf1cb1caecabca8c9,0xfda6d9ad97d94d54d2,0x9dcddc1dbbdb2db2da,0x7f7ef6ff23e6ee28dd,0xcfcdfaaf99f96f8af8],
[0x4febfe8fe2fdffdffd,0xcb14acf9907caffdff,0xcb9db98b8eb82b71b4,0xfbd3bcebc9bbdbb3ba,0x9c36c36c2cc07bf8bd,0xdc77c6dc5cc52c43c3,0x7d1bcf6ccfcbecadc8,0xbde4de2dbbd76d56d4,0x1e2ae19e03df4df2de,0x1e45e45e43e40e40e3,0xfe95e6ee62e5be5be5,0x9f8df86f7cf75f26eb,0x2fddfddfd6fb1fa5f9,0x6183ff6feafe7fe5fe,0x68f67e67463e63e4d,0xd75670b7016fa6cc6a,0x38237f57e47aa77075,0xd8fb8f68e385484a84,0x2a92a70a299c393891,0xebbbb92b70b05af1ae,0x2d0dcc9cb3ca0bfdbe,0xbd39d2dd2dd23d19d1,0xae31e0fe05de8d6cd5,0xceb7eb2eadea6e8be5],
[0xafa5fa0f6af63f07eb,0xefc9fc7fc2fbbfaffa,0xff9fe8fdcfd0fd0fc,0xbb61b49b39aa58e67a,0x2bbcbb4ba2b81b6fb6,0x1c33c1bbfabe6be0bd,0x9c77c67c55c55c4bc4,0x6ce6cd2cb4c97c87c7,0x5d87d68d3fd2dd19cf,0xae28e24e01dcedc0d9,0x4e50e4ae4ae48e48e3,0xcec6ec2ea1e76e68e5,0x4f02f00efaee8edaec,0x4fb0f75f6df1cf0af0,0xafc4fc2fc0fbafb6fb,0x6fdefd8fd2fcefccfc,0x5d58c46f2ecbcff2fe,0x1d2ecf6c74fdef6fe5,0x9a6bfeefb6f6cea0e3,0x3cd6cd6ca6c17be7b2,0xff0ff0ff0ffd0fd0e5,0x9e39e39f0ff0ff0ff0,0x5d55d55e39e39e39e3,0x7005000d55d55d55d5],
[0x40d909f09f09f01900,0x15d75b648417f17f0f,0xc7557557337186ff6d,0xd8398397c176776575,0x1a2aa1799394593986,0x8b2bb2bb29aa1aa1aa,0x9c88bb6bb6ba8ba8ba,0x5d75d75ca7ca7ca6c8,0x2dfadd6dacd75d75d7,0x2e05e05e05e03e03e0,0x9e37e37e37e36e35e3,0xe40e40e40e3de3be3,0x1e40e40e40e40e40e4,0xde5ae52e52e52e43e4,0x4e74e74e74e74e62e5,0x6e74e74e74e74e74e7,0x7e87e87e87e76e76e7,0x6e96e95e95e89e87e8,0x6e96e96e96e96e96e9,0x3ed3ed3ec2ea7e98e9,0x4f32ee6ee4ed3ed3ed,0xfffeffdffbff9fecf8,0x807607407406e061ff,0xa08a08a08108107907],
[0x726f09609609508e08,0x281973661d5224633b,0x9e77e4bd94c44a558c,0x109806a03f000f30eb,0x717c1511261030e60d,0x2812472231f11c719,0x285373367d5d043830,0xdd6fcf7c31b32a0c98,0xb601406000fc2ed2df,0x18187fe7ef7dd7b46d,0x79128fd8c788787286,0xbb65abba63a169ad92,0xce67dc5d38cebc76c2,0xa56a000ff2fdbf67ee,0xda14a0199e9698e485,0x1b8bb67b34b01a92a5,0xada1d37ccfc56bfdbf,0x6f57f00edcea4e6ce1,1030903,0,0,0x358940119802001400,3644473974,0],
[0,0x22ef16303501d01900,0xc8292c5b244,0x900000000000000000,0x932932932932932932,0xcb9cb8cb8080632932,0xf1bd14b9cb9cb9cb9,1022464,0x902902902900a00a00,0x902902902902902902,0xf4f536d1b105d03e02,0xa12e0db000dfcb3e77,0x972a61b41c3942511c,0x4ebdcf2ae9a238f583,0xd8107d36fd6085133a,0x4a3799e9518d78b884,0xcc01bd3b68b1cadfa7,0x9deadbcd23ce6c9ac6,0x4f77f3aedeea1e64df,0x6f61e57bd877b000fb,0x50c509e08a014fcbf9,0x81280d90d90d90d90c,0xf12812812812812812,0x976368a57641433b14],
[0x7c76bd9b28a6399e7d,0x9094015000f27e62d2,0x82682682682281d312,0xd27d27d27d26826826,0xa70c5a350e43a3a627,0x8c84bb0b06a879f284,0x507e000f81eecd98d5,0xb33e2d92c025c19311,0xcb33acea509097c267,0x6d0fcddc92c47c15bf,0xef9cf9cf1ef05ebada,0xd333000fcefcefcefc,0xd9ad34c01c01a676c,0x50000040200000002,0x1c0800001205000008,0x3c0b00002c080000,0x680e0000520b00,0x110000a0110000840e,0xc140000e4140000c2,0x16217000134170001,0x1c41a0001901a00,0x200002321d0001f81d,0xec230002ac2000026c,0x37626000332220002],
[0x40e290003c22600,0x2c0004b22c00046029,0xbc2e0005622d00050a,0x67c32000618320005,0x74a330006e03500,0x3900081e340007b037,0x6c3e0008f83a000886,42551017481,0,0,0xf248000a6248000000,0xc1a4b000b824c000a,0xd4e50000cb04f00,0x8000df205000dee02,0x2007000e0c0a000dfc,0xe3a06000e2e06000e,239468544,0x80000e460000000000,0x541f000f4607000e46,0xfd01f000f921f000f,0x10461900100e1c00,0x20010aa1a00107819,0x140f0010e2190010de,17],
[0x1170070011321f00,0x1e0011bc1f00117e1f,0x7cb9001236080011fa,0x4ac22a165a57270281,0x9ed1fbd843c5aea59,0xceac77ef8420341e1b,0x85c5e368c69ed6a580,0xcd2d95346fc6f1233f,0x5cbfe3844d72720098,0x43e33f25fa59790cf8,0xf1eb2f6fe5cecb6949,0x2f943d04407dff87ff,0x6ee8a0b86efe3c4e2c,0x4f00c4c64a0f108066,0xbb589ec0f0058430c,0xeebbf1cb90b80ee04,0x3ccc93f73928506344,0x3ce9d9bd588187fbd4,0x1877490909a8428b01,0x409008440a3ac441a9,0xc5eabd274c59824839,0xb35dce07cb7bd2013c,0xd145a77259066c11d6,0x39706823274526c996],
[0x326d9e9e1313d9131,0x1b508107e39d4716a0,0x3f06c56d47ea50f787,0xd205cc6bd42012fcf0,0x1e983bf1b900ab598b,0xbdcf35a55c0eb8d391,0x237fd110d0bd7b552a,0xed33c1f1fdb262f475,0x382209d60d506eecde,0x215f57886cc8450ff,0xdccf87fd28039ab0fe,0xdd7f94f0ef7edbca7e,0xcb2494338d0535adf,0xce18efdf8db165e650,0x1d9f15887335bd19fe,0x132165f070a0b6847a,0x78f8007efaea4519da,0xad630794eeae1a3f14,0xc67992f8a977f9d34,0x7a56afb3370020ca62,0x73dab4e542316db04a,0x36b1a5d926c3f5e9ef,0x95ef385723f19e350,0xcb5d5dcb3fac1aafc2],
[0x353ae71b8bdecc59e3,0xee1ab94dd2340d303,0xfde3cc248b97fa4bc0,0x984bac71d1c02becc3,0x43d75f743782d8513d,0xdbaaf487718b1bf835,0xb5ee9712e06f04d6bb,0x25c9b30d7cac10d427,0xe05359b9b605fcd3ef,0xd5bdcf99cf24cffdc6,0xe6288b5b09deca3e45,0x7c2b090950113a78fa,0xe9dcc8d039798ea5c6,0xcc71788fc0c696f5bc,0x84f975762154cdf81a,0x387397ee87ca278adc,0xb8156fef2ca3a26b73,0x68d48a5e365dd572b8,0x4c073b467e62de28e8,0x379fda726189ca4a87,0x2779bc3dc136437bc4,0xcafcf1f0ee417ef1d7,0x8c82f7174dc92ab953,0xc36873468c1276f166],
[0x4873802670540222c8,0x56eda6611dd5ffec24,0x72b9d4b125822fc68,0x62c73f0c213f04d9e0,0x8b5c6d80dd656a6b8b,0x5b661fe6fa835258f4,0x6ddd638cbc1739e5ec,0xcc6c8129e166bb7f8a,0xd0762788afee8ec1d5,0x1fdc6b0b97f461bbf2,0x1c8babd597521579c,0x187fc6f712b54ce57e,0xba764aa3a8d0bdd0cd,0xa455013e69956a44e1,0x926c6fc8db096ecc1b,0xaedfa428c39b3370db,0xdf73234273e4e630e7,0x93f0cf339e2ed8e84e,0x9463c77e3fa5d91856,0xa605ae35e26835cb3f,0xb8fc9bc050b921321a,0x8359dac51a0f936673,0xc20cd6c7b36ab54fd0,0xb7c2909cf6571813f0],
[0x1a58bb5b5836d24d9d,0x41d51938d697726ee5,0x41ca461b77722c1e2e,0x314fb2bd544475588e,0xa18fef842172cf8845,0x1ae28e89c21af039fd,0x492bad0fc8f3226244,0x3b778e3bad617fe18d,0x3691ec029cc0fa090e,0x25eeba5ab41b4f1803,0xb5db5b54dd5411e1be,0xf7f688731d39b0b7bc,0x8d5a246737da9c4573,0x27e4ba3cbfb1131b1a,0x32b10c61f5392df1f7,0x29facfd9875b2fe155,0x34cf0c3b95e8e60190,0xec5d5634b1ec53cb32,0xe2123d15efde2f0a2c,0xb73fa4177bf338be95,0x432d8d55b8d2262bc6,0x6cf625100c48f09946,0x2a21021c4f0fe3e2b9,0xdf8c5cea59becb2218]]

def tile11 : List (List Nat) :=
[[0xf34e3facca9d293b7c,0xf4ab049ad30fb32400,0xef1ed491adf592f01b,0xa2a396cc464229ccd0,0xa4337ad3e16446a513,0x680526b71da79c633a,0x80377b3792aeebc98e,0x9e386044a6c1a08826,0xbe0cbfab263dfd043a,0x1cc77387052a6721e6,0xa8dfe6b705f1cecad7,0x3dbf6237cfb386008e,0x5583c69cf2ff646e5c,0xcf1b7696d28e5b4a06,0x2906abeb89865357ca,0xd4d393899a0e382ef6,0x526db8075f73e5ee60,0x3b6ec62662be1d76f9,0x5b429e8cdf4229950a,0xc675faec3371cc1520,0xc00485e3fc7b555cbc,0x9a49e04cc457ae643,0x573d7b169b904e55c2,0x86b542632fe195e633],
[0x98e1dc888b80f25d41,0x9858ec445a5d4a7228,0x1d338837f37f3a5004,0xe44b452ca99c90274c,0x1be697f49a5329152b,0xc1cbc8e2ce4a6ae1d5,0x7a4d2cf1e72a94abbf,0x6e7491696e6b3602f5,0x60900755eaae7fde9e,0x7df9ac3a57854d827e,0xb04c3f52e9a960bc53,0x9556ef9c937c9f199c,0xf65b0f020c4ea4a4bb,0x878e936ead1487161d,0x8f66947d9430394d38,0xb1692bd4cd9b2d01b4,0xc2acca77635e76b8fa,0x3467a3a00e5aa24619,0x643c3d19be936bc5f,0x222e43abc8d9077ee3,0x3e0723806b5709d4a4,0x87386a46fd9c523980,0x762582e813e60b57c2,0x9850f82f3916bd477a],
[0x4209fd6145a1951cfa,0x6ed8bafa732c968f49,0x1d307c49dcf84731de,0x9807b35cff433b3bee,0x673c0c4b44bb7606e3,0x9574fff8497b817f53,0x797f1c6255bf9359,0x84577c746ca686669e,0x6231dac7951ec60289,0x6b9c6a50c36e936b18,0xaac57ce2aba27b0c1e,0xbd26008ec3e1adbf33,0x98c5adbf7b5446d404,0x95d4b27614f56a38b2,0x9ae07ee0d6e673161,0xc5a2c380a497271869,0xb71f73afc964722ecb,0xe9c163d31f38e92901,0x155511f6783ea8680e,0x2f3845ec460b582a70,0x4723c76dd43548fd48,0xa709cc9212329372fd,0x94a2f087b9319def8,0x3fbac9f48d2c0fd1bb],
[0x6fe3110bbc96e910f5,0xea1503b344d1abacfd,0xc4c6493f8b28cb137d,0x104084939a66f7990e,0xab8df4e9c3021bb3a1,0x25ef32913dc2c344b0,0x968cea9ddea6eb3d43,0x58267492d88fef8e0,0xaa6b73e91014b9e4bd,0xf71a3b2c59003ab252,0x7f4a0d3ceb426e4b8c,0x97c25d0721b3f10774,0x2ce4c11b59216bee00,0xc7c0662247fcc92aa1,0xbda9a8d0e965fca8fc,0xf99bc5598105f531b3,0x6b794fa3f19f5829b4,0xdc3d58ecf84cb8188f,0x8d353a460dc0b2f2c5,0x1b81c3fc3519326ced,0x8ef22355652bf2ec3e,0x1cc15e20642dd7f089,0xfb55a56877417a6fae,0xb79cdbbba831902f21],
[0xa38acfc50570be1e4d,0xb1afddf140d0ce5320,0x127cae040eebdbae04,0x29c195a2d6fb2e0847,0xb35397e538a14fb7ec,0x8672e1fb5a6464a61,0xeaaa227e0f13b57f38,0xcd0995b052df99bb8a,0x479fb896d62c6967ad,0x8adad932f9aba7b150,0xf880adbd7fd6539954,0x1572d68e0f6bb8d508,0x54388b7f0e2de7c98f,0x48f3ce0a529e8a7d0,0xd0ef4dea3ce16ea945,0x5b0038f0ae32cced27,0xdd15b8b877d34805ab,0xf9e84de37dca7bee5,0x3ff194db83e6ac64c9,0x40c59d85a2bdec7caf,0x5de78da797a7efda76,0xe0aac4f5ecffe9297,0xb10984bda1014e5467,0x789382d878bf030e74],
[0x93a78329bbe749679a,0x1ff93ad76348b393d0,0xf1136104ab473d2e81,0x9a2b856bf68931b284,0xf0832a02ab5d26e0eb,0xc98739b0b899fca4ad,0xc29a128d7695ed753,0x9a8ad5b646aa07aa3a,0xab62f813d92026d233,0x4fb1b59b6d6283ec9d,0xe7ebdea65131f4ae35,0xe29a775b5e6446f5ae,0x651a37bf80463076d8,0x488b9611062a727cfc,0xb2ce5d466d7e2216b,0x9d7e1aa3da931eab9d,0xb204aa444e642169,0x61b623b279ab07e551,0xab222c78fedb42d579,0x940dd325782e2ef849,0xdd051487b7d2888285,0xb6756bc46bd25a73b0,0x8416f71acf101268e4,0xf7f3fcd0d78f84f897],
[0xdb01bb060da8f033e8,0x33828344c8c5174626,0xe2b8a77b6cd42c934f,0xf6c07d6f586874dfdf,0x94d04ff5d403857ea2,0x63766c077d3c4b2806,0xf13cde301789f8ab93,0xbc233bf21e9d0d7d94,0x98ccc0c21aae2b3259,0x668bd0a7eaf66713ee,0x7899d41e7b58465f92,0x7e2d2507dc39406d6c,0x4cf7ecc0cb9e55974,0xa17e317ea64c920c21,0x92664bafea1ecc10e,0x4eeaae4820b0c0eb53,0xc39555fa7a1bdd044c,0x5fc1f4ebd4da43171d,0xa34c8999da0f8f1af3,0x22b80803176269fd14,0x287f89fd716e12196,0x9a423815b8e730d0fb,0x6f80eb1898f70cf89a,0x612a8c3b03d2e77cdf],
[0x62f6aaa3a8e071db7e,0x72eff659327781261c,0xe22fa2a027caaaff91,0x6413aeaea0c3426ad6,0x214d745302d0d877fc,0x30c530ce46ff799ae6,0x483736a30087f8ae0e,0x29196fe0d002ec0926,0x14bab9b66addb4ecb0,0xe2e0a0644755b2b73f,0xf9072ed38a37cc2fb5,0xecedcaf568cf8df0e5,0x947cf928c54c6101e5,0x3a27bcd08bea1d73d,0x37aabe0d9de023ced2,0xd63106a02867062182,0x64d776894e661dfa38,0x4e431b18c3d47c22cf,0xfd9969f65754f72836,0x7b2d8e18e86396748,0xd1ec220eed5b7e16f5,0x237905885805662768,0xcc722a0e5a3fd184de,0x924325ff0a9981f003],
[0x4dc6071788b703b4f8,0x8566881c6a2b15adce,0xef07a064cd343f6b51,0xf6b24ff09c37398fc8,0x262c4accf600e405ef,0xee74647cf573dec168,0xcc9e0a60c6bc83da46,0x7fe183f05c60c2cc84,0xd664ae39482fee0ad8,0xded42f38b0d50fa3e8,0x466355136fdd0293cb,0x42f615fb2f246e47b2,0x2f7fd09b624ccaa217,0x87eabe2a245e8d2be2,0xde1d0db28a5d2b4d5d,0xbc18e622abbb12a64,0xe56b3c335f81a15b74,0xa4b3a8647f644acc69,0x2a1282d435cc846033,0x95aedfc8a7d59f6f3e,0x97084342a87f1f7c69,0xda38534de410f6f33d,0x330c84bbcff353d206,0x87253a8f4d8c3a71b7],
[0x22e545e0b42442d2fe,0xefa600e391e5f526f,0x79ad4710f474273615,0x14cd4df0a609f48025,0xf0f09b520f374583ca,0x726faa1aad57cec252,0x1e21c6bad34bb9ee0e,0x39ca3841af88c83545,0xec88baef13c7aeaead,0x2579c2e1d88554d2a7,0x7c623c1ffcc164e8c2,0xc4589b783455a78d4c,0xcc94633ac0c8040bc7,0xec4c51eedfb4045c32,0x21823db5c1b077d099,0xc705399500c4ed51,0x8a626d82f74282f140,0xd2a6f9a8cfd8f0b7fb,0x8eaad6aead948514a0,0xab8a8c3b1c9d9870de,0xcfdeab51fa184a94d5,0xf3940837c8f83fd108,0xca53fa59a69c41422,0xa1c3d41bcd1cf3d541],
[0x7a885cc4455eb46b09,0xe9606a50e78e30ae03,0xdfc2450bb7205ef2c0,0xaf6506ae68b30dc8b8,0x99abad3d3d57f25db7,0x7219711815919ed8d4,0x3c7d40fe333cf357be,0x3f0ce7ef9b44d691dd,0x17d700573c95ccf1a0,0x6256a365d3bbf4e456,0xabaa95d4894059e1d2,0x8b4711ee8a4e9a6285,0xedf23850c42599f2ab,0x412c6068c3eb77e4d4,0xc0037408aa46e6be7f,0x9fa2748f2b6cbf2ce4,0x5f680c594d4be9e978,0xb6dbf4396c54faa90f,0x5f184be0d414103210,0x6ffcdcbf32ee34cd1e,0xbc46aa73dc74bb8ca7,0x9731e39bfc7302d968,0x3c2064291630f98929,0xa0d1dade888befb47b],
[0xde31d67a58ca899cc3,0x87b0bde64932a40f2a,0x922d57a482971593eb,0x46c81ca7c969ddf574,0xe10cc4008c4cc47008,0xc34dfd5faed5ae9936,0xc744aa1232369c1ca5,0x5ef239742b541e7fd6,0x1393c26c897cf5656a,0xacebbf638f9d47f7f5,0x3a03cd56dee60672d6,0x8aeb713c1a5b93ab2d,0x2b5609699f35843e3a,0xb22483b8504dee755b,0x80b3b4d5784f5fd12e,0x42679394e9b613320e,0x2cb098d0e0a3f9cac2,0x292d49476ee5e74643,0x5d3842d7134aad45f0,0x23dcbfd8243a2145ff,0x165c2a096757e7b283,0x111103e93d8f467b62,0x59fb2794c28c35aa45,0x13418c15b4896c15c7],
[0x1fb5333750a7fc28aa,0xa92391c0e91839c9ba,0xef5269d22ddb5db8db,0x40cadfbbd6d8e48b1f,0x21852cc0b39bf4a0b1,0xb817ab3546b7c2c9ba,0xc360b4bacb9dd585b4,0xfe9a23196805bd2a00,0x40cf7611e1ad7cd996,0x3cc6ce593993bf463a,0x900b249962599d0b43,0xcf3dc0707b8fb00004,0x386a289b0ed0294f7f,0xf650be55cb1636c477,0x53df43864de8853773,0x7fc940ef21787dc455,0xc46bac2ea30b891ec9,0xbe3137799bfd6ac972,0x1385cc0ab97b405000,0x11580e45da49ed3908,0xae72f126c2be4869a0,0x5797ed35d002e3acc,0xe7bc3babba71f996e6,0x293a25565a0798f212],
[0xa9a32aa2c36b8ed2d1,0x53f0df10c279fbc89f,0xc92581104f9ba41b93,0x18a8b179480ff5484d,0x26aa9b2893977571cf,0xb4b5264e763b41a761,0xf5079e140efbb85f7b,0xf2f4219cd8e6325c0,0x85303ea4d0cc5be4d2,0x6cd921f52b6cf28a36,0xf735aa00fe51c6f8f,0x26af0f502d047a3ea1,0xdc7ea2a09cc8fdb51c,0xcb020a690afb5b9713,0x824f13961fca615399,0x51d31e1747a73662af,0x3c83a34dc7d9ca6dd6,0x69aa89c3d674e00ef7,0x236ed76fa504770a38,0x2b7195a8f7322d5f89,0x85c1ad2ae133962926,0x491c0d95766a7c3a5,0x592784d7c809f3a022,0x66efae01b9814fa41f],
[0x563203c784dedd7c4f,0xb04f5c1f9ca7b01405,0x83829c913150d74c35,0xdda289190dc3fd29d1,0xef8b4010527adf8d9,0x9282ff0d4ce52ed521,0x4eb4b9f26d864f089a,0xffab3a694f8fe2044a,0xb98a2454e8468649d2,0x89b6b90a2177ffe97d,0x30db52446bf45400ab,0x2c15ff8d547d564b7f,0xbb77e1e61de810cfa2,0x5b72b8c88739116af,0x46df03a0a923c7280a,0x30205611cdf6f0c539,0x9a4f230e7392c53021,0x206c0163e282d54523,0x21f9003bbfc6ab882e,0x108477b71fd0cfe78d,0xff3b4d2ad94007328d,0x9645f4f33d9eff727f,0xcb47256636ca38d02,0xacfbfbf95c181219f4],
[0x526f668d791661483c,0x51c9b9b1e323db7690,0x22245accf543d1bb1d,0x6c920d570d637f370a,0x3005cedf9469078964,0xd3776278249483d1ac,0xaf74b6d53b03e1291,0x6ebf285562e36a533c,0x889ff7373fd0cb8ce0,0x8d317fe52804097891,0xb19c401a59d3d335a5,0x35a034e69b6062dd77,0x24fd83a4a5c85fa030,0x853e226a8916caaf2d,0x24cd0b7e5990f88699,0x5e219f0319f9fd0fa5,0x180b40f7b388b87851,0xe695e4a62701179fbd,0x463b4b5ea4b3424376,0xbb73aaeada76de1bf7,0xa36b2022c886308b34,0xa34bd0b5af9b859299,0x89b5ab9af14f9ed69f,0xbfbc6fa7ee12fe9fb9]]

def tile12 : List (List Nat) :=
[[0xeb4f677fdf372223f8,0xbc9b1eed7f9da5bc2c,0xc57b0955db0c7f8da2,0x1a999ab79f4effdabc,0x50536bf947133e6af6,0x5957e74ffe5420ce0,0x38355461c6ecf44697,0xa2aad645ea1274b1f2,0x7fe5c291bf8cf55931,0x85b9c30c106b1c0c21,0x41c23e3810dcc1f47,0xc75f71ee5a517fd702,0x2e08445dd7995fae6,0x676b3240e67fba0d5a,0x46d9fce09747e36bbc,0x63c602c6786f0dfd47,0x78ebdb4ca804c63bad,0xece3efe80700e0180,0x906940656e5e3c4867,0xf9eac5180f619831e,0x32b497cf7bcab5cd51,0xfbb77c1aabddb444cc,0xc9407886493b86e2b3,0x654d5423002cf18c83],
[0x765063af76ad4f34ea,0x67c0aed95e2b8e95a0,0x7a438b384034e1fbad,0x6da942e0588a57ef88,0x865f6fe6bf6545b95d,0xc01445d07731226693,0xf0ce8a325e847f9082,0xdbe6be2c4f2dff0913,0x151bbe392daf4d6a74,0x316934ddb04fb101c5,0x9f16fd5116756d,0x478025e5bf956e5134,0x980bb295f326ffb261,0x3ee0ac0133b59edef0,0x4c55cafa3fcfa549c1,0x2bf73afba3a9989241,0xc2bd0d6ece619b7c47,0xfeb3801a74d6a65439,0x661045f33a6b4f34ca,0x2e83b4abdbf78b4c71,0x41bd30de2dbf67fb96,0xfe0ec927a5fab30c60,0x871af23d69f7320b90,0x43196a6d6bc9dd2b2f],
[0xc82fb1616432bb535,0x8cdee4377ef7dc293e,0x725f8655e667b529dd,0x82c97aad9eed2a4c80,0x222a5cfe83111d4076,0xe2a564c95f8b985354,0xb722552eb8bfb43453,0xf063d32e955eafded4,0x90af5ee5e2890a46bf,0x6ab268ef3761834960,0x49c7563c0d185c9737,0xcd5513a46b5d83f96b,0xb2e46936ccd8f9a191,0xe34d190cb0c13e692d,0x13ee5f5dd070e875a,0x801e88a95d69b56de,0xb079cb3631768dac72,0x60fb7c67bbaee37d70,0x428fba32bd47e7d3cd,0x5d3e2581037edee365,0xeac64486ec7457535b,0x7bbca32097bbcb701a,0x9c19e9fbc68ae74bd7,0x7153eba126a21b8d8f],
[0x4693efa3963cc28676,0xaee7dad0116ed5d7a0,0x54fcfac1134456ea21,0x3ac5f8acf412d3cda,0xff56432266cbd487e2,0x205413ff1097f17ab,0x54d13aa9213ee4eb51,0x3b437d87eb05ececbf,0xa4c06037c2b6a7f1dd,0x5e7cb6ca12731b9f0f,0x80c3b7f13cbd4d93a7,0xa2b0ab2b3ef5278586,0x6e84835eb3ebeeb87d,0x65c2155032c4aaddd2,0x3152fb008cfaf8cccb,0x19bd4dee34930de16a,0xfd45a1444b663351b6,0x237346466bdf277379,0xc4d1f1b4500b12b10a,0xa9f63b9e111272285e,0xab81406e86091678f9,0x1a780443c03768930f,0xd8a16852348a7862a1,0x47953c0edbef9774b2],
[0xe24626b1eb23b379ea,0xe769391dc4cd735111,0x11f60b8d8e991ebe02,0x90a9e829b43510136e,0x2a2ce5da5c0edf419e,0x4ca79674a6a79bbc1a,0xb6efed32ae190ffcca,0xfb0dba89a15f0dc3ae,0x29416ca793ade66865,0x886e6d463909cb6f6,0x846f71dd6fd59d283f,0xab7803c158dcb6195c,0x3d1b0dcc1ef21bd521,0xc0761b5df67f75f322,0x61ac89e777cee1ff6b,0x82a9218e557922c2cb,0xc426b6f63c3eb715f,0xff0d635feee8aef0b5,0xbd1199b0adbcc9443c,0x638eed31c2bd9586c6,0x8e23705970b1870b41,0x43a86e63c88fd1b96,0x1ffdf5016fc42a789b,0xdfb300139daa29d7f8],
[0x85e11c2b4f85003a7e,0xb77720cadca6a12ea8,0x3ebe3bd540f606663c,0x9673d0d78537a529e,0xddc00869a1dab5c5a9,0xa391da12d7eea41ce8,0x21ab6237463b9b77f0,0x1f8f96a8560d3b190e,0x423f111009a47b1ab,0xb6a8103b71d22b8651,0x419c8b9ebc111fecae,0xee9bf95f9157950985,0x4d4c40897638ccb75a,0x250d5019d41a990233,0x6fbd42b34ff876d661,0x3dddedb5168595a6a4,0x9e2bf81075e6581c94,0x8fd5a3051f03137c24,0x983a6adeead03eb3d2,0x52d3014dfbf75baec0,0xa5e3675922989ce1b0,0x2ab431e1e3ba0acbe3,0x2e6bed13e1500a030c,0xa59060e82d354b7004],
[0xc6dff7148c56ce6b3f,0x4b67a59819274ea057,0x8364a57b8bf7679ca6,0x6cb7fc995dd6e3d6fe,0x3f4d0e0afe02d8e7a9,0x3a3dba20fbaa22d784,0xad387ad93fdd11f466,0xfd538ddd709b84df8b,0x1c4244dec7b896f327,0xedf43faf4d01233f7c,0xf76385e728f38a2e86,0x31c7cb48494a3516c,0xee62ebe7cbeac1a775,0xb40a8eb6bb109cd4cf,0xfcc1aca643adc146f5,0x1de6b84dc4952d26a0,0x7f257e3f963039f6a2,0x5726cd353c6793b486,0x80fd73626c9aa71971,0x230178023802912dab,0x18b48017223e713916,0xd6fff4f471b63a1d03,0x90c81aa1d175a75d,0x59f368dd8e0484d5ab],
[0x43056cc7d71f11f3c6,0xc93723d052a8c67bc,0x2534e0a0c1f4025b83,0x6411c19394813b6a9c,0x7a60c36f9ce1c5a252,0xc7105927d85b0c8dda,0x915c991b5f4a11b245,0xb04ebce97884749df6,0x70eddfb9231f77f08b,0x845a8804fb3eb6ba5d,0xc81b08ca1857e16001,0xeb55dc87cbe391f27a,0xd0e7fbb93f8f096437,0xf20fc7c10ef9fe7961,0x125200158248b4848a,0x590f4f44504177b358,0x4c89b86553d8470694,0xd1d415d61df28906f1,0xf1ac9ee32a9b22a2de,0x7955b67690ea2a607d,0xaa1283a6f10740f6d,0x18882ed525ebc50c5,0xeb8c5932eb9a570a4,0x63781a4c8f88861337],
[0xf2257e5fca1fc76867,0xefd7f7a3c3182ab1ed,0x6b30d941cf42873d1b,0xcc90e77d81f38e6a0b,0x51e12639b21a252b37,0x6b9163ef694d681f26,0xf23d87a939df758fed,0x3cb4d64e2a5dd248ae,0xaf2df86b10024a60ce,0xf1846f172aa2f5137e,0x6276cb4c1379599985,0x402a931be0b0a6f357,0x6f941ff2f2efe029e4,0x4f52f2fe344e76aa,0xf86ffea1ab2bb89bd,0x318ea6ce0e259dae8d,0xa173ac4b137cb777cf,0xde0aade7ae12cfb881,0x1eb155733c78aae5b8,0xb41e829fe8d6a1dbd4,0xe115530132d250df54,0xdb99a8ae34cb200ab,0x752f2087dcaeaaace2,0x4adbae791ba7f5660c],
[0x70d560b4537175cd18,0xf0d5c55587ed2785f7,0x339c7eb7845a280a06,0x97f477c04548a7afd6,0xb68d40b03dfecc44d0,0x391c06402accf80506,0x8e403f9a61ea608c3c,0x172ef221d0b88b0b85,0x89b1ca0cf4e098c6ca,0xa96f952156af9be31a,0x3f32d8f270d7f36e43,0x74d2ab718c3d9c25bb,0x2f3e0010b2da83aca9,0xacbd27bb59019b8bab,0x3b778250ac40d1de93,0x42396363903eef41ca,0xf8f629bece155e5a91,0x44344293351daf66ba,0x19bfaec3ad6bdde934,0xe3394a8353d99642c3,0x84e5a2655ad3223a1f,0xda5efc52371007e9cb,0xfb509fce713c424e48,0x29ce2a820dd6f1c957],
[0xecdac01d34314c3049,0xa2b2c267ad29f21227,0x9c957d9be7bd987461,0xc0f9fe059220b81eee,0x65326896923f099bc8,0x7e97e88f86bcd3b203,0x4fcd86117f2b20e8d6,0x2f7fd60aa2b83979cf,0x75353d04624a2a2781,0x7e1b2aa640ff5dca6b,0x55a3e8de2f7d40e551,0xc3698d8549f6d360eb,0xeb70d2e1ebd8f3a5e6,0xc7a31168e53879cb0e,0xc53acdc3099dec4ae7,0xd97ff7ec4b1f3606df,0x69e8a16d6ff7c372dc,0xcf01daa994e124c39,0x4dbc3ad22fa53c6853,0x3f76e686c0ae9094f0,0xb24ac1d10423c00a17,0xe28a65cc75bc01cf3f,0x6b05ffbe410ebe135b,0xdce0e06abb52877355],
[0xf5d5af8a4215627257,0x88d1ae7fce51d83300,0x5227910272dd58dde4,0x35407236f03f89c883,0x4ae86ae1211b9ccc73,0xe7be884acc2b4c8b5,0x73d9e11ae363f9c7b2,0xf11b5ddf3b950a1a0e,0x9f39648761bd712ac8,0xcc0874ebc9fa0bc34c,0x8d7fa2d1c944006b62,0x8e012e734c30e57084,0x4ae43c4039272422f0,0xa35f705403c75efb75,0x5305b2bbe263a9e151,0x80ee09d7271c3b4998,0xc1fa44da713f75f519,0x4ff06c1f0169abdd20,0xe74d49a0a8ba7e3871,0xd739f795716a41b506,0x2d05743b30fdf8c4af,0x490b0442b5e54b5525,0xfa7fd36a4307be1bed,0x7e3165b65260a6b782],
[0xa850ed706c2eacce18,0x737f8fb46846e9e051,0xcf893897c01cc56dc4,0xec8f6606fde708b659,0x8df394e1abc0b31b70,0xde881b6e5d4455bad6,0xbb26ba4b199a94ee5d,0x20237563e40f6002c9,0x4f5c03da275fb229b8,0x9dcfa56049c781be6a,0xb70cdd7e863e5b6a7f,0xac9eb2d154a3a4770b,0xa21c7cb06bf48222c5,0xc7a89b47a43fe8168,0x2eac84f9d231c6751e,0xedb00e0d310ab33ddb,0x7f8f475866935387e4,0x76db67e384b6214728,0x6ea3631ae85eddf087,0xa3a86c7c31f43e728e,0x2b14468da4fb32f050,0xee483c3845ba6d3eb5,0x7d42515ce5c891bd3c,0xb885f167f0f84c8190],
[0x66cbeb3e53aa1fb6fc,0xb9dce96653463f8ccd,0x8bfd0bc47c3cbe9609,0xc80f74c1993f24835b,0x842de631aefabcb49,0xa66c98b57904673326,0x3ec3457408aef43dfd,0x5056f8098237f6c03d,0xf7c2a7c073bc2e10bd,0x5754e62fb541318134,0xd667aff210752f7b2c,0x1e33377703a72619b5,0xcdec9c00c84c2ae86,0xb4019177a1c0947e15,0x2cfb92d79fd457b232,0xc42f1e40ed472470e3,0x6d132acc0f081cb663,0x5e9b4bfc0ca1c75394,0x2c8d472aa1ea90fcb0,0x7e3c380e9f8f71be70,0x6548fff0eefd49afcd,0x93f05713db153e70d1,0x18286934b7f759c33a,0xf8852ed1fb84525066],
[0x3562fe4030a1e908d5,0x6321a7c6d65d696baa,0x309cb08f82545edfcc,0x8ef49f20e4aab2e4d5,0xa5b8cc327894912be2,0x59b3d440c1d1b6b312,0x8995e5f912954fdb09,0x98fa0b41257ca88136,0x5bdc4c3f1c5ef701df,0xb0c34424f576999b82,0x2bc3004be1c632b9c2,0x23a573e51a84a61bfd,0x259bb887b2d520b33a,0x6a343077cea2bc3d56,0x2d48f922221fc01408,0x763f21663d5fcde9dc,0xa2a30f2ba1217c13ae,0x72966fbc6411d2341c,0xb3892e0887a1fd6c71,0x791a816cee2b8d0a8a,0xc5c752d5b72698d0a0,0x398bc64768874dce0b,0x1c7b0296a365c7bba1,0xe4d0a60f1f1d2b0fff],
[0xc5a37e593acbf98d2d,0x43e6a87ff66efc5040,0xfa905901776a6df52e,0x416bb0c4bfb3d61caa,0x489afdfe0f05d5a5c7,0x5df8f9d9c2e8d2b27a,0x498dff89d611b76a07,0x370417cbd2f59141f2,0xa10719943848765a4,0xc1bc1de0792db9f949,0x96572da92c8de50bda,0x3a79ecc1c478019758,0xb178f1d141339873a5,0x9678a387b95baea271,0x20ce6fd6ad59caf41d,0x90ffd1d5dbb2297f0,0x23a1aef6d9a880e9ef,0x2786370e2ca237d80b,0xce87fd9ef831947cde,0x79ab813e874edf0c45,0x81e0e0a17e44bfd46e,0xa0b740abb5f57daf22,0x70063879c9b0bb9b2f,0xb721799408d45e5083]]

def tile13 : List (List Nat) :=
[[0x3b5893484ecfa3fdf1,0x86a54d1c452122ee0b,0xc343c569a51569a141,0x367423c439623c8fd2,0xc42c45d8f6e47168de,0x42a593f95dffc0dbab,0x449d43e8c2ee17a688,0xd9ad0e2a113d831c41,0xe6375e5896edac3710,0xd9cd97836496a092d6,0x1aa179288a962830b2,0xe51b724fe2c8dc548a,0x2a922a3882a085a33f,0x2379823414abbf9347,0x276582faed6cadec6d,0xf632ea4267e58ea9ec,0x9a789947ea843f97d,0xcde80835878843156d,0x60e21a32e896764eb4,0x646b6e64ba88a2a1f6,0xcb7965d781559b1565,0x22fcb2b08910c0f6e7,0x13c151d44e7bf3b401,0x7ed2b6869ee195b7e1],
[0x793f6ab5144bbf8e09,0x29c21f2127ba8cfae,0xfb2d584b873bcad465,0x63812e752c46ef92d5,0x3ee6b6d51884a78b48,0x76ec8d61374c17247c,0xd19cfbad633693c2c1,0xd8a6814bf7f3ed487b,0x377d090bed98d72695,0xea233382b790e35c19,0xec9926ced088f7a29f,0x6490cbb89015d1bd5c,0x1e99ab90c8fa107fa5,0xace1cdbfe0dcbef9a6,0x1c90692a72fff12050,0xa9d28ab68f2851942d,0x6d08eeef859d5c7005,0x7970f6af3ae68fa1b3,0x30c22b0f5528c6fe,0xac030f2567a64183a,0xfc530a02d4d1fe82d7,0x9e7b18c395cdf33f61,0xa5e5897525201bde74,0x264a4efff158d941fd],
[0xb776a5fdb0351b1d5d,0xd2b84f5d0713b5bbb,0xaf71f09811d067110c,0x31c38575a4c66d54ef,0x74ccbf052adf1dd9b7,0xa2f81e2e3fd170233d,0x9f4978e6733278b837,0x104a3b921f20d773b9,0x9a65921044d9953a5e,0x6b072ee2e387b7fc6c,0x614b612d7ec78539d,0x36d4470e0d8864ee68,0x75f45573b3c60e90cd,0x619e4186481c3bbf99,0x559d0178cd18130094,0x930393f2929430862b,0x5fe34b7414b2dc4c71,0x4ac8eee1da6d54d261,0x875c0f8217482539c6,0xb57c33c9223d661a3f,0x9c9efd6da72009f30e,0x22de17c4d7fb6b32a0,0xca1fb9641ce7a780a3,0x4a43742a6e43bf8be4],
[0xf276d6ebb8aeb7f117,0xfbc1b49fe40ac5dc81,0xe383994d5760c01d5,0xa56844018dfe68922c,0x8e37456c259a77d697,0x8f4daa3b2b0bbac256,0x12be7f319b4c2dd2bb,0x61ca728beaf1e7a3ab,0x7dfbee0a90ea03c2fa,0xc4b6542d05f1a7b1c6,0x5746500b6fb015c7a0,0xdd4abb8b5f8b477131,0x86f5c5e1cd273b8531,0xc84a5859c0d3296d46,0x43094c46f9b1078358,0x63873d7010cfbad418,0x6837c2137ff446c008,0x123e032af1791f8808,0x54633adcb13331846e,0xac7d5e957c208c15d2,0xac163fc3bd86f22ef,0xbae0b4803e2640fe63,0xe4d366d9b21505cf7f,0x5429f66bf8021956e3],
[0xe25fac6678952efdc,0x26d8b71b1619c74ac0,0xd54830939e2d4e6676,0xe28402dff311cd9a85,0x1cef1674e028a130f6,0x5af993bb88afa27f35,0x77aaf3ddc8eb5c1824,0x336c05b377350b409b,0x40047c3afc3ee097f,0xa7736260b463add21,0x1b90e9e52fe8e892a3,0xc8f128b22e02f4cf3e,0x6db2b20950153407,0xf910c3721d695869ab,0x6891d0e4525580ceee,0x9ffac5f0f4d9e0dd07,0x2f399b6278f38a1878,0x673ef9fb0427104f80,0xc8f165ff5943fac460,0xe7778aa676d322b878,0x9f6299c44f9800857d,0xf7384f30d63346cb39,0xc7407d97b7d57f4a9b,0xe2db1971e30533fa53],
[0x2c6d53cad3c6896d82,0xb770b110fdc91e1e32,0xde932a41d5de0620af,0x46a7fdad0eac1f526a,0xb70eb0f3eeef9dcbae,0x494a1f8d1619027556,0x9701c3d2d8c21569b5,0x1de0a8ca5a41288ff5,0xfb83df0c6e412602e4,0x28bb0a4868474e3719,0x2b1a1d077967b20267,0x73e4b66117dd559b2f,0xb46c74c5e17fcc69cd,0xc46c4d4d5c9ee7b868,0xf233cb6f231c16e246,0x29f4b42806ca9448be,0x5f9ecd7bf106376199,0xfcb5dda1b1438ad657,0xa8a22771573b7fc69b,0xc87eec70247a1c0359,0xb8d55441d45b8095d3,0x1b40c853781908b80,0xe2f9e65e3070bce964,0x7c9afd9d2481cf7fae],
[0x5fe9b5ce39ebe407d7,0x60b53f49eb1e0052e9,0x81a5448df82bebd3a7,0x5de5956f761a3c43b1,0xa2fe716c82fa35f5e1,0x73d9c29387dd364043,0xd30cff253ea884b2e,0xaff496a5c2d2b39cdd,0xd8f1adf8283768eee2,0xdacaf9bdcf9e4e5d61,0xb6a03f4535e577f60b,0xf269169101ac4f2a13,0x52720887cb99cf3f64,0x408e5db183b6912b32,0x193c123d8d277f637e,0xd3ff6db4809ed8b7d,0xb411f91a90cbef079c,0x6633c8f3cb0a9b7d35,0xef5df719991994969,0x808906f21556cde57f,0xf059a24dcea0d21d5f,0xfb7213b7093c02eab8,0x795586009cf68d636a,0x984424d2f5067c33d7],
[0xbeb346b31382189f7a,0x7805d9e17fca88261e,0x4fb1f8bbd41b8ca9fb,0x1b28709d590e38ae0,0xae70b3f828175c34bd,0x737fcccb89a403406e,0xb5f119bf87f959a142,0x448885743e5c62d2df,0x79463a58ecf2cba37d,0xf2012f3341d5be9035,0x114592ea9e5b413885,0xcf7439f6cb5f24caa3,0x2c60e9850cf0cb5bad,0xdfe9501924f57267cc,0x300a8f1dc6b7beb45a,0x527a1c6165984688d1,0xfd1fad3f44808f38fc,0x8788ac2a75352d22c2,0xdd9adc70a68493246d,0x6b4e8027673b790f01,0x54c81e1b511e7dfab5,0xdf1f20dfaba129e1d7,0xb9670d20038307aefe,0x58fefc7d2776344639],
[0xd7cf4cfff849a0535d,0xbd205a9764eb6902d1,0x3c2e5f3d8d7cb9433b,0xf42b2bece315997458,0xa1dca0612d75eedfc7,0x23f9a523da046b13db,0x6d250135b26f87ae1a,0x4a66310da89c94630d,0xa440937a11d7f66995,0x1339bc8d294d6cc855,0x22432d6db9a00f75ef,0x8efa28b71935494c82,0x99ae589658b0e84693,0x9aae26b29b7dfb1eb5,0x799ad4d641ce40aa61,0xae2929466c32dffd78,0x6c4d8b792905106b21,0x4442ed67c4e845ef7e,0xda0f5cbbdcfd8d0d69,0xf314bbdd398bab6cee,0x22578261082d52beca,0x5b3725694d42d84b00,0x1421f58002689cab8e,0x33bd62816fa3690d5e],
[0x984243b979f590b6a0,0x215c1dacecfa9ea360,0x22901d29398ed09b04,0x8ad705d0c12556f5b0,0xa044cf0ccaacd95a69,0x47fd59bf3ab4303dda,0xcfb65a9412e6f1e3a7,0x354f927811fd9de62e,0x4255afd19b9bf2313c,0x6a85b618c90c4e033b,0x6dbee9b80ef3286806,0x5a7a5e0c05b74c6128,0x533a3813617e8ae5c9,0x53634bc5e0d1a02925,0xc8ccb68bff5f160ede,0x4d4afd369c5b002207,0x516db815be583234b7,0x13ae681057cf54a929,0xa53ebcabf3b2a303c3,0x17142248ba3ffe27ea,0xed1a0080740c67d9b8,0x5b265f619e6ddb3c61,0x863e65c4952080f02f,0x871d3c40949fab800a],
[0x5d5538fb333e0761d4,0xad0201a3aed43bec3,0x3538d489d449f48cb8,0x8415ff83983c356eef,0xfdc9ae51fbb3b45d00,0x6030251f9111095e82,0x26bc6c86152387cd51,0x896e26898042a57511,0xad925f32159a48268c,0xa10387215dc6a03716,0xeaba4643f6d0e285a,0xd9896941415023a7e0,0x92076c482ad9af8246,0xb7672cb6d9f1ee245f,0x4ca50246a1692d8a34,0xbb9a48fbe117b5435a,0xfdaa76eab202133408,0x5d3c3a53e82a48e04e,0xdbd39ec5594027682d,0xd41d85aac4fa765196,0x64fcde96274794e230,0xfb2d6fda00ac36882e,0x56973f99369596548b,0x55467ebcebba3598ff],
[0x94374d9b2f499d1333,0x52255f7630a1ee1bb,0x2a423083fee7dc9861,0xf8d921939311115db,0xb0334fb3dbab51a150,0x94a9aa7a7809264570,0xacb2bedbe7ad5fe1a,0x1b43f7da0fec04c9bd,0x44638200be1d3150bd,0x92cbc97fbb4be636ce,0xe450220f450b29812c,0x75219ac40749d0bf92,0x3145cc97fec3358023,0x6df29d6aa27f9b012a,0x555802c01fc36b126a,0xe36dfd9c9603d28441,0xdead4e3b4e4db8b818,0x763783335c842cc90b,0x275343706e398d86e2,0xc5090610b4cacaf3b9,0x78b6e9f40250d14177,0x156eb19c8f7746ece2,0x8c8f04c8f05db9578,0x96e6305f36044eb3fc],
[0xbadb76bb48fb892e8f,0x1b8e42276cc143d362,0xadb35b85032954b6c4,0x6a654216e1bae1d6de,0x73bcbc6d45a13a1353,0x5ca29525519270bd40,0x6594126e2ad3beab3b,0xac4b8a464bb7e73108,0x20517bdc151a5cf67f,0xbd1997d69b5dbae8a0,0xb17e4c5c8336e81904,0xf2d284bc8d5a33151b,0xa1a93de14088113765,0x742f3061811346e28f,0x5422ee3537683dc1e0,0x4ed719ef0cf0a0a4db,0x1f211b5f598844f6fa,0x49d4923c7d398fb668,0xfa01ad0f576d190ddf,0xf145b38f7f95c44b5,0xa9eb03abc63015d2c0,0xd8f81faf7438166b76,0x16c62030dede4d93d1,0xf224602c61928761ad],
[0x4603060108b657b3f4,0xe52882f559067cd8b1,0xe5d805195a3307014d,0xce19d7b1940449261a,0x1ad36e23add6b97b6b,0x149889926c66f7092b,0x9848e11a549bc689be,0x6dbe7523966c4683cf,0xf932f58423d63a602a,0xacb03d7853b8059721,0xf2d32de0122e422a64,0x85a17d5fa59723b4ed,0x6e22e6970de42110da,0x2340953e160071c05b,0xeba67e6571331ddf24,0xadd65e16dfc4264bbc,0xde46db222ca6cbf300,0x915e67ec0a2219a9d6,0x7d8510f67f8f524db5,0xd3bd873f0990d6d86e,0xeb247ed2eb62c11cae,0xdd3f143266be5474,0x4a29589cf59b49a8f4,0x7e8c2546f0ca8671cd],
[0xe9a3a0ea31278e4b8c,0xb6847bd66639ce0cd2,0x33d8c116c2ee5cc4e4,0x7ea74a8f356e9a1c7f,0x9c4d444d507f453fdc,0xb0eda8a88d30c4b098,0xd4a2e2c773a592041c,0x1334cbc0149ce68b65,0xd16c40fd48d37ae533,0xd45aed76cf7b9d79e,0xa79cf928904937b647,0xe5d8cf866fee1d09c0,0xec83940aa091681467,0x9c053c7200e553fb06,0xfef6f7148a40eb1d69,0xfb67e15e2c7f8f7c2a,0x72665fdae6972dbdf1,0x1bd22b839476c768d1,0xed10b2b60c079061e0,0xa977ea1a05a20deb31,0xd88f9ebf6deb521837,0x30c5203d21227f793e,0x103c8f5547ce979b20,0x77c15ef81b46d8797f],
[0x9fc41833c14239f902,0xf8d5025871687d4193,0x486deccd4b3e4cfcab,0x55736171635c6c6d21,0x1eabe95399d87315cc,0xc128e1294049734751,0xafbf42ba21bb487a1f,0x7226284e86d5483e34,0xd8d4e7909255dd8765,0xeeabdb127f2e152831,0x888f00e1947b6fffd5,0xdbad590c273326c7d1,0xa91506a0b86f7374c0,0x1b24ce0cf58f29075a,0xeb3f9b90ea27e90adf,0x15f505fbc8cc92c0b3,0x892244da37f6a907a,0x590911d4af336483d7,0xeb766a256d067ed1a3,0x974d3dd3e27befc28f,0xb5bb98796ec5f8bb13,0x7d9fae9468b22c4248,0x7bac8a7b479dadea5f,0x3b5f20ebfc0719742f]]

def tile14 : List (List Nat) :=
[[0xd4834726b81d046362,0x70c8586ab12730bebf,0xf60c3c0dd1870b4c53,0x7db9c15de1c4357973,0xd8d4207408647f1979,0xe2c645670e71febee4,0xbdacfb1cf17a866bb0,0xc5079e329068b60e6,0x572f4c18c1dcb3d751,0xf2dbee0a6381f5f6f4,0x87c54138ce8c069f28,0x15aae62cf77ef815cf,0xc31a389e3a026109df,0x3a8ee4d95a90236085,0x99a9449587290cf35a,0x14aafb0dc64c87c16f,0xc580d9bd46fe83cde3,0x6391d049cbe8dbdd2a,0x9e7d2fa924a7a78079,0xe6311d2fc85ff22b6e,0x1e23a2ed819db9c2c,0x4a503a2b12c0805067,0xf7b37ad2e1733b1ca7,0x14f0602c7406849af],
[0x61218c7664f6ecedbb,0xb87f487c363786ba23,0xcc3db41829d2025000,0x32afd179f4c40f903a,0x86b53c29820e58aab7,0x1d0bd8aaf6a11a1b97,0xa581ff46c266b64c37,0x3150be37f04e48f4dc,0x8dc533c0c604f6a6df,0x6aaa32942d0f5d3c9d,0x45cbaee6d4646d5b9c,0x71a2e459fc28b08bd8,0xa654134885a770c2d,0xb82ff5a0571c7b64e0,0xbaf2f6c006c0fe0489,0xc59351f9b14fd4e648,0xa94a660befd121d488,0xb21dbcb2632172bfa0,0xb0554181dc36580777,0xc0927008745c4f573f,0x93d6369e29d007215d,0x3c0f5515b3d7e96a9,0x2229337201d78d614c,0x2b6851c9e63d31042c],
[0xd3318e6d943f52ecfd,0x5d9b87575102b21b5,0xd30f1f96f5c799c9b7,0x9d747e024173f47b3,0x5f0760fb52991ae4b9,0x8144e4dee3e57b7311,0x3ecef6bc750b95e9ef,0xd0a804af56f001b694,0xbad6c5cc27ff27a674,0xc02b18330f5dc8a309,0x8a1c22a870211fc7b3,0x8e4734d993c8203747,0xe9b7a80378d19c5a36,0xbe27554777301ac082,0x495dd07424fed6dec9,0x22be49a4247683b688,0xceb449d77f201530c8,0x8b67df24a02b9e131b,0xbaf8199f3002d254b2,0xfbe4ceb04e28efbf70,0x3c5830adf4eb132bc1,0xb9847e386e1b99a48b,0x8ad9deb9f4f0160df4,0x5c86544a3b0629d027],
[0x3fd89d0c9aed3e5ee1,0x8d2c9cf5492318b9dd,0x4bef1e7cf4eec14e4f,0xeb784a7d4944ac7c72,0x182449e1c55e97921f,0xae790c745b902d3cf5,0x5e38af21fcb67d4752,0x1f5a6f87d3ca7148f9,0x14a26b4f44d08cab54,0x6059a6d8140c83e29b,0x6687f1bd226fcc04d6,0x2784332788f9a91baf,0x7b218073f2f543ec2e,0x31ad34eaa614fe7ed8,0xd66d24fa460e9f1d6,0x89ee261400a4c121cc,0x8f3c02c2f6d598ea04,0x47fd4fbd1819e4b763,0x82c5834776e988e4d1,0xe8e2e8daced135790f,0x92df9668abad30ce96,0x3d7ad71084c42586b5,0x108a889301862b3332,0xcdf198b6204bf9089d],
[0x2a5a4a02c8a7fd64c5,0x5dc3c9fcc9d3aa1f8a,0x1e8c76d472f9a98d77,0x65d8fa5750d6eff75a,0x794b352f87f816e1f9,0x691a30ce5b383ad7c4,0xba5a7103fafd329e66,0x3cafd0371ad4ceefcc,0xcaccda9c04c2c93c92,0x819fa2db5cb12d5fb3,0x944928aeaf8c69927a,0x501444384a0022c530,0x95640a4d532250e1bb,0xf21cc3c0b1cd84d9d9,0xda5a5e90c72dd83c2d,0x987992cf96034342a6,0x17190e69886ff72903,0x934fd0fd6d9ca54280,0xa131031e89ce8ec83f,0xb6fc06ffcef60bc4b9,0xebde5ce33787946599,0x7e7420cb7394055bd7,0x5c9ac261b7de91f464,0x85e67b8fc29562a0c2],
[0x117ad7dac194febf88,0x976b8b2dc97a8c7a03,0x35ae760d30af80799e,0x14f1cb98f3d2a3c92,0x2a77d4c85d1d8089f8,0xfce166979680df4441,0xa1c3fb57af36609774,0xfdca57013413d4447b,0xa699239b4409b61131,0xcc4bc466b77b37bb9,0x4bda2c8f1a6679c002,0x9ac8b580b3d9e56a5f,0xf090efdc3fb463ac1b,0x41feec386af284a515,0x7c1f1422272f12c42b,0xd7ff7802388f11d095,0xa9c2d1172eae95542e,0x3bee9e356381b96d14,0xfcf1bc36254d39610f,0xb8c56ca42bbc95e847,0xfdbefba860b795823a,0x287d35fd73f4f66849,0x8fa73ede4dd4d48c1b,0xc3d947a0421a6d529f],
[0xc4d7094f57df5c0a14,0xd9b6603bf4c9c99d29,0xb65ec325aeaf9a9d15,0x5ba9d2097f3c1ac848,0xb887a9909b9c8cfc22,0xb60ac02c659eabaef3,0x3719b57f8875a0fd81,0x99c428fb17b5d874e3,0xda8775cfd09f6f02c2,0x763982b4afdada9497,0xcc48020192d03edc1b,0x38dee6aa794827499c,0x5e4ef807478fbcce7f,0x452736fae775282743,0x645514bd65659d763e,0x955a545448c736854c,0xebc933f42cb9bdf8d0,0x81d35dc5050d3e4dc3,0xd65e994650abbbe8c7,0x9cad600f752a650f3,0xd76c1eb765a8317902,0x73140e7346ad63dce,0x94a01d399a831526fe,0x11a3fae39b0538f365],
[0x87a795ce4aa271bb55,0x70afcf915d9c453c59,0x1cb068a97131c5bce8,0x7b75850d238e928ce,0xcda5c739e123bde4a7,0x9f59e23dbb71fd95a1,0x69e1461d88ca2a8937,0xe28842e982daf3e98e,0x5b9abf9928190f653a,0xac53c7b5b5fe211a85,0xbc2b28558fc054bee7,0xbe8f8f54fb332f84b6,0x275c01d2d04c5f93f,0xc6860e43933f0b8800,0xc186dc80014f4168a4,0x53d1991cf71a0f05ba,0x7aaacaada7ce582bde,0xe6d43dd507dd4bfa77,0xf1b6100bca038edb43,0x884c958b0eb299a27,0x90c43e992c6551f757,0x31022038ef3130995b,0xc1881582a2b5f7b190,0x4afd91e06d632ea8db],
[0xf3119516409958be6d,0x5db4ddcd121aa3d13d,0x4dfdd91f3c10e8160e,0xa780634294bfedf8e9,0xa5a62223a1c8732fd5,0x9f2af0c0128168778a,0x87787853403d2839d8,0x9ee0205eddb289b7b2,0xb4e3318b63a4bb5d58,0xe8126e6dafe4074541,0x3493448a8cdeefd77e,0xdad89ddad29e155049,0x1380f8cc068295cbfc,0x1faacd63a8fe83d123,0x650376b892172f1b30,0x69611af7ea8824eee1,0xe6bc3ab914102ca017,0xfd9577692da4722cdc,0x2311cbc1ce755b7ca,0x2d06fc4af06be271ac,0x6b724fe79161f209bc,0x335e35d2b54eee83ca,0x2c502f504a9b7a26b,0xcd33dc2c9a8b637e4e],
[0x95112a86811ddb965e,0x4d8fd33265f051885e,0xd981304636e9176a70,0x4226b60621ef98b329,0xe56ffe17c63561746f,0x22785862b4c1674f26,0xcb2008b6637df27607,0x50209a37bd6043e7ae,0x269469c025f33365ed,0x5481399f0db9a7b7de,0x6494b491ef821d634,0xccb8b727a90db451f2,0x2f026792f2279666b8,0x68ae4f014a9bbcea23,0x321d24d2b136260792,0x55276a2c9536075ab5,0x358043de1cbb3d91a2,0x9bd8875ef644a85b50,0x22b7f15d5fdde7715f,0x120a1f1bbdb38fa311,0xcd616452020618efdd,0xc7bd7d5139610813c9,0xa8b2a9aeb6c03375f8,0x8762dde4fd2efcc594],
[0x4e9d4f24f7d3539fa1,0x9fe1e36be52147e125,0xa0af0ef06c5c6a8bc,0x3f8cdcc4a534d75c0,0x24022f495573f5f5ec,0x5176d2c3c6f9bc3f02,0x413ed95e1b7897dfda,0xb70eec6dd3327ea80,0x8643fe79403812a86b,0x4956a3f1f4827879ff,0xb7d679b50141f5e601,0x81b3e10085e161180,0x2f876b36869eeeb18e,0x53a08164f9988f8ac3,0xde0a98681200021f4f,0xd5db8124d19846f483,0xd4c78149bc87327dcd,0x5f52d428b744150649,0x9e7c1f9f9ceedd2491,0xa397d849e95f18d092,0xee39fa18f6a2f20c02,0x14c9773171523ab7f8,0xbbfe63cec586194c71,0x90d66128309cac959],
[0xf222ba19d7040bd460,0x3e38438493ca482869,0xc818b84b9f6e8509e9,0xee24b1aea1518cf3d7,0x4f0d322622d9b853a2,0xd7b9a9ae7827631d65,0x62c05c32b96ffe8f0a,0xfa1a3bfe67ee7bae13,0x7805baef78bb041061,0xe88e49716b18096348,0xff114e6f9e9e3fdd10,0xd3db8339283c7ccdc4,0xdae7f998cac46b51d0,0x3502e9d7fa4c0372e7,0xe487200ceed6780159,0x30be69138da736ac35,0x84f1f3d442a07ab51,0x1e5d1fabdde54f506f,0x691dc0fa213b7f6ad3,0xcd6392ab3f86636702,0xe40fd6bdf53ad74a68,0xb4ac0d7ba83b81985b,0x3c100d0a8421ac2702,0xae2799dd80e57d80aa],
[0x7e2ab1c45dbd153070,0xadeb64041670be1c7b,0x5ff19729d09bcece68,0xbc4fbede83f7971a,0xe4d113168d7e89734b,0x84f9266ee9d9457448,0x28e8f6bfe92a3ac1fa,0xa0bf9f024c9bff84d5,0x5dbf342cbbb48cf1d1,0xe5f51ad85a0ad0a23c,0x183c45a9ffe5ef267e,0xbbd17839c4da34555e,0xe424a6f8a90579244d,0x8fe3b3cc203d70a0d4,0x1e735ed2b828410758,0x97749415fcd959bc73,0x478c9cc8b298af5b83,0xe4dd2466719fa9ed,0xe807d3a21fd8ca2d51,0x18c1686800c7caf627,0x3a7e06a5b91ac34d26,0xe6302397e6cd3ec838,0xedcac664c01708723f,0xaac99e33b707785e24],
[0xa8a930462d9e00f07b,0xc8911924a904fe48cc,0xffd792002da69978a9,0xd7d71162222538001c,0x68237f039d03ca12d2,0xc0b05b0516a8847b99,0x80f73fee991f9493d8,0xf98d2610ab6178c154,0x65f7812038dd32a9ed,0xe0e8404c10be26c16,0x1b42b9fef67f725095,0xc176e1c93503ec8da0,0xf6e5196141183495ca,0xbc9dbbf8edbb92742a,0xf8d5b62d41c0ff8365,0xea170c78996f601690,0x6fafcd10c9dafc2c98,0x67435d2a4d7d9c2346,0xb2b6c1812b1c1a6c5c,0xeb6f7f18da1c275389,0xd19dd7053b67b68742,0x878afc84d01a2efdec,0xa87e0f50d7da5843d4,0xc56337d0d9d57a6f1e],
[0xe2f6c4813bc2242957,0xb19555572430aadf66,0xb3534fbe53126f3d16,0x5746c96e1653368f4d,0x5bba30f17aa040a0b6,0x59f800df494e59974f,0x5f6cde0bc4c6214b96,0x13f89596833ab1b662,0x5c4aa03c051d7a3bc3,0xcbc60b2b2776a833d9,0x31521e69d685c173cc,0xac11c1d8f2f3999c46,0x37349976693d88739b,0xaed831abde991de0f0,0x7d432ce5e008ff426a,0x5c7b31ede056637cf0,0xb9dfc84c95866ea503,0x624ffdd1963714b707,0x40bb09f7660ef17ebb,0xc51b68abc74908f90b,0xd9c8310b4217e0ea,0x85675c0819696efe87,0xb6fbffa510d9ae42dd,0x63dd5738e9facc510],
[0x34d76a9c181e27b0fb,0x418c2c33d138a67c0a,0xdf3147177fb029126a,0x3d23ee88d5f4067a9,0x2238d8e060cd8951be,0x5ebf06baf5da8df2a0,0x1b021212838200486e,0x2d9fe71022e851646c,0x1cb40a9255d0b643d6,0x7488868e6de74d577a,0x29ed413ccb0c505568,0x9d94813e6f077a9aca,0x73a3dbd93497700e4d,0x6e43eabf375d4acd71,0x9f40f20fd9fb364159,0xe17f57a8fce9f150de,0x4c31fc094bcb944673,0x7a1f0b40fbd71da80a,0x3794137ce41ada7703,0x61b1aeb0a736d31196,0x9417ac785226c3ea1e,0xe6abcd99265fc943a6,0x63c4e981ea47558f08,0xafc2f4493d8416f886]]

def tile15 : List (List Nat) :=
[[0x577b43613084c0738,0x81a10d4317495f32fb,0x5c8519ec0a3b1dae1d,0x57fe044a05fb565acf,0xb65ddb9e24e4998978,0x8241c1fddcb536f2e8,0x34af3b5302bfb740c1,0x58700f2abff0ff9ccd,0x6a8e41eacd5d8a1493,0x9011d8476466c894ae,0xe212702ed454fce255,0xe69f2931d7ce09a521,0xe1173550c203be9846,0xcc61522614b81df3d4,0x38df2f596e3c7ecc05,0xa91a2d510d13b90a6c,0x2c102abee94da96892,0x1c15ba3a085a6fe2cf,0xec25fbaa2b829ad743,0x4e013c51682eb8a25c,0x742c5f9fc694e74f94,0xa7d00be485fd565dcd,0x20e8cb752a816a7d86,0xdd141d7cfe0de5545a],
[0x8973ddcbb9604e6956,0xb244f36ce914016201,0x4fcd276b0784296ce2,0xdafe3f9d90b01e8625,0xf2c3d02d2508ff36c3,0x36b634e1fb233a8b6a,0x55e98f9f701fb49a01,0x6e53dae0cb65dd0466,0xa85c48f5aa9b37d149,0xafe1387e0c9bca8c6d,0x796d236133955b5336,0xfc3c34082b6cfc80b7,0x4b29e7efe008dc694,0xa5281801c515f21d05,0x447a139194bc7bf7cd,0x60062450dcedf16bd,0xe1387e0c9b63353d74,0xce224f5fbf15dcbd70,0xf80124da5b94ddaf9,0x32f1d290056a3df2b1,0x969ac5f663ba1e7972,0x472c2e984acabe0772,0x8cf4ebfdb0104566d9,0x162f5bc4bb86f5fc31],
[0xeff38902722624ab4,0x792588935098e854f0,0x3852d971f98f15e473,0x223d179de2b8693a69,0xe1153643058dc02ffb,0x5babc9415616cb9e37,0x6ee9d0d62fcb6e0068,0xbfd6862b4e31d2f010,0xc84ae11c93fd0e9081,0x9d2d4067cbc01073a7,0xe1978de82644dad7d7,0xfbd4761f42d0725b67,0x4a2daff654350a8c78,0x491a16089d5f18a125,0x279293732a43ff859c,0xb49577634df802567d,0x12fa8075099ef3b23f,0xcb1846db645ad5af35,0x47d7cdfd72722cdae2,0x4bff2a4509e8018b3d,0x7a556f987d01971c4c,0x24193303bb37b87ef1,0xb4b92cd5c7264d45c3,0xf4a14cb03d6e316dd],
[0x4a533ed5a3a68a41f8,0x42353c39c378e928af,0x27b1963f3f2b5ebcc2,0xded8da90c337d0513d,0xe1c1e19d413ce9bb3f,0x634da33c25931bc445,0x4918ac94c852fd6d5f,0x8b9843ab10a97e1613,0xaa0d7aecbe9ef1dd25,0xbecc097acde3da71a0,0xfe0d51d88a6b10a59e,0xd82f609cce0f1a7e79,0x37b9eb9a7f1abd00c8,0x507d6244b6e80b724a,0xbe4d96af887d45ada7,0x1a982efd26a4e83da5,0x303fb06108da38de48,0x5642ae7199303febc0,0x5b7c45fe7db0929256,0x671eb5adca5e21c800,0x1163589434962d015e,0xeaee81840229519543,0xcc4e499a829cd712f1,0xb7285131e83c7f4f5a],
[0x3f100a67521ea46bb3,0xaa23c5e44568a078e1,0xc5eab8f20e0cf8fb6d,0x9dde15975c9e6af2d6,0xdf87ac4cb1677bd015,0xe258fe12a5edbd3789,0x960dff05cef4ace67c,0x2ad48ab961a58598ac,0x7177706b91f1abf99c,0xe81d4996a540f7d176,0x6203bb2f4bd7deb0a2,0xe1d328b910f22ae7b6,0x1bc8e0c85c51b17c01,0x4e591fbc4be39226e5,0x98049ff645b04abbeb,0xda2b71e5043b57a9ca,0xecbe6951ed59080832,0xaa984e7fb469d5268,0xc8e94350c33f08d0f8,0x6b710da05550499ffd,0xf4970217f8c469c4b2,0xa8ed59a06f74162a60,0x59e188152f1c180ca8,0x16461554419f20c8d8],
[0x7461756313efc37c5b,0x37c1228b7755712a4c,0x2838c35240ed003d79,0x7dc25a74d618313472,0x23f87ab3f64acea9ec,0x253d89d414d145deba,0xce245f6607554e0016,0xefbb4dcf3296322ce7,0xeee9a3e3ed97e80dd3,0x93f53c6207031f744c,0xa640703f8082a08c88,0xb1147570a674d7b30e,0xff2710c11d94570044,0x21d76bf2dc9f88b8d9,0xae8a06784480a9fe13,0x53b7838d502fd529d6,0x88d522363508bb501e,0xafadcee274847daa6b,0x3e6838fedd393e47b7,0xf9b90782a413b386f1,0x9c1502ea8643edcd41,0xffe6218c4c23e37e5f,0xb45732078e1f590000,0xc33f3c20fa9c982659],
[0x53681730f86ca31351,0x2f7a0343bc388f4b2d,0xf44cfd11c07241ee40,0x1a61e1f5f6c74065c,0xde88527cdd63ac847a,0xfd500ba89b2b23f0b,0xb714a8510f67aa4111,0xaa248ae1e4f3de4e21,0xfda3e2e50ab56d73ce,0x4b47a0f993b52d2e1,0x2f6479b732444f3d51,0x5bcd102a158abba692,0xb47f949fac37ae5a4c,0xef1f415e148699ae81,0xb21988bcfc02df5b4a,0x7cb7506ee56af3f74f,0x781d426711a2c13ba2,0x9eabb13b3f92f09afb,0xb5b92cfdc74254dd74,0xf0a3a8c5fbdf92caf1,0xf84a0e9d64876b2cb0,0xbcc36ddf8ac6f0d8e7,0xe1518de147ccde2c9e,0x1afcd35234070e884f],
[0x9c059111c7f2a61708,0x25df4cc5320c32ca8b,0x83f34508747aab7662,0x58d53c138dd56017f2,0xdaa43ab13378d72d23,0xf081887ee92687d2d3,0x6db3f68c5634431bc2,0x1f30b4c7dc1d27c2b8,0x736bcc5e7913d5d774,0x846ef1f0dcd5425c5a,0x29e5ef0f0474bb2033,0x77cda0cf293690f541,0x2661b6342828f775cc,0x1c9a78aba58b20a342,0x6bca64af6f936835ba,0xdeba97ed7d5dc2ea68,0xa9bcbeadf97068ebc2,0x2e53294579c2d3b22,0x828e39e904da67f8ed,0x84a8a29079d9490636,0x37af6801c24408182e,0x1f501f3aab9f8042aa,0x489cf8d2af6f287927,0x38de414c5f5df191ad],
[0xec01d53424adf8a454,0xc2d50ecc42166785c5,0x6d24682edcadfb6887,0x299347e581b14becc,0x26657dc7c318aeec19,0x7a7bd1774cf7e104b8,0x15803cde6626340c4e,0xaafae0aa01b2dc05d7,0xaee541738a9b2ef618,0x3aede855a8703b2ccf,0xbad92443da1c43451c,0x91f39749a8463db431,0xef9cd6d2bff4719ef6,0x4635d2b2892cb1f9d4,0xd69070a7ecdcc829b9,0x80f0906ef99f214da4,0xefea30dcbe37f536bd,0x5893a6b600cd154329,0xb293a7d375c6d2382a,0x7ce888fa81f8bd952d,0x91cda53d30e1c026c7,0x394556fa62e40470af,0xe98f2fb6ffcad846aa,0x6253bbb1d977c709ca],
[0xad76ce3e39d7d77131,0x70ae8103d2a0ef9c56,0xecd2ea9c67e9a14778,0xfe8703b1d879324967,0xa615953d3ebec94988,0x4b1f54996525af3f7,0x9fb430381df0fce024,0xbccf1f3fc1ef0b066,0xe9beb5b56b7ffc1d59,0x87feff9445217d346,0x35c40077faabadb6c3,0xf6c5e37a54a0a535bc,0x3e71636ef872651a61,0x456a1ade9f78cd40ce,0x7b0b9c0ba7e8c361b7,0x7929f1c6fd32bcb8b8,0xa121ad6fbbc90037f9,0xbb28414e8ef067a2db,0x7e1b2d5de6d27a3ec1,0xbb0e95da3e61d596cb,0x5d7fb8d7bd7d4d0547,0x81c1b9889a1e370e40,0x8bbcd5a109116fe052,0x47aa9ebeacc3dacecb],
[0xd2d3e18b39d83ccfa7,0xc3f567c5e0f361b00c,0xd2beec86478c7f2a16,0xf7a66657a5778d395e,0xeb064e046def91115f,0x712d35a6f3b365ff25,0xffe0399759fb67ae85,0xa43d24724e8c159031,0xa01899d5b66b274b0b,0xf68df30d2316f8f223,0x6d6c6036d74a0562b7,0x4d8439556070a2a5ee,0x8218ec9e6f26a74b21,0x857da1fe32e7d2edb6,0xe437516fded272a966,0x7148f0d06ac9ce008b,0xa8dd3014a25d6b5899,0xd5dece9fe3517ff348,0x828d4278e4c1ebcb9a,0x2b67f4898703eb6c0d,0xd34c429aaf5c39cbe9,0x7282268b39d6cb4049,0x857e39322e299bde1,0x531079cebde4ca39eb],
[0x9990da6a2b11acb2d4,0x59dcfc8153265bcd16,0xb322c442a71e2e19e0,0xaec10bc5a1288c5dab,0x37ad66da53f9bd9720,0x44422a351cd849a0fd,0x5dd41c7a3d661d0bd8,0xe5cb7675466c779120,0x3720785e1663f21518,0x34607bfe68c10d7bae,0xa66fc3170230ad2270,0xe171f508e960b3ea6d,0xcbfc8fa52fe720f81f,0x46984586f80351e0f6,0xe53b1050c69dfefc2a,0x1fec8365f786db495a,0x3866350599b8ad54bc,0x1fedf54d875473a108,0x2fb68f0358cbf6ec20,0x24c76e8178b97478d2,0x758fc884c63a24e293,0x58da5280125cc8b61f,0x52f063ae56f8f7091,0x560250eb9e816e8760],
[0x1967af7cdc8af21ee4,0xf25e41782ed8f1de42,0xc16bcda57aa557b1cb,0x666b470211dbf1822f,0x3f99455b67e2167f84,0xf5f6fddc77f4048a59,0x3e37d06c9facd6846d,0x918da3ce9eba4f7c56,0xf4f39cdcff28c71888,0xaa619e2052c6a6e4c2,0x3e3e96d100feca6082,0x25b69ac8a16c44c3a7,0x2f187375baa68673ac,0xa7e6a9affa62d102b7,0xb218dced38139d5085,0xe8ea07f2076fb351f5,0x8f81887bf21980b0ff,0x272cd0c67757f01581,0xcb90991c11e23f39a,0x9ae937774a09755aff,0xa202df989e3034a39a,0x615f4c58fb6ce1987a,0xd8dc0edfdf0a0ac231,0x7ff500c987cab46b84],
[0x600ae0dcce78d8ec5b,0xd01a4389918e02c379,0xa2a732c4e92e03a612,0xae614c73af343dd9f5,0x268c95fa5c72534a2f,0xfa53de81966efb9292,0xb9460a80d217417704,0xc4e3e88b5b254d4a16,0x15f877691b99d76561,0xe72ffeb0526ab54861,0x2ebf5c96514d37e305,0x852d9496036ff1cefd,0xcad74c5997aac8ef31,0x2efb1be9d1be28ea0f,0x3d0773bc2bba2f2b7e,0x9b73d01c6a8cd9ff96,0xf82d78142e9d575ede,0x7db86bce2ddd668ee5,0x54e0be0655bd4ea739,0x9515ee8daabb0de309,0x137d2e91afe845b4b8,0x793ee4c800856a2a6a,0xe4bc98486afe456e61,0x5839fd72fc8bc72140],
[0x79527252af6e4f4b58,0xc6277b8fff1692eac8,0x2a54dcc223cf17126b,0xbbb79e536099d7678e,0xc27e0cf8a9c75ce2ce,0xae42837bd451344b24,0x2b97d638fb85a4c40,0xfcb5e6795ff77cc04d,0xfa2f986db274f2bdea,0xc00f6feecbf4973ef9,0xc7f6fd1010c857de8e,0x5dc0be505739a95a2,0x40870089c85c7f5070,0xe562967d1060e7bf7e,0x77ccac61462e7d8c03,0x6d833bf83d65877de6,0x1079c0408d88a26536,0xd863548ab159b97c8f,0xe3a51ef873539cad4a,0x67790b8c0cb9e5ccf6,0x21bd7197e19a644f19,0x52359fb72ef07aac2c,0x38b5559e5404fa2050,0x7bcc7117d1720f8f17],
[0xbcee4bb3232a519858,0x42a63fa2455a1cc011,0x884ff951b727123390,0x335b849fecfaad0cea,0xad9a900ea24861a993,0xe7374742d93518cf9d,0xafadd54afcb66f2c2f,0xc8a1025237aa55a550,0x4e52779cbf0b3e0e62,0x2b74bf6150e2a80603,0x8d4bd3665aca96d797,0xddba92bc45c2f52d5c,0x93d4e5c2a35f681eaa,0x3cf3fd852d60a4b7e3,0x5ff95ec93bedcff7ce,0x9bab45387313184911,0x591bbd2675841283b5,0x1d764f6fb86da21cd,0xb26a44bb4258eae517,0x75f074e41ed770de49,0xd52ed1db28dbccefe0,0xa7745cf18ae0380286,0xd91bb47a3ae60db727,0x9c019cfb4f58cfa602]]

def tile16 : List (List Nat) :=
[[0x9eab2247e82f2d68c9,0xb6445a548fe2d11bfa,0xe58b20e67abd5113d8,0xf50b40a81044a21d05,0xc40906d1ecaaab7b87,0xfd378707bb32019502,0xc489826202677df43d,0x70e49bc33b16714fce,0x883280e1ff8a68e6d3,0x2111288c525e9c029f,0xddb2f147990d281c01,0xbb5709ff79f62977ed,0xb216457d299d0e98ae,0xd1693211672c94accc,0x547fa7d2dddcb5801f,0x77774bb53fcbf5184f,0xafa2f3aaad94ba1b35,0xd54533eb744fb050e3,0xe74089820fdd38ff1f,0x232f84f5504f9ec71c,0x96158c17b3775bd6a,0x6b714c3a5cee802585,0xb277d01e4f4d2e4e04,0x60d6c5b623d8a7bcf8],
[0xc0ecb6b28f3adc4097,0xe3df5ef25f1c072738,0xe4be2621ec6ec8d5ee,0x8b1cde8e687e79b36b,0x95a89bb999d076c7a1,0xf4196481f4c3c47fd3,0x1208ebba64d4c40e2,0x44bc3ac602e8e534d5,0x7f3751613c6ebf4fae,0x7176027dced4b26457,0xce6dadaa561732719c,0x251a5accbbd16a37f4,0xe705c44103da842357,0x809c25d98c077bd15,0x3472a62db37f39abd6,0x5498960b55eb2c824a,0x3d8fa1c2934b996824,0x637180aa6d1666a547,0xc32cc7596baf14771d,0xbc621c107f7531499f,0x7738f71e644688dd79,0x9e5caf2a0a311231e0,0x4f4619ede49d5faae6,0xd779d1e22674725411],
[0x3eb8f42cfd5404dffc,0x799364f8bdceb5ed8,0xc703b1b94720c8d2c0,0xc9da2715a0d587a68d,0x49fd88114ec4ababaf,0x52d508996d85fafb94,0x6d78baecc8500e9167,0x5d5e323f4428f9e22b,0x55a8cd5d3c4344ad2,0xd3d4e7ab9725a634f9,0x88797fe6641e1ba50a,0xb23f5cef4c67d81123,0xc96b5b1a19fc1e4146,0x955bb5f68bd29759e3,0xd1268706457dbea090,0x41052325db7f55ba,0x159fb84df79076b0c8,0x8bfee8015fc7bf081d,0x7ff7b869b0577e248e,0xda0a3e9efb10f87faa,0xe2a3b557f35ddc1e60,0x955a01f2aca3f5441,0xa3b36af038cf72cbe9,0x39491e76a3a2bc7021],
[0x373d434de4254e3af1,0x764f9a7dc7219d0244,0xad894e77b724ad4be3,0xe3bc12e27369cab1a6,0xd25321967e4434ad39,0xb083e4cf172593a646,0x75fb726ceb9d72ed96,0x1d8d507a5c180c13d5,0xc5c14a00f3e6bcdc,0xefe6181ee9458fe6d0,0x49024461c18b7cff2b,0x9a52a0b12542df9bba,0x54bbc192869367ae42,0x120a8c0026925c6b7e,0x76f52591529459c1a4,0x6c47dbb09df37fefb5,0xdde0c636eea8211f7c,0x77a52c0044e5e9bf7c,0xc0aa7b2435a900f03,0xab9d632bce42b1235c,0x5798d5b9e48d37a68b,0x158628aaa7e496c821,0xf3f5a5fff2fc09a2f5,0xa073dde0f3170f150f],
[0xb2183ee18c9e902fd6,0x8fab95f3ef22aa7fa4,0x98270e7b0b9f12f5d5,0x6f3b9f711334ddc495,0x80f9326cfa5b1bbdde,0x8239683ba244a74e7f,0xa3b420a3bb87eb2419,0x53ad58642ee40bdf8c,0x2b731c51c0b9660df0,0x435a1eba3e7a96e6ee,0x382f15f4d38a14bb7d,0xbb5a62a32881da6f4,0x7563e23e07c8a1df21,0x9b5391a0fcdcecefab,0xe94d82cb226471bdee,0xa9e7200268f3f21f87,0x2061b215d287027872,0x588d3133c51e6fbb06,0x991a2ac59281f89df6,0xa74c4f9379806ace3c,0x61ea0d86c03a77cd04,0x1c1415f8f060026784,0x6b4e7dde763547813d,0x8463da0c0cba2f209e],
[0x106e16497984e1ef0c,0xfdd0b0a72a9642bb75,0xb333c7ea32b99dfc3a,0x4d446aa0b25608bbfe,0x249c8dd9e1fd353175,0x8f61a472334e1d0b40,0x72063d1040f46e26c5,0x3daabff685c512ace9,0x8880a99775fb9e1178,0x614b0467eba3eb49b1,0xd01dad60216038591c,0x505b9128de747a4b2c,0xa0e06fe3712207f337,0xbafa110802decb9eec,0x110baa84735539e63f,0xeac484bade38e569c9,0x2134d046a3afbbf894,0x2cda867907d6026213,0x5bed50fcd42fbb171,0xafbbe146c511a0ca2b,0xbd9715d3e84e85cbcb,0x18727c180746f670db,0x801959c24106fb93c2,0x6f9d2f6464919b10d1],
[0x4033013b5d125b8f0f,0x7194c3aa32ca10c95e,0xc61f166b04f73c273d,0x823b7634c5dd8377d5,0xf36f6e2caed0ea55de,0xa07ace17f0e93a832,0x982571c4e402439d74,0x8414d6db1acf9608b0,0xb10828b42ee9183599,0xf46b79c99905c2c855,0xe64a017e770397541d,0x228c08a5804c92c2b4,0x1e4c2c7b81fdb0693e,0x6ff1031abf3adf9697,0xf2c6547e1dd4ae7f2,0x84847759bda95b31f4,0x9303cc450a5048865c,0xa0f45e59e4e322152c,0xa5d0cc5da490d90784,0x98aac1fcb7972b0a6,0x3a2a4e5ad6e1d39ea2,0x962e86d4ace281d123,0x40746ff81c89dea6e8,0xd19de9e68c6b96f05b],
[0x91eeb8b20da7b0794,0x29d33a75f717185307,0xc84eab3c3fccd1a9de,0xb5f9c1c314fc93564f,0x4c030bd7c2b2c6e0,0x7b9fea078bc8f4c1ff,0x3a8b2a78f1384a3535,0x2ba1c321217b215e5c,0x31deef7928b26c14f1,0xaae5f616aa9b194906,0x49eff94b04036d2023,0x7469110759cbaec45d,0xf215a711ccead1e234,0xfe3cac981b0defdac6,0x1bdbfefc0263ec902d,0x5d744ef28440710b57,0x9f9a98e4a6f2653aaa,0x8ce9b6700f76a642ba,0xc06b354950cb3e4f,0xe61e71678d5ae6ef60,0x718dac5871c90af9a7,0x429b43779f539cd076,0x33394c26d5ebc12012,0x3fbf21fdcb80b81a8f],
[0xa345404c02e8390d40,0x4cd0c0ad0272bcb245,0x5506fec37a53f3e8ec,0x6a9ddc5166187e5e93,0x4858898f8043b881ca,0x1322e51bb97715ea53,0xdbdf5c9b692c12bb64,0x1f654e666cc3e7ed13,0xc0e0979fe373ccae8,0xa8dba8c31b7fd1ef05,0x67df524e1fb492bde0,0x924db2b45444eb6c24,0x94c4a6c279ac82bdab,0x63029fda313d0f0954,0xa86c6b1d17fca67ed3,0x7a1e83714ca8f5ffc,0x3017123202d90ceedc,0x73ff74c920671e7c9,0xa90b2916f46253462c,0xe4cc0ed2ebbaa852e2,0x605bf9b1e42f57731c,0xff3687464d816aee84,0x44fd74c2acdf2252a5,0xb1ac04f2bab1b54595],
[0x1378cbd4145ca4eb56,0x7fc531cf84fffdd4d,0x99081962239e55a0f,0x4359d8049486e80412,0xd0ebf0781960ee4b43,0xfae816913275687339,0x25882193b6e80803f3,0xceea896f69fb47b541,0xdd4cd66e15c3d8fd40,0xd55feadc5cdaaae0e5,0x23e934a89b30ea091d,0xb3f919a5d26cc974cf,0xb63b6459bed3b26a3b,0x6d450f59e0c4acfe48,0xa69e7cf2de07650736,0x6f92da76a59f3d973d,0x860bd0673dd2426616,0xb20ca91cfaeb03d750,0xaa311cc2d8e73c92e5,0xd05768e0db18432569,0x9fc32811fc2dbe892a,0xef5f33bdaa183e8e2d,0x2c3388e26943833b02,0x1013afe9afe33292bc],
[0x985364c8c5f53b77c1,0xd934ff1f26dec0198,0xfebaf282e743c92f4d,0x3d9ee90a46588aed6f,0x9a90abe1b8379bd0bb,0xbae2e50b2579aaaab,0x36f9f990e3df64efad,0x41697a1142af7a1362,0x324dee036fb8cabc78,0xa46c245b9b5ab3e165,0x10709960b5f00ade08,0x42e8664722d26ee54f,0x83a3f396d3d3a2151a,0xee34aefff8056eabb5,0x26460cecb100bad8ec,0x1ef41d90d0792267e3,0xe34f2149a3f5af04ce,0xa4fea3467ca8b1f742,0xc1b14359fb691332b8,0xff7e7400384c3d2c6f,0xa0028e179e99a398de,0x17df20fe126bacb000,0xd22966ba465975984f,0xe9895df3dba98a69d8],
[0x8f6c106e1f96cd22aa,0xd965bf47f8ac43de6c,0x57d0ac3b47d31418d0,0x20ce77361950d30e14,0xff51ad10201b16c272,0xbf32daa8d5f7948a77,0x1c3f528dda55420787,0x65cef66187d5bd9181,0xb186838dfd18d0f05f,0x375a3ea658e500a3b9,0xaa9ad60a765b821d6a,0x32966eccad9aae89d1,0xb0f4fbbc1f5720584f,0xece0227bec9f065c81,0x16e978e1b5d6424f89,0x4ba166eac8aa8dd789,0x5f4019de27583b4828,0xb9ba18b41408803f48,0x1c9a437499d111d62a,0x63b7ea0a8cccf80637,0xa31bf38cc3e060b0e1,0xb0932a6c6726c1c5c8,0x4f960b933b6e127f2b,0x42b050e8d2ee06ddc2],
[0xc0ecd63b655b889d6,0xf8552ae838883f78c6,0xa2de2c0f8e4a38619b,0x916f0670820c404eef,0xbbc6aa7ddb4609ba60,0xe8d129eccadc8cb71b,0xff6441ef230c0d915c,0xcd2d81a1f9bd10dde7,0x63df496981110ab758,0x9100be915099969d5c,0x6831ae9adec5651d3,0x8632e182c6bfe534cc,0xc6e821895d3daa0910,0xaf6ff0232834c25af,0x91db3431f5b391cd96,0x8e2501c671df0b8ff0,0x69a68a9016616705f8,0x977292ccb6d4a57250,0x814f06c3a6a38d4ef7,0x66004c1f4065e2519a,0x64987ee8dd071d7e8,0x1ab6a97556a07423bf,0x14ec98cc58138e4c50,0xcc157f44b13a4dbe49],
[0x86a9c2899fc33b904d,0x6fb94452ee996e0d39,0x875cac05b9c4651ca0,0x34b40db9d9d432fd3e,0x324461e5e705049220,0xbb711790bf025786cb,0x3de2322b902fa76516,0x36ddd5ad7efbf91622,0x430d986e238087d879,0xeb9bb3253ba39eb890,0x369b9c2263a215f83a,0x73f563263cb74861f,0xb47196bda68f7f5f99,0x7d32eeef2a05faba45,0x971375a4d7b4a818c9,0x2a22a7e161d500c700,0x3e201e182f6074f373,0x1fb43d5de8ce3fc5f4,0x9fb8e854f42eebafea,0xab36205f4bdc517404,0x73973c18644166711f,0xcd21b656a09e55cd1a,0xfe55e411740d01e656,0xf16a016ad260068cec],
[0x8d0ad9aaf316c87640,0x7f4376b64bee05d696,0x785392f11d5c5be8ce,0x99696c2fafc2d6979,0x26ae1fe73d4ed02ac4,0xcc1c1e258d0d0bf46d,0xe88e7676880a74a1e9,0x27897d3be5816f7a90,0x9eaad65fa8b5adc06d,0x28528e048f7cb622d8,0x2c4e6ede076ce3ba8c,0x805787f68ba674a7e1,0x9dc666f80707279744,0x44898d9879b8f51756,0xad9ae932e84a788310,0xd9ad7b74f1853ea731,0x5f802d6af75744d645,0x4714d5614d42ae742d,0xa76e0a34667679182f,0x7a75b0035436afe92a,0xdc837e519186cf80c3,0xacaa02e308eefec6e3,0x2560ecb42b550b5ac,0x8915e6003bde0cb929],
[0xcb15a402edb728cebf,0xf1f051cf11be2b7b8c,0xdcf4d09d354403c86c,0xa54078762c5a1e21a0,0x87f8c6ad93e617210c,0x3e80f38506cec2636a,0x62f4921a441dbf19f,0x91ee8808a7ee94b69f,0x96e60b1841a275de81,0x2a822af3ce2c435adc,0x37e7dd517f87e4c835,0x3cfc1853f5c42a37c3,0x75f34fc02db9ebe001,0x9215b1eac1d5b8e3c4,0xa77976d150af9a6f0a,0xf5ad516519a77bc52,0x42d1c373831adc98e0,0xeb18cc9e148433b377,0xb7aac55cddf558bd64,0xf6d974f4adf1be930e,0x80ddce90f09abb0797,0x8a97e88e5909bb88d2,0x84a73f6b4c3b7d83fc,0xa53fa7e3111a6bfa96]]

def tile17 : List (List Nat) :=
[[0xbab44dcaa19a5bf2ae,0x13022f87b8130623ef,0x283a1f1eac4ab46517,0x5bda46c5f885262450,0x3db23fc379f5fdfb2e,0xc91825ed5278394908,0x7e3575096cae3bab32,0xa824ec915ffdc4999f,0x5f4e81666cf59cfdab,0x95cd9f99c84dcb598e,0x12f161b7a2ce642d0f,0x87cc5df8c632280ea3,0xe64430376288f4240e,0xda55d19944a35d9698,0x66f7aa68b2f721868d,0xbf437628be0531c3df,0x3095efc780bc3e28f,0x7da4abcd6ef5a78407,0x12a8374c787c996685,0x26fc71c62a8ad1525d,0x2c2c1954e980e91818,0xe96241979c05e7d5bc,0xd27712e836ed0a1f56,0xa56bfb16d652d8222e],
[0x19ae26540a732174e0,0x3bf3e5c9caa259db27,0x4f31a5943d38f7496f,0x884805bcc1ace421d7,0xd16958816dca3971f,0xc60a59d2e40273d16b,0x43390d2be58f45bd65,0x8eff5017bbe5f8d960,0xb9392765171f876725,0x180a08d71599be6222,0x6ab21b4ffe1d842b3d,0x76773f45c2c2ee63ac,0x513b4d493b4437e638,0x61ec43c8dc3a75634b,0x53d8129c588767b0a2,0xa502cc4335eafe3359,0xfdfffc40c1b81b03e9,0x79e65d19918018f75d,0xca2ec66f10fad46f13,0xdfddb1f79ca32c6ef8,0xffcd5a7b109bc65821,0xf6a01ad212147f3ae,0x66425668dde10d1f7e,0xd9cb076e777d97c1d8],
[0x1d1274ab14153cc378,0x71cf2f033fb78c04cc,0x6eb3f447ff1f2f05a8,0xb54251dac6137b054a,0x2caa42a97b33d92a59,0x36123c5c2c2566902a,0xdc4f4b52a5158553a7,0xcf7fe5553bce2b430a,0x2d0a1e312417b00ed7,0xdfc10002dc3ea54ad0,0xca2dc7d0506069bac2,0xe7f3ce7fad7f43f284,0x5b921bf9b551f7f241,0x75a4a34d4f4c3b453f,0x756201bc9913ee2014,0xfb50cf9f21b32dec14,0xb5c72fe7bcd462144e,0x127a65e9a502e394d7,0x14fdc94682b3a69bb5,0xae47f12d4dd4c56ae6,0xf46b8bff477aee82c1,0x12d5689e4f6b1d1220,0x4f7731aadfb4c95d38,0x8b136e683f4e6c99a2],
[0x8815ac90570377d155,0xbdbe321e8ce6b9099d,0xc27871158e8b65fe71,0x4c4b5d7dd404982fe8,0x7d150ec0edc4bb27d6,0x5066f30065f43e0a9f,0x8a2c7cd3202d3f575,0xdf9f6e74e2fdfd093c,0xce5ffc7be1ddbae138,0x3513d71769ececd949,0x34c1b6e1c0b19d1584,0x2d1e26bf8f150c0685,0x3e0b252119dd390250,0x4ee267c1af35f0fefe,0xd515d2276cde90190c,0x55a46ffdac61c1987e,0x2376ab9400537b6db0,0x334c84108e476bdb6a,0xfea05d90ca39e20696,0x38254dead55dc754f9,0x5d87f9196e26e7426f,0x1ffd55cd6061782a33,0xbc57cb9112b63a292d,0xe3da2ecb80648cf3e2],
[0x286f07972474c6a472,0x31c8d66b16957a8b70,0xe1a7c7ca29f9041ace,0x48be1321b34fa99d52,0x24a83f60fcb701d35b,0xe824fac29409c835c8,0x120a69145ed32ced2b,0xbafbcacf9e3b1f2d10,0xe5476a304b6eedbeb,0xd545329f27cd3559c3,0x588f4fd5d37edac419,0x91357cc031dbd63770,0x784e7859798e4bb180,0xabbe07f287431f1613,0x8e36db5a66a3092d0a,0xcf08dabf9a85246cc0,0xa9ac1a92bc2b7cebd1,0x80f03bd4e1fe850561,0xb692fb3721c60bf484,0xb37a50ab7971be9d7e,0xf6ebacfefab03c9f19,0xd5b581c366ff31cb4f,0x22e5fcb7f359897893,0x924727e619ad3118b4],
[0x4fd1c19968ee9ef204,0xc3163e5918a2baffa9,0x2dc83d0e5feca64826,0x3bdf1f8e625c691e6b,0x92dc5868dcc35b9df4,0xd018bc2ea70ce38dae,0xd47650d7aa00411ac8,0xc5eb203ead827aff19,0xb8b5698e8c0c734813,0xa5cb99cccddd7a2537,0x90ff19ac17f804ad2a,0xea9ebb9b7467576384,0x586264f3ad248db26b,0x68d9d387b699842029,0xfb69514dc733aa021,0xa903623e7e6aada63f,0x92c52cf86043cdc9f,0xb593a017b1497329a5,0xe292e42a9a4de4a4e4,0xfeafdfb7ec478b8698,0x531da8dee90c98c987,0xe99d8031f5501e93c7,0xd3d0ee25781192ed14,0xafac261e6ad9b8e287],
[0xa3310cc56d4b60a10d,0x35e163ecd3fd538d47,0xf181decbab3e99a18b,0xc18b51acc8236f7a44,0x1d85c1d182c6b9267d,0x5ac3636c116b4ad9d8,0x296bbbc41a2b47d8e2,0xdadbdaa9c435af269d,0x10e13c183804467e5e,0x7c3fa6b163b7e385ae,0x6f9c28a155ab609911,0x1ac5365fc8168f1e84,0xe62e2ba95c08ed50e2,0x4e9d3c598006c09ae5,0xd7fb7c4b1f7f5c66f0,0xff3d8a9fad2ab6610a,0xd17f455903a6a47fe,0x4402ca98a50235b492,0xde22f372e948f1fbc2,0x468cb6f85347bf16b8,0x920f51460240bceb7f,0xb9d43aa8f4baad80c1,0xd819317496a4955ea,0x4efbcbe30187604cfc],
[0x7c0340973ba340bb6b,0x18db28317d58bfe96c,0x621ba2dc7fd24b0406,0x6d260525e155772beb,0xaed5052b5bae450cf,0x7f86951d84726bc914,0x679c9cb4a6f1a8c394,0xd093857e53bcddf921,0x6561058d2a28f7426,0xfcded7d78f5f1d782b,0x92fc056c9c2ea383f5,0x339f45c4e2ed59c1b3,0x4a7c23f54c7bc4e0d6,0xef0fab2f7e1616012c,0xe58eb948b5f51a7f18,0x13d3c4c53f5cdb8b79,0x30152b3db70171a5d0,0xd180d1cf63bbc064aa,0x40ccd7f66b00f0e882,0x94f4042009d9069d38,0xad21d7ed3f1fbf1a9f,0x9e53fffa50df4825b8,0xdcee9389a438f008d1,0x497448a2535a1b38d0],
[0x4f3e91279e72efb39e,0x73a2c083cedcbf7588,0x161d8a58a939352ff7,0xd6713f85477c769ff0,0xc0aa27dcaf82f54e5,0xec36dc68b8b9851987,0x6d52b1f22c46478537,0x499151db7b05e11723,0xa3a94c304af3d2e358,0x2cf68ec41e989e9adf,0x701a7356f34043ba87,0xc4d6b484cbcb0984bd,0xe25364602fd3501d15,0x951e62347e2b89d3bd,0x1de39f28a3aa386e6,0x1255c847934da8ab26,0x49cf05f05e1eb0d4ee,0x3ba09686f5613ee0c8,0xd9533d07b3ba15a931,0x92ab730d4a6c4afbae,0xef7e05197155424168,0x7e9327dfb9d5979ce6,0x1a3a9b7aa1e06bdabc,0xfb9b9ec9d4456fc471],
[0x10e3616fb415237d26,0x6fce216d2bb96b535d,0x3885c9cf29a11c8747,0x9a40410d49c5ac7dd9,0x6a13856e68c8e0cdfe,0x6d6f04b46bef36f609,0x6e3d556143d6948f,0x35ea79a5912c48146,0x20863f236ab5210ece,0x7f28e3c44d31bc7085,0xedb9ed85cd985b2685,0x9c91ace4fdb0015701,0x17a4977f8701d06d39,0xb0c317f52babaddcb,0x8b03abc126b5d1cb20,0x32d2823b75ceea37cf,0x7e16a41a61ec3be4,0x26367bf1ca766dfb38,0x57c13f78dc351ddd95,0xa84a2ac3463aecda2a,0x37337510b80eb6e05c,0xb1da9f25230d1c015a,0x17afb7a4502bf3170,0x70283a355708906cd9],
[0x487bf3c19b0c3b09dc,0x6439421d4dbd235a8c,0xaa5273ce8b6d5a6e0f,0x17d26994e4dfa0a53,0x8165fbeed0403a742b,0xfe2ac9cf6ad1216c7b,0x65f0320de428ecea7f,0x713f98a0a5a9912ca8,0xe81585d4e9006ab493,0xb82acbd6bca3689bce,0x46ad3c494753da4d83,0x964bc35a1a58bfea15,0xfecf4299d1a28f57f,0x4e0ae1a5a8465a57be,0x62489c94f96ae3fb8a,0xa974ad76f104c44ed4,0x278cde6bfaf9e42489,0x64ad4f99a2648bd42a,0x867d71789ba31f6c4c,0x47d6e4694d2f67b9cc,0x9c32bd7e16ca79197a,0x459b959d0377a08fc,0xc7f145191346b7ace2,0x3e5651f92039d02471],
[0xf068cb2a72cd1a9662,0xdd57a1246f12a93c93,0xb0d3508a3a882f4319,0x3f4314e030bbc8d53b,0xb30a6bcd08c194da1c,0x5308e6a2fae7bcbf13,0x3724325f28fd49f7ef,0x8f1769b7c7aa7149a5,0xd5d411233b15d25204,0xfa33a223b0e6a6a680,0x54348e264f4c85af0e,0x1b1dbfaacdae73e558,0xc612650e6a8c81173a,0xdd45a3d29f5f1e1e0e,0x3c14a93ad1c239b05d,0xfcfe5f7202caf97660,0x1fcbbeecad1165df3b,0x6e96bc0c1c845b9ba9,0x5b48c73cbff42de3a4,0x736bdc2b853eeb93a7,0x539bd24b6318ee2c7e,0x358f288562344171fb,0xa33f029246c515f6be,0x3ffe44e0ce0de28038],
[0x3e4a20b474df5a3b7b,0xad24f523cae6bda413,0x84adc56439a7b048ef,0x1daf7c40342cf72f2b,0x4916b86a4358848ab2,0x222c330695e7f6b764,0x461ec4c423737048d1,0xb402d3667b1ccb2685,0xc0fe375a77c09f716e,0x99fce3764d1b936de6,0x56b3c6c6d8b6a0729f,0x3af47c1252cc54a986,0x5c1868d2322b57e620,0xde8b9c0554f193ca84,0x3ea6573361a693012a,0xd0af826b41f170b44a,0xac8e3037c7d9dcc621,0xf3e753d249d0949c5b,0xa454c840a5e94c1b97,0x8d84deaa4e9ee9fb24,0x810c54fec563ab05ce,0xeb5b9702a1ea68985,0x1453e47be01e7faf07,0xc49b934b4112f12e71],
[0x9ec78742b17e2f1f68,0x6f661b8bb8fc208685,0x3ba1a72d19ddabdeb2,0xd4b8b7170c88ab4c63,0x8a71398f472cac458e,0x17d7986a50e361fc46,0x840c770fc406269694,0x557706c45913a63dd1,0xce807bd869dd9c738,0x87db3bbd3e352d1c60,0xcf3d210411021f9eca,0x20e75e7892ec718ade,0x9c1bea57424155948a,0x33d620f038e1a72866,0x34033ab1c381a7ec88,0xafb88dc8e48741b50f,0xc4896e0977c94dc2b8,0xdae1eb154242ac9892,0x12908ddae45b12ffcb,0x62f8d2aa14b0963a93,0x5e802fff38e49ae0b2,0xc0354bd4cd20beea9f,0xe3b474768e4b83c6cc,0x97cd3e88e3d1f55628],
[0x2653b4886bb712367f,0xb5bfb11b98650665d9,0x20a725c90af79670c4,0x935ce5a1f5891a2e6c,0x409c88387b23ff7e77,0xc682d8a12a95680428,0xdaf28ca43f90ae6171,0x1a8e89a9609d9f1925,0x1f5a8f1ffa9b26d040,0x51af01fa8e680d8a3f,0x2094276a8b59dec619,0x82ec45414677ad58e4,0x2996bd37eb0fc01cfa,0x89d579cb2a727baacf,0x2b3c748ad3e23586a1,0x974b3de3ec2e8e424a,0x901519b8c29d8a9591,0x433016da93cbf937fd,0x200c6f6c234b5155ad,0xfb9e22a55c497deca9,0x46223a115c49f2fe73,0x63b88907f5d0904c7c,0xb782bca1c7d9c18688,0x6091ccf1f6bb7c7f35],
[0x7760e8e1320d5941f5,0x9ba759b7c38d4999d8,0x285d3b5bd9c13e0c3d,0x40969087597c4b0516,0xae5787d12fc149ab3a,0x885301fba589b11186,0xcaa42928b4022c5979,0xf086095acee8601f1a,0x8546ea73437085ad8c,0xacd9a04a41657f79f5,0xd0a58478159951391,0x4fa99b52ce5baca9a7,0x8cf0e86911718b125,0x36cd3a83aeaab1950d,0xfc1b21c88a9fe8a1a4,0x715cbc18bc46006825,0x3afaf8868a3aa2a907,0xe2ea8388c62a1f19d5,0xe6e3da34436e6b561e,0xd633204f38d70b4c49,0xa1cf0b80254046e1d7,0x4a9d3a2533dfd610e5,0x38c4c31cc0ee6758e0,0xe1d3e95a6f817df5ae]]

def tile18 : List (List Nat) :=
[[0x214d88a56c88a187d2,0x5bc9f392157d18091b,0xc31eef5b1548ae22a6,0x295acedddb64890297,0xcc7cbc101eb83e94b4,0xf22e02e7231e3456ac,0x16feb640c1fe2bd626,0x204da0ef66d4270444,0x1bea2d0e37c8787e14,0x6c27ad972fe585a382,0x56f77f7f8ebe2d1e0c,0xc5578de50a4b7bd5dd,0xc673a333dc4d275526,0xe04b5823cef06b6751,0x57fd2f621d144a6752,0x8493f960d53f72f015,0x6ffc31b2ab6022a5ce,0xcc676885af981f699e,0xc3d314d8c55d34f8c5,0xa831852186e94b18c7,0x62c230710a117ece3e,0x88d0b8455048ac1f37,0xb8fc1fa5fd2da8f228,0xddc07bb2b41c626e95],
[0x3fa933b0d1588bf211,0xc1733478d702d425bf,0xf24daa91a1471330d5,0x7c05b352a99c05ed2a,0x44494cf532cf9f9329,0xe596323dd5d039a9f7,0x14c8d4827fac5559c9,0xf8e64af9ea5e32105d,0x2412ec17dc5514305d,0xb35edcd73a0b58b886,0x84635dc0c11b956b9d,0xa1d0aa58a8b81c1cd2,0x19dfbaa812f3284ec7,0x6b96d519b7ef70437b,0x5b7ca3fadf162933ee,0xbfb9944460bfd0a610,0x204452010073e3a935,0x8980ccdf8ffdfadcd5,0xf9b490b1be1d01dcb,0x4d6619237c01b51597,0x33781182d02642ad8e,0x3b5532423406b56acc,0x8d1fe8cb29c3195b0d,0xfe2d91343e9bdef895],
[0x42931f0527aa3fe282,0x2b0bf81afdaef3088b,0xcafdeca11bb005258c,0xb7bfe4b382eddce740,0x4f045fc3b419c2f600,0xab1bb6d8da0153c18d,0x5a312941114190f16,0x6f3b9b83cfa0eb196c,0xc8f37b84d67ba48298,0xaa32b8e7b3545df59e,0x49dff41e4f2faca1cd,0xa735adba276c07948c,0x72233624106ff72dcc,0xc37cdfd967200bafc5,0x4e7e76b4232d754c08,0x3239e8d8ed74d3c5c,0x813c559e7057d0d259,0xaf1cdc6a95f5e869,0x839e4b0b2192232032,0xefe28b9bc737852b93,0x50a4431a63302754e1,0x2216029286637f6e46,0x2e7c33c86864f2c895,0xdf4b53775b69ff1c6e],
[0x62787bbcbba12253fb,0xa67b4647f22a103f6e,0x1165d3be3c42907d8d,0xc82fb6526b1b55dbd8,0xc6f1941ff157058833,0xedd71d9c4d634b828a,0xcc598e13204929dc2a,0x5c6fef01b00588496c,0x4ffe28f8d8e1115116,0x131dda0d144e2c601b,0x7f03bc6f6dec7dde2e,0x9be5ba213a889d5bb5,0x7fb3a22eeb3761c704,0x43a9c55ec19e956716,0xe5114f6b67c00c32ba,0x6c0811f73b234e2179,0xaa47e04b14c89fb2b6,0x87b7a75739662f956a,0x6b1e484fdc6fc815d5,0xe289eb4ba235b6276a,0x912fed0efd82b57232,0xc1ead766baf0e5c6d7,0x8a5dad9afb3b368586,0x5bcdf934ee127948ed],
[0xdfd45134565534a6d1,0x622fffbf999e5ad8b0,0xf98f5e9207114fb76c,0x934e4efb0a040a8047,0x645bd7b6bb98d67041,0x6a882b10db30d4fda,0xd1d8d6f058cf2b9b0f,0x9f9df801c657afb9ab,0x4c57217871f8148cdd,0x445ed3eae683b92cf4,0x4bdb5dac4713d58c13,0x25755b9d6275964bee,0x689dd4eb591d43d31f,0xb966b0630a0f711501,0xd4fcfda73d2beec398,0xefd08da72f0e73afd3,0xc8315a90fcca6f6830,0x684c982ddf944a8298,0x7514a7319ce25c0d22,0x65a3ce9f10396f836c,0xc5498a5723a409fe8c,0x79040b8b8028b1d5c3,0xf0f48d70b30c34b057,0x1bd3fd8a634653c1de],
[0xe2a9b91ec2c0fc2d1f,0x2f9dd2526781a5b240,0xe6486ebbbdf30982ac,0x3b4ac153bb99e85bf0,0x17978fa592b96900d4,0xb95ffd59e03703a003,0xc96851609bbc755ceb,0x59cfa96b365c76fd75,0xdfcb70c10f5efef168,0x8fe649d9f0df241e07,0x12dd93cb7c80ab4e26,0xda8853e9eba7a57b4d,0x1b00904ffbdcdc7bc0,0x8ca8be120ef5070c61,0xa96c18064cb735596f,0x84ac543e54331ecd9e,0x89b80e4087a399bf06,0x840cf638080f891380,0x758607e8a2d6678429,0xef47905c712eb34c85,0x553a2dee104251d9e9,0xb7b4d563fa3ef0fea9,0x8de381cb46671f6f02,0x58bf6acc591144770a],
[0xa76a4a19f85ad7bb45,0xd5724b198e8edf3d40,0xcae96650ac8d2b93fc,0x65dd1f6ad23e3d3353,0x4b549f65e6fd687fa4,0x89169cb74b8e396752,0x24447b69ee972dc560,0xe54d8384efcd44e9ef,0xcefa26bed089997b50,0xa42cf335f2c47d7d06,0x5c730c3d7a8d56a3e1,0x23013932974c41c647,0x7d3398e9c6b6cd7eaa,0xf0691011f33916906c,0xdd2e3c5715f176868,0x1bea71acf33de9497d,0xcf49a7a1666911d13e,0xa88b1a2e11e99aadd3,0xd0bd0607524c7f67aa,0x8f3de7c2c623a95c15,0x34c838f209a54f3460,0x8ff9ce02861bec0b6a,0x3ef7841243696d0063,0x678cccc47b6361362f],
[0xc6f84671611fa69a6e,0x2379a9724c8cb20b8,0x8bff192f628fcecb8d,0xded49fc46f370c7c7b,0xd0ad6fe78252b86fa3,0xe6d4f306e749eecd33,0xb95c17c50b6c9ff94b,0x4dfbc3373c871ebc6a,0x64d140d43e95bb850b,0x9aa83074fed71822e5,0xee1f796239ac240ecf,0x12e762af44af5440bb,0xb6e11426aeebbd571,0xa0b5a7ebb0126ec33d,0x4d1faa30cfefcf8d38,0x1c1c3b35192f5f574a,0x33f965c0db762af7e5,0xb24fb625d13a2b2992,0x27681163773b40ceef,0x362989c59eaaaa6967,0x36fdafbcea3d24f3fe,0xfa092e71293e11b4a7,0xd11d94ce3e8679800a,0xd7ea77fe7722ed7a9],
[0xd6a613e0022114827a,0x6d443e2508e556861,0x41d401da6401460701,0x9af60bccd2fa01b024,0x5ac6d8212adbea85cb,0xd469e45fe87a82fee9,0xc9d5e5cd7b562ecd71,0xb61cb9c6e96431cefb,0xcb946a2b282f45268f,0x9e0b186574ce5ef1fa,0xaa938485343d18203a,0xf53a6b288e95b1c410,0xbcaab48715e9ce5968,0xfa2c27fb0fa204f9a3,0x44106572d05b9c4af1,0xce648ff2e65b780d9c,0xcf4644121875fecb55,0x15b191f9de017c81ba,0xd3ae9e5d4fb2fd7657,0x748599d813c36583b,0xaf8517eac831751ab2,0xa68c6b235cd9dca155,0x66f4c4b58c71f62b9b,0xbd4be4397721d68f60],
[0x903b53f627f1a31ea7,0x9be396191f1907e8d4,0x593168a2bb9d538868,0xa85b50e320e33afa63,0x6aed0383bed59e25c4,0x6f25356cd8533e7c95,0x7253386e2c11872b,0xf299237f09d31ce898,0x885daf3a139cd06eb,0x5272e785c7b2c9df8d,0x548062e5fa66795671,0x25c76260b2d1d5c5e3,0x3129716fa5c242c4fc,0xaefb020ab08b991001,0x8a08110bd395ca7ade,0xf334d33047c530efb8,0xe876ec8014d4e3d2cc,0x51a615ab7c3c1215dc,0xcde8c11c313987cb51,0x351545d9e3d657071c,0x37584191ac569bfa1e,0x3513294b7b6afa7b92,0xca5f036c61dc564832,0x2a63c3c5aec3a6e637],
[0xc6fd3f7945673083ed,0x5827cb5f46783ebf6d,0x6beeed379b50dc85e7,0xb05e6c5d5a3f046be8,0xe3342c51f6dce2c246,0xdf642a92958dda3405,0xd9b3059d319e7cd991,0x9c6965473b9acd4e04,0xbf148fd76b800d7902,0xd2b4d6100d4c653f9f,0x9fe43a737f1895df15,0xa4cd07af60442002b3,0x6380c126d97e4f53f2,0x644b50ca97b957364a,0xf1387061dde1029a,0xcf5f5d5bce0f2e1126,0x668b4d9a84ed7c23ef,0x25053607a527bcb21a,0x1005c689dbfd2f9144,0x312e8758567bc07c45,0xcf3134196d96a8a632,0xf3eb0d01e439d281a7,0xd2397217925768a43b,0x7d3324003aca33ceec],
[0x798dd9171e12214519,0x2cfdf49661965f15a5,0xdf35906a01f2fa5c5f,0x9692696a5ca5cf78a3,0xeba0974f4a76f6fe9a,0x1e1b2f53c3f708977a,0x20722aa902859b3168,0xca8c4f2a953bbb5e91,0xa05a88ad204825bc6,0x36fe8d0fc226f5b0fc,0x17f68f5c159dff5f39,0x3290b7edc0f6da3a89,0x68f383dde3a9e3b698,0xd32670e8f790efa9c7,0x5e15fd597427fa3a08,0x7df66db0b19e264720,0xd9d941ac2dc49c2d4a,0x8755840d825d6f6b44,0x947990fb39c9e36f8d,0x3560d70ed8cb77e7ab,0x1eb11cfcb1063a2a15,0xaddd8bb0f74ccdbd28,0x832424078d9f0fe111,0xb0d4a05f455f881f75],
[0x36cd4faf817acef560,0x2219b4de94e04e0555,0x9caaf87d6ea5866a0,0xf80c1154cbd12ba446,0x724e774cb201c0e49b,0x14765d7aff8e0d3bc9,0xa2a2704c2a3c0b00,0xcf523ec24586dc4563,0x1ad97aa801bb891c43,0xca582884ae4cda25bf,0x6f64a7f55e3dea894a,0xc34cac724f5307932a,0xe082d6887736d2c966,0x8b647984ae89d5e43f,0xebc36a22eec5f5ae6d,0xff6c488e9f746b8029,0x1a28ba94c09986d237,0xb322a726e94fbf480f,0xd8c44f399edf62c346,0x1d3b37f14607c4fd27,0x92c7b28668ea1b3873,0xafebe878b7b8e76b67,0x5d06ce26927a03fb06,0xabcbf8a87cac31c00f],
[0x621bd92c097355bf0f,0x8824aa35c4a9c7c6ec,0xf0f92a2b2adf24a976,0xc5841e5a1ec03c51d5,0x89750482f0c0e2795a,0x2fcb0b4dc79e392a30,0x5ab5bfaddc4a7edce7,0x7bff5ae14672527284,0xf197a5d202244a3fd5,0x1a2540e3d5ebba59a8,0x7d0fa0c11c5d98650c,0x3e971c98883e7d95a,0xb0fd7724f44c5fa15d,0xc740d49776a58dedca,0x6d79c316c8f7c7ee17,0x6d7936f439e5243763,0x58a7c54299235e7b83,0x4893cece161aa8ab77,0xbdf690c518aeb61420,0xe9a8f75427593e16e5,0x972b9eefe29c746e30,0xdad1eb539b58fb9a0e,0xefb2ea6946878d5e60,0x29db79eccc74543645],
[0xfef8e32a0d769d6c7a,0xe6b2095c9e3266470e,0x9897bbdd14472d8889,0xa4ac0b9e2e6425ec1f,0xca99dedf6d8e5d66e1,0xe5b42f220c114a3be9,0xb68959afad997f8190,0x2edd234bd362a85edd,0x1d0f7dde4ebd9277b4,0x5024d0b4477ad0082,0x4af4b13b47bd5b2d58,0x16b43d557dc0933e2b,0xff528da0e2ad8d666e,0xf2e04f582af3286bdf,0x6d0d181e505ae09818,0xec6b089ea040f23728,0x65469e0a45ae7b59ff,0x41fc8614c6739eea9f,0xa52c073ce9bcfc04a1,0xe148c46764ad41c754,0x616e65fe12134e4823,0x95ac4f597a51a5078c,0x3bbfed9acad8d611e0,0x970e6e29a6868acb6],
[0xe3ff237c5faf09b28,0x364088374ee2a0e125,0x83eded7b022703b81c,0x12dee2dd95cbdb29ba,0xc950f1bbca4f56bc35,0xbd5d0b14887de5341a,0x13200df002c6f2f38c,0xbcb4a5e57a9e866922,0x4969cc1929e36bf81e,0x714f65bbd648d87eca,0x143ccd70d7895e76f8,0xbf8b2c2bd9402cb977,0xaa8f6d20c684c65e97,0x7626aad281d2c23cac,0xb672ab3305538ff332,0xfc599865f3555aa799,0xbd21b8eb10071dd410,0xd01a46d5340a5ecd51,0xee10c165514e46599d,0xb688f0bd327586c779,0xeea64b8c96035fb92a,0xfe3ed46b0eb981ef7a,0x3784654dc9fd21962d,0x3c58e8860e6116e7f8]]

def tile19 : List (List Nat) :=
[[0x690d73d3fa68ddf04c,0xa62945e78239002a08,0xa1bf5e2a2f226aa7ed,0x144dec3eb67f3661e9,0x259a01149e91d7b444,0xf655b8cde6285c4b71,0xdea89cbfcdef467a9d,0xd6af13e566ecbaf08f,0xbb91571b91005e5a8b,0xf5988e1aa9252d32c9,0x64bd4ce6cc4eed4026,0xf800ec3c0d131c96fe,0x754b07c0b51d98f068,0xb35d0f850abfbab7b2,0x31a4f84a22a04fe2f6,0xee26eeef842480fe7a,0x2f1019e2275ac067e0,0xba4a53b1b36c1bec70,0x2753a1fc3358270d3,0x1f3d1f0e18a4610a93,0x273e7671bb70e2f436,0x6f8df2c8e5003cf2cf,0xa578572cc3f985fe93,0xca70c18b6e2fe18931],
[0xc85792b9a17ae09ce,0xad3f9be827e953abe4,0x16c439b84abebf3a82,0x755aa5112f7f140919,0x4e7b6a7800d01ba835,0x579dc45fe95a3ca4e4,0x131af7d30189d04384,0x70e70f4ccb29e46aca,0xf5071f3ddec53df78e,0xea4e7ba55790e09310,0xede662eb3e34de6059,0xb2315a13c85847bdee,0xc344abf090f5b48100,0xadfdb3917217df8165,0x38c05241ecd974e742,0xc1e41d11a097f64e57,0xdc357c1f56b4b155b7,0x8cff269662ef297a1d,0x98970e4fb53c1d9b6,0xcd88f9be525f185ab9,0x7a51ba90eb246a9653,0xda79ef7177003e7fa3,0x558b46d8ff33d03bf7,0x50a3ff6071f331b670],
[0x5168cb74ca5165f6b3,0xc078550bc6bed46b1a,0x60f8ad5611b7b46ac,0xf9ef415783a52b52ac,0x529f2107f2b40a1b9,0xdcc69d3cf1223a18f6,0x349f17d174fae299c1,0x977a7ba39d3256116f,0x5634d6206dc8c7bfc5,0x299ca0a94149c3111a,0xc76ae5a9ad8e2d22be,0xf6a38b0494291e351,0x62010bcddbff728156,0xe56bb7cdc59d88ce0d,0x821ca148636be251d9,0x18ec721865df50e9ee,0xebb590597ffe7e5766,0x7a70178cd69c0ef2d6,0x5e96c48cc753cd79fa,0xe780cd27c750f4df7f,0x195f3dc1eeb168ddb1,0x1b7fe0efc1ba3ffec0,0x85bee81bad42afa9df,0x8f93b61857b903fcf9],
[0x8eb5afeac1e02ebec5,0xf3f5c05e806005213f,0x6f1dad4a10c23d7b33,0x8fece9105dc64f6a33,0xd9e47f2e9976340771,0xfc175e4ff6a8960cc6,0x89500eaf3650dc96f4,0xc8893695978054b983,0x937c681506233965ae,0x988ec0ec4bbe0ec267,0xda159b4ee32097e934,0xd1bf7ca37c8ce73679,0x6188affe631632d858,0x5b3fb637c80295d8e1,0x34be0dc592c76bef43,0xc5fe29d475f3065d80,0x1477229913d1374201,0x841e7a2d249d73e7ee,0xcaf2b8afde42361bae,0x52b46dc9acd9ef4fdd,0x2cbe9d5a835ecf25f5,0x14ee9668581c048a16,0x370539b67f4d7b54f,0xcf65958d94542584b8],
[0x655434dc32bf15da17,0x63af77148aa01ba78e,0xe54ce84e38e7a330,0xf3e502175db3543fd3,0x80126c5411e838fd6,0x40eedcd1f776c6f8b8,0x90e1321a3d63710cce,0x574aefec4e24f59a47,0xe3c055b28635feb381,0xbd52b1c0ff9cfe4ec,0x2faef7ac5b984be4a4,0x5ca20ea654fdfa8fcc,0xf37bb41d0a19d4e061,0xf41b0ca945d49660f,0xfa72bbb647c0d0fecd,0x518f757124d1dbb4fb,0xc89d2ae9d2593d6f5,0x6e957a197f425e0376,0xb4bf650b79c7a3ad1c,0x31e30b562da362d3a1,0x13142b4faf53485d63,0xfb9631727e6c26cfc4,0xc59dd0431aa3f227bb,0xb78b4be3e54f188b59],
[0x2f82b5644bd2006fdf,0xf0ce2d5774ae5489ef,0x7ee5648f606d061f05,0x1a27b1ed59920ecde7,0x5aab78d9b6d6eaff60,0x461da0cdab430a4cff,0xe8f04bb2240459a751,0x95d51bc22ff34aaa7f,0x325f4bd31d6e489a03,0x19596e804ebd2a8031,0x9e380adbbdb3c6a009,0x92a5ecb155e77a2074,0xe5fd90972305666c89,0x3fe9c1547f9d8c888a,0xed3e7da8bb65d446e1,0xd5249f2d58f6eb7d99,0xb6f41bcd359c0f9338,0x3781ba6d69c1819d92,0xa6b26f67570b3bd821,0x79dcddd49b247dd32e,0xb217683a7a9898673f,0x9b017c6fa02894e370,0x9f9150dcae3eeba2eb,0x805dda9a5d1d8a155d],
[0xfa355418ede7e5a9df,0xdc7cea9043fe7da62d,0x9510ad3a9549b241d5,0x681a355f4454f46023,0x1a13873c5e476c9306,0xd5e22e8a90af00246d,0xd474e3d7a9e526a056,0xe65d26b5a73e1d7161,0x91227a4db95c20a283,0xa32a3be5d687101275,0xd84c2a7e38ca9d3e8d,0x56c1da42d7df1e3b55,0xb00808f709fb855c61,0xa12bfa6e2aee545b38,0xa851807fc6fe6be131,0x9f1b22e6278c1168b2,0x2fe3a1579ecd81e251,0xd3ce39a634674ca5bc,0xe2f8a8dacb2f67c24d,0xde78c7c1efdc0e70e6,0x89e61d3d0b2d300e3d,0xd9cff5ee24b0b1d771,0x675de9ccf4a59aa69c,0x6e6cc47d629c56af6a],
[0x55c9dca2c9ff6f855a,0xee87c8de9a32a1fbe0,0x1ad351704af398f6a8,0xb8cf74191866c60eec,0xee641c57cad3787df3,0x8d129fd15f80812e3a,0x47c9d34e20bd2e57db,0x5bdf3980917e654526,0xbf715c15d71878d7c5,0x2b3c04484c11bea3ce,0x1d01b5a62012ebfb08,0xa3bef10ca38696d22e,0x174fd22f3beb92308b,0xfd3df2d1bf639bbf1,0x8a9e79792a901988a0,0xdf5ff22a5f0c039632,0x90901f3d2203da29a5,0x56a670c98a20c0983e,0x9703806973e7027e73,0xefb872b8dfbd6b606,0xb6fe4a002f1d393656,0xf92a7c54a7a280dfdd,0xf570b624232ac07b53,0x3825b42924b5616e26],
[0x4b9856d9c79471fce2,0x353c458cbfe01a07e7,0xd645bfa46f28ae05fd,0x15a1cedccb7359e5c3,0x39f38ad95df76bfe2f,0x144b0378594115d26d,0x418d68ed01cb16761a,0xa6e3fe06bf5697ae1b,0x8dc1eec690291b813c,0x12250c0bd92c768501,0xc1673a14a3e286d1ad,0xb2190cf33c12fdc14f,0x20cbac0dbfbf804e82,0xbd87dd70c2e6571001,0xe4cff364187b7a2479,0x346fc67d02a994bd2a,0xb7ba320d0cef8388cc,0x93a215b4e5f081eb42,0xb11579dbeb68994d0e,0x3873c5f4c00511f813,0xf3590561fc16660c92,0xe074f8e8b7b233ef80,0xa133aa51b543b894f4,0x793890af0f26de2535],
[0x875a4d53a8ca95253c,0x7c828fd58f59230354,0xced9a05368558e452a,0xa0bcb52578d736bb3a,0xa96ae2eca9dacfbdcd,0x90b84a2acf56746780,0xd2e4c6b9566a2e2523,0x4dbcc107a32ba2cbb9,0xf50005418cd6ceac88,0x55ab51ea305d54114,0x46c6ba3c229edb2207,0x99e170a1f3a5ec43c9,0xd94186cb30fb0da475,0xb84931a5556e70ca65,0xa3a6631d18f311f867,0xc3438d506880419ade,0xb9662682641e7f6f3f,0x62161f93d67bfe7d37,0x6502beeefa7a48f958,0x97b71ef84bd1930d26,0xbf5fecdfe6b1254ec1,0x5f868678c8cf989985,0x733c7e6722c47fd7c,0xeaf07d3d1ceae5b262],
[0x829b559f57cc7d9f74,0x5c0aaa2c027b2cc3c,0x1936737aafc6521c5,0xddae8dc7d6bcff7fb0,0x24827132ee8373819a,0x8516b5a1be4713dd37,0x99fdb0a2a7e21ca283,0xb80eb71ef9ea26dfdf,0x833f55725aefa84a36,0x760d847a8da2517355,0xd4dd3c3ac106a4a661,0xaa82829d8bee27961c,0x9f9459977dfdd237d3,0x43b6096f9db39a7d66,0x68db50417bb63c979,0xc586fd74e0cbf8acba,0x94fbe84704b3170cb6,0x41ea06923126b37962,0xf3d70020232fd4abfc,0x68169bfe6abd223992,0x6be9a0cc4674707c7d,0x21b120697f2d98b5d0,0xa66ae0b76f7fbc7f5f,0x836dee1763cb142065],
[0xedc64c671a831d355a,0x2afe9f19005fe464c0,0x3c4665ba2eaea69f1b,0x7bec0193e28e5933a4,0x6e2cc1d3bfbd634b5f,0xdbd11f3015977f43b6,0x83f2d80767d713377,0x2a2d2c7000d5d28763,0x595caafc54e04da0b3,0xf4b3b9f56d18aefff3,0x8313cbf30871200a29,0xa450219414836b0769,0x8a5b318de5647de633,0x66513a9ce515321df3,0xee0192aabb8f1fdd8d,0x13ab8ef36e19414b0b,0x8d1f3c2e23f972db7b,0x69413abdcc54ad2c30,0xcff2aca77145e46615,0x1c3a444ab9c7b380f,0xf8ee5d0570e83e48b8,0x69b95b2b818a10c6ab,0x6fbbec81a32e670679,0xc5a171592f46b9e076],
[0xacbe3892e7c016a97f,0xc876756bfb910376c8,0x69d9c769f7be71cbe5,0x34bced57cf2e266c54,0x5690817b5ce27c85be,0x7746c3e4f04c5c879e,0xfe3a97f73a8eb7209e,0x41b35181c67af90fe2,0x1a92391b378d6fd4c3,0xe4cfd6932a1bc3b652,0xe176ebbeea1bf722b9,0x929e891e55d7b73c60,0x2366a3f109cbd57dbc,0x3dcd5e230b9b9a534a,0xc0e26dec4a94911a5,0x4347a02d0bd99ecfc9,0x2c8be06cf98cf3ef5e,0xde258e3b71138f075c,0x90f7f7f9c8ff392ff6,0x189b91f9744dd37878,0x4a65056addf4dfb9e4,0x4b4a12f1f9a98dcbeb,0x25e189182d5163fd5f,0xec19a27ca865386de9],
[0x8d6507b4ddb13cd0c4,0x14877383121204e4dc,0x44d69b9b38ed72eaf2,0x461f0210e74c758f98,0x703c82d9ccc3355617,0xb7a5d0d327465d7da3,0x17b3e417bccca9849,0x10fd1c3659d3843fe2,0xe8b815999ba9afda21,0x5fd8fb6f378e3825ae,0xffcf258c0e070ca3e5,0xa53205a3c344ec3b0b,0xde31d691f8cfae81f,0xde41967aea32780ed6,0x38dd4044c1bb24325b,0xf5d13180c256364c8,0x4233875b68e02e18fe,0x5298aa91ce395387cc,0xc9dcdc886dff9ec52a,0x9186c444591a3fa86c,0xe17a4ad9896b196746,0x31de8d1157b438ecea,0x6726c36c38abdd914,0x558a07381f3e88e246],
[0x15b7da9e49b46d2747,0x4fcf9b95b222db8a7b,0xa361d1b2b5504ae23b,0x3461669b8a68a38630,0xdf799b7daa2a19f090,0xcf887de3b296a6c996,0xb76103db3f2a540a99,0xf33432740741811a0a,0x248f30165f1560edc4,0x21e64a49bfb141d638,0x3400b128c68a3862ec,0xa397d939f4b852572e,0xb852b6760fd2d29644,0x379f1fc90b0605c637,0x7035563988b71b0d82,0x43639dbeac047b1d72,0x830cb7836c39c66c64,0x139edee1b23edfe829,0x3c557c2ac96f2892d4,0x8ac0729b4c175e152e,0x9a8e5ce38b97da9db1,0x6fbc493352c3a6d10f,0x2a53e36dda15ab6186,0xce576dd796d0d4fa2a],
[0xeba664e0eb71409c02,0x84f0ed4f040068968c,0x8ada108f69ef2d1294,0xe0ff40b94b5dd40a3e,0x4115171ee6b22dbfd8,0x77def19998dedf1528,0x405dd6c63b99c7516e,0x531de7c382d5fbd790,0xc59d2d0ccef918466a,0xea2f05dab10d1e8a92,0xf895965fa516b05d69,0xbc9775a449bb54f34e,0xc643c085c557747530,0x3ea862dc2e95f98e81,0x9ffab017f8294a2dbf,0x6c35fe38ce30031c96,0x3d722029ae4d57bd65,0x29b03257039140142,0x3a4b37c2c77579d071,0x7c909d3ea99be6bdfb,0xa4caafd10b34b59d8,0x669f200df7e7520e76,0x9dd3b080919af1e6f9,0x98cceb929602164ecd]]

def tile20 : List (List Nat) :=
[[0xd220197874a974ae4d,0x116e9c7e67fc725a9,0x28602cd802ca627a2,0x468ba8144c7513988d,0x44ce60db3d1e91c91,0xb3670f28330b5ccbcc,0xa1e28e62962eb5781,0xa676407baae2a23822,0xccbd068bd4e64ed6c6,0x6ad8acd0c821ae3886,0xf04161712df848d64d,0x600a25cdd64d0df8d7,0xc3e70508d8174c057a,0x6cfeb5b499500badc,0xa7d22c0e90a2fcc07,0x4031bd6db2d1833b1,0x4aa8da89209c6126e2,0xd7b3afdebd2ccfa0ee,0x2ea3251f84f51e2345,0xcee6a8b33d448a2304,0x88249abdc782f424eb,0x36af7ecb9951304c28,0x1c6f44afa5e16546ee,0xa6b1db5bf95ad24108],
[0xd8bdf27a03f81879d9,0xb9ac09fa1addd19eb8,0x9def71f17d2754008d,0xff179eff35803ee129,0x3e75af2fa11bb9034a,0xc02cc05a0688df32e3,0x373e5193937aad9e00,0xa10b0e41e8881eb243,0xe8e840312a16df199a,0xd6a011cfd633d5250,0x4f06328902736c1b19,0xf1cc110eac7ed814d2,0xa2cb57269c9ad32173,0x7227a2347433589e39,0x6bab348465f89ac526,0x74b0b2372a211f7317,0x562ce365ece51438fd,0xcc60b3229009eeaa03,0x9c44219fabacd9c9f8,0xf4b944e9702b8f13ea,0xedcafc5431eda646f0,0xee8908c22b784d0510,0x650385c0fe7b31c435,0x29c8bd1f7417b555ba],
[0xf8f3d003a9273e1315,0x9c86f77eeb202869db,0x46e9c9bd0e5e843eeb,0xcda13ea522e7b39301,0x1e06a64f33f4715ec5,0xa31bf8c9208f161aea,0x8d0250ec42e5d82330,0x97758736973117062e,0x118e0faaa61fff58fe,0x9f13cb78a0cedf02c,0xd7ac11be0d053d5037,0xeabcc4aa20b997edf3,0xc2666fc4d95497ad0,0xe821057a035fc4fb4b,0x89c50cb01f3d328205,0xccb07e8e596a6f3518,0x63d6ed33cfb4d16f8f,0x7c7c84d06b29edab05,0x588ca40350ecf86aa2,0x750fa2fd1d04fdbea9,0xec967ff8c4efe6df06,0x5b380c017b1b0b1f7c,0x3b2c0cc53b989fa4ae,0x8d1792ea37126461b6],
[0x4b72876b26236e48a4,0xf1286057c4beea9797,0xbde1e7335b4041008c,0x3751efbeba46096c34,0xf55b54555e08ab7adf,0x8bb7640f0468141c5a,0x2279aed31865476db9,0x2f036f64b290f18f0d,0x24732ce69c939154b3,0xdb5e9192a61edced52,0xc838455fa6f669c349,0x4b4e48360686a3d8ce,0x76c06c838989247fe8,0x9701a0e07914a8ee51,0xad66aa4c6788c3e1c9,0xeaa0a6111caa33158a,0x4fb0a42b906033513,0x3d121ee6e5d6f80777,0x867590b86e1d1d4e08,0x3b3449518d8ab9450,0x579f54f48298e9c934,0x69ec090f109dc38863,0xf7e1c1c1f34f0a7f03,0xdd069801ea307e5017],
[0x1f09aaa8d5eff3621,0x84965a58a8345af81f,0x37d6bd7598ed4ff728,0x35011b1c649f78564d,0x6e562868e6fbfb1c31,0x1a5391130cfc77e9f7,0x5a600480d25f929a43,0x893e502d9ce48f4ea2,0x246197c6683ae647b8,0xa408c21235f5e80cc4,0x4e25ae0982b6de677a,0x11804550ed9d61425f,0x5e6e108f159a0137d,0x98eaccbab16010e22a,0x98ee4b156ecfff9d0e,0x31ea8f572fd580d99c,0xaef557662d9735b64,0x2a787e4eb956ebd2d1,0x4a1b7bf2a4fa6a7d0a,0x7d1b1d01070cc43827,0x2c4415fb72d0dad3f3,0xecc9793fda724b411f,0xbf51caf6a7adc2ea0c,0x5ab0543bbfea281bf1],
[0xa13261677cb1a38981,0xc8d4e7cb7062417a73,0x4b9c78be5f5282affc,0x5efd84fb264c58af80,0x51b4c2d1d38c5d87c4,0xd538b3ba31576eef75,0xb4e67fabd89a11a2d4,0x7170bcb32da33c39cb,0x1d257b1bd17d541a38,0xdae386859345d1009c,0x60d4cb56bc19a2669e,0xb3da60039a6cbaea56,0xd7b7816901565d02ad,0x15937d4b712fd6ffc4,0x5a39591e44a2f3a63,0xcb44d41e7b7cc6a6f8,0x60a5a0ccf5bf7f1b11,0x1ff7c2e870bf0beb49,0x48cc540863a943c725,0xd57c9f9f5ef0ce08ba,0x3ce70c192be12bdc14,0xf5084e5b9a3eb2e1a4,0x2eb6d91608fe94d826,0xcf57c308ddacc80e31],
[0x56ea73335a9bcfcbdc,0x28f6c94299cc8e0544,0x8ae350dee452a210e6,0x58bdc491bc181ee962,0x539bbcb17adb23a1e7,0x57a0d788177df4959f,0x17ba759686220f2288,0x151406639057a2ee78,0x4a2d94ad0a8fd9496b,0x74bfba12a22740b776,0x108e072fa3d6b93e9d,0x752d0437d2e6b1fa49,0x7f5b7aba7eef1c9e8e,0x4b2ab7bbdf8757caa5,0x2c8475d3a5ed7bd301,0x820ad2d219afe72a54,0x80b0f565778faadde2,0x6bfdf469a2fced1f5c,0xeecd81d12fc3b5355,0xadf4779d51bd0b52b,0x962235646c1545e605,0x60337db0f90c3a8df2,0xd79ac10e8da832450c,0xecdbfe3fa2ac19988f],
[0xfe3ffc66430bcd884e,0x802e51cfe966fab314,0x107283593fdfdde85d,0xb2bc895b1f4c64fe4c,0xb66c51c043077c5cd8,0x6bbf3eb3dd238dae1f,0x525ec55a96574dd387,0xfcb34a89b70ae28643,0xb5f359fbb7e7dba6f8,0x97280e97f50827adfe,0xe7a37e635f191ec5ff,0xe2f6d1b5b0678f1ca8,0x3a79a9dca3cd9712cf,0x709321d1740cab6211,0x805178ed1dac23157,0xa433addd23a4628355,0x9c0e78e620f50ab45d,0xe1857a943873a11d4,0x94689e116ebf7c707d,0xa716b4b5bbd41cd91b,0x27ba427cbdf8ba7045,0xdf7d4335b7f7cb6213,0xd5d60afe1519db94fc,0x68c9810eb68812391f],
[0xc37fac8428e0c0e8e0,0xf7ba0300fe28eb1e0e,0x7a537d4cb7338d9aa4,0x7e6f1f74f925470c13,0x3170a3a511830c5a44,0xebf87671bb21b924fb,0xc09122bc5153d63603,0x320a9ec2e94f82586a,0x318de59a3891ca63fd,0xd0266c7928010d909f,0xdfa55e6c53ac8ad4eb,0x7c9d028170076a36b0,0xdcf19d93316066c3f6,0xa9f660bd29122b7ad4,0xe800a6010ddc19ff7,0xa95d1076bc85cdc935,0x8a06d69ded61ed6faf,0xe4ff97b5cefc461f14,0xccb68824499e7fe5a2,0xbdad425cd714274700,0x2c35333c359e4604a0,0xf5962a46ab853cc689,0x4a59a5a5544119ecd3,0x7088037df010eadcfc],
[0x47da7c5d2f45b22426,0x4419d4b44a2bdb3c6a,0x6bdb072d106748fae,0xab6097337ce277ab65,0xc29566c1c1b951e7e4,0xa0522db544e3d4c124,0x6e30e2a64bb876ff3b,0xb269f4191b7243a455,0xe3b6cff84f775bfcf5,0x644bd113878289c188,0x401cf230a266452aa9,0xba7e9026ad759d88e7,0x675c5f2fdd2dcc328,0x6a3305937161b4a163,0x7d7c5fdcf5685f0737,0xe499af4727c02d231d,0x2808bb607534f81c4b,0xef78f5a7bcaba79e1,0x19dbcdd62e259df4bd,0x2ec99088a609db4ea5,0xa876eda8d251c2d503,0xdca9f529eb00d02348,0xa24e0360b884b82cda,0xbb78e3d4d82a6f3030],
[0xf3fbb04bfc83dc0a99,0xf0f00b06b6c3924ece,0x786c32a9ed825a9081,0xa09ed20fafb56b0fb5,0xbeeb79e2a6a41fcb43,0x6f5d5cd32823646db,0x7cab12f7d54427b914,0x8a43c1891fb25804ec,0x7fece24dda73f748e2,0x4a93fe361ac7ce6008,0x59ec4488628e017863,0xa89e0408daf05cc2ec,0x5aba0184149721ab76,0xffab446b0badd28567,0xc0833cb2a479741cda,0xdcbaeadb5926d2b65,0xf552098c931f620104,0xab128438ec0e37ff2f,0x63e6165ab6d16321bf,0xdefd9b2cbedb943bab,0xa22a748389f8bed9f1,0x5a6c42a3159e13d0ec,0xf6149715a524486c0a,0x27b58963c47e7a9591],
[0xd1e798278be37ff723,0xd89cbe3f3e053b42b5,0xa1b83c8184367f56c1,0x5417be9742f019c8e4,0xcef5121ee27f343887,0x9421a76355f04e73e6,0xbb3a2dfe39e9b2ef91,0x92498027d30ad9cb42,0xb223cb20c8f0e8490e,0x467ffc6e3878b27a5c,0xd63067621df08a4653,0xa5f2b32f976146c76b,0xc4cce6b564364301a4,0xedf2255f0b4a0531dc,0xf66449d61ab51ccf35,0x7a18efe02d2e4745c1,0xdb793fa7bdce5ac2c1,0x5b02b2b7aadb74e4c0,0xe3253160c397eba26f,0xfe5caed126f4f57296,0x22e16502d7684b0599,0xdb413cfd9500462823,0xbc4a671c52d5fae146,0x691876707d4a69ebcd],
[0xa963b2114f5938f505,0xc7ae2188573323e2be,0x21834e7cc1987dddba,0xb4004ffdb985ee788a,0xd0c509ad2e8a1b0782,0xd17b104fefbc945beb,0x8f7868bb6ea060f45f,0xc9e8f81937f4b5b7f4,0xd3a0c9dbd306d9237e,0x50ed7c5eb123b08271,0xbbe0fe9d7597e0d499,0x7badb2908f3b979039,0x2b367a494a2bf8bbec,0x1c679b66bef20b3975,0x13627e627652dab70a,0x8028dcaaacbff93b5c,0x51de7fc27ec701619a,0x77d016a9bfee5ba609,0xf1e7342c047c9a3056,0xf31e2ba5051b0e973f,0x12836c53cc706a6310,0x961f380146753f852,0x59efc901d97489ea0d,0xde822e724c0f3f76ea],
[0x4df695381898fe8d33,0xdc75619a8123ade6ff,0x26c603775b7a383c8b,0xc475c110ebc89f529d,0x8b922457913845e4e3,0x51d6763ccffec4b785,0x896bf313cc6f99b336,0x31a97f0654fafbfb4c,0xf7065439439bc6a7de,0xb0da32216846359694,0xa20c40ad44d7ea5681,0xd85437e78f317af2e,0x25c48bcdeeb10c5051,0x6e8a824a07bb754a92,0x899a11b303ebe17a5e,0x8bbfbd7ac4e7e58ef0,0x7b1a7918d3427aa0bf,0xc7d82df831c61f625d,0x7124d7dff6b04a21d8,0x484126c535e96b226b,0xf2e5693075e88da715,0x9f21e53e69c13a5bdf,0x293d82c29a77b8ea1d,0x4f151f62bf6c890860],
[0xd4992ffec59a9b410,0x5ec248eafa4642c2d3,0x164a9c5c8225641c8d,0xf3b438f2a5f5e60b0f,0x2dfef44b82a77db5,0xdc58183edad216b510,0xcc5eed96e82b40c170,0x71c04d52dee370c0ef,0xab9b7d1e8ccc03ad73,0x2fb9f1280280b7944f,0x6f9982d11880afbd5b,0xf37ad7ef8568fac7f2,0xd010694d65d00d565a,0xe4e9dc5e91a280423e,0x38ceeddd6e08047e22,0xe0e9213ab236af8753,0x59e4e0d8c1b2964a90,0x94b76aa259e7b0e97f,0x60c712cb314b4585b3,0xe4d70f0cb77273ee72,0x45cc2f398ef9fa7fa1,0xf821276ed0abc8500b,0x12072b949b2e063369,0xa5bfe0fa31e3a51210],
[0x1ce4401a1c41747d26,0xf43e822b65c8e2ffc7,0x4399b0fd84c30d7350,0x7e2395758a47dda980,0xaa4b23c9dc2caae866,0x7247e4f972ef293ce5,0xead65c3ce2dd4665cd,0x8d1583f500e719543c,0x24e9bf8172c3a8e8d7,0xdc80538c90c5977a1b,0x9b8ac876d8830c3aa0,0x5aa187007e4d7bcada,0xe826212fb7e12726b6,0x8b7a6383b314bee073,0x59cd33491254c4c0c9,0x45cf85bed0cdbd3395,0x8cf7e7d21ef6dfc0ef,0xf8957c35691e143df9,0xade2183f6bcb7277f6,0xff46663cb8f7c0ee7c,0x22630b22d915e3d9a4,0x431ff30767b04ad8e0,0x4dbb743c58e60f50ce,0xb7f43c56c0c611a4a3]]

def tile21 : List (List Nat) :=
[[0x97961dc13a7e1035c0,0x79603e94a930abdfba,0x2dbe90714be5a0cdbc,0x3d805415e5ac41f953,0xfb0ca1b12604c43979,0xfc353cec92fd2fdcd1,0x39e4ff9ccab8a4d07a,0xff76a81eba4606d302,0x26015a18e4b0ce677e,0xd3f67092d49e56f38c,0x38d0633aef8ad921aa,0xe4987b6a134615ae80,0x5b3468feddb1ed7ae3,0xadb92545c802a42a44,0x177996101dfbaae7e1,0x83ff5d0454c6c9b251,0x83256336c15bd1edf1,0xc9a6e949d0c710d6bf,0xb2b3ec9e561edc1fb0,0x10b1655ea8da088e79,0xe2eb008c8866315927,0xd2849a93b645493e66,0xdc3f79dcad70293ec9,0xd0be232c531ce0d2b5],
[0x34ecd1bf5110379b42,0x31f41e1e81065a790b,0x8fbb11c40acb9d9d6,0xa6a60f5e7d31b1093e,0x1f1ac1d2e904bd2bb5,0xd57280fcffdf3db867,0xff9e3bda5a5afbf102,0xdcdb12c05cd91c21bf,0x39c475f979cd245395,0xb983e7a821c5bf9c46,0xecd9c0bdfc49b1c6d2,0xc1af1481d0dc950025,0x20ef1541fd6030c261,0x672c4d77fcf7bd1146,0xc5eef6244eba98c50,0xd0e59cdc023ba873af,0xf32e0a2c2acbbcb6bd,0xedcb96e4d9b931b8b3,0x3cfe89d1f098228754,0xa3c22352c9577481b6,0xe8fca02f412c1d787e,0xcefef3ea7b526eeab7,0x7cb4fc0e82ba21bda,0x4c910c823c6e080b8f],
[0x70c6e02518fdc75cf5,0x1961a9041628672311,0x8cd2133dd78f3b3347,0xd6e72984193dc84eab,0xa1187050f1fa1d123f,0x94a1125ba0cc537e0b,0xd644d4c87e1441f394,0x9dceeff15352617d91,0x3751b74f01bcb46d25,0x874a5440b1f5f5b77,0x2b4ba09937a1b8f326,0xbf661c2354c29d4550,0x8ef0b65d2e39491597,0x9459f1a75e3ca8a531,0xe27e84205dcd493bba,0xf2057f350b4d038ae3,0x5c4ddb0da4d0e77fae,0xb2c19e933e195ab61a,0xef0f788a3dc6cfd038,0xbe147885dfbdbe45ea,0x5ba438864e642d4c00,0x5ac2cdb050f38abfa2,0x72e220b4966e36f6fc,0xdcd4c1b43ce1ca6c68],
[0x54f29315636e170b65,0x433fee6a20c93cdc00,0x48b0154d9ea997bc9f,0x6ef41c82654f00da7b,0x8c83f456852d54197c,0x7d64620f15fbaf50b6,0x3036154e17d3df19be,0xa88508b9ba9c3fd7ed,0xf51c9e7defd2295b5b,0xc3ceb155c7be28e6e,0xf10065a6aade4a5ce1,0x3717f3aeef663dedd9,0x6256eac11236749db5,0x76e944ebdf7f2e7257,0x10247dad57c59f785,0x5c1dbf31f3be75f4b,0xba5f64efb0adab53bb,0x9ed9e13a884411f84,0x4cf6bb32835f490750,0xd56fc8d9f8ae1d1dcd,0x674ea99064268376,0x37ccc59d42099728e8,0x9c00ea65ae7905d9ba,0xa356fcfebfecbc5287],
[0x51bcc94b0bc70fa369,0x555e1dd5aa29af6de1,0x897764b8a603cc16fc,0xba10309ed8ba054ea9,0x9f0f53178801ca51a7,0xc4f989d6098ed68d10,0x333cbeadd2546250c1,0x4d0f937d35882e080f,0xbeb25e523d7f75436e,0xc2dbf8b3739defefa9,0x102a5d0aafc3333d68,0x465d70c565dd940e41,0xf616846ff248b2911,0x63e386279cb1868682,0xc1362b3a06fa4753e3,0x4f72ed87aa33f200be,0x34ecdc8a247c9a9443,0x431278a56adbea91fd,0x5f03e055106e93fa60,0xb3ecbc8aac464a8f79,0xd25dbb3346ebef5779,0xe3422517e7d3e2641b,0x1326bdb4261b8bfe49,0xb616c03958e216fb1e],
[0xd5dc6720a8628e2b7b,0x170681233ea35b080b,0xd2ffa7ac9132add1ba,0x74c0fd40dd8cc0288f,0x2419057661c5960ab4,0x33e1241179d5b6c502,0x46a2bc16ec4223b014,0xe05ffd4cf07746420a,0xdd279d5b6825b3d0c6,0xba9e15ad67e60bc42b,0xb32fac89610167ee0d,0xf6f3e7820c22971157,0xa4374611c6e46e8157,0xf8f518bf1f5998be40,0x4cf30a43f6fd93fc8a,0x8c1884e1ec81c2b78b,0xd1c2356cd49cd4636c,0xd1a9750047a93b780f,0x80577d8932d136e19d,0xeb668f80331510b782,0x640e1c777f5ed7e8b8,0x117346711a8656c043,0x1c1b3ab51879055e52,0xbd77174605e4983b4b],
[0xdc050a029caec32aaa,0x4504c63afccbf79fbb,0xead5b455b7b8b8c75a,0x439858807669325550,0xc17657da9cbd1e7305,0x2f5173cf031f9f4f08,0x9b900d3e3fdd44dfcc,0xf2602b3eeddbc4fc3b,0x3a0290973ed7668ec4,0x5fd5f9cfeca6dece8,0x9a240e9b03b74ec6da,0x109e65508c043bda90,0x19234e264a308831de,0x823feba4dc5eb4304f,0xbf5d6e6bd061bb0ec,0x502a1b0d90391483ff,0xd92b7f4e7cc47da2ba,0x5cf22774479bd0d39b,0x5d987cc3cea2392d87,0xf194a5011a0c2d2664,0xca423daacb94dfafff,0xf5ba3d8baaf9f0a40,0xd7f653b7dfc58bd1be,0xb8562c9338e413002d],
[0x82ea69df5894f2bba2,0xd7252fca93f52fb2d3,0xca031611ae1811552a,0x689e5267e998f84473,0xa9eb8537aa990d25b8,0x64b93fa90de52b5d49,0x49971ed1f777edc1f9,0x298770498d51ca83d5,0xbdb9ba373acc8863ec,0x3edba4838ccebda96e,0x43d093f0dc5fb49df2,0xe27214f060eb4fc32b,0xb1de60c17b289d266e,0xd910edc63c4c9e64c9,0xbb84eabfeee0a756e6,0xd74968d355037a4b73,0xf2c48c826c30be3e8f,0x5fa21ccf16bde3f040,0x22a288144ea9fad2a,0xdc565895546b2258fb,0xbd1bb84f525fe6c699,0x4050501d5e04d8d229,0x2808d92b0ae7f40410,0xb9b0262f78d8dd9914],
[0xb1dd35575261dee090,0x6bfd9162cf16741da7,0xf8fc772dd5b1378eb5,0xec63d9822d73e06551,0xd61230296d5cff6751,0x76ca983eeec6ba8d53,0x87bac8ff28be3f97b8,0x2bd669420bc8d79187,0x37d894506152ed1466,0xfb78aa75ad615c629c,0xf36a2d9de00578c92e,0xb3419e7e3ab981431b,0xfef2dbd97144a3157a,0xed1175bf5f6f81f4f7,0xec161ca18f1d2325e1,0x4cae12902d24319813,0x170ea00e0cb274db9c,0xc15ffa084918f075a,0x7084d6e89b4319266,0xd00f5fa1806c651c98,0xaffe32ee5bf539158d,0xc281ba7eab4069573f,0x37255170bb85113401,0x43e5cb4d2a6c24d450],
[0xdcae94e7fc45415f7a,0x23e3408b53258d20e1,0x426725a6a5854b2bb0,0x28c7783fa9139f212f,0x5b6fe518509d8e47a9,0x4b87dd48536df9e371,0xab1b3f5be1c34537b1,0x82774fead639399a70,0xf2c3522ea57effe4f6,0xd2029ccff552fc2cee,0x75a5f3f4e81e061ac3,0x6924dc5cb4dd6882e0,0x8788feedb82a90ab0b,0xeab9f94ccecb047a09,0x552f70e2a5c9edf6fd,0xd31817ced2e62404e,0xa3bbdb5fb9e0b259e0,0xa66657aa13aff5ca76,0xd6451687cf3873a300,0x311a0c6052983a6bfe,0x9e9a411d9165a48546,0x4ca626cec9ad107528,0x6e7b680c0a21b7c690,0x77e12511a1c3a10925],
[0x7d2288eaee9c86ada0,0x6cdf71a37e0b5727e1,0xff2b5411cd48df135b,0x17c2621d2fbd6c3669,0x741b00515a935fb57,0x76ecd80516fc169868,0x6e6d2f37246b3fb331,0x9f8c2677576b516a73,0x945f811dedaaa36978,0x6893de0b90589f0eff,0xc4a5489e1ffd5d6b70,0x22685e394030285e46,0x2ebbc84f8d85312aa0,0x87a0a70a914a1ee924,0x7f9d292547a875e251,0x6d1b638fe855dd248e,0x1839a7dbb556befb6d,0x957e1fa2d1231b36b8,0xe0cce8a91880226f94,0xb4675491b4db783c63,0x3c9c30331d5fd8fba9,0x4e6b7e47b9e385ec63,0xd676cdd241c061d134,0xf4741269306158d9c4],
[0x420a19e100e6a50008,0x5d9030bfe8a38f2eb4,0x234d8725a37db5f160,0xf68efe1e32941ecebd,0xd31ac71ce34e76c5fa,0xfa3cf17fe7be1200af,0x924f711cf11a7cdfaf,0x235af3c660e2a4f0ef,0x5f1e68358043ac2e10,0xe7eca4018994f51299,0x88bc8634c7b4e4f0eb,0xe7163a4de7c431db7d,0xcb5ae17408f6b9fe4f,0xf02b9035cbeaebc839,0x95b69c2c448c57e175,0x7e99af188f9e5e5941,0x60b966b243b5e5269c,0x3287e1625e3178824c,0xcce1e81ebf0c871169,0xc2b2c738cc85c5e881,0xe618e384c7231866ea,0x22c5b88e978af99bfc,0x964cb08d6567dbda03,0xecbb6326d701d25c78],
[0xc9ebd87c6e0b269e32,0x9ea20ec5c52667d12d,0x6d8f68f083f53e5920,0xfe2a35889809d74195,0x9399fdf15966102a71,0xc899c5663a725e7904,0xbd54fe9491584f89a6,0xb60c1a89af689e1b3d,0x9974a90e3428967e94,0x4062138df1ec5480df,0x53c5b54517f600fd3b,0x5852e0321f075243a,0x915764783c6ed8423e,0xaca47ef8e6b5eda63e,0xba0aec97ea6fb42e37,0xc2036462af389fa316,0x3563c17b04f2fa61a8,0xcd3a4c25b919341030,0x17dc5e27348fd513ed,0xbea1fdf35a90749426,0x74f762ae1048bd9a5f,0xb0c758f0e42327f070,0x91a38f0cb458d3f39c,0x9624661d0021a1c951],
[0xef09ec3529e560fb37,0xb3c8c32184831046ec,0xe75cc4a793501be898,0xf7d0cea5f02bb625e,0x837aaee16e493d47e8,0x5196f72a5e2f648532,0xf860017ef61af37a7d,0x8274e2f3d2aca2eb58,0x499693212bcdc188c5,0xdd6aec10729199d9c4,0x891d0522feb6097845,0xeaee7aa5923bd5d8f1,0x28eea199107090603e,0xd08cfe12c1c4ce56de,0x54faa07cc35df34280,0x529083e5a91bee4b79,0x6468e75e88afd005a3,0x5f2051be21954f6301,0x75ad08d15260eff9a5,0xaf686a8de4dd84e796,0x9f6e5ab4627f1a8c79,0x24633468aceafa3a2a,0x3e34e5b579a7803044,0xf7f875f3e0278067],
[0xf3568266e7f93c8446,0x1dbd809a025a97547a,0x15fdc1edd441ce61f8,0xf68564a4229285bb6c,0xdd32cd784c1e8f9cc2,0x28d5d7bcc9ec2b1865,0x95252b3e3339c56a89,0xe1b2eeb8e8e507f992,0xb8315f5beeefc29929,0xc4b3acbe93dafe699d,0xcaaa17ee4a88f70561,0x6f2887767c6cfe4f64,0xd0284641548024ec78,0xcdf18ec2e2778c8836,0x36432cd6771237f9cf,0xb80000878ab02b9dd2,0xea9912b7c549f14e3f,0x852effbe0bc5a64645,0x3b8900acdf525d3367,0x1ce24b508c0b27ef39,0x13c9199ff71c21ea8f,0xa950dc6a3bec2b4eaa,0x19b79c8ad10896ecdd,0xc61e3aabeaa5b87e5f],
[0x4f470582a115d7def7,0x6f0923593c0775255f,0xcefb25f52c3a256762,0x732d4540a5d21b03f4,0xc5dfb0db32013ba63a,0x9257b05d3dd803947e,0x57d2024015695b4895,0x89d428e8df8e389388,0x10459ee744fc02ebdc,0x65f1cb04c3236e3245,0x46b65c130acde30af1,0x9015d037ffba3cb340,0x64cb14e27375b45a5,0x564bbdcad9cd7aa880,0x6ba67e89e3f3bfe14c,0x9abef2a1a1542d2d7f,0x52f4487bdc783b9d79,0x802369c437db86e49a,0x8d0996fbaa657069b,0x5fddef8e4d369c3a9c,0x8bd19ea7ff0fa05b07,0x83fa5fa94577b9480c,0x5c57b05fb9781dd55d,0xfe37b2de4cc1805a2e]]

def tile22 : List (List Nat) :=
[[0x332854b74f0492c1d6,0xd31044d7b8028a1b0e,0xc558efceadab19b0ff,0x8232c992c4011a3b8f,0x51acdbe1f3eeefe2d3,0xb762d013b00520c645,0x51f62d828e7d7db689,0xf9407f53875a04763c,0xdd2d548134177c6aae,0xf72f7fd32540991a0c,0x16366e0159427898de,0xb7377016400230b2a,0xd07458591d018ab340,0xcc87f97b374c587174,0x17d52632feed933001,0x12e27898eb1463c610,0x3ad43b30e4696759dd,0x7b51680146c767841b,0xe890a352b1948210e,0xe49c2148e10e14749a,0x6cc96f3d2d7ad5d477,0x2bbdf216ab7cb2a9c6,0x5203812d5919977bf,0x4a9537dd97a17aa8fb],
[0x23ac4df1fb07855bb0,0x898b27db577cefb760,0xcc2d0eab72337b9e94,0x729d134fd5affc27e1,0xe78f64f377d4130bd0,0x48470b067f7cce7833,0x8edf802e6e769c9d1c,0xa1ea68845d33e59c02,0xaad0cca80c48d40414,0xace39027ba86b692b9,0x87e424a4da2a03f4f1,0x168b6f5fe3df68ea23,0x4fda6a1e7bd0e6c990,0xea49f83ca65c378fdc,0x2d891d03f1177b1c97,0xeaf50f216005137ce,0xeba284a3e9b5e60fa7,0x653d0f0ac834b480f,0x6146d035229ac9e87e,0xcf65f1fdc719bcadb8,0xf2cec9cdabb85fc252,0x706ad0e376417f444b,0x6e8e3b0bfb59d88c1d,0x8747e176c024379f29],
[0x5ca935c71b9dc6b6d3,0x7e81e8c7e03ffe2721,0xda70d2e6b9a3b1b8eb,0xa2943703491d17ed10,0xd39ed8c841ccfdef11,0x43601678500e6b6c4a,0xd4329d875699d79463,0x40f88a21b2fa72d26,0x51480859f64175d4e7,0x2e950eb551f6425d30,0xd03c2f8de47b507a12,0x25aa008de27ed803b6,0xfdc79cf7c2df0a9bab,0x140f6a465e19ac59f7,0xda19983f7c8db156b8,0x676a587d88550b9ac6,0x76534eec60c0c5c321,0x2e571b678fadf4e675,0x796cc89317d748e38b,0x21f6e3f02312abeb52,0x51c4f88ca165a86d30,0x4a77a60aa209b1b7dc,0x68273c958838b28c06,0x1093b50a925071ef1d],
[0x52e330cba957bb7a6c,0x3c2881ceb7555fe4f4,0x86772d6322376191a0,0x6eda1e91e523905134,0x12f487ef08c7d6e126,0x71a8f830f2a9e79aba,0xe4edd73bb75bc029ee,0xc1af09aba64062f0d4,0x94285ac98403d676b6,0xcb4e3bf31e01c888e5,0x162cd2b00b8d1ab654,0x482a98acb87a1602e,0x808e7bd9c3446fda86,0xdbab5271dd962b64a5,0x39cfa4a74cd25a4a94,0x95ab1ab8fc7aec0ee8,0x93899c2bc0809c8c68,0x4a51b2521072faaa5e,0xeda55e02ede5c4dc8a,0x241ead1000b132d901,0x4028bd2387dcc1029c,0x9576064eeaf4e37e21,0x5835707f0ea789edf8,0xbc7d9b6ff955a4928c],
[0xa30697336564df194d,0x8a54e5fc87a31735b4,0x3bce197782ab7af88c,0xa2b7fb045fba3b358d,0xd5ae8f034d041e4f0e,0x75560401609245643e,0x719494646e7de652ec,0x958356344ae49118a0,0x9a933335843720704b,0xad51afb3030b33dc34,0xff3f252fef7403e876,0x6d087180cfac428682,0x3ef83c9f8f2a692383,0xa5ef0503cf6125f195,0xe98365098a73a66d89,0xa57b7e93b2f8f4f6c4,0x854349c6d7655e3fd3,0x9dc85532a116e97ef4,0x7ebdb381ef96c54696,0x5023cdf82355b00183,0x1761aeb82a1b4df599,0x8f98b8b5aeee2cb9bc,0xffb8823a4a1b672735,0x3b0403247f2fa75968],
[0x67517c644cc7cf034b,0x2ec3bf7c29df5ae2ba,0x28f76d002e2a4ff38d,0xffcf82c01f22d05e7d,0x3e155531ec0ab5298b,0xfba6beecbb9f430b83,0xd5e8171225e243dc28,0x39f1d55bb76fe4ce6b,0x102a4b1c525c11839b,0x2d4062a422b5bcf8fe,0xb86eded26dcf10294c,0xbde3cf3ca2d11c218,0x1777291c6fca300a39,0xe808973ea2d4c04069,0xd70fe63c22d457f4ed,0x5d27d3206fc3834ee4,0x6e22e2cbd8f5c45b24,0x7c10eb678f51168b41,0x2afcfc06cc10786d63,0x55c8a10d20a411aa69,0x15719c9a4a0b3e023c,0x833039988ea76f8036,0x5a29e69fe25e4b1d97,0x15b4bdf64419825905],
[0x967891fd887c7bd8e1,0x9730aa038f8ab6830f,0xe50e82d1a2b09fab01,0xa0a7e02a512b0f7e3e,0xa9207e9ce9f5a08414,0xa9de4027632d33e14b,0x164997aafb118cc05f,0x5d3d4d50120e5bebba,0x29e3188c0dd692a6cc,0xd6abbce58832b9086b,0x22e074d07429a9e563,0x773ab0c687ef2d4067,0xbc2badd40c6125691c,0x3f37292ccd77e2b5fa,0xb264c65bac9254b7e,0x152e8e406e8ba691f8,0xc2335406ab22dac4f0,0xa0cb61486f00a195dd,0x7c0b03ba413950798,0x7bd420a0c2b059b2cf,0x6005d828719898552f,0x97de08c329b9ab8aee,0xb5271ad62861dc7d47,0xa13615eb9a6e1d6e9c],
[0x389abbeee45ff984b,0x8f2ea1f9410c27c3b3,0xfa9b01c574bd1f1a0e,0xe2b7414f2410ad33e8,0xc62706643bd81b4db2,0xe194da97fc43226e14,0xb811faf7b254c1f9d7,0xfcedcc8c08474b3b93,0x8d644717c0dbcd711c,0x2ddd2079d37fa4dd23,0xce2aea30a05b17ee5,0x712534bea8635a4e7a,0xe806bbb503f7df10ec,0xa0edb34f5bc9406cb1,0xad86d0780a0a30c6ba,0x9977afb219488b1bbf,0x9fe5704dda07aae6fd,0xfb092ae7c79b01b8ce,0xb270f9a2bc30790e38,0xa60dc4fb4542f78855,0xe6f4bb391d1fcf137b,0xf2c328e8f03ac1f3a5,0x5ccffddf10c0af1301,0x1dd0af175039689215],
[0xfa415781271d56ff93,0x1db1845f9f72fec072,0x7d87e7e94bfd5302e7,0x101d15f9651d73b6d5,0x66eef7a4a6c4f4a502,0xfea4199b1f5628f532,0x68a6ed666b55a665b,0x7cb89be4dc11197bc3,0x1056583ed12cc44cb9,0xef0b292f606307edbb,0x5d07fb76aa20324f9f,0x224c082807b0821574,0x22ef2fd1da3969c857,0x677f4021f1702eca4e,0xe47714684820590527,0xf1fc2f44aaa47aa5bf,0x7e7a2d8b9612daeb01,0x1742d2f9f7ead7aea8,0x8471eab9e148e588b8,0xeb704ca8681b4b3ce4,0xbd14978519639b5437,0x7b64ab5cdf3186c83a,0x7c3690267dc778547a,0xc064689f53838ee63c],
[0x43ed4f8ea4023c452,0x93055c96aa45b2dcc9,0x22c6debe8bd22a9725,0x3ebc3f5f2cde845b2,0xdbaa75452b3fdab2a1,0x7dd97cd2309f4ccdf0,0x3121648b7693891cd2,0x813a10bdcf523957c8,0x4c43bb3ac3ba52cf3d,0x62844b66a79a39eb8c,0x203aa922901693239f,0x2c54ecd08e9af4881c,0x524100d4e104045d4a,0xf4e5a4db24c06bcaf7,0x857f90e0070b0d597d,0x56cce9b3026232fd38,0xa41e5d51ed7c8ee8f6,0x2117a70c0e03a983f0,0x75b17ba426b7b5f6ea,0x5c5269365dc2febe48,0xdcc10c7e1206ee5473,0x4857f3ec8766c3157b,0xf42b6d3cf7c2242453,0xf4442f726df5efb266],
[0xc67f517881bcb3e400,0x39f00509960c96c9ce,0x61eb7fc63c6a1998ef,0x2c01339dc5d32e055c,0x29f77f3d0456e8f5e6,0xee84c4057ec0ffa62e,0x7a40f066c0fad0ee52,0xef69ba1110f29e12b3,0x7d08f443ec911e8809,0xf0c7ea1594421569c8,0xf2a7efab7a0f846d5,0xb4ddf292261446b683,0x13438636f7e4a100af,0x987210090f28baf63c,0xec186e54dd5005897b,0x174d77fe228c008af2,0x18166b74257ddafe4e,0xcf441f67773e9cee60,0xb5ad5b8eea8a98269d,0x3a4bc847c94e8b4b06,0xecfc8f19990f03cf5a,0x16eaa2e8d0654415a6,0x4989ca4ddd5b239efd,0x903664625b61de0d78],
[0x31493d1ed642c613b5,0xab4ffd8b9616f12629,0x60dde30d62b60c25ca,0xc222f108837b292e6b,0x83b2b391c894c8cf07,0x4e5b7c9f01a14ec156,0x381cab11fa5d4d14e3,0xa734de71a644e13581,0x4d69ae4cd8b8e9b7c,0xe69f57882642ed14dc,0xcc5dfdfd0a394be87f,0x2e82586c5208e4ff32,0x65124a2661d3c4d707,0x127028a575b291d68b,0x1429211a42a5d726ca,0x7b6aa836ad6aa0029c,0x9a619cdaa2e7bf667,0x1e9aa1816ebb8edbe5,0x12c99b4c9337a5bdf8,0x7d76d3350658ec6c20,0x95c0e76f4ed54dea88,0xfda560046c8e7cc783,0x365c1264544483951c,0x2bcc502c76922c03ea],
[0xdfe350239aa1526a22,0x3111b41849e06a1b5b,0x6ef061d607bd6d6a4a,0x4c41512ca18ad196b0,0xae94cf095cc84c9735,0x4b0451ae32c4ffbdc6,0x8f822f23ae5d22750c,0xc4d0f8c6790f93760d,0xe90148e090f399613d,0xb174b2b78b565e6319,0x4d56971f5e792dd740,0xb8bf562c9100ae4cd8,0x70edbd5475776f36b4,0x56d3dc71f5cf8f9edc,0x490bb93b122ae981a0,0x863cf7236c6c0637b3,0xc88b6e829a5ad0d8f5,0x29a20e1d258b80d7d,0x701b9e03b65084266f,0xec760dc9c808396a9f,0x14c0136bdf10e92ce3,0x75a75a18ae4a7e3178,0x9df89e759186ae2de3,0x62c557b36ccc75d1aa],
[0xc762627e09616775ce,0xd0c9947678748e7b72,0xb1460b6f2ed50329e8,0x4ae2e943b6030a2192,0x916e89fcb1fcfa6e48,0x8eb083e0e689c04cde,0x47331e5d7583835a2e,0x415bce6a85282bb94,0x1de8b0bc86d597ac61,0xa7847b3705644e9113,0x1c07adfe2b0fd58a22,0x64209e33df0d7c94de,0x557205a99a56e827ff,0x4c798d95be8e0e09d,0x9c7966c94a41fdbaf5,0xfc773f714af5c28df9,0x69222c2370fe6fe039,0x6d884d0c25947c16c9,0x5e360a92c2e48457ed,0x7dd6c7a49a5f8133aa,0x961876fd7c75966810,0xc9188d8468a97759f9,0x77534269c7e0b4ae46,0x7dac36dc7dd676f5c2],
[0x26e87aa02ad8b628d4,0xba389792c323f62675,0x2352956d221d161560,0x8c84f26c13520eff0c,0x1a32d12de8bbc05b66,0xc97d75b6b238878b11,0x254459c1fcd95cc1e4,0x27a3abfaf8186ab268,0xcb3e5cb808f706eff6,0xf4e6a879218779c577,0x7382296cf56fe68017,0xa464450480bb076055,0x1af58c8a426451ae97,0x4f64c89ab748b6984,0x912a6a015eabe940c2,0xd5942f6e096f04a661,0x53a6558ba118972535,0xe3dae75cf1a9e99724,0x68fdd9441c39d1f34b,0x56c6a63f9e83abcd65,0x63b86af8312e8263b2,0xba1494eeb381c43d20,0xbbd241c614464b4782,0x1b2c7501c174b1ac11],
[0x12c7cb3d5a5fbe0f18,0xadce358e8887e02773,0x790a984521ef77c117,0x925e4ff7537725a653,0x22727072d21b3a20b,0xc7a504ce6f8173a3d1,0xfcfa68ccf64fc63785,0xb9fd99307a4e50d51e,0x357bc34d542be47ca7,0xeb9935d3b1d8132727,0x2bd2c2abac84b6790,0x340f69512da2c9f4d9,0xa2d6cbc7a7a7366a07,0x6c4c27bad8a252d8cb,0xbea0d150b9c28bdd77,0xafe76805caa9fb2e49,0x62d4ed62195d55e4f,0x3ce8bf278902cb8fcc,0x85b2b8383ed5283478,0xd70bd1a1341cbe53c9,0xdfb2427836db8d7158,0x462d267564e96df8ca,0xbb7700c91fe6a4e4ad,0xecf05e02d7f017d15b]]

def tile23 : List (List Nat) :=
[[0x6dfea29f5c7f9c0199,0x360367deafb9710548,0x63fe03693784b4d3bc,0x52818e621d3a3c4549,0xe252b48337f86906d5,0xc12b2792dfc6f9617b,0x6dcc804d05e3b6064a,0xfd7ea9d3fdda783f7e,0x1bc57706a783c85a9e,0xbc806f7a4a0542e1ec,0x6742398b9f107cd534,0xc752ff1268739c7d86,0x77cbf20cbb066a3cbf,0x532ad9dd35763efd27,0x6be87fca643dbc1a7e,0xb6043c2644bf490709,0xc5009b42c5cfcf63,0xdf486675a95fb3291c,0xf9786627b3b5f06339,0x9ac41c1c12be106ec7,0x9f6d8784534e94c92,0xfd91f86a170ea4fb77,0x505f8adbe3850e5643,0x8d437f61bf7ba7cd5],
[0xae0f582abd052f90b9,0x4ebb8ed02e9a784f47,0x6f3293af0900a7530,0x3f1b95c9b837bba4ae,0x1c21c7d6d222275eb6,0x6f52759706b676a0f,0xa88c5662089f761577,0xe95b3e8017eb9aaaa5,0xfc5969f5f974eca6af,0xdc357e2e954a3224bd,0xb09bb864293836b42,0xb8f762d50df2fc4e,0x917669aa2ea8b4af27,0x942cbe5f5d46e64431,0x77dd5e88f9c8a3f4e6,0x43d7772ef196440144,0xb51b744fc6228c9061,0x9fc1b442ca1fd49731,0x1ca39571aac35d12e2,0xe799d632755ee4980,0xa34103ebd45c1914a8,0x75f153f6f2568e6cdd,0x6280ffb0a41ee2995a,0x6493fb462981842184],
[0xbd89b8489558d00230,0x8c01690fa9c6fee7c4,0xa2bac369d9b8c9ae83,0x2057c34b9bc3b47d44,0xcfe6fe48a47dab1242,0x3445f44f497f739dd2,0x8768943af925a8e443,0x173c7d0671c58eb2da,0x7816042f393dca316e,0x33e51e5f9d6e10ea5,0x592ca0ab19dd618113,0x4858d831adff5eef44,0x95ce83fe705af5a909,0xb74a59f225dc4e5c8c,0x12a64a0d3d82a04e45,0xd4eb3b92226acd7949,0xfc8e23aa18a581f065,0xb20084932069bddbb3,0x251a64f236dbf1b5a,0x954581028d03efff25,0x8da8a87aa74705a60d,0xa898e5b7c547cb6594,0x6a3f044f4ff102f635,0xa7dcd5b9bbeb0c2163],
[0x45a43e55e88d025a8d,0x74fb7bd16f75441b6b,0x2f2ca4127fded5b6f4,0x7097a57a9c47e48ece,0x149cf57f2ef82fbc3d,0x9b7a56f9a5fb223f80,0xde9ad936f343fbf431,0xec83affc901d5aa0af,0x12177bb9ca1303c148,0x9f1549ab0977e65483,0xd2a70a91ca9b665fe8,0x67b8ed254c37c1b1ed,0x7ccb5cff94f48c3077,0x86fba788e8e2123112,0xf0b0036c4349e536e,0x74e5c826c291872b0f,0x16182f0907d976fbc,0x1a4b801aa3c242bb2f,0xe831502b087f609286,0x2f5585327e07646a0a,0x715de620a3e5702ce7,0x4355a813214ea5ab1a,0xdc66328a3cded4fef7,0x58878ecea76da29640],
[0xa1b24dad08978991b2,0x4c2e1e64ff59da9d2b,0x5125c92311fd864eda,0x416c746296a4653ce3,0x706959076332e56492,0x7dbc685a751d764936,0xce67719e0df540d517,0x9048b4632c984e272f,0x9ba194c7be91c1d92d,0xe5e7358e766c9c4543,0xdb8dc0228401f010fb,0x426bc6f8607f3d26a7,0x5f35a534f0ded16e97,0x1f29ca7aea883ec752,0x5c2f08571c88d078c6,0xd131cebcdd07575536,0x19ca464406038ba5a,0x28a31cbfc42792356a,0x6834dd83c1cd1db4d5,0x2f8efe740bfb10083f,0x53bc5ad1d910dd10e3,0x80b4130a06466d3a1,0xfda1f51d8fcca1242e,0x4bacee05875422cff2],
[0x3dff865720b293d929,0x5b1c1e50f848e83b87,0xd9be76327e50f07826,0x4336788753c3e29afc,0x883cfc788d4ed1b611,0x617189b3ae96d9763d,0x184810e8a150b4dcbc,0x5f007a399e9b230c08,0x4f16841ada291192f2,0x113bf98e718b8d64f1,0x4c3b146f8437b15f04,0xa6133fc05a5ba952b7,0x3232b277ccbfe2231c,0xe8d3070fffa7357859,0x6d1188636f1b9bf8e7,0x9304cfa746724ee043,0x939fde74027d66df16,0xba9ab8831ec28bc0,0x9527fb05c37a85a9a6,0x56af02034bd412991d,0x639fcf0c4ca031a117,0xbe0e7e9c0ea73311c4,0xb4a35d5ad08444cc18,0x45e5c7702db67bf75a],
[0x4616c552c35a302826,0xef872710feaf91e090,0xf22dfd320f2a568e5e,0x70b6dfa43c33cc600,0xce4d8ffcf71107a371,0x1549c364aca6b01872,0x9408c8f04c8f05db95,0x70f24a9f1e143fd543,0xd83f98240589175fab,0x7b217ba73d2a20f820,0x72a2e3205d9c1cc78,0x33c4b17bd5398bca3,0x886c48303980ed614f,0x98434efaa2f9a97fdb,0xf95386e75ace228ee3,0x3c34a4d44d60b8f042,0xac216e3fe7657bae8b,0x75202c064578cee0b3,0xff66812e694d3022db,0xca11c23cc60c68a10f,0xd568a4e46c0dc24c8a,0x66551c09352ba4ac86,0x5624df4ef7b5a422a,0xe74110910fc9221a63],
[0x4d495edf1ff1e3710c,0xa63fb54a645cf7e346,0x276906fd51287b0854,0x26ef0446c3e3c4f7df,0x15d5c86305595e714b,0xa43ac2188977c55d58,0xdf9d55ce96d5125014,0xeb5a18231eedbd3147,0x34dfe349d49bc8d69a,0xd5155dddc18ecc83ff,0xd0db77cbe3edc04f65,0xe36f6176c4d9c797f2,0xa72cb6afcece915cce,0x4b2f0629c0e7a697de,0xa5ed512a8c87adb3a,0xaeeb6900bc32d5cddd,0xf9dfc36ba3354e836d,0xba56cd1faa6d15ae9b,0x3658231dc4cf6d0f88,0x457d71cbee34aace16,0xae2efb90ce4e9285a1,0xa6e7115713e969ac70,0xb6167d70ccf0eec1a8,0x595ea535f1b3f40563],
[0x154e320551c57d82f5,0x9f0afb66b760ea05d2,0x64961762d36fc19472,0x1924002e807bce921d,0x51002de505078b8139,0x1fb88d085517cc5aa6,0xe619a9bb6b7721abac,0xc83a840069c0470ca7,0xc7e65523e34c51a013,0x1bc52762a49a4f9fae,0xfd5c4379f69f09392c,0xbd1efe015f75fe7291,0xb6682a4ac4449ee850,0x9e74c0bba7a4c71b79,0xc15e9a13c2cff6fe8c,0x3e32d2193be961d118,0x561e8f21701f8e4ea6,0x3ca82c8948e78905b3,0xcacc27e5278792800e,0x88684623af7cd6138,0x6883ab8a7a1afb7aef,0xcc412901944672be09,0x54062986e822377fb7,0x7542581d4ea337017d],
[0x92fd85c912314358c1,0x5b52723aa2c03edf6d,0xc28ad1037519fbb2ca,0x85b11d067d75bb738e,0x11901b4e144bd25c49,0x81590aaa6c8cbc78c4,0xff989bda5707d6b6d,0x4a1a95fed522d31672,0x2c96f1a23815ec1e81,0xc6875a81c80889bfc8,0xbd4bbfd22ed35d77ac,0xd397b900f90f1e3a0a,0x3433a9f780f734b0da,0xe7c6fda67629b10578,0x3d2bda96702aef40fe,0x8d8ed9f523e48629d,0x74666ad43d966f171,0xbea0c54e2af28e99c0,0x51bc90a213de2cebd7,0xedf2e0894a38160407,0xc91bbcbd171b04cb02,0xb304337126ed36386b,0xf7f966a4086a0ee07a,0xcf4db083e29382b1d4],
[0x47d762fedf503d9d48,0xde4f2b7fcaf827d028,0x39d566e3d7d8249a70,0x8c9cda70c0964ed14a,0x798ab893bf212e7131,0xf4529c229bb66fbf0a,0x42f89e0af0721c890d,0xc24fad7aebd2664d13,0xe813173fa1a3b72d2e,0x178c7cbaf0ad6a104a,0x2e2b71ba9d86828c39,0x432bf17fb1ca8dea16,0xe1d989f643333dd172,0x175a86eaaab1fe699e,0x3587cfbd9809c5e277,0x603cdd4f769264e0ae,0xa9a05eccf8b607d3f2,0xfbc15e8442cdb65874,0xb3829030a1ea17f011,0x309244f94971caff8e,0xfbcb2ba81c57ffc08d,0xc1be921a0b081e2f54,0x3f63e90fe6cd949014,0x4105c582565100cbd3],
[0x30c399d91c29eb759e,0xba4196492d75ab16e6,0x94456d598e8e47d4ca,0x436fccfadbe182929e,0xa2dff50580a7193ddb,0xfc87a574b82e8cc78f,0x799089f4b5adf66f5c,0x5722c427d262f88f34,0xf249023eda58c04054,0x36e9c8926aca45a1e7,0xe6d11ff14f1c0f30a1,0x8a1b5d978defd8b4ed,0xf5f3539b35cdcdde8,0xa635c926f7560a5584,0xbaaeb7cf065031982,0x9d8b449b24f473e11f,0x9c489a5eb32f0eada6,0x3cfc10475c032e277a,0x5ec283ac63fc01514d,0x25419dd6ee65b64d0,0xabe2bbb4f812761fd3,0xbd6fc08062d980c91,0x4ea75bf966c2cb0118,0x61558e82be5d659f8b],
[0xc04fecffccc86a415c,0x4f884077b5c2158b6f,0x85fea4ccd997383d4a,0xca1ac3da6ea6d82d34,0xa6f95d0206ad935bd2,0x68743e04465e69dafa,0x742688d208d98132f,0x265e4a20835f4236e1,0xa995d7c6c999752ac6,0x20a50960d2cc4c4881,0x793376c6198f70417,0x460ad33385775d8a09,0xc6171eea6c89c3ef0a,0x9272666503f9a142f2,0x22f95f7f433f3a143b,0xa0c41370bc0f117b0b,0xaf4bb8f7dd3b34b61b,0xd56339096520e35cf6,0xb51b96ac1f70ad59bc,0xf514032ed284021f3b,0xc7d33b139f63f3a292,0x16f6c65dba595117b7,0x3a949f8d6e8dbfe9c7,0x6f2d2e1fdc9c3ed296],
[0xa7a34c95268a960a90,0xbaedd9ae5c3726150e,0x65e08e3011757c26a2,0x74bfa1fae05c5248a2,0xf2d09a76c31d7dff11,0xc2964cb668d60ec469,0x4eda09fd2c348bb449,0x7c17b5bd544704838f,0x2be6a91a2f6d0fe988,0x20965cf75c33170120,0x2526c9f9f6456f1930,0x9c9413b9fde8f485,0xeac4ceb75a830cb4c7,0x3500a076585407d064,0xada00e2f6e1d28d37a,0x53b0118b22c3a5edea,0x4f36dfa135c620eac,0x69d7705e7d6d5389fe,0x5411feaa4e1779001e,0xe3d44a726f56602fcf,0x5b8cb70cb7f7fd17cd,0x665d1906a761cbf641,0x83a14912d2207fcb95,0x85dfa9dcf883d493a9],
[0xd434389c3b3aee42d2,0x613419bf3a6df56843,0xcdff3418ac1fad7a51,0x4c59e1660551a8b517,0xa01cd56cbfaf32ab1d,0x1825812a4752effa2f,0xdcb63fdd72d9418bcb,0xcef3efdfdf3f38e4f0,0xe61f53430a6959910e,0xa4abca83c3667d1107,0xbc9f851ffbc170dad9,0xc636497e9ebbe07f49,0xf6a89a3ecfa742f71d,0x5d3285851a20249b98,0xf1fc096006945c27a,0x5cf9755537a6243969,0xceec6cacbde8447bf2,0x839b8c067d390012a6,0xdf21750458534e783f,0xbd177991e83826c5b7,0xeed19f4d4bc0652db7,0xe8b0ab886e2100bdb9,0xc17f61afe247f31c9c,0xf54d26cb7caba35d03],
[0x3919f86f6e8b15c123,0xd9042a8c4fda300fac,0x790bd74fbf17d9f201,0x7fdb13896777f2cd4e,0x3b2f01fd5b21c0cc78,0x5f908eaaeb29326d3e,0x45aaca642ea9f0ab58,0x2939ce6a0d09910b9d,0x3872efda713df7f162,0xbc800f7f48ac96b1c,0x985c8a4c442767577,0xb1b04bdb5b3ff892b4,0x81b6d49c59dccb4ba0,0x746898e83a75925033,0x59df63c240e25ef12e,0x5b30ed371c25b59a3e,0x6ce50d0c6ca2db61a0,0xb0c99a6ca0db8efe6f,0x160a613550259daa1e,0xdb5b3732c386568bc1,0x7ea49857d37b9d53f8,0xc45b5528084f0a3dd0,0x9da9274b4836923bdb,0xf15b4b138f17fd77ac]]

def tile24 : List (List Nat) :=
[[0xbb34f4db54b4543582,0xc62f81f6d0d7b9bc27,0x5a0c885e4c4e927ee1,0x92e9bd945f7278ee74,0xca0f8eacde03e2f7d,0xff54df0be865677d46,0xd2810a06320c8cb76a,0x190c052ac9394e3547,0x438fca8867ea6a5dd0,0x86ca99da47b77e006b,0xd11e89be907b3d617c,0xdcb869da809cbd4d78,0x25760b308051a56c05,0x2ac3b70e40f6e44730,0x4ed77157768ab3659c,0xb971c17484033897d1,0xb9a085c7f230b1cf86,0xc593b2373ac2595e40,0xac801007a00b2dd6c2,0xc388ce7b5d319799b5,0x22404618626ee78799,0x2a6aa20c9090eadd08,0xeca19e80c6c7d3a6e5,0xc1a474b51f8b5fcb47],
[0xefed0c80d8849c5491,0x5e1e5a1e3667b6f6cb,0xef9d8480aee24661c5,0xc2f2a19dff7c5da02c,0xeabfb4866993dee37d,0x71c1da5048b6aafe6d,0x117e1fb03233aa549f,0x2f51b0ba3700321981,0x4c1bead5ed83bf24fd,0xd750c320456afeca94,0x319bbbdbc7586b6b88,0x5af919c2ffb1b8acdf,0x22ff4faeab9a9c2f80,0x28a5b34540aebd6737,0xd08000b64aa6f61563,0x833afb8ad1b03f92f0,0xa9522cc79b973538d6,0x12cd53e86853903fef,0x60edcba73f4ec7e63e,0x3907b45fb19e7839fe,0xfff101de6ce4a02b29,0xdd6f84a29f541697a8,0x30fb49bdb36ede1118,0x12701861e87e6de7db],
[0x7405eac0c95cb3805a,0xe9ac3575eac1d19392,0xe47bc1e3306eb17e49,0x9a68bfb6d6af5c2c54,0x1435e12699b246ec6d,0xbd56b386b2be631893,0x9d0cb4d178013ed13a,0xf59c1c524bb7f89e93,0xe45a19246453da54fa,0x1c133b903e6d28a5a7,0x6a778112b357683e7d,0x47a34330acb1ccac62,0xb1e57665d259d30d8,0xc7e4bf2673e13e9432,0xd96c18661216d03a23,0x9e0dee6a052094b717,0xc7c36feb2a55871feb,0xc732a085a2b10c6ddb,0x59d7f973d7485decbc,0x154166e9e691d8c811,0x5c0c1ab39e56002e78,0x2cf86520902ec8ad16,0x5180628d582d4d37c1,0xab928c5bd2a02165e],
[0x18cc78a92c6664e452,0xbd67d38ded4a48da1,0x962bb80b7a208bc109,0xd046b2c9d6afde1bc,0x537cf862d4252549f5,0xe9a36e523b8fc4600,0x57eaf0ca4ca7c2fa1d,0x46d964770cc72c7a90,0xf2d04dc165d80a0dce,0x2cb5808a57c46adbd,0x8ce762c2d251c3d068,0xb2d3e82d5c2690bd75,0x3249423a03dfe82ab5,0x9a9a6127de61d8d867,0xce33986746d7077e6a,0xeefe678e3214a3b59d,0x2bdabee287dd2c4d62,0x5837430dd3fec82183,0x81876468d56944eb4e,0xc00055e66f1f9c4a27,0x6373e58d826bc52676,0x73bd1a7f8fb2aefd80,0x53404a8be43d4ee5d0,0x78a0c8ead440dadf78],
[0x66f6e88897b16fe070,0xa45843dff2696210d0,0xb66f5c6440475eec97,0xd902b43aa71829e63,0x2b4251f3ede6b02e15,0x9d282c6e3f05d6b88d,0x135cdb0511f22f2e55,0x85acd00ffa2f16ee22,0xed979e7c780e1f58d1,0x8a3b026f5dfd6924d4,0xaf866e1b44bbfb17ff,0x81d834e034dcc30ef9,0x10e517a93c29b98c1,0xb6bdddfe1ccb5570e9,0xef0bd8136efa4aa5b5,0xf60a0a0f380b11e8ba,0xba7d3fd5ed66692581,0xd3aa79ebb7adcdf8b6,0x60c77654ba5072b86e,0x5824037834c58e1219,0x1e735ab489f83d94a7,0xcd81911049a2aba28b,0x1af51fe50a0a4cc25d,0xd2dee03be228517ffa],
[0x157244be8254270e60,0xfde36c753366d31aba,0xa7a74d2555d598ec77,0x5ccb052931cdfadc72,0xf91319e3ee9ad30dbb,0x113320706a56dc9a7a,0xfe74934622786345ca,0xff742e41de6c1c9978,0x91dbddd363d92fcf94,0x8b73391edb19991ce6,0xd35389d55e1114d9c6,0x47e3cf4901e0001913,0x457c161e04606fd401,0xc0d90cda9b8bc9bf3b,0xac65b398288d4e0cfd,0x75116a6cb012bb0769,0x9f6cae0492ebe37b94,0x36c4dbee466b039e46,0xaae103ce117a9f1273,0xe181b9bfba4eadb38e,0xa26b8fea1efcdaed27,0x751a312c063106189e,0x28970db11d9c9e8aca,0x8740710e477a1aff92],
[0x85cf4adb00b4bfd6ff,0x168df520760f6f3778,0x2605728e76337ea3dd,0x8928d80c2c51c1c1eb,0x95ab0e50bc96cc1335,0xbe22e70678fc46abf4,0x6f136920b36b9a93f1,0xdcc9f7ea7ce972082e,0x2b65824dcf3c4c3561,0xd7677a0e0f7f521f81,0x1c3899448e8cc07b03,0xf6828fcf3269fe530b,0xff888d98f5328878bc,0xed5a73a1fb3d786f23,0x3f450c02f63b89914c,0xdc05059d3fa4c4426b,0x9700e92dd5009d0c51,0x5f5a0fa92dca90ea42,0xdf55fd00c282b9c770,0x5aca6bb3244c78bf11,0x6cd699b2916b8977c5,0x7431f172d8879750d6,0xb5a14158386c8df2fc,0x69e1a1d9fc5005c61a],
[0x63344ba3e90349f2da,0xe727291f7cdc605521,0x7a81f8585b77905790,0xc332bafdbf4138b752,0xf1e8a2329972c772d4,0xdcf79b72e8ee308f85,0x3a31ceda5e6ea368d0,0x1e4f3f8ccc19e088d,0xb2d25d43d6e0581658,0x5180ab127726e7b5,0x7a3461559bf4c2a4ad,0x5ee18e073eaa4d7f7b,0xde87821b69576beba,0xb332fda14ba9c01463,0x29cf720fd626d66cd2,0xf9111ce4e21b927c4e,0x893e662ecb13e121a7,0x7b4ed47b9a528e074c,0xb43141c9393e69e928,0x58ebd556096c35683c,0x7b873664585a32acb5,0x927d63c8ad3e0edbd9,0x14cd68f21ca0243125,0x6b2cbd1bfefdc35e0d],
[0xb438b1ec7773cabdf1,0x4540a2be8cc08b171e,0x4c28d4cedf1b27b367,0xcda3bf564757585bd3,0x2014c20d70828c1df7,0x6c10e2d7fa3e8ccce2,0xdb2ecd384fa07c4be3,0x34266aa89dbc98ebc4,0xdc9149f93535eeab27,0x7ccebf206458ebd5de,0xd139fba9269af5865,0xce3428da38f88c1875,0x300eb1128ae3affd60,0x4a09565fb83ccb7b7,0x5663c78cfca356931b,0x7d0e584031024c7863,0x9a252145a52883e0a0,0xfb6a927770400258b4,0xc2305d0273e8926925,0x8f77886787dcf1e37,0xb9e0a97733a0eda78a,0xd66d9d4d0daecc74ca,0x2ed5ce06ee5135c22d,0x4da25a01ff2c766150],
[0x66d3d2ad04cc909054,0x30e1b9afbc6cd81c61,0x2a628c011ad1bf697a,0x23efccf4f971537e13,0xc0e713962e5dd0dca7,0xa234405eb3e10dcb0a,0xdb785cf94107913098,0x143bdf7e5a04a52919,0xf1128ca21571ef739b,0x6b701b4206465d4c95,0x6dbbe5da54f5ecc0dc,0xff4cc0026fd1e72093,0x3c70f7be3f2be55896,0x89771eb2f07ab99641,0x4c94bf2b10e11dde65,0xdd681d8a8fbfb03a18,0xf4dc6b92edd04df615,0x5b719ecc20fd7d032b,0x98f42ad5cde35a3e05,0xf1a1916eec86c11d88,0x5a6445a518f82fab83,0x8fddd74ce383c95f6b,0x6b358b0bd26bb116fa,0x3fa37bbd4ce563f877],
[0x49fc93d4670bc00938,0x8abf1bfe5cfa2b2430,0x4024aca1a668126058,0xa59ecd54c722da0ba7,0xd8db9acf083a8f9d08,0x830865ea0ade78271c,0x56e32fe46e322ad394,0xd75c834d41bbb0bb9a,0x8c3d60167c68135be3,0x5d1ca0aff7b81ec97e,0x462f29969d823785f4,0x882548c545f1afce63,0x6c23df2c4c2b87641,0x77a5581e3cb989973,0x55a53af4de922b3bfe,0x99ea21bf5ee50157c9,0x8aa699d61c2f0639b1,0x128bd9d342d7877929,0x2703dad97c6c470b51,0x4e62e275833f6d1ed5,0xc04791805172639587,0x397d4652ffd655749f,0xb34df4e6ea0beb3ee6,0xd7bc52c9ec62dca598],
[0x366a5f8bd3fa03fe15,0x57f3568c04e651c64c,0x71e762b753fd7d9190,0xa6cf38f50223c17abc,0xd9cd9775de0b9859eb,0xc11909909271941b80,0xd8acd8162ba720a469,0x7c776fa8e2278caf13,0x3defc054004637ee68,0x9f2507bb787774303a,0xf29d1e6ebe1ce9de82,0xf06a440e6a1905a27d,0x15859f46b0569394ca,0x214d3bc7deaf907477,0xe3ae9c5ee6fb47bd71,0x7a3a04a2a40a2a160d,0xace617addde783b08,0xf0287f3402bb371855,0xeba765d97d7bc993a2,0xd79cabcd73ada9d633,0x10a0dbda9991de3ffb,0x42615df00967d99774,0xe51bb0952bd60ae198,0xf452c408331367b058],
[0x650bd691c57517a75,0xaa4d4c6fad259865b2,0x2fb8dff02c619df899,0xa4fca590cb9c9ad878,0x70a2be07ef37b17e63,0x6dc72cb6b530815e7b,0x68a21e3f8e14de3727,0x715151d67ba28cd5a2,0x8990d11c63236d1065,0x149cee21fd7d28841b,0xab775eebf7640ec048,0x11cbbb7ddefe8399c,0xe45b6ffaf73fe0c66e,0xba6630384aa1f6c6c2,0x6dfd72ca73bdda158,0x89fc054c66cf6d78a9,0x1b5031d60f84e276f0,0x46d712040262068475,0xe107aef4f2e16c634a,0xa947f074d1921c74de,0xc6176c0db54cd9ff0e,0xcb53c233d4b7b470f3,0x56dd7ed63448351a39,0xf213befaef6ef9c10a],
[0xfda288c3e6d9932f6,0x4797af4bc8fb684b5a,0x377b9df5014080bb47,0x3a0f3b4adc11b96098,0xa2e172b07eda0fa155,0xcdd54c4e7fd4d55ec5,0x7e80ca161e200494dc,0xf55300af13be1f197b,0xbfa1fe4239e8dc5493,0x52fa7e5fd70d98a875,0x9571b8f9c94547f84f,0x571a9bb036065369f4,0x628fad8dacef40d922,0x79655f404a3a1ac43,0xbc364a2056d0066bdb,0xb17c92a8b0334f3759,0x3285ef591517057b72,0x43f46af86346d2d7c1,0x94a98afe8591c4cb65,0x8d8668f2a7281bd9aa,0xf848eadcf1920edc2d,0x2027997144b59cce60,0x8469b21abafc7a456e,0x5096842df3758396e1],
[0xedc177a1be807c7e3c,0x68ef68efec3f951117,0x8db002163136d7cd5d,0xd90eea525cc6920386,0x1de2138f0c481f7864,0x72c565678ddff64d04,0xe9520ddb6f01812f,0x36bf458e4d911823c6,0xf7df866d935f410540,0xb5c90b1b9fa9b527eb,0xa844344cd2b06abc8a,0xbb12d81d660c72a89d,0x98d1afe8042b06e5ab,0xd29555e0a46177d82d,0x3cdb177933c1819e88,0x48293386fe14487ad1,0x39a53b34342a7d517a,0x89b74a5a85d8553884,0x2e60280dd5027770d7,0xb168cebca9fde01bbd,0x5616462398a407deb4,0x23aa9ee70014f0c10,0x46d57ece2f16fc345,0x127dafedb13b40e782],
[0xbf550bbbd18b0cc84a,0x9fa0614041d7581d9f,0xe9de2cf2209155392b,0xd5989faffdccde119a,0xd37089099b6d67a0fe,0xe09e2bc26875e30750,0x2a009d5a3270b438d5,0x6bd6a2873d767b978c,0xed4cb2161ac163032f,0xce30dd3acdc61fc079,0x621578eb51d5f4c3f2,0x41906d1b646e714ade,0x27a2eb2feadd17c2dd,0xf9d5dbfc81ca1f28c0,0xc63094595cacef6a04,0x2976553afee6658476,0x6f27efbb03fd96b26f,0x15beae27d15101aeef,0xf1d9f797de6bc54d56,0x99d02a71e2ba38641b,0x4742606ab4b07757ec,0xa0733cf5a354487357,0xab3f706713916b473f,0x6d1fa0d75e31e9cbf1]]

def tile25 : List (List Nat) :=
[[0x962bbc5629cf1e49b,0x80761d023ed60da340,0x4ee910c1606cdea30f,0x6fcc97281783d6f225,0x877ff4e67e95f3d200,0xd4ca8750ea2fba7b12,0xa3d87fedb6b90f5c01,0x9bd7c31fda50cfd6b4,0x8fcd08e975daf12000,0xc4f27d536c54e90eb9,0xf8d2c7886203e1447c,0x27114643822f2aaa59,0x2cf69fad913d0539e6,0x31f9ea89560aa50ba3,0xe7f54e03755b595bc0,0xe46901169e08ba07ad,0xc79134a38fd2644f0f,0xff4d1bb2b439320d08,0xc226d3b86351d14838,0x45390298bdc70028d1,0x8afab43b00bd489dc9,0x12d7048d64fe96938d,0x7c5bdc4bdabe5f9d30,0xb29326146978dec438],
[0x694af18b4a098c093d,0x9ec499d10702de88d0,0x69b004dc383c1628c5,0xb3d3292f8d406dd821,0xe56fe2a092e0eaedef,0xca80dbebe4057dd618,0xd44a365ed35eded8e0,0x24d0c3c0614710cf45,0xbde5d98d985ef8b872,0xe651c19e6365767b1d,0xf8feb4843a330cbd06,0x9bbe09a8eb8dff6dbd,0x3bdace963fa4189acd,0x1470322b9876b0805e,0x3bbf6f506b84388547,0x35722ea679416a0941,0xffa3b0bfcdd4075cc9,0x65319311fe5d841965,0x93a2f3d2c5a69c584c,0xbd59fcaa7ea8db853c,0x5dc3bd20d26962057d,0xd39f3c7ec3a7a522a6,0x172ce69fa0e34ec3ee,0xc922cc264f0776a074],
[0x81d81bba608a81be70,0xb8d7f159a906619e26,0x6321ba78b03e4fc1dd,0x38f501ffb8620d4caf,0xfaa5e5560e74169fc,0x8cace007c6119d9087,0xd205e7be85ca72683a,0x52e1909e403215f6cd,0x96eb69c16099ab728c,0x4f0646d5bdec1b5a01,0xa661178837376a34eb,0x795b553195c183a09,0x90c0a4018a464488aa,0xf1a3de0173799a6a85,0x2e007de300c3184064,0x9c0121ab05ff8ba551,0x847c71e5fd01565a9b,0xe65f154e28a8fe20e3,0x2ed67da75e17d87a62,0x1b7aed157d30ded5c6,0x7442d64488eea7d8bc,0x1a16fb9b283311b087,0x5b55de983ed426c5f8,0x971edc90420872df6e],
[0x9d653f36f6aade0c88,0x3086b3caa45052c952,0x91597fe159a748f131,0x820b614c69a7151724,0x2b4a68904e218925c6,0xfc79f3dda4a013463d,0x6210d86887b8eba07,0x56d74d942df6abe413,0x42217ed5e2d3bde76f,0xf3051fb6ddbc908aff,0x833dad85252a69eb40,0xc430bc4473d42adeea,0xe97eaa968efc59cacb,0x70dd6b1ae884a9704,0x3c3111b8c9e4dd9f67,0x947c356b6ab07d8daa,0xb81ca132e72ca12bf,0xfaf12c52ff2a203515,0x557de2bbd316e2d747,0xc470ec170841c1a17f,0xb4d2a6093539fd53fe,0xd812039dacb81f9445,0xf3fa948577439099b1,0x31b68d8d7de47bf6d3],
[0x66717de7cc8963a238,0x345fd54942e9aabcd1,0x3679a7cd89518d0b2,0xd6949397b034b1743b,0x1c70a58ca19f806a63,0x59db9905c6ab7b0982,0x93dd23001f3674c74b,0xca8b24310770e8fe29,0x108e10c880dc753b1e,0x69b43f97cdf9d3eb29,0x1c6daf40d541898e55,0x1c8f15b8f93a48b99e,0x534f971c0d491b3622,0xa99e22c446d1445b5d,0x98326a06ac92ea873a,0x174d0d5069dee33e27,0x4890134be13f237e5a,0x133722e30bffef4bf5,0x7a962954052c470dc7,0x9eaf081040622859ab,0x57cd6b5f645ab6d708,0x290bbba95841bf3c44,0x767af3281d50f2279a,0xc98993e7e80c2d5997],
[0x69e283c2f12565bf75,0x896750f66d47b76823,0xdfe89d0e2ccfe300d4,0x1c7705c0f918edbfde,0x2abef418f7ddb6c1ad,0x6ed21cb69e3e324985,0xf4604cb1dba2854d11,0x37f01f7ea55877d014,0xcc4a40759bb01d260e,0x1db96fd25a466e09cd,0x1079cc377ce3b9452f,0x2b30d76e8a54ba4bd3,0xb6ffacd501f32c602a,0xd49e89910a332099b8,0x173e9a0ad3fd7a170f,0x4f73c7e29249d18445,0xe51d1dad094cbc09d4,0x1a8dc348608f9ac7bd,0x3aff9d20c1a35e7dc8,0xb0a725a5562c0d807,0x1f0ae42d358a5d057a,0xfe0630e8fa636e5153,0xe691fd88672e9f96bd,0xac12bfc6e199dcadf4],
[0xb41a2dbd14b8a1d8f,0xc1562001c7e93314e2,0x158863525a1c1ec3a6,0x4c08ce27c4dc0920c2,0xd29bcdc73a6187929d,0xd74c49e34440be3346,0x5afe4fe6e346afdd43,0x18374f196fc039b0f3,0x91cf52f830727583e1,0x4e1b74faa0642dc14a,0xdbc47b1a7735ebcd76,0x8feee562676ca5ff3,0xb11530f87459d01e23,0xe01f320471da813f0a,0xa277e546c984b7b771,0x764ab0ef5e4b6a02c2,0x98d1f785c2d3c011e8,0x29f063c9856a9341b9,0xdb0b26d361eb16fab3,0xa05b8f4ef5368d7f9c,0xeaecdf81936a5aa256,0x8e3013e0133d8f7304,0x97c3ddf6e1aa133009,0x4c6bfa61837de341f4],
[0xe214308a5c18a101da,0xcfae23509d1f276112,0x67db491462b00ff3c2,0xf02fc732ef86bcc8d1,0x34c4cc4c429539f07,0x3b5d207938700584f1,0x9e4738f953c34d981,0x94b36e27b73568af3a,0x9ef7f0ff192c86027a,0x460bbef1265607487d,0x34c24603d9e2742869,0xe25d76f56ce938db50,0x602f8679aadc7dff57,0x3907c82057c1342ac1,0xf9423911009e13ecc,0xfa5a3baa490da1c603,0x67c231089a77be6cb2,0x5ae920b82e306a03ef,0x1e600bf36d77880034,0x9eae9d1d887811ed62,0x8531c6807f77df025,0x1b934903bf4e4b626d,0x7787d64657ad4a93aa,0x8d5ebc3d2cb5a9478d],
[0xd5c25330a8f1e20cc6,0x6b4276ad2ae6dc7846,0xede60bb74299175322,0x3f895fa967b6bfc84b,0x1a7c20cd6f213ae9cc,0x6104efcad4423cff7,0x1543508995e2b8a83,0xb4714ef86277b0900b,0xabb73f5f687d325fad,0xeb3a1c0001cc2d7841,0x61f7e8f1eb993f2d11,0xd10f5231a274c16ebe,0xb7a17ee20764465ef3,0x3a4539ecb63c227f52,0x277c90ce85ae2b249c,0xe4f5cf4cdaf9dfbda,0x61bd6d4c7609bd6e5c,0xe9cb02e039e169c4a9,0x1fda1c10cbc00ad0,0x4cfd0b4a7f02147ec1,0x6cdbb398c8ab6543f1,0x659788f016b3cbd49b,0x543245d96cd0e3a11b,0x2c38f868f9c6168c90],
[0x19e01d0bd980c0b609,0xa42009f6dbc824d17f,0xa097bd5f5c85fa4f35,0xb27edc7d81fe6f8ac,0x2f4c00d7d6e10ee7b8,0x2d7ff2a949376cf851,0x41b785ee04faf8d42b,0x96c7b9351a0aa2540,0x3048243324c877b4c3,0xc484889243edc37d5e,0xb785a3b5c6f4ea5bf2,0x43d85571f10cf0a201,0xf73e2db9d87c03a40e,0xcce3919540df3e4cc3,0x77e46e8f105ca03eba,0xc23f6de0b6d04dfb62,0x5f212636a93c894fa9,0xbd65ee57e2190418ab,0x3382832ce5e0a33f3b,0x3df4e8396622b897bb,0xd8a79479289ba5c1e,0x459c1dcf67ac3ad018,0xe080a950303b0d22fe,0x7ce21c4d786340af47],
[0x7d970aafa066e3e529,0x47620cf6466c3ca064,0xbaab5b9c2b96f13476,0x43533befd99b199f92,0x32b714ec3efff5aec4,0x45afa3f9605da36038,0x84535dda8006456aab,0x82fb36e207682f53c2,0x9e147a72bc6cd4f64c,0xe08d6db40637ffc289,0x92c39fbd59a59fb870,0xa7b07be406f3ee9d02,0xc3e5d2dfb0e84d13c7,0xa51e9cdc67856332e8,0xc6113476d3f1b9793c,0x66927e9189d20ca168,0xeb0e84f9d81a0b30e1,0x85cb8d809e02806c96,0xd8e7b769a9aa00d815,0x566f3e7b5d1f6d0216,0x29f5a05db8cb5c0b12,0xe754d89d4e5a57356d,0x7f4321f7b33fb3efa9,0x97ce18f66c20a6b777],
[0xe6dbfd38e8c6fb6cde,0x829ce5e234702e28cb,0xf7ee6d82d3b18e4e65,0x276af704cde197d170,0x5295491d9775e797ba,0x15207dba1450dc5712,0xe95f88b7214a8c3f85,0x60281e1ba5cad47faf,0xb66be45779c657edb7,0x1b6006e5810c1dcf4,0xd1d862c2d420dec57c,0x2a6269bd552ff0b046,0x72b6a23d5f3899895c,0x75f954a9bd7d81fdfa,0x6139dd206f938903b4,0x626ba6e1367e16af5,0xe8659b9402a1141753,0x4d804ccaa0118149e7,0x173aad91a4cf3640b,0xa5b7856f9adcdddc39,0x6f9e245cd12e04317c,0xe4a8b7811e3effbe1,0x916958193501ee9440,0xb9f818966f52a23b4c],
[0x693234b06afc58df6f,0x727a6cac89d5013e4a,0x5837f2c602eb3cbde1,0x67cba107d73ec6b8f0,0x5cb0e9abf4df0ed901,0xf338369a66ce1974a8,0x48c6d688fd64ab3f7f,0xa09a4014a89655937d,0x99f5d86476a8e65ae0,0x245bd5e9bc77d63a43,0x3df895add0bbcae24d,0x3a0dd78558fd0d7f3c,0x332a796523169319bf,0xa413ffa1975835427,0xffe98329376d00e80e,0xcb641430f83fc8ca00,0x9dd89ac37ce81567da,0x99c8b4b6315deb36bf,0x560369731fc35bc51c,0xe7944894b44a7ced42,0xdd6d107248d79dae6d,0xbd28ce2f74a0851d5,0xe5de7e06e9c6e2a581,0x79ba9cd0808683e8ba],
[0xa0978e5408496099a3,0xa3308692be5299012e,0x194aeecc99eb262a03,0xc036c76ce101543ba3,0x4966aae4ab7bc1b06a,0xe6f4c3865d1a2cefc1,0x9a81bc6c1b8a84053f,0xaf031045a09cb3d825,0x762f666b405932b5fa,0x6bb642147732f4cb01,0x9127b92f009898781a,0xf7cac2779df419a07b,0x67c9304f99158466d2,0xa05d33956605455e42,0x40eb06f73605ada80e,0x756f7fe6eacec26fd1,0xdd25ca680bcdf56ff8,0x8aff9a2aa67043b6d4,0x558948d70f047240da,0xdc86b8f6bd7bb46d5e,0x20a030b7c2670ea05d,0x1b0d4c137af167f3c2,0x547f1b29520e7c063e,0x8c084a3cd75a528357],
[0x2704b6a30e4e24c4b2,0xc5f1d55bdaf7d9d8ac,0x2bc131e032fd89d52c,0xea235193af2044cd1d,0x9162cc14b350602cad,0xd6b2873d85226f0d70,0x819b073b59a6e97bc3,0xf566b538287a47ae03,0x2711894add28928eb4,0x5f397676b154315222,0xab0dc68bbc53df2d6c,0x1ea80f7e4a9ef72699,0x3128ccb05a8bb7141,0xb512b84648ebd78adb,0x74ef6d5b6920df98b8,0x5bf49bfaf0b2ad1175,0xd34906015c80a28b87,0x3113301186584d7890,0x8cc03bb7b33a0b541,0xf56ef95c0585abcf54,0x47dabfb4fe480f42a6,0xed618a17dda8c683f2,0x5a87c0620e8b5bc734,0x8c1c52a4e1ff0ea930],
[0x33f69523f7bcb34e04,0x305210638311a4dbc8,0x73e6f3924217430a5,0x301aa78a947c3f79f4,0xe11bf06297a3be8c60,0xf87a1aeb708523a9d1,0xe8839f8bc83c8795ab,0x1103ae0427cddcd827,0xf321a6f694771e51fb,0x90e275a45c4ff52cb9,0xcb81f4593791e246ba,0xe9bd1ff75fb2962548,0x90c9bd370fa1733535,0x7bebc6efa2ebe4e,0x5f60b34686ab4aa402,0xeaa3ed1bf5161ef0ad,0x4c44a2d670c2d82ded,0x13a191fde3b208ef45,0x1a9f943ebff931e70e,0xaefc9155922ca8c45f,0x12f4fd88dd5e46fe4a,0x585250237ae1cf9f31,0x677f436a1ec4bc890d,0x2d7251269c1ecbd63e]]

def tile26 : List (List Nat) :=
[[0x987a3c6e8eab2c0cad,0xfcd8260508c95aeaaa,0xf34915f8561e80139,0xb46dabfc2be4964c5,0x377967e9846c76c7dc,0x77468711bbf868b101,0x6db6a1796f556cfd15,0x58ac9adf73fa62bc9a,0xa6e70b8c7fdd90dfef,0x1cfb255f228297f75c,0x464a0c33b1f1052bba,0x8627f5b3c2b328a18b,0x1dd62269892e3d11f1,0xa355dd4541413e966d,0x57b2b499cf3c96ca7c,0xfc1ff34f11099d9e2b,0xca2b285ad5cd49f49b,0x65377347de559a4ba6,0x91743b220f8031c6fd,0x92a1e71c55ab15a887,0x4e5ee8a49d3648d951,0xf1ad64e6e759a77073,0x17139e7e21226439e5,0xf081596868e0337d35],
[0x73ee85b18e63b366f8,0x51ba516c5ec12c8d90,0x9e1570e477292d6603,0x59c38b3e2d2015f6dc,0xefefd257d75d253697,0xaa790869f9460d7ecf,0x5c8977902c70111ba7,0x21607fa5b622a9b0d,0x92458f398cc8a07751,0xc56955eec9fdadcf65,0xbed960e8f4c516321b,0x545a24189c132d1496,0xef0771df0ce1590f88,0x199ad79d143fd0a1d1,0x603c848f54561d24a6,0x45da9496dd32e08617,0x31f09e786eeaa45e1e,0x790ef111ddf437eefb,0x1a4227cd07aa693e89,0x105dbeae58be38abd4,0x1fe2d0c59b4e0642b5,0xf480af5552c732cba8,0xed37f06e6df69f5e85,0xc2bd21b15adacaf56c],
[0xb1f3bedd497725a2d1,0xb76fd564b8282a6034,0x560f9b743db625784c,0x23b1386168dc42b413,0xde4bdc4e244ebab7f,0x28c046c343722360d,0xda65243d51bcfb4424,0x1375983d4101d8c6a5,0xbf227c1c7ccf54b509,0x60bfc8561c01a58044,0x2511d15d05b4037b8a,0xe51a3d766462a1bbd2,0x27e2f5e86ae147833,0xbd9c904bb77825157f,0x1c60d7314505c53656,0x1a4f7f07b4ab2b3f27,0xdc65369e6b7b53f1f1,0x72a88277d08af9281c,0x4dbab156a551acbb6b,0x15ed5e8f51fb079b4a,0xa2447b67e0993a6ff3,0x92a37e5f4ad906f408,0xe7a9c4d3407d6111f4,0x1034c2843a4fba5e14],
[0x50b517fa597ce377c4,0xdc18e3ecb9f21867d0,0xf54d79317550de2cf1,0xaff643f37358a8ec42,0x34195503dc2676aece,0x8bdf54b4441c79f2,0xd42a8e2c23fb83545d,0x22f10d9a1deff1e545,0x5b017b9cb5cbe1a2b4,0x8b1d5c7454d2225de3,0x252308ec2a5fe828cc,0x2a8e55dfcf53e59954,0xb5ed8ee054c99a3663,0xb09a23aedb47968de6,0x31772b295008f381df,0xe2d4fd54bd636fae59,0x8a522267c688447b81,0x4a0ef97869027baa72,0x70bb5a53548b3ef4b2,0x24cb2ef9c2c6f43bd4,0x1e26a0235dceb784cf,0x7e7786bc6c718df1a6,0x82e1c44232cec3aba2,0x22acf11c34ac9a6409],
[0xaecd3680d21e91be1c,0xccf58132df488341c3,0x78610dc3150356e7d8,0x85d87c94a65ce53a8a,0x26e98d80e9f985abea,0x6de26ca9abc40176ea,0xa82b4c05ae0a4cc333,0xb26fc5c35d0b1f801f,0x5d9b8ef9c5fc5ac11a,0x8ae8d893b4efcab7e4,0x70932794c4179e5608,0x33c556153e1383947,0xa3a9057c80dcf542a9,0x32c032a3eae09a7b9a,0xf7e946368fec1b7744,0x8ba35d3788f3c6ae66,0x5003eedfe8cf7f7891,0x9e817b3a016939ba3c,0x4eece23e6cedf0a4ea,0xe846ace343b5f71fe1,0x88603f1067a9f5a032,0x94e3225405a22188c5,0xd5fc8ddeb01e9fbedd,0x909183f703bc0ddc0d],
[0xe42d671dc767d78875,0xc44664e5fcccf5a6dc,0x148e78aac09fdd43f3,0x50dd0ed568347de871,0x8c443e638fdc5664b4,0xbca8dc948566499298,0x82a1ff90490640d55a,0x9511c8312aada03960,0x59508de92df2987e6b,0x942131d4ba6bd2d684,0xbdd498cdf52aed3776,0x4effc7ccc73b08bb89,0x969662954036791640,0xe4128ff015bf1387bc,0x1433464fcc98f5ae9c,0xd49e998b125c22ee4c,0xa38c3ae55cd9517cd0,0x60ddc97f89008e034e,0xdefd2dccc8218afc8e,0x23b86ff3ed0b15d221,0x375bd83dd4108288aa,0x7646569f8b1d97e5db,0xcad442e2a8caabbc4f,0x1fb91dd0711a8f0e56],
[0x20527362084803b8e9,0x1e9e590ba5007caebf,0xedc7d70b352dbfba7f,0x4881a5bc3d8a1af5aa,0x14e9c8394391f4e3fe,0x462d9f531fa2c15fd,0x11b5621b956a5d1e57,0x4a9902b2697f04e9a5,0xbce0ccbad77f8b3c1d,0x202ac73f6c21605c80,0x6d2486b32b8e761aa,0x4b16abe583e04dbe66,0xd5de9e119e626e7f3b,0xe6019dac132516d549,0x299cf5cea7229d5151,0xb6f00a23c5da96bdac,0xbc47d432c441688e0e,0x777de050d39e7bda22,0x6b89f083b3a5d80381,0xe614483eb13f9246e8,0x741c13087be91a65e2,0xcdac397f5f421ee505,0xf7d4a21ff7fb9b6b89,0x88902c62f73d8583cb],
[0xad8ce9a2969e8eee5f,0x47853f2f367e3713dd,0xaad273c503dd9f6ecd,0x264b4a876f7adece23,0xd33a0f67330958d45d,0xa6d1e616fb1f48d63d,0x26339a56d92baeba60,0x3d4baacff55d3570b3,0xc03cfbafd31d15daf0,0xcf2dc3ca2da528bf9a,0xb8ee5ee2163639f778,0x4fe7b95ce15ac5b1d9,0x806be2beb3b1d5746e,0x44107a52c47bb2413,0xb269bddbf9643a2de6,0xa552081dc9ab7dd07b,0x5617b34a9f4c309c0a,0xbae525f32818846d7a,0x7862e2fb94d5baba3f,0xd450a0b86af6c10fb6,0x43f395cdb3eb8530e0,0xcccd9c239e77e57cc0,0x772f47b91d89d7f8ee,0xc24124ed1c11ef3095],
[0xe7c1d00cc611e0e57,0x7fc6836936d95edce0,0x7ef48836d8cbdcdb43,0x24a16bfb2ef97cd30c,0x154b77937554dcbd24,0x1422d7ed8112a46120,0x4d30098702321e6471,0xd0c14f945f3d13a0b3,0xbcf9e2abd1fc8c29ab,0x8eeafcccc873c57418,0x844c72062302f6f45f,0x7c1914b7aad141ed03,0x17b7ded67f84700664,0x6e9de153b259e3dd86,0xe0fc0d121941483f33,0xd97c7124a772ec2523,0xbfa4c692ac95b8ec77,0x770d8dc2a158914d83,0x75aa1baea448512ded,0x452b5746a9fa875461,0x73bacfb2702f1d2f2a,0xee75be138a9d96850e,0x197cf3403e6dde0f96,0x7c8d0b1a73384b0c8f],
[0x949822bbe6046091ad,0xd34f38cf8934beb87d,0xff35ab9d8df24404a7,0x1da101303f6adcb3a5,0x4173d49cdb083e55e6,0xebb25687c8e91b93a4,0x72d96036effa63ee3f,0xc0ae606895f8632b89,0xcdcf5aa274e04d9ae4,0x4b8427349df3f7503e,0x48efde1637fc37d939,0xb3be78400ff6e2aa1c,0x5b029a1e91e50cec45,0xea06a323446165341c,0xf8ec179c38e34c5618,0xf90f8a018fff0bcfc6,0x6128363220f8753adb,0x97b5e62ca4a89644de,0x7f299723182a09adf2,0x316693f8180e45d8f4,0x24439c071a2dce8550,0x512f464bbae7827330,0xacc4d825eb9817cf26,0x279eb9b476aa7a5821],
[0x699243148466e93326,0xf9a1bd47ab687f9e5,0x5f2bfb036502331040,0x14e13ebcb071bd34d4,0xa2d060906356a4ec01,0x8c416314f8061ecc6,0x7e3cd9234e96a61f32,0x8c7708665726ab50b6,0xfc5afe8158dd273fd2,0x2d9cf44c9c1511b5d9,0x4cba682517da3b9ab4,0x99e601dcb151d1c359,0x27d4819821afa984e1,0x7091be37a578c11dea,0xc0f306cb80542c3de3,0xe3787df1d9b82e5166,0x1e5593e446236830d2,0xe24da31e550dd0fe58,0xe2860450f7fe1e1614,0x3670f978ba41c0c590,0xe0e166bd1036aea8c3,0x739192529a1c4959e2,0xa5195741ecaf9fcc91,0xc68e51e047670884e],
[0x9a4cab71f98975da45,0x97583be8c009b55ad7,0x2f693799e05a33129f,0xab37b79b957b2af497,0xa881bc8668c48771cb,0x68c0365e797cb6f3e6,0xb2c1a168a53d37fd26,0x399e7e3d2dcde831e8,0xed25ed6fd812d5a4e0,0xad1549f847f2616702,0x16cbe2a387d16cd149,0xd39e98e20770010071,0x5c9586953aa37f0b2a,0x3bbcfcb8c5128025b1,0xfa29d7496cf82191ab,0xa51dd4ebe1cad269b4,0xf967f0b5b32dc1dbd9,0x5adc553fd23959adeb,0x30b8d9de5b87990d5e,0x1080df5f524d3281f7,0xcc550ae073addcff1,0x2c050ae5c1391fc5f1,0x68996de6f944eac6b1,0x2151e8ca96c0ca5578],
[0xc548e09214c3e83da9,0xfb4d2d24369bd13be3,0x3b1ba6ef4f42892e55,0x59b4b3aa1cbf0c6591,0x20d0005f8ae7e0fc6c,0x4294d543c55461e5b1,0xf12c575ed5ad4d63d3,0xbd8e4ba8d0187956ef,0x5d48a99689df66b246,0x838c57b5feb6845fa3,0x815ace9865d61312ab,0xb2384aa2b2cfc279fc,0x977ca6301c2b5d92be,0x5324a2b771899211d,0xba28ec6007219054b4,0xfaf4fe7e789fa5c09c,0x1ec195c9290d0d2d9a,0xd03716a7157ed52656,0x45064e666097e9a7e1,0xda6fcc774efdaf45f4,0x1a5412bb9578ce3566,0x70d02e2073344f5ed0,0xf562ca4c573c7eb296,0xe69486fa8cfcec2209],
[0xaf1f7581ba4e72d992,0x80808fe5ef563940a7,0xd92703ed10bde7763e,0x666702d20ed6809b2e,0x6eac6360c11e8857fb,0xb97e6de79283e281a1,0x17a7364960513094a5,0x69141726de62379c47,0x9df1aeed5e710046b5,0x43c1a0976dbcd29252,0xf1c57a48ae8c64aa0f,0xc9ab3e036a2beaf225,0xec9d17b3a081f2b9d9,0xdd747aff110a5aebab,0x226a2d925fa66e5b3,0x45766dd25741d2af17,0xf05a5f98914a6895bd,0xa9e4d7c1e7d9670296,0x4a8f11ccf5384b9de,0xeeee23471d07a0b524,0x5b05f27d2ca834a4cf,0xf7efdf01e68e562661,0x45d5bd1a674074d0b7,0xb45cc19d6c9858f8fc],
[0x5c06207be675ab6534,0x259a84ecc6e726b93c,0x3ceb8f02bfcba4bf71,0x99d89721281eb87d89,0x29c09659547a2fc9d2,0xb2a6f268be3f060ba5,0x97025faa9b1d14da41,0x4d0eebcab16074422f,0xcb203cbd36b8b279ae,0xe02a62fe720eb53853,0x502afa063fb2fa178,0xf064a17c66d09cd4c3,0xa98792946dceb4179d,0xf397e08be4c70729de,0x841e73587f1356beaf,0x4c73c3c0ed2b64384d,0x605295bf4a61a15d2e,0x6467e7155dde180706,0x2280e73977ab5f8cf8,0xf9024116d3dc06d7e4,0x372df14ee3e35ea751,0xfd903ab4c8fa5c233b,0xd05f834741111e8db3,0xbe2e7ba629715f5cba],
[0xe51487f024dadbf213,0xf1e0ff6c21eb0a81b2,0x610cb82763eb52266f,0xeb192c75db966b715f,0x443e843c325a1fa4a5,0x4b21a7bc788533d3b9,0xfd96c46c5b5c86d3fc,0xbc936ced833ca0c00,0xa53da156398f6b41ce,0xfda5fcc3fda148acbc,0xba514a0da5bd201553,0x497d1873ab2257ec8e,0xb08d5553e2a24ced76,0x37a450a30f8bb62098,0xba0848ecd4add68e64,0xcf7c143cf868a43ecc,0xcad7270796e13ececd,0xdb0ef442b7bd166fe8,0x325fc83e5f890ee8ce,0x8b2f376bee412e1700,0x8765e95eaac7b50389,0x879747e6e3b950a22c,0x5037714fe9acbd1b73,0x9ac60398820c10b323]]

def tile27 : List (List Nat) :=
[[0x7216bebe159e2bffb9,0x466a81de2cb5fe34e1,0xbf43da67a6d4ece1f4,0x40724824e13fc8c7a5,0x31931a043b8313f3b2,0xf824b7cbd57919d416,0x2a9d5927fde7b02636,0x20118aa026c3e8542b,0xbcadf7f1831d48947c,0x7ada1e68acd7499bcb,0x611ffa187017db4338,0x497ef5090fc3510374,0xffb9b82b6db9b8bdb0,0xf260711121afd8ab5,0x4626f99250488356e0,0xd9a5512e40a7f1762e,0x6739fdacff2630652,0x3455a38c24850c3cc2,0x5263957e11ff949247,0x8889d142715748f0fb,0xb886fbfbb53eae2437,0x80ab98e317e21b2131,0xbacf2423c9bd0982d6,0xa09c0d4fe45adbf49d],
[0x8b4be94b305381077e,0xb173170f19b502d9a3,0x588f52f500ebf28c12,0x4d0b5b0f9fd9280844,0xc3ef4a4bc15d51ea67,0x5c7c5c0a5dca329acc,0xef7cc49fcd0bc7efcc,0xd1f893bcf8aecb859d,0x23d1f84276b19c950c,0xfd27346972a82df50f,0x17e51f3e010626026a,0x74d2cc20a993a0936e,0x6e60ec8f4f9b2474df,0xb000fd24fb9be40ce8,0x17900e314348390796,0x6ab908fa4fef91d88b,0xff55d8723c88237b2,0x35c3c3fd8fac2fc2ac,0x26ce14a9d98412f5e4,0x7c8a47946092bdc437,0x6ac37da68e5e5f8467,0x2524e6cbbf706d379,0xeac6cd60a513fe7182,0xd2086086d7933182f8],
[0x88b55f22890ce0b7aa,0x1f0862b2d25eaa740b,0xfdafcfc81f63fffb84,0x71eb9cabe57b35377c,0x3b765a578362e8a982,0x1dd5c0533ca1c90122,0xdf993b8a13fbb836e5,0xf2f49a04864d82ba29,0x49eeb78bf84cb77138,0xbf19b1ef6e6c375e00,0x77b33cdea08425f4e3,0xdfbc59b16c64be56c9,0x49a20403e5acfd36d7,0xae756bdd4d3c76f620,0xfe14a2452a9277f9b3,0x7573e633a82d16eb11,0x69ce408dd0ec491085,0x7448e9cd38d7ea8d46,0xfce49dacdc0ff8f6b3,0xc38691e633d7d45a4d,0x552fdf6fe4560eb248,0x2e25ac19c177d7af1b,0x58c59f77dbe1b57ab5,0xa0d3b006ba3cc72903],
[0xb2811bce4765d7ecb3,0xc42ea306fc9d988f04,0xf4b5cd26d9500a1e79,0xd98dfa1a51bce5dd52,0x8140709200d0a233f9,0x9a642c1ea1806415eb,0xc9c30d15effbf021e2,0x7f647f23ecca411ded,0xae6d8eefc0cd24d6b8,0x68cb8c444d0e399fdc,0xfecf8403c16f2e6ca,0xf01ca2e97a19fc5a22,0xc827fdb7c7972d8946,0x3638f1106a67b22728,0x2af616878904830ec8,0x723c04b6d51313d8fb,0x6593b52b81dec10187,0x55eff57f78807c1899,0x9b94a00793f0386352,0x5ddd2752570c93ad2d,0x4bd5bc894797701819,0xa42cc1c2570de509ec,0xdd89f28e19ffb84a85,0x422cd242a3b3707dbe],
[0x7325ed79b13adbf847,0x9e0776968c4a7026d1,0x52ef057a1d946530fc,0x5b2d75a52f28eb0e1a,0x9bc908bdfd17aa45ca,0xd4ba84c82514597334,0xb1c01c5a89a32850d,0x74d507bd880ef54561,0x4fd2843cdb88659baf,0x465d6c23abe5807d42,0x61e3f8bd7f641d0ffc,0xee7c3fc9876ff9147e,0x30da6f0939cbac86e5,0xcad26df9dfae8aa0f5,0x8e2afd697c25119941,0xbd60a3eafd4d476b84,0xcd6353dcaeaccdb9bb,0x69445fec5ab28926a9,0x4e600385abc46ce6ab,0xcd10378c4940799450,0xcbe18f96480baa00fd,0xb69c46306baa1c6f8e,0xd870a56703cc8da775,0xe261d937eef5bfe281],
[0xecc00ec06984091b12,0x32d782c77799a5ecb6,0xe25c90cfe8b76b6cb,0x5210231600fbca2ec8,0x423fa93d429a46b938,0x5f5bd068b3e801494d,0x44f9689664303f1d5c,0x5c94380c8205537e64,0x95a7411168dfaa3d2d,0x9c5c0cb6a8009150b2,0x2dd96b24cdf06b5bf0,0xfb2373dd804cf95ba0,0x9a204d88013e957275,0x29df1be84c0554f167,0x69ccf7621716f49202,0x6fe23d2e2e43b697ac,0x978c96ce72e4ab2c9a,0xaf8944f9c785deb06b,0x30e20787bbd6f737d3,0x753ecaf9212814675e,0x891befb575bb07c3a1,0xd00f6a519ab51dfe90,0x89ce5fc0ba70dfad13,0x1d0dcc60c8ad9c1601],
[0x6839feb8768cb866f2,0x8824d7c757e8119717,0xcf7459ffb3d0cdbc25,0xadf2049a77947c03ea,0x3a4fce78796ef920d3,0x82b31365e3dd0c6049,0x6f9e279337879bd415,0xbf8064f5c25cf52def,0x28887e91cb7312b9d5,0x9d7c0acb2e7b37a0d1,0xca9d287f83184dc814,0xe5e3dc1c89fc58dba9,0x4486d65066670dbea,0x96fded3a10e3d1f38a,0x85529b56570737d3f1,0x5bc65fcca31bca9cfb,0x96ae7c0eae63400d29,0xae36e2d4c77cddb403,0xc65b4756d87631692a,0xb230a165f7511f40fc,0x6b23c8671e93739f90,0x35748533b6828ceb9d,0x247af923860a006f77,0xedeb99dc4e37565be],
[0x7f64880ec581ac2b3e,0x3556946179252a845c,0x3fed1630bb9c55924d,0x4c3f8ada221ebab3ee,0x3c95c11b2bf7dcf723,0x352f21552c14b73be3,0x6596c0eaea130d95a5,0x7fd41f6754c76bf2ee,0x199ace1048b9456cc3,0xddc29efc527ad3ff5b,0x5e03bc859e9a94b066,0xaf25045eede3680ae6,0x26b00ca62f052ff1c7,0x96ddfdefccf629abc3,0xb5acf4cb7427334962,0xc7f4fe72c97b78059,0xe48a006e6c492cf24b,0xb7cc032dd92c68c866,0x6c21dd45b8476a7965,0x78a23e5fb9fcf63ac8,0x9c8ada2922541190e,0x13f2aadbef7597c7f3,0x6b780b58fd70fa879a,0xf08ebe55ace581b838],
[0xb7254ddc9708bfc239,0xb6b6bf21fdc334f96e,0xaffe8d77e3718087db,0x6c171c293f58c4348d,0x6fe0a80d33c3ebc704,0x13eb6d07e2e4dba583,0x20eaebfc9d6f614f47,0x212b42f8b0e153a688,0x471b7a0fa486493c74,0x5d883a6841be034dc,0x9caee9969c921aa43b,0x1650d946e2e12e7d03,0x9a8f7bef61fcc2d118,0xe6ddd300297cb38fca,0x4c205a9c80f93604c8,0xbb54fabc376241d62a,0xc9469ebefdaacf04fa,0xf35eb5a28bbafffd90,0x46fdac7df27941e23b,0x4c437d6d8cb2528b74,0x3793347ac2db31a126,0x624961fd06998a25a7,0x9718ef65e9c942d34b,0xc5285879d1a39b98d5],
[0x6b5a8bc8217aa0f7c3,0x2c53859ec9cd6c8077,0x9b804e363a065720ae,0x47bbccbbd55c87e15b,0x2d0db667a926ec1ed0,0x97d2994c74e097a574,0xe54d32b0608252de2d,0x74ca800be3a8f467cc,0xde13ba5dada16d559,0xa8ecdd33a58d83ddd9,0xe0d9c792f4e9891fc0,0x36bfaba2be34ec5d6f,0x4e372bb2b19f5e2742,0xfa50307fd5a6f78eb9,0x78460c9ab84840479a,0x813f44a76d6a28d46e,0xf15f2188e84707e176,0x128eb262bfa8692203,0x2eb8f97f63c13a35e9,0x9e29ce1ed77b19b72d,0xbaf4a2ac1d295c0ef5,0xbfd318e03e925b9a1e,0x64d18c4525b021e8d7,0xdd43db150cc99e0709],
[0xa3e7220b05d9a68efe,0xf72c5a0483bf7a65a1,0x5b5612dd9a2a845f38,0xb7d1179ad83fa3b27c,0x98b2a71a85d9a2bf65,0x9cfa08018d7d2982a9,0x47f03e5e944fc8c8d3,0x3595ad160233c49acc,0x3583226bf08e088a37,0x21ddb401270f7856a7,0x3cb7b1a4b96f25136a,0x457d9f21c7f71c4279,0x5dbbf8a7c5b754b260,0xc7ce98de0ad731bd28,0xa6e98e3a579246a5f0,0xd90769dbf2ef9c05f,0x8bc47a6fde83c40535,0xaced17a4b91c090d11,0x56afa3466fad998f05,0x8e91bee96edbecd2e2,0x3f5f9fdb08b65eb5cf,0xc7a0c5055e497bbc6b,0x519564e8fe2277e641,0x459eda83c778c5af68],
[0xd50229dd40feb9d5f,0xd3c67715374c0af2db,0x48eec3f949f52249e,0x296fae4fd318241f02,0x2913a31526c6364307,0x29b4c2a1c1020919fa,0xeaa224f91146ef0f3,0x7d7f5faf3b55312bd0,0xfc3ec8f02a0b07c8ec,0xa5680587114e6a5338,0x5aa65a6e9c6e11a89,0xc996443d04932e4715,0x90f304a8fd670d45f,0xe7bfa4d615029e866,0x2ab893d9496203e90e,0x548594ac4b0dd0032c,0xa8ea8379152125da67,0x8c1004ab4b22f48097,0xcc4e1e9b1d2c7501e7,0x1b5c04dc365537f897,0x56c3e63f24c6d25667,0xeb5474c3a3f25402f3,0x808dd18ec2b287a786,0xdd02a078a2edc31bb8],
[0xeb2f92bcf770f103b0,0x1fd97a61c9e58638fb,0x2d4a7270f9a6bc91e6,0xe8b1e3313e47623856,0xfd1d7dc64bd6767eab,0x6332772d970bcbe4a6,0x2973e6bd61ab01c871,0xd11dd7c9ad22f8da34,0x6e7abd22c3efb2025f,0xc2c1c9546186efce9f,0x7e9827bd31a60b7b4b,0x23121b1bf5e05fc941,0x55fda6706de95e1261,0x3ff28871ff01f6bbd1,0x71173ca86bb8632c2b,0x7da2413df0a1de29ac,0x5c34879024151bc5ac,0x5f1a9fd4c1797d3d9d,0xe8c2fca12759535821,0x66595d3328f188c07b,0x6060d133e91bd19323,0xff3bd3d164b20cd861,0x9306452c46f94e35d4,0xd1b78c62cd380c3070],
[0xa685f2fa3625d5efa4,0x638639fa40058e3d2c,0xc1c59eeb1af79163d8,0x4f3f97890437304b97,0xd337199b6b26fe6c2e,0x45cd45e83094c8c323,0x260a5397e9372e0d3c,0x5dc829919d4c7748bf,0x6e423bd9129326a70f,0x2ed50ea6c00dc366db,0x4596023a635e3811e5,0xf254c76dd0352be227,0x94343da56e8214b174,0xc33f96f60c85d35d7c,0xf8de8945e7425e1b80,0xee6a091e436fb13b9a,0x535d098ddf08d8f1d6,0x7a406ccb658ea068c8,0x9117218c36aa0e9ae7,0xe1a9c41aea8490c369,0x18edfe872272e011e5,0x42c37c1a51743245b8,0x82c48c2bcc1793f107,0xeb41cb859e640e158b],
[0x1287507492693344b7,0x76c4734293d6ac765,0x4d26548d5b0bac6002,0xed77e47f3a497c7877,0x260d8dbaa25e10127b,0xaf66c10087e9d8fa77,0x36e80bd21b4a45afeb,0x7c7c09d5484345f0e0,0x8c814f07629cbf2ea9,0xa0e7cd556e320b0cd3,0x74111a8d93cacbdc7e,0xd6ecc7bf2aede35130,0x694442074d2a5db86a,0xb3a435497c15ba7b3c,0x2b08498d2e4b0c26c5,0x9493a78b9d4b82db96,0x311d5d0297e68e47fc,0x74e059e12cf792c795,0x5367df805d69eb50ff,0x5a90c05a7ba0de33f0,0x8164cbb6323e476fd3,0x9b84c2a46644946b88,0x4498b03855985246ae,0x54aba5eb1d08b0f23c],
[0x2a96b0ee4601ccfd95,0xdd08ebd88ff56e106f,0x752ad44c5f370b38dd,0xa436e5c318a2e07873,0x39ec26c1b0fc183d75,0x33c36c1911d66d72a9,0xcaa82aeddc9cf2f810,0x7f1825da79dd1c09b4,0x5f7b90b78134b91ded,0x64235ac6eab433c382,0x6023b5264cd5e1256e,0xdbd0d317df819e7de2,0xadc82b1b8a5296f322,0x1bff2f1723109c9779,0x9f8176ecdc78ab595,0xba3121240c84eac539,0xc393b78a0a741a894f,0xa2504a7d4b89b33d1b,0xfce6c36edaaa95b8be,0x8a9faee82d929b36d0,0x6e4d299d6416e776ba,0xc2f23e5b45b6dfd363,0x9d863cfbe09e4eb208,0x86e1f20bc45f751b96]]

def tile28 : List (List Nat) :=
[[0xd184777578739307e,0x86d911b8596a382ae,0x3fff5a701f5d8086bf,0x691852a853342aeca4,0x9b8aa7876a1873429c,0x207f9fcd293bbf789f,0xc39b8438266ebce6d5,0xd14144f4be163f3c1,0xf44587430dadfa08d9,0x6019f995d8e68e1d2b,0x46001c082a868b0df5,0x4ec1a91548874a09ec,0xf44b536a0220b93e22,0x4d48606c8acd0e4056,0xb8346f7b1a0934c330,0x873bf370a77a8335dd,0x2e83b07e9a16031e20,0xa83c197eb7380211f6,0x807c2d4b62bbb383c9,0xb45411bdc804181000,0xdcdb7ffbb2b5406ea2,0x11ff11f98c449b2c3a,0xac14d406f4d413a868,0x68f2715f77d74bfafa],
[0x9ca2a8f6dd8a4069e7,0x9d56cb84daf65073f7,0x91abb3c47555065bb2,0xc13183008455af8df1,0x6c66b8edf3b024019f,0x8d20e8bcf0fe177d36,0xe233e914c6029782d8,0xc1249738e4c252c094,0x3677d2bd7e8e762958,0xd341adcc223d58d3b8,0x7f0a9f9e8cad48692f,0xc9e2a3efddfddc0d22,0xa9e2c87e1f4a5930c5,0x100283b57c63345ad1,0x1262f3bd4925fd1c9b,0x4abeaee5349ecf3901,0x3a4c4b0225a824b029,0xfee1832febc4caac15,0x6cec2f290831c0e6ab,0x852588b28d1614466e,0xab2b090f8034c5030b,0xd63222e3f739842285,0x8612f6eb6bfb8f2fcb,0xf46abeba65394d9e01],
[0x54bae7149fbe6a3ed6,0x418931226199e13e7c,0x9c2bc229425681836d,0x94f5710d0f1eb171fc,0xcf0278dddc244ef963,0x325cadd5d237530d57,0xe3c43afe7d9ad1c2b6,0xb840ca0aec4d2fef8,0x260c7fa12b62d55e39,0x59f79e857048ebcc77,0x3dbfc0fcd9ece38d31,0xbf4ebf107004458d53,0x128bcca8670c02f07,0x68b445d8255a04de68,0x37314bbd0827da6d76,0x8c6d2c1767df67991b,0xc6145c5b2d8919802d,0xa4dc344dce630ea2c,0x3df7ccdaf3f3711962,0xfbf7612bddded6f6f2,0xe439d7906e41a04711,0x5923abd7267c882404,0xed4de686198f21bb71,0xab003c13c397d4af6],
[0x35ad15434da20efc09,0xccc800643c44495ccf,0xc365befb3f5fe53a77,0x65eb9f186f3bc396c8,0x8a83f9a4992ee8cb70,0x3cf26e7dbc66accf0c,0xa3b06f1ae4c6261b57,0x707e8816d79114d73c,0x17a000c07df2cd46f4,0xab8a88dd27f5b82352,0xb1ac1322c06665463e,0x7c0f0b0ee1dd77136b,0x8aa1369c0ce61434a3,0x9768f02d8ca5e22c1f,0xd2cb6d2bb330aa81e8,0xd290d20365817c5b0e,0x2d2a4964a037cd6d75,0x837f91683521d022ec,0x241d00193f9ddf89da,0xe3819e39c7944d09c4,0xdf6fddcb4cdd98c66c,0x6e33622d0141849229,0x8ba03e42a62289a71f,0x34987959d257704b53],
[0xf15ca140eedeb7aed,0xef29f88e4aa20828d7,0xc650e194c78d77224f,0x8b26fb0838f492d3aa,0x268afbb9db630e5312,0x73ca52427fbfdff80,0x66f1baef733ca12e42,0xae1ab0a72c5aabc263,0x99c0968b37f0a436aa,0xafdb373c9595c1cdf3,0x627859ba2255c40560,0x7006bdd88d4fef4fd9,0xbee8ff91806d5ec6d5,0xca648888777ceca955,0x1ecd22086aef819b3d,0x8fb7a613ae17b75af,0x86ac9bfb1b7779b39e,0x96a1b0b7fb2ee83612,0x8fffdc9b8b22d8f6d7,0xd3f59c00e346ce9dd8,0x1340401c0f118cc8b,0x85656eb0d1a5ad242a,0xe67e31c9d26d83100b,0x464f8200cba0f25a9a],
[0x478c6689785884e161,0x849582817f1252d2de,0x8860ddb91e5b15c9b,0xd24c26db38fb54873e,0xd0ce22119d3edddb00,0x2490e96e2159536096,0xf42dc256527c7648d7,0x86b267d328e419f2a4,0xa52d6ac9c7d4c6aea5,0xcd6839b791f3b0bfba,0xd3b5c7e974ba8637de,0x676f8de7d56853848c,0xa616f33b0c45cb3d96,0x3b629af1ada69bd3,0xa6659d2b2bbe6ab215,0xa1ecc39b295930b72b,0xfda69ee50aa2732b4e,0x33e33803fb75d45a43,0x7d8be141ded0e980f6,0xab3b9fd3c01e2ada34,0xc609e48ecaea936b96,0x19e435bdc50aa33f0,0x37a4422e4ee0f57796,0x97c248c4e1c5ed6d9c],
[0xfe4fc225167fc7fafd,0x79a6402de05630ff6a,0x19641e03b9313e2c90,0x101191551600a6345d,0x5cce94302d87eab8eb,0x682c59abbedb88845a,0xb230eba93fbdac3d64,0x4eded024325f7299a0,0xb63bf32e88aeeb4018,0x21ee2216047e7de2df,0xa64cc7bccd8d082ceb,0xa37894416f49098cf8,0xcfc2bc19561a4a247e,0x995f6909d6118af3a,0x11228a7e0f9b00716e,0xc573ba9f2a8f2ee031,0x1ee3764aecdcea6511,0x511b61a32e189a4ce0,0xc644049e7986e281e0,0xb95a854d795638f43d,0xbd050d6a9bdf79c9cc,0x471699d626b308ab88,0xd80c356e1ca968c764,0x8becb9c5c348e11325],
[0x7486ca054b84a2c50f,0x5eba930162c6abd8fc,0xc05a85ea3c9abe4042,0x1118e486060e4506de,0xaa49da186bffa40ac1,0x56c9579cb7d45f46de,0x27939a69e4ddc01fd3,0x6057aed1bc9eb424c0,0xf7281b0ba870bd084c,0xb37c252ed088eb2753,0x91e13626a58a0b7e2,0xc539ddfbf6c50aec89,0x808108d0f5e4bc494,0x9b4d1197e5cfb0e46f,0x58f998651e64f8b197,0x107f2ffde0fca76891,0xb6c8198d72dff983b5,0xaba61630beef8d2a3c,0x63216114256871ea18,0xcab7b5040a5150f27c,0x597cb8130954a051a4,0xe60a1223a0aa3fab71,0x4636217b69b5936cbf,0x7c8907c8f6b2ac5e8b],
[0x957215340f595b6f2c,0xc27186feec71ea1485,0x2af2c29a92e4669abe,0x2e3fcbebd867f15dae,0x220a26148ae68b8cd0,0xe8a51c8659ddf4936e,0xe30a99b4e789420fcd,0xa5f30588e77384aa1d,0x53b032d55513fcb07d,0x3e42b8b369dc0002b6,0xd065425987e12f4e93,0xfd57484ecb883acfa4,0xf7b5e24f851a8c8b6f,0x260fe444f02f5428b3,0xd22691bc85265e1022,0xac89227a23deeccc26,0xeb88a6788f2cadf6cc,0xd8dc67a8b4e471d504,0xf8e67aaf6131713f0d,0xf14b4c4e5fd51b9bc9,0xf8f3315f5359df5ef3,0x8df45185a09c5098fc,0x10a57b4bb61d021c11,0x9a9b4fde9f59e03162],
[0xa642a3484329ff2897,0x8b01c457cf3232d6a1,0x78c160da7d43730de4,0x3857f6f357f22ad773,0x9d207aa461c5591323,0xeb112190e46bcb6d18,0x8cb1de318f0bf07a14,0x1a7a9d430d62dd0b52,0x129acb8d925de716ae,0x8769b69618f797d6ca,0x45b3fd1dc76d6bc19d,0x5128cb8207f4ece48c,0xb41b89ba181e300af5,0x48cdb8527e3a232707,0xf01a6f0b7f733b6f21,0x60deb0eb2751e0b67a,0xd3b6562f4a28ad6e94,0xb5c2dd74cf4aae1334,0x624fa442a17c5ae292,0x943c282effbd34138,0x9ba53942e210ad6db1,0xa42fdcfb55529f7dea,0x7ec9ff76a26cc5b19a,0x8cd0363a1c15fa941b],
[0xeb32d51984c0d63698,0x91fa4d47b485f2ee81,0xd2fe94db74fa3fe523,0xd01757e712b241636c,0x6d15092e1d65c0b892,0x28e06af634c3db9a8,0xd73b9c2836fb2ccb45,0x60d6ce9447f8cbadfd,0x2bd867121d945558a4,0xb176cdb6b1edb1a10d,0xf13abdd335271c7b70,0x5ab93a524836b170b7,0xc37c75ad41fdc5b8aa,0xc5be06a5db5466ca9f,0xc175c4c6ce0f812f47,0x7cbfc793904eb99212,0x2f24ae468c9163a29a,0x920ebd8530b0f25f65,0x638d141e0b03a8b414,0x1f0cbb582f40e42d36,0x72eb3cbcf0b17d45f9,0xca9b4fbcd618c6858f,0x8c995c17fc19bccead,0xc200f0b4ea15f0e494],
[0xf8b880ea21b328aae1,0xb78051db3b0ac4859d,0xd4bdfe2628cdccf1c4,0x4e8e5fcdb507b312ba,0x83348278a93d6ef407,0x8b900bc5f82635bdde,0x1b8c7a30f3b7a13ad6,0x36e5d8a027277db36,0x195eb1717715b09751,0xe874cae121ffd694b,0x1b4456d02d037abf80,0xc21db3896153281f52,0x6b79396adf08476cae,0x912effd6d0387523a4,0x5f5d0e27eeb9a7962,0xd0c3e90455cd1542a0,0x13ce7c5547cd95008,0x2ad12bc68f6a8d5828,0xc0f1fa8138154502b1,0xb4513573c3dcf81694,0xf2ea62a87bda716d67,0x2f5959a57d6cd492a8,0xdeb10549b5fe1780c9,0xa4231cf8f0a6b06792],
[0x1aa884afae698a775b,0xa7d9e440904db88f4e,0xcb4db16a23e4ac0801,0x4b3767ed4f3a888b5c,0x3fd44c31b46c6ac72a,0x59bbbda281e165b735,0x3c832b1bdbedc67861,0x24c0899cca80c8c107,0xf3f36de35eee82cc17,0x418165532e9445785,0x56080c384ae005f22e,0x7bade93f7f6d02420f,0x1f80ef449c1bcf4de9,0x8de73316b6f7c7f79a,0x8af481a83006c8beb,0x4d8d2f16ec9d4b72aa,0x963d89cd5ee1ef34be,0xda59fc176ea4368ec7,0xf99b196b28ee85a81a,0x7f75ad8d3fea1b4705,0xa5409044344d396efa,0x428023efc076330079,0x81ede40655f36967ab,0x18ea313bd404fc91ec],
[0x9cbd1b969082a23548,0xeec6754fa91fd0c55a,0xef438d00f160662d5b,0xbef304749e5a3e6ecd,0x4a06f7802f1ab58b74,0xed9779f6574c1b94f3,0xf53a7aa494c40495ed,0xb6e9f7b6a7f9f15a23,0xee55d6043502a7523d,0x7e616fa89e36301013,0x771caa81e4f179c2c6,0x7c031d0c220e29ffe2,0xa7b424d8285a7a9105,0x53e838e91f90a2eeb6,0xd292601f99dfb0fb21,0x8021721021425cf219,0x68a45ee267334040a7,0xfc82f4f754af03d233,0x54e6e852e49dc86b7,0x3beb5dfcf2465e67fe,0xd5764556c2e88ad235,0xfc0c5ecf0e046b564e,0xa3a9cd1fafbc1e4bcd,0x722ad6399f8ec9c6fb],
[0xe5d895fbfc456d2b62,0x3928d3bee1af376777,0x6f61cbfbee23012369,0x269c9af9287c5c624c,0x8e9ad11471a629394c,0x2ac4e43894d59a6526,0xa147ec042f387bb5fe,0x4493b0fa9e846d8dad,0x473376b3a29a41b7c1,0x8cfcb8f1cb09529ac4,0x5e2caa53553657b293,0xac0fd185f6c0150bbd,0xd1fede4719fc58e0c0,0x5d6db510c5fcb82675,0xa25b192b6a1dfed9bc,0xa9c16bfee28297f253,0x41806d427e96523bc7,0x31372144d3d2814bc5,0x34cf0129ab211a476b,0x2286d7ed23c95eee37,0x3bdf2fc7371a04435,0x43b86ecd42345f8555,0x793072e13c8723482d,0x970d173fb87921822a],
[0x2696a6c7f1745d2b39,0xe36f92851fc1b3eaf7,0xe0a869aa8ce4c5d245,0x1e4f60f89228e01fd7,0x437f0767a74937256e,0x7d7574de8538847fa5,0x698ee09309a335d90c,0x727761103a8ea78652,0xbbf4c3e2705eeca7bb,0xf28833abdb847e5a78,0xa46c334186a344a407,0xec476afbe6c356a7f1,0x2308794eb142480549,0x860fcd198a04ee07a4,0xeb37c15c89c1c4ffa,0xda07aeb3489cff28a1,0x54ab4ac1e594d54ef6,0x4c2fb7d4d23671cc39,0xe610c133afe58dd0ed,0x1325cc40bd352a3807,0x8e73bb625b75d67673,0xa491689513b54f9ea7,0xe2698bb188b330d433,0xb91c4dea241b9676ff]]

def tile29 : List (List Nat) :=
[[0x49b89966d7b33dd838,0xb31425008bf7522110,0xca97f9998c3c2e32a5,0xc0d4a3a3f8afd3b99f,0x419207f30a035ed95a,0xe13301701c16bff94c,0x6ab6d238ad8e1a628a,0x819e4cd8798893e257,0x2d7f66513d79d55dd6,0x899a55fa17dcb223bf,0xa205495ad39bbe6891,0xc49ac61400fa219ef8,0x1257191541c7d64d0c,0x71e05af1acc39883d1,0x3b9b9c0d165e23eeca,0xd6ae5d3d01e32843f8,0x5f32e49b01ca287666,0xb31fc62a5db8715f66,0x4d67237ef033623452,0x78b7ccfae3649b28c6,0x8b6601da50dde44bdf,0xe0ff4bd5a91a754ae5,0x48ec1f3227342b007c,0xb1d719756d2202fea3],
[0x50c2f7fad3ec2f916a,0x6e899d8b2df2022479,0xf3a5d0b747326ec4e6,0xafe38c59faef0d6252,0x8260fe2fa183646789,0xe50db5b4eb8a96bf5d,0x46f49ebc3293f76364,0x5e7714f1a2ecf413d5,0xe256c280c2437d6ab0,0xf2eaa6a7a464f077eb,0x749b2e8858710f2ea2,0x78593ea7f3367f224d,0x1cfb1cb56866053c2c,0x924746733bfa0c04e2,0x3129d5da59a04b85f5,0xf936982418904fa88c,0x4799f774cd25fd4a4,0xdd83be4c4787c91e92,0x1d9e7931b2a8ec4d36,0x8b29cd3cb0e60c5d97,0x45d28e8c1918f89501,0x8297a01567234d7f4a,0x918bcdad713a414d72,0x5cbb298ac7e572fcc8],
[0x377217e88f77cb363d,0x1af14558c4720fbaf4,0x49a23dec953790de57,0x7862af19bf4c6917bd,0x9f89fda4d9cde113f2,0x6fb11ccb19c50ca04b,0x7fef2efa9729067a9c,0x7c8e88b9cea457608,0xe4fbeb1ce624c857c8,0x6da5b389e39fbd3c4d,0x90c8c2ff9e5e143304,0xba0976475507408340,0xbaa6ea0d0d48d580d1,0x4c3a20326c8384e711,0x9ce4a5ecc0702fad5e,0x313c4b170dc67677f0,0xb7785584d8eae8fd8a,0xab3d9be86f968a968c,0x73b5e8bc971e74c9b9,0x639cebd2e080cf947e,0x5cc9c95e10ca7a8db9,0x92c9b5de5a84cbf353,0x5919d56cf29a4d2849,0xa9c9e1fcb0218df399],
[0x6ed09d18907db1bca0,0xd598c3681303dc304c,0x594ec5f2e1a55d0af3,0xcd58033aa618f04fd0,0xe22433483d859119fc,0xfcac3e340ee4765609,0xdb2c0f1f19b10ebade,0xfdd35be2b0b9f526f3,0xca0b169c332fe90c66,0x5b424d304c3536b4fa,0xe140a11c8b5d118f0b,0xc57c896fc1ecf5b24e,0x235da3d36c0c1287bf,0xbca683feef4fff8b5e,0xfd9adc082001950c73,0xecb0142859c41986d2,0x70408090fdd992bf56,0x565fff55c313c55e8d,0x550c56d53e73cf7646,0xc332ded2e3ec5dfa1b,0x14d508e904c0bae77a,0x25b9e6b97a2c34f64c,0xe6f0931a5d4ff91783,0x5020392a50661d99eb],
[0xb289414b0a7acd1055,0xb9fdea98fd03318854,0x9de77c4b17f156e8a8,0x1933b93828dce597b,0xd2a24b51c2d345b239,0x318e8125641bff247e,0xa74135b078244a99d6,0x849f6ba160fb98461e,0x5abbe0bad9295347f5,0xb5beba1f18a716c2fa,0x84d10435eb571514c9,0x7d0f32de3c81725a3c,0xa157551d46c52b61a9,0x4f81bcab5823ac159d,0x803e52dfc644c39282,0x235249351bffba41fe,0x52c7426c2ecb739215,0x73a59c14ba05cbe696,0x618a1f6197087ce734,0x55dea0719b8a8b5ce9,0xb2a93c8af2822fb733,0xd6af334f7e27761402,0xc0145cecb3e8681772,0x58f3edbd9eb713f21a],
[0x8e4a3746d07e8dd057,0x8fd732a23b3f2049e3,0x4f6e2f4f4a583712e1,0x75efa3487fb3c3e0b3,0x75cc6047084fe177b9,0x52abd37dedfaa92b29,0xb07e4de6d1cfd5599a,0xb5715741aa91c978ac,0xe2bccb3723f770d13a,0x8a41b2e826fcb922c4,0xbaa1b7becbe2c69df9,0x9a9635afb2bd23dff,0xb5bc408fd8bfea27d3,0x1ff7afe472c1d5323,0x67db113d3e53bfa3f,0x24879bd0546d51269d,0xff58989d3d76c1129e,0x95d574c3bf1fa08624,0xcf0b5e610cb7c86066,0x97276d6e1bcd35303a,0x146c968e23c2d94153,0x89d9f289c90ee41336,0x7ac1b5b014c63bcdfc,0xae2ca5cda0d4391f7b],
[0x99498674b71cca54a7,0xec8cffec8bb261cb48,0x5271db4d8507cae0e5,0x6d72090c31e5c10c28,0x7e89eca94347a49321,0x66b73608fb4352be8e,0x488cfe14c31a20654b,0x50ce184c39f723b97,0x451e40eb6b12dfb63,0xba4fa5796557f22416,0xfb8ff64ce8a3ee6341,0xe199323a90e0146780,0xa72779e8a8d9e93322,0x51529ff39245d315dc,0x19199a7d393c1a8e52,0xb70b13875e4649f3db,0xf7ca769cab23d99826,0xfb303d50d44963cef7,0xa4550f521380d1c956,0x4f5ec15eb422ed2850,0x73cbe720b2ea5540ca,0xb4adec3dbaaf4df223,0xada16902707d90490d,0xd9b5077e5709d38b75],
[0x519c9f6c28fedc2b8b,0x25192c49acd49fdc83,0x12e62c8550f632292b,0x18c4d68764ff9cc719,0xfe527ba725d3e94d7d,0x1e9d1064024335e2c0,0x7e0a069ac54f87e570,0x26bddecac149908339,0x62a549f0990335d0c1,0x795ad53bb92389abf9,0xad71d5c6f1c1d97596,0x958c5369b0e6c69674,0x67b09371cf881df3ff,0x4adeedce8c0acd3901,0x85568ff5a5768d92de,0x8957459ab38f5413f1,0x35ee6f0fe12a61f335,0x5b254b2f94bc1127d3,0xa8f3a7c5815652099c,0xdc93a07e093b0f79c4,0xe3d028b6efaff3d70,0x9e522e9967a89b1a4b,0xb65525e911ac852a63,0xd24f0a76f4a7b325e3],
[0xa473845c47ad5a1e95,0x90b858570cad5d75de,0xc0bfada1fbf133e9a1,0x53130188e874132b1a,0x949c6b53d2f7358160,0xb1fb342aeda08cc679,0x117dd22c82aa519183,0x752b26a460a58037ba,0x5b9eae07a8fa8c4268,0xa14bfeda6d2e0b36bc,0xcb41369076881748bb,0x99628e4c1519f4f97f,0x8a10573a47471787fe,0xaa03f5f7a9a601113a,0xb37ce0f8006935228a,0x928788d886854f684c,0x7cc54728d23be22acf,0xebb0441094fde43f94,0x75058698953e7a2e85,0x77d304fd854700ce47,0xbbd5111da674081b46,0x77f88c164fd34c1e96,0x9cc563c5fb9ed9e187,0xeffe6f67675dccaba8],
[0x215fefaa0c9fc70cd4,0x192205a0e7aaa4f652,0x5deb60ecae5cc4e647,0x71e07a9c07b68bb8ff,0xbd51834cd7cdd316a3,0x20f2e91b747f483bd2,0x2108130bc2ca54356d,0xe86ced98dbdcbaf183,0xb85fd35d2300a5c51a,0xb7c0de7c93e18a6a63,0x7ad2c06b3412546105,0xc65deeb1919ff92ccb,0xa996ed9e127e8ef2cf,0x4d9ee5f55cad1706a2,0xf785eba313d21c8855,0x30f40a67de417537c6,0xaa23d4abbf7da28b35,0x4b437c806130e7dc55,0xbf8f8ffdee6a1128e5,0xe5819dacd2a4039d03,0xf61e427d1c8954abf,0x9688103ef4b40e1032,0x950476241a0b060a7e,0xdb219e47cf83ecf97d],
[0x663a7f2f4584cdb6ef,0xb5876743e6918bc8fc,0x16b22ed51d1ea0f206,0x93c9a1eac97f1fed74,0xbe39b26262c8706897,0xc55f591bb9425b9283,0x8c6e367c08d4e972a4,0x2daffecf375ac6fde2,0x612e6f28248f73ddbd,0xdb8dbb743a1a4407d8,0x48673a4a5b28ac8259,0x9d4f7574f65990658f,0xcda0327fef9b8cafeb,0x6d470a9fb1791c483c,0xd2cc85dbdc715d4b39,0xfdc24106dea43fed89,0x13a917489553b27182,0x320ff5ee98d830f603,0x8c0307e903f72b94dc,0x23a92607333d84b7ff,0xbc7315b340183b5d91,0x83191a7d7c14024ca8,0xa89cc017868e29c6f7,0xd02cd9d4b9bafc3a73],
[0x25c415c7e71bc74ac9,0x6b87b8f882e9759096,0x19411bb587422c1786,0x1628c8de9aad2e8cd,0x5626b22a9e65851631,0x7827a66c4c8654c41,0x6c87c686ceaecb42e,0xa20d413dbd94363b94,0xaae3f306df90024b90,0xe72bacde4e96313b8c,0x3712864146c02fc6d8,0x312a07eca7bae8968f,0x1473fc51d4f8d030a7,0x5096014835499d9299,0xd3f9dcdd498831f68e,0x2b6749a8eb6cd15c93,0x139df1dd9fcb6d42d,0x8bf18d68e3f9751eaa,0x25932fd76a8d9a2b3a,0x670d0b658b7351e60b,0xf98b02d1171bebbab1,0x56e9e06322c5d72f18,0x9bb3c1deb103199ae,0xa7c50e684a0d02b83f],
[0xf0b9f4964ec1bc267c,0x7243334543747e3314,0x63f8be8cee83201203,0x59460d9dbb729eb755,0x739715f83726efa5cb,0xe4d7e6f8ef223186cc,0xcd61ad2c9c378a2d68,0xfb631cf47af6e8d907,0x5da28b52bec5942594,0xcacc0e6fd4b5153712,0x1c863f4a989b8b7340,0x1d5edfc3bf02a8afc0,0x2b292747bf6b0f5645,0xb82b4316d9811bd4b8,0xc0a8d8bd909a53d02f,0xeafc91af7f6c84b9a6,0x6f975fcc2b9a6672bb,0x291cba25d8184394cd,0xfbd290eb4c120af171,0xac17bb7e7bee1f7d79,0x26600c6f6a76380341,0xa768fa9c79182d440e,0x178bdc8b6d59b837de,0x903dbd17426cc3a5f],
[0x8577d55fe1179ea7b4,0xfc4a8977e80cceb4ff,0x92e557c31b225ea7e,0x7ff679d6994a558495,0xe3d80bcd89e503ee0d,0xde63bdb6ced3c08961,0x415572f5f30cc3629f,0x555f10530210d0b129,0xc1c6ee94b4d4557f52,0xbdcce952b9d741f6da,0xd423ba5dd091f23191,0xf74b11afe7b5fd4a47,0xa8ff8ed270926e600f,0x59611f54cc1944b902,0xc4b16b58f973f859f3,0x82f8883ae5f640d1e7,0x44c480903cfc95ce4d,0x6e78ccc0c512bc8b36,0xaaa16e0adc49657731,0xa878c869018656c4c6,0xcfa6dc6dde3c0b6f9b,0x84cc1c8f632da321bd,0x2c16e47ac1e56e8bd3,0x4b97d58d65ee48e23d],
[0x4873fc68ffbc9810eb,0x8175cd242dc8e11f06,0x9843fa20ba1f586b6e,0xe6db53776de90f9c26,0x7f8bed7a1a8244045f,0x59c0fa5690ebcf4ca3,0xb7fa9187ada7d135d1,0x269489d4c91c5063b9,0xad228d05c8de26b298,0xd7faabb8292c39a4f3,0xec019f9fdc88778ef,0xa7dbe00694eeb04635,0xcd8f1e10463deef9c8,0x3d0e18707ad078697e,0x63a79b516a2a31d34d,0xb2fc8bdfd434e26d98,0xe3d61a8421cfe1f203,0x99574708b008a833c9,0x4662ed542b575c00ac,0x1bf20906d253a6c51e,0x28146ffbca701c855b,0xdc16dce9ee12b254,0x510f3ca1a5eff702ac,0xf434e4ee010dae80e4],
[0xd4f4bec907b9363fce,0xee8ef48e1bd143b342,0xd54f1ef006a787efd1,0x2afdd6c86f24a5d1d1,0x16709a7a541ad4e96a,0x758d243ed4ec3dd34e,0x397f3599c2bcaee750,0xc15fc208a4109de3a9,0xf54ef31e630104d441,0x1d472e7866b73a097b,0x4c2817412db1e35127,0x12e13649342e2109a5,0x2e121cd8b47d8fd9a9,0x5fc7eed0a788a5167e,0x4482fe551b333043fb,0xc15161920cd78e66a5,0x10c70eef9c08e1683c,0x47af25772428a783f5,0x36e188850f17cb2f57,0x878c12a760fbd6ecaf,0x53e45a55d1037c8f6a,0x83fe7e9096ca1ddf9d,0xdf53e75bc0762fc4ea,0x61e0fef2a26e9d6d0f]]

def tile30 : List (List Nat) :=
[[0xc252a2fc133eeba178,0xfdbe3465803d802fff,0x2cc74f319a70b8b85c,0xd641e84d5294ea6236,0xc7779a040f13059d9b,0x3c660a66a42eea1051,0x7ab1356e3fd27c9c96,0xb8952f16df3b596595,0xbfb395df9112892f53,0xab8dc2655d0a9b65b9,0xe9e043668fe3fcfdd8,0xfca8f76f1a75c9bc92,0xe22f800a53e0abdf61,0x1015f9e9fad2aacc3a,0xd7548028102a673bd,0x9abf1dbcf75284c769,0x35c1ffbd3703bdfb5f,0xfed26ba005f50faed8,0x64960f5f99778dc6d8,0xc88d3559fdcfe9d4b7,0x5c7d990d7b03994068,0x8909a54a2cb2a56ffe,0x9b24dd41f6dbe29b27,0x74608056524e47a2e7],
[0x7488a3da4c5a455463,0x53c039512f11b926c1,0x825eed3087ee754afc,0x728c52f08f94537bae,0x3ea3311c88421ae772,0x276b86e592565c20fb,0x187a79b76b875afde,0xb7094f6fadf65612bf,0xff9972747e28e2d768,0x58d22db55ee4865a7,0xddfb2934d263484633,0x9a321787593913b0f1,0xbbd48ed664e7a0e0b1,0x13eabfd55099ffbc48,0xb0b338453d486632cb,0xc8010255ea30ab743c,0x7dd98529d53f69f59,0xe06f9c3804d52bd1cd,0x6d55df12da107504f8,0x539f1c13a326924595,0x1112a11c7a3b2320c4,0x1fdcfe17454f32fda6,0xf0ebe8016e3d415956,0xb62659c80cc99e029d],
[0x37930f0eb47516b564,0xa129a982b2cdbe1a48,0xf0cce37414bb6db336,0x4ddb0ae4bc8ed53d80,0x8ccd3ebd81adf48038,0xb5555f5f00837266d7,0x8769e0d4bdb3ea67f0,0x9c89af5e2f5fed3c54,0x2bee72d897277e658,0x241044d2bc3ffab7cb,0x21ff5f7cc53e0c94ea,0x865b18b6c615c49512,0x91bf32ce70f566c5a2,0xdc3504ad1af4047c87,0x3a973d0de00f11f490,0xc69a9a4aeb0072b1c1,0xeb6e0df673a1da6cb5,0xbb0b37223dd9a638a2,0x8cde8d5498ae1646da,0xc163c1d9a9c807225,0xc15bb66720534f30de,0x19c4a1ef1d3e6b90ee,0xc586a02a6e2abff0d6,0x878d9ae04c92f3e72c],
[0x291d375e64b6efc2e7,0x7f884424c2c2b57074,0xa35ac5043bcfbc7bb8,0x4e03879a6d8f5e2e5c,0xc7e81f9fb8c5c32bda,0x6c4807a131dd1af97c,0xe5d4e91ea9e3d6226,0x543e5691faf17bef71,0xd4a3718360b9228151,0x40c7e61cd90c026875,0xe8dba67e34ea8a0977,0x322103ca0c2b389456,0x1c6d0c86d25ac1a102,0x360dc2b2fef5dec67d,0x68f1235cb52eb98775,0x3d8e80dc82ad1f52df,0xd81b9f5a5c15ec5f66,0xd823544e6538b8c50f,0x38f6671aac75204f8b,0x47e5c7024f23809c4f,0xc111b7eaa829d69977,0x14becdf9ac56c0035e,0xd19e44c2dfb1f28bc9,0x66eda988984d53a748],
[0x1775f340d5356689e8,0xfdd4980be11735f3b4,0x963bef295f000d9192,0x3630406b3d196141ce,0x4dcb3d4903606c53cf,0x1f2239d354782c4f9c,0xfc7adec21c8ac22c46,0xd7bdd09b104f003497,0x36328f9868df6ab287,0x4684671f1bf544f2dc,0x39a54c6ff6a553f704,0x12e47ebaf77476a7b6,0x362e99692937d9ba3,0xb05fe59f557aed744d,0x40dd19d9767cb6dc70,0x1d3052f61abd920616,0x68256c5a2830e95fd0,0x16e482536bccc756fc,0x831fcf6abb6b57192,0xa7cc4fec87254e3b6,0xad31117a1e7e2ef7a7,0x43a62c58d969d824c5,0xf026c2b3a7a04590b5,0xa94c5cf6c60143bd55],
[0x1ed4f3881b42ddf6bc,0x52d120c455179ca954,0x493ff55ce80bfa0a4a,0x2aec54ff783c06e7b7,0x8f8698d65672e4c0ec,0x9042e98270e831af24,0xed31ede97591fb63fe,0x68cbddb374d20727b,0x78d1e245069d611588,0xc94900cfde39acacc2,0xba21906b50775a2988,0xd1962d5d80542488e0,0x35dba7de31190af835,0x10cb9041a48fdf80bd,0x6163b46eaf634b75e9,0x43806b7bcd5421f3a4,0x34a923ea98d0aa03db,0xe1ca668a91c21d545d,0x90e50127bee3c97905,0x74e6e7979613e1542e,0x1018d132bff3ddcb4b,0xcca226132f9f3fc99a,0x84efb7f08faeb36eef,0x7c6ccc3d3d913a07e0],
[0x2cd7f629dff113cf9c,0xb316742ffacc133c89,0xfae606f3bb25afdf44,0x173061f440f6967985,0xc2d3e3465baab6e53,0xf91ecadfc01eb1c18,0xd6bf0a28dfe8ce3886,0x5a67db13aa5169889f,0x9c50bfa0816432f9bb,0x5de068bbc646790c79,0x84415741f99a738945,0x44eb816c3e77e3a415,0xd9fe89258183422978,0x8369ebe265143103a5,0x28ba96c6923168b239,0x209ba5c62333006f57,0x3e1e142280498e342,0x272cd844e2cde4cdf3,0x4241defe8fdb57cb10,0xbf10e3027e8c09efbe,0x919b5c2ec80631ca9e,0x7bc8726e55f3ff9065,0x378c6e0fbfaf760dae,0x21c297f7e9ab9b1bb0],
[0x446a004e2f4ebf656b,0x6cc94a1072d1f8060b,0xe9fc6a4a11b6d099f3,0x1c56b3c203d0986bf9,0x76622833b600ea4940,0xf6eb3be78d1c935786,0x698ac2da1021f77eaf,0xb8d8100b61048be455,0xe8c418c22fefe1fee4,0xb001f8923513dc2c6b,0x20fd6add2f99f54ace,0xe5adeeda8f086a8b58,0x45a1a92bcdd29607a1,0xedf6702e74ac76483f,0xd215d10a783af46167,0x43447a8edfa5f6ed31,0x8193ad4cf0c964dc21,0x5aa796765562f0e8ec,0x4a5905192b1a629123,0x740b3edf9422452ec5,0x7592665f14e4361d61,0xab13ab8515c354b2bd,0x95b0b560c2f4c1a0e2,0x195a624588c478c2cf],
[0xdf19908431e087bc7c,0x92bbe5f0a9f1d70ef6,0x83eb3f5cacb1bf4371,0xaeecec98ded9187d01,0x28bce4dc3a3167da2e,0xf1ab3fdab603c1ead6,0xfec47155eba1024151,0x2d5dec45a67e2ebec9,0x670483d9d899cbc73d,0xd779a42ab21fa55fa0,0x10c3535110400ca962,0x824e849d725c102a85,0x93684d72f0a46abbf7,0x5574062c926cdaf247,0x76fdc36df2d6fd3ed2,0xd2cafa19b4ea4357e2,0xaee508ad3d0b3aad33,0xf20d9bd475f3704d4a,0xc32c2a8c7befc54e2a,0xf0ab7c825a1cacfa0c,0xcf18773adb0c5741ac,0x3a51c9ed87203bafc1,0x4399d534e1adff1b13,0x39ca8db5e46482d70c],
[0x1265e0f0bacb427089,0x97ccb88281d7129529,0x3872593a61fa5d6e7f,0xa9109e226cc5c49b6b,0x51a4f8394d3b905bc6,0xcbf8a8c6611e32c8e7,0xac989e7d42522e0f27,0x33d544f6d0d230387a,0xea65c4bd2da0ee7b3d,0xfb9325d70572059085,0xa7153c37dd29a42406,0x3f8395261b712ace15,0x41b2770375e95c326c,0x30dab4bc0eac670084,0x1e97610add6ca68c0b,0xf99cb58fbb0d444981,0x519c1c714d668ed874,0xde3cc7e3cafb9b623e,0xab4f9ad9e7d1c5d82a,0xaff45e349f4dcf0307,0x439ad43ffeedd554ee,0xfe95386493820cd24c,0x445f9ecc2b81ffa454,0xb2da3702405f13f62e],
[0xe5d285ab04c40bc70b,0xb1441bab246b1cec23,0xb6021128682ae4cf61,0xcaafee1f00afba8969,0xb4365156e198b09d33,0xa06248e96ed12107,0x4e6b540ec5cd17afec,0x62e9dad6660cb0adcd,0x881669d6d42769b703,0x7ce1d108d0a080b858,0xcc898d1f57631df608,0x1bbc3cd018154e2d7,0xcadd2b4e1274bb3ed2,0xfa09fa5e77267fc43a,0x122c0609ae6900dbe8,0x5319eb031c839c6a7d,0xece7e67709818957d7,0x10f823364ff44074b7,0x7d579c773705fe715b,0x3ad0d3d38e07652952,0x103e5e3c9d36d27679,0xcb3c2a09bae5ea2cef,0x63c3492d4c4719fdcc,0x78657dacb5f47a78e7],
[0xe750bf986610f3fa4c,0xa9ba14e6fe8c16114c,0x11c0a7cb7b083977d1,0xb279de6b769f346193,0x40910865942b1ec9a9,0x22e8f35f6f002928f0,0xfd8ecf4620908c5979,0xe127819b34c310322a,0x454c19cc8ab63578db,0x4878249f355aef18cd,0xab6d5acf1a290fc349,0xdd92b45927336bba42,0x7fcd94d34a71996bf,0xbaa0a256882b4deb6a,0xfa0c9a75016be04942,0x1ce1c480fda0eee322,0x4cbb3b3fe170f0e6d4,0x9b955afaece0aea501,0xfea49c60193d85060,0x8ddb618195a332565e,0x762b343afcc30f9b50,0xa42cc9d7d3cc83eabc,0x7eca34bff85f81d320,0x1d5206e9d9130ecf03],
[0x6f962d60c283d32ba8,0x40f310a34e9a13fe91,0xdd0628b50ba6d4772f,0x4eed3c27dd02f8867c,0x1a88ef81f638086afd,0x8f61d63fd5e471e15f,0xc57e4ddba3bfd05a9f,0x712bf358cd6c481f65,0xd23d989382bc6f274c,0xa463d87fd2af679464,0x2f5a9d15841ee305cc,0xefdce39aa35acc98f6,0xe4a7d02b6076f9af71,0x846c9756c35cde22a6,0xfda11c0e48f3b33440,0xf10f18b460bd17cae3,0x5493278e51e2956f0e,0xac8d7fb6201786bb75,0x44a8bf96b61c41337a,0xf48401d68d3dd13a04,0x893d7c564ac03188c6,0xdd545df68cc2ac84f8,0x3ae4f3c3493f2a0c65,0x98bfa544042176788c],
[0x7937f95339e637a96f,0x268874be019a9fe46f,0x51b3e2c7c4f556ca8f,0x3d3f5110f2f86a98c2,0xc225c25590d50c2372,0x190585ca0dc473e7ad,0x2850f9486aace2f03f,0x50af6eb68ffa15c7b2,0x35cb1f098c7e9e047d,0xf95a0b81c15ffb9066,0xb25a5751a44f2cad75,0x746aab2b50c890d81d,0xa3aaa11b903f807c2b,0x645e08d3cff8e827fe,0x5a8e01e67deb9ffa6d,0xffa959e31f6fdaadde,0x97cd6c6a7fc2c8e618,0xe0f60e98d5caec86ee,0xebad1dc06762d70264,0x3f04875dd7c38412d2,0xce646c8fcb11d6500,0xc302b0b8e563cae29,0x18bc016508601697c0,0xb8c1e33830ec7aca23],
[0x4c9bf1e5be23c12f8f,0x50789b634d084b4ac7,0xb527dc208603df75bd,0xa44e8f81252911f9f7,0x1cc7b8f9cf0d9f4f4e,0x9e44ed60e18757c99c,0x90f90be6eed00dec40,0xb67cc70646453f81bb,0x1e52724d193deac279,0xa456eb024145a84c6f,0x1eabfcfb84970f9d0,0x3baca30abc7598f496,0xc26d0254e614dad02e,0xff4dc8d9b89597ee80,0x2159f94c9c0b648b42,0xad53a7483e31e1ade3,0x9bdabde9f150db463f,0x3c630a37791f7a15ac,0x42cddbc3b3df245cf5,0xf9357335b91170ad31,0x94633220756e2b4746,0xfcfaa3e7f29ac3054e,0x192558d970b65a1f6,0x8b6752988d74dcc95b],
[0x129e4f30cae37440da,0xfc672c1a7aaaa6cfb3,0x72288e3b52a5edfb4c,0x947010eb2badf85fb5,0x488bd18d39618e7af0,0x18395b18a4bd0f8ad9,0x1924ce805a50b127ea,0x39b29fe4c870c92b28,0xe82ac477de56eeee6c,0x89570a9a17b47fbe7b,0x1ed046eaf05544744d,0xd24341a6ea605a37f,0xd95bb09c53158eb6bc,0x671c180079b3e35c23,0x7bc4d5aa97712cb7f7,0x1010000c279f0595b,0x40100030100020100,0x70100060100050100,0xa0100090100080100,0xc01000001000b0100,0xf01000e01000d0100,0x110100100100030100,0x130100120100040100,0x150100140100000100]]

def tile31 : List (List Nat) :=
[[0x170100040100160100,0x1a0100190100180100,0x1d01001c01001b0100,0x1f01001e0100070100,0x220100210100200100,0x250100240100230100,0x40100270100260100,0x2a0100290100280100,0x2d01002c01002b0100,0x1101002f01000f0200,0x310100130100300100,0xf0100320100150100,0x340100110100330100,0x1a0100350100130100,0x380100370100360100,0x3b01003a0100390100,0x3d01001d01003c0100,0x4001003f01003e0100,0x430100420100410100,0x450100220100440100,0x470100240100460100,0x490100480100210100,0x4b01002401004a0100,0x6201004d01004c0100],
[0x5001004f01004e0100,0x530100520100510100,0x5501005401002a0100,0x570100210100560100,0x5a0100590100580100,0x5d01004602005b0100,0x6001005f01005e0100,0x630100620100610100,0x660100650100640100,0x690100680100670100,0x6c01006b01006a0100,0x6f01006e01006d0100,0x720100710100700100,0x750100740100730100,0x780100770100760100,0x7b01007a0100790100,0x7e01007d01007c0100,0x8101008001007f0100,0x840100830100820100,0x870100860100850100,0x8a0100890100880100,0x8d01008c01008b0100,0x8f01007701008e0100,0x920100910100900100],
[0x950100940100930100,0x980100970100960100,0x9b01009a0100990100,0x9f01009e02009c0100,0xa50400a10100a00100,0xa80100a70100a60100,0xac0100ab0100aa0200,0xb00200ae0100ad0100,0xb30100b20100b10100,0xb60100b50100b40100,0xb90100b80100b70100,0xbc0100bb0100ba0100,0xbe0101370100bd0100,0xc00100bf0100710100,0xc30100c20100c10100,0xc60100c50100c40100,0xc90100c80100c70100,0xcc0100cb0100ca0100,0xcf0100ce0100cd0100,0xd20100d10100d00100,0xd50100d40100d30100,0xd80100d70100d60100,0xdb0100da0100d90100,0xde0100dd0100dc0100],
[0xe10100e00100df0100,0xc20300e30100e20100,0xe80100e70100e60100,0xea0100e90100c40100,0xed0100ec0100eb0100,0xf00100ef0100ee0100,0xf20100f10100c20100,0xf50100f40100f30100,0x6d0100f70100f60100,0xf90101750100f80101,0xfc0100fb0100fa0100,0xd30100fe0100fd0100,0x10101000100ff0100,0x40101030101020101,0x70101060101050101,0xa0101090101080101,0xd01010c01010b0101,0x1001010f01010e0101,0x130101120101110101,0x160101150101140101,0x190101180101170101,0x1b01011a0100580101,0x1e0100ec02011c0101,0x2101012001011f0101],
[0x240101230101220101,0x270101260101250101,0x2a0101290101280101,0x2d01012c01012b0101,0x3001012f01012e0101,0x330101320101310101,0x360101350101340101,0x390101380101370101,0x3c01013b01013a0101,0x6a01013e01013d0101,0x2e01014001013f0101,0x430101420101410101,0x450101440101310101,0x480101470101460101,0x4b01014a0101490101,0x4e01014d01014c0101,0x5101015001014f0101,0x540101530101520101,0x560101310101550101,0x580101570101330101,0x5b01015a0101590101,0x5e01015d01015c0101,0x6101016001015f0101,0x640101630101620101],
[0x670101660101650101,0x6a0101690101680101,0x6c01013f01016b0101,0x6f01016e01016d0101,0x730101720201700101,0x770101760101750201,0x7a0101790101780101,0x7d01017c01017b0101,0x8001017f01017e0101,0x830101820101810101,0x860101850101840101,0x510101880101870101,0x8b01018a0101890101,0xc01018c0101530101,0x8f01018e01018d0101,0x910101500101900101,0x930101920101180101,0x980101970301940101,0x9b01019a0101990101,0x9e01019d01019c0101,0x230101a20101a10301,0xa40101250101a30101,0xa70101a60101a50101,0xaa0101a90101a80101],
[0x7a0101ac0101ab0101,0x10000000101ad0101,281475278700544,0x4f0000000100002d00,0x60000000010000,72058049304461313,1099520409600,0xac000000010000a2,0x10000b70000000100,281478550257664,0x9d0000000b0000e100,0x2e2000000240001,0xf0002ed00000001,3298595176448,0x480000000150003d5,0x40004910000000100,281496552210432,0xf60000001500051600,0x635000000050005,0x600069000000007,1099628019712,0x7af000000080006fa,0x500081d0000000700,0x5000892000000],
[0xf000000030008da00,0x97e000000070009,0x40009e800000005,1099682283520,0xa9600000005000a3e,0x1000ac30000000400,0x5000ad3000000,0x2b00000001000b0300,0xb7f00000006000b,0x7000bcb00000004,3298737979392,0xca900000006000c3e,0x3f000d0a0000000900,0x2400105a000100,0x28000000380013db00,0x1831000000180017,0x2900191a00000010,58274585575424,0x1edd00000011001df7,0x2e001f270000000400,563095982309376,0x270000001500222900,0x2332000000010023,72096699715158021],
[5498155630592,0x25010000001b0023e7,0x500250d0000000100,281635434004480,0xbb0000000700256600,0x25c7000000010025,0x900261800000006,0xd0026a10000,0x27b000000006002757,0x40028020000000600,281647815589888,0x870000000600284d00,0x28b8000000040028,0x60028c400000001,2199714660352,0x2a1900000011002952,0x7002a270000000100,281657529597952,0xd600000008002a8d00,0x2b5000000007002a,0x5002b6500000001,2199754899456,0x2bdf00000001002bd3,0x5002c240000000300],
[0x93004e002c65000000,0xf200000005002faf00,0x320c00000036002f,0x2400326000000006,5498424918016,0x3539000000220033fa,0x3500358b0000000600,844662361292800,0x9f0000001c00378b00,0x38f9000000050038,0x3003a3d0000001f,1100500500480,0x3b2a00000001003b0f,0x1003b340000000100,281729721958400,0x6e00000001003b6300,0x3b9000000001003b,72124084426637321,29687829168128,0x3f4f00000002003f1a,0xc003fff0000000300,7600104601026560,0x140000000d00426600,0x43710000000a0043],
[0x60043f30000000d,8797238722560,0x44e80000000900449a,0xe0045110000000200,0x60045d5000000,0x2a0000000100461700,0x46e00000000b0046,0xd00471500000005,7697781096448,0x4805000000020047ee,0x5004a2e0000002800,0x7004a74000000,0xd000000001004ac600,0x4c710000001c004a,0x3a004d2000000011,0xd004f6b0000,0x508d0000000f005016,0x30052290000002900,7037227829821440,0x690000000100535c00,0x53c2000000050053,0x400055f600000046,42882446065664,0x5a6e00000001005a64],
[0x1005ab40000000800,0x7005ac4000000,0x620000001f005af700,0x5fb600c20063005c,0x2900600a00000005,0xa0061700000,0x62b8000000170061e0,0x2c00661200f6008300,0x53004b00697902b900,0xbe0000001c006cfa03,0x6f1300000006006e,0x700711c00000031,0x3af00530071540000,0x76990000001a0074ad,0x110076a80000000100,281987436773376,0xea0000000c00776700,0x7b78045800670077,0x7007c4d0000000d,51679139069952,0x7e2a00000001007e13,0x1007e870000000a00,282018994716672,0xeb00000001007ecb00],
[0x7f0d00000001007e,72197446763020289,1101647380480,0x7f8900000001007f67,0x1007fa50000000100,0x7007fc5000000,0x170000000b0080c900,0x8226000000010082,0x300837700000017,0xd0083b40000,0x84b00000000600846a,0x10085070000000200,0x7008511000000,21483597568,0x865d000000080086,0x700866800000001,6599333642240,0x875a00000001008751,0x70087e10000000600,0xc00882d000000,0x5a000000080088e200,0x89b6000000070089,0x80089ed00000003,6599393869824],
[0x8b6b00000005008b06,0x4008bd60000000500,0x5008c2a000000,0xda00000009008c7f00,0x8d3d00000007008c,72213385386655751,9897982558208,0x8ea300000004008e64,0x7008ef00000000700,0x7008f54000000,0x3c04ed003b008fb100,0x96f605dd002d0093,0x2000977900000007,1102078214144,0x995000000005009907,0x2009a6b0000001600,6756063315492864,0xae00000009009c3000,0x9cd200000002009c,0x6009dbe00000015,38485557379072,0xa11b0000001f00a009,0x600a1280000000100,563643473199104],
[0xfe0000001200a19500,0xa30b0000000100a2,0x1a00a36300000009,4400818946048,0xa61d0000001000a5ab,0xa00a62c0000000100,282190692745216,0x80000000700a6b200,0xa8600000001a00a7,0x600a86c00000001,7699415564288,0xa93c0000000100a930,0x100a9ac0000000a00,0x400a9b8000000,0x140000000100aa0600,0xaa770000000500aa,72245563281637388,7699450560512,0xab760000000100ab6d,0x200abda0000000600,4504338261082112,0xe10000000100acd400,0xad440000000900ac,0x800ad5200000001],
[1102424440832,0xae190000000700adac,0x400ae2a0000000100,282223911632896,0xc40000000400ae6a00,0xaf0d0000000300ae,0x4600af8a00000010,31888839345646,0xb66d0000002400b4f8,0x2d00b6c20000000500,0xb00b8d1000000,0x3e0000001800b92f00,0xba4e0000000100ba,72263091043172367,7699718144000,0xbb9c0000000700bb4b,0x400bd3b0000002600,7882113260978176,0x280000000500bed900,0xc00b0000001600bf,72268829119479809,2202247692288,0xc0810000000100c06d,0x100c08c0000000100]]

def tile32 : List (List Nat) :=
[[282302546444288,0xcd0000000100c0c200,0xc0d80000000100c0,72269748242481153,6600307638272,0xc1920000000300c164,0xe00c19d0000000100,282311589363712,0x3d0000000500c2ed00,0xc34e0000000100c3,0x1000c35f00000001,28590602059776,0xc6490000000500c604,0x700c6780000000300,0xc00c6ef000000,0x310000000100c82600,0xc87b0000000500c8,0x3400c88500000001,1102922055680,0xcb9f0000000500cb52,0x100cbb10000000100,282350126628864,0x720000000700cbf600,0xcc860000000100cc],
[72282538655088641,1102946631680,0xcd600000000a00ccce,0x400cd880000000100,5348908314132480,0xc90000000100ceaf00,0xcf0e0000000400ce,0x1a00cf2300000002,7700073218048,0xd09a0000000100d08e,0x100d0c20000000400,0x400d0cd000000,0xd0000000200d0f900,0xd3700000002300d1,0x200d40e00000010,36287442780160,0xd5bf0000000800d561,0x100d6470000000a00,0x700d654000000,0xf20000000100d6e200,0xd7900000000d00d6,0x200d7cc00000004,37387017060352,0xdacd0000000100dabd],
[0x1500de530747005b00,0x600e031000000,0xc90824002f00e06b00,0xe6170000001200e3,0x900e62300000001,5501429547008,0xe9350000001900e6f3,0x300e9bf0000000f00,0x400e9e5000000,0x110000000100ea0700,0xea370000000400ea,0x1200ea4400000001,1103453224960,0xeb430000000600eafb,0x100ebae0000000800,0x600ebb8000000,0x720000000100ec6800,0xecb00000000300ec,0x400ecba00000001,0xd00ece50000,0xedb80000000100edac,0x600ee040000000600,0x400ee68000000,0xce0000000300ee9900],
[0xef790000000d00ee,0x400f07600000013,2203061059584,0xf1240000000800f0d4,0x2e00f4420888003200,0x2b00f7b0093e00,0xb40000000600fa8800,0xfd790000003c00fa,0x2100fdb100000005,1103788769280,0xff610000000900feff,0x320100320000001600,0xd7003e0103540a5900,0x42000000160106f70a,0x10988000000060109,0x10010c050000002a,0xa010caa0000,0xd2500000001010d0e,0x1010d8c0000000901,0xe010d98000000,0x1700000006010ec200,0x1106000000018010f,0xd01107800000001,21994811621376],
[0x5a0ee51fc00750b23,0x864419cfa62e88589e,0x5f5f429e5761e0f890,0x9d13c29cda3659d13c,0xc5bc8fc7255702f569,0xdfa8dc0ae911c85fca,0x8c54277c7e00d375cf,0x7c40b25ea27c0665eb,0x7869a005f6ce476dc6,0xb637119666f8c5724f,0xdbe013375cb51b518e,0xc9666f82a2fe09a003,0xbae5f5d8116c6dab21,0xdba15b1499810f00c9,0x9b37deaf2fa609e2c5,0x1c31aacf63fe91eef7,0x7663a5639e56fa01a7,0x66bd1318a6c2280fac,0x8aed43d2f341ef7065,0x95f84eeef34cc31fb4,0x83488b95abc9c8506a,0xa79a3597f64d2fe855,0x7bd6f9eb6c222e043c,0xab33e3e552fd8b2b13],
[0xa5d7710d7d188f7fa9,0x105d6ac32a7edb1aa5,0x6219f04685f9744ce3,0x9a18487eab2f6f7fc9,0xe5ee93343097b4cbd9,0xf600c0bd801040a2f4,0x25a02cc9482bd80502,0xf220df1a02cc9880b3,0x59fdc12cfe20df260d,0x2c401348b20020c2ca,0x26e09de8960f4f3b09,0xf610980cf6272fe9d6,0x8cdb5de00d3624f813,0x9bdf81e48428032d26,0xcea0983005095588d1,0x86801a0000009c8024,0xd2f32199adadb54bcb,0x3f26000659f959b771,0x82c8551677700001bb,0x75b8fe98e309c0f3,0x80a7f3cd415df2cfa8,0x8b48843a1aac0bd006,0x1e0f9cbfd1ed5ce2de,0x3d933b0ba3e1d9cc1d],
[0xee8a519037423d9fa8,0x596e8183300e851b20,0x2191b775006b6a427d,0x96ceac116ae3f40012,0xe4511ed921675c7a0d,0xefd1f66cb6b1ca2dd9,0xe949887c2144f348ef,0x394743fc03e987d1a3,0x86d7be5cbf3cd40deb,0x2c76deb9cc080c3390,0xcb4021db5720044de2,0x58b02448f166a566de,0x873c90780f8517d220,0xcf3df815b6ae3986aa,0x49692aa259c2a00509,0x7006b888df61160008,0x620fdb77428c5f3248,0x83abdd2202eeb3a146,0x7764e770a719a04593,0xff10c594319b716322,0xfc40970fa15887625f,0xe1ad2c40b8c2b10637,0xb299b6ad6753a8fd52,0x7abb0ce0fea4f3e990],
[0x5954e3a49daf0b38ce,0x97f185da0332a90b80,0xbebc8a120cb9985f87,0x60585380ab75acd604,0x62c704d52793c119c3,0x82a6e8ea0de501ec66,0x4b6eb5e66bc812fb25,0x879aafcf3a9cb875db,0x559adadc952e19985f,0xbec97e79f4e546f5fe,0x2e29db4b6eb59ac0d2,0xd3d03ac9adac5ad3e5,0xfb410bca440b500218,0x79f69116ebff94f56c,0x9ee7617add02aeba87,0xe27d31ee39f70f8215,0xbf1a1a663ff4fdc1b4,0xcea75182eca74e0a06,0x854f821431a4b36d5a,0x3de8c97a60ecec7280,0xc7e80857074a957527,0x7d1c10adbf999660c5,0xed90852ffe011c10a0,0x83f65c02c46de92781],
[0xe101867cc9ceb858b0,0x4424edde56e5821178,0xd05f5f635f4906bf02,0xe58d2f7b42a3ca9eab,0xeda4970f47d687fec1,0xc2c06596e38a5a2345,0x92cc6ab5c225598d20,0x3de2bc88d968046716,0xe0e9fc7089e352d462,0xfa53dad191684b4bea,0x88b566b6b21b53b66d,0xe13becd7ca6eb01161,0x55cb31aad708912e15,0xd7a05780d3f7f9d07b,0x182897ae33a89e1962,0x8eb88b5bfeac3ecd5f,0x3bd0e59c5e09af46b5,0xdad63ae22d6ff51818,0x35adf8f13eb4e10cfe,0xbbc5ab4f728a87c2,0xa146c2be1221dbfd2f,0xf0f88d8c0ccb569a33,0x335fe6f41ed4cffb90,0x9878519cd6ff41ed99],
[0xbf7a5cbb7891fa6976,0x1f6f3e8c0bcb54a37f,0x4d207a053238af0149,0x3487c0c33c661075e0,0x35becb87092f66dea,0x2cbe42a8374ec7e837,0xb05c8f85177a72008c,0xb8c871843a8f26464a,0x3943aaa210b7567c4d,0xe5f7fee7e783da9cb1,0x3f04e5316ad9b641b6,0x13a93ff904ad0cd982,0x4b758f281a4a1fd5,0x291ca6c9d4267dc795,0xf47efce7d038aa1f0b,0xc8cf30d2f8e0b109b,0x4802af8b110eb7e15e,0x1462e345b93796de67,0x2b2869303455bfd19e,0xdfe8d7f7591f8a6c6,0x22c5224927299b6090,0x8865960b74e33b79d0,0x1f674a77a9c9181311,0xc88fb3a794f3e4db56],
[0x5309f23ce90595ef35,0x8c11a826d2dbcf68d8,0xa9114eb081601c91a8,0x7c0eec9a6349b4be48,0xe29525ba9d8df05377,0xdcc3f2269c70f26f1f,0xebbeae9f34f0f3e0ee,0xf9ab3955694322d62b,0xaaffc6ddfd0d52e1dd,0x7ba9daf8bc021d9d5b,0x968701b36a8a971760,0x6893b5d96bacfe003,0xef5ad0040239008260,0xd66eb41a356356d078,0x4aa018edc14cfff00c,0x116041301625452dad,0xee68003411e35ae581,0x748bf401f9cbd01d,0x9a0c21f10630fa0000,0x2acc73bb68f3fe83c,0x2ce672da617ac17718,0xac55ceecdb8f7b1b6e,0xefa5f20ed42e1f15ad,0x3606ff71f3085591f5],
[0x14537b3b007a36f3da,0x6bb02dc1e828766dab,0xc78f44044f1e8d224c,0xf28b9d2b36e3de7b3b,0xf7e5b9e2b36e3de6fb,0x3c11a60472cc247c59,0x6631326928ceeef3e0,0xbf8f185aa99e843759,0x21f7ee8d24f3e53dd8,0x476204f3318e968958,0x1122d665eff8df83a9,0x17b17e0891480bf0ae,0x3db197972f7dcaf690,0x802af7fc6fd7bff419,0x5f70fa9c286277fa49,0x1163e3bd76c622c23c,0xd552152ce5e1a5a1fe,0x2664dd130f0d0b948,0x682e46c15657b3061f,0x89efedfd77510d65d,0x6af1f8b08f17dc3eac,0xbd96962574a3c4cf23,0xc3c342e523554854b2,0x595ecc187c09993744],
[0x8df8fd91a5d0b91b05,0x6ac3544d1e08d60f37,0x966de2b4888275e6dc,0x9f6707bf8d8be016b7,0x15fb66a56dd59d8ca7,0xf1bf050a9273c28c2c,0xd6c384249c89297bdf,0x53048fe256a5f58306,0xf1bf18490b964f9e8b,0xa5dc637fb4d1a63bdf,0xb49c5a62a911708d63,0x7634f975d13385e6f1,0x7c90ec022938c8dfe0,0x11a072ebd7e1217db5,0xb70b5a2c80efdcd77b,0xa2657245c7453346fe,0x9c7a86f50dcc49b8b0,0xba8228c3dc28e9d27b,0x6ed1013b49c1a9a40a,0xaf2cec0e939496a840,0x8654470afc8d65d700,0x7695e7046732b4a8a,0x1e4c887ebc4efbf6ad,0x48d4b1351b8be3e155],
[0xbe20a97a614609719f,0xd18afb4ec4ee0b0f4e,0xdd5c855cd1a3b4467e,0x93388da3bd741cd5e6,0x3b734f00e89c0d9e5c,0x639595fda1ce3d05ac,0x25d4964dfa315bff66,0x9fb489fa80215c8345,0x874908b03fe82dea67,0xa59a4f697fac608161,0xa2807a4b1bf3c3c983,0x3c2940d17b47344ed0,0xebb768e6894b5a0b58,0xf33895711ae008c4d2,0xcbe9b94455d28ddfba,0xbbcbee7a81002d6c5c,0x181696ae691261e509,0x81cd84771144f78bb7,0x88a86b1c53ebd33130,0x734fefded7c9c772b0,0x6774ef57c16de9840d,0xf95cabd1520d1ada37,0x2b450533c0fad6db8b,0x3e23e1316f0868a741],
[0xb8021d8d6d62d65825,0x32c3c1ed4fa202bd86,0xf583ecb800b18f8ee5,0x764e4a44d4d06bbaa8,0x785bfb8491353419a2,0xe987af315b2dc69cb6,0x1c7e14c9ae466dddb4,0x535663f3308f6b15b3,0x59d0d506e97d4c1b45,0xcbee2b7223cbe9102d,0x223d6a8230ecd47cdd,0x9f146c9411197ee6b7,0x7d8421b5eb448223a,0x2d120022474ee25a2f,0x12eb017d315307a8db,0x28acc63d4ed4a87314,0x8ff18973356a42e431,0xc5dfb90e938533000a,0x8e76b25e5cf22ee666,0xc92f38da95894b368b,0xa5ccf5890ca995dd24,0x88fbf543c1e3aaaa54,0x96780b2f280890f842,0x161d02c4639daa9a40],
[0x1dcc0ed51c320899b6,0x1118e61ba29988d183,0xcab290a25f010ead51,0x32696615901e010702,0x990db77cdfcd78041c,0x6c0c129a45e8f90682,0x16df51c5483413809a,0xbeae53345ec5bbfd4d,0xf7e08d38d4631d7f7a,0x458bb4cbf7fc308755,0x2950d29aeb17ae57a0,0x35be789456feb8e6a1,0x1422eb60a305b9a5e,0xd1c726324e49c93581,0x758016c800d0d432e0,0xa3804303a141000572,0xd52d82c072553b1cf,0xb11ec3abb32103ac52,0xf2f873f40b870e44ab,0x34e6697f82e404b91e,0x40a1174e577dd89a8,0x7645c9392784924f7,0x536aebb50c0eb4b2c,0xf0f8aa60553000fdea]]

def tile33 : List (List Nat) :=
[[0x865c9a8002b90dc027,0xaec04dae814144cb9c,0x8310baf2ee2fe2201,0x291b892ebeb7fa8ea4,0xe843d5bd87e9894de4,0x952ff51352a2bd52bd,0x22eb5ecb0eb97d06af,0xd6d69f2e78d7efb3c7,0xb57f164734be3d252c,0x40618504c54592941a,0xb0f07b1615c766decb,0x5d87865883849a9a70,0x451f523f5a4498d4d3,0x943f50aa47dd69856f,0x2f3d85d88907db1232,0xea699ea2423634309f,0x35d88657ada16cffd3,0xb27534dc61e1462d4d,0xd9b91af41e01667bbf,0xdc2158219df0ffd3ce,0xd13da511cbf7490229,0xe8296b7d68ced22e5e,0x384060db36e2f65036,0x9e7cdd39e687c75efa],
[0x871b662103d2b94f23,0x6479961c6845b16600,0xcd11700b1600d916f2,0x1f0b9f821d8dbd330,0x70488a7b19e14a23cd,0x99091099091003d79,0x51029099091099091,0x51029051029051029,0x1390b11390b11390b1,0xa90a10a90a11390b1,0x790690a90a10a90a1,0x79069079069079069,0x2b91892b91892b9189,0x8108088000eb2b9189,0x190118288208180f3,0x19011019011019011,0x6205207205a062052,0x4904104904107205a,0xba07a049041049041,0xda0a20ba07a0da0a2,0x84802284002b03b022,0x83800100a001850033,0x6205985800100a001,0x14a05906205914a059],
[0x51041051041051041,0x12306b0e31ca051041,0x4b03919b0b311b1ca,0x878039870039868039,0x2b01203300b023012,0xaa0120a200288001b,0x910690aa0120a2002,0x91069091069091069,0x5a0b10620b105a0b1,0x8302303300b0620b1,0x7308a8a002b03b01b,0x8a809a89808a89009a,0x99081099081099081,0xa207207a05a099081,0x120a90a207207a05a,0x1a0a90120a901a0a9,0x61009061009061009,0xba039052039061009,0x330b20ba039052039,0x8d802b0430b206b023,0x8c808b8c00938b8003,0x85b002f00628e08d0,0x56004a004b004d0043,0x5000300c7000100],
[562980031299603]]

def tiles (block : Nat) : List (List Nat) :=
  (if block < 17 then (if block < 8 then (if block < 4 then (if block < 2 then (if block < 1 then tile0 else tile1) else (if block < 3 then tile2 else tile3)) else (if block < 6 then (if block < 5 then tile4 else tile5) else (if block < 7 then tile6 else tile7))) else (if block < 12 then (if block < 10 then (if block < 9 then tile8 else tile9) else (if block < 11 then tile10 else tile11)) else (if block < 14 then (if block < 13 then tile12 else tile13) else (if block < 15 then tile14 else (if block < 16 then tile15 else tile16))))) else (if block < 25 then (if block < 21 then (if block < 19 then (if block < 18 then tile17 else tile18) else (if block < 20 then tile19 else tile20)) else (if block < 23 then (if block < 22 then tile21 else tile22) else (if block < 24 then tile23 else tile24))) else (if block < 29 then (if block < 27 then (if block < 26 then tile25 else tile26) else (if block < 28 then tile27 else tile28)) else (if block < 31 then (if block < 30 then tile29 else tile30) else (if block < 32 then tile31 else (if block < 33 then tile32 else tile33))))))
def dataWord (i : Nat) : Nat :=
  strict i fun j => ((tiles (j/384)).getD ((j/24) % 16) []).getD (j % 24) 0

def directFamilyAt : Nat := 0
def directSegmentsAt : Nat := 198
def directFeaturesAt : Nat := 3874
def directNumbersAt : Nat := 5215
def paletteFamilyAt : Nat := 12447
def paletteIndexAt : Nat := 12645
def paletteValuesAt : Nat := 16908
def cdfAt : Nat := 33112
def distributionsAt : Nat := 36621
def proofsAt : Nat := 36961
def casesAt : Nat := 107060
def blocksAt : Nat := 108446
def claimsAt : Nat := 111456
def claimWordsAt : Nat := 114312
def claimSpecialsAt : Nat := 114672
def groupWidth : Nat := 8
def spanBits : Nat := 6
def beginBits : Nat := 14
def region (v : Nat) : Nat × Nat :=
  (if v < 4028 then (if v < 1510 then (if v < 1080 then (if v < 550 then (if v < 50 then (0,0) else (1,50)) else (if v < 1050 then (2,550) else (3,1050))) else (if v < 1480 then (if v < 1180 then (4,1080) else (5,1180)) else (if v < 1500 then (6,1480) else (7,1500)))) else (if v < 3390 then (if v < 1940 then (if v < 1660 then (8,1510) else (9,1660)) else (if v < 3340 then (10,1940) else (11,3340))) else (if v < 3636 then (if v < 3440 then (12,3390) else (13,3440)) else (if v < 3832 then (14,3636) else (15,3832))))) else (if v < 6856 then (if v < 5288 then (if v < 4924 then (if v < 4224 then (16,4028) else (17,4224)) else (if v < 4938 then (18,4924) else (19,4938))) else (if v < 6688 then (if v < 5988 then (20,5288) else (21,5988)) else (if v < 6716 then (22,6688) else (23,6716)))) else (if v < 9118 then (if v < 7998 then (if v < 7742 then (24,6856) else (25,7742)) else (if v < 8798 then (26,7998) else (27,8798))) else (if v < 11230 then (if v < 10014 then (28,9118) else (29,10014)) else (if v < 13730 then (30,11230) else (if v < 16230 then (31,13730) else (32,16230)))))))
def contextIndex (ctx : Nat) : Nat :=
  (if ctx < 900 then (if ctx < 600 then (0+ctx-0) else (54+ctx-600)) else (if ctx < 1000 then (65+ctx-900) else (if ctx < 1150 then (67+ctx-1000) else (81+ctx-1150))))
def bitWindow (position count : Nat) : Nat :=
  if count=0 then 0 else strict position fun start => strict count fun width =>
  let q := start / 72
  let s := start % 72
  let lo := dataWord q >>> s
  let mid := if 72 < s+width then lo ||| (dataWord (q+1) <<< (72-s)) else lo
  let full := if 144 < s+width then mid ||| (dataWord (q+2) <<< (144-s)) else mid
  full &&& ((1 <<< width)-1)

def little (p n : Nat) := bitWindow (8*p) (8*n)
def byte (p : Nat) := little p 1

def lowBitNumber (n : Nat) := Nat.log2 (n ^^^ (n &&& (n-1)))

def readGamma (p : Nat) : Nat × Nat :=
  strict p fun position =>
  let width := lowBitNumber (bitWindow position 20)
  ((1 <<< width) + bitWindow (position+width+1) width,position+2*width+1)

def piece (n start width : Nat) := (n >>> start) &&& ((1 <<< width)-1)

def boundaryStart : Nat := 0
def boundaryWidth : Nat := 10
def tagStart : Nat := 10
def tagWidth : Nat := 8
def signStart : Nat := 18
def signWidth : Nat := 22
def factorStart : Nat := 40
def factorWidth : Nat := 13
def numberWidthStart : Nat := 53
def numberWidthWidth : Nat := 6
def numberStartStart : Nat := 59
def numberStartWidth : Nat := 16
def termStartStart : Nat := 75
def termStartWidth : Nat := 9
def termCountStart : Nat := 84
def termCountWidth : Nat := 3
def segmentWidth : Nat := 87
def featureDivStart : Nat := 0
def featureDivWidth : Nat := 10
def featureModStart : Nat := 10
def featureModWidth : Nat := 7
def featureWeightStart : Nat := 17
def featureWeightWidth : Nat := 16
def featureWidth : Nat := 33

def selectBit (base : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0,_,position,_ => position
  | fuel+1,rank,position,word =>
    if word=0 then
      strict (bitWindow (base+position+64) 64) fun more => selectBit base fuel rank (position+64) more
    else if rank=0 then position+lowBitNumber word
    else selectBit base fuel (rank-1) position (word &&& (word-1))

def monotoneAt (start low count index : Nat) : Nat :=
  strict count fun n => strict index fun j =>
  let w := Nat.log2 (3*n)+1
  let q := j/16
  let checks := start+n*low
  strict (if q=0 then 0 else bitWindow (checks+(q-1)*w) w) fun before =>
  let highs := checks+((n-1)/16)*w
  strict (bitWindow (highs+before) 64) fun word =>
  let position := selectBit highs (n+21) (j % 16) before word
  ((position-j) <<< low)+bitWindow (start+j*low) low

def selectSegment (ordinal : Nat) : Nat → Nat → Nat → Nat
  | 0,lo,_ => lo
  | k+1,lo,hi =>
    if hi-lo≤1 then lo else
      let pivot := (lo+hi)/2
      let previous := bitWindow (8*directSegmentsAt+segmentWidth*(pivot-1)) boundaryWidth
      if ordinal < previous then selectSegment ordinal k lo pivot else selectSegment ordinal k pivot hi

def linearFeature (coord : Nat) : Nat → Nat → Nat → Nat → Nat × Nat
  | 0,_,pos,neg => (pos,neg)
  | n+1,index,pos,neg =>
    strict (bitWindow (8*directFeaturesAt+featureWidth*index) featureWidth) fun row =>
    let divisor := piece row featureDivStart featureDivWidth
    let modulus := piece row featureModStart featureModWidth
    let signedWeight := piece row featureWeightStart featureWeightWidth
    let digit := coord/divisor
    let v := if modulus=0 then digit else digit % modulus
    if signedWeight % 2 = 0 then linearFeature coord n (index+1) (pos+v*(signedWeight/2)) neg
    else linearFeature coord n (index+1) pos (neg+v*(signedWeight/2+1))

def templateAt (f coord index : Nat) : Nat :=
  strict index fun ordinal =>
  strict (little (directFamilyAt+3*f) 3) fun fam =>
  let first := fam &&& 65535
  let total := fam >>> 16
  strict (selectSegment ordinal 12 first (first+total)) fun j =>
  strict (bitWindow (8*directSegmentsAt+segmentWidth*j) segmentWidth) fun desc =>
  let code := piece desc tagStart tagWidth
  if code<2 then code else
    let old := if j=first then 0 else bitWindow (8*directSegmentsAt+segmentWidth*(j-1)) boundaryWidth
    let within := ordinal-old
    let w := piece desc numberWidthStart numberWidthWidth
    let start := piece desc numberStartStart numberStartWidth
    let value := if w=0 then within else if w<32 then bitWindow (8*directNumbersAt+start+w*within) w
      else monotoneAt (8*directNumbersAt+start) (w-32) (piece desc boundaryStart boundaryWidth-old) within
    let base := piece desc signStart signWidth
    let magnitude := piece desc factorStart factorWidth
    let pos := value*magnitude+(if base % 2 = 0 then base/2 else 0)
    let neg := if base % 2 = 0 then 0 else base/2+1
    let (plus,minus) := linearFeature coord (piece desc termCountStart termCountWidth) (piece desc termStartStart termStartWidth) pos neg
    if plus<minus then 2 else 3+(code-2)+128*(plus-minus)

def sumPacked (word : Nat) : Nat → Nat
  | 0 => 0
  | j+1 => sumPacked word j + piece word (spanBits*j) spanBits

abbrev Menu := Nat × Nat × Nat × Nat × Nat

def menuFor (p : Nat) : Menu :=
  strict p fun id =>
  let v := id/2
  let (shape,origin) := region v
  let coord := v-origin
  let family := 2*shape+(id % 2)
  strict (little (paletteFamilyAt+3*family) 3) fun dir =>
  let base := dir &&& 65535
  let width := dir >>> 16
  let g := coord/groupWidth
  let block := base+g/16
  let entry := 8*paletteIndexAt+(beginBits+16*spanBits)*block
  strict (bitWindow (entry+beginBits) (16*spanBits)) fun lengths =>
  let j := g % 16
  if piece lengths (spanBits*j) spanBits = 0 then (family,coord,0,0,width) else
    let start := bitWindow entry beginBits + sumPacked lengths j
    let (n,pos) := readGamma (8*(paletteValuesAt+start))
    (family,coord,n,pos,width)

def tailOrdinal : Nat → Nat → Nat → Nat
  | 0,p,base => base + (readGamma p).1 - 1
  | j+1,p,base =>
    let (gap,next) := readGamma p
    tailOrdinal j next (base+gap)

def optionAt (m : Menu) (i : Nat) : Nat :=
  let (f,x,n,p,w) := m
  if i≥n then 2 else
    let t := if i<3 then bitWindow (p+i*w) w else tailOrdinal (i-3) (p+3*w) 0
    templateAt f x t

def optionCount (m : Menu) : Nat := m.2.2.1

def optionsFor (p : Nat) := let m := menuFor p; (List.range (optionCount m)).map (optionAt m)
def distLow (start s : Nat) := if s=0 then 0 else bitWindow (8*cdfAt+12*(start+s-1)) 12

def searchDistribution (start pos : Nat) : Nat → Nat → Nat → Nat
  | 0,lo,_ => lo
  | k+1,lo,hi =>
    if hi-lo≤1 then lo else
      let pivot := (lo+hi)/2
      if distLow start pivot ≤ pos then searchDistribution start pos k pivot hi
      else searchDistribution start pos k lo pivot

def interval (context residue : Nat) : Nat × Nat × Nat :=
  strict context fun ctx => strict residue fun pos =>
  let id := contextIndex ctx
  let row := little (distributionsAt+4*id) 4
  let start := row/512
  let last := row % 512
  let symbol := searchDistribution start pos 12 0 (last+1)
  let lo := distLow start symbol
  let hi := if symbol=last then 4096 else distLow start (symbol+1)
  (symbol,lo,hi-lo)

def digitBits : Nat := 4
def cacheOn : Bool := true
def headerFamily (t : Nat) : Nat :=
  match t with
  | 11 => 1
  | 12 => 2
  | 128 => 3
  | _ => 0
def claimRoot (k : Nat) : Nat := match k with
  | 0 => 48
  | 1 => 96
  | 2 => 136
  | 3 => 176
  | _ => 232

def claimCode : Nat → Nat → Nat → Nat → Nat × Nat
  | 0,_,_,p => (0,p)
  | n+1,start,look,p =>
    strict (bitWindow (8*claimWordsAt+12*(start+(look &&& 7))) 12) fun item =>
    if item<2048 then (item/8,p+item % 8)
    else claimCode n (item-2048) (look >>> 3) (p+3)

def claimNumber (context position : Nat) : Nat × Nat :=
  strict position fun p =>
  let (s,after) := claimCode 4 (claimRoot context) (bitWindow p 9) p
  if context<3 then (s,after)
  else if s<8 then (little (claimSpecialsAt+2*((context-3)*8+s)) 2,after)
  else let width := s-8
       ((1 <<< width)-1+bitWindow after width,after+width)
end PriorG11.Compressed

namespace PriorG11.Learning

abbrev Lit := Nat × Bool
abbrev Clause := List Lit

def opposite (l : Lit) : Lit := (l.1,!l.2)
def agrees (v : Nat → Bool) (l : Lit) : Prop := v l.1 = l.2
def holds (v : Nat → Bool) (c : Clause) : Prop := ∃ l ∈ c, agrees v l
theorem opposite_agrees (v : Nat → Bool) (l : Lit) : agrees v (opposite l) ↔ ¬agrees v l := by
  simp only [agrees,opposite]
  cases v l.1 <;> cases l.2 <;> decide

def tag (l : Lit) := 2*l.1+l.2.toNat
def assign (a : Nat) (l : Lit) : Nat := a ||| (1 <<< tag l)
def respects (v : Nat → Bool) (a : Nat) : Prop := ∀ l, a.testBit (tag l) = true → agrees v l

theorem tag_injective : Function.Injective tag := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  cases b <;> cases d <;> simp [tag,Bool.toNat] at h ⊢ <;> omega

theorem respects_add {v a p} (ha : respects v a) (hp : agrees v p) : respects v (assign a p) := by
  intro l hit
  have h : a.testBit (tag l)=true ∨ p=l := by
    simpa [assign,Nat.shiftLeft_eq,Nat.testBit_two_pow,tag_injective.eq_iff] using hit
  rcases h with old|rfl
  · exact ha _ old
  · exact hp

def allFalseExcept (a : Nat) (keep : Option Lit) (c : Clause) : Bool :=
  c.all fun l => some l == keep || a.testBit (tag (opposite l))

theorem surviving_literal {v c a keep} (hc : holds v c) (ha : respects v a)
    (test : allFalseExcept a keep c = true) : ∃ l, some l = keep ∧ agrees v l := by
  obtain ⟨l,mem,ok⟩ := hc
  have h := List.all_eq_true.mp test l mem
  simp only [Bool.or_eq_true,beq_iff_eq] at h
  rcases h with same|neg
  · exact ⟨l,same,ok⟩
  · exact ((opposite_agrees v l).mp (ha _ neg) ok).elim

def evaluated {α : Type} (x : Nat) (f : Nat → α) : α :=
  match x with | 0 => f 0 | k+1 => f (k+1)

theorem evaluated_eq {α : Type} (x : Nat) (f : Nat → α) : evaluated x f = f x := by
  cases x <;> rfl

inductive Obligation where
  | need (fact : Lit)
  | finish (fact : Lit) (reason : Nat)

structure Trail (α : Type) where
  permanent : Nat
  conditional : Nat
  stream : α
  hypotheses : Clause

abbrev Picker (α : Type) := Nat → Nat → Lit → α → Option (Option (Nat × Bool) × α)

def Trail.valid {α : Type} (v : Nat → Bool) (s : Trail α) :=
  respects v s.permanent ∧ ((∀ p ∈ s.hypotheses, agrees v p) → respects v s.conditional)

def Trail.assertPermanent {α : Type} (s : Trail α) (p : Lit) : Trail α :=
  evaluated (assign s.permanent p) fun r =>
    evaluated (assign s.conditional p) fun a => ⟨r,a,s.stream,s.hypotheses⟩

def Trail.assertConditional {α : Type} (s : Trail α) (p : Lit) : Trail α :=
  evaluated (assign s.conditional p) fun a => ⟨s.permanent,a,s.stream,s.hypotheses⟩

def Trail.assume {α : Type} (s : Trail α) (p : Lit) (more : α) : Trail α :=
  evaluated (assign s.conditional p) fun a => ⟨s.permanent,a,more,p::s.hypotheses⟩

theorem Trail.assume_valid {α : Type} {v s p} (more : α) (h : Trail.valid v s) : Trail.valid v (s.assume p more) := by
  simp only [Trail.assume,evaluated_eq,Trail.valid]
  refine ⟨h.1,fun facts => respects_add (h.2 ?_) (facts _ List.mem_cons_self)⟩
  intro l hl
  exact facts l (List.mem_cons_of_mem p hl)

theorem forced {v r p c} (hc : holds v c) (hr : respects v r) (tested : allFalseExcept r (some p) c = true) :
    agrees v p := by
  obtain ⟨l,eq,hl⟩ := surviving_literal hc hr tested
  exact Option.some.inj eq ▸ hl

def needs (p : Lit) (c : Clause) : List Obligation :=
  (c.filter fun l => l != p).map fun l => .need (opposite l)

def walk {α : Type} (db : Nat → Clause) (pick : Picker α) :
    Nat → Trail α → List Obligation → Option (Trail α)
  | _,s,[] => some s
  | 0,_,_ :: _ => none
  | fuel+1,s,.need p :: tail =>
    if s.conditional.testBit (tag p) then walk db pick fuel s tail
    else match pick s.permanent s.conditional p s.stream with
      | none => none
      | some (none,more) => walk db pick fuel (s.assume p more) tail
      | some (some reason,more) =>
        let finish := .finish p reason.1 :: tail
        let next := if reason.2 then finish else needs p (db reason.1) ++ finish
        walk db pick fuel {s with stream := more} next
  | fuel+1,s,.finish p key :: tail =>
    if allFalseExcept s.permanent (some p) (db key) then
      walk db pick fuel (s.assertPermanent p) tail
    else if allFalseExcept s.conditional (some p) (db key) then
      walk db pick fuel (s.assertConditional p) tail
    else none

theorem walk_preserves {α : Type} {db : Nat → Clause} {pick : Picker α} {v fuel s t tasks}
    (hm : ∀ i, holds v (db i)) (valid : Trail.valid v s) (done : walk db pick fuel s tasks = some t) :
    Trail.valid v t := by
  induction fuel generalizing s tasks with
  | zero =>
    cases tasks with
    | nil => exact Option.some.inj done ▸ valid
    | cons h q => cases done
  | succ n ih =>
    cases tasks with
    | nil => exact Option.some.inj done ▸ valid
    | cons action tail =>
      cases action with
      | need p =>
        by_cases known : s.conditional.testBit (tag p)=true
        · exact ih valid (by simpa only [walk,if_pos known] using done)
        · cases h : pick s.permanent s.conditional p s.stream with
          | none => simp only [walk,if_neg known,h,reduceCtorEq] at done
          | some pair =>
            obtain ⟨ref,more⟩ := pair
            cases ref with
            | none => exact ih (Trail.assume_valid more valid) (by simpa only [walk,if_neg known,h] using done)
            | some key => exact ih (s := {s with stream := more}) valid (by simpa only [walk,if_neg known,h] using done)
      | finish p key =>
        by_cases perm : allFalseExcept s.permanent (some p) (db key)=true
        · have hp := forced (hm key) valid.1 perm
          have next : Trail.valid v (s.assertPermanent p) := by
            simp only [Trail.assertPermanent,evaluated_eq,Trail.valid]
            exact ⟨respects_add valid.1 hp,fun scope => respects_add (valid.2 scope) hp⟩
          exact ih next (by simpa only [walk,if_pos perm] using done)
        · by_cases cond : allFalseExcept s.conditional (some p) (db key)=true
          · have next : Trail.valid v (s.assertConditional p) := by
              simp only [Trail.assertConditional,evaluated_eq,Trail.valid]
              exact ⟨valid.1,fun scope => respects_add (valid.2 scope) (forced (hm key) (valid.2 scope) cond)⟩
            exact ih next (by simpa only [walk,if_neg perm,if_pos cond] using done)
          · simp only [walk,if_neg perm,if_neg cond,reduceCtorEq] at done

def insertLit (p : Lit) : Clause → Clause
  | [] => [p]
  | q::rest => if tag p ≤ tag q then p::q::rest else q::insertLit p rest

theorem mem_insertLit {l p c} (h : l=p ∨ l∈c) : l∈insertLit p c := by
  induction c with
  | nil => simpa [insertLit] using h
  | cons q t ih =>
    by_cases early : tag p ≤ tag q
    · simpa only [insertLit,if_pos early,List.mem_cons] using h
    · simp only [insertLit,if_neg early,List.mem_cons]
      rcases h with rfl|inc
      · exact Or.inr (ih (Or.inl rfl))
      · rcases List.mem_cons.mp inc with same|other
        · exact Or.inl same
        · exact Or.inr (ih (Or.inr other))

def sortLits : Clause → Clause
  | [] => []
  | p::rest => insertLit p (sortLits rest)

theorem mem_sortLits {l c} (h : l∈c) : l∈sortLits c := by
  induction c with
  | nil => cases h
  | cons p rest ih =>
    apply mem_insertLit
    exact (List.mem_cons.mp h).imp_right ih

def consequence (hyps additional : Clause) : Clause := sortLits (additional ++ hyps.map opposite)

theorem consequence_holds {v hyps additional} (notAll : ¬(∀ p ∈ hyps, agrees v p)) :
    holds v (consequence hyps additional) := by
  push Not at notAll
  obtain ⟨p,hp,bad⟩ := notAll
  have inc : opposite p ∈ additional ++ hyps.map opposite := List.mem_append_right _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  exact ⟨opposite p,mem_sortLits inc,(opposite_agrees v p).mpr bad⟩

abbrev Packet (α : Type) := Nat × Clause × α

def derive {α : Type} (db : Nat → Clause) (pick : Picker α) (fuel root : Nat)
    (packet : Packet α) : Option (Nat × Clause × α) :=
  let start : Trail α := ⟨root,root,packet.2.2,[]⟩
  let closing := db packet.1
  match walk db pick fuel start (closing.map fun l => .need (opposite l)) with
  | none => none
  | some final => if allFalseExcept final.conditional none closing then
      some (final.permanent,consequence final.hypotheses packet.2.1,final.stream) else none

theorem derive_sound {α : Type} {db : Nat → Clause} {pick : Picker α} {v root next clause cursor} {packet : Packet α} {fuel}
    (hm : ∀ i, holds v (db i)) (hr : respects v root) (ok : derive db pick fuel root packet = some (next,clause,cursor)) :
    respects v next ∧ holds v clause := by
  let start : Trail α := ⟨root,root,packet.2.2,[]⟩
  have hi : Trail.valid v start := ⟨hr,fun _ => hr⟩
  cases hw : walk db pick fuel start ((db packet.1).map fun l => .need (opposite l)) with
  | none => simp only [derive,show (⟨root,root,packet.2.2,[]⟩ : Trail α)=start from rfl,hw,reduceCtorEq] at ok
  | some final =>
    have sound := walk_preserves hm hi hw
    by_cases hit : allFalseExcept final.conditional none (db packet.1)=true
    · have eq : (final.permanent,consequence final.hypotheses packet.2.1,final.stream)=(next,clause,cursor) := by
        simpa only [derive,show (⟨root,root,packet.2.2,[]⟩ : Trail α)=start from rfl,hw,if_pos hit,Option.some.injEq] using ok
      have ec : consequence final.hypotheses packet.2.1 = clause := congrArg (fun p => p.2.1) eq
      have er : final.permanent = next := congrArg Prod.fst eq
      rw [← er,← ec]
      refine ⟨sound.1,consequence_holds ?_⟩
      intro hypotheses
      obtain ⟨p,absurd,_⟩ := surviving_literal (hm packet.1) (sound.2 hypotheses) hit
      cases absurd
    · simp only [derive,show (⟨root,root,packet.2.2,[]⟩ : Trail α)=start from rfl,hw,if_neg hit,reduceCtorEq] at ok

def tautology : Clause := [(0,false),(0,true)]

theorem holds_tautology (v : Nat → Bool) : holds v tautology := by
  cases h : v 0 with
  | false => exact ⟨(0,false),by decide,h⟩
  | true => exact ⟨(0,true),by decide,h⟩

def rule (source : Nat → Clause) (prior : List Clause) (n key : Nat) : Clause :=
  if key % 2=0 then source (key/2) else if key/2<n then prior.getD (n-1-key/2) tautology else tautology

theorem rule_holds {source v prior n} (hs : ∀ i, holds v (source i))
    (hd : ∀ c ∈ prior, holds v c) (key : Nat) : holds v (rule source prior n key) := by
  unfold rule
  split
  · exact hs _
  · split
    · rw [List.getD_eq_getElem?_getD]
      cases h : prior[n-1-key/2]? with
      | none => exact holds_tautology v
      | some c => exact hd c (List.mem_of_getElem? h)
    · exact holds_tautology v

abbrev Cursor := Nat
abbrev Distribution := Nat → Nat → Nat × Nat × Nat

def makeCursor (v pos : Nat) : Cursor := (pos <<< 32) ||| v

def refill (read : Nat → Nat) (v pos : Nat) : Cursor :=
  if v < 8388608 then
    evaluated (v*256+read pos) fun w =>
      if w < 8388608 then makeCursor (w*256+read (pos+1)) (pos+2) else makeCursor w (pos+1)
  else makeCursor v pos

def draw (read : Nat → Nat) (interval : Distribution) (ctx : Nat) (s : Cursor) : Nat × Cursor :=
  evaluated s fun word =>
    let residue := word &&& 4095
    let (symbol,lo,count) := interval ctx residue
    let next := count * ((word &&& 4294967295) >>> 12) + (residue-lo)
    (symbol,evaluated next fun v => refill read v (word >>> 32))

def rankOrOnly (read : Nat → Nat) (interval : Distribution) (count ctx : Nat) (s : Cursor) : Nat × Cursor :=
  if count ≤ 1 then (0,s) else draw read interval ctx s

def priorRefs (p : Lit) (n : Nat) : List Clause → List Nat
  | [] => []
  | c::cs => if p ∈ c then (2*(n-1)+1) :: priorRefs p (n-1) cs else priorRefs p (n-1) cs

end PriorG11.Learning

namespace PriorG11.Stream
open PriorG11.Learning
open PriorG11.Compressed

abbrev State := Nat × Nat

def symbol (ctx s : Nat) := draw byte interval ctx s

def digitNumber (ctx : Nat) : Nat → Nat → Nat → Nat → Nat → Nat × Nat
  | 0,_,_,acc,s => (acc,s)
  | fuel+1,tier,shift,acc,s =>
    let (digit,after) := symbol (ctx+min 3 tier) s
    let base := 1 <<< digitBits
    let total := acc+((digit % base) <<< shift)
    if digit<base then (total,after) else digitNumber ctx fuel (tier+1) (shift+digitBits) total after

def transmittedNat (ctx s : Nat) := digitNumber ctx 8 0 0 0 s

def readExtras : Nat → Nat → Nat → Clause × Nat
  | 0,_,s => ([],s)
  | count+1,base,s =>
    let (gap,after) := transmittedNat 1150 s
    let v := base+gap
    let (rest,final) := readExtras count (v+1) after
    ((v/2,v % 2 == 1)::rest,final)

def packet (step : Nat) (s : State) : Packet State :=
  let (family,afterFamily) := symbol 900 s.1
  let (param,afterParam) := transmittedNat (1000+4*headerFamily family) afterFamily
  let closing := if family=128 then 2*(step-1-param)+1 else 2*(family+128*param)
  let (count,afterCount) := symbol 901 afterParam
  let (extra,after) := readExtras count 0 afterCount
  (closing,extra,(after,s.2))

def presentUnit (a : Nat) (p : Lit) : Bool → Clause → Bool
  | seen, [] => seen
  | seen, h :: tail => if h = p then presentUnit a p true tail
    else a.testBit (tag (opposite h)) && presentUnit a p seen tail

def firstForced (source : Nat → Clause) (enabled : Nat → Bool) (conditional : Nat) (p : Lit) (m : Menu) :
    Nat → Nat → Nat → Option Nat
  | 0,_,_ => none
  | _+1,_,0 => none
  | fuel+1,i,left+1 =>
    if i≥optionCount m then none else
      let a := optionAt m i
      if a<2 then firstForced source enabled conditional p m fuel (i+1) (left+1) else
        if 3≤a && presentUnit conditional p false (source (a-3)) then some a
        else firstForced source enabled conditional p m fuel (i+1) left

def chooseReason (source : Nat → Clause) (enabled : Nat → Bool) (n : Nat) (prior : List Clause)
    (_root conditional : Nat) (p : Lit) (s : State) : Option (Option (Nat × Bool) × State) :=
  let id := tag p
  let m := evaluated id menuFor
  match firstForced source enabled conditional p m 4 0 2 with
  | some a => some (some (2*(a-3),true),s)
  | none =>
    let size := optionCount m
    let shift := 24*(((id*1103515245+12345) >>> 11) % 512)
    let old := if cacheOn then (s.2 >>> shift) &&& 16777215 else 0
    let reuse := cacheOn && size>1 && old/128==id+1
    let (value,after) := rankOrOnly byte interval size (2*((size-1)/3)+reuse.toNat) s.1
    let rank := if reuse then if value=0 then old % 128 else if value-1 < old % 128 then value-1 else value else value
    let saved := if cacheOn && size>1 then s.2 ^^^ ((old ^^^ ((id+1)*128+rank)) <<< shift) else s.2
    if rank≥size then none else match optionAt m rank with
    | 0 => some (none,(after,saved))
    | 1 =>
      let refs := priorRefs p n prior
      let (which,more) := rankOrOnly byte interval refs.length (600+(refs.length-1)/3) after
      (refs[which]?).map fun key => (some (key,false),(more,saved))
    | 2 => none
    | a+3 => some (some (2*a,false),(after,saved))

end PriorG11.Stream
namespace PriorG11.Blocks
open PriorG11.Learning PriorG11.Stream

abbrev Claims := List (Nat × Clause)

def preserves (v : Nat → Bool) (outputs : Claims) := ∀ item ∈ outputs, holds v item.2

def validate (step : Nat) (c : Clause) : Claims → Option Claims
  | [] => some []
  | x::xs => if x.1 = step then (if x.2 = c then some xs else none) else some (x::xs)

theorem validate_correct {step c outputs rest v} (hc : holds v c)
    (checked : validate step c outputs = some rest) (ok : preserves v rest) : preserves v outputs := by
  cases outputs with
  | nil => intro a h; cases h
  | cons x xs =>
    by_cases hi : x.1 = step
    · by_cases equal : x.2 = c
      · have e : xs = rest := by simpa only [validate,if_pos hi,if_pos equal,Option.some.injEq] using checked
        intro a member
        rcases List.mem_cons.mp member with rfl|old
        · exact equal ▸ hc
        · exact ok a (e ▸ old)
      · simp only [validate,if_pos hi,if_neg equal,reduceCtorEq] at checked
    · have e : x::xs = rest := by simpa only [validate,if_neg hi,Option.some.injEq] using checked
      exact e ▸ ok

def segment {α : Type} (source : Nat → Clause) (pick : Nat → List Clause → Picker α)
    (packet : Nat → α → Packet α) (fuel : Nat) : Nat → Nat → Nat → Nat → List Clause → α → Claims → Bool
  | 0,_,_,_,_,_,outputs => outputs.isEmpty
  | k+1,step,n,root,prior,input,outputs =>
    match derive (rule source prior n) (pick n prior) fuel root (packet n input) with
    | none => false
    | some (next,clause,after) =>
      match validate step clause outputs with
      | none => false
      | some rest => evaluated next fun r =>
        segment source pick packet fuel k (step+1) (n+1) r (clause::prior) after rest

theorem segment_sound {α : Type} {source : Nat → Clause} {pick : Nat → List Clause → Picker α}
    {packet : Nat → α → Packet α} {v fuel k} (hs : ∀ i, holds v (source i))
    {step n root prior input outputs} (hp : ∀ c ∈ prior, holds v c) (hr : respects v root)
    (ok : segment source pick packet fuel k step n root prior input outputs=true) : preserves v outputs := by
  induction k generalizing step n root prior input outputs with
  | zero =>
    cases outputs with
    | nil => intro o h; cases h
    | cons o os => cases ok
  | succ k ih =>
    cases hd : derive (rule source prior n) (pick n prior) fuel root (packet n input) with
    | none => simp only [segment,hd,reduceCtorEq] at ok
    | some result =>
      obtain ⟨next,c,after⟩ := result
      obtain ⟨hn,hc⟩ := derive_sound (rule_holds hs hp) hr hd
      cases hval : validate step c outputs with
      | none => simp only [segment,hd,hval,reduceCtorEq] at ok
      | some rest =>
        apply validate_correct hc hval
        apply ih (input := after) (n := n+1) (step := step+1) (root := next) (prior := c::prior)
        · intro a ha
          rcases List.mem_cons.mp ha with rfl|old
          · exact hc
          · exact hp _ old
        · exact hn
        · simpa only [segment,hd,hval,evaluated_eq] using ok

def previous (published : Nat → Claims) : Nat → List Clause
  | 0 => []
  | k+1 => ((published k).map Prod.snd).reverse ++ previous published k

def expected (steps : Nat) (published : Claims) (isLast : Bool) : Claims :=
  published ++ (if isLast then [(steps-1,[])] else [])

theorem complete {source : Nat → Clause} {v} (hs : ∀ i, holds v (source i))
    (enabled : Nat → Bool) (start : Nat → State) (length : Nat → Nat) (published : Nat → Claims)
    (last : Nat) (checked : ∀ j ≤ last,
      segment source (chooseReason source enabled) packet 500000 (length j) 0 (previous published j).length
          0 (previous published j) (start j) (expected (length j) (published j) (j == last))=true) : False := by
  have initial : respects v 0 := by intro l bit; simp at bit
  have accumulated (j : Nat) (hj : j≤last) : ∀ c ∈ previous published j, holds v c := by
    induction j with
    | zero => intro c hc; cases hc
    | succ k ih =>
      have small : k≤last := by omega
      have h := segment_sound hs (ih small) initial (checked k small)
      intro c member
      rw [previous,List.mem_append] at member
      rcases member with new|old
      · rw [List.mem_reverse,List.mem_map] at new
        obtain ⟨o,ho,rfl⟩ := new
        exact h o (List.mem_append_left _ ho)
      · exact ih small c old
  have h := segment_sound hs (accumulated last (le_refl _)) initial (checked last (le_refl _))
  have inc : (length last-1,[]) ∈ expected (length last) (published last) (last == last) := by simp [expected]
  obtain ⟨_,m,_⟩ := h _ inc
  cases m

end PriorG11.Blocks

namespace PriorG11.Blocks
open PriorG11.Learning PriorG11.Stream PriorG11.Compressed

def parseLits : Nat → Nat → Nat → Clause × Nat
  | 0,_,pos => ([],pos)
  | n+1,base,pos =>
    let (d,after) := claimNumber (if base=0 then 3 else 4) pos
    let v := base+d
    let (xs,next) := parseLits n (v+1) after
    ((v/2,v % 2 == 1)::xs,next)

def parseClaims : Nat → Nat → Nat → Claims
  | 0,_,_ => []
  | n+1,base,pos =>
    let (gap,more) := claimNumber 1 pos
    let (count,after) := claimNumber 2 more
    let (clause,next) := parseLits count 0 after
    let step := base+gap
    (step,clause)::parseClaims n (step+1) next

def firstBlock (i : Nat) := little (casesAt+3*i) 2
def blockCount (i : Nat) := byte (casesAt+3*i+2)
def lengthOf (b : Nat) := little (blocksAt+7*b+3) 2
def startOf (b : Nat) : State :=
  let first := proofsAt+little (blocksAt+7*b) 3
  (makeCursor (little first 4) (first+4),0)
def claimsOf (b : Nat) : Claims :=
  strict (little (blocksAt+7*b+5) 2) fun offset =>
  if offset=0 then [] else
    let (count,after) := claimNumber 0 (8*(claimsAt+offset-1))
    parseClaims count 0 after

def oneBlock (cell j : Nat) (source : Nat → Clause) (enabled : Nat → Bool) : Bool :=
  let first := firstBlock cell
  let last := blockCount cell-1
  let b := first+j
  let prior := previous (fun k => claimsOf (first+k)) j
  segment source (chooseReason source enabled) packet 500000 (lengthOf b) 0 prior.length 0 prior
    (startOf b) (expected (lengthOf b) (claimsOf b) (j == last))

def whole (cell : Nat) (source : Nat → Clause) (enabled : Nat → Bool) : Bool :=
  let last := blockCount cell-1
  (List.range (last+1)).all fun j => oneBlock cell j source enabled

theorem whole_sound {v source enabled cell} (hs : ∀ i, holds v (source i)) :
    whole cell source enabled = false := by
  cases chk : whole cell source enabled with
  | false => rfl
  | true =>
    exfalso
    apply complete hs enabled (fun j => startOf (firstBlock cell+j)) (fun j => lengthOf (firstBlock cell+j))
      (fun j => claimsOf (firstBlock cell+j)) (blockCount cell-1)
    intro j hj
    exact List.all_eq_true.mp chk j (List.mem_range.mpr (by omega))

end PriorG11.Blocks

namespace PriorG11.Proof
open SharedCases Bounds Learning Blocks

def active [Slice] (b : CellData) : Nat → Bool :=
  Rup.enS b.budget b.independentMask b.mode b.symmetry b.pins b.pairs b.masks

def reason [Slice] (b : CellData) (key : Nat) : Clause :=
  if active b key then Rup.expS b.budget b.independentMask b.mode b.pins b.pairs b.masks key else tautology

def before (i : Fin 4) : Nat := match i.val with
  | 0 => 0 | 1 => 126 | 2 => 197 | _ => 325

def number (i : Fin 4) (j : Nat) := (blockCount (before i+j)-1)+1

def atBlock (i : Fin 4) (j s : Nat) : Bool :=
  let b := (cellsAt i).getD j default
  oneBlock (before i+j) s (@reason ⟨i⟩ b) (@active ⟨i⟩ b)

abbrev Works (i : Fin 4) (j : Nat) := ∀ s < number i j, atBlock i j s=true
abbrev Successful := ∀ i : Fin 4, ∀ j < (cellsAt i).length, Works i j
abbrev Span (i : Fin 4) (start finish : Nat) := ∀ j, start≤j → j<finish → Works i j

theorem appendSpan {i a b c} (l : Span i a b) (r : Span i b c) : Span i a c := by
  intro j ha hc
  by_cases h : j<b
  · exact l j ha h
  · exact r j (by omega) hc
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range0x0 : Span 0 0 38 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range0x1 : Span 0 38 53 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 2 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range0x2 : Span 0 53 63 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range0x3 : Span 0 63 84 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range0x4 : Span 0 84 114 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 2 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range0x5 : Span 0 114 126 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range1x0 : Span 1 0 20 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range1x1 : Span 1 20 37 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range1x2 : Span 1 37 52 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range1x3 : Span 1 52 57 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 2 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range1x4 : Span 1 57 61 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 4 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range1x5 : Span 1 61 71 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 2 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range2x0 : Span 2 0 31 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range2x1 : Span 2 31 50 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 3 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range2x2 : Span 2 50 62 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range2x3 : Span 2 62 88 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range2x4 : Span 2 88 112 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 2 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range2x5 : Span 2 112 128 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range3x0 : Span 3 0 47 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range3x1 : Span 3 47 73 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range3x2 : Span 3 73 80 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 2 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range3x3 : Span 3 80 113 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 3 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range3x4 : Span 3 113 120 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (change s < 1 at hs) <;> interval_cases s <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem range3x5 : Span 3 120 137 := by
  intro j lo hi
  interval_cases j <;> intro s hs <;> (first | change s < 1 at hs | change s < 3 at hs) <;> interval_cases s <;> decide +kernel
theorem successful : Successful := by
  intro i
  fin_cases i
  · intro j hj
    exact (appendSpan range0x0 (appendSpan range0x1 (appendSpan range0x2 (appendSpan range0x3 (appendSpan range0x4 range0x5))))) j (Nat.zero_le j) hj
  · intro j hj
    exact (appendSpan range1x0 (appendSpan range1x1 (appendSpan range1x2 (appendSpan range1x3 (appendSpan range1x4 range1x5))))) j (Nat.zero_le j) hj
  · intro j hj
    exact (appendSpan range2x0 (appendSpan range2x1 (appendSpan range2x2 (appendSpan range2x3 (appendSpan range2x4 range2x5))))) j (Nat.zero_le j) hj
  · intro j hj
    exact (appendSpan range3x0 (appendSpan range3x1 (appendSpan range3x2 (appendSpan range3x3 (appendSpan range3x4 range3x5))))) j (Nat.zero_le j) hj
end PriorG11.Proof
namespace PriorG11.SharedCases
variable [sctx : Slice]
section
private abbrev tS (n:Nat):=Finset (Fin n)
private abbrev tX (n:Nat):=Fin n->Bool
private abbrev tY (n:Nat):=Fin n->Nat
private abbrev tK:=Finset Nat
private abbrev tL:=List Bool
private abbrev tJ:=Nat×Bool
private abbrev tG:=Bool×Nat×Nat
private abbrev tF:=Finset
open List renaming all_eq_true->p0,any_cons->p1,any_eq_true->p2,getD_eq_getElem?_getD->p3,getElem?_append_left->p4,getElem?_eq_getElem->p5,getElem?_map->p6,getElem_of_mem->p7,length_ofFn->p8,length_singleton->p9,length_take->p10,map_append->p11,map_cons->p12,map_nil->p13,mem_cons_self->p14,mem_filter->p15,mem_map->p16,mem_range->p17,mem_toFinset->p18,nodup_append->p19,range->p20,toFinset_card_of_nodup->p21
open Nat renaming find->p22,find_min->p23,find_spec->p24,not_lt->p25,one_shiftLeft->p26,testBit_or->p27,zero_testBit->p28
open Finset renaming card_eq_one->p29,card_filter->p30,card_filter_add_card_filter_not->p31,card_image_of_injOn->p32,card_image_of_injective->p33,card_le_card->p34,card_sdiff_add_card_eq_card->p35,disjoint_left->p36,eq_empty_of_forall_notMem->p37,filter_filter->p38,image_nonempty->p39,inter_subset_right->p40,le_max'->p41,max'_mem->p42,mem_insert->p43,mem_sigma->p44,mem_toList->p45,one_lt_card->p46,range->p47,singleton_injective->p48,singleton_subset_iff->p49,sum_add_distrib->p50,sum_congr->p51,sum_eq_zero->p52,univ->p53
open Bool renaming eq_false_iff->p54,false->p55,false_and->p56,false_or->p57,noConfusion->p58,not_eq_false->p59,not_not->p60,not_true->p61,or_assoc->p62,true->p63,true_and->p64
open Prod renaming fst->p65
open Sum (inl inr)
open List renaming length->tD
namespace DagTools
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Finset (mem_coe mem_biUnion sum_subset mem_product filter_congr univ)
namespace A0
abbrev RT:=@Relation.ReflTransGen
abbrev rC:=@Relation.ReflTransGen.cases_head
abbrev rI:=@Relation.ReflTransGen.head_induction_on
abbrev sI:=@Nat.strong_induction_on
abbrev oF:=@List.ofFn
lemma lL{a b c:Nat}:a<b->b<=c->a<c:=lt_of_lt_of_le
lemma dT{p:Prop}[Decidable p]:(decide p=p63)=p:=decide_eq_true_eq
lemma m0{α}[DecidableEq α](a:α):a∈({a}:tF α):=Finset.mem_singleton_self a
noncomputable abbrev cP:=@Classical.decPred
lemma bA{a b:Bool}:((a&&b)=p63)=(a=p63/\b=p63):=Bool.and_eq_true a b
lemma bO{a b:Bool}:((a||b)=p63)=(a=p63\/b=p63):=Bool.or_eq_true a b
abbrev EP:=@Equiv.Perm
lemma mF{α}{s:tF α}{p}[DecidablePred p]{a}:a∈s.filter p<->a∈s/\p a:=Finset.mem_filter
lemma mS{α}[DecidableEq α]{a b:α}:a∈({b}:tF α)<->a=b:=Finset.mem_singleton
lemma mR{n m:Nat}:n∈p47 m<->n<m:=Finset.mem_range
lemma mI{α}[DecidableEq α]{s t:tF α}{a}:a∈s∩t<->a∈s/\a∈t:=Finset.mem_inter
lemma mU{α}[Fintype α](a:α):a∈(p53:tF α):=Finset.mem_univ a
lemma mD{α}[DecidableEq α]{s t:tF α}{a}:a∈s\t<->a∈s/\a∉t:=Finset.mem_sdiff
lemma mG{α β}[DecidableEq β]{f:α->β}{s:tF α}{b}:b∈s.image f<->∃a∈s,f a=b:=Finset.mem_image
lemma mN{α}[DecidableEq α]{s t:tF α}{a}:a∈s∪t<->a∈s\/a∈t:=Finset.mem_union
lemma nE{α}(a:α):a∉(∅:tF α):=Finset.notMem_empty a
abbrev U0:=Σ _:Nat,Nat
abbrev rH:=@Relation.ReflTransGen.head
abbrev rR:=@Relation.ReflTransGen.refl
abbrev rK:=@Relation.ReflTransGen.cases_tail
abbrev rT:=@Relation.ReflTransGen.tail
abbrev fE:=@Finset.eq_empty_iff_forall_notMem
abbrev fS:=@Finset.sum_filter_add_sum_filter_not
abbrev fN:=@Finset.not_nonempty_iff_eq_empty
abbrev fU:=@Finset.card_union_of_disjoint
abbrev fI:=@Finset.inter_subset_left
abbrev lP:=@List.length_pos_of_ne_nil
abbrev lR:=List.finRange
abbrev lS:=@List.mem_singleton
abbrev nA:=@Nat.add_sub_cancel_left
abbrev nL:=@Nat.le_add_right
abbrev bF:=Bool.false_eq_true
abbrev lA:=@List.length_append
abbrev lO:=@List.foldl_cons
abbrev o1:=@Or.inl
abbrev o2:=@Or.inr
abbrev nZ:=@Nat.zero_le
abbrev nO:=@Nat.zero_lt_one
abbrev nT:=@Nat.lt_of_lt_of_le
lemma fw{α}(a:α):({a}:tF α).card=1:=Finset.card_singleton a
abbrev fz:=@Finset.card_pos
abbrev gk:=@Finset.not_nonempty_empty
abbrev g5:=p47
abbrev g6:=@List.mem_append
abbrev g8:=@Finset.card_eq_zero
abbrev gI:=@Finset.filter_eq_empty_iff
abbrev hC:=@List.mem_finRange
abbrev hE:=@Finset.single_le_sum
abbrev hD:=@dite_eq_left
abbrev hF:=@Sum.inl.injEq
abbrev hG:=@List.getElem_append_left
abbrev hH:=@List.getElem_append_right
abbrev hI:=@Option.some.injEq
abbrev hJ:=@Nat.not_lt_zero
abbrev hK:=@List.length_replicate
abbrev hL:=@List.getElem_mem
abbrev hN:=@Finset.card_le_card_of_injOn
abbrev hO:=@Finset.card_filter_le
end A0
section
open A0
def xp:Bool->Bool->Bool->Bool
 | true,a,b=>a&&b
 | false,a,b=>a||b
@[simp] lemma gop_true(a b:Bool):xp p63 a b=(a&&b):=rfl
@[simp] lemma gop_false(a b:Bool):xp p55 a b=(a||b):=rfl
abbrev qD:=List (tG)
abbrev Dag:=qD
def gZ(D:qD)(j:Nat):Bool:=(D.getD j (p55,0,0)).1
def yx(D:qD)(j:Nat):Nat:=(D.getD j (p55,0,0)).2.1
def yf(D:qD)(j:Nat):Nat:=(D.getD j (p55,0,0)).2.2
def zp(w:tL)(g:tG):tL:=w++[xp g.1 (w.getD g.2.1 p55) (w.getD g.2.2 p55)]
def wl(D:qD)(w:tL):tL:=D.foldl zp w
def fO(D:qD){n:Nat}(x:tX n)(w:Nat):Bool:=(wl D (oF x)).getD w p55
abbrev val(D:qD){n:Nat}:=@fO D n
def q0(n:Nat)(D:qD):Prop:=∀j,j<(tD D)->yx D j<n+j/\yf D j<n+j/\yx D j≠yf D j
def qg(D:qD)(w:Nat):tK:=(g5 (tD D)).filter (λ j=>yx D j=w\/yf D j=w)
def fanout (D:qD)(w:Nat):Nat:=(qg D w).card
def b5(n:Nat)(D:qD):Prop:=∀w,w+1<n+(tD D)->1<=fanout D w
def fV(n:Nat)(D:qD):Prop:=q0 n D/\b5 n D/\D≠[]
abbrev StrictLive:=fV
def qb(n:Nat)(D:qD):Nat:=n+(tD D)-1
def q9{n:Nat}(v:Fin n):tX n:=λ i=>decide (i=v)
def fM(n:Nat)(D:qD)(w:Nat):tS n:=univ.filter (λ v=>fO D (q9 v) w=p63)
abbrev supp:=fM
def q6(D:qD)(K:tK):Nat:=∑ w∈K,(fanout D w-1)
def inner(n:Nat)(D:qD):tK:=g5 (n+(tD D)-1)
def yr(n:Nat)(D:qD):Nat:=q6 D (inner n D)
def fJ(n:Nat)(D:qD):Nat:=q6 D ((inner n D).filter (λ w=>(fM n D w).Nonempty))
def Bzero (n:Nat)(D:qD):Nat:=q6 D ((inner n D).filter (λ w=>¬(fM n D w).Nonempty))
def kl(n:Nat)(D:qD):tK:=(g5 (n+(tD D))).filter (λ w=>2<=fanout D w)
def fX(n:Nat)(D:qD):tS n:=(kl n D).biUnion (fM n D)
def ineligSet (n:Nat)(D:qD):Finset (Fin n):=univ \ fX n D
def units(n:Nat)(D:qD):tF U0:=(inner n D).sigma (λ w=>g5 (fanout D w-1))
def ww(n:Nat)(D:qD):tF U0:=(units n D).filter (λ u=>(fM n D u.1).Nonempty)
def jw(D:qD):tF (tJ):=g5 (tD D)×ˢ p53
def fC(D:qD)(e:tJ):Nat:=if e.2=p63 then yf D e.1 else yx D e.1
def qc(n:Nat)(D:qD)(K:tK):tF (tJ):=(jw D).filter (λ e=>fC D e∈K/\n+e.1∉K)
def w5(n:Nat)(D:qD)(K:tK):tK:=(g5 (tD D)).filter (λ j=>n+j∈K/\yx D j∈K/\yf D j∈K)
def z8(n:Nat)(K:tK):tK:=K.filter (λ w=>w<n)
def q2(n:Nat)(D:qD)(T:tS n):tK:=(g5 (n+(tD D))).filter (λ w=>(fM n D w∩T).Nonempty)
def q4(n:Nat)(D:qD)(x y:Fin n):tK:=(g5 (n+(tD D))).filter (λ w=>x∈fM n D w/\y∉fM n D w)
def gN(n:Nat)(D:qD)(b:tY n):Prop:=∀v∈fX n D,2<=fanout D (b v)/\fM n D (b v)={v}
abbrev PureBranch:=gN
def qh(n:Nat)(D:qD)(b:tY n):tF U0:=(fX n D).image (λ v=>(⟨b v,0⟩:U0))
def residualUnits (n:Nat)(D:qD)(b:Fin n->Nat):Finset (U0):=ww n D \ qh n D b
section
variable (D:qD)(j:Nat)(h:j<(tD D))
include D j h
lemma xd :gZ D j=(D[j]).1:=by simp[gZ,p5 h]
lemma xe :yx D j=(D[j]).2.1:=by simp[yx,p5 h]
lemma xf :yf D j=(D[j]).2.2:=by simp[yf,p5 h]
end
lemma km(g:tG)(D:qD)(w:tL):wl (g::D) w=wl D (zp w g):=rfl
lemma vi(D E:qD)(w:tL):wl (D++E) w=wl E (wl D w):=by simp[wl,List.foldl_append]
lemma zf(w:tL)(g:tG):(zp w g).length=w.length+1:=by simp[zp]
lemma jk(D:qD):∀w:tL,(wl D w).length=w.length+(tD D):=by induction D with|nil=>{intro w;simp[wl]}|cons g D ih=>{intro w;rw[km,ih,zf];simp;omega}
lemma jo(w:tL)(g:tG)(i:Nat)(h:i<w.length):(zp w g).getD i p55=w.getD i p55:=by simp[zp,p4 h]
lemma jx(D:qD):∀(w:tL) (i:Nat),i<w.length->(wl D w).getD i p55=w.getD i p55:=by induction D with|nil=>{intro w i _;rfl}|cons g D ih=>{intro w i h;rw[km,ih _ _ (by rw[zf];omega),jo _ _ _ h]}
lemma b6(w:tL)(i:Nat)(h:w.length<=i):w.getD i p55=p55:=by simp[List.getElem?_eq_none h]
lemma zq(w:tL)(g:tG):(zp w g).getD w.length p55=xp g.1 (w.getD g.2.1 p55) (w.getD g.2.2 p55):=by simp[zp]
lemma kn(D:qD)(w:tL)(j:Nat)(a:j<(tD D)):(wl D w).getD (w.length+j) p55=xp (gZ D j) ((wl (D.take j) w).getD (yx D j) p55) ((wl (D.take j) w).getD (yf D j) p55):=by have c:D=D.take j++D[j]::D.drop (j+1):=by{simp};have d:(wl (D.take j) w).length=w.length+j:=by{rw[jk,p10];omega};rw[xd D j a,xe D j a,xf D j a];conv_lhs=>{rw[c,vi,km]};rw[jx _ _ _ (by rw[zf,d];omega),<-d,zq]
lemma zg(D:qD)(w:tL)(j i:Nat)(a:i<w.length+j)(c:j<=(tD D)):(wl (D.take j) w).getD i p55=(wl D w).getD i p55:=by have d:D=D.take j++D.drop j:=by{simp};have g:(wl (D.take j) w).length=w.length+j:=by{rw[jk,p10];omega};conv_rhs=>{rw[d,vi]};rw[jx (D.drop j) (wl (D.take j) w) i (by rw[g];exact a)]
section
variable (D:qD){n:Nat}(x:tX n)
include D n x
lemma qa(i:Nat)(h:i<n):fO D x i=x ⟨i,h⟩:=by unfold fO;rw[jx _ _ _ (by simpa using h)];simp[h]
lemma z0(w:Nat)(h:n+(tD D)<=w):fO D x w=p55:=by unfold fO;exact b6 _ _ (by rw[jk];simpa using h)
lemma xx(k w:Nat)(a:w<n+k)(c:k<=(tD D)):fO (D.take k) x w=fO D x w:=by unfold fO;exact zg D _ k w (by simpa using a) c
end
lemma qu{n:Nat}{D:qD}(c:q0 n D)(x:tX n)(j:Nat)(a:j<(tD D)):fO D x (n+j)=xp (gZ D j) (fO D x (yx D j)) (fO D x (yf D j)):=by obtain⟨g,d,-⟩:=c j a;have h:=kn D (oF x) j a;simp only[p8] at h;unfold fO;rw[h,zg D _ j _ (by simpa using g) a.le,zg D _ j _ (by simpa using d) a.le]
lemma jy{n:Nat}{D:qD}(c:q0 n D)(x:tX n)(f:Nat->Bool)(a:∀i (h:i<n),f i=x ⟨i,h⟩)(d:∀j,j<(tD D)->f (n+j)=xp (gZ D j) (f (yx D j)) (f (yf D j))):∀w,w<n+(tD D)->fO D x w=f w:=by intro w;induction w using sI with|_ w ih=>{intro q;by_cases l:w<n;{rw[qa D x w l,a w l]};{obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have g:j<(tD D):=by{omega};obtain⟨p,m,-⟩:=c j g;rw[qu c x j g,d j g,ih _ p (by omega),ih _ m (by omega)]}}
abbrev ko:=Bool ⊕ Nat
def qv(W:tL):ko->Bool
 | inl b=>b
 | inr k=>W.getD k p55
def wz(m:List ko)(i:Nat):ko:=m.getD i (inl p55)
def wf(t:Bool):ko->ko->ko ⊕ (Nat×Nat)
 | inl a,r=>inl (if a=t then r else inl a)
 | inr i,inl b=>inl (if b=t then inr i else inl b)
 | inr i,inr j=>if i=j then inl (inr i) else inr (i,j)
def w9:GateOp->Bool
 | GateOp.and=>p63
 | _=>p55
def qi(n:Nat)(st:List ko×qD)(g:Gate):List ko×qD:=match g.inputs with|[]=>(st.1++[inl (w9 g.op)],st.2)|[a]=>(st.1++[wz st.1 a],st.2)|a::b::_=>match wf (w9 g.op) (wz st.1 a) (wz st.1 b) with|inl r=>(st.1++[r],st.2)|inr p=>(st.1++[inr (n+st.2.length)],st.2++[(w9 g.op,p.1,p.2)])
def jp(B:Nat):ko->Prop
 | inl _=>True
 | inr k=>k<B
def v6(n:Nat)(st:List ko×qD):Prop:=q0 n st.2/\∀r∈st.1,jp (n+st.2.length) r
lemma xg{B a:Nat}(h:B<=a)(r:ko)(c:jp B r):jp a r:=by rcases r with b|k;{trivial};{exact lL c h}
lemma yg(W:tL)(m:List ko)(i:Nat):qv W (wz m i)=(m.map (qv W)).getD i p55:=by simp only[wz,p3,p6];cases m[i]?<;>rfl
lemma zh(B:Nat)(m:List ko)(a:∀r∈m,jp B r)(i:Nat):jp B (wz m i):=by simp only[wz,p3];rcases h:m[i]? with _|r;{trivial};{exact a r (List.mem_of_getElem? h)}
lemma vs(W:tL)(g:tG)(r:ko)(a:jp W.length r):qv (zp W g) r=qv W r:=by rcases r with b|k;{rfl};{exact jo W g k a}
lemma x5(t:Bool)(W:tL)(a b r:ko)(h:wf t a b=inl r):qv W r=xp t (qv W a) (qv W b):=by rcases a with a|i;{simp only[wf,hF] at h;subst h;cases t<;>cases a<;>simp[qv]};{rcases b with b|j;{simp only[wf,hF] at h;subst h;cases t<;>cases b<;>simp[qv]};{simp only[wf] at h;split_ifs at h with hij;simp only[hF] at h;subst h;subst hij;cases t<;>simp[qv]}}
lemma xh(B:Nat)(t:Bool)(a b r:ko)(c:jp B a)(d:jp B b)(h:wf t a b=inl r):jp B r:=by rcases a with a|i;{simp only[wf,hF] at h;subst h;split_ifs;{exact d};{trivial}};{rcases b with b|j;{simp only[wf,hF] at h;subst h;split_ifs;{exact c};{trivial}};{simp only[wf] at h;split_ifs at h;simp only[hF] at h;subst h;exact c}}
lemma x6(t:Bool)(a b:ko)(p:Nat×Nat)(h:wf t a b=inr p):a=inr p.1/\b=inr p.2/\p.1≠p.2:=by rcases a with a|i;{simp[wf] at h};{rcases b with b|j;{simp[wf] at h};{simp only[wf] at h;split_ifs at h with hij;cases h;exact⟨rfl,rfl,hij⟩}}
section
variable (op:GateOp)(a:op∈({GateOp.and,GateOp.or}:Set GateOp))
include op a
lemma xz :op.eval []=w9 op:=by rcases a with rfl|rfl<;>rfl
lemma b3(u:Bool):op.eval [u]=u:=by rcases a with rfl|rfl<;>simp[GateOp.eval]
lemma x7(u v:Bool):op.eval [u,v]=xp (w9 op) u v:=by rcases a with rfl|rfl<;>simp[GateOp.eval,w9]
end
lemma v7(D E:qD)(k:Nat)(h:k<(tD D)):(D++E).getD k (p55,0,0)=D.getD k (p55,0,0):=by simp[p4 h]
lemma kp(D:qD)(g:tG):(D++[g]).getD (tD D) (p55,0,0)=g:=by simp[]
lemma vz{n:Nat}{D:qD}(d:q0 n D)(t:Bool)(i j:Nat)(c:i<n+(tD D))(a:j<n+(tD D))(l:i≠j):q0 n (D++[(t,i,j)]):=by intro k m;simp only[lA,p9] at m;by_cases h:k<(tD D);{simp only[yx,yf,v7 D _ k h];exact d k h};{have g:k=(tD D):=by{omega};subst g;simp only[yx,yf,kp];exact⟨c,a,l⟩}
lemma k1{n:Nat}{D:qD}(a:q0 n D)(k:Nat):q0 n (D.take k):=by intro j g;simp only[p10] at g;have d:j<k:=by{omega};have c:j<(tD D):=by{omega};have e:(D.take k).getD j (p55,0,0)=D.getD j (p55,0,0):=by{simp[d]};simp only[yx,yf,e];exact a j c
lemma kq(n:Nat)(st:List ko×qD)(g:Gate)(d:g.op∈({GateOp.and,GateOp.or}:Set GateOp)/\g.inputs.length<=2)(h:v6 n st):v6 n (qi n st g)/\(qi n st g).2.length<=st.2.length+1/\∀(x:tX n) (w:tL),st.1.map (qv (wl st.2 (oF x)))=w->(qi n st g).1.map (qv (wl (qi n st g).2 (oF x)))=w++[g.op.eval (g.inputs.map λ i=>w.getD i p55)]:=by obtain⟨m,D⟩:=st;obtain⟨op,L⟩:=g;obtain⟨q,v⟩:=d;obtain⟨J,l⟩:=h;dsimp only at J l q v ⊢;rcases L with _|⟨a,_|⟨b,_|⟨c,P⟩⟩⟩;{exact⟨⟨J,λ r j=>by{simp only[qi,g6,lS] at j;rcases j with j|rfl;exact l r j;trivial}⟩,by simp[qi],λ x w y=>by{subst y;simp only[qi,p11,p12,p13,qv,xz op q]}⟩};{exact⟨⟨J,λ r j=>by{simp only[qi,g6,lS] at j;rcases j with j|rfl;exact l r j;exact zh _ m l a}⟩,by simp[qi],λ x w y=>by{subst y;simp only[qi,p11,p12,p13,b3 op q,yg]}⟩};{have H:=zh _ m l a;have z:=zh _ m l b;rcases hc:wf (w9 op) (wz m a) (wz m b) with r|p;{exact⟨⟨by simpa only[qi,hc] using J,λ K j=>by{simp only[qi,hc,g6,lS] at j ⊢;rcases j with j|rfl;exact l K j;exact xh _ _ _ _ _ H z hc}⟩,by simp[qi,hc],λ x w y=>by{subst y;simp only[qi,hc,p11,p12,p13,x7 op q,x5 _ (wl D (oF x)) _ _ _ hc,yg]}⟩};{obtain⟨R,Q,M⟩:=x6 _ _ _ _ hc;rw[R] at H;rw[Q] at z;exact⟨⟨by simpa only[qi,hc] using vz J (w9 op) p.1 p.2 H z M,λ K j=>by{simp only[qi,hc,g6,lS,lA,p9] at j ⊢;rcases j with j|rfl;exact xg (by omega) K (l K j);show n+(tD D)<n+((tD D)+1);omega}⟩,by simp[qi,hc],λ x w y=>by{subst y;have u:=jk D (oF x);rw[p8] at u;have hW':wl (D++[(w9 op,p.1,p.2)]) (oF x)=zp (wl D (oF x)) (w9 op,p.1,p.2):=by{rw[vi];rfl};have X:m.map (qv (zp (wl D (oF x)) (w9 op,p.1,p.2)))=m.map (qv (wl D (oF x))):=List.map_congr_left (λ r j=>vs _ _ r (u.symm▸l r j));have U:(zp (wl D (oF x)) (w9 op,p.1,p.2)).getD (n+(tD D)) p55=xp (w9 op) ((m.map (qv (wl D (oF x)))).getD a p55) ((m.map (qv (wl D (oF x)))).getD b p55):=by{rw[<-u,zq,<-yg,<-yg,R,Q];rfl};simp only[qi,hc,hW',p11,p12,p13,X,qv,U,x7 op q]}⟩}};{simp at v}
lemma kr(n:Nat)(a:List Gate)(c:∀g∈a,g.op∈({GateOp.and,GateOp.or}:Set GateOp)/\g.inputs.length<=2):∀st:List ko×qD,v6 n st->v6 n (a.foldl (qi n) st)/\(a.foldl (qi n) st).2.length<=st.2.length+a.length/\∀(x:tX n) (w:tL),st.1.map (qv (wl st.2 (oF x)))=w->(a.foldl (qi n) st).1.map (qv (wl (a.foldl (qi n) st).2 (oF x)))=a.foldl (λ w g=>w++[g.op.eval (g.inputs.map λ i=>w.getD i p55)]) w:=by induction a with|nil=>{exact λ st h=>⟨h,by simp,λ _ _ d=>d⟩}|cons g a ih=>{intro st h;obtain⟨q,v,p⟩:=kq n st g (c g (by simp)) h;obtain⟨m,u,l⟩:=ih (λ r j=>c r (by simp[j])) _ q;exact⟨m,by{simp only[lO,List.length_cons];omega},λ x w d=>by{simp only[lO];exact l x _ (p x w d)}⟩}
lemma b7(n:Nat)(x:tX n):((p20 n).map inr).map (qv (wl ([]:qD) (oF x)))=oF x:=by apply List.ext_getElem;{simp};{intro i a c;simp only[List.length_map,List.length_range] at a;simp[qv,wl,a]}
lemma z3{n:Nat}(C:Circuit)(a:Monotone2 C):(∃b:Bool,∀x:tX n,C.eval (oF x)=b)\/(∃i:Fin n,∀x:tX n,C.eval (oF x)=x i)\/(∃D:qD,q0 n D/\D≠[]/\(tD D)<=C.size/\∀x:tX n,fO D x (qb n D)=C.eval (oF x)):=by obtain⟨⟨v,l⟩,d,c⟩:=kr n C.gates a ((p20 n).map inr,([]:qD)) ⟨λ j z=>absurd z (by simp),λ r g=>by{simp only[p16,p17] at g;obtain⟨k,hk,rfl⟩:=g;simpa[jp] using hk}⟩;generalize C.gates.foldl (qi n) ((p20 n).map inr,([]:qD))=st at v l d c;obtain⟨m,D⟩:=st;dsimp only at v l d c;have p:∀x:tX n,C.eval (oF x)=qv (wl D (oF x)) (wz m C.output):=λ x=>by{rw[yg,c x (oF x) (b7 n x)];rfl};have hk:=zh _ m l C.output;rcases g:wz m C.output with b|k;{exact .inl ⟨b,λ x=>by{rw[p x,g];rfl}⟩};{rw[g] at hk;have hk':k<n+(tD D):=hk;by_cases q:k<n;{exact .inr (.inl ⟨⟨k,q⟩,λ x=>by{rw[p x,g];exact qa D x k q}⟩)};{have u:(D.take (k-n+1)).length=k-n+1:=by{rw[p10];omega};exact .inr (.inr ⟨D.take (k-n+1),k1 v _,λ h=>by{rw[h] at u;simp at u},by{simp only[List.length_nil,Nat.zero_add] at d;unfold Circuit.size;omega},λ x=>by{have y:qb n (D.take (k-n+1))=k:=by{unfold qb;rw[u];omega};rw[y,xx D x (k-n+1) k (by omega) (by omega),p x,g];rfl}⟩)}}
lemma zi{D:qD}{w:Nat}(h:fanout D w=0)(j:Nat)(a:j<(tD D)):yx D j≠w/\yf D j≠w:=by unfold fanout qg at h;rw[g8,gI] at h;have:=h (mR.2 a);tauto
def v8(c a:Nat):Nat:=if c<a then a-1 else a
def qw(c w:Nat):Nat:=if w<c then w else w+1
def y0(n j:Nat)(D:qD):qD:=(D.eraseIdx j).map (λ g=>(g.1,v8 (n+j) g.2.1,v8 (n+j) g.2.2))
lemma yb(n j:Nat)(D:qD)(a:j<(tD D)):(y0 n j D).length=(tD D)-1:=by simp[y0,List.length_eraseIdx,a]
lemma k2(n j:Nat)(D:qD)(k:Nat)(c:qw j k<(tD D)):gZ (y0 n j D) k=gZ D (qw j k)/\yx (y0 n j D) k=v8 (n+j) (yx D (qw j k))/\yf (y0 n j D) k=v8 (n+j) (yf D (qw j k)):=by have e:(y0 n j D).getD k (p55,0,0)=((D.getD (qw j k) (p55,0,0)).1,v8 (n+j) (D.getD (qw j k) (p55,0,0)).2.1,v8 (n+j) (D.getD (qw j k) (p55,0,0)).2.2):=by{simp only[y0,p3,p6,List.getElem?_eraseIdx];unfold qw at c ⊢;split_ifs at c ⊢<;>simp[p5 c]};unfold gZ yx yf;rw[e];exact⟨rfl,rfl,rfl⟩
section
variable {n:Nat}{D:qD}(g:q0 n D)(j:Nat)(c:j<(tD D))(d:fanout D (n+j)=0)
include n D g j c d
lemma jq :q0 n (y0 n j D):=by intro k u;rw[yb n j D c] at u;have hk':qw j k<(tD D):=by{unfold qw;split_ifs<;>omega};have h:(k<j/\qw j k=k)\/(j<=k/\qw j k=k+1):=by{unfold qw;split_ifs<;>omega};obtain⟨r,q,i⟩:=g _ hk';obtain⟨ra,p⟩:=zi d _ hk';obtain⟨-,m,l⟩:=k2 n j D k hk';rw[m,l];generalize qw j k=k' at *;generalize yx D k'=a at *;generalize yf D k'=b at *;refine⟨?_,?_,?_⟩<;>unfold v8<;>split_ifs<;>omega
lemma xi(x:tX n)(w:Nat)(h:w<n+((tD D)-1)):fO (y0 n j D) x w=fO D x (qw (n+j) w):=by refine jy (jq g j c d) x (λ u=>fO D x (qw (n+j) u)) (λ i l=>by{show fO D x (qw (n+j) i)=_;rw[show qw (n+j) i=i by{unfold qw;split_ifs<;>omega}];exact qa D x i l}) (λ k y=>by{rw[yb n j D c] at y;have hk':qw j k<(tD D):=by{unfold qw;split_ifs<;>omega};obtain⟨q,v,r⟩:=k2 n j D k hk';obtain⟨ra,p⟩:=zi d _ hk';have m:∀a,a≠n+j->qw (n+j) (v8 (n+j) a)=a:=λ a z=>by{unfold qw v8;split_ifs<;>omega};show fO D x (qw (n+j) (n+k))=_;rw[show qw (n+j) (n+k)=n+qw j k by{unfold qw;split_ifs<;>omega},q,v,r,m _ ra,m _ p];exact qu g x _ hk'}) w (by{rw[yb n j D c];exact h})
end
section
variable {n:Nat}(F:(tX n)->Bool)(a:∀i:Fin n,∃x y:tX n,(∀k,k≠i->x k=y k)/\F x≠F y)
include n F a
lemma x8 :∀(s:Nat) (D:qD),(tD D)=s->q0 n D->D≠[]->(∀x:tX n,fO D x (qb n D)=F x)->∃D':qD,fV n D'/\D'.length<=s/\∀x:tX n,fO D' x (qb n D')=F x:=by intro s;induction s using sI with|_ s ih=>{intro D r z q K;have Q:0<(tD D):=lP q;by_cases U:b5 n D;{exact⟨D,⟨z,U,q⟩,r.le,K⟩};{obtain⟨w,P,d⟩:∃w,w+1<n+(tD D)/\fanout D w=0:=by_contra λ v=>U (λ w P=>by_contra λ h0=>v ⟨w,P,by omega⟩);by_cases m:w<n;{obtain⟨x,y,L,H⟩:=a ⟨w,m⟩;exact absurd (by{rw[<-K x,<-K y];have p:qb n D≠w:=by{unfold qb;omega};have l:=jy z y (λ u=>if u=w then y ⟨w,m⟩ else fO D x u) (λ i R=>by{by_cases c:i=w;subst c;simp;simp only[c,ite_false];rw[qa D x i R];exact L ⟨i,R⟩ (λ h=>c (congrArg Fin.val h))}) (λ j g=>by{obtain⟨ha,Z⟩:=zi d j g;have M:n+j≠w:=by{omega};simp only[M,ha,Z,ite_false];exact qu z x j g}) (qb n D) (by{unfold qb;omega});simp only[p,ite_false] at l;exact l.symm}) H};{obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have g:j<(tD D):=by{omega};have J:=yb n j D g;obtain⟨D',h1,h2,h3⟩:=ih ((tD D)-1) (by omega) (y0 n j D) J (jq z j g d) (λ h=>by{rw[h] at J;simp at J;omega}) (λ x=>by{have Y:qb n (y0 n j D)=n+((tD D)-1)-1:=by{unfold qb;rw[J]};have X:qw (n+j) (n+((tD D)-1)-1)=qb n D:=by{unfold qw qb;split_ifs<;>omega};rw[Y,xi z j g d x _ (by omega),X];exact K x});exact⟨D',h1,by omega,h3⟩}}}
lemma yt(D:qD)(d:q0 n D)(c:D≠[])(g:∀x:tX n,fO D x (qb n D)=F x):∃D':qD,fV n D'/\D'.length<=(tD D)/\∀x:tX n,fO D' x (qb n D')=F x:=x8 F a (tD D) D rfl d c g
end
lemma zy{n:Nat}(C:Circuit)(a:Monotone2 C)(g:∀b:Bool,∃x:tX n,C.eval (oF x)≠b)(d:∀i:Fin n,∃x:tX n,C.eval (oF x)≠x i)(c:∀i:Fin n,∃x y:tX n,(∀k,k≠i->x k=y k)/\C.eval (oF x)≠C.eval (oF y)):∃D:qD,fV n D/\(tD D)<=C.size/\∀x:tX n,fO D x (qb n D)=C.eval (oF x):=by rcases z3 (n:=n) C a with ⟨b,p⟩|⟨i,m⟩|⟨D,q,j,l,r⟩;{obtain⟨x,h⟩:=g b;exact absurd (p x) h};{obtain⟨x,h⟩:=d i;exact absurd (m x) h};{obtain⟨D',v,z,u⟩:=yt (λ x=>C.eval (oF x)) c D q j r;exact⟨D',v,by omega,u⟩}
section
variable {n:ℕ} {D:qD}
lemma ql{w:Nat}:w∈inner n D↔w+1<n+(tD D):=by unfold inner;rw[mR];omega
lemma qf(j:Nat):fC D (j,p55)=yx D j:=by simp[fC]
lemma qo(j:Nat):fC D (j,p63)=yf D j:=by simp[fC]
lemma qz(a:q0 n D)(w:Nat)(h:n+(tD D)<=w+1):fanout D w=0:=by unfold fanout qg;rw[g8,gI];intro j d;have c:=mR.1 d;have:=a j c;omega
lemma wk(a:q0 n D){w:Nat}(h:1<=fanout D w):w+1<n+(tD D):=by by_contra c;have:=qz a w (by omega);omega
lemma yo(P:tJ->Prop) [DecidablePred P]:((jw D).filter P).card=∑ j∈g5 (tD D),((if P (j,p55) then 1 else 0)+(if P (j,p63) then 1 else 0)):=by rw[p30,jw,Finset.sum_product];refine p51 rfl (λ j _=>?_);rw[Fintype.sum_bool,add_comm]
lemma ks:(jw D).card=2*(tD D):=by simp[jw,Finset.card_product,Nat.mul_comm]
lemma xq(d:q0 n D)(e:tJ)(a:e∈jw D):fC D e+1<n+(tD D):=by obtain⟨j,c⟩:=e;have g:j<(tD D):=by{simpa[jw] using a};have:=d j g;cases c;{rw[qf];omega};{rw[qo];omega}
lemma k3(a:q0 n D)(w:Nat):fanout D w=((jw D).filter (λ e=>fC D e=w)).card:=by rw[yo,fanout,qg,p30];refine p51 rfl (λ j c=>?_);have:=(a j (mR.1 c)).2.2;rw[qf,qo];split_ifs<;>omega
lemma zd(a:q0 n D)(K:tK):∑ w∈K,fanout D w=((jw D).filter (λ e=>fC D e∈K)).card:=by rw[Finset.card_eq_sum_card_fiberwise (f:=fC D) (s:=(jw D).filter (λ e=>fC D e∈K)) (t:=K) (λ e c=>mem_coe.2 (mF.1 (mem_coe.1 c)).2)];refine p51 rfl (λ w d=>by{rw[k3 a,p38];congr 1;ext e;simp only[mF];exact⟨λ⟨c,rfl⟩=>⟨c,d,rfl⟩,λ⟨c,_,h⟩=>⟨c,h⟩⟩})
lemma yp{K:tK}(a:∀w∈K,1<=fanout D w):q6 D K+K.card=∑ w∈K,fanout D w:=by rw[q6,Finset.card_eq_sum_ones,<-p50];exact p51 rfl (λ w c=>Nat.sub_add_cancel (a w c))
lemma vj(h:fV n D):yr n D+n=(tD D)+1:=by obtain⟨d,j,a⟩:=h;have:=lP a;have:=yp (λ w g=>j w (ql.1 g));have:∑ w∈inner n D,fanout D w=2*(tD D):=by{rw[zd d,Finset.filter_true_of_mem (λ e i=>ql.2 (xq d e i)),ks]};have:(inner n D).card=n+(tD D)-1:=Finset.card_range _;unfold yr;omega
lemma jz(n:Nat)(D:qD):yr n D=fJ n D+Bzero n D:=by unfold yr fJ Bzero q6;exact (fS _ _ _).symm
lemma vk(h:fV n D)(w:Nat)(c:w<n+(tD D)):RT (λ a b=>b<n+(tD D)/\n<=b/\(yx D (b-n)=a\/yf D (b-n)=a)) w (qb n D):=by obtain⟨l,m,-⟩:=h;generalize hk:n+(tD D)-w=k;induction k using sI generalizing w with|_ k ih=>{by_cases g:w+1=n+(tD D);{rw[show w=qb n D by{unfold qb;omega}]};{obtain⟨j,i⟩:=fz.1 (m w (by omega));simp only[qg,mF,mR] at i;have:=l j i.1;exact rH (b:=n+j) ⟨by omega,by omega,by simpa using i.2⟩ (ih (n+(tD D)-(n+j)) (by omega) (n+j) (by omega) rfl)}}
lemma w3{v:Fin n}{w:Nat}:v∈fM n D w↔fO D (q9 v) w=p63:=by simp[fM]
lemma x9(c:q0 n D)(x y:tX n)(a:∀i,x i=p63->y i=p63)(w:Nat):fO D x w=p63->fO D y w=p63:=by induction w using sI with|_ w ih=>{by_cases g:w<n;{rw[qa D x w g,qa D y w g];exact a _};{by_cases m:w<n+(tD D);{obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have d:j<(tD D):=by{omega};obtain⟨l,h,-⟩:=c j d;rw[qu c x j d,qu c y j d];have:=ih _ l;have:=ih _ h;cases gZ D j<;>simp only[gop_true,gop_false,bA,bO]<;>tauto};{rw[z0 D x w (by omega)];simp}}}
lemma wc(D:qD)(i:Fin n):fM n D i.1={i}:=by ext v;rw[w3,qa D (q9 v) i.1 i.2];simp[q9,eq_comm]
lemma xn(D:qD)(w:Nat)(h:n+(tD D)<=w):fM n D w=∅:=by ext v;simp[w3,z0 D (q9 v) w h]
lemma yy(c:q0 n D)(j:Nat)(a:j<(tD D)):fM n D (n+j)=if gZ D j=p63 then fM n D (yx D j)∩fM n D (yf D j) else fM n D (yx D j)∪fM n D (yf D j):=by ext v;rw[w3,qu c _ j a];cases gZ D j<;>simp[w3]
lemma v9(h:fV n D)(K:tK)(c:K⊆inner n D)(a:∀j,j<(tD D)->n+j∈K->yx D j∈K\/yf D j∈K):(qc n D K).card+(w5 n D K).card=(z8 n K).card+q6 D K:=by obtain⟨p,q,-⟩:=h;have d:∀w∈K,w+1<n+(tD D):=λ w g=>ql.1 (c g);have J:q6 D K+K.card=((jw D).filter (λ e=>fC D e∈K)).card:=by{rw[<-zd p,yp (λ w g=>q w (d w g))]};have r:=p31 (s:=(jw D).filter (λ e=>fC D e∈K)) (λ e:tJ=>n+e.1∈K);rw[p38,p38] at r;have H:((jw D).filter (λ e=>fC D e∈K/\n+e.1∈K)).card=((g5 (tD D)).filter (λ j=>n+j∈K)).card+(w5 n D K).card:=by{rw[yo,w5,p30,p30,<-p50];refine p51 rfl (λ j l=>?_);have:=a j (mR.1 l);rw[qf,qo];by_cases m:n+j∈K<;>by_cases y:yx D j∈K<;>by_cases v:yf D j∈K<;>simp_all};have z:K.card=(z8 n K).card+((g5 (tD D)).filter (λ j=>n+j∈K)).card:=by{rw[<-p31 (s:=K) (λ w=>w<n),z8];congr 1;have i:K.filter (λ w=>¬w<n)=((g5 (tD D)).filter (λ j=>n+j∈K)).image (λ j=>n+j):=by{ext w;simp only[mF,mG,mR];exact⟨λ⟨g,u⟩=>⟨w-n,⟨by{have:=d w g;omega},by rwa[Nat.add_sub_cancel' (by omega)]⟩,by omega⟩,λ⟨j,⟨_,l⟩,h⟩=>⟨h▸l,by omega⟩⟩};rw[i,p33 _ (add_right_injective n)]};unfold qc;omega
lemma vt(T:tS n)(a:fM n D (qb n D)∩T=∅):q2 n D T⊆inner n D:=by intro w d;simp only[q2,mF,mR] at d;rw[ql];by_contra g;have c:w=qb n D:=by{unfold qb;omega};rw[c,a] at d;exact gk d.2
lemma jl(D:qD)(T:tS n):(z8 n (q2 n D T)).card=T.card:=by have c:z8 n (q2 n D T)=T.image (λ v:Fin n=>v.1):=by{ext w;simp only[z8,q2,mF,mR,mG];constructor;{rintro⟨⟨-,v,a⟩,d⟩;have g:fM n D w={⟨w,d⟩}:=wc D ⟨w,d⟩;rw[g,mI,mS] at a;exact⟨v,a.2,by rw[a.1]⟩};{rintro⟨v,a,rfl⟩;refine⟨⟨by have:=v.2;omega,v,?_⟩,v.2⟩;rw[wc];simp[a]}};rw[c,p33 _ Fin.val_injective]
lemma z4(h:fV n D)(T:tS n)(a:fM n D (qb n D)∩T=∅):(qc n D (q2 n D T)).card+(w5 n D (q2 n D T)).card=T.card+q6 D (q2 n D T):=by rw[<-jl D T];refine v9 h _ (vt T a) (λ j g i=>by{obtain⟨m,l,-⟩:=h.1 j g;simp only[q2,mF,mR] at i ⊢;obtain⟨v,c⟩:=i.2;rw[mI,yy h.1 j g] at c;split_ifs at c with ht;{rw[mI] at c;exact .inl ⟨by omega,v,mI.2 ⟨c.1.1,c.2⟩⟩};{rw[mN] at c;exact c.1.elim (λ d=>.inl ⟨by omega,v,mI.2 ⟨d,c.2⟩⟩) (λ d=>.inr ⟨by omega,v,mI.2 ⟨d,c.2⟩⟩)}})
lemma va(h:fV n D)(x y:Fin n)(c:x≠y)(a:x∉fM n D (qb n D)):(qc n D (q4 n D x y)).card+(w5 n D (q4 n D x y)).card=1+q6 D (q4 n D x y):=by have m:q4 n D x y⊆inner n D:=λ w i=>by{simp only[q4,mF,mR] at i;rw[ql];by_contra r;have:w=qb n D:=by{unfold qb;omega};exact a (this▸i.2.1)};have p:z8 n (q4 n D x y)={x.1}:=by{ext w;simp only[z8,q4,mF,mR,mS];exact⟨λ⟨⟨_,d,_⟩,i⟩=>by{rw[wc D ⟨w,i⟩,mS] at d;rw[d]},λ h=>h▸⟨⟨by{have:=x.2;omega},by{rw[wc];exact m0 x},by{rw[wc,mS];exact λ r=>c r.symm}⟩,x.2⟩⟩};have q:=v9 h _ m (λ j v z=>by{obtain⟨K,J,-⟩:=h.1 j v;simp only[q4,mF,mR] at z ⊢;obtain⟨-,d,g⟩:=z;rw[yy h.1 j v] at d g;split_ifs at d g with ht;{rw[mI] at d g;exact if l:y∈fM n D (yx D j) then .inr ⟨by omega,d.2,λ r=>g ⟨l,r⟩⟩ else .inl ⟨by omega,d.1,l⟩};{rw[mN] at d g;exact d.elim (λ u=>.inl ⟨by omega,u,λ r=>g (.inl r)⟩) (λ u=>.inr ⟨by omega,u,λ r=>g (.inr r)⟩)}});rwa[p,fw] at q
lemma xr{u:U0}:u∈units n D↔u.1∈inner n D/\u.2+1<fanout D u.1:=by rw[units,p44,mR];constructor<;>rintro⟨a,c⟩<;>exact⟨a,by omega⟩
lemma wh(n:Nat)(D:qD)(p:Nat->Prop) [DecidablePred p]:((units n D).filter (λ u=>p u.1)).card=q6 D ((inner n D).filter p):=by have a:(units n D).filter (λ u=>p u.1)=((inner n D).filter p).sigma (λ w=>g5 (fanout D w-1)):=by{ext u;simp only[units,mF,p44];tauto};rw[a,Finset.card_sigma,q6];simp
lemma k4(n:Nat)(D:qD):(ww n D).card=fJ n D:=by unfold ww fJ;exact wh n D (λ w=>(fM n D w).Nonempty)
lemma zz{v:Fin n}:v∈fX n D↔∃w,2<=fanout D w/\v∈fM n D w:=by simp only[fX,kl,mem_biUnion,mF,mR];constructor;{rintro⟨w,⟨-,c⟩,a⟩;exact⟨w,c,a⟩};{rintro⟨w,c,a⟩;refine⟨w,⟨?_,c⟩,a⟩;by_contra d;rw[xn D w (by omega)] at a;exact nE v a}
lemma zb{v:Fin n}:v∈ineligSet n D↔∀w,v∈fM n D w->fanout D w<=1:=by rw[ineligSet,mD,zz];constructor;{rintro⟨-,h⟩ w a;by_contra d;exact h ⟨w,by omega,a⟩};{intro h;refine⟨mU v,?_⟩;rintro⟨w,a,c⟩;have:=h w c;omega}
lemma wg{v:Fin n}{T:tS n}:(({v}:tS n)∩T).Nonempty↔v∈T:=by constructor;{rintro⟨u,a⟩;rw[mI,mS] at a;exact a.1▸a.2};{intro h;exact⟨v,mI.2 ⟨m0 v,h⟩⟩}
lemma zr(b:tY n)(a:gN n D b):Set.InjOn (λ v=>(⟨b v,0⟩:U0)) (fX n D:Set (Fin n)):=by intro v i g c j;have d:b v=b g:=congrArg Sigma.fst j;have h:=(a v i).2;rw[d,(a g c).2] at h;exact (p48 h).symm
lemma yl(c:q0 n D)(b:tY n)(a:gN n D b):qh n D b⊆ww n D:=by intro u g;obtain⟨v,d,rfl⟩:=mG.1 g;obtain⟨j,h⟩:=a v d;have i:1<=fanout D (b v):=by{omega};rw[ww,mF,xr];refine⟨⟨ql.2 (wk c i),?_⟩,?_⟩;{show 0+1<fanout D (b v);omega};{show (fM n D (b v)).Nonempty;rw[h];exact Finset.singleton_nonempty v}
lemma ke(b:tY n)(a:gN n D b):(qh n D b).card=(fX n D).card:=p32 (zr b a)
lemma kf(c:q0 n D)(b:tY n)(a:gN n D b):(residualUnits n D b).card+(fX n D).card=fJ n D:=by rw[<-ke b a,<-k4];exact p35 (yl c b a)
lemma jm(c:q0 n D)(b:tY n)(a:gN n D b)(T:tS n):q6 D (q2 n D T)=(T∩fX n D).card+((residualUnits n D b).filter (λ u=>(fM n D u.1∩T).Nonempty)).card:=by have H:q6 D (q2 n D T)=((units n D).filter (λ u=>(fM n D u.1∩T).Nonempty)).card:=by{rw[wh n D (λ w=>(fM n D w∩T).Nonempty)];symm;refine sum_subset (λ w g=>by{rw[mF] at g;have:=ql.1 g.1;exact mF.2 ⟨mR.2 (by omega),g.2⟩}) (λ w g j=>by{rw[q2,mF] at g;have m:w∉inner n D:=λ hc=>j (mF.2 ⟨hc,g.2⟩);rw[ql] at m;simp[qz c w (by omega)]})};have z:(units n D).filter (λ u=>(fM n D u.1∩T).Nonempty)=(qh n D b).filter (λ u=>(fM n D u.1∩T).Nonempty)∪(residualUnits n D b).filter (λ u=>(fM n D u.1∩T).Nonempty):=by{ext u;have i:=yl c b a;simp only[residualUnits,ww,mN,mF,mD];exact⟨λ d=>if p:u∈qh n D b then .inl ⟨p,d.2⟩ else .inr ⟨⟨⟨d.1,d.2.mono fI⟩,p⟩,d.2⟩,λ | .inl d=>⟨(mF.1 (i d.1)).1,d.2⟩ | .inr d=>⟨d.1.1.1,d.2⟩⟩};have r:(qh n D b).filter (λ u=>(fM n D u.1∩T).Nonempty)=(T∩fX n D).image (λ v=>(⟨b v,0⟩:U0)):=by{rw[qh,Finset.filter_image];congr 1;ext v;simp only[mF,mI];exact⟨λ⟨h,l⟩=>⟨by rwa[(a v h).2,wg] at l,h⟩,λ⟨q,h⟩=>⟨h,by rwa[(a v h).2,wg]⟩⟩};rw[H,z,fU (Finset.disjoint_filter_filter (show Disjoint (qh n D b) (residualUnits n D b) from Finset.disjoint_sdiff)),r,p32 ((zr b a).mono (Finset.coe_subset.2 p40))]
end
def gL{n:Nat}(a:EP (Fin n))(w:Nat):Nat:=if h:w<n then (a ⟨w,h⟩).1 else w
def relabel {n:Nat}(a:EP (Fin n))(D:qD):qD:=D.map (λ g=>(g.1,gL a g.2.1,gL a g.2.2))
section
variable {n:Nat}(a:EP (Fin n))
include n a
lemma yh{w:Nat}(h:w<n):gL a w=(a ⟨w,h⟩).1:=by simp[gL,h]
lemma qt{w:Nat}(h:n<=w):gL a w=w:=by simp[gL,p25.2 h]
lemma qy{m:Nat}(c:n<=m)(w:Nat):gL a w<m↔w<m:=by by_cases h:w<n;{rw[yh a h];have:=(a ⟨w,h⟩).2;constructor<;>intro<;>omega};{rw[qt a (p25.1 h)]}
lemma yz(w:Nat):gL a⁻¹ (gL a w)=w:=by by_cases h:w<n;{rw[yh a h,yh a⁻¹ (a ⟨w,h⟩).2];simp};{rw[qt a (p25.1 h),qt a⁻¹ (p25.1 h)]}
lemma tr_liftP_inv'(w:Nat):gL a (gL a⁻¹ w)=w:=by simpa using yz a⁻¹ w
end
lemma tr_liftP_inj{n:Nat}(c:EP (Fin n)){a b:Nat}:gL c a=gL c b↔a=b:=by refine⟨λ h=>?_,congrArg _⟩;have:=congrArg (gL c⁻¹) h;rwa [yz,yz] at this
lemma relabel_length{n:Nat}(a:EP (Fin n))(D:qD):(relabel a D).length=(tD D):=by simp[relabel]
lemma ba{n:Nat}(c:EP (Fin n))(D:qD)(j:Nat)(a:j<(tD D)):gZ (relabel c D) j=gZ D j:=by rw[xd _ j (by rw[relabel_length];exact a),xd D j a];simp[relabel]
section
variable {n:Nat}(a:EP (Fin n))
include n a
lemma kt(D:qD)(j:Nat)(c:j<(tD D)):yx (relabel a D) j=gL a (yx D j):=by rw[xe _ j (by rw[relabel_length];exact c),xe D j c];simp[relabel]
lemma ku(D:qD)(j:Nat)(c:j<(tD D)):yf (relabel a D) j=gL a (yf D j):=by rw[xf _ j (by rw[relabel_length];exact c),xf D j c];simp[relabel]
lemma j3{D:qD}(c:q0 n D):q0 n (relabel a D):=by intro j d;rw[relabel_length] at d;obtain⟨l,i,g⟩:=c j d;rw[kt a D j d,ku a D j d];exact⟨(qy a (nL n j) _).2 l,(qy a (nL n j) _).2 i,λ h=>g ((tr_liftP_inj a).1 h)⟩
lemma fH{D:qD}(c:q0 n D)(x:tX n)(w:Nat):fO (relabel a D) x (gL a w)=fO D (λ i=>x (a i)) w:=by by_cases h:w<n+(tD D);{refine (jy (j3 a c) x (λ l=>fO D (λ i=>x (a i)) (gL a⁻¹ l)) (λ i g=>by{show fO D (λ i=>x (a i)) (gL a⁻¹ i)=x ⟨i,g⟩;rw[yh a⁻¹ g,qa D _ _ (a⁻¹ ⟨i,g⟩).2];simp}) (λ j d=>by{rw[relabel_length] at d;show fO D (λ i=>x (a i)) (gL a⁻¹ (n+j))=_;rw[qt a⁻¹ (nL n j),ba a D j d,kt a D j d,ku a D j d,yz,yz,qu c _ j d]}) (gL a w) (by{rw[relabel_length];exact (qy a (nL _ _) w).2 h})).trans (by{show fO D (λ i=>x (a i)) (gL a⁻¹ (gL a w))=_;rw[yz]})};{have hw':=p25.1 h;rw[qt a (le_trans (nL _ _) hw'),z0 _ _ _ (by{rw[relabel_length];exact hw'}),z0 _ _ _ hw']}
lemma wa(D:qD)(w:Nat):fanout (relabel a D) (gL a w)=fanout D w:=by unfold fanout qg;rw[relabel_length];congr 1;apply filter_congr;intro j c;have hj':=mR.1 c;rw[kt a D j hj',ku a D j hj',tr_liftP_inj,tr_liftP_inj]
lemma kv{D:qD}(c:b5 n D):b5 n (relabel a D):=by rcases eq_or_ne D [] with rfl|g;{exact c};{intro d j;rw[relabel_length] at j;have i:=lP g;rw[<-tr_liftP_inv' a d,wa];apply c;by_cases h:d<n;{have:=(qy a⁻¹ le_rfl d).2 h;omega};{rw[qt a⁻¹ (p25.1 h)];exact j}}
lemma relabel_strictLive{D:qD}(h:fV n D):fV n (relabel a D):=⟨j3 a h.1,kv a h.2.1,by simpa[relabel] using h.2.2⟩
lemma xa{D:qD}(d:q0 n D)(c:D≠[])(x:tX n):fO (relabel a D) x (qb n (relabel a D))=fO D (λ i=>x (a i)) (qb n D):=by have g:=lP c;have e:qb n (relabel a D)=gL a (qb n D):=by{rw[qt a (by unfold qb;omega)];simp[qb,relabel_length]};rw[e,fH a d]
lemma k5(v:Fin n):(λ i=>q9 v (a i))=q9 (a⁻¹ v):=by funext i;simp only[q9,decide_eq_decide];constructor;{intro h;rw[<-h];simp};{intro h;rw[h];simp}
end
lemma relabel_supp{n:Nat}(c:EP (Fin n)){D:qD}(d:q0 n D)(w:Nat):fM n (relabel c D) (gL c w)=(fM n D w).image c:=by ext v;simp only[fM,mF,mU,true_and,mG];rw[fH c d,k5];constructor;{intro h;exact⟨c⁻¹ v,h,by simp⟩};{rintro⟨a,g,rfl⟩;simpa using g}
namespace A0r
abbrev rL:=@relabel_length
abbrev rS:=@relabel_supp
abbrev tI:=@tr_liftP_inv'
abbrev gq:=@tr_liftP_inj
end A0r
open A0r
lemma ym{n:Nat}(c:EP (Fin n)){D:qD}(d:q0 n D):fX n (relabel c D)=(fX n D).image c:=by ext v;simp only[fX,mem_biUnion,mG,kl,mF,mR];constructor;{rintro⟨h,⟨hw',g⟩,j⟩;obtain⟨w,rfl⟩:∃w,h=gL c w:=⟨gL c⁻¹ h,(tI c h).symm⟩;rw[rS c d,mG] at j;obtain⟨a,i,rfl⟩:=j;rw[wa] at g;rw[rL,qy c (nL _ _)] at hw';exact⟨a,⟨w,⟨hw',g⟩,i⟩,rfl⟩};{rintro⟨a,⟨w,⟨l,g⟩,i⟩,rfl⟩;refine⟨gL c w,⟨?_,?_⟩,?_⟩;{rw[rL];exact (qy c (nL _ _) w).2 l};{rw[wa];exact g};{rw[rS c d];exact Finset.mem_image_of_mem _ i}}
lemma relabel_ineligSet{n:Nat}(c:EP (Fin n)){D:qD}(d:q0 n D):ineligSet n (relabel c D)=(ineligSet n D).image c:=by ext v;simp only[ineligSet,ym c d,mD,mU,true_and,mG];constructor;{intro h;exact⟨c⁻¹ v,λ i=>h ⟨c⁻¹ v,i,by simp⟩,by simp⟩};{rintro⟨a,l,rfl⟩ ⟨b,j,g⟩;exact l (c.injective g▸j)}
lemma vu(n:Nat)(D:qD):(ineligSet n D).card+(fX n D).card=n:=by have h:=p35 (Finset.subset_univ (fX n D));rw[Finset.card_univ,Fintype.card_fin] at h;exact h
def yi{n:Nat}(G:Fin n->Fin n->Prop)(x:tX n):Prop:=∃u v:Fin n,G u v/\x u=p63/\x v=p63
def gK(n:Nat)(G:Fin n->Fin n->Prop)(D:qD):Prop:=∀x:tX n,fO D x (qb n D)=p63↔yi G x
abbrev sem_Comp:=gK
def w6{n:Nat}(G:Fin n->Fin n->Prop):Prop:=(∀u v,G u v->G v u)/\(∀u,¬G u u)/\(∀v w,v≠w->∃z,G v z/\¬G w z)/\(∀u v,∃a,G u a/\a≠v)
def q5(n:Nat)(D:qD)(a b:Nat):Prop:=b<n+(tD D)/\n<=b/\(yx D (b-n)=a\/yf D (b-n)=a)
def q1{n:Nat}(u z:Fin n):tX n:=λ i=>decide (i=u)||decide (i=z)
def wm{n:Nat}(v:Fin n)(x:tX n):tX n:=λ i=>decide (i=v)||x i
def yc{n:Nat}(A:tS n):tX n:=λ i=>decide (i∈A)
lemma yu{α:Type}{r p:α->α->Prop}(h:∀a b,r a b->p a b){a b:α}(c:RT r a b):RT p a b:=by induction c with|refl=>{exact .refl}|tail _ d ih=>{exact rT ih (h _ _ d)}
section
variable {n:ℕ} {G:Fin n->Fin n->Prop} {D:qD}
lemma jr(v:Fin n)(x:tX n):∀k,k≠v->x k=wm v x k:=by intro k c;simp[wm,c]
lemma vb(v:Fin n)(x:tX n):wm v x v=p63:=by simp[wm]
lemma kg{x:tX n}{u:Fin n}(a:x u=p63):∀i,q9 u i=p63->x i=p63:=by intro i c;simp only[q9,dT] at c;rw[c];exact a
lemma q3(d:q0 n D){u:Fin n}{w:Nat}(c:u∈fM n D w){x:tX n}(a:x u=p63):fO D x w=p63:=x9 d (q9 u) x (kg a) w (w3.1 c)
lemma wx{v:Fin n}{w:Nat}(a:v∈fM n D w):w<n+(tD D):=by by_contra c;rw[xn D w (by omega)] at a;exact nE v a
section
variable (Q:q0 n D){j:Nat}(A:j<(tD D))
include Q j A
lemma qm(d:gZ D j=p63):fM n D (n+j)=fM n D (yx D j)∩fM n D (yf D j):=by rw[yy Q j A];simp[d]
lemma yj(d:gZ D j=p55):fM n D (n+j)=fM n D (yx D j)∪fM n D (yf D j):=by rw[yy Q j A];simp[d]
lemma sem_supp_and_sub(d:gZ D j=p63)(s:Bool):fM n D (n+j)⊆fM n D (fC D (j,s)):=by rw[qm Q A d];cases s;{rw[qf];exact fI};{rw[qo];exact p40}
lemma w7(s:Bool):fC D (j,s)<n+j:=by obtain⟨g,d,-⟩:=Q j A;cases s;{rw[qf];exact g};{rw[qo];exact d}
lemma xj(s:Bool):fC D (j,s)≠fC D (j,!s):=by obtain⟨-,-,d⟩:=Q j A;cases s;{simpa[fC] using d};{simpa[fC] using d.symm}
end
lemma qs{j:Nat}(a:j<(tD D))(s:Bool):q5 n D (fC D (j,s)) (n+j):=by refine⟨by omega,by omega,?_⟩;rw[nA];cases s;{exact .inl (qf j).symm};{exact .inr (qo j).symm}
lemma y3{a b:Nat}:q5 n D a b↔∃j s,j<(tD D)/\b=n+j/\fC D (j,s)=a:=by constructor;{rintro⟨h,g,c|c⟩;{exact⟨b-n,p55,by omega,by omega,by rw[qf];exact c⟩};{exact⟨b-n,p63,by omega,by omega,by rw[qo];exact c⟩}};{rintro⟨j,s,d,rfl,rfl⟩;refine⟨by omega,by omega,?_⟩;rw[nA];cases s;{exact .inl (qf j).symm};{exact .inr (qo j).symm}}
lemma wb(c:q0 n D){a b:Nat}(h:q5 n D a b):a<b:=by obtain⟨i,g,d⟩:=h;have:=c (b-n) (by omega);omega
lemma wr{a c:Nat}(h:q5 n D a c):c-n∈qg D a:=by unfold qg;rw[mF,mR];exact⟨by have:=h.1;have:=h.2.1;omega,h.2.2⟩
lemma zs{a c:Nat}(h:q5 n D a c):1<=fanout D a:=fz.2 ⟨_,wr h⟩
lemma qj{a c h:Nat}(g:q5 n D a c)(d:q5 n D a h)(i:fanout D a=1):c=h:=by have l:=wr g;have j:=wr d;obtain⟨r,m⟩:=p29.1 (show (qg D a).card=1 from i);rw[m,mS] at l j;have:=g.2.1;have:=d.2.1;omega
lemma wn(g:q0 n D)(x y:tX n)(v:Fin n)(d:∀k,k≠v->x k=y k)(w:Nat)(c:fO D x w≠fO D y w):RT (λ a b=>q5 n D a b/\fO D x b≠fO D y b) v.1 w:=by induction w using sI with|_ w ih=>{by_cases l:w<n;{rw[qa D x w l,qa D y w l] at c;have i:(⟨w,l⟩:Fin n)=v:=by_contra λ hc=>c (d _ hc);rw[<-i]};{by_cases h:w<n+(tD D);{obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have m:j<(tD D):=by{omega};obtain⟨z,u,-⟩:=g j m;have q:=c;rw[qu g x j m,qu g y j m] at q;by_cases r:fO D x (yx D j)=fO D y (yx D j);exact rT (ih _ u λ p=>q (by rw[r,p])) ⟨⟨h,by omega,.inr (by rw[nA])⟩,c⟩;exact rT (ih _ z r) ⟨⟨h,by omega,.inl (by rw[nA])⟩,c⟩};{exact absurd (by rw[z0 D x w (by omega),z0 D y w (by omega)]) c}}}
def kw(n:Nat)(D:qD)(b v:Nat):Prop:=b=v\/¬RT (λ a c=>q5 n D a c/\c≠b) v (qb n D)
lemma k6(j:q0 n D)(x y:tX n)(v:Fin n)(g:∀k,k≠v->x k=y k)(b:Nat)(d:kw n D b v.1)(i:fO D x b=fO D y b):fO D x (qb n D)=fO D y (qb n D):=by by_contra m;rcases d with rfl|d;{rw[qa D x _ v.2,qa D y _ v.2] at i;exact m (congrArg (λ f=>fO D f (qb n D)) (funext λ k=>if hk:k=v then hk▸i else g k hk))};{exact d (yu (λ _ _ h=>⟨h.1,λ hc=>h.2 (hc▸i)⟩) (wn j x y v g _ m))}
def q7(n:Nat)(D:qD)(a b:Nat):Prop:=RT (λ a c=>q5 n D a c/\fanout D a=1) a b
lemma wp(d:q0 n D){v b:Nat}(h:q7 n D v b):kw n D b v:=by induction h using rI with|refl=>{exact .inl rfl}|@head a c g _ ih=>{by_cases m:b=a;{exact .inl m};{right;intro q;rcases rC q with j|⟨r,p,i⟩;{have y:=qz d a (by rw[j];unfold qb;omega);have u:=g.2;omega};{have l:c=r:=qj g.1 p.1 g.2;subst l;rcases ih with rfl|ih;{exact p.2 rfl};{exact ih i}}}}
lemma z9(a:q0 n D)(v:Fin n):∀w,v∈fM n D w->(∀u,u<w->v∈fM n D u->fanout D u<=1)->q7 n D v.1 w:=by intro w;induction w using sI with|_ w ih=>{intro h d;by_cases p:w<n;{have:=wc D ⟨w,p⟩;rw[this,mS] at h;rw[h];exact .refl};{have r:=wx h;obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have m:j<(tD D):=by{omega};have g:∀s:Bool,v∈fM n D (fC D (j,s))->q7 n D v.1 (n+j):=λ s i=>by{have c:q5 n D (fC D (j,s)) (n+j):=qs m s;have hlt':=w7 a m s;have:=zs c;have:=d _ hlt' i;exact rT (ih _ hlt' i (λ u y=>d u (by omega))) ⟨c,by omega⟩};rw[yy a j m] at h;split_ifs at h with ht;exact g p55 (by{rw[qf];exact (mI.1 h).1});rcases mN.1 h with l|l;exact g p55 (by{rw[qf];exact l});exact g p63 (by{rw[qo];exact l})}}
lemma wd(d:w6 G)(v:Fin n):¬yi G (q9 v):=by rintro⟨a,c,g,h,hc⟩;simp only[q9,dT] at h hc;rw[h,hc] at g;exact d.2.1 _ g
lemma yv{u v:Fin n}(a:G u v):yi G (q1 u v):=⟨u,v,a,by simp[q1],by simp[q1]⟩
lemma qn(a:w6 G)(c:gK n G D):fM n D (qb n D)=∅:=fE.2 (λ v d=>wd a v ((c _).1 (w3.1 d)))
lemma yw(i:w6 G)(g:q0 n D)(h:gK n G D)(v:Fin n)(b:Nat)(d:kw n D b v.1):fM n D b⊆{v}:=by intro u M;rw[mS];by_contra L;obtain⟨p,l,q,-⟩:=i;obtain⟨z,K,m⟩:=q v u (Ne.symm L);have r:=k6 g _ _ v (jr v (q1 u z)) b d (by rw[q3 g M (by simp[q1]),q3 g M (by simp[wm,q1])]);have P:=(h (wm v (q1 u z))).2 ⟨v,z,K,vb v _,by simp[wm,q1]⟩;rw[<-r] at P;obtain⟨a,c,j,y,hc⟩:=(h _).1 P;simp only[q1,bO,dT] at y hc;rcases y with rfl|rfl<;>rcases hc with rfl|rfl;{exact l _ j};{exact m j};{exact m (p _ _ j)};{exact l _ j}
lemma vl(d:w6 G)(a:q0 n D)(g:gK n G D)(v:Fin n)(c:v∈fX n D):∃b,2<=fanout D b/\fM n D b={v}/\q7 n D v.1 b:=by classical have h:∃w,2<=fanout D w/\v∈fM n D w:=zz.1 c;obtain⟨p,l⟩:=p24 h;have i:q7 n D v.1 (p22 h):=z9 a v _ l (λ u m j=>by{have:=p23 h m;by_contra q;exact this ⟨by omega,j⟩});exact⟨p22 h,p,Finset.Subset.antisymm (yw d a g v _ (wp a i)) (p49.2 l),i⟩
def zt(n:Nat)(D:qD)(b:tY n):Prop:=∀v∈fX n D,2<=fanout D (b v)/\fM n D (b v)={v}/\q7 n D v.1 (b v)
lemma zj(c:w6 G)(a:q0 n D)(d:gK n G D):∃b:tY n,zt n D b:=by classical have h:∀v:Fin n,∃b,v∈fX n D->2<=fanout D b/\fM n D b={v}/\q7 n D v.1 b:=by{intro v;by_cases g:v∈fX n D;{obtain⟨b,i⟩:=vl c a d v g;exact⟨b,λ _=>i⟩};{exact⟨0,λ h=>absurd h g⟩}};choose b i using h;exact⟨b,λ v g=>i v g⟩
lemma j4{b:tY n}(a:zt n D b):gN n D b:=λ v c=>⟨(a v c).1,(a v c).2.1⟩
lemma sem_exists_pureBranch(c:w6 G)(a:q0 n D)(d:gK n G D):∃b:tY n,gN n D b:=by obtain⟨b,g⟩:=zj c a d;exact⟨b,j4 g⟩
lemma sem_mem_inelig{v:Fin n}:v∈ineligSet n D↔v∉fX n D:=by simp[ineligSet]
lemma vm(d:q0 n D){v:Fin n}(c:v∈ineligSet n D){w:Nat}(a:v∈fM n D w):q7 n D v.1 w:=z9 d v w a (λ u _ g=>zb.1 c u g)
lemma sem_inelig_pure(g:w6 G)(a:q0 n D)(h:gK n G D){v:Fin n}(d:v∈ineligSet n D){w:Nat}(c:v∈fM n D w):fM n D w={v}:=Finset.Subset.antisymm (yw g a h v w (wp a (vm a d c))) (p49.2 c)
lemma q8{v:Fin n}{w:Nat}:w∈q2 n D {v}↔v∈fM n D w:=by simp only[q2,mF,mR];constructor;{rintro⟨-,u,a⟩;rw[mI,mS] at a;exact a.2▸a.1};{intro h;exact⟨wx h,v,mI.2 ⟨h,m0 v⟩⟩}
lemma we{v:Fin n}{e:tJ}:e∈qc n D (q2 n D {v})↔e.1<(tD D)/\v∈fM n D (fC D e)/\v∉fM n D (n+e.1):=by simp only[qc,jw,mF,mem_product,mR,mU,and_true,q8]
lemma v1{v:Fin n}(a:v∈ineligSet n D):q6 D (q2 n D {v})=0:=by unfold q6;refine p52 (λ w c=>?_);have:=zb.1 a w (q8.1 c);omega
lemma y4(i:w6 G)(c:q0 n D)(g:gK n G D){u v:Fin n}(d:G u v):∃j,j<(tD D)/\gZ D j=p63/\fO D (q1 u v) (n+j)=p63/\u∉fM n D (n+j)/\v∉fM n D (n+j)/\∃s:Bool,u∈fM n D (fC D (j,s))/\v∉fM n D (fC D (j,s))/\v∈fM n D (fC D (j,!s))/\u∉fM n D (fC D (j,!s)):=by classical have y:∃w,fO D (q1 u v) w=p63/\u∉fM n D w/\v∉fM n D w:=⟨qb n D,(g _).2 (yv d),by{rw[qn i g];simp},by{rw[qn i g];simp}⟩;obtain⟨l,p,m⟩:=p24 y;have q:∀a,a<p22 y->fO D (q1 u v) a=p63->u∈fM n D a\/v∈fM n D a:=λ a Q R=>by_contra λ hc=>by{rw[not_or] at hc;exact p23 y Q ⟨R,hc.1,hc.2⟩};generalize p22 y=w at l p m q;have Y:w<n+(tD D):=by{by_contra hc;rw[z0 D _ w (by omega)] at l;cases l};have Z:n<=w:=by{by_contra hc;rw[qa D _ w (by omega)] at l;have X:fM n D w={⟨w,by omega⟩}:=wc D ⟨w,by omega⟩;rw[X,mS] at p m;simp only[q1,bO,dT] at l;rcases l with h|h;exact p h.symm;exact m h.symm};obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have J:j<(tD D):=by{omega};obtain⟨Q,U,-⟩:=c j J;have H:=l;have A:=p;have B:=m;rw[qu c _ j J] at l;rw[yy c j J] at p m;cases ht:gZ D j;{rw[ht] at l p m;simp only[gop_false,bO] at l;simp only[bF,ite_false,mN,not_or] at p m;rcases l with h|h;{rcases q _ Q h with z|z;exact (p.1 z).elim;exact (m.1 z).elim};{rcases q _ U h with z|z;exact (p.2 z).elim;exact (m.2 z).elim}};{rw[ht] at l p m;simp only[gop_true,bA] at l;simp only[ite_true,mI,not_and] at p m;refine⟨j,J,ht,H,A,B,?_⟩;rcases q _ Q l.1 with P|P;{have M:=p P;have K:=(q _ U l.2).resolve_left M;exact⟨p55,P,λ h=>m h K,K,M⟩};{have M:=m P;have L:=(q _ U l.2).resolve_right M;exact⟨p63,L,M,P,λ h=>p h L⟩}}
lemma qe(c:w6 G)(h:fV n D)(d:gK n G D){v:Fin n}(g:v∈ineligSet n D):∃e:tJ,e.1<(tD D)/\gZ D e.1=p63/\fM n D (fC D e)={v}/\fM n D (n+e.1)=∅/\(∀a,G v a->a∈fM n D (fC D (e.1,!e.2)))/\qc n D (q2 n D {v})={e}/\w5 n D (q2 n D {v})=∅:=by have R:=h.1;have P:=z4 h {v} (by{rw[qn c d];simp});rw[v1 g,fw] at P;have i:∀a,G v a->∃j s,j<(tD D)/\gZ D j=p63/\(j,s)∈qc n D (q2 n D {v})/\a∈fM n D (fC D (j,!s)):=λ a m=>by{obtain⟨j,X,ht,-,M,-,s,h1,-,Z,-⟩:=y4 c R d m;exact⟨j,s,X,ht,we.2 ⟨X,h1,M⟩,Z⟩};obtain⟨a0,Q,-⟩:=c.2.2.2 v v;obtain⟨K,s0,H,u,p,-⟩:=i a0 Q;have q:(qc n D (q2 n D {v})).card=1:=by{have:=fz.2 ⟨_,p⟩;omega};obtain⟨e,J⟩:=p29.1 q;rw[J,mS] at p;subst p;have M:=we.1 (J▸m0 _);have l:fM n D (fC D (K,s0))={v}:=sem_inelig_pure c R d g M.2.1;exact⟨(K,s0),H,u,l,p37 (λ x U=>M.2.2 ((mS.1 (l▸sem_supp_and_sub R H u s0 U))▸U)),λ a m=>by{obtain⟨j,s,-,-,L,Y⟩:=i a m;rw[J,mS,Prod.mk.injEq] at L;obtain⟨rfl,rfl⟩:=L;exact Y},J,g8.1 (by omega)⟩
lemma j5(c:w6 G)(h:fV n D)(g:gK n G D){u v:Fin n}(d:G u v):u∈fX n D\/v∈fX n D:=by by_contra hc;rw[not_or] at hc;obtain⟨R,-,-,-,-,q,l,-⟩:=qe c h g (sem_mem_inelig.2 hc.1);obtain⟨Q,-,-,p,-,-,i,-⟩:=qe c h g (sem_mem_inelig.2 hc.2);obtain⟨j,K,-,-,y,r,s,P,-,M,-⟩:=y4 c h.1 g d;have J:(j,s)∈qc n D (q2 n D {u}):=we.2 ⟨K,P,y⟩;have H:(j,!s)∈qc n D (q2 n D {v}):=we.2 ⟨K,M,r⟩;rw[l,mS] at J;rw[i,mS] at H;subst J;subst H;obtain⟨a,m,z⟩:=c.2.2.2 u v;have L:a∈fM n D (fC D (j,!s)):=q a m;rw[p,mS] at L;exact z L
lemma vv{A:tS n}(d:∀a∈A,∀b∈A,¬G a b):¬yi G (yc A):=by rintro⟨a,c,g,h,hc⟩;simp only[yc,dT] at h hc;exact d a h c hc g
lemma vc(h:w6 G)(c:q0 n D)(g:gK n G D)(A:tS n)(i:∀a∈A,∀b∈A,¬G a b)(x:Fin n)(d:∃a∈A,G x a):∃j s,j<(tD D)/\gZ D j=p63/\x∈fM n D (fC D (j,s))/\x∉fM n D (n+j)/\Disjoint (fM n D (fC D (j,s))) A:=by by_contra H;have m:∀j s,j<(tD D)->gZ D j=p63->x∈fM n D (fC D (j,s))->x∉fM n D (n+j)->fO D (yc A) (fC D (j,s))=p63/\fO D (wm x (yc A)) (fC D (j,s))=p63:=λ j s p y q R=>by{obtain⟨a,K,J⟩:=Finset.not_disjoint_iff.1 (λ Z=>H ⟨j,s,p,y,q,R,Z⟩);exact⟨q3 c K (by simp[yc,J]),q3 c K (by simp[wm,yc,J])⟩};have P:∀w,x∉fM n D w->fO D (yc A) w=fO D (wm x (yc A)) w:=λ w=>by{induction w using sI with|_ w ih=>{intro r;by_cases M:w<n;{rw[qa D _ w M,qa D _ w M];rw[wc D ⟨w,M⟩,mS] at r;exact jr x _ _ (λ hc=>r hc.symm)};by_cases Y:w<n+(tD D);{obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have p:j<(tD D):=by{omega};obtain⟨L,Q,-⟩:=c j p;rw[qu c _ j p,qu c _ j p];cases y:gZ D j;{rw[yj c p y,mN,not_or] at r;rw[ih _ L r.1,ih _ Q r.2]};{have v:=r;rw[qm c p y,mI,not_and] at v;by_cases l:x∈fM n D (yx D j);{have q:=m j p55 p y (l) r;rw[qf] at q;rw[ih _ Q (v l),q.1,q.2]};by_cases u:x∈fM n D (yf D j);{have q:=m j p63 p y (u) r;rw[qo] at q;rw[ih _ L l,q.1,q.2]};{rw[ih _ L l,ih _ Q u]}}};{rw[z0 D _ w (by omega),z0 D _ w (by omega)]}}};obtain⟨a,L,l⟩:=d;exact vv i ((g _).1 (P (qb n D) (qn h g▸nE x)▸(g _).2 ⟨x,a,l,vb x _,by simp[wm,yc,L]⟩))
def fD(n:Nat)(D:qD)(x:Fin n):tF (tJ):=qc n D (q2 n D {x})
def sem_bar (e:Nat×Bool):Nat×Bool:=(e.1,!e.2)
lemma sem_mem_W{x:Fin n}{e:tJ}:e∈fD n D x↔e.1<(tD D)/\x∈fM n D (fC D e)/\x∉fM n D (n+e.1):=we
lemma sem_bar_bar(e:tJ):sem_bar (sem_bar e)=e:=by simp[sem_bar]
lemma sem_same_gate{e f:tJ}(h:e.1=f.1):f=e\/f=sem_bar e:=by obtain⟨j,s⟩:=e;obtain⟨k,t⟩:=f;simp only at h;subst h;cases s<;>cases t<;>simp[sem_bar]
lemma sem_W_and(c:q0 n D){x:Fin n}{e:tJ}(a:e∈fD n D x):gZ D e.1=p63:=by obtain⟨g,d,h⟩:=sem_mem_W.1 a;by_contra i;rw[Bool.not_eq_true] at i;apply h;rw[yj c g i,mN];obtain⟨j,s⟩:=e;cases s;{left;simpa[fC] using d};{right;simpa[fC] using d}
namespace A0b
abbrev sM:=@sem_mem_W
abbrev sA:=@sem_W_and
abbrev sP:=@sem_inelig_pure
abbrev sU:=@sem_supp_and_sub
abbrev sE:=@sem_mem_inelig
lemma sK{g:Nat}{s:Bool}:sem_bar (g,!s)=(g,s):=by cases s<;>rfl
lemma sX{D:qD}{g w:Nat}(h:yx D g=w\/yf D g=w):∃s,fC D (g,s)=w:=h.elim (λ h=>⟨p55,h⟩) (λ h=>⟨p63,h⟩)
end A0b
open A0b
lemma xt(a:w6 G)(h:fV n D)(c:gK n G D)(x:Fin n):(fD n D x).card+(w5 n D (q2 n D {x})).card=1+q6 D (q2 n D {x}):=by have d:=z4 h {x} (by rw[qn a c];simp);rwa [fw] at d
lemma z5(d:w6 G)(c:q0 n D)(g:gK n G D){x y:Fin n}(a:G x y):∃e,e∈fD n D x/\sem_bar e∈fD n D y/\y∉fM n D (fC D e)/\x∉fM n D (fC D (sem_bar e))/\fO D (q1 x y) (n+e.1)=p63:=by obtain⟨j,m,-,h,l,i,s,u,r,q,p⟩:=y4 d c g a;exact⟨(j,s),sM.2 ⟨m,u,l⟩,sM.2 ⟨m,q,i⟩,r,p,h⟩
lemma qk(c:q0 n D){R:Nat->Nat->Prop}(d:∀a b,R a b->q5 n D a b){a b:Nat}(h:RT R a b):a<=b:=by induction h with|refl=>{exact le_refl _}|tail _ g ih=>{exact le_trans ih (le_of_lt (wb c (d _ _ g)))}
lemma j6(d:q0 n D){x:Fin n}(g:w5 n D (q2 n D {x})=∅){j:Nat}(c:j<(tD D))(a:x∈fM n D (n+j)):gZ D j=p55/\¬(x∈fM n D (yx D j)/\x∈fM n D (yf D j)):=by have h:¬(x∈fM n D (yx D j)/\x∈fM n D (yf D j)):=by{intro m;have i:j∈w5 n D (q2 n D {x}):=by{rw[w5,mF,mR];exact⟨c,q8.2 a,q8.2 m.1,q8.2 m.2⟩};rw[g] at i;exact nE _ i};refine⟨?_,h⟩;by_contra l;rw[p59] at l;rw[qm d c l,mI] at a;exact h a
lemma j7(c:w6 G)(h:fV n D)(d:gK n G D)(b:tY n)(a:gN n D b)(x:Fin n):(fD n D x).card+(w5 n D (q2 n D {x})).card=1+(({x}:tS n)∩fX n D).card+((residualUnits n D b).filter (λ u=>x∈fM n D u.1)).card:=by have m:=xt c h d x;have l:=jm h.1 b a {x};have j:(residualUnits n D b).filter (λ u=>(fM n D u.1∩{x}).Nonempty)=(residualUnits n D b).filter (λ u=>x∈fM n D u.1):=by{refine filter_congr (λ u _=>?_);constructor;{rintro⟨y,g⟩;rw[mI,mS] at g;exact g.2▸g.1};{intro i;exact⟨x,mI.2 ⟨i,m0 x⟩⟩}};rw[j] at l;omega
section
variable (Q:q0 n D)
include Q
lemma qd(x:tX n){j:Nat}(a:j<(tD D))(s:Bool):fO D x (n+j)=xp (gZ D j) (fO D x (fC D (j,s))) (fO D x (fC D (j,!s))):=by rw[qu Q x j a];cases s;{simp[fC]};{cases gZ D j<;>simp[fC,Bool.and_comm,Bool.or_comm]}
lemma vn{v b t:Nat}(h:q7 n D v b)(g:b<=t):b=v\/¬RT (λ a c=>q5 n D a c/\c≠b) v t:=by induction h using rI with|refl=>{exact .inl rfl}|@head a c i l ih=>{by_cases p:b=a;{exact .inl p};{right;intro u;rcases rC u with y|⟨z,r,j⟩;{have J:=wb Q i.1;have H:=qk Q (λ _ _ q=>q.1) l;omega};{have m:c=z:=qj i.1 r.1 i.2;subst m;rcases ih with rfl|ih;{exact r.2 rfl};{exact ih j}}}}
lemma kh(x y:tX n)(v:Fin n)(g:∀k,k≠v->x k=y k)(b t:Nat)(d:b=v.1\/¬RT (λ a c=>q5 n D a c/\c≠b) v.1 t)(i:fO D x b=fO D y b):fO D x t=fO D y t:=by by_contra m;rcases d with rfl|d;{rw[qa D x _ v.2,qa D y _ v.2] at i;have l:x=y:=by{funext k;by_cases p:k=v;{rw[p];exact i};{exact g k p}};exact m (by rw[l])};{exact d (yu (λ a c h=>⟨h.1,λ hc=>h.2 (by rw[hc];exact i)⟩) (wn Q x y v g _ m))}
lemma j8{a c q:Nat}(hc:q7 n D a c)(d:RT (q5 n D) a q):RT (q5 n D) c q\/(q7 n D q c/\q≠c):=by revert d;induction hc using rI with|refl=>{exact λ d=>.inl d}|@head a v h i ih=>{intro d;rcases rC d with l|⟨r,u,j⟩;{right;have z:=wb Q h.1;have y:=qk Q (λ _ _ p=>p.1) i;refine⟨?_,by omega⟩;rw[<-l];exact rH h i};{have m:v=r:=qj h.1 u h.2;subst m;exact ih j}}
lemma vd(v:Fin n){j:Nat}(c:j<(tD D))(s:Bool)(g:q7 n D v.1 (fC D (j,!s)))(i:fanout D (fC D (j,!s))=1)(x y:tX n)(d:∀k,k≠v->x k=y k):fO D x (fC D (j,s))=fO D y (fC D (j,s)):=by by_contra z;have M:=yu (λ _ _ h=>h.1) (wn Q x y v d _ z);have:=w7 Q c s;have:=w7 Q c (!s);rcases j8 Q g M with H|⟨H,P⟩;{rcases rC H with q|⟨A,u,l⟩;exact xj Q c s q.symm;have r:=qj (qs c (!s)) u i;subst r;have:=qk Q (λ _ _ h=>h) l;omega};{rcases rC H with q|⟨L,u,l⟩;exact P q;have r:=qj (qs c s) u.1 u.2;subst r;have:=qk Q (λ _ _ h=>h.1) l;omega}
end
lemma ze(g:w6 G)(c:q0 n D)(h:gK n G D){i:Fin n}(d:i∈ineligSet n D){b:Nat}(a:q7 n D i.1 b)(j:2<=fanout D b):fM n D b=∅:=by have l:=yw g c h i b (wp c a);refine p37 (λ x m=>?_);have p:=l m;rw[mS] at p;have q:=zb.1 d b (p▸m);omega
lemma j9{a t:Nat}(c:RT (q5 n D) a t):q7 n D a t\/∃b,q7 n D a b/\2<=fanout D b:=by induction c using rI with|refl=>{exact .inl rR}|@head a j d _ ih=>{by_cases h:fanout D a=1;{rcases ih with g|⟨b,g,i⟩;{exact .inl (rH ⟨d,h⟩ g)};{exact .inr ⟨b,rH ⟨d,h⟩ g,i⟩}};{have:=zs d;exact .inr ⟨a,rR,by omega⟩}}
lemma yd(c:q0 n D){b:Nat}(d:2<=fanout D b)(a:fM n D b=∅):b∈(inner n D).filter (λ w=>¬(fM n D w).Nonempty):=mF.2 ⟨ql.2 (wk c (w:=b) (by omega)),by rw[a];exact gk⟩
lemma y7(d:q0 n D)(a:Bzero n D=0){b:Nat}(c:2<=fanout D b):(fM n D b).Nonempty:=by by_contra g;rw[fN] at g;have h:fanout D b-1<=∑ w∈(inner n D).filter (λ w=>¬(fM n D w).Nonempty),(fanout D w-1):=hE (f:=λ w=>fanout D w-1) (λ _ _=>nZ _) (yd d c g);unfold Bzero q6 at a;omega
section
variable (K:w6 G)(H:fV n D)(C:gK n G D)(B:Bzero n D=0){i:Fin n}(M:i∈ineligSet n D)
include K H C B i M
lemma v3{w:Nat}(c:RT (q5 n D) i.1 w):q7 n D i.1 w:=by rcases j9 c with l|⟨b,l,p⟩;{exact l};{have m:=y7 H.1 B p;rw[ze K H.1 C M l p] at m;exact absurd m gk}
lemma zv:q7 n D i.1 (qb n D):=v3 K H C B M (vk H i.1 (by have:=i.2;omega))
end
lemma zk{x y:Fin n}{w:Nat}:w∈q4 n D x y↔x∈fM n D w/\y∉fM n D w:=by simp only[q4,mF,mR];exact⟨λ h=>h.2,λ h=>⟨wx h.1,h⟩⟩
lemma y5{x y:Fin n}{e:tJ}:e∈qc n D (q4 n D x y)↔e.1<(tD D)/\(x∈fM n D (fC D e)/\y∉fM n D (fC D e))/\¬(x∈fM n D (n+e.1)/\y∉fM n D (n+e.1)):=by simp only[qc,jw,mF,mem_product,mR,mU,and_true,zk]
lemma vp(g:q0 n D)(b:tY n)(d:gN n D b){x y:Fin n}(a:x≠y)(c:x∈fX n D):q6 D (q4 n D x y)=1+((residualUnits n D b).filter (λ u=>x∈fM n D u.1/\y∉fM n D u.1)).card:=by have K:q6 D (q4 n D x y)=((units n D).filter (λ u=>x∈fM n D u.1/\y∉fM n D u.1)).card:=by{rw[wh n D (λ w=>x∈fM n D w/\y∉fM n D w)];symm;refine sum_subset (λ w p=>zk.2 (mF.1 p).2) (λ w p l=>by{have q:w∉inner n D:=λ hc=>l (mF.2 ⟨hc,zk.1 p⟩);rw[ql] at q;simp[qz g w (by omega)]})};have J:(units n D).filter (λ u=>x∈fM n D u.1/\y∉fM n D u.1)={(⟨b x,0⟩:U0)}∪(residualUnits n D b).filter (λ u=>x∈fM n D u.1/\y∉fM n D u.1):=by{ext u;have j:=yl g b d;simp only[residualUnits,ww,mN,mF,mD,mS];exact⟨λ h=>if r:u∈qh n D b then .inl (by{obtain⟨v,z,rfl⟩:=mG.1 r;have i:=h.2.1;rw[(d v z).2,mS] at i;rw[i]}) else .inr ⟨⟨⟨h.1,⟨x,h.2.1⟩⟩,r⟩,h.2⟩,λ | .inl h=>h▸⟨(mF.1 (j (mG.2 ⟨x,c,rfl⟩))).1,by{rw[(d x c).2];exact m0 x},by{rw[(d x c).2,mS];exact λ hc=>a hc.symm}⟩ | .inr h=>⟨h.1.1.1,h.2⟩⟩};have H:(⟨b x,0⟩:U0)∉(residualUnits n D b).filter (λ u=>x∈fM n D u.1/\y∉fM n D u.1):=λ hc=>(mD.1 (mF.1 hc).1).2 (mG.2 ⟨x,c,rfl⟩);rw[K,J,Finset.singleton_union,Finset.card_insert_of_notMem H];omega
lemma vw(c:q0 n D){x y:Fin n}(a:x≠y){w:Nat}(d:x∈fM n D w/\y∈fM n D w):∃j s,j<(tD D)/\gZ D j=p55/\x∈fM n D (n+j)/\y∈fM n D (n+j)/\x∈fM n D (fC D (j,s))/\y∉fM n D (fC D (j,s))/\y∈fM n D (fC D (j,!s))/\x∉fM n D (fC D (j,!s)):=by classical have l:∃u,x∈fM n D u/\y∈fM n D u:=⟨w,d⟩;obtain⟨m,p⟩:=p24 l;have i:∀u<p22 l,¬(x∈fM n D u/\y∈fM n D u):=λ _ J=>p23 l J;generalize p22 l=f at m p i;have L:=wx m;have Q:n<=f:=by{by_contra hc;have K:fM n D f={⟨f,by omega⟩}:=wc D ⟨f,by omega⟩;rw[K,mS] at m p;exact a (m.trans p.symm)};obtain⟨j,rfl⟩:∃j,f=n+j:=⟨f-n,by omega⟩;have H:j<(tD D):=by{omega};obtain⟨P,M,-⟩:=c j H;have q:=i _ P;have z:=i _ M;cases ht:gZ D j;{have h1':=m;have h2':=p;rw[yj c H ht,mN] at h1' h2';refine⟨j,?_⟩;rcases h1' with v|r;{have h:=λ hc=>q ⟨v,hc⟩;have g:=h2'.resolve_left h;exact⟨p55,H,ht,m,p,v,h,g,λ hc=>z ⟨hc,g⟩⟩};{have g:=λ hc=>z ⟨r,hc⟩;have h:=h2'.resolve_right g;exact⟨p63,H,ht,m,p,r,g,h,λ hc=>q ⟨hc,h⟩⟩}};{rw[qm c H ht,mI] at m p;exact absurd ⟨m.1,p.1⟩ q}
section
variable (K:w6 G)(H:fV n D)(C:gK n G D)(b:tY n)(P:gN n D b)
include K H C b P
lemma v4{x c z:Fin n}(a:x≠c)(m:x∈fX n D)(d:∀u∈residualUnits n D b,x∈fM n D u.1->c∈fM n D u.1){w:Nat}(p:x∈fM n D w/\c∈fM n D w)(j:G x z)(g:¬G c z):q6 D (q4 n D x c)=1/\w5 n D (q4 n D x c)=∅/\(qc n D (q4 n D x c)).card=2/\∃e∈qc n D (q4 n D x c),gZ D e.1=p55/\c∈fM n D (n+e.1):=by have hS:=H.1;have r:q6 D (q4 n D x c)=1:=by{rw[vp hS b P a m,gI.2 (λ u y hc=>hc.2 (d u y hc.1)),Finset.card_empty]};have h4:=va H x c a (qn K C▸nE x);rw[r] at h4;obtain⟨U,R,h3,Z,Y,Q,B,A,-,-⟩:=vw hS a p;have M:(U,R)∈qc n D (q4 n D x c):=y5.2 ⟨h3,⟨B,A⟩,λ hc=>hc.2 Q⟩;obtain⟨j2,s2,h1,-,X,N,h6⟩:=vc K hS C {c,z} (λ u y v J=>by{simp only[p43,mS] at y J;rcases y with rfl|rfl<;>rcases J with rfl|rfl;{exact K.2.1 _};{exact g};{exact λ hc=>g (K.1 _ _ hc)};{exact K.2.1 _}}) x ⟨z,by simp,j⟩;have h5:(j2,s2)∈qc n D (q4 n D x c):=y5.2 ⟨h1,⟨X,λ hc=>p36.1 h6 hc (by simp)⟩,λ hc=>N hc.1⟩;have:=p46.2 ⟨_,M,_,h5,λ L=>N ((Prod.mk.inj L).1▸Y)⟩;exact⟨r,g8.1 (by omega),by omega,(U,R),M,Z,Q⟩
lemma bb{x c:Fin n}(a:x≠c)(i:x∈fX n D)(d:∀u∈residualUnits n D b,x∈fM n D u.1->c∈fM n D u.1){w:Nat}(j:x∈fM n D w/\c∈fM n D w):∃e0,∀e∈fD n D x,e≠e0->c∈fM n D (fC D e):=by classical obtain⟨z,p,J⟩:=K.2.2.1 x c a;obtain⟨-,-,X,Q,y,q,-⟩:=v4 K H C b P a i d j p J;obtain⟨e0,B⟩:=p29.1 (show ((qc n D (q4 n D x c)).erase Q).card=1 by rw[Finset.card_erase_of_mem y,X]);refine⟨e0,λ e A r=>by_contra λ L=>?_⟩;obtain⟨Y,U,R⟩:=sM.1 A;exact r (mS.1 (B▸Finset.mem_erase.2 ⟨λ v=>Bool.false_ne_true (q▸v▸sA H.1 A),y5.2 ⟨Y,⟨U,L⟩,λ hc=>R hc.1⟩⟩))
end
end
end
end DagTools
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Finset (card_le_univ nodup_toList univ)
open List (Nodup)
open DagTools
abbrev V:=Fin 10
abbrev EdgeIdx:=Fin 14
section
open DagTools.A0
abbrev qO:=tJ
abbrev Slot:=qO
def k7:List (Nat×Nat):= choose ([(0,3),(0,7),(1,4),(1,9),(2,5),(2,6),(3,7),(3,9),(4,7),(4,8),(5,6),(5,9),(6,8),(7,8)]) ([(0,8),(0,9),(1,4),(1,9),(2,5),(2,6),(3,7),(3,9),(4,7),(4,8),(5,6),(5,9),(6,8),(7,8)]) ([(0,8),(0,9),(1,3),(1,7),(2,5),(2,6),(3,7),(3,9),(4,7),(4,8),(5,6),(5,9),(6,8),(7,8)]) ([(0,8),(0,9),(1,3),(1,7),(2,4),(2,9),(3,7),(3,9),(4,7),(4,8),(5,6),(5,9),(6,8),(7,8)])
def gJ(x:Fin 10->Bool):Prop:=∃u v:Fin 10,(u.1,v.1)∈k7/\x u=p63/\x v=p63
def fL(C:Circuit):Prop:=∀x:Fin 10->Bool,C.eval (oF x)=p63↔gJ x
def neigh(v:V):Nat:= choose ([136,528,96,641,386,580,292,281,208,42].getD v.1 0) ([768,528,96,640,386,580,292,280,209,43].getD v.1 0) ([768,136,96,642,384,580,292,282,209,41].getD v.1 0) ([768,136,528,642,388,576,288,282,209,45].getD v.1 0)
abbrev adj(u v:V):Prop:=(neigh u).testBit v.1=p63
end
namespace A1
abbrev EI:=EdgeIdx
abbrev SL:=fV 10
abbrev PB:=gN 10
abbrev SC:=gK 10 adj
end A1
section
open DagTools.A0 DagTools.A0r DagTools.A0b A1
def ep0 (e:EI):V:=Fin.ofNat 10 (k7.getD e.val (0,0)).1
def ep1 (e:EI):V:=Fin.ofNat 10 (k7.getD e.val (0,0)).2
def endpoint (s:Bool)(e:EI):V:=if s then ep1 e else ep0 e
def sflip(s:Bool)(p:qO):qO:=(p.1,xor s p.2)
@[simp] lemma sflip_false(p:qO):sflip p55 p=p:=by rcases p with ⟨g,b⟩;simp[sflip]
@[simp] lemma sflip_true(p:qO):sflip p63 p=sem_bar p:=by rcases p with ⟨g,b⟩;cases b<;>rfl
lemma sflip_not(s:Bool)(p:qO):sflip (!s) p=sem_bar (sflip s p):=by rcases p with ⟨g,b⟩;cases s<;>cases b<;>rfl
lemma sflip_inj(s:Bool){p q:qO}(h:sflip s p=sflip s q):p=q:=by rcases p with ⟨g,c⟩;rcases q with ⟨d,a⟩;cases s<;>cases c<;>cases a<;>simp[sflip] at h ⊢<;>exact h
def js(u v:V):List EI->EI×Bool
 | []=>(0,p55)
 | e::rest=> if ep0 e==u&&ep1 e==v then (e,p55) else if ep1 e==u&&ep0 e==v then (e,p63) else js u v rest
def fW(u v:V):EI×Bool:=js u v (lR 14)
abbrev edgeOfPair:=fW
lemma wt(u v:V)(h:adj u v):endpoint (fW u v).2 (fW u v).1=u/\endpoint (!(fW u v).2) (fW u v).1=v:=by revert u v h;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma graph_ok:w6 adj:=by unfold w6;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
namespace A1b
abbrev G0:=graph_ok
end A1b
open A1b
lemma ja:∀u v:V,adj u v↔(u.1,v.1)∈k7\/(v.1,u.1)∈k7:=by rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma xk(e:EI):adj (ep0 e) (ep1 e):=by revert e;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma xm(x:V->Bool):gJ x↔yi adj x:=by constructor;{rintro⟨u,v,e,d,c⟩;exact⟨u,v,(ja u v).2 (o1 e),d,c⟩};{rintro⟨u,v,a,d,c⟩;rcases (ja u v).1 a with e|e;{exact⟨u,v,e,d,c⟩};{exact⟨v,u,e,c,d⟩}}
lemma xu:¬gJ (λ _=>p55):=by rintro⟨_,_,_,h,_⟩;contradiction
lemma k8(i:V):¬gJ (q9 i):=λ h=>wd G0 i ((xm _).1 h)
lemma normalized(C:Circuit)(c:Monotone2 C)(a:fL C):∃D:qD,SL D/\(tD D)<=C.size/\SC D:=by obtain⟨D,l,le,m⟩:=zy (n:=10) C c (by{intro b;cases b;{refine⟨λ _=>p63,?_⟩;rw[Ne,p59];exact (a _).2 ⟨7,8,by rcases sctx with ⟨vv⟩; fin_cases vv <;> decide,rfl,rfl⟩};{exact⟨λ _=>p55,λ h=>xu ((a _).1 h)⟩}}) (by{intro i;exact⟨q9 i,λ h=>k8 i ((a _).1 (by rw[h];simp[q9]))⟩}) (by{intro i;obtain⟨j,g,_⟩:=G0.2.2.2 i i;refine⟨q9 j,q1 i j,?_,?_⟩;{intro k d;simp[q1,q9,d]};{intro h;exact k8 j ((a _).1 (h.trans ((a _).2 ((xm _).2 (yv g)))))}});exact⟨D,l,le,λ x=>by rw[m,a];exact xm x⟩
def mask (m:Nat):Finset V:=univ.filter (λ v=>m.testBit v.val)
abbrev independent(T:tF V):Prop:=∀a∈T,∀b∈T,¬adj a b
def zw(a:EP V):Prop:=∀i j,adj (a i) (a j)↔adj i j
def w4(a:List Nat)(v:V):V:=Fin.ofNat 10 (a.getD v.1 0)
def gA:EP V:=Equiv.refl V
def specialPerm:EP V:=⟨w4 [0,3,2,1,7,5,6,4,8,9],w4 [0,3,2,1,7,5,6,4,8,9],by decide +kernel,by decide +kernel⟩
def gB : EP V := if sctx.default.val = 1 then specialPerm else gA
def autPerm(a:Fin 2):EP V:=match a.1 with|0=>gA|_=>gB
lemma bd:zw gA:=by intro i j;rfl
lemma be:zw gB:=by unfold zw;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma auto_autPerm(a:Fin 2):zw (autPerm a):=by fin_cases a;{exact bd};{exact be}
lemma rename{D:qD}(h:SL D)(d:SC D)(c:EP V)(a:zw c):SC (relabel c D):=by intro x;rw[xa c h.1 h.2.2,d];constructor;{rintro⟨u,v,g,j,i⟩;exact⟨c u,c v,(a _ _).2 g,j,i⟩};{rintro⟨u,v,g,j,i⟩;refine⟨c.symm u,c.symm v,(a _ _).1 (by simpa using g),by simpa using j,by simpa using i⟩}
lemma yn(a:EP V)(D:qD)(c:D≠[]){w:Nat}:gL a w∈inner 10 (relabel a D)↔w∈inner 10 D:=by have g:0<(tD D):=lP c;simp only[inner,mR,rL];by_cases d:w<10;{rw[yh a d];have:=(a ⟨w,d⟩).2;omega};{rw[qt a (by omega)]}
def gn(a:EP V)(b:V->Nat)(v:V):Nat:=gL a (b (a.symm v))
abbrev relabelBranch:=gn
lemma relabel_pureBranch(a:EP V){D:qD}(c:q0 10 D){b:V->Nat}(d:PB D b):PB (relabel a D) (gn a b):=by intro v h;rw[ym a c] at h;obtain⟨u,i,rfl⟩:=mG.1 h;have g:=d u i;simp only[gn,Equiv.symm_apply_apply];refine⟨by rw[wa];exact g.1,?_⟩;rw[rS a c,g.2,Finset.image_singleton]
lemma relabel_residualUnits_mem(a:EP V){D:qD}(h:SL D)(b:V->Nat)(u:U0):(⟨gL a u.1,u.2⟩:U0)∈residualUnits 10 (relabel a D) (gn a b)↔u∈residualUnits 10 D b:=by rcases u with ⟨w,i⟩;simp only[residualUnits,mD,ww,units,mF,p44,mR,qh,mG,ym a h.1,yn a D h.2.2,wa,rS a h.1,p39,Sigma.mk.inj_iff,heq_eq_eq];exact⟨λ⟨⟨⟨l,hr⟩,g⟩,d⟩=>⟨⟨⟨l,hr⟩,g⟩,λ⟨v,j,c⟩=>d ⟨a v,⟨v,j,rfl⟩,by simpa[gn] using ⟨congrArg (gL a) c.1,c.2⟩⟩⟩,λ⟨⟨⟨l,hr⟩,g⟩,d⟩=>⟨⟨⟨l,hr⟩,g⟩,λ⟨_,⟨v,j,rfl⟩,c⟩=>d ⟨v,j,by{simp only[gn,Equiv.symm_apply_apply] at c;exact⟨(gq a).1 c.1,c.2⟩}⟩⟩⟩
def gP(D:qD)(a:EI->qO):Prop:=∀s e,sflip s (a e)∈fD 10 D (endpoint s e)/\endpoint (!s) e∉fM 10 D (fC D (sflip s (a e)))
abbrev GoodEdge:=gP
lemma get_edges{D:qD}(c:q0 10 D)(a:SC D):∃edge:EI->qO,gP D edge:=by classical have j:∀e:EI,∃p:qO,p∈fD 10 D (ep0 e)/\sem_bar p∈fD 10 D (ep1 e)/\ep1 e∉fM 10 D (fC D p)/\ep0 e∉fM 10 D (fC D (sem_bar p)):=by{intro e;obtain⟨p,i,h,g,d,_⟩:=z5 G0 c a (xk e);exact⟨p,i,h,g,d⟩};choose edge hedge using j;refine⟨edge,λ s e=>?_⟩;cases s;{simpa[endpoint,sflip_false] using ⟨(hedge e).1,(hedge e).2.2.1⟩};{simpa[endpoint,sflip_true] using ⟨(hedge e).2.1,(hedge e).2.2.2⟩}
def relabelEdge(c:EP V)(a:EI->qO)(e:EI):qO:=let p:=fW (c.symm (ep0 e)) (c.symm (ep1 e));sflip p.2 (a p.1)
lemma relabelEdge_fst(c:EP V)(a:EI->qO)(e:EI):(relabelEdge c a e).1=(a (fW (c.symm (ep0 e)) (c.symm (ep1 e))).1).1:=rfl
lemma surplus_bound{D:qD}(h:SL D)(a:(tD D)<=18)(b:V->Nat)(c:PB D b):(residualUnits 10 D b).card+Bzero 10 D+1<=(ineligSet 10 D).card:=by have j:=vj h;have i:=jz 10 D;have g:=vu 10 D;have d:=kf h.1 b c;omega
lemma inelig_indep{D:qD}(h:SL D)(c:SC D):independent (ineligSet 10 D):=by intro a l b j i;rcases j5 G0 h c i with g|d;{exact (sE.1 l) g};{exact (sE.1 j) d}
def orbitMasks:List Nat:= choose ([1,2,4,8,16,32,64,128,256,512,3,5,6,10,12,17,20,24,33,34,40,48,65,66,72,80,130,132,160,192,257,258,260,264,288,513,516,528,576,640,768,7,14,21,28,35,42,49,56,67,74,81,88,134,162,194,259,261,262,266,268,289,290,296,517,529,532,577,592,644,704,769,772,263,270,291,298,533,593,773]) ([1,2,4,16,32,64,256,512,3,5,17,33,65,6,10,34,66,130,258,20,260,516,48,80,528,288,576,768,7,11,35,67,131,21,49,81,14,134,262,42,74,266,162,290,194,532,772,592,15,135,43,75,163,195,270,298]) ([1,2,4,8,16,32,64,128,256,512,3,5,6,9,12,17,18,20,24,33,34,40,48,65,66,72,80,129,132,160,192,258,260,264,288,514,516,528,576,640,768,7,13,19,21,22,25,28,35,41,49,50,56,67,73,81,82,88,133,161,193,262,268,290,296,518,530,532,578,592,644,704,770,772,23,29,51,57,83,89,534,594,774]) ([1,2,4,8,16,32,64,128,256,512,3,5,6,9,12,17,18,24,33,34,36,40,48,65,66,68,72,80,129,132,160,192,258,260,264,288,514,528,576,640,768,7,13,19,25,35,37,38,41,44,49,50,56,67,69,70,73,76,81,82,88,133,161,164,193,196,262,268,290,292,296,530,578,592,704,770,39,45,51,57,71,77,83,89,165,197,294,300,594])
def maskImage(a:Fin 2)(m:Nat):Nat:=(lR 10).foldl (λ c v=>if m.testBit v.1 then c|||(1<<<(autPerm a v).1) else c) 0
lemma za(n k:Nat):(1<<<n).testBit k=decide (n=k):=by rw[p26,Nat.testBit_two_pow]
lemma k9(a:Fin 2)(m:Nat)(L:List V)(c:Nat)(k:Nat):(L.foldl (λ s v=>if m.testBit v.1 then s|||(1<<<(autPerm a v).1) else s) c).testBit k=(c.testBit k||L.any (λ v=>m.testBit v.1&&decide ((autPerm a v).1=k))):=by induction L generalizing c with|nil=>{simp}|cons v d ih=>{simp only[lO,p1,ih];by_cases g:m.testBit v.1=p63;{simp only[g,ite_true,p64,p27,za,p62]};{simp only[g,bF,ite_false,p56,p57]}}
lemma mask_maskImage(a:Fin 2)(m:Fin 1024):mask (maskImage a m.1)=(mask m.1).image (autPerm a):=by ext u;simp only[mask,maskImage,mF,mU,true_and,mG,k9,p28,p57,p2,hC,bA,dT];constructor;{rintro⟨v,d,c⟩;exact⟨v,d,Fin.ext c⟩};{rintro⟨v,d,rfl⟩;exact⟨v,d,rfl⟩}
def jc(m:Nat):Bool:=k7.all (λ e=>!(m.testBit e.1&&m.testBit e.2))
def zc(m:Nat):Bool:=m==0||!jc m||(lR 2).any (λ a=>orbitMasks.elem (maskImage a m))
def wu(lo:Nat):Nat->Bool
 | 0=>p63
 | n+1=>zc lo&&wu (lo+1) n
lemma v5:(p20 16).all (λ b=>wu (b*64) 64)=p63:=by rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma jd(a n m:Nat)(h:wu a n=p63)(c:a<=m)(d:m<a+n):zc m=p63:=by induction n generalizing a with|zero=>{omega}|succ n ih=>{simp only[wu,bA] at h;by_cases g:m=a;{subst g;exact h.1};{exact ih (a+1) h.2 (by omega) (by omega)}}
lemma je{m:Nat}(a:independent (mask m)):jc m=p63:=by unfold jc;rw[p0];intro e d;have c:e.1<10/\e.2<10:=of_decide_eq_true (p0.1 (show k7.all (λ p=>decide (p.1<10/\p.2<10))=p63 by rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel) e d);cases h:m.testBit e.1<;>cases g:m.testBit e.2;rfl;rfl;rfl;exact absurd ((ja ⟨e.1,c.1⟩ ⟨e.2,c.2⟩).2 (.inl d)) (a ⟨e.1,c.1⟩ (mF.2 ⟨mU _,h⟩) ⟨e.2,c.2⟩ (mF.2 ⟨mU _,g⟩))
lemma orbit_dispatch(m:Fin 1024)(d:m.1≠0)(c:independent (mask m.1)):∃a:Fin 2,maskImage a m.1∈orbitMasks:=by have j:=jd ((m.1/64)*64) 64 m.1 (p0.1 v5 (m.1/64) (p17.2 (by omega))) (by omega) (by omega);simp only[zc,je c,p61,Bool.or_false,bO,beq_iff_eq,p2,hC,true_and,List.elem_eq_mem,dT] at j;exact j.resolve_left d
lemma kj(S:tF V)(L:List V)(a:Nat)(k:Nat):(L.foldl (λ s v=>if v∈S then s|||(1<<<v.1) else s) a).testBit k=(a.testBit k||L.any (λ v=>decide (v∈S)&&decide (v.1=k))):=by induction L generalizing a with|nil=>{simp}|cons v c ih=>{simp only[lO,p1,ih];by_cases d:v∈S;{simp only[d,ite_true,decide_true,p64,p27,za,p62]};{simp only[d,ite_false,decide_false,p56,p57]}}
lemma kx(S:tF V)(L:List V)(c:Nat)(a:c<2^10):L.foldl (λ s v=>if v∈S then s|||(1<<<v.1) else s) c<2^10:=by induction L generalizing c with|nil=>{exact a}|cons v d ih=>{simp only[lO];by_cases g:v∈S;{simp only[g,ite_true];apply ih;apply Nat.or_lt_two_pow a;rw[p26];exact Nat.pow_lt_pow_right (by omega) v.2};{simp only[g,ite_false];exact ih c a}}
lemma repr_finset(S:tF V):∃m:Fin 1024,mask m.1=S:=by let n:Nat:=(lR 10).foldl (λ s v=>if v∈S then s|||(1<<<v.1) else s) 0;refine⟨⟨n,kx S (lR 10) 0 (by omega)⟩,?_⟩;ext v;simp only[mask,mF,mU,true_and,n,kj,p28,p57,p2,hC,bA,dT];exact⟨λ⟨u,d,a⟩=>Fin.ext a▸d,λ c=>⟨v,c,rfl⟩⟩
def fF(D:qD)(x:V):Nat:=(fD 10 D x).card
def cap(k I:Nat)(x:V):Nat:=if I.testBit x.1 then 1 else 2+k
def gQ(D:qD)(x:V)(j:Nat):Prop:=j<fF D x
abbrev SLive:=gQ
def Together(D:qD)(x c:V):Prop:=∃w,x∈fM 10 D w/\c∈fM 10 D w
def ineligNbrs(I:Nat)(x:V):List V:=(lR 10).filter (λ y=>(neigh x).testBit y.1&&I.testBit y.1)
def eligNbrs(I:Nat)(x:V):List V:=(lR 10).filter (λ y=>(neigh x).testBit y.1&&!I.testBit y.1)
def pinTarget(a:EI->qO)(x y:V):qO:=let p:=fW x y;sflip p.2 (a p.1)
def pinSlots(I:Nat)(a:EI->qO)(x:V):List qO:=let c:=ineligNbrs I x;let d:=eligNbrs I x;c.map (pinTarget a x)++match d with|[]=>[]|y::_=>[pinTarget a x y]
def yk(D:qD)(w:Nat):Nat:=∑ v∈fM 10 D w,2^v.1
def zl(D:qD):Option U0->Nat
 | none=>0
 | some u=>yk D u.1
def GoodLayout(D:qD)(k I:Nat)(d:V->Nat->qO)(g:EI->qO)(c:V->Nat)(a:Fin k->Option U0):Prop:=PB D c/\(∀u∈residualUnits 10 D c,∃t:Fin k,a t=some u)/\(∀t u,a t=some u->u∈residualUnits 10 D c)/\(∀i h u,a i=some u->a h=some u->i=h)/\(∀i h:Fin k,i.1<h.1->zl D (a i)<=zl D (a h))/\(∀x,fF D x<=cap k I x)/\(∀x j,d x j∈fD 10 D x)/\(∀x m l,m<fF D x->l<fF D x->d x m=d x l->m=l)/\(∀x e,e∈fD 10 D x->∃j<fF D x,d x j=e)/\gP D g/\(∀x:V,¬I.testBit x.1->∀r,(hr:r<(pinSlots I g x).length)->r<fF D x/\d x r=(pinSlots I g x)[r])
end
namespace A2
abbrev G1:=GoodLayout
abbrev L5{D k I W E F O}(g:G1 D k I W E F O):=g.2.2.2.2.2.1
abbrev L6{D k I W E F O}(g:G1 D k I W E F O):=g.2.2.2.2.2.2.1
abbrev L7{D k I W E F O}(g:G1 D k I W E F O):=g.2.2.2.2.2.2.2.1
abbrev L8{D k I W E F O}(g:G1 D k I W E F O):=g.2.2.2.2.2.2.2.2.1
abbrev L9{D k I W E F O}(g:G1 D k I W E F O):=g.2.2.2.2.2.2.2.2.2.1
end A2
section
open DagTools.A0 DagTools.A0r DagTools.A0b A1 A1b A2
lemma pinTarget_mem_W{D:qD}{a:EI->qO}(c:gP D a){x y:V}(i:adj x y):pinTarget a x y∈fD 10 D x/\sem_bar (pinTarget a x y)∈fD 10 D y:=by have d:=wt x y i;unfold pinTarget;have h:=(c (fW x y).2 (fW x y).1).1;have g:=(c (!(fW x y).2) (fW x y).1).1;rw[d.1] at h;rw[d.2,sflip_not] at g;exact⟨h,g⟩
lemma z6{D:qD}(h:SL D)(g:SC D){I:Nat}(c:mask I=ineligSet 10 D){a:EI->qO}(d:gP D a)(x:V):(pinSlots I a x).Nodup/\∀p∈pinSlots I a x,p∈fD 10 D x:=by have i:∀y∈ineligNbrs I x,adj x y/\y∈ineligSet 10 D:=λ y v=>by{simp only[ineligNbrs,p15,hC,true_and,bA] at v;exact⟨v.1,c▸mF.2 ⟨mU _,v.2⟩⟩};have j:∀y∈eligNbrs I x,adj x y/\y∉ineligSet 10 D:=λ y v=>by{simp only[eligNbrs,p15,hC,true_and,bA,Bool.not_eq_true'] at v;exact⟨v.1,by{rw[<-c,mask,mF];simp[v.2]}⟩};have u:∀y∈ineligNbrs I x,fM 10 D (fC D (sem_bar (pinTarget a x y)))={y}:=λ y v=>sP G0 h.1 g (i y v).2 (sM.1 (pinTarget_mem_W d (i y v).1).2).2.1;have H:((ineligNbrs I x).map (pinTarget a x)).Nodup:=Nodup.map_on (λ M h0 L Z U=>p48 (((u M h0).symm.trans (U.symm▸u L Z)))) ((List.nodup_finRange 10).filter _);constructor;{unfold pinSlots;cases r:eligNbrs I x with|nil=>{simpa using H}|cons y _=>{refine p19.2 ⟨H,List.nodup_singleton _,λ p h3 q hq U=>?_⟩;simp only[lS] at hq;subst hq U;obtain⟨z,hz,Q⟩:=p16.1 h3;have ⟨hxy,hyn⟩:=j y (r▸p14);have l:=(sM.1 (pinTarget_mem_W d hxy).2).2.1;rw[<-Q,u z hz,mS] at l;exact hyn (l▸(i z hz).2)}};{intro p m;unfold pinSlots at m;rcases g6.1 m with Y|X;{obtain⟨y,v,rfl⟩:=p16.1 Y;exact (pinTarget_mem_W d (i y v).1).1};{cases r:eligNbrs I x with|nil=>{simp[r] at X}|cons y _=>{simp only[r,lS] at X;subst X;exact (pinTarget_mem_W d (j y (r▸p14)).1).1}}}
lemma jn{D:qD}(h:SL D)(d:SC D){I:Nat}(c:mask I=ineligSet 10 D){a:EI->qO}(g:gP D a)(x:V):(pinSlots I a x).length<=fF D x:=by obtain⟨j,i⟩:=z6 h d c g x;rw[<-p21 j];exact p34 (λ p l=>i p (p18.1 l))
def b4(I:Nat)(x:V):Nat:=(ineligNbrs I x).length+if (eligNbrs I x).isEmpty then 0 else 1
lemma vx(I:Nat)(a:EI->qO)(x:V):(pinSlots I a x).length=b4 I x:=by unfold pinSlots b4;cases eligNbrs I x<;>simp
section
variable {D:qD}(H:SL D)(S:SC D){k I:Nat}(M:mask I=ineligSet 10 D){b:V->Nat}(P:PB D b)(K:(residualUnits 10 D b).card<=k)
include D H S k I M b P K
lemma jf(x:V):fF D x<=cap k I x:=by unfold cap fF;by_cases l:I.testBit x.1=p63;{simp only[l,ite_true];have j:x∈ineligSet 10 D:=M▸mF.2 ⟨mU _,l⟩;obtain⟨p,_,_,_,_,_,m,_⟩:=qe G0 H S j;change fD 10 D x={p} at m;rw[m,fw]};{simp[l];have i:=p34 (fI:({x}:tF V)∩fX 10 D⊆{x});have:=hO (residualUnits 10 D b) (λ u=>x∈fM 10 D u.1);have:=j7 G0 H S b P x;simp only[fw] at i;omega}
lemma pin_kill(x:V)(d:I.testBit x.1=p55)(g:2+k<b4 I x):False:=by obtain⟨l,m⟩:=get_edges H.1 S;have q:=jn H S M m x;rw[vx] at q;have p:=jf H S M P K x;simp only[cap,d,bF,ite_false] at p;omega
lemma construct_layout_from{d:EI->qO}(l:gP D d):∃(wire:V->Nat->qO) (order:Fin k->Option U0),G1 D k I wire d b order:=by classical let R:=(residualUnits 10 D b).toList;let A:=R.mergeSort (λ u v=>decide (yk D u.1<=yk D v.1));have U:A.Perm R:=List.mergeSort_perm R _;have h7:A.length=(residualUnits 10 D b).card:=U.length_eq.trans (Finset.length_toList _);have h4:A.Nodup:=U.nodup_iff.2 (nodup_toList _);have hf:A.Pairwise (λ u v=>yk D u.1<=yk D v.1):=(List.pairwise_mergeSort (le:=λ u v:U0=>decide (yk D u.1<=yk D v.1)) (λ _ _ _ h1 h2=>decide_eq_true (Nat.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2))) (λ _ _=>by simp[Nat.le_total]) R).imp of_decide_eq_true;let C:List (Option U0):=List.replicate (k-A.length) none++A.map some;have X:C.length=k:=by{simp[C,h7];omega};let order:Fin k->Option U0:=λ t=>C[t.1]'(X.symm▸t.2);let L (x:V):List qO:=if I.testBit x.1 then [] else pinSlots I d x;have Z (x:V):(L x).Nodup:=by{unfold L;split;exact .nil;exact (z6 H S M l x).1};have Y (x:V):∀p∈L x,p∈fD 10 D x:=by{unfold L;split;simp;exact (z6 H S M l x).2};let J (x:V):List qO:=L x++((fD 10 D x) \ (L x).toFinset).toList;have h3 (x:V):(J x).Nodup:=p19.2 ⟨Z x,nodup_toList _,λ p hp q hq h5=>by{subst h5;exact (mD.1 (p45.1 hq)).2 (p18.2 hp)}⟩;have N (x:V) (p:qO):p∈J x↔p∈fD 10 D x:=by{simp only[J,g6,p45,mD,p18];exact⟨λ | .inl h1=>Y x p h1 | .inr h2=>h2.1,λ h1=>if hp:p∈L x then .inl hp else .inr ⟨h1,hp⟩⟩};have B (x:V):(J x).length=fF D x:=by{rw[<-p21 (h3 x)];congr 1;ext p;simp[N]};let wire (x:V) (j:Nat):qO:=if hj:j<(J x).length then (J x)[j] else (J x)[0]'(by{rw[B];obtain⟨y,xy,_⟩:=G0.2.2.2 x x;obtain⟨p,hp,_⟩:=z5 G0 H.1 S xy;exact fz.2 ⟨p,hp⟩});refine⟨wire,order,P,?_,?_,?_,?_,jf H S M P K,?_,?_,?_,l,?_⟩;{intro u hu;obtain⟨ht,f1,rfl⟩:=p7 (U.mem_iff.2 (p45.2 hu));exact⟨⟨k-A.length+ht,by omega⟩,by{simp only[order,C];rw[hH (by simp)];simp}⟩};{intro t u hw;have Q:some u∈C:=hw▸hL _;simp only[C,g6,List.mem_replicate,p16] at Q;rcases Q with ⟨_,hh⟩|⟨v,hv,h5⟩;cases hh;cases h5;exact p45.1 (U.mem_iff.1 hv)};{intro t1 t2 u h1 h2;have f2:∀t:Fin k,order t=some u->k-A.length<=t.1:=λ t ht=>by{by_contra c;simp only[order,C] at ht;rw[hG (by{simp;omega}),List.getElem_replicate] at ht;cases ht};have:=f2 t1 h1;have:=f2 t2 h2;simp only[order,C] at h1 h2;rw[hH (by{simp;omega})] at h1 h2;simp only[hK,List.getElem_map,hI] at h1 h2;have:=(Nodup.getElem_inj_iff h4).1 (h1.trans h2.symm);exact Fin.ext (by omega)};{intro t1 t2 c;have hg:C.Pairwise (λ a b=>zl D a<=zl D b):=by{rw[List.pairwise_append];refine⟨List.pairwise_replicate.2 (.inr (Nat.le_refl 0)),List.pairwise_map.2 hf,?_⟩;intro a ha _ _;rw[List.eq_of_mem_replicate ha];exact nZ _};exact List.pairwise_iff_getElem.1 hg t1.1 t2.1 (X.symm▸t1.2) (X.symm▸t2.2) c};{intro x j;unfold wire;split<;>exact (N x _).1 (hL _)};{intro x j1 j2 hm hl h5;rw[<-B x] at hm hl;simp only[wire,hm,hl,hD] at h5;exact (Nodup.getElem_inj_iff (h3 x)).1 h5};{intro x e he;obtain⟨j,hj,rfl⟩:=p7 ((N x e).2 he);exact⟨j,B x▸hj,by simp[wire,hj]⟩};{intro x hy r hr;have hd:L x=pinSlots I d x:=by{simp[L,hy]};have c:r<(J x).length:=by{simp only[J,lA,hd];omega};exact⟨B x▸c,by{simp only[wire,c,hD,J];rw[hG (hd▸hr)];simp[hd]}⟩}
end
def resAt(D:qD){k:Nat}(a:Fin k->Option U0)(t:Nat)(x:V):Prop:=∃c:t<k,match a ⟨t,c⟩ with|none=>False|some u=>x∈fM 10 D u.1
def gR(D:qD)(x:V):Prop:=1<=(w5 10 D (q2 10 D {x})).card
abbrev has_merge:=gR
def opp(D:qD)(a:V->Nat->qO)(x:V)(j:Nat)(y:V):Prop:=gQ D x j/\y∈fM 10 D (fC D (sem_bar (a x j)))
def lab(D:qD)(a:V->Nat->qO)(x:V)(j:Nat)(y:V):Prop:=gQ D x j/\y∈fM 10 D (fC D (a x j))
def rsub(D:qD){k:Nat}(c:V->Nat->qO)(a:Fin k->Option U0)(t:Nat)(x:V)(j:Nat):Prop:=gQ D x j/\∀y:V,resAt D a t y->lab D c x j y
def ra(D:qD)(a:V->Nat->qO)(c:EI->qO)(s:Bool)(e:EI)(x:V)(j:Nat):Prop:=gQ D x j/\a x j=sflip s (c e)
def gT(D:qD)(a:V->Nat->qO)(c:EI->qO)(x:V)(j:Nat):Prop:=gQ D x j/\∀(e:EI) (s:Bool),a x j≠sflip s (c e)
abbrev free_slot:=gT
def gU(D:qD)(a:V->Nat->qO)(x:V)(j:Nat):Prop:=gQ D x j/\fM 10 D (fC D (sem_bar (a x j)))=∅
abbrev empty_opp:=gU
def after(D:qD)(a:V->Nat->qO)(c:EI->qO)(e:EI)(x:V)(j:Nat):Prop:=gQ D x j/\(c e).1<(a x j).1
def afree(D:qD)(a:V->Nat->qO)(c:EI->qO)(e:EI)(x:V)(j:Nat):Prop:=after D a c e x j/\gT D a c x j
def aempty(D:qD)(a:V->Nat->qO)(c:EI->qO)(e:EI)(x:V)(j:Nat):Prop:=after D a c e x j/\gU D a x j
lemma hmInelig{D:qD}(h:SL D)(c:SC D){x:V}(a:x∈ineligSet 10 D):¬gR D x:=by obtain⟨_,_,_,_,_,_,_,d⟩:=qe G0 h c a;simp[gR,d]
lemma ka{D:qD}{a:V->Nat->qO}{c:EI->qO}(g:gP D c){x:V}{j:Nat}(d:gU D a x j):gT D a c x j:=by refine⟨d.1,λ e s i=>?_⟩;have l:=(g (!s) e).1;rw[sflip_not,<-i] at l;have h:=(sM.1 l).2.1;rw[d.2] at h;exact nE _ h
lemma commonInelig{D:qD}(g:q0 10 D)(d:SC D){x y:V}(c:x∈ineligSet 10 D)(a:x≠y):¬Together D x y:=by rintro⟨w,hxw,hyw⟩;have h:=sP G0 g d c hxw;rw[h,mS] at hyw;exact a hyw.symm
section
variable {D:qD} {k I:Nat} {W:V->Nat->qO} {E:EI->qO} {F:V->Nat} {O:Fin k->Option U0}
lemma commonExit_of(h:SL D)(d:SC D)(c:G1 D k I W E F O){x y:V}(a:Together D x y):(∃j<cap k I x,lab D W x j y)\/(∃l<cap k I y,lab D W y l x):=by obtain⟨w0,v,U⟩:=a;let S:=(g5 (10+(tD D))).filter (λ w=>x∈fM 10 D w/\y∈fM 10 D w);have M:S.Nonempty:=⟨w0,mF.2 ⟨mR.2 (wx v),v,U⟩⟩;set w:=S.max' M;have ⟨H,hxw,hyw⟩:=mF.1 (p42 S M);have:=mR.1 H;have z:w+1<10+(tD D):=by{have p:w≠qb 10 D:=λ h0=>nE x (qn G0 d▸h0▸hxw);unfold qb at p;omega};obtain⟨g,hg⟩:=fz.1 (nT nO (h.2.1 w z));obtain⟨q,Q⟩:=mF.1 hg;have hg_lt':=mR.1 q;obtain⟨s,K⟩:=sX Q;have J:=K▸w7 h.1 hg_lt' s;have m:¬(x∈fM 10 D (10+g)/\y∈fM 10 D (10+g)):=λ r=>by{have:=p41 S (10+g) (mF.2 ⟨mR.2 (by omega),r⟩);omega};by_cases u:x∈fM 10 D (10+g);{obtain⟨l,i,X⟩:=L8 c y (g,s) (sM.2 ⟨hg_lt',K▸hyw,λ hy=>m ⟨u,hy⟩⟩);exact .inr ⟨l,lL i (L5 c y),i,X▸K▸hxw⟩};{obtain⟨j,i,Y⟩:=L8 c x (g,s) (sM.2 ⟨hg_lt',K▸hxw,u⟩);exact .inl ⟨j,lL i (L5 c x),i,Y▸K▸hyw⟩}
lemma labLive_of{x y:V}{j:Nat}(h:lab D W x j y):gQ D x j:=h.1
lemma selfLab_of(c:G1 D k I W E F O){x:V}{j:Nat}(a:gQ D x j):lab D W x j x:=⟨a,(sM.1 (L6 c x j)).2.1⟩
lemma labCommon_of(c:G1 D k I W E F O){x y:V}{j:Nat}(a:lab D W x j y):Together D x y:=⟨fC D (W x j),(sM.1 (L6 c x j)).2.1,a.2⟩
lemma live0_of(c:q0 10 D)(a:SC D)(x:V):gQ D x 0:=by obtain⟨y,d,_⟩:=G0.2.2.2 x x;obtain⟨p,g,_⟩:=z5 G0 c a d;exact fz.2 ⟨p,g⟩
lemma ineligNoRes_of(d:G1 D k I W E F O)(a:mask I=ineligSet 10 D){t:Nat}{x:V}(c:I.testBit x.1=p63):¬resAt D O t x:=by rintro⟨p,g⟩;cases j:O ⟨t,p⟩ with|none=>{rw[j] at g;exact g}|some u=>{rw[j] at g;have:=mR.1 (p44.1 (mF.1 (mD.1 (d.2.2.1 ⟨t,p⟩ u j)).1).1).2;exact (sE.1 (a▸mF.2 ⟨mU _,c⟩)) (zz.2 ⟨u.1,by omega,g⟩)}
lemma resCommon_of{t:Nat}{x y:V}(a:resAt D O t x)(c:resAt D O t y):Together D x y:=by obtain⟨g,a⟩:=a;obtain⟨_,c⟩:=c;cases d:O ⟨t,g⟩ with|none=>{rw[d] at a;exact a.elim}|some u=>{rw[d] at a c;exact⟨u.1,a,c⟩}
lemma adjCommon_of(h:SL D)(d:SC D){i a b:V}(c:i∈ineligSet 10 D)(j:adj i a)(g:adj i b):Together D a b:=by obtain⟨e,_,_,_,_,l,_,_⟩:=qe G0 h d c;exact⟨fC D (e.1,!e.2),l a j,l b g⟩
lemma ky(a:G1 D k I W E F O)(x:V):haveI:=cP (λ t:Fin k=>resAt D O t.1 x);((p53:tF (Fin k)).filter (λ t:Fin k=>resAt D O t.1 x)).card=((residualUnits 10 D F).filter (λ u=>x∈fM 10 D u.1)).card:=by classical let S:=(p53:tF (Fin k)).filter (λ t:Fin k=>resAt D O t.1 x);let T:=(residualUnits 10 D F).filter (λ u=>x∈fM 10 D u.1);have g:∀t∈S,∃u∈T,O t=some u:=λ t L=>by{obtain⟨_,c⟩:=(mF.1 L).2;cases p:O t with|none=>{rw[p] at c;exact c.elim}|some u=>{rw[p] at c;exact⟨u,mF.2 ⟨a.2.2.1 t u p,c⟩,rfl⟩}};have Y:=hN (λ t=>(O t).getD ⟨0,0⟩) (λ t L=>by{obtain⟨u,h,p⟩:=g t L;simpa[p] using h}) (λ R K Q J d=>by{obtain⟨v,_,m⟩:=g R K;obtain⟨P,_,l⟩:=g Q J;simp only[m,l,Option.getD_some] at d;exact a.2.2.2.1 R Q v m (d▸l)});have X:T.card<=S.card:=by{by_cases U:k=0;{subst U;have M:T=∅:=fE.2 (λ u h=>(a.2.1 u (mF.1 h).1).elim (λ t _=>t.elim0));simp[M]};choose f hf using a.2.1;refine hN (λ u=>if h:u∈residualUnits 10 D F then f u h else ⟨0,Nat.pos_of_ne_zero U⟩) (λ u h=>by{have ⟨j,y⟩:=mF.1 h;simp only[j,hD];exact mF.2 ⟨mU _,(f u j).2,by simpa[hf u j] using y⟩}) (λ v H P z d=>by{have r:=(mF.1 H).1;have q:=(mF.1 z).1;simp only[r,q,hD] at d;exact Option.some.inj ((hf v r).symm.trans (d▸hf P q))})};change S.card=T.card;omega
lemma sC{x:V}{d:Nat}{S:tF (Fin k)}[DecidablePred (λ t:Fin k=>resAt D O t.1 x)](i:S.card=k-d)(u:d+1<=((p53:tF (Fin k)).filter (λ t:Fin k=>resAt D O t.1 x)).card):∃t∈S,resAt D O t.1 x:=by by_contra l;push Not at l;let C:=(p53:tF (Fin k)).filter (λ t:Fin k=>resAt D O t.1 x);have m:(S∪C).card<=k:=by{simpa using card_le_univ (S∪C)};rw[fU (p36.2 λ t r p=>l t r (mF.1 p).2)] at m;omega
section
variable (H:SL D)(S:SC D)(G:G1 D k I W E F O)
include H S G
lemma wo(x:V):haveI:=cP (λ t:Fin k=>resAt D O t.1 x);fF D x+(w5 10 D (q2 10 D {x})).card<=2+((p53:tF (Fin k)).filter (λ t:Fin k=>resAt D O t.1 x)).card:=by classical have i:=j7 G0 H S F G.1 x;have d:=p34 (fI:({x}:tF V)∩fX 10 D⊆{x});simp only[fw] at d;have g:=ky G x;change ((p53:tF (Fin k)).filter (λ t:Fin k=>resAt D O t.1 x)).card=_ at g;unfold fF;omega
lemma sizeCode_of(x:V)(d:Nat)(A:tF (Fin k))(i:A.card=k-d)(a:gQ D x (2+d)):∃t∈A,resAt D O t.1 x:=by classical have q:=wo H S G x;exact sC i (by{unfold gQ at a;change _<=2+_ at q;omega})
lemma hmTop_of(x:V)(a:gR D x):¬gQ D x (1+k):=by classical intro g;have i:=wo H S G x;let C:=(p53:tF (Fin k)).filter (λ t:Fin k=>resAt D O t.1 x);have:C.card<=k:=by{simpa using card_le_univ C};unfold gQ at g;unfold gR at a;change _<=2+C.card at i;omega
lemma hmCode_of(x:V)(d:Nat)(A:tF (Fin k))(j:A.card=k-d)(c:gR D x)(a:gQ D x (1+d)):∃t∈A,resAt D O t.1 x:=by classical have r:=wo H S G x;exact sC j (by{unfold gQ at a;unfold gR at c;change _<=2+_ at r;omega})
lemma riSlots_of(p:mask I=ineligSet 10 D){x c:V}(m:x≠c)(q:I.testBit x.1=p55){j l:Nat}(d:j<l)(a:gQ D x l)(g:Together D x c):lab D W x j c\/lab D W x l c\/∃t:Fin k,resAt D O t.1 x/\¬resAt D O t.1 c:=by by_contra P;push Not at P;obtain⟨J,A,K⟩:=P;have y:x∈fX 10 D:=by_contra λ Q=>by{have U:=sE.2 Q;rw[<-p,mask,mF] at U;simp[q] at U};obtain⟨w,hw⟩:=g;obtain⟨e0,X⟩:=bb G0 H S F G.1 m y (λ u hu Y=>by{obtain⟨t,ht⟩:=G.2.1 u hu;obtain⟨_,L⟩:=K t ⟨t.2,by simpa[ht] using Y⟩;simpa[ht] using L}) hw;have v:=lt_trans d a;have z:W x j≠W x l:=λ h1=>Nat.ne_of_lt d (L7 G x j l v a h1);by_cases R:W x j=e0;exact A ⟨a,X (W x l) (L6 G x l) (λ h2=>z (R.trans h2.symm))⟩;exact J ⟨v,X (W x j) (L6 G x j) R⟩
lemma expose_of(x:V)(A:Nat)(d:independent (mask A))(i:∃a∈mask A,adj x a):∃j<cap k I x,gQ D x j/\∀c∈mask A,¬lab D W x j c:=by obtain⟨g,s,hlt,_,v,y,u⟩:=vc G0 H.1 S (mask A) d x i;obtain⟨j,p,r⟩:=L8 G x (g,s) (sM.2 ⟨hlt,v,y⟩);exact⟨j,lL p (L5 G x),p,λ c S q=>p36.1 u (r▸q.2) S⟩
end
lemma xb(S:tF V)(m:Nat)(a:∀v∈S,v.1<m):∑ v∈S,2^v.1<2^m:=by induction m generalizing S with|zero=>{simp[fE.2 λ v g=>hJ _ (a v g)]}|succ m ih=>{rw[<-fS S (λ v:V=>v.1<m)];have:=ih (S.filter (λ v=>v.1<m)) (λ v g=>(mF.1 g).2);have:∑ v∈S.filter (λ v=>¬v.1<m),2^v.1<=2^m:=by{by_cases j:(S.filter (λ v=>¬v.1<m)).Nonempty;{obtain⟨p,d⟩:=j;have c:p.1=m:=by{have:=a p (mF.1 d).1;have:=(mF.1 d).2;omega};have i:S.filter (λ v=>¬v.1<m)={p}:=by{ext v;simp only[mS];exact⟨λ g=>Fin.ext (by{have:=a v (mF.1 g).1;have:=(mF.1 g).2;omega}),λ h=>h▸d⟩};rw[i,Finset.sum_singleton,c]};{rw[fN.1 j];simp}};rw[Nat.pow_succ];omega}
lemma lex_step_bit(g:G1 D k I W E F O){t:Nat}(c:t+1<k)(x:V)(a:∀y:V,x.1<y.1->(resAt D O t y↔resAt D O (t+1) y))(d:resAt D O t x):resAt D O (t+1) x:=by classical by_contra K;let C (s:Nat):=univ.filter (λ v:V=>resAt D O s v);have i:∀(s:Nat)(r:s<k),zl D (O ⟨s,r⟩)=∑ v∈C s,2^v.1:=λ s r=>by{cases X:O ⟨s,r⟩ with|none=>{have:C s=∅:=by{ext v;simp[C,resAt,X]};simp[zl,this]}|some u=>{have:C s=fM 10 D u.1:=by{ext v;simp[C,resAt,r,X]};simp[zl,yk,this]}};let A:=univ.filter (λ v:V=>resAt D O t v);let B:=univ.filter (λ v:V=>resAt D O (t+1) v);have p:∑ v∈A,2^v.1<=∑ v∈B,2^v.1:=by{rw[<-i t (by omega),<-i (t+1) c];exact g.2.2.2.2.1 ⟨t,by omega⟩ ⟨t+1,c⟩ (by simp)};rw[<-fS A (λ v=>x.1<v.1),<-fS B (λ v=>x.1<v.1)] at p;have m:A.filter (λ v=>x.1<v.1)=B.filter (λ v=>x.1<v.1):=by{ext v;simp only[A,B,mF,mU,true_and];exact⟨λ⟨Q,q⟩=>⟨(a v q).1 Q,q⟩,λ⟨Q,q⟩=>⟨(a v q).2 Q,q⟩⟩};rw[m] at p;have P:2^x.1<=∑ v∈A.filter (λ v=>¬x.1<v.1),2^v.1:=hE (f:=λ v:V=>2^v.1) (λ _ _=>nZ _) (mF.2 ⟨mF.2 ⟨mU _,d⟩,Nat.lt_irrefl _⟩);have L:=xb (B.filter (λ v=>¬x.1<v.1)) x.1 (λ v U=>by{have:=mF.1 U;have:=(mF.1 this.1).2;have:v.1≠x.1:=λ h=>K (Fin.ext h▸this);omega});omega
def b8(D:qD)(x:V)(a b:Nat):Prop:=q5 10 D a b/\x∈fM 10 D a/\x∈fM 10 D b
section
variable (Q:q0 10 D){x:V}(M:w5 10 D (q2 10 D {x})=∅){a b c:Nat}
include Q x M a b c
lemma vy(d:b8 D x a c)(g:b8 D x b c):a=b:=by have l:=d.1.2.1;have j:c-10<(tD D):=by{have:=d.1.1;omega};have m:=j6 Q M j (by simpa[Nat.add_sub_of_le l] using d.2.2);rcases d.1.2.2 with u|r<;>rcases g.1.2.2 with q|p;{exact u.symm.trans q};{exact (m.2 ⟨u.symm▸d.2.1,p.symm▸g.2.1⟩).elim};{exact (m.2 ⟨q.symm▸g.2.1,r.symm▸d.2.1⟩).elim};{exact r.symm.trans p}
lemma kb(h:RT (b8 D x) a c)(g:RT (b8 D x) b c):RT (b8 D x) a b\/RT (b8 D x) b a:=by induction h with|refl=>{exact .inr g}|@tail u c q l ih=>{rcases rK g with rfl|⟨d,r,p⟩;{exact .inl (rT q l)};{have m:u=d:=vy Q M l p;subst m;exact ih r}}
end
lemma jg(h:SL D)(a:SC D){x:V}(c:w5 10 D (q2 10 D {x})=∅):∀(d:Nat) (g:Nat) (s:Bool),g<(tD D)->(tD D)-g<=d->x∈fM 10 D (fC D (g,s))->∃e∈fD 10 D x,fM 10 D (fC D (g,s))⊆fM 10 D (fC D e)/\(e=(g,s)\/(x∈fM 10 D (10+g)/\RT (b8 D x) (10+g) (fC D e))):=by intro d;induction d with|zero=>{intro _ _ _ _ _;omega}|succ d ih=>{intro g s K P X;by_cases i:x∈fM 10 D (10+g);{have L:=j6 h.1 c K i;have u:fM 10 D (fC D (g,s))⊆fM 10 D (10+g):=by{rw[yj h.1 K L.1];cases s<;>simp[fC]};have m:10+g+1<10+(tD D):=by{have:10+g≠qb 10 D:=λ R=>wd G0 x ((a (q9 x)).1 (w3.1 (R▸i)));unfold qb at this;omega};obtain⟨H,z⟩:=fz.1 (nT nO (h.2.1 (10+g) m));simp only[qg,mF,mR] at z;obtain⟨J,p⟩:=sX z.2;have M:g<H:=by{have:=h.1 H z.1;cases J<;>simp[fC] at p<;>omega};obtain⟨e,U,q,r⟩:=ih H J z.1 (by omega) (p▸i);refine⟨e,U,u.trans (p▸q),.inr ⟨i,?_⟩⟩;rcases r with rfl|⟨y,j⟩;rw[p];exact .head ⟨⟨by omega,by omega,by simpa using z.2⟩,i,y⟩ j};{exact⟨(g,s),sM.2 ⟨K,X,i⟩,Finset.Subset.refl _,.inl rfl⟩}}
lemma rsubPair(h:SL D)(l:SC D)(d:G1 D k I W E F O){t:Nat}{x:V}(c:resAt D O t x)(hM:w5 10 D (q2 10 D {x})=∅):∃u:U0,∃ht:t<k,O ⟨t,ht⟩=some u/\∃j1 j2:Nat,j1<fF D x/\j2<fF D x/\j1≠j2/\rsub D W O t x j1/\rsub D W O t x j2/\RT (b8 D x) u.1 (fC D (W x j1))/\RT (b8 D x) u.1 (fC D (W x j2)):=by obtain⟨ht,v⟩:=c;cases p:O ⟨t,ht⟩ with|none=>{rw[p] at v;exact v.elim}|some u=>{rw[p] at v;have X:=d.2.2.1 ⟨t,ht⟩ u p;have fc:2<=fanout D u.1:=by{have:=mR.1 (p44.1 (mF.1 (mD.1 X).1).1).2;omega};obtain⟨g1,L,g2,K,R⟩:=(p46 (s:=qg D u.1)).1 (by{unfold fanout at fc;omega});simp only[qg,mF,mR] at L K;obtain⟨s1,J⟩:=sX L.2;obtain⟨s2,H⟩:=sX K.2;obtain⟨e1,hi,h3,f7⟩:=jg h l hM (tD D) g1 s1 L.1 (by omega) (J▸v);obtain⟨e2,hg,h0,f6⟩:=jg h l hM (tD D) g2 s2 K.1 (by omega) (H▸v);have h5:e1≠e2:=λ hf=>by{subst hf;rcases f7 with rfl|⟨_,g⟩<;>rcases f6 with hh|⟨_,h2⟩;{exact R (congrArg p65 hh)};{have:=qk h.1 (λ _ _ h=>h.1) h2;rw[J] at this;have:=w7 h.1 K.1 s2;omega};{subst hh;have:=qk h.1 (λ _ _ h=>h.1) g;rw[H] at this;have:=w7 h.1 L.1 s1;omega};{have hu:∀z U Z Y,z<(tD D)->U<(tD D)->z≠U->fC D (z,Z)=u.1->fC D (U,Y)=u.1->RT (b8 D x) (10+z) (10+U)->False:=λ z U Z Y fb fa f8 f5 Q h4=>by{rcases rK h4 with hf|⟨w,hw,q⟩;exact f8 (by omega);have:=qk h.1 (λ _ _ h=>h.1) hw;have:=w7 h.1 fb Z;have M:=j6 h.1 hM fa q.2.2;have m:=q.1.2.2;rw[nA] at m;cases Y<;>simp[fC] at Q<;>rcases m with hA|hB;{omega};{exact M.2 ⟨Q.symm▸v,hB.symm▸q.2.1⟩};{exact M.2 ⟨hA.symm▸q.2.1,Q.symm▸v⟩};{omega}};rcases kb h.1 hM g h2 with fe|fd;exact hu g1 g2 s1 s2 L.1 K.1 R J H fe;exact hu g2 g1 s2 s1 K.1 L.1 R.symm H J fd}};obtain⟨j1,he,h9⟩:=L8 d x e1 hi;obtain⟨j2,hd,h8⟩:=L8 d x e2 hg;have r:∀j e,j<fF D x->W x j=e->fM 10 D u.1⊆fM 10 D (fC D e)->rsub D W O t x j:=λ j e hj hwe ha=>⟨hj,λ y ⟨_,h7⟩=>⟨hj,hwe▸ha (by{rw[p] at h7;exact h7})⟩⟩;have mkRT:∀g s e,g<(tD D)->(yx D g=u.1\/yf D g=u.1)->fC D (g,s)=u.1->(e=(g,s)\/(x∈fM 10 D (10+g)/\RT (b8 D x) (10+g) (fC D e)))->RT (b8 D x) u.1 (fC D e):=λ g s e hg hq hf hc=>by{rcases hc with rfl|⟨hx,hrt⟩;{rw[hf]};{exact .head ⟨⟨by omega,by omega,by simpa using hq⟩,v,hx⟩ hrt}};exact⟨u,ht,p,j1,j2,he,hd,λ hje=>h5 (h9.symm.trans (hje▸h8)),r j1 e1 he h9 (J▸h3),r j2 e2 hd h8 (H▸h0),h9▸mkRT g1 s1 e1 L.1 L.2 J f7,h8▸mkRT g2 s2 e2 K.1 K.2 H f6⟩}
lemma rsubTwo_of(h:SL D)(l:SC D)(d:G1 D k I W E F O){t:Nat}{x:V}(c:resAt D O t x)(i:¬gR D x)(a:Nat):∃j<cap k I x,j≠a/\rsub D W O t x j:=by have hM:w5 10 D (q2 10 D {x})=∅:=g8.1 (by{unfold gR at i;omega});obtain⟨_,_,_,j1,j2,he,hd,hne,r1,r2,_,_⟩:=rsubPair h l d c hM;by_cases g:j1=a;{exact⟨j2,lL hd (L5 d x),λ hm=>hne (g.trans hm.symm),r2⟩};{exact⟨j1,lL he (L5 d x),g,r1⟩}
lemma rsubDisj_of(h:SL D)(l:SC D)(d:G1 D k I W E F O){t1 t2:Nat}{x y1 y2:V}{j:Nat}(c1:resAt D O t1 x)(c2:resAt D O t2 x)(hy1:resAt D O t1 y1)(hn2:¬resAt D O t2 y1)(hy2:resAt D O t2 y2)(hn1:¬resAt D O t1 y2)(i:¬gR D x)(hj:gQ D x j)(hr1:¬rsub D W O t1 x j)(hr2:¬rsub D W O t2 x j):5<=fF D x:=by have hM:w5 10 D (q2 10 D {x})=∅:=g8.1 (by{unfold gR at i;omega});have hsub:∀{a b},RT (b8 D x) a b->fM 10 D a⊆fM 10 D b:=λ r=>by{induction r with|refl=>{exact Finset.Subset.refl _}|@tail u v _ s ih=>{have l0:=s.1.2.1;have j0:v-10<(tD D):=by{have:=s.1.1;omega};have m:=j6 h.1 hM j0 (by simpa[Nat.add_sub_of_le l0] using s.2.2);have hv:fM 10 D v=fM 10 D (yx D (v-10))∪fM 10 D (yf D (v-10)):=(by simpa[Nat.add_sub_of_le l0] using yj h.1 j0 m.1);refine ih.trans ?_;rw[hv];rcases s.1.2.2 with hu|hu;{rw[hu];exact Finset.subset_union_left};{rw[hu];exact Finset.subset_union_right}}};obtain⟨u1,ht1,p1,a1,a2,ha1,ha2,ha12,ra1,ra2,ta1,ta2⟩:=rsubPair h l d c1 hM;obtain⟨u2,ht2,p2,b1,b2,hb1,hb2,hb12,rb1,rb2,tb1,tb2⟩:=rsubPair h l d c2 hM;have h12:∀a b,RT (b8 D x) u1.1 (fC D (W x a))->RT (b8 D x) u2.1 (fC D (W x b))->a≠b:=λ a b ta tb hab=>by{subst hab;rcases kb h.1 hM ta tb with h1|h2;{obtain⟨_,hy1m⟩:=hy1;rw[p1] at hy1m;exact hn2 ⟨ht2,by rw[p2];exact hsub h1 hy1m⟩};{obtain⟨_,hy2m⟩:=hy2;rw[p2] at hy2m;exact hn1 ⟨ht1,by rw[p1];exact hsub h2 hy2m⟩}};have:=h12 a1 b1 ta1 tb1;have:=h12 a1 b2 ta1 tb2;have:=h12 a2 b1 ta2 tb1;have:=h12 a2 b2 ta2 tb2;have:j≠a1:=λ e=>hr1 (e▸ra1);have:j≠a2:=λ e=>hr1 (e▸ra2);have:j≠b1:=λ e=>hr2 (e▸rb1);have:j≠b2:=λ e=>hr2 (e▸rb2);have:j<fF D x:=hj;omega
lemma oppSelf_of(a:q0 10 D)(c:G1 D k I W E F O)(x:V)(j:Nat):¬opp D W x j x:=by rintro⟨_,d⟩;have h:=L6 c x j;have ⟨hlt,hx1,hxn⟩:=sM.1 h;have i:=sA a h;apply hxn;rw[qm a hlt i,mI];rcases hwe:W x j with ⟨g,s⟩;rw[hwe] at hx1 d;cases s<;>simp[fC,sem_bar] at hx1 d ⊢;{exact⟨hx1,d⟩};{exact⟨d,hx1⟩}
section
variable (Q:q0 10 D)(G:G1 D k I W E F O){x y:V}{j:Nat}
include Q G x y j
lemma labOppMerge_of(c:lab D W x j y)(a:opp D W x j y):gR D y:=by rcases c with ⟨_,c⟩;rcases a with ⟨_,a⟩;have m:=L6 G x j;have i:=(sM.1 m).1;have l:y∈fM 10 D (yx D (W x j).1)/\y∈fM 10 D (yf D (W x j).1):=by{rcases hwe:W x j with ⟨g,s⟩;rw[hwe] at c a;cases s<;>simp[fC,sem_bar] at c a ⊢;exact⟨c,a⟩;exact⟨a,c⟩};exact fz.2 ⟨_,mF.2 ⟨mR.2 i,q8.2 (by{rw[qm Q i (sA Q m),mI];exact l}),q8.2 l.1,q8.2 l.2⟩⟩
lemma smateAny_of(c:lab D W x j y)(a:¬opp D W x j y):∃l<cap k I y,gQ D y l/\W y l=W x j:=by rcases c with ⟨i,c⟩;have p:=L6 G x j;have q:=(sM.1 p).1;obtain⟨l,h,m⟩:=L8 G y (W x j) (sM.2 ⟨q,c,λ r=>a ⟨i,sU Q q (sA Q p) (!(W x j).2) r⟩⟩);exact⟨l,lL h (L5 G y),h,m⟩
lemma omateAny_of(a:opp D W x j y)(c:¬lab D W x j y):∃l<cap k I y,gQ D y l/\W y l=sem_bar (W x j):=by rcases a with ⟨i,a⟩;have q:=L6 G x j;have m:=(sM.1 q).1;obtain⟨l,h,p⟩:=L8 G y (sem_bar (W x j)) (sM.2 ⟨m,a,λ u=>c ⟨i,sU Q m (sA Q q) (W x j).2 u⟩⟩);exact⟨l,lL h (L5 G y),h,p⟩
end
section
variable (H:SL D)(S:SC D)(G:G1 D k I W E F O)(M:mask I=ineligSet 10 D)
include H S G M
lemma inelig_unique_slot{y:V}(d:I.testBit y.1=p63):fD 10 D y={W y 0}/\∀a,adj y a->a∈fM 10 D (fC D (sem_bar (W y 0))):=by have p:y∈ineligSet 10 D:=M▸mF.2 ⟨mU _,d⟩;obtain⟨e,_,_,_,_,m,j,_⟩:=qe G0 H S p;change fD 10 D y={e} at j;have l:=mS.1 (j▸L6 G y 0);rw[l];exact⟨j,m⟩
lemma ineligOpp_bar_eq{x y:V}(d:x≠y)(g:I.testBit y.1=p63){j:Nat}(a:opp D W x j y):sem_bar (W x j)=W y 0:=by have r:=L6 G x j;have m:=(sM.1 r).1;have q:sem_bar (W x j)∈fD 10 D y:=sM.2 ⟨m,a.2,λ z=>d (mS.1 (sP G0 H.1 S (M▸mF.2 ⟨mU _,g⟩) (sU H.1 m (sA H.1 r) (W x j).2 z)▸(sM.1 r).2.1))⟩;rwa[(inelig_unique_slot H S G M g).1,mS] at q
lemma ineligOppNF_of{x y:V}(g:x≠y)(l:I.testBit y.1=p63){j:Nat}(c:opp D W x j y):¬gT D W E x j:=by intro r;obtain⟨a,z,_⟩:=G0.2.2.2 y y;set p:=fW y a;have u:sflip p.2 (E p.1)∈fD 10 D y:=by{simpa[p,(wt y a z).1] using (L9 G p.2 p.1).1};rw[(inelig_unique_slot H S G M l).1,mS] at u;exact r.2 p.1 (!p.2) (by rw[sflip_not,u,<-ineligOpp_bar_eq H S G M g l c,sem_bar_bar])
lemma ineligOppInelig_of{i j:V}(g:I.testBit i.1=p63)(l:I.testBit j.1=p63)(_hne:i≠j):¬opp D W i 0 j:=by rintro⟨_,r⟩;have y:i∈ineligSet 10 D:=M▸mF.2 ⟨mU _,g⟩;have u:j∈ineligSet 10 D:=M▸mF.2 ⟨mU _,l⟩;obtain⟨a,v,_⟩:=G0.2.2.2 i i;have p:=(inelig_unique_slot H S G M g).2 a v;rw[sP G0 H.1 S u r,mS] at p;subst a;exact (j5 G0 H S v).elim (sE.1 y) (sE.1 u)
end
lemma ineligFilter_of(h:SL D)(m:SC D)(H:Bzero 10 D=0)(r:G1 D k I W E F O)(J:mask I=ineligSet 10 D){i y d:V}(K:I.testBit i.1=p63)(j:¬adj i y)(p:adj i d)(q:opp D W i 0 y):∃l<cap k I d,aempty D W E (fW i d).1 d l/\gT D W E d l/\¬lab D W d l y/\∀x2:V,adj i x2->lab D W d l x2/\¬opp D W d l x2:=by have fj:i∈ineligSet 10 D:=J▸mF.2 ⟨mU _,K⟩;have hx:=zv G0 h m H fj;obtain⟨L,hq,fb,he,hg,_,h6,_⟩:=qe G0 h m fj;have g3:W i 0=L:=by{simpa[fD,h6] using (L6 r) i 0};have U:(E (fW i d).1).1=L.1:=by{have hW:=(L9 r (fW i d).2 (fW i d).1).1;rw[(wt i d p).1] at hW;simp only[fD,h6,mS] at hW;simpa[sflip] using congrArg p65 hW};have M:∀w,fO D (λ _:V=>p55) w=p55:=λ w=>if z:w<10+(tD D) then jy h.1 _ (λ _=>p55) (λ _ _=>rfl) (λ j _=>by cases gZ D j<;>rfl) w z else z0 D _ w (by omega);have Y:RT (q5 10 D) i.1 (10+L.1):=(yu (λ _ _ h=>h.1) (wn h.1 (q9 i) (λ _=>p55) i (λ _ hk=>by simp[q9,hk]) (fC D L) (by{rw[w3.1 (he▸m0 i),M];decide}))).tail (qs hq L.2);have h7:q7 10 D (10+L.1) (qb 10 D):=by{rcases j8 h.1 hx Y with g9|⟨fy,_⟩;{have:=qk h.1 (λ _ _ h=>h) g9;have:=lP h.2.2;rw[show 10+L.1=qb 10 D by{unfold qb at *;omega}];exact .refl};{exact fy}};have hf:fO D (q1 i y) (10+L.1)=p63:=by{rw[qd h.1 _ hq L.2,fb,gop_true,q3 h.1 (he▸m0 i) (by simp[q1]),q3 h.1 (by simpa[g3,sem_bar] using q.2) (by simp[q1])];rfl};have f4:fO D (q1 i y) (qb 10 D)=p55:=by{cases hv:fO D (q1 i y) (qb 10 D);rfl;exfalso;obtain⟨a,b,fc,ha,hb⟩:=(m _).1 hv;simp only[q1,bO,dT] at ha hb;rcases ha with rfl|rfl<;>rcases hb with rfl|rfl;{exact G0.2.1 _ fc};{exact j fc};{exact j (G0.1 _ _ fc)};{exact G0.2.1 _ fc}};have fk:∀{a b},q7 10 D a b->fO D (q1 i y) a=p63->fO D (q1 i y) b=p55->∃u v,q7 10 D a u/\q5 10 D u v/\fanout D u=1/\fO D (q1 i y) u=p63/\fO D (q1 i y) v=p55:=by{intro a b gc;induction gc using rI with|refl=>{intro h1 h2;rw[h1] at h2;cases h2}|@head a c f7 _ ih=>{intro ha hb;cases hs:fO D (q1 i y) c;{exact⟨a,c,.refl,f7.1,f7.2,ha,hs⟩};{obtain⟨u,v,ga,B⟩:=ih hs hb;exact⟨u,v,.head f7 ga,B⟩}}};obtain⟨u,v,h5,ff,fa,fr,h9⟩:=fk h7 hf f4;obtain⟨g,s,P,rfl,rfl⟩:=y3.1 ff;have h4:gZ D g=p63/\fO D (q1 i y) (fC D (g,!s))=p55:=by{rw[qd h.1 _ P s,fr] at h9;cases fs:gZ D g;simp[fs] at h9;exact⟨rfl,by simpa[fs,gop_true] using h9⟩};have f9:L.1<g:=by{have:=qk h.1 (λ _ _ h=>h.1) h5;have:=w7 h.1 P s;omega};have Z:q7 10 D i.1 (10+L.1):=by{rcases j9 Y with ge|⟨b,gd,fx⟩;exact ge;exact absurd (ze G0 h.1 m fj gd fx▸y7 h.1 H fx) gk};have Q:q7 10 D i.1 (fC D (g,s)):=Z.trans h5;have hy:=Q.tail ⟨qs P s,fa⟩;have X:fM 10 D (fC D (g,s))=∅:=by{have hn:=kh h.1 (q9 i) (λ _=>p55) i (λ _ hk=>by simp[q9,hk]) (10+L.1) (fC D (g,s)) (vn h.1 Z (qk h.1 (λ _ _ h=>h.1) h5)) (by{rw[M];exact p54.2 (λ ht=>nE i (hg▸w3.2 ht))});rw[M] at hn;exact fE.2 λ z hz=>p58 ((w3.1 hz).symm.trans ((mS.1 (yw G0 h.1 m i _ (wp h.1 Q) hz))▸hn))};have f1:∀x2,adj i x2->x2∈fM 10 D (fC D (g,!s))/\x2∉fM 10 D (10+g):=λ x2 fd=>by{have hp:fO D (q1 i x2) (10+g)≠fO D (q9 x2) (10+g):=λ fl=>by{have fu:=k6 h.1 (q1 i x2) (q9 x2) i (λ _ hk=>by simp[q1,q9,hk]) (10+g) (wp h.1 hy) fl;rw[(m _).2 (yv fd),p54.2 (λ ht=>wd G0 x2 ((m _).1 ht))] at fu;cases fu};have fh:=x9 h.1 (q9 x2) (q1 i x2) (kg (by simp[q1])) (10+g);have ⟨R,hh⟩:fO D (q1 i x2) (10+g)=p63/\fO D (q9 x2) (10+g)=p55:=by{cases f6:fO D (q1 i x2) (10+g)<;>cases f5:fO D (q9 x2) (10+g)<;>first|exact⟨rfl,rfl⟩|exact absurd (f6.trans f5.symm) hp|exact absurd (fh f5) (by{rw[f6];decide})};rw[qd h.1 _ P s,h4.1,gop_true,bA] at R;have fn:=vd h.1 i P (!s) (by simpa[p60] using Q) (by simpa[p60] using fa) (q1 i x2) (q9 x2) (λ _ hk=>by simp[q1,q9,hk]);exact⟨w3.2 (fn▸R.2),λ hm=>p58 ((w3.1 hm).symm.trans hh)⟩};obtain⟨l,h3,hl⟩:=L8 r d (g,!s) (sM.2 ⟨P,(f1 d p).1,(f1 d p).2⟩);have hd:gU D W d l:=⟨h3,by{rw[hl,sK];exact X}⟩;exact⟨l,lL h3 (L5 r d),⟨⟨h3,by{rw[U,hl];exact f9}⟩,hd⟩,ka (L9 r) hd,λ⟨_,hj⟩=>p58 ((q3 h.1 (hl▸hj) (x:=q1 i y) (by simp[q1])).symm.trans h4.2),λ x2 fd=>⟨⟨h3,hl▸(f1 x2 fd).1⟩,λ⟨_,ho⟩=>nE x2 (by{rw[hl,sK,X] at ho;exact ho})⟩⟩
end
def es(D:qD)(a:EI->qO)(s:Bool)(e:EI)(x:V):Prop:=x∈fM 10 D (fC D (sflip s (a e)))
def lt_e(a:EI->qO)(d c:EI):Prop:=(a d).1<(a c).1
def sgate(a:EI->qO)(d c:EI):Prop:=(a d).1=(a c).1
def jh(D:qD)(u v:V)(g:Nat):Prop:=g<(tD D)/\gZ D g=p63/\∃s:Bool,u∈fM 10 D (fC D (g,s))/\v∉fM 10 D (fC D (g,s))/\v∈fM 10 D (fC D (g,!s))/\u∉fM 10 D (fC D (g,!s))
def fZ(D:qD)(a:EI->qO)(e:EI):Prop:=∃g,g≠(a e).1/\jh D (ep0 e) (ep1 e) g
abbrev has_sec:=fZ
def sec_pair(D:qD)(a:V->Nat->qO)(c:EI->qO)(e:EI)(d g:Nat):Prop:=gQ D (ep0 e) d/\gQ D (ep1 e) g/\(a (ep0 e) d).1≠(c e).1/\a (ep1 e) g=sem_bar (a (ep0 e) d)
def wy(D:qD)(x:V->Bool)(d c:Nat):Prop:=RT (λ a b=>q5 10 D a b/\fO D x a=p63/\fO D x b=p63) d c
def zm(D:qD)(d c:Nat):Prop:=RT (λ a b=>q5 10 D a b/\fM 10 D a=∅/\fanout D a=1) d c
def xv(D:qD)(b:Nat):Prop:=fM 10 D b=∅/\2<=fanout D b
def gS(D:qD)(a:Nat):Prop:=zm D a (qb 10 D)/\fM 10 D (qb 10 D)=∅
abbrev stay_empty:=gS
def hit_b(D:qD)(a:Nat):Prop:=Bzero 10 D=1/\∃b0,zm D a b0/\xv D b0
def gX(D:qD)(a:Nat)(z:V):Prop:=∃r,zm D a r/\z∈fM 10 D r/\∀t∈fM 10 D r,z<=t
abbrev pick_z:=gX
def h0Prop(D:qD)(a:V->Nat->qO)(c:EI->qO)(d:EI)(z:V)(l:Nat):Prop:=after D a c d z l/\(opp D a z l (ep0 d)\/opp D a z l (ep1 d))
def kc(D:qD)(c:EI->qO)(d:EI)(a b:V)(h:Nat):Prop:=h<(tD D)/\wy D (q1 (ep0 d) (ep1 d)) (10+(c d).1) (10+h)/\fO D (q1 a b) (10+h)=p55
noncomputable def wi(D:qD)(c:EI->qO)(d:EI)(a b:V):Nat:=open Classical in if hex:∃h,kc D c d a b h then p22 hex else 0
def bc(D:qD)(c:EI->qO)(d:EI)(a b:V)(g:EI):Prop:=fZ D c d\/(fO D (q1 a b) (10+(c d).1)=p63/\wy D (q1 (ep0 d) (ep1 d)) (10+(c d).1) (10+(c g).1)/\wy D (q1 (ep0 d) (ep1 d)) (10+(c g).1) (10+wi D c d a b)/\(c g).1<wi D c d a b)
def efhProp(D:qD)(c:V->Nat->qO)(d:EI->qO)(h:EI)(a b:V)(i:EI)(g:V)(l:Nat):Prop:=after D c d i g l/\¬opp D c g l a/\¬opp D c g l b/\(opp D c g l (ep0 h)\/opp D c g l (ep1 h))
def eseProp(D:qD)(c:EI->qO)(h:EI)(a b:V)(i:EI)(g:V)(d:EI):Prop:=lt_e c i d/\(es D c p55 d g\/es D c p63 d g)/\bc D c h a b d
def mescProp(D:qD)(w:V->Nat->qO)(e:EI->qO)(d:EI)(am:Nat)(z:V)(l:Nat):Prop:=(opp D w z l (ep0 d)\/opp D w z l (ep1 d))/\∃e':EI,!am.testBit e'.1/\∃s:Bool,ra D w e s e' z l
section
open Finset (min'_mem min'_le)
variable {D:qD} {k I:Nat} {W:V->Nat->qO} {E:EI->qO} {F:V->Nat} {O:Fin k->Option U0}
abbrev AR:=wy
abbrev EC:=zm
abbrev s2:=@q1 10
lemma sF(h:q0 10 D){u a b:V}{w:Nat}(m:u∈fM 10 D w)(e:u=a\/u=b)(v:fO D (s2 a b) w=p55):False:=by cases (q3 h m (x:=s2 a b) (by rcases e with rfl|rfl<;>simp[q1])).symm.trans v
lemma ji(a:q0 10 D){u v:V}{g:Nat}(c:jh D u v g):∃s:Bool,(g,s)∈fD 10 D u/\(g,!s)∈fD 10 D v/\u∈fM 10 D (fC D (g,s))/\v∈fM 10 D (fC D (g,!s)):=by obtain⟨d,p,s,m,i,l,j⟩:=c;exact⟨s,sM.2 ⟨d,m,λ h=>j (sU a d p (!s) h)⟩,sM.2 ⟨d,l,λ h=>i (sU a d p s h)⟩,m,l⟩
lemma secNotRa0_of{e:EI}{a c:Nat}(d:sec_pair D W E e a c):¬ra D W E p55 e (ep0 e) a:=λ g=>d.2.2.1 (by rw[g.2,sflip_false])
lemma secNotRa1_of{e:EI}{c a:Nat}(d:sec_pair D W E e c a):¬ra D W E p63 e (ep1 e) a:=λ g=>by have i:(W (ep1 e) a).1=(W (ep0 e) c).1:=by{rw[d.2.2.2];rfl};have h:(W (ep1 e) a).1=(E e).1:=by{rw[g.2,sflip_true];rfl};exact d.2.2.1 (i.symm.trans h)
lemma secEq_of{e:EI}{c a:Nat}(d:sec_pair D W E e c a)(y:V):(lab D W (ep1 e) a y↔opp D W (ep0 e) c y)/\(lab D W (ep0 e) c y↔opp D W (ep1 e) a y):=by have _:=d.1;have _:=d.2.1;constructor<;>(simp only[lab,opp,d.2.2.2,sem_bar_bar];tauto)
section
variable (Q:q0 10 D)
include Q
lemma hasSecAny_of(a:G1 D k I W E F O){e:EI}(c:fZ D E e):∃ju<cap k I (ep0 e),∃jv<cap k I (ep1 e),sec_pair D W E e ju jv:=by obtain⟨g,m,r⟩:=c;obtain⟨s,l,j,_,_⟩:=ji Q r;obtain⟨ju,i,p⟩:=L8 a (ep0 e) (g,s) l;obtain⟨jv,h,q⟩:=L8 a (ep1 e) (g,!s) j;exact⟨ju,lL i (L5 a _),jv,lL h (L5 a _),i,h,by rw[p];exact m,by rw[p,q];rfl⟩
lemma fG(a:gP D E)(e:EI):jh D (ep0 e) (ep1 e) (E e).1:=by have d:=a p55 e;have h:=a p63 e;rw[sflip_false] at d;rw[sflip_true] at h;obtain⟨g,j,_⟩:=sM.1 d.1;obtain⟨_,i,_⟩:=sM.1 h.1;exact⟨g,sA Q d.1,(E e).2,by simpa[endpoint] using j,by simpa[endpoint] using d.2,by simpa[endpoint,sem_bar] using i,by simpa[endpoint,sem_bar] using h.2⟩
lemma qp{x:V->Bool}{a b:Nat}(h:AR D x a b):a<=b:=qk Q (λ _ _ d=>d.1) h
lemma vq(u v:V):∀w:Nat,fO D (s2 u v) w=p63->u∉fM 10 D w->v∉fM 10 D w->∃g,jh D u v g/\AR D (s2 u v) (10+g) w:=by intro w;induction w using sI with|ind w ih=>{intro q l i;by_cases A:w<10;{rw[qa D _ w A] at q;simp only[q1,bO,dT] at q;rcases q with L|L;exact absurd (w3.2 (by{rw[qa D _ w A,q9,L];simp})) l;exact absurd (w3.2 (by{rw[qa D _ w A,q9,L];simp})) i};by_cases m:w-10<(tD D);{set j:=w-10;let X:=yx D j;let Y:=yf D j;have c:w=10+j:=by{omega};have:=Q j m;have y:=c▸qs m p55;have r:=c▸qs m p63;have p:=q;rw[c,qu Q _ j m] at q;cases P:gZ D j;{rw[P,gop_false,bO] at q;rw[c,yj Q m P,mN,not_or] at l i;rcases q with z|d;obtain⟨g,K,J⟩:=ih (X) (by omega) z l.1 i.1;exact⟨g,K,J.tail ⟨y,z,p⟩⟩;obtain⟨g,K,J⟩:=ih (Y) (by omega) d l.2 i.2;exact⟨g,K,J.tail ⟨r,d,p⟩⟩};{rw[P,gop_true,bA] at q;by_cases U:u∉fM 10 D (X)/\v∉fM 10 D (X);{obtain⟨g,K,J⟩:=ih (X) (by omega) q.1 U.1 U.2;exact⟨g,K,J.tail ⟨y,q.1,p⟩⟩};by_cases R:u∉fM 10 D (Y)/\v∉fM 10 D (Y);{obtain⟨g,K,J⟩:=ih (Y) (by omega) q.2 R.1 R.2;exact⟨g,K,J.tail ⟨r,q.2,p⟩⟩};rw[c,qm Q m P,mI] at l i;have ha':u∈fM 10 D (X)\/v∈fM 10 D (X):=by{tauto};have hb':u∈fM 10 D (Y)\/v∈fM 10 D (Y):=by{tauto};refine⟨j,⟨m,P,?_⟩,c▸.refl⟩;rcases ha' with M|z;{have H:=λ h=>l ⟨M,h⟩;have d:=hb'.resolve_left H;exact⟨p55,M,λ h=>i ⟨h,d⟩,d,H⟩};{have d:=λ h=>i ⟨z,h⟩;have H:=hb'.resolve_right d;exact⟨p63,H,d,z,λ h=>l ⟨h,H⟩⟩}}};{rw[z0 D _ w (by omega)] at q;cases q}}
lemma y8{e:EI}(a:¬fZ D E e){w:Nat}(h:fO D (s2 (ep0 e) (ep1 e)) w=p63)(d:ep0 e∉fM 10 D w)(c:ep1 e∉fM 10 D w):AR D (s2 (ep0 e) (ep1 e)) (10+(E e).1) w:=by obtain⟨g,m,l⟩:=vq Q (ep0 e) (ep1 e) w h d c;have:g=(E e).1:=by{by_contra j;exact a ⟨g,j,m⟩};rwa [this] at l
lemma jt(c:SC D){e:EI}(a:¬fZ D E e):AR D (s2 (ep0 e) (ep1 e)) (10+(E e).1) (qb 10 D):=by have g:=qn G0 c;exact y8 Q a ((c _).2 (yv (xk e))) (by rw[g];exact nE _) (by rw[g];exact nE _)
lemma y6{x:V->Bool}{z:V}{a b:Nat}(h:AR D x a b)(c:z∈fM 10 D a)(d:z∉fM 10 D b):∃g s,g<(tD D)/\10+g<=b/\fO D x (10+g)=p63/\AR D x a (fC D (g,s))/\z∈fM 10 D (fC D (g,s))/\z∉fM 10 D (10+g)/\AR D x (10+g) b:=by induction h using rI with|refl=>{exact absurd c d}|@head u v l p ih=>{by_cases m:z∈fM 10 D v;{obtain⟨g,s,P,M,L,K,J,H,y⟩:=ih m;exact⟨g,s,P,M,L,rH l K,J,H,y⟩};{obtain⟨g,s,r,rfl,rfl⟩:=y3.1 l.1;exact⟨g,s,r,qp Q p,l.2.2,rR,c,m,p⟩}}
lemma w8{a b:Nat}(c:EC D a b):a<=b:=qk Q (λ _ _ h=>h.1) c
end
section
variable {R:Nat->Nat->Prop}(Q:q0 10 D)(Y:∀x y,R x y->q5 10 D x y){a c q:Nat}(M:EC D a c)(N:RT R a q)
include R Q Y a c q M N
lemma y9:RT R c q\/(EC D a q/\EC D q c/\q≠c):=by induction M using rI with|refl=>{exact .inl N}|@head u v j m ih=>{rcases rC N with rfl|⟨r,p,l⟩;{have:=wb Q j.1;have:=w8 Q m;exact .inr ⟨rR,rH j m,by omega⟩};{have:r=v:=qj (Y _ _ p) j.1 j.2.2;subst this;rcases ih l with K|⟨J,H,z⟩;exact .inl K;exact .inr ⟨rH j J,H,z⟩}}
lemma qx(h:c<=q):RT R a c/\RT R c q:=by induction M using rI with|refl=>{exact⟨rR,N⟩}|@head u v m r ih=>{rcases rC N with rfl|⟨z,l,p⟩;{have:=wb Q m.1;have:=w8 Q r;omega};{have:z=v:=qj (Y _ _ l) m.1 m.2.2;subst this;obtain⟨J,H⟩:=ih p;exact⟨rH l J,H⟩}}
lemma qr(i:q<=c):EC D a q:=by rcases y9 Q Y M N with m|⟨p,_,_⟩;{have:=qk Q Y m;have l:q=c:=by{omega};rw[l];exact M};{exact p}
end
section
variable (Q:q0 10 D)
include Q
lemma z7{a d c:Nat}(m:EC D a d)(l:EC D a c)(i:¬(fM 10 D d=∅/\fanout D d=1))(g:¬(fM 10 D c=∅/\fanout D c=1)):d=c:=by rcases y9 Q (λ _ _ h=>h.1) m l with v|⟨_,u,q⟩;{rcases rC v with rfl|⟨_,p,_⟩;{rfl};{exact absurd p.2 i}};{rcases rC u with r|⟨_,p,_⟩;{exact absurd r q};{exact absurd p.2 g}}
lemma pickUniq_of{w:Nat}{c a:V}(i:gX D w c)(g:gX D w a):c=a:=by obtain⟨y,u,l,p⟩:=i;obtain⟨v,r,j,m⟩:=g;have q:=z7 Q u r (λ h=>by rw[h.1] at l;exact nE _ l) (λ h=>by rw[h.1] at j;exact nE _ j);subst q;exact le_antisymm (p a j) (m c l)
end
lemma sameStay_of{d c:EI}(a:sgate E d c)(g:gS D (10+(E d).1)):gS D (10+(E c).1):=by unfold sgate at a;rw[<-a];exact g
lemma samePick_of{d c:EI}{z:V}(a:sgate E d c)(g:gX D (10+(E d).1) z):gX D (10+(E c).1) z:=by unfold sgate at a;rw[<-a];exact g
section
variable (H:SL D)(S:SC D)
include H S
lemma yq(c:Bzero 10 D<=1):∀d w,w<10+(tD D)->qb 10 D-w=d->gS D w\/hit_b D w\/∃z:V,gX D w z:=by intro d;induction d using sI with|ind d ih=>{intro w P M;by_cases j:(fM 10 D w).Nonempty;{exact .inr (.inr ⟨(fM 10 D w).min' j,w,rR,min'_mem _ j,min'_le _⟩)};rw[fN] at j;by_cases p:w=qb 10 D;{exact .inl ⟨p▸rR,qn G0 S⟩};have:=lP H.2.2;have q:w+1<10+(tD D):=by{unfold qb at p;omega};have L:=H.2.1 w q;by_cases v:2<=fanout D w;{exact .inr (.inl ⟨by{by_cases J:Bzero 10 D=0;exact absurd (y7 H.1 J v) (j▸gk);omega},w,rR,j,v⟩)};have m:fanout D w=1:=by{omega};obtain⟨g,i⟩:=fz.1 (show 0<(qg D w).card by{unfold fanout at m;omega});simp only[qg,mF,mR] at i;have l:q5 10 D w (10+g):=⟨by omega,by omega,by{rw[nA];exact i.2}⟩;have:=wb H.1 l;have y:q5 10 D w (10+g)/\fM 10 D w=∅/\fanout D w=1:=⟨l,j,m⟩;rcases ih (qb 10 D-(10+g)) (by{unfold qb at M ⊢;omega}) (10+g) (by omega) rfl with ⟨hch,hso⟩|⟨u,b0,hcb,his⟩|⟨z,r,hcr,hzr,hmin⟩;{exact .inl ⟨.head y hch,hso⟩};{exact .inr (.inl ⟨u,b0,.head y hcb,his⟩)};{exact .inr (.inr ⟨z,r,.head y hcr,hzr,hmin⟩)}}
lemma stepAny_of(c:Bzero 10 D<=1)(g:gP D E)(a:EI):gS D (10+(E a).1)\/hit_b D (10+(E a).1)\/∃z:V,gX D (10+(E a).1) z:=yq H S c _ (10+(E a).1) (by have i:=(sM.1 (g p55 a).1).1;rw[sflip_false] at i;omega) rfl
lemma stepAny0_of(g:Bzero 10 D=0)(d:gP D E)(a:EI):gS D (10+(E a).1)\/∃z:V,gX D (10+(E a).1) z:=by rcases stepAny_of H S (by omega) d a with i|l|j;{exact .inl i};{exact absurd l.1 (by omega)};{exact .inr j}
lemma pickZH0_of(j:G1 D k I W E F O){c:EI}{z:V}(d:gX D (10+(E c).1) z)(a:¬fZ D E c):∃l<cap k I z,h0Prop D W E c z l:=by classical set u:=ep0 c;set v:=ep1 c;obtain⟨r,hcr,hzr,_⟩:=d;have L:=(qx H.1 (λ _ _ d=>d.1) hcr (jt H.1 S a) (by{have:=wx hzr;have:=lP H.2.2;unfold qb;omega})).2;have hb:∃g,g<(tD D)/\fO D (s2 u v) (10+g)=p63/\z∉fM 10 D (10+g)/\∃s:Bool,AR D (s2 u v) r (fC D (g,s))/\z∈fM 10 D (fC D (g,s)):=by{obtain⟨g,s,h1,_,h3,h4,h5,h6,_⟩:=y6 H.1 L hzr (by{rw[qn G0 S];exact nE _});exact⟨g,h1,h3,h6,s,h4,h5⟩};set g0:=p22 hb;obtain⟨m,J,A,s,K,p⟩:=p24 hb;have hW:(g0,s)∈fD 10 D z:=sM.2 ⟨m,p,A⟩;have M:=sA H.1 hW;obtain⟨l,q,h7⟩:=L8 j z (g0,s) hW;have Z:r<10+g0:=lt_of_le_of_lt (qp H.1 K) (w7 H.1 m s);refine⟨l,lL q (L5 j z),⟨q,by{have:=w8 H.1 hcr;rw[h7];dsimp;omega}⟩,?_⟩;set y:=fC D (g0,!s);rw[show (opp D W z l u\/opp D W z l v)↔(u∈fM 10 D y\/v∈fM 10 D y) by simp[opp,gQ,q,h7,sem_bar,y]];by_contra Y;push Not at Y;have h8:fO D (s2 u v) y=p63:=by{rw[qd H.1 _ m s,M,gop_true,bA] at J;exact J.2};have R:z∉fM 10 D y:=λ Q=>A <| by{rw[qm H.1 m M,mI];cases s<;>simp only[fC,y,Bool.not_false,p61] at p Q ⊢;exact⟨p,Q⟩;exact⟨Q,p⟩};rcases y9 H.1 (λ _ _ d=>d.1) hcr (y8 H.1 a h8 Y.1 Y.2) with ha|⟨_,h0,U⟩;{obtain⟨g1,s1,h1,h2,h3,h4,h5,h6,_⟩:=y6 H.1 ha hzr R;have hk:y<10+p22 hb:=w7 H.1 m (!s);exact p23 hb (by omega:g1<p22 hb) ⟨h1,h3,h6,s1,h4,h5⟩};{rcases rC h0 with he|⟨_,h9,X⟩;exact U he;have:=w8 H.1 (qj h9.1 (qs m (!s)) h9.2.2▸X);omega}
end
lemma ve(d:SC D){a b:V}(c:¬adj a b):fO D (s2 a b) (qb 10 D)=p55:=by cases j:fO D (s2 a b) (qb 10 D) with|false=>{rfl}|true=>{exfalso;obtain⟨x,y,g,i,h⟩:=(d (s2 a b)).1 j;simp only[q1,bO,dT] at i h;rcases i with rfl|rfl<;>rcases h with rfl|rfl;{exact G0.2.1 _ g};{exact c g};{exact c (G0.1 _ _ g)};{exact G0.2.1 _ g}}
section
variable (H:SL D)(S:SC D){d:EI}{a b:V}(U:¬adj a b)(N:¬fZ D E d)
include H S d a b U N
lemma ya:kc D E d a b (wi D E d a b)/\∀w<10+wi D E d a b,AR D (s2 (ep0 d) (ep1 d)) (10+(E d).1) w->fO D (s2 a b) w=p63:=by classical have v:=lP H.2.2;have q:10+((tD D)-1)=qb 10 D:=by{unfold qb;omega};have p:∃g,kc D E d a b g:=⟨(tD D)-1,by omega,q▸jt H.1 S N,q▸ve S U⟩;rw[show wi D E d a b=p22 p by{unfold wi;exact hD p}];refine⟨p24 p,λ w z u=>?_⟩;have:=qp H.1 u;have m:w-10<p22 p:=by{omega};have l:10+(w-10)=w:=by{omega};cases y:fO D (s2 a b) w;exact absurd ⟨lt_trans m (p24 p).1,l.symm▸u,l.symm▸y⟩ (p23 p m);rfl
lemma zo{s:Bool}(g:AR D (s2 (ep0 d) (ep1 d)) (10+(E d).1) (fC D (wi D E d a b,s))):gZ D (wi D E d a b)=p63/\a∉fM 10 D (fC D (wi D E d a b,!s))/\b∉fM 10 D (fC D (wi D E d a b,!s))/\(ep0 d∈fM 10 D (fC D (wi D E d a b,!s))\/ep1 d∈fM 10 D (fC D (wi D E d a b,!s))):=by set y:=wi D E d a b;obtain⟨⟨m,u,z⟩,hmin⟩:=ya H S U N;have p:=w7 H.1 m s;have hvf':=z;rw[qd H.1 _ m s,hmin _ p g] at hvf';have J:gZ D y=p63:=by{cases A:gZ D y;rw[A,gop_false] at hvf';simp at hvf';rfl};have l:fO D (s2 a b) (fC D (y,!s))=p55:=by{rw[J,gop_true,p64] at hvf';exact hvf'};have q:fO D (s2 (ep0 d) (ep1 d)) (10+y)=p63:=by{rcases rK u with M|⟨_,_,P⟩;exact absurd (lt_of_le_of_lt (qp H.1 g) p) (M▸lt_irrefl _);exact P.2.2};have r:fO D (s2 (ep0 d) (ep1 d)) (fC D (y,!s))=p63:=by{rw[qd H.1 _ m s,J,gop_true,bA] at q;exact q.2};refine⟨J,λ R=>sF H.1 R (.inl rfl) l,λ Q=>sF H.1 Q (.inr rfl) l,by_contra λ v=>?_⟩;push Not at v;exact p58 ((hmin _ (w7 H.1 m (!s)) (y8 H.1 N r v.1 v.2)).symm.trans l)
lemma x3(A:fO D (s2 a b) (10+(E d).1)=p63):gZ D (wi D E d a b)=p63:=by obtain⟨⟨_,m,q⟩,_⟩:=ya H S U N;rcases rK m with u|⟨_,r,v⟩;{rw[<-u,q] at A;cases A};{obtain⟨g,s,_,y,p⟩:=y3.1 v.1;have z:g=wi D E d a b:=by{omega};rw[z] at p;subst p;exact (zo H S U N r).1}
end
lemma maskClosure_of(H:SL D)(S:SC D)(B:Bzero 10 D=0)(G:G1 D k I W E F O){d:EI}{am cm:Nat}(hd:am.testBit d.1=p63)(hnsec:¬fZ D E d)(hstay:∀e:EI,am.testBit e.1=p63->¬gS D (10+(E e).1))(hpick:∀e:EI,am.testBit e.1=p63->∀z:V,cm.testBit z.1=p55->¬gX D (10+(E e).1) z)(hfree:∀z:V,cm.testBit z.1=p63->∀l<cap k I z,¬gT D W E z l)(hopp:∀z:V,cm.testBit z.1=p63->∀l<cap k I z,∀y:V,cm.testBit y.1=p63->¬opp D W z l y)(hesc:∀z:V,cm.testBit z.1=p63->∀l<cap k I z,¬mescProp D W E d am z l):False:=by set x:=s2 (ep0 d) (ep1 d);let Good (w:Nat):Prop:=(∃z:V,cm.testBit z.1=p63/\z∈fM 10 D w)\/(∃e:EI,am.testBit e.1=p63/\EC D (10+(E e).1) w);have hstep:{a b:Nat}->{e:EI}->am.testBit e.1=p63->EC D (10+(E e).1) a->q5 10 D a b->(∃z:V,cm.testBit z.1=p63/\z∈fM 10 D a)\/EC D (10+(E e).1) b:=by{intro a b e he hza hab;rcases stepAny0_of H S B (L9 G) e with hs|⟨z,hzx⟩;{exact absurd hs (hstay e he)};{have hzc:cm.testBit z.1=p63:=by{cases hcb:cm.testBit z.1;{exact absurd hzx (hpick e he z hcb)};{rfl}};obtain⟨r,hzr,hzmr,_⟩:=hzx;rcases y9 H.1 (λ _ _ h=>h.1) hzr hza with hra|⟨_,har,hne⟩;{rcases rC hra with rfl|⟨_,hr,_⟩;{exact .inl ⟨z,hzc,hzmr⟩};{rw[hr.2.1] at hzmr;exact absurd hzmr (nE z)}};{rcases rC har with rfl|⟨c,ha,_⟩;{exact absurd rfl hne};{have hcb:c=b:=qj ha.1 hab ha.2.2;exact .inr (hza.tail ⟨hab,ha.2.1,ha.2.2⟩)}}}};have hGood:∀w,AR D x (10+(E d).1) w->Good w:=by{intro w;induction w using sI with|ind b ih=>{intro har;rcases rK har with rfl|⟨a,hara,hstep_ab⟩;{exact .inr ⟨d,hd,rR⟩};{have hga:Good a:=ih a (wb H.1 hstep_ab.1) hara;have hfrom_z:(∃z:V,cm.testBit z.1=p63/\z∈fM 10 D a)->Good b:=by{rintro⟨z,hzc,hza⟩;obtain⟨g,s,hg,rfl,rfl⟩:=y3.1 hstep_ab.1;by_cases hzb:z∈fM 10 D (10+g);{exact .inl ⟨z,hzc,hzb⟩};{have hW:(g,s)∈fD 10 D z:=sM.2 ⟨hg,hza,hzb⟩;have hA:=sA H.1 hW;obtain⟨l,hl,hWl⟩:=L8 G z (g,s) hW;have hlcap:l<cap k I z:=lL hl (L5 G z);have hnf:=hfree z hzc l hlcap;have ⟨e',s',he'⟩:∃e' s',W z l=sflip s' (E e'):=by{unfold gT at hnf;push Not at hnf;exact hnf hl};have hge':(E e').1=g:=by{have:=congrArg p65 (hWl.symm.trans he');cases s'<;>simpa[sflip] using this.symm};set y:=fC D (g,!s);have hOy:fO D x y=p63:=by{have hOb:=hstep_ab.2.2;rw[qd H.1 x hg s,hA,gop_true,bA] at hOb;exact hOb.2};have hy_eq:fC D (sem_bar (W z l))=y:=by{rw[hWl];rfl};by_cases hopp_uv:ep0 d∈fM 10 D y\/ep1 d∈fM 10 D y;{have hopp':opp D W z l (ep0 d)\/opp D W z l (ep1 d):=hopp_uv.imp (λ h=>⟨hl,hy_eq.symm▸h⟩) (λ h=>⟨hl,hy_eq.symm▸h⟩);have ham':am.testBit e'.1=p63:=by{cases hbit:am.testBit e'.1;{exact absurd ⟨hopp',e',by simp[hbit],s',hl,he'⟩ (hesc z hzc l hlcap)};{rfl}};exact .inr ⟨e',ham',by{rw[hge'];exact rR}⟩};{push Not at hopp_uv;have hgy:Good y:=ih y (w7 H.1 hg (!s)) (y8 H.1 hnsec hOy hopp_uv.1 hopp_uv.2);rcases hgy with ⟨z',hz'c,hz'y⟩|⟨e'',he'',hze''⟩;{exact absurd ⟨hl,hy_eq.symm▸hz'y⟩ (hopp z hzc l hlcap z' hz'c)};{rcases hstep he'' hze'' (qs hg (!s)) with ⟨z'',hz''c,hz''y⟩|hzb'';{exact absurd ⟨hl,hy_eq.symm▸hz''y⟩ (hopp z hzc l hlcap z'' hz''c)};{exact .inr ⟨e'',he'',hzb''⟩}}}}};rcases hga with hza|⟨e,he,hza⟩;{exact hfrom_z hza};{rcases hstep he hza hstep_ab.1 with hza'|hzb';{exact hfrom_z hza'};{exact .inr ⟨e,he,hzb'⟩}}}}};rcases hGood (qb 10 D) (jt H.1 S hnsec) with ⟨z,_,hzq⟩|⟨e,he,hze⟩;{rw[qn G0 S] at hzq;exact nE z hzq};{exact hstay e he ⟨hze,qn G0 S⟩}
lemma bcInit_of(h:SL D)(i:SC D)(j:gP D E){c:EI}{a b:V}(d:¬adj a b)(g:(es D E p55 c a/\es D E p63 c b)\/(es D E p55 c b/\es D E p63 c a)):bc D E c a b c:=by by_cases q:fZ D E c;{exact .inl q};{right;have p:=fG h.1 j c;have l:fO D (s2 a b) (10+(E c).1)=p63:=by{rw[qd h.1 _ p.1 (E c).2,p.2.1,gop_true];have K:fC D ((E c).1,(E c).2)=fC D (sflip p55 (E c)):=by{simp[sflip_false]};have J:fC D ((E c).1,!(E c).2)=fC D (sflip p63 (E c)):=by{simp[sflip_true,sem_bar]};rw[K,J];rcases g with ⟨y,v⟩|⟨v,y⟩<;>{rw[q3 h.1 y (by simp[q1]),q3 h.1 v (by simp[q1])];rfl}};obtain⟨⟨_,m,r⟩,_⟩:=ya h i d q;have H:=qp h.1 m;have z:(E c).1≠wi D E c a b:=λ u=>by{rw[u,r] at l;cases l};exact⟨l,rR,m,by omega⟩}
section
variable (H:SL D)(S:SC D)(G:G1 D k I W E F O){d:EI}{a b:V}(U:¬adj a b)
include H S G d a b U
lemma zu(g:¬fZ D E d){s:Bool}(j:AR D (s2 (ep0 d) (ep1 d)) (10+(E d).1) (fC D (wi D E d a b,s)))(i:fM 10 D (fC D (wi D E d a b,s))=∅):∃z:V,(z=ep0 d\/z=ep1 d)/\z≠a/\z≠b/\∃l<cap k I z,gQ D z l/\(W z l).1=wi D E d a b/\gU D W z l:=by set M:=wi D E d a b;have v:=(ya H S U g).1.1;obtain⟨ht,X,B,R⟩:=zo H S U g j;have A:fM 10 D (10+M)=∅:=fE.2 λ c P=>nE _ (i▸sU H.1 v ht s P);have y:∀{z:V},z=ep0 d\/z=ep1 d->z∈fM 10 D (fC D (M,!s))->∃z:V,(z=ep0 d\/z=ep1 d)/\z≠a/\z≠b/\∃l<cap k I z,gQ D z l/\(W z l).1=M/\gU D W z l:=λ {z} L r=>by{obtain⟨l,u,Q⟩:=L8 G z (M,!s) (sM.2 ⟨v,r,A▸nE _⟩);exact⟨z,L,λ Y=>X (by{rw[Y] at r;exact r}),λ Y=>B (by{rw[Y] at r;exact r}),l,lL u (L5 G z),u,by rw[Q],u,by{rw[Q,sK];exact i}⟩};exact R.elim (y (.inl rfl)) (y (.inr rfl))
lemma qq(j:¬fZ D E d){m:Nat}(_hws_lt:m<10+wi D E d a b)(i:AR D (s2 (ep0 d) (ep1 d)) (10+(E d).1) m)(A:AR D (s2 (ep0 d) (ep1 d)) m (10+wi D E d a b))(r:EC D m (10+wi D E d a b)):∃z:V,(z=ep0 d\/z=ep1 d)/\z≠a/\z≠b/\∃l<cap k I z,gQ D z l/\(W z l).1=wi D E d a b/\gU D W z l:=by rcases rK r with Q|⟨p,K,y⟩;{omega};{obtain⟨g,s,_,M,B⟩:=y3.1 y.1;have P:g=wi D E d a b:=by{omega};rw[P] at B;exact zu H S G U j (B▸i.trans (qx H.1 (λ _ _ L=>L.1) K A (le_of_lt (wb H.1 y.1))).1) (B▸y.2.1)}
lemma vf(i:¬fZ D E d)(p:fO D (s2 a b) (10+(E d).1)=p63){m:Nat}(_hws_lt:m<10+wi D E d a b)(q:AR D (s2 (ep0 d) (ep1 d)) (10+(E d).1) m)(j:AR D (s2 (ep0 d) (ep1 d)) m (10+wi D E d a b)){c:V}(v:gX D m c):EC D m (10+wi D E d a b)\/(c≠a/\c≠b/\gR D c)\/(∃l<cap k I c,gQ D c l/\m<10+(W c l).1/\((¬opp D W c l a/\¬opp D W c l b/\(opp D W c l (ep0 d)\/opp D W c l (ep1 d)))\/gT D W E c l))\/(∃e3:EI,m<10+(E e3).1/\(es D E p55 e3 c\/es D E p63 e3 c)/\bc D E d a b e3):=by set hs:=wi D E d a b;obtain⟨r,hcr,hd,_⟩:=v;by_cases hm:10+hs<=r;{exact .inl (qr H.1 (λ _ _ hp=>hp.1) hcr j hm)};obtain⟨X,Z⟩:=qx H.1 (λ _ _ hp=>hp.1) hcr j (by omega);by_cases J:c∈fM 10 D (10+hs);{obtain⟨⟨Q,_,h3⟩,_⟩:=ya H S U i;have hf:=mI.1 (qm H.1 Q (x3 H S U i p)▸J);exact .inr (.inl ⟨λ he=>sF H.1 J (.inl he) h3,λ he=>sF H.1 J (.inr he) h3,fz.2 ⟨hs,mF.2 ⟨mR.2 Q,q8.2 J,q8.2 hf.1,q8.2 hf.2⟩⟩⟩)};obtain⟨g,s,L,_,h8,Y,M,h7,h5⟩:=y6 H.1 Z hd J;have hW:(g,s)∈fD 10 D c:=sM.2 ⟨L,M,h7⟩;obtain⟨l,A,P⟩:=L8 G c (g,s) hW;have B:m<10+g:=by{have:=w8 H.1 hcr;have:=qp H.1 Y;have:=w7 H.1 L s;omega};have K:=(q.trans X).trans Y;by_cases ha:g=hs;{subst ha;obtain⟨_,hl,hk,hi⟩:=zo H S U i K;exact .inr (.inr (.inl ⟨l,lL A (L5 G c),A,P▸B,.inl (by simpa[opp,gQ,A,P,sem_bar] using And.intro hl (And.intro hk hi))⟩))};by_cases h6:gT D W E c l;{exact .inr (.inr (.inl ⟨l,lL A (L5 G c),A,P▸B,.inr h6⟩))};have ⟨e3,s3,hb⟩:∃e3 s3,W c l=sflip s3 (E e3):=by{unfold gT at h6;push Not at h6;exact h6 A};have h2:(E e3).1=g:=by{simpa[sflip,P] using (congrArg p65 hb).symm};have h4:fO D (s2 (ep0 d) (ep1 d)) (fC D (g,s))=p63:=by{rw[qd H.1 _ L s,sA H.1 hW,gop_true,bA] at h8;exact h8.1};have R:es D E s3 e3 c:=by{unfold es;rw[<-hb,P];exact M};exact .inr (.inr (.inr ⟨e3,by omega,by{cases s3;exact .inl R;exact .inr R},.inr ⟨p,h2.symm▸K.tail ⟨qs L s,h4,h8⟩,h2.symm▸h5,by omega⟩⟩))
lemma bcStay_of{j:EI}(i:bc D E d a b j)(g:gS D (10+(E j).1)):fZ D E d\/∃z:V,(z=ep0 d\/z=ep1 d)/\z≠a/\z≠b/\∃l<cap k I z,aempty D W E j z l:=by rcases i with q|⟨_,K,r,v⟩;{exact .inl q};{by_cases q:fZ D E d;{exact .inl q};{right;have:=(ya H S U q).1.1;have:=lP H.2.2;obtain⟨z,Q,P,M,l,y,u,J,L⟩:=qq H S G U q (by omega) K r (qr H.1 (λ _ _ R=>R.1) g.1 r (by{unfold qb;omega}));exact⟨z,Q,P,M,l,y,⟨u,J▸v⟩,L⟩}}
lemma bcPick_of{A:EI}{c:V}(m:bc D E d a b A)(j:gX D (10+(E A).1) c):fZ D E d\/(∃z:V,(z=ep0 d\/z=ep1 d)/\z≠a/\z≠b/\∃l<cap k I z,aempty D W E A z l)\/(c≠a/\c≠b/\gR D c)\/(∃l<cap k I c,efhProp D W E d a b A c l\/afree D W E A c l)\/(∃e3:EI,e3≠A/\eseProp D E d a b A c e3):=by rcases m with v|⟨Q,B,y,J⟩;{exact o1 v};{by_cases v:fZ D E d;{exact o1 v};{rcases vf H S G U v Q (by omega) B y j with K|hm|⟨l,u,r,h2,R⟩|⟨e3,C,X,Z⟩;{obtain⟨z,P,h1,h0,l,u,r,M,Y⟩:=qq H S G U v (by omega) B y K;exact o2 (o1 ⟨z,P,h1,h0,l,u,⟨r,by{rw[M];exact J}⟩,Y⟩)};{exact o2 (o2 (o1 hm))};{exact o2 (o2 (o2 (o1 ⟨l,u,R.elim (λ⟨ha,hb,P⟩=>o1 ⟨⟨r,by omega⟩,ha,hb,P⟩) (λ h3=>o2 ⟨⟨r,by omega⟩,h3⟩)⟩)))};{exact o2 (o2 (o2 (o2 ⟨e3,λ he=>by{rw[he] at C;omega},by{unfold lt_e;omega},X,Z⟩)))}}}
end
end
end
end
abbrev CellKill (k I m s:Nat):Prop:=∃t c x:List Nat,∀v:Nat->Bool,(∀u,Rup.enS k I m s t c x u=true->Rup.Holds v (Rup.expS k I m t c x u))->False
namespace P3
abbrev CK:=CellKill
open DagTools
open Rup
open PriorG11.SharedCases renaming GoodLayout->V0,SLive->V1,autPerm->V2,ineligOpp_bar_eq->V3,lt_e->V4,maskImage->V5,pinSlots->V6,pinTarget->V7,relabelEdge_fst->V8,relabel_residualUnits_mem->V9,resAt->Va,sflip->Vb,sflip_not->Vc
open DagTools renaming StrictLive->Vd,ineligSet->Ve,residualUnits->Vf,sem_bar->Vg,sem_bar_bar->Vh,sem_mem_W->Vi
open Rup renaming avoidMask->Vj,edgeIdxS->Vk,eligNbrsN->Vl,ineligNbrsN->Vm,nbrsN->Vn
open List renaming mem_map->Vo,length_map->Vp,range->Vq
open Nat renaming reduceLT->Vr
abbrev Ei:=EdgeIdx
abbrev Ws:=V->Nat->Slot
abbrev Es:=Ei->Slot
abbrev Os k:=Fin k->Option (Σ _:Nat,Nat)
abbrev LN:=List Nat
abbrev F(x:Nat):V:=Fin.ofNat 10 x
abbrev J(e:Nat):Ei:=Fin.ofNat 14 e
noncomputable def bP(P:Prop):Bool:=@decide P (Classical.propDecidable P)
@[local simp] lemma bt{P:Prop}:bP P=true <->P:=@decide_eq_true_iff P (Classical.propDecidable P)
@[local simp] lemma bf{P:Prop}:bP P=false <->¬P:=@decide_eq_false_iff_not P (Classical.propDecidable P)
lemma sA{a b}:((a&&b)=true)=(a=true/\b=true):=Bool.and_eq_true a b
lemma sD{p} [Decidable p]:(decide p=true)=p:=decide_eq_true_eq
lemma sQ{α} [BEq α] [LawfulBEq α] {a b:α}:(a==b)=true <->a=b:=beq_iff_eq
lemma sN{α} [BEq α] [LawfulBEq α] {a b:α}:(a != b)=true <->a≠b:=bne_iff_ne
lemma sB{a}:((!a)=true)=(a=false):=Bool.not_eq_true' a
lemma sC{a b c:Prop}:(a/\b)/\c <->a/\b/\c:=and_assoc
lemma sT{α}{a b:α}:(if True then a else b)=a:=ite_true a b
lemma sF{α}{a b:α}:(if False then a else b)=b:=ite_false a b
abbrev mo{a b:Nat} (h:a<b):=Nat.mod_eq_of_lt h
abbrev T{P Q:Prop} (h:P <->Q):=h.1
abbrev W{P Q:Prop} (h:P <->Q):=h.2
lemma f0v{x}(h:x<10):(F x).1=x:=mo h
lemma f0n{x y}(hx:x<10)(hy:y<10)(h:x≠y):F x≠F y:=λ q=>h (by rw[<-f0v hx,<-f0v hy,q])
lemma f0e(x:V):F x.1=x:=Fin.ext (mo x.2)
lemma f4e(e:Ei):J e.1=e:=Fin.ext (mo e.2)
lemma aM(n r:Nat):r&&&(2^n-1)<2^n:=by rw[Nat.and_two_pow_sub_one_eq_mod];exact Nat.mod_lt _ (Nat.two_pow_pos n)
lemma a1(r:Nat):r&&&1<2:=aM 1 r
lemma a4(r:Nat):r&&&15<16:=aM 4 r
lemma a6(r:Nat):r&&&63<64:=aM 6 r
lemma bnot1{s}(h:s<2):((1-s)==1)=!(s==1):=by rcases (by omega:s=0\/s=1) with rfl|rfl<;>rfl
abbrev mF{α p} [DecidablePred p] {s:Finset α} {a}:=@Finset.mem_filter α p _ s a
abbrev mU{α} [Fintype α]:=@Finset.mem_univ α _
abbrev mG{α β} [DecidableEq β] {f:α->β} {s a}:=@Finset.mem_image α β _ f s a
abbrev lR{n m}:=@List.mem_range n m
abbrev lF{α p} {l:List α} {a}:=@List.mem_filter α p l a
lemma finE{n x}(h:x<n):∃u:Fin n,u.1=x:=⟨⟨x,h⟩,rfl⟩
lemma eN{e}(h:e<14):F (ep0N e)=ep0 (J e)/\F (ep1N e)=ep1 (J e)/\ep0N e<10/\ep1N e<10:=by obtain⟨u,rfl⟩:=finE h;revert u;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
abbrev e0q{e} (h:e<14):=(eN h).1
abbrev e1q{e} (h:e<14):=(eN h).2.1
abbrev e0l{e} (h:e<14):=(eN h).2.2.1
abbrev e1l{e} (h:e<14):=(eN h).2.2.2
lemma enq{s e}(d:s<2)(he:e<14):F (epN s e)=endpoint (s==1) (J e):=by obtain⟨u,rfl⟩:=finE d;obtain⟨v,rfl⟩:=finE he;revert u v;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma enl{s e}(he:e<14):epN s e<10:=by unfold epN;split<;>[exact e0l he;exact e1l he]
lemma aBi{x y}(d:x<10)(hy:y<10):adjB x y=true <->adj (F x) (F y):=by obtain⟨u,rfl⟩:=finE d;obtain⟨v,rfl⟩:=finE hy;revert u v;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma cNq(k I){x}(d:x<10):capN k I x=cap k I (F x):=by unfold capN inIB cap;simp[mo d]
lemma c5{k I x j}(h:j<capN k I x)(_:k<=3:=by omega):j<5:=by unfold capN at h;split at h<;>omega
lemma c5V{k I j}{z:V}(h:j<cap k I z)(_:k<=3:=by omega):j<5:=c5 (by rw[cNq k I z.2,f0e];exact h)
lemma iB{I x}(d:x<10)(h:inIB I x=true):I.testBit (F x).1=true:=by rw[f0v d];exact h
lemma nB{I x}(d:x<10)(h:inIB I x=false):I.testBit (F x).1=false:=by rw[f0v d];exact h
lemma nMap(x:V):(Vn x.1).map F=(List.finRange 10).filter (λ y=>(neigh x).testBit y.1):=by revert x;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma nLt{i n}(d:i<10)(h3:n<3)(hn:n<(Vn i).length):(Vn i).getD n 0<10/\adj (F i) (F ((Vn i).getD n 0))/\n<3:=by have q:∀u:V,∀k:Fin 3,k.1<(Vn u.1).length->(Vn u.1).getD k.1 0<10/\adj u (F ((Vn u.1).getD k.1 0)):=(by rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel);obtain⟨u,rfl⟩:=finE d;have k:=(q u) ⟨n,h3⟩ hn;exact⟨k.1,(f0e u).symm▸k.2,h3⟩
lemma eSq{x y}(d:x<10)(hy:y<10)(f:adj (F x) (F y)):(Vk x y).1<14/\(Vk x y).2<2/\J (Vk x y).1=(edgeOfPair (F x) (F y)).1/\((Vk x y).2==1)=(edgeOfPair (F x) (F y)).2:=by obtain⟨u,rfl⟩:=finE d;obtain⟨v,rfl⟩:=finE hy;revert f u v;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma aMi{a}(d:a<16):independent (mask (Vj a)):=by obtain⟨u,rfl⟩:=finE d;revert u;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma aMn{x a}(d:x<10)(f:a<16)(h:((Vj a)&&&neighN x)≠0):∃v∈mask (Vj a),adj (F x) v:=by obtain⟨u,rfl⟩:=finE d;obtain⟨v,rfl⟩:=finE f;revert h u v;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma nMem{x}(d:x<10):∀y∈Vn x,y<10:=by obtain⟨u,rfl⟩:=finE d;revert u;rcases sctx with ⟨vv⟩; fin_cases vv <;> decide +kernel
lemma nF{x}(d:x<10)(p:Nat->Bool)(q:V->Bool)(hp:∀y<10,p y=q (F y)):((Vn x).filter p).map F=(List.finRange 10).filter (λ y=>(neigh (F x)).testBit y.1&&q y):=by have f:=nMap (F x);simp only[Fin.val_ofNat,mo d] at f;rw[show (Vn x).filter p=(Vn x).filter (q ∘ F) from List.filter_congr λ y hy=>hp y (nMem d y hy),<-List.filter_map,f,List.filter_filter];exact List.filter_congr λ _ _=>Bool.and_comm _ _
lemma iNq I {x}(hx:x<10):(Vm I x).map F=ineligNbrs I (F x):=nF hx (inIB I) (λ y=>I.testBit y.1) λ y hy=>by simp[inIB,mo hy]
lemma eNq I {x}(hx:x<10):(Vl I x).map F=eligNbrs I (F x):=nF hx (λ y=>!inIB I y) (λ y=>!I.testBit y.1) λ y hy=>by simp[inIB,mo hy]
lemma p3c{k m}(hk:k<=3)(d:m<1<<<k):((Finset.univ:Finset (Fin k)).filter (λ t=>m.testBit t.1)).card=pop3 m:=by have q:∀a:Fin 4,∀b:Fin 8,b.1<1<<<a.1->((Finset.univ:Finset (Fin a.1)).filter (λ t=>b.1.testBit t.1)).card=pop3 b.1:=(by decide +kernel);exact q ⟨k,by omega⟩ ⟨m,by interval_cases k<;>omega⟩ d
namespace EP
lemma sL(a b:Nat):a+b-a=b:=Nat.add_sub_cancel_left a b
lemma d1{a b m:Nat}(h:b<m:=by omega):(a*m+b)/m=a:=by rw[Nat.mul_comm,Nat.mul_add_div (by omega),Nat.div_eq_of_lt h,Nat.add_zero]
lemma m1{a b m:Nat}(h:b<m:=by omega):(a*m+b) % m=b:=by rw[Nat.mul_comm,Nat.mul_add_mod,mo h]
abbrev C b (P Q:Nat->Prop) (i:Nat):=cond (i.blt b) (P i) (Q i)
lemma cT{a b}{P Q:Nat->Prop}(h:a<b:=by omega):C b P Q a=P a:=by simp[C,Nat.blt_eq,h]
lemma cF{a b}{P Q:Nat->Prop}(h:b<=a:=by omega):C b P Q a=Q a:=by simp[C,Nat.blt_eq,Nat.not_lt.2 h]
def s0 n (f:Nat->Prop) i:=f (i-n)
def s1 n u (f:Nat->Nat->Prop) i:=f ((i-n)/u) ((i-n) % u)
def s2 n u v (f:Nat->Nat->Nat->Prop) i:=f ((i-n)/v/u) ((i-n)/v % u) ((i-n) % v)
def s3 n u v w (f:Nat->Nat->Nat->Nat->Prop) i:=f ((i-n)/w/v/u) ((i-n)/w/v % u) ((i-n)/w % v) ((i-n) % w)
lemma b0 a {n f}:s0 n f (n+a)=f a:=by rw[s0,sL]
lemma b1 a b {n u f}(_:b<u:=by omega):s1 n u f (n+a*u+b)=f a b:=by rw[s1,Nat.add_assoc,sL,d1,m1]
lemma b2 a b c {n u v f}(_:b<u/\c<v:=by omega):s2 n u v f (n+(a*u+b)*v+c)=f a b c:=by rw[s2,Nat.add_assoc,sL,d1,m1,d1,m1]
lemma b3 a b c d {n u v w f}(_:b<u/\c<v/\d<w:=by omega):s3 n u v w f (n+((a*u+b)*v+c)*w+d)=f a b c d:=by rw[s3,Nat.add_assoc,sL,d1,m1,d1,m1,d1,m1]
lemma l{i b}{P Q:Nat->Prop}{R}(h:P i=R)(_:i<b:=by omega):C b P Q i=R:=(cT (a:=i) (b:=b)).trans h
lemma r{i b}{P Q:Nat->Prop}{R}(h:Q i=R)(_:b<=i:=by omega):C b P Q i=R:=(cF (a:=i) (b:=b)).trans h
abbrev U3{α} (t:LN) d (f:Ei->V->V->α):=let v:=untriple t d;f (J v.1) (F v.2.1) (F v.2.2)
abbrev Uc{α} (t c:LN) (f:Ei->V->V->Ei->V->α) d:=let u:=unctx c d;U3 t u.1 f (J u.2.1) (F u.2.2)
abbrev Um{α} (b:LN) a (f:Ei->Nat->α):=let u:=unmask b a;f (J u.1) u.2.1
abbrev eP0 D {k} w (o:Os k):=C 1080 (C 550 (C 50 (λ i=>V1 D (F (i/5)) (i % 5)) (s2 50 5 10 λ x j c=>lab D w (F x) j (F c))) (C 1050 (s2 550 5 10 λ x j c=>opp D w (F x) j (F c)) (s1 1050 10 λ t x=>Va D o t (F x)))) (C 1480 (C 1180 (s1 1080 10 λ x y=>Together D (F x) (F y)) (s2 1180 10 10 λ t x y=>Va D o t (F x)/\¬Va D o t (F y))) (C 1500 (s1 1480 10 λ t x=>∀v:V,x<=v.1->(Va D o t v <->Va D o (t+1) v)) (C 1510 (s0 1500 λ x=>has_merge D (F x)) (s2 1510 10 5 λ t x j=>rsub D w o t (F x) j))))
abbrev eP1 D w e:=C 3636 (C 3340 (C 1940 (s2 1660 14 10 λ s a x=>es D e (s==1) (J a) (F x)) (s3 1940 14 10 5 λ s a x j=>ra D w e (s==1) (J a) (F x) j)) (C 3390 (s1 3340 5 λ x j=>free_slot D w e (F x) j) (C 3440 (s1 3390 5 λ x j=>empty_opp D w (F x) j) (s1 3440 14 λ a b=>e (J a)=e (J b))))) (C 4224 (C 3832 (s1 3636 14 λ a b=>e (J a)=Vg (e (J b))) (C 4028 (s1 3832 14 λ a b=>sgate e (J a) (J b)) (s1 4028 14 λ a b=>V4 e (J a) (J b)))) (C 4924 (s2 4224 10 5 λ a x j=>after D w e (J a) (F x) j) (C 4938 (s0 4924 λ a=>has_sec D e (J a)) (s2 4938 5 5 λ a u v=>sec_pair D w e (J a) u v))))
abbrev eP2 D w e t:=C 7556 (C 6702 (C 5988 (s2 5288 10 5 λ a x j=>afree D w e (J a) (F x) j) (C 6688 (s2 5988 10 5 λ a x j=>aempty D w e (J a) (F x) j) (s0 6688 λ a=>stay_empty D (10+(e (J a)).1)))) (C 6716 (λ _=>False) (C 6856 (s1 6716 10 λ a z=>pick_z D (10+(e (J a)).1) (F z)) (s2 6856 10 5 λ a z l=>h0Prop D w e (J a) (F z) l)))) (C 7720 (λ _=>False) (C 7742 (λ _=>False) (C 7966 (s1 7742 14 λ d a=>U3 t d (bc D e) (J a)) (λ _=>False))))
abbrev eP3 D w e t c (b:LN):=C 10334 (C 9118 (C 8798 (s2 7998 16 5 λ x a j=>V1 D (F x) j/\∀y∈mask (Vj a),¬lab D w (F x) j y) (s1 8798 5 λ d l=>Uc t c (efhProp D w e) d l)) (C 10014 (s1 9118 14 λ d a=>Uc t c (eseProp D e) d (J a)) (s2 10014 10 5 λ a z l=>Um b a (mescProp D w e) (F z) l))) (C 13730 (C 11230 (λ _=>False) (s3 11230 5 10 5 λ x j y l=>V1 D (F x) j/\V1 D (F y) l/\w (F y) l=w (F x) j)) (C 16230 (s3 13730 5 10 5 λ x j y l=>V1 D (F x) j/\V1 D (F y) l/\w (F y) l=Vg (w (F x) j)) (s3 16230 10 3 5 λ a y n l=>let x:=(Vn a).getD n 0;aempty D w e (J (Vk a x).1) (F x) l/\free_slot D w e (F x) l/\¬lab D w (F x) l (F y)/\∀z:V,adj (F a) z->lab D w (F x) l z)))
def eP(D:Dag)(w:Ws)(e:Es)(t c b:LN){k}(o:Os k):Nat->Prop:=C 5288 (C 1660 (eP0 D w o) (eP1 D w e)) (C 7998 (eP2 D w e t) (eP3 D w e t c b))
lemma p0(D:Dag)(w:Ws)(e:Es)(t c b:LN){k}(o:Os k)(i:Nat){n P}(h:eP0 D w o n=P)(eq:i=n:=by rfl)(_:n<1660:=by omega):eP D w e t c b o i <->P:=by rw[eq,eP,cT,cT,h]
lemma p1(D:Dag)(w:Ws)(e:Es)(t c b:LN){k}(o:Os k)(i:Nat){n P}(h:eP1 D w e n=P)(eq:i=n:=by rfl)(_:1660<=n/\n<5288:=by omega):eP D w e t c b o i <->P:=by rw[eq,eP,cT,cF,h]
lemma p2(D:Dag)(w:Ws)(e:Es)(t c b:LN){k}(o:Os k)(i:Nat){n P}(h:eP2 D w e t n=P)(eq:i=n:=by rfl)(_:5288<=n/\n<7998:=by omega):eP D w e t c b o i <->P:=by rw[eq,eP,cF,cT,h]
lemma p3(D:Dag)(w:Ws)(e:Es)(t c b:LN){k}(o:Os k)(i:Nat){n P}(h:eP3 D w e t c b n=P)(eq:i=n:=by rfl)(_:7998<=n:=by omega):eP D w e t c b o i <->P:=by rw[eq,eP,cF,cF,h]
lemma symM{P:Nat->Nat->Prop}(s:∀a b,P a b->P b a){x y}:P (min x y) (max x y) <->P x y:=by by_cases h:x<=y;{simp[Nat.min_eq_left h,Nat.max_eq_right h]};{simp only[Nat.min_eq_right (by omega:y<=x),Nat.max_eq_left (by omega:y<=x)];exact⟨s _ _,s _ _⟩}
end EP
noncomputable def trP(D:Dag)(w:Ws)(e:Es)(t c b:LN){k}(o:Os k)(i:Nat):Bool:=bP (EP.eP D w e t c b o i)
section Ev
open EP
variable {D:Dag} {w:Ws} {e:Es} {t c b:LN} {k:Nat} {o:Os k}
lemma v0{x j}(_:x<10/\j<5:=by constructor<;>first|assumption|omega):eP D w e t c b o (fLive x j) <->V1 D (F x) j:=by rw[fLive,eP,cT,cT,eP0,cT,cT,cT,d1,m1]
abbrev v1{x j y} (_:x<10/\j<5/\y<10:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p0 D w e t c b o (fLab x j y) (l (l (r (b2 x j y))))
abbrev v2{x j y} (_:x<10/\j<5/\y<10:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p0 D w e t c b o (fOpp x j y) (l (r (l (b2 x j y))))
abbrev v3{a x} (_:a<3/\x<10:=by omega):=p0 D w e t c b o (fRes a x) (l (r (r (b1 a x))))
abbrev v4{x y} (_:x<10/\y<10:=by omega):=(p0 D w e t c b o (fCommon x y) (r (l (l (b1 (min x y) (max x y)))))).trans (symM (P:=λ a b=>Together D (F a) (F b)) λ _ _ ⟨z,p,q⟩=>⟨z,q,p⟩)
abbrev v5{a x y} (_:a<3/\x<10/\y<10:=by omega):=p0 D w e t c b o (fDiff a x y) (r (l (r (b2 a x y))))
abbrev v6{a x} (_:a<2/\x<10:=by omega):=p0 D w e t c b o (fEqGe a x) (r (r (l (b1 a x))))
abbrev v7{x} (_:x<10:=by first|assumption|omega):=p0 D w e t c b o (fHm x) (r (r (r (l (b0 x)))))
abbrev v8{a x j} (_:a<3/\x<10/\j<5:=by omega):=p0 D w e t c b o (fRsub a x j) (r (r (r (r (b2 a x j)))))
abbrev v9{s a x} (_:s<2/\a<14/\x<10:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p1 D w e t c b o (fEs s a x) (l (l (l (b2 s a x))))
abbrev u0{s a x j} (_:s<2/\a<14/\x<10/\j<5:=by refine⟨?_,?_,?_,?_⟩<;>first|assumption|omega):=p1 D w e t c b o (fRa s a x j) (l (l (r (b3 s a x j))))
abbrev u1{x j} (_:x<10/\j<5:=by constructor<;>first|assumption|omega):=p1 D w e t c b o (fFree x j) (l (r (l (b1 x j))))
abbrev u2{x j} (_:x<10/\j<5:=by constructor<;>first|assumption|omega):=p1 D w e t c b o (fEmpty x j) (l (r (r (l (b1 x j)))))
abbrev u3{a d} (_:a<14/\d<14:=by omega):=p1 D w e t c b o (fGate a d) (l (r (r (r (b1 a d)))))
abbrev u4{a d} (_:a<14/\d<14:=by omega):=p1 D w e t c b o (fGflip a d) (r (l (l (b1 a d))))
abbrev u5{a d} (_:a<14/\d<14:=by omega):=(p1 D w e t c b o (fSgate a d) (r (l (r (l (b1 (min a d) (max a d))))))).trans (symM (P:=λ a b=>sgate e (J a) (J b)) λ _ _=>Eq.symm)
abbrev u6{a d} (_:a<14/\d<14:=by constructor<;>first|assumption|omega):=p1 D w e t c b o (fLt a d) (r (l (r (r (b1 a d)))))
abbrev u7{a x j} (_:a<14/\x<10/\j<5:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p1 D w e t c b o (fAfter a x j) (r (r (l (b2 a x j))))
abbrev u8{a} (_:a<14:=by first|assumption|omega):=p1 D w e t c b o (fHsec a) (r (r (r (l (b0 a)))))
abbrev u9{a u v} (_:a<14/\u<5/\v<5:=by omega):=p1 D w e t c b o (fSecp a u v) (r (r (r (r (b2 a u v)))))
abbrev t0{a x j} (_:a<14/\x<10/\j<5:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p2 D w e t c b o (fAfree a x j) (l (l (l (b2 a x j))))
abbrev t1{a x j} (_:a<14/\x<10/\j<5:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p2 D w e t c b o (fAempty a x j) (l (l (r (l (b2 a x j)))))
abbrev t2{a} (_:a<14:=by first|assumption|omega):=p2 D w e t c b o (fStay a) (l (l (r (r (b0 a)))))
abbrev t4{a z} (_:a<14/\z<10:=by constructor<;>first|assumption|omega):=p2 D w e t c b o (fPick a z) (l (r (r (l (b1 a z)))))
abbrev t5{a z l0} (_:a<14/\z<10/\l0<5:=by omega):=p2 D w e t c b o (fH0 a z l0) (l (r (r (r (b2 a z l0)))))
abbrev y2{d a} (_:d<16/\a<14:=by constructor<;>first|assumption|omega):=p2 D w e t c b o (fBc d a) (r (r (r (l (b1 d a)))))
abbrev y4{x a j} (_:x<10/\a<16/\j<5:=by omega):=p3 D w e t c b o (fAvoid x a j) (l (l (l (b2 x a j))))
abbrev y5{d l0} (_:d<64/\l0<5:=by constructor<;>first|assumption|omega):=p3 D w e t c b o (fEfh d l0) (l (l (r (b1 d l0))))
abbrev y6{d a} (_:d<64/\a<14:=by constructor<;>first|assumption|omega):=p3 D w e t c b o (fEse d a) (l (r (l (b1 d a))))
abbrev y7{a z l0} (_:a<6/\z<10/\l0<5:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p3 D w e t c b o (fMesc a z l0) (l (r (r (b2 a z l0))))
abbrev y9{x j y l0} (_:x<10/\j<5/\y<10/\l0<5:=by omega):=p3 D w e t c b o (fSmate x j y l0) (r (l (r (b3 x j y l0))))
abbrev x0{x j y l0} (_:x<10/\j<5/\y<10/\l0<5:=by omega):=p3 D w e t c b o (fOmate x j y l0) (r (r (l (b3 x j y l0))))
abbrev x1{a y n l0} (_:a<10/\y<10/\n<3/\l0<5:=by omega):=p3 D w e t c b o (fIfilt a y n l0) (r (r (r (b3 a y n l0))))
abbrev Hp(P:Nat->Prop):=Holds (λ i=>bP (P i))
section Hc
variable {P:Nat->Prop}
lemma R{a}(h:P a):Hp P [(a,true)]:=⟨_,.head _,bt.2 h⟩
lemma j0{a}(h:¬P a):Hp P [(a,false)]:=⟨_,.head _,bf.2 h⟩
lemma G{a c}(h:P a->Hp P c):Hp P ((a,false)::c):=(Classical.em (P a)).elim (λ q=>let ⟨l,hl,hy⟩:=h q;⟨l,.tail _ hl,hy⟩) (λ q=>⟨_,.head _,bf.2 q⟩)
lemma jT{a c}(h:¬P a->Hp P c):Hp P ((a,true)::c):=(Classical.em (P a)).elim (λ q=>⟨_,.head _,bt.2 q⟩) (λ q=>let ⟨l,hl,hy⟩:=h q;⟨l,.tail _ hl,hy⟩)
abbrev B{a b} (h:P a->P b):=G λ q=>R (h q)
abbrev Z{a b} (h:P a->¬P b):=G λ q=>j0 (h q)
abbrev j3{a b c} (h:P a->P b->P c):=G λ p=>B (h p)
abbrev k3{a b c} (h:P a->P b->¬P c):=G λ p=>Z (h p)
abbrev jFT{a b c} (h:P a->¬P b->Hp P c):=G λ p=>jT (h p)
abbrev jFF{a b c} (h:P a->P b->Hp P c):=G λ p=>G (h p)
abbrev jTT{a b c} (h:¬P a->¬P b->Hp P c):=jT λ p=>jT (h p)
abbrev jFFT{a b c d} (h:P a->P b->¬P c->Hp P d):=G λ p=>jFT (h p)
lemma cb{a b}{p q:Prop}(ha:P a <->p)(hb:P b <->q)(f:p->q):Hp P [(a,false),(b,true)]:=B λ h=>hb.2 (f (ha.1 h))
lemma cz{a b}{p q:Prop}(ha:P a <->p)(hb:P b <->q)(f:p->¬q):Hp P [(a,false),(b,false)]:=Z λ h k=>f (ha.1 h) (hb.1 k)
lemma c3{a b c}{p q r:Prop}(ha:P a <->p)(hb:P b <->q)(hc:P c <->r)(f:p->q->r):Hp P [(a,false),(b,false),(c,true)]:=j3 λ h k=>hc.2 (f (ha.1 h) (hb.1 k))
lemma jI{a b c}{p:Bool}(h:P a->(P b <->P c)):Hp P [(a,false),(b,p),(c,!p)]:=G λ q=>match p with|false=>G λ r=>R ((h q).1 r)|true=>jT λ r=>j0 λ s=>r ((h q).2 s)
lemma jQ{a b c}{p:Bool}(h:(P a <->P b)->P c):Hp P [(a,p),(b,p),(c,true)]:=by cases p;{exact G λ a=>G λ b=>R (h ⟨λ _=>b,λ _=>a⟩)};{exact jT λ a=>jT λ b=>R (h ⟨λ x=>absurd x a,λ x=>absurd x b⟩)}
lemma jL{c1 c2}:Hp P c1->Hp P (c1++c2)|⟨l,hl,hy⟩=>⟨l,List.mem_append_left _ hl,hy⟩
lemma jR{c1 c2}:Hp P c2->Hp P (c1++c2)|⟨l,hl,hy⟩=>⟨l,List.mem_append_right _ hl,hy⟩
lemma jG{n} {f:Nat->Nat}:(∃j<n,P (f j))->Hp P ((Vq n).map λ j=>(f j,true))
 | ⟨j,hj,q⟩=>⟨_,Vo.2 ⟨j,lR.2 hj,rfl⟩,bt.2 q⟩
lemma jF2{n} {f g:Nat->Nat}:(∃j<n,P (f j)\/P (g j))->Hp P ((Vq n).flatMap λ j=>[(f j,true),(g j,true)])
 | ⟨j,hj,h⟩=>h.elim (λ p=>⟨(f j,true),List.mem_flatMap.2 ⟨j,lR.2 hj,by simp⟩,bt.2 p⟩) (λ p=>⟨(g j,true),List.mem_flatMap.2 ⟨j,lR.2 hj,by simp⟩,bt.2 p⟩)
end Hc
lemma jM{m x}(hk:k<=3)(hx:x<10)(h:∃i:Fin k,m.testBit i.1=true/\Va D o i.1 (F x)):Holds (trP D w e t c b o) (maskRes k m x):=by obtain⟨⟨i,d⟩,f,j⟩:=h;have q:=W (v3 (D:=D) (w:=w) (e:=e) (t:=t) (c:=c) (b:=b) (o:=o)) j;unfold maskRes;rcases (by omega:i=0\/i=1\/i=2) with rfl|rfl|rfl;{exact jL (jL (by simp[d,f];exact R q))};{exact jL (jR (by simp[d,f];exact R q))};{exact jR (by simp[d,f];exact R q)}
lemma jU{I eo x y}{f:Nat->Nat->Nat}(d:eo<14)(h:∃z:V,(z=ep0 (J eo)\/z=ep1 (J eo))/\z≠F x/\z≠F y/\∃l<cap k I z,eP D w e t c b o (f z.1 l)):Holds (trP D w e t c b o) (uvSlots k I (ep0N eo) (ep1N eo) x y λ z l=>(f z l,true)):=by obtain⟨z,n,m,j,l,hl,i⟩:=h;have p u (hu:u<10) (he:F u=z):Holds (trP D w e t c b o) (if u != x&&u != y then (Vq (capN k I u)).map λ l=>(f u l,true) else []):=by{have ha:u≠x:=λ q=>m (by rw[<-he,q]);have v:u≠y:=λ q=>j (by rw[<-he,q]);simp[ha,v];exact jG ⟨l,by rw[cNq k I hu,he];exact hl,by rw[<-he,f0v hu] at i;exact i⟩};rcases n with rfl|rfl;{exact jL (p _ (e0l d) (e0q d))};{exact jR (p _ (e1l d) (e1q d))}
end Ev
def MOk(D:Dag):Nat->Prop
 | 0=>True
 | 1=>Bzero 10 D=0
 | _=>False
def SOk(_D:Dag) (_e:Es) {k} (_o:Os k):Nat->Prop
 | 0=>True
 | _=>False
lemma mIn{D I x}(q:mask I=Ve 10 D)(d:x<10)(h:inIB I x=true):F x∈Ve 10 D:=by rw[<-q];exact mF.2 ⟨mU _,iB d h⟩
lemma sfB(s:Bool)(p:Slot):Vb s (Vg p)=Vb (!s) p:=by rcases p with ⟨g,b⟩;cases s<;>cases b<;>rfl
lemma sf1(s:Bool)(p:Slot):(Vb s p).1=p.1:=by cases s<;>rfl
def pinL(I x:Nat):LN:=Vm I x++(Vl I x).take 1
lemma pinLq I {x}(hx:x<10)(e:Es):V6 I e (F x)=(pinL I x).map λ y=>V7 e (F x) (F y):=by dsimp only[V6,pinL];rw[List.map_append,<-iNq I hx,List.map_map];congr 1;have q:=eNq I hx;cases h:Vl I x<;>rw[h] at q<;>rw[<-q]<;>rfl
lemma pLn{I x}(d:x<10)(e:Es):(V6 I e (F x)).length=(Vm I x).length+(if (Vl I x).isEmpty then 0 else 1):=by rw[pinLq I d,Vp,pinL,List.length_append];cases Vl I x<;>rfl
abbrev pR(D:Dag) (w:Ws) (e:Es) (x r y:Nat):=y<10/\adj (F x) (F y)/\V1 D (F x) r/\w (F x) r=V7 e (F x) (F y)
section Pin
variable {D:Dag} {k I x r:Nat} {w:Ws} {e:Es} {br:V->Nat} {o:Os k} (L:V0 D k I w e br o)
include L
lemma pAt(f:x<10)(h:inIB I x=false)(i:r<(pinL I x).length):pR D w e x r (pinL I x)[r]:=by have hp:r<(V6 I e (F x)).length:=by{rw[pinLq I f,Vp];exact i};have hn:=L.2.2.2.2.2.2.2.2.2.2 (F x) (by rw[nB f h];decide) r hp;have j:(pinL I x)[r]∈Vn x:=(List.mem_append.1 (List.getElem_mem i)).elim (λ d=>(lF.1 d).1) (λ d=>(lF.1 (List.mem_of_mem_take d)).1);have m:F (pinL I x)[r]∈(Vn x).map F:=Vo.2 ⟨_,j,rfl⟩;have h3:=nMap (F x);simp only[Fin.val_ofNat,mo f] at h3;rw[h3,lF] at m;refine⟨nMem f _ j,m.2,hn.1,hn.2.trans ?_⟩;simp only[pinLq I f,List.getElem_map]
lemma pIn(h:x<10)(d:inIB I x=false)(f:r<(Vm I x).length):pR D w e x r ((Vm I x).getD r 0):=by have hl:r<(pinL I x).length:=by{unfold pinL;simp;omega};have i:(Vm I x).getD r 0=(pinL I x)[r]:=by{rw[List.getD_eq_getElem _ _ f];simp[pinL,List.getElem_append_left f]};simpa only[i] using pAt L h d hl
lemma pEn(i:x<10)(f:inIB I x=false)(h:(Vl I x).isEmpty=false):pR D w e x (Vm I x).length ((Vl I x).getD 0 0):=by cases d:Vl I x with|nil=>{simp[d] at h}|cons y m=>{have hl:(Vm I x).length<(pinL I x).length:=by{unfold pinL;rw[d];simp};have j:(pinL I x)[(Vm I x).length]=y:=(by simp[pinL,d]);simpa only[j,List.getD_cons_zero] using pAt L i f hl}
end Pin
abbrev QT t d:=let v:=untriple t d;v.1<14/\v.2.1<10/\v.2.2<10/\¬adj (F v.2.1) (F v.2.2)
lemma qT{t d}(h:validTriple t d=true):QT t d:=by simp only[validTriple,sA,sD,sB,sC] at h;obtain⟨_,a,b,c,d⟩:=h;exact⟨a,b,c,λ q=>by rw[(aBi b c).2 q] at d;cases d⟩
lemma qC{t c d}(h:validCtx t c d=true):let u:=unctx c d;u.1<16/\u.2.1<14/\u.2.2<10/\QT t u.1:=by simp only[validCtx,sA,sD,sC] at h;exact⟨a4 _,h.2.2.1,h.2.2.2,qT h.2.1⟩
lemma qM{b a}(h:validMask b a=true):a<6/\(unmask b a).1<14/\(unmask b a).2.1.testBit (unmask b a).1=true:=by simp only[validMask,sA,sD,sC] at h;exact⟨h.2.1,h.2.2.1,h.2.2.2⟩
section Sound
variable {D:Dag} {k I P N:Nat} {w:Ws} {e:Es} {br:V->Nat} {o:Os k} {U X Y:LN} (H:Vd 10 D) (A:sem_Comp 10 adj D) (K:k<=3) (Q:mask I=Ve 10 D) (L:V0 D k I w e br o) (M:MOk D P) (S:SOk D e o N)
abbrev H0 D w e U X Y {k} (o:Os k):=Holds (trP D w e U X Y o)
lemma cN{x}(d:x<10){j}(f:j<cap k I (F x)):j<capN k I x:=by rw[cNq k I d];exact f
abbrev Lc(L:V0 D k I w e br o):=L.2.2.2.2.2.1
abbrev Li(L:V0 D k I w e br o):=L.2.2.2.2.2.2.2.1
abbrev Lw(L:V0 D k I w e br o):=L.2.2.2.2.2.2.2.2.1
abbrev Le(L:V0 D k I w e br o):=L.2.2.2.2.2.2.2.2.2.1
abbrev Lp(L:V0 D k I w e br o):=L.2.2.2.2.2.2.2.2.2.2
lemma zOpp2{z l a}(h:opp D w (F z) l (ep0 (J a))\/opp D w (F z) l (ep1 (J a)))(hz:z<10:=by first|assumption|omega)(hl:l<5:=by first|assumption|omega)(ha:a<14:=by first|assumption|omega):H0 D w e U X Y o [(fOpp z l (ep0N a),true),(fOpp z l (ep1N a),true)]:=jT λ n=>h.elim (λ j=>absurd ((v2 ⟨hz,hl,e0l ha⟩).2 (by rw[e0q ha];exact j)) n) (λ i=>R ((v2 ⟨hz,hl,e1l ha⟩).2 (by rw[e1q ha];exact i)))
lemma zF2{a x j b u v}{P0 R:Prop}(ha:EP.eP D w e U X Y o a <->P0/\¬opp D w (F x) j (F u)/\¬opp D w (F x) j (F v)/\R)(hx:x<10:=by first|assumption|omega)(hj:j<5:=by first|assumption|omega)(hu:u<10:=by first|assumption|omega)(hv:v<10:=by first|assumption|omega):H0 D w e U X Y o [(a,false),(fOpp x j (if b=1 then v else u),false)]:=Z λ hf ho=>(Classical.em (b=1)).elim (λ d=>(ha.1 hf).2.2.1 (T v2 (by simpa only[d,sT] using ho))) (λ d=>(ha.1 hf).2.1 (T v2 (by simpa only[d,sF] using ho)))
variable {g r:Nat}
include H A K Q L M S
omit M S in lemma z0 (_:g<16)(q:enabled0 k I g r=true):H0 D w e U X Y o (expand0 k I g r):=by interval_cases g<;>(simp only[expand0,enabled0,Vr,sT,sF,sA,sD,sQ,sN,sB,sC] at q ⊢;have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_));{exact R (W v0 (live0_of H.1 A (F _)))};{have:=c5 q.2;exact cb v0 v1 (selfLab_of L)};{have:=c5 q.2;exact cb v0 v0 Nat.lt_of_succ_lt};{have:=c5 q.2.1;exact j3 λ _ d=>W v4 (labCommon_of L (T v1 d))};{apply G;intro i;have d:=(p3c K q.2.2.2.1).trans q.2.2.2.2;have ⟨t,h,f⟩:=sizeCode_of H A L (F _) _ _ d (T v0 i);exact jM K q.1 ⟨t,(mF.1 h).2,f⟩};{exact j0 λ d=>ineligNoRes_of L Q (iB q.1 q.2.1) (T v3 d)};{have ⟨n,h,i⟩:=q;rw[Bool.or_eq_true] at i;exact j0 λ d=>by{have f:=T v4 d;rcases i with m|j;{exact commonInelig H.1 A (mIn Q (by omega) m) (f0n (by omega) h (by omega)) f};{exact commonInelig H.1 A (mIn Q h j) (@f0n sctx ((r>>>4)&&&15) (r&&&15) h (by omega) (by omega)) (by have ⟨z,a,b⟩:=f;exact⟨z,b,a⟩)}}};{exact c3 v3 v3 v4 resCommon_of};{exact cb v5 v3 And.left};{exact cz v5 v3 And.right};{exact R (W v4 (adjCommon_of H A (mIn Q q.1 q.2.1) ((aBi q.1 q.2.2.1).1 q.2.2.2.2.2.1) ((aBi q.1 q.2.2.2.1).1 q.2.2.2.2.2.2)))};{have:=c5 q.2.2.2.2.2;apply jFFT;intro d m j;apply jT;intro i;rcases riSlots_of H A L Q (f0n q.1 q.2.2.1 q.2.2.2.1.symm) (nB q.1 q.2.1) q.2.2.2.2.1 (T v0 m) (T v4 d) with p|n|⟨t,h,f⟩;{exact absurd (W v1 p) j};{exact absurd (W v1 n) i};{exact jG ⟨t.1,t.2,W v5 ⟨h,f⟩⟩}};{have ⟨j,i,h,d⟩:=expose_of H A L (F _) (Vj ((r>>>4)&&&15)) (aMi q.2.1) (aMn q.1 q.2.1 q.2.2.2);have f:=cN q.1 i;exact jG ⟨j,f,(y4 ⟨q.1,q.2.1,(c5 f)⟩).2 ⟨h,d⟩⟩};{have:=c5 q.2.1;exact cb y4 v0 And.left};{have:=c5 q.2.1;exact Z λ f d=>(T y4 f).2 (F _) (mF.2 ⟨mU _,by rw[f0v q.2.2.2.1];exact q.2.2.2.2⟩) (T v1 d)};{exact cb v3 v3 (lex_step_bit L q (F 9) (λ y d=>by have:=y.2;simp at d;omega))}
omit M S in lemma z1 (_:16<=g)(_:g<32)(q:enabled0 k I g r=true):H0 D w e U X Y o (expand0 k I g r):=by interval_cases g<;>(simp only[expand0,enabled0,Vr,sT,sF,sA,sD,sQ,sN,sB,sC] at q ⊢;have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_));{exact jQ λ d=>W v6 λ v h=>by{have f:v=F 9:=Fin.ext (by have:=v.2;simp;omega);rw[f];exact (v3).symm.trans (d.trans (v3 ⟨(by omega),(by omega)⟩))}};{exact j3 λ d h=>W v3 (lex_step_bit L q.1 (F _) (λ y f=>T v6 d y (by rw[f0v (by omega)] at f;omega)) (T v3 h))};{apply G;intro i;exact jQ λ d=>W v6 λ v j=>by{by_cases h:v.1=((r>>>3)&&&15);{have f:v=F ((r>>>3)&&&15):=Fin.ext (by rw[f0v (by omega)];exact h);rw[f];exact (v3).symm.trans (d.trans (v3 ⟨(by omega),(by omega)⟩))};{exact T v6 i v (by omega)}}};{exact j0 λ d=>hmInelig H A (mIn Q q.1 q.2) (T v7 d)};{exact cz v7 v0 (hmTop_of H A L (F _))};{apply jFF;intro i j;have d:=(p3c K q.2.2.2.1).trans q.2.2.2.2;have ⟨t,h,f⟩:=hmCode_of H A L (F _) _ _ d (T v7 i) (T v0 j);exact jM K q.1 ⟨t,(mF.1 h).2,f⟩};{have:=c5 q.2.2.2;exact cb v8 v0 And.left};{have:=c5 q.2.2.2.1;exact j3 λ f d=>W v1 ((T v8 f).2 (F _) (T v3 d))};{apply jFT;intro d m;have ⟨j,p,f,i⟩:=rsubTwo_of H A L (T v3 d) (λ n=>m (W v7 n)) (unsl ((r>>>3)&&&63)).2;have h:=cN q.2.1 p;exact⟨(fRsub (r&&&7) (unsl ((r>>>3)&&&63)).1 j,true),Vo.2 ⟨j,lF.2 ⟨lR.2 h,by simp[f]⟩,rfl⟩,bt.2 ((v8 ⟨(by omega),q.2.1,(c5 h)⟩).2 i)⟩};{have:=c5 q.2;exact j0 λ d=>oppSelf_of H.1 L (F _) _ (T v2 d)};{have:=c5 q.2.1;exact G λ _=>j3 λ f d=>W v7 (labOppMerge_of H.1 L (T v1 f) (T v2 d))};{have u:=c5 q.2.1;apply jFFT;intro j f h;have ⟨l,p,i,m⟩:=smateAny_of H.1 L (T v1 f) (λ n=>h (W v2 n));have d:=cN q.2.2.1 p;exact jG ⟨l,d,(y9 ⟨q.1,u,q.2.2.1,(c5 d)⟩).2 ⟨T v0 j,i,m⟩⟩};{have:=c5 q.2.1;have:=c5 q.2.2.2.2.2;exact B λ d=>W v0 (T y9 d).2.1};{have:=c5 q.2.1;have:=c5 q.2.2.2.2.2.1;exact jI λ j=>by{have ⟨f,h,d⟩:=T y9 j;by_cases i:((r>>>16)&&&1)=1;{simp only[i,sT];refine (v2).trans (Iff.trans ?_ (v2).symm);simp only[opp,f,h,d,true_and]};{simp only[i,sF];refine (v1).trans (Iff.trans ?_ (v1).symm);simp only[lab,f,h,d,true_and]}}};{have u:=c5 q.2.1;apply jFFT;intro j d h;have ⟨l,p,i,n⟩:=omateAny_of H.1 L (T v2 d) (λ m=>h (W v1 m));have f:=cN q.2.2.1 p;exact jG ⟨l,f,(x0 ⟨q.1,u,q.2.2.1,(c5 f)⟩).2 ⟨T v0 j,i,n⟩⟩};{have:=c5 q.2.1;have:=c5 q.2.2.2.2.2;exact B λ d=>W v0 (T x0 d).2.1}
omit S in lemma z2 (_:32<=g)(_:g<48)(q:enabled1 k I P g r=true):H0 D w e U X Y o (expand1 k I g r):=by have hE:=Le L;interval_cases g<;>(simp only[expand1,enabled1,Vr,sT,sF,sA,sD,sQ,sN,sB,sC] at q ⊢;have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_));{have:=c5 q.2.1;have:=c5 q.2.2.2.2.2.1;exact jI λ j=>by{have ⟨f,h,d⟩:=T x0 j;by_cases i:((r>>>16)&&&1)=1;{simp only[i,sT];refine (v2).trans (Iff.trans ?_ (v1).symm);simp only[lab,opp,f,h,d,Vh,true_and]};{simp only[i,sF];refine (v1).trans (Iff.trans ?_ (v2).symm);simp only[lab,opp,f,h,d,true_and]}}};{have:=c5 q.2.1;exact k3 λ _ d f=>ineligOppNF_of H A L Q (f0n q.1 q.2.2.1 q.2.2.2.1.symm) (iB q.2.2.1 q.2.2.2.2) (T v2 d) (T u1 f)};{have ⟨v,u,f,_,p,n,m⟩:=q;have:=c5 u;exact k3 λ _ h j=>by{have i:=sem_inelig_pure graph_ok H.1 A (mIn Q f p) (T v2 h).2;have d:=(T v2 j).2;rw[i,Finset.mem_singleton] at d;exact f0n n f m d}};{have:=c5 q.2.1;apply G;intro h;exact jI λ f=>by{have j:=V3 H A L Q (f0n q.1 q.2.2.1 q.2.2.2.1.symm) (iB q.2.2.1 q.2.2.2.2.1) (T v2 f);have d:=congrArg Vg j.symm;rw[Vh] at d;have i:=live0_of H.1 A (F ((r>>>6)&&&15));refine (v1).trans (Iff.trans ?_ (v2).symm);simp only[lab,opp,T v0 h,i,d,true_and]}};{have ⟨h1,h2,h,z,h5,h6⟩:=q;have:=c5 h6;have f:(r&&&15)≠((r>>>4)&&&15):=λ p=>by{rw[p,z] at h2;exact Bool.noConfusion h2};apply jFF;intro n m;exact Z λ j i=>by{have v:=V3 H A L Q (f0n h1 h f) (iB h z) (T v2 j);have u:=V3 H A L Q (f0n h1 h f) (iB h z) (T v2 i);have d:=congrArg Vg (v.trans u.symm);rw[Vh,Vh] at d;have a0:=Li L (F (r&&&15)) _ _ (T v0 n) (T v0 m) d;omega}};{exact R (W v2 ⟨live0_of H.1 A (F _),(inelig_unique_slot H A L Q (iB q.1 q.2.1)).2 (F _) ((aBi q.1 q.2.2.1).1 q.2.2.2)⟩)};{have ⟨h1,n,h3,h4,_,h6,h3lt,h7⟩:=q;have a3:Bzero 10 D=0:=by{rw[h1] at M;exact M};have ⟨f,d,i⟩:=nLt n h3lt h7;have v:¬adj (F (r&&&15)) (F ((r>>>4)&&&15)):=λ ha=>by{rw[(aBi n h4).2 ha] at h6;exact Bool.noConfusion h6};apply G;intro h;have ⟨l,hl,a2,z,u,m⟩:=ineligFilter_of H A a3 L Q (iB n h3) v d (T v2 h);have j:=cN f hl;have a0:=(eSq n f d).2.2.1;exact jG ⟨l,j,(x1 ⟨n,h4,i,(c5 j)⟩).2 ⟨by rw[a0];exact a2,z,u,λ x2 p=>(m x2 p).1⟩⟩};{exact j0 λ d=>ineligOppInelig_of H A L Q (iB q.1 q.2.1) (iB q.2.2.1 q.2.2.2.1) (f0n q.1 q.2.2.1 q.2.2.2.2) (T v2 d)};{have f:((r>>>4)&&&1)<2:=a1 _;exact j0 λ d=>by{have h:=(v9 ⟨f,q,(enl q)⟩).1 d;rw[enq (by omega) q,bnot1 f] at h;exact (hE _ (J _)).2 h}};{exact j3 λ f d=>W v7 (by{have ⟨j,i,h⟩:=Lw L (ep0 (J (r&&&15))) (e (J (r&&&15))) (by simpa[endpoint,Vb] using (hE false (J (r&&&15))).1);exact labOppMerge_of H.1 L ⟨i,by rw[h];simpa[es,Vb] using T v9 f⟩ ⟨i,by rw[h];simpa[es,Vb,Vg] using T v9 d⟩})};{have d:((r>>>4)&&&1)<2:=a1 _;exact R ((v9 ⟨d,q,(enl q)⟩).2 (by rw[enq d q];exact (Vi.1 (hE _ (J _)).1).2.1))};{let b0:=(r&&&1)==1;let z:=J ((r>>>1)&&&15);let x0:=F ((r>>>5)&&&15);let p0:=Vb b0 (e z);have hs:(r&&&1)<2:=a1 _;apply jFT;intro v u;have f:=(hE b0 z).1;have i:=(Vi.1 f).1;have h:x0∉supp 10 D (10+p0.1):=λ n=>u (W v9 (by rw[bnot1 hs];have d:=sem_supp_and_sub H.1 i (sem_W_and H.1 f) (!p0.2) n;rw[show (p0.1,!p0.2)=Vb (!b0) (e z) by rw[Vc];rfl] at d;exact d));have ⟨j,hj,p⟩:=Lw L x0 _ (Vi.2 ⟨i,T v9 v,h⟩);have m:=cN q.2 (lt_of_lt_of_le hj (Lc L _));exact jG ⟨j,m,(u0 ⟨hs,q.1,q.2,(c5 m)⟩).2 ⟨hj,p⟩⟩};{have:(r&&&1)<2:=a1 _;have:=c5 q.2.2.2;exact Z λ f d=>by{have ⟨i,m⟩:=T u0 f;have ⟨h,j⟩:=T u0 d;have:=Li L (F _) _ _ i h (m.trans j.symm);omega}};{have:(r&&&1)<2:=a1 _;have:=c5 q.2.2;exact cb u0 v0 And.left};{have:(r&&&1)<2:=a1 _;have:=c5 q.2.2;exact B λ d=>W v9 (by rw[es,<-(T u0 d).2];exact (Vi.1 (L.2.2.2.2.2.2.1 _ _)).2.1)};{have j:(r&&&1)<2:=a1 _;have:=c5 q.2.2;exact Z λ m f=>by{have ⟨d,h⟩:=T u0 m;have i:=T v9 f;rw[bnot1 j,es,Vc,<-h] at i;exact oppSelf_of H.1 L (F _) _ ⟨d,i⟩}}
omit H A Q M S in lemma z3 (_:48<=g)(_:g<64)(q:enabled1 k I P g r=true):H0 D w e U X Y o (expand1 k I g r):=by have hE:=Le L;interval_cases g<;>(simp only[expand1,enabled1,Vr,sT,sF,sA,sD,sQ,sN,sB,sC] at q ⊢;have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_));{have i:(r&&&1)<2:=a1 _;have:=c5 q.2.2.1;exact jI λ j=>by{have ⟨d,f⟩:=T u0 j;by_cases h:((r>>>15)&&&1)=1;{simp only[h,sT];refine (v2).trans (Iff.trans ?_ (v9).symm);simp only[opp,es,d,f,<-Vc,<-bnot1 i,true_and]};{simp only[h,sF];refine (v1).trans (Iff.trans ?_ (v9).symm);simp only[lab,es,d,f,true_and]}}};{have:=c5 q.2.2.2;have d:(unsl (r&&&63)).2<(V6 I e (F (unsl (r&&&63)).1)).length:=by{rw[pLn q.1];exact q.2.2.1};exact R (W v0 (Lp L (F _) (by rw[nB q.1 q.2.1];decide) _ d).1)};{have:=c5 q.2.2.2.1;have ⟨h,d,i,j⟩:=pIn L q.1 q.2.1 q.2.2.1;have f:(Vm I (unsl (r&&&63)).1).getD (unsl (r&&&63)).2 0=((r>>>6)&&&15):=(List.getD_eq_getElem _ 0 q.2.2.1).trans ((List.getD_eq_getElem _ 10 q.2.2.1).symm.trans q.2.2.2.2);rw[f] at h d j;exact R (W v2 ⟨i,by rw[j];exact (Vi.1 (pinTarget_mem_W hE d).2).2.1⟩)};{have:=c5 q.2.2.2;have ⟨d,f,h,m⟩:=pIn L q.1 q.2.1 q.2.2.1;have ⟨p,n,j,i⟩:=eSq q.1 d f;exact R (W u0 ⟨h,by rw[m,V7,j,i]⟩)};{have:=c5 q.2.2.2;have ⟨d,f,h,m⟩:=pEn L q.1 q.2.1 q.2.2.1;have ⟨p,n,j,i⟩:=eSq q.1 d f;exact R (W u0 ⟨h,by rw[m,V7,j,i]⟩)};{have:((r>>>12)&&&1)<2:=a1 _;have:=c5 q.2.1;have:=c5 q.2.2.2.2.2.1;exact j3 λ j i=>by{have ⟨f,_,h⟩:=T y9 j;have ⟨_,d⟩:=T u0 i;exact W u0 ⟨f,h.symm.trans d⟩}};{have j:((r>>>12)&&&1)<2:=a1 _;have:=c5 q.2.1;have:=c5 q.2.2.2.2.2.1;exact j3 λ n m=>by{have ⟨h,_,i⟩:=T x0 n;have ⟨_,f⟩:=T u0 m;have d:=congrArg Vg (i.symm.trans f);rw[Vh] at d;exact W u0 ⟨h,by rw[bnot1 j,Vc];exact d⟩}};{have:=c5 q.2;exact cb u1 v0 And.left};{have:((r>>>6)&&&1)<2:=a1 _;have:=c5 q.2.1;exact Z λ f d=>(T u1 f).2 (J _) _ (T u0 d).2};{have:=c5 q.2;exact cb u2 v0 And.left};{have:=c5 q.2.1;exact Z λ h f=>by have d:=(T v2 f).2;rw[(T u2 h).2] at d;exact Finset.notMem_empty _ d};{exact cb u3 u5 (congrArg Prod.fst)};{exact B λ d=>W u5 (by unfold sgate;rw[T u4 d];rfl)};{apply jFT;intro d f;rcases sem_same_gate (T u5 d).symm with i|h;{exact absurd (W u3 i) f};{exact R (W u4 h)}};{have:((r>>>14)&&&1)<2:=a1 _;have:((r>>>15)&&&1)<2:=a1 _;have:=c5 q.2.2.2;exact j3 λ j i=>by{have d:=(T u0 j).2.symm.trans (T u0 i).2;have h:((r>>>14)&&&1)=0\/((r>>>14)&&&1)=1:=(by omega);have f:((r>>>15)&&&1)=0\/((r>>>15)&&&1)=1:=(by omega);rcases h with h|h<;>rcases f with f|f<;>simp only[h,f] at d ⊢;{exact W u3 (sflip_inj false d)};{exact W u4 (by simpa[Vb,Vg] using d)};{exact W u4 (by change Vb true _=Vb false _ at d;rw[sflip_true,sflip_false] at d;have h'':=congrArg Vg d;rwa [Vh] at h'')};{exact W u3 (sflip_inj true d)}}};{have:((r>>>8)&&&1)<2:=a1 _;exact jI λ d=>(v9).trans (by unfold es;rw[T u3 d];exact (v9).symm)}
omit H A Q L M S in lemma z4 (_:64<=g)(_:g<80)(q:enabled2 k I P g r=true):H0 D w e U X Y o (expand2 k I P g r):=by interval_cases g<;>(simp only[expand2,enabled2,Vr,sT,sF,sA,sD,sQ,sN,sC] at q ⊢;have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_));{have d:((r>>>8)&&&1)<2:=a1 _;exact jI λ f=>(v9).trans (by{unfold es;rw[T u4 f,sfB,<-bnot1 d];exact (v9).symm})};{exact Z λ d f=>by have a:=T u5 d;have b:=T u6 f;unfold sgate at a;unfold V4 at b;omega};{apply jTT;intro d f;have a:(e (J _)).1≠(e (J _)).1:=λ i=>d (W u5 i);have b:¬(e (J _)).1<(e (J _)).1:=λ h=>f (W u6 h);exact R (W u6 (by unfold V4;omega))};{exact Z λ f d=>by have a:=T u6 f;have b:=T u6 d;unfold V4 at a b;omega};{exact c3 u6 u6 u6 Nat.lt_trans};{have:=c5 q.2.2;exact cb u7 v0 And.left};{have:((r>>>10)&&&1)<2:=a1 _;have:=c5 q.2.2;exact Z λ i f=>by have h:=(T u7 i).2;have d:=congrArg Prod.fst (T u0 f).2;rw[sf1] at d;omega};{have:((r>>>10)&&&1)<2:=a1 _;have:=c5 q.2.2.1;exact j3 λ i f=>W u6 (by have h:=(T u7 i).2;have d:=congrArg Prod.fst (T u0 f).2;rw[sf1] at d;unfold V4;omega)};{have:=c5 q.2.2;exact cb t0 u7 And.left};{have:=c5 q.2.2;exact cb t0 u1 And.right};{have:=c5 q.2.2;exact cb t1 u7 And.left};{have:=c5 q.2.2;exact cb t1 u2 And.right};{have d:=c5 q.2.1;have:=c5 q.2.2;exact B λ f=>(v0 ⟨(e0l q.1),d⟩).2 (by rw[e0q q.1];exact (T u9 f).1)};{have:=c5 q.2.1;have d:=c5 q.2.2;exact B λ f=>(v0 ⟨(e1l q.1),d⟩).2 (by rw[e1q q.1];exact (T u9 f).2.1)};{have d:=c5 q.2.1;have:=c5 q.2.2;exact Z λ f h=>secNotRa0_of (T u9 f) (by rw[<-e0q q.1];exact (u0 ⟨(by omega),q.1,(e0l q.1),d⟩).1 h)};{have:=c5 q.2.1;have d:=c5 q.2.2;exact Z λ f h=>secNotRa1_of (T u9 f) (by rw[<-e1q q.1];exact (u0 ⟨(by omega),q.1,(e1l q.1),d⟩).1 h)}
omit Q S in lemma z5 (_:80<=g)(_:g<96)(q:enabled2 k I P g r=true):H0 D w e U X Y o (expand2 k I P g r):=by have hE:=Le L;interval_cases g<;>(simp only[expand2,enabled2,Vr,sT,sF,sA,sD,sQ,sN,sC] at q ⊢;have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_));{have ⟨d,u,p,h⟩:=q;have j:=c5 u;have i:=c5 p;exact jI λ n=>by{have f:=secEq_of (T u9 n) (F ((r>>>9)&&&15));by_cases m:((r>>>13)&&&1)=1;{simp only[m,sT];exact (v1 ⟨(e1l d),i,h⟩).trans (by rw[e1q d,f.1,<-e0q d];exact (v2 ⟨(e0l d),j,h⟩).symm)};{simp only[m,sF];exact (v1 ⟨(e0l d),j,h⟩).trans (by rw[e0q d,f.2,<-e1q d];exact (v2 ⟨(e1l d),i,h⟩).symm)}}};{apply G;intro h;have ⟨j,p,i,n,m⟩:=hasSecAny_of H.1 L (T u8 h);have f:j<capN k I (ep0N (r&&&15)):=by{rw[cNq k I (e0l q),e0q q];exact p};have d:i<capN k I (ep1N (r&&&15)):=by{rw[cNq k I (e1l q),e1q q];exact n};exact⟨(fSecp (r&&&15) j i,true),List.mem_flatMap.2 ⟨j,lR.2 f,Vo.2 ⟨i,lR.2 d,rfl⟩⟩,bt.2 ((u9 ⟨q,(c5 f),(c5 d)⟩).2 m)⟩};{apply jT;intro f;rcases P with _|_|_|_;{omega};{rcases stepAny0_of H A M hE (J _) with d|⟨z,h⟩;{exact absurd (W t2 d) f};{exact jG ⟨z.1,z.2,W t4 (by rw[f0e];exact h)⟩}};{exact M.elim};{exact M.elim}};{contradiction};{exact c3 u5 t2 t2 sameStay_of};{exact c3 u5 t4 t4 samePick_of};{have:=c5 q.2.2.2;exact cb t5 u7 And.left};{have:=c5 q.2.2.2;exact G λ d=>zOpp2 (T t5 d).2};{apply jFT;intro j f;have ⟨l,m,h⟩:=pickZH0_of H A L (T t4 j) (λ i=>f (W u8 i));have d:=cN q.2.2 m;exact jG ⟨l,d,(t5 ⟨q.2.1,q.2.2,(c5 d)⟩).2 h⟩};{contradiction};{contradiction};{have:=c5 q.2.1;exact cb v2 v0 And.left};{contradiction};{contradiction};{contradiction};{contradiction}
omit Q M S in lemma z6 (_:96<=g)(_:g<101)(q:enabled3 k I P N U X Y g r=true):H0 D w e U X Y o (expand3 k I U X Y g r):=by have hE:=Le L;have:=a4 r;interval_cases g<;>(simp only[expand3,enabled3,Vr,sT,sF,sA,sD,sQ,sN,sC] at q ⊢;have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_));{contradiction};{have ⟨j,n,m,i⟩:=qT q.2;exact j3 λ h f=>W y2 (bcInit_of H A hE i (by{by_cases d:((r>>>4)&&&1)=1;{simp only[d,sT] at h f;exact Or.inr ⟨T (v9 (s:=0)) h,T (v9 (s:=1)) f⟩};{simp only[d,sF] at h f;exact Or.inl ⟨T (v9 (s:=0)) h,T (v9 (s:=1)) f⟩}}))};{have ⟨n,_,_,m⟩:=qT q.2.1;apply jFFT;intro p i j;rcases bcStay_of H A L m (T y2 p) (T t2 i) with hs|⟨z,h,f,d,l,v,u⟩;{exact absurd (W u8 hs) j};{exact jU n ⟨z,h,f,d,l,v,(t1 ⟨q.2.2,z.2,(c5V v)⟩).2 (by rw[f0e];exact u)⟩}};{contradiction};{contradiction}
omit Q M S in lemma z7 (_:101<=g)(_:g<108)(q:enabled3 k I P N U X Y g r=true):H0 D w e U X Y o (expand3 k I U X Y g r):=by have:=a6 r;interval_cases g<;>(simp only[expand3,enabled3,Vr,sT,sF,sA,sD,sQ,sN,sC] at q ⊢;have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_));{have ⟨b8,h,j,a9,_,_,a3⟩:=qC q.2;apply jFF;intro b6 a2;rcases bcPick_of H A L a3 (T y2 b6) (T t4 a2) with hs|⟨z,a0,v,u,l,p,b7⟩|⟨b5,b4,a7⟩|⟨l,p,a8⟩|⟨n,a5,f⟩;{exact jL (jL (jL (jR (R (W u8 hs)))))};{exact jL (jL (jL (jL (jU a9 ⟨z,a0,v,u,l,p,(t1 ⟨h,z.2,(c5V p)⟩).2 (by rw[f0e];exact b7)⟩))))};{apply jL;apply jL;apply jR;split_ifs with i;{exact R (W v7 a7)};{exact absurd ⟨λ m=>b5 (by rw[m]),λ m=>b4 (by rw[m])⟩ i}};{have d:=cN j p;have:=c5 d;exact jL (jR (jF2 ⟨l,d,a8.imp (y5 ⟨(a6 r),(c5 d)⟩).2 (t0 ⟨h,j,(c5 d)⟩).2⟩))};{have hne':n.1≠(unctx X (r&&&63)).2.1:=λ m=>a5 (by rw[<-f4e n,m]);exact jR ⟨(fEse (r&&&63) n.1,true),Vo.2 ⟨n.1,lF.2 ⟨lR.2 n.2,by simp[hne']⟩,rfl⟩,bt.2 (W y6 (by rw[f4e];exact f))⟩}};{have ⟨_,d,f,_,_,_,_⟩:=qC q.2.1;have:=c5 q.2.2;exact cb y5 u7 And.left};{have ⟨_,_,d,_,h,f,_⟩:=qC q.2.1;have:=c5 q.2.2;exact zF2 y5};{have ⟨_,_,h,f,_,_,_⟩:=qC q.2.1;have:=c5 q.2.2;exact G λ d=>zOpp2 (T y5 d).2.2.2};{have ⟨_,d,_,_,_,_,_⟩:=qC q.2.1;exact cb y6 u6 And.left};{have ⟨_,_,i,_,_,_,_⟩:=qC q.2.1;apply jFT;intro h j;rcases (T y6 h).2.1 with f|d;{exact absurd (W (v9 (s:=0)) f) j};{exact R (W (v9 (s:=1)) d)}};{have d:=(qC q.2.1).1;exact B λ f=>W y2 (T y6 f).2.2}
omit Q S in lemma z8 (_:108<=g)(_:g<115)(q:enabled3 k I P N U X Y g r=true):H0 D w e U X Y o (expand3 k I U X Y g r):=by interval_cases g<;>(simp only[expand3,enabled3,Vr,sT,sF,sA,sD,sQ,sN,sC] at q ⊢);{have ⟨hm1,hvm⟩:=q;subst hm1;have ⟨ha6,hd14,hdbit⟩:=qM hvm;by_contra hnh;have hns:¬has_sec D e (J (unmask Y (r&&&7)).1):=λ hs=>hnh ⟨_,List.mem_cons_self ..,bt.2 (W (u8 hd14) hs)⟩;have hstay:∀e0:Ei,(unmask Y (r&&&7)).2.1.testBit e0.1=true->¬stay_empty D (10+(e e0).1):=λ e0 he0 hs=>hnh ⟨(fStay e0.1,true),List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨e0.1,lF.2 ⟨lR.2 e0.2,he0⟩,List.mem_cons_self ..⟩)),bt.2 (W (t2 e0.2) (by rwa[f4e]))⟩;have hpick:∀e0:Ei,(unmask Y (r&&&7)).2.1.testBit e0.1=true->∀z:V,(unmask Y (r&&&7)).2.2.testBit z.1=false->¬pick_z D (10+(e e0).1) z:=λ e0 he0 z hz hp=>hnh ⟨(fPick e0.1 z.1,true),List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨e0.1,lF.2 ⟨lR.2 e0.2,he0⟩,List.mem_cons_of_mem _ (Vo.2 ⟨z.1,lF.2 ⟨lR.2 z.2,by simp[hz]⟩,rfl⟩)⟩)),bt.2 (W (t4 ⟨e0.2,z.2⟩) (by rwa[f4e,f0e]))⟩;have hfree:∀z:V,(unmask Y (r&&&7)).2.2.testBit z.1=true->∀l<cap k I z,¬free_slot D w e z l:=λ z hz l hl hf=>by{have hlN:l<capN k I z.1:=cN z.2 (by rwa[f0e]);exact hnh ⟨(fFree z.1 l,true),List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨z.1,lF.2 ⟨lR.2 z.2,hz⟩,List.mem_flatMap.2 ⟨l,lR.2 hlN,List.mem_cons_self ..⟩⟩)),bt.2 (W (u1 ⟨z.2,c5 hlN⟩) (by rwa[f0e]))⟩};have hopp:∀z:V,(unmask Y (r&&&7)).2.2.testBit z.1=true->∀l<cap k I z,∀y:V,(unmask Y (r&&&7)).2.2.testBit y.1=true->¬opp D w z l y:=λ z hz l hl y hy ho=>by{have hlN:l<capN k I z.1:=cN z.2 (by rwa[f0e]);exact hnh ⟨(fOpp z.1 l y.1,true),List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨z.1,lF.2 ⟨lR.2 z.2,hz⟩,List.mem_flatMap.2 ⟨l,lR.2 hlN,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (Vo.2 ⟨y.1,lF.2 ⟨lR.2 y.2,hy⟩,rfl⟩))⟩⟩)),bt.2 (W (v2 ⟨z.2,c5 hlN,y.2⟩) (by rwa[f0e,f0e]))⟩};have hesc:∀z:V,(unmask Y (r&&&7)).2.2.testBit z.1=true->∀l<cap k I z,¬mescProp D w e (J (unmask Y (r&&&7)).1) (unmask Y (r&&&7)).2.1 z l:=λ z hz l hl hm=>by{have hlN:l<capN k I z.1:=cN z.2 (by rwa[f0e]);exact hnh ⟨(fMesc (r&&&7) z.1 l,true),List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨z.1,lF.2 ⟨lR.2 z.2,hz⟩,List.mem_flatMap.2 ⟨l,lR.2 hlN,List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩⟩)),bt.2 (W (y7 ⟨ha6,z.2,c5 hlN⟩) (by rwa[f0e]))⟩};exact maskClosure_of H A M L (by rwa[Fin.val_ofNat,mo hd14]) hns hstay hpick hfree hopp hesc};{have ⟨_,hvm,hz,hl⟩:=q;have ⟨ha6,hd14,_⟩:=qM hvm;have:=c5 hl;exact G λ hm=>zOpp2 (T (y7 ⟨ha6,hz,this⟩) hm).1 hz this hd14};{have ⟨_,hvm,hz,hl⟩:=q;have ⟨ha6,_,_⟩:=qM hvm;have hl5:=c5 hl;apply G;intro hm;obtain⟨_,e',he',s,hra⟩:=T (y7 ⟨ha6,hz,hl5⟩) hm;cases s;{exact⟨(fRa 0 e'.1 (unsl ((r>>>3)&&&63)).1 (unsl ((r>>>3)&&&63)).2,true),List.mem_flatMap.2 ⟨e'.1,lF.2 ⟨lR.2 e'.2,he'⟩,by simp⟩,bt.2 (W (u0 ⟨by omega,e'.2,hz,hl5⟩) (by simpa[f4e] using hra))⟩};{exact⟨(fRa 1 e'.1 (unsl ((r>>>3)&&&63)).1 (unsl ((r>>>3)&&&63)).2,true),List.mem_flatMap.2 ⟨e'.1,lF.2 ⟨lR.2 e'.2,he'⟩,by simp⟩,bt.2 (W (u0 ⟨by omega,e'.2,hz,hl5⟩) (by simpa[f4e] using hra))⟩}};{contradiction};{contradiction};{contradiction};{contradiction}
omit H A K Q L M S in lemma z9 (_:115<=g)(_:g<117)(q:enabled3 k I P N U X Y g r=true):H0 D w e U X Y o (expand3 k I U X Y g r):=by interval_cases g<;>simp[enabled3] at q
omit Q M S in lemma za (_:117<=g)(_:g<128)(q:enabled3 k I P N U X Y g r=true):H0 D w e U X Y o (expand3 k I U X Y g r):=by interval_cases g<;>(simp only[expand3,enabled3,Vr,sT,sF,sA,sD,sQ,sN,sB,sC] at q ⊢;have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_));{have ⟨d,f,i⟩:=nLt q.2.1 q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.1;have h:=c5 q.2.2.2.2.2.2.2.2;exact B λ j=>(t1 ⟨(eSq q.2.1 d f).1,d,h⟩).2 (T x1 j).1};{have ⟨d,_,f⟩:=nLt q.2.1 q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.1;have:=c5 q.2.2.2.2.2.2.2.2;exact B λ h=>W u1 (T x1 h).2.1};{have ⟨d,_,h⟩:=nLt q.2.1 q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.1;have:=c5 q.2.2.2.2.2.2.2.2;exact Z λ i f=>(T x1 i).2.2.1 (T v1 f)};{have ⟨_,m,_,u,_,_,i3,i,n,f,d⟩:=q;have ⟨h,_,j⟩:=nLt m i3 i;have:=c5 n;exact B λ p=>W v1 ((T x1 p).2.2.2 (F _) ((aBi m f).1 d))};{contradiction};{exact Z λ f d=>f0n (by omega) q.2.2.2 (by omega) (pickUniq_of H.1 (T t4 f) (T t4 d))};{contradiction};{contradiction};{have:=c5 q.2.1;exact cb v1 v0 labLive_of};{apply G;intro i;rcases commonExit_of H A L (T v4 i) with ⟨j,n,d⟩|⟨l,m,d⟩;{have h:=cN (by omega) n;exact jL (jG ⟨j,h,(v1 ⟨(by omega),(c5 h),q.2.1⟩).2 d⟩)};{have f:=cN q.2.1 m;exact jR (jG ⟨l,f,(v1 ⟨q.2.1,(c5 f),(by omega)⟩).2 d⟩)}};{have ⟨hx,hni,hp,hy1,hy2,hjc⟩:=q;have hj5:=c5 hjc;have ht1:(if ((r>>>4)&&&3)=2 then 1 else 0)<3:=(by split_ifs<;>omega);have ht2:(if ((r>>>4)&&&3)=0 then 1 else 2)<3:=(by split_ifs<;>omega);exact jT λ hm=>G λ c1=>G λ c2=>G λ h1=>jT λ hn2=>G λ h2=>jT λ hn1=>G λ hj=>jT λ hr1=>jT λ hr2=>by{have h5:=rsubDisj_of H A L (T v3 c1) (T v3 c2) (T v3 h1) (λ u=>hn2 (W v3 u)) (T v3 h2) (λ u=>hn1 (W v3 u)) (λ u=>hm (W v7 u)) (T v0 hj) (λ u=>hr1 (W v8 u)) (λ u=>hr2 (W v8 u));split_ifs with hk;{exact R (W v0 (by show 4<fF D (F (r&&&15));omega))};{have hc:=L.2.2.2.2.2.1 (F (r&&&15));unfold cap at hc;rw[f0v hx] at hc;dsimp only[R1.B,inIB] at hni;rw[hni] at hc;simp only[Bool.false_eq_true,ite_false] at hc;omega}}}
omit S in lemma zS(c:Nat)(q:enS k I P N U X Y c=true):H0 D w e U X Y o (expS k I P U X Y c):=by unfold expS expandScheme;unfold enS enabled at q;dsimp only at q ⊢;have d:c&&&127<128:=aM 7 c;generalize c&&&127=g at d q ⊢;split_ifs at q ⊢ with a b e;{exact if f:g<16 then z0 H A K Q L f q else z1 H A K Q L (by omega) b q};{exact if f:g<48 then z2 H A K Q L M (by omega) f q else z3 K L (by omega) a q};{exact if f:g<80 then z4 K (by omega) f q else z5 H A K L M (by omega) e q};{exact if f:g<101 then z6 H A K L (by omega) f q else if f:g<108 then z7 H A K L (by omega) f q else if f:g<115 then z8 H A K L M (by omega) f q else if f:g<117 then z9 (by omega) f q else za H A K L (by omega) d q}
end Sound
section K
variable {D:Dag} {k I mode sym:Nat} {b:V->Nat} {e:Es}
abbrev Gk D k I m b e:=Vd 10 D/\sem_Comp 10 adj D/\k<=3/\mask I=Ve 10 D/\PureBranch 10 D b/\(Vf 10 D b).card<=k/\GoodEdge D e/\MOk D m
lemma kC(p:CK k I mode sym)(g:Gk D k I mode b e)(_j:∀w o,V0 D k I w e b o->SOk D e o sym):False:=by obtain⟨h,d,f,q,i,m,v,n⟩:=g;obtain⟨w,o,L⟩:=construct_layout_from h d q i m v;obtain⟨t,c,x,u⟩:=p;exact u (trP D w e t c x o) (zS h d f q L n)
abbrev k0(hK:CK k I mode 0) (g:Gk D k I mode b e):=kC hK g λ _ _ _=>trivial
end K
end P3
open DagTools

end PriorG11.SharedCases
namespace PriorG11.SharedCases
open DagTools
def impossibleCell [Slice] (b : CellData) : Prop := ∀ v : Nat → Bool,
  (∀ key, Rup.enS b.budget b.independentMask b.mode b.symmetry b.pins b.pairs b.masks key=true →
    Rup.Holds v (Rup.expS b.budget b.independentMask b.mode b.pins b.pairs b.masks key)) → False

def provedCells [Slice] (cells : List CellData) := ∀ c ∈ cells, impossibleCell c

def permits (I R B : Nat) (c : CellData) : Bool := decide
  (c.independentMask=I ∧ c.budget≤3 ∧ R≤c.budget ∧ c.symmetry=0 ∧ (c.mode=0 ∨ c.mode=1 ∧ B=0))

def finiteDispatch [Slice] (cells : List CellData) : Bool := orbitMasks.all fun I =>
  let count := (mask I).card
  decide (count≤4) && (List.range 4).all fun R => (List.range 4).all fun B =>
    if R+B+1 ≤ count then cells.any (permits I R B) || (List.finRange 10).any fun x =>
      decide (I.testBit x.val=false ∧ 2+R < b4 I x)
    else true

open P3 in
theorem lowerFromAbelianTarskiArtSabintsev [Slice] (cells : List CellData) (all : provedCells cells) (table : finiteDispatch cells=true) :¬(∃C:PEqualNP.CircuitLowerBounds.Circuit,PEqualNP.MetaComplexity.Monotone2 C/\C.size<=18/\(∀x:Fin 10->Bool,(C.eval (List.ofFn x)=true <->∃u v:Fin 10,(u.1,v.1)∈k7/\x u=true/\x v=true))):=by
  rintro⟨C,hM,h7,h3⟩
  obtain⟨D0,d,h1,i⟩:=normalized C hM h3
  have p:=le_trans h1 h7
  obtain⟨b0,h5⟩:=sem_exists_pureBranch graph_ok d.1 i
  have h8:=surplus_bound d p b0 h5
  obtain⟨m,hm⟩:=repr_finset (ineligSet 10 D0)
  have h4:m.1≠0:=λ h0=>by{have e:(ineligSet 10 D0).card=0:=(by rw[<- hm,h0];decide +kernel);omega}
  obtain⟨a,z⟩:=orbit_dispatch m h4 (by rw[hm];exact inelig_indep d i)
  let σ:=autPerm a
  let D:=relabel σ D0
  let b:=relabelBranch σ b0
  have h:StrictLive 10 D:=relabel_strictLive σ d
  have hc:sem_Comp 10 adj D:=rename d i σ (auto_autPerm a)
  have hb:PureBranch 10 D b:=relabel_pureBranch σ d.1 h5
  have h6:(residualUnits 10 D b).card+Bzero 10 D+1<=(ineligSet 10 D).card:=surplus_bound h (by rw[relabel_length];exact p) b hb
  obtain⟨e,hE⟩:=get_edges h.1 hc
  have j:mask (maskImage a m.1)=ineligSet 10 D:=(by rw[mask_maskImage a m,hm,relabel_ineligSet σ d.1])
  generalize maskImage a m.1=I at z j
  rw[<- j] at h6
  let R:=(residualUnits 10 D b).card
  let B := Bzero 10 D
  have entry := List.all_eq_true.mp table I z
  have both := (Bool.and_eq_true _ _).mp entry
  have bound : (mask I).card ≤ 4 := of_decide_eq_true both.1
  have fitting : R+B+1 ≤ (mask I).card := h6
  have hR : R ∈ List.range 4 := List.mem_range.mpr (by omega)
  have hB : B ∈ List.range 4 := List.mem_range.mpr (by omega)
  have dispatch := List.all_eq_true.mp (List.all_eq_true.mp both.2 R hR) B hB
  simp only [if_pos fitting,Bool.or_eq_true,List.any_eq_true] at dispatch
  rcases dispatch with ⟨c,member,permit⟩ | ⟨v,_,pin⟩
  · have requirements : c.independentMask=I ∧ c.budget≤3 ∧ R≤c.budget ∧ c.symmetry=0 ∧
        (c.mode=0 ∨ c.mode=1 ∧ B=0) := of_decide_eq_true permit
    obtain ⟨hmI,hk,hr,hs,mode⟩ := requirements
    have md : MOk D c.mode := by
      rcases mode with zero | ⟨one,hz⟩
      · rw [zero]; trivial
      · rw [one]; exact hz
    have killed : CK c.budget I c.mode 0 := by
      refine ⟨c.pins,c.pairs,c.masks,?_⟩
      have done := all c member
      unfold impossibleCell at done
      simpa only [hmI,hs] using done
    exact k0 killed ⟨h,hc,hk,j,hb,hr,hE,md⟩
  · have p : I.testBit v.val=false ∧ 2+R < b4 I v := of_decide_eq_true pin
    exact pin_kill h hc j hb (le_refl R) v p.1 p.2

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem dispatch0 : @finiteDispatch ⟨0⟩ cells0=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem dispatch1 : @finiteDispatch ⟨1⟩ cells1=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem dispatch2 : @finiteDispatch ⟨2⟩ cells2=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem dispatch3 : @finiteDispatch ⟨3⟩ cells3=true := by decide +kernel
end PriorG11.SharedCases

namespace PriorG11.Bounds
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def edges : List (Nat × Nat) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
abbrev G := PEqualNP.EdgeOwnership.edgeGraph 11 edges
theorem adjacent (a b : Fin 11) : G.Adj a b ↔ (a.val,b.val) ∈ edges ∨ (b.val,a.val) ∈ edges := by
  exact (show ∀ a b : Fin 11, G.Adj a b ↔ (a.val,b.val) ∈ edges ∨ (b.val,a.val) ∈ edges by decide +kernel) a b
open PriorG11.SharedCases

abbrev Certified := ∀ i : Fin 4, @provedCells ⟨i⟩ (cellsAt i)

theorem dispatchAt (i : Fin 4) : @finiteDispatch ⟨i⟩ (cellsAt i) = true := by
  fin_cases i
  · exact SharedCases.dispatch0
  · exact SharedCases.dispatch1
  · exact SharedCases.dispatch2
  · exact SharedCases.dispatch3

def vertex (i : Fin 4) : Fin 11 := ⟨i.val,by have := i.isLt; omega⟩

theorem sliceEdges (i : Fin 4) : ∀ u v : Fin 10,
    G.Adj ((vertex i).succAbove u) ((vertex i).succAbove v) ↔
      (u.val,v.val) ∈ @k7 ⟨i⟩ ∨ (v.val,u.val) ∈ @k7 ⟨i⟩ := by
  fin_cases i <;> decide +kernel

theorem sliceEvaluation (i : Fin 4) (x : Fin 10 → Bool) : graphFun G ∅ ((vertex i).insertNth false x) = true ↔
    ∃ u v : Fin 10, (u.val,v.val) ∈ @k7 ⟨i⟩ ∧ x u=true ∧ x v=true := by
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
  constructor
  · rintro ⟨a,b,edge,ha,hb⟩
    have ea : a≠vertex i := by intro eq; subst a; simp at ha
    have eb : b≠vertex i := by intro eq; subst b; simp at hb
    obtain ⟨u,rfl⟩ := Fin.exists_succAbove_eq ea
    obtain ⟨v,rfl⟩ := Fin.exists_succAbove_eq eb
    rw [Fin.insertNth_apply_succAbove] at ha hb
    rcases (sliceEdges i u v).mp edge with h|h
    · exact ⟨u,v,h,ha,hb⟩
    · exact ⟨v,u,h,hb,ha⟩
  · rintro ⟨u,v,edge,hu,hv⟩
    refine ⟨(vertex i).succAbove u,(vertex i).succAbove v,(sliceEdges i u v).mpr (Or.inl edge),?_,?_⟩
    · simpa using hu
    · simpa using hv

theorem four_lower (certified : Certified) (v : Fin 11) (C : Circuit) (hv : v.val<4) (legal : IsAO2 10 C)
    (relation : ∀ x : Fin 10 → Bool, circuitFun 10 C x = graphFun G ∅ (v.insertNth false x)) : 19≤C.size := by
  let i : Fin 4 := ⟨v.val,hv⟩
  have same : vertex i = v := Fin.ext rfl
  have mono : Monotone2 C := fun g h => ⟨legal.1 g h,by have := legal.2.2 g h; omega⟩
  by_contra h
  apply @lowerFromAbelianTarskiArtSabintsev ⟨i⟩ (cellsAt i) (certified i) (dispatchAt i)
  refine ⟨C,mono,by omega,fun x => ?_⟩
  change circuitFun 10 C x=true ↔ _
  rw [relation x,← same]
  exact sliceEvaluation i x

end PriorG11.Bounds

namespace PriorG11.Proof
open SharedCases Bounds Learning Blocks

theorem certified (all : Successful) : Certified := by
  intro i b member
  obtain ⟨j,hj,he⟩ := List.getElem_of_mem member
  have eq : (cellsAt i).getD j default = b := (List.getD_eq_getElem _ _ hj).trans he
  have checked : whole (before i+j) (@reason ⟨i⟩ b) (@active ⟨i⟩ b)=true := by
    apply List.all_eq_true.mpr
    intro s hs
    have result := all i j hj s (List.mem_range.mp hs)
    simpa only [atBlock, eq] using result
  intro v allowed
  have admissible (key : Nat) : holds v (@reason ⟨i⟩ b key) := by
    by_cases h : @active ⟨i⟩ b key=true
    · simp only [reason,if_pos h]
      obtain ⟨lit,member,agreesWith⟩ := allowed key h
      exact ⟨lit,member,agreesWith⟩
    · simpa only [reason,if_neg h] using holds_tautology v
  exact Bool.noConfusion (checked.symm.trans (whole_sound admissible))

end PriorG11.Proof

namespace PriorG11.Bounds
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def evaluation (x : Fin 11 → Bool) := edges.any (fun e => x ⟨e.1%11,Nat.mod_lt _ (by decide)⟩ && x ⟨e.2%11,Nat.mod_lt _ (by decide)⟩)
theorem graphRead (x : Fin 11 → Bool) : graphFun G ∅ x = evaluation x := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false, decide_false, Bool.false_or, decide_eq_true_eq,
    evaluation,List.any_eq_true,Bool.and_eq_true_iff]
  have inRange : ∀ e ∈ edges, e.1 < 11 ∧ e.2 < 11 := by decide
  constructor
  · rintro ⟨a,b,h,ha,hb⟩
    rcases (adjacent a b).mp h with h | h
    · exact ⟨(a.val,b.val),h,by simpa [Nat.mod_eq_of_lt a.isLt] using ha,by simpa [Nat.mod_eq_of_lt b.isLt] using hb⟩
    · exact ⟨(b.val,a.val),h,by simpa [Nat.mod_eq_of_lt b.isLt] using hb,by simpa [Nat.mod_eq_of_lt a.isLt] using ha⟩
  · rintro ⟨⟨a,b⟩,h,ha,hb⟩
    have bounds := inRange (a,b) h
    refine ⟨⟨a,bounds.1⟩,⟨b,bounds.2⟩,(adjacent _ _).mpr (Or.inl h),?_,?_⟩
    · simpa [Nat.mod_eq_of_lt bounds.1] using ha
    · simpa [Nat.mod_eq_of_lt bounds.2] using hb

def packed (x : Fin 11 → Bool) : Bool :=
  ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).any
    (fun i => x (Fin.ofNat 11 (i/11)) && x (Fin.ofNat 11 (i % 11)))

theorem graph_packed (x : Fin 11 → Bool) : graphFun G ∅ x = packed x := by
  rw [graphRead]
  rfl

theorem packed_lower (certified : Certified) (v : Fin 11) (C : Circuit) (hv : v.val < 4) (hC : IsAO2 10 C)
    (hF : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = packed (v.insertNth false x)) :
    19 ≤ C.size :=
  four_lower certified v C hv hC (fun x => (hF x).trans (graph_packed _).symm)

end PriorG11.Bounds
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PreparedCircuit.Reindex

def wire {n m : ℕ} (σ : Fin n → Fin m) (i : ℕ) : ℕ :=
  if hi : i < n then (σ ⟨i, hi⟩).val else m + (i - n)

def gate {n m : ℕ} (σ : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire σ)⟩

def circuit {n m : ℕ} (σ : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (gate σ), wire σ C.output⟩

theorem size_eq {n m} (σ : Fin n → Fin m) (C : Circuit) : (circuit σ C).size = C.size := by
  simp [circuit, Circuit.size]

private theorem readWire {n m} (σ : Fin n → Fin m) (x : Fin m → Bool) (gates : List Bool) (i : ℕ) :
    (List.ofFn x ++ gates).getD (wire σ i) false =
      (List.ofFn (fun j => x (σ j)) ++ gates).getD i false := by
  by_cases hi : i < n
  · let j := σ ⟨i, hi⟩
    have left : j.val < (List.ofFn x).length := by simp
    have right : i < (List.ofFn (fun k => x (σ k))).length := by simpa using hi
    simp only [wire, hi, ↓reduceDIte]
    rw [List.getD_append _ _ _ _ left, List.getD_append _ _ _ _ right]
    simp [List.getD_eq_getElem?_getD, hi, j]
  · have left : (List.ofFn x).length ≤ m + (i - n) := by simp
    have right : (List.ofFn (fun k => x (σ k))).length ≤ i := by simpa using Nat.le_of_not_gt hi
    simp only [wire, hi, ↓reduceDIte]
    rw [List.getD_append_right _ _ _ _ left, List.getD_append_right _ _ _ _ right]
    simp

private def appendValue (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem foldGates {n m} (σ : Fin n → Fin m) (x : Fin m → Bool) (gs : List Gate)
    (priorValues : List Bool) : ∃ suffix : List Bool,
      (gs.map (gate σ)).foldl appendValue (List.ofFn x ++ priorValues) = List.ofFn x ++ suffix ∧
      gs.foldl appendValue (List.ofFn (fun j => x (σ j)) ++ priorValues) = List.ofFn (fun j => x (σ j)) ++ suffix := by
  induction gs generalizing priorValues with
  | nil => exact ⟨priorValues, rfl, rfl⟩
  | cons g gs ih =>
    let w := List.ofFn (fun j => x (σ j)) ++ priorValues
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    have inputs : (gate σ g).inputs.map (fun i => (List.ofFn x ++ priorValues).getD i false) =
        g.inputs.map (fun i => w.getD i false) := by
      simp only [gate, List.map_map]
      apply List.map_congr_left
      intro i _
      exact readWire σ x priorValues i
    have left : appendValue (List.ofFn x ++ priorValues) (gate σ g) = List.ofFn x ++ (priorValues ++ [v]) := by
      unfold appendValue
      rw [inputs]
      exact List.append_assoc _ _ _
    have right : appendValue w g = List.ofFn (fun j => x (σ j)) ++ (priorValues ++ [v]) :=
      List.append_assoc _ _ _
    obtain ⟨suffix, hl, hr⟩ := ih (priorValues ++ [v])
    refine ⟨suffix, ?_, ?_⟩
    · simp only [List.map_cons, List.foldl_cons, left]
      exact hl
    · change gs.foldl appendValue (appendValue w g) = _
      rw [right]
      exact hr

theorem eval_eq {n m} (σ : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    (circuit σ C).eval (List.ofFn x) = C.eval (List.ofFn (fun j => x (σ j))) := by
  obtain ⟨suffix, hl, hr⟩ := foldGates σ x C.gates []
  simp only [List.append_nil] at hl hr
  change ((C.gates.map (gate σ)).foldl appendValue (List.ofFn x)).getD (wire σ C.output) false =
    (C.gates.foldl appendValue (List.ofFn (fun j => x (σ j)))).getD C.output false
  rw [hl, hr]
  exact readWire σ x suffix C.output

end PreparedCircuit.Reindex

namespace PriorG11.Join

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PreparedCircuit.Reindex

def append (P T : Circuit) : Circuit := ⟨P.gates ++ T.gates, T.output⟩

theorem append_size (P T : Circuit) : (append P T).size = P.size + T.size := by
  simp [append, Circuit.size]

theorem append_eval (P T : Circuit) (x : List Bool) :
    (append P T).eval x = T.eval (P.wires x) := by
  simp [append, Circuit.eval, Circuit.wires, List.foldl_append]

theorem append_legal {n : ℕ} {P T : Circuit} (hP : IsAO2 n P)
    (hT : IsAO2 (n+P.size) T) : IsAO2 n (append P T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact hP.1 g h
    · exact hT.1 g h
  · intro j hj i hi
    change j < (P.gates ++ T.gates).length at hj
    change i ∈ ((P.gates ++ T.gates).getD j ⟨GateOp.or,[]⟩).inputs at hi
    by_cases hp : j < P.gates.length
    · rw [List.getD_append _ _ _ _ hp] at hi
      exact hP.2.1 j hp i hi
    · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hp)] at hi
      rw [List.length_append] at hj
      have h := hT.2.1 (j-P.gates.length) (by omega) i hi
      simp only [Circuit.size] at h
      omega
  · intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact hP.2.2 g h
    · exact hT.2.2 g h

theorem reindex_legal {a b : ℕ} (σ : Fin a → Fin b) {T : Circuit}
    (hT : IsAO2 a T) : IsAO2 b (circuit σ T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
    exact hT.1 k hk
  · intro j hj i hi
    have hj' : j < T.gates.length := by simpa [circuit] using hj
    have he : gateAt (circuit σ T) j = gate σ (gateAt T j) := by
      simp [gateAt, circuit, List.getD_eq_getElem?_getD, hj']
    rw [he] at hi
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hi
    have h := hT.2.1 j hj' w hw
    by_cases low : w<a
    · simp only [wire,low, ↓reduceDIte]
      exact (σ ⟨w,low⟩).isLt.trans_le (Nat.le_add_right _ _)
    · simp only [wire,low, ↓reduceDIte]
      omega
  · intro g hg
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
    simpa [gate] using hT.2.2 k hk

theorem wires_length (P : Circuit) (x : List Bool) : (P.wires x).length = x.length + P.size := by
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have go : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length+gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g t ih => intro w; simp only [List.foldl_cons, ih, step, List.length_append,
        List.length_cons, List.length_nil]; omega
  exact go P.gates x

theorem ofFn_getD {k : ℕ} (w : List Bool) (h : w.length=k) :
    List.ofFn (fun i : Fin k => w.getD i.val false) = w := by
  subst k
  apply List.ext_getElem
  · simp
  · intro i _ hi
    simp [List.getD_eq_getElem?_getD, hi]

def plug {n k : ℕ} (P : Circuit) (σ : Fin k → Fin (n+P.size)) (T : Circuit) : Circuit :=
  append P (circuit σ T)

theorem plug_size {n k : ℕ} (P : Circuit) (σ : Fin k → Fin (n+P.size)) (T : Circuit) :
    (plug P σ T).size = P.size+T.size := by
  rw [plug, append_size, size_eq]

theorem plug_legal {n k : ℕ} (P : Circuit) (σ : Fin k → Fin (n+P.size)) (T : Circuit)
    (hp : IsAO2 n P) (ht : IsAO2 k T) : IsAO2 n (plug P σ T) :=
  append_legal hp (reindex_legal σ ht)

theorem plug_eval {n k : ℕ} (P : Circuit) (σ : Fin k → Fin (n+P.size)) (T : Circuit)
    (x : Fin n → Bool) :
    (plug P σ T).eval (List.ofFn x) =
      T.eval (List.ofFn fun j => (P.wires (List.ofFn x)).getD (σ j).val false) := by
  let z : Fin (n+P.size) → Bool := fun i => (P.wires (List.ofFn x)).getD i.val false
  have hz : List.ofFn z = P.wires (List.ofFn x) := ofFn_getD _
    (by rw [wires_length, List.length_ofFn])
  calc
    _ = (circuit σ T).eval (P.wires (List.ofFn x)) := append_eval _ _ _
    _ = (circuit σ T).eval (List.ofFn z) := congrArg _ hz.symm
    _ = T.eval (List.ofFn fun j => z (σ j)) := eval_eq σ T z

end PriorG11.Join
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
namespace TailExamples
def words : List Nat := [16909538860378144768,16909539410841305088,16927600263721314816,17213020425657819296,17215830820325998784,17216961118282247904,18374403832151997952]
def circuits : List Circuit := [⟨[⟨.and,[0,4]⟩,⟨.and,[1,2]⟩,⟨.or,[3,6]⟩,⟨.and,[5,6]⟩,⟨.and,[7,8]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.and,[1,2]⟩,⟨.and,[3,6]⟩,⟨.and,[5,6]⟩,⟨.or,[0,7]⟩,⟨.or,[4,8]⟩,⟨.and,[9,10]⟩],11⟩,⟨[⟨.and,[1,2]⟩,⟨.or,[3,4]⟩,⟨.or,[0,6]⟩,⟨.and,[5,6]⟩,⟨.and,[7,8]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.or,[4,5]⟩,⟨.and,[1,6]⟩,⟨.and,[3,6]⟩,⟨.or,[0,7]⟩,⟨.or,[2,8]⟩,⟨.and,[9,10]⟩],11⟩,⟨[⟨.and,[3,4]⟩,⟨.or,[2,6]⟩,⟨.or,[5,6]⟩,⟨.and,[1,7]⟩,⟨.and,[0,8]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.or,[2,3]⟩,⟨.or,[4,6]⟩,⟨.or,[5,6]⟩,⟨.and,[1,7]⟩,⟨.and,[0,8]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.or,[0,1]⟩,⟨.or,[3,4]⟩,⟨.or,[2,6]⟩,⟨.and,[5,6]⟩,⟨.and,[7,8]⟩,⟨.or,[9,10]⟩],11⟩]
def W (i : Fin 7) := circuits.getD i.val ⟨[],0⟩
theorem legalAndSize : ∀ i : Fin 7, IsAO2 6 (W i) ∧ (W i).size = 6 := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem realization : ∀ (i : Fin 7) (x : Fin 6 → Bool), (W i).eval (List.ofFn x) =
    (words.getD i.val 0).testBit (∑ j : Fin 6, if x j then 2^j.val else 0) := by decide +kernel
end TailExamples
namespace PriorG11.Templates

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm TailExamples

theorem word_index (w : ℕ) (hw : w ∈ words) :
    ∃ i : Fin 7, words.getD i.val 0 = w := by
  obtain ⟨j,hj,he⟩ := List.getElem_of_mem hw
  have hj' : j < 7 := hj
  exact ⟨⟨j,hj'⟩, (List.getD_eq_getElem words 0 hj).trans he⟩

theorem bit_weight : ∀ i : Fin 6,
    ([1,2,4,8,16,32] : List ℕ).getD i.val 0 = 2^i.val := by decide +kernel

theorem word_tail_witness {n : ℕ} (f : (Fin n → Bool) → Bool) (s : ℕ)
    (lower : ∀ C : Circuit, IsAO2 n C → (∀ x, C.eval (List.ofFn x) = f x) → s ≤ C.size)
    (P : Circuit) (hp : IsAO2 n P) (room : P.size + 6 < s)
    (w : ℕ) (hw : w ∈ words) (σ : Fin 6 → Fin (n + P.size)) :
    ∃ x : Fin n → Bool,
      w.testBit (∑ i : Fin 6, if (P.wires (List.ofFn x)).getD (σ i).val false
        then ([1,2,4,8,16,32] : List ℕ).getD i.val 0 else 0) ≠ f x := by
  obtain ⟨j, rfl⟩ := word_index w hw
  by_contra! h
  let T := W j
  let C := Join.plug P σ T
  have legal := Join.plug_legal P σ T hp (legalAndSize j).1
  have exact_size : C.size = P.size + 6 :=
    (Join.plug_size P σ T).trans (congrArg (P.size + ·) (legalAndSize j).2)
  have agrees (x : Fin n → Bool) : C.eval (List.ofFn x) = f x := by
    rw [show C.eval (List.ofFn x) = _ from Join.plug_eval P σ T x,
      show (W j).eval _ = _ from realization j (fun i => (P.wires (List.ofFn x)).getD (σ i).val false)]
    simpa only [bit_weight] using h x
  have required := lower C legal agrees
  omega

end PriorG11.Templates

end PEqualNP.Outside.L_meta_18562

open PEqualNP.Outside.L_meta_18562.PriorG11 in
theorem PEqualNP.Outside.L_meta_18562 : ∀ (x1 : Fin (11 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   ↑x1 < (4 : ℕ) →     PEqualNP.TopForm.IsAO2 (10 : ℕ) x2 →       x2.size ≤ (12 : ℕ) →         ∀ x6 ∈ [(16909538860378144768 : ℕ), (16909539410841305088 : ℕ), (16927600263721314816 : ℕ), (17213020425657819296 : ℕ), (17215830820325998784 : ℕ), (17216961118282247904 : ℕ), (18374403832151997952 : ℕ)],           ∀ (x8 : Fin (6 : ℕ) → Fin ((10 : ℕ) + x2.size)),             ∃ (x9 : Fin (10 : ℕ) → Bool),               x6.testBit (∑ x10 : Fin (6 : ℕ), if (x2.wires (List.ofFn x9)).getD (↑(x8 x10)) Bool.false = Bool.true then [(1 : ℕ), (2 : ℕ), (4 : ℕ), (8 : ℕ), (16 : ℕ), (32 : ℕ)].getD ↑x10 (0 : ℕ) else (0 : ℕ)) ≠                 have x10 : Fin (11 : ℕ) → Bool := x1.insertNth Bool.false x9;                 [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)].any fun (x11 : ℕ) => x10 (Fin.ofNat (11 : ℕ) (x11 / (11 : ℕ))) && x10 (Fin.ofNat (11 : ℕ) (x11 % (11 : ℕ))) := by
  intro v P hv hp hb w hw σ
  let f := fun x : Fin 10 → Bool => Bounds.packed (v.insertNth false x)
  have lower (C) := Bounds.packed_lower (Proof.certified Proof.successful) v C hv
  exact Templates.word_tail_witness f 19 lower P hp (by omega) w hw σ
