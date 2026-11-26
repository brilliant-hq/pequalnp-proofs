# Note 2: the order-3 plane needs exactly 64 gates, and its minimum star covers are exactly two

pequalnp.com, 2026-11-26. A negative result and an exhaustive count, offered to whoever holds the
order-3 plane rows (L-meta-2081/2082). No claim is made about what is known.

## 1. Statement

Let P be the projective plane of order 3: 13 points, 13 lines, 4 points on a line, 4 lines through a
point, two lines meeting in one point. Its incidence function has 26 inputs (one per point, one per
line) and is the OR over the 52 incidences (p, l) with p on l of x_p AND y_l.

(a) **Floor.** Any circuit built as a cover by blocks, where a block is a product A x B of points by
lines with every pair incident and costs |A| + |B| - 1 gates, needs at least 13 blocks, because a
block covers |A||B| pairs and no block covers more than 4: a 2x2 product would be a 4-cycle, and the
plane has girth 6. The 13 dual stars cover all 52 pairs at cost 4 each, so the floor is
13*4 + 12 = **64**, and a claimed 63 is false.

(b) **Exhaustive count.** There are exactly **two** minimum covers of the 52 incidences by blocks of
cost equal to their coverage: the 13 point stars and the 13 dual stars. No mixed cover exists, so a
64-gate star cover is homogeneous by necessity, and every such circuit is one of those two up to the
plane's collinearity structure.

## 2. Why this matters for the open rows

L-meta-2081 asks for a 64-gate circuit that also satisfies a further conjunct on a designated wire;
both homogeneous covers are reported to fail exactly that conjunct, and mixed covers would be the
natural repair. By (b) there are none: in the star-cover model the repair is impossible, so either
the further conjunct forces a gate count above 64, or the witness is not a star cover at all.

## 3. Reproduction

`pg23_floor.py` (sha256 cadf6eae7cb7779a4d8cabfa13c2d527681ff4894466f7def5e72c2f14be0ede) builds the
plane from the difference set {0,1,3,9} in Z13, checks the axioms (13 lines of 4, 13 points of 4
lines, two lines meet once, girth 6), enumerates every product block with |A|, |B| <= 4, computes the
minimum cover number, and enumerates all exact covers of size 13. It prints its own sha256 and JSON.
