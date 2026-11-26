# Notes on L-meta-8205 (order-3 plane circuit search)

## Geometry

The statement uses the Singer difference set for the projective plane of order 3:

- Points: ℤ/13ℤ
- Difference set D = {0, 1, 3, 9}
- Lines: the 13 translates D + t for t = 0..12

Verified properties:
- Every line has 4 points
- Every pair of points in exactly one line
- This is the unique PG(2,3)

## Statement summary

Existence of a monotone fan-in-2 circuit C of size ≤ 32 such that:
- NestedCover.ReadsBack 27 C
- C is true on the “incident pair” inputs derived from the difference set
- C is false on generic maximal false inputs (no full line present on either side)

## Status

This is a constructive search step (part of a reduction of L-meta-2401).
A correct circuit of size ≤ 32 has not yet been produced in this session.

PMLL / structured search under drQedwards.
