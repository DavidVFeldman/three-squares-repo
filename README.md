# Polynomial identities, sums of three squares, and quaternionic (anti-)automorphisms

D. V. Feldman (University of New Hampshire)

Words in a free monoid on four letters, fixed by reversal-with-inversion of the
first letter pair, evaluate under a quaternionic substitution to identities

    (t^2+u^2)^{2m} (x^2+y^2+z^2)^n  =  f_1^2 + f_j^2 + f_k^2

of integer polynomials. The paper (in `paper/`) proves the cancellation theorem
behind the family over every commutative ring, classifies the identities up to
sign-equivalence by an exact census with generating function
(1+s)/(1-s-q-3sq), proves injectivity of the word evaluation via Świerczkowski's
freeness theorem, shows (with Pfister's theory) that the even exponent is forced
whenever three squares are genuinely needed, and proves that the rotations
through arccos(1/3) about the three coordinate axes generate a free group of
rank three, by a rank-one-modulo-3 refinement of Świerczkowski's method.

## Formal verification

`lean/` contains a Lean 4 formalization, checked against Mathlib: 91 theorems
in four files, produced in four commissioned rounds (work orders and reports in
`docs/`). Closure standard throughout: every theorem compiles with
`#print axioms` showing at most `propext`, `Classical.choice`, `Quot.sound`;
no `sorry`; no `native_decide`. Machine-checked contents include:

- the cancellation theorem (division-free strip induction, arbitrary
  commutative ring) and the three-squares identity  (`Round1.lean`);
- the [2,3,3] obstruction: no bilinear composition formula  (`Round1.lean`);
- the census bijection |S(m,n)| = 2 R(m, ceil(n/2)-1)  (`Round2.lean`);
- Świerczkowski's freeness theorem for the arccos(1/3) pair, by a simplified
  per-initial-letter invariant  (`Round2.lean`);
- injectivity of the generic word evaluation up to sign, and the
  sign-equivalence classification  (`Round3.lean`);
- freeness of the rank-three coordinate-axis rotation group (the paper's
  Theorem on three axes), by the mesh argument, with Świerczkowski's theorem
  re-derived from it — two independent proofs of the pair's freeness — and the
  classes-count capstone: numClasses m n = R(m, ceil(n/2)-1)  (`Round4.lean`).

To check: `cd lean && lake build`. CI runs the build and asserts the axiom audit.

## Scripts

`scripts/gen_appendix.py` regenerates the paper's appendix tables from the
words and verifies each identity symbolically before printing it.
