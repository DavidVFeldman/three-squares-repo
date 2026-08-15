# Aristotle Commission — Three Squares, Round 1

**Project.** Formal verification of the cancellation core of *Polynomial identities, sums of three squares, and quaternionic (anti-)automorphisms* (D. V. Feldman). Paper source `piq_rewrite.tex` accompanies this order for reference; the Lean statements are authoritative where they and the paper differ in packaging.

**Session protocol.** Fresh session; all state is in this tarball. No mid-flight questions. **Report rather than repair anything that fails as stated**: if a statement in `Round1.lean` does not compile, or appears false, or resists proof, record the finding in the report and proceed to the next item. Do not modify any definition or theorem statement. Auxiliary private lemmas may be added freely.

**Deliverable.** The tarball returned with `Round1.lean` completed, a build log, and a report listing, per theorem: status (proved / failed-as-stated / blocked), the `#print axioms` output, and (for M2.4–M2.5) whether `decide` or `native_decide` was used.

**Closure criterion.** A theorem is closed only when it compiles and `#print axioms` shows at most `propext`, `Classical.choice`, `Quot.sound`. Exception: M2.4 and M2.5 may additionally show `Lean.ofReduceBool`. No other axioms; no `sorry` in closed items.

---

## Contents and intent

`Round1.lean` defines: the four-letter alphabet; words as lists; the involutions ι_α, ι_β; the symmetry class `IsSym` (reversal-with-α-inversion, **without** reducedness, which this round does not need); reducedness; letter counts; the quaternionic evaluation `hW` over an arbitrary commutative ring; the coordinatewise anti-involution `theta`; the recurrence-defined census function `Rc`; a brute-force word enumerator; and two 3×3 matrix statements.

### Module M1 — Cancellation core (required)

| Item | Statement | Method sketch |
|---|---|---|
| M1.1 | `theta_mul`, `theta_theta` | `ext`; quaternion component simp lemmas; `ring`. |
| M1.2 | `theta_hL`, `theta_hW` | Four letter cases; then list induction. Note `List.prod` of a reversed list needs manual induction (the monoid is noncommutative); use `theta_mul` to reverse as you go. |
| M1.3 | `isSym_strip` | Pure list lemma. Peel head `c`; `IsSym` forces the last letter to be `c.ia` and the interior to be symmetric. |
| M1.4 | `imI_conj` | Four cases; destructure `p`; each is an exact polynomial identity (machine-verified in sympy prior to commissioning — no division, valid over any `CommRing`). |
| M1.5 | `imI_hW_eq_zero` | **Main theorem.** Strong induction on `σ.length` via M1.3; split `hW` over the decomposition with `List.prod_cons/append`; apply M1.4. |
| M1.6 | `alphaCount_even` | Same induction skeleton as M1.5. |
| M1.7 | `normSq_hL_alpha/beta`, `normSq_hW` | Letter norms by `ring`; then induction with `normSq_mul`. If the component formula for `normSq` over a general `CommRing` is missing from Mathlib, derive it locally from `normSq_def`. |
| M1.8 | `three_squares` | Assemble M1.5 + M1.7 + the component formula. This is the paper's Corollary 3.5 in machine form. |
| M1.9 | `i_mul_hW`, `hW_ib_components` | Letter cases then induction; components by expanding multiplication by `⟨0,1,0,0⟩`. Inverse-free by design. |
| M1.10 | `hW_neg_yz` | Letter cases then induction. With M1.9b this is the paper's Proposition 4.1. |

Design note: the induction route (M1.3–M1.5) rather than the fixed-point route is deliberate. The fixed-point argument yields only `2 * imI = 0` over a general ring; the strip induction is division-free and closes over every `CommRing` directly. Do not "simplify" M1.5 to the fixed-point argument.

### Module M2 — Census (required except as marked)

| Item | Statement | Method sketch |
|---|---|---|
| M2.1–M2.3 | `Rc_zero`, `Rc_one`, `Rc_two` | Induction on `k`; unfold one step of `Rc`; `ring`/`omega`. |
| M2.4–M2.5 | `census_1_3`, `census_2_1` | **NATIVE permitted.** Search spaces 4^5 = 1024 and 4^5 = 1024; try `decide` first. These are consistency smoke tests linking the enumerator to `Rc` (12 = 2·Rc 1 1, 4 = 2·Rc 2 0). |

The full bijection `censusCount m n = 2 * Rc m (⌈n/2⌉ − 1)` is **out of scope** for this round (Round 2, via the bisection lemma).

### Module M3 — The [2,3,3] obstruction (M3.1 required; M3.2 report-if-blocked)

| Item | Statement | Method sketch |
|---|---|---|
| M3.1 | `no_orthogonal_skew` | `Matrix.det_transpose`, `Matrix.det_neg` (odd dimension), `det_mul`, `det_one`; conclude `det B = 0` and `(det B)^2 = 1`. Short. |
| M3.2 | `no_bilinear_233` | Extract Gram conditions by specializing `(t,u)` to `(1,0)`, `(0,1)`, `(1,1)` and polarizing over ℝ (evaluate at basis vectors and sums of basis vectors to recover matrix entries as dot products). Then `B := A₁ᵀ * A₂` is skew and, via `Matrix.mul_eq_one_comm`, orthogonal; apply M3.1. The coefficient bookkeeping has been machine-verified symbolically. If the polarization plumbing exceeds reasonable effort, report M3.2 blocked with M3.1 closed. |

---

## Out of scope (announced for later rounds)

- **Round 2:** the bisection lemma for reduced symmetric words; the bijection `censusCount m n = 2 * Rc m k`; Świerczkowski's freeness theorem for the rotation pair through arccos(1/3) about perpendicular axes (his 1958 divisibility-by-3 induction, transported to quaternions over `Zsqrtd 2` — a complete proof plan will accompany that order).
- **Round 3:** injectivity of `hW` on reduced words at the √2-specialization; the sign-equivalence classification.

Nothing in Round 1 depends on anything out of scope.
