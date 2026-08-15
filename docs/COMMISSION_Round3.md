# Aristotle Commission — Three Squares, Round 3

**Project.** Final mathematical round of the formalization of *Polynomial identities, sums of three squares, and quaternionic (anti-)automorphisms* (D. V. Feldman). Rounds 1 and 2 are closed (48/48, no sorries, no axiom exceptions). This round delivers injectivity of the word evaluation and the sign-equivalence classification — together, the formal content of the paper's Theorems 6.1 and 6.2.

**Session protocol.** Fresh session; all state is in this tarball. No mid-flight questions. **Report rather than repair anything that fails as stated.** `Round1.lean` and `Round2.lean` are the closed artifacts of the previous rounds and are **frozen**: import them, use anything in them (including, e.g., `isSym_strip`, `bisection_exists`, `reduced_ibMap`, `swierczkowski_free`), modify nothing. All definitions in `Round3.lean` are final; private auxiliary lemmas may be added freely. Add a `Round3` target to `lakefile.toml` as in Round 2.

**Deliverable.** The tarball returned with `Round3.lean` completed, a build log, and a report listing per theorem: status, `#print axioms` output.

**Closure criterion.** Compiles; `#print axioms` shows at most `propext`, `Classical.choice`, `Quot.sound`. No `native_decide` exceptions this round; no `sorry` in closed items.

**Pre-certification.** All statements verified numerically before commissioning: the letter bridge `conjMat (qL c) = genM c` exactly (the norm 3 supplies Round 2's scaling — no adjustment factor); the word bridge on all 1457 reduced words of length ≤ 6 by exact ℤ[√2] arithmetic; multiplicativity and sign-kill of `conjMat` on 200 random quaternions; the transpose and orthogonality laws through length 6; reducedness and the factorization of the distinct-head concatenation on 9840 reduced pairs; and the classification on all 52 symmetric reduced words of length ≤ 6 at the level of polynomial quaternions. If a statement resists, suspect the route, then report.

---

## Design note (binding)

The comparison theorem C3d must **not** introduce a general free-group reduction function. The commissioned route needs none:

1. **Equal lengths** from orthogonality (C2c): equal matrices give `(9:R2)^ℓ₁ • 1 = (9:R2)^ℓ₂ • 1`.
2. **Equal heads** strip: multiply by the transpose generator, apply C2b, cancel the entrywise factor 9 over ℤ[√2] (componentwise over ℤ), recurse on the reduced tails.
3. **Distinct heads** `c ≠ d`: the concatenation `invRev (c :: τ₁) ++ (d :: τ₂)` is *automatically reduced* — its junction letters are `c.inv` then `d`, and the junction condition `d ≠ (c.inv).inv = c` is exactly the case hypothesis — and nonempty, with matrix
   `(evalM σ₁)ᵀ · evalM σ₂ = (evalM σ₁)ᵀ · evalM σ₁ = (9:R2)^ℓ₁ • 1 = (3:R2)^(ℓ₁+ℓ₂) • 1`,
   which is precisely the scalar form forbidden by Round 2's `swierczkowski_free`.

This is the entire reason Round 2 delivered Świerczkowski in the `≠ (3)^ℓ • 1` form.

## Items

### C0 — product laws (warm-up)
`hW_cons`, `evalM_cons`, `evalM_append`: `List.map_cons/append`, `List.prod_cons/append`.

### C1 — quaternion-to-matrix bridge
| Item | Theorem | Notes |
|---|---|---|
| C1a | `re_conj_pure` | Destructure; `ring`. |
| C1b | `conjMat_mul` | Either the basis-decomposition route (via C1a and linearity) or brute force: `ext i j`, `Matrix.mul_apply`, destructure both quaternions, `Fin.sum_univ_three`, `ring`. Both work; the second is dumber and safer. |
| C1c | `conjMat_neg` | `ext`; `ring`. |
| C1d | `conjMat_qL` | Four letters × nine entries; `Zsqrtd` components, √2·√2 = 2. |
| C1e | `conjMat_qW` | Induction; base `conjMat 1 = 1` (nine entries). |

### C2 — transposes and orthogonality
`genM_transpose`, `genM_orth` (four finite checks each); `evalM_orth` (induction; mind the `smul` bookkeeping: `(9)^(n+1) = 9 * 9^n` and `Matrix.mul_smul`/`smul_mul`); `evalM_invRev` (induction via `invRev (c :: τ) = invRev τ ++ [c.inv]`, C0c, C2a, `Matrix.transpose_mul`); `reduced_invRev` (Round-2 `reduced_mirror` pattern with `inv_inv`).

### C3 — the comparison theorem
| Item | Theorem | Notes |
|---|---|---|
| C3a | `length_eq_of_evalM_eq` | Compare `re` of the (0,0) entries of C2c's scalars; `(9:R2)^ℓ` has `re = 9^ℓ` and `im = 0` (push through `Int.cast`); conclude in ℕ/ℤ. |
| C3b | `reduced_invRev_append` | The junction lemma; `(invRev (c :: τ)).getLast? = some c.inv` is the key private helper. Chain-append criterion with the established `Chain'`/`IsChain` transport. |
| C3c | `genM_cancel` | Left-multiply by `(genM c)ᵀ`; C2b; entrywise 9-cancellation over ℤ[√2] via `Zsqrtd.ext` and ℤ. |
| **C3d** | `evalM_inj` | **Substantial item.** Strong induction with an explicit length bound (house pattern). Full route in the docstring and the design note above. The head of ω for the final `swierczkowski_free` application: destructure `invRev (c :: τ₁)` as a cons (nonempty since length = τ₁.length + 1); `List.cons_append` re-associates ω into the `e :: rest` shape the Round-2 statement takes. |

### C4, C5 — injectivity, specialized and generic
`qW_inj_pm` (assemble C1c, C1e, C3d). `qmap_hW` (private multiplicative/unital kit for `qmap`, then induction). `hWgen_inj_pm` — **the paper's Theorem 6.1**: specialize by `MvPolynomial.eval₂Hom (Int.castRingHom R2) ![Zsqrtd.sqrtd, 1, Zsqrtd.sqrtd, 1, 0]`, transport by C5a (with `qmap φ (-p) = -(qmap φ p)` in the kit), finish by C4. If `MvPolynomial` elaboration demands `noncomputable` markers beyond those provided, add them; the statements are final.

### D — the classification (paper Theorem 6.2)
| Item | Theorem | Notes |
|---|---|---|
| D0 | `quat_eq_iff_triple` | `QuaternionAlgebra.ext`; the triple-language bridge. |
| **D1** | `sign_classification` | Backward: trivial / third-alternative-by-`rfl`. Forward: each of the four alternatives is an instance of C5b, the ι_β ones against `σ.map Letter.ib` (reduced by Round 2's `reduced_ibMap`); translate `σ' = σ.map Letter.ib` conclusions using `ib_ib` (Round 2) and `List.map_map`. Note the hypotheses `IsSym` are not needed by the proof of the forward direction (C5b needs only reducedness) — they are part of the statement because that is the paper's Theorem 6.2 setting; do not remove them. |
| D2 | `ibMap_ne_self` | Round 2's `bisection_exists` produces the β-middle; `counts_encode` gives `betaCount σ ≥ 1`; a word equal to its own ι_β-image has no β-letters (`List.map` fixed-point analysis or a `countP` argument: `betaCount (σ.map ib)` counts the same letters, but the *middle letter itself* flips — simplest is to extract a β-letter from `betaCount σ ≥ 1` via `List.countP_pos` and contradict pointwise fixedness from `List.map_eq_self`-style reasoning). |

---

## After this round

Round 3 completes the planned mathematical formalization: with it, the paper's Theorems 3.2, 6.1, 6.2 (both the classification and the count), Propositions 4.1, the $[2,3,3]$ obstruction, and Świerczkowski's theorem are all machine-checked. No Round 4 is currently planned; the remaining paper-level items (rank-3 freeness, fine-equivalence exactness for even n, the Pfister half of Proposition 4.3(ii)) are open mathematics or deliberate citations, not formalization debt.
