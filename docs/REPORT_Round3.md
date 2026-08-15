# Report — Three Squares, Round 3

**Deliverable.** `Round3.lean`, completed. All 23 commissioned items (C0a–C0c, C1a–C1e,
C2a–C2e, C3a–C3d, C4, C5a, C5b, D0, D1, D2) are closed. There are no `sorry`s in the
file, no `axiom` declarations, no `@[implemented_by]`, and no `native_decide`.
`Round1.lean` and `Round2.lean` were not modified. `lakefile.toml` gained a `Round3`
library target and the corresponding default target, as instructed.

**Build.** `lake build Round1 Round2 Round3` completes successfully (8031 jobs); the
transcript, including the `#print axioms` audit at the end of `Round3.lean`, is in
`build_round3.log`. No warnings originate in `Round3.lean` (the two `List.Chain'`
deprecation warnings come from the frozen `Round1.lean`, and the two `<;>` linter hints
from the frozen `Round2.lean`).

## §1 Elaboration repair (statements untouched)

As shipped, `Round3.lean` did not parse in the pinned toolchain for one mechanical
reason: the transpose notation `Mᵀ`, used in the statements of C2a–C2d and C3d's route,
is scoped to the `Matrix` namespace, and `Round1.lean`'s `open Matrix` is local to that
file. A single file-level `open Matrix` was added after `open Quaternion`, with a comment
recording that it is an addition. No commissioned definition or statement was altered.

## §2 Per-item status and axioms

Every item below compiles and satisfies the closure criterion (at most `propext`,
`Classical.choice`, `Quot.sound`). The exact `#print axioms` output is reproduced.

| Item | Theorem | Status | `#print axioms` |
|---|---|---|---|
| C0a | `hW_cons` | proved | `propext, Quot.sound` |
| C0b | `evalM_cons` | proved | `propext, Classical.choice, Quot.sound` |
| C0c | `evalM_append` | proved | `propext, Classical.choice, Quot.sound` |
| C1a | `re_conj_pure` | proved | `propext, Quot.sound` |
| C1b | `conjMat_mul` | proved | `propext, Classical.choice, Quot.sound` |
| C1c | `conjMat_neg` | proved | `propext, Quot.sound` |
| C1d | `conjMat_qL` | proved | `propext, Classical.choice, Quot.sound` |
| C1e | `conjMat_qW` | proved | `propext, Classical.choice, Quot.sound` |
| C2a | `genM_transpose` | proved | `propext, Classical.choice, Quot.sound` |
| C2b | `genM_orth` | proved | `propext, Classical.choice, Quot.sound` |
| C2c | `evalM_orth` | proved | `propext, Classical.choice, Quot.sound` |
| C2d | `evalM_invRev` | proved | `propext, Classical.choice, Quot.sound` |
| C2e | `reduced_invRev` | proved | `propext, Classical.choice, Quot.sound` |
| C3a | `length_eq_of_evalM_eq` | proved | `propext, Classical.choice, Quot.sound` |
| C3b | `reduced_invRev_append` | proved | `propext, Classical.choice, Quot.sound` |
| C3c | `genM_cancel` | proved | `propext, Classical.choice, Quot.sound` |
| C3d | `evalM_inj` | proved | `propext, Classical.choice, Quot.sound` |
| C4 | `qW_inj_pm` | proved | `propext, Classical.choice, Quot.sound` |
| C5a | `qmap_hW` | proved | `propext, Classical.choice, Quot.sound` |
| C5b | `hWgen_inj_pm` | proved | `propext, Classical.choice, Quot.sound` |
| D0 | `quat_eq_iff_triple` | proved | `propext, Quot.sound` |
| D1 | `sign_classification` | proved | `propext, Classical.choice, Quot.sound` |
| D2 | `ibMap_ne_self` | proved | `propext, Classical.choice, Quot.sound` |

Nothing was found to be false, and no commissioned statement required amendment.

## §3 Notes on the routes taken

* **C1b (`conjMat_mul`).** The brute-force route of the work order was used: nine entries,
  `Matrix.mul_apply` plus `Fin.sum_univ_three`, quaternion component lemmas, then `ring`.
  Two points mattered for it to elaborate in reasonable time. First, `Matrix.ext` must be
  applied explicitly (`apply Matrix.ext; intro i j`) rather than via `ext i j`: the latter
  descends further into the `Zsqrtd` components of each entry and blows up. Second, after
  `fin_cases` the index literals appear in `⟨k, _⟩` form, so `Fin.zero_eta`, `Fin.mk_one`
  and `Fin.reduceFinMk` must be in the `simp only` set for the `!![…]`/`![…]` lookup lemmas
  to fire; otherwise `ring` sees opaque atoms and fails. No heartbeat raise is needed.
* **C1c (`conjMat_neg`).** Reduced to the single quaternion identity
  `(-q) v (star (-q)) = q v (star q)`, proved componentwise. Note that `neg_mul`/`mul_neg`
  do not fire on `ℍ[R2]` here, so the componentwise route is the reliable one; the matrix
  statement then follows by `simp only [conjMat, …]` under the binders.
* **C2b/C2c.** `genM_orth` closes entrywise with `√2·√2 = 2` handled by descending to the
  `Zsqrtd` components (`ext <;> simp`). `evalM_orth` is the stated induction with
  `Matrix.smul_mul`/`Matrix.mul_smul` and `smul_smul` bookkeeping.
* **C3a.** The (0,0) entries of C2c's scalars give `(9 : R2)^ℓ₁ = (9 : R2)^ℓ₂`; this is
  pushed through `Int.cast`, the `re`-component is taken with `Zsqrtd.re_intCast`, and the
  conclusion is `Nat.pow_right_injective` after `exact_mod_cast`.
* **C3c.** The scalar `9` is cancelled by a private lemma `nine_smul_cancel`, which works
  entrywise and then componentwise over ℤ (`Zsqrtd.ext` plus linear arithmetic). No
  integral-domain instance on `Zsqrtd 2` is required.
* **C3d.** Exactly the commissioned route, with a private length-bounded auxiliary
  `evalM_inj_aux` (house pattern). Equal heads strip by C0b/C3c; for distinct heads the
  word `ω := invRev σ₁ ++ σ₂` is reduced by C3b, its matrix is `(3 : R2)^(ω.length) • 1`
  after rewriting `9 = 3²` and `ω.length = 2·ℓ₁` (C3a), and `ω` is destructured as a cons
  by case analysis on the append (nonempty because `σ₂` is). Round 2's
  `swierczkowski_free` then gives the contradiction. No free-group reduction function was
  introduced, as required by the design note.
* **C5.** The private kit is `qmap_one`, `qmap_mul`, `qmap_neg`, `qmap_hL`; `qmap_hW` is
  the induction with C0a. For C5b the specialization is the commissioned
  `MvPolynomial.eval₂Hom (Int.castRingHom R2) ![Zsqrtd.sqrtd, 1, Zsqrtd.sqrtd, 1, 0]`,
  packaged as `specHom`; the bridge `qmap specHom (hWgen σ) = qW σ` closes with
  `norm_num` on the `eval₂Hom` applications followed by `rfl` (the vector lookups at
  indices 2, 3, 4 are definitional).
* **D1.** Each of the four alternatives is a direct instance of C5b, the ι_β ones against
  `σ.map Letter.ib`, whose reducedness is Round 2's `reduced_ibMap`. As anticipated in the
  work order, the `IsSym` hypotheses are not used by the forward direction; they were kept
  because they are part of the paper's Theorem 6.2 setting.
* **D2.** Round 2's `bisection_exists` plus `counts_encode` give `betaCount σ ≥ 1`, hence
  (via `List.countP_pos_iff`) a β-letter of `σ`; a private pointwise-fixedness lemma
  `map_fixed` turns `σ.map Letter.ib = σ` into `Letter.ib x = x` for that letter, which is
  false by case analysis.

## §4 Private auxiliaries added

`conj_neg_aux`, `reduced_isChain3`, `reduced_tail`, `invRev_cons`, `nine_smul_cancel`,
`evalM_inj_aux`, `qmap_one`, `qmap_mul`, `qmap_neg`, `qmap_hL`, `qmap_specHom_hWgen`,
`map_fixed`, and the (public, auxiliary) definition `specHom`. All are additions permitted
by the work order; none alters a commissioned statement.
