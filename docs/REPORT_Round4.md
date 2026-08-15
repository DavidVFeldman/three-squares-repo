# Report — Three Squares, Round 4

**Deliverable.** `Round4.lean`, completed. All 20 commissioned items (E1, E2a, E2b, E3a,
E3b, E4 ×2, E5, E6, E7a, E7b, F0a, F0b, F1, F2, F3a, F3b, F4, F5, F6) are closed. There
are no `sorry`s in the file, no `axiom` declarations, no `@[implemented_by]`, and no
`native_decide`. No commissioned definition or statement was altered, and nothing was
found to be false. `Round1.lean`, `Round2.lean`, `Round3.lean` were not modified
(verified by `git diff`). `lakefile.toml` gained a `Round4` library target and the
corresponding default target, as instructed.

**Build.** `lake build Round1 Round2 Round3 Round4` completes successfully (8033 jobs);
the transcript, including the `#print axioms` audit at the end of `Round4.lean`, is in
`build_round4.log`.

**Design note compliance (Module E).** No quotient rings are used anywhere. Rank-one-ness
modulo 3 is carried throughout by the exact identity E1 over ℤ[√2]; the induction E5 stays
in ℤ[√2], with the modulus always explicit as `+ (3 : R2) • E`. `ZMod 3` occurs at exactly
one place — inside the proof of E2b, as the target of the componentwise residue
computation (the private lemma `zmod3_core`, closed by a plain `decide` over its 81
cases). There is no `Ideal.Quotient`, no `ZMod`-valued matrix, and no reduction
homomorphism on matrices.

## §1 Per-item status and axioms

Every item below compiles and satisfies the closure criterion (at most `propext`,
`Classical.choice`, `Quot.sound`). The exact `#print axioms` output is reproduced.

| Item | Theorem | Status | `#print axioms` |
|---|---|---|---|
| E1 | `genR_decomp` | proved | `propext, Classical.choice, Quot.sound` |
| E2a | `three_dvd_iff` | proved | `propext, Classical.choice, Quot.sound` |
| E2b | `three_prime_mul` | proved | `propext, Classical.choice, Quot.sound` |
| E3a | `mesh_unit` | proved | `propext, Classical.choice, Quot.sound` |
| E3b | `mesh_inv` | proved | `propext, Classical.choice, Quot.sound` |
| E4 | `colR_unit` | proved | `propext, Classical.choice, Quot.sound` |
| E4 | `rowR_unit` | proved | `propext, Classical.choice, Quot.sound` |
| E5 | `evalR_decomp` | proved | `propext, Classical.choice, Quot.sound` |
| E6 | `rank3_free` | proved | `propext, Classical.choice, Quot.sound` |
| E7a | `genR_emb` | proved | `propext, Quot.sound` |
| E7b | `swierczkowski_free'` | proved | `propext, Classical.choice, Quot.sound` |
| F0a | `mem_SFin` | proved | `propext, Classical.choice, Quot.sound` |
| F0b | `SFin_card` | proved | `propext, Classical.choice, Quot.sound` |
| F1 | `isSym_ibMap` | proved | `propext, Quot.sound` |
| F2 | `ibMap_mem_SFin` | proved | `propext, Classical.choice, Quot.sound` |
| F3a | `orbit_card` | proved | `propext, Classical.choice, Quot.sound` |
| F3b | `orbit_eq_of_mem` | proved | `propext, Classical.choice, Quot.sound` |
| F4 | `card_SFin_eq_two_mul` | proved | `propext, Classical.choice, Quot.sound` |
| F5 | `numClasses_eq` | proved | `propext, Classical.choice, Quot.sound` |
| F6 | `orbit_eq_iff_sign` | proved | `propext, Classical.choice, Quot.sound` |

No item required `native_decide`; every decision procedure (the 81 residue pairs of E2b,
the 36 mesh dot products of E3a/E3b, the `Fin 3` searches of E4, the entrywise checks of
E1) is closed by plain kernel `decide` or by `simp`-normalisation to a decidable numeral
statement.

## §2 Routes taken

**E1.** `cases g`, then `Matrix.ext` and `fin_cases` on both indices; each of the 54
entries reduces by `simp` on `genR`/`colR`/`rowR`/`defR`/`vecMulVec` and, where a product
`(±2√2)(∓2√2)` occurs, by a kernel `decide` on the resulting `Zsqrtd` equation
(√2·√2 = 2).

**E2a.** Forward: `rintro ⟨w, rfl⟩` and read off `Zsqrtd.re_mul`/`Zsqrtd.im_mul` with
`(3 : R2) = ⟨3, 0⟩`. Backward: the witness `⟨p, q⟩` built from the two integer witnesses.

**E2b.** Both hypotheses and the goal are pushed through E2a to statements about the
integer components, then those components are cast into `ZMod 3` via
`ZMod.intCast_zmod_eq_zero_iff_dvd`. The arithmetic core is the private lemma
`zmod3_core`, a single `decide` over the 81 residue quadruples, applied to
`(x*y).re = x.re*y.re + 2*x.im*y.im` and `(x*y).im = x.re*y.im + x.im*y.re`.

**E3a/E3b.** `three_dvd_iff` first; then `cases g <;> cases h` with the junction
hypothesis reverted, and `simp` on `rowR`, `colR`, `Rot.inv`, `dotProduct`,
`Fin.sum_univ_three`. The thirty legal meshes evaluate to ±1, ±7, ±2√2 or ±4√2-type
values with a component prime to 3; the six forbidden junctions evaluate to ±9.

**E4.** One explicit witness index per generator (index 1 for the `a`/`A` axis, index 0
otherwise — the slot carrying the entry 1), discharged by `three_dvd_iff` and `simp`.

**E5.** Stated exactly as commissioned; proved from a private auxiliary
`evalR_decomp_aux` that carries the last letter as an explicit parameter constrained by
`(g :: τ).getLast? = some l`, so that the reverse recursion is free of dependent-proof
bookkeeping; the commissioned form follows by
`List.getLast?_eq_getLast_of_ne_nil`. The recursion is `List.reverseRecOn` on `τ`:

* base `τ = []`: E1 with `u = 1` and `E = defR g` (using `¬ (3 : R2) ∣ 1` from E2a);
* step `τ = τ' ++ [k]`: re-associate to `(g :: τ') ++ [k]`, split the chain with
  `List.isChain_append` to get both reducedness of the prefix and the junction
  `k ≠ l'.inv` at the prefix's last letter `l'`, apply the induction hypothesis and E1,
  and collect with the private outer-product product rule
  `outer_mul_outer : vecMulVec c v * vecMulVec w x = (v ⬝ᵥ w) • vecMulVec c x`
  (derived from Mathlib's `Matrix.vecMulVec_mul_vecMulVec`). The new scalar
  `u * (rowR l' ⬝ᵥ colR k)` is prime to 3 by `mesh_unit` and `three_prime_mul`; the
  remaining terms are collected into the new `E` and the scalar bookkeeping is closed by
  `module`.

**E6.** From E5, the entry at the indices supplied by `colR_unit g` and
`rowR_unit ((g :: τ).getLast _)` gives
`u * colR g i * rowR l j + 3 * E i j = 3^(τ.length + 1) * (1 : Matrix _ _ R2) i j`,
so `3 ∣ u * colR g i * rowR l j`; two applications of `three_prime_mul` contradict this.
The `n ≥ 1` bookkeeping is `pow_succ` on `(g :: τ).length = τ.length + 1`.

**E7.** `genR_emb` is `cases c <;> rfl`. For `swierczkowski_free'`, reducedness is
transported through `List.isChain_map` using injectivity of `emb` and
`emb d.inv = (emb d).inv`, the evaluation through `List.map_map` and
`List.map_congr_left` with E7a, and the exponent through `List.length_map`; E6 then
applies. This is a second, independent machine-checked proof of freeness for the pair
(Round 2's `swierczkowski_free` proves the same statement by the mod-9 integer-triple
invariant).

**F0a.** The only non-formal point is the missing length condition: it is supplied by the
private lemma `counts_add_length : alphaCount σ + betaCount σ = σ.length` together with
`mem_allWords`.

**F0b.** `List.toFinset_card_of_nodup` applied to `(nodup_allWords _).filter _`; the
filtered list is literally the list whose length is `censusCount m n`, so no rewriting of
the filter predicate is needed.

**F1.** The kernel is `(c.ib).ia = (c.ia).ib` by cases; then
`(σ.map ib).reverse.map ia = (σ.reverse.map ia).map ib` by `List.map_reverse`/`List.map_map`,
and the equivalence follows from injectivity of `List.map Letter.ib`.

**F3a.** Nonemptiness of `σ` comes from `betaCount σ = n ≥ 1`; then Round 3's
`ibMap_ne_self` and `Finset.card_pair`.

**F4.** `((SFin m n).image orbit).biUnion id = SFin m n` (members lie in their own orbits;
orbits of members stay inside by F2), pairwise disjointness from F3b, and each orbit of
card 2 by F3a; `Finset.card_biUnion` and `Finset.sum_const` finish.

**F5.** `Nat.eq_of_mul_eq_mul_left` on `2 * numClasses m n = 2 * Rc m ((n-1)/2)`, obtained
from F4, F0b and Round 2's `censusCount_eq`.

**F6.** Reduces to `orbit σ' = orbit σ ↔ (σ' = σ ∨ σ' = σ.map ib)` after rewriting with
Round 3's `sign_classification` (whose hypotheses come from F0a); forward by
`σ' ∈ orbit σ' = orbit σ`, backward by `rfl` and F3b.

## §3 Residual warnings

Two warnings originate in `Round4.lean`, both cosmetic and both documented here:

1. `Round4.lean:56` — `List.Chain'` is a deprecated alias for `List.IsChain` in the pinned
   Mathlib. The occurrence is inside the commissioned definition `Reduced3`, which is
   final, so the warning cannot be removed without editing a commissioned definition. (The
   decidability instance for `Reduced3` elaborates because the frozen `Round1.lean` already
   supplies `decidableListChain'`.) The same warning occurs for `Reduced` in `Round1.lean`.
2. `Round4.lean:109` — a linter hint suggesting `(tac1; tac2)` in place of `tac1 <;> tac2`
   inside the E1 proof. The suggested rewrite does *not* elaborate (in several of the 54
   entry branches the `simp` already closes the goal, so the sequenced `decide` reports
   "no goals"), so the `<;>` form was kept. This matches the situation recorded for
   `Round2.lean`.
