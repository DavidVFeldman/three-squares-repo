# Report — Three Squares, Round 2

`Round2.lean` is complete: **all 26 commissioned theorems are proved**, the file
compiles with no `sorry`, no added axioms, no `axiom` declarations and no
`native_decide`. `Round1.lean` was **not modified** (only imported); the
`lakefile.toml` gained a `Round2` library target so that the new file is built
by `lake build`. Nothing was found to be false, and no commissioned definition
or statement was altered.

The full build transcript, including the `#print axioms` audit at the end of
`Round2.lean`, is in `build_round2.log`.

## 1. Status per theorem

Every theorem below: **proved**. The axiom column is the `#print axioms`
output; `p` = `propext`, `Q` = `Quot.sound`, `C` = `Classical.choice`.
No theorem shows `Lean.ofReduceBool`.

| Item | Theorem | Status | Axioms |
|---|---|---|---|
| A0a | `mem_allWords` | proved | p, C, Q |
| A0b | `nodup_allWords` | proved | p, Q |
| A1a | `ia_ia`, `ib_ib`, `inv_inv`, `ia_inv`, `ib_inv` | proved | none |
| A1b | `reduced_mirror` | proved | p, C, Q |
| A1c | `alphaCount_mirror`, `betaCount_mirror` | proved | p, Q |
| A1c | `alphaCount_ibMap`, `betaCount_ibMap` | proved | p, Q |
| A1c | `reduced_ibMap` | proved | p, C, Q |
| A2a | `isSym_encode` | proved | p, Q |
| A2b | `reduced_encode` | proved | p, C, Q |
| A2c | `counts_encode` | proved | p, C, Q |
| A2d | `bisection_exists` | proved | p, C, Q |
| A2e | `encode_inj` | proved | p, Q |
| A3a | `nCount_partition` | proved | p, C, Q |
| A3b | `eCount_symm_alpha`, `eCount_symm_beta` | proved | p, C, Q |
| A3c | `eCount_peel_a`, `eCount_peel_b` | proved | p, C, Q |
| A3d | `pCount_eq` | proved | p, C, Q |
| A3e | `pCount_eq_Rc` | proved | p, C, Q |
| A4a | `pbCount_eq_pCount` | proved | p, C, Q |
| A4b | `censusCount_eq` | proved | p, C, Q |
| A4c | `census_2_3`, `census_1_5` | proved | p, Q |
| B1a | `inv_start` | proved | p, C, Q |
| B1b | `inv_step` | proved | p, C, Q |
| B2 | `core` | proved | p, C, Q |
| B3a | `vecMul_genM` | proved | p, C, Q |
| B3b | `vecMul_evalM` | proved | p, C, Q |
| B4 | `swierczkowski_free` | proved | p, C, Q |

### A4c: `decide` vs `native_decide`

**Plain kernel `decide` was used for both spot-checks; `native_decide` was not
needed**, so neither theorem depends on `Lean.ofReduceBool`.

One wrinkle worth recording: `Rc` is compiled by well-founded recursion in the
pinned toolchain and therefore does *not* reduce in the kernel, so
`decide` cannot evaluate the right-hand side `2 * Rc 2 1`. Each spot-check
therefore first rewrites the `Rc`-value through the Round-1 closed forms
(`Rc_two`, `Rc_one`) to a numeral, and then evaluates the 4⁷ = 16384-word
census by `decide` under `set_option maxRecDepth 100000`. The left-hand side —
the actual enumeration — is thus still checked by the kernel.

## 2. Route taken, per module

### Module A

Auxiliary infrastructure (all `private`, added, nothing commissioned changed):
the counts `eCount`/`nCount`/`pCount`/`pbCount`/`censusCount` are lengths of
filtered enumerations, i.e. `List.countP` over `allWords`, and three moves
suffice.

* `perm_map_allWords` — a letterwise involution permutes `allWords ℓ`
  (nodup + same membership, via `List.perm_ext_iff_of_nodup`). This drives
  A3b (`f = Letter.inv`) and A4a (`f = Letter.ib`) through the single
  transport lemma `count_transport`.
* `perm_append_allWords` — `w ↦ w ++ [c]` is a bijection from `allWords n`
  onto the words of `allWords (n+1)` ending in `c`. With
  `reduced_append_letter` (`Reduced (w ++ [c]) ↔ Reduced w ∧ w.getLast? ≠ c⁻¹`)
  this gives the peeling recurrences A3c-a/b directly, without ℕ-subtraction.
* `countP_last_partition` — the five-way partition of a count by the value of
  `getLast?`, plus the boolean bookkeeping lemmas `and_not_last*` for the
  "does not end in `e`" predicates. A3a, A3d and the two auxiliary counts
  `count_not_A`, `count_not_B` are immediate instances; the `getLast? = none`
  term is `none_term` (only the empty word, only at (0,0)).

**A2d** (`bisection_exists`) is *not* proved by the positional-symmetry route
in the docstring; it uses the Round-1 strip lemma `isSym_strip` instead, by
induction on a length bound. Stripping `σ = c :: (σ' ++ [c.ia])` with `σ'`
symmetric, the induction hypothesis gives `σ' = encode pos p w` and one checks
`σ = encode pos p (c :: w)` by associativity, since
`(c :: w).reverse.map ι_α = (w.reverse.map ι_α) ++ [c.ia]`. Reducedness of
`c :: w` is inherited from `σ` (`reduced_cons`, `reduced_append`), and the
junction condition on `(c :: w).getLast?` is the induction hypothesis when
`w ≠ []`, and reducedness of `σ` at the `c`/middle junction when `w = []`.
The base cases are the single ι_α-fixed letter (p = 1) and `σ = [c, c.ia]`,
where reducedness forces `c` to be a β-letter (p = 2).

**A3e** (`pCount_eq_Rc`) is the strong induction described in the order, with
an explicit bound (`pCount_eq_Rc_aux`). After A3d and the peelings, each of the
four `Rc`-clauses is ℕ-linear and closed by `omega`; the identity that makes it
work is `eCount .b m (k+1) = pCount m k`. Two extra vanishing facts are needed
and proved (`eCount_alpha_zero`, `eCount_beta_zero`: a word of α-count 0 cannot
end in an α-letter, likewise for β). Bases `pCount 0 0 = 1` and
`pCount 1 0 = 2` are by `decide`.

**A4b** (`censusCount_eq`) transports cardinalities as a single list
permutation rather than through `Finset`: with `k = (n-1)/2` and
`p = if n odd then 1 else 2` (so `n = 2k + p`),

```
(Lt.map (encode true p) ++ Lf.map (encode false p)) ~ (allWords (2m+n)).filter (census predicate)
```

where `Lt`, `Lf` are the filtered lists whose lengths are *definitionally*
`pCount m k` and `pbCount m k`. Nodup on the left is A2e (injectivity of
`encode` in `w`, and disjointness of the two middle signs); membership in both
directions is A2a–A2c one way and A2d the other, with the parity argument
`2·betaCount w + p' = 2k + p ⟹ p' = p ∧ betaCount w = k`. Concluding with A4a
and A3e gives `2 * Rc m k`.

### Module B

Exactly the commissioned design. `inv_start` and `inv_step` are `omega` after
destructuring (`omega` handles the literal-modulus divisibilities); `core` is a
fold induction through a private accumulator lemma `core_aux`; `vecMul_genM` is
four `fin_cases`/`Zsqrtd`-component computations; `vecMul_evalM` is
`List.prod_cons` + `Matrix.vecMul_vecMul`.

In **B4** the final step avoids needing an integral-domain instance for
`Zsqrtd 2`: comparing index 2 gives `√2 · (d₃ : ℤ[√2]) = 0`, and taking the
`im`-component of that equation yields `d₃ = 0` outright, contradicting B2 via
`dvd_zero`.

## 3. Deviations, repairs, notes

* **No commissioned statement or definition was modified**, and nothing was
  repaired in `Round1.lean`.
* One `private` restatement, `reduced_isChain : Reduced σ ↔ List.IsChain _ σ`
  (definitionally `Iff.rfl`), is used throughout: `List.Chain'` is a deprecated
  alias for `List.IsChain` in the pinned Mathlib and the rewriting API
  (`isChain_append`, `isChain_map`, `isChain_reverse`, …) is stated for the
  latter only.
* `lakefile.toml` now lists a `Round2` library target (and `Round2` among the
  default targets). This was necessary for `lake build` to build the new file;
  no other project file was touched.
* Remaining build warnings: the two `List.Chain'` deprecation notices from
  `Round1.lean` (which is frozen), and two cosmetic
  `Used tac1 <;> tac2 where (tac1; tac2) would suffice` hints in `Round2.lean`.
  The hinted rewrite was tried and does *not* elaborate (in some branches the
  earlier tactic already closes the goal), so the `<;>` forms were kept.
