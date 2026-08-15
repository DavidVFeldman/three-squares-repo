# Aristotle Commission — Three Squares, Round 2

**Project.** Continuation of Round 1 (closed 22/22, no sorries, no axiom exceptions). This round delivers the census bijection and the Świerczkowski freeness theorem — the two pillars on which Round 3 (injectivity of the word evaluation) will stand.

**Session protocol.** Fresh session; all state is in this tarball. No mid-flight questions. **Report rather than repair anything that fails as stated.** `Round1.lean` is the closed Round-1 artifact and is **frozen**: import it, use anything in it, modify nothing in it — including its repair instances and private lemmas. All definitions in `Round2.lean` are final; auxiliary private lemmas may be added freely.

**Deliverable.** The tarball returned with `Round2.lean` completed, a build log, and a report listing, per theorem: status (proved / failed-as-stated / blocked), the `#print axioms` output, and (for A4c) whether `decide` or `native_decide` was used.

**Closure criterion.** Compiles, and `#print axioms` shows at most `propext`, `Classical.choice`, `Quot.sound`. Exception: A4c only may additionally show `Lean.ofReduceBool`. No `sorry` in closed items.

**Pre-certification.** Every commissioned statement was verified numerically before this order was written: the A3 recurrence system for all m, k ≤ 5; the bisection roundtrip on all 160 symmetric reduced words of length ≤ 8; the final census identity across the (m,n) table; the invariant B1a/B1b exhaustively over residues mod 9; the core B2 on all 39364 reduced words of length ≤ 9; the bridge B3a on a systematic grid; and the freeness B4 on all 13120 reduced words of length ≤ 8 by exact ℤ[√2] matrix arithmetic. If a statement resists, suspect the route, then report; the statements themselves are not in doubt.

---

## Module A — Census bijection: `censusCount m n = 2 * Rc m ((n-1)/2)`

Structure: enumeration infrastructure (A0), symmetry kit (A1), the bisection `σ = w ++ β^{±p} ++ ι_α(ρ(w))` as an explicit encode with existence and injectivity (A2), the last-letter-refined counts with peeling recurrences (A3), assembly (A4).

| Item | Theorems | Notes |
|---|---|---|
| A0 | `mem_allWords`, `nodup_allWords` | Induction on ℓ. Nodup: the four head-cons maps are injective with pairwise disjoint images. |
| A1 | `ia_ia` … `reduced_ibMap` | Letter kit by `cases <;> rfl`; word lemmas by `List.chain'_reverse`, `List.chain'_map`, `List.countP_map/reverse`. |
| A2a–c | `isSym_encode`, `reduced_encode`, `counts_encode` | Direct computations. For A2b the single hypothesis on `w.getLast?` covers both junctions because ι_α fixes β-letters and preserves the α/β classes. |
| **A2d** | `bisection_exists` | **Substantial item 1.** Detailed route in the docstring: positional symmetry `σ.get (ℓ-1-i) = (σ.get i).ia`, middle-letter analysis by parity and reducedness, `w := σ.take ((ℓ-p)/2)`, equality by `List.ext_get` over three index ranges. A prefix of a reduced word is reduced (private helper). |
| A2e | `encode_inj` | Lengths give p (parity), the middle letter gives pos, takes give w. |
| A3a,d | `nCount_partition`, `pCount_eq` | Partition of a filtered list by the value of `getLast?`; the empty word contributes iff (m,k) = (0,0). |
| A3b | `eCount_symm_alpha/beta` | Bijection `w ↦ w.map Letter.inv`; note `(w.map f).getLast? = (w.getLast?).map f`. |
| A3c | `eCount_peel_a/b` | Bijection `w' ↦ w' ++ [c]` between the class ending in `c` and prefixes not ending in `c.inv`, the latter written additively via the partition (no ℕ-subtraction). |
| **A3e** | `pCount_eq_Rc` | **Substantial item 2.** Strong induction on m + k against the four clauses of `Rc`; after rewriting with A3a–d the goal is ℕ-linear (`omega`). Bases `pCount 0 0 = 1`, `pCount 1 0 = 2` by `decide`. |
| A4a | `pbCount_eq_pCount` | ι_β bijection, same pattern as A3b. |
| **A4b** | `censusCount_eq` | **Main theorem.** Disjoint union over the middle sign; cardinality transport through encode via A2a–A2e (pass between filtered-list lengths and `Finset` cards using `nodup_allWords`); conclude with A4a, A3e. Note `(n-p)/2 = (n-1)/2` in ℕ-division for both parities of n with p = 1 resp. 2 — a small arithmetic lemma worth isolating. |
| A4c | `census_2_3`, `census_1_5` | **NATIVE permitted** (4⁷ = 16384 each). Independent spot-checks; try `decide` with raised `maxRecDepth` first. |

## Module B — Świerczkowski freeness, arccos(1/3) about e₁ and e₂

The design differs from Świerczkowski's 1958 paper in one respect, deliberately: his normalization "assume the word begins with A" (conjugation by a power of A) is replaced by a per-initial-letter starting row (`startVec`), after which a single left-to-right invariant handles every reduced word. The invariant, its base cases, and all twelve transitions are exactly as certified; the generators are the scaled conjugation actions of √2 + i and √2 + j, which is the form Round 3 consumes.

| Item | Theorems | Notes |
|---|---|---|
| B1a | `inv_start` | Four concrete integer checks. |
| B1b | `inv_step` | Twelve transitions; destructure, unfold, `omega` (literal-modulus divisibility is in scope for `omega`). |
| B2 | `core` | Fold induction with the accumulator invariant; skeleton in the docstring. |
| B3a | `vecMul_genM` | Four cases; `fin_cases` the index; `Zsqrtd` arithmetic (√2·√2 = 2), close by `ring` after pushing to components if needed. |
| B3b | `vecMul_evalM` | `List.prod_cons` + `Matrix.vecMul_mul`. |
| **B4** | `swierczkowski_free` | **Main theorem.** Apply `vecMul (row (startVec c))` to the supposed equality; compare index 2; `Zsqrtd 2` is an integral domain, `sqrtd ≠ 0`, `Int.cast_injective`; contradict B2 with `dvd_zero`. |

---

## Out of scope (Round 3 preview)

Injectivity of the Round-1 evaluation `hW` on reduced words: the quaternion-to-rotation bridge at the specialization (√2, 1, √2, 1, 0), the identification of the conjugation matrices with `genM` up to scaling, and free-group normal-form multiplication to compare distinct reduced words. Round 3 will consume B4 in exactly the form stated here. Nothing in Round 2 depends on anything out of scope.
