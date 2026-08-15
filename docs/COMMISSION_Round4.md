# Aristotle Commission — Three Squares, Round 4

**Project.** Extension round for *Polynomial identities, sums of three squares, and quaternionic (anti-)automorphisms* (D. V. Feldman). Rounds 1–3 are closed (71/71, no sorries, no axiom exceptions). This round formalizes the paper's new Theorem 6.6 — freeness of the rotations through arccos(1/3) about the three coordinate axes, by the rank-one-modulo-3 mesh argument — and the classes-count capstone, the single theorem whose statement is Theorem 6.2's counting sentence.

**Session protocol.** Fresh session; all state is in this tarball. No mid-flight questions. **Report rather than repair anything that fails as stated.** `Round1.lean`, `Round2.lean`, `Round3.lean` are frozen: import and use freely (this round leans on `nodup_allWords`, `reduced_ibMap`, `alphaCount_ibMap`, `betaCount_ibMap`, `ib_ib`, `censusCount_eq`, `ibMap_ne_self`, `sign_classification`, `genM`, `evalM`), modify nothing. All definitions in `Round4.lean` are final; private auxiliaries welcome. Add a `Round4` target to `lakefile.toml`.

**Deliverable.** The tarball returned with `Round4.lean` completed, a build log, and a per-theorem report with `#print axioms` output.

**Closure criterion.** Compiles; `#print axioms` at most `propext`, `Classical.choice`, `Quot.sound`. **No `native_decide` this round** — every decision procedure is small (81 residue pairs, 36 dot products, `Fin 3` searches); plain `decide` must suffice.

**Pre-certification.** All hard-coded data verified before commissioning: the six decompositions `genR g = vecMulVec (colR g) (rowR g) + 3 • defR g` exactly over ℤ[√2]; all thirty legal mesh scalars non-divisible by 3 and all six forbidden junctions divisible; the 81-case residue statement behind primality of 3; unit entries in every `colR`/`rowR`; the `u • outer + 3E` decomposition constructively on all 23436 reduced rank-three words of length ≤ 6; and the orbit counts against `Rc` across the (m,n) table with every orbit of size two. If a statement resists, suspect the route, then report.

---

## Design note (binding)

Module E uses **no quotient rings**. Rank-one-ness modulo 3 is carried by the exact identity E1 over ℤ[√2]; primality of 3 by the componentwise residue lemma E2; the induction E5 stays in ℤ[√2] throughout, with the "modulo 3" always explicit as `+ 3 • E`. Do not introduce `Ideal.Quotient`, `ZMod`-valued matrices, or a reduction homomorphism on matrices; `ZMod 3` may appear only inside the proof of E2b as the target of the componentwise residue computation.

## Module E — rank-three freeness

| Item | Theorem | Notes |
|---|---|---|
| E1 | `genR_decomp` | Six cases × nine entries; `Zsqrtd` components, √2·√2 = 2. |
| E2a | `three_dvd_iff` | Componentwise divisibility; witness `⟨z.re/3, z.im/3⟩` via `Int.ediv`-exactness from the hypothesis. |
| E2b | `three_prime_mul` | Pass components through `Int.cast` to `ZMod 3`; the 81-case core is a single `decide` after generalizing the four residues. |
| E3a | `mesh_unit` | 30 legal junctions; destructure both generators, unfold the dot product, `decide` (after E2a the divisibility is a concrete integer-pair check). |
| E3b | `mesh_inv` | Six sanity cases; certifies sharpness of the criterion. Not used by E6. |
| E4 | `colR_unit`, `rowR_unit` | Decidable `∃` over `Fin 3`; `decide` per generator. |
| **E5** | `evalR_decomp` | **Substantial item.** Reverse recursion (`List.reverseRecOn`); outer-product product rule `vecMulVec u v * vecMulVec u' v' = (v ⬝ᵥ u') • vecMulVec u v'` (prove privately if absent from Mathlib); junction legality from `Chain'` append facts; new unit via `mesh_unit` + `three_prime_mul`. Watch the `getLast` positional bookkeeping across the append. |
| **E6** | `rank3_free` | **Main theorem** (paper Thm 6.6). Entrywise divisibility of `u • vecMulVec (colR g) (rowR l)` by 3 at the E4 indices; `three_prime_mul` twice; contradiction with `¬ 3 ∣ u`. Note `((3)^n • 1 − 3 • E)` is `3 • ((3)^(n−1) • 1 − E)` for n ≥ 1. |
| E7 | `genR_emb`, `swierczkowski_free'` | Cross-validation: Round 2's theorem re-derived from E6. Transport of `Reduced` through the injective, inv-commuting embedding; `List.map_map`. The ledger then holds two independent proofs of the pair's freeness. |

## Module F — the classes-count capstone

| Item | Theorem | Notes |
|---|---|---|
| F0 | `mem_SFin`, `SFin_card` | `List.mem_toFinset`, `mem_allWords`, Bool/Prop bridging; nodup via `nodup_allWords` + `List.Nodup.filter`, then `List.toFinset_card_of_nodup`. |
| F1 | `isSym_ibMap` | Kernel: `(c.ib).ia = (c.ia).ib` by cases; then `map_map`/`map_reverse`. |
| F2 | `ibMap_mem_SFin` | F0a + F1 + Round 2 lemmas. |
| F3 | `orbit_card`, `orbit_eq_of_mem` | Round 3's `ibMap_ne_self` (nonemptiness from `betaCount = n ≥ 1`: a word with a positive count is nonempty); `Finset.card_pair`; double-image via `ib_ib`. |
| **F4** | `card_SFin_eq_two_mul` | Partition into orbits: `Finset.card_biUnion` over the image with pairwise disjointness from F3b; every element lies in its own orbit; orbits stay inside by F2. |
| **F5** | `numClasses_eq` | **Capstone** (paper Thm 6.2, counting sentence). F0b + F4 + Round 2's `censusCount_eq`; cancel 2 with `Nat.eq_of_mul_eq_mul_left`. |
| F6 | `orbit_eq_iff_sign` | The semantics bridge to Round 3's `sign_classification`; both directions short. This theorem entitles `numClasses` to its name. |

---

## After this round

Round 4 completes the expanded formalization program: the paper's Theorems 3.2, 6.1, 6.2 (classification and count), 6.6, Proposition 4.1, the [2,3,3] obstruction, and Świerczkowski's theorem (twice, by independent arguments) will all be machine-checked. The remaining open mathematics — the symmetric-word Conjecture and the Pfister half of Proposition 4.3(ii) — is deliberately outside the ledger. The publication pipeline follows.
