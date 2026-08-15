# Round 1 — Delivery Report

**File:** `Round1.lean` (single module, default target `Round1`).
**Build:** `lake build Round1` — completes successfully; log in `build.log`.
**Sorries:** none. **Axioms added:** none. **`native_decide`:** not used anywhere.

All 22 commissioned items are **closed**. No commissioned definition or theorem
statement was altered.

---

## 1. Two elaboration repairs (statements untouched)

As shipped, the file did not elaborate in the pinned toolchain
(Lean 4.28.0 / Mathlib `v4.28.0`). Two failures were mechanical, and both were
repaired by *adding* auxiliary declarations, leaving every commissioned
definition and statement byte-for-byte as commissioned.

1. **`Decidable (Reduced σ)` (the instance right after `def Reduced`).**
   In the current Mathlib `List.Chain'` is a deprecated alias for
   `List.IsChain`, and the decidability instance is registered only for
   `IsChain`; `infer_instance` cannot see through the alias, so the shipped
   instance failed with an instance-synthesis error.
   *Repair:* the instance `ThreeSquares.decidableListChain'` is added before
   `Reduced`, defined as `decidable_of_iff (List.IsChain r l) Iff.rfl` — i.e.
   literally the `IsChain` instance, transported along a definitional `Iff.rfl`.
   The shipped instance then elaborates unchanged.
   (The two remaining build warnings are the deprecation notices for
   `List.Chain'`; they come from the commissioned `def Reduced` and from the
   repair instance that must mention `Chain'` to be found. They cannot be
   removed without editing `def Reduced`.)

2. **M1.9a `i_mul_hW`.** `Quaternion R` is a plain, non-reducible definition
   unfolding to `QuaternionAlgebra R (-1) 0 (-1)`, and the
   anonymous-constructor notation `(⟨0,1,0,0⟩ : ℍ[R])` elaborates at the
   *unfolded* type. Type-class resolution does not unfold `Quaternion`, so the
   products in the statement produced
   `failed to synthesize HMul ℍ[R,-1,-1] ℍ[R] ?m`.
   *Repair:* the two `local instance`s `hmulQuatAlgLeft`/`hmulQuatAlgRight`,
   each defined as `instHMul`. They are the ordinary quaternion
   multiplication (definitionally `instHMul` for `Mul ℍ[R]`), so the meaning of
   the commissioned statement is unchanged; they only let it elaborate. The
   proof goes through an auxiliary `qI R : ℍ[R] := ⟨0,1,0,0⟩` and the
   commissioned statement is discharged by `i_mul_hW' t u x y z σ`
   (definitional match).

No other deviation from the shipped file, apart from the added private
auxiliary lemmas listed below, one `set_option maxRecDepth 10000` before the
census block, and an `#print axioms` audit block at the end of the file.

---

## 2. Per-theorem status and axioms

Allowed set: `propext`, `Classical.choice`, `Quot.sound`.

| Item | Theorem | Status | `#print axioms` |
|---|---|---|---|
| M1.1a | `theta_mul` | proved | `[propext, Quot.sound]` |
| M1.1b | `theta_theta` | proved | `[propext, Quot.sound]` |
| M1.2a | `theta_hL` | proved | `[propext, Quot.sound]` |
| M1.2b | `theta_hW` | proved | `[propext, Quot.sound]` |
| M1.3 | `isSym_strip` | proved | `[propext, Quot.sound]` |
| M1.4 | `imI_conj` | proved | `[propext, Quot.sound]` |
| M1.5 | `imI_hW_eq_zero` | proved | `[propext, Classical.choice, Quot.sound]` |
| M1.6 | `alphaCount_even` | proved | `[propext, Classical.choice, Quot.sound]` |
| M1.7a | `normSq_hL_alpha` | proved | `[propext, Quot.sound]` |
| M1.7a | `normSq_hL_beta` | proved | `[propext, Quot.sound]` |
| M1.7b | `normSq_hW` | proved | `[propext, Quot.sound]` |
| M1.8 | `three_squares` | proved | `[propext, Classical.choice, Quot.sound]` |
| M1.9a | `i_mul_hW` | proved | `[propext, Quot.sound]` |
| M1.9b | `hW_ib_components` | proved | `[propext, Quot.sound]` |
| M1.10 | `hW_neg_yz` | proved | `[propext, Quot.sound]` |
| M2.1 | `Rc_zero` | proved | `[propext, Quot.sound]` |
| M2.2 | `Rc_one` | proved | `[propext, Quot.sound]` |
| M2.3 | `Rc_two` | proved | `[propext, Quot.sound]` |
| M2.4 | `census_1_3` | proved | *does not depend on any axioms* |
| M2.5 | `census_2_1` | proved | *does not depend on any axioms* |
| M3.1 | `no_orthogonal_skew` | proved | `[propext, Classical.choice, Quot.sound]` |
| M3.2 | `no_bilinear_233` | proved | `[propext, Classical.choice, Quot.sound]` |

**M2.4 / M2.5: `decide`, not `native_decide`.** Plain kernel `decide` closes
both, once `maxRecDepth` is raised to 10000 (the search spaces are 4⁵ = 1024
words each). Consequently the two census theorems are axiom-free — in
particular `Lean.ofReduceBool` does **not** appear, and the exception granted
in the commission is not used.

---

## 3. Proof notes

* **M1.3 `isSym_strip`.** Case split on `[]`, `[c]`, `c :: d :: t`; in the last
  case the tail is written `L ++ [e]` via `List.eq_nil_or_concat`. Symmetry
  gives `ι_α e = c` (hence `e = c.ia`, using the private `ia_ia`) and, after
  `List.append_cancel_right`, `IsSym L`.
* **M1.5 / M1.6.** Both go through the commissioned strip induction, packaged
  as private auxiliary lemmas `imI_hW_aux` / `alphaCount_aux` that induct on an
  explicit length bound `n` (this is the strong induction on `σ.length`). The
  decomposition step uses the private `hW_strip`:
  `hW (c :: (σ' ++ [c.ia])) = hL c * hW σ' * hL c.ia`. The fixed-point route was
  not used, as instructed.
* **M1.4.** The four polynomial identities close by `simp` with the quaternion
  component lemmas followed by `ring`; no division, valid over any `CommRing`.
* **M1.7.** `Quaternion.normSq_def'` (`normSq a = a.re^2 + a.imI^2 + a.imJ^2 +
  a.imK^2`) is available in Mathlib for a general `CommRing`, so no local
  version was needed. `normSq_hW` is an induction using `map_mul` for the
  multiplicative `normSq`.
* **M1.9b.** Obtained by applying `re`, `imI`, `imJ`, `imK` to M1.9a and
  reading off the four component equations; no ordered-field reasoning is used
  (the base ring is an arbitrary `CommRing`).
* **M3.2.** Exactly the commissioned route. Specializing `(t,u)` to `(1,0)`,
  `(0,1)`, `(1,1)` gives `|A₁v|² = |v|²`, `|A₂v|² = |v|²`, `⟨A₁v,A₂v⟩ = 0`;
  polarizing at `v + w` gives the bilinear forms; evaluating at
  `Pi.single i 1` recovers `A₁ᵀA₁ = 1`, `A₂ᵀA₂ = 1` and
  `A₁ᵀA₂ + A₂ᵀA₁ = 0`. With `B := A₁ᵀA₂` one gets `Bᵀ = -B`, and
  `Bᵀ * B = 1` after converting `A₁ᵀA₁ = 1` into `A₁A₁ᵀ = 1` via
  `mul_eq_one_comm` (Mathlib has renamed `Matrix.mul_eq_one_comm` to the
  root-namespace `mul_eq_one_comm`). M3.1 finishes it. M3.2 is **not** blocked.

## 4. Private auxiliary declarations added

`ia_ia`, `hW_strip`, `imI_hW_aux`, `alphaCount_aux`, `qI`, `i_mul_hL`,
`i_mul_hW'`, `mulVec_pencil`, `sum_bilin_expand`, `sum_mul_comm3`, plus the
two non-private repair items described in §1 (`decidableListChain'`,
`hmulQuatAlgLeft`/`hmulQuatAlgRight`, the latter two `local`).
