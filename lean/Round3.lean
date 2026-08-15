/-
Round 3 — Injectivity and the sign-equivalence classification, for
"Polynomial identities, sums of three squares, and quaternionic (anti-)automorphisms"
(D. V. Feldman, University of New Hampshire).

This file imports Round1.lean and Round2.lean, the CLOSED artifacts of the
previous rounds; both are frozen — import and use freely, modify nothing.
All definitions below are final; every `sorry` is commissioned. If a
statement fails as written, REPORT it and move on — do not repair. Private
auxiliary lemmas may be added freely.

Closure criterion per theorem: compiles, and `#print axioms` shows at most
propext, Classical.choice, Quot.sound. No native_decide exceptions this round.

Every statement below has been certified numerically before commissioning:
the letter bridge exactly, the word bridge on all 1457 reduced words of
length ≤ 6, multiplicativity and sign-kill on random quaternions,
orthogonality and the transpose law through length 6, the distinct-head
concatenation on 9840 reduced pairs, and the classification on all 52
symmetric reduced words of length ≤ 6 at the level of polynomial
quaternions. If a statement resists, suspect the route, then report.

Design note. The comparison theorem C3d deliberately avoids free-group
reduction machinery. Equal lengths come from orthogonality; equal heads
strip by transpose-multiplication and cancellation of 9; and for distinct
heads c ≠ d the concatenation invRev σ₁ ++ σ₂ is automatically reduced
(its junction letters are c.inv then d, legal precisely because d ≠ c) and
nonempty, with matrix exactly the scalar form that Round 2's
`swierczkowski_free` forbids. Do not introduce a general word-reduction
function.
-/
import Round1
import Round2

open Quaternion

-- Auxiliary (added, not commissioned): the transpose notation `Mᵀ` used in the
-- statements of C2–C3 is scoped to the `Matrix` namespace, and Round 1's
-- `open Matrix` is local to that file. Opening it here is required for the
-- commissioned statements to parse; no statement is altered.
open Matrix

namespace ThreeSquares

/-! ### C0: small product laws for the evaluations -/

section C0
variable {R : Type*} [CommRing R]

/-- C0a. One-step law for the quaternionic evaluation. `List.map_cons`,
`List.prod_cons`. -/
theorem hW_cons (t u x y z : R) (c : Letter) (σ : Word) :
    hW t u x y z (c :: σ) = hL t u x y z c * hW t u x y z σ := by
  simp [hW]

/-- C0b. One-step law for the matrix evaluation. -/
theorem evalM_cons (c : Letter) (σ : Word) :
    evalM (c :: σ) = genM c * evalM σ := by
  simp [evalM]

/-- C0c. Concatenation law for the matrix evaluation. `List.map_append`,
`List.prod_append`. -/
theorem evalM_append (σ τ : Word) :
    evalM (σ ++ τ) = evalM σ * evalM τ := by
  simp [evalM]

end C0

/-! ### C1: the quaternion-to-matrix bridge at the specialization

The specialization is (t,u,x,y,z) = (√2, 1, √2, 1, 0) in ℤ[√2], so that the
letters α, β evaluate to √2 + i and √2 + j, each of norm 3. The conjugation
action p ↦ q p (star q) on pure quaternions is matrix-valued and
multiplicative without any inverses; on the letter values it produces
exactly the 3-scaled rotation matrices `genM` of Round 2 — the norm 3
supplies the scaling. -/

/-- The specialized letter values: α ↦ √2 + i, β ↦ √2 + j. -/
def qL (c : Letter) : ℍ[R2] := hL Zsqrtd.sqrtd 1 Zsqrtd.sqrtd 1 0 c

/-- The specialized word evaluation. -/
def qW (σ : Word) : ℍ[R2] := hW Zsqrtd.sqrtd 1 Zsqrtd.sqrtd 1 0 σ

/-- The pure basis i, j, k. -/
def pureBasis : Fin 3 → ℍ[R2] := ![⟨0,1,0,0⟩, ⟨0,0,1,0⟩, ⟨0,0,0,1⟩]

/-- The matrix of the conjugation action p ↦ q p (star q) on the pure part,
in the basis (i, j, k): column j lists the (imI, imJ, imK)-coefficients of
q · (pureBasis j) · star q. -/
def conjMat (q : ℍ[R2]) : Matrix (Fin 3) (Fin 3) R2 :=
  Matrix.of fun i j =>
    ![(q * pureBasis j * star q).imI,
      (q * pureBasis j * star q).imJ,
      (q * pureBasis j * star q).imK] i

/-- C1a. Conjugation preserves purity, over any commutative ring's
quaternions: the real part of q v (star q) vanishes when v is pure.
Destructure and `ring` (the identity q v q̄ + q v̄ q̄ = q (v + v̄) q̄ is
behind it, but direct expansion is simplest). -/
theorem re_conj_pure (q v : ℍ[R2]) (hv : v.re = 0) :
    (q * v * star q).re = 0 := by
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, hv]
  ring

/-- Auxiliary: conjugation is insensitive to the sign of the conjugator. -/
private lemma conj_neg_aux (q v : ℍ[R2]) : (-q) * v * star (-q) = q * v * star q := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp <;> ring

/-- C1b. The conjugation matrix is multiplicative. Route: either decompose
q · pureBasis j · star q over the pure basis using `re_conj_pure` and
linearity of p ↦ q p (star q), or destructure both quaternions and close
each of the nine entries of `Matrix.mul_apply` by `ring` after `simp` with
the component multiplication lemmas. -/
theorem conjMat_mul (p q : ℍ[R2]) :
    conjMat (p * q) = conjMat p * conjMat q := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      conjMat, pureBasis, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
    ring

/-- C1c. The conjugation matrix kills the sign. `ext`; `ring`. -/
theorem conjMat_neg (q : ℍ[R2]) : conjMat (-q) = conjMat q := by
  simp only [conjMat, conj_neg_aux]

/-- C1d. On the specialized letters the conjugation matrix is exactly the
3-scaled generator of Round 2. Four cases; `ext i j; fin_cases i <;>
fin_cases j;` then `Zsqrtd` component arithmetic (√2·√2 = 2), `decide` or
`ring`. -/
theorem conjMat_qL (c : Letter) : conjMat (qL c) = genM c := by
  cases c <;>
  · apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [conjMat, pureBasis, qL, hL, genM] <;>
      ring

/-- C1e. The bridge along words. Induction with C0a, C0b, C1b, C1d; the
base case is conjMat 1 = 1. -/
theorem conjMat_qW (σ : Word) : conjMat (qW σ) = evalM σ := by
  induction σ with
  | nil =>
      have h1 : qW [] = 1 := by simp [qW, hW]
      rw [h1, evalM]
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [conjMat, pureBasis]
  | cons c t ih =>
      have hq : qW (c :: t) = qL c * qW t := by
        simp only [qW, qL, hW_cons]
      rw [hq, conjMat_mul, ih, conjMat_qL, evalM_cons]

/-! ### C2: transposes and orthogonality -/

/-- The formal inverse word: reverse and invert every letter. -/
def invRev (σ : Word) : Word := σ.reverse.map Letter.inv

/-- Auxiliary (added): `Reduced` unfolded to the non-deprecated `List.IsChain`,
so that the `IsChain` rewriting API applies (the Round-2 transport). -/
private lemma reduced_isChain3 (σ : Word) :
    Reduced σ ↔ List.IsChain (fun c d => d ≠ c.inv) σ := Iff.rfl

/-- Auxiliary: the tail of a reduced word is reduced. -/
private lemma reduced_tail {c : Letter} {τ : Word} (h : Reduced (c :: τ)) : Reduced τ :=
  (reduced_isChain3 _).2 (((reduced_isChain3 _).1 h).tail)

/-- Auxiliary: peeling the last letter off a formal inverse. -/
private lemma invRev_cons (c : Letter) (τ : Word) :
    invRev (c :: τ) = invRev τ ++ [c.inv] := by simp [invRev]

/-- C2a. Transposing a generator inverts its letter. Four cases;
`ext i j; fin_cases i <;> fin_cases j <;> rfl` or `decide`. -/
theorem genM_transpose (c : Letter) : (genM c)ᵀ = genM c.inv := by
  cases c <;>
  · apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [genM, Letter.inv]

/-- C2b. The generators are orthogonal after removing the scaling 3:
transposed times itself is 9. Four cases; entry computations with
√2·√2 = 2. -/
theorem genM_orth (c : Letter) :
    (genM c)ᵀ * genM c = (9 : R2) • (1 : Matrix (Fin 3) (Fin 3) R2) := by
  cases c <;>
  · apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [genM, Matrix.mul_apply, Fin.sum_univ_three] <;> ext <;> simp

/-- C2c. Orthogonality along words. Induction on σ with C0b,
`Matrix.transpose_mul`, C2b, and `Matrix.smul_mul`/`mul_smul`
associativity bookkeeping. -/
theorem evalM_orth (σ : Word) :
    (evalM σ)ᵀ * evalM σ
      = ((9 : R2) ^ σ.length) • (1 : Matrix (Fin 3) (Fin 3) R2) := by
  induction σ with
  | nil => simp [evalM]
  | cons c t ih =>
      rw [evalM_cons, Matrix.transpose_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc (genM c)ᵀ, genM_orth, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_smul, ih, List.length_cons, pow_succ, smul_smul]
      ring_nf

/-- C2d. The matrix of the formal inverse is the transpose. Induction:
`invRev (c :: τ) = invRev τ ++ [c.inv]`, then C0c, C2a,
`Matrix.transpose_mul`. -/
theorem evalM_invRev (σ : Word) : evalM (invRev σ) = (evalM σ)ᵀ := by
  induction σ with
  | nil => simp [invRev, evalM]
  | cons c t ih =>
      have h2 : evalM [c.inv] = genM c.inv := by simp [evalM]
      rw [invRev_cons, evalM_append, ih, h2, evalM_cons, Matrix.transpose_mul, genM_transpose]

/-- C2e. The formal inverse of a reduced word is reduced. Same pattern as
Round 2's `reduced_mirror`, with `inv_inv` in place of the ι_α facts. -/
theorem reduced_invRev {σ : Word} (h : Reduced σ) : Reduced (invRev σ) := by
  rw [invRev, reduced_isChain3, List.isChain_map, List.isChain_reverse]
  exact ((reduced_isChain3 σ).1 h).imp
    (fun {x y} hxy => by revert hxy; cases x <;> cases y <;> decide)

/-! ### C3: the comparison theorem -/

/-- C3a. Equal matrices force equal lengths. From C2c the scalars
(9 : R2)^ℓ₁ and (9 : R2)^ℓ₂ agree; compare, e.g., the `re`-components of the
(0,0) entries, land in ℤ, and use strict monotonicity of 9^· (or
`Nat.pow_right_injective`). -/
theorem length_eq_of_evalM_eq {σ₁ σ₂ : Word}
    (h : evalM σ₁ = evalM σ₂) : σ₁.length = σ₂.length := by
  have h1 := evalM_orth σ₁
  rw [h, evalM_orth σ₂] at h1
  have h2 := congrFun (congrFun h1 0) 0
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h2
  have h3 : ((9 ^ σ₁.length : ℤ) : R2) = ((9 ^ σ₂.length : ℤ) : R2) := by
    push_cast; exact h2.symm
  have h4 : (9 ^ σ₁.length : ℤ) = (9 ^ σ₂.length : ℤ) := by
    have := congrArg Zsqrtd.re h3
    rwa [Zsqrtd.re_intCast, Zsqrtd.re_intCast] at this
  have h5 : (9 : ℕ) ^ σ₁.length = 9 ^ σ₂.length := by exact_mod_cast h4
  exact Nat.pow_right_injective (by norm_num) h5

/-- C3b. The distinct-head concatenation is reduced. The last letter of
`invRev (c :: τ₁)` is `c.inv` (note `invRev (c :: τ₁) = invRev τ₁ ++
[c.inv]`), the junction demands `d ≠ (c.inv).inv = c`, which is the
hypothesis; the pieces are reduced by C2e and assumption. Use the
chain-append criterion (`List.isChain_append` in the pinned Mathlib, with
the `Chain'`/`IsChain` transport already used in Rounds 1–2). -/
theorem reduced_invRev_append {c d : Letter} {τ₁ τ₂ : Word}
    (h₁ : Reduced (c :: τ₁)) (h₂ : Reduced (d :: τ₂)) (hcd : c ≠ d) :
    Reduced (invRev (c :: τ₁) ++ (d :: τ₂)) := by
  rw [reduced_isChain3, List.isChain_append]
  refine ⟨(reduced_isChain3 _).1 (reduced_invRev h₁), (reduced_isChain3 _).1 h₂, ?_⟩
  intro x hx y hy
  rw [invRev_cons, List.getLast?_concat] at hx
  simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
  subst hx; subst hy
  cases c <;> cases d <;> simp_all [Letter.inv]

/-- Auxiliary: the scalar 9 may be cancelled from a matrix over ℤ[√2]. -/
private lemma nine_smul_cancel {X Y : Matrix (Fin 3) (Fin 3) R2}
    (h : (9 : R2) • X = (9 : R2) • Y) : X = Y := by
  apply Matrix.ext
  intro i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at hij
  have hre := congrArg Zsqrtd.re hij
  have him := congrArg Zsqrtd.im hij
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] at hre him
  refine Zsqrtd.ext ?_ ?_ <;> simp_all

/-- C3c. Left cancellation of a generator. Multiply on the left by
(genM c)ᵀ, apply C2b, and cancel the scalar 9 entrywise: in ℤ[√2],
9·x = 9·y forces x = y on `re`- and `im`-components over ℤ. -/
theorem genM_cancel {c : Letter} {X Y : Matrix (Fin 3) (Fin 3) R2}
    (h : genM c * X = genM c * Y) : X = Y := by
  have h1 : (genM c)ᵀ * (genM c * X) = (genM c)ᵀ * (genM c * Y) := by rw [h]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, genM_orth] at h1
  simp only [Matrix.smul_mul, Matrix.one_mul] at h1
  exact nine_smul_cancel h1

/-- Auxiliary: the comparison theorem with an explicit length bound. -/
private lemma evalM_inj_aux : ∀ (n : ℕ) (σ₁ σ₂ : Word), σ₁.length ≤ n →
    Reduced σ₁ → Reduced σ₂ → evalM σ₁ = evalM σ₂ → σ₁ = σ₂ := by
  intro n
  induction n with
  | zero =>
      intro σ₁ σ₂ hl _ _ h
      have h0 : σ₁ = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
      subst h0
      have hlen := (length_eq_of_evalM_eq h).symm
      exact (List.length_eq_zero_iff.mp (by simpa using hlen)).symm
  | succ n ih =>
      intro σ₁ σ₂ hl h₁ h₂ h
      match σ₁, σ₂ with
      | [], σ₂ =>
          have hlen := (length_eq_of_evalM_eq h).symm
          exact (List.length_eq_zero_iff.mp (by simpa using hlen)).symm
      | (c :: τ₁), [] =>
          have hlen := length_eq_of_evalM_eq h
          simp at hlen
      | (c :: τ₁), (d :: τ₂) =>
          by_cases hcd : c = d
          · subst hcd
            have hstep : genM c * evalM τ₁ = genM c * evalM τ₂ := by
              rw [← evalM_cons, ← evalM_cons]; exact h
            have htail := genM_cancel hstep
            have hrec := ih τ₁ τ₂ (by simp at hl; omega)
              (reduced_tail h₁) (reduced_tail h₂) htail
            rw [hrec]
          · exfalso
            set σ₁ := c :: τ₁ with hσ₁
            set σ₂ := d :: τ₂ with hσ₂
            have hlen : σ₁.length = σ₂.length := length_eq_of_evalM_eq h
            have hω : Reduced (invRev σ₁ ++ σ₂) := reduced_invRev_append h₁ h₂ hcd
            have hmat : evalM (invRev σ₁ ++ σ₂)
                = ((9 : R2) ^ σ₁.length) • (1 : Matrix (Fin 3) (Fin 3) R2) := by
              rw [evalM_append, evalM_invRev, ← h, evalM_orth]
            have hlength : (invRev σ₁ ++ σ₂).length = σ₁.length + σ₂.length := by
              simp [invRev]
            have h3 : ((9 : R2) ^ σ₁.length) = (3 : R2) ^ ((invRev σ₁ ++ σ₂).length) := by
              rw [hlength, ← hlen, show (9 : R2) = 3 ^ 2 by norm_num, ← pow_mul]
              ring_nf
            rw [h3] at hmat
            obtain ⟨e, rest, hcons⟩ : ∃ e rest, invRev σ₁ ++ σ₂ = e :: rest := by
              cases hh : invRev σ₁ ++ σ₂ with
              | nil => simp [hσ₂] at hh
              | cons e rest => exact ⟨e, rest, rfl⟩
            rw [hcons] at hω hmat
            exact swierczkowski_free e rest hω hmat

/-- C3d — MAIN comparison theorem. Distinct reduced words have distinct
matrices. Strong induction on `σ₁.length` (private auxiliary with an
explicit bound, as in previous rounds). Lengths agree by C3a; the empty
case is immediate. For σ₁ = c :: τ₁, σ₂ = d :: τ₂:
if c = d, strip with C0b and C3c and recurse on the reduced tails
(`Reduced (c :: τ) → Reduced τ`: chain tail, private helper);
if c ≠ d, the word ω := invRev (c :: τ₁) ++ (d :: τ₂) is reduced (C3b) and
nonempty, and
  evalM ω = (evalM σ₁)ᵀ * evalM σ₂        (C0c, C2d)
          = (evalM σ₁)ᵀ * evalM σ₁        (hypothesis)
          = (9 : R2)^ℓ₁ • 1               (C2c)
          = (3 : R2)^(ω.length) • 1,
since 9 = 3² and ω.length = ℓ₁ + ℓ₂ = 2·ℓ₁ by C3a. Destructure ω as a cons
(its head is the head of invRev (c :: τ₁)) and contradict Round 2's
`swierczkowski_free`. -/
theorem evalM_inj {σ₁ σ₂ : Word} (h₁ : Reduced σ₁) (h₂ : Reduced σ₂)
    (h : evalM σ₁ = evalM σ₂) : σ₁ = σ₂ :=
  evalM_inj_aux σ₁.length σ₁ σ₂ le_rfl h₁ h₂ h

/-! ### C4: quaternion injectivity at the specialization -/

/-- C4 — injectivity up to sign for the specialized quaternion evaluation.
Apply `conjMat` to either alternative; C1c kills the sign, C1e transports
to matrices, C3d concludes. -/
theorem qW_inj_pm {σ₁ σ₂ : Word} (h₁ : Reduced σ₁) (h₂ : Reduced σ₂)
    (h : qW σ₁ = qW σ₂ ∨ qW σ₁ = -qW σ₂) : σ₁ = σ₂ := by
  refine evalM_inj h₁ h₂ ?_
  rw [← conjMat_qW, ← conjMat_qW]
  rcases h with h | h
  · rw [h]
  · rw [h, conjMat_neg]

/-! ### C5: the polynomial-level theorem (paper Theorem 6.1) -/

/-- Componentwise application of a ring homomorphism to a quaternion. -/
def qmap {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (p : ℍ[R]) : ℍ[S] := ⟨φ p.re, φ p.imI, φ p.imJ, φ p.imK⟩

/-- Auxiliary: the multiplicative/unital kit for `qmap`. -/
private lemma qmap_one {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    qmap φ 1 = 1 := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp [qmap]

private lemma qmap_mul {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p q : ℍ[R]) :
    qmap φ (p * q) = qmap φ p * qmap φ q := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;>
    simp [qmap, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private lemma qmap_neg {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : ℍ[R]) :
    qmap φ (-p) = -(qmap φ p) := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp [qmap]

private lemma qmap_hL {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (t u x y z : R) (c : Letter) :
    qmap φ (hL t u x y z c) = hL (φ t) (φ u) (φ x) (φ y) (φ z) c := by
  cases c <;> refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp [qmap, hL]

/-- C5a. qmap is compatible with the word evaluation. Prove first (private)
that qmap is multiplicative and unital — the quaternion product components
are ±-signed sums of products, preserved by any ring homomorphism — and
that qmap carries `hL t u x y z c` to `hL (φ t) (φ u) (φ x) (φ y) (φ z) c`;
then induct with C0a. -/
theorem qmap_hW {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (t u x y z : R) (σ : Word) :
    qmap φ (hW t u x y z σ) = hW (φ t) (φ u) (φ x) (φ y) (φ z) σ := by
  induction σ with
  | nil => simpa [hW] using qmap_one φ
  | cons c s ih => rw [hW_cons, qmap_mul, ih, qmap_hL, hW_cons]

/-- The polynomial ring of the five variables, over ℤ. -/
noncomputable abbrev P5 := MvPolynomial (Fin 5) ℤ

/-- The generic word evaluation: hW at the variables themselves. -/
noncomputable def hWgen (σ : Word) : ℍ[P5] :=
  hW (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)
     (MvPolynomial.X 3) (MvPolynomial.X 4) σ

/-- Auxiliary: the specialization homomorphism sending the five variables to
(√2, 1, √2, 1, 0) in ℤ[√2]. -/
noncomputable def specHom : P5 →+* R2 :=
  MvPolynomial.eval₂Hom (Int.castRingHom R2) ![Zsqrtd.sqrtd, 1, Zsqrtd.sqrtd, 1, 0]

/-- Auxiliary: the specialization carries the generic evaluation to `qW`. -/
private lemma qmap_specHom_hWgen (σ : Word) : qmap specHom (hWgen σ) = qW σ := by
  rw [hWgen, qmap_hW, qW, hW]
  norm_num [specHom]
  rfl

/-- C5b — MAIN THEOREM (paper Theorem 6.1, formal form). The generic
evaluation is injective on reduced words, even up to sign. Specialize with
the evaluation homomorphism φ : P5 →+* R2 sending the variables to
(√2, 1, √2, 1, 0) — e.g. `MvPolynomial.eval₂Hom (Int.castRingHom R2)
![Zsqrtd.sqrtd, 1, Zsqrtd.sqrtd, 1, 0]` — transport the hypothesis through
C5a (note qmap of a negation is the negation of qmap: fold into the private
kit), and conclude by C4. -/
theorem hWgen_inj_pm {σ₁ σ₂ : Word} (h₁ : Reduced σ₁) (h₂ : Reduced σ₂)
    (h : hWgen σ₁ = hWgen σ₂ ∨ hWgen σ₁ = -hWgen σ₂) : σ₁ = σ₂ := by
  refine qW_inj_pm h₁ h₂ ?_
  rcases h with h | h
  · left
    rw [← qmap_specHom_hWgen, ← qmap_specHom_hWgen, h]
  · right
    rw [← qmap_specHom_hWgen, ← qmap_specHom_hWgen, h, qmap_neg]

/-! ### Module D: the sign-equivalence classification (paper Theorem 6.2)

Sign-equivalence of the identity triples (f₁, f_j, f_k) — global sign and
joint negation of the last two entries — corresponds at the quaternion
level (both quaternions having vanishing imI, by Round 1) to the four-fold
alternative below, and the classification says its solutions among
symmetric reduced words are exactly σ' ∈ {σ, ι_β σ}. -/

/-- D0. Quaternions with vanishing imI agree iff their remaining three
components agree; the bridge between the paper's triple language and the
quaternion language. `QuaternionAlgebra.ext` both ways. -/
theorem quat_eq_iff_triple {R : Type*} [CommRing R] {p q : ℍ[R]}
    (hp : p.imI = 0) (hq : q.imI = 0) :
    p = q ↔ (p.re = q.re ∧ p.imJ = q.imJ ∧ p.imK = q.imK) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    exact QuaternionAlgebra.ext h1 (by rw [hp, hq]) h2 h3

/-- D1 — MAIN classification. For symmetric reduced words, the quaternion of
σ' is a signed copy of that of σ or of ι_β σ exactly when σ' is σ or ι_β σ.
Backward: the first case is trivial and the second is reflexivity of the
third alternative. Forward: the four alternatives feed C5b — for the ι_β
alternatives with σ.map Letter.ib in place of σ₂, whose reducedness is
Round 2's `reduced_ibMap`; note `(σ.map Letter.ib).map Letter.ib = σ` via
`ib_ib` when translating the conclusion back. -/
theorem sign_classification {σ σ' : Word}
    (hσ : IsSym σ) (hσr : Reduced σ) (hσ' : IsSym σ') (hσ'r : Reduced σ') :
    (hWgen σ' = hWgen σ ∨ hWgen σ' = -hWgen σ ∨
     hWgen σ' = hWgen (σ.map Letter.ib) ∨ hWgen σ' = -hWgen (σ.map Letter.ib))
      ↔ (σ' = σ ∨ σ' = σ.map Letter.ib) := by
  have hib : Reduced (σ.map Letter.ib) := (reduced_ibMap σ).2 hσr
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl (hWgen_inj_pm hσ'r hσr (Or.inl h))
    · exact Or.inl (hWgen_inj_pm hσ'r hσr (Or.inr h))
    · exact Or.inr (hWgen_inj_pm hσ'r hib (Or.inl h))
    · exact Or.inr (hWgen_inj_pm hσ'r hib (Or.inr h))
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))

/-- Auxiliary: a list fixed by a letterwise map is fixed pointwise. -/
private lemma map_fixed {f : Letter → Letter} : ∀ {l : Word}, l.map f = l → ∀ x ∈ l, f x = x := by
  intro l
  induction l with
  | nil => intro _ x hx; simp at hx
  | cons e t ih =>
      intro h x hx
      rw [List.map_cons, List.cons.injEq] at h
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact h.1
      · exact ih h.2 x hx'

/-- D2. The ι_β-partner is genuinely distinct: sign-equivalence classes have
size exactly two. Route: by Round 2's `bisection_exists`, σ contains a
β-letter (its middle block); if σ.map Letter.ib = σ then every letter of σ
is ι_β-fixed (`List.map_eq_self`-style, or compare at the membership of the
β-letter), contradiction. -/
theorem ibMap_ne_self {σ : Word} (h1 : IsSym σ) (h2 : Reduced σ)
    (h3 : σ ≠ []) : σ.map Letter.ib ≠ σ := by
  intro hfix
  obtain ⟨pos, p, w, hp, heq, -, -⟩ := bisection_exists h1 h2 h3
  have hb : betaCount σ = 2 * betaCount w + p := by
    rw [heq]; exact (counts_encode pos p w).2
  have hposb : 0 < betaCount σ := by rcases hp with rfl | rfl <;> omega
  obtain ⟨x, hx, hxb⟩ := List.countP_pos_iff.1 hposb
  have hfixed := map_fixed hfix x hx
  cases x <;> simp_all [Letter.ib]

/-! ### Axiom audit -/

#print axioms hW_cons
#print axioms evalM_cons
#print axioms evalM_append
#print axioms re_conj_pure
#print axioms conjMat_mul
#print axioms conjMat_neg
#print axioms conjMat_qL
#print axioms conjMat_qW
#print axioms genM_transpose
#print axioms genM_orth
#print axioms evalM_orth
#print axioms evalM_invRev
#print axioms reduced_invRev
#print axioms length_eq_of_evalM_eq
#print axioms reduced_invRev_append
#print axioms genM_cancel
#print axioms evalM_inj
#print axioms qW_inj_pm
#print axioms qmap_hW
#print axioms hWgen_inj_pm
#print axioms quat_eq_iff_triple
#print axioms sign_classification
#print axioms ibMap_ne_self

end ThreeSquares
