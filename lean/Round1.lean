/-
Round 1 — Cancellation core of
"Polynomial identities, sums of three squares, and quaternionic (anti-)automorphisms"
(D. V. Feldman, University of New Hampshire).

This file contains all definitions and theorem statements for Round 1.
Every `sorry` is commissioned. Do not alter any definition or statement;
if a statement fails as written, REPORT it and move on — do not repair.

Closure criterion per theorem: compiles, and `#print axioms` shows at most
propext, Classical.choice, Quot.sound. Exception: the two theorems marked
NATIVE may additionally use Lean.ofReduceBool (via `native_decide`); if plain
`decide` succeeds within resource limits, prefer it and note which was used.

Mathlib conventions assumed: `ℍ[R]` is `Quaternion R` with components
`re`, `imI`, `imJ`, `imK`; `Quaternion.normSq` is multiplicative.
If a needed component-arithmetic simp lemma is missing for general
commutative rings, prove a local version by `ext` and `ring` rather than
changing any statement below.
-/
import Mathlib

open Quaternion

namespace ThreeSquares

/-- The four letters α, α⁻¹, β, β⁻¹. -/
inductive Letter
  | a | A | b | B
deriving DecidableEq, Repr

namespace Letter

/-- ι_α: invert the α-letters, fix the β-letters. -/
def ia : Letter → Letter
  | a => A | A => a | b => b | B => B

/-- ι_β: invert the β-letters, fix the α-letters. -/
def ib : Letter → Letter
  | a => a | A => A | b => B | B => b

/-- Formal inverse of a letter. -/
def inv : Letter → Letter
  | a => A | A => a | b => B | B => b

end Letter

/-- Words are lists of letters, multiplied left to right. -/
abbrev Word := List Letter

/-- The symmetry class S, WITHOUT the reducedness condition (not needed in
this round): words fixed by reversal-with-α-inversion. -/
def IsSym (σ : Word) : Prop := σ.reverse.map Letter.ia = σ

instance (σ : Word) : Decidable (IsSym σ) := by unfold IsSym; infer_instance

/-- Auxiliary (added, not commissioned): in the current Mathlib, `List.Chain'`
is a deprecated alias for `List.IsChain` and the decidability instance is
registered for the latter only, so `infer_instance` cannot see through the
alias. This instance restores it; it is definitionally the `IsChain`
instance. Without it the (unmodified) instance for `Reduced` below fails to
elaborate. -/
instance decidableListChain' {α : Type*} (r : α → α → Prop) [DecidableRel r] (l : List α) :
    Decidable (l.Chain' r) :=
  decidable_of_iff (List.IsChain r l) Iff.rfl

/-- No letter is adjacent to its formal inverse. -/
def Reduced (σ : Word) : Prop := σ.Chain' (fun c d => d ≠ c.inv)

instance (σ : Word) : Decidable (Reduced σ) := by unfold Reduced; infer_instance

def alphaCount (σ : Word) : ℕ := σ.countP (fun c => c == Letter.a || c == Letter.A)
def betaCount  (σ : Word) : ℕ := σ.countP (fun c => c == Letter.b || c == Letter.B)

section Evaluation

variable {R : Type*} [CommRing R]

/-- Auxiliary (added, not commissioned): in the current Mathlib
`Quaternion R` is a plain (non-reducible) definition unfolding to
`QuaternionAlgebra R (-1) 0 (-1)`, and the anonymous-constructor notation
`(⟨0,1,0,0⟩ : ℍ[R])` elaborates at the unfolded type. Type-class resolution
does not unfold `Quaternion`, so the heterogeneous products appearing in the
statement of M1.9a below cannot be synthesised. These two instances are
literally `instHMul` for the quaternion multiplication (they are definitionally
the ordinary multiplication of `ℍ[R]`); they only repair elaboration and do
not change the meaning of any statement. -/
local instance hmulQuatAlgLeft {R : Type*} [CommRing R] :
    HMul (QuaternionAlgebra R (-1) 0 (-1)) (Quaternion R) (Quaternion R) := instHMul

local instance hmulQuatAlgRight {R : Type*} [CommRing R] :
    HMul (Quaternion R) (QuaternionAlgebra R (-1) 0 (-1)) (Quaternion R) := instHMul

/-- Letter evaluation: α ↦ t+iu, α⁻¹ ↦ t−iu, β ↦ x+yj+zk, β⁻¹ ↦ x−yj−zk. -/
def hL (t u x y z : R) : Letter → ℍ[R]
  | .a => ⟨t,  u, 0, 0⟩
  | .A => ⟨t, -u, 0, 0⟩
  | .b => ⟨x, 0,  y,  z⟩
  | .B => ⟨x, 0, -y, -z⟩

/-- Word evaluation: the ordered product of the letter values. -/
def hW (t u x y z : R) (σ : Word) : ℍ[R] := (σ.map (hL t u x y z)).prod

/-- θ(p) = i⁻¹ p̄ i, written coordinatewise so that no inverses are needed. -/
def theta (p : ℍ[R]) : ℍ[R] := ⟨p.re, -p.imI, p.imJ, p.imK⟩

/-! ### Module M1: the cancellation theorem and its companions -/

/-- M1.1a. θ is anti-multiplicative. Proof route: `ext` then `simp` with the
quaternion multiplication component lemmas, closing by `ring`. -/
theorem theta_mul (p q : ℍ[R]) : theta (p * q) = theta q * theta p := by
  ext <;> simp [theta] <;> ring

/-- M1.1b. θ is an involution. -/
theorem theta_theta (p : ℍ[R]) : theta (theta p) = p := by
  ext <;> simp [theta]

/-- M1.2a. θ on letter values realizes ι_α. Four cases; each closes by
`ext` and `simp`/`ring`. -/
theorem theta_hL (t u x y z : R) (c : Letter) :
    theta (hL t u x y z c) = hL t u x y z c.ia := by
  cases c <;> ext <;> simp [theta, hL, Letter.ia]

/-- M1.2b. Intertwining: θ ∘ h = h ∘ (reverse ∘ map ι_α). Induction on σ,
using `List.prod_cons`, `theta_mul`, `theta_hL`, and `List.map_append`,
`List.prod_append` on the reversed side. -/
theorem theta_hW (t u x y z : R) (σ : Word) :
    theta (hW t u x y z σ) = hW t u x y z (σ.reverse.map Letter.ia) := by
  induction σ with
  | nil => ext <;> simp [hW, theta]
  | cons c s ih =>
      simp only [hW, List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
        List.prod_append] at *
      rw [theta_mul, ih, theta_hL]
      simp

/-- Auxiliary: ι_α is an involution on letters. -/
private theorem ia_ia (c : Letter) : c.ia.ia = c := by cases c <;> rfl

/-- M1.3. Structure of symmetric words: empty, a single ι_α-fixed letter
(hence a β-letter), or c · σ' · ι_α(c) with σ' symmetric. Pure list
manipulation: peel the first letter, use `List.reverse_cons`, compare last
letters, take σ' the interior. -/
theorem isSym_strip {σ : Word} (h : IsSym σ) :
    σ = [] ∨ (∃ c : Letter, σ = [c] ∧ c.ia = c) ∨
    ∃ (c : Letter) (σ' : Word), σ = c :: (σ' ++ [c.ia]) ∧ IsSym σ' := by
  match σ with
  | [] => exact Or.inl rfl
  | [c] =>
      refine Or.inr (Or.inl ⟨c, rfl, ?_⟩)
      simpa [IsSym] using h
  | c :: d :: t =>
      refine Or.inr (Or.inr ?_)
      rcases (d :: t).eq_nil_or_concat with hn | ⟨L, e, he⟩
      · simp at hn
      · rw [List.concat_eq_append] at he
        rw [he] at h ⊢
        simp only [IsSym, List.reverse_cons, List.reverse_append, List.map_append, List.map_cons,
          List.map_reverse, List.map_nil, List.reverse_nil, List.cons_append,
          List.nil_append, List.cons.injEq] at h
        obtain ⟨h1, h2⟩ := h
        have hd : e = c.ia := by rw [← h1, ia_ia]
        subst hd
        refine ⟨c, L, rfl, ?_⟩
        have hcancel := List.append_cancel_right h2
        rw [IsSym, List.map_reverse, hcancel]

/-- M1.4. The strip step: conjugation-with-a-twist by any letter preserves
vanishing of the i-coefficient. Four cases on c; in each, destructure p,
substitute `hp`, and close the imI component by `ring` after `simp` with the
multiplication component lemmas. (These four polynomial identities have been
verified symbolically; they are exact, with no division.) -/
theorem imI_conj (t u x y z : R) (c : Letter) {p : ℍ[R]} (hp : p.imI = 0) :
    (hL t u x y z c * p * hL t u x y z c.ia).imI = 0 := by
  obtain ⟨pr, pi, pj, pk⟩ := p
  simp only [] at hp
  subst hp
  cases c <;> simp [hL, Letter.ia] <;> ring

/-- Auxiliary: the evaluation of a stripped symmetric word factors. -/
private theorem hW_strip (t u x y z : R) (c : Letter) (σ' : Word) :
    hW t u x y z (c :: (σ' ++ [c.ia]))
      = hL t u x y z c * hW t u x y z σ' * hL t u x y z c.ia := by
  simp [hW, List.prod_cons, mul_assoc]

/-- Auxiliary: the strip induction for M1.5, with an explicit length bound. -/
private theorem imI_hW_aux (t u x y z : R) : ∀ (n : ℕ) (σ : Word), σ.length ≤ n → IsSym σ →
    (hW t u x y z σ).imI = 0 := by
  intro n
  induction n with
  | zero => intro σ hl _; rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]; simp [hW]
  | succ n ih =>
      intro σ hl hσ
      rcases isSym_strip hσ with rfl | ⟨c, rfl, hc⟩ | ⟨c, σ', rfl, hσ'⟩
      · simp [hW]
      · cases c <;> simp_all [hW, hL, Letter.ia]
      · rw [hW_strip]
        refine imI_conj _ _ _ _ _ _ (ih σ' ?_ hσ')
        simp at hl
        omega

/-- M1.5 — MAIN THEOREM (cancellation). For symmetric words the
i-coefficient of the evaluation vanishes, over every commutative ring.
Strong induction on `σ.length` via `isSym_strip`; the decomposition case
uses `hW (c :: σ' ++ [c.ia]) = hL c * hW σ' * hL c.ia`
(from `List.map_cons/append` and `List.prod_cons/append`) and `imI_conj`.
Base cases: the empty product (imI of 1 is 0) and single β-letters
(imI of hL b, hL B is 0 by definition). -/
theorem imI_hW_eq_zero (t u x y z : R) {σ : Word} (hσ : IsSym σ) :
    (hW t u x y z σ).imI = 0 :=
  imI_hW_aux t u x y z σ.length σ le_rfl hσ

/-- Auxiliary: the strip induction for M1.6, with an explicit length bound. -/
private theorem alphaCount_aux : ∀ (n : ℕ) (σ : Word), σ.length ≤ n → IsSym σ →
    Even (alphaCount σ) := by
  intro n
  induction n with
  | zero => intro σ hl _; rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]; simp [alphaCount]
  | succ n ih =>
      intro σ hl hσ
      rcases isSym_strip hσ with rfl | ⟨c, rfl, hc⟩ | ⟨c, σ', rfl, hσ'⟩
      · simp [alphaCount]
      · cases c <;> simp_all [alphaCount, Letter.ia]
      · have hrec := ih σ' (by simp at hl; omega) hσ'
        cases c <;>
          simpa [alphaCount, List.countP_cons, Letter.ia, Nat.even_add_one, parity_simps]
            using hrec

/-- M1.6. Symmetric words have evenly many α-letters. Same strip induction;
stripping removes zero or two α-letters, and the base cases have none. -/
theorem alphaCount_even {σ : Word} (hσ : IsSym σ) : Even (alphaCount σ) :=
  alphaCount_aux σ.length σ le_rfl hσ

/-- M1.7a. Norms of letter values. Two families; each closes by `simp`
with the normSq component formula and `ring`. If the general-ring formula
`normSq p = p.re^2 + p.imI^2 + p.imJ^2 + p.imK^2` is not available as a simp
lemma, derive it locally from `normSq_def` (`normSq a = (a * star a).re`). -/
theorem normSq_hL_alpha (t u x y z : R) (c : Letter)
    (hc : c = Letter.a ∨ c = Letter.A) :
    normSq (hL t u x y z c) = t^2 + u^2 := by
  rcases hc with rfl | rfl <;> simp [hL, normSq_def']

theorem normSq_hL_beta (t u x y z : R) (c : Letter)
    (hc : c = Letter.b ∨ c = Letter.B) :
    normSq (hL t u x y z c) = x^2 + y^2 + z^2 := by
  rcases hc with rfl | rfl <;> simp [hL, normSq_def']

/-- M1.7b. The norm of a word evaluation. Induction on σ with
`normSq_mul` and the letter norms; the exponents track the letter counts. -/
theorem normSq_hW (t u x y z : R) (σ : Word) :
    normSq (hW t u x y z σ)
      = (t^2 + u^2)^(alphaCount σ) * (x^2 + y^2 + z^2)^(betaCount σ) := by
  induction σ with
  | nil => simp [hW, alphaCount, betaCount]
  | cons c s ih =>
      rw [hW, List.map_cons, List.prod_cons, map_mul, ← hW, ih]
      cases c <;> simp [hL, normSq_def', alphaCount, betaCount, pow_succ] <;> ring

/-- M1.8 — THE IDENTITY. Combines M1.5 and M1.7b with the component formula
for normSq. This is the machine form of the paper's Corollary 3.5. -/
theorem three_squares (t u x y z : R) {σ : Word} (hσ : IsSym σ) :
    (t^2 + u^2)^(alphaCount σ) * (x^2 + y^2 + z^2)^(betaCount σ)
      = (hW t u x y z σ).re^2 + (hW t u x y z σ).imJ^2 + (hW t u x y z σ).imK^2 := by
  have hn := normSq_hW t u x y z σ
  rw [normSq_def', imI_hW_eq_zero t u x y z hσ] at hn
  rw [← hn]
  ring

/-- Auxiliary: the quaternion `i`, at the type `ℍ[R]` (the statement of M1.9a
writes it with anonymous-constructor notation). -/
private def qI (R : Type*) [CommRing R] : ℍ[R] := ⟨0, 1, 0, 0⟩

/-- Auxiliary: the letter form of M1.9a. -/
private theorem i_mul_hL (t u x y z : R) (c : Letter) :
    qI R * hL t u x y z c = hL t u x y z c.ib * qI R := by
  cases c <;> ext <;> simp [hL, Letter.ib, qI]

/-- Auxiliary: M1.9a, stated with `qI`. -/
private theorem i_mul_hW' (t u x y z : R) (σ : Word) :
    qI R * hW t u x y z σ = hW t u x y z (σ.map Letter.ib) * qI R := by
  induction σ with
  | nil => simp [hW, qI]
  | cons c s ih =>
      simp only [hW, List.map_cons, List.prod_cons] at *
      rw [← mul_assoc, i_mul_hL, mul_assoc, ih, ← mul_assoc]

/-- M1.9a. Multiplying by i on the left realizes ι_β, with i carried to the
right; no inverses are used. Induction on σ after the four letter cases
`(⟨0,1,0,0⟩ : ℍ[R]) * hL c = hL c.ib * ⟨0,1,0,0⟩`. -/
theorem i_mul_hW (t u x y z : R) (σ : Word) :
    (⟨0,1,0,0⟩ : ℍ[R]) * hW t u x y z σ
      = hW t u x y z (σ.map Letter.ib) * ⟨0,1,0,0⟩ :=
  i_mul_hW' t u x y z σ

/-- M1.9b. Component form: ι_β fixes re and imI and negates imJ and imK.
Extract components from M1.9a (multiply out ⟨0,1,0,0⟩ on both sides). -/
theorem hW_ib_components (t u x y z : R) (σ : Word) :
    (hW t u x y z (σ.map Letter.ib)).re = (hW t u x y z σ).re ∧
    (hW t u x y z (σ.map Letter.ib)).imI = (hW t u x y z σ).imI ∧
    (hW t u x y z (σ.map Letter.ib)).imJ = -(hW t u x y z σ).imJ ∧
    (hW t u x y z (σ.map Letter.ib)).imK = -(hW t u x y z σ).imK := by
  have h := i_mul_hW' (R := R) t u x y z σ
  have h1 := congrArg QuaternionAlgebra.re h
  have h2 := congrArg QuaternionAlgebra.imI h
  have h3 := congrArg QuaternionAlgebra.imJ h
  have h4 := congrArg QuaternionAlgebra.imK h
  simp [qI] at h1 h2 h3 h4
  exact ⟨h2.symm, h1.symm, by rw [h4, neg_neg], h3.symm⟩

/-- M1.10. The substitution (y,z) ↦ (−y,−z) realizes ι_β. Induction on σ
after the four letter cases. Combined with M1.9b this is the paper's
parity proposition (Proposition 4.1). -/
theorem hW_neg_yz (t u x y z : R) (σ : Word) :
    hW t u x (-y) (-z) σ = hW t u x y z (σ.map Letter.ib) := by
  induction σ with
  | nil => simp [hW]
  | cons c s ih =>
      simp only [hW, List.map_cons, List.prod_cons] at *
      rw [ih]
      congr 1
      cases c <;> ext <;> simp [hL, Letter.ib]

end Evaluation

/-! ### Module M2: census combinatorics -/

/-- The census function, defined by the transfer recurrence extracted from
the generating function (1+s)/(1−s−q−3sq). R(0,0)=1, R(1,0)=2 are the base
overrides; thereafter R(m,0)=R(m−1,0) and
R(m,k) = R(m−1,k) + R(m,k−1) + 3·R(m−1,k−1). -/
def Rc : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 1, 0 => 2
  | (m+2), 0 => Rc (m+1) 0
  | 0, (k+1) => Rc 0 k
  | (m+1), (k+1) => Rc m (k+1) + Rc (m+1) k + 3 * Rc m k

/-- M2.1. Sanity: the m=0 row is constant 1. Induction. -/
theorem Rc_zero (k : ℕ) : Rc 0 k = 1 := by
  induction k with
  | zero => simp [Rc]
  | succ k ih => rw [Rc, ih]

/-- M2.2. The m=1 closed form (paper: type (1,n) has 2n or 2n−2 identities). -/
theorem Rc_one (k : ℕ) : Rc 1 k = 4*k + 2 := by
  induction k with
  | zero => simp [Rc]
  | succ k ih => rw [Rc, ih, Rc_zero, Rc_zero]; ring

/-- M2.3. The m=2 closed form. -/
theorem Rc_two (k : ℕ) : Rc 2 k = 8*k^2 + 4*k + 2 := by
  induction k with
  | zero => simp [Rc]
  | succ k ih => rw [show (2:ℕ) = 1+1 from rfl, Rc, ih, Rc_one, Rc_one]; ring

/-- All words of length ℓ. -/
def allWords : ℕ → List Word
  | 0 => [[]]
  | n+1 => (allWords n).flatMap (fun w => [Letter.a, .A, .b, .B].map (· :: w))

/-- The number of symmetric reduced words of type (m,n)
(α-count 2m, β-count n; the length is then determined). -/
def censusCount (m n : ℕ) : ℕ :=
  ((allWords (2*m + n)).filter (fun σ =>
      decide (IsSym σ) && decide (Reduced σ)
        && (alphaCount σ == 2*m) && (betaCount σ == n))).length

-- Raised only to let the kernel run the `decide` evaluations below; both
-- census theorems are closed by plain `decide` (no `native_decide`).
set_option maxRecDepth 10000

/-- M2.4 — NATIVE. Smoke test: type (1,3) has 12 symmetric reduced words,
i.e. 2·Rc 1 1 (the paper's 6 identity classes, doubled by ι_β). -/
theorem census_1_3 : censusCount 1 3 = 12 := by decide

/-- M2.5 — NATIVE. Smoke test: type (2,1) has 4 symmetric reduced words,
i.e. 2·Rc 2 0. -/
theorem census_2_1 : censusCount 2 1 = 4 := by decide

/-! ### Module M3: the [2,3,3] obstruction -/

open Matrix

/-- M3.1. A 3×3 real matrix cannot be both orthogonal and skew-symmetric.
Determinant: skewness gives det B = det Bᵀ = det(−B) = −det B, so det B = 0;
orthogonality gives (det B)² = 1. Use `Matrix.det_transpose`,
`Matrix.det_neg` (dimension 3 is odd), `Matrix.det_mul`, `Matrix.det_one`. -/
theorem no_orthogonal_skew (B : Matrix (Fin 3) (Fin 3) ℝ)
    (horth : Bᵀ * B = 1) (hskew : Bᵀ = -B) : False := by
  have h1 : B.det * B.det = 1 := by
    have h := congrArg Matrix.det horth
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  have h2 : B.det = -B.det := by
    have h := congrArg Matrix.det hskew
    rwa [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin,
      show ((-1:ℝ)^3) = -1 by norm_num, neg_one_mul] at h
  have h3 : B.det = 0 := by linarith
  rw [h3] at h1
  norm_num at h1

/-- Auxiliary: components of a matrix pencil applied to a vector. -/
private theorem mulVec_pencil (A B : Matrix (Fin 3) (Fin 3) ℝ) (t u : ℝ)
    (v : Fin 3 → ℝ) (k : Fin 3) :
    ((t • A + u • B).mulVec v) k = t * (A.mulVec v k) + u * (B.mulVec v k) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- Auxiliary: bilinear expansion of a sum of products. -/
private theorem sum_bilin_expand (a b c d : Fin 3 → ℝ) :
    ∑ k, (a k + b k) * (c k + d k)
      = ∑ k, a k * c k + ∑ k, a k * d k + ∑ k, b k * c k + ∑ k, b k * d k := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- Auxiliary: symmetry of the dot product, in coordinates. -/
private theorem sum_mul_comm3 (a b : Fin 3 → ℝ) : ∑ k, a k * b k = ∑ k, b k * a k :=
  Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- M3.2. No bilinear [2,3,3] composition formula over ℝ. From the identity,
extract the coefficients of t², u², tu (specialize t,u to (1,0), (0,1), (1,1))
to get, for all v: |A₁v|² = |v|², |A₂v|² = |v|², ⟨A₁v, A₂v⟩ = 0. Polarize
(division by 2 is available in ℝ) to obtain A₁ᵀA₁ = 1, A₂ᵀA₂ = 1,
A₁ᵀA₂ + A₂ᵀA₁ = 0. Set B := A₁ᵀ * A₂; then Bᵀ = −B, and Bᵀ * B = 1 using
`Matrix.mul_eq_one_comm` to convert A₁ᵀA₁ = 1 into A₁A₁ᵀ = 1. Conclude by
M3.1. This theorem is the self-contained kernel of the paper's
Remark 4.4 on the case (a,n) = (1,1). -/
theorem no_bilinear_233 :
    ¬ ∃ A₁ A₂ : Matrix (Fin 3) (Fin 3) ℝ,
        ∀ (t u : ℝ) (v : Fin 3 → ℝ),
          (∑ k, ((t • A₁ + u • A₂).mulVec v k)^2)
            = (t^2 + u^2) * (∑ i, (v i)^2) := by
  rintro ⟨A₁, A₂, h⟩
  -- the three quadratic-form consequences
  have e1 : ∀ v : Fin 3 → ℝ, ∑ k, (A₁.mulVec v k)^2 = ∑ i, (v i)^2 := by
    intro v
    have hv := h 1 0 v
    simp only [mulVec_pencil] at hv
    simpa using hv
  have e2 : ∀ v : Fin 3 → ℝ, ∑ k, (A₂.mulVec v k)^2 = ∑ i, (v i)^2 := by
    intro v
    have hv := h 0 1 v
    simp only [mulVec_pencil] at hv
    simpa using hv
  have e3 : ∀ v : Fin 3 → ℝ, ∑ k, (A₁.mulVec v k) * (A₂.mulVec v k) = 0 := by
    intro v
    have hv := h 1 1 v
    simp only [mulVec_pencil, one_mul] at hv
    have expand : ∑ k, (A₁.mulVec v k + A₂.mulVec v k)^2
        = (∑ k, (A₁.mulVec v k)^2) + 2 * (∑ k, (A₁.mulVec v k) * (A₂.mulVec v k))
          + (∑ k, (A₂.mulVec v k)^2) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [expand, e1, e2] at hv
    linarith
  -- polarization
  have p1 : ∀ v w : Fin 3 → ℝ, ∑ k, (A₁.mulVec v k) * (A₁.mulVec w k) = ∑ i, v i * w i := by
    intro v w
    have hvw := e1 (v + w)
    simp only [Matrix.mulVec_add, Pi.add_apply, sq] at hvw
    rw [sum_bilin_expand, sum_bilin_expand] at hvw
    have hv := e1 v
    have hw := e1 w
    simp only [sq] at hv hw
    rw [sum_mul_comm3 (A₁.mulVec w) (A₁.mulVec v), sum_mul_comm3 w v] at hvw
    linarith
  have p2 : ∀ v w : Fin 3 → ℝ, ∑ k, (A₂.mulVec v k) * (A₂.mulVec w k) = ∑ i, v i * w i := by
    intro v w
    have hvw := e2 (v + w)
    simp only [Matrix.mulVec_add, Pi.add_apply, sq] at hvw
    rw [sum_bilin_expand, sum_bilin_expand] at hvw
    have hv := e2 v
    have hw := e2 w
    simp only [sq] at hv hw
    rw [sum_mul_comm3 (A₂.mulVec w) (A₂.mulVec v), sum_mul_comm3 w v] at hvw
    linarith
  have p3 : ∀ v w : Fin 3 → ℝ,
      (∑ k, (A₁.mulVec v k) * (A₂.mulVec w k))
        + (∑ k, (A₁.mulVec w k) * (A₂.mulVec v k)) = 0 := by
    intro v w
    have hvw := e3 (v + w)
    simp only [Matrix.mulVec_add, Pi.add_apply] at hvw
    rw [sum_bilin_expand] at hvw
    have hv := e3 v
    have hw := e3 w
    linarith
  -- the Gram conditions
  have hA1 : A₁ᵀ * A₁ = 1 := by
    ext i j
    have hp := p1 (Pi.single i 1) (Pi.single j 1)
    simp only [Matrix.mulVec_single, Matrix.col_apply, MulOpposite.op_one, one_smul] at hp
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hp]
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have hA2 : A₂ᵀ * A₂ = 1 := by
    ext i j
    have hp := p2 (Pi.single i 1) (Pi.single j 1)
    simp only [Matrix.mulVec_single, Matrix.col_apply, MulOpposite.op_one, one_smul] at hp
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hp]
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  -- the orthogonal skew matrix
  set B : Matrix (Fin 3) (Fin 3) ℝ := A₁ᵀ * A₂ with hB
  have hBt : Bᵀ = A₂ᵀ * A₁ := by rw [hB, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hskew : Bᵀ = -B := by
    rw [hBt, hB]
    ext i j
    have hp := p3 (Pi.single i 1) (Pi.single j 1)
    simp only [Matrix.mulVec_single, Matrix.col_apply, MulOpposite.op_one, one_smul] at hp
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.neg_apply]
    rw [show ∑ k, A₂ k i * A₁ k j = ∑ k, A₁ k j * A₂ k i from
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)]
    linarith
  have hA1' : A₁ * A₁ᵀ = 1 := mul_eq_one_comm.mp hA1
  have horth : Bᵀ * B = 1 := by
    rw [hBt, hB, Matrix.mul_assoc, ← Matrix.mul_assoc A₁ A₁ᵀ A₂, hA1', Matrix.one_mul, hA2]
  exact no_orthogonal_skew B horth hskew

/-! ### Axiom audit -/

#print axioms theta_mul
#print axioms theta_theta
#print axioms theta_hL
#print axioms theta_hW
#print axioms isSym_strip
#print axioms imI_conj
#print axioms imI_hW_eq_zero
#print axioms alphaCount_even
#print axioms normSq_hL_alpha
#print axioms normSq_hL_beta
#print axioms normSq_hW
#print axioms three_squares
#print axioms i_mul_hW
#print axioms hW_ib_components
#print axioms hW_neg_yz
#print axioms Rc_zero
#print axioms Rc_one
#print axioms Rc_two
#print axioms census_1_3
#print axioms census_2_1
#print axioms no_orthogonal_skew
#print axioms no_bilinear_233

end ThreeSquares
