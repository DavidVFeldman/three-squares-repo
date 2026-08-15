/-
Round 4 — Rank-three freeness and the classes-count capstone, for
"Polynomial identities, sums of three squares, and quaternionic (anti-)automorphisms"
(D. V. Feldman, University of New Hampshire).

This file imports Round1.lean, Round2.lean, Round3.lean — the CLOSED artifacts
of the previous rounds; all three are frozen: import and use freely, modify
nothing. All definitions below are final; every `sorry` is commissioned. If a
statement fails as written, REPORT it and move on — do not repair. Private
auxiliary lemmas may be added freely. Add a `Round4` target to lakefile.toml.

Closure criterion per theorem: compiles; `#print axioms` shows at most
propext, Classical.choice, Quot.sound. No native_decide exceptions: all decision
procedures in this round are small (81 residue pairs, 36 dot products,
Fin 3 searches); plain `decide` must suffice.

Every hard-coded datum below has been certified before commissioning: the six
outer-product decompositions exactly over ℤ[√2]; the thirty unit meshes and six
divisible inverse-junctions; the 81-case primality of 3; the unit entries of
every column and row vector; the u·outer + 3E decomposition constructively on
all 23436 reduced rank-three words of length ≤ 6; and the orbit counts against
Rc across the (m,n) table. If a statement resists, suspect the route, then
report.

Design note (Module E, binding). The rank-one-modulo-3 argument is formalized
with NO quotient rings: rank-one-ness is the exact identity
  genR g = vecMulVec (colR g) (rowR g) + 3 • defR g
over ℤ[√2] itself, primality of 3 is the componentwise residue check E2, and
the whole induction lives in ℤ[√2]. Do not introduce Ideal.Quotient or ZMod-
valued matrices.
-/
import Round1
import Round2
import Round3

open Quaternion Matrix

namespace ThreeSquares

/-! ## Module E: freeness for the three coordinate axes -/

/-- The six generators: rotations through arccos(1/3) about e₁, e₂, e₃ and
their inverses. -/
inductive Rot
  | a | A | b | B | c | C
deriving DecidableEq, Repr

namespace Rot
def inv : Rot → Rot
  | a => A | A => a | b => B | B => b | c => C | C => c
end Rot

abbrev Word3 := List Rot

/-- No letter adjacent to its inverse. -/
def Reduced3 (σ : Word3) : Prop := σ.Chain' (fun x y => y ≠ x.inv)

instance (σ : Word3) : Decidable (Reduced3 σ) := by unfold Reduced3; infer_instance

open Zsqrtd in
/-- The six 3-scaled rotation matrices. `a`,`b` are Round 2's `genM a`, `genM b`
(axes e₁, e₂); `c` is the rotation about e₃; capitals are transposes. -/
def genR : Rot → Matrix (Fin 3) (Fin 3) R2
  | .a => !![3, 0, 0; 0, 1, -2*sqrtd; 0, 2*sqrtd, 1]
  | .A => !![3, 0, 0; 0, 1, 2*sqrtd; 0, -2*sqrtd, 1]
  | .b => !![1, 0, 2*sqrtd; 0, 3, 0; -2*sqrtd, 0, 1]
  | .B => !![1, 0, -2*sqrtd; 0, 3, 0; 2*sqrtd, 0, 1]
  | .c => !![1, -2*sqrtd, 0; 2*sqrtd, 1, 0; 0, 0, 3]
  | .C => !![1, 2*sqrtd, 0; -2*sqrtd, 1, 0; 0, 0, 3]

def evalR (σ : Word3) : Matrix (Fin 3) (Fin 3) R2 := (σ.map genR).prod

open Zsqrtd in
/-- The column vector of the rank-one part of each generator. -/
def colR : Rot → Fin 3 → R2
  | .a => ![0, 1,  2*sqrtd]
  | .A => ![0, 1, -2*sqrtd]
  | .b => ![1, 0, -2*sqrtd]
  | .B => ![1, 0,  2*sqrtd]
  | .c => ![1,  2*sqrtd, 0]
  | .C => ![1, -2*sqrtd, 0]

open Zsqrtd in
/-- The row vector of the rank-one part of each generator. -/
def rowR : Rot → Fin 3 → R2
  | .a => ![0, 1, -2*sqrtd]
  | .A => ![0, 1,  2*sqrtd]
  | .b => ![1, 0,  2*sqrtd]
  | .B => ![1, 0, -2*sqrtd]
  | .c => ![1, -2*sqrtd, 0]
  | .C => ![1,  2*sqrtd, 0]

/-- The integral correction matrix: 1 at the fixed-axis diagonal slot and 3 at
the second moving slot's diagonal corner. -/
def defR : Rot → Matrix (Fin 3) (Fin 3) R2
  | .a | .A => !![1,0,0; 0,0,0; 0,0,3]
  | .b | .B => !![0,0,0; 0,1,0; 0,0,3]
  | .c | .C => !![0,0,0; 0,3,0; 0,0,1]

/-- E1. The exact rank-one-plus-3 decomposition of every generator.
Six cases; `ext i j; fin_cases i <;> fin_cases j;` then `Zsqrtd` component
arithmetic (√2·√2 = 2) and `decide`/`ring`. `Matrix.vecMulVec` is the outer
product. -/
theorem genR_decomp (g : Rot) :
    genR g = vecMulVec (colR g) (rowR g) + (3 : R2) • defR g := by
  cases g <;>
  · refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [genR, colR, rowR, defR, vecMulVec] <;> decide

/-- E2a. Divisibility by 3 in ℤ[√2] is componentwise. One direction reads off
components of `3 * w`; the other builds the witness `⟨z.re/3, z.im/3⟩`. -/
theorem three_dvd_iff (z : R2) :
    (3 : R2) ∣ z ↔ (3 : ℤ) ∣ z.re ∧ (3 : ℤ) ∣ z.im := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨⟨w.re, by simp⟩, ⟨w.im, by simp⟩⟩
  · rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    exact ⟨⟨p, q⟩, by ext <;> simp [hp, hq]⟩

/-- Auxiliary: the 81-case residue core behind E2b. -/
private lemma zmod3_core : ∀ p q r s : ZMod 3, ¬(p = 0 ∧ q = 0) → ¬(r = 0 ∧ s = 0) →
    ¬(p * r + 2 * q * s = 0 ∧ p * s + q * r = 0) := by decide

/-- E2b. 3 is prime in ℤ[√2]: a product of two non-multiples is a non-multiple.
Route: by E2a pass to the residues of the components modulo 3 (`Int.emod`, or
cast to `ZMod 3`); the product components are `x.re*y.re + 2*x.im*y.im` and
`x.re*y.im + x.im*y.re`; the resulting 81-case statement over `ZMod 3` closes
by `decide`. -/
theorem three_prime_mul {x y : R2}
    (hx : ¬ (3 : R2) ∣ x) (hy : ¬ (3 : R2) ∣ y) : ¬ (3 : R2) ∣ (x * y) := by
  rw [three_dvd_iff] at hx hy ⊢
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] at *
  have key := zmod3_core (x.re : ZMod 3) (x.im : ZMod 3) (y.re : ZMod 3) (y.im : ZMod 3)
    (by rintro ⟨h1, h2⟩; exact hx ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 h1,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 h2⟩)
    (by rintro ⟨h1, h2⟩; exact hy ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 h1,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 h2⟩)
  rintro ⟨h1, h2⟩
  refine key ⟨?_, ?_⟩
  · have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (x.re * y.re + 2 * x.im * y.im) 3).2 h1
    push_cast at h ⊢
    linear_combination h
  · have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (x.re * y.im + x.im * y.re) 3).2 h2
    push_cast at h ⊢
    linear_combination h

/-- Auxiliary: 3 is not a unit multiple in ℤ[√2]. -/
private lemma three_not_dvd_one : ¬ (3 : R2) ∣ 1 := by
  rw [three_dvd_iff]; simp

/-- E3a. The thirty legal junctions have unit mesh scalars. After E2a and
unfolding the dot product this is a finite computation; `decide` per case
(destructure both generators). -/
theorem mesh_unit (g h : Rot) (hgh : h ≠ g.inv) :
    ¬ (3 : R2) ∣ (rowR g ⬝ᵥ colR h) := by
  rw [three_dvd_iff]
  revert hgh
  cases g <;> cases h <;>
    simp [rowR, colR, Rot.inv, dotProduct, Fin.sum_univ_three]

/-- E3b. Sanity: at a forbidden junction the mesh scalar IS divisible by 3
(indeed it is 9 or −7+16 = 9-adjacent; the six cases give ±9). This lemma is
not used by E6 but certifies that the meshing criterion is sharp. -/
theorem mesh_inv (g : Rot) : (3 : R2) ∣ (rowR g ⬝ᵥ colR (g.inv)) := by
  rw [three_dvd_iff]
  cases g <;>
    simp [rowR, colR, Rot.inv, dotProduct, Fin.sum_univ_three]

/-- E4. Every column and row vector has an entry that is not a multiple of 3
(the entry 1 at the first moving slot). Decidable existentials over `Fin 3`. -/
theorem colR_unit (g : Rot) : ∃ i, ¬ (3 : R2) ∣ colR g i := by
  cases g
  · exact ⟨1, by rw [three_dvd_iff]; simp [colR]⟩
  · exact ⟨1, by rw [three_dvd_iff]; simp [colR]⟩
  · exact ⟨0, by rw [three_dvd_iff]; simp [colR]⟩
  · exact ⟨0, by rw [three_dvd_iff]; simp [colR]⟩
  · exact ⟨0, by rw [three_dvd_iff]; simp [colR]⟩
  · exact ⟨0, by rw [three_dvd_iff]; simp [colR]⟩
theorem rowR_unit (g : Rot) : ∃ j, ¬ (3 : R2) ∣ rowR g j := by
  cases g
  · exact ⟨1, by rw [three_dvd_iff]; simp [rowR]⟩
  · exact ⟨1, by rw [three_dvd_iff]; simp [rowR]⟩
  · exact ⟨0, by rw [three_dvd_iff]; simp [rowR]⟩
  · exact ⟨0, by rw [three_dvd_iff]; simp [rowR]⟩
  · exact ⟨0, by rw [three_dvd_iff]; simp [rowR]⟩
  · exact ⟨0, by rw [three_dvd_iff]; simp [rowR]⟩

/-- Auxiliary: `Reduced3` unfolded to the non-deprecated `List.IsChain`. -/
private theorem reduced3_isChain (σ : Word3) :
    Reduced3 σ ↔ List.IsChain (fun x y : Rot => y ≠ x.inv) σ := Iff.rfl

/-- Auxiliary: the evaluation is multiplicative on concatenation. -/
private theorem evalR_append (σ τ : Word3) : evalR (σ ++ τ) = evalR σ * evalR τ := by
  simp [evalR, List.map_append, List.prod_append]

/-- Auxiliary: the evaluation of a one-letter word. -/
private theorem evalR_single (g : Rot) : evalR [g] = genR g := by
  simp [evalR]

/-- Auxiliary: the outer-product product rule. -/
private theorem outer_mul_outer (c v w x : Fin 3 → R2) :
    vecMulVec c v * vecMulVec w x = (v ⬝ᵥ w) • vecMulVec c x := by
  rw [Matrix.vecMulVec_mul_vecMulVec]
  refine Matrix.ext fun i j => ?_
  simp [Matrix.vecMulVec, mul_comm, mul_assoc]

/-- Auxiliary: E5, with the last letter carried as an explicit parameter so
that the reverse recursion has no dependent-proof bookkeeping. -/
private theorem evalR_decomp_aux : ∀ (τ : Word3) (g l : Rot), Reduced3 (g :: τ) →
    (g :: τ).getLast? = some l →
    ∃ (u : R2) (E : Matrix (Fin 3) (Fin 3) R2),
      ¬ (3 : R2) ∣ u ∧
      evalR (g :: τ) = u • vecMulVec (colR g) (rowR l) + (3 : R2) • E := by
  intro τ
  induction τ using List.reverseRecOn with
  | nil =>
      intro g l _ hl
      simp only [List.getLast?_singleton, Option.some_inj] at hl
      subst hl
      exact ⟨1, defR g, three_not_dvd_one, by rw [evalR_single, genR_decomp]; simp⟩
  | append_singleton τ' k ih =>
      intro g l hred hl
      have hlk : l = k := by
        rw [← List.cons_append, List.getLast?_append_of_ne_nil _ (by simp)] at hl
        simpa using hl.symm
      subst hlk
      rw [← List.cons_append] at hred ⊢
      obtain ⟨l', hl'⟩ : ∃ l', (g :: τ').getLast? = some l' :=
        ⟨_, List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil _ _)⟩
      have hsplit := (List.isChain_append (R := fun x y : Rot => y ≠ x.inv)).1 hred
      have hjunc : l ≠ l'.inv := hsplit.2.2 l' hl' l (by simp)
      obtain ⟨u, E, hu, hE⟩ := ih g l' hsplit.1 hl'
      refine ⟨u * (rowR l' ⬝ᵥ colR l),
        u • (vecMulVec (colR g) (rowR l') * defR l) + E * vecMulVec (colR l) (rowR l)
          + (3 : R2) • (E * defR l),
        three_prime_mul hu (mesh_unit l' l hjunc), ?_⟩
      rw [evalR_append, evalR_single, hE, genR_decomp l]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, outer_mul_outer]
      module

/-- E5 — the structure theorem. Along every nonempty reduced word the product
is a unit multiple of the outer product of the first column with the last row,
modulo 3. Route: reverse recursion on τ (`List.reverseRecOn`): the base is E1
for `[g]` with `u = 1`; the append step multiplies by `genR h` on the right,
expands both factors by the decomposition, and collects
  (u • vecMulVec C R + 3E)(vecMulVec C' R' + 3D')
    = (u * (R ⬝ᵥ C')) • vecMulVec C R' + 3 • (…),
using `Matrix.vecMulVec_mul_vecMulVec` (or prove the outer-product product
rule privately: `vecMulVec u v * vecMulVec u' v' = (v ⬝ᵥ u') • vecMulVec u v'`).
The new scalar is a non-multiple of 3 by `mesh_unit` (the junction is legal by
reducedness) and `three_prime_mul`. Mind the getLast bookkeeping:
`(σ ++ [h]).getLast _ = h` and reducedness of the prefix from
`List.Chain'` append facts. -/
theorem evalR_decomp (g : Rot) (τ : Word3) (h : Reduced3 (g :: τ)) :
    ∃ (u : R2) (E : Matrix (Fin 3) (Fin 3) R2),
      ¬ (3 : R2) ∣ u ∧
      evalR (g :: τ)
        = u • vecMulVec (colR g) (rowR ((g :: τ).getLast (by simp)))
          + (3 : R2) • E :=
  evalR_decomp_aux τ g _ h (List.getLast?_eq_getLast_of_ne_nil _)

/-- E6 — MAIN THEOREM (paper Theorem 6.6): the three rotations generate a free
group of rank three; no nonempty reduced word is the scaled identity. Route:
suppose equality; by E5,
  u • vecMulVec (colR g) (rowR l) = (3)^n • 1 − 3 • E = 3 • (…) for n ≥ 1,
so every entry of the left side is divisible by 3; evaluate at the indices
provided by E4 and cancel with `three_prime_mul` twice to conclude 3 ∣ u,
contradiction. -/
theorem rank3_free (g : Rot) (τ : Word3) (h : Reduced3 (g :: τ)) :
    evalR (g :: τ) ≠ ((3 : R2) ^ (g :: τ).length) • (1 : Matrix (Fin 3) (Fin 3) R2) := by
  intro heq
  obtain ⟨u, E, hu, hE⟩ := evalR_decomp g τ h
  obtain ⟨i, hi⟩ := colR_unit g
  obtain ⟨j, hj⟩ := rowR_unit ((g :: τ).getLast (by simp))
  have hent := congrFun (congrFun (hE.symm.trans heq) i) j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul] at hent
  have hdvd : (3 : R2) ∣ u * colR g i * rowR ((g :: τ).getLast (by simp)) j := by
    refine ⟨(3 : R2) ^ τ.length * (1 : Matrix (Fin 3) (Fin 3) R2) i j - E i j, ?_⟩
    have hlen : ((g :: τ).length) = τ.length + 1 := rfl
    rw [hlen, pow_succ] at hent
    linear_combination hent
  exact three_prime_mul (three_prime_mul hu hi) hj hdvd

/-- The embedding of the Round-2 alphabet into the rank-three alphabet. -/
def emb : Letter → Rot
  | .a => .a | .A => .A | .b => .b | .B => .B

/-- E7a. The embedding matches the matrices. Four cases; `rfl` or `decide`. -/
theorem genR_emb (c : Letter) : genR (emb c) = genM c := by
  cases c <;> rfl

/-- E7b — cross-validation: Świerczkowski's theorem for the pair, re-derived
from rank-three freeness, in exactly the shape of Round 2's
`swierczkowski_free`. Transport reducedness (emb is injective and commutes
with formal inversion) and the evaluation (`List.map_map`, E7a), then apply E6.
The ledger thereby contains two independent machine-checked proofs of the
freeness of the pair. -/
theorem swierczkowski_free' (c : Letter) (τ : Word) (h : Reduced (c :: τ)) :
    evalM (c :: τ) ≠ ((3 : R2) ^ (c :: τ).length) • (1 : Matrix (Fin 3) (Fin 3) R2) := by
  have hembinv : ∀ d : Letter, emb d.inv = (emb d).inv := by intro d; cases d <;> rfl
  have hembinj : Function.Injective emb := by intro d e hde; cases d <;> cases e <;> simp_all [emb]
  have hmap : ∀ σ : Word, evalR (σ.map emb) = evalM σ := by
    intro σ
    simp only [evalR, evalM, List.map_map]
    congr 1
    exact List.map_congr_left fun d _ => genR_emb d
  have hred3 : Reduced3 (emb c :: τ.map emb) := by
    rw [show emb c :: τ.map emb = (c :: τ).map emb from rfl, reduced3_isChain, List.isChain_map]
    refine List.IsChain.imp (R := fun d e : Letter => e ≠ d.inv) ?_ h
    intro d e hde hcon
    exact hde (hembinj (by rw [hcon, hembinv]))
  intro heq
  refine rank3_free (emb c) (τ.map emb) hred3 ?_
  rw [show emb c :: τ.map emb = (c :: τ).map emb from rfl, hmap, List.length_map, heq]

/-! ## Module F: the classes-count capstone (paper Theorem 6.2, counting side) -/

/-- The symmetric reduced words of type (m,n), as a Finset. -/
def SFin (m n : ℕ) : Finset Word :=
  ((allWords (2*m + n)).filter (fun σ =>
      decide (IsSym σ) && decide (Reduced σ)
        && (alphaCount σ == 2*m) && (betaCount σ == n))).toFinset

/-- Auxiliary: the two letter counts partition the length. -/
private theorem counts_add_length (σ : Word) : alphaCount σ + betaCount σ = σ.length := by
  induction σ with
  | nil => rfl
  | cons c t ih =>
      simp only [alphaCount, betaCount] at ih
      cases c <;> simp [alphaCount, betaCount] <;> omega

/-- F0a. Membership unfolds to the four conditions (the length condition is
implied via `mem_allWords`). -/
theorem mem_SFin {m n : ℕ} {σ : Word} :
    σ ∈ SFin m n ↔ IsSym σ ∧ Reduced σ ∧ alphaCount σ = 2*m ∧ betaCount σ = n := by
  rw [SFin, List.mem_toFinset, List.mem_filter, mem_allWords]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨-, ⟨⟨hs, hr⟩, ha⟩, hb⟩
    exact ⟨hs, hr, ha, hb⟩
  · rintro ⟨hs, hr, ha, hb⟩
    refine ⟨?_, ⟨⟨hs, hr⟩, ha⟩, hb⟩
    rw [← counts_add_length σ, ha, hb]

/-- F0b. The Finset counts what the enumerator counts. The filtered list is
nodup by `nodup_allWords` and `List.Nodup.filter`, so `toFinset` preserves
length. -/
theorem SFin_card (m n : ℕ) : (SFin m n).card = censusCount m n :=
  List.toFinset_card_of_nodup ((nodup_allWords _).filter _)

/-- F1. ι_β preserves the symmetry class. Letterwise: ι_α and ι_β commute and
`Letter.ib` commutes with `Letter.ia`; then `List.map_map`, `List.map_reverse`.
(A commutation lemma `∀ c, (c.ib).ia = (c.ia).ib` by `cases c <;> rfl` is the
kernel.) -/
theorem isSym_ibMap (σ : Word) : IsSym (σ.map Letter.ib) ↔ IsSym σ := by
  have hcomm : ∀ c : Letter, (c.ib).ia = (c.ia).ib := by intro c; cases c <;> rfl
  have hinj : Function.Injective (List.map Letter.ib) :=
    List.map_injective_iff.2 (fun c d hcd => by cases c <;> cases d <;> simp_all [Letter.ib])
  have hkey : (σ.map Letter.ib).reverse.map Letter.ia
      = (σ.reverse.map Letter.ia).map Letter.ib := by
    simp only [List.map_reverse, List.map_map]
    exact congrArg List.reverse (List.map_congr_left fun c _ => hcomm c)
  rw [IsSym, IsSym, hkey]
  exact ⟨fun h => hinj h, fun h => by rw [h]⟩

/-- F2. SFin is closed under ι_β. F0a, F1, Round 2's `reduced_ibMap` and the
count lemmas `alphaCount_ibMap`, `betaCount_ibMap`. -/
theorem ibMap_mem_SFin {m n : ℕ} {σ : Word} (hσ : σ ∈ SFin m n) :
    σ.map Letter.ib ∈ SFin m n := by
  rw [mem_SFin] at hσ ⊢
  exact ⟨(isSym_ibMap σ).2 hσ.1, (reduced_ibMap σ).2 hσ.2.1,
    (alphaCount_ibMap σ).trans hσ.2.2.1, (betaCount_ibMap σ).trans hσ.2.2.2⟩

/-- The sign-equivalence class of a word: its ι_β-orbit, as a two-element
Finset. -/
def orbit (σ : Word) : Finset Word := {σ, σ.map Letter.ib}

/-- The number of sign-equivalence classes of type (m,n). -/
def numClasses (m n : ℕ) : ℕ := ((SFin m n).image orbit).card

/-- F3a. Orbits of members are genuine pairs. `ibMap_ne_self` (Round 3) with
nonemptiness from `betaCount σ = n ≥ 1`; `Finset.card_pair`. -/
theorem orbit_card {m n : ℕ} (hn : 1 ≤ n) {σ : Word} (hσ : σ ∈ SFin m n) :
    (orbit σ).card = 2 := by
  rw [mem_SFin] at hσ
  obtain ⟨hs, hr, -, hb⟩ := hσ
  have hne : σ ≠ [] := by
    rintro rfl
    rw [show betaCount [] = 0 from rfl] at hb
    omega
  exact Finset.card_pair (Ne.symm (ibMap_ne_self hs hr hne))

/-- F3b. Membership in an orbit determines the orbit. Two cases; the second
uses `List.map_map` and `ib_ib` (Round 2) to compute the double image, and
`Finset.pair_comm`. -/
theorem orbit_eq_of_mem {σ τ : Word} (h : τ ∈ orbit σ) : orbit τ = orbit σ := by
  have hdouble : (σ.map Letter.ib).map Letter.ib = σ := by
    rw [List.map_map]
    refine (List.map_congr_left fun c _ => ib_ib c).trans (List.map_id _)
  rcases Finset.mem_insert.1 h with rfl | h'
  · rfl
  · rw [Finset.mem_singleton] at h'
    subst h'
    rw [orbit, orbit, hdouble, Finset.pair_comm]

/-- F4. The census is twice the number of classes. Route: SFin is the disjoint
union of the distinct orbits: `Finset.biUnion` over `(SFin m n).image orbit`
of `id` equals `SFin m n` (every σ lies in its own orbit; orbits of members
stay inside by F2), the orbits are pairwise disjoint (two orbits sharing an
element are equal by F3b), and each has cardinality 2 (F3a). Conclude with
`Finset.card_biUnion`. -/
theorem card_SFin_eq_two_mul (m n : ℕ) (hn : 1 ≤ n) :
    (SFin m n).card = 2 * numClasses m n := by
  have hmem : ∀ σ : Word, σ ∈ orbit σ := fun σ => Finset.mem_insert_self _ _
  have hcover : ((SFin m n).image orbit).biUnion id = SFin m n := by
    ext τ
    simp only [Finset.mem_biUnion, Finset.mem_image, id]
    constructor
    · rintro ⟨o, ⟨σ, hσ, rfl⟩, hτ⟩
      rcases Finset.mem_insert.1 hτ with rfl | hτ'
      · exact hσ
      · rw [Finset.mem_singleton] at hτ'
        subst hτ'
        exact ibMap_mem_SFin hσ
    · intro hτ
      exact ⟨orbit τ, ⟨τ, hτ, rfl⟩, hmem τ⟩
  have hdisj : ∀ o ∈ (SFin m n).image orbit, ∀ o' ∈ (SFin m n).image orbit,
      o ≠ o' → Disjoint (id o) (id o') := by
    intro o ho o' ho' hne
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 ho
    obtain ⟨σ', -, rfl⟩ := Finset.mem_image.1 ho'
    simp only [id]
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact hne ((orbit_eq_of_mem hx).symm.trans (orbit_eq_of_mem hx'))
  calc (SFin m n).card
      = (((SFin m n).image orbit).biUnion id).card := by rw [hcover]
    _ = ∑ o ∈ (SFin m n).image orbit, (id o).card := Finset.card_biUnion hdisj
    _ = ∑ _o ∈ (SFin m n).image orbit, 2 := by
        refine Finset.sum_congr rfl ?_
        rintro o ho
        obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 ho
        exact orbit_card hn hσ
    _ = 2 * numClasses m n := by rw [Finset.sum_const, numClasses, smul_eq_mul, mul_comm]

/-- F5 — CAPSTONE (paper Theorem 6.2, counting sentence): the number of
sign-equivalence classes of identities of type (m,n) is R(m, ⌈n/2⌉−1).
Assemble F0b, F4, Round 2's `censusCount_eq`, and cancel the factor 2. -/
theorem numClasses_eq (m n : ℕ) (hn : 1 ≤ n) :
    numClasses m n = Rc m ((n - 1) / 2) := by
  refine Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) ?_
  rw [← card_SFin_eq_two_mul m n hn, SFin_card, censusCount_eq m n hn]

/-- F6 — the semantics bridge: two members of SFin lie in the same orbit
exactly when their generic quaternion evaluations differ by the sign-
equivalence alternative of Round 3's `sign_classification`. Forward: orbit
equality gives σ' ∈ orbit σ (σ' lies in its own orbit), i.e. σ' = σ or
σ' = σ.map ib, and each alternative is one disjunct (by `rfl` and reflexivity).
Backward: `sign_classification` (hypotheses from F0a) gives σ' = σ or
σ' = σ.map ib, then F3b. This theorem is what entitles `numClasses` to its
name. -/
theorem orbit_eq_iff_sign {m n : ℕ} {σ σ' : Word}
    (hσ : σ ∈ SFin m n) (hσ' : σ' ∈ SFin m n) :
    orbit σ' = orbit σ
      ↔ (hWgen σ' = hWgen σ ∨ hWgen σ' = -hWgen σ ∨
         hWgen σ' = hWgen (σ.map Letter.ib) ∨ hWgen σ' = -hWgen (σ.map Letter.ib)) := by
  obtain ⟨hs, hr, -, -⟩ := mem_SFin.1 hσ
  obtain ⟨hs', hr', -, -⟩ := mem_SFin.1 hσ'
  rw [sign_classification hs hr hs' hr']
  constructor
  · intro h
    have : σ' ∈ orbit σ := h ▸ Finset.mem_insert_self _ _
    rcases Finset.mem_insert.1 this with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Finset.mem_singleton.1 h')
  · rintro (rfl | rfl)
    · rfl
    · exact orbit_eq_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-! ### Axiom audit -/

#print axioms genR_decomp
#print axioms three_dvd_iff
#print axioms three_prime_mul
#print axioms mesh_unit
#print axioms mesh_inv
#print axioms colR_unit
#print axioms rowR_unit
#print axioms evalR_decomp
#print axioms rank3_free
#print axioms genR_emb
#print axioms swierczkowski_free'
#print axioms mem_SFin
#print axioms SFin_card
#print axioms isSym_ibMap
#print axioms ibMap_mem_SFin
#print axioms orbit_card
#print axioms orbit_eq_of_mem
#print axioms card_SFin_eq_two_mul
#print axioms numClasses_eq
#print axioms orbit_eq_iff_sign

end ThreeSquares
