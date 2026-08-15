/-
Round 2 — Census bijection and Świerczkowski freeness, for
"Polynomial identities, sums of three squares, and quaternionic (anti-)automorphisms"
(D. V. Feldman, University of New Hampshire).

This file imports Round1.lean, which is the CLOSED Round-1 artifact; it is
frozen — do not modify it in any way. All definitions below are final; every
`sorry` is commissioned. If a statement fails as written, REPORT it and move
on — do not repair. Private auxiliary lemmas may be added freely.

Closure criterion per theorem: compiles, and `#print axioms` shows at most
propext, Classical.choice, Quot.sound. The two theorems marked NATIVE may
additionally use Lean.ofReduceBool; prefer plain `decide` where feasible and
report which was used. All other theorems: no axiom exceptions.

Every theorem statement below has been certified numerically prior to
commissioning: the count identities on the ranges stated in the work order,
the invariant exhaustively over residues mod 9, the freeness statement on all
13120 reduced words of length ≤ 8, and the bisection on all 160 symmetric
reduced words of length ≤ 8. If one resists proof, suspect the proof route,
not the statement — and then report.
-/
import Round1

open Quaternion

namespace ThreeSquares

/-! ## Module A: the census bijection  `censusCount m n = 2 * Rc m ((n-1)/2)` -/

/-! ### A0: enumeration infrastructure -/

/-- A0a. Membership in the enumerator is exactly a length condition.
Induction on ℓ; `List.mem_flatMap`, `List.mem_map`. -/
theorem mem_allWords (ℓ : ℕ) (σ : Word) : σ ∈ allWords ℓ ↔ σ.length = ℓ := by
  induction ℓ generalizing σ with
  | zero => simp [allWords, List.length_eq_zero_iff]
  | succ n ih =>
      cases σ with
      | nil => simp [allWords]
      | cons c w =>
          simp only [allWords, List.mem_flatMap, List.mem_map, ih, List.length_cons,
            Nat.add_right_cancel_iff]
          constructor
          · rintro ⟨w', hw', c', -, h⟩
            cases h; exact hw'
          · intro h
            exact ⟨w, h, c, by cases c <;> simp, rfl⟩

/-- A0b. The enumerator has no duplicates. Induction on ℓ: the four cons maps
are injective with disjoint ranges (distinct head letters). -/
theorem nodup_allWords (ℓ : ℕ) : (allWords ℓ).Nodup := by
  induction ℓ with
  | zero => simp [allWords]
  | succ n ih =>
      rw [allWords, List.nodup_flatMap]
      refine ⟨fun w _ => by simp, ih.imp ?_⟩
      intro w w' hne
      simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_cons]
      rintro x ⟨c, -, rfl⟩ ⟨c', -, h⟩
      exact hne (by injection h with _ h2; exact h2.symm)

/-! ### A1: letter and word symmetries -/

/-- A1a. Letter algebra: the involutions commute with formal inversion.
All by `cases c <;> rfl`. -/
theorem ia_ia (c : Letter) : c.ia.ia = c := by cases c <;> rfl
theorem ib_ib (c : Letter) : c.ib.ib = c := by cases c <;> rfl
theorem inv_inv (c : Letter) : c.inv.inv = c := by cases c <;> rfl
theorem ia_inv (c : Letter) : c.inv.ia = c.ia.inv := by cases c <;> rfl
theorem ib_inv (c : Letter) : c.inv.ib = c.ib.inv := by cases c <;> rfl

/-- Auxiliary (added): `Reduced` unfolded to the non-deprecated `List.IsChain`,
so that the `IsChain` rewriting API applies. -/
private theorem reduced_isChain (σ : Word) :
    Reduced σ ↔ List.IsChain (fun c d => d ≠ c.inv) σ := Iff.rfl

/-- A1b. The mirror map w ↦ ι_α(ρ(w)) preserves reducedness. Via
`List.chain'_reverse` and `List.chain'_map`, using `ia_inv` and `ia_ia`. -/
theorem reduced_mirror (w : Word) :
    Reduced (w.reverse.map Letter.ia) ↔ Reduced w := by
  rw [reduced_isChain, reduced_isChain, List.isChain_map, List.isChain_reverse]
  constructor <;> intro h <;>
    exact h.imp (fun {x y} hxy => by revert hxy; cases x <;> cases y <;> decide)

/-- A1c. Letterwise involutions and reversal preserve the letter counts.
`List.countP_map`, `List.countP_reverse`, and a case check on letters. -/
theorem alphaCount_mirror (w : Word) :
    alphaCount (w.reverse.map Letter.ia) = alphaCount w := by
  simp only [alphaCount, List.countP_map, List.countP_reverse]
  congr 1
  funext c
  cases c <;> rfl
theorem betaCount_mirror (w : Word) :
    betaCount (w.reverse.map Letter.ia) = betaCount w := by
  simp only [betaCount, List.countP_map, List.countP_reverse]
  congr 1
  funext c
  cases c <;> rfl
theorem alphaCount_ibMap (w : Word) :
    alphaCount (w.map Letter.ib) = alphaCount w := by
  simp only [alphaCount, List.countP_map]
  congr 1
  funext c
  cases c <;> rfl
theorem betaCount_ibMap (w : Word) :
    betaCount (w.map Letter.ib) = betaCount w := by
  simp only [betaCount, List.countP_map]
  congr 1
  funext c
  cases c <;> rfl
theorem reduced_ibMap (w : Word) :
    Reduced (w.map Letter.ib) ↔ Reduced w := by
  rw [reduced_isChain, reduced_isChain, List.isChain_map]
  constructor <;> intro h <;>
    exact h.imp (fun {x y} hxy => by revert hxy; cases x <;> cases y <;> decide)

/-! ### A2: the bisection -/

/-- The middle block: p copies of β (pos = true) or β⁻¹ (pos = false). -/
def midWord (pos : Bool) (p : ℕ) : Word :=
  List.replicate p (if pos then Letter.b else Letter.B)

/-- Assemble a symmetric word from its left half, middle sign, and middle
length. -/
def encode (pos : Bool) (p : ℕ) (w : Word) : Word :=
  w ++ midWord pos p ++ (w.reverse.map Letter.ia)

/-- A2a. Encoded words are symmetric, for every w and p.
Unfold `IsSym`; `List.reverse_append`, `List.map_append`, `ia_ia`;
the middle block is ι_α-fixed and palindromic. -/
theorem isSym_encode (pos : Bool) (p : ℕ) (w : Word) :
    IsSym (encode pos p w) := by
  have hmid : (midWord pos p).reverse.map Letter.ia = midWord pos p := by
    simp only [midWord, List.reverse_replicate, List.map_replicate]
    cases pos <;> rfl
  simp only [IsSym, encode, List.reverse_append, List.map_append, hmid,
    List.map_reverse, List.reverse_reverse, List.map_map, List.append_assoc]
  congr 1
  simp [Function.comp_def, ia_ia]

/-- A2b. Encoded words are reduced, given a reduced left half whose last
letter respects the junction. Chain analysis at the two junctions: the
condition `w.getLast? ≠ some β^{-sign}` handles both, since ι_α fixes
β-letters and moves α-letters to α-letters. -/
theorem reduced_encode (pos : Bool) (p : ℕ) (hp : p = 1 ∨ p = 2) (w : Word)
    (hw : Reduced w)
    (hlast : w.getLast? ≠ some (if pos then Letter.B else Letter.b)) :
    Reduced (encode pos p w) := by
  set x : Letter := if pos then Letter.b else Letter.B with hxdef
  have hmid : List.IsChain (fun c d => d ≠ c.inv) (midWord pos p) ∧
      (midWord pos p).head? = some x ∧ (midWord pos p).getLast? = some x := by
    rcases hp with rfl | rfl <;>
      refine ⟨?_, ?_, ?_⟩ <;>
      simp [midWord, ← hxdef, List.replicate] <;> cases pos <;> decide
  obtain ⟨hmc, hmh, hml⟩ := hmid
  have hmne : midWord pos p ≠ [] := by
    intro h; rw [h] at hmh; simp at hmh
  have hheadmirror : (w.reverse.map Letter.ia).head? = (w.getLast?).map Letter.ia := by
    rw [List.head?_map, List.head?_reverse]
  rw [reduced_isChain] at hw ⊢
  rw [encode, List.isChain_append, List.isChain_append]
  refine ⟨⟨hw, hmc, ?_⟩, (reduced_mirror w).2 (by rwa [reduced_isChain]), ?_⟩
  · intro u hu v hv
    rw [hmh] at hv
    cases hv
    intro hcon
    apply hlast
    rw [Option.mem_def] at hu
    rw [hu]
    congr 1
    cases pos <;> cases u <;> simp_all [Letter.inv]
  · intro u hu v hv
    rw [List.getLast?_append_of_ne_nil _ hmne, hml] at hu
    cases hu
    rw [hheadmirror] at hv
    obtain ⟨a', ha', rfl⟩ := Option.mem_map.1 hv
    intro hcon
    apply hlast
    rw [Option.mem_def] at ha'
    rw [ha']
    congr 1
    cases pos <;> cases a' <;> simp_all [Letter.inv, Letter.ia]

/-- A2c. Counts of an encoded word. `List.countP_append` plus A1c. -/
theorem counts_encode (pos : Bool) (p : ℕ) (w : Word) :
    alphaCount (encode pos p w) = 2 * alphaCount w ∧
    betaCount (encode pos p w) = 2 * betaCount w + p := by
  have ha : alphaCount (midWord pos p) = 0 := by
    simp only [midWord, alphaCount, List.countP_replicate]
    cases pos <;> simp
  have hb : betaCount (midWord pos p) = p := by
    simp only [midWord, betaCount, List.countP_replicate]
    cases pos <;> simp
  constructor
  · show List.countP _ _ = _
    simp only [encode, List.countP_append]
    have := alphaCount_mirror w
    simp only [alphaCount] at this ha ⊢
    omega
  · show List.countP _ _ = _
    simp only [encode, List.countP_append]
    have := betaCount_mirror w
    simp only [betaCount] at this hb ⊢
    omega

/-- Auxiliary: the empty word is reduced. -/
private lemma reduced_nil : Reduced [] := (reduced_isChain []).2 (by simp)

/-- Auxiliary: reducedness of a word with one letter prepended. -/
private lemma reduced_cons (c : Letter) (rest : Word) :
    Reduced (c :: rest) ↔ (Reduced rest ∧ ∀ y ∈ rest.head?, y ≠ c.inv) := by
  rw [reduced_isChain, reduced_isChain, show c :: rest = [c] ++ rest from rfl,
    List.isChain_append]
  simp

/-- Auxiliary: a prefix of a reduced word is reduced. -/
private lemma reduced_append (l₁ l₂ : Word) (h : Reduced (l₁ ++ l₂)) : Reduced l₁ :=
  (List.isChain_append.1 ((reduced_isChain _).1 h)).1

/-- Auxiliary: the last letter of a cons, when the tail is nonempty. -/
private lemma getLast?_cons_ne_nil (c : Letter) (w : Word) (h : w ≠ []) :
    (c :: w).getLast? = w.getLast? := by
  cases w with
  | nil => simp at h
  | cons d t => simp [List.getLast?_cons, Option.getD]

/-- Auxiliary: the bisection, by the Round-1 strip induction on the length. -/
private lemma bisection_aux : ∀ (n : ℕ) (σ : Word), σ.length ≤ n → IsSym σ → Reduced σ → σ ≠ [] →
    ∃ (pos : Bool) (p : ℕ) (w : Word),
      (p = 1 ∨ p = 2) ∧ σ = encode pos p w ∧ Reduced w ∧
      w.getLast? ≠ some (if pos then Letter.B else Letter.b) := by
  intro n
  induction n with
  | zero => intro σ hl _ _ hne; exact absurd (List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)) hne
  | succ n ih =>
      intro σ hl hsym hred hne
      rcases isSym_strip hsym with rfl | ⟨c, rfl, hc⟩ | ⟨c, σ', rfl, hσ'⟩
      · exact absurd rfl hne
      · refine ⟨c == Letter.b, 1, [], Or.inl rfl, ?_, reduced_nil, by simp⟩
        cases c <;> simp_all [encode, midWord, Letter.ia]
      · by_cases hnil : σ' = []
        · subst hnil
          have h2 : Reduced [c, c.ia] := by simpa using hred
          have hcc : c.ia ≠ c.inv := (List.isChain_cons_cons.1 ((reduced_isChain _).1 h2)).1
          refine ⟨c == Letter.b, 2, [], Or.inr rfl, ?_, reduced_nil, by simp⟩
          cases c <;> simp_all [encode, midWord, Letter.ia, Letter.inv]
        · have hlen : σ'.length ≤ n := by simp at hl; omega
          obtain ⟨hrest, hhead⟩ := (reduced_cons c (σ' ++ [c.ia])).1 hred
          have hred' : Reduced σ' := reduced_append _ _ hrest
          obtain ⟨pos, p, w, hp, heq, hwred, hwlast⟩ := ih σ' hlen hσ' hred' hnil
          refine ⟨pos, p, c :: w, hp, ?_, ?_, ?_⟩
          · rw [heq]; simp [encode, List.append_assoc]
          · rw [reduced_cons]
            refine ⟨hwred, ?_⟩
            intro y hy
            apply hhead
            rw [heq]
            simp only [encode, List.append_assoc, List.head?_append]
            cases w with
            | nil => simp at hy
            | cons d t => simpa using hy
          · by_cases hw : w = []
            · subst hw
              simp only [List.getLast?_singleton]
              intro hcon
              have hh : (σ' ++ [c.ia]).head? = some (if pos then Letter.b else Letter.B) := by
                rw [heq]
                rcases hp with rfl | rfl <;> simp [encode, midWord, List.replicate]
              have hne' := hhead (if pos then Letter.b else Letter.B) (by rw [hh]; rfl)
              apply hne'
              rw [Option.some_inj] at hcon
              cases pos <;> simp_all [Letter.inv]
            · rw [getLast?_cons_ne_nil c w hw]
              exact hwlast

/-- A2d — the substantial item of Module A. Every nonempty symmetric reduced
word decodes: it is an encoding, with middle length read off the parity of
the total length.

Route. First establish the positional form of symmetry:
`hσ : IsSym σ` gives `σ.get ⟨σ.length - 1 - i, _⟩ = (σ.get ⟨i, _⟩).ia`
for all `i` (from `List.get_reverse` and `List.get_map`). If `σ.length` is
odd, the middle letter is ι_α-fixed, hence a β-letter (`cases` on it); take
p = 1. If even, the two middle letters are `c` and `c.ia` and adjacent;
reducedness rules out α-letters (`c.ia = c.inv` for those), so both are the
same β-letter; take p = 2. Set `w := σ.take ((σ.length - p) / 2)` and prove
`σ = encode pos p w` by `List.ext_get`, splitting indices into the three
ranges and using the positional symmetry for the mirror range. Reducedness of
`w` is inherited (`List.IsPrefix.reduced`-style: a prefix of a reduced word is
reduced — prove as a private helper via `List.Chain'.prefix` or directly);
the junction condition on `w.getLast?` is read off reducedness of σ at the
junction. Nonemptiness of σ forces a middle to exist: a nonempty all-α
symmetric reduced word is impossible (odd length: middle would be ι_α-fixed;
even length: the middle pair would be `c, c.ia = c.inv`). -/
theorem bisection_exists {σ : Word} (h1 : IsSym σ) (h2 : Reduced σ)
    (h3 : σ ≠ []) :
    ∃ (pos : Bool) (p : ℕ) (w : Word),
      (p = 1 ∨ p = 2) ∧ σ = encode pos p w ∧ Reduced w ∧
      w.getLast? ≠ some (if pos then Letter.B else Letter.b) :=
  bisection_aux σ.length σ le_rfl h1 h2 h3

/-- A2e. Encodings are injective in all three arguments (given p, p' ∈ {1,2}).
Lengths determine p from parity; the letter at the middle position
determines pos; then `w` is the take of the common word. -/
theorem encode_inj {pos pos' : Bool} {p p' : ℕ} {w w' : Word}
    (hp : p = 1 ∨ p = 2) (hp' : p' = 1 ∨ p' = 2)
    (h : encode pos p w = encode pos' p' w') :
    pos = pos' ∧ p = p' ∧ w = w' := by
  have hlen := congrArg List.length h
  simp only [encode, midWord, List.length_append, List.length_replicate, List.length_map,
    List.length_reverse] at hlen
  have hpp : p = p' := by rcases hp with rfl | rfl <;> rcases hp' with rfl | rfl <;> omega
  subst hpp
  have hwlen : w.length = w'.length := by omega
  rw [encode, encode, List.append_assoc, List.append_assoc] at h
  obtain ⟨hw, hrest⟩ := List.append_inj h hwlen
  subst hw
  refine ⟨?_, rfl, rfl⟩
  have hmid : midWord pos p = midWord pos' p := List.append_cancel_right hrest
  rcases hp with rfl | rfl <;> (cases pos <;> cases pos' <;> simp_all [midWord])

/-! ### Auxiliary counting infrastructure (added, not commissioned)

The refined counts of §A3 are lengths of filtered enumerations, i.e. `countP`
over `allWords`. The lemmas below provide the three moves used throughout:
transport along a letterwise involution, transport along appending a last
letter, and the partition of a count by the value of `getLast?`. -/

/-- A letterwise involution permutes the enumeration of words of a given
length. -/
private lemma perm_map_allWords (f : Letter → Letter) (hf : ∀ c, f (f c) = c) (ℓ : ℕ) :
    ((allWords ℓ).map (List.map f)).Perm (allWords ℓ) := by
  have hinj : Function.Injective (List.map f) := by
    intro l₁ l₂ h
    have := congrArg (List.map f) h
    simpa [List.map_map, Function.comp_def, hf] using this
  refine (List.perm_ext_iff_of_nodup ((nodup_allWords ℓ).map hinj) (nodup_allWords ℓ)).mpr ?_
  intro w
  simp only [List.mem_map, mem_allWords]
  constructor
  · rintro ⟨w', hw', rfl⟩; simpa using hw'
  · intro hw
    exact ⟨w.map f, by simpa using hw, by simp [List.map_map, Function.comp_def, hf]⟩

/-- Appending a fixed last letter is a bijection from the words of length `n`
onto the words of length `n+1` ending in that letter. -/
private lemma perm_append_allWords (c : Letter) (n : ℕ) :
    ((allWords n).map (fun w => w ++ [c])).Perm
      ((allWords (n+1)).filter (fun w => w.getLast? == some c)) := by
  have hinj : Function.Injective (fun w : Word => w ++ [c]) := by
    intro l₁ l₂ h; exact List.append_cancel_right h
  refine (List.perm_ext_iff_of_nodup ((nodup_allWords n).map hinj)
    ((nodup_allWords (n+1)).filter _)).mpr ?_
  intro w
  simp only [List.mem_map, List.mem_filter, mem_allWords, beq_iff_eq]
  constructor
  · rintro ⟨w', hw', rfl⟩
    exact ⟨by simp [hw'], by simp⟩
  · rintro ⟨hlen, hlast⟩
    have hne : w ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    refine ⟨w.dropLast, ?_, ?_⟩
    · have : w.dropLast.length = w.length - 1 := List.length_dropLast
      omega
    · have hg : w.getLast hne = c := by
        rw [List.getLast?_eq_some_getLast hne] at hlast
        exact Option.some_injective _ hlast
      rw [← hg]
      exact List.dropLast_append_getLast hne

/-- Reducedness of a word with one letter appended. -/
private lemma reduced_append_letter (w : Word) (c : Letter) :
    Reduced (w ++ [c]) ↔ (Reduced w ∧ w.getLast? ≠ some c.inv) := by
  rw [reduced_isChain, reduced_isChain, List.isChain_append]
  constructor
  · rintro ⟨h1, -, h3⟩
    refine ⟨h1, ?_⟩
    intro hl
    have := h3 c.inv (by rw [hl]; rfl) c (by simp)
    exact this (by cases c <;> rfl)
  · rintro ⟨h1, h2⟩
    refine ⟨h1, by simp, ?_⟩
    intro x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    intro hcon
    exact h2 (by rw [Option.mem_def] at hx; rw [hx, hcon]; cases x <;> rfl)

/-- Every letter is either an α-letter or a β-letter. -/
private lemma counts_length (w : Word) : alphaCount w + betaCount w = w.length := by
  induction w with
  | nil => rfl
  | cons c t ih =>
      simp only [alphaCount, betaCount, List.countP_cons, List.length_cons] at ih ⊢
      cases c <;> simp at ih ⊢ <;> omega

/-- The five-way partition of a count by the value of `getLast?`. -/
private lemma countP_last_partition (p : Word → Bool) (l : List Word) :
    l.countP p = l.countP (fun w => p w && (w.getLast? == none))
      + l.countP (fun w => p w && (w.getLast? == some Letter.a))
      + l.countP (fun w => p w && (w.getLast? == some Letter.A))
      + l.countP (fun w => p w && (w.getLast? == some Letter.b))
      + l.countP (fun w => p w && (w.getLast? == some Letter.B)) := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      simp only [List.countP_cons, ih]
      rcases hx : x.getLast? with _ | c
      · cases p x <;> simp <;> omega
      · cases c <;> cases p x <;> simp <;> omega

/-- Boolean bookkeeping for the "does not end in `e`" predicate. -/
private lemma and_not_last (X : Bool) (u : Option Letter) (e d : Letter) (hd : d ≠ e) :
    ((X && !(u == some e)) && (u == some d)) = (X && (u == some d)) := by
  revert hd
  cases u with
  | none => cases X <;> simp
  | some c => cases c <;> cases d <;> cases e <;> cases X <;> simp

private lemma and_not_last_none (X : Bool) (u : Option Letter) (e : Letter) :
    ((X && !(u == some e)) && (u == none)) = (X && (u == none)) := by
  cases u with
  | none => cases X <;> simp
  | some c => cases c <;> cases e <;> cases X <;> simp

private lemma and_not_last_self (X : Bool) (u : Option Letter) (e : Letter) :
    ((X && !(u == some e)) && (u == some e)) = false := by
  cases u with
  | none => cases X <;> simp
  | some c => cases c <;> cases e <;> cases X <;> simp

/-- Formal inversion of every letter preserves reducedness. -/
private lemma reduced_invMap (w : Word) : Reduced (w.map Letter.inv) ↔ Reduced w := by
  rw [reduced_isChain, reduced_isChain, List.isChain_map]
  constructor <;> intro h <;>
    exact h.imp (fun {x y} hxy => by revert hxy; cases x <;> cases y <;> decide)

private lemma alphaCount_invMap (w : Word) : alphaCount (w.map Letter.inv) = alphaCount w := by
  simp only [alphaCount, List.countP_map]
  congr 1
  funext c
  cases c <;> rfl

private lemma betaCount_invMap (w : Word) : betaCount (w.map Letter.inv) = betaCount w := by
  simp only [betaCount, List.countP_map]
  congr 1
  funext c
  cases c <;> rfl

/-- Transport of a count along a letterwise involution preserving reducedness
and the two letter counts. -/
private lemma count_transport (f : Letter → Letter) (hf : ∀ c, f (f c) = c)
    (hred : ∀ w : Word, Reduced (w.map f) ↔ Reduced w)
    (hα : ∀ w : Word, alphaCount (w.map f) = alphaCount w)
    (hβ : ∀ w : Word, betaCount (w.map f) = betaCount w)
    (g : Option Letter → Bool) (m k ℓ : ℕ) :
    (allWords ℓ).countP (fun w =>
        (decide (Reduced w) && (alphaCount w == m) && (betaCount w == k)) && g w.getLast?)
      = (allWords ℓ).countP (fun w =>
        (decide (Reduced w) && (alphaCount w == m) && (betaCount w == k))
          && g ((w.getLast?).map f)) := by
  conv_lhs => rw [← (perm_map_allWords f hf ℓ).countP_eq]
  rw [List.countP_map]
  apply List.countP_congr
  intro w _
  simp only [Function.comp_apply, hred, hα, hβ, List.getLast?_map]

/-! ### A3: the refined counts and the recurrence -/

/-- Reduced words with prescribed letter counts, ending in the letter c. -/
def eCount (c : Letter) (m k : ℕ) : ℕ :=
  ((allWords (m + k)).filter (fun w =>
      decide (Reduced w) && (alphaCount w == m) && (betaCount w == k)
        && (w.getLast? == some c))).length

/-- Reduced words with prescribed letter counts (no last-letter condition). -/
def nCount (m k : ℕ) : ℕ :=
  ((allWords (m + k)).filter (fun w =>
      decide (Reduced w) && (alphaCount w == m) && (betaCount w == k))).length

/-- Reduced words with prescribed letter counts, not ending in β⁻¹. -/
def pCount (m k : ℕ) : ℕ :=
  ((allWords (m + k)).filter (fun w =>
      decide (Reduced w) && (alphaCount w == m) && (betaCount w == k)
        && !(w.getLast? == some Letter.B))).length

/-- The `getLast? = none` term of a partition: only the empty word
contributes, and only for (m,k) = (0,0). -/
private lemma none_term (m k : ℕ) :
    (allWords (m+k)).countP (fun w =>
      (decide (Reduced w) && (alphaCount w == m) && (betaCount w == k))
        && (w.getLast? == none)) = if m = 0 ∧ k = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos (m+k) with h | h
  · have hm : m = 0 := by omega
    have hk : k = 0 := by omega
    subst hm; subst hk
    decide
  · rw [List.countP_eq_zero.2, if_neg (by omega)]
    intro w hw
    rw [mem_allWords] at hw
    have hne : w ≠ [] := by intro hn; rw [hn] at hw; simp at hw; omega
    simp [List.getLast?_eq_none_iff, hne]

/-- The count of reduced words of type (m,k) not ending in α⁻¹. -/
private lemma count_not_A (m k : ℕ) :
    (allWords (m+k)).countP (fun w =>
        (decide (Reduced w) && (alphaCount w == m) && (betaCount w == k))
          && !(w.getLast? == some Letter.A))
      = (if m = 0 ∧ k = 0 then 1 else 0)
        + eCount .a m k + eCount .b m k + eCount .B m k := by
  rw [countP_last_partition]
  simp only [and_not_last_none, and_not_last_self,
    and_not_last _ _ Letter.A Letter.a (by decide),
    and_not_last _ _ Letter.A Letter.b (by decide),
    and_not_last _ _ Letter.A Letter.B (by decide), none_term]
  simp only [eCount, ← List.countP_eq_length_filter]
  simp

/-- The count of reduced words of type (m,k) not ending in β⁻¹. -/
private lemma count_not_B (m k : ℕ) :
    (allWords (m+k)).countP (fun w =>
        (decide (Reduced w) && (alphaCount w == m) && (betaCount w == k))
          && !(w.getLast? == some Letter.B))
      = (if m = 0 ∧ k = 0 then 1 else 0)
        + eCount .a m k + eCount .A m k + eCount .b m k := by
  rw [countP_last_partition]
  simp only [and_not_last_none, and_not_last_self,
    and_not_last _ _ Letter.B Letter.a (by decide),
    and_not_last _ _ Letter.B Letter.A (by decide),
    and_not_last _ _ Letter.B Letter.b (by decide), none_term]
  simp only [eCount, ← List.countP_eq_length_filter]
  simp

/-- A3a. Partition by last letter; the empty word contributes exactly at
(0,0). Partition the filtered list by the value of `getLast?`
(`List.length_filter` bookkeeping; nodup is not needed for lengths of
filters, only disjointness of the predicates). -/
theorem nCount_partition (m k : ℕ) :
    nCount m k = (if m = 0 ∧ k = 0 then 1 else 0)
      + eCount .a m k + eCount .A m k + eCount .b m k + eCount .B m k := by
  simp only [nCount, eCount, ← List.countP_eq_length_filter]
  rw [countP_last_partition, none_term]

/-- A3b. Inverting every letter is a count-preserving involution swapping the
last-letter classes a ↔ A and b ↔ B. Bijection `w ↦ w.map Letter.inv` on the
filtered sets; use `nodup_allWords` and `Finset`/`List` card transport, or a
direct `List.length_map`-with-`List.filter_map` argument. -/
theorem eCount_symm_alpha (m k : ℕ) : eCount .a m k = eCount .A m k := by
  simp only [eCount, ← List.countP_eq_length_filter]
  refine Eq.trans (count_transport Letter.inv inv_inv reduced_invMap alphaCount_invMap
    betaCount_invMap (fun u => u == some Letter.a) m k (m+k)) ?_
  refine List.countP_congr (fun w _ => ?_)
  cases h : w.getLast? with
  | none => simp
  | some c => cases c <;> simp [Letter.inv]
theorem eCount_symm_beta (m k : ℕ) : eCount .b m k = eCount .B m k := by
  simp only [eCount, ← List.countP_eq_length_filter]
  refine Eq.trans (count_transport Letter.inv inv_inv reduced_invMap alphaCount_invMap
    betaCount_invMap (fun u => u == some Letter.b) m k (m+k)) ?_
  refine List.countP_congr (fun w _ => ?_)
  cases h : w.getLast? with
  | none => simp
  | some c => cases c <;> simp [Letter.inv]

/-- A3c-a. Peeling the last letter a: the prefix is any reduced word of
counts (m-1, k) not ending in A = a.inv. Bijection `w' ↦ w' ++ [.a]`.
The right side is written additively via the partition, to avoid
subtraction. -/
theorem eCount_peel_a (m k : ℕ) (hm : 1 ≤ m) :
    eCount .a m k = (if m - 1 = 0 ∧ k = 0 then 1 else 0)
      + eCount .a (m-1) k + eCount .b (m-1) k + eCount .B (m-1) k := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [← count_not_A m' k]
  show ((allWords (m' + 1 + k)).filter _).length = _
  rw [← List.countP_eq_length_filter, show m' + 1 + k = (m' + k) + 1 from by omega,
    ← List.countP_filter, ← (perm_append_allWords Letter.a (m' + k)).countP_eq,
    List.countP_map]
  refine List.countP_congr (fun w _ => ?_)
  simp only [Function.comp_apply]
  have hα : alphaCount (w ++ [Letter.a]) = alphaCount w + 1 := by
    simp [alphaCount, List.countP_append]
  have hβ : betaCount (w ++ [Letter.a]) = betaCount w := by
    simp [betaCount, List.countP_append]
  rw [hα, hβ]
  have hr := reduced_append_letter w Letter.a
  by_cases hR : Reduced w
  · by_cases hl : w.getLast? = some Letter.A <;> simp [hr, hR, hl, Letter.inv]
  · simp [hr, hR]

/-- A3c-b. Peeling the last letter b: the prefix is any reduced word of
counts (m, k-1) not ending in B = b.inv. -/
theorem eCount_peel_b (m k : ℕ) (hk : 1 ≤ k) :
    eCount .b m k = (if m = 0 ∧ k - 1 = 0 then 1 else 0)
      + eCount .a m (k-1) + eCount .A m (k-1) + eCount .b m (k-1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [← count_not_B m k']
  show ((allWords (m + (k' + 1))).filter _).length = _
  rw [← List.countP_eq_length_filter, show m + (k' + 1) = (m + k') + 1 from by omega,
    ← List.countP_filter, ← (perm_append_allWords Letter.b (m + k')).countP_eq,
    List.countP_map]
  refine List.countP_congr (fun w _ => ?_)
  simp only [Function.comp_apply]
  have hα : alphaCount (w ++ [Letter.b]) = alphaCount w := by
    simp [alphaCount, List.countP_append]
  have hβ : betaCount (w ++ [Letter.b]) = betaCount w + 1 := by
    simp [betaCount, List.countP_append]
  rw [hα, hβ]
  have hr := reduced_append_letter w Letter.b
  by_cases hR : Reduced w
  · by_cases hl : w.getLast? = some Letter.B <;> simp [hr, hR, hl, Letter.inv]
  · simp [hr, hR]

/-- A3d. The prefix count in terms of the refined counts. Same partition
argument as A3a. -/
theorem pCount_eq (m k : ℕ) :
    pCount m k = (if m = 0 ∧ k = 0 then 1 else 0)
      + eCount .a m k + eCount .A m k + eCount .b m k := by
  rw [← count_not_B m k]
  simp only [pCount, ← List.countP_eq_length_filter]

/-- A reduced word with no α-letters cannot end in an α-letter. -/
private lemma eCount_alpha_zero (c : Letter) (hc : c = Letter.a ∨ c = Letter.A) (k : ℕ) :
    eCount c 0 k = 0 := by
  simp only [eCount, ← List.countP_eq_length_filter]
  refine List.countP_eq_zero.2 (fun w _ => ?_)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_and]
  rintro ⟨⟨-, hα⟩, -⟩ hlast
  have hmem : c ∈ w := List.mem_of_getLast? hlast
  have : 0 < alphaCount w := by
    rw [alphaCount, List.countP_pos_iff]
    exact ⟨c, hmem, by rcases hc with rfl | rfl <;> rfl⟩
  omega

/-- A reduced word with no β-letters cannot end in a β-letter. -/
private lemma eCount_beta_zero (c : Letter) (hc : c = Letter.b ∨ c = Letter.B) (m : ℕ) :
    eCount c m 0 = 0 := by
  simp only [eCount, ← List.countP_eq_length_filter]
  refine List.countP_eq_zero.2 (fun w _ => ?_)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_and]
  rintro ⟨-, hβ⟩ hlast
  have hmem : c ∈ w := List.mem_of_getLast? hlast
  have : 0 < betaCount w := by
    rw [betaCount, List.countP_pos_iff]
    exact ⟨c, hmem, by rcases hc with rfl | rfl <;> rfl⟩
  omega

/-- The A3e recurrence, with an explicit bound for the strong induction. -/
private lemma pCount_eq_Rc_aux : ∀ (N m k : ℕ), m + k ≤ N → pCount m k = Rc m k := by
  intro N
  induction N with
  | zero =>
      intro m k h
      obtain ⟨rfl, rfl⟩ : m = 0 ∧ k = 0 := by omega
      rw [show Rc 0 0 = 1 from by simp [Rc]]
      decide
  | succ N ih =>
      intro m k h
      cases k with
      | zero =>
          cases m with
          | zero =>
              rw [show Rc 0 0 = 1 from by simp [Rc]]
              decide
          | succ m' =>
              cases m' with
              | zero =>
                  rw [show Rc 1 0 = 2 from by simp [Rc]]
                  decide
              | succ m'' =>
                  show pCount (m'' + 2) 0 = Rc (m'' + 2) 0
                  have hRc : Rc (m'' + 2) 0 = Rc (m'' + 1) 0 := by simp [Rc]
                  have hp2 := pCount_eq (m'' + 2) 0
                  have hp1 := pCount_eq (m'' + 1) 0
                  have ha := eCount_peel_a (m'' + 2) 0 (by omega)
                  have hsa := eCount_symm_alpha (m'' + 2) 0
                  have hsa' := eCount_symm_alpha (m'' + 1) 0
                  have hb2 := eCount_beta_zero Letter.b (Or.inl rfl) (m'' + 2)
                  have hb1 := eCount_beta_zero Letter.b (Or.inl rfl) (m'' + 1)
                  have hB1 := eCount_beta_zero Letter.B (Or.inr rfl) (m'' + 1)
                  have hih := ih (m'' + 1) 0 (by omega)
                  simp only [show m'' + 2 - 1 = m'' + 1 from rfl, Nat.succ_ne_zero,
                    false_and, if_false] at hp2 hp1 ha ⊢
                  omega
      | succ k' =>
          cases m with
          | zero =>
              have hRc : Rc 0 (k' + 1) = Rc 0 k' := by simp [Rc]
              have hp1 := pCount_eq 0 (k' + 1)
              have hp0 := pCount_eq 0 k'
              have hb := eCount_peel_b 0 (k' + 1) (by omega)
              have h0a := eCount_alpha_zero Letter.a (Or.inl rfl) (k' + 1)
              have h0A := eCount_alpha_zero Letter.A (Or.inr rfl) (k' + 1)
              have hih := ih 0 k' (by omega)
              simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, and_false, if_false,
                true_and] at hp0 hp1 hb ⊢
              omega
          | succ m' =>
              have hRc : Rc (m' + 1) (k' + 1)
                  = Rc m' (k' + 1) + Rc (m' + 1) k' + 3 * Rc m' k' := by simp [Rc]
              have hp := pCount_eq (m' + 1) (k' + 1)
              have hpa := pCount_eq m' (k' + 1)
              have hpb := pCount_eq (m' + 1) k'
              have hpc := pCount_eq m' k'
              have ha := eCount_peel_a (m' + 1) (k' + 1) (by omega)
              have hb := eCount_peel_b (m' + 1) (k' + 1) (by omega)
              have hbmid := eCount_peel_b m' (k' + 1) (by omega)
              have hs1 := eCount_symm_alpha (m' + 1) (k' + 1)
              have hs2 := eCount_symm_alpha m' (k' + 1)
              have hs3 := eCount_symm_alpha (m' + 1) k'
              have hs4 := eCount_symm_alpha m' k'
              have ht1 := eCount_symm_beta m' (k' + 1)
              have hih1 := ih m' (k' + 1) (by omega)
              have hih2 := ih (m' + 1) k' (by omega)
              have hih3 := ih m' k' (by omega)
              simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, false_and, and_false,
                if_false] at hp hpa hpb ha hb hbmid ⊢
              omega

/-- A3e — the second substantial item. The prefix count satisfies the Round-1
recurrence. Strong induction on m + k. Unfold the four clauses of `Rc`; in
each, rewrite `pCount` via A3d and push through the peeling recurrences
A3c-a/b together with the symmetries A3b (which convert `eCount .A`, `.B`
into `.a`, `.b`); the remaining goal is linear arithmetic over ℕ (`omega`),
using the induction hypotheses at (m-1,k), (m,k-1), (m-1,k-1). The base
values pCount 0 0 = 1, pCount 1 0 = 2 may be established by `decide`. -/
theorem pCount_eq_Rc (m k : ℕ) : pCount m k = Rc m k :=
  pCount_eq_Rc_aux (m + k) m k le_rfl

/-! ### A4: assembly -/

/-- Reduced words with counts (m,k) not ending in β (the ι_β-mirror of
`pCount`). -/
def pbCount (m k : ℕ) : ℕ :=
  ((allWords (m + k)).filter (fun w =>
      decide (Reduced w) && (alphaCount w == m) && (betaCount w == k)
        && !(w.getLast? == some Letter.b))).length

/-- A4a. The ι_β-map is a count-preserving involution exchanging the two
prefix conditions. Same bijection pattern as A3b, with `reduced_ibMap` and
the A1c count lemmas. -/
theorem pbCount_eq_pCount (m k : ℕ) : pbCount m k = pCount m k := by
  simp only [pbCount, pCount, ← List.countP_eq_length_filter]
  refine Eq.trans (count_transport Letter.ib ib_ib reduced_ibMap alphaCount_ibMap
    betaCount_ibMap (fun u => !(u == some Letter.b)) m k (m+k)) ?_
  refine List.countP_congr (fun w _ => ?_)
  cases h : w.getLast? with
  | none => simp
  | some c => cases c <;> simp [Letter.ib]

/-- A4b — MAIN THEOREM of Module A. The census equals twice the recurrence
value. Route: by A2d/A2e the symmetric reduced words of type (m,n) are the
disjoint union, over pos ∈ {true, false}, of the encodings of prefix words
with counts (m, (n-1)/2) satisfying the pos-junction condition (the middle
length p is determined by the parity of n, and betaCount w = (n-p)/2 equals
(n-1)/2 in ℕ-division for both parities). Transport cardinalities through
the encode bijection (A2a–A2c one way, A2d/A2e the other; use
`nodup_allWords` to pass between filtered-list lengths and Finset cards,
e.g. via `List.toFinset` and `Finset.card_nbij`). The pos = true class has
cardinality pCount m ((n-1)/2), the pos = false class pbCount m ((n-1)/2);
conclude with A4a and A3e. -/
theorem censusCount_eq (m n : ℕ) (hn : 1 ≤ n) :
    censusCount m n = 2 * Rc m ((n - 1) / 2) := by
  set k := (n - 1) / 2 with hk
  set p := if n % 2 = 1 then 1 else 2 with hpdef
  have hp12 : p = 1 ∨ p = 2 := by rw [hpdef]; split <;> simp
  have hnp : n = 2 * k + p := by rw [hk, hpdef]; split <;> omega
  set Lt := ((allWords (m+k)).filter (fun w =>
      decide (Reduced w) && (alphaCount w == m) && (betaCount w == k)
        && !(w.getLast? == some Letter.B))) with hLt
  set Lf := ((allWords (m+k)).filter (fun w =>
      decide (Reduced w) && (alphaCount w == m) && (betaCount w == k)
        && !(w.getLast? == some Letter.b))) with hLf
  have hinj : ∀ pos : Bool, Function.Injective (encode pos p) := by
    intro pos w w' hww
    exact (encode_inj hp12 hp12 hww).2.2
  have hperm : (Lt.map (encode true p) ++ Lf.map (encode false p)).Perm
      ((allWords (2*m+n)).filter (fun σ =>
        decide (IsSym σ) && decide (Reduced σ) && (alphaCount σ == 2*m)
          && (betaCount σ == n))) := by
    refine (List.perm_ext_iff_of_nodup ?_ ((nodup_allWords _).filter _)).mpr ?_
    · refine List.Nodup.append (((nodup_allWords _).filter _).map (hinj true))
        (((nodup_allWords _).filter _).map (hinj false)) ?_
      intro σ hσ hσ'
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hσ
      obtain ⟨w', -, hww⟩ := List.mem_map.1 hσ'
      exact absurd (encode_inj hp12 hp12 hww).1 (by simp)
    · intro σ
      simp only [List.mem_append, List.mem_map, List.mem_filter, mem_allWords, hLt, hLf,
        Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_eq_eq_not,
        Bool.not_true, beq_eq_false_iff_ne, ne_eq]
      constructor
      · rintro (⟨w, ⟨hwlen, ⟨⟨hred, hα⟩, hβ⟩, hlast⟩, rfl⟩ |
            ⟨w, ⟨hwlen, ⟨⟨hred, hα⟩, hβ⟩, hlast⟩, rfl⟩)
        · obtain ⟨hca, hcb⟩ := counts_encode true p w
          refine ⟨?_, ⟨⟨isSym_encode _ _ _, reduced_encode true p hp12 w hred (by simpa using hlast)⟩,
            by rw [hca, hα]⟩, by rw [hcb, hβ]; omega⟩
          simp only [encode, midWord, List.length_append, List.length_replicate,
            List.length_map, List.length_reverse, hwlen]
          omega
        · obtain ⟨hca, hcb⟩ := counts_encode false p w
          refine ⟨?_, ⟨⟨isSym_encode _ _ _, reduced_encode false p hp12 w hred (by simpa using hlast)⟩,
            by rw [hca, hα]⟩, by rw [hcb, hβ]; omega⟩
          simp only [encode, midWord, List.length_append, List.length_replicate,
            List.length_map, List.length_reverse, hwlen]
          omega
      · rintro ⟨hlen, ⟨⟨hsym, hred⟩, hα⟩, hβ⟩
        have hne : σ ≠ [] := by
          intro hcon
          rw [hcon] at hβ
          simp [betaCount] at hβ
          omega
        obtain ⟨pos, p', w, hp', rfl, hwred, hwlast⟩ := bisection_exists hsym hred hne
        obtain ⟨hca, hcb⟩ := counts_encode pos p' w
        rw [hca] at hα
        rw [hcb] at hβ
        have hpp : p' = p ∧ betaCount w = k := by
          rcases hp' with rfl | rfl <;> rcases hp12 with h | h <;> omega
        obtain ⟨rfl, hβw⟩ := hpp
        have hαw : alphaCount w = m := by omega
        have hwlen : w.length = m + k := by
          have := counts_length w
          omega
        cases pos
        · exact Or.inr ⟨w, ⟨hwlen, ⟨⟨hwred, hαw⟩, hβw⟩, by simpa using hwlast⟩, rfl⟩
        · exact Or.inl ⟨w, ⟨hwlen, ⟨⟨hwred, hαw⟩, hβw⟩, by simpa using hwlast⟩, rfl⟩
  have hlen := hperm.length_eq
  simp only [List.length_append, List.length_map] at hlen
  have hcensus : censusCount m n = Lt.length + Lf.length := by
    rw [censusCount, ← hlen]
  rw [hcensus]
  have h1 : Lt.length = pCount m k := rfl
  have h2 : Lf.length = pbCount m k := rfl
  rw [h1, h2, pbCount_eq_pCount, pCount_eq_Rc]
  omega

-- Raised only to let the kernel run the two `decide` evaluations below; both
-- A4c spot-checks are closed by plain `decide` (no `native_decide`). The
-- closed forms for `Rc` come from Round 1, since `Rc` itself is compiled by
-- well-founded recursion and does not reduce.
set_option maxRecDepth 100000

/-- A4c — NATIVE. Independent spot-checks of A4b beyond the Round-1 pair,
search spaces 4^7 = 16384. Closed by plain `decide`. -/
theorem census_2_3 : censusCount 2 3 = 2 * Rc 2 1 := by
  rw [Rc_two, show 2 * (8*1^2+4*1+2) = 28 from by norm_num]
  decide
theorem census_1_5 : censusCount 1 5 = 2 * Rc 1 2 := by
  rw [Rc_one, show 2 * (4*2+2) = 20 from by norm_num]
  decide

/-! ## Module B: Świerczkowski freeness for the arccos(1/3) pair

The two rotations are the conjugation actions of the quaternions √2 + i and
√2 + j: rotations through arccos(1/3) about the perpendicular axes e₁ and e₂.
Letters reuse `ThreeSquares.Letter`: a, A are the first rotation and its
inverse; b, B the second and its inverse.

The proof tracks a single row vector of the 3-scaled matrix product. Rows of
the form (d₁, d₂, √2·d₃) with integer dᵢ are preserved, and the induced
integer dynamics admits a mod-3 invariant implying d₃ ≠ 0 for every nonempty
reduced word, whence the product is never scalar. The starting row depends
only on the first letter (e₂ for a/A, e₁ for b/B), which eliminates
Świerczkowski's conjugation-normalization step entirely. -/

/-- Integer triples (d₁, d₂, d₃). -/
abbrev T3 := ℤ × ℤ × ℤ

/-- The integer row dynamics of the four scaled generators. -/
def step : Letter → T3 → T3
  | .a, (d₁, d₂, d₃) => (3*d₁, d₂ + 4*d₃, d₃ - 2*d₂)
  | .A, (d₁, d₂, d₃) => (3*d₁, d₂ - 4*d₃, d₃ + 2*d₂)
  | .b, (d₁, d₂, d₃) => (d₁ - 4*d₃, 3*d₂, d₃ + 2*d₁)
  | .B, (d₁, d₂, d₃) => (d₁ + 4*d₃, 3*d₂, d₃ - 2*d₁)

/-- The tracked starting row, by initial letter: e₂ for the a-family
(which moves the 2,3-plane), e₁ for the b-family (which moves the
1,3-plane). -/
def startVec : Letter → T3
  | .a | .A => (0, 1, 0)
  | .b | .B => (1, 0, 0)

/-- Run the dynamics along a word, left to right. -/
def run (σ : Word) (v : T3) : T3 := σ.foldl (fun v c => step c v) v

/-- The invariant carried after each letter, indexed by that letter. -/
def Inv : Letter → T3 → Prop
  | .a, (d₁, d₂, d₃) => ¬(3 ∣ d₃) ∧ (3 ∣ d₁) ∧ (3 ∣ (d₂ - d₃))
  | .A, (d₁, d₂, d₃) => ¬(3 ∣ d₃) ∧ (3 ∣ d₁) ∧ (3 ∣ (d₂ + d₃))
  | .b, (d₁, d₂, d₃) => ¬(3 ∣ d₃) ∧ (3 ∣ d₂) ∧ (3 ∣ (d₁ + d₃))
  | .B, (d₁, d₂, d₃) => ¬(3 ∣ d₃) ∧ (3 ∣ d₂) ∧ (3 ∣ (d₁ - d₃))

/-- B1a. The invariant is established by the first letter. Four cases;
each is a concrete integer computation (`decide` or `norm_num`). -/
theorem inv_start (c : Letter) : Inv c (step c (startVec c)) := by
  cases c <;> · show ¬ _ ∧ _ ∧ _
                omega

/-- B1b. The invariant propagates along any non-cancelling step. Twelve
transitions (c' ≠ c.inv); each is linear divisibility arithmetic over ℤ
with modulus 3 — destructure v, unfold, and close with `omega` (which
handles ∣ with literal divisors). Exhaustively certified over residues
mod 9 prior to commissioning. -/
theorem inv_step (c c' : Letter) (hcc : c' ≠ c.inv) {v : T3}
    (hv : Inv c v) : Inv c' (step c' v) := by
  obtain ⟨d₁, d₂, d₃⟩ := v
  cases c <;> cases c' <;>
    first
      | exact absurd rfl hcc
      | · replace hv : ¬ _ ∧ _ ∧ _ := hv
          show ¬ _ ∧ _ ∧ _
          omega

/-- B2 — the core. Along every nonempty reduced word, started from the row
adapted to its first letter, the third coordinate is never divisible by 3.
Induct along τ with an accumulator carrying `Inv` for the last processed
letter (private auxiliary recommended:
`aux : ∀ τ c v, Inv c v → Chain' (fun c d => d ≠ c.inv) (c :: τ) →
¬ 3 ∣ (τ.foldl (fun v c => step c v) v).2.2`), then instantiate with
`inv_start`. Note `run (c :: τ) v = τ.foldl _ (step c v)` by
`List.foldl_cons`. -/
private theorem core_aux : ∀ (τ : Word) (c : Letter) (v : T3), Inv c v →
    List.IsChain (fun x y => y ≠ x.inv) (c :: τ) →
    ¬ (3:ℤ) ∣ (τ.foldl (fun v c => step c v) v).2.2 := by
  intro τ
  induction τ with
  | nil =>
      intro c v hv _
      revert hv
      cases c <;> · intro hv
                    exact hv.1
  | cons d t ih =>
      intro c v hv hch
      rw [List.foldl_cons]
      rw [List.isChain_cons_cons] at hch
      exact ih d (step d v) (inv_step c d hch.1 hv) hch.2

theorem core (c : Letter) (τ : Word) (h : Reduced (c :: τ)) :
    ¬ (3 : ℤ) ∣ (run (c :: τ) (startVec c)).2.2 := by
  rw [run, List.foldl_cons]
  exact core_aux τ c (step c (startVec c)) (inv_start c) h

/-! ### B3: the matrix form over ℤ[√2] -/

/-- ℤ[√2]. -/
abbrev R2 := Zsqrtd 2

open Zsqrtd in
/-- The 3-scaled rotation matrices: `a` is 3·(rotation through arccos(1/3)
about e₁, the conjugation action of √2 + i), `b` is 3·(the same about e₂,
the action of √2 + j); capitals are the transposes (= scaled inverses). -/
def genM : Letter → Matrix (Fin 3) (Fin 3) R2
  | .a => !![3, 0, 0; 0, 1, -2*sqrtd; 0, 2*sqrtd, 1]
  | .A => !![3, 0, 0; 0, 1, 2*sqrtd; 0, -2*sqrtd, 1]
  | .b => !![1, 0, 2*sqrtd; 0, 3, 0; -2*sqrtd, 0, 1]
  | .B => !![1, 0, -2*sqrtd; 0, 3, 0; 2*sqrtd, 0, 1]

/-- The matrix of a word: the ordered product. -/
def evalM (σ : Word) : Matrix (Fin 3) (Fin 3) R2 := (σ.map genM).prod

/-- The ℤ[√2]-row encoded by an integer triple. -/
def row (v : T3) : Fin 3 → R2 :=
  ![(v.1 : R2), (v.2.1 : R2), Zsqrtd.sqrtd * (v.2.2 : R2)]

/-- B3a. One-step bridge: row-vector action of a generator is the integer
dynamics. Four cases; `funext i; fin_cases i;` then `Matrix.vecMul` /
`Matrix.dotProduct` simp and `Zsqrtd` component arithmetic (push to `re`/`im`
with `Zsqrtd.ext` if convenient), closing by `ring`. Uses √2·√2 = 2. -/
theorem vecMul_genM (c : Letter) (v : T3) :
    Matrix.vecMul (row v) (genM c) = row (step c v) := by
  obtain ⟨d₁, d₂, d₃⟩ := v
  funext i
  fin_cases i <;>
    cases c <;>
      simp [Matrix.vecMul, row, genM, step, dotProduct, Fin.sum_univ_three] <;>
      ext <;> simp <;> ring

/-- B3b. The bridge along a word. Induction with `List.prod_cons` and
`Matrix.vecMul_mul`. -/
theorem vecMul_evalM (σ : Word) (v : T3) :
    Matrix.vecMul (row v) (evalM σ) = row (run σ v) := by
  induction σ generalizing v with
  | nil => simp [evalM, run, Matrix.vecMul_one]
  | cons c t ih =>
      rw [evalM, List.map_cons, List.prod_cons, ← Matrix.vecMul_vecMul, vecMul_genM]
      rw [← evalM, ih, run, run, List.foldl_cons]

/-- B4 — MAIN THEOREM of Module B (Świerczkowski, 1958, in scaled form for
the arccos(1/3) pair about the axes e₁, e₂). No nonempty reduced word
evaluates to the scalar matrix: the group generated by the two rotations is
free of rank 2. Route: suppose equality; apply `Matrix.vecMul (row
(startVec c))` to both sides; the left side is `row (run …)` by B3b, the
right is `(3:R2)^ℓ • row (startVec c)` (via `Matrix.vecMul_smul` and
`Matrix.vecMul_one`). Both starting rows have third coordinate 0, so
comparing index 2 gives `sqrtd * (d₃ : R2) = 0`; `R2` is an integral domain
and `sqrtd ≠ 0`, so `(d₃ : R2) = 0`, and `Int.cast_injective` gives
`d₃ = 0`, contradicting B2 (0 is divisible by 3). -/
theorem swierczkowski_free (c : Letter) (τ : Word) (h : Reduced (c :: τ)) :
    evalM (c :: τ) ≠ ((3 : R2) ^ (c :: τ).length) • (1 : Matrix (Fin 3) (Fin 3) R2) := by
  intro heq
  have hstart : (startVec c).2.2 = 0 := by cases c <;> rfl
  have hv := congrArg (fun M => Matrix.vecMul (row (startVec c)) M) heq
  simp only [vecMul_evalM, Matrix.vecMul_smul, Matrix.vecMul_one] at hv
  have h2 := congrFun hv 2
  simp only [row, Matrix.cons_val, Pi.smul_apply, hstart] at h2
  have h3 : ((run (c :: τ) (startVec c)).2.2 : R2) * Zsqrtd.sqrtd = 0 := by
    rw [mul_comm]
    simpa using h2
  have h4 : (run (c :: τ) (startVec c)).2.2 = 0 := by
    have := congrArg Zsqrtd.im h3
    simpa using this
  exact core c τ h (by rw [h4]; exact dvd_zero 3)

/-! ### Axiom audit -/

#print axioms mem_allWords
#print axioms nodup_allWords
#print axioms ia_ia
#print axioms ib_ib
#print axioms inv_inv
#print axioms ia_inv
#print axioms ib_inv
#print axioms reduced_mirror
#print axioms alphaCount_mirror
#print axioms betaCount_mirror
#print axioms alphaCount_ibMap
#print axioms betaCount_ibMap
#print axioms reduced_ibMap
#print axioms isSym_encode
#print axioms reduced_encode
#print axioms counts_encode
#print axioms bisection_exists
#print axioms encode_inj
#print axioms nCount_partition
#print axioms eCount_symm_alpha
#print axioms eCount_symm_beta
#print axioms eCount_peel_a
#print axioms eCount_peel_b
#print axioms pCount_eq
#print axioms pCount_eq_Rc
#print axioms pbCount_eq_pCount
#print axioms censusCount_eq
#print axioms census_2_3
#print axioms census_1_5
#print axioms inv_start
#print axioms inv_step
#print axioms core
#print axioms vecMul_genM
#print axioms vecMul_evalM
#print axioms swierczkowski_free

end ThreeSquares
