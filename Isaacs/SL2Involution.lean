module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Data.Fintype.Parity
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# `SL(2, q)`: Isaacs 7.4, and the order of the group

Isaacs, *Finite Group Theory*, Lemma 7.4: if `q` is odd, then `-I` is the unique involution in
`SL(2, q)`.  Isaacs needs this for Lemma 7.3 — the automorphism group of an elementary abelian
group of order `p ^ 2` is `GL(2, p)` — on the way to Theorem 7.1.

Nothing here is special to a finite field: the statement holds over any commutative domain in
which `2 ≠ 0`, which is the only use made of "`q` is odd".

Isaacs' proof runs through minimal and characteristic polynomials and Cayley–Hamilton.  The proof
here is the same idea in the form that `mathlib` supports directly: a matrix `M` with `M * M = 1`
and `det M = 1` satisfies `adjugate M = M`, because
`adjugate M = (M * M) * adjugate M = M * (det M • 1) = M`; in dimension `2` the adjugate is
`!![d, -b; -c, a]`, so `M = !![a, b; c, d]` has `b = -b`, `c = -c` and `a = d`.  With `2 ≠ 0` this
forces `M` to be the scalar matrix `a • 1`, and `det M = a ^ 2 = 1` leaves `a = ±1`.

* `Matrix.eq_one_or_neg_one_of_mul_self_eq_one` and
  `Matrix.SpecialLinearGroup.eq_neg_one_of_mul_self_eq_one` are **Lemma 7.4**;
* `Matrix.SpecialLinearGroup.neg_one_mul_self` and
  `Matrix.SpecialLinearGroup.neg_one_ne_one` say that `-I` really is an involution, so it is *the*
  involution of `SL(2, q)`;
* `Matrix.card_specialLinearGroup_fin_two'` is the order `q (q - 1) (q + 1)` of `SL(2, q)`, the
  other input to Lemma 7.3.  `mathlib` has `|GL(n, q)|` (`Matrix.card_GL_field`) and the
  surjectivity of the determinant, so this is the first isomorphism theorem applied to
  `det : GL(n, q) → Fˣ`, whose kernel is `SL(n, q)`.
-/

@[expose] public section

namespace Matrix

universe u

/-- A matrix of determinant `1` that squares to the identity is its own adjugate. -/
theorem adjugate_eq_self_of_mul_self_eq_one {R : Type u} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] {M : Matrix n n R} (hdet : M.det = 1) (hM : M * M = 1) :
    adjugate M = M := by
  calc adjugate M = M * M * adjugate M := by rw [hM, one_mul]
    _ = M * (M * adjugate M) := by rw [Matrix.mul_assoc]
    _ = M := by rw [mul_adjugate, hdet, one_smul, mul_one]

variable {R : Type u} [CommRing R] [IsDomain R]

/-- **Isaacs, Lemma 7.4.**  Over a domain in which `2 ≠ 0`, a `2 × 2` matrix of determinant `1`
that squares to the identity is `±1`. -/
theorem eq_one_or_neg_one_of_mul_self_eq_one (h2 : (2 : R) ≠ 0)
    {M : Matrix (Fin 2) (Fin 2) R} (hdet : M.det = 1) (hM : M * M = 1) :
    M = 1 ∨ M = -1 := by
  have hadj := adjugate_eq_self_of_mul_self_eq_one hdet hM
  rw [adjugate_fin_two] at hadj
  -- comparing entries of `!![d, -b; -c, a] = M`
  have e00 : M 1 1 = M 0 0 := by
    have h := congrFun (congrFun hadj 0) 0
    simpa using h
  have e01 : -M 0 1 = M 0 1 := by
    have h := congrFun (congrFun hadj 0) 1
    simpa using h
  have e10 : -M 1 0 = M 1 0 := by
    have h := congrFun (congrFun hadj 1) 0
    simpa using h
  have hb : M 0 1 = 0 := by
    have h1 : (2 : R) * M 0 1 = 0 := by linear_combination -e01
    exact (mul_eq_zero.mp h1).resolve_left h2
  have hc : M 1 0 = 0 := by
    have h1 : (2 : R) * M 1 0 = 0 := by linear_combination -e10
    exact (mul_eq_zero.mp h1).resolve_left h2
  -- so `M` is scalar, and its determinant is the square of that scalar
  have hsq : M 0 0 * M 0 0 = 1 := by
    rw [det_fin_two, hb, hc, e00] at hdet
    linear_combination hdet
  have ha : M 0 0 = 1 ∨ M 0 0 = -1 := by
    have hfac : (M 0 0 - 1) * (M 0 0 + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  rcases ha with ha | ha
  · refine Or.inl ?_
    have hd : M 1 1 = 1 := e00.trans ha
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
  · refine Or.inr ?_
    have hd : M 1 1 = -1 := e00.trans ha
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

/-- **Isaacs, Lemma 7.4**, in the form "the unique involution": a `2 × 2` matrix of determinant `1`
that squares to the identity and is not the identity is `-1`. -/
theorem eq_neg_one_of_mul_self_eq_one (h2 : (2 : R) ≠ 0) {M : Matrix (Fin 2) (Fin 2) R}
    (hdet : M.det = 1) (hM : M * M = 1) (hne : M ≠ 1) : M = -1 :=
  (eq_one_or_neg_one_of_mul_self_eq_one h2 hdet hM).resolve_left hne

namespace SpecialLinearGroup

omit [IsDomain R] in
/-- `-I` is an involution of `SL(2, R)`. -/
theorem neg_one_mul_self :
    (-1 : SpecialLinearGroup (Fin 2) R) * (-1 : SpecialLinearGroup (Fin 2) R) = 1 := by
  rw [neg_mul_neg, one_mul]

omit [IsDomain R] in
/-- `-I ≠ I` in `SL(2, R)` when `2 ≠ 0`. -/
theorem neg_one_ne_one (h2 : (2 : R) ≠ 0) :
    (-1 : SpecialLinearGroup (Fin 2) R) ≠ (1 : SpecialLinearGroup (Fin 2) R) := by
  intro hcon
  have h := congrFun (congrFun (congrArg (fun t : SpecialLinearGroup (Fin 2) R =>
    (t : Matrix (Fin 2) (Fin 2) R)) hcon) 0) 0
  simp only [coe_neg, coe_one, neg_apply, one_apply_eq] at h
  exact h2 (by linear_combination -h)

/-- **Isaacs, Lemma 7.4.**  Over a domain in which `2 ≠ 0`, every element of `SL(2, R)` squaring to
the identity is `±1`. -/
theorem eq_one_or_eq_neg_one_of_mul_self_eq_one (h2 : (2 : R) ≠ 0)
    {t : SpecialLinearGroup (Fin 2) R} (ht : t * t = 1) : t = 1 ∨ t = -1 := by
  have hmat : (t : Matrix (Fin 2) (Fin 2) R) * (t : Matrix (Fin 2) (Fin 2) R) = 1 := by
    rw [← coe_mul, ht, coe_one]
  rcases eq_one_or_neg_one_of_mul_self_eq_one h2 t.det_coe hmat with h | h
  · exact Or.inl (Subtype.ext (by rw [h, coe_one]))
  · exact Or.inr (Subtype.ext (by rw [h, coe_neg, coe_one]))

/-- **Isaacs, Lemma 7.4.**  `-I` is the unique involution of `SL(2, q)` for odd `q`. -/
theorem eq_neg_one_of_mul_self_eq_one (h2 : (2 : R) ≠ 0)
    {t : SpecialLinearGroup (Fin 2) R} (ht : t * t = 1) (hne : t ≠ 1) : t = -1 :=
  (eq_one_or_eq_neg_one_of_mul_self_eq_one h2 ht).resolve_left hne

/-- Isaacs' hypothesis "`q` is odd", for the prime field: `2 ≠ 0` in `ZMod p` for odd primes. -/
theorem two_ne_zero_zmod_of_prime_ne_two {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  exact hne
    ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp h2))

/-- **Isaacs, Lemma 7.4** over the prime field: for an odd prime `p`, the negative of the identity
is the unique involution of `SL(2, p)`.  This is the shape in which the lemma is used, `ZMod p`
being the field over which the automorphism group of an elementary abelian group of order `p ^ 2`
is `GL(2, p)`. -/
theorem eq_neg_one_of_mul_self_eq_one_zmod {p : ℕ} (hp : p.Prime) (hne : p ≠ 2)
    {t : SpecialLinearGroup (Fin 2) (ZMod p)} (ht : t * t = 1) (hone : t ≠ 1) : t = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  exact eq_neg_one_of_mul_self_eq_one (two_ne_zero_zmod_of_prime_ne_two hp hne) ht hone

end SpecialLinearGroup

/-!
## The order of `SL(2, q)`

`|GL(n, q)|` is `mathlib`'s `Matrix.card_GL_field`, and the determinant is a surjection
`GL(n, q) → Fˣ` with kernel `SL(n, q)`, so `|SL(n, q)| = |GL(n, q)| / (q - 1)`.  For `n = 2` this
is `q (q - 1) (q + 1)`, the count Isaacs uses in the proof of Lemma 7.3.
-/

section Card

variable (F : Type*) [Field F] [Fintype F]

omit [Fintype F] in
/-- `SL(n, F)` is the kernel of the determinant `GL(n, F) → Fˣ`. -/
theorem card_specialLinearGroup_eq_card_ker_det (n : Type*) [Fintype n] [DecidableEq n] :
    Nat.card (SpecialLinearGroup n F)
      = Nat.card ((GeneralLinearGroup.det : GL n F →* Fˣ).ker) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun A : SpecialLinearGroup n F =>
      (⟨SpecialLinearGroup.toGL A, SpecialLinearGroup.coeToGL_det A⟩ :
        (GeneralLinearGroup.det : GL n F →* Fˣ).ker)) ⟨?_, ?_⟩)
  · intro A B hAB
    exact SpecialLinearGroup.toGL_injective (congrArg Subtype.val hAB)
  · rintro ⟨g, hg⟩
    refine ⟨⟨(g : Matrix n n F), ?_⟩, Subtype.ext (Units.ext rfl)⟩
    exact congrArg Units.val (MonoidHom.mem_ker.mp hg)

/-- `|GL(n, F)| = |SL(n, F)| * (|F| - 1)` for a finite field. -/
theorem card_generalLinearGroup_eq (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n] :
    Nat.card (GL n F) = Nat.card (SpecialLinearGroup n F) * (Fintype.card F - 1) := by
  classical
  have hquot : Nat.card (GL n F ⧸ (GeneralLinearGroup.det : GL n F →* Fˣ).ker)
      = Nat.card Fˣ :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      GeneralLinearGroup.det_surjective).toEquiv
  have hcard := Subgroup.card_mul_index (GeneralLinearGroup.det : GL n F →* Fˣ).ker
  rw [Subgroup.index_eq_card, hquot, Nat.card_eq_fintype_card (α := Fˣ),
    Fintype.card_units] at hcard
  rw [← hcard, card_specialLinearGroup_eq_card_ker_det]

/-- **The order of `SL(2, q)`**: `q (q - 1) (q + 1)`, in the form `q (q ^ 2 - 1)`. -/
theorem card_specialLinearGroup_fin_two :
    Nat.card (SpecialLinearGroup (Fin 2) F)
      = Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  classical
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hGL : Nat.card (GL (Fin 2) F)
      = (Fintype.card F ^ 2 - Fintype.card F ^ 0) * (Fintype.card F ^ 2 - Fintype.card F ^ 1) := by
    rw [card_GL_field]
    exact Fin.prod_univ_two fun i : Fin 2 => Fintype.card F ^ 2 - Fintype.card F ^ (i : ℕ)
  rw [card_generalLinearGroup_eq] at hGL
  refine Nat.eq_of_mul_eq_mul_right (show 0 < Fintype.card F - 1 by omega) ?_
  rw [hGL, pow_zero, pow_one]
  have h1 : Fintype.card F ^ 2 - Fintype.card F
      = Fintype.card F * (Fintype.card F - 1) := by
    rw [Nat.mul_sub, mul_one, pow_two]
  rw [h1]
  ring

/-- The order of `SL(2, q)` in Isaacs' shape, `q (q - 1) (q + 1)`. -/
theorem card_specialLinearGroup_fin_two' :
    Nat.card (SpecialLinearGroup (Fin 2) F)
      = Fintype.card F * ((Fintype.card F - 1) * (Fintype.card F + 1)) := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [card_specialLinearGroup_fin_two]
  congr 1
  have : Fintype.card F ^ 2 = Fintype.card F * Fintype.card F := pow_two _
  rw [this, Nat.sub_mul, Nat.mul_add, mul_one, one_mul]
  omega

end Card

end Matrix
