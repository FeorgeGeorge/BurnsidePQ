module

public import PreCFSG.GlaubermanLemma

/-!
# `A`-invariant cosets

Isaacs, *Finite Group Theory*, Theorem 3.27: let `A` act on `G` by automorphisms, write
`C = C_G(A)`, and let `H ≤ G` be an `A`-invariant subgroup with `(|A|, |H|) = 1` and one of `A`,
`H` solvable.  Then the `A`-invariant left cosets of `H` in `G`, and likewise the `A`-invariant
right cosets, are exactly the cosets meeting `C`.

The easy direction is a computation: a coset `cH` with `c ∈ C` satisfies `(cH)ᵃ = cᵃHᵃ = cH`.
The substance is the converse, which is Glauberman's lemma
(`CoprimeAction.exists_isInvariant`, Isaacs 3.24(a)) applied to the coset: `H` acts transitively
on it by right translation, `A` acts on it because it is invariant, and the compatibility
condition `(xh)ᵃ = xᵃhᵃ` is just the statement that `A` acts by automorphisms.

As in `PreCFSG/GlaubermanLemma.lean`, the conjugacy half of Schur–Zassenhaus is carried as the
explicit hypothesis `CoprimeAction.SchurZassenhausConjugacy`.
-/

@[expose] public section

namespace CoprimeAction

open scoped Pointwise

universe u

variable {G A : Type u} [Group G] [Group A] [MulDistribMulAction A G]

/-!
## Pointwise preliminaries
-/

theorem mem_leftCoset_iff' {H : Subgroup G} {x y : G} : y ∈ x • (H : Set G) ↔ x⁻¹ * y ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa using hh
  · intro hy
    exact ⟨x⁻¹ * y, hy, by simp⟩

/-- An `A`-invariant subgroup is invariant as a set. -/
theorem smul_coe_eq {H : Subgroup G} (hHinv : ∀ (a : A) (h : G), h ∈ H → a • h ∈ H) (a : A) :
    a • (H : Set G) = (H : Set G) := by
  ext y
  simp only [Set.mem_smul_set, SetLike.mem_coe]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact hHinv a h hh
  · intro hy
    exact ⟨a⁻¹ • y, by simpa using hHinv a⁻¹ y hy, by simp⟩

/-- `A` acts on left cosets: `(cS)ᵃ = cᵃSᵃ`. -/
theorem smul_smul_set (a : A) (c : G) (s : Set G) : a • (c • s) = (a • c) • (a • s) := by
  ext y
  simp only [Set.mem_smul_set, smul_eq_mul]
  constructor
  · rintro ⟨z, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨a • h, ⟨h, hh, rfl⟩, (smul_mul' a c h).symm⟩
  · rintro ⟨z, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨c * h, ⟨h, hh, rfl⟩, smul_mul' a c h⟩

/-- Two elements of the same left coset generate the same left coset. -/
theorem leftCoset_eq_of_mem {H : Subgroup G} {x c : G} (hc : c ∈ x • (H : Set G)) :
    c • (H : Set G) = x • (H : Set G) := by
  ext y
  rw [mem_leftCoset_iff', mem_leftCoset_iff']
  constructor
  · intro hy
    have : x⁻¹ * y = (x⁻¹ * c) * (c⁻¹ * y) := by group
    rw [this]
    exact H.mul_mem (mem_leftCoset_iff'.mp hc) hy
  · intro hy
    have hcx : c⁻¹ * x ∈ H := by simpa using H.inv_mem (mem_leftCoset_iff'.mp hc)
    have : c⁻¹ * y = (c⁻¹ * x) * (x⁻¹ * y) := by group
    rw [this]
    exact H.mul_mem hcx hy

/-- Inverting turns a right coset into a left coset. -/
theorem inv_rightCoset {H : Subgroup G} (x : G) : ((H : Set G) * {x})⁻¹ = x⁻¹ • (H : Set G) := by
  ext y
  simp only [Set.mem_inv, Set.mem_mul, Set.mem_singleton_iff, mem_leftCoset_iff', inv_inv,
    SetLike.mem_coe]
  constructor
  · rintro ⟨h, hh, z, hz, hzy⟩
    rw [hz] at hzy
    have hy : y = x⁻¹ * h⁻¹ := by
      rw [← inv_inv y, ← hzy, mul_inv_rev]
    rw [hy]
    simpa using H.inv_mem hh
  · intro hy
    exact ⟨(x * y)⁻¹, H.inv_mem hy, x, rfl, by group⟩

/-- The `A`-action commutes with inversion of sets. -/
theorem smul_set_inv (a : A) (s : Set G) : a • s⁻¹ = (a • s)⁻¹ := by
  ext y
  simp only [Set.mem_inv, Set.mem_smul_set]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z⁻¹, hz, by rw [smul_inv']⟩
  · rintro ⟨z, hz, hzy⟩
    exact ⟨z⁻¹, by simpa using hz, by rw [smul_inv', hzy, inv_inv]⟩

variable [Finite G] [Finite A]

/-!
## Isaacs' Theorem 3.27
-/

/-- The hard half of Isaacs 3.27: an `A`-invariant left coset of an `A`-invariant subgroup
contains an element centralizing `A`.  This is Glauberman's lemma applied to the coset. -/
theorem exists_fixed_mem_of_smul_eq (hSZ : SchurZassenhausConjugacy.{u}) {H : Subgroup G}
    (hHinv : ∀ (a : A) (h : G), h ∈ H → a • h ∈ H)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card H))
    (hsolv : Group.IsSolvable A ∨ Group.IsSolvable H) {x : G}
    (hX : ∀ a : A, a • (x • (H : Set G)) = x • (H : Set G)) :
    ∃ c ∈ x • (H : Set G), ∀ a : A, a • c = c := by
  -- `A` acts on `H` by automorphisms
  let : MulDistribMulAction A H :=
    { smul := fun a h ↦ ⟨a • (h : G), hHinv a (h : G) h.2⟩
      one_smul := fun h ↦ Subtype.ext (one_smul A (h : G))
      mul_smul := fun a b h ↦ Subtype.ext (mul_smul a b (h : G))
      smul_mul := fun a h k ↦ Subtype.ext (smul_mul' a (h : G) (k : G))
      smul_one := fun a ↦ Subtype.ext (smul_one a) }
  have hcoe : ∀ (a : A) (h : H), ((a • h : H) : G) = a • (h : G) := fun _ _ ↦ rfl
  -- `H` acts on the coset by right translation, transitively
  let : MulAction H {y : G // y ∈ x • (H : Set G)} :=
    { smul := fun h y ↦ ⟨(y : G) * (h : G)⁻¹, by
        have hy2 : x⁻¹ * (y : G) ∈ H := mem_leftCoset_iff'.mp y.2
        rw [mem_leftCoset_iff']
        have hrw : x⁻¹ * ((y : G) * (h : G)⁻¹) = (x⁻¹ * (y : G)) * (h : G)⁻¹ := by group
        rw [hrw]
        exact H.mul_mem hy2 (H.inv_mem h.2)⟩
      one_smul := fun y ↦ Subtype.ext (by
        change (y : G) * ((1 : H) : G)⁻¹ = (y : G)
        rw [OneMemClass.coe_one, inv_one, mul_one])
      mul_smul := fun h k y ↦ Subtype.ext (by
        change (y : G) * ((h : G) * (k : G))⁻¹ = (y : G) * (k : G)⁻¹ * (h : G)⁻¹
        group) }
  -- `A` acts on the coset because the coset is invariant
  let : MulAction A {y : G // y ∈ x • (H : Set G)} :=
    { smul := fun a y ↦ ⟨a • (y : G), by
        have hy : a • (y : G) ∈ a • (x • (H : Set G)) := Set.smul_mem_smul_set y.2
        rwa [hX a] at hy⟩
      one_smul := fun y ↦ Subtype.ext (one_smul A (y : G))
      mul_smul := fun a b y ↦ Subtype.ext (mul_smul a b (y : G)) }
  have : Nonempty {y : G // y ∈ x • (H : Set G)} :=
    ⟨⟨x, mem_leftCoset_iff'.mpr (by simp)⟩⟩
  have : MulAction.IsPretransitive H {y : G // y ∈ x • (H : Set G)} := by
    refine ⟨fun y z ↦ ?_⟩
    refine ⟨⟨(z : G)⁻¹ * (y : G), ?_⟩, ?_⟩
    · have hy := mem_leftCoset_iff'.mp y.2
      have hz := mem_leftCoset_iff'.mp z.2
      have : (z : G)⁻¹ * (y : G) = ((x⁻¹ * (z : G))⁻¹) * (x⁻¹ * (y : G)) := by group
      rw [this]
      exact H.mul_mem (H.inv_mem hz) hy
    · exact Subtype.ext (by
        change (y : G) * ((z : G)⁻¹ * (y : G))⁻¹ = (z : G)
        group)
  -- the compatibility condition is that `A` acts by automorphisms
  have hcompat : IsCompatible H A {y : G // y ∈ x • (H : Set G)} := by
    intro a h y
    refine Subtype.ext ?_
    change a • ((y : G) * (h : G)⁻¹) = (a • (y : G)) * (((a • h : H) : G))⁻¹
    rw [hcoe, smul_mul', smul_inv']
  obtain ⟨c, hc⟩ := exists_isInvariant hSZ hcop hsolv hcompat
  exact ⟨(c : G), c.2, fun a ↦ congrArg Subtype.val (hc a)⟩

/-- **Isaacs, Theorem 3.27, left cosets.**  The `A`-invariant left cosets of an `A`-invariant
subgroup `H` are exactly those meeting `C_G(A)`. -/
theorem smul_leftCoset_eq_iff (hSZ : SchurZassenhausConjugacy.{u}) {H : Subgroup G}
    (hHinv : ∀ (a : A) (h : G), h ∈ H → a • h ∈ H)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card H))
    (hsolv : Group.IsSolvable A ∨ Group.IsSolvable H) (x : G) :
    (∀ a : A, a • (x • (H : Set G)) = x • (H : Set G)) ↔
      ∃ c ∈ x • (H : Set G), ∀ a : A, a • c = c := by
  refine ⟨exists_fixed_mem_of_smul_eq hSZ hHinv hcop hsolv, ?_⟩
  rintro ⟨c, hcx, hc⟩ a
  rw [← leftCoset_eq_of_mem hcx, smul_smul_set, hc a, smul_coe_eq hHinv]

/-- **Isaacs, Theorem 3.27, right cosets.**  Same statement for right cosets, obtained from the
left-coset case by inversion: `(Hx)⁻¹ = x⁻¹H`, inversion preserves `A`-invariance, and it
preserves membership in `C_G(A)`. -/
theorem rightCoset_smul_eq_iff (hSZ : SchurZassenhausConjugacy.{u}) {H : Subgroup G}
    (hHinv : ∀ (a : A) (h : G), h ∈ H → a • h ∈ H)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card H))
    (hsolv : Group.IsSolvable A ∨ Group.IsSolvable H) (x : G) :
    (∀ a : A, a • ((H : Set G) * {x}) = (H : Set G) * {x}) ↔
      ∃ c ∈ (H : Set G) * {x}, ∀ a : A, a • c = c := by
  have hinv := inv_rightCoset (H := H) x
  constructor
  · intro hY
    have hX : ∀ a : A, a • (x⁻¹ • (H : Set G)) = x⁻¹ • (H : Set G) := by
      intro a
      rw [← hinv, smul_set_inv, hY a]
    obtain ⟨c, hcx, hc⟩ := exists_fixed_mem_of_smul_eq hSZ hHinv hcop hsolv hX
    refine ⟨c⁻¹, ?_, fun a ↦ by rw [smul_inv', hc a]⟩
    have hmem : c ∈ ((H : Set G) * {x})⁻¹ := by rw [hinv]; exact hcx
    simpa using hmem
  · rintro ⟨c, hcx, hc⟩ a
    have hc' : c⁻¹ ∈ x⁻¹ • (H : Set G) := by
      rw [← hinv]
      simpa using hcx
    have hX : a • (x⁻¹ • (H : Set G)) = x⁻¹ • (H : Set G) := by
      rw [← leftCoset_eq_of_mem hc', smul_smul_set, smul_inv', hc a, smul_coe_eq hHinv]
    rw [← hinv, smul_set_inv] at hX
    exact inv_injective hX

end CoprimeAction
