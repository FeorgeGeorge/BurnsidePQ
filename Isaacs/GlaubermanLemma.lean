module

public import Isaacs.SchurZassenhausConjugacy
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Glauberman's lemma

Isaacs, *Finite Group Theory*, Lemma 3.24: let the finite group `A` act on the finite group `G`
by automorphisms with `(|A|, |G|) = 1`, at least one of `A`, `G` solvable, and let `A` and `G`
both act on a nonempty set `Ω` on which `G` is transitive, subject to Isaacs' compatibility
condition

`(∗)   (α · g) · a = (α · a) · gᵃ`.

Then `Ω` contains an `A`-invariant element, and any two `A`-invariant elements are in the same
orbit of `C_G(A)`.

## Left actions

`mathlib` actions are on the left, so (∗) is transcribed as

`a • (g • α) = (a • g) • (a • α)`,

i.e. the action of `A` on `Ω` is semilinear over the action of `A` on `G`.  This is exactly the
condition for the two actions to assemble into an action of the semidirect product `G ⋊ A`
(`CoprimeAction.semidirectAction`), which is what drives Isaacs' proof.

## The Schur–Zassenhaus input

The proof needs the *conjugacy* half of the Schur–Zassenhaus theorem, which `mathlib` does not
have — it proves only the existence half, `Subgroup.exists_right_complement'_of_coprime`.  Rather
than assume it as an axiom, it is carried as an explicit hypothesis,
`CoprimeAction.SchurZassenhausConjugacy`, on the statements that need it; see the docstring there
for how to discharge it.
-/

@[expose] public section

namespace CoprimeAction

universe u v

/-!
## The Schur–Zassenhaus conjugacy hypothesis
-/

/--
The conjugacy half of the Schur–Zassenhaus theorem: if `N` is a normal Hall subgroup of `Γ` and
one of `N`, `Γ ⧸ N` is solvable, then any two complements of `N` in `Γ` are conjugate.

`mathlib` has only the existence half (`Subgroup.exists_right_complement'_of_coprime`), so this is
taken as a hypothesis: it appears in the statement of every result that uses it, so nothing here
is assumed silently.

It is discharged verbatim by the Qiuzhen CFSG development's Huppert I.18.2,
`BenderSuzuki.External.huppert_I_18_2_complements_conjugate_of_solvable_normal_or_quotient`
(the solvability hypothesis is exactly the one carried here, so the Feit–Thompson-backed
unconditional I.18.3 is not needed).
-/
def SchurZassenhausConjugacy : Prop :=
  ∀ (Γ : Type u) [Group Γ] [Finite Γ] (N H K : Subgroup Γ) [N.Normal],
    Nat.Coprime (Nat.card N) N.index → (Group.IsSolvable N ∨ Group.IsSolvable (Γ ⧸ N)) →
      N.IsComplement' H → N.IsComplement' K → ∃ g : Γ, K = H.map (MulAut.conj g).toMonoidHom

/-- **The hypothesis is a theorem** (Huppert I.18.2), proved in
`Isaacs/SchurZassenhausConjugacy.lean` from a port of the Qiuzhen CFSG development.  It is kept
as an explicit hypothesis on the statements below so that they record exactly where complement
conjugacy is used; pass `CoprimeAction.schurZassenhausConjugacy` to instantiate any of them.

`Subgroup.index_eq_card` bridges the two spellings of the Hall condition: this file states it as
`Nat.Coprime (Nat.card N) N.index`, Huppert I.18.2 as `Nat.Coprime (Nat.card N) (Nat.card (Γ ⧸ N))`.
-/
theorem schurZassenhausConjugacy : SchurZassenhausConjugacy.{u} :=
  fun _Γ _ _ N H K _ hcop hsolv hH hK ↦
    SchurZassenhausConj.complements_conjugate_of_solvable N H K
      (by rwa [Subgroup.index_eq_card] at hcop) hsolv hH hK

/-- Conjugation by an element of `H` fixes `H`. -/
theorem map_conj_self {Γ : Type*} [Group Γ] {H : Subgroup Γ} {h : Γ} (hh : h ∈ H) :
    H.map (MulAut.conj h).toMonoidHom = H := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine ⟨?_, fun hx ↦ ⟨h⁻¹ * x * h, H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh, by group⟩⟩
  rintro ⟨y, hy, rfl⟩
  exact H.mul_mem (H.mul_mem hh hy) (H.inv_mem hh)

/-- The conjugator provided by `CoprimeAction.SchurZassenhausConjugacy` may be taken inside the
normal subgroup: write it as `n * h` with `n ∈ N` and `h ∈ H`, and note that the `h` part does not
move `H`. -/
theorem SchurZassenhausConjugacy.exists_mem (hSZ : SchurZassenhausConjugacy.{u})
    {Γ : Type u} [Group Γ] [Finite Γ] (N H K : Subgroup Γ) [N.Normal]
    (hcop : Nat.Coprime (Nat.card N) N.index)
    (hsolv : Group.IsSolvable N ∨ Group.IsSolvable (Γ ⧸ N))
    (hH : N.IsComplement' H) (hK : N.IsComplement' K) :
    ∃ n ∈ N, K = H.map (MulAut.conj n).toMonoidHom := by
  obtain ⟨g, hg⟩ := hSZ Γ N H K hcop hsolv hH hK
  obtain ⟨⟨n, h⟩, hnh⟩ := hH.2 g
  have hnh' : (n : Γ) * (h : Γ) = g := hnh
  subst hnh'
  refine ⟨n, n.2, ?_⟩
  have hconj : (MulAut.conj ((n : Γ) * (h : Γ))).toMonoidHom
      = (MulAut.conj (n : Γ)).toMonoidHom.comp (MulAut.conj (h : Γ)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hg, hconj, ← Subgroup.map_map, map_conj_self h.2]

/-!
## The semidirect product attached to the action
-/

variable {G A : Type u} [Group G] [Group A] [MulDistribMulAction A G]
variable {Ω : Type v} [MulAction G Ω] [MulAction A Ω]

variable (G A Ω) in
/-- Isaacs' compatibility condition (∗), for left actions: the action of `A` on `Ω` is semilinear
over the action of `A` on `G`. -/
def IsCompatible : Prop := ∀ (a : A) (g : G) (α : Ω), a • (g • α) = (a • g) • (a • α)

variable (G A) in
/-- The semidirect product `G ⋊ A` formed from the action of `A` on `G` by automorphisms. -/
abbrev Semidirect : Type u := G ⋊[MulDistribMulAction.toMulAut A G] A

instance [Finite G] [Finite A] : Finite (Semidirect G A) :=
  Finite.of_injective (fun x : Semidirect G A ↦ (x.left, x.right))
    (fun _ _ h ↦ SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- Under the compatibility condition (∗), the actions of `G` and of `A` on `Ω` assemble into an
action of the semidirect product `G ⋊ A`. -/
@[reducible]
def semidirectAction (h : IsCompatible G A Ω) : MulAction (Semidirect G A) Ω where
  smul x α := x.left • (x.right • α)
  one_smul α := by
    change (1 : Semidirect G A).left • ((1 : Semidirect G A).right • α) = α
    rw [SemidirectProduct.one_left, SemidirectProduct.one_right, one_smul, one_smul]
  mul_smul x y α := by
    change (x * y).left • ((x * y).right • α) = x.left • (x.right • (y.left • (y.right • α)))
    rw [h x.right y.left (y.right • α), SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      mul_smul, mul_smul]
    rfl

variable (G A) in
/-- The copy of `G` inside `G ⋊ A`. -/
def Gcopy : Subgroup (Semidirect G A) :=
  (SemidirectProduct.inl (φ := MulDistribMulAction.toMulAut A G)).range

variable (G A) in
/-- The copy of `A` inside `G ⋊ A`. -/
def Acopy : Subgroup (Semidirect G A) :=
  (SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut A G)).range

theorem mem_Gcopy_iff {x : Semidirect G A} : x ∈ Gcopy G A ↔ x.right = 1 := by
  constructor
  · rintro ⟨g, rfl⟩
    rfl
  · exact fun hx ↦ ⟨x.left, SemidirectProduct.ext rfl hx.symm⟩

theorem mem_Acopy_iff {x : Semidirect G A} : x ∈ Acopy G A ↔ x.left = 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · exact fun hx ↦ ⟨x.right, SemidirectProduct.ext hx.symm rfl⟩

theorem inl_mem_Gcopy (g : G) :
    (SemidirectProduct.inl g : Semidirect G A) ∈ Gcopy G A := ⟨g, rfl⟩

theorem inr_mem_Acopy (a : A) :
    (SemidirectProduct.inr a : Semidirect G A) ∈ Acopy G A := ⟨a, rfl⟩

instance Gcopy_normal : (Gcopy G A).Normal := by
  have h : Gcopy G A = (SemidirectProduct.rightHom (φ := MulDistribMulAction.toMulAut A G)).ker :=
    SemidirectProduct.range_inl_eq_ker_rightHom
  rw [h]
  infer_instance

theorem card_Gcopy : Nat.card (Gcopy G A) = Nat.card G :=
  Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).symm.toEquiv

theorem card_Acopy : Nat.card (Acopy G A) = Nat.card A :=
  Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inr_injective).symm.toEquiv

theorem index_Gcopy : (Gcopy G A).index = Nat.card A := by
  have h : Gcopy G A = (SemidirectProduct.rightHom (φ := MulDistribMulAction.toMulAut A G)).ker :=
    SemidirectProduct.range_inl_eq_ker_rightHom
  rw [h, Subgroup.index_ker]
  have hrange : (SemidirectProduct.rightHom (φ := MulDistribMulAction.toMulAut A G)).range = ⊤ :=
    MonoidHom.range_eq_top.mpr fun a ↦ ⟨SemidirectProduct.inr a, rfl⟩
  rw [hrange]
  exact Nat.card_congr Subgroup.topEquiv.toEquiv

/-- `G` and `A` are complementary inside `G ⋊ A`. -/
theorem isComplement'_Gcopy_Acopy : (Gcopy G A).IsComplement' (Acopy G A) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxG, hxA⟩
    exact Subgroup.mem_bot.mpr
      (SemidirectProduct.ext (mem_Acopy_iff.mp hxA) (mem_Gcopy_iff.mp hxG))
  · refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
    exact ⟨_, inl_mem_Gcopy x.left, _, inr_mem_Acopy x.right,
      SemidirectProduct.inl_left_mul_inr_right x⟩

/-- Solvability of `A` or of `G` transfers to the semidirect product's normal subgroup or
quotient, in the form the Schur–Zassenhaus conjugacy hypothesis wants: `Gcopy ≅ G` and
`(G ⋊ A) ⧸ Gcopy ≅ A`. -/
theorem isSolvable_or (h : Group.IsSolvable A ∨ Group.IsSolvable G) :
    Group.IsSolvable (Gcopy G A) ∨ Group.IsSolvable (Semidirect G A ⧸ Gcopy G A) := by
  have hker : Gcopy G A = (SemidirectProduct.rightHom
      (φ := MulDistribMulAction.toMulAut A G)).ker := SemidirectProduct.range_inl_eq_ker_rightHom
  rcases h with hA | hG
  · refine Or.inr ?_
    have : Group.IsSolvable A := hA
    have hsurj : Function.Surjective (SemidirectProduct.rightHom
        (φ := MulDistribMulAction.toMulAut A G)) := fun a ↦ ⟨SemidirectProduct.inr a, rfl⟩
    exact Group.isSolvable_of_isSolvable_injective
      (f := ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)).toMonoidHom) (MulEquiv.injective _)
  · refine Or.inl ?_
    have : Group.IsSolvable G := hG
    exact Group.isSolvable_of_isSolvable_injective
      (f := (MonoidHom.ofInjective (SemidirectProduct.inl_injective
        (φ := MulDistribMulAction.toMulAut A G))).symm.toMonoidHom) (MulEquiv.injective _)


/-!
## Glauberman's lemma
-/

section Glauberman

/-- How the semidirect product acts through its two factors. -/
theorem inl_smul (hcompat : IsCompatible G A Ω) (g : G) (α : Ω) :
    letI := semidirectAction hcompat
    (SemidirectProduct.inl g : Semidirect G A) • α = g • α := by
  let := semidirectAction hcompat
  change (SemidirectProduct.inl g : Semidirect G A).left •
    ((SemidirectProduct.inl g : Semidirect G A).right • α) = g • α
  simp

theorem inr_smul (hcompat : IsCompatible G A Ω) (a : A) (α : Ω) :
    letI := semidirectAction hcompat
    (SemidirectProduct.inr a : Semidirect G A) • α = a • α := by
  let := semidirectAction hcompat
  change (SemidirectProduct.inr a : Semidirect G A).left •
    ((SemidirectProduct.inr a : Semidirect G A).right • α) = a • α
  simp

/-- The stabilizer of a point, together with the copy of `G`, is coprime-Hall inside `G ⋊ A`:
the intersection has order dividing `|G|` and index dividing `|A|`. -/
theorem coprime_subgroupOf_stabilizer (hcop : Nat.Coprime (Nat.card A) (Nat.card G))
    (S : Subgroup (Semidirect G A)) :
    Nat.Coprime (Nat.card ((Gcopy G A).subgroupOf S)) ((Gcopy G A).subgroupOf S).index := by
  have hcard : Nat.card ((Gcopy G A).subgroupOf S) ∣ Nat.card G := by
    have h1 : Nat.card ((Gcopy G A).subgroupOf S)
        = Nat.card ((Gcopy G A ⊓ S : Subgroup (Semidirect G A))) := by
      rw [← Subgroup.subgroupOf_map_subtype]
      exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective S)).symm
    rw [h1, ← card_Gcopy (G := G) (A := A)]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hindex : ((Gcopy G A).subgroupOf S).index ∣ Nat.card A := by
    rw [← index_Gcopy (G := G) (A := A)]
    have hrel : (Gcopy G A).relIndex S ∣ (Gcopy G A).index :=
      Subgroup.relIndex_dvd_index_of_normal (Gcopy G A) S
    exact hrel
  have h2 : Nat.Coprime (Nat.card ((Gcopy G A).subgroupOf S)) (Nat.card A) :=
    Nat.Coprime.coprime_dvd_left hcard (Nat.Coprime.symm hcop)
  exact Nat.Coprime.coprime_dvd_right hindex h2

variable [Finite G] [Finite A] [MulAction.IsPretransitive G Ω]

/-- **Glauberman's lemma, existence part** (Isaacs, Lemma 3.24(a)).  A coprime pair of compatible
actions, with `G` transitive, has an `A`-invariant point. -/
theorem exists_isInvariant (hSZ : SchurZassenhausConjugacy.{u})
    (hcop : Nat.Coprime (Nat.card A) (Nat.card G)) (hsolv : Group.IsSolvable A ∨ Group.IsSolvable G)
    (hcompat : IsCompatible G A Ω) [Nonempty Ω] :
    ∃ α : Ω, ∀ a : A, a • α = α := by
  let := semidirectAction hcompat
  obtain ⟨α₀⟩ := ‹Nonempty Ω›
  set S : Subgroup (Semidirect G A) := MulAction.stabilizer (Semidirect G A) α₀ with hSdef
  -- Schur–Zassenhaus gives a complement `B` of `G ⊓ S` in `S`
  obtain ⟨B, hB⟩ := Subgroup.exists_right_complement'_of_coprime
    (N := (Gcopy G A).subgroupOf S) (coprime_subgroupOf_stabilizer hcop S)
  have hB'le : B.map S.subtype ≤ S := Subgroup.map_subtype_le B
  -- `B` is also a complement of `G` in `G ⋊ A`
  have hcompl : (Gcopy G A).IsComplement' (B.map S.subtype) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff, eq_bot_iff]
      rintro x ⟨hxG, hxB⟩
      have hxS : x ∈ S := hB'le hxB
      have h1 : (⟨x, hxS⟩ : S) ∈ (Gcopy G A).subgroupOf S := hxG
      have h2 : (⟨x, hxS⟩ : S) ∈ B := by
        obtain ⟨b, hb, hbx⟩ := hxB
        have : b = (⟨x, hxS⟩ : S) := Subtype.ext hbx
        exact this ▸ hb
      have := (disjoint_iff.mp hB.disjoint).le ⟨h1, h2⟩
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp this))
    · refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G α₀ (x • α₀)
      have hy : (SemidirectProduct.inl g : Semidirect G A)⁻¹ * x ∈ S := by
        change ((SemidirectProduct.inl g : Semidirect G A)⁻¹ * x) • α₀ = α₀
        rw [mul_smul, ← hg, ← inl_smul hcompat, inv_smul_smul]
      obtain ⟨⟨n, b⟩, hnb⟩ := hB.2 (⟨_, hy⟩ : S)
      have hnb' : ((n : S) : Semidirect G A) * ((b : S) : Semidirect G A) =
          (SemidirectProduct.inl g : Semidirect G A)⁻¹ * x := congrArg Subtype.val hnb
      refine ⟨(SemidirectProduct.inl g : Semidirect G A) * ((n : S) : Semidirect G A), ?_,
        ((b : S) : Semidirect G A), ?_, ?_⟩
      · exact (Gcopy G A).mul_mem (inl_mem_Gcopy g) n.2
      · exact ⟨(b : S), b.2, rfl⟩
      · change (SemidirectProduct.inl g : Semidirect G A) * ((n : S) : Semidirect G A) *
          ((b : S) : Semidirect G A) = x
        rw [mul_assoc, hnb', mul_inv_cancel_left]
  -- conjugacy of complements moves `A` inside the stabilizer
  obtain ⟨x, hx⟩ := hSZ (Semidirect G A) (Gcopy G A) (Acopy G A) (B.map S.subtype)
    (by rw [card_Gcopy, index_Gcopy]; exact Nat.Coprime.symm hcop) (isSolvable_or hsolv)
    isComplement'_Gcopy_Acopy hcompl
  refine ⟨x⁻¹ • α₀, fun a ↦ ?_⟩
  have hid : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom
      = MonoidHom.id (Semidirect G A) :=
    MonoidHom.ext fun y ↦ (show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group)
  have hA : Acopy G A = (B.map S.subtype).map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [hx, Subgroup.map_map, hid, Subgroup.map_id]
  have hAle : Acopy G A ≤ MulAction.stabilizer (Semidirect G A) (x⁻¹ • α₀) := by
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, hA, ← hSdef]
    exact Subgroup.map_mono hB'le
  have := hAle (inr_mem_Acopy a)
  rw [MulAction.mem_stabilizer_iff, inr_smul hcompat] at this
  exact this


/-- **Glauberman's lemma, conjugacy part** (Isaacs, Lemma 3.24(b)).  Two `A`-invariant points lie
in the same orbit of `C_G(A)`.

This is the existence part applied to the transporter `{x : G // x • α = β}`, which is a coset of
the stabilizer `G_α`: that stabilizer is `A`-invariant and acts transitively on the transporter by
right translation, and an `A`-invariant point of the transporter is exactly an element of
`C_G(A)` carrying `α` to `β`. -/
theorem exists_fixed_smul_eq (hSZ : SchurZassenhausConjugacy.{u})
    (hcop : Nat.Coprime (Nat.card A) (Nat.card G)) (hsolv : Group.IsSolvable A ∨ Group.IsSolvable G)
    (hcompat : IsCompatible G A Ω) {α β : Ω} (hα : ∀ a : A, a • α = α) (hβ : ∀ a : A, a • β = β) :
    ∃ c : G, (∀ a : A, a • c = c) ∧ c • α = β := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G α β
  -- the stabilizer of `α` is `A`-invariant, so `A` acts on it by automorphisms
  have hstab : ∀ (a : A) (h : G), h • α = α → (a • h) • α = α := by
    intro a h hh
    have h1 := hcompat a h α
    rw [hh, hα a] at h1
    exact h1.symm
  let : MulDistribMulAction A (MulAction.stabilizer G α) :=
    { smul := fun a h ↦ ⟨a • (h : G), hstab a (h : G) h.2⟩
      one_smul := fun h ↦ Subtype.ext (one_smul A (h : G))
      mul_smul := fun a b h ↦ Subtype.ext (mul_smul a b (h : G))
      smul_mul := fun a h k ↦ Subtype.ext (smul_mul' a (h : G) (k : G))
      smul_one := fun a ↦ Subtype.ext (smul_one a) }
  have hcoe : ∀ (a : A) (h : MulAction.stabilizer G α),
      ((a • h : MulAction.stabilizer G α) : G) = a • (h : G) := fun _ _ ↦ rfl
  -- the transporter from `α` to `β`
  let : MulAction (MulAction.stabilizer G α) {x : G // x • α = β} :=
    { smul := fun h x ↦ ⟨(x : G) * (h : G)⁻¹, by
        rw [mul_smul, MulAction.mem_stabilizer_iff.mp (inv_mem h.2), x.2]⟩
      one_smul := fun x ↦ Subtype.ext (by
        change (x : G) * ((1 : MulAction.stabilizer G α) : G)⁻¹ = (x : G)
        rw [OneMemClass.coe_one, inv_one, mul_one])
      mul_smul := fun h k x ↦ Subtype.ext (by
        change (x : G) * ((h : G) * (k : G))⁻¹ = (x : G) * (k : G)⁻¹ * (h : G)⁻¹
        group) }
  let : MulAction A {x : G // x • α = β} :=
    { smul := fun a x ↦ ⟨a • (x : G), by
        have h1 := hcompat a (x : G) α
        rw [x.2, hα a, hβ a] at h1
        exact h1.symm⟩
      one_smul := fun x ↦ Subtype.ext (one_smul A (x : G))
      mul_smul := fun a b x ↦ Subtype.ext (mul_smul a b (x : G)) }
  have : Nonempty {x : G // x • α = β} := ⟨⟨g, hg⟩⟩
  have : MulAction.IsPretransitive (MulAction.stabilizer G α) {x : G // x • α = β} := by
    refine ⟨fun x y ↦ ?_⟩
    refine ⟨⟨(y : G)⁻¹ * (x : G), ?_⟩, ?_⟩
    · rw [MulAction.mem_stabilizer_iff, mul_smul, x.2]
      exact inv_smul_eq_iff.mpr y.2.symm
    · exact Subtype.ext (by
        change (x : G) * ((y : G)⁻¹ * (x : G))⁻¹ = (y : G)
        group)
  -- the two actions are compatible, since `A` acts by automorphisms
  have hcompat' : IsCompatible (MulAction.stabilizer G α) A {x : G // x • α = β} := by
    intro a h x
    refine Subtype.ext ?_
    change a • ((x : G) * (h : G)⁻¹) = (a • (x : G)) * ((a • h : MulAction.stabilizer G α) : G)⁻¹
    rw [hcoe, smul_mul', smul_inv']
  -- and the hypotheses of the existence part hold for the stabilizer
  have hcop' : Nat.Coprime (Nat.card A) (Nat.card (MulAction.stabilizer G α)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_subgroup_dvd_card _) hcop
  have hsolv' : Group.IsSolvable A ∨ Group.IsSolvable (MulAction.stabilizer G α) :=
    hsolv.imp id fun hG ↦ by have := hG; exact inferInstance
  obtain ⟨c, hc⟩ := exists_isInvariant hSZ hcop' hsolv' hcompat'
  exact ⟨(c : G), fun a ↦ congrArg Subtype.val (hc a), c.2⟩
end Glauberman
end CoprimeAction
