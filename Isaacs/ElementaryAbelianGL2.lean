module

public import Isaacs.GL2Lemma
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# `Aut(E)` as `GL(2, p)`, and Isaacs' Lemma 7.3 for a faithful action

`Isaacs/GL2Lemma.lean` proves Isaacs' Lemma 7.3 inside `GL(2, p)`.  Isaacs applies it, in the
proofs of Theorems 7.5 and 7.1, through the identification of `Aut(E)` with `GL(2, p)` for an
elementary abelian group `E` of order `p ^ 2`.  This file makes that identification and restates
7.3 for a group acting faithfully on such an `E`.

The identification is the usual one: `Additive E` has exponent `p`, so it is a module over
`ZMod p` (`AddCommGroup.zmodModule`); it is finite of order `p ^ 2`, so it is two-dimensional
(`Module.card_eq_pow_finrank`); a basis turns its endomorphism algebra into `Matrix (Fin 2)
(Fin 2) (ZMod p)` (`LinearMap.toMatrixAlgEquiv`), and units into units.

Only the existence of an injective homomorphism is recorded
(`PiGroups.exists_injective_toGL2`), which is all that transporting 7.3 needs; this keeps the
`ZMod p`-module structure — which is not an instance, being built from a hypothesis — confined to
one proof.
-/

@[expose] public section

namespace PiGroups

universe u

variable {p : ℕ} [Fact p.Prime]

/-!
## The embedding of `Aut(E)` in `GL(2, p)`
-/

/-- An elementary abelian group of order `p ^ 2` has automorphism group embedded in `GL(2, p)`. -/
theorem exists_injective_toGL2 {V : Type u} [CommGroup V] [Finite V]
    (hexp : ∀ x : V, x ^ p = 1) (hcard : Nat.card V = p ^ 2) :
    ∃ φ : MulAut V →* GL2 p, Function.Injective φ := by
  classical
  have hnz : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- `Additive V` is a `ZMod p`-module
  have hVadd : ∀ x : Additive V, (p : ℕ) • x = 0 := fun x => hexp (Additive.toMul x)
  have instMod : Module (ZMod p) (Additive V) := AddCommGroup.zmodModule hVadd
  have instFin : Fintype (Additive V) := Fintype.ofFinite _
  -- of dimension two, since `|V| = p ^ 2`
  have hfr : Module.finrank (ZMod p) (Additive V) = 2 := by
    have h1 : Fintype.card (Additive V)
        = Fintype.card (ZMod p) ^ Module.finrank (ZMod p) (Additive V) :=
      Module.card_eq_pow_finrank
    rw [ZMod.card p] at h1
    have h2 : Nat.card (Additive V) = Fintype.card (Additive V) := Nat.card_eq_fintype_card
    have h3 : Nat.card (Additive V) = Nat.card V := rfl
    rw [← h2, h3, hcard] at h1
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h1).symm
  have b : Module.Basis (Fin 2) (ZMod p) (Additive V) :=
    Module.finBasisOfFinrankEq (ZMod p) (Additive V) hfr
  -- an automorphism of `V` is a unit of the endomorphism algebra of `Additive V`
  let toAdd : MulAut V → (Additive V →ₗ[ZMod p] Additive V) := fun σ =>
    (AddMonoidHom.mk' (fun x => Additive.ofMul (σ (Additive.toMul x)))
      (fun a c => by simp)).toZModLinearMap p
  have htoAdd : ∀ (σ : MulAut V) (x : Additive V),
      (toAdd σ : Additive V → Additive V) x = Additive.ofMul (σ (Additive.toMul x)) :=
    fun _ _ => rfl
  let toEnd : MulAut V →* (Module.End (ZMod p) (Additive V))ˣ :=
    { toFun := fun σ =>
        { val := toAdd σ
          inv := toAdd σ.symm
          val_inv := by ext x; simp [htoAdd]
          inv_val := by ext x; simp [htoAdd] }
      map_one' := by ext x; simp [htoAdd]
      map_mul' := fun σ τ => by ext x; simp [htoAdd] }
  have htoEnd : ∀ (σ : MulAut V) (x : Additive V),
      ((toEnd σ : Module.End (ZMod p) (Additive V)) : Additive V → Additive V) x
        = Additive.ofMul (σ (Additive.toMul x)) := fun _ _ => rfl
  have ue : (Module.End (ZMod p) (Additive V))ˣ ≃* (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv
  refine ⟨ue.toMonoidHom.comp toEnd, ?_⟩
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have h1 : toEnd σ = 1 := ue.injective (by simpa using hσ)
  ext y
  have h2 := congrArg
    (fun u : (Module.End (ZMod p) (Additive V))ˣ =>
      ((u : Module.End (ZMod p) (Additive V)) : Additive V → Additive V) (Additive.ofMul y)) h1
  rw [htoEnd] at h2
  simpa using h2

/-!
## The `p`-part of `|GL(2, p)|`
-/

/-- `|GL(2, p)| = p (p - 1) ^ 2 (p + 1)`. -/
theorem card_GL2 : Nat.card (GL2 p) = p * ((p - 1) * (p + 1)) * (p - 1) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [Matrix.card_generalLinearGroup_eq, Matrix.card_specialLinearGroup_fin_two', ZMod.card p]

/-- The `p`-part of `|GL(2, p)|` is `p`, so every `p`-subgroup of `GL(2, p)` has order at most
`p`. -/
theorem card_le_of_isPGroup_GL2 {Q : Subgroup (GL2 p)} (hQ : IsPGroup p ↑Q) :
    Nat.card ↑Q ≤ p := by
  have hp : p.Prime := Fact.out
  have hp2 := hp.two_le
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd : Nat.card ↑Q ∣ Nat.card (GL2 p) := Subgroup.card_subgroup_dvd_card Q
  rw [hk, card_GL2, mul_assoc] at hdvd
  -- `p` divides neither `p - 1` nor `p + 1`
  have hnd1 : ¬ p ∣ (p - 1) := by
    intro h
    have h4 := Nat.le_of_dvd (by omega) h
    omega
  have hnd2 : ¬ p ∣ (p + 1) := by
    intro h
    have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp h
    have := Nat.le_of_dvd one_pos h1
    omega
  have hnM : ¬ p ∣ ((p - 1) * (p + 1)) * (p - 1) := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h5 | h5
    · rcases (Nat.Prime.dvd_mul hp).mp h5 with h6 | h6
      · exact hnd1 h6
      · exact hnd2 h6
    · exact hnd1 h5
  -- so `p ^ k ∣ p * M` with `p ∤ M` forces `k ≤ 1`
  have hk1 : k ≤ 1 := by
    by_contra hcon
    have h2 : p ^ 2 ∣ p ^ k := pow_dvd_pow p (by omega)
    have h3 : p * p ∣ p * (((p - 1) * (p + 1)) * (p - 1)) := by
      rw [← pow_two]
      exact h2.trans hdvd
    exact hnM ((mul_dvd_mul_iff_left (a := p) hp.pos.ne').mp h3)
  calc Nat.card ↑Q = p ^ k := hk
    _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
    _ = p := pow_one p

/-!
## Isaacs' Lemma 7.3 for a faithful action
-/

/-- A faithful action gives an injective map to the automorphism group. -/
theorem toMulAut_injective {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [FaithfulSMul G V] : Function.Injective (MulDistribMulAction.toMulAut G V) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine eq_of_smul_eq_smul (α := V) (m₁ := g) (m₂ := 1) fun x => ?_
  rw [one_smul]
  exact congrArg (fun σ : MulAut V => σ x) hg

/-- **Isaacs, Lemma 7.3, for a faithful action.**  If `G` acts faithfully on an elementary abelian
group of order `p ^ 2`, then a `p`-subgroup of `G` normalizing a subgroup `L` of order prime to
`p` whose `2`-subgroups are all abelian centralizes `L`.

This is `PiGroups.lemma_7_3` transported along the embedding `G ↪ Aut(V) ≅ GL(2, p)` of
`PiGroups.exists_injective_toGL2`. -/
theorem lemma_7_3_of_faithful {G V : Type u} [Group G] [CommGroup V] [Finite V]
    [MulDistribMulAction G V] [FaithfulSMul G V] (hp2 : p ≠ 2)
    (hexp : ∀ x : V, x ^ p = 1) (hcard : Nat.card V = p ^ 2)
    {P L : Subgroup G} (hP : IsPGroup p P) (hPN : P ≤ Subgroup.normalizer (L : Set G))
    (hLp : ¬ p ∣ Nat.card L)
    (hL2 : ∀ B : Subgroup G, B ≤ L → IsPGroup 2 B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    ∀ x ∈ P, ∀ y ∈ L, x * y = y * x := by
  obtain ⟨ψ, hψ⟩ := exists_injective_toGL2 (V := V) hexp hcard
  set φ : G →* GL2 p := ψ.comp (MulDistribMulAction.toMulAut G V) with hφdef
  have hφ : Function.Injective φ := hψ.comp toMulAut_injective
  have hrange : L.map φ ≤ φ.range := Subgroup.map_le_range φ L
  -- the image of `P` normalizes the image of `L`
  have hPN' : P.map φ ≤ Subgroup.normalizer ((L.map φ : Subgroup (GL2 p)) : Set (GL2 p)) := by
    rintro - ⟨x, hx, rfl⟩
    refine map_conj_eq_self_iff.mp ?_
    have hcomp : (MulAut.conj (φ x)).toMonoidHom.comp φ
        = φ.comp (MulAut.conj x).toMonoidHom :=
      MonoidHom.ext fun w => by simp [MulAut.conj_apply]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
      map_conj_eq_self_iff.mpr (hPN hx)]
  -- and has order prime to `p`, with abelian `2`-subgroups
  have hLp' : ¬ p ∣ Nat.card ↑(L.map φ) := by
    rwa [Subgroup.card_map_of_injective hφ]
  have hL2' : ∀ B : Subgroup (GL2 p), B ≤ L.map φ → IsPGroup 2 B →
      ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro B hBL hB2 x hx y hy
    have hBrange : B ≤ φ.range := hBL.trans hrange
    have hBeq : (B.comap φ).map φ = B := Subgroup.map_comap_eq_self hBrange
    have hcomapL : B.comap φ ≤ L := by
      intro z hz
      obtain ⟨w, hw, hwz⟩ := hBL hz
      exact hφ hwz.symm ▸ hw
    have hcomap2 : IsPGroup 2 ↑(B.comap φ) := hB2.comap_of_injective φ hφ
    obtain ⟨a, ha, rfl⟩ := hBeq ▸ hx
    obtain ⟨b, hb, rfl⟩ := hBeq ▸ hy
    rw [← map_mul, ← map_mul, hL2 (B.comap φ) hcomapL hcomap2 a ha b hb]
  -- Lemma 7.3 inside `GL(2, p)`, pulled back
  have hcomm := lemma_7_3 hp2 (hP.map φ) hPN' hLp' hL2'
  intro x hx y hy
  exact hφ (by
    rw [map_mul, map_mul]
    exact hcomm (φ x) ⟨x, hx, rfl⟩ (φ y) ⟨y, hy, rfl⟩)

/-- A group acting faithfully on an elementary abelian group of order `p ^ 2` has all its
`p`-subgroups of order at most `p`. -/
theorem card_le_of_isPGroup_of_faithful {G V : Type u} [Group G] [CommGroup V] [Finite V]
    [MulDistribMulAction G V] [FaithfulSMul G V]
    (hexp : ∀ x : V, x ^ p = 1) (hcard : Nat.card V = p ^ 2)
    {Q : Subgroup G} (hQ : IsPGroup p ↑Q) : Nat.card ↑Q ≤ p := by
  obtain ⟨ψ, hψ⟩ := exists_injective_toGL2 (V := V) hexp hcard
  have hφ : Function.Injective (ψ.comp (MulDistribMulAction.toMulAut G V)) :=
    hψ.comp toMulAut_injective
  calc Nat.card ↑Q = Nat.card ↑(Q.map (ψ.comp (MulDistribMulAction.toMulAut G V))) :=
        (Subgroup.card_map_of_injective hφ).symm
    _ ≤ p := card_le_of_isPGroup_GL2 (hQ.map _)

end PiGroups
