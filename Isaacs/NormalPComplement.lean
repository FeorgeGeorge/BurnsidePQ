module

public import Isaacs.PLocalSubgroups

/-!
# Normal `p`-complements, and Isaacs' Lemma 7.7

Towards Isaacs, *Finite Group Theory*, Theorem 7.1 (Thompson): if `P ∈ Syl_p(G)` with `p ≠ 2` and
both `C_G(Z(P))` and `N_G(J(P))` have normal `p`-complements, then so does `G`.

This file sets up the two things that theorem needs before its own induction can start.

* `PiGroups.HasNormalPComplement p G`: a normal subgroup of order prime to `p` with `p`-group
  quotient — a normal Hall `p'`-subgroup.  Isaacs uses repeatedly that this property is inherited
  by subgroups (`PiGroups.HasNormalPComplement.subgroup`) and by homomorphic images
  (`PiGroups.HasNormalPComplement.quotient`, `.of_mulEquiv`).
* **Lemma 7.7**: modulo a normal `p'`-subgroup `N`, normalizers and centralizers of `p`-subgroups
  are the images of the normalizers and centralizers.  Part (a) is Lemma 2.17, already available
  as `PiGroups.normalizer_map_mk'_eq`; part (b) is `PiGroups.centralizer_map_mk'_eq`, proved here
  from (a): an element of `N_G(P)` whose image centralizes `P̄` has `⁅P, x⁆ ≤ N ⊓ P = 1`.

`mathlib` has Burnside's normal `p`-complement theorem (`Subgroup.ker_transferSylow_isComplement'`,
for `N_G(P) ≤ C_G(P)`) but no notion of normal `p`-complement as such, and not Frobenius'
criterion, which is what Theorem 7.1 starts from.
-/

@[expose] public section

namespace PiGroups

open CoprimeAction

universe u

variable {p : ℕ} {G : Type u} [Group G]

/-!
## Normal `p`-complements
-/

variable (p G) in
/-- `G` **has a normal `p`-complement**: a normal subgroup of order prime to `p` whose quotient is
a `p`-group. -/
def HasNormalPComplement : Prop :=
  ∃ (N : Subgroup G) (_ : N.Normal), ¬ p ∣ Nat.card N ∧ IsPGroup p (G ⧸ N)

namespace HasNormalPComplement

/-- Having a normal `p`-complement transfers along isomorphisms. -/
theorem of_mulEquiv {H : Type u} [Group H] (e : G ≃* H) (h : HasNormalPComplement p G) :
    HasNormalPComplement p H := by
  obtain ⟨N, hNnormal, hNcard, hNquot⟩ := h
  have := hNnormal
  have hmapn : (N.map e.toMonoidHom).Normal := hNnormal.map _ e.surjective
  refine ⟨N.map e.toMonoidHom, hmapn, ?_, ?_⟩
  · rwa [Subgroup.card_map_of_injective e.injective]
  · exact hNquot.of_surjective (QuotientGroup.map N (N.map e.toMonoidHom) e.toMonoidHom
      (Subgroup.le_comap_map _ _)) (by
        rintro ⟨x⟩
        obtain ⟨y, rfl⟩ := e.surjective x
        exact ⟨(y : G), rfl⟩)

/-- Subgroups inherit a normal `p`-complement. -/
theorem subgroup (h : HasNormalPComplement p G) (H : Subgroup G) :
    HasNormalPComplement p ↥H := by
  obtain ⟨N, hNnormal, hNcard, hNquot⟩ := h
  have := hNnormal
  refine ⟨N.subgroupOf H, inferInstance, ?_, ?_⟩
  · intro hdvd
    refine hNcard (hdvd.trans ?_)
    rw [← Subgroup.card_map_of_injective (K := N.subgroupOf H) H.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  · exact (hNquot.to_subgroup (H.map (QuotientGroup.mk' N))).of_equiv
      (quotientSubgroupOfEquivMap N H).symm

/-- Quotients inherit a normal `p`-complement. -/
theorem quotient (h : HasNormalPComplement p G) (K : Subgroup G) [K.Normal] :
    HasNormalPComplement p (G ⧸ K) := by
  obtain ⟨N, hNnormal, hNcard, hNquot⟩ := h
  have := hNnormal
  refine ⟨N.map (QuotientGroup.mk' K), inferInstance, ?_, ?_⟩
  · intro hdvd
    refine hNcard (hdvd.trans ?_)
    exact Subgroup.card_dvd_of_surjective ((QuotientGroup.mk' K).subgroupMap N)
      (MonoidHom.subgroupMap_surjective _ N)
  · -- `(G ⧸ K) ⧸ (N K ⧸ K) ≃* G ⧸ N K`, a quotient of the `p`-group `G ⧸ N`
    have hmap : (N ⊔ K).map (QuotientGroup.mk' K) = N.map (QuotientGroup.mk' K) := by
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
    have hiso :=
      (QuotientGroup.quotientMulEquivOfEq (G := G ⧸ K) hmap).symm.trans
        (QuotientGroup.quotientQuotientEquivQuotient K (N ⊔ K) le_sup_right)
    refine IsPGroup.of_equiv ?_ hiso.symm
    exact hNquot.of_surjective (QuotientGroup.map N (N ⊔ K) (MonoidHom.id G) (by
        simp)) (by
      rintro ⟨x⟩
      exact ⟨QuotientGroup.mk x, rfl⟩)

end HasNormalPComplement

/-- The `p'`-core is a `p'`-group, so its order is prime to `p`. -/
theorem not_dvd_card_piCore_compl [Finite G] [Fact p.Prime] :
    ¬ p ∣ Nat.card (piCore ({p}ᶜ : Set ℕ) G) := by
  intro hdvd
  have hmem : p ∈ (Nat.card (piCore ({p}ᶜ : Set ℕ) G)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩
  exact (IsPiGroup.iff_card.mp isPiGroup_piCore p hmem) rfl

/-- A group has a normal `p`-complement exactly when its `p'`-core has `p`-group quotient: the
`p'`-core is then *the* normal `p`-complement, and in particular it is characteristic. -/
theorem hasNormalPComplement_iff [Finite G] [Fact p.Prime] :
    HasNormalPComplement p G ↔ IsPGroup p (G ⧸ piCore ({p}ᶜ : Set ℕ) G) := by
  constructor
  · rintro ⟨N, hNnormal, hNcard, hNquot⟩
    have := hNnormal
    have hNle : N ≤ piCore ({p}ᶜ : Set ℕ) G :=
      le_piCore hNnormal (isPiGroup_compl_of_not_dvd hNcard)
    exact hNquot.of_surjective (QuotientGroup.map N _ (MonoidHom.id G) (by simpa using hNle))
      (by rintro ⟨x⟩; exact ⟨QuotientGroup.mk x, rfl⟩)
  · intro h
    exact ⟨piCore ({p}ᶜ : Set ℕ) G, inferInstance, not_dvd_card_piCore_compl, h⟩


/-!
## Isaacs' Lemma 7.7
-/

/-- A `p`-subgroup meets a normal subgroup of order prime to `p` trivially. -/
theorem eq_one_of_mem_of_mem [Finite G] [Fact p.Prime] {N P : Subgroup G}
    (hN : ¬ p ∣ Nat.card N) (hP : IsPGroup p P) {z : G} (hzN : z ∈ N) (hzP : z ∈ P) : z = 1 := by
  have hinf : N ⊓ P = ⊥ := by
    by_contra hne
    obtain ⟨k, hk⟩ := (hP.to_le (inf_le_right : N ⊓ P ≤ P)).exists_card_eq
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hk
      exact hne (Subgroup.card_eq_one.mp hk)
    exact hN ((dvd_pow_self p hk0).trans (hk ▸ Subgroup.card_dvd_of_le inf_le_left))
  exact Subgroup.mem_bot.mp (hinf ▸ Subgroup.mem_inf.mpr ⟨hzN, hzP⟩)

/-- **Isaacs, Lemma 7.7(b).**  Modulo a normal `p'`-subgroup, the centralizer of a `p`-subgroup is
the image of the centralizer.

An element of the quotient centralizing `P̄` normalizes `P̄`, so by Lemma 2.17 it is the image of
some `y ∈ N_G(P)`; then for `u ∈ P` the element `y⁻¹ u y * u⁻¹` lies in `P` and maps to `1`, so it
lies in `N ⊓ P = 1`. -/
theorem centralizer_map_mk'_eq [Finite G] [Fact p.Prime] (hSZ : SchurZassenhausConjugacy.{u})
    {N : Subgroup G} [N.Normal] (hN : ¬ p ∣ Nat.card N) {P : Subgroup G} (hP : IsPGroup p P) :
    Subgroup.centralizer ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = (Subgroup.centralizer (P : Set G)).map (QuotientGroup.mk' N) := by
  refine le_antisymm (fun xbar hxbar => ?_) ?_
  · -- `xbar` normalizes the image of `P`, so it comes from `N_G(P)` by Lemma 2.17
    have hnorm : xbar ∈ Subgroup.normalizer
        ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
      Subgroup.centralizer_le_normalizer _ hxbar
    rw [normalizer_map_mk'_eq hSZ hN hP] at hnorm
    obtain ⟨y, hy, rfl⟩ := hnorm
    refine ⟨y, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_, rfl⟩
    -- `y⁻¹ u y` lies in `P`, and agrees with `u` modulo `N`
    have hconj : y⁻¹ * u * y ∈ P := by
      have h1 := Subgroup.mem_normalizer_iff.mp hy (y⁻¹ * u * y)
      have h2 : y * (y⁻¹ * u * y) * y⁻¹ = u := by group
      rw [h2] at h1
      exact h1.mpr hu
    have hquot : (QuotientGroup.mk' N) (y⁻¹ * u * y * u⁻¹) = 1 := by
      have hcomm := Subgroup.mem_centralizer_iff.mp hxbar ((QuotientGroup.mk' N) u)
        ⟨u, hu, rfl⟩
      simp only [map_mul, map_inv]
      calc ((QuotientGroup.mk' N) y)⁻¹ * (QuotientGroup.mk' N) u * (QuotientGroup.mk' N) y
              * ((QuotientGroup.mk' N) u)⁻¹
          = ((QuotientGroup.mk' N) y)⁻¹ * ((QuotientGroup.mk' N) u * (QuotientGroup.mk' N) y)
              * ((QuotientGroup.mk' N) u)⁻¹ := by group
        _ = ((QuotientGroup.mk' N) y)⁻¹ * ((QuotientGroup.mk' N) y * (QuotientGroup.mk' N) u)
              * ((QuotientGroup.mk' N) u)⁻¹ := by rw [hcomm]
        _ = 1 := by group
    have hmemN : y⁻¹ * u * y * u⁻¹ ∈ N := by
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hquot
    have hmemP : y⁻¹ * u * y * u⁻¹ ∈ P := mul_mem hconj (inv_mem hu)
    have hone := eq_one_of_mem_of_mem hN hP hmemN hmemP
    have h3 : y⁻¹ * u * y = u := mul_inv_eq_one.mp hone
    calc u * y = y * (y⁻¹ * u * y) := by group
      _ = y * u := by rw [h3]
  · rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨u, hu, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hy u hu
    rw [← map_mul, ← map_mul, this]

end PiGroups
