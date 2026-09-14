module

public import Isaacs.SubnormalJoin

/-!
# Baer's theorem: Isaacs 2.12

Isaacs, *Finite Group Theory*, Theorem 2.12 (Baer): for a subgroup `H` of a finite group `G`,

> `H ⊆ F(G)` if and only if `⟨H, H ^ x⟩` is nilpotent for every `x ∈ G`.

One direction is immediate from `PiGroups.isNilpotent_fitting`.  The other is Isaacs' induction on
`|G|`: a proper subgroup `K ⊇ H` inherits the hypothesis, so `H ≤ F(K)` by induction and
`H ⊴⊴ K` by Theorem 2.2 (`PiGroups.le_fitting_iff`).  That is exactly the hypothesis of Wielandt's
zipper lemma (`PiGroups.exists_unique_coatom_of_not_isSubnormal`), so if `H` were not subnormal it
would lie in a unique maximal subgroup `M`; but each `⟨H, H ^ x⟩` is then proper — otherwise `G`
itself is nilpotent and `H` is subnormal by Isaacs 2.1 — hence contained in a maximal subgroup
containing `H`, which is `M`.  So every conjugate of `H` lies in `M`, the normal closure `H ^ G` is
proper, and `H ⊴⊴ H ^ G ⊴ G` gives the contradiction.

This is the last step before Isaacs' Theorem 2.13, which is the hypothesis
`Burnside.InvolutionInvertsElement` used in Step 7 of Burnside's `p ^ a q ^ b` theorem.
-/

@[expose] public section

namespace PiGroups

universe u

variable {G : Type u} [Group G]

/-- Conjugating inside a subgroup, seen from the subgroup or from the ambient group. -/
theorem map_subgroupOf_conj {H K : Subgroup G} (hHK : H ≤ K) (x : ↥K) :
    (H.subgroupOf K).map (MulAut.conj x).toMonoidHom
      = (H.map (MulAut.conj (x : G)).toMonoidHom).subgroupOf K := by
  ext u
  constructor
  · rintro ⟨⟨w, hwK⟩, hwH, rfl⟩
    exact ⟨w, hwH, rfl⟩
  · rintro ⟨h, hh, hhu⟩
    exact ⟨⟨h, hHK hh⟩, hh, Subtype.ext hhu⟩

private theorem baer_aux :
    ∀ (X : Type u) [Group X] [Finite X],
      ∀ H : Subgroup X, (∀ x : X, Group.IsNilpotent ↥(H ⊔ H.map (MulAut.conj x).toMonoidHom)) →
        H ≤ fitting X := by
  refine induction_on_card ?_
  intro X _ _ ih H hnil
  -- `H` itself is nilpotent, by taking `x = 1`
  have hHnil : Group.IsNilpotent ↥H := by
    have h1 := hnil 1
    rwa [map_conj_eq_self_iff.mpr (one_mem _), sup_idem] at h1
  -- every proper subgroup containing `H` contains it subnormally, by induction and Theorem 2.2
  have hsub : ∀ K : Subgroup X, H ≤ K → K ≠ ⊤ → (H.subgroupOf K).IsSubnormal := by
    intro K hHK hKtop
    have hcardK : Nat.card ↥K < Nat.card X := by
      have h1 := card_lt_card_of_lt (lt_top_iff_ne_top.mpr hKtop)
      rwa [Subgroup.card_top] at h1
    have hnilK : ∀ x : ↥K, Group.IsNilpotent
        ↥((H.subgroupOf K) ⊔ (H.subgroupOf K).map (MulAut.conj x).toMonoidHom) := by
      intro x
      have hHxK : H.map (MulAut.conj (x : X)).toMonoidHom ≤ K := by
        rintro _ ⟨h, hh, rfl⟩
        exact mul_mem (mul_mem x.2 (hHK hh)) (inv_mem x.2)
      rw [map_subgroupOf_conj hHK x, ← Subgroup.subgroupOf_sup hHK hHxK]
      have := hnil (x : X)
      exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (sup_le hHK hHxK)).symm
    exact (le_fitting_iff.mp (ih ↥K hcardK (H.subgroupOf K) hnilK)).2
  -- so `H` is subnormal: otherwise the zipper lemma gives a unique maximal overgroup
  have hHsub : H.IsSubnormal := by
    by_contra hns
    obtain ⟨M, hM, -, huniq⟩ := exists_unique_coatom_of_not_isSubnormal hsub hns
    have hconj : ∀ x : X, H.map (MulAut.conj x).toMonoidHom ≤ M := by
      intro x
      have hne : H ⊔ H.map (MulAut.conj x).toMonoidHom ≠ ⊤ := by
        intro htop
        refine hns ?_
        have hXnil : Group.IsNilpotent X := by
          have h1 := hnil x
          rw [htop] at h1
          exact Group.nilpotent_of_mulEquiv Subgroup.topEquiv
        exact isSubnormal_of_isNilpotent H
      obtain ⟨K, hK, hle⟩ := (IsCoatomic.eq_top_or_exists_le_coatom _).resolve_left hne
      rw [← huniq K hK (le_sup_left.trans hle)]
      exact le_sup_right.trans hle
    -- hence the normal closure of `H` is proper, and `H ⊴⊴ H ^ G ⊴ G`
    have hncM : Subgroup.normalClosure (H : Set X) ≤ M := by
      rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro z hz
      obtain ⟨v, hv, hzconj⟩ := Group.mem_conjugatesOfSet_iff.mp hz
      obtain ⟨c, rfl⟩ := isConj_iff.mp hzconj
      exact hconj c ⟨v, hv, rfl⟩
    have hnctop : Subgroup.normalClosure (H : Set X) ≠ ⊤ := fun h =>
      hM.1 (top_le_iff.mp (h ▸ hncM))
    exact hns (Subgroup.IsSubnormal.trans Subgroup.le_normalClosure
      (hsub _ Subgroup.le_normalClosure hnctop) (Subgroup.Normal.isSubnormal inferInstance))
  exact le_fitting_iff.mpr ⟨hHnil, hHsub⟩

/-- **Isaacs, Theorem 2.12** (Baer).  A subgroup of a finite group lies in the Fitting subgroup
exactly when it generates a nilpotent subgroup with each of its conjugates. -/
theorem le_fitting_iff_isNilpotent_sup_conj [Finite G] {H : Subgroup G} :
    H ≤ fitting G ↔ ∀ x : G, Group.IsNilpotent ↥(H ⊔ H.map (MulAut.conj x).toMonoidHom) := by
  constructor
  · intro hle x
    have hfix : (fitting G).map (MulAut.conj x).toMonoidHom = fitting G :=
      map_conj_eq_self_iff.mpr (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x)
    have h2 : H ⊔ H.map (MulAut.conj x).toMonoidHom ≤ fitting G :=
      sup_le hle (hfix ▸ Subgroup.map_mono hle)
    have : Group.IsNilpotent ↥((H ⊔ H.map (MulAut.conj x).toMonoidHom).subgroupOf (fitting G)) :=
      inferInstance
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h2)
  · exact fun h => baer_aux G H h

end PiGroups
