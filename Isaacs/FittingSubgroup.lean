module

public import Isaacs.PLocalSubgroups
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The Fitting subgroup, and Isaacs' Theorem 2.2

Isaacs, *Finite Group Theory*, Theorem 2.2: for a subgroup `H` of a finite group `G`,

> `H ⊆ F(G)` if and only if `H` is nilpotent and subnormal in `G`.

`mathlib` has subnormality (`Subgroup.IsSubnormal`, with the transitivity and image lemmas used
below) but no Fitting subgroup for groups — the `Fitting` that appears there is Fitting's lemma
for modules and the Lie-theoretic Fitting decomposition.  So `PiGroups.fitting` is defined here,
as the join of all normal nilpotent subgroups:

* `PiGroups.le_fitting`: every normal nilpotent subgroup lies in `F(G)` — true by definition;
* `PiGroups.fitting_characteristic`: `F(G)` is characteristic, hence normal;
* `PiGroups.fitting_eq_iSup_piCore`: in a finite group, `F(G)` is the join of the `p`-cores
  `O_p(G)`, so it is the internal product of them;
* `PiGroups.isNilpotent_fitting`: `F(G)` is nilpotent.  This is Fitting's theorem: the content is
  that a join of pairwise commuting normal `p`-subgroups, for distinct primes `p`, is nilpotent;
* `PiGroups.le_fitting_iff`: **Theorem 2.2** itself.

Along the way, two facts of independent interest:

* `PiGroups.isSubnormal_of_isNilpotent` (Isaacs' Lemma 2.1): every subgroup of a finite nilpotent
  group is subnormal — the chain `H < N_G(H) < N_G(N_G(H)) < ⋯` climbs to `G` by the normalizer
  condition;
* `PiGroups.eq_top_of_forall_sylow_le`: a subgroup containing every Sylow subgroup is everything.

Theorem 2.2 is the first step towards Isaacs' Theorem 2.12 (Baer) and 2.13, which
`Isaacs/BurnsidePQTheorem.lean` still carries as the hypothesis
`Burnside.InvolutionInvertsElement` in Step 7 of Burnside's `p ^ a q ^ b` theorem.

The `π`-core machinery is the one from `Isaacs/PiSeparableGroups.lean`: `O_p(G)` is
`PiGroups.piCore {p} G`, whose maximality (`PiGroups.le_piCore`) is what makes the join of the
`p`-cores manageable.

## Relation to the Qiuzhen CFSG development

CFSG defines the same Fitting subgroup — `fittingSubgroup G = sSup {N | N.Normal ∧ IsNilpotent N}`
in `FeitThompson/Fitting/Core.lean` — and proves it normal, characteristic, equal to the join of
the `p`-cores, and nilpotent; it also has Lemma 2.1 twice over
(`GorensteinWalter/Section2/ControlCore.lean` and `FeitThompson/BGsection8/theorem_8_1.lean`, the
latter with the same `Nat.card G - Nat.card H` induction used here).  What it does not have is
Theorem 2.2: nothing there connects `Subgroup.IsSubnormal` to the Fitting subgroup.  Two
deliberate differences in what is done here: nilpotency of a join comes from surjectivity of
`A × B →* ↥(A ⊔ B)` (`PiGroups.isNilpotent_sup_of_commute`), so no independence or coprimality of
orders is needed, where CFSG builds the internal direct product with `Subgroup.noncommPiCoprod`
and `iSupIndep`; and the cores are the `π`-cores of this development rather than a separate
`pCore`.

For Isaacs 2.13 there is a shorter route than 2.12 that skips the Fitting subgroup altogether:
CFSG proves the **Baer–Suzuki theorem** (`BaerSuzuki.baer_suzuki`, by Alperin–Lyons), that a
`p`-element `x` with `⟨x, x ^ g⟩` a `p`-group for all `g` lies in `O_p(G)`.  Its contrapositive at
`p = 2` gives exactly the `g` that Isaacs extracts from Baer's theorem, and the rest of 2.13 is
the elementary computation that two involutions `t`, `u` satisfy `t (tu) t⁻¹ = (tu)⁻¹`.
-/

@[expose] public section

namespace PiGroups

universe u

variable {G : Type u} [Group G]

/-!
## Preliminaries
-/

/-- A proper subgroup of a finite group is smaller. -/
theorem card_lt_card_of_lt [Finite G] {A B : Subgroup G} (hlt : A < B) :
    Nat.card A < Nat.card B := by
  have hle : Nat.card A ≤ Nat.card B := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hlt.le)
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exact absurd (Subgroup.eq_of_le_of_card_ge hlt.le h.ge) hlt.ne

/-- A finite `p`-group is a `{p}`-group.  (Converse of `PiGroups.IsPiGroup.isPGroup`.) -/
theorem IsPGroup.isPiGroup {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (h : IsPGroup p X) : IsPiGroup ({p} : Set ℕ) X := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := h.exists_card_eq
  rw [IsPiGroup.iff_card]
  intro r hr
  obtain ⟨hrp, hrdvd, -⟩ := Nat.mem_primeFactors.mp hr
  rw [hn] at hrdvd
  exact (Nat.prime_dvd_prime_iff_eq hrp hp).mp (hrp.dvd_of_dvd_pow hrdvd)

/-- A subgroup that contains every Sylow subgroup is the whole group: its order is divisible by
every prime power dividing `|G|`. -/
theorem eq_top_of_forall_sylow_le [Finite G] {K : Subgroup G}
    (hK : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, (P : Subgroup G) ≤ K) : K = ⊤ := by
  refine Subgroup.eq_of_le_of_card_ge le_top ?_
  rw [Subgroup.card_top]
  refine Nat.le_of_dvd Nat.card_pos ?_
  refine (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mp ?_
  rw [Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
    have h1 : Nat.card ↥(P : Subgroup G) ∣ Nat.card ↥K := Subgroup.card_dvd_of_le (hK p hp P)
    rw [P.card_eq_multiplicity] at h1
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp h1
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

/-!
## Subgroups of nilpotent groups are subnormal

This is Isaacs' Lemma 2.1.  `mathlib` has the normalizer condition for nilpotent groups
(`Group.normalizerCondition_of_isNilpotent`) and the inductive predicate `Subgroup.IsSubnormal`;
all that is needed is to climb the normalizer chain, which strictly increases the order.
-/

/-- Under the normalizer condition every subgroup is subnormal: climb the normalizer chain. -/
theorem isSubnormal_of_normalizerCondition [Finite G] (hnc : NormalizerCondition G)
    (H : Subgroup G) : H.IsSubnormal := by
  have key : ∀ (n : ℕ) (K : Subgroup G), Nat.card G - Nat.card K ≤ n → K.IsSubnormal := by
    intro n
    induction n with
    | zero =>
      intro K hK
      have hle : Nat.card K ≤ Nat.card G := Subgroup.card_le_card_group K
      have hKG : Nat.card K = Nat.card G := by omega
      rw [Subgroup.eq_top_of_card_eq K hKG]
      exact Subgroup.IsSubnormal.top
    | succ n ih =>
      intro K hK
      rcases eq_or_ne K ⊤ with rfl | hne
      · exact Subgroup.IsSubnormal.top
      · have hlt : K < Subgroup.normalizer (K : Set G) := hnc K hne.lt_top
        refine Subgroup.IsSubnormal.step K (Subgroup.normalizer (K : Set G))
          Subgroup.le_normalizer (ih _ ?_) inferInstance
        have h1 : Nat.card K < Nat.card (Subgroup.normalizer (K : Set G)) :=
          card_lt_card_of_lt hlt
        have h2 : Nat.card (Subgroup.normalizer (K : Set G)) ≤ Nat.card G :=
          Subgroup.card_le_card_group _
        omega
  exact key (Nat.card G) H (Nat.sub_le _ _)

/-- **Isaacs, Lemma 2.1.**  Every subgroup of a finite nilpotent group is subnormal. -/
theorem isSubnormal_of_isNilpotent [Finite G] [Group.IsNilpotent G] (H : Subgroup G) :
    H.IsSubnormal :=
  isSubnormal_of_normalizerCondition Group.normalizerCondition_of_isNilpotent H

/-!
## Fitting's theorem

A join of two nilpotent subgroups that centralize each other is nilpotent, because it is the image
of their direct product.  For the `p`-cores of a finite group this applies: distinct primes give
subgroups that meet trivially, and normal subgroups meeting trivially commute elementwise.
-/

/-- If two nilpotent subgroups centralize each other, their join is nilpotent: it is the image of
`A × B` under the multiplication homomorphism. -/
theorem isNilpotent_sup_of_commute {A B : Subgroup G} [B.Normal] (hA : Group.IsNilpotent A)
    (hB : Group.IsNilpotent B) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Group.IsNilpotent ↥(A ⊔ B) := by
  have := hA
  have := hB
  refine Group.nilpotent_of_surjective
    ((Subgroup.inclusion (le_sup_left : A ≤ A ⊔ B)).noncommCoprod
      (Subgroup.inclusion (le_sup_right : B ≤ A ⊔ B))
      (fun a b => Subtype.ext (hcomm a a.2 b b.2))) ?_
  rintro ⟨x, hx⟩
  rw [← SetLike.mem_coe, Subgroup.mul_normal A B] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext rfl⟩

/-- The join of the `p`-cores over a finite set of primes is nilpotent. -/
theorem isNilpotent_iSup_piCore [Finite G] (S : Finset ℕ) :
    (∀ p ∈ S, p.Prime) → Group.IsNilpotent ↥(⨆ p ∈ S, piCore ({p} : Set ℕ) G) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _
    have hbot : (⨆ p ∈ (∅ : Finset ℕ), piCore ({p} : Set ℕ) G) = ⊥ := by simp
    rw [hbot]
    infer_instance
  | insert p S hpS ih =>
    intro hS
    rw [Finset.iSup_insert]
    have hp : p.Prime := hS p (Finset.mem_insert_self p S)
    have : Fact p.Prime := ⟨hp⟩
    have hBnil := ih fun r hr => hS r (Finset.mem_insert_of_mem hr)
    -- the `p`-core is a `p`-group, hence nilpotent
    have hApi : IsPiGroup ({p} : Set ℕ) (piCore ({p} : Set ℕ) G) := isPiGroup_piCore
    have hAnil : Group.IsNilpotent ↥(piCore ({p} : Set ℕ) G) :=
      (IsPiGroup.isPGroup hApi).isNilpotent
    -- the rest of the join is an `S`-group, so the two meet trivially
    have hBle : (⨆ r ∈ S, piCore ({r} : Set ℕ) G) ≤ piCore (↑S : Set ℕ) G :=
      iSup₂_le fun r hr => le_piCore inferInstance
        (isPiGroup_piCore.mono (Set.singleton_subset_iff.mpr (by exact_mod_cast hr)))
    have hBpi : IsPiGroup (↑S : Set ℕ) ↑(⨆ r ∈ S, piCore ({r} : Set ℕ) G) :=
      IsPiGroup.of_le hBle isPiGroup_piCore
    have hApi' : IsPiGroup ((↑S : Set ℕ)ᶜ) (piCore ({p} : Set ℕ) G) :=
      hApi.mono (Set.singleton_subset_iff.mpr (by exact_mod_cast hpS))
    have hdisj : Disjoint (piCore ({p} : Set ℕ) G) (⨆ r ∈ S, piCore ({r} : Set ℕ) G) :=
      (disjoint_of_isPiGroup hBpi hApi').symm
    exact isNilpotent_sup_of_commute hAnil hBnil
      (commute_of_disjoint_of_normalIn le_top le_top inferInstance inferInstance hdisj)

/-- In a finite nilpotent group the `p`-cores, taken over any set of primes containing the prime
divisors of the order, generate the whole group: they are the Sylow subgroups. -/
theorem iSup_piCore_eq_top [Finite G] [Group.IsNilpotent G] {S : Finset ℕ}
    (hS : (Nat.card G).primeFactors ⊆ S) : (⨆ p ∈ S, piCore ({p} : Set ℕ) G) = ⊤ := by
  refine eq_top_of_forall_sylow_le fun p hp P => ?_
  have : Fact p.Prime := ⟨hp⟩
  by_cases hdvd : p ∣ Nat.card G
  · have hpS : p ∈ S := hS (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩)
    refine le_trans (le_piCore inferInstance (IsPGroup.isPiGroup hp P.isPGroup')) ?_
    exact le_iSup₂ (f := fun p (_ : p ∈ S) => piCore ({p} : Set ℕ) G) p hpS
  · have hcard : Nat.card ↥(P : Subgroup G) = 1 := by
      rw [P.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hdvd, pow_zero]
    rw [Subgroup.card_eq_one.mp hcard]
    exact bot_le

/-!
## The Fitting subgroup
-/

variable (G) in
/-- **The Fitting subgroup** `F(G)`: the join of all the normal nilpotent subgroups of `G`.  In a
finite group it is itself nilpotent (`PiGroups.isNilpotent_fitting`), so it is the largest normal
nilpotent subgroup. -/
def fitting : Subgroup G := sSup {N : Subgroup G | N.Normal ∧ Group.IsNilpotent N}

/-- Every normal nilpotent subgroup lies in the Fitting subgroup. -/
theorem le_fitting {N : Subgroup G} (hN : N.Normal) (hnil : Group.IsNilpotent N) :
    N ≤ fitting G :=
  le_sSup ⟨hN, hnil⟩

instance fitting_characteristic : (fitting G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK ↦ ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have := hK.2
  exact le_fitting (hK.1.map _ φ.surjective) (Group.nilpotent_of_mulEquiv (φ.subgroupMap K))

/-- In a finite group the Fitting subgroup is the join of the `p`-cores. -/
theorem fitting_eq_iSup_piCore [Finite G] :
    fitting G = ⨆ p ∈ (Nat.card G).primeFactors, piCore ({p} : Set ℕ) G := by
  refine le_antisymm (sSup_le ?_) ?_
  · rintro N ⟨hN, hnil⟩
    have := hN
    have := hnil
    have hsub : (Nat.card ↥N).primeFactors ⊆ (Nat.card G).primeFactors :=
      Nat.primeFactors_mono (Subgroup.card_subgroup_dvd_card N) Nat.card_pos.ne'
    have htop : (⨆ p ∈ (Nat.card G).primeFactors, piCore ({p} : Set ℕ) ↥N) = ⊤ :=
      iSup_piCore_eq_top hsub
    calc N = (⊤ : Subgroup ↥N).map N.subtype := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = (⨆ p ∈ (Nat.card G).primeFactors, piCore ({p} : Set ℕ) ↥N).map N.subtype := by
          rw [htop]
      _ = ⨆ p ∈ (Nat.card G).primeFactors, (piCore ({p} : Set ℕ) ↥N).map N.subtype := by
          simp only [Subgroup.map_iSup]
      _ ≤ ⨆ p ∈ (Nat.card G).primeFactors, piCore ({p} : Set ℕ) G :=
          iSup₂_mono fun p _ => le_piCore inferInstance
            (isPiGroup_piCore.of_equiv
              ((piCore ({p} : Set ℕ) ↥N).equivMapOfInjective _ N.subtype_injective))
  · refine iSup₂_le fun p hp => ?_
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hp'⟩
    exact le_fitting inferInstance (IsPiGroup.isPGroup isPiGroup_piCore).isNilpotent

/-- **Fitting's theorem.**  The Fitting subgroup of a finite group is nilpotent, so it is the
largest normal nilpotent subgroup. -/
instance isNilpotent_fitting [Finite G] : Group.IsNilpotent ↥(fitting G) := by
  have := isNilpotent_iSup_piCore (G := G) (Nat.card G).primeFactors fun p hp =>
    Nat.prime_of_mem_primeFactors hp
  exact Group.nilpotent_of_mulEquiv (MulEquiv.subgroupCongr fitting_eq_iSup_piCore.symm)

/-!
## Isaacs' Theorem 2.2
-/

/-- The hard half of Isaacs' Theorem 2.2, by induction on `|G|`: a nilpotent subnormal subgroup
lies in the Fitting subgroup.  If `H < G`, a penultimate term `M` of a subnormal chain from `H` is
normal in `G` and proper, `H` is nilpotent and subnormal in `M`, and `F(M)` is characteristic in
`M`, hence a normal nilpotent subgroup of `G`. -/
theorem le_fitting_of_isNilpotent_of_isSubnormal :
    ∀ (n : ℕ) (X : Type u) [Group X] [Finite X], Nat.card X ≤ n →
      ∀ H : Subgroup X, Group.IsNilpotent ↥H → H.IsSubnormal → H ≤ fitting X := by
  intro n
  induction n with
  | zero =>
    intro X _ _ hcard H _ _
    have := Nat.card_pos (α := X)
    omega
  | succ n ih =>
    intro X _ _ hcard H hnil hsub
    rcases eq_or_ne H ⊤ with rfl | hne
    · have := hnil
      have : Group.IsNilpotent X := Group.nilpotent_of_mulEquiv Subgroup.topEquiv
      exact le_fitting inferInstance hnil
    · obtain ⟨M, hMnormal, hHM, hMlt⟩ := hsub.exists_normal_and_le_and_lt_top_of_ne hne
      have := hMnormal
      have hcardM : Nat.card ↥M < Nat.card X := by
        have h1 := card_lt_card_of_lt hMlt
        rwa [Subgroup.card_top] at h1
      have hHMnil : Group.IsNilpotent ↥(H.subgroupOf M) := by
        have := hnil
        exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHM).symm
      have hle : H.subgroupOf M ≤ fitting ↥M :=
        ih ↥M (by omega) _ hHMnil hsub.subgroupOf
      have h1 : H ≤ (fitting ↥M).map M.subtype := by
        have h2 := Subgroup.map_mono (f := M.subtype) hle
        rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hHM] at h2
      exact h1.trans (le_fitting inferInstance
        (Group.nilpotent_of_mulEquiv ((fitting ↥M).equivMapOfInjective _ M.subtype_injective)))

/-- **Isaacs, Theorem 2.2.**  A subgroup of a finite group lies in the Fitting subgroup exactly
when it is nilpotent and subnormal. -/
theorem le_fitting_iff [Finite G] {H : Subgroup G} :
    H ≤ fitting G ↔ Group.IsNilpotent ↥H ∧ H.IsSubnormal := by
  constructor
  · intro hle
    have hnil : Group.IsNilpotent ↥(H.subgroupOf (fitting G)) := inferInstance
    refine ⟨Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle), ?_⟩
    exact Subgroup.IsSubnormal.trans hle
      (isSubnormal_of_isNilpotent (H.subgroupOf (fitting G)))
      (Subgroup.Normal.isSubnormal inferInstance)
  · rintro ⟨hnil, hsub⟩
    exact le_fitting_of_isNilpotent_of_isSubnormal (Nat.card G) G le_rfl H hnil hsub

end PiGroups
