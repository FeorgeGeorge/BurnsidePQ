module

public import Isaacs.PLocalSubgroups
public import Isaacs.NoncyclicAbelianAction
public import Isaacs.InvolutionInverts
public import Isaacs.ThompsonNormalPComplement
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Burnside's `p ^ a q ^ b` theorem

Isaacs, *Finite Group Theory*, Theorem 7.8: a finite group of order `p ^ a * q ^ b`, for primes
`p` and `q`, is solvable.  `mathlib` has Burnside's *normal `p`-complement* theorem
(`Mathlib/GroupTheory/Transfer.lean`) and Burnside's counting lemma, but not this theorem.

Isaacs argues from a counterexample of smallest order.  This file sets that situation up as
`Burnside.IsMinCounterexample`, proves the reductions of the opening paragraph of his proof, and
then runs all nine of his steps to the contradiction.

The reductions:

* `Burnside.IsMinCounterexample.isSolvable_subgroup` / `.isSolvable_quotient`: every proper
  subgroup and every proper quotient is solvable, because its order still has at most the two
  prime divisors `p` and `q`;
* `Burnside.IsMinCounterexample.isSimpleGroup`: hence `G` is simple, since an extension of
  solvable by solvable is solvable;
* `Burnside.IsMinCounterexample.normalizer_eq_of_isCoatom`: if `1 < K ⊴ M` with `M` maximal, then
  `N_G(K) = M` — the observation Isaacs says "will be used repeatedly";
* `Burnside.IsMinCounterexample.piCore_ne_bot_or_of_isCoatom`: a maximal subgroup `M` is solvable
  and nontrivial, so `O_p(M) > 1` or `O_q(M) > 1`.

Then the nine steps:

* `.step1` and `.step1_of_isNilpotent` — the normalizer of a nilpotent subgroup whose order both
  primes divide is, when maximal, the unique maximal subgroup containing it;
* `.step2` — a nontrivial subgroup normalized by a Sylow `p`-subgroup generates `G` with any
  Sylow `q`-subgroup, and so is not a `q`-group;
* `.step3` — a maximal subgroup has `O_p(M) = 1` or `O_q(M) = 1`, and hence (`.piPart_ne_bot_xor`)
  exactly one of the two is nontrivial;
* `.step4` — a `p`-subgroup normalized by a `q`-central element contains no `p`-central element,
  where `Burnside.IsPCentral p x` says that `x ≠ 1` lies in the centre of some Sylow `p`-subgroup;
* `.exists_isPCentral_mem_centralizer` and `.step5` — every `p`-subgroup is centralized by a
  `p`-central element, and a maximal subgroup of `p`-type contains no `q`-central element;
* `.step6` — a `q`-central element normalizes no nontrivial `p`-subgroup;
* `.step7` — `q ≠ 2`, given `Burnside.InvolutionInvertsElement` (Isaacs' Theorem 2.13), a
  hypothesis discharged by `PiGroups.involutionInvertsElement` in
  `Isaacs/InvolutionInverts.lean`;
* `.step8` — if `M` is a `p`-type maximal subgroup and `S ∈ Syl_p(M)`, then `J(S) ⊴ M` and `S` is
  a full Sylow `p`-subgroup of `G`.  `M` satisfies the five hypotheses of Thompson's normal-`J`
  theorem (7.6, `PiGroups.thompsonSubgroup_normal`): it is solvable, `p ≠ 2` by Step 7, its Sylow
  `2`-subgroups are trivial because `|G|` is odd, `O_p′(M) = O_q(M) = 1` because `M` is of
  `p`-type, and `C_M(Z(S)) = S` because `Z(S)` contains the `p`-central subgroup `Z(P)` for any
  `P ∈ Syl_p(G)` above `S`, so Step 6 forbids an element of order `q` in `C_M(Z(S))`.  If `S`
  were not Sylow in `G`, normalizers would grow to a `p`-group `T > S` normalizing `J(S)`, giving
  `T ≤ N_G(J(S)) = M` against `S ∈ Syl_p(M)`;
* `.step9` — the contradiction.  Choose `S, T ∈ Syl_p(G)` with `J(S) ≠ J(T)` and `D = S ⊓ T` as
  large as possible; `D > 1` by counting, so `N_G(D)` is proper and lies in a maximal `M`, which
  contains a `p`-central element and hence is of `p`-type.  A Sylow `p`-subgroup `U` of `M` above
  `M ⊓ S` is Sylow in `G` by Step 8 and meets `S` above `D`, so `J(U) = J(S)` by maximality, and
  likewise `J(V) = J(T)`.  But `U` and `V` are `M`-conjugate while `J(U) ⊴ M`, so `J(S) = J(T)`.

`Burnside.isSolvable_of_card_eq_pow_mul_pow` is the theorem itself.

Four remarks on the formalization.

*Minimal counterexamples.*  `IsMinCounterexample p q G` bundles Isaacs' three standing
assumptions.  `Burnside.isSolvable_of_forall_not_isMinCounterexample` shows this really does
reduce the theorem: if no group is a minimal counterexample, every `{p, q}`-group is solvable.
So the whole of the work is to refute `IsMinCounterexample`, which
`Burnside.not_isMinCounterexample` does.

*`{p, q}`-groups.*  "The order of `G` has at most the two prime divisors `p` and `q`" is
`PiGroups.IsPiGroup {p, q} G`, which by `PiGroups.IsPiGroup.iff_card` says precisely that
`(Nat.card G).primeFactors ⊆ {p, q}`.  Phrasing it this way rather than as `∃ a b, Nat.card G =
p ^ a * q ^ b` makes the closure under subgroups and quotients immediate, and connects directly
to the `π`-separability API: `O_p(M)` is `piCore {p} M` and `O_q(M)` is `piCore {p}ᶜ M`, the two
cores that `PiGroups.IsPiSeparable.piCore_ne_bot_or` produces.

*Isaacs' counting.*  Step 9 opens with `|G_p|² > |G_p||G_q| = |G| ≥ |ST| = |G_p|²/|S ∩ T|`.
`Burnside.IsMinCounterexample.one_lt_card_inf_sylow` reaches the same conclusion from
`|S ⊓ T : 1| ≤ |S : 1| ⋅ |T : 1|` (`Subgroup.index_inf_le`), which avoids the product formula
for the set `ST`.

*Symmetry.*  Isaacs says at Step 9 "we can assume that `|G|_p > |G|_q`".  Here the step is proved
as `step9_aux` under that hypothesis and then applied to `h` or to `h.symm`, the same minimal
counterexample with `p` and `q` interchanged.

Two results from elsewhere in the development carry the proof.  Step 1 needs Isaacs' Theorem 4.33
(`O_p'(H) ≤ O_p'(G)` for `p`-local `H` in a `p`-solvable `G`), which is
`PiGroups.map_piCore_compl_le_piCore_compl`; Steps 8 and 9 need Thompson's normal-`J` theorem
(7.6), which is `PiGroups.thompsonSubgroup_normal` in `Isaacs/NormalJTheorem.lean`.
-/

@[expose] public section

namespace Burnside

open PiGroups

universe u

variable {p q : ℕ} {G : Type u} [Group G] [Finite G]

/-!
## `{p, q}`-groups
-/

/-- In a `{p, q}`-group with `p ≠ q`, being a `p'`-group is being a `q`-group. -/
theorem isPiGroup_compl_singleton_iff {X : Type*} [Group X] [Finite X] (hpq : p ≠ q)
    (hX : IsPiGroup {p, q} X) : IsPiGroup ({p}ᶜ : Set ℕ) X ↔ IsPiGroup {q} X := by
  rw [IsPiGroup.iff_card] at hX
  rw [IsPiGroup.iff_card, IsPiGroup.iff_card]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_compl_iff] at hX ⊢
  refine ⟨fun h r hr ↦ ?_, fun h r hr ↦ ?_⟩
  · rcases hX r hr with h1 | h1
    · exact absurd h1 (h r hr)
    · exact h1
  · rw [h r hr]
    exact fun hc ↦ hpq hc.symm

/-- `O_p'(X) = O_q(X)` in a `{p, q}`-group. -/
theorem piCore_compl_singleton_eq {X : Type*} [Group X] [Finite X] (hpq : p ≠ q)
    (hX : IsPiGroup {p, q} X) : piCore ({p}ᶜ : Set ℕ) X = piCore {q} X := by
  unfold piCore
  congr 1
  ext K
  exact and_congr_right fun _ ↦ isPiGroup_compl_singleton_iff hpq (hX.to_subgroup K)

/-- A group whose order is `p ^ a * q ^ b` for primes `p`, `q` is a `{p, q}`-group. -/
theorem isPiGroup_pair_of_card_eq {X : Type*} [Group X] [Finite X] {a b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hcard : Nat.card X = p ^ a * q ^ b) : IsPiGroup {p, q} X := by
  rw [IsPiGroup.iff_card]
  intro r hr
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  have hdvd : r ∣ p ^ a * q ^ b := hcard ▸ Nat.dvd_of_mem_primeFactors hr
  rcases (Nat.Prime.dvd_mul hrp).mp hdvd with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hrp hp).mp (hrp.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hrp hq).mp (hrp.dvd_of_dvd_pow h))

/-- A proper subgroup of a finite group is smaller than the group. -/
theorem card_lt_of_ne_top {K : Subgroup G} (hK : K ≠ ⊤) : Nat.card K < Nat.card G := by
  rw [← K.index_mul_card]
  exact lt_mul_of_one_lt_left Nat.card_pos (Subgroup.one_lt_index_of_ne_top hK)

/-!
## The minimal counterexample
-/

/-- Isaacs' setting for Theorem 7.8: `G` is a counterexample to Burnside's theorem of smallest
possible order.  Every `{p, q}`-group of smaller order is solvable, but `G` is not. -/
structure IsMinCounterexample (p q : ℕ) (G : Type u) [Group G] [Finite G] : Prop where
  /-- The order of `G` is divisible by no primes other than `p` and `q`. -/
  isPiGroup : IsPiGroup {p, q} G
  /-- `G` is a counterexample. -/
  not_isSolvable : ¬ Group.IsSolvable G
  /-- It is one of smallest order. -/
  min : ∀ (H : Type u) [Group H] [Finite H], IsPiGroup {p, q} H → Nat.card H < Nat.card G →
    Group.IsSolvable H

namespace IsMinCounterexample

variable (h : IsMinCounterexample p q G)

include h

theorem nontrivial : Nontrivial G := by
  rcases subsingleton_or_nontrivial G with hs | hs
  · exact absurd (inferInstance : Group.IsSolvable G) h.not_isSolvable
  · exact hs

/-- Every proper subgroup of the minimal counterexample is solvable. -/
theorem isSolvable_subgroup (K : Subgroup G) (hK : K ≠ ⊤) : Group.IsSolvable K :=
  h.min K (h.isPiGroup.to_subgroup K) (card_lt_of_ne_top hK)

/-- Every proper quotient of the minimal counterexample is solvable. -/
theorem isSolvable_quotient (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : Group.IsSolvable (G ⧸ N) :=
  h.min (G ⧸ N) (h.isPiGroup.to_quotient N) (card_quotient_lt N hN)

/-- **The minimal counterexample is simple**: a nontrivial proper normal subgroup would split it
into two solvable pieces. -/
theorem isSimpleGroup : IsSimpleGroup G where
  toNontrivial := h.nontrivial
  eq_bot_or_eq_top_of_normal N hN := by
    by_contra hcon
    push Not at hcon
    have := hN
    have : Group.IsSolvable N := h.isSolvable_subgroup N hcon.2
    have : Group.IsSolvable (G ⧸ N) := h.isSolvable_quotient N hcon.1
    refine h.not_isSolvable (Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) ?_)
    rw [QuotientGroup.ker_mk', N.range_subtype]

/-- A maximal subgroup of the minimal counterexample is nontrivial: otherwise every proper
subgroup would be trivial, making `G` cyclic. -/
theorem ne_bot_of_isCoatom {M : Subgroup G} (hM : IsCoatom M) : M ≠ ⊥ := by
  rintro rfl
  have := h.nontrivial
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hgen : Subgroup.zpowers g = ⊤ :=
    hM.2 _ (bot_lt_iff_ne_bot.mpr (fun hc ↦ hg (Subgroup.zpowers_eq_bot.mp hc)))
  have : IsCyclic G := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, hgen⟩
  exact h.not_isSolvable (Group.isSolvable_of_comm (IsCyclic.commGroup (α := G)).mul_comm)

/-- A maximal subgroup of the minimal counterexample is solvable. -/
theorem isSolvable_of_isCoatom {M : Subgroup G} (hM : IsCoatom M) : Group.IsSolvable M :=
  h.isSolvable_subgroup M hM.1

/-- **Isaacs' repeatedly used observation.**  If `K` is a nontrivial normal subgroup of a maximal
subgroup `M`, then `M = N_G(K)`: indeed `M ≤ N_G(K)`, and `N_G(K) ≠ G` because `G` is simple. -/
theorem normalizer_eq_of_isCoatom {M K : Subgroup G} (hM : IsCoatom M) (hKM : K ≤ M)
    [hKnorm : (K.subgroupOf M).Normal] (hK : K ≠ ⊥) : Subgroup.normalizer (K : Set G) = M := by
  have := h.isSimpleGroup
  have hle : M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKnorm
  have hne : Subgroup.normalizer (K : Set G) ≠ ⊤ := by
    intro htop
    have : K.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K ‹K.Normal› with hbot | htop'
    · exact hK hbot
    · exact hM.1 (top_le_iff.mp (htop' ▸ hKM))
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact heq.symm
  · exact absurd (hM.2 _ hlt) hne

/-- **Isaacs' starting point for the maximal subgroups.**  A maximal subgroup `M` of the minimal
counterexample is solvable and nontrivial, hence has a nonidentity normal subgroup of prime-power
order: either `O_p(M) > 1` or `O_q(M) > 1`. -/
theorem piCore_ne_bot_or_of_isCoatom (hpq : p ≠ q) {M : Subgroup G} (hM : IsCoatom M) :
    piCore {p} M ≠ ⊥ ∨ piCore {q} M ≠ ⊥ := by
  have : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).mpr (h.ne_bot_of_isCoatom hM)
  have : Group.IsSolvable M := h.isSolvable_of_isCoatom hM
  rcases (IsPiSeparable.of_isSolvable (π := {p}) (G := M)).piCore_ne_bot_or with hc | hc
  · exact Or.inl hc
  · exact Or.inr (by rwa [piCore_compl_singleton_eq hpq (h.isPiGroup.to_subgroup M)] at hc)

end IsMinCounterexample

/-!
## Sylow subgroups of a `{p, q}`-group
-/

/-- The order of a `{p, q}`-group is `p ^ a * q ^ b`. -/
theorem card_eq_pow_mul_pow {X : Type*} [Group X] [Finite X] (hpq : p ≠ q)
    (hX : IsPiGroup {p, q} X) :
    Nat.card X = p ^ (Nat.card X).factorization p * q ^ (Nat.card X).factorization q := by
  classical
  have hne : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have hsub : (Nat.card X).factorization.support ⊆ ({p, q} : Finset ℕ) := by
    intro r hr
    rw [Nat.support_factorization] at hr
    rcases IsPiGroup.iff_card.mp hX r hr with hr' | hr' <;> subst hr' <;> simp
  have hprod : (Nat.card X).factorization.prod (· ^ ·)
      = ∏ r ∈ ({p, q} : Finset ℕ), r ^ (Nat.card X).factorization r :=
    Finset.prod_subset hsub (fun r _ hr => by simp [Finsupp.notMem_support_iff.mp hr])
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hne]
  rw [hprod, Finset.prod_pair hpq]

/-- In a `{p, q}`-group, a Sylow `p`-subgroup and a Sylow `q`-subgroup are complements. -/
theorem isComplement'_sylow {X : Type*} [Group X] [Finite X] (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hX : IsPiGroup {p, q} X) (P : Sylow p X) (Q : Sylow q X) :
    (P : Subgroup X).IsComplement' (Q : Subgroup X) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
  · rw [P.card_eq_multiplicity, Q.card_eq_multiplicity]
    exact (card_eq_pow_mul_pow hpq hX).symm
  · exact IsPGroup.disjoint_of_ne p q hpq _ _ P.isPGroup' Q.isPGroup'

/-!
## The `p`-part of a subgroup

`piPart π K` is `O_π(K)` viewed as a subgroup of the ambient group.  Since `O_π` is characteristic,
it is carried along by any conjugation that stabilizes `K` (`map_conj_piPart`), which is how
`K ⊴ M` upgrades to `K_p ⊴ M` in Isaacs' argument.
-/

/-- `O_π(K)`, as a subgroup of the ambient group. -/
def piPart (π : Set ℕ) (K : Subgroup G) : Subgroup G := (piCore π K).map K.subtype

omit [Finite G] in
theorem piPart_le (π : Set ℕ) (K : Subgroup G) : piPart π K ≤ K := Subgroup.map_subtype_le _

theorem isPiGroup_piPart (π : Set ℕ) (K : Subgroup G) : IsPiGroup π (piPart π K) :=
  isPiGroup_piCore.of_equiv ((piCore π K).equivMapOfInjective _ K.subtype_injective)

omit [Finite G] in
/-- A `π`-subgroup of `K` that is normalized by `K` lies in `O_π(K)`. -/
theorem le_piPart {π : Set ℕ} {K A : Subgroup G} (hAK : A ≤ K)
    (hnorm : K ≤ Subgroup.normalizer A) (hA : IsPiGroup π A) : A ≤ piPart π K := by
  have hnormal : (A.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).mpr hnorm
  have hpi : IsPiGroup π (A.subgroupOf K) :=
    hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAK).symm
  have := Subgroup.map_mono (f := K.subtype) (le_piCore hnormal hpi)
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAK] at this

omit [Finite G] in
/-- Conjugation that stabilizes `K` stabilizes `O_π(K)`. -/
theorem map_conj_piPart (π : Set ℕ) {K : Subgroup G} {g : G}
    (hg : K.map (MulAut.conj g).toMonoidHom = K) :
    (piPart π K).map (MulAut.conj g).toMonoidHom = piPart π K := by
  let e : ↥K ≃* ↥K := ((MulAut.conj g).subgroupMap K).trans (MulEquiv.subgroupCongr hg)
  have hchar : (piCore π ↥K).map e.toMonoidHom = piCore π ↥K :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance e
  have hcomp : K.subtype.comp e.toMonoidHom = ((MulAut.conj g).toMonoidHom).comp K.subtype :=
    MonoidHom.ext fun _ => rfl
  calc (piPart π K).map (MulAut.conj g).toMonoidHom
      = (piCore π ↥K).map (((MulAut.conj g).toMonoidHom).comp K.subtype) := by
        rw [piPart, Subgroup.map_map]
    _ = (piCore π ↥K).map (K.subtype.comp e.toMonoidHom) := by rw [hcomp]
    _ = ((piCore π ↥K).map e.toMonoidHom).map K.subtype := by rw [← Subgroup.map_map]
    _ = piPart π K := by rw [hchar, piPart]

omit [Finite G] in
/-- `O_π(K)` is normal in anything that normalizes `K`. -/
theorem piPart_normal_of_le_normalizer {π : Set ℕ} {K M : Subgroup G}
    (hM : M ≤ Subgroup.normalizer K) : M ≤ Subgroup.normalizer (piPart π K) := by
  intro g hg
  exact map_conj_eq_self_iff.mp (map_conj_piPart π (map_conj_eq_self_iff.mpr (hM hg)))

/-- The `p`- and `q`-parts of `K` cover `K`.  This holds when `K` is nilpotent
(`splitsPQ_of_isNilpotent`), and it is what Step 1's induction actually uses. -/
def SplitsPQ (p q : ℕ) (K : Subgroup G) : Prop := piPart {p} K ⊔ piPart {q} K = K

/-- In a finite nilpotent group the Sylow subgroups are normal, so the `p`- and `q`-parts of a
nilpotent `{p, q}`-subgroup cover it. -/
theorem splitsPQ_of_isNilpotent (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {K : Subgroup G}
    (hKnil : Group.IsNilpotent K) (hK : IsPiGroup {p, q} K) : SplitsPQ p q K := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have := hKnil
  obtain ⟨P⟩ : Nonempty (Sylow p ↥K) := inferInstance
  obtain ⟨Q⟩ : Nonempty (Sylow q ↥K) := inferInstance
  -- the Sylow subgroups of a nilpotent group are normal, hence contained in the cores
  have hPn : (P : Subgroup ↥K).Normal :=
    ((Group.isNilpotent_of_finite_tfae (G := ↥K)).out 0 3 :).mp hKnil p inferInstance P
  have hQn : (Q : Subgroup ↥K).Normal :=
    ((Group.isNilpotent_of_finite_tfae (G := ↥K)).out 0 3 :).mp hKnil q inferInstance Q
  have hPle : (P : Subgroup ↥K) ≤ piCore {p} ↥K :=
    le_piCore hPn (IsPiGroup.of_isPGroup (π := ({p} : Set ℕ)) hp rfl P.isPGroup')
  have hQle : (Q : Subgroup ↥K) ≤ piCore {q} ↥K :=
    le_piCore hQn (IsPiGroup.of_isPGroup (π := ({q} : Set ℕ)) hq rfl Q.isPGroup')
  have htop : (P : Subgroup ↥K) ⊔ (Q : Subgroup ↥K) = ⊤ :=
    (isComplement'_sylow hp hq hpq hK P Q).sup_eq_top
  have hsup : piCore {p} ↥K ⊔ piCore {q} ↥K = ⊤ :=
    top_le_iff.mp (htop ▸ sup_le_sup hPle hQle)
  have hmap := congrArg (Subgroup.map K.subtype) hsup
  rwa [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap

/-- `O_π` is carried along by isomorphisms. -/
theorem piCore_map_equiv {A B : Type u} [Group A] [Group B] [Finite A] [Finite B] (π : Set ℕ)
    (e : A ≃* B) : (piCore π A).map e.toMonoidHom = piCore π B := by
  have key : ∀ {C D : Type u} [Group C] [Group D] [Finite C] [Finite D] (f : C ≃* D),
      (piCore π C).map f.toMonoidHom ≤ piCore π D := by
    intro C D _ _ _ _ f
    exact le_piCore (Subgroup.Normal.map inferInstance _ f.surjective)
      (isPiGroup_piCore.of_equiv ((piCore π C).equivMapOfInjective _ f.injective))
  refine le_antisymm (key e) ?_
  have h1 := Subgroup.map_mono (f := e.toMonoidHom) (key e.symm)
  rwa [Subgroup.map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B from
    MonoidHom.ext fun x => by simp, Subgroup.map_id] at h1

/-- The `π`-part of a subgroup, computed inside a larger subgroup. -/
theorem piPart_eq_map_piCore_subgroupOf (π : Set ℕ) {X Y : Subgroup G} (hYX : Y ≤ X) :
    piPart π Y = ((piCore π ↥(Y.subgroupOf X)).map (Y.subgroupOf X).subtype).map X.subtype := by
  rw [Subgroup.map_map, piPart,
    ← piCore_map_equiv π (Subgroup.subgroupOfEquivOfLe hYX), Subgroup.map_map]
  congr 1

/-- **Isaacs 4.33 in the ambient group.**  If `Y ≤ X` is `p`-local in `X` and `X` is `p`-solvable,
then `O_p'(Y) ≤ O_p'(X)`. -/
theorem piPart_compl_le_of_isPLocal (hp : p.Prime) {X Y : Subgroup G}
    (hsep : IsPiSeparable ({p} : Set ℕ) ↥X) (hYX : Y ≤ X)
    (hlocal : IsPLocal p (Y.subgroupOf X)) :
    piPart ({p}ᶜ : Set ℕ) Y ≤ piPart ({p}ᶜ : Set ℕ) X := by
  have : Fact p.Prime := ⟨hp⟩
  have h433 := PiGroups.map_piCore_compl_le_piCore_compl (G := ↥X)
    CoprimeAction.schurZassenhausConjugacy hsep hlocal
  rw [piPart_eq_map_piCore_subgroupOf ({p}ᶜ : Set ℕ) hYX]
  exact Subgroup.map_mono h433

omit [Finite G] in
/-- The centralizer of a subgroup is contained in its normalizer. -/
theorem centralizer_le_normalizer (A : Subgroup G) :
    Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer A := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hcomm : ∀ z ∈ A, x * z = z * x := fun z hz => (Subgroup.mem_centralizer_iff.mp hx z hz).symm
  constructor
  · intro hy
    rw [hcomm y hy]
    simpa using hy
  · intro hy
    have hxy : x * (x * y * x⁻¹) = x * y := by
      rw [hcomm _ hy]
      group
    rwa [mul_left_cancel hxy] at hy

/-- If `K` splits and `p` divides `|K|`, its `p`-part is nontrivial. -/
theorem piPart_ne_bot_of_dvd (hp : p.Prime) (_hq : q.Prime) (hpq : p ≠ q) {K : Subgroup G}
    (hsplit : SplitsPQ p q K) (hpK : p ∣ Nat.card K) : piPart ({p} : Set ℕ) K ≠ ⊥ := by
  intro hbot
  rw [SplitsPQ, hbot, bot_sup_eq] at hsplit
  -- then `K` is a `q`-group, so `p` cannot divide its order
  have hKq : IsPiGroup ({q} : Set ℕ) K := hsplit ▸ isPiGroup_piPart _ _
  have := IsPiGroup.iff_card.mp hKq p (Nat.mem_primeFactors.mpr ⟨hp, hpK, Nat.card_pos.ne'⟩)
  exact hpq this

namespace IsMinCounterexample

variable (h : IsMinCounterexample p q G)

include h

/-- The setting is symmetric in `p` and `q`. -/
theorem symm : IsMinCounterexample q p G where
  isPiGroup := by rw [Set.pair_comm]; exact h.isPiGroup
  not_isSolvable := h.not_isSolvable
  min := by
    intro H _ _ hH hlt
    exact h.min H (by rw [Set.pair_comm]; exact hH) hlt

/-- Both primes divide the order of the minimal counterexample: otherwise it would be a
`p`-group or a `q`-group, hence nilpotent, hence solvable. -/
theorem prime_dvd_card (_hp : p.Prime) (hq : q.Prime) : p ∣ Nat.card G := by
  by_contra hcon
  have hq' : IsPiGroup ({q} : Set ℕ) G := by
    rw [IsPiGroup.iff_card]
    intro r hr
    rcases IsPiGroup.iff_card.mp h.isPiGroup r hr with hr' | hr'
    · exact absurd (hr' ▸ Nat.dvd_of_mem_primeFactors hr) hcon
    · exact hr'
  have : Fact q.Prime := ⟨hq⟩
  have : Group.IsNilpotent G := (IsPiGroup.isPGroup hq').isNilpotent
  exact h.not_isSolvable inferInstance

/-!
## Step 2
-/

/-- **Isaacs' Step 2.**  If a Sylow `p`-subgroup normalizes a nontrivial subgroup `V`, then `V`
together with any Sylow `q`-subgroup generates `G`.

Writing `g = y x` with `y ∈ Q` and `x ∈ P` — possible because `P` and `Q` are complements — the
conjugate `g V g⁻¹ = y V y⁻¹` lies in `⟨V, Q⟩`, so `⟨V, Q⟩` contains the normal closure of `V`,
which is nontrivial and hence everything by simplicity. -/
theorem step2 (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (P : Sylow p G) (Q : Sylow q G)
    {V : Subgroup G} (hV : V ≠ ⊥) (hPV : (P : Subgroup G) ≤ Subgroup.normalizer V) :
    V ⊔ (Q : Subgroup G) = ⊤ := by
  have := h.isSimpleGroup
  have hcompl := (isComplement'_sylow hp hq hpq h.isPiGroup P Q).symm
  -- every conjugate of `V` lies in `⟨V, Q⟩`
  have hconjle : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ V ⊔ (Q : Subgroup G) := by
    intro g
    obtain ⟨⟨y, x⟩, hyx⟩ := hcompl.2 g
    have hyx' : (y : G) * (x : G) = g := hyx
    have hgV : V.map (MulAut.conj g).toMonoidHom
        = V.map (MulAut.conj (y : G)).toMonoidHom := by
      have hx : V.map (MulAut.conj (x : G)).toMonoidHom = V :=
        map_conj_eq_self_iff.mpr (hPV x.2)
      calc V.map (MulAut.conj g).toMonoidHom
          = V.map (MulAut.conj ((y : G) * (x : G))).toMonoidHom := by rw [hyx']
        _ = (V.map (MulAut.conj (x : G)).toMonoidHom).map (MulAut.conj (y : G)).toMonoidHom := by
            rw [Subgroup.map_map]
            congr 1
            exact MonoidHom.ext fun v => by simp [MulAut.conj_apply, mul_assoc]
        _ = V.map (MulAut.conj (y : G)).toMonoidHom := by rw [hx]
    rw [hgV]
    rintro _ ⟨v, hv, rfl⟩
    have hy : (y : G) ∈ V ⊔ (Q : Subgroup G) :=
      (le_sup_right : (Q : Subgroup G) ≤ V ⊔ (Q : Subgroup G)) y.2
    have hv' : v ∈ V ⊔ (Q : Subgroup G) :=
      (le_sup_left : V ≤ V ⊔ (Q : Subgroup G)) hv
    simpa [MulAut.conj_apply] using mul_mem (mul_mem hy hv') (inv_mem hy)
  -- so `⟨V, Q⟩` contains the normal closure of `V`, which is `⊤`
  have hnc : Subgroup.normalClosure (V : Set G) ≤ V ⊔ (Q : Subgroup G) := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro z hz
    obtain ⟨v, hv, hzconj⟩ := Group.mem_conjugatesOfSet_iff.mp hz
    obtain ⟨c, rfl⟩ := isConj_iff.mp hzconj
    exact hconjle c ⟨v, hv, rfl⟩
  have hnc_ne : Subgroup.normalClosure (V : Set G) ≠ ⊥ := by
    intro hcon
    exact hV (le_bot_iff.mp (hcon ▸ Subgroup.le_normalClosure))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure (V : Set G))
    inferInstance with hbot | htop
  · exact absurd hbot hnc_ne
  · exact top_le_iff.mp (htop ▸ hnc)

/-- **Isaacs' Step 2, second part.**  A nontrivial subgroup normalized by a Sylow `p`-subgroup
cannot be a `q`-group. -/
theorem not_isPGroup_of_sylow_le_normalizer (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (P : Sylow p G) {V : Subgroup G} (hV : V ≠ ⊥) (hPV : (P : Subgroup G) ≤ Subgroup.normalizer V) :
    ¬ IsPGroup q V := by
  have : Fact q.Prime := ⟨hq⟩
  intro hVq
  obtain ⟨Q, hQ⟩ := hVq.exists_le_sylow
  have htop : V ⊔ (Q : Subgroup G) = ⊤ := h.step2 hp hq hpq P Q hV hPV
  rw [sup_eq_right.mpr hQ] at htop
  -- but `p` divides `|G|` and `Q` is a `q`-group
  have hpG : p ∣ Nat.card G := h.prime_dvd_card hp hq
  obtain ⟨k, hk⟩ := Q.isPGroup'.exists_card_eq
  have hcard : Nat.card G = q ^ k := by
    rw [← hk, htop, Subgroup.card_top]
  rw [hcard] at hpG
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpG))

end IsMinCounterexample

/-!
## Step 1
-/

/-- A nontrivial `p`-subgroup has order divisible by `p`. -/
theorem prime_dvd_card_of_ne_bot (hp : p.Prime) {A : Subgroup G} (hA : IsPGroup p A)
    (hne : A ≠ ⊥) : p ∣ Nat.card A := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk
    exact hne (Subgroup.card_eq_one.mp hk)
  rw [hk]
  exact dvd_pow_self p hk0

/-- The `{p}ᶜ`-part and the `{q}`-part of a `{p, q}`-subgroup agree. -/
theorem piPart_compl_eq (hpq : p ≠ q) {X : Subgroup G} (hX : IsPiGroup {p, q} ↥X) :
    piPart ({p}ᶜ : Set ℕ) X = piPart ({q} : Set ℕ) X := by
  rw [piPart, piPart, piCore_compl_singleton_eq hpq hX]

omit [Finite G] in
/-- A `{q}`-group is a `{p}ᶜ`-group. -/
theorem isPiGroup_compl_of_singleton (hpq : p ≠ q) {A : Subgroup G}
    (hA : IsPiGroup ({q} : Set ℕ) A) : IsPiGroup ({p}ᶜ : Set ℕ) A :=
  hA.mono (Set.singleton_subset_iff.mpr (by simpa using hpq.symm))

namespace IsMinCounterexample

variable (h : IsMinCounterexample p q G)

include h

/-- **Isaacs' Step 1.**  If `K` is covered by its `p`- and `q`-parts, both primes divide `|K|`,
and `M = N_G(K)` is a maximal subgroup, then `M` is the *unique* maximal subgroup containing `K`.

Isaacs takes `K` maximal among the counterexamples; here the induction is on `|G| - |K|`.  Given a
second maximal subgroup `X ⊇ K`, Theorem 4.33 applied to the `p`-local subgroup `M ⊓ X = N_X(K_p)`
of the solvable group `X` puts `K_q` inside `O_q(X)`, and symmetrically `K_p ≤ O_p(X)`.  Then
`L = O_p(X) O_q(X)` contains `K`, is normalized by exactly `X`, and either equals `K` — forcing
`M = X` — or is strictly larger, in which case the induction hypothesis makes `X` the unique
maximal subgroup containing `L`, while `L` centralizes enough of `K` to lie in `M` as well. -/
theorem step1 (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∀ K : Subgroup G, SplitsPQ p q K →
      p ∣ Nat.card K → q ∣ Nat.card K → IsCoatom (Subgroup.normalizer (K : Set G)) →
      ∀ X : Subgroup G, IsCoatom X → K ≤ X → X = Subgroup.normalizer (K : Set G) := by
  refine induction_on_card_compl ?_
  intro K ih hsplit hpK hqK hMmax X hX hKX
  by_contra hXne
  have hsplit' : SplitsPQ q p K := by rw [SplitsPQ, sup_comm]; exact hsplit
  -- the two parts of `K`
  have hKple : piPart ({p} : Set ℕ) K ≤ K := piPart_le _ _
  have hKqle : piPart ({q} : Set ℕ) K ≤ K := piPart_le _ _
  have hKM : K ≤ Subgroup.normalizer K := Subgroup.le_normalizer
  have hKpne : piPart ({p} : Set ℕ) K ≠ ⊥ := piPart_ne_bot_of_dvd hp hq hpq hsplit hpK
  have hKqne : piPart ({q} : Set ℕ) K ≠ ⊥ := piPart_ne_bot_of_dvd hq hp hpq.symm hsplit' hqK
  have hKpM : Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((piPart ({p} : Set ℕ) K : Subgroup G) : Set G) :=
    piPart_normal_of_le_normalizer le_rfl
  have hKqM : Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((piPart ({q} : Set ℕ) K : Subgroup G) : Set G) :=
    piPart_normal_of_le_normalizer le_rfl
  -- `M = N_G(K_p) = N_G(K_q)`
  have : ((piPart ({p} : Set ℕ) K).subgroupOf (Subgroup.normalizer (K : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hKple.trans hKM)).mpr hKpM
  have : ((piPart ({q} : Set ℕ) K).subgroupOf (Subgroup.normalizer (K : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hKqle.trans hKM)).mpr hKqM
  have hMp : Subgroup.normalizer ((piPart ({p} : Set ℕ) K : Subgroup G) : Set G)
      = Subgroup.normalizer (K : Set G) :=
    h.normalizer_eq_of_isCoatom hMmax (hKple.trans hKM) hKpne
  have hMq : Subgroup.normalizer ((piPart ({q} : Set ℕ) K : Subgroup G) : Set G)
      = Subgroup.normalizer (K : Set G) :=
    h.normalizer_eq_of_isCoatom hMmax (hKqle.trans hKM) hKqne
  -- `X` is solvable, hence `p`- and `q`-separable
  have hXpi : IsPiGroup {p, q} ↥X := h.isPiGroup.to_subgroup X
  have : Group.IsSolvable ↥X := h.isSolvable_subgroup X hX.1
  -- `M ⊓ X = N_X(K_p)` is `p`-local in `X`; 4.33 puts `K_q` into `O_q(X)`
  have key : ∀ (r s : ℕ), r.Prime → s.Prime → r ≠ s →
      piPart ({r} : Set ℕ) K ≠ ⊥ → piPart ({r} : Set ℕ) K ≤ K →
      piPart ({s} : Set ℕ) K ≤ K →
      Subgroup.normalizer ((piPart ({r} : Set ℕ) K : Subgroup G) : Set G)
        = Subgroup.normalizer (K : Set G) →
      Subgroup.normalizer (K : Set G)
        ≤ Subgroup.normalizer ((piPart ({s} : Set ℕ) K : Subgroup G) : Set G) →
      IsPiSeparable ({r} : Set ℕ) ↥X →
      piPart ({s} : Set ℕ) K ≤ piPart ({r}ᶜ : Set ℕ) X := by
    intro r s hr _hs hrs hrne hrle hsle hMr hMs hsep
    have hrX : piPart ({r} : Set ℕ) K ≤ X := hrle.trans hKX
    have hlocal : IsPLocal r ((Subgroup.normalizer (K : Set G) ⊓ X).subgroupOf X) := by
      refine ⟨(piPart ({r} : Set ℕ) K).subgroupOf X, ?_, ?_, ?_⟩
      · intro hbot
        apply hrne
        have := congrArg (Subgroup.map X.subtype) hbot
        rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hrX, Subgroup.map_bot] at this
      · exact (IsPiGroup.isPGroup (isPiGroup_piPart _ _)).of_equiv
          (Subgroup.subgroupOfEquivOfLe hrX).symm
      · rw [← Subgroup.subgroupOf_normalizer_eq hrX, hMr, Subgroup.inf_subgroupOf_right]
    have h433 : piPart ({r}ᶜ : Set ℕ) (Subgroup.normalizer (K : Set G) ⊓ X)
        ≤ piPart ({r}ᶜ : Set ℕ) X :=
      piPart_compl_le_of_isPLocal hr hsep inf_le_right hlocal
    refine le_trans (le_piPart (le_inf (hsle.trans hKM) (hsle.trans hKX))
      (le_trans inf_le_left hMs) ?_) h433
    exact isPiGroup_compl_of_singleton hrs (isPiGroup_piPart _ _)
  have hKqL : piPart ({q} : Set ℕ) K ≤ piPart ({q} : Set ℕ) X := by
    have := key p q hp hq hpq hKpne hKple hKqle hMp hKqM IsPiSeparable.of_isSolvable
    rwa [piPart_compl_eq hpq hXpi] at this
  have hKpL : piPart ({p} : Set ℕ) K ≤ piPart ({p} : Set ℕ) X := by
    have := key q p hq hp hpq.symm hKqne hKqle hKple hMq hKpM IsPiSeparable.of_isSolvable
    rwa [piPart_compl_eq hpq.symm (by rwa [Set.pair_comm] at hXpi)] at this
  -- `L = O_p(X) O_q(X)`
  have hLpX : X ≤ Subgroup.normalizer ((piPart ({p} : Set ℕ) X : Subgroup G) : Set G) :=
    piPart_normal_of_le_normalizer Subgroup.le_normalizer
  have hLqX : X ≤ Subgroup.normalizer ((piPart ({q} : Set ℕ) X : Subgroup G) : Set G) :=
    piPart_normal_of_le_normalizer Subgroup.le_normalizer
  have hLX : piPart ({p} : Set ℕ) X ⊔ piPart ({q} : Set ℕ) X ≤ X :=
    sup_le (piPart_le _ _) (piPart_le _ _)
  have hKL : K ≤ piPart ({p} : Set ℕ) X ⊔ piPart ({q} : Set ℕ) X := by
    rw [← hsplit]
    exact sup_le_sup hKpL hKqL
  have hXLnorm : X ≤ Subgroup.normalizer
      ((piPart ({p} : Set ℕ) X ⊔ piPart ({q} : Set ℕ) X : Subgroup G) : Set G) := by
    intro x hx
    refine map_conj_eq_self_iff.mp ?_
    rw [Subgroup.map_sup, map_conj_eq_self_iff.mpr (hLpX hx), map_conj_eq_self_iff.mpr (hLqX hx)]
  have hLne : piPart ({p} : Set ℕ) X ⊔ piPart ({q} : Set ℕ) X ≠ ⊥ := by
    intro hbot
    exact hKpne (le_bot_iff.mp (hbot ▸ le_sup_left.trans' hKpL))
  have : ((piPart ({p} : Set ℕ) X ⊔ piPart ({q} : Set ℕ) X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mpr hXLnorm
  have hLnorm : Subgroup.normalizer
      ((piPart ({p} : Set ℕ) X ⊔ piPart ({q} : Set ℕ) X : Subgroup G) : Set G) = X :=
    h.normalizer_eq_of_isCoatom hX hLX hLne
  -- `L` splits, and both primes divide its order
  have hLsplit : SplitsPQ p q (piPart ({p} : Set ℕ) X ⊔ piPart ({q} : Set ℕ) X) := by
    refine le_antisymm (sup_le (piPart_le _ _) (piPart_le _ _)) (sup_le_sup ?_ ?_)
    · exact le_piPart le_sup_left (le_trans hLX hLpX) (isPiGroup_piPart _ _)
    · exact le_piPart le_sup_right (le_trans hLX hLqX) (isPiGroup_piPart _ _)
  have hpL : p ∣ Nat.card
      ((piPart ({p} : Set ℕ) X ⊔ piPart ({q} : Set ℕ) X : Subgroup G)) :=
    dvd_trans (prime_dvd_card_of_ne_bot hp (IsPiGroup.isPGroup (isPiGroup_piPart _ _)) hKpne)
      (Subgroup.card_dvd_of_le (le_trans hKpL le_sup_left))
  have hqL : q ∣ Nat.card
      ((piPart ({p} : Set ℕ) X ⊔ piPart ({q} : Set ℕ) X : Subgroup G)) :=
    dvd_trans (prime_dvd_card_of_ne_bot hq (IsPiGroup.isPGroup (isPiGroup_piPart _ _)) hKqne)
      (Subgroup.card_dvd_of_le (le_trans hKqL le_sup_right))
  rcases eq_or_lt_of_le hKL with heq | hlt
  · -- `K = L`, so `M = N_G(K) = N_G(L) = X`
    exact hXne (by rw [← hLnorm, ← heq])
  · -- `K < L`: the induction hypothesis makes `X` the unique maximal subgroup over `L`
    have hcardL : Nat.card K
        < Nat.card ((piPart ({p} : Set ℕ) X ⊔ piPart ({q} : Set ℕ) X : Subgroup G)) :=
      card_lt_card_of_lt hlt
    have huniq := ih _ hcardL hLsplit hpL hqL (by rw [hLnorm]; exact hX)
    -- `L ≤ M`, because each part centralizes the other and hence normalizes `K_p`, `K_q`
    have hdisj : Disjoint (piPart ({p} : Set ℕ) X) (piPart ({q} : Set ℕ) X) :=
      disjoint_of_isPiGroup (isPiGroup_piPart _ _)
        (isPiGroup_compl_of_singleton hpq (isPiGroup_piPart _ _))
    have hcomm : ∀ x ∈ piPart ({p} : Set ℕ) X, ∀ y ∈ piPart ({q} : Set ℕ) X, x * y = y * x :=
      commute_of_disjoint_of_normalIn (piPart_le _ _) (piPart_le _ _)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (piPart_le _ _)).mpr hLpX)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (piPart_le _ _)).mpr hLqX) hdisj
    have hLqM : piPart ({q} : Set ℕ) X ≤ Subgroup.normalizer K := by
      refine le_trans ?_ (le_trans (centralizer_le_normalizer (piPart ({p} : Set ℕ) K))
        (le_of_eq hMp))
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact hcomm z (hKpL hz) y hy
    have hLpM : piPart ({p} : Set ℕ) X ≤ Subgroup.normalizer K := by
      refine le_trans ?_ (le_trans (centralizer_le_normalizer (piPart ({q} : Set ℕ) K))
        (le_of_eq hMq))
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hcomm x hx z (hKqL hz)).symm
    have := huniq (Subgroup.normalizer (K : Set G)) hMmax (sup_le hLpM hLqM)
    exact hXne (by rw [← hLnorm, this])

/-- **Isaacs' Step 1**, as he states it: if `K` is nilpotent, both primes divide `|K|`, and
`M = N_G(K)` is maximal, then `M` is the unique maximal subgroup of `G` containing `K`. -/
theorem step1_of_isNilpotent (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {K : Subgroup G}
    (hKnil : Group.IsNilpotent K) (hpK : p ∣ Nat.card K) (hqK : q ∣ Nat.card K)
    (hMmax : IsCoatom (Subgroup.normalizer (K : Set G)))
    {X : Subgroup G} (hX : IsCoatom X) (hKX : K ≤ X) :
    X = Subgroup.normalizer (K : Set G) :=
  h.step1 hp hq hpq K
    (splitsPQ_of_isNilpotent hp hq hpq hKnil (h.isPiGroup.to_subgroup K)) hpK hqK hMmax X hX hKX

end IsMinCounterexample

/-!
## Step 3: the centre of the `p`-part

`centerPart π M` is `Z(O_π(M))` seen inside `G`.  It is a nontrivial abelian normal subgroup of a
maximal subgroup `M`, and Step 3 plays the two of them, for `π = {p}` and `π = {q}`, against each
other.
-/

omit [Finite G] in
/-- The centre of a subgroup, viewed in the ambient group. -/
theorem map_center_subtype (K : Subgroup G) :
    (Subgroup.center ↥K).map K.subtype = K ⊓ Subgroup.centralizer (K : Set G) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact congrArg Subtype.val (((Subgroup.mem_center_iff).mp hy) ⟨g, hg⟩)
  · rintro x ⟨hxK, hxc⟩
    refine ⟨⟨x, hxK⟩, Subgroup.mem_center_iff.mpr fun y => ?_, rfl⟩
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxc) (y : G) y.2)

/-- **Hall–Higman 1.2.3 in the ambient group** (`PiGroups.centralizer_piCore_le_piCore`).  If
`M` is `π`-separable and `O_π'(M) = 1`, then `O_π(M)` contains its own centralizer in `M`. -/
theorem inf_centralizer_piPart_le (π : Set ℕ) {M : Subgroup G} (hsep : IsPiSeparable π ↑M)
    (hcompl : piPart πᶜ M = ⊥) :
    M ⊓ Subgroup.centralizer ((piPart π M : Subgroup G) : Set G) ≤ piPart π M := by
  have hcore : piCore πᶜ ↑M = ⊥ := by
    rwa [piPart, Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective] at hcompl
  have hHH := centralizer_piCore_le_piCore (G := ↑M) hsep hcore
  rintro x ⟨hxM, hxc⟩
  refine ⟨⟨x, hxM⟩, hHH (Subgroup.mem_centralizer_iff.mpr fun u hu => ?_), rfl⟩
  exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxc) (u : G) ⟨u, hu, rfl⟩)

/-- `Z(O_π(M))`, as a subgroup of the ambient group. -/
def centerPart (π : Set ℕ) (M : Subgroup G) : Subgroup G :=
  piPart π M ⊓ Subgroup.centralizer ((piPart π M : Subgroup G) : Set G)

omit [Finite G] in
theorem centerPart_le_piPart (π : Set ℕ) (M : Subgroup G) : centerPart π M ≤ piPart π M :=
  inf_le_left

omit [Finite G] in
theorem centerPart_le (π : Set ℕ) (M : Subgroup G) : centerPart π M ≤ M :=
  (centerPart_le_piPart π M).trans (piPart_le π M)

theorem isPiGroup_centerPart (π : Set ℕ) (M : Subgroup G) : IsPiGroup π (centerPart π M) :=
  IsPiGroup.of_le (centerPart_le_piPart π M) (isPiGroup_piPart π M)

omit [Finite G] in
/-- Elements of `Z(O_π(M))` commute. -/
theorem centerPart_comm (π : Set ℕ) (M : Subgroup G) :
    ∀ x ∈ centerPart π M, ∀ y ∈ centerPart π M, x * y = y * x := by
  intro x hx y hy
  exact ((Subgroup.mem_centralizer_iff.mp hx.2) y (centerPart_le_piPart π M hy)).symm

/-- The centre of a nontrivial `p`-part is nontrivial. -/
theorem centerPart_ne_bot (hp : p.Prime) {M : Subgroup G} (hne : piPart ({p} : Set ℕ) M ≠ ⊥) :
    centerPart ({p} : Set ℕ) M ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Nontrivial (piPart ({p} : Set ℕ) M) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hP : IsPGroup p (piPart ({p} : Set ℕ) M) :=
    IsPiGroup.isPGroup (isPiGroup_piPart _ _)
  have hcenter : Subgroup.center (piPart ({p} : Set ℕ) M) ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp hP.center_nontrivial
  intro hbot
  refine hcenter ?_
  refine (Subgroup.map_eq_bot_iff_of_injective _ (piPart ({p} : Set ℕ) M).subtype_injective).mp ?_
  rw [map_center_subtype]
  exact hbot

omit [Finite G] in
/-- Anything normalizing `M` normalizes `Z(O_π(M))`. -/
theorem le_normalizer_centerPart (π : Set ℕ) {M : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (M : Set G)) :
    (centerPart π M).map (MulAut.conj g).toMonoidHom = centerPart π M := by
  have hP : (piPart π M).map (MulAut.conj g).toMonoidHom = piPart π M :=
    map_conj_piPart π (map_conj_eq_self_iff.mpr hg)
  have hmem : ∀ z : G, z ∈ piPart π M ↔ g * z * g⁻¹ ∈ piPart π M :=
    Subgroup.mem_normalizer_iff.mp (map_conj_eq_self_iff.mp hP)
  have hback : ∀ z : G, z ∈ piPart π M → g⁻¹ * z * g ∈ piPart π M := by
    intro z hz
    refine (hmem (g⁻¹ * z * g)).mpr ?_
    have hgz : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
    rw [hgz]
    exact hz
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨(hmem x).mp hx.1, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have hxz : x * (g⁻¹ * z * g) = (g⁻¹ * z * g) * x :=
      ((Subgroup.mem_centralizer_iff.mp hx.2) _ (hback z hz)).symm
    change z * ((MulAut.conj g) x) = ((MulAut.conj g) x) * z
    simp only [MulAut.conj_apply]
    calc z * (g * x * g⁻¹) = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by rw [hxz]
      _ = (g * x * g⁻¹) * z := by group
  · intro y hy
    refine ⟨g⁻¹ * y * g, ⟨hback y hy.1,
      Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩, by simp [MulAut.conj_apply]; group⟩
    have hyz : y * (g * z * g⁻¹) = (g * z * g⁻¹) * y :=
      ((Subgroup.mem_centralizer_iff.mp hy.2) _ ((hmem z).mp hz)).symm
    calc z * (g⁻¹ * y * g) = g⁻¹ * ((g * z * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * z * g⁻¹)) * g := by rw [hyz]
      _ = (g⁻¹ * y * g) * z := by group

omit [Finite G] in
/-- The join of two commuting abelian subgroups is abelian. -/
theorem comm_sup {A B : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  have hclosure : A ⊔ B = Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have hcent : ∀ x ∈ A ⊔ B, ∀ y ∈ (A : Set G) ∪ (B : Set G), x * y = y * x := by
    intro x hx
    rw [hclosure] at hx
    refine Subgroup.closure_induction (p := fun z _ => ∀ y ∈ (A : Set G) ∪ (B : Set G),
      z * y = y * z) ?_ ?_ ?_ ?_ hx
    · rintro z (hz | hz) y (hy | hy)
      · exact hA z hz y hy
      · exact hAB z hz y hy
      · exact (hAB y hy z hz).symm
      · exact hB z hz y hy
    · intro y _
      simp
    · intro z w _ _ hz hw y hy
      calc z * w * y = z * (w * y) := by group
        _ = z * (y * w) := by rw [hw y hy]
        _ = (z * y) * w := by group
        _ = (y * z) * w := by rw [hz y hy]
        _ = y * (z * w) := by group
    · intro z _ hz y hy
      have := hz y hy
      calc z⁻¹ * y = z⁻¹ * y * z * z⁻¹ := by group
        _ = z⁻¹ * (y * z) * z⁻¹ := by group
        _ = z⁻¹ * (z * y) * z⁻¹ := by rw [← this]
        _ = y * z⁻¹ := by group
  intro x hx y hy
  rw [hclosure] at hy
  refine Subgroup.closure_induction (p := fun z _ => x * z = z * x) ?_ ?_ ?_ ?_ hy
  · intro z hz
    exact hcent x hx z hz
  · simp
  · intro z w _ _ hz hw
    calc x * (z * w) = (x * z) * w := by group
      _ = (z * x) * w := by rw [hz]
      _ = z * (x * w) := by group
      _ = z * (w * x) := by rw [hw]
      _ = (z * w) * x := by group
  · intro z _ hz
    calc x * z⁻¹ = z⁻¹ * (z * x) * z⁻¹ := by group
      _ = z⁻¹ * (x * z) * z⁻¹ := by rw [← hz]
      _ = z⁻¹ * x := by group

/-!
## Faithful action on a cyclic `q`-group

The last arithmetic input of Step 3: a `p`-group acting faithfully on a cyclic `q`-group embeds in
its automorphism group, which has order `φ(q ^ k) = q ^ (k - 1) * (q - 1)`, so `p ∣ q - 1`.
-/

/-- A nontrivial `p`-group has order divisible by `p`. -/
theorem prime_dvd_card_of_nontrivial {A : Type*} [Group A] [Finite A] [Nontrivial A]
    (hp : p.Prime) (hA : IsPGroup p A) : p ∣ Nat.card A := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Nat.card_eq_one_iff_unique] at hk
    exact (not_subsingleton A) hk.1
  rw [hk]
  exact dvd_pow_self p hk0

/-- If a nontrivial `p`-group acts faithfully on a nontrivial cyclic `q`-group, with `p ≠ q`
primes, then `p ∣ q - 1`. -/
theorem prime_dvd_sub_one_of_faithful {C A : Type*} [Group C] [Finite C] [Nontrivial C]
    [IsCyclic C] [Group A] [Finite A] [Nontrivial A] [MulDistribMulAction A C]
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hA : IsPGroup p A) {k : ℕ}
    (hcard : Nat.card C = q ^ k)
    (hfaith : ∀ a : A, (∀ c : C, a • c = c) → a = 1) :
    p ∣ q - 1 := by
  -- the action embeds `A` into `Aut C`
  have hinj : Function.Injective (MulDistribMulAction.toMulAut A C) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    refine hfaith a fun c => ?_
    have hc := congrArg (fun e : MulAut C => e c) ha
    simpa using hc
  have hdvd : Nat.card A ∣ Nat.card (MulAut C) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  -- `|Aut C| = φ (q ^ k)`
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Nat.card_eq_one_iff_unique] at hcard
    exact (not_subsingleton C) hcard.1
  have hcardAut : Nat.card (MulAut C) = q ^ (k - 1) * (q - 1) := by
    rw [IsCyclic.card_mulAut, hcard, Nat.totient_prime_pow hq (Nat.pos_of_ne_zero hk0)]
  -- so `p` divides `q ^ (k-1) * (q - 1)`, and `p ≠ q`
  have hpdvd : p ∣ q ^ (k - 1) * (q - 1) := by
    rw [← hcardAut]
    exact (prime_dvd_card_of_nontrivial hp hA).trans hdvd
  have hcop : Nat.Coprime p (q ^ (k - 1)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hq).mpr hpq)
  exact (Nat.Coprime.dvd_of_dvd_mul_left hcop hpdvd)

omit [Finite G] in
/-- Conjugation carries centralizers to centralizers. -/
theorem map_centralizer_conj (z g : G) :
    (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom
      = Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro w hw
    rw [show w = g * z * g⁻¹ from hw]
    have hyz : z * y = y * z := (Subgroup.mem_centralizer_iff.mp hy) z rfl
    change (g * z * g⁻¹) * ((MulAut.conj g) y) = ((MulAut.conj g) y) * (g * z * g⁻¹)
    simp only [MulAut.conj_apply]
    calc (g * z * g⁻¹) * (g * y * g⁻¹) = g * (z * y) * g⁻¹ := by group
      _ = g * (y * z) * g⁻¹ := by rw [hyz]
      _ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
  · intro x hx
    refine ⟨g⁻¹ * x * g, Subgroup.mem_centralizer_iff.mpr ?_, by simp [MulAut.conj_apply]; group⟩
    intro w hw
    rw [show w = z from hw]
    have hxz : (g * z * g⁻¹) * x = x * (g * z * g⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hx) (g * z * g⁻¹) rfl
    calc z * (g⁻¹ * x * g) = g⁻¹ * ((g * z * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * z * g⁻¹)) * g := by rw [hxz]
      _ = (g⁻¹ * x * g) * z := by group

omit [Finite G] in
/-- If `y` normalizes `W` and commutes with `b`, then `y` normalizes the conjugate `W ^ b`. -/
theorem map_conj_conj_of_commute {W : Subgroup G} {y b : G}
    (hyW : W.map (MulAut.conj y).toMonoidHom = W) (hby : y * b = b * y) :
    (W.map (MulAut.conj b).toMonoidHom).map (MulAut.conj y).toMonoidHom
      = W.map (MulAut.conj b).toMonoidHom := by
  have hcomp : (MulAut.conj y).toMonoidHom.comp (MulAut.conj b).toMonoidHom
      = (MulAut.conj b).toMonoidHom.comp (MulAut.conj y).toMonoidHom := by
    ext u
    change y * (b * u * b⁻¹) * y⁻¹ = b * (y * u * y⁻¹) * b⁻¹
    calc y * (b * u * b⁻¹) * y⁻¹ = (y * b) * u * (y * b)⁻¹ := by group
      _ = (b * y) * u * (b * y)⁻¹ := by rw [hby]
      _ = b * (y * u * y⁻¹) * b⁻¹ := by group
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hyW]

/-!
## `p`-central elements

Isaacs calls a nonidentity element `p`-central if it lies in the centre of some Sylow
`p`-subgroup, and writes `U*` for the subgroup generated by the `p`-central elements of a
`p`-subgroup `U`.  Step 4 is about these.
-/

/-- A `p`-central element: a nonidentity element of the centre of some Sylow `p`-subgroup. -/
def IsPCentral (p : ℕ) (x : G) : Prop :=
  x ≠ 1 ∧ ∃ P : Sylow p G, x ∈ (P : Subgroup G) ∧ ∀ y ∈ (P : Subgroup G), x * y = y * x

omit [Finite G] in
/-- Conjugates of `p`-central elements are `p`-central. -/
theorem IsPCentral.conj {x : G} (hx : IsPCentral p x) (g : G) : IsPCentral p (g * x * g⁻¹) := by
  obtain ⟨hx1, P, hxP, hxc⟩ := hx
  refine ⟨fun hc => hx1 ?_, g • P, ?_, ?_⟩
  · have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this, hc]
    group
  · rw [Sylow.coe_subgroup_smul]
    exact ⟨x, hxP, rfl⟩
  · intro y hy
    rw [Sylow.coe_subgroup_smul] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hxz := hxc z hz
    change (g * x * g⁻¹) * ((MulAut.conj g) z) = ((MulAut.conj g) z) * (g * x * g⁻¹)
    simp only [MulAut.conj_apply]
    calc (g * x * g⁻¹) * (g * z * g⁻¹) = g * (x * z) * g⁻¹ := by group
      _ = g * (z * x) * g⁻¹ := by rw [hxz]
      _ = (g * z * g⁻¹) * (g * x * g⁻¹) := by group

/-- `U*`: the subgroup generated by the `p`-central elements of `U`. -/
def pCentralPart (p : ℕ) (U : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | IsPCentral p x ∧ x ∈ U}

omit [Finite G] in
theorem pCentralPart_le (p : ℕ) (U : Subgroup G) : pCentralPart p U ≤ U :=
  Subgroup.closure_le _ |>.mpr fun _ hx => hx.2

omit [Finite G] in
theorem mem_pCentralPart {x : G} {U : Subgroup G} (hx : IsPCentral p x) (hxU : x ∈ U) :
    x ∈ pCentralPart p U :=
  Subgroup.subset_closure ⟨hx, hxU⟩

omit [Finite G] in
theorem pCentralPart_mono {U V : Subgroup G} (huv : U ≤ V) :
    pCentralPart p U ≤ pCentralPart p V :=
  Subgroup.closure_mono fun _ hx => ⟨hx.1, huv hx.2⟩

omit [Finite G] in
/-- Conjugation carries `U*` to `(U ^ g)*`. -/
theorem map_conj_pCentralPart (U : Subgroup G) (g : G) :
    (pCentralPart p U).map (MulAut.conj g).toMonoidHom
      = pCentralPart p (U.map (MulAut.conj g).toMonoidHom) := by
  rw [pCentralPart, pCentralPart, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxc, hxU⟩, rfl⟩
    exact ⟨hxc.conj g, ⟨x, hxU, rfl⟩⟩
  · rintro ⟨hyc, x, hxU, rfl⟩
    refine ⟨x, ⟨?_, hxU⟩, rfl⟩
    have hback := hyc.conj g⁻¹
    have hx : g⁻¹ * ((MulAut.conj g).toMonoidHom x) * g⁻¹⁻¹ = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rwa [hx] at hback

omit [Finite G] in
/-- Anything normalizing `U` normalizes `U*`. -/
theorem map_conj_pCentralPart_self {U : Subgroup G} {g : G}
    (hg : U.map (MulAut.conj g).toMonoidHom = U) :
    (pCentralPart p U).map (MulAut.conj g).toMonoidHom = pCentralPart p U := by
  rw [map_conj_pCentralPart, hg]

omit [Finite G] in
/-- `U*` is generated by `p`-central elements, so its own `p`-central part is itself. -/
theorem pCentralPart_idem (p : ℕ) (U : Subgroup G) :
    pCentralPart p (pCentralPart p U) = pCentralPart p U := by
  refine le_antisymm (pCentralPart_le _ _) ?_
  rw [pCentralPart]
  refine Subgroup.closure_le _ |>.mpr fun x hx => ?_
  exact mem_pCentralPart hx.1 (mem_pCentralPart hx.1 hx.2)

/-!
## Isaacs' Theorem 2.13

Step 7 rules out `p = 2` and `q = 2`, and for that Isaacs appeals to his Theorem 2.13, carried
here as the hypothesis `Burnside.InvolutionInvertsElement`.  That definition lives in
`Isaacs/InvolutionInverts.lean`, which is also where it is discharged, so that the file proving
it need not import this one.
-/

namespace IsMinCounterexample

variable (h : IsMinCounterexample p q G)

include h

/-- In the minimal counterexample the centre is trivial. -/
theorem center_eq_bot : Subgroup.center G = ⊥ := by
  have := h.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with hb | ht
  · exact hb
  · exact absurd (Group.isSolvable_of_comm fun a b =>
      ((Subgroup.mem_center_iff).mp (ht ▸ Subgroup.mem_top a) b).symm) h.not_isSolvable

/-- A maximal subgroup of the minimal counterexample is self-normalizing. -/
theorem normalizer_eq_self_of_isCoatom {M : Subgroup G} (hM : IsCoatom M) :
    Subgroup.normalizer (M : Set G) = M := by
  have : (M.subgroupOf M).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  exact h.normalizer_eq_of_isCoatom hM le_rfl (h.ne_bot_of_isCoatom hM)

open scoped IsMulCommutative in
/-- **Step 3, the centre part.**  If both cores of a maximal subgroup `M` are nontrivial, then
`Z = Z(O_p(M)) Z(O_q(M))` is nontrivial and abelian, `M` is the unique maximal subgroup containing
it, and `C_G(z) ≤ M` for every `1 ≠ z ∈ Z`. -/
theorem step3_center (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {M : Subgroup G}
    (hM : IsCoatom M) (hPne : piPart ({p} : Set ℕ) M ≠ ⊥) (hQne : piPart ({q} : Set ℕ) M ≠ ⊥) :
    (∀ x ∈ centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M,
        ∀ y ∈ centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M, x * y = y * x) ∧
      (∀ X : Subgroup G, IsCoatom X →
        centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M ≤ X → X = M) ∧
      (∀ z ∈ centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M, z ≠ 1 →
        Subgroup.centralizer ({z} : Set G) ≤ M) := by
  classical
  -- the two centres
  have hZpne : centerPart ({p} : Set ℕ) M ≠ ⊥ := centerPart_ne_bot hp hPne
  have hZqne : centerPart ({q} : Set ℕ) M ≠ ⊥ := centerPart_ne_bot hq hQne
  have hZpM : centerPart ({p} : Set ℕ) M ≤ M := centerPart_le _ _
  have hZqM : centerPart ({q} : Set ℕ) M ≤ M := centerPart_le _ _
  -- they commute with each other, because the two cores do
  have hOdisj : Disjoint (piPart ({p} : Set ℕ) M) (piPart ({q} : Set ℕ) M) :=
    disjoint_of_isPiGroup (isPiGroup_piPart _ _)
      (isPiGroup_compl_of_singleton hpq (isPiGroup_piPart _ _))
  have hOcomm : ∀ x ∈ piPart ({p} : Set ℕ) M, ∀ y ∈ piPart ({q} : Set ℕ) M, x * y = y * x :=
    commute_of_disjoint_of_normalIn (piPart_le _ _) (piPart_le _ _)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (piPart_le _ _)).mpr
        (piPart_normal_of_le_normalizer Subgroup.le_normalizer))
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (piPart_le _ _)).mpr
        (piPart_normal_of_le_normalizer Subgroup.le_normalizer)) hOdisj
  have hZcomm : ∀ x ∈ centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M,
      ∀ y ∈ centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M, x * y = y * x :=
    comm_sup (centerPart_comm _ _) (centerPart_comm _ _)
      (fun x hx y hy => hOcomm x (centerPart_le_piPart _ _ hx) y (centerPart_le_piPart _ _ hy))
  -- `M` is the unique maximal subgroup containing `Z`
  have huniq : ∀ X : Subgroup G, IsCoatom X →
      centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M ≤ X → X = M := by
    have hZle : centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M ≤ M := sup_le hZpM hZqM
    have hZne : centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M ≠ ⊥ := fun hbot =>
      hZpne (le_bot_iff.mp (hbot ▸ (le_sup_left :
        centerPart ({p} : Set ℕ) M ≤ centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M)))
    have hZnorm : ∀ g ∈ M, (centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M).map
        (MulAut.conj g).toMonoidHom
          = centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M := by
      intro g hg
      rw [Subgroup.map_sup, le_normalizer_centerPart _ (Subgroup.le_normalizer hg),
        le_normalizer_centerPart _ (Subgroup.le_normalizer hg)]
    have : ((centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M).subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hZle).mpr
        (fun g hg => map_conj_eq_self_iff.mp (hZnorm g hg))
    have hMZ : Subgroup.normalizer
        ((centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M : Subgroup G) : Set G) = M :=
      h.normalizer_eq_of_isCoatom hM hZle hZne
    -- `Z` is abelian, hence nilpotent
    have : IsMulCommutative ↥(centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M) :=
      ⟨⟨fun x y => Subtype.ext (hZcomm x x.2 y y.2)⟩⟩
    have : Group.IsNilpotent ↥(centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M) :=
      inferInstance
    -- both primes divide `|Z|`
    have hpZ : p ∣ Nat.card ↥(centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M) :=
      dvd_trans (prime_dvd_card_of_ne_bot hp
        (IsPiGroup.isPGroup (isPiGroup_centerPart _ _)) hZpne)
        (Subgroup.card_dvd_of_le le_sup_left)
    have hqZ : q ∣ Nat.card ↥(centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M) :=
      dvd_trans (prime_dvd_card_of_ne_bot hq
        (IsPiGroup.isPGroup (isPiGroup_centerPart _ _)) hZqne)
        (Subgroup.card_dvd_of_le le_sup_right)
    intro X hX hZX
    rw [← hMZ]
    exact h.step1_of_isNilpotent hp hq hpq inferInstance hpZ hqZ (by rw [hMZ]; exact hM) hX hZX
  -- centralizers of nonidentity elements of `Z` lie in `M`
  refine ⟨hZcomm, huniq, ?_⟩
  intro z hz hz1
  have hZC : centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M
      ≤ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro g hg
    rw [show g = z from hg]
    exact hZcomm z hz x hx
  have hCne : Subgroup.centralizer ({z} : Set G) ≠ ⊤ := by
    intro htop
    refine hz1 ?_
    have hzc : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({z} : Set G) := htop ▸ Subgroup.mem_top g
      exact ((Subgroup.mem_centralizer_iff.mp hg) z rfl).symm
    rw [h.center_eq_bot] at hzc
    exact Subgroup.mem_bot.mp hzc
  obtain ⟨X, hX, hCX⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom
      (Subgroup.centralizer ({z} : Set G))).resolve_left hCne
  rw [← huniq X hX (hZC.trans hCX)]
  exact hCX

omit h [Finite G] in
/-- A normal `p`-subgroup of `N` lies inside every Sylow `p`-subgroup of `N`. -/
theorem le_sylow_of_normal {N K : Subgroup G} (hKN : K ≤ N)
    (hKnorm : N ≤ Subgroup.normalizer (K : Set G)) (hKp : IsPGroup p K) (T : Sylow p ↥N) :
    K ≤ (T : Subgroup ↥N).map N.subtype := by
  have hKn : (K.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr hKnorm
  have hKpp : IsPGroup p (K.subgroupOf N) :=
    hKp.of_equiv (Subgroup.subgroupOfEquivOfLe hKN).symm
  have hsup : (K.subgroupOf N) ⊔ (T : Subgroup ↥N) = (T : Subgroup ↥N) :=
    T.is_maximal' (hKpp.to_sup_of_normal_left T.isPGroup') le_sup_right
  have hle : K.subgroupOf N ≤ (T : Subgroup ↥N) := hsup ▸ le_sup_left
  have hmap := Subgroup.map_mono (f := N.subtype) hle
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKN] at hmap

omit h in
/-- **The Sylow escape argument.**  If a Sylow `p`-subgroup `S` of a subgroup `N` is not a full
Sylow `p`-subgroup of `G`, then `N_G(S)` is not contained in `N`: some `g ∉ N` normalizes `S`.

Inside a Sylow `p`-subgroup `P > S` of `G` the normalizer of `S` is strictly larger than `S`, and
it cannot lie in `N`, since `S` is already maximal among the `p`-subgroups of `N`. -/
theorem exists_conj_eq_not_mem (hp : p.Prime) {N : Subgroup G} (T : Sylow p ↥N)
    (hnotSylow : ∀ P : Sylow p G, (T : Subgroup ↥N).map N.subtype ≠ (P : Subgroup G)) :
    ∃ g : G, ((T : Subgroup ↥N).map N.subtype).map (MulAut.conj g).toMonoidHom
        = (T : Subgroup ↥N).map N.subtype ∧ g ∉ N := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set S : Subgroup G := (T : Subgroup ↥N).map N.subtype with hSdef
  have hSmem : ∀ t : ↥N, t ∈ (T : Subgroup ↥N) → (t : G) ∈ S := by
    intro t ht
    rw [hSdef]
    exact ⟨t, ht, rfl⟩
  have hSp : IsPGroup p ↥S := T.isPGroup'.map _
  obtain ⟨P, hSP⟩ := hSp.exists_le_sylow
  have hSltP : S < (P : Subgroup G) := lt_of_le_of_ne hSP (hnotSylow P)
  have : Group.IsNilpotent ↥(P : Subgroup G) := P.isPGroup'.isNilpotent
  have hnc : NormalizerCondition ↥(P : Subgroup G) := Group.normalizerCondition_of_isNilpotent
  have hlt : S.subgroupOf (P : Subgroup G) < ⊤ :=
    lt_of_le_of_ne le_top fun htop =>
      absurd (hSltP.trans_le (Subgroup.subgroupOf_eq_top.mp htop)) (lt_irrefl S)
  obtain ⟨x, hxnorm, hxnot⟩ := SetLike.exists_of_lt (hnc _ hlt)
  have hxnormG : (x : G) ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      exact (Subgroup.mem_normalizer_iff.mp hxnorm ⟨w, hSP hw⟩).mp hw
    · intro hw
      have hwP : w ∈ (P : Subgroup G) := by
        have h1 : (x : G) * w * (x : G)⁻¹ ∈ (P : Subgroup G) := hSP hw
        have h2 : w = (x : G)⁻¹ * ((x : G) * w * (x : G)⁻¹) * (x : G) := by group
        rw [h2]
        exact mul_mem (mul_mem (inv_mem x.2) h1) x.2
      exact (Subgroup.mem_normalizer_iff.mp hxnorm ⟨w, hwP⟩).mpr hw
  have hSW : S ≤ Subgroup.normalizer (S : Set G) ⊓ (P : Subgroup G) :=
    le_inf Subgroup.le_normalizer hSP
  have hSltW : S < Subgroup.normalizer (S : Set G) ⊓ (P : Subgroup G) := by
    refine lt_of_le_of_ne hSW fun heq => hxnot ?_
    have hxS : (x : G) ∈ S := by
      rw [heq]
      exact ⟨hxnormG, x.2⟩
    exact hxS
  have hWN : ¬ (Subgroup.normalizer (S : Set G) ⊓ (P : Subgroup G) ≤ N) := by
    intro hWle
    have hTW : (T : Subgroup ↥N)
        ≤ (Subgroup.normalizer (S : Set G) ⊓ (P : Subgroup G)).subgroupOf N := by
      intro t ht
      exact hSW (hSmem t ht)
    have hWp : IsPGroup p ((Subgroup.normalizer (S : Set G) ⊓ (P : Subgroup G)).subgroupOf N) :=
      (P.isPGroup'.to_le inf_le_right).of_equiv (Subgroup.subgroupOfEquivOfLe hWle).symm
    have heqT := T.is_maximal' hWp hTW
    have hWS : Subgroup.normalizer (S : Set G) ⊓ (P : Subgroup G) ≤ S := by
      have h1 := Subgroup.map_mono (f := N.subtype) (le_of_eq heqT)
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWle, ← hSdef] at h1
    exact absurd (hSltW.trans_le hWS) (lt_irrefl S)
  obtain ⟨g, hgW, hgN⟩ := SetLike.not_le_iff_exists.mp hWN
  exact ⟨g, map_conj_eq_self_iff.mpr hgW.1, hgN⟩

/-- **Step 3, the Sylow step.**  A Sylow `p`-subgroup `S` of `M` normalizes the nontrivial
`q`-group `O_q(M)`, so by Step 2 it is not a full Sylow `p`-subgroup of `G`.  Inside a Sylow
`p`-subgroup `P ≥ S` of `G` its normalizer is therefore strictly larger, and that normalizer
cannot lie in `M`: there is `g ∉ M` normalizing `S`. -/
theorem step3_sylow (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {M : Subgroup G}
    (hQne : piPart ({q} : Set ℕ) M ≠ ⊥) :
    ∃ (S : Subgroup G) (g : G), S ≤ M ∧ piPart ({p} : Set ℕ) M ≤ S ∧
      S.map (MulAut.conj g).toMonoidHom = S ∧ g ∉ M := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T⟩ : Nonempty (Sylow p ↥M) := inferInstance
  have hSM : (T : Subgroup ↥M).map M.subtype ≤ M := Subgroup.map_subtype_le _
  -- `O_p(M) ≤ S`, because `O_p(M)` is a normal `p`-subgroup of `M`
  have hOpS : piPart ({p} : Set ℕ) M ≤ (T : Subgroup ↥M).map M.subtype :=
    le_sylow_of_normal (piPart_le _ _)
      (piPart_normal_of_le_normalizer Subgroup.le_normalizer)
      (IsPiGroup.isPGroup (isPiGroup_piPart _ _)) T
  -- `S` is not a full Sylow `p`-subgroup of `G`, by Step 2
  have hnotSylow : ∀ P : Sylow p G, (T : Subgroup ↥M).map M.subtype ≠ (P : Subgroup G) := by
    intro P heq
    refine (h.not_isPGroup_of_sylow_le_normalizer hp hq hpq P hQne ?_)
      (IsPiGroup.isPGroup (isPiGroup_piPart _ _))
    rw [← heq]
    exact hSM.trans (piPart_normal_of_le_normalizer Subgroup.le_normalizer)
  obtain ⟨g, hgS, hgM⟩ := exists_conj_eq_not_mem hp T hnotSylow
  exact ⟨_, g, hSM, hOpS, hgS, hgM⟩

open scoped IsMulCommutative in
/-- **Step 3, the case analysis.**  With both cores of `M` nontrivial, `A = Z(O_p(M)) ^ g` (for the
`g ∉ M` of `step3_sylow`) acts on `Z(O_q(M))`; if it were noncyclic, or acted unfaithfully, then
Isaacs 6.21 would put `Z` inside `M ^ g`, forcing `g ∈ M`.  So `Z(O_p(M))` is cyclic and `p`
divides `|Aut (Z(O_q(M)))|`. -/
theorem step3_key (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {M : Subgroup G}
    (hM : IsCoatom M) (hPne : piPart ({p} : Set ℕ) M ≠ ⊥) (hQne : piPart ({q} : Set ℕ) M ≠ ⊥) :
    IsCyclic ↥(centerPart ({p} : Set ℕ) M) ∧
      p ∣ Nat.card (MulAut ↥(centerPart ({q} : Set ℕ) M)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hZcomm, huniq, hCz⟩ := h.step3_center hp hq hpq hM hPne hQne
  obtain ⟨S, g, hSM, hOpS, hgS, hgM⟩ := h.step3_sylow hp hq hpq hQne
  set A : Subgroup G := (centerPart ({p} : Set ℕ) M).map (MulAut.conj g).toMonoidHom with hAdef
  -- `A ≤ S ≤ M`, and `A` normalizes `Z(O_q(M))`
  have hZpS : centerPart ({p} : Set ℕ) M ≤ S := (centerPart_le_piPart _ _).trans hOpS
  have hAS : A ≤ S := by
    rw [hAdef, ← hgS]
    exact Subgroup.map_mono hZpS
  have hAM : A ≤ M := hAS.trans hSM
  have hAN : A ≤ Subgroup.normalizer ((centerPart ({q} : Set ℕ) M : Subgroup G) : Set G) :=
    fun a ha => map_conj_eq_self_iff.mp (le_normalizer_centerPart _
      (Subgroup.le_normalizer (hAM ha)))
  let _inst := CoprimeAction.conjActionOfLeNormalizer A (centerPart ({q} : Set ℕ) M) hAN
  have hsmul : ∀ (a : A) (n : centerPart ({q} : Set ℕ) M),
      ((a • n : centerPart ({q} : Set ℕ) M) : G) = (a : G) * (n : G) * (a : G)⁻¹ :=
    fun _ _ => rfl
  -- `A` is an abelian `p`-group, nontrivial, of order prime to `|Z(O_q(M))|`
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    rw [hAdef]
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    have huv := centerPart_comm ({p} : Set ℕ) M u hu v hv
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc (g * u * g⁻¹) * (g * v * g⁻¹) = g * (u * v) * g⁻¹ := by group
      _ = g * (v * u) * g⁻¹ := by rw [huv]
      _ = (g * v * g⁻¹) * (g * u * g⁻¹) := by group
  have : IsMulCommutative ↥A := ⟨⟨fun x y => Subtype.ext (hAcomm x x.2 y y.2)⟩⟩
  have hApi : IsPGroup p ↥A := by
    rw [hAdef]
    exact (IsPiGroup.isPGroup (isPiGroup_centerPart _ _)).map _
  have hAne : A ≠ ⊥ := by
    rw [hAdef]
    intro hbot
    exact centerPart_ne_bot hp hPne
      ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp hbot)
  have : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot _).mpr hAne
  have hcop : Nat.Coprime p (Nat.card ↥(centerPart ({q} : Set ℕ) M)) := by
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨k, hk⟩ := (IsPiGroup.isPGroup (isPiGroup_centerPart ({q} : Set ℕ) M)).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hq).mpr hpq)
  -- if `Z(O_q(M))` is generated by the centralizers of the nonidentity elements of `A`, we get a
  -- contradiction with `g ∉ M`
  have hkey : (⨆ (a : ↥A) (_ : a ≠ 1),
      FixedPoints.subgroup (↥(Subgroup.zpowers a)) ↥(centerPart ({q} : Set ℕ) M)) ≠ ⊤ := by
    intro hgen
    have hCle : ∀ a : ↥A, a ≠ 1 →
        (FixedPoints.subgroup (↥(Subgroup.zpowers a)) ↥(centerPart ({q} : Set ℕ) M)).map
          (centerPart ({q} : Set ℕ) M).subtype ≤ M.map (MulAut.conj g).toMonoidHom := by
      intro a ha
      rintro _ ⟨x, hx, rfl⟩
      -- `x` is fixed by `a`, so it centralizes `a`
      have hfix : (a : G) * (x : G) * (a : G)⁻¹ = (x : G) := by
        have hx' : x ∈ FixedPoints.subgroup ↥(Subgroup.zpowers a)
            ↥(centerPart ({q} : Set ℕ) M) := hx
        rw [FixedPoints.mem_subgroup] at hx'
        have hxa := hx' ⟨(a : ↥A), Subgroup.mem_zpowers _⟩
        rw [← hsmul]
        exact congrArg (Subtype.val (p := fun y => y ∈ centerPart ({q} : Set ℕ) M)) hxa
      have hxcent : (x : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
        refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
        rw [show w = (a : G) from hw]
        calc (a : G) * (x : G) = ((a : G) * (x : G) * (a : G)⁻¹) * (a : G) := by group
          _ = (x : G) * (a : G) := by rw [hfix]
      -- and the centralizer of `a` lies in `M ^ g`
      obtain ⟨z, hz, hza⟩ : ∃ z ∈ centerPart ({p} : Set ℕ) M, g * z * g⁻¹ = (a : G) := by
        have hmem : (a : G) ∈ (centerPart ({p} : Set ℕ) M).map (MulAut.conj g).toMonoidHom := a.2
        obtain ⟨z, hz, hzz⟩ := hmem
        exact ⟨z, hz, by simpa [MulAut.conj_apply] using hzz⟩
      have hzne : z ≠ 1 := by
        intro hz1
        refine ha (Subtype.ext ?_)
        rw [← hza, hz1]
        simp
      have hsub : Subgroup.centralizer ({(a : G)} : Set G) ≤ M.map (MulAut.conj g).toMonoidHom := by
        rw [← hza, ← map_centralizer_conj]
        exact Subgroup.map_mono
          (hCz z ((le_sup_left : centerPart ({p} : Set ℕ) M ≤
            centerPart ({p} : Set ℕ) M ⊔ centerPart ({q} : Set ℕ) M) hz) hzne)
      exact hsub hxcent
    -- so `Z(O_q(M)) ≤ M ^ g`
    have hZqle : centerPart ({q} : Set ℕ) M ≤ M.map (MulAut.conj g).toMonoidHom := by
      have hmap : ((⊤ : Subgroup ↥(centerPart ({q} : Set ℕ) M)).map
          (centerPart ({q} : Set ℕ) M).subtype) ≤ M.map (MulAut.conj g).toMonoidHom := by
        rw [← hgen, Subgroup.map_iSup]
        refine iSup_le fun a => ?_
        rw [Subgroup.map_iSup]
        exact iSup_le fun ha => hCle a ha
      rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    -- and `Z(O_p(M)) ≤ S = S ^ g ≤ M ^ g`
    have hZple : centerPart ({p} : Set ℕ) M ≤ M.map (MulAut.conj g).toMonoidHom :=
      calc centerPart ({p} : Set ℕ) M ≤ S := hZpS
        _ = S.map (MulAut.conj g).toMonoidHom := hgS.symm
        _ ≤ M.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hSM
    -- `M ^ g` is a maximal subgroup containing `Z`, hence equals `M`
    have hMg : IsCoatom (M.map (MulAut.conj g).toMonoidHom) :=
      (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (MulAut.conj g)) M).mpr hM
    have hMgM := huniq _ hMg (sup_le hZple hZqle)
    exact hgM ((h.normalizer_eq_self_of_isCoatom hM) ▸ map_conj_eq_self_iff.mp hMgM)
  -- `A` is cyclic and acts faithfully
  have hcyc : IsCyclic ↥A := by
    by_contra hncyc
    exact hkey (NoncyclicAbelian.eq_top_iSup_zpowers p hApi hcop hncyc)
  refine ⟨?_, ?_⟩
  · -- `Z(O_p(M)) ≅ A` is cyclic
    exact (MulEquiv.isCyclic ((centerPart ({p} : Set ℕ) M).equivMapOfInjective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)).mpr hcyc
  · -- the action is faithful, so `A` embeds into `Aut (Z(O_q(M)))`
    have hfaith : ∀ a : ↥A, (∀ n : ↥(centerPart ({q} : Set ℕ) M), a • n = n) → a = 1 := by
      intro a hafix
      by_contra hane
      refine hkey (top_le_iff.mp ?_)
      refine le_trans ?_ (le_iSup_of_le a (le_iSup_of_le hane le_rfl))
      have hinvfix : ∀ m : ↥(centerPart ({q} : Set ℕ) M), a⁻¹ • m = m := by
        intro m
        calc a⁻¹ • m = a⁻¹ • (a • m) := by rw [hafix m]
          _ = m := inv_smul_smul a m
      have hpow : ∀ (k : ℤ) (m : ↥(centerPart ({q} : Set ℕ) M)), (a ^ k) • m = m := by
        intro k m
        induction k using Int.induction_on with
        | zero => simp
        | succ k ih => rw [zpow_add_one, mul_smul, hafix, ih]
        | pred k ih => rw [zpow_sub_one, mul_smul, hinvfix, ih]
      intro n _
      rw [FixedPoints.mem_subgroup]
      intro z
      obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).mp z.2
      change ((z : ↥A)) • n = n
      exact (congrArg (fun w : ↥A => w • n) hk.symm).trans (hpow k n)
    have hinj : Function.Injective
        (MulDistribMulAction.toMulAut ↥A ↥(centerPart ({q} : Set ℕ) M)) := by
      rw [injective_iff_map_eq_one]
      intro a ha
      refine hfaith a fun n => ?_
      have := congrArg (fun e : MulAut ↥(centerPart ({q} : Set ℕ) M) => e n) ha
      simpa using this
    have hdvd : Nat.card ↥A ∣ Nat.card (MulAut ↥(centerPart ({q} : Set ℕ) M)) := by
      rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    exact (prime_dvd_card_of_nontrivial hp hApi).trans hdvd

/-- **Isaacs' Step 3.**  For a maximal subgroup `M` of the minimal counterexample, `O_p(M) = 1` or
`O_q(M) = 1`. -/
theorem step3 (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {M : Subgroup G} (hM : IsCoatom M) :
    piPart ({p} : Set ℕ) M = ⊥ ∨ piPart ({q} : Set ℕ) M = ⊥ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hPne, hQne⟩ := hcon
  -- both centres are cyclic, and each prime divides the automorphism order of the other centre
  obtain ⟨hZpcyc, hpAut⟩ := h.step3_key hp hq hpq hM hPne hQne
  obtain ⟨hZqcyc, hqAut⟩ := h.symm.step3_key hq hp hpq.symm hM hQne hPne
  -- so `p ∣ q - 1` and `q ∣ p - 1`
  have hlt : ∀ (r s : ℕ), r.Prime → s.Prime → r ≠ s → ∀ {C : Type u} [Group C] [Finite C]
      [IsCyclic C] [Nontrivial C], IsPiGroup ({s} : Set ℕ) C →
      r ∣ Nat.card (MulAut C) → r < s := by
    intro r s hr hs hrs C _ _ _ _ hC hdvd
    have : Fact s.Prime := ⟨hs⟩
    obtain ⟨k, hk⟩ := (IsPiGroup.isPGroup hC).exists_card_eq
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero, Nat.card_eq_one_iff_unique] at hk
      exact (not_subsingleton C) hk.1
    rw [IsCyclic.card_mulAut, hk, Nat.totient_prime_pow hs (Nat.pos_of_ne_zero hk0)] at hdvd
    have hcopr : Nat.Coprime r (s ^ (k - 1)) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hr hs).mpr hrs)
    have hdvd' : r ∣ s - 1 := Nat.Coprime.dvd_of_dvd_mul_left hcopr hdvd
    have hs2 : 2 ≤ s := hs.two_le
    have hrle : r ≤ s - 1 := Nat.le_of_dvd (by omega) hdvd'
    omega
  have : Nontrivial ↥(centerPart ({q} : Set ℕ) M) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (centerPart_ne_bot hq hQne)
  have : Nontrivial ↥(centerPart ({p} : Set ℕ) M) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (centerPart_ne_bot hp hPne)
  have := hZpcyc
  have := hZqcyc
  have h1 : p < q := hlt p q hp hq hpq (isPiGroup_centerPart _ _) hpAut
  have h2 : q < p := hlt q p hq hp hpq.symm (isPiGroup_centerPart _ _) hqAut
  omega

omit h [Finite G] in
/-- `O_π(M) ≠ 1` as a subgroup of `G` is the same as `O_π(M) ≠ 1` inside `M`. -/
theorem piPart_ne_bot_iff (π : Set ℕ) (M : Subgroup G) :
    piPart π M ≠ ⊥ ↔ piCore π ↥M ≠ ⊥ :=
  not_congr (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective)

/-- **Isaacs' `p`-type/`q`-type dichotomy.**  Every maximal subgroup of the minimal counterexample
has exactly one nontrivial core. -/
theorem piPart_ne_bot_xor (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {M : Subgroup G}
    (hM : IsCoatom M) :
    (piPart ({p} : Set ℕ) M ≠ ⊥ ∧ piPart ({q} : Set ℕ) M = ⊥) ∨
      (piPart ({p} : Set ℕ) M = ⊥ ∧ piPart ({q} : Set ℕ) M ≠ ⊥) := by
  rcases h.step3 hp hq hpq hM with hbot | hbot
  · refine Or.inr ⟨hbot, ?_⟩
    rcases h.piCore_ne_bot_or_of_isCoatom hpq hM with hne | hne
    · exact absurd ((piPart_ne_bot_iff ({p} : Set ℕ) M).mpr hne) (not_not.mpr hbot)
    · exact (piPart_ne_bot_iff ({q} : Set ℕ) M).mpr hne
  · refine Or.inl ⟨?_, hbot⟩
    rcases h.piCore_ne_bot_or_of_isCoatom hpq hM with hne | hne
    · exact (piPart_ne_bot_iff ({p} : Set ℕ) M).mpr hne
    · exact absurd ((piPart_ne_bot_iff ({q} : Set ℕ) M).mpr hne) (not_not.mpr hbot)



/-- A `p`-subgroup of `G` is proper, since `q` divides `|G|`. -/
theorem ne_top_of_isPGroup (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {V : Subgroup G}
    (hVp : IsPGroup p V) : V ≠ ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  intro htop
  rw [htop] at hVp
  obtain ⟨k, hk⟩ := (hVp.of_equiv Subgroup.topEquiv).exists_card_eq
  have hqG : q ∣ Nat.card G := h.symm.prime_dvd_card hq hp
  rw [hk] at hqG
  exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqG)).symm

/-! ### Step 4 -/

/-- **Step 4.**  If a `q`-central element `y` normalizes a `p`-subgroup `V`, then `V` contains no
`p`-central element.

Following Isaacs, we pass to the subgroup `V*` generated by the `p`-central elements of `V`, which
is again normalized by `y`, and we let `W` be maximal among the `p`-subgroups of `G` that are
normalized by `y` and generated by `p`-central elements.  If `V*` is nontrivial then so is `W`, and
we set `N = N_G(W)`.  A Sylow `p`-subgroup `S` of `N` cannot be a full Sylow `p`-subgroup of `G`,
since `⟨y⟩ ⊔ S ≤ N < ⊤` while Step 2 (with `p` and `q` interchanged) forces `⟨y⟩ ⊔ P = ⊤` for every
full Sylow `p`-subgroup `P`.  The Sylow escape argument therefore produces `g ∉ N` normalizing `S`,
and `W ^ g ≠ W`, so some `p`-central generator `z` of `W` has `z ^ g ∉ W`.  Writing `g = b * a` with
`b` in a Sylow `q`-subgroup centralizing `y` and `a` in a Sylow `p`-subgroup centralizing `z`, we
get `z ^ g = z ^ b ∈ W ^ b ⊓ N`, and then `(W ⊔ (W ^ b ⊓ N))*` is a `p`-group normalized by `y`,
generated by `p`-central elements, and strictly larger than `W` — contradicting the choice of
`W`. -/
theorem step4 (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {V : Subgroup G} (hVp : IsPGroup p V)
    {y : G} (hy : IsPCentral q y) (hyV : y ∈ Subgroup.normalizer (V : Set G)) :
    ∀ x ∈ V, ¬ IsPCentral p x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have := h.isSimpleGroup
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun U : Subgroup G => (U : Set G)) SetLike.coe_injective
  intro x hxV hxc
  -- the `p`-subgroups normalized by `y` and generated by `p`-central elements
  set 𝒮 : Set (Subgroup G) :=
    {U | IsPGroup p U ∧ y ∈ Subgroup.normalizer (U : Set G) ∧ pCentralPart p U = U} with h𝒮
  have hmem : ∀ U : Subgroup G, U ∈ 𝒮 ↔
      (IsPGroup p U ∧ y ∈ Subgroup.normalizer (U : Set G) ∧ pCentralPart p U = U) := by
    intro U
    rw [h𝒮]
    exact Iff.rfl
  have hVstar : pCentralPart p V ∈ 𝒮 :=
    (hmem _).mpr ⟨hVp.to_le (pCentralPart_le p V),
      map_conj_eq_self_iff.mp (map_conj_pCentralPart_self (map_conj_eq_self_iff.mpr hyV)),
      pCentralPart_idem p V⟩
  have : Nonempty ↥𝒮 := ⟨⟨pCentralPart p V, hVstar⟩⟩
  -- choose `W` of largest order in that family
  obtain ⟨W₀, hW₀⟩ := Finite.exists_max fun U : ↥𝒮 => Nat.card (U : Subgroup G)
  set W : Subgroup G := (W₀ : Subgroup G) with hWdef
  obtain ⟨hWp, hyW, hWstar⟩ := (hmem W).mp W₀.2
  have hmax : ∀ U ∈ 𝒮, Nat.card U ≤ Nat.card W := fun U hU => hW₀ ⟨U, hU⟩
  -- `W` is nontrivial, since it is at least as large as the nontrivial group `V*`
  have hxstar : x ∈ pCentralPart p V := mem_pCentralPart hxc hxV
  have hWne : W ≠ ⊥ := by
    intro hbot
    have hle := hmax _ hVstar
    rw [hbot, Subgroup.card_bot] at hle
    have hone : Nat.card (pCentralPart p V) = 1 := le_antisymm hle Nat.card_pos
    exact hxc.1 (Subgroup.mem_bot.mp (Subgroup.card_eq_one.mp hone ▸ hxstar))
  -- and `W` is not everything, since `q` divides `|G|`
  have hWtop : W ≠ ⊤ := h.ne_top_of_isPGroup hp hq hpq hWp
  -- `N = N_G(W)` is a proper subgroup containing `y`
  set N : Subgroup G := Subgroup.normalizer (W : Set G) with hNdef
  have hWN : W ≤ N := Subgroup.le_normalizer
  have hyN : y ∈ N := hyW
  have hNtop : N ≠ ⊤ := by
    intro htop
    have : W.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W inferInstance with hb | ht
    · exact hWne hb
    · exact hWtop ht
  -- a Sylow `p`-subgroup `S` of `N`, necessarily containing `W`
  obtain ⟨T⟩ : Nonempty (Sylow p ↥N) := inferInstance
  set S : Subgroup G := (T : Subgroup ↥N).map N.subtype with hSdef
  have hSN : S ≤ N := Subgroup.map_subtype_le _
  have hWS : W ≤ S := le_sylow_of_normal hWN le_rfl hWp T
  -- `y` is `q`-central: fix a Sylow `q`-subgroup `Q` with `y ∈ Z(Q)`
  obtain ⟨hy1, Q, hyQ, hyQc⟩ := id hy
  have hyzp : Subgroup.zpowers y ≠ ⊥ := fun hcon => hy1 (Subgroup.zpowers_eq_bot.mp hcon)
  have hQnorm : (Q : Subgroup G) ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
    refine le_trans ?_ (centralizer_le_normalizer (Subgroup.zpowers y))
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact Commute.zpow_left (hyQc z hz) n
  -- `S` is not a full Sylow `p`-subgroup of `G`, by Step 2 with `p` and `q` interchanged
  have hnotSylow : ∀ P : Sylow p G, S ≠ (P : Subgroup G) := by
    intro P heq
    have htop : Subgroup.zpowers y ⊔ (P : Subgroup G) = ⊤ :=
      h.symm.step2 hq hp (Ne.symm hpq) Q P hyzp hQnorm
    refine hNtop (top_le_iff.mp ?_)
    rw [← htop]
    refine sup_le (Subgroup.zpowers_le.mpr hyN) ?_
    rw [← heq]
    exact hSN
  -- the Sylow escape argument: some `g ∉ N` normalizes `S`
  obtain ⟨g, hgS, hgN⟩ := exists_conj_eq_not_mem hp T hnotSylow
  have hgW : W.map (MulAut.conj g).toMonoidHom ≠ W := fun hcon => hgN (map_conj_eq_self_iff.mp hcon)
  -- so some `p`-central generator of `W` is moved out of `W`
  have hex : ∃ z : G, IsPCentral p z ∧ z ∈ W ∧ g * z * g⁻¹ ∉ W := by
    by_contra hcon
    push Not at hcon
    have hstep : (pCentralPart p W).map (MulAut.conj g).toMonoidHom ≤ W := by
      rw [pCentralPart, MonoidHom.map_closure]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨z, ⟨hzc, hzW⟩, rfl⟩
      simpa using hcon z hzc hzW
    rw [hWstar] at hstep
    refine hgW (Subgroup.eq_of_le_of_card_ge hstep ?_)
    exact le_of_eq (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).symm
  obtain ⟨z, hzc, hzW, hznot⟩ := hex
  obtain ⟨hz1, P, hzP, hzPc⟩ := id hzc
  -- `G = QP`, so write `g = b * a` with `b ∈ Q` and `a ∈ P`
  obtain ⟨⟨b, a⟩, hba⟩ := (isComplement'_sylow hp hq hpq h.isPiGroup P Q).symm.2 g
  have hba' : (b : G) * (a : G) = g := hba
  -- since `a` centralizes `z`, conjugation by `g` acts on `z` as conjugation by `b`
  have hconj : g * z * g⁻¹ = (b : G) * z * (b : G)⁻¹ := by
    have haz : (a : G) * z * (a : G)⁻¹ = z := by
      rw [← hzPc (a : G) a.2]
      group
    calc g * z * g⁻¹ = (b : G) * ((a : G) * z * (a : G)⁻¹) * (b : G)⁻¹ := by
          rw [← hba']; group
      _ = (b : G) * z * (b : G)⁻¹ := by rw [haz]
  -- `y` normalizes `W ^ b ⊓ N`, hence also `W ⊔ (W ^ b ⊓ N)`
  have hyW' : W.map (MulAut.conj y).toMonoidHom = W := map_conj_eq_self_iff.mpr hyW
  have hyWb := map_conj_conj_of_commute hyW' (hyQc (b : G) b.2)
  have hyN' : N.map (MulAut.conj y).toMonoidHom = N :=
    map_conj_eq_self_iff.mpr (Subgroup.le_normalizer hyN)
  have hyU : (W ⊔ (W.map (MulAut.conj (b : G)).toMonoidHom ⊓ N)).map (MulAut.conj y).toMonoidHom
      = W ⊔ (W.map (MulAut.conj (b : G)).toMonoidHom ⊓ N) := by
    rw [Subgroup.map_sup, hyW', Subgroup.map_inf _ _ _ (MulAut.conj y).injective, hyWb, hyN']
  -- the join is a `p`-group, since `W ^ b ⊓ N` normalizes `W`
  have hUp : IsPGroup p ↥(W ⊔ (W.map (MulAut.conj (b : G)).toMonoidHom ⊓ N)) :=
    hWp.to_sup_of_normal_left' ((hWp.map (MulAut.conj (b : G)).toMonoidHom).to_le inf_le_left)
      inf_le_right
  -- its `p`-central part belongs to the family and strictly contains `W`
  have hUstar : pCentralPart p (W ⊔ (W.map (MulAut.conj (b : G)).toMonoidHom ⊓ N)) ∈ 𝒮 :=
    (hmem _).mpr ⟨hUp.to_le (pCentralPart_le _ _),
      map_conj_eq_self_iff.mp (map_conj_pCentralPart_self hyU), pCentralPart_idem _ _⟩
  have hWU : W ≤ pCentralPart p (W ⊔ (W.map (MulAut.conj (b : G)).toMonoidHom ⊓ N)) := by
    conv_lhs => rw [← hWstar]
    exact pCentralPart_mono le_sup_left
  have hzgmem : g * z * g⁻¹ ∈ W.map (MulAut.conj (b : G)).toMonoidHom ⊓ N := by
    constructor
    · rw [hconj]
      exact ⟨z, hzW, rfl⟩
    · have hmemS : g * z * g⁻¹ ∈ S.map (MulAut.conj g).toMonoidHom := ⟨z, hWS hzW, rfl⟩
      exact hSN (hgS.le hmemS)
  have hzgU : g * z * g⁻¹ ∈ pCentralPart p (W ⊔ (W.map (MulAut.conj (b : G)).toMonoidHom ⊓ N)) :=
    mem_pCentralPart (hzc.conj g) (Subgroup.mem_sup_right hzgmem)
  have hlt : W < pCentralPart p (W ⊔ (W.map (MulAut.conj (b : G)).toMonoidHom ⊓ N)) :=
    lt_of_le_of_ne hWU fun heq => hznot (by rw [heq]; exact hzgU)
  exact absurd (hmax _ hUstar) (not_le.mpr (card_lt_card_of_lt hlt))


/-! ### Step 5 -/

/-- The centre of a Sylow `p`-subgroup is nontrivial, so it contains an element of order `p`; such
an element is `p`-central and centralizes the whole Sylow subgroup. -/
theorem exists_isPCentral_of_sylow (hp : p.Prime) (hq : q.Prime) (P : Sylow p G) :
    ∃ x : G, IsPCentral p x ∧ orderOf x = p ∧ ∀ y ∈ (P : Subgroup G), x * y = y * x := by
  have : Fact p.Prime := ⟨hp⟩
  have hnt : Nontrivial ↥(P : Subgroup G) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (P.ne_bot_of_dvd_card (h.prime_dvd_card hp hq))
  have hcnt : Nontrivial (Subgroup.center ↥(P : Subgroup G)) := P.isPGroup'.center_nontrivial
  have hZp : IsPGroup p ↥(Subgroup.center ↥(P : Subgroup G)) := P.isPGroup'.to_subgroup _
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.center ↥(P : Subgroup G))) p (prime_dvd_card_of_nontrivial hp hZp)
  have hcomm : ∀ y ∈ (P : Subgroup G), ((z : ↥(P : Subgroup G)) : G) * y
      = y * ((z : ↥(P : Subgroup G)) : G) := fun y hy =>
    (congrArg Subtype.val ((Subgroup.mem_center_iff.mp z.2) ⟨y, hy⟩)).symm
  have horder : orderOf ((z : ↥(P : Subgroup G)) : G) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  refine ⟨((z : ↥(P : Subgroup G)) : G), ⟨?_, P, (z : ↥(P : Subgroup G)).2, hcomm⟩,
    horder, hcomm⟩
  intro hx1
  rw [hx1, orderOf_one] at horder
  exact hp.one_lt.ne horder

/-- **Step 5, first half.**  Every `p`-subgroup of `G` is centralized by a `p`-central element:
take a Sylow `p`-subgroup `P` containing it, and any element of order `p` in `Z(P)`. -/
theorem exists_isPCentral_mem_centralizer (hp : p.Prime) (hq : q.Prime) {V : Subgroup G}
    (hV : IsPGroup p V) : ∃ x : G, IsPCentral p x ∧ x ∈ Subgroup.centralizer (V : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hVP⟩ := hV.exists_le_sylow
  obtain ⟨x, hxc, _, hxP⟩ := h.exists_isPCentral_of_sylow hp hq P
  exact ⟨x, hxc, Subgroup.mem_centralizer_iff.mpr fun v hv => (hxP v (hVP hv)).symm⟩

/-- **Step 5, second half.**  A maximal subgroup of `p`-type contains no `q`-central element.

`V = O_p(M)` is nontrivial by Step 3, so `N_G(V) = M`, and Hall–Higman 1.2.3 inside the solvable
group `M` gives `C_G(V) = C_M(V) ≤ V`.  By the first half `C_G(V)` contains a `p`-central element,
hence so does `V`; Step 4 then forbids `q`-central elements in `N_G(V) = M`. -/
theorem step5 (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {M : Subgroup G} (hM : IsCoatom M)
    (hqbot : piPart ({q} : Set ℕ) M = ⊥) : ∀ y ∈ M, ¬ IsPCentral q y := by
  intro y hyM hy
  have hVne : piPart ({p} : Set ℕ) M ≠ ⊥ := by
    rcases h.piPart_ne_bot_xor hp hq hpq hM with ⟨hne, _⟩ | ⟨_, hne⟩
    · exact hne
    · exact absurd hqbot hne
  have hVM : piPart ({p} : Set ℕ) M ≤ M := piPart_le _ _
  have hVp : IsPGroup p (piPart ({p} : Set ℕ) M) := IsPiGroup.isPGroup (isPiGroup_piPart _ _)
  have hVnormal : ((piPart ({p} : Set ℕ) M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVM).mpr
      (piPart_normal_of_le_normalizer Subgroup.le_normalizer)
  have hnorm : Subgroup.normalizer ((piPart ({p} : Set ℕ) M : Subgroup G) : Set G) = M :=
    h.normalizer_eq_of_isCoatom hM hVM hVne
  -- `M` is solvable, so Hall–Higman applies to it
  have hsolv : Group.IsSolvable ↥M := h.isSolvable_of_isCoatom hM
  have hsep : IsPiSeparable ({p} : Set ℕ) ↥M := IsPiSeparable.of_isSolvable
  have hcompl : piPart (({p} : Set ℕ)ᶜ) M = ⊥ := by
    rw [piPart_compl_eq hpq (h.isPiGroup.to_subgroup M)]
    exact hqbot
  have hCV : Subgroup.centralizer ((piPart ({p} : Set ℕ) M : Subgroup G) : Set G)
      ≤ piPart ({p} : Set ℕ) M := by
    intro c hc
    refine inf_centralizer_piPart_le ({p} : Set ℕ) hsep hcompl ⟨?_, hc⟩
    rw [← hnorm]
    exact centralizer_le_normalizer _ hc
  obtain ⟨x, hxc, hxC⟩ := h.exists_isPCentral_mem_centralizer hp hq hVp
  refine h.step4 hp hq hpq hVp hy ?_ x (hCV hxC) hxc
  rw [hnorm]
  exact hyM

/-! ### Step 6 -/

/-- **Step 6.**  A `q`-central element normalizes no nontrivial `p`-subgroup.

A maximal subgroup `M` containing `N_G(V)` contains a `p`-central element, namely one centralizing
`V`; so `M` is not of `q`-type by Step 5 with the primes interchanged, hence of `p`-type by
Step 3, and then Step 5 keeps every `q`-central element out of `M ⊇ N_G(V)`. -/
theorem step6 (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {V : Subgroup G} (hVp : IsPGroup p V)
    (hVne : V ≠ ⊥) {y : G} (hy : IsPCentral q y) : y ∉ Subgroup.normalizer (V : Set G) := by
  intro hyV
  have := h.isSimpleGroup
  have hNtop : Subgroup.normalizer (V : Set G) ≠ ⊤ := by
    intro htop
    have : V.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal V inferInstance with hb | ht
    · exact hVne hb
    · exact h.ne_top_of_isPGroup hp hq hpq hVp ht
  obtain ⟨M, hM, hNM⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (Subgroup.normalizer (V : Set G))).resolve_left hNtop
  -- `M` contains a `p`-central element, so it is not of `q`-type
  obtain ⟨x, hxc, hxC⟩ := h.exists_isPCentral_mem_centralizer hp hq hVp
  have hxM : x ∈ M := hNM (centralizer_le_normalizer _ hxC)
  have hpne : piPart ({p} : Set ℕ) M ≠ ⊥ := fun hbot =>
    h.symm.step5 hq hp (Ne.symm hpq) hM hbot x hxM hxc
  -- hence of `p`-type, and then it contains no `q`-central element
  have hqbot : piPart ({q} : Set ℕ) M = ⊥ := (h.step3 hp hq hpq hM).resolve_left hpne
  exact h.step5 hp hq hpq hM hqbot y (hNM hyV) hy

/-! ### Step 7 -/

/-- **Step 7.**  Neither prime is `2`.

If `q = 2`, a `q`-central element of order `2` inverts an element `x` of odd prime order by
Isaacs' Theorem 2.13, and `x` has order `p` because `|G|` has no other odd prime divisor.  So a
`q`-central element normalizes the nontrivial `p`-subgroup `⟨x⟩`, which Step 6 forbids.

This is the one place where `Burnside.InvolutionInvertsElement` (Isaacs 2.13) is used; it is not
proved in this development. -/
theorem step7 (h213 : InvolutionInvertsElement.{u}) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    q ≠ 2 := by
  intro hq2
  have : Fact q.Prime := ⟨hq⟩
  have := h.isSimpleGroup
  -- a `q`-central element `t` of order `q = 2`
  obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
  obtain ⟨t, htc, htorder, -⟩ := h.symm.exists_isPCentral_of_sylow hq hp Q
  -- `O_2(G) = 1`, since `G` is simple and not a `q`-group
  have hO2 : piCore ({q} : Set ℕ) G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (piCore ({q} : Set ℕ) G) inferInstance with
      hb | ht
    · exact hb
    · refine absurd ?_ h.not_isSolvable
      have hGq : IsPiGroup ({q} : Set ℕ) G :=
        (ht ▸ isPiGroup_piCore).of_equiv Subgroup.topEquiv
      have : Group.IsNilpotent G := (IsPiGroup.isPGroup hGq).isNilpotent
      infer_instance
  have htO2 : t ∉ piCore ({2} : Set ℕ) G := by
    rw [← hq2, hO2]
    exact fun hmem => htc.1 (Subgroup.mem_bot.mp hmem)
  -- Isaacs 2.13 produces an element of odd prime order inverted by `t`
  obtain ⟨r, x, hr, hr2, hxorder, hinv⟩ := h213 G t (hq2 ▸ htorder) htO2
  -- that order must be `p`
  have hrdvd : r ∣ Nat.card G := hxorder ▸ orderOf_dvd_natCard x
  have hrp : r = p := by
    rcases IsPiGroup.iff_card.mp h.isPiGroup r
      (Nat.mem_primeFactors.mpr ⟨hr, hrdvd, Nat.card_pos.ne'⟩) with hr' | hr'
    · exact hr'
    · exact absurd (hq2 ▸ hr' : r = 2) hr2
  -- `⟨x⟩` is a nontrivial `p`-subgroup normalized by the `q`-central element `t`
  have hx1 : x ≠ 1 := by
    intro hx1
    rw [hx1, orderOf_one] at hxorder
    exact hr.ne_one hxorder.symm
  have hXp : IsPGroup p ↥(Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxorder, hrp, pow_one])
  have hXne : Subgroup.zpowers x ≠ ⊥ := fun hbot => hx1 (Subgroup.zpowers_eq_bot.mp hbot)
  refine h.step6 hp hq hpq hXp hXne htc ?_
  refine map_conj_eq_self_iff.mp (Subgroup.eq_of_le_of_card_ge ?_ ?_)
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hct : (MulAut.conj t) x = x⁻¹ := hinv
    change (MulAut.conj t) (x ^ n) ∈ Subgroup.zpowers x
    rw [map_zpow, hct]
    exact ⟨-n, by simp⟩
  · exact le_of_eq (Subgroup.card_map_of_injective (K := Subgroup.zpowers x)
      (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective).symm

/-!
## Step 8 and Step 9

Isaacs' last two steps are where Thompson's normal-`J` theorem (7.6,
`PiGroups.thompsonSubgroup_normal`) enters, and with it the Thompson subgroup itself.
-/

/-- Since `p ≠ 2` and `q ≠ 2`, the order of `G` is odd. -/
theorem not_two_dvd_card (hp2 : p ≠ 2) (hq2 : q ≠ 2) : ¬ (2 : ℕ) ∣ Nat.card G := by
  intro hdvd
  have hmem : (2 : ℕ) ∈ (Nat.card G).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hdvd, Nat.card_pos.ne'⟩
  have h1 := IsPiGroup.iff_card.mp h.isPiGroup 2 hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  rcases h1 with h1 | h1
  · exact hp2 h1.symm
  · exact hq2 h1.symm

omit h in
/-- If `|G|` is odd then every `2`-subgroup of a subgroup of `G` is trivial, hence abelian. -/
theorem forall_two_commute_of_not_two_dvd (h2 : ¬ (2 : ℕ) ∣ Nat.card G) (X : Subgroup G) :
    ∀ B : Subgroup ↥X, IsPGroup 2 ↥B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro B hB x hx y hy
  obtain ⟨k, hk⟩ := hB.exists_card_eq
  have hdvd : Nat.card ↥B ∣ Nat.card G :=
    (Subgroup.card_subgroup_dvd_card B).trans (Subgroup.card_subgroup_dvd_card X)
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rw [pow_zero] at hk
    have hbot : B = ⊥ := Subgroup.eq_bot_of_card_eq _ hk
    rw [hbot, Subgroup.mem_bot] at hx hy
    rw [hx, hy]
  · exact absurd ((dvd_pow_self 2 hkpos.ne').trans (hk ▸ hdvd)) h2

/-!
## The `p`-central element inside `Z(S)`

Isaacs: "Let `S ⊆ P ∈ Syl_p(G)`, and observe that `S = M ∩ P`.  Since `M` is a `p`-type maximal
subgroup, we can write `M = N_G(V)` for some `p`-subgroup `V`, and we have `V ⊆ S ⊆ P`.  Then
`Z(P) ⊆ N_G(V) ∩ P = M ∩ P = S`, and it follows that `Z(P) ⊆ Z(S)`."
-/

/-- A Sylow `p`-subgroup of a `p`-type maximal subgroup meets every Sylow `p`-subgroup of `G`
containing it in itself, and its centre contains a `p`-central element. -/
theorem exists_isPCentral_mem_centerOf (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {M : Subgroup G} (hM : IsCoatom M) (hqbot : piPart ({q} : Set ℕ) M = ⊥)
    {S : Subgroup G} (hSM : S ≤ M) (hSp : IsPGroup p ↥S) (hSsyl : ¬ p ∣ S.relIndex M) :
    ∃ z : G, IsPCentral p z ∧ z ∈ centerOf S := by
  have : Fact p.Prime := ⟨hp⟩
  -- `V = O_p(M)` is nontrivial and `M = N_G(V)`
  have hVne : piPart ({p} : Set ℕ) M ≠ ⊥ := by
    rcases h.piPart_ne_bot_xor hp hq hpq hM with ⟨hne, _⟩ | ⟨_, hne⟩
    · exact hne
    · exact absurd hqbot hne
  have hVM : piPart ({p} : Set ℕ) M ≤ M := piPart_le _ _
  have hVp : IsPGroup p (piPart ({p} : Set ℕ) M) := IsPiGroup.isPGroup (isPiGroup_piPart _ _)
  have hVnormal : ((piPart ({p} : Set ℕ) M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVM).mpr
      (piPart_normal_of_le_normalizer Subgroup.le_normalizer)
  have hnorm : Subgroup.normalizer ((piPart ({p} : Set ℕ) M : Subgroup G) : Set G) = M :=
    h.normalizer_eq_of_isCoatom hM hVM hVne
  -- `V ≤ S`
  have hVS : piPart ({p} : Set ℕ) M ≤ S := by
    have hsupp : IsPGroup p ↥(piPart ({p} : Set ℕ) M ⊔ S) :=
      isPGroup_sup_of_le_normalizer hVM hSM hnorm.ge hVp hSp
    have heq : S = piPart ({p} : Set ℕ) M ⊔ S :=
      eq_of_isPGroup_of_not_dvd_relIndex le_sup_right (sup_le hVM hSM) hsupp hSsyl
    exact heq ▸ le_sup_left
  -- a Sylow `p`-subgroup `P` of `G` above `S`, with `M ⊓ P = S`
  obtain ⟨P, hSP⟩ := hSp.exists_le_sylow
  have hMP : S = M ⊓ (P : Subgroup G) :=
    eq_of_isPGroup_of_not_dvd_relIndex (le_inf hSM hSP) inf_le_left
      (P.isPGroup'.to_le inf_le_right) hSsyl
  -- `Z(P) ≤ M ⊓ P = S`, hence `Z(P) ≤ Z(S)`
  have hZPM : centerOf (P : Subgroup G) ≤ M := by
    rw [← hnorm]
    refine le_trans ?_ (centralizer_le_normalizer _)
    exact (centerOf_le_centralizer _).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hVS.trans hSP)))
  have hZPS : centerOf (P : Subgroup G) ≤ S := hMP ▸ le_inf hZPM (centerOf_le _)
  have hZPZS : centerOf (P : Subgroup G) ≤ centerOf S :=
    le_inf hZPS ((centerOf_le_centralizer _).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hSP)))
  -- `Z(P)` is nontrivial, and its nonidentity elements are `p`-central
  have hPne : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card (h.prime_dvd_card hp hq)
  have hex : ∃ z ∈ centerOf (P : Subgroup G), z ≠ 1 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact centerOf_ne_bot P.isPGroup' hPne
      (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx))
  obtain ⟨z, hzZ, hz1⟩ := hex
  refine ⟨z, ⟨hz1, P, hzZ.1, fun y hy => ?_⟩, hZPZS hzZ⟩
  exact (Subgroup.mem_centralizer_iff.mp hzZ.2 y hy).symm

/-- `p` divides the order of a `p`-type maximal subgroup. -/
theorem prime_dvd_card_of_pType (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {M : Subgroup G}
    (hM : IsCoatom M) (hqbot : piPart ({q} : Set ℕ) M = ⊥) : p ∣ Nat.card ↥M := by
  have hVne : piPart ({p} : Set ℕ) M ≠ ⊥ := by
    rcases h.piPart_ne_bot_xor hp hq hpq hM with ⟨hne, _⟩ | ⟨_, hne⟩
    · exact hne
    · exact absurd hqbot hne
  exact (prime_dvd_card_of_ne_bot hp (IsPiGroup.isPGroup (isPiGroup_piPart _ _)) hVne).trans
    (Subgroup.card_dvd_of_le (piPart_le _ _))

/-- **Step 8, the fifth hypothesis of the normal-`J` theorem.**  `C_M(Z(S)) = S`.

If `C_M(Z(S))` were not a `p`-group it would contain an element `y` of order `q`, and the
`p`-central element `z ∈ Z(S)` would then normalize `⟨y⟩` — against Step 6 with `p` and `q`
interchanged.  So `C_M(Z(S))` is a `p`-subgroup of `M` containing the Sylow subgroup `S`. -/
theorem centralizer_centerOf_inf_eq_of_pType (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {M : Subgroup G} (hM : IsCoatom M) (hqbot : piPart ({q} : Set ℕ) M = ⊥)
    {S : Subgroup G} (hSM : S ≤ M) (hSp : IsPGroup p ↥S) (hSsyl : ¬ p ∣ S.relIndex M) :
    Subgroup.centralizer ((centerOf S : Subgroup G) : Set G) ⊓ M = S := by
  have hpf : Fact p.Prime := ⟨hp⟩
  have hqf : Fact q.Prime := ⟨hq⟩
  obtain ⟨z, hzc, hzZ⟩ := h.exists_isPCentral_mem_centerOf hp hq hpq hM hqbot hSM hSp hSsyl
  set C : Subgroup G := Subgroup.centralizer ((centerOf S : Subgroup G) : Set G) ⊓ M with hCdef
  have hSC : S ≤ C := le_inf (le_centralizer_centerOf S) hSM
  have hCp : IsPGroup p ↥C := by
    by_contra hnp
    -- `q` divides `|C|`
    have hqdvd : q ∣ Nat.card ↥C := by
      by_contra hnq
      refine hnp (IsPiGroup.isPGroup ?_)
      rw [IsPiGroup.iff_card]
      intro r hr
      have h1 := IsPiGroup.iff_card.mp (h.isPiGroup.to_subgroup C) r hr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ (Nat.mem_primeFactors.mp hr).2.1) hnq
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) q hqdvd
    have hordy : orderOf ((y : ↥C) : G) = q := by rw [Subgroup.orderOf_coe]; exact hy
    have hYq : IsPGroup q ↥(Subgroup.zpowers ((y : ↥C) : G)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hordy, pow_one]
    have hYne : Subgroup.zpowers ((y : ↥C) : G) ≠ ⊥ := by
      intro hbot
      have h1 : ((y : ↥C) : G) = 1 :=
        Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers ((y : ↥C) : G))
      rw [h1, orderOf_one] at hordy
      exact hq.one_lt.ne hordy
    -- `z` centralizes `y`, hence normalizes `⟨y⟩`
    have hzy : z * ((y : ↥C) : G) = ((y : ↥C) : G) * z :=
      Subgroup.mem_centralizer_iff.mp (y : ↥C).2.1 z hzZ
    have hzN : z ∈ Subgroup.normalizer
        ((Subgroup.zpowers ((y : ↥C) : G) : Subgroup G) : Set G) := by
      refine centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      rintro w hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact (Commute.symm hzy).zpow_left n
    exact h.symm.step6 hq hp (Ne.symm hpq) hYq hYne hzc hzN
  exact (eq_of_isPGroup_of_not_dvd_relIndex hSC inf_le_right hCp hSsyl).symm

/-!
## Step 8
-/

/-- **Isaacs 7.8, Step 8.**  Let `M` be a `p`-type maximal subgroup and `S ∈ Syl_p(M)`.  Then
`J(S) ⊴ M` and `S` is a full Sylow `p`-subgroup of `G`.

`M` satisfies the five hypotheses of the normal-`J` theorem: it is solvable, `p ≠ 2`, its Sylow
`2`-subgroups are trivial because `|G|` is odd, `O_p′(M) = O_q(M) = 1` because `M` is of
`p`-type, and `C_M(Z(S)) = S`.  If `S` were not Sylow in `G`, normalizers would grow to a
`p`-group `T > S` normalizing `J(S)`, so `T ≤ N_G(J(S)) = M`, against `S ∈ Syl_p(M)`. -/
theorem step8 (h213 : InvolutionInvertsElement.{u}) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {M : Subgroup G} (hM : IsCoatom M) (hqbot : piPart ({q} : Set ℕ) M = ⊥)
    {S : Subgroup G} (hSM : S ≤ M) (hSp : IsPGroup p ↥S) (hSsyl : ¬ p ∣ S.relIndex M) :
    M ≤ Subgroup.normalizer ((thompsonSubgroup p S : Subgroup G) : Set G) ∧ ¬ p ∣ S.index := by
  have hpf : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := h.symm.step7 h213 hq hp (Ne.symm hpq)
  have hq2 : q ≠ 2 := h.step7 h213 hp hq hpq
  have h2 : ¬ (2 : ℕ) ∣ Nat.card G := h.not_two_dvd_card hp2 hq2
  -- `S`, read inside `M`, is a Sylow `p`-subgroup
  have hSsub : IsPGroup p ↥(S.subgroupOf M) :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSM).symm
  have hSi : ¬ p ∣ (S.subgroupOf M).index := hSsyl
  set S' : Sylow p ↥M := hSsub.toSylow hSi with hS'def
  have hS'coe : (S' : Subgroup ↥M) = S.subgroupOf M := rfl
  -- the hypotheses of the normal-`J` theorem
  have hsolvM : Group.IsSolvable ↥M := h.isSolvable_of_isCoatom hM
  have hsep : IsPiSeparable ({p} : Set ℕ) ↥M := IsPiSeparable.of_isSolvable
  have hcore : piCore (({p} : Set ℕ)ᶜ) ↥M = ⊥ := by
    rw [piCore_compl_singleton_eq hpq (h.isPiGroup.to_subgroup M)]
    exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp hqbot
  have hP5 : Subgroup.centralizer ((centerOf (S' : Subgroup ↥M) : Subgroup ↥M) : Set ↥M)
      = (S' : Subgroup ↥M) := by
    rw [hS'coe, centerOf_subgroupOf hSM, ← centralizer_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr ((centerOf_le S).trans hSM),
      ← Subgroup.inf_subgroupOf_right,
      h.centralizer_centerOf_inf_eq_of_pType hp hq hpq hM hqbot hSM hSp hSsyl]
  have hJnormal : (thompsonSubgroup p (S' : Subgroup ↥M)).Normal :=
    thompsonSubgroup_normal hp2 hsep (forall_two_commute_of_not_two_dvd h2 M) hcore S' hP5
  have hJsub : ((thompsonSubgroup p S).subgroupOf M).Normal := by
    rw [← thompsonSubgroup_subgroupOf hSM, ← hS'coe]
    exact hJnormal
  have hJM : M ≤ Subgroup.normalizer ((thompsonSubgroup p S : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      ((thompsonSubgroup_le p S).trans hSM)).mp hJsub
  refine ⟨hJM, ?_⟩
  -- `S` is a full Sylow `p`-subgroup of `G`
  intro hdvd
  have hSne : S ≠ ⊥ := by
    intro hbot
    refine hSsyl ?_
    rw [hbot, Subgroup.relIndex, Subgroup.bot_subgroupOf, Subgroup.index_bot]
    exact h.prime_dvd_card_of_pType hp hq hpq hM hqbot
  have hJne : thompsonSubgroup p S ≠ ⊥ := thompsonSubgroup_ne_bot hp hSp hSne
  have hJnorm : Subgroup.normalizer ((thompsonSubgroup p S : Subgroup G) : Set G) = M :=
    h.normalizer_eq_of_isCoatom hM ((thompsonSubgroup_le p S).trans hSM) hJne
  obtain ⟨P, hSP⟩ := hSp.exists_le_sylow
  have hSlt : S < (P : Subgroup G) :=
    lt_of_le_of_ne hSP fun heq => P.not_dvd_index (heq ▸ hdvd)
  have hTlt : S < (P : Subgroup G) ⊓ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
    lt_inf_normalizer P.isPGroup' hSlt
  have hTM : (P : Subgroup G) ⊓ Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ M := by
    rw [← hJnorm]
    exact le_normalizer_of_characteristic_subgroupOf (thompsonSubgroup_le p S)
      (thompsonSubgroup_characteristic p S) inf_le_right
  exact absurd (eq_of_isPGroup_of_not_dvd_relIndex hTlt.le hTM
    (P.isPGroup'.to_le inf_le_left) hSsyl) hTlt.ne

/-!
## Step 9: the counting

Isaacs: "`|G_p|² > |G_p||G_q| = |G| ≥ |ST| = |S||T|/|S ∩ T| = |G_p|²/|S ∩ T|`, and so
`|S ∩ T| > 1`."  We reach the same conclusion from `|S ⊓ T : 1| ≤ |S : 1| ⬝ |T : 1|`
(`Subgroup.index_inf_le`), which avoids the product formula for sets.
-/

omit h in
/-- Sylow `p`-subgroups have equal order. -/
theorem sylow_card_eq (hp : p.Prime) (S T : Sylow p G) :
    Nat.card ↥(S : Subgroup G) = Nat.card ↥(T : Subgroup G) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [S.card_eq_multiplicity, T.card_eq_multiplicity]

omit h in
/-- Sylow `p`-subgroups have equal index. -/
theorem sylow_index_eq (hp : p.Prime) (S T : Sylow p G) :
    (S : Subgroup G).index = (T : Subgroup G).index := by
  have h1 := Subgroup.card_mul_index (S : Subgroup G)
  have h2 := Subgroup.card_mul_index (T : Subgroup G)
  rw [sylow_card_eq hp S T] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)

/-- In a `{p, q}`-group the index of a Sylow `p`-subgroup is the order of a Sylow
`q`-subgroup. -/
theorem sylow_index_eq_card (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (P : Sylow p G) (Q : Sylow q G) :
    (P : Subgroup G).index = Nat.card ↥(Q : Subgroup G) := by
  have hpf : Fact p.Prime := ⟨hp⟩
  have hqf : Fact q.Prime := ⟨hq⟩
  have h1 : Nat.card ↥(P : Subgroup G) * Nat.card ↥(Q : Subgroup G) = Nat.card G := by
    rw [P.card_eq_multiplicity, Q.card_eq_multiplicity]
    exact (card_eq_pow_mul_pow hpq h.isPiGroup).symm
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos
    ((Subgroup.card_mul_index (P : Subgroup G)).trans h1.symm)

/-- The `p`-part and the `q`-part of `|G|` are different. -/
theorem sylow_card_ne (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (P : Sylow p G)
    (Q : Sylow q G) : Nat.card ↥(P : Subgroup G) ≠ Nat.card ↥(Q : Subgroup G) := by
  have hpf : Fact p.Prime := ⟨hp⟩
  have hqf : Fact q.Prime := ⟨hq⟩
  intro heq
  rw [P.card_eq_multiplicity, Q.card_eq_multiplicity] at heq
  have hfac : (Nat.card G).factorization p = 0 := by
    by_contra hne
    have hdvd : p ∣ q ^ (Nat.card G).factorization q := by
      rw [← heq]; exact dvd_pow_self p hne
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd))
  refine P.ne_bot_of_dvd_card (h.prime_dvd_card hp hq) (Subgroup.eq_bot_of_card_eq _ ?_)
  rw [P.card_eq_multiplicity, hfac, pow_zero]

omit h in
/-- **Isaacs' counting.**  When the `p`-part of `|G|` exceeds the `q`-part, any two Sylow
`p`-subgroups meet nontrivially. -/
theorem one_lt_card_inf_sylow (hp : p.Prime) (S T : Sylow p G)
    (hlt : (S : Subgroup G).index < Nat.card ↥(S : Subgroup G)) :
    1 < Nat.card ↥((S : Subgroup G) ⊓ (T : Subgroup G)) := by
  by_contra hcon
  have hpos := Nat.card_pos (α := ↥((S : Subgroup G) ⊓ (T : Subgroup G)))
  have hone : Nat.card ↥((S : Subgroup G) ⊓ (T : Subgroup G)) = 1 := by omega
  have hidx : ((S : Subgroup G) ⊓ (T : Subgroup G)).index
      ≤ (S : Subgroup G).index * (T : Subgroup G).index := Subgroup.index_inf_le
  have hmul := Subgroup.card_mul_index ((S : Subgroup G) ⊓ (T : Subgroup G))
  rw [hone, one_mul] at hmul
  have hSmul := Subgroup.card_mul_index (S : Subgroup G)
  have hbpos : 0 < (S : Subgroup G).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [sylow_index_eq hp T S, hmul, ← hSmul] at hidx
  exact absurd (Nat.le_of_mul_le_mul_right hidx hbpos) (Nat.not_le.mpr hlt)

/-- The Thompson subgroups of the Sylow `p`-subgroups are not all equal: otherwise `J(P)` would
be a nontrivial proper normal subgroup of the simple group `G`. -/
theorem exists_ne_thompsonSubgroup (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∃ S T : Sylow p G, thompsonSubgroup p (S : Subgroup G) ≠ thompsonSubgroup p (T : Subgroup G) :=
  by
  have hpf : Fact p.Prime := ⟨hp⟩
  have := h.isSimpleGroup
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  have hPne : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card (h.prime_dvd_card hp hq)
  have hJne : thompsonSubgroup p (P : Subgroup G) ≠ ⊥ :=
    thompsonSubgroup_ne_bot hp P.isPGroup' hPne
  have hJnormal : (thompsonSubgroup p (P : Subgroup G)).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    intro g _
    refine map_conj_eq_self_iff.mp ?_
    rw [← thompsonSubgroup_map_equiv (MulAut.conj g) (P : Subgroup G)]
    exact (hcon (g • P) P).symm ▸ rfl
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal _ hJnormal with hbot | htop
  · exact hJne hbot
  · exact h.ne_top_of_isPGroup hp hq hpq P.isPGroup'
      (top_le_iff.mp (htop ▸ thompsonSubgroup_le p (P : Subgroup G)))

/-- **Isaacs 7.8, Step 9**, under the assumption that the `p`-part of `|G|` exceeds the `q`-part.

Choose `S, T ∈ Syl_p(G)` with `J(S) ≠ J(T)` and `D = S ⊓ T` as large as possible; `D > 1` by the
counting, so `N_G(D)` is proper and lies in a maximal subgroup `M`, which contains a `p`-central
element and so is of `p`-type.  A Sylow `p`-subgroup `U` of `M` containing `M ⊓ S` is Sylow in
`G` by Step 8 and meets `S` above `D`, so `J(U) = J(S)` by maximality; likewise `J(V) = J(T)`.
But `U` and `V` are `M`-conjugate and `J(U) ⊴ M`, so `J(S) = J(T)`. -/
theorem step9_aux (h213 : InvolutionInvertsElement.{u}) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q)
    (hbig : ∀ S : Sylow p G, (S : Subgroup G).index < Nat.card ↥(S : Subgroup G)) : False := by
  have hpf : Fact p.Prime := ⟨hp⟩
  have := h.isSimpleGroup
  obtain ⟨⟨S, T⟩, hmem, hmax⟩ := Set.exists_max_image
    {ST : Sylow p G × Sylow p G |
      thompsonSubgroup p (ST.1 : Subgroup G) ≠ thompsonSubgroup p (ST.2 : Subgroup G)}
    (fun ST => Nat.card ↥((ST.1 : Subgroup G) ⊓ (ST.2 : Subgroup G))) (Set.toFinite _)
    (by
      obtain ⟨S₀, T₀, hST₀⟩ := h.exists_ne_thompsonSubgroup hp hq hpq
      exact ⟨(S₀, T₀), hST₀⟩)
  have hST : thompsonSubgroup p (S : Subgroup G) ≠ thompsonSubgroup p (T : Subgroup G) := hmem
  have hSneT : (S : Subgroup G) ≠ (T : Subgroup G) := fun heq => hST (by rw [heq])
  set D : Subgroup G := (S : Subgroup G) ⊓ (T : Subgroup G) with hDdef
  have hDS : D < (S : Subgroup G) :=
    lt_of_le_of_ne inf_le_left fun heq =>
      hSneT (Subgroup.eq_of_le_of_card_ge (heq ▸ (inf_le_right : D ≤ (T : Subgroup G)))
        (sylow_card_eq hp T S).le)
  have hDT : D < (T : Subgroup G) :=
    lt_of_le_of_ne inf_le_right fun heq =>
      hSneT (Subgroup.eq_of_le_of_card_ge (heq ▸ (inf_le_left : D ≤ (S : Subgroup G)))
        (sylow_card_eq hp S T).le).symm
  -- `D > 1`, so `N_G(D)` is proper
  have hD1 : 1 < Nat.card ↥D := one_lt_card_inf_sylow hp S T (hbig S)
  have hDne : D ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hD1
    omega
  have hDp : IsPGroup p ↥D := S.isPGroup'.to_le inf_le_left
  have hNDne : Subgroup.normalizer ((D : Subgroup G) : Set G) ≠ ⊤ := by
    intro htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D
      (Subgroup.normalizer_eq_top_iff.mp htop) with hbot | htop'
    · exact hDne hbot
    · exact h.ne_top_of_isPGroup hp hq hpq S.isPGroup'
        (top_le_iff.mp (htop' ▸ hDS.le))
  obtain ⟨M, hM, hNDM⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom
      (Subgroup.normalizer ((D : Subgroup G) : Set G))).resolve_left hNDne
  -- `M` contains a `p`-central element, hence is of `p`-type
  obtain ⟨x, hxc, hxC⟩ := h.exists_isPCentral_mem_centralizer hp hq hDp
  have hxM : x ∈ M := hNDM (centralizer_le_normalizer D hxC)
  have hqbot : piPart ({q} : Set ℕ) M = ⊥ := by
    rcases h.piPart_ne_bot_xor hp hq hpq hM with ⟨_, hbot⟩ | ⟨hbot, _⟩
    · exact hbot
    · exact absurd hxc (h.symm.step5 hq hp (Ne.symm hpq) hM hbot x hxM)
  -- for `R = S` and `R = T`, a Sylow `p`-subgroup of `M` with the same Thompson subgroup
  have hfind : ∀ R : Sylow p G, D < (R : Subgroup G) →
      ∃ U : Subgroup G, U ≤ M ∧ IsPGroup p ↥U ∧ ¬ p ∣ U.relIndex M ∧
        thompsonSubgroup p U = thompsonSubgroup p (R : Subgroup G) := by
    intro R hDR
    obtain ⟨U, hMRU, hUM, hUp, hUi⟩ :=
      exists_sylow_le_of_le (H := M) (X := M ⊓ (R : Subgroup G)) inf_le_left
        (R.isPGroup'.to_le inf_le_right)
    have hUsyl : ¬ p ∣ U.index := (h.step8 h213 hp hq hpq hM hqbot hUM hUp hUi).2
    refine ⟨U, hUM, hUp, hUi, ?_⟩
    by_contra hne
    have hDlt : Nat.card ↥D < Nat.card ↥(U ⊓ (R : Subgroup G)) := by
      refine card_lt_card_of_lt (lt_of_lt_of_le (lt_inf_normalizer R.isPGroup' hDR) ?_)
      exact le_inf
        (le_trans (le_inf (inf_le_right.trans hNDM) inf_le_left) hMRU) inf_le_left
    exact absurd (hmax ((hUp.toSylow hUsyl : Sylow p G), R) hne) (Nat.not_le.mpr hDlt)
  obtain ⟨U, hUM, hUp, hUi, hJU⟩ := hfind S hDS
  obtain ⟨V, hVM, hVp, hVi, hJV⟩ := hfind T hDT
  -- `U` and `V` are conjugate in `M`, and `J(U) ⊴ M`
  obtain ⟨n, hnM, hVeq⟩ := exists_conj_of_sylow_le hUM hVM hUp hVp hUi hVi
  have hJM : M ≤ Subgroup.normalizer ((thompsonSubgroup p U : Subgroup G) : Set G) :=
    (h.step8 h213 hp hq hpq hM hqbot hUM hUp hUi).1
  have hUV : thompsonSubgroup p V = thompsonSubgroup p U := by
    rw [hVeq, thompsonSubgroup_map_equiv, map_conj_eq_self_iff.mpr (hJM hnM)]
  exact hST (by rw [← hJU, ← hJV]; exact hUV.symm)

/-- **Isaacs 7.8, Step 9.**  The minimal counterexample does not exist. -/
theorem step9 (h213 : InvolutionInvertsElement.{u}) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    False := by
  have hpf : Fact p.Prime := ⟨hp⟩
  have hqf : Fact q.Prime := ⟨hq⟩
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
  have hne := h.sylow_card_ne hp hq hpq P Q
  rcases Nat.lt_or_ge (Nat.card ↥(Q : Subgroup G)) (Nat.card ↥(P : Subgroup G)) with hlt | hge
  · refine h.step9_aux h213 hp hq hpq fun S => ?_
    rw [h.sylow_index_eq_card hp hq hpq S Q, sylow_card_eq hp S P]
    exact hlt
  · refine h.symm.step9_aux h213 hq hp (Ne.symm hpq) fun S => ?_
    rw [h.symm.sylow_index_eq_card hq hp (Ne.symm hpq) S P, sylow_card_eq hq S Q]
    omega

end IsMinCounterexample

/-!
## The reduction
-/

/-- Auxiliary induction for `Burnside.isSolvable_of_forall_not_isMinCounterexample`. -/
theorem isSolvable_of_forall_not_aux
    (hno : ∀ (X : Type u) [Group X] [Finite X], ¬ IsMinCounterexample p q X) :
    ∀ (X : Type u) [Group X] [Finite X], IsPiGroup {p, q} X →
      Group.IsSolvable X := by
  refine induction_on_card ?_
  intro X _ _ ih hX
  by_contra hcon
  exact hno X ⟨hX, hcon, fun H _ _ hH hlt ↦ ih H hlt hH⟩

/-- **The reduction to a minimal counterexample.**  If no group is a minimal counterexample, then
every `{p, q}`-group is solvable. -/
theorem isSolvable_of_forall_not_isMinCounterexample
    (hno : ∀ (X : Type u) [Group X] [Finite X], ¬ IsMinCounterexample p q X)
    (hG : IsPiGroup {p, q} G) : Group.IsSolvable G :=
  isSolvable_of_forall_not_aux hno G hG

/-- **Burnside's `p ^ a q ^ b` theorem**, modulo the nonexistence of a minimal counterexample. -/
theorem isSolvable_of_card_eq
    (hno : ∀ (X : Type u) [Group X] [Finite X], ¬ IsMinCounterexample p q X)
    (hp : p.Prime) (hq : q.Prime) {a b : ℕ} (hcard : Nat.card G = p ^ a * q ^ b) :
    Group.IsSolvable G :=
  isSolvable_of_forall_not_isMinCounterexample hno (isPiGroup_pair_of_card_eq hp hq hcard)

/-!
## Burnside's theorem
-/

/-- **No minimal counterexample exists.** -/
theorem not_isMinCounterexample (hp : p.Prime) (hq : q.Prime) :
    ¬ IsMinCounterexample p q G := by
  intro h
  rcases eq_or_ne p q with rfl | hpq
  · have hpf : Fact p.Prime := ⟨hp⟩
    have h1 := h.isPiGroup
    rw [Set.pair_eq_singleton p] at h1
    have hPG : IsPGroup p G := IsPiGroup.isPGroup h1
    have : Group.IsNilpotent G := hPG.isNilpotent
    exact h.not_isSolvable inferInstance
  · exact h.step9 PiGroups.involutionInvertsElement hp hq hpq

/-- **Burnside's `p ^ a q ^ b` theorem.**  A finite group whose order has at most two prime
divisors is solvable. -/
theorem isSolvable_of_isPiGroup_pair (hp : p.Prime) (hq : q.Prime)
    (hG : IsPiGroup {p, q} G) : Group.IsSolvable G :=
  isSolvable_of_forall_not_isMinCounterexample (fun _ _ _ => not_isMinCounterexample hp hq) hG

/-- **Burnside's `p ^ a q ^ b` theorem.**  A finite group of order `p ^ a * q ^ b`, for primes
`p` and `q`, is solvable. -/
theorem isSolvable_of_card_eq_pow_mul_pow (hp : p.Prime) (hq : q.Prime) {a b : ℕ}
    (hcard : Nat.card G = p ^ a * q ^ b) : Group.IsSolvable G :=
  isSolvable_of_card_eq (fun _ _ _ => not_isMinCounterexample hp hq) hp hq hcard

end Burnside
