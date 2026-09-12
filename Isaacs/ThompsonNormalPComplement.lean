module

public import Isaacs.NormalJTheorem

/-!
# Thompson's normal `p`-complement theorem: Isaacs 7.1

Isaacs, *Finite Group Theory*, Theorem 7.1 (Thompson):

> Let `P ∈ Syl_p(G)`, where `G` is a finite group and `p ≠ 2`, and assume that `C_G(Z(P))` and
> `N_G(J(P))` have normal `p`-complements.  Then `G` has a normal `p`-complement.

This is `PiGroups.hasNormalPComplement_of_thompson` (and
`PiGroups.hasNormalPComplement_of_thompson'`, stated for one Sylow `p`-subgroup as Isaacs does).
It completes the proof that Frobenius kernels are nilpotent.

**It is not a corollary of Frobenius' Theorem 5.26 and the normal-`J` theorem 7.6.**  Isaacs
proves it by a minimal-counterexample argument of its own, in seven steps, which *uses* both of
those: 5.26 to produce a nonidentity `p`-subgroup whose normalizer has no normal `p`-complement,
and 7.6 for the final contradiction.

`PiGroups.ThompsonHypothesis` is the hypothesis, stated for every Sylow `p`-subgroup;
`PiGroups.thompsonHypothesis_of_sylow` is Isaacs' remark that checking one suffices.  The minimal
counterexample chooses a "bad" subgroup `U` (`PiGroups.Bad`) with `|N_G(U)|_p` as large as
possible and then `|U|` as large as possible, which `PiGroups.badWeight` packs into a single
natural number so that `PiGroups.exists_bad_max` is an ordinary finite maximum.  Writing
`Ḡ = G/U` and `L = bigL p G` for the preimage of `L̄ = O_p′(Ḡ)` (as in
`Isaacs/NormalJTheorem.lean`), the steps are:

* `PiGroups.thompson_step_one` — **Step 1**: `U = O_p(G)`.  If `N_G(U)` were proper, some `X` —
  `J(S)` or `Z(S)` for `S ∈ Syl_p(N_G(U))` — would be bad; `S` is not Sylow in `G`, so
  normalizers grow and `X` is normalized by a `p`-group strictly larger than `S`, giving
  `|N_G(X)|_p > |N_G(U)|_p` against the choice of `U`;
* `PiGroups.thompson_step_two` — **Step 2**: `G / U` has a normal `p`-complement.  The preimage
  `X` of `J(P̄)` or `Z(P̄)` satisfies `U < X ≤ P` with `P ≤ N_G(X)`, so `X` is not bad, and
  `N_Ḡ(X̄) = N_G(X)‾`.  With `PiGroups.isPiSeparable_of_hasNormalPComplement_quotient` this
  makes `G` `p`-solvable;
* `PiGroups.thompson_step_three` — **Step 3**: `O_p′(G) = 1`, via Lemma 7.7;
* `PiGroups.thompson_step_four` — **Step 4**: `P` is a maximal subgroup.  A proper `H ⊇ P`
  inherits the hypothesis, so has a normal `p`-complement `K`; both `K` and `O_p(G)` are
  normalized by `H` and meet trivially, so Hall–Higman forces `K = 1`;
* `PiGroups.thompson_step_five` — **Step 5**: `C_G(Z(P)) = P`;
* `PiGroups.thompson_step_six` — **Step 6**: `L̄` is abelian.  No nontrivial proper subgroup of
  `L̄` is `P̄`-invariant, so the `P̄`-invariant Sylow `q`-subgroup supplied by coprime action
  (`NoncyclicAbelian.exists_invariant_sylow`) is all of `L̄`; then `⁅L̄, L̄⁆` is proper and
  `P̄`-invariant, hence trivial;
* **Step 7** is inside the main theorem: a Sylow `2`-subgroup `Q` of `G` has `Q̄ ≤ L̄` and
  `Q ⊓ U = 1`, so `Q` is abelian; 7.6 then makes `J(P) ⊴ G`, and `G = N_G(J(P))` has a normal
  `p`-complement after all.

**Isaacs' Lemma 7.7** — `N_Ḡ(P̄) = N_G(P)‾` and `C_Ḡ(P̄) = C_G(P)‾` modulo a normal
`p′`-subgroup — is `PiGroups.normalizer_map_mk'_eq_of_not_dvd` and
`PiGroups.centralizer_map_mk'_le_of_not_dvd`.  Its first half is Isaacs' Lemma 2.17, which
`Isaacs/PLocalSubgroups.lean` derives from conjugacy of complements and so carries the
`SchurZassenhausConjugacy` hypothesis; the proof here follows Isaacs' own Frattini argument
(`P ∈ Syl_p(P N)`, so a conjugate of `P` inside `P N` is already `P N`-conjugate to it), which
needs only Sylow's theorem.  So this file, like 7.5 and 7.6, is hypothesis-free.
-/

@[expose] public section

namespace PiGroups

open scoped commutatorElement

universe u

variable {G : Type u} [Group G] {p : ℕ}

/-!
## The centre and the Thompson subgroup under the inclusion of a subgroup
-/

/-- `Z(Q)`, read inside `Q`, is the centre of `Q`; in particular it is characteristic. -/
instance centerOf_characteristic (Q : Subgroup G) : ((centerOf Q).subgroupOf Q).Characteristic := by
  have h : (centerOf Q).subgroupOf Q = Subgroup.center ↥Q := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff]
    constructor
    · intro hx y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 (y : G) y.2)
    · intro hx
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      exact congrArg Subtype.val (hx ⟨y, hy⟩)
  rw [h]
  infer_instance

/-- The centre of a subgroup is the same computed inside `H` or inside `G`. -/
theorem map_centerOf {H : Subgroup G} (S : Subgroup ↥H) :
    (centerOf S).map H.subtype = centerOf (S.map H.subtype) := by
  have hcen := centralizer_map_subtype (H := H) S
  have hmap : (Subgroup.centralizer ((S : Set ↥H))).map H.subtype
      = Subgroup.centralizer ((S.map H.subtype : Subgroup G) : Set G) ⊓ H := by
    rw [← hcen, Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [centerOf, centerOf, Subgroup.map_inf S (Subgroup.centralizer ((S : Set ↑H))) H.subtype
    H.subtype_injective, hmap, ← inf_assoc,
    inf_eq_left.mpr (inf_le_left.trans (Subgroup.map_subtype_le S))]

/-- Membership in `E(Q)` transfers between `H` and `G`. -/
theorem mem_maxElemAb_map {H : Subgroup G} {S A : Subgroup ↥H} (hA : A ∈ maxElemAb p S) :
    A.map H.subtype ∈ maxElemAb p (S.map H.subtype) := by
  refine ⟨Subgroup.map_mono hA.1, hA.2.1.map _, fun B hB hBea => ?_⟩
  have hBH : B ≤ H := hB.trans (Subgroup.map_subtype_le S)
  have hBsub : B.subgroupOf H ≤ S := by
    rw [← Subgroup.comap_map_eq_self_of_injective H.subtype_injective S]
    exact Subgroup.comap_mono hB
  have h1 : Nat.card ↥(B.subgroupOf H) ≤ Nat.card ↥A :=
    hA.2.2 _ hBsub (hBea.comap_of_injective H.subtype_injective)
  have h2 : Nat.card ↥((B.subgroupOf H).map H.subtype) = Nat.card ↥(B.subgroupOf H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBH] at h2
  rw [h2, Subgroup.card_map_of_injective H.subtype_injective]
  exact h1

/-- `E(Q)` is the same computed inside `H` or inside `G`. -/
theorem maxElemAb_map {H : Subgroup G} {S : Subgroup ↥H} {B : Subgroup G}
    (hB : B ∈ maxElemAb p (S.map H.subtype)) : B.subgroupOf H ∈ maxElemAb p S := by
  have hBH : B ≤ H := hB.1.trans (Subgroup.map_subtype_le S)
  refine ⟨?_, hB.2.1.comap_of_injective H.subtype_injective, fun C hC hCea => ?_⟩
  · rw [← Subgroup.comap_map_eq_self_of_injective H.subtype_injective S]
    exact Subgroup.comap_mono hB.1
  · have h1 : Nat.card ↥(C.map H.subtype) ≤ Nat.card ↥B :=
      hB.2.2 _ (Subgroup.map_mono hC) (hCea.map _)
    have h2 : Nat.card ↥(C.map H.subtype) = Nat.card ↥C :=
      Subgroup.card_map_of_injective H.subtype_injective
    have h3 : Nat.card ↥((B.subgroupOf H).map H.subtype) = Nat.card ↥(B.subgroupOf H) :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBH] at h3
    rw [← h2, ← h3]
    exact h1

/-- The Thompson subgroup is the same computed inside `H` or inside `G`. -/
theorem map_thompsonSubgroup {H : Subgroup G} (S : Subgroup ↥H) :
    (thompsonSubgroup p S).map H.subtype = thompsonSubgroup p (S.map H.subtype) := by
  refine le_antisymm ?_ ?_
  · rw [thompsonSubgroup, Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hA => le_thompsonSubgroup (mem_maxElemAb_map hA)
  · refine iSup₂_le fun B hB => ?_
    have hBH : B ≤ H := hB.1.trans (Subgroup.map_subtype_le S)
    have hmem : B.subgroupOf H ∈ maxElemAb p S := maxElemAb_map hB
    have h1 : B = (B.subgroupOf H).map H.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBH]
    rw [h1]
    exact Subgroup.map_mono (le_thompsonSubgroup hmem)

/-!
## The hypothesis of Theorem 7.1
-/

variable (p) in
/-- Isaacs' hypothesis for Theorem 7.1: `C(Z(S))` and `N(J(S))` have normal `p`-complements for
every Sylow `p`-subgroup `S`.  Isaacs states it for one Sylow `p`-subgroup; since Sylow
`p`-subgroups are conjugate the two forms agree (`thompsonHypothesis_of_sylow`). -/
def ThompsonHypothesis (X : Type u) [Group X] : Prop :=
  ∀ S : Sylow p X,
    HasNormalPComplement p
        ↥(Subgroup.centralizer ((centerOf (S : Subgroup X) : Subgroup X) : Set X)) ∧
    HasNormalPComplement p
        ↥(Subgroup.normalizer ((thompsonSubgroup p (S : Subgroup X) : Subgroup X) : Set X))

/-- If the theorem is known for a subgroup `H` that nevertheless has no normal `p`-complement,
then for some Sylow `p`-subgroup `S` of `H` one of `N_G(J(S))`, `C_G(Z(S))` has no normal
`p`-complement either. -/
theorem exists_bad_of_not_hasNormalPComplement [Finite G] [Fact p.Prime] {H : Subgroup G}
    (hH : ¬ HasNormalPComplement p ↥H)
    (hthm : ThompsonHypothesis p ↥H → HasNormalPComplement p ↥H) :
    ∃ S : Subgroup G, S ≤ H ∧ IsPGroup p ↥S ∧ ¬ p ∣ S.relIndex H ∧
      (¬ HasNormalPComplement p
          ↥(Subgroup.centralizer ((centerOf S : Subgroup G) : Set G)) ∨
        ¬ HasNormalPComplement p
          ↥(Subgroup.normalizer ((thompsonSubgroup p S : Subgroup G) : Set G))) := by
  have hnot : ¬ ThompsonHypothesis p ↥H := fun h => hH (hthm h)
  rw [ThompsonHypothesis, not_forall] at hnot
  obtain ⟨S', hS'⟩ := hnot
  refine ⟨(S' : Subgroup ↥H).map H.subtype, Subgroup.map_subtype_le _,
    S'.isPGroup'.map _, ?_, ?_⟩
  · have hsub : (((S' : Subgroup ↥H).map H.subtype).subgroupOf H) = (S' : Subgroup ↥H) :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [Subgroup.relIndex, hsub]
    exact S'.not_dvd_index
  · -- translate the two conditions from `H` to `G`
    have hcen : Subgroup.centralizer ((centerOf (S' : Subgroup ↥H) : Subgroup ↥H) : Set ↥H)
        = (Subgroup.centralizer
            ((centerOf ((S' : Subgroup ↥H).map H.subtype) : Subgroup G) : Set G)).subgroupOf H := by
      rw [← map_centerOf, centralizer_map_subtype]
    have hnor : Subgroup.normalizer ((thompsonSubgroup p (S' : Subgroup ↥H) : Subgroup ↥H) : Set ↥H)
        = (Subgroup.normalizer
            ((thompsonSubgroup p ((S' : Subgroup ↥H).map H.subtype) : Subgroup G) :
              Set G)).subgroupOf H := by
      rw [← map_thompsonSubgroup, normalizer_map_subtype]
    rw [not_and_or, hcen, hnor] at hS'
    rcases hS' with h | h
    · exact Or.inl fun hc => h (hasNormalPComplement_subgroupOf hc)
    · exact Or.inr fun hc => h (hasNormalPComplement_subgroupOf hc)

/-!
## The choice of `U`

Isaacs picks a nonidentity `p`-subgroup `U` whose normalizer has no normal `p`-complement —
Frobenius' Theorem 5.26 supplies one — with `|N_G(U)|_p` as large as possible and, subject to
that, `|U|` as large as possible.  The two conditions are packed into a single weight, since
`|U| ≤ |G| < |G| + 1`.
-/

variable (p) in
/-- The nonidentity `p`-subgroups whose normalizer has no normal `p`-complement. -/
def Bad (X : Type u) [Group X] : Set (Subgroup X) :=
  {U | U ≠ ⊥ ∧ IsPGroup p ↥U ∧
    ¬ HasNormalPComplement p ↥(Subgroup.normalizer ((U : Subgroup X) : Set X))}

variable (p) in
/-- `|N_G(U)|_p` first, then `|U|`, packed into one natural number. -/
noncomputable def badWeight (X : Type u) [Group X] [Finite X] (U : Subgroup X) : ℕ :=
  (Nat.card ↥(Subgroup.normalizer ((U : Subgroup X) : Set X))).factorization p *
      (Nat.card X + 1) + Nat.card ↥U

/-- **Frobenius' Theorem 5.26**: if `G` has no normal `p`-complement then some nonidentity
`p`-subgroup has a normalizer without one. -/
theorem bad_nonempty [Finite G] [Fact p.Prime] (hG : ¬ HasNormalPComplement p G) :
    (Bad p G).Nonempty := by
  by_contra hempty
  refine hG (hasNormalPComplement_of_normalizer fun Y hY hYp => ?_)
  by_contra hcon
  exact hempty ⟨Y, hY, hYp, hcon⟩

/-- Isaacs' choice of `U`. -/
theorem exists_bad_max [Finite G] [Fact p.Prime] (hG : ¬ HasNormalPComplement p G) :
    ∃ U ∈ Bad p G, ∀ V ∈ Bad p G, badWeight p G V ≤ badWeight p G U := by
  exact Set.exists_max_image (Bad p G) (badWeight p G) (Set.toFinite _) (bad_nonempty hG)

/-- The first half of the choice: `|N_G(V)|_p ≤ |N_G(U)|_p`. -/
theorem factorization_le_of_badWeight_le [Finite G] {U V : Subgroup G}
    (h : badWeight p G V ≤ badWeight p G U) :
    (Nat.card ↥(Subgroup.normalizer ((V : Subgroup G) : Set G))).factorization p
      ≤ (Nat.card ↥(Subgroup.normalizer ((U : Subgroup G) : Set G))).factorization p := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  have hUc : Nat.card ↥U ≤ Nat.card G := Subgroup.card_le_card_group _
  have hVc : Nat.card ↥V ≤ Nat.card G := Subgroup.card_le_card_group _
  have h2 : ((Nat.card ↥(Subgroup.normalizer ((U : Subgroup G) : Set G))).factorization p + 1) *
        (Nat.card G + 1)
      ≤ (Nat.card ↥(Subgroup.normalizer ((V : Subgroup G) : Set G))).factorization p *
        (Nat.card G + 1) := Nat.mul_le_mul_right _ hlt
  rw [add_mul, one_mul] at h2
  rw [badWeight, badWeight] at h
  omega

/-- The second half of the choice: when the `p`-parts agree, `|V| ≤ |U|`. -/
theorem card_le_of_badWeight_le [Finite G] {U V : Subgroup G}
    (h : badWeight p G V ≤ badWeight p G U)
    (heq : (Nat.card ↥(Subgroup.normalizer ((V : Subgroup G) : Set G))).factorization p
      = (Nat.card ↥(Subgroup.normalizer ((U : Subgroup G) : Set G))).factorization p) :
    Nat.card ↥V ≤ Nat.card ↥U := by
  rw [badWeight, badWeight, heq] at h
  omega

/-- The join of a `p`-subgroup normalized by `H` with a `p`-subgroup of `H` is a `p`-group. -/
theorem isPGroup_sup_of_le_normalizer {H U S : Subgroup G} (hUH : U ≤ H) (hSH : S ≤ H)
    (hHN : H ≤ Subgroup.normalizer (U : Set G)) (hUp : IsPGroup p ↥U) (hSp : IsPGroup p ↥S) :
    IsPGroup p ↥(U ⊔ S) := by
  have hnorm : (U.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mpr hHN
  have hjoin : IsPGroup p ↥(U.subgroupOf H ⊔ S.subgroupOf H) :=
    IsPGroup.to_sup_of_normal_left (hUp.of_equiv (Subgroup.subgroupOfEquivOfLe hUH).symm)
      (hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm)
  have hmap : (U.subgroupOf H ⊔ S.subgroupOf H).map H.subtype = U ⊔ S := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hUH, inf_eq_left.mpr hSH]
  exact hmap ▸ hjoin.map H.subtype

/-- A subgroup of a group with a normal `p`-complement has one. -/
theorem HasNormalPComplement.of_le {K L : Subgroup G} (h : HasNormalPComplement p ↥L)
    (hKL : K ≤ L) : HasNormalPComplement p ↥K :=
  (h.subgroup (K.subgroupOf L)).of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL)

/-- A nontrivial finite `p`-group has nontrivial centre. -/
theorem centerOf_ne_bot [Finite G] [Fact p.Prime] {S : Subgroup G} (hSp : IsPGroup p ↥S)
    (hS : S ≠ ⊥) : centerOf S ≠ ⊥ := by
  have hnt : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS
  have hcen : Nontrivial ↥(Subgroup.center ↥S) := hSp.center_nontrivial
  have heq : (centerOf S).subgroupOf S = Subgroup.center ↥S := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff]
    exact ⟨fun hx y => Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 (y : G) y.2),
      fun hx => ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        congrArg Subtype.val (hx ⟨y, hy⟩)⟩⟩
  intro hbot
  rw [hbot] at heq
  rw [Subgroup.bot_subgroupOf] at heq
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hcen heq.symm

/-- The exponent of `p` in `|S|` for a `p`-subgroup `S` of index prime to `p` in `H`. -/
theorem factorization_eq_of_not_dvd_relIndex [Finite G] [Fact p.Prime] {S H : Subgroup G}
    (hSH : S ≤ H) (hSi : ¬ p ∣ S.relIndex H) :
    (Nat.card ↥H).factorization p = (Nat.card ↥S).factorization p := by
  have hmul : S.relIndex H * Nat.card ↥S = Nat.card ↥H := by
    have h := relIndex_mul_card_inf S H
    rwa [inf_eq_left.mpr hSH] at h
  have h0 : S.relIndex H ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [← hmul, Nat.factorization_mul h0 Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hSi, zero_add]

/-!
## Step 1 of Isaacs' proof: `U = O_p(G)`
-/

/-- **Isaacs 7.1, Step 1.**  The chosen bad subgroup is `O_p(G)`.

If `N = N_G(U)` were proper, the theorem would hold for `N`, so some Sylow `p`-subgroup `S` of `N`
would have `N_G(J(S))` or `C_G(Z(S))` without a normal `p`-complement.  Taking `X` to be `J(S)` or
`Z(S)` accordingly, `X` is a bad subgroup; and `S` is not Sylow in `G` (else the hypothesis would
apply), so normalizers grow and `X` is normalized by a `p`-group strictly bigger than `S`.  That
makes `|N_G(X)|_p > |N_G(U)|_p`, against the choice of `U`.  Hence `U ⊴ G`, so `U ≤ O_p(G)`; and
`O_p(G)` is itself bad with the same `|N_G(-)|_p`, so `|O_p(G)| ≤ |U|`. -/
theorem thompson_step_one [Finite G] [Fact p.Prime]
    (IH : ∀ (Y : Type u) [Group Y] [Finite Y], Nat.card Y < Nat.card G →
      ThompsonHypothesis p Y → HasNormalPComplement p Y)
    (hyp : ThompsonHypothesis p G)
    {U : Subgroup G} (hU : U ∈ Bad p G)
    (hmax : ∀ V ∈ Bad p G, badWeight p G V ≤ badWeight p G U) :
    U = piCore ({p} : Set ℕ) G := by
  have hp : p.Prime := Fact.out
  obtain ⟨hUne, hUp, hNbad⟩ := hU
  have hUN : U ≤ Subgroup.normalizer ((U : Subgroup G) : Set G) := Subgroup.le_normalizer
  -- `N_G(U) = ⊤`
  have hNtop : Subgroup.normalizer ((U : Subgroup G) : Set G) = ⊤ := by
    by_contra hNne
    have hcardN : Nat.card ↥(Subgroup.normalizer ((U : Subgroup G) : Set G)) < Nat.card G := by
      calc Nat.card ↥(Subgroup.normalizer ((U : Subgroup G) : Set G))
          < Nat.card ↥(⊤ : Subgroup G) := card_lt_card_of_lt (lt_of_le_of_ne le_top hNne)
        _ = Nat.card G := Subgroup.card_top
    obtain ⟨S, hSN, hSp, hSi, hbad⟩ :=
      exists_bad_of_not_hasNormalPComplement hNbad (IH _ hcardN)
    -- `U ≤ S`
    have hUS : U ≤ S := by
      have hsupp : IsPGroup p ↥(U ⊔ S) := isPGroup_sup_of_le_normalizer hUN hSN le_rfl hUp hSp
      have heq : S = U ⊔ S :=
        eq_of_isPGroup_of_not_dvd_relIndex le_sup_right (sup_le hUN hSN) hsupp hSi
      exact heq ▸ le_sup_left
    have hSne : S ≠ ⊥ := fun hbot => hUne (le_bot_iff.mp (hbot ▸ hUS))
    -- `S` is not a Sylow `p`-subgroup of `G`
    have hSdvd : p ∣ S.index := by
      by_contra hnd
      have hSyl := hyp (hSp.toSylow hnd)
      rcases hbad with h | h
      · exact h hSyl.1
      · exact h hSyl.2
    -- normalizers grow: a `p`-group `T` with `S < T ≤ N_G(S)`
    obtain ⟨P', hSP'⟩ := hSp.exists_le_sylow
    have hSlt : S < (P' : Subgroup G) :=
      lt_of_le_of_ne hSP' fun h => P'.not_dvd_index (h ▸ hSdvd)
    have hTlt : S < (P' : Subgroup G) ⊓ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
      lt_inf_normalizer P'.isPGroup' hSlt
    -- the bad subgroup `X`, characteristic in `S`
    obtain ⟨X, hXS, hXchar, hXne, hXbad⟩ :
        ∃ X : Subgroup G, X ≤ S ∧ (X.subgroupOf S).Characteristic ∧ X ≠ ⊥ ∧
          ¬ HasNormalPComplement p
            ↥(Subgroup.normalizer ((X : Subgroup G) : Set G)) := by
      rcases hbad with h | h
      · exact ⟨centerOf S, centerOf_le S, centerOf_characteristic S, centerOf_ne_bot hSp hSne,
          fun hc => h (hc.of_le (Subgroup.centralizer_le_normalizer _))⟩
      · exact ⟨thompsonSubgroup p S, thompsonSubgroup_le p S, thompsonSubgroup_characteristic p S,
          thompsonSubgroup_ne_bot hp hSp hSne, h⟩
    have hXbadmem : X ∈ Bad p G := ⟨hXne, hSp.to_le hXS, hXbad⟩
    -- `T` normalizes `X`, so `|N_G(X)|_p` exceeds `|N_G(U)|_p`
    have hTX : (P' : Subgroup G) ⊓ Subgroup.normalizer ((S : Subgroup G) : Set G)
        ≤ Subgroup.normalizer ((X : Subgroup G) : Set G) :=
      le_normalizer_of_characteristic_subgroupOf hXS hXchar inf_le_right
    have hTp : IsPGroup p ↥((P' : Subgroup G) ⊓ Subgroup.normalizer ((S : Subgroup G) : Set G)) :=
      P'.isPGroup'.to_le inf_le_left
    obtain ⟨k, hk⟩ := hTp.exists_card_eq
    have hkle : k ≤ (Nat.card ↥(Subgroup.normalizer
        ((X : Subgroup G) : Set G))).factorization p := by
      refine (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp ?_
      rw [← hk]
      exact Subgroup.card_dvd_of_le hTX
    obtain ⟨j, hj⟩ := hSp.exists_card_eq
    have hjk : j < k := by
      have hlt : Nat.card ↥S < Nat.card ↥((P' : Subgroup G) ⊓
          Subgroup.normalizer ((S : Subgroup G) : Set G)) := card_lt_card_of_lt hTlt
      rw [hj, hk] at hlt
      exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
    have hjN : (Nat.card ↥(Subgroup.normalizer
        ((U : Subgroup G) : Set G))).factorization p = j := by
      rw [factorization_eq_of_not_dvd_relIndex hSN hSi, hj, Nat.Prime.factorization_pow hp]
      simp
    have hle := factorization_le_of_badWeight_le (hmax X hXbadmem)
    omega
  -- `U ≤ O_p(G)`, and `O_p(G)` is bad with the same `p`-part
  have hUnormal : U.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    exact hNtop
  have hUcore : U ≤ piCore ({p} : Set ℕ) G := le_piCore hUnormal (IsPGroup.isPiGroup hp hUp)
  have hCne : piCore ({p} : Set ℕ) G ≠ ⊥ := fun hbot => hUne (le_bot_iff.mp (hbot ▸ hUcore))
  have hCnorm : Subgroup.normalizer ((piCore ({p} : Set ℕ) G : Subgroup G) : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hCbad : piCore ({p} : Set ℕ) G ∈ Bad p G := by
    refine ⟨hCne, IsPiGroup.isPGroup (p := p) isPiGroup_piCore, ?_⟩
    rw [hCnorm, ← hNtop]
    exact hNbad
  have heqf : (Nat.card ↥(Subgroup.normalizer
        ((piCore ({p} : Set ℕ) G : Subgroup G) : Set G))).factorization p
      = (Nat.card ↥(Subgroup.normalizer ((U : Subgroup G) : Set G))).factorization p := by
    rw [hCnorm, hNtop]
  exact (Subgroup.eq_of_le_of_card_ge hUcore
    (card_le_of_badWeight_le (hmax _ hCbad) heqf)).symm ▸ rfl

/-!
## Transport along an automorphism

Isaacs states the hypothesis of 7.1 for one Sylow `p`-subgroup and remarks that it then holds for
all of them.  That is `thompsonHypothesis_of_sylow`, and it needs `Z(-)`, `J(-)`, centralizers,
normalizers and the property of having a normal `p`-complement to be carried along by an
automorphism.
-/

theorem centralizer_map_equiv (e : G ≃* G) (A : Subgroup G) :
    Subgroup.centralizer ((A.map e.toMonoidHom : Subgroup G) : Set G)
      = (Subgroup.centralizer (A : Set G)).map e.toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, SetLike.mem_coe,
    MulEquiv.coe_toMonoidHom]
  constructor
  · intro hx
    refine ⟨e.symm x, fun y hy => ?_, by simp⟩
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hx (e y) ⟨y, hy, rfl⟩
  · rintro ⟨w, hw, rfl⟩ y ⟨z, hz, rfl⟩
    simp only [← map_mul]
    exact congrArg e (hw z hz)

theorem normalizer_map_equiv (e : G ≃* G) (A : Subgroup G) :
    Subgroup.normalizer ((A.map e.toMonoidHom : Subgroup G) : Set G)
      = (Subgroup.normalizer (A : Set G)).map e.toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq A e).symm

theorem centerOf_map_equiv (e : G ≃* G) (A : Subgroup G) :
    centerOf (A.map e.toMonoidHom) = (centerOf A).map e.toMonoidHom := by
  rw [centerOf, centerOf, centralizer_map_equiv,
    Subgroup.map_inf A (Subgroup.centralizer (A : Set G)) e.toMonoidHom e.injective]

theorem mem_maxElemAb_map_equiv (e : G ≃* G) {Q A : Subgroup G} (hA : A ∈ maxElemAb p Q) :
    A.map e.toMonoidHom ∈ maxElemAb p (Q.map e.toMonoidHom) := by
  refine ⟨Subgroup.map_mono hA.1, hA.2.1.map _, fun B hB hBea => ?_⟩
  have hBmap : B.map e.symm.toMonoidHom ≤ Q := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨w, hw, rfl⟩ := hB hz
    simpa using hw
  have h1 : Nat.card ↥(B.map e.symm.toMonoidHom) ≤ Nat.card ↥A :=
    hA.2.2 _ hBmap (hBea.map _)
  rwa [Subgroup.card_map_of_injective e.symm.injective,
    ← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective (K := A)] at h1

theorem thompsonSubgroup_map_equiv (e : G ≃* G) (Q : Subgroup G) :
    thompsonSubgroup p (Q.map e.toMonoidHom) = (thompsonSubgroup p Q).map e.toMonoidHom := by
  refine le_antisymm (iSup₂_le fun B hB => ?_) ?_
  · have hcomp1 : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G :=
      MonoidHom.ext fun x => by simp
    have hcomp2 : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G :=
      MonoidHom.ext fun x => by simp
    have hmem : B.map e.symm.toMonoidHom ∈ maxElemAb p Q := by
      have h := mem_maxElemAb_map_equiv (p := p) e.symm hB
      rwa [Subgroup.map_map, hcomp1, Subgroup.map_id] at h
    have hBeq : B = (B.map e.symm.toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_map, hcomp2, Subgroup.map_id]
    rw [hBeq]
    exact Subgroup.map_mono (le_thompsonSubgroup hmem)
  · rw [thompsonSubgroup, Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hA => le_thompsonSubgroup (mem_maxElemAb_map_equiv e hA)

theorem HasNormalPComplement.map_equiv (e : G ≃* G) {A : Subgroup G}
    (h : HasNormalPComplement p ↥A) : HasNormalPComplement p ↥(A.map e.toMonoidHom) :=
  h.of_mulEquiv (Subgroup.equivMapOfInjective A e.toMonoidHom e.injective)

/-- Isaacs states the hypothesis of 7.1 for one Sylow `p`-subgroup; since Sylow `p`-subgroups are
conjugate, it then holds for all of them. -/
theorem thompsonHypothesis_of_sylow [Finite G] [Fact p.Prime] (P : Sylow p G)
    (hC : HasNormalPComplement p
      ↥(Subgroup.centralizer ((centerOf (P : Subgroup G) : Subgroup G) : Set G)))
    (hN : HasNormalPComplement p
      ↥(Subgroup.normalizer ((thompsonSubgroup p (P : Subgroup G) : Subgroup G) : Set G))) :
    ThompsonHypothesis p G := by
  intro S
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  have hSeq : (S : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]; rfl
  constructor
  · rw [hSeq, centerOf_map_equiv, centralizer_map_equiv]
    exact hC.map_equiv _
  · rw [hSeq, thompsonSubgroup_map_equiv, normalizer_map_equiv]
    exact hN.map_equiv _

/-!
## Correspondence
-/

/-- For `U ⊴ G` contained in `X`, membership in `X` may be tested in `G / U`. -/
theorem mem_map_mk'_iff {U X : Subgroup G} [U.Normal] (hUX : U ≤ X) (y : G) :
    (QuotientGroup.mk' U) y ∈ X.map (QuotientGroup.mk' U) ↔ y ∈ X := by
  refine ⟨fun h => ?_, fun h => Subgroup.mem_map_of_mem _ h⟩
  have h1 : y ∈ (X.map (QuotientGroup.mk' U)).comap (QuotientGroup.mk' U) := h
  rwa [Subgroup.comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])] at h1

/-- **Correspondence theorem for normalizers**: for `U ⊴ G` with `U ≤ X`,
`N_{G/U}(X/U) = N_G(X)/U`. -/
theorem normalizer_map_mk'_of_le {U X : Subgroup G} [U.Normal] (hUX : U ≤ X) :
    Subgroup.normalizer ((X.map (QuotientGroup.mk' U) : Subgroup (G ⧸ U)) : Set (G ⧸ U))
      = (Subgroup.normalizer (X : Set G)).map (QuotientGroup.mk' U) := by
  have hconj : ∀ y z : G, (QuotientGroup.mk' U) y * (QuotientGroup.mk' U) z *
      ((QuotientGroup.mk' U) y)⁻¹ = (QuotientGroup.mk' U) (y * z * y⁻¹) := by
    intro y z
    simp only [← map_inv, ← map_mul]
  ext g
  constructor
  · intro hg
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective U g
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_normalizer_iff.mpr fun z => ?_)
    have h1 := Subgroup.mem_normalizer_iff.mp hg ((QuotientGroup.mk' U) z)
    rwa [hconj, mem_map_mk'_iff hUX, mem_map_mk'_iff hUX] at h1
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_normalizer_iff.mpr fun z => ?_
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective U z
    rw [hconj, mem_map_mk'_iff hUX, mem_map_mk'_iff hUX]
    exact Subgroup.mem_normalizer_iff.mp hy w

/-- The comap form of the correspondence. -/
theorem normalizer_eq_comap_of_le {U X : Subgroup G} [U.Normal] (hUX : U ≤ X) :
    Subgroup.normalizer (X : Set G)
      = (Subgroup.normalizer ((X.map (QuotientGroup.mk' U) : Subgroup (G ⧸ U)) :
          Set (G ⧸ U))).comap (QuotientGroup.mk' U) := by
  rw [normalizer_map_mk'_of_le hUX, Subgroup.comap_map_eq_self
    (by rw [QuotientGroup.ker_mk']; exact hUX.trans Subgroup.le_normalizer)]

/-- The image of a group with a normal `p`-complement has one. -/
theorem HasNormalPComplement.map_mk' {A U : Subgroup G} [U.Normal]
    (h : HasNormalPComplement p ↥A) :
    HasNormalPComplement p ↥(A.map (QuotientGroup.mk' U)) := by
  set f : ↥A →* G ⧸ U := (QuotientGroup.mk' U).comp A.subtype with hf
  have hrange : f.range = A.map (QuotientGroup.mk' U) := by
    rw [hf, MonoidHom.range_comp, A.range_subtype]
  rw [← hrange]
  exact (h.quotient f.ker).of_mulEquiv (QuotientGroup.quotientKerEquivRange f)

/-!
## Step 2 of Isaacs' proof: `G / U` has a normal `p`-complement
-/

/-- A Sylow `p`-subgroup is nontrivial when `p` divides the order. -/
theorem sylow_ne_bot_of_dvd [Finite G] [Fact p.Prime] (S : Sylow p G) (hdvd : p ∣ Nat.card G) :
    (S : Subgroup G) ≠ ⊥ := by
  intro hb
  have hfac : 0 < (Nat.card G).factorization p :=
    Nat.Prime.factorization_pos_of_dvd Fact.out Nat.card_pos.ne' hdvd
  have h1 : Nat.card ↥(S : Subgroup G) = p ^ (Nat.card G).factorization p :=
    S.card_eq_multiplicity
  rw [hb, Subgroup.card_bot] at h1
  exact absurd h1.symm (Nat.one_lt_pow hfac.ne' (Fact.out : p.Prime).one_lt).ne'

/-- The key consequence of the choice of `U`: a `p`-subgroup `X` with `U < X ≤ P` normalized by
`P` is not bad, so `N_G(X)` has a normal `p`-complement. -/
theorem hasNormalPComplement_normalizer_of_lt [Finite G] [Fact p.Prime]
    {U : Subgroup G} (hU : U ∈ Bad p G)
    (hmax : ∀ V ∈ Bad p G, badWeight p G V ≤ badWeight p G U)
    (hNU : Subgroup.normalizer ((U : Subgroup G) : Set G) = ⊤)
    (P : Sylow p G) {X : Subgroup G} (hUX : U < X) (hXP : X ≤ (P : Subgroup G))
    (hPX : (P : Subgroup G) ≤ Subgroup.normalizer ((X : Subgroup G) : Set G)) :
    HasNormalPComplement p ↥(Subgroup.normalizer ((X : Subgroup G) : Set G)) := by
  by_contra hbad
  have hXne : X ≠ ⊥ := fun h => hU.1 (le_bot_iff.mp (h ▸ hUX.le))
  have hXbad : X ∈ Bad p G := ⟨hXne, P.isPGroup'.to_le hXP, hbad⟩
  have hfX : (Nat.card ↥(Subgroup.normalizer ((X : Subgroup G) : Set G))).factorization p
      = (Nat.card G).factorization p := by
    have h1 : ¬ p ∣ (P : Subgroup G).relIndex
        (Subgroup.normalizer ((X : Subgroup G) : Set G)) := fun h =>
      P.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hPX))
    have h2 : ¬ p ∣ (P : Subgroup G).relIndex ⊤ := by
      rw [Subgroup.relIndex_top_right]; exact P.not_dvd_index
    rw [factorization_eq_of_not_dvd_relIndex hPX h1,
      ← factorization_eq_of_not_dvd_relIndex (le_top : (P : Subgroup G) ≤ ⊤) h2,
      Subgroup.card_top]
  have hfU : (Nat.card ↥(Subgroup.normalizer ((U : Subgroup G) : Set G))).factorization p
      = (Nat.card G).factorization p := by rw [hNU, Subgroup.card_top]
  have hcard := card_le_of_badWeight_le (hmax X hXbad) (by rw [hfX, hfU])
  exact absurd (Subgroup.eq_of_le_of_card_ge hUX.le hcard) hUX.ne

/-- In `Ḡ = G/U`, the normalizer of a nontrivial subgroup of `P̄` normalized by `P̄` has a normal
`p`-complement. -/
theorem hasNormalPComplement_normalizer_quotient [Finite G] [Fact p.Prime]
    {U : Subgroup G} [U.Normal] (hU : U ∈ Bad p G)
    (hmax : ∀ V ∈ Bad p G, badWeight p G V ≤ badWeight p G U)
    (hNU : Subgroup.normalizer ((U : Subgroup G) : Set G) = ⊤)
    (P : Sylow p G) (hUP : U ≤ (P : Subgroup G))
    {Y : Subgroup (G ⧸ U)} (hYP : Y ≤ (P : Subgroup G).map (QuotientGroup.mk' U))
    (hYne : Y ≠ ⊥)
    (hYnorm : (P : Subgroup G).map (QuotientGroup.mk' U)
      ≤ Subgroup.normalizer ((Y : Subgroup (G ⧸ U)) : Set (G ⧸ U))) :
    HasNormalPComplement p ↥(Subgroup.normalizer ((Y : Subgroup (G ⧸ U)) : Set (G ⧸ U))) := by
  set X : Subgroup G := Y.comap (QuotientGroup.mk' U) with hX
  have hUX : U ≤ X := by
    intro u hu
    have h1 : (QuotientGroup.mk' U) u = 1 := (QuotientGroup.eq_one_iff u).mpr hu
    rw [hX, Subgroup.mem_comap, h1]
    exact one_mem _
  have hmapX : X.map (QuotientGroup.mk' U) = Y :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective U) Y
  have hmapU : U.map (QuotientGroup.mk' U) = ⊥ := by
    rw [eq_bot_iff]
    rintro - ⟨u, hu, rfl⟩
    exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff u).mpr hu)
  have hXP : X ≤ (P : Subgroup G) := by
    have h1 : ((P : Subgroup G).map (QuotientGroup.mk' U)).comap (QuotientGroup.mk' U)
        = (P : Subgroup G) :=
      Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hUP)
    rw [← h1]
    exact Subgroup.comap_mono hYP
  have hUltX : U < X := lt_of_le_of_ne hUX fun h => hYne (by rw [← hmapX, ← h, hmapU])
  have hPX : (P : Subgroup G) ≤ Subgroup.normalizer ((X : Subgroup G) : Set G) := by
    rw [normalizer_eq_comap_of_le hUX, hmapX]
    exact fun g hg => Subgroup.mem_comap.mpr (hYnorm (Subgroup.mem_map_of_mem _ hg))
  have hres := hasNormalPComplement_normalizer_of_lt hU hmax hNU P hUltX hXP hPX
  rw [← hmapX, normalizer_map_mk'_of_le hUX]
  exact hres.map_mk'

/-- **Isaacs 7.1, Step 2.**  `G / U` has a normal `p`-complement.

`|G/U| < |G|`, so the theorem holds there, and it is enough to check the hypothesis for the Sylow
`p`-subgroup `P̄`.  The preimage `X` of `J(P̄)` or `Z(P̄)` satisfies `U < X ≤ P` with `P ≤ N_G(X)`,
so `N_G(X)` has a normal `p`-complement by the choice of `U`; and `N_Ḡ(X̄) = N_G(X)‾`. -/
theorem thompson_step_two [Finite G] [Fact p.Prime]
    (IH : ∀ (Y : Type u) [Group Y] [Finite Y], Nat.card Y < Nat.card G →
      ThompsonHypothesis p Y → HasNormalPComplement p Y)
    {U : Subgroup G} [U.Normal] (hU : U ∈ Bad p G)
    (hmax : ∀ V ∈ Bad p G, badWeight p G V ≤ badWeight p G U)
    (hNU : Subgroup.normalizer ((U : Subgroup G) : Set G) = ⊤)
    (P : Sylow p G) (hUP : U ≤ (P : Subgroup G)) :
    HasNormalPComplement p (G ⧸ U) := by
  have hp : p.Prime := Fact.out
  have hsurj : Function.Surjective (QuotientGroup.mk' U) := QuotientGroup.mk'_surjective U
  have hlt : Nat.card (G ⧸ U) < Nat.card G := by
    have hmul := Subgroup.card_mul_index U
    have h1 : 1 < Nat.card ↥U := (Subgroup.one_lt_card_iff_ne_bot U).mpr hU.1
    have hpos : 0 < U.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [← Subgroup.index_eq_card, ← hmul]
    calc U.index = 1 * U.index := (one_mul _).symm
      _ < Nat.card ↥U * U.index := (Nat.mul_lt_mul_right hpos).mpr h1
  by_cases hdvd : p ∣ Nat.card (G ⧸ U)
  · have hPbar : ((P.mapSurjective hsurj : Sylow p (G ⧸ U)) : Subgroup (G ⧸ U)) ≠ ⊥ :=
      sylow_ne_bot_of_dvd _ hdvd
    have hPcoe : ((P.mapSurjective hsurj : Sylow p (G ⧸ U)) : Subgroup (G ⧸ U))
        = (P : Subgroup G).map (QuotientGroup.mk' U) := rfl
    refine IH (G ⧸ U) hlt (thompsonHypothesis_of_sylow (P.mapSurjective hsurj) ?_ ?_)
    · refine HasNormalPComplement.of_le ?_ (Subgroup.centralizer_le_normalizer _)
      refine hasNormalPComplement_normalizer_quotient hU hmax hNU P hUP
        (hPcoe ▸ centerOf_le _)
        (centerOf_ne_bot (P.mapSurjective hsurj).isPGroup' hPbar) ?_
      rw [← hPcoe]
      exact le_normalizer_of_characteristic_subgroupOf (centerOf_le _)
        (centerOf_characteristic _) Subgroup.le_normalizer
    · refine hasNormalPComplement_normalizer_quotient hU hmax hNU P hUP
        (hPcoe ▸ thompsonSubgroup_le p _)
        (thompsonSubgroup_ne_bot hp (P.mapSurjective hsurj).isPGroup' hPbar) ?_
      rw [← hPcoe]
      exact le_normalizer_of_characteristic_subgroupOf (thompsonSubgroup_le p _)
        (thompsonSubgroup_characteristic p _) Subgroup.le_normalizer
  · exact hasNormalPComplement_of_not_dvd hdvd

/-!
## Isaacs' Lemma 7.7

For `N ⊴ G` of order prime to `p` and a `p`-subgroup `P`, `N_Ḡ(P̄) = N_G(P)‾` and
`C_Ḡ(P̄) = C_G(P)‾`.  Part (a) is Isaacs' Lemma 2.17; `Isaacs/PLocalSubgroups.lean` proves it
from conjugacy of complements, hence under the `SchurZassenhausConjugacy` hypothesis.  Isaacs
instead uses the Frattini argument — `P ∈ Syl_p(P N)`, so a conjugate of `P` inside `P N` is
already `P N`-conjugate to it — and that needs only Sylow's theorem, which is why the version
here is hypothesis-free.
-/

/-- `P` is a Sylow `p`-subgroup of `P N` when `N ⊴ G` has order prime to `p`. -/
theorem not_dvd_relIndex_sup [Finite G] [Fact p.Prime] {N Q : Subgroup G} [N.Normal]
    (hN : ¬ p ∣ Nat.card ↥N) (hQ : IsPGroup p ↥Q) : ¬ p ∣ Q.relIndex (Q ⊔ N) := by
  have hp : p.Prime := Fact.out
  have hdisj : Q ⊓ N = ⊥ :=
    disjoint_iff.mp (disjoint_of_isPiGroup (IsPGroup.isPiGroup hp hQ)
      (isPiGroup_compl_of_not_dvd hN))
  -- `|Q N| = |Q| |N|`
  have e1 : N.relIndex Q * Nat.card ↥(N ⊓ Q) = Nat.card ↥Q := relIndex_mul_card_inf N Q
  rw [inf_comm N Q, hdisj, Subgroup.card_bot, mul_one] at e1
  have e2 : N.relIndex (Q ⊔ N) * Nat.card ↥(N ⊓ (Q ⊔ N)) = Nat.card ↥(Q ⊔ N) :=
    relIndex_mul_card_inf N (Q ⊔ N)
  rw [inf_eq_left.mpr (le_sup_right : N ≤ Q ⊔ N), Subgroup.relIndex_sup_right Q N, e1] at e2
  have e3 : Q.relIndex (Q ⊔ N) * Nat.card ↥(Q ⊓ (Q ⊔ N)) = Nat.card ↥(Q ⊔ N) :=
    relIndex_mul_card_inf Q (Q ⊔ N)
  rw [inf_eq_left.mpr (le_sup_left : Q ≤ Q ⊔ N), ← e2] at e3
  have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
  have heq : Q.relIndex (Q ⊔ N) = Nat.card ↥N := by
    refine Nat.eq_of_mul_eq_mul_left hQpos ?_
    calc Nat.card ↥Q * Q.relIndex (Q ⊔ N) = Q.relIndex (Q ⊔ N) * Nat.card ↥Q := by ring
      _ = Nat.card ↥Q * Nat.card ↥N := e3
  rw [heq]
  exact hN

/-- **The Frattini step of Isaacs' Lemma 7.7(a)**: `N_G(P N) ≤ N_G(P) N`. -/
theorem normalizer_sup_le_of_not_dvd [Finite G] [Fact p.Prime] {N : Subgroup G} [N.Normal]
    (hN : ¬ p ∣ Nat.card ↥N) {P : Subgroup G} (hP : IsPGroup p ↥P) :
    Subgroup.normalizer ((P ⊔ N : Subgroup G) : Set G)
      ≤ Subgroup.normalizer (P : Set G) ⊔ N := by
  intro g hg
  have hNc : N.map (MulAut.conj g).toMonoidHom = N := Subgroup.Normal.conj_smul_eq_self g N
  have hΓ : (P ⊔ N).map (MulAut.conj g).toMonoidHom = P ⊔ N := map_conj_eq_self_iff.mpr hg
  have hPgp : IsPGroup p ↥(P.map (MulAut.conj g).toMonoidHom) := hP.map _
  have hsupg : P.map (MulAut.conj g).toMonoidHom ⊔ N = P ⊔ N := by
    conv_lhs => rw [← hNc]
    rw [← Subgroup.map_sup, hΓ]
  have hPle : P ≤ P ⊔ N := le_sup_left
  have hPgle : P.map (MulAut.conj g).toMonoidHom ≤ P ⊔ N := hsupg ▸ le_sup_left
  have hi1 : ¬ p ∣ (P.subgroupOf (P ⊔ N)).index := not_dvd_relIndex_sup hN hP
  have hi2 : ¬ p ∣ ((P.map (MulAut.conj g).toMonoidHom).subgroupOf (P ⊔ N)).index := by
    have h := not_dvd_relIndex_sup (Q := P.map (MulAut.conj g).toMonoidHom) hN hPgp
    rwa [hsupg] at h
  obtain ⟨n, hn, hPn⟩ := exists_conj_of_sylow_le hPle hPgle hP hPgp hi1 hi2
  -- `n⁻¹ g` normalizes `P`
  have hcomp : ∀ a b : G, (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom
      = (MulAut.conj (a * b)).toMonoidHom :=
    fun a b => MonoidHom.ext fun w => by simp [MulAut.conj_apply, mul_assoc]
  have hkey : P.map (MulAut.conj (n⁻¹ * g)).toMonoidHom = P := by
    have h1 := congrArg (Subgroup.map (MulAut.conj n⁻¹).toMonoidHom) hPn
    rw [Subgroup.map_map, Subgroup.map_map, hcomp, hcomp, inv_mul_cancel,
      show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G from
        MonoidHom.ext fun w => by simp, Subgroup.map_id] at h1
    exact h1
  have hmem : n⁻¹ * g ∈ Subgroup.normalizer (P : Set G) := map_conj_eq_self_iff.mp hkey
  have hg' : g = n * (n⁻¹ * g) := by group
  rw [hg']
  exact mul_mem (sup_le_sup_right (Subgroup.le_normalizer : P ≤ _) N hn)
    (Subgroup.mem_sup_left hmem)

/-- **Isaacs, Lemma 7.7(a)**: `N_Ḡ(P̄) = N_G(P)‾` modulo a normal `p'`-subgroup. -/
theorem normalizer_map_mk'_eq_of_not_dvd [Finite G] [Fact p.Prime] {N : Subgroup G} [N.Normal]
    (hN : ¬ p ∣ Nat.card ↥N) {P : Subgroup G} (hP : IsPGroup p ↥P) :
    Subgroup.normalizer ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = (Subgroup.normalizer (P : Set G)).map (QuotientGroup.mk' N) := by
  have hmapN : N.map (QuotientGroup.mk' N) = ⊥ := by
    rw [eq_bot_iff]
    rintro - ⟨u, hu, rfl⟩
    exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff u).mpr hu)
  have hPsup : (P ⊔ N).map (QuotientGroup.mk' N) = P.map (QuotientGroup.mk' N) := by
    rw [Subgroup.map_sup, hmapN, sup_bot_eq]
  refine le_antisymm ?_ (Subgroup.le_normalizer_map _)
  rw [← hPsup, normalizer_map_mk'_of_le (le_sup_right : N ≤ P ⊔ N)]
  refine (Subgroup.map_mono (normalizer_sup_le_of_not_dvd hN hP)).trans ?_
  rw [Subgroup.map_sup, hmapN, sup_bot_eq]

/-- **Isaacs, Lemma 7.7(b)**: `C_Ḡ(P̄) ≤ C_G(P)‾` modulo a normal `p'`-subgroup. -/
theorem centralizer_map_mk'_le_of_not_dvd [Finite G] [Fact p.Prime] {N : Subgroup G} [N.Normal]
    (hN : ¬ p ∣ Nat.card ↥N) {P : Subgroup G} (hP : IsPGroup p ↥P) :
    Subgroup.centralizer ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      ≤ (Subgroup.centralizer (P : Set G)).map (QuotientGroup.mk' N) := by
  have hp : p.Prime := Fact.out
  have hdisj : P ⊓ N = ⊥ :=
    disjoint_iff.mp (disjoint_of_isPiGroup (IsPGroup.isPiGroup hp hP)
      (isPiGroup_compl_of_not_dvd hN))
  intro y hy
  have hyN : y ∈ Subgroup.normalizer
      ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
    Subgroup.centralizer_le_normalizer _ hy
  rw [normalizer_map_mk'_eq_of_not_dvd hN hP] at hyN
  obtain ⟨x, hxN, rfl⟩ := hyN
  refine Subgroup.mem_map_of_mem _ (Subgroup.mem_centralizer_iff.mpr fun z hz => ?_)
  have hzP : z ∈ P := hz
  -- the commutator lies in `P`, because `x` normalizes `P`
  have h1 : x * z * x⁻¹ * z⁻¹ ∈ P :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp hxN z).mp hzP) (inv_mem hzP)
  -- and in `N`, because `x̄` centralizes `P̄`
  have h2 : x * z * x⁻¹ * z⁻¹ ∈ N := by
    have hcomm : (QuotientGroup.mk' N) z * (QuotientGroup.mk' N) x
        = (QuotientGroup.mk' N) x * (QuotientGroup.mk' N) z :=
      Subgroup.mem_centralizer_iff.mp hy _ (Subgroup.mem_map_of_mem _ hzP)
    have h3 : (QuotientGroup.mk' N) (x * z * x⁻¹ * z⁻¹) = 1 := by
      simp only [map_mul, map_inv, ← hcomm]
      group
    exact (QuotientGroup.eq_one_iff _).mp h3
  have h4 : x * z * x⁻¹ * z⁻¹ = 1 := by
    have := Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rwa [hdisj, Subgroup.mem_bot] at this
  have h5 : x * z * x⁻¹ = z := mul_inv_eq_one.mp h4
  calc z * x = (x * z * x⁻¹) * x := by rw [h5]
    _ = x * z := by group

/-!
## `E(Q)` and `J(Q)` along an injective homomorphism

Step 3 needs `J(P)‾ = J(P̄)` for the canonical map modulo a `p'`-subgroup, which is injective on
`P`.  The general statement subsumes the inclusion of a subgroup and an automorphism.
-/

theorem map_le_range' {H : Type u} [Group H] (φ : G →* H) (S : Subgroup G) : S.map φ ≤ φ.range := by
  rintro - ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

theorem comap_le_of_map_le {H : Type u} [Group H] {φ : G →* H} (hφ : Function.Injective φ)
    {S : Subgroup G} {B : Subgroup H} (hB : B ≤ S.map φ) : B.comap φ ≤ S := by
  have h := Subgroup.comap_mono (f := φ) hB
  rwa [Subgroup.comap_map_eq_self (by rw [(MonoidHom.ker_eq_bot_iff φ).mpr hφ]; exact bot_le)] at h

/-- `E(S)` is carried into `E(S.map φ)` by an injective `φ`. -/
theorem mem_maxElemAb_map_injective {H : Type u} [Group H] {φ : G →* H}
    (hφ : Function.Injective φ) {S A : Subgroup G} (hA : A ∈ maxElemAb p S) :
    A.map φ ∈ maxElemAb p (S.map φ) := by
  refine ⟨Subgroup.map_mono hA.1, hA.2.1.map _, fun B hB hBea => ?_⟩
  have hBeq : (B.comap φ).map φ = B :=
    Subgroup.map_comap_eq_self (hB.trans (map_le_range' φ S))
  have h1 : Nat.card ↥(B.comap φ) ≤ Nat.card ↥A :=
    hA.2.2 _ (comap_le_of_map_le hφ hB) (hBea.comap_of_injective hφ)
  have hcardA : Nat.card ↥(A.map φ) = Nat.card ↥A := Subgroup.card_map_of_injective hφ
  have hcardB : Nat.card ↥B = Nat.card ↥(B.comap φ) := by
    conv_lhs => rw [← hBeq]
    exact Subgroup.card_map_of_injective hφ
  rw [hcardA, hcardB]
  exact h1

/-- Conversely, `E(S.map φ)` comes from `E(S)`. -/
theorem comap_mem_maxElemAb_of_map {H : Type u} [Group H] {φ : G →* H}
    (hφ : Function.Injective φ) {S : Subgroup G} {B : Subgroup H}
    (hB : B ∈ maxElemAb p (S.map φ)) : B.comap φ ∈ maxElemAb p S := by
  refine ⟨comap_le_of_map_le hφ hB.1, hB.2.1.comap_of_injective hφ, fun C hC hCea => ?_⟩
  have hBeq : (B.comap φ).map φ = B :=
    Subgroup.map_comap_eq_self (hB.1.trans (map_le_range' φ S))
  have h1 : Nat.card ↥(C.map φ) ≤ Nat.card ↥B :=
    hB.2.2 _ (Subgroup.map_mono hC) (hCea.map _)
  have hcardC : Nat.card ↥(C.map φ) = Nat.card ↥C := Subgroup.card_map_of_injective hφ
  have hcardB : Nat.card ↥B = Nat.card ↥(B.comap φ) := by
    conv_lhs => rw [← hBeq]
    exact Subgroup.card_map_of_injective hφ
  rw [hcardC, hcardB] at h1
  exact h1

/-- **`J(-)` commutes with an injective homomorphism.** -/
theorem thompsonSubgroup_map_injective {H : Type u} [Group H] {φ : G →* H}
    (hφ : Function.Injective φ) (S : Subgroup G) :
    thompsonSubgroup p (S.map φ) = (thompsonSubgroup p S).map φ := by
  refine le_antisymm (iSup₂_le fun B hB => ?_) ?_
  · have hBeq : (B.comap φ).map φ = B :=
      Subgroup.map_comap_eq_self (hB.1.trans (map_le_range' φ S))
    rw [← hBeq]
    exact Subgroup.map_mono (le_thompsonSubgroup (comap_mem_maxElemAb_of_map hφ hB))
  · rw [thompsonSubgroup, Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hA => le_thompsonSubgroup (mem_maxElemAb_map_injective hφ hA)

/-- `Z(-)` commutes with an injective homomorphism onto its image. -/
theorem centerOf_map_injective {H : Type u} [Group H] {φ : G →* H}
    (hφ : Function.Injective φ) (S : Subgroup G) :
    centerOf (S.map φ) ⊓ φ.range = (centerOf S).map φ := by
  refine le_antisymm ?_ (le_inf ?_ (map_le_range' φ _))
  · rintro x ⟨⟨hx1, hx2⟩, y, rfl⟩
    obtain ⟨z, hzS, hzy⟩ := hx1
    have hzy' : z = y := hφ hzy
    subst hzy'
    refine Subgroup.mem_map_of_mem _ ⟨hzS, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    exact hφ (by
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.mp hx2 (φ w) (Subgroup.mem_map_of_mem _ hw))
  · rintro - ⟨y, ⟨hy1, hy2⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem _ hy1, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro - ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subgroup.mem_centralizer_iff.mp hy2 w hw)

/-- `J(Q)` computed inside `Q` itself. -/
theorem thompsonSubgroup_top_subgroupOf (Q : Subgroup G) :
    thompsonSubgroup p (⊤ : Subgroup ↥Q) = (thompsonSubgroup p Q).subgroupOf Q := by
  refine Subgroup.map_injective Q.subtype_injective ?_
  rw [map_thompsonSubgroup, ← MonoidHom.range_eq_map, Q.range_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (thompsonSubgroup_le p Q)]

/-- `Z(Q)` computed inside `Q` itself. -/
theorem centerOf_top_subgroupOf (Q : Subgroup G) :
    centerOf (⊤ : Subgroup ↥Q) = (centerOf Q).subgroupOf Q := by
  refine Subgroup.map_injective Q.subtype_injective ?_
  rw [map_centerOf, ← MonoidHom.range_eq_map, Q.range_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (centerOf_le Q)]

/-- A homomorphism injective on `Q` restricts to an injective homomorphism from `↥Q`. -/
theorem injective_comp_subtype {H : Type u} [Group H] {φ : G →* H} {Q : Subgroup G}
    (hker : Q ⊓ φ.ker = ⊥) : Function.Injective (φ.comp Q.subtype) := by
  refine (MonoidHom.ker_eq_bot_iff _).mp ?_
  rw [eq_bot_iff]
  intro x hx
  have h1 : (x : G) ∈ Q ⊓ φ.ker := ⟨x.2, hx⟩
  rw [hker, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.mpr (Subtype.ext h1)

/-- **`J(-)` commutes with a homomorphism injective on `Q`.** -/
theorem thompsonSubgroup_map_of_inf_ker {H : Type u} [Group H] {φ : G →* H} {Q : Subgroup G}
    (hker : Q ⊓ φ.ker = ⊥) :
    thompsonSubgroup p (Q.map φ) = (thompsonSubgroup p Q).map φ := by
  have hψ := injective_comp_subtype hker
  have hQmap : Q.map φ = (⊤ : Subgroup ↥Q).map (φ.comp Q.subtype) := by
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Q.range_subtype]
  rw [hQmap, thompsonSubgroup_map_injective hψ, thompsonSubgroup_top_subgroupOf,
    ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (thompsonSubgroup_le p Q)]

/-- **`Z(-)` commutes with a homomorphism injective on `Q`.** -/
theorem centerOf_map_of_inf_ker {H : Type u} [Group H] {φ : G →* H} {Q : Subgroup G}
    (hker : Q ⊓ φ.ker = ⊥) : centerOf (Q.map φ) = (centerOf Q).map φ := by
  have hψ := injective_comp_subtype hker
  have hQmap : Q.map φ = (⊤ : Subgroup ↥Q).map (φ.comp Q.subtype) := by
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Q.range_subtype]
  have hrange : (φ.comp Q.subtype).range = Q.map φ := by
    rw [MonoidHom.range_comp, Q.range_subtype]
  have hcen := centerOf_map_injective hψ (⊤ : Subgroup ↥Q)
  rw [← hQmap, hrange, inf_eq_left.mpr (centerOf_le _)] at hcen
  rw [hcen, centerOf_top_subgroupOf, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (centerOf_le Q)]

/-!
## Step 3 of Isaacs' proof: `O_p'(G) = 1`
-/

/-- **Isaacs 7.1, Step 3.**  `O_p'(G) = 1`.

Modulo `K = O_p'(G)` the map is injective on `P`, so `J(P̄) = J(P)‾` and `Z(P̄) = Z(P)‾`; Lemma
7.7 then identifies `N_Ḡ(J(P̄))` and `C_Ḡ(Z(P̄))` with images of groups that have normal
`p`-complements.  So `Ḡ` would have one if it were smaller than `G` — but then so would `G`. -/
theorem thompson_step_three [Finite G] [Fact p.Prime]
    (IH : ∀ (Y : Type u) [Group Y] [Finite Y], Nat.card Y < Nat.card G →
      ThompsonHypothesis p Y → HasNormalPComplement p Y)
    (hyp : ThompsonHypothesis p G) (hG : ¬ HasNormalPComplement p G) (P : Sylow p G) :
    piCore ({p}ᶜ : Set ℕ) G = ⊥ := by
  have hp : p.Prime := Fact.out
  set K : Subgroup G := piCore ({p}ᶜ : Set ℕ) G with hK
  have hKp' : ¬ p ∣ Nat.card ↥K := not_dvd_card_piCore_compl
  have hkerK : (QuotientGroup.mk' K).ker = K := QuotientGroup.ker_mk' K
  by_contra hKne
  -- `|G / K| < |G|`
  have hlt : Nat.card (G ⧸ K) < Nat.card G := by
    have hmul := Subgroup.card_mul_index K
    have h1 : 1 < Nat.card ↥K := (Subgroup.one_lt_card_iff_ne_bot K).mpr hKne
    have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [← Subgroup.index_eq_card, ← hmul]
    calc K.index = 1 * K.index := (one_mul _).symm
      _ < Nat.card ↥K * K.index := (Nat.mul_lt_mul_right hpos).mpr h1
  -- `mk' K` is injective on any `p`-subgroup
  have hinf : ∀ Q : Subgroup G, IsPGroup p ↥Q → Q ⊓ (QuotientGroup.mk' K).ker = ⊥ := by
    intro Q hQ
    rw [hkerK]
    exact disjoint_iff.mp (disjoint_of_isPiGroup (IsPGroup.isPiGroup hp hQ)
      (isPiGroup_compl_of_not_dvd hKp'))
  have hsurj : Function.Surjective (QuotientGroup.mk' K) := QuotientGroup.mk'_surjective K
  have hPcoe : ((P.mapSurjective hsurj : Sylow p (G ⧸ K)) : Subgroup (G ⧸ K))
      = (P : Subgroup G).map (QuotientGroup.mk' K) := rfl
  -- the hypothesis passes to `Ḡ`
  have hhyp : ThompsonHypothesis p (G ⧸ K) := by
    refine thompsonHypothesis_of_sylow (P.mapSurjective hsurj) ?_ ?_
    · rw [hPcoe, centerOf_map_of_inf_ker (hinf _ P.isPGroup')]
      refine HasNormalPComplement.of_le ?_
        (centralizer_map_mk'_le_of_not_dvd hKp'
          (P.isPGroup'.to_le (centerOf_le (P : Subgroup G))))
      exact (hyp P).1.map_mk'
    · rw [hPcoe, thompsonSubgroup_map_of_inf_ker (hinf _ P.isPGroup'),
        normalizer_map_mk'_eq_of_not_dvd hKp'
          (P.isPGroup'.to_le (thompsonSubgroup_le p (P : Subgroup G)))]
      exact (hyp P).2.map_mk'
  -- so `Ḡ` has a normal `p`-complement, and then so does `G`
  have hquot : HasNormalPComplement p (G ⧸ K) := IH (G ⧸ K) hlt hhyp
  refine hG (hasNormalPComplement_iff.mpr ?_)
  have h1 : IsPGroup p ((G ⧸ K) ⧸ piCore ({p}ᶜ : Set ℕ) (G ⧸ K)) :=
    hasNormalPComplement_iff.mp hquot
  have h2 : IsPGroup p ((G ⧸ K) ⧸ (⊥ : Subgroup (G ⧸ K))) :=
    h1.of_equiv (QuotientGroup.quotientMulEquivOfEq piCore_quotient_piCore_eq_bot)
  exact h2.of_equiv (QuotientGroup.quotientBot (G := G ⧸ K))

/-!
## Steps 4 and 5 of Isaacs' proof
-/

/-- `J(-)` computed inside a subgroup containing `P`. -/
theorem thompsonSubgroup_subgroupOf {H P : Subgroup G} (hPH : P ≤ H) :
    thompsonSubgroup p (P.subgroupOf H) = (thompsonSubgroup p P).subgroupOf H := by
  refine Subgroup.map_injective H.subtype_injective ?_
  rw [map_thompsonSubgroup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hPH, inf_eq_left.mpr ((thompsonSubgroup_le p P).trans hPH)]

/-- The hypothesis of 7.1 passes to a subgroup containing a Sylow `p`-subgroup. -/
theorem ThompsonHypothesis.subgroup_of_le [Finite G] [Fact p.Prime] (hyp : ThompsonHypothesis p G)
    (P : Sylow p G) {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H) :
    ThompsonHypothesis p ↥H := by
  refine thompsonHypothesis_of_sylow (P.subtype hPH) ?_ ?_
  · have hcoe : ((P.subtype hPH : Sylow p ↥H) : Subgroup ↥H) = (P : Subgroup G).subgroupOf H := rfl
    rw [hcoe, centerOf_subgroupOf hPH, ← centralizer_map_subtype,
      Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr ((centerOf_le (P : Subgroup G)).trans hPH)]
    exact hasNormalPComplement_subgroupOf (hyp P).1
  · have hcoe : ((P.subtype hPH : Sylow p ↥H) : Subgroup ↥H) = (P : Subgroup G).subgroupOf H := rfl
    rw [hcoe, thompsonSubgroup_subgroupOf hPH, ← normalizer_map_subtype,
      Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr ((thompsonSubgroup_le p (P : Subgroup G)).trans hPH)]
    exact hasNormalPComplement_subgroupOf (hyp P).2

/-- **Isaacs 7.1, Step 4.**  `P` is a maximal subgroup of `G`.

A proper `H ⊇ P` inherits the hypothesis, so by induction it has a normal `p`-complement `K`.
Both `K` and `O_p(G)` are normalized by `H` and meet trivially, so `K` centralizes `O_p(G)`; by
Hall–Higman `K ≤ O_p(G)`, whence `K = 1` and `H` is a `p`-group. -/
theorem thompson_step_four [Finite G] [Fact p.Prime]
    (IH : ∀ (Y : Type u) [Group Y] [Finite Y], Nat.card Y < Nat.card G →
      ThompsonHypothesis p Y → HasNormalPComplement p Y)
    (hyp : ThompsonHypothesis p G) (hsolv : IsPiSeparable ({p} : Set ℕ) G)
    (hcore : piCore ({p}ᶜ : Set ℕ) G = ⊥) (P : Sylow p G) {H : Subgroup G}
    (hPH : (P : Subgroup G) ≤ H) (hHne : H ≠ ⊤) : H = (P : Subgroup G) := by
  have hp : p.Prime := Fact.out
  have hcardH : Nat.card ↥H < Nat.card G := by
    calc Nat.card ↥H < Nat.card ↥(⊤ : Subgroup G) := card_lt_card_of_lt (lt_of_le_of_ne le_top hHne)
      _ = Nat.card G := Subgroup.card_top
  obtain ⟨K, hKnormal, hKcard, hKquot⟩ :=
    IH ↥H hcardH (hyp.subgroup_of_le P hPH)
  have := hKnormal
  -- push `K` into `G`
  set K' : Subgroup G := K.map H.subtype with hK'
  have hK'H : K' ≤ H := Subgroup.map_subtype_le _
  have hK'card : ¬ p ∣ Nat.card ↥K' := by
    rwa [hK', Subgroup.card_map_of_injective H.subtype_injective]
  have hK'conj : ∀ h ∈ H, ∀ k ∈ K', h * k * h⁻¹ ∈ K' := by
    rintro h hh - ⟨k, hk, rfl⟩
    exact ⟨⟨h, hh⟩ * k * ⟨h, hh⟩⁻¹, hKnormal.conj_mem k hk ⟨h, hh⟩, rfl⟩
  -- `O_p(G)` is normalized by `H` and meets `K'` trivially
  set U : Subgroup G := piCore ({p} : Set ℕ) G with hU
  have hUH : U ≤ H := (piCore_le_sylow P).trans hPH
  have hUconj : ∀ h ∈ H, ∀ x ∈ U, h * x * h⁻¹ ∈ U :=
    fun h _ x hx => (inferInstance : U.Normal).conj_mem x hx h
  have hdisj : K' ⊓ U = ⊥ :=
    disjoint_iff.mp (disjoint_of_isPiGroup (isPiGroup_compl_of_not_dvd hK'card)
      (by rw [compl_compl]; exact isPiGroup_piCore))
  -- so `K'` centralizes `O_p(G)`, hence lies in it by Hall–Higman
  have hK'C : K' ≤ Subgroup.centralizer (U : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (commute_of_inf_eq_bot hK'H hUH hK'conj hUconj hdisj hx (SetLike.mem_coe.mp hy)).symm
  have hK'U : K' ≤ U := hK'C.trans (centralizer_piCore_le_piCore hsolv hcore)
  have hK'bot : K' = ⊥ := le_bot_iff.mp (hdisj ▸ le_inf le_rfl hK'U)
  have hKbot : K = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hK'bot
  -- then `H` is a `p`-group containing the Sylow `p`-subgroup `P`
  have hHp : IsPGroup p ↥H :=
    (hKquot.of_equiv (QuotientGroup.quotientMulEquivOfEq hKbot)).of_equiv
      (QuotientGroup.quotientBot (G := ↥H))
  exact P.3 hHp hPH

/-- **Isaacs 7.1, Step 5.**  `C_G(Z(P)) = P`. -/
theorem thompson_step_five [Finite G] [Fact p.Prime]
    (IH : ∀ (Y : Type u) [Group Y] [Finite Y], Nat.card Y < Nat.card G →
      ThompsonHypothesis p Y → HasNormalPComplement p Y)
    (hyp : ThompsonHypothesis p G) (hG : ¬ HasNormalPComplement p G)
    (hsolv : IsPiSeparable ({p} : Set ℕ) G) (hcore : piCore ({p}ᶜ : Set ℕ) G = ⊥)
    (P : Sylow p G) :
    Subgroup.centralizer ((centerOf (P : Subgroup G) : Subgroup G) : Set G) = (P : Subgroup G) := by
  refine thompson_step_four IH hyp hsolv hcore P (le_centralizer_centerOf _) ?_
  intro htop
  exact hG (((hyp P).1).of_mulEquiv (by rw [htop]; exact Subgroup.topEquiv))

/-!
## Step 6 of Isaacs' proof: `L̄` is abelian

`L = bigL p G` is the preimage of `L̄ = O_p'(Ḡ)`, as in `Isaacs/NormalJTheorem.lean`.
-/

/-- **Isaacs 7.1, Step 6, first paragraph.**  No subgroup strictly between `U` and `L` is
normalized by `P`: `P X` is a group containing `P`, so by Step 4 it is `P` or `G`. -/
theorem eq_of_le_bigL_of_le_normalizer [Finite G] [Fact p.Prime]
    (IH : ∀ (Y : Type u) [Group Y] [Finite Y], Nat.card Y < Nat.card G →
      ThompsonHypothesis p Y → HasNormalPComplement p Y)
    (hyp : ThompsonHypothesis p G) (hsolv : IsPiSeparable ({p} : Set ℕ) G)
    (hcore : piCore ({p}ᶜ : Set ℕ) G = ⊥) (P : Sylow p G)
    {X : Subgroup G} (hUX : piCore ({p} : Set ℕ) G ≤ X) (hXL : X ≤ bigL p G)
    (hPX : (P : Subgroup G) ≤ Subgroup.normalizer (X : Set G)) :
    X = piCore ({p} : Set ℕ) G ∨ X = bigL p G := by
  rcases eq_or_ne (X ⊔ (P : Subgroup G)) ⊤ with htop | hne
  · right
    refine le_antisymm hXL fun y hy => ?_
    exact sup_inf_bigL_le P.isPGroup' hUX hXL hPX
      (Subgroup.mem_inf.mpr ⟨htop ▸ Subgroup.mem_top y, hy⟩)
  · left
    have hne' : (P : Subgroup G) ⊔ X ≠ ⊤ := by rwa [sup_comm]
    have h1 : (P : Subgroup G) ⊔ X = (P : Subgroup G) :=
      thompson_step_four IH hyp hsolv hcore P le_sup_left hne'
    exact le_antisymm
      (le_piCore_of_isPGroup_of_le_bigL (P.isPGroup'.to_le (h1 ▸ le_sup_right)) hXL) hUX

/-- The same statement read in `Ḡ`. -/
theorem eq_bot_or_eq_piCore_of_le_normalizer [Finite G] [Fact p.Prime]
    (IH : ∀ (Y : Type u) [Group Y] [Finite Y], Nat.card Y < Nat.card G →
      ThompsonHypothesis p Y → HasNormalPComplement p Y)
    (hyp : ThompsonHypothesis p G) (hsolv : IsPiSeparable ({p} : Set ℕ) G)
    (hcore : piCore ({p}ᶜ : Set ℕ) G = ⊥) (P : Sylow p G)
    {Y : Subgroup (G ⧸ piCore ({p} : Set ℕ) G)}
    (hYL : Y ≤ piCore ({p}ᶜ : Set ℕ) (G ⧸ piCore ({p} : Set ℕ) G))
    (hPY : ((P : Subgroup G).map (QuotientGroup.mk' (piCore ({p} : Set ℕ) G)))
      ≤ Subgroup.normalizer (Y : Set (G ⧸ piCore ({p} : Set ℕ) G))) :
    Y = ⊥ ∨ Y = piCore ({p}ᶜ : Set ℕ) (G ⧸ piCore ({p} : Set ℕ) G) := by
  set U : Subgroup G := piCore ({p} : Set ℕ) G with hU
  set X : Subgroup G := Y.comap (QuotientGroup.mk' U) with hX
  have hmapX : X.map (QuotientGroup.mk' U) = Y :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective U) Y
  have hmapU : U.map (QuotientGroup.mk' U) = ⊥ := by
    rw [eq_bot_iff]
    rintro - ⟨u, hu, rfl⟩
    exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff u).mpr hu)
  have hmapL : (bigL p G).map (QuotientGroup.mk' U)
      = piCore ({p}ᶜ : Set ℕ) (G ⧸ U) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective U) _
  have hUX : U ≤ X := by
    intro u hu
    have h1 : (QuotientGroup.mk' U) u = 1 := (QuotientGroup.eq_one_iff u).mpr hu
    rw [hX, Subgroup.mem_comap, h1]
    exact one_mem _
  have hXL : X ≤ bigL p G := Subgroup.comap_mono hYL
  have hPX : (P : Subgroup G) ≤ Subgroup.normalizer (X : Set G) := by
    rw [normalizer_eq_comap_of_le hUX, hmapX]
    exact fun g hg => Subgroup.mem_comap.mpr (hPY (Subgroup.mem_map_of_mem _ hg))
  rcases eq_of_le_bigL_of_le_normalizer IH hyp hsolv hcore P hUX hXL hPX with h | h
  · left; rw [← hmapX, h, hmapU]
  · right; rw [← hmapX, h, hmapL]

/-- **Isaacs 7.1, Step 6.**  `L̄ = O_p'(G/U)` is abelian.

By the first paragraph, `L̄` has no nontrivial proper `P̄`-invariant subgroup.  Coprime action
gives a `P̄`-invariant Sylow `q`-subgroup, which must therefore be all of `L̄`; so `L̄` is a
`q`-group, its derived subgroup is proper and `P̄`-invariant, hence trivial. -/
theorem thompson_step_six [Finite G] [Fact p.Prime]
    (IH : ∀ (Y : Type u) [Group Y] [Finite Y], Nat.card Y < Nat.card G →
      ThompsonHypothesis p Y → HasNormalPComplement p Y)
    (hyp : ThompsonHypothesis p G) (hsolv : IsPiSeparable ({p} : Set ℕ) G)
    (hcore : piCore ({p}ᶜ : Set ℕ) G = ⊥) (P : Sylow p G) :
    ∀ x ∈ piCore ({p}ᶜ : Set ℕ) (G ⧸ piCore ({p} : Set ℕ) G),
      ∀ y ∈ piCore ({p}ᶜ : Set ℕ) (G ⧸ piCore ({p} : Set ℕ) G), x * y = y * x := by
  have hp : p.Prime := Fact.out
  set U : Subgroup G := piCore ({p} : Set ℕ) G with hU
  set Lbar : Subgroup (G ⧸ U) := piCore ({p}ᶜ : Set ℕ) (G ⧸ U) with hLbar
  set Pbar : Subgroup (G ⧸ U) := (P : Subgroup G).map (QuotientGroup.mk' U) with hPbar
  have hPbarp : IsPGroup p ↥Pbar := P.isPGroup'.map _
  have hLp' : ¬ p ∣ Nat.card ↥Lbar := not_dvd_card_piCore_compl
  have hcop : Nat.Coprime p (Nat.card ↥Lbar) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hLp'
  have hPbarN : Pbar ≤ Subgroup.normalizer (Lbar : Set (G ⧸ U)) := fun g _ => by
    rw [Subgroup.normalizer_eq_top Lbar]; exact Subgroup.mem_top g
  -- the conjugation action of `P̄` on `L̄`
  let _inst := CoprimeAction.conjActionOfLeNormalizer Pbar Lbar hPbarN
  have hcoe : ∀ (a : ↥Pbar) (g : ↥Lbar),
      ((a • g : ↥Lbar) : G ⧸ U) = (a : G ⧸ U) * (g : G ⧸ U) * (a : G ⧸ U)⁻¹ :=
    fun a g => CoprimeAction.conjActionOfLeNormalizer_coe Pbar Lbar hPbarN a g
  -- `L̄` is a `q`-group
  rcases eq_or_ne Lbar ⊥ with hLbot | hLne
  · intro x hx y hy
    rw [hLbot, Subgroup.mem_bot] at hx hy
    rw [hx, hy]
  obtain ⟨q, hq, hqdvd⟩ : ∃ q, q.Prime ∧ q ∣ Nat.card ↥Lbar :=
    Nat.exists_prime_and_dvd fun h => hLne (Subgroup.eq_bot_of_card_eq _ h)
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q, hQinv⟩ :=
    NoncyclicAbelian.exists_invariant_sylow (A := ↥Pbar) (G := ↥Lbar) hPbarp hcop (q := q)
  have hQconj : ∀ a ∈ Pbar, ∀ z ∈ (Q : Subgroup ↥Lbar).map Lbar.subtype,
      a * z * a⁻¹ ∈ (Q : Subgroup ↥Lbar).map Lbar.subtype := by
    rintro a ha - ⟨g, hg, rfl⟩
    refine ⟨(⟨a, ha⟩ : ↥Pbar) • g, (hQinv.invariant ⟨a, ha⟩ g).mp hg, ?_⟩
    exact (hcoe ⟨a, ha⟩ g).symm
  have hQne : (Q : Subgroup ↥Lbar).map Lbar.subtype ≠ ⊥ := by
    intro hbot
    exact sylow_ne_bot_of_dvd Q hqdvd
      ((Subgroup.map_eq_bot_iff_of_injective _ Lbar.subtype_injective).mp hbot)
  have hQeq : (Q : Subgroup ↥Lbar).map Lbar.subtype = Lbar :=
    ((eq_bot_or_eq_piCore_of_le_normalizer IH hyp hsolv hcore P
      (Subgroup.map_subtype_le _) (le_normalizer_of_conj_mem hQconj)).resolve_left hQne)
  have hQtop : (Q : Subgroup ↥Lbar) = ⊤ := by
    refine Subgroup.map_injective Lbar.subtype_injective ?_
    rw [hQeq, ← MonoidHom.range_eq_map, Lbar.range_subtype]
  have hLq : IsPGroup q ↥Lbar :=
    (hQtop ▸ Q.isPGroup' : IsPGroup q ↥(⊤ : Subgroup ↥Lbar)).of_equiv Subgroup.topEquiv
  -- the derived subgroup of `L̄` is proper and `P̄`-invariant, hence trivial
  have hnt : Nontrivial ↥Lbar := (Subgroup.nontrivial_iff_ne_bot Lbar).mpr hLne
  have hnil : Group.IsNilpotent ↥Lbar := hLq.isNilpotent
  have hcomm : commutator ↥Lbar < ⊤ :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥Lbar)
  have hCle : (commutator ↥Lbar).map Lbar.subtype ≤ Lbar := Subgroup.map_subtype_le _
  have hCnorm : Pbar ≤ Subgroup.normalizer
      (((commutator ↥Lbar).map Lbar.subtype : Subgroup (G ⧸ U)) : Set (G ⧸ U)) := by
    refine le_normalizer_of_characteristic_subgroupOf hCle ?_ hPbarN
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Lbar.subtype_injective]
    infer_instance
  have hCne : (commutator ↥Lbar).map Lbar.subtype ≠ Lbar := by
    intro hbot
    refine absurd ?_ hcomm.ne
    refine Subgroup.map_injective Lbar.subtype_injective ?_
    rw [hbot, ← MonoidHom.range_eq_map, Lbar.range_subtype]
  have hCbot : (commutator ↥Lbar).map Lbar.subtype = ⊥ :=
    (eq_bot_or_eq_piCore_of_le_normalizer IH hyp hsolv hcore P hCle hCnorm).resolve_right hCne
  have hCbot' : commutator ↥Lbar = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ Lbar.subtype_injective).mp hCbot
  intro x hx y hy
  have h1 : ⁅(⟨x, hx⟩ : ↥Lbar), (⟨y, hy⟩ : ↥Lbar)⁆ ∈ commutator ↥Lbar :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [hCbot', Subgroup.mem_bot] at h1
  have h2 := congrArg (Subtype.val) h1
  simp only [commutatorElement_def] at h2
  push_cast at h2
  have h3 : x * y * x⁻¹ * y⁻¹ = 1 := h2
  have h4 : x * y * x⁻¹ = y := mul_inv_eq_one.mp h3
  calc x * y = (x * y * x⁻¹) * x := by group
    _ = y * x := by rw [h4]

/-!
## Step 7 and the theorem
-/

omit [Group G] in
/-- A group that is both a `q`-group and an `r`-group for distinct primes is trivial. -/
theorem card_eq_one_of_isPGroup_of_isPGroup {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    {Y : Type*} [Group Y] [Finite Y] (h1 : IsPGroup q Y) (h2 : IsPGroup r Y) :
    Nat.card Y = 1 := by
  have hqf : Fact q.Prime := ⟨hq⟩
  have hrf : Fact r.Prime := ⟨hr⟩
  obtain ⟨a, ha⟩ := h1.exists_card_eq
  obtain ⟨b, hb⟩ := h2.exists_card_eq
  rcases Nat.eq_zero_or_pos a with rfl | hapos
  · rwa [pow_zero] at ha
  · exfalso
    have hdvd : q ∣ r ^ b := by rw [← hb, ha]; exact dvd_pow_self q hapos.ne'
    exact hqr ((Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow hdvd))

/-- **Isaacs 7.1, second half of Step 2.**  `G` is `p`-solvable, because `1 ≤ U ≤ L ≤ G` has
factors a `p`-group, a `p'`-group and a `p`-group. -/
theorem isPiSeparable_of_hasNormalPComplement_quotient [Finite G] [Fact p.Prime]
    (h : HasNormalPComplement p (G ⧸ piCore ({p} : Set ℕ) G)) :
    IsPiSeparable ({p} : Set ℕ) G := by
  refine IsPiSeparable.of_normal_of_quotient (piCore ({p} : Set ℕ) G)
    (IsPiSeparable.of_isPiOrCompl (Or.inl isPiGroup_piCore)) ?_
  refine IsPiSeparable.of_normal_of_quotient
    (piCore ({p}ᶜ : Set ℕ) (G ⧸ piCore ({p} : Set ℕ) G))
    (IsPiSeparable.of_isPiOrCompl (Or.inr isPiGroup_piCore)) ?_
  exact IsPiSeparable.of_isPiOrCompl
    (Or.inl (IsPGroup.isPiGroup Fact.out (hasNormalPComplement_iff.mp h)))

/-- **Isaacs, Theorem 7.1: Thompson's normal `p`-complement theorem.**

Let `P ∈ Syl_p(G)` with `G` finite and `p ≠ 2`, and assume `C_G(Z(P))` and `N_G(J(P))` have normal
`p`-complements.  Then `G` has a normal `p`-complement. -/
theorem hasNormalPComplement_of_thompson [Finite G] [Fact p.Prime] (hp2 : p ≠ 2)
    (hyp : ThompsonHypothesis p G) : HasNormalPComplement p G := by
  have key : ∀ (n : ℕ) (X : Type u) [Group X] [Finite X], Nat.card X ≤ n →
      ThompsonHypothesis p X → HasNormalPComplement p X := by
    intro n
    induction n with
    | zero =>
      intro X _ _ hcard
      exact absurd (Nat.card_pos (α := X)) (by omega)
    | succ n ih =>
      intro X _ _ hcard hypX
      by_contra hG
      have hp : p.Prime := Fact.out
      have IH : ∀ (Y : Type u) [Group Y] [Finite Y], Nat.card Y < Nat.card X →
          ThompsonHypothesis p Y → HasNormalPComplement p Y :=
        fun Y _ _ hlt => ih Y (by omega)
      obtain ⟨P⟩ : Nonempty (Sylow p X) := inferInstance
      obtain ⟨U, hU, hmax⟩ := exists_bad_max hG
      -- Step 1
      have hUcore : U = piCore ({p} : Set ℕ) X := thompson_step_one IH hypX hU hmax
      subst hUcore
      have hNU : Subgroup.normalizer ((piCore ({p} : Set ℕ) X : Subgroup X) : Set X) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.mpr inferInstance
      have hUP : piCore ({p} : Set ℕ) X ≤ (P : Subgroup X) := piCore_le_sylow P
      -- Step 2 and `p`-solvability
      have hstep2 : HasNormalPComplement p (X ⧸ piCore ({p} : Set ℕ) X) :=
        thompson_step_two IH hU hmax hNU P hUP
      have hsolv : IsPiSeparable ({p} : Set ℕ) X :=
        isPiSeparable_of_hasNormalPComplement_quotient hstep2
      -- Step 3
      have hcore : piCore ({p}ᶜ : Set ℕ) X = ⊥ := thompson_step_three IH hypX hG P
      -- Step 5
      have hP5 := thompson_step_five IH hypX hG hsolv hcore P
      -- Step 6
      have hLab := thompson_step_six IH hypX hsolv hcore P
      -- Step 7: a Sylow `2`-subgroup of `X` is abelian
      have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hpXq : IsPGroup p ((X ⧸ piCore ({p} : Set ℕ) X) ⧸
          piCore ({p}ᶜ : Set ℕ) (X ⧸ piCore ({p} : Set ℕ) X)) :=
        hasNormalPComplement_iff.mp hstep2
      have habel2 : ∀ B : Subgroup X, IsPGroup 2 ↥B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
        obtain ⟨Q⟩ : Nonempty (Sylow 2 X) := inferInstance
        refine (forall_two_commute_iff_sylow Q).mpr fun x hx y hy => ?_
        set U : Subgroup X := piCore ({p} : Set ℕ) X with hUdef
        set Lbar : Subgroup (X ⧸ U) := piCore ({p}ᶜ : Set ℕ) (X ⧸ U) with hLdef
        set Qbar : Subgroup (X ⧸ U) := (Q : Subgroup X).map (QuotientGroup.mk' U) with hQdef
        have hQ2 : IsPGroup 2 ↥Qbar := Q.isPGroup'.map _
        -- `Q̄` is a `p'`-group, so it lies in the normal `p`-complement `L̄`
        have hZbot : Qbar.map (QuotientGroup.mk' Lbar) = ⊥ := by
          refine Subgroup.eq_bot_of_card_eq _
            (card_eq_one_of_isPGroup_of_isPGroup Nat.prime_two hp (Ne.symm hp2)
              (hQ2.map _) (hpXq.to_subgroup _))
        have hQL : Qbar ≤ Lbar := by
          intro z hz
          have h1 : (QuotientGroup.mk' Lbar) z = 1 :=
            Subgroup.mem_bot.mp (hZbot ▸ Subgroup.mem_map_of_mem _ hz)
          exact (QuotientGroup.eq_one_iff z).mp h1
        -- `Q ⊓ U = 1`, so commuting modulo `U` is commuting
        have hQU : (Q : Subgroup X) ⊓ U = ⊥ :=
          Subgroup.eq_bot_of_card_eq _
            (card_eq_one_of_isPGroup_of_isPGroup Nat.prime_two hp (Ne.symm hp2)
              (Q.isPGroup'.to_le inf_le_left)
              ((IsPiGroup.isPGroup (p := p) isPiGroup_piCore).to_le inf_le_right))
        have hcomm : (QuotientGroup.mk' U) x * (QuotientGroup.mk' U) y
            = (QuotientGroup.mk' U) y * (QuotientGroup.mk' U) x :=
          hLab _ (hQL (Subgroup.mem_map_of_mem _ hx)) _ (hQL (Subgroup.mem_map_of_mem _ hy))
        have hmemU : x * y * (y * x)⁻¹ ∈ U := by
          refine (QuotientGroup.eq_one_iff _).mp ?_
          have h3 : (QuotientGroup.mk' U) (x * y * (y * x)⁻¹) = 1 := by
            simp only [map_mul, map_inv, hcomm]
            group
          exact h3
        have hmemQ : x * y * (y * x)⁻¹ ∈ (Q : Subgroup X) :=
          mul_mem (mul_mem hx hy) (inv_mem (mul_mem hy hx))
        have h4 : x * y * (y * x)⁻¹ = 1 := by
          have h5 := Subgroup.mem_inf.mpr ⟨hmemQ, hmemU⟩
          rwa [hQU, Subgroup.mem_bot] at h5
        exact mul_inv_eq_one.mp h4
      -- the normal-`J` theorem gives `J(P) ⊴ X`, whose normalizer is `X`
      have hJ : (thompsonSubgroup p (P : Subgroup X)).Normal :=
        thompsonSubgroup_normal hp2 hsolv habel2 hcore P hP5
      have htop : Subgroup.normalizer
          ((thompsonSubgroup p (P : Subgroup X) : Subgroup X) : Set X) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.mpr hJ
      exact hG (((hypX P).2).of_mulEquiv (by rw [htop]; exact Subgroup.topEquiv))
  exact key (Nat.card G) G le_rfl hyp

/-- **Isaacs, Theorem 7.1**, stated as Isaacs does: for one Sylow `p`-subgroup. -/
theorem hasNormalPComplement_of_thompson' [Finite G] [Fact p.Prime] (hp2 : p ≠ 2) (P : Sylow p G)
    (hC : HasNormalPComplement p
      ↥(Subgroup.centralizer ((centerOf (P : Subgroup G) : Subgroup G) : Set G)))
    (hN : HasNormalPComplement p
      ↥(Subgroup.normalizer ((thompsonSubgroup p (P : Subgroup G) : Subgroup G) : Set G))) :
    HasNormalPComplement p G :=
  hasNormalPComplement_of_thompson hp2 (thompsonHypothesis_of_sylow P hC hN)

end PiGroups
