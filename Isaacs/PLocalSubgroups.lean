module

public import Isaacs.PiSeparableGroups
public import Isaacs.ThompsonPxQ
public import Mathlib.GroupTheory.Sylow

/-!
# `p`-local subgroups: Isaacs' Lemma 2.17 and Theorem 4.33

Isaacs, *Finite Group Theory*, Theorem 4.33: in a finite `p`-solvable group `G`, every `p`-local
subgroup `H` satisfies `O_p'(H) ≤ O_p'(G)`.  A subgroup is `p`-local if it is the normalizer of a
nontrivial `p`-subgroup (`PiGroups.IsPLocal`); `p`-solvable is `{p}`-separable.  This is the step
Isaacs uses in the proof of Burnside's `p ^ a q ^ b` theorem, and it is where Thompson's `P × Q`
lemma gets used.

* `PiGroups.piCore_compl_eq_bot_of_piCore_compl_eq_bot` — 4.33 in the case `O_p'(G) = 1`.  With
  `H = N_G(P)`, `Q = O_p'(H)` and `U = O_p(G)`: `P` and `Q` are normal in `H` and meet trivially,
  so they commute elementwise; `Q` centralizes `C_U(P)`, because `C_U(P) ≤ U ⊓ H`, a normal
  `p`-subgroup of `H`; so Thompson's `P × Q` lemma (`CoprimeAction.thompson_pq`), applied to `P`
  and `Q` acting by conjugation on the `p`-group `U`, gives `Q ≤ C_G(U)`; Hall–Higman 1.2.3
  (`PiGroups.centralizer_piCore_le_piCore`) gives `C_G(U) ≤ U`, so `Q` is both a `p`-group and a
  `p'`-group, hence trivial.  This case needs neither `P ≠ 1` nor `H = N_G(P)` on the nose: all it
  uses is that `P` is a `p`-subgroup normal in `H` with `C_U(P) ≤ H`.

* `PiGroups.normalizer_map_mk'_eq` — **Lemma 2.17**: for `N ⊴ G` of order prime to `p` and a
  `p`-subgroup `P`, `N_{G ⧸ N}(P N ⧸ N) = N_G(P) N ⧸ N`; hence `p`-locality passes to such
  quotients (`PiGroups.IsPLocal.map_mk'`).  The content is `N_G(P N) ≤ N_G(P) N`
  (`PiGroups.normalizer_sup_le`), proved by Isaacs' Frattini argument: `P` is a Sylow
  `p`-subgroup of `P N`, so a conjugate of `P` lying in `P N` is already `P N`-conjugate to it.
  This needs only Sylow's theorem — in particular no complement conjugacy, so neither 2.17 nor
  anything derived from it carries `CoprimeAction.SchurZassenhausConjugacy`.

* `PiGroups.map_piCore_compl_le_piCore_compl` — **Theorem 4.33** in general, by Isaacs' reduction
  to the first case through `Ḡ = G ⧸ O_p'(G)`, where `O_p'(Ḡ) = 1`
  (`PiGroups.piCore_quotient_piCore_eq_bot`) and `H̄` is still `p`-local by 2.17.

Everything here carries the `CoprimeAction.SchurZassenhausConjugacy` hypothesis, like the rest of
the development downstream of `Isaacs/GlaubermanLemma.lean`.
-/

@[expose] public section

namespace PiGroups

open CoprimeAction

universe u

variable {π : Set ℕ} {p : ℕ} {G : Type u} [Group G]

/-!
## Preliminaries
-/

/-- A finite `{p}`-group is a `p`-group. -/
theorem IsPiGroup.isPGroup [Finite G] (h : IsPiGroup ({p} : Set ℕ) G) : IsPGroup p G := by
  rw [IsPiGroup.iff_card] at h
  refine IsPGroup.of_card (n := (Nat.card G).primeFactorsList.length)
    (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdvd ↦ ?_)
  exact h d (Nat.mem_primeFactors.mpr ⟨hd, hdvd, Nat.card_pos.ne'⟩)

/-- A `π`-subgroup and a `π'`-subgroup meet trivially. -/
theorem disjoint_of_isPiGroup [Finite G] {A B : Subgroup G} (hA : IsPiGroup π A)
    (hB : IsPiGroup πᶜ B) : Disjoint A B := by
  rw [disjoint_iff]
  by_contra hne
  have : Nontrivial (A ⊓ B : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  exact not_subsingleton _
    (IsPiGroup.subsingleton (IsPiGroup.of_le inf_le_left hA) (IsPiGroup.of_le inf_le_right hB))

/-- Elements of two subgroups that are normal in a common subgroup `H` and meet trivially
commute. -/
theorem commute_of_disjoint_of_normalIn {H A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H)
    (hAn : (A.subgroupOf H).Normal) (hBn : (B.subgroupOf H).Normal) (hdisj : Disjoint A B) :
    ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := by
  intro x hx y hy
  have hdisj' : Disjoint (A.subgroupOf H) (B.subgroupOf H) :=
    Subgroup.disjoint_def.mpr fun {z} hz1 hz2 ↦
      Subtype.ext (Subgroup.disjoint_def.mp hdisj hz1 hz2)
  exact congrArg Subtype.val
    (Subgroup.commute_of_normal_of_disjoint _ _ hAn hBn hdisj' ⟨x, hA hx⟩ ⟨y, hB hy⟩ hx hy)

/-- `O_π(G ⧸ O_π(G)) = 1`: the preimage of a normal `π`-subgroup of `G ⧸ O_π(G)` is an extension
of a `π`-group by a `π`-group, hence lies in `O_π(G)`. -/
theorem piCore_quotient_piCore_eq_bot [Finite G] : piCore π (G ⧸ piCore π G) = ⊥ := by
  have hNK : piCore π G ≤ (piCore π (G ⧸ piCore π G)).comap (QuotientGroup.mk' (piCore π G)) := by
    intro x hx
    have h1 : (QuotientGroup.mk' (piCore π G)) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [Subgroup.mem_comap, h1]
    exact one_mem _
  have hmap : ((piCore π (G ⧸ piCore π G)).comap (QuotientGroup.mk' (piCore π G))).map
      (QuotientGroup.mk' (piCore π G)) = piCore π (G ⧸ piCore π G) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hKpi : IsPiGroup π ((piCore π (G ⧸ piCore π G)).comap (QuotientGroup.mk' (piCore π G))) :=
    IsPiGroup.of_normal_of_quotient
      (isPiGroup_piCore.of_equiv (Subgroup.subgroupOfEquivOfLe hNK).symm)
      (IsPiGroup.of_equiv (by rw [hmap]; exact isPiGroup_piCore)
        (quotientSubgroupOfEquivMap _ _).symm)
  have hle := le_piCore (K := (piCore π (G ⧸ piCore π G)).comap
    (QuotientGroup.mk' (piCore π G))) inferInstance hKpi
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff y).mpr (hle hx))

/-- The conjugation action of `G` on a normal subgroup. -/
instance conjAction (U : Subgroup G) [U.Normal] : MulDistribMulAction G U :=
  MulDistribMulAction.compHom U (MulAut.conjNormal (H := U))

/-!
## `p`-local subgroups
-/

/-- A subgroup is `p`-local if it is the normalizer of a nontrivial `p`-subgroup. -/
def IsPLocal (p : ℕ) {X : Type*} [Group X] (H : Subgroup X) : Prop :=
  ∃ P : Subgroup X, P ≠ ⊥ ∧ IsPGroup p P ∧ H = Subgroup.normalizer (P : Set _)

/-!
## Isaacs 4.33, the case `O_p'(G) = 1`
-/

variable [Finite G] [Fact p.Prime]

/-- **Isaacs, Theorem 4.33**, main case: if `O_p'(G) = 1` then `O_p'(H) = 1` for every `p`-local
subgroup `H`.  Only these properties of a `p`-local subgroup are used: `H` contains a `p`-subgroup
`P` normal in `H` such that every element of `O_p(G)` centralizing `P` lies in `H`. -/
theorem piCore_compl_eq_bot_of_piCore_compl_eq_bot (hSZ : SchurZassenhausConjugacy.{u})
    (hsep : IsPiSeparable ({p} : Set ℕ) G) (hbot : piCore ({p}ᶜ : Set ℕ) G = ⊥)
    {P H : Subgroup G} (hP : IsPGroup p P) (hPH : P ≤ H) [hPn : (P.subgroupOf H).Normal]
    (hCU : ∀ u ∈ piCore ({p} : Set ℕ) G, (∀ x ∈ P, x * u = u * x) → u ∈ H) :
    piCore ({p}ᶜ : Set ℕ) H = ⊥ := by
  have hp : p.Prime := ‹Fact p.Prime›.out
  -- `G` acts by conjugation on the `p`-group `U = O_p(G)`
  have hcoe : ∀ (g : G) (v : piCore ({p} : Set ℕ) G),
      ((g • v : piCore ({p} : Set ℕ) G) : G) = g * (v : G) * g⁻¹ :=
    fun g v ↦ MulAut.conjNormal_apply g v
  have hU : IsPGroup p (piCore ({p} : Set ℕ) G) := IsPiGroup.isPGroup isPiGroup_piCore
  -- `Q`, the image of `O_p'(H)` in `G`, is a `p'`-subgroup normal in `H`
  have hQpi : IsPiGroup ({p}ᶜ : Set ℕ) ((piCore ({p}ᶜ : Set ℕ) H).map H.subtype) :=
    isPiGroup_piCore.of_equiv
      ((piCore ({p}ᶜ : Set ℕ) H).equivMapOfInjective _ H.subtype_injective)
  have hQle : (piCore ({p}ᶜ : Set ℕ) H).map H.subtype ≤ H := Subgroup.map_subtype_le _
  have hQeq : ((piCore ({p}ᶜ : Set ℕ) H).map H.subtype).subgroupOf H = piCore ({p}ᶜ : Set ℕ) H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hQn : (((piCore ({p}ᶜ : Set ℕ) H).map H.subtype).subgroupOf H).Normal := by
    rw [hQeq]; infer_instance
  have hQdvd : ¬ p ∣ Nat.card ((piCore ({p}ᶜ : Set ℕ) H).map H.subtype) := fun hdvd ↦
    IsPiGroup.iff_card.mp hQpi p (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩) rfl
  -- `P` and `Q` are normal in `H` and meet trivially, so they commute
  have hcomm : ∀ x ∈ P, ∀ y ∈ (piCore ({p}ᶜ : Set ℕ) H).map H.subtype, x * y = y * x :=
    commute_of_disjoint_of_normalIn hPH hQle hPn hQn
      (disjoint_of_isPiGroup (IsPiGroup.of_isPGroup (π := ({p} : Set ℕ)) hp rfl hP) hQpi)
  -- `Q` fixes every element of `U` fixed by `P`
  have hfix : ∀ u : piCore ({p} : Set ℕ) G, (∀ x ∈ P, x • u = u) →
      ∀ y ∈ (piCore ({p}ᶜ : Set ℕ) H).map H.subtype, y • u = u := by
    intro u hu y hy
    -- such a `u` centralizes `P`, hence lies in `H`
    have hcu : ∀ x ∈ P, x * (u : G) = (u : G) * x := by
      intro x hx
      have h1 : x * (u : G) * x⁻¹ = (u : G) := by
        rw [← hcoe x u]
        exact congrArg Subtype.val (hu x hx)
      calc x * (u : G) = x * (u : G) * x⁻¹ * x := by group
        _ = (u : G) * x := by rw [h1]
    have huH : (u : G) ∈ H := hCU (u : G) u.2 hcu
    -- `U ⊓ H` is a normal `p`-subgroup of `H`, and `Q` a normal `p'`-subgroup
    have hUHn : ((piCore ({p} : Set ℕ) G ⊓ H).subgroupOf H).Normal := by
      rw [Subgroup.inf_subgroupOf_right]; infer_instance
    have hcomm2 := commute_of_disjoint_of_normalIn (A := piCore ({p} : Set ℕ) G ⊓ H)
      (B := (piCore ({p}ᶜ : Set ℕ) H).map H.subtype) inf_le_right hQle hUHn hQn
      (disjoint_of_isPiGroup (IsPiGroup.of_le inf_le_left isPiGroup_piCore) hQpi)
    refine Subtype.ext ?_
    rw [hcoe]
    have h2 := hcomm2 (u : G) ⟨u.2, huH⟩ y hy
    calc y * (u : G) * y⁻¹ = (u : G) * y * y⁻¹ := by rw [← h2]
      _ = (u : G) := by group
  -- Thompson's `P × Q` lemma: `Q` acts trivially on `U`, that is, `Q ≤ C_G(U)`
  have hQfix := thompson_pq hSZ hU hP hQdvd hcomm hfix
  -- Hall–Higman 1.2.3: `C_G(U) ≤ U`
  have hQU : (piCore ({p}ᶜ : Set ℕ) H).map H.subtype ≤ piCore ({p} : Set ℕ) G := by
    refine le_trans ?_ (centralizer_piCore_le_piCore hsep hbot)
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h1 : y * g * y⁻¹ = g := by
      rw [← hcoe y ⟨g, hg⟩]
      exact congrArg Subtype.val (hQfix y hy ⟨g, hg⟩)
    calc g * y = y * g * y⁻¹ * y := by rw [h1]
      _ = y * g := by group
  -- so `Q` is a `p`-group and a `p'`-group, hence trivial
  have : Subsingleton ((piCore ({p}ᶜ : Set ℕ) H).map H.subtype) :=
    IsPiGroup.subsingleton (IsPiGroup.of_le hQU isPiGroup_piCore) hQpi
  refine (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp (eq_bot_iff.mpr ?_)
  intro y hy
  exact Subgroup.mem_bot.mpr
    (congrArg Subtype.val (Subsingleton.elim (⟨y, hy⟩ :
      ((piCore ({p}ᶜ : Set ℕ) H).map H.subtype)) 1))

/-!
## Isaacs 2.17

`p`-locality passes to quotients by normal subgroups of order prime to `p`.  This is what lets
Isaacs reduce Theorem 4.33 to the case `O_p'(G) = 1`.
-/

open scoped Pointwise

omit [Finite G] in
/-- Conjugation fixes a subgroup exactly when it is normalized. -/
theorem map_conj_eq_self_iff {H : Subgroup G} {g : G} :
    H.map (MulAut.conj g).toMonoidHom = H ↔ g ∈ Subgroup.normalizer (H : Set _) :=
  Subgroup.conjAct_pointwise_smul_iff

omit [Finite G] [Fact p.Prime] in
/-- A finite group of order prime to `p` is a `p'`-group. -/
theorem isPiGroup_compl_of_not_dvd {X : Type*} [Group X] [Finite X] (h : ¬ p ∣ Nat.card X) :
    IsPiGroup ({p}ᶜ : Set ℕ) X := by
  rw [IsPiGroup.iff_card]
  intro r hr hrp
  rw [Set.mem_singleton_iff] at hrp
  exact h (hrp ▸ Nat.dvd_of_mem_primeFactors hr)

/-!
## Sylow subgroups of a subgroup

Isaacs' proof of Lemma 2.17 is a Frattini argument: `P` is a Sylow `p`-subgroup of `P N`, so any
two such are conjugate in `P N`.  These are the facts about Sylow subgroups of a subgroup that
that argument needs.
-/

omit [Finite G] in
/-- `|K : H ⊓ K| ⬝ |H ⊓ K| = |K|`. -/
theorem relIndex_mul_card_inf (H K : Subgroup G) :
    H.relIndex K * Nat.card ↥(H ⊓ K) = Nat.card ↥K := by
  have hcard : Nat.card ↥(H.subgroupOf K) = Nat.card ↥(H ⊓ K) := by
    rw [← Subgroup.card_map_of_injective (f := K.subtype) K.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
  have h := Subgroup.card_mul_index (H.subgroupOf K)
  rw [hcard] at h
  rw [Subgroup.relIndex, mul_comm]
  exact h

/-- A `p`-subgroup of `H` lies in a `p`-subgroup of `H` of index prime to `p` — a Sylow
`p`-subgroup of `H`, read in the ambient group. -/
theorem exists_sylow_le_of_le {H X : Subgroup G} (hXH : X ≤ H)
    (hX : IsPGroup p X) :
    ∃ S : Subgroup G, X ≤ S ∧ S ≤ H ∧ IsPGroup p S ∧ ¬ p ∣ (S.subgroupOf H).index := by
  obtain ⟨S₀, hS₀⟩ := (hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXH).symm).exists_le_sylow
  refine ⟨(S₀ : Subgroup ↥H).map H.subtype, ?_, Subgroup.map_subtype_le _,
    S₀.isPGroup'.map _, ?_⟩
  · have h1 := Subgroup.map_mono (f := H.subtype) hS₀
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXH] at h1
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact S₀.not_dvd_index

/-- Two `p`-subgroups of `H` of index prime to `p` are conjugate by an element of `H`. -/
theorem exists_conj_of_sylow_le {H S T : Subgroup G} (hSH : S ≤ H)
    (hTH : T ≤ H) (hS : IsPGroup p S) (hT : IsPGroup p T) (hSi : ¬ p ∣ (S.subgroupOf H).index)
    (hTi : ¬ p ∣ (T.subgroupOf H).index) :
    ∃ n ∈ H, T = S.map (MulAut.conj n).toMonoidHom := by
  -- both are Sylow `p`-subgroups of `H`
  have key : ∀ Y : Subgroup G, Y ≤ H → IsPGroup p Y → ¬ p ∣ (Y.subgroupOf H).index →
      ∀ Y₀ : Sylow p ↥H, Y.subgroupOf H ≤ (Y₀ : Subgroup ↥H) →
        Y.subgroupOf H = (Y₀ : Subgroup ↥H) := by
    intro Y hYH hY hYi Y₀ hle
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    -- the index of `Y` inside `Y₀` is both a power of `p` and prime to `p`
    have hdvd : Nat.card (Y₀ : Subgroup ↥H) ∣ Nat.card ↥(Y.subgroupOf H) *
        (Y.subgroupOf H).index := by
      rw [Subgroup.card_mul_index]
      exact Subgroup.card_subgroup_dvd_card _
    have hcop : Nat.Coprime (Nat.card (Y₀ : Subgroup ↥H)) ((Y.subgroupOf H).index) := by
      obtain ⟨k, hk⟩ := Y₀.isPGroup'.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hYi)
    exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right hdvd)
  obtain ⟨S₀, hS₀⟩ := (hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm).exists_le_sylow
  obtain ⟨T₀, hT₀⟩ := (hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).exists_le_sylow
  have hSeq := key S hSH hS hSi S₀ hS₀
  have hTeq := key T hTH hT hTi T₀ hT₀
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq ↥H S₀ T₀
  refine ⟨(n : G), n.2, ?_⟩
  -- transport the conjugation from `H` to `G`
  have hmap : (T.subgroupOf H : Subgroup ↥H)
      = (S.subgroupOf H).map (MulAut.conj n).toMonoidHom := by
    rw [hSeq, hTeq, ← hn, Sylow.coe_subgroup_smul]
    rfl
  have h1 := congrArg (Subgroup.map H.subtype) hmap
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTH] at h1
  have hcomp : H.subtype.comp (MulAut.conj n).toMonoidHom
      = (MulAut.conj (n : G)).toMonoidHom.comp H.subtype := by
    ext w
    rfl
  rw [h1, Subgroup.map_map, hcomp, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hSH]

/-- `P` is a Sylow `p`-subgroup of `P N` when `N ⊴ G` has order prime to `p`. -/
theorem not_dvd_relIndex_sup {N Q : Subgroup G} [N.Normal]
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
theorem normalizer_sup_le {N : Subgroup G} [N.Normal]
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

/-- **Isaacs, Lemma 2.17.**  If `N ⊴ G` has order prime to `p` and `P` is a `p`-subgroup of `G`,
then `N_{G ⧸ N}(P N ⧸ N) = N_G(P) N ⧸ N`. -/
theorem normalizer_map_mk'_eq {N : Subgroup G} [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {P : Subgroup G} (hP : IsPGroup p P) :
    Subgroup.normalizer ((P.map (QuotientGroup.mk' N)) : Set (G ⧸ N))
      = (Subgroup.normalizer (P : Set _)).map (QuotientGroup.mk' N) := by
  -- membership in `P N ⧸ N` is membership in `P N`
  have hpre : ∀ x : G, (QuotientGroup.mk' N) x ∈ P.map (QuotientGroup.mk' N) ↔ x ∈ P ⊔ N := by
    intro x
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hconj : ∀ g x : G, (QuotientGroup.mk' N) (g * x * g⁻¹)
      = (QuotientGroup.mk' N) g * (QuotientGroup.mk' N) x * ((QuotientGroup.mk' N) g)⁻¹ := by
    intro g x
    simp
  -- so the normalizer of `P N ⧸ N` is the image of the normalizer of `P N`
  have hcomap : (Subgroup.normalizer
      ((P.map (QuotientGroup.mk' N)) : Set (G ⧸ N))).comap (QuotientGroup.mk' N)
      = Subgroup.normalizer ((P ⊔ N : Subgroup G) : Set G) := by
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h x
      rw [← hpre x, ← hpre (g * x * g⁻¹), hconj]
      exact h _
    · intro h xbar
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N xbar
      rw [hpre x, ← hconj, hpre]
      exact h x
  have hstep : Subgroup.normalizer ((P.map (QuotientGroup.mk' N)) : Set (G ⧸ N))
      = (Subgroup.normalizer ((P ⊔ N : Subgroup G) : Set G)).map (QuotientGroup.mk' N) := by
    rw [← hcomap, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)]
  have hNbot : N.map (QuotientGroup.mk' N) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨n, hn, rfl⟩
    exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff n).mpr hn)
  have heasy : Subgroup.normalizer (P : Set _)
      ≤ Subgroup.normalizer ((P ⊔ N : Subgroup G) : Set G) := by
    intro l hl
    have hNl : N.map (MulAut.conj l).toMonoidHom = N := Subgroup.Normal.conj_smul_eq_self l N
    refine map_conj_eq_self_iff.mp ?_
    rw [Subgroup.map_sup, map_conj_eq_self_iff.mpr hl, hNl]
  rw [hstep]
  refine le_antisymm ?_ (Subgroup.map_mono heasy)
  calc (Subgroup.normalizer ((P ⊔ N : Subgroup G) : Set G)).map (QuotientGroup.mk' N)
      ≤ (Subgroup.normalizer (P : Set _) ⊔ N).map (QuotientGroup.mk' N) :=
        Subgroup.map_mono (normalizer_sup_le hN hP)
    _ = (Subgroup.normalizer (P : Set _)).map (QuotientGroup.mk' N) := by
          rw [Subgroup.map_sup, hNbot, sup_bot_eq]

/-- **Isaacs, Lemma 2.17**, the form used for Theorem 4.33: a `p`-local subgroup stays `p`-local
in a quotient by a normal subgroup of order prime to `p`. -/
theorem IsPLocal.map_mk' {N : Subgroup G} [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {L : Subgroup G} (hL : IsPLocal p L) :
    IsPLocal p (L.map (QuotientGroup.mk' N)) := by
  obtain ⟨P, hP0, hP, rfl⟩ := hL
  refine ⟨P.map (QuotientGroup.mk' N), ?_, hP.map _, (normalizer_map_mk'_eq hN hP).symm⟩
  -- `P` is not contained in `N`, because `p` divides `|P|` but not `|N|`
  intro hbot
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk
    exact hP0 (Subgroup.card_eq_one.mp hk)
  have hpP : p ∣ Nat.card P := by rw [hk]; exact dvd_pow_self p hk0
  exact hN (hpP.trans (Subgroup.card_dvd_of_le hbot))

/-!
## Isaacs 4.33, the general case
-/

omit [Finite G] [Fact p.Prime] in
/-- The image of a `π`-subgroup is a `π`-subgroup. -/
theorem IsPiGroup.map {H : Subgroup G} (hH : IsPiGroup π H) {K : Type*} [Group K] (ϕ : G →* K) :
    IsPiGroup π (H.map ϕ) := by
  rw [← H.range_subtype, MonoidHom.map_range]
  exact hH.of_surjective (ϕ.domRestrict H).rangeRestrict (ϕ.domRestrict H).rangeRestrict_surjective

/-- **Isaacs, Theorem 4.33.**  In a finite `p`-solvable group `G`, the `p'`-core of a `p`-local
subgroup `H` is contained in `O_p'(G)`.

Isaacs reduces to the case `O_p'(G) = 1` by passing to `Ḡ = G ⧸ O_p'(G)`, where the `p'`-core is
trivial (`PiGroups.piCore_quotient_piCore_eq_bot`) and `H̄` is still `p`-local
(`PiGroups.IsPLocal.map_mk'`, which is Lemma 2.17).  Then `O_p'(H̄) = 1` by the main case, and the
image of `O_p'(H)` is a normal `p'`-subgroup of `H̄`, hence trivial: that is,
`O_p'(H) ≤ O_p'(G)`. -/
theorem map_piCore_compl_le_piCore_compl (hSZ : SchurZassenhausConjugacy.{u})
    (hsep : IsPiSeparable ({p} : Set ℕ) G) {H : Subgroup G} (hH : IsPLocal p H) :
    (piCore ({p}ᶜ : Set ℕ) H).map H.subtype ≤ piCore ({p}ᶜ : Set ℕ) G := by
  have hp : p.Prime := ‹Fact p.Prime›.out
  -- `O_p'(G)` has order prime to `p`, so `H̄` is `p`-local in `Ḡ = G ⧸ O_p'(G)`
  have hNdvd : ¬ p ∣ Nat.card (piCore ({p}ᶜ : Set ℕ) G) := fun hdvd ↦
    IsPiGroup.iff_card.mp isPiGroup_piCore p
      (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩) rfl
  obtain ⟨P, -, hPp, hHP⟩ := IsPLocal.map_mk' (N := piCore ({p}ᶜ : Set ℕ) G) hNdvd hH
  -- the main case applies in `Ḡ`: an element of `O_p(Ḡ)` centralizing `P` normalizes it
  have hmain : piCore ({p}ᶜ : Set ℕ)
      ↥(Subgroup.normalizer (P : Set (G ⧸ piCore ({p}ᶜ : Set ℕ) G))) = ⊥ := by
    refine piCore_compl_eq_bot_of_piCore_compl_eq_bot hSZ (hsep.quotient _)
      piCore_quotient_piCore_eq_bot hPp Subgroup.le_normalizer ?_
    intro u _ hu
    rw [Subgroup.mem_normalizer_iff]
    refine fun y ↦ ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
    · rw [← hu y hy]
      simpa using hy
    · have h3 : u * y = u * (u * y * u⁻¹) := by rw [← hu _ hy]; group
      rwa [(mul_left_cancel h3).symm] at hy
  -- the image of `O_p'(H)` in `Ḡ` is a normal `p'`-subgroup of `H̄ = N_Ḡ(P)`
  have hQ'le : (piCore ({p}ᶜ : Set ℕ) H).map H.subtype ≤ H := Subgroup.map_subtype_le _
  have hQ'n : ∀ h ∈ H, ∀ z ∈ (piCore ({p}ᶜ : Set ℕ) H).map H.subtype,
      h * z * h⁻¹ ∈ (piCore ({p}ᶜ : Set ℕ) H).map H.subtype := by
    rintro h hh _ ⟨z, hz, rfl⟩
    exact ⟨⟨h, hh⟩ * z * ⟨h, hh⟩⁻¹, Subgroup.Normal.conj_mem inferInstance z hz ⟨h, hh⟩, rfl⟩
  have hQbarle : ((piCore ({p}ᶜ : Set ℕ) H).map H.subtype).map
      (QuotientGroup.mk' (piCore ({p}ᶜ : Set ℕ) G)) ≤ Subgroup.normalizer (P : Set _) := by
    rw [← hHP]
    exact Subgroup.map_mono hQ'le
  have hQbarn : ((((piCore ({p}ᶜ : Set ℕ) H).map H.subtype).map
      (QuotientGroup.mk' (piCore ({p}ᶜ : Set ℕ) G))).subgroupOf
        (Subgroup.normalizer (P : Set _))).Normal := by
    refine ⟨fun n hn g ↦ ?_⟩
    obtain ⟨q, hq, hqn⟩ := hn
    have hg : (g : G ⧸ piCore ({p}ᶜ : Set ℕ) G) ∈ H.map
        (QuotientGroup.mk' (piCore ({p}ᶜ : Set ℕ) G)) := by rw [hHP]; exact g.2
    obtain ⟨h, hh, hgh⟩ := hg
    refine ⟨h * q * h⁻¹, hQ'n h hh q hq, ?_⟩
    simp only [Subgroup.coe_subtype, map_mul, map_inv, hgh, hqn]
  have hQbarpi : IsPiGroup ({p}ᶜ : Set ℕ) ((((piCore ({p}ᶜ : Set ℕ) H).map H.subtype).map
      (QuotientGroup.mk' (piCore ({p}ᶜ : Set ℕ) G)))) :=
    IsPiGroup.map (isPiGroup_piCore.of_equiv
      ((piCore ({p}ᶜ : Set ℕ) H).equivMapOfInjective _ H.subtype_injective)) _
  -- hence it lies in `O_p'(H̄) = 1`
  have hbot : (((piCore ({p}ᶜ : Set ℕ) H).map H.subtype).map
      (QuotientGroup.mk' (piCore ({p}ᶜ : Set ℕ) G))) = ⊥ := by
    have hle := le_piCore (π := ({p}ᶜ : Set ℕ)) hQbarn
      (IsPiGroup.of_equiv hQbarpi (Subgroup.subgroupOfEquivOfLe hQbarle).symm)
    rw [hmain, le_bot_iff] at hle
    have := congrArg (Subgroup.map
      (Subgroup.normalizer (P : Set (G ⧸ piCore ({p}ᶜ : Set ℕ) G))).subtype) hle
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQbarle, Subgroup.map_bot] at this
  -- that is, `O_p'(H) ≤ ker = O_p'(G)`
  have := (Subgroup.map_eq_bot_iff _).mp hbot
  rwa [QuotientGroup.ker_mk'] at this

end PiGroups
