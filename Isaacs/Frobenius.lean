module

public import Isaacs.NormalPComplement
public import Isaacs.SubnormalJoin
public import Mathlib.GroupTheory.Focal

/-!
# Towards Frobenius' normal `p`-complement theorem: Isaacs 5.25–5.28

Isaacs, *Finite Group Theory*, Theorem 5.26 (Frobenius): for a finite group `G` and a prime `p`,
the following are equivalent.

1. `G` has a normal `p`-complement;
2. `N_G(X)` has a normal `p`-complement for every nonidentity `p`-subgroup `X`;
3. `N_G(X) / C_G(X)` is a `p`-group for every `p`-subgroup `X`.

This file proves that equivalence, as `PiGroups.frobenius_tfae`.  `mathlib` supplies the **focal
subgroup theorem** (`Subgroup.commutator_inf_eq_focalSubgroup`) and the transfer map to `P ⧸ P*`
(`Subgroup.transferFocal`), which is what Isaacs' Theorem 5.25 rests on.  The chain is:

* `PiGroups.ControlsFusion`: `H` controls its own fusion in `G` — `G`-conjugate elements of `H`
  are already `H`-conjugate;
* `PiGroups.focalSubgroup_eq_commutator_of_controlsFusion`: under fusion control the focal
  subgroup `P*` is just the derived subgroup `⁅P, P⁆`, so it is proper in `P`;
* `PiGroups.hasNormalPComplement_of_ker_transferFocal`: if the kernel of the transfer
  `G → P ⧸ P*` has a normal `p`-complement, so does `G`.  This is the inductive step of Isaacs
  5.25, and it needs no hypothesis at all — fusion control enters only to make the kernel a
  *proper* subgroup, so that an induction on `|G|` can run;
* `PiGroups.hasNormalPComplement_normalizer` and
  `PiGroups.isPGroup_normalizer_quotient_centralizer` are Isaacs' Lemma 5.27, the easy
  implications (1) ⇒ (2) ⇒ (3);
* `PiGroups.exists_conj_mem_centralizer_inf` is Isaacs' Lemma 5.28: under (3), any two Sylow
  `p`-subgroups `P`, `Q` satisfy `Q = P ^ c` for some `c ∈ C_G(P ⊓ Q)`;
* `PiGroups.controlsFusion_sylow` turns 5.28 into fusion control for a Sylow `p`-subgroup, using
  `N_G(P) = C_G(P) P`;
* `PiGroups.NormalizerQuotientIsPGroup.subgroup` says condition (3) passes to subgroups, which is
  what lets the induction on `|G|` close in
  `PiGroups.hasNormalPComplement_of_normalizerQuotient`.

Nothing here is in `mathlib`: it has Burnside's normal `p`-complement theorem (the special case
where `P` is abelian and central in its normalizer) but not Frobenius'.
-/

@[expose] public section

namespace PiGroups

open scoped commutatorElement

universe u

variable {p : ℕ} {G : Type u} [Group G]

/-!
## Control of fusion
-/

/-- `H` **controls its own fusion** in `G`: two elements of `H` that are conjugate in `G` are
already conjugate in `H`. -/
def ControlsFusion (H : Subgroup G) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, (∃ g : G, y = g * x * g⁻¹) → ∃ u ∈ H, y = u * x * u⁻¹

/-- Under fusion control the focal subgroup collapses to the derived subgroup: every generator
`⁅x, u⁆` of `P*` can be rewritten with `u` taken inside `P`. -/
theorem focalSubgroup_eq_commutator_of_controlsFusion {H : Subgroup G} (h : ControlsFusion H) :
    Subgroup.focalSubgroup H = ⁅H, H⁆ := by
  refine le_antisymm ?_ (Subgroup.commutator_le_focalSubgroup H)
  rw [Subgroup.focalSubgroup_def, Subgroup.closure_le]
  rintro g ⟨hgH, x, hx, u, rfl⟩
  -- `⁅x, u⁆ = x * (u * x⁻¹ * u⁻¹)`, and the second factor is a conjugate of `x⁻¹` lying in `H`
  have hy : u * x⁻¹ * u⁻¹ ∈ H := by
    have h1 : u * x⁻¹ * u⁻¹ = x⁻¹ * ⁅x, u⁆ := by
      rw [commutatorElement_def]
      group
    rw [h1]
    exact mul_mem (inv_mem hx) hgH
  obtain ⟨v, hv, hvy⟩ := h x⁻¹ (inv_mem hx) (u * x⁻¹ * u⁻¹) hy ⟨u, rfl⟩
  have hcomm : ⁅x, u⁆ = ⁅x, v⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    have h2 : u * x⁻¹ * u⁻¹ = v * x⁻¹ * v⁻¹ := hvy
    calc x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
      _ = x * (v * x⁻¹ * v⁻¹) := by rw [h2]
      _ = x * v * x⁻¹ * v⁻¹ := by group
  rw [hcomm]
  exact Subgroup.commutator_mem_commutator hx hv

/-!
## Sylow subgroups of a subgroup, seen in the ambient group
-/

/-!
## Sylow subgroups cover `p`-quotients
-/

/-- If `X ⧸ M` is a `p`-group then a Sylow `p`-subgroup of `X` covers it: `S M = X`.  The index of
`S ⊔ M` divides both the index of `S`, which is prime to `p`, and the index of `M`, which is a
power of `p`. -/
theorem sylow_sup_eq_top [Finite G] [Fact p.Prime] {M S : Subgroup G} [M.Normal]
    (hquot : IsPGroup p (G ⧸ M)) (hSi : ¬ p ∣ S.index) : S ⊔ M = ⊤ := by
  obtain ⟨k, hk⟩ := hquot.exists_card_eq
  have hMindex : M.index = p ^ k := by rw [Subgroup.index_eq_card, hk]
  have h2 : (S ⊔ M).index ∣ p ^ k :=
    hMindex ▸ Subgroup.index_dvd_of_le le_sup_right
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp h2
  have hone : (S ⊔ M).index = 1 := by
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rwa [pow_zero] at hj
    · exact absurd ((dvd_pow_self p hjpos.ne').trans
        (hj ▸ Subgroup.index_dvd_of_le (le_sup_left : S ≤ S ⊔ M))) hSi
  exact Subgroup.index_eq_one.mp hone

/-- Consequently every element of `G` factors as an element of `M` times a Sylow element. -/
theorem exists_mem_sylow_mul [Finite G] [Fact p.Prime] {M S : Subgroup G} [M.Normal]
    (hquot : IsPGroup p (G ⧸ M)) (hSi : ¬ p ∣ S.index) (g : G) :
    ∃ m ∈ M, ∃ s ∈ S, g = m * s := by
  have htop := sylow_sup_eq_top hquot hSi
  have hmem : g ∈ (M ⊔ S : Subgroup G) := by
    rw [sup_comm]
    exact htop ▸ Subgroup.mem_top g
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hmem
  obtain ⟨m, hm, s, hs, hg⟩ := hmem
  exact ⟨m, hm, s, hs, hg.symm⟩

/-!
## The transfer step of Isaacs 5.25
-/

/-- The index of the transfer kernel is `|P : P*|`, a power of `p`. -/
theorem index_ker_transferFocal [Finite G] [Fact p.Prime] (P : Sylow p G) :
    ∃ k : ℕ, ((P : Subgroup G).transferFocal.ker).index = p ^ k := by
  have hiso : Nat.card (G ⧸ (P : Subgroup G).transferFocal.ker)
      = Nat.card (↥(P : Subgroup G) ⧸ (P : Subgroup G).focalSubgroupOf) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (Subgroup.transferFocal_surjective P)).toEquiv
  obtain ⟨k, hk⟩ := (P.isPGroup'.to_quotient (P : Subgroup G).focalSubgroupOf).exists_card_eq
  exact ⟨k, by rw [Subgroup.index_eq_card, hiso, hk]⟩

/-- **The inductive step of Isaacs 5.25.**  If the kernel `K` of the transfer `G → P ⧸ P*` has a
normal `p`-complement, then so does `G`.

The `p'`-core `R` of `K` is characteristic in `K ⊴ G`, hence normal in `G`, and
`[G : R] = [K : R] · [G : K]` is a product of two powers of `p`. -/
theorem hasNormalPComplement_of_ker_transferFocal [Finite G] [Fact p.Prime] (P : Sylow p G)
    (hK : HasNormalPComplement p ↥((P : Subgroup G).transferFocal.ker)) :
    HasNormalPComplement p G := by
  have hRquot : IsPGroup p (↥((P : Subgroup G).transferFocal.ker) ⧸
      piCore ({p}ᶜ : Set ℕ) ↥((P : Subgroup G).transferFocal.ker)) :=
    hasNormalPComplement_iff.mp hK
  refine ⟨(piCore ({p}ᶜ : Set ℕ) ↥((P : Subgroup G).transferFocal.ker)).map
    ((P : Subgroup G).transferFocal.ker).subtype, inferInstance, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective
      ((P : Subgroup G).transferFocal.ker).subtype_injective]
    exact not_dvd_card_piCore_compl
  · -- `[G : R] = [K : R] * [G : K]`, a power of `p`
    have hrel : ((piCore ({p}ᶜ : Set ℕ) ↥((P : Subgroup G).transferFocal.ker)).map
        ((P : Subgroup G).transferFocal.ker).subtype).relIndex
          ((P : Subgroup G).transferFocal.ker)
        = (piCore ({p}ᶜ : Set ℕ) ↥((P : Subgroup G).transferFocal.ker)).index := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective
          ((P : Subgroup G).transferFocal.ker).subtype_injective]
    have hmul := Subgroup.relIndex_mul_index (Subgroup.map_subtype_le
      (piCore ({p}ᶜ : Set ℕ) ↥((P : Subgroup G).transferFocal.ker)))
    rw [hrel] at hmul
    obtain ⟨a, ha⟩ := hRquot.exists_card_eq
    obtain ⟨b, hb⟩ := index_ker_transferFocal P
    refine IsPGroup.of_card (n := a + b) ?_
    rw [← Subgroup.index_eq_card, ← hmul, hb, Subgroup.index_eq_card, ha, pow_add]

/-!
## Isaacs' Lemma 5.27: the easy implications
-/

/-- **Isaacs 5.27, (1) ⇒ (2).**  If `G` has a normal `p`-complement, so does every subgroup — in
particular every normalizer. -/
theorem hasNormalPComplement_normalizer (h : HasNormalPComplement p G) (X : Subgroup G) :
    HasNormalPComplement p ↥(Subgroup.normalizer (X : Set G)) :=
  h.subgroup _

/-- **Isaacs 5.27, (2) ⇒ (3).**  If `N_G(X)` has a normal `p`-complement `K`, then `K` centralizes
the `p`-subgroup `X`, because `⁅X, K⁆ ≤ X ⊓ K = 1`; so `N_G(X) / C_G(X)` is a `p`-group. -/
theorem isPGroup_normalizer_quotient_centralizer [Finite G] [Fact p.Prime] {X : Subgroup G}
    (hX : IsPGroup p X) (h : HasNormalPComplement p ↥(Subgroup.normalizer (X : Set G))) :
    IsPGroup p (↥(Subgroup.normalizer (X : Set G)) ⧸
      (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))) := by
  obtain ⟨K, hKnormal, hKcard, hKquot⟩ := h
  have := hKnormal
  have hXN : X ≤ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer
  have hXnormal : (X.subgroupOf (Subgroup.normalizer (X : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXN).mpr le_rfl
  have hXp : IsPGroup p (X.subgroupOf (Subgroup.normalizer (X : Set G))) :=
    hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXN).symm
  have hKC : K ≤ (Subgroup.centralizer (X : Set G)).subgroupOf
      (Subgroup.normalizer (X : Set G)) := by
    intro k hk
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro y hy
    have hyN : y ∈ Subgroup.normalizer (X : Set G) := hXN hy
    have hx' : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (X : Set G)))
        ∈ X.subgroupOf (Subgroup.normalizer (X : Set G)) := by
      rwa [Subgroup.mem_subgroupOf]
    -- the commutator of `y` with `k` lies in `K` and in `X`, hence is trivial
    have hc1 : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (X : Set G))) * k *
        (⟨y, hyN⟩ : ↥(Subgroup.normalizer (X : Set G)))⁻¹ * k⁻¹ ∈ K :=
      mul_mem (hKnormal.conj_mem k hk ⟨y, hyN⟩) (inv_mem hk)
    have hc2 : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (X : Set G))) * k *
        (⟨y, hyN⟩ : ↥(Subgroup.normalizer (X : Set G)))⁻¹ * k⁻¹
        ∈ X.subgroupOf (Subgroup.normalizer (X : Set G)) := by
      have h1 : k * (⟨y, hyN⟩ : ↥(Subgroup.normalizer (X : Set G)))⁻¹ * k⁻¹
          ∈ X.subgroupOf (Subgroup.normalizer (X : Set G)) :=
        hXnormal.conj_mem _ (inv_mem hx') k
      have h2 : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (X : Set G))) * k *
          (⟨y, hyN⟩ : ↥(Subgroup.normalizer (X : Set G)))⁻¹ * k⁻¹
          = (⟨y, hyN⟩ : ↥(Subgroup.normalizer (X : Set G))) *
            (k * (⟨y, hyN⟩ : ↥(Subgroup.normalizer (X : Set G)))⁻¹ * k⁻¹) := by group
      rw [h2]
      exact mul_mem hx' h1
    have hone := eq_one_of_mem_of_mem hKcard hXp hc1 hc2
    have h3 : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (X : Set G))) * k *
        (⟨y, hyN⟩ : ↥(Subgroup.normalizer (X : Set G)))⁻¹ = k := mul_inv_eq_one.mp hone
    have h4 := congrArg (Subtype.val) h3
    push_cast at h4
    calc y * (k : G) = (y * (k : G) * y⁻¹) * y := by group
      _ = (k : G) * y := by rw [h4]
  exact hKquot.of_surjective
    (QuotientGroup.map K _ (MonoidHom.id ↥(Subgroup.normalizer (X : Set G)))
      (by simpa using hKC))
    (by rintro ⟨x⟩; exact ⟨QuotientGroup.mk x, rfl⟩)

/-!
## Isaacs' Lemma 5.28
-/

/-- Normalizers grow: a proper subgroup of a `p`-group is proper in the part of its normalizer
lying in that `p`-group. -/
theorem lt_inf_normalizer [Finite G] [Fact p.Prime] {P D : Subgroup G} (hP : IsPGroup p P)
    (hDP : D < P) : D < P ⊓ Subgroup.normalizer (D : Set G) := by
  have hDle : D ≤ P := hDP.le
  have hnil : Group.IsNilpotent ↥P := hP.isNilpotent
  have hlt : D.subgroupOf P < ⊤ :=
    lt_of_le_of_ne le_top fun htop =>
      absurd (Subgroup.subgroupOf_eq_top.mp htop) (not_le_of_gt hDP)
  obtain ⟨x, hxnorm, hxnot⟩ :=
    SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := ↥P) _ hlt)
  refine lt_of_le_of_ne (le_inf hDle Subgroup.le_normalizer) fun heq => hxnot ?_
  have hxN : (x : G) ∈ Subgroup.normalizer (D : Set G) :=
    mem_normalizer_of_mem_normalizer_subgroupOf hDle x.2 hxnorm
  have hxD : (x : G) ∈ D := heq.ge (Subgroup.mem_inf.mpr ⟨x.2, hxN⟩)
  rwa [Subgroup.mem_subgroupOf]

/-- **Isaacs, Lemma 5.28.**  If `N_G(X) / C_G(X)` is a `p`-group for every `p`-subgroup `X`, then
any two Sylow `p`-subgroups are conjugate by an element centralizing their intersection.

Induction on `|P ⊓ Q|`.  With `D = P ⊓ Q` proper in both, `N = N_G(D)` and `C = C_G(D)`, choose
Sylow `p`-subgroups `S ⊇ P ⊓ N` and `T ⊇ Q ⊓ N` of `N`, and `R ∈ Syl_p(G)` above `S`.  Since
`N = S C`, `T = S ^ y` for some `y ∈ C`.  Normalizers grow, so `P ⊓ R` and `R ^ y ⊓ Q` are both
strictly larger than `D`, and induction conjugates `P` to `R` and `R ^ y` to `Q` by elements
centralizing `D`. -/
theorem exists_conj_mem_centralizer_inf [Finite G] [Fact p.Prime]
    (h3 : ∀ X : Subgroup G, IsPGroup p X →
      IsPGroup p (↥(Subgroup.normalizer (X : Set G)) ⧸
        (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))))
    (P Q : Sylow p G) :
    ∃ c ∈ Subgroup.centralizer (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G),
      (Q : Subgroup G) = (P : Subgroup G).map (MulAut.conj c).toMonoidHom := by
  have key : ∀ (n : ℕ) (P Q : Sylow p G),
      Nat.card G - Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) ≤ n →
      ∃ c ∈ Subgroup.centralizer (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G),
        (Q : Subgroup G) = (P : Subgroup G).map (MulAut.conj c).toMonoidHom := by
    intro n
    induction n with
    | zero =>
      intro P Q hcard
      have h1 : Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) ≤ Nat.card G :=
        Subgroup.card_le_card_group _
      have h2 : (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (by omega)
      have hP : (P : Subgroup G) = ⊤ := top_le_iff.mp (h2 ▸ inf_le_left)
      have hQ : (Q : Subgroup G) = ⊤ := top_le_iff.mp (h2 ▸ inf_le_right)
      exact ⟨1, one_mem _, by rw [hP, hQ, map_conj_eq_self_iff.mpr (one_mem _)]⟩
    | succ n ih =>
      intro P Q hcard
      rcases eq_or_ne (P : Subgroup G) (Q : Subgroup G) with heq | hne
      · exact ⟨1, one_mem _, by rw [heq, map_conj_eq_self_iff.mpr (one_mem _)]⟩
      have hcardeq : Nat.card ↥(P : Subgroup G) = Nat.card ↥(Q : Subgroup G) := by
        rw [P.card_eq_multiplicity, Q.card_eq_multiplicity]
      have hDP : (P : Subgroup G) ⊓ (Q : Subgroup G) < (P : Subgroup G) :=
        lt_of_le_of_ne inf_le_left fun heq2 =>
          hne (Subgroup.eq_of_le_of_card_ge (heq2 ▸ inf_le_right) hcardeq.ge)
      have hDQ : (P : Subgroup G) ⊓ (Q : Subgroup G) < (Q : Subgroup G) :=
        lt_of_le_of_ne inf_le_right fun heq2 =>
          hne (Subgroup.eq_of_le_of_card_ge (heq2 ▸ inf_le_left) hcardeq.le).symm
      have hDp : IsPGroup p ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) :=
        P.isPGroup'.to_le inf_le_left
      have hquot := h3 ((P : Subgroup G) ⊓ (Q : Subgroup G)) hDp
      -- normalizers grow inside `P` and inside `Q`
      have hPN := lt_inf_normalizer P.isPGroup' hDP
      have hQN := lt_inf_normalizer Q.isPGroup' hDQ
      -- Sylow `p`-subgroups of `N` containing `P ⊓ N` and `Q ⊓ N`
      obtain ⟨S, hPNS, hSN, hSp, hSi⟩ :=
        exists_sylow_le_of_le
          (H := Subgroup.normalizer (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G))
          (X := (P : Subgroup G) ⊓
            Subgroup.normalizer (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G))
          inf_le_right (P.isPGroup'.to_le inf_le_left)
      obtain ⟨T, hQNT, hTN, hTp, hTi⟩ :=
        exists_sylow_le_of_le
          (H := Subgroup.normalizer (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G))
          (X := (Q : Subgroup G) ⊓
            Subgroup.normalizer (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G))
          inf_le_right (Q.isPGroup'.to_le inf_le_left)
      obtain ⟨R, hSR⟩ := hSp.exists_le_sylow
      -- `T = S ^ m` for some `m ∈ N`, and `m` may be adjusted to lie in `C`
      obtain ⟨m, hmN, hTeq⟩ := exists_conj_of_sylow_le hSN hTN hSp hTp hSi hTi
      obtain ⟨y, hyC, s, hsS, hm⟩ :=
        exists_mem_sylow_mul (G := ↥(Subgroup.normalizer
            (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G)))
          (M := (Subgroup.centralizer (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) :
            Set G)).subgroupOf _)
          (S := S.subgroupOf _) hquot hSi ⟨m, hmN⟩
      have hmval : m = (y : G) * (s : G) := congrArg Subtype.val hm
      have hyCG : (y : G) ∈ Subgroup.centralizer
          (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G) := hyC
      have hsSG : (s : G) ∈ S := hsS
      -- so `T = S ^ y`
      have hTy : T = S.map (MulAut.conj (y : G)).toMonoidHom := by
        rw [hTeq, hmval]
        have hconj : (MulAut.conj ((y : G) * (s : G))).toMonoidHom
            = (MulAut.conj (y : G)).toMonoidHom.comp (MulAut.conj (s : G)).toMonoidHom :=
          MonoidHom.ext fun w => by simp [MulAut.conj_apply, mul_assoc]
        rw [hconj, ← Subgroup.map_map, map_conj_eq_self_iff.mpr (Subgroup.le_normalizer hsSG)]
      -- induction for the pair `(P, R)`
      have hPR : (P : Subgroup G) ⊓ (Q : Subgroup G) < (P : Subgroup G) ⊓ (R : Subgroup G) :=
        lt_of_lt_of_le hPN (le_inf inf_le_left (hPNS.trans hSR))
      have hcardPR := card_lt_card_of_lt hPR
      have hRle : Nat.card ↥((P : Subgroup G) ⊓ (R : Subgroup G)) ≤ Nat.card G :=
        Subgroup.card_le_card_group _
      obtain ⟨x, hxC, hxR⟩ := ih P R (by omega)
      -- induction for the pair `(y • R, Q)`
      have hyR : ((y : G) • R : Sylow p G) = (y : G) • R := rfl
      have hcoeR : (((y : G) • R : Sylow p G) : Subgroup G)
          = (R : Subgroup G).map (MulAut.conj (y : G)).toMonoidHom := rfl
      have hQR : (P : Subgroup G) ⊓ (Q : Subgroup G) <
          (((y : G) • R : Sylow p G) : Subgroup G) ⊓ (Q : Subgroup G) := by
        refine lt_of_lt_of_le hQN (le_inf ?_ inf_le_left)
        calc (Q : Subgroup G) ⊓ Subgroup.normalizer
              (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G) ≤ T := hQNT
          _ = S.map (MulAut.conj (y : G)).toMonoidHom := hTy
          _ ≤ (R : Subgroup G).map (MulAut.conj (y : G)).toMonoidHom := Subgroup.map_mono hSR
          _ = (((y : G) • R : Sylow p G) : Subgroup G) := hcoeR.symm
      have hcardQR := card_lt_card_of_lt hQR
      have hQRle : Nat.card ↥((((y : G) • R : Sylow p G) : Subgroup G) ⊓ (Q : Subgroup G))
          ≤ Nat.card G := Subgroup.card_le_card_group _
      obtain ⟨z, hzC, hzQ⟩ := ih ((y : G) • R) Q (by omega)
      -- assemble
      refine ⟨z * ((y : G) * x), mul_mem ?_ (mul_mem hyCG ?_), ?_⟩
      · exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQR.le) hzC
      · exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPR.le) hxC
      · calc (Q : Subgroup G)
            = (((y : G) • R : Sylow p G) : Subgroup G).map (MulAut.conj z).toMonoidHom := hzQ
          _ = ((R : Subgroup G).map (MulAut.conj (y : G)).toMonoidHom).map
                (MulAut.conj z).toMonoidHom := by rw [hcoeR]
          _ = (((P : Subgroup G).map (MulAut.conj x).toMonoidHom).map
                (MulAut.conj (y : G)).toMonoidHom).map (MulAut.conj z).toMonoidHom := by rw [hxR]
          _ = (P : Subgroup G).map (MulAut.conj (z * ((y : G) * x))).toMonoidHom := by
              rw [Subgroup.map_map, Subgroup.map_map]
              congr 1
              exact MonoidHom.ext fun w => by simp [MulAut.conj_apply, mul_assoc]
  exact key (Nat.card G) P Q (Nat.sub_le _ _)


/-!
## Isaacs 5.26: hypothesis (3) yields fusion control
-/

/-- An element of the centralizer of a set fixes each of its members under conjugation. -/
theorem conj_eq_of_mem_centralizer {S : Set G} {z w : G}
    (hz : z ∈ Subgroup.centralizer S) (hw : w ∈ S) : z * w * z⁻¹ = w := by
  rw [← Subgroup.mem_centralizer_iff.mp hz w hw, mul_assoc, mul_inv_cancel, mul_one]

/-- Under hypothesis (3) a Sylow `p`-subgroup satisfies `N_G(P) = C_G(P) P`.

Indeed `P` is a Sylow `p`-subgroup of `N_G(P)` and `N_G(P) / C_G(P)` is a `p`-group, so `P`
covers that quotient. -/
theorem exists_centralizer_mul_mem_sylow [Finite G] [Fact p.Prime]
    (h3 : ∀ X : Subgroup G, IsPGroup p X →
      IsPGroup p (↥(Subgroup.normalizer (X : Set G)) ⧸
        (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))))
    (P : Sylow p G) {g : G} (hg : g ∈ Subgroup.normalizer (((P : Subgroup G)) : Set G)) :
    ∃ z ∈ Subgroup.centralizer (((P : Subgroup G)) : Set G), ∃ s ∈ (P : Subgroup G),
      g = z * s := by
  have hrel : ((P : Subgroup G).subgroupOf
      (Subgroup.normalizer (((P : Subgroup G)) : Set G))).index ∣ (P : Subgroup G).index :=
    Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer
  have hSi : ¬ p ∣ ((P : Subgroup G).subgroupOf
      (Subgroup.normalizer (((P : Subgroup G)) : Set G))).index := fun hd =>
    P.not_dvd_index (hd.trans hrel)
  obtain ⟨z, hz, s, hs, hzs⟩ :=
    exists_mem_sylow_mul (G := ↥(Subgroup.normalizer (((P : Subgroup G)) : Set G)))
      (M := (Subgroup.centralizer (((P : Subgroup G)) : Set G)).subgroupOf _)
      (S := (P : Subgroup G).subgroupOf _) (h3 (P : Subgroup G) P.isPGroup') hSi ⟨g, hg⟩
  exact ⟨(z : G), hz, (s : G), hs, congrArg Subtype.val hzs⟩

/-- **Isaacs 5.26, the fusion step.**  Under hypothesis (3), a Sylow `p`-subgroup `P` controls
its own fusion in `G`.

If `y = x ^ g` with `x, y ∈ P`, then `y` lies in `P ⊓ P ^ g`, so Lemma 5.28 supplies
`c ∈ C_G(P ^ g ⊓ P)` with `P = (P ^ g) ^ c`.  Thus `c g` normalizes `P` and still conjugates `x`
to `y`, because `c` fixes `y`.  Finally `N_G(P) = C_G(P) P`, and the central factor may be
discarded. -/
theorem controlsFusion_sylow [Finite G] [Fact p.Prime]
    (h3 : ∀ X : Subgroup G, IsPGroup p X →
      IsPGroup p (↥(Subgroup.normalizer (X : Set G)) ⧸
        (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))))
    (P : Sylow p G) : ControlsFusion (P : Subgroup G) := by
  rintro x hx y hy ⟨g, hg⟩
  have hcoe : ((g • P : Sylow p G) : Subgroup G)
      = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := rfl
  have hyQ : y ∈ ((g • P : Sylow p G) : Subgroup G) := by
    rw [hcoe]
    exact ⟨x, hx, hg.symm⟩
  obtain ⟨c, hc, hPQ⟩ := exists_conj_mem_centralizer_inf h3 (g • P) P
  -- `c` fixes `y`, since `y ∈ P ^ g ⊓ P`
  have hcy : c * y * c⁻¹ = y :=
    conj_eq_of_mem_centralizer hc (Subgroup.mem_inf.mpr ⟨hyQ, hy⟩)
  -- `c g` normalizes `P`
  have hmapP : (P : Subgroup G).map (MulAut.conj (c * g)).toMonoidHom = (P : Subgroup G) := by
    have hcomp : (MulAut.conj (c * g)).toMonoidHom
        = (MulAut.conj c).toMonoidHom.comp (MulAut.conj g).toMonoidHom :=
      MonoidHom.ext fun w => by simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, ← Subgroup.map_map, ← hcoe, ← hPQ]
  have hN : c * g ∈ Subgroup.normalizer (((P : Subgroup G)) : Set G) :=
    map_conj_eq_self_iff.mp hmapP
  -- and it still conjugates `x` to `y`
  have hcg : y = (c * g) * x * (c * g)⁻¹ := by
    rw [← hcy, hg]
    group
  -- discard the central factor of `c g`
  obtain ⟨z, hz, s, hs, hzs⟩ := exists_centralizer_mul_mem_sylow h3 P hN
  refine ⟨s, hs, ?_⟩
  have hw : s * x * s⁻¹ ∈ (P : Subgroup G) := mul_mem (mul_mem hs hx) (inv_mem hs)
  calc y = (c * g) * x * (c * g)⁻¹ := hcg
    _ = z * (s * x * s⁻¹) * z⁻¹ := by rw [hzs]; group
    _ = s * x * s⁻¹ := conj_eq_of_mem_centralizer hz hw

/-!
## Passing the hypotheses of 5.26 to subgroups
-/

/-- A group of order prime to `p` is its own normal `p`-complement. -/
theorem hasNormalPComplement_of_not_dvd [Finite G] (h : ¬ p ∣ Nat.card G) :
    HasNormalPComplement p G := by
  refine ⟨⊤, inferInstance, ?_, ?_⟩
  · rwa [Subgroup.card_top]
  · exact IsPGroup.of_card (n := 0) (by
      rw [pow_zero, ← Subgroup.index_eq_card, Subgroup.index_top])

/-- A normal `p`-complement in `K` induces one in the copy of `K` inside another subgroup. -/
theorem hasNormalPComplement_subgroupOf {K H : Subgroup G} (h : HasNormalPComplement p ↥K) :
    HasNormalPComplement p ↥(K.subgroupOf H) := by
  have h2 : HasNormalPComplement p ↥(K ⊓ H : Subgroup G) :=
    (h.subgroup ((K ⊓ H : Subgroup G).subgroupOf K)).of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ H ≤ K))
  have e : ↥(K.subgroupOf H) ≃* ↥(K ⊓ H : Subgroup G) := by
    rw [← Subgroup.subgroupOf_map_subtype K H]
    exact Subgroup.equivMapOfInjective _ _ H.subtype_injective
  exact h2.of_mulEquiv e.symm

/-- Membership in the image of a subgroup of `H` under the inclusion, tested on `H`. -/
theorem mem_map_subtype_iff {H : Subgroup G} (Y : Subgroup ↑H) (n : ↑H) :
    (n : G) ∈ Y.map H.subtype ↔ n ∈ Y := by
  rw [← Subgroup.mem_subgroupOf, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective]

/-- The normalizer computed inside a subgroup `H` is the restriction to `H` of the ambient
normalizer of the image. -/
theorem normalizer_map_subtype {H : Subgroup G} (Y : Subgroup ↑H) :
    (Subgroup.normalizer ((Y.map H.subtype : Subgroup G) : Set G)).subgroupOf H
      = Subgroup.normalizer ((Y : Set ↑H)) := by
  have hle : ∀ g : G, g ∈ Y.map H.subtype → g ∈ H := fun g hg => Subgroup.map_subtype_le _ hg
  ext h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_set_normalizer_iff, Subgroup.mem_set_normalizer_iff]
  simp only [SetLike.mem_coe]
  constructor
  · intro hh n
    rw [← mem_map_subtype_iff Y n, ← mem_map_subtype_iff Y (h * n * h⁻¹)]
    push_cast
    exact hh (n : G)
  · intro hh g
    by_cases hgH : g ∈ H
    · have h1 := hh ⟨g, hgH⟩
      rw [← mem_map_subtype_iff Y ⟨g, hgH⟩, ← mem_map_subtype_iff Y (h * ⟨g, hgH⟩ * h⁻¹)] at h1
      push_cast at h1
      exact h1
    · refine ⟨fun hg => absurd (hle g hg) hgH, fun hg => absurd ?_ hgH⟩
      have h2 : (h : G)⁻¹ * ((h : G) * g * (h : G)⁻¹) * (h : G) ∈ H :=
        mul_mem (mul_mem (inv_mem h.2) (hle _ hg)) h.2
      have heqg : (h : G)⁻¹ * ((h : G) * g * (h : G)⁻¹) * (h : G) = g := by group
      rwa [heqg] at h2

/-!
## The three conditions of Isaacs 5.26
-/

/-- **Isaacs 5.26(2).**  The normalizer of every nonidentity `p`-subgroup has a normal
`p`-complement. -/
def NormalizerHasNormalPComplement (p : ℕ) (X : Type u) [Group X] : Prop :=
  ∀ Y : Subgroup X, Y ≠ ⊥ → IsPGroup p Y →
    HasNormalPComplement p ↑(Subgroup.normalizer ((Y : Set X)))

/-- **Isaacs 5.26(3).**  `N_X(Y) / C_X(Y)` is a `p`-group for every `p`-subgroup `Y`. -/
def NormalizerQuotientIsPGroup (p : ℕ) (X : Type u) [Group X] : Prop :=
  ∀ Y : Subgroup X, IsPGroup p Y →
    IsPGroup p (↑(Subgroup.normalizer ((Y : Set X))) ⧸
      (Subgroup.centralizer ((Y : Set X))).subgroupOf (Subgroup.normalizer ((Y : Set X))))

omit [Group G] in
/-- Condition (3) is automatic for the trivial subgroup: `C_G(1) = G`. -/
theorem isPGroup_normalizer_quotient_centralizer_bot [Group G] :
    IsPGroup p (↑(Subgroup.normalizer (((⊥ : Subgroup G)) : Set G)) ⧸
      (Subgroup.centralizer (((⊥ : Subgroup G)) : Set G)).subgroupOf
        (Subgroup.normalizer (((⊥ : Subgroup G)) : Set G))) := by
  have htop : (Subgroup.centralizer (((⊥ : Subgroup G)) : Set G)).subgroupOf
      (Subgroup.normalizer (((⊥ : Subgroup G)) : Set G)) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, -⟩ -
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hy
    simp [hy]
  refine IsPGroup.of_card (n := 0) ?_
  rw [pow_zero, ← Subgroup.index_eq_card, htop, Subgroup.index_top]

/-- **Isaacs 5.27, (2) ⇒ (3)**, in the packaged form. -/
theorem normalizerQuotientIsPGroup_of_normalizerHasNormalPComplement [Finite G] [Fact p.Prime]
    (h2 : NormalizerHasNormalPComplement p G) : NormalizerQuotientIsPGroup p G := by
  intro Y hY
  rcases eq_or_ne Y ⊥ with rfl | hne
  · exact isPGroup_normalizer_quotient_centralizer_bot
  · exact isPGroup_normalizer_quotient_centralizer hY (h2 Y hne hY)

/-- The centralizer computed inside a subgroup `H` is the restriction to `H` of the ambient
centralizer of the image. -/
theorem centralizer_map_subtype {H : Subgroup G} (Y : Subgroup ↑H) :
    (Subgroup.centralizer ((Y.map H.subtype : Subgroup G) : Set G)).subgroupOf H
      = Subgroup.centralizer ((Y : Set ↑H)) := by
  ext h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  simp only [SetLike.mem_coe]
  constructor
  · intro hh n hn
    have h1 := hh (n : G) ((mem_map_subtype_iff Y n).mpr hn)
    exact Subtype.ext (by push_cast; exact h1)
  · intro hh g hg
    have hgH : g ∈ H := Subgroup.map_subtype_le _ hg
    have h1 := hh ⟨g, hgH⟩ ((mem_map_subtype_iff Y ⟨g, hgH⟩).mp hg)
    exact congrArg Subtype.val h1

/-- Transport of the `p`-group condition on a quotient along a homomorphism that pulls the
normal subgroup back correctly: `A ⧸ M` then embeds into `B ⧸ N`. -/
theorem isPGroup_quotient_of_comap {A B : Type*} [Group A] [Group B]
    {M : Subgroup A} [M.Normal] {N : Subgroup B} [N.Normal] (hB : IsPGroup p (B ⧸ N))
    (f : A →* B) (hMN : M = N.comap f) :
    IsPGroup p (A ⧸ M) := by
  have hker : ((QuotientGroup.mk' N).comp f).ker = M := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hMN]
  have hp : IsPGroup p (A ⧸ ((QuotientGroup.mk' N).comp f).ker) :=
    hB.of_injective _ (QuotientGroup.kerLift_injective _)
  exact hp.of_equiv (QuotientGroup.quotientMulEquivOfEq hker)

/-- Condition (3) passes to subgroups: `N_H(Y) / C_H(Y)` embeds in `N_G(Y) / C_G(Y)`. -/
theorem NormalizerQuotientIsPGroup.subgroup
    (h : NormalizerQuotientIsPGroup p G) (H : Subgroup G) :
    NormalizerQuotientIsPGroup p ↑H := by
  intro Y hYp
  have hN : (Subgroup.normalizer ((Y.map H.subtype : Subgroup G) : Set G)).subgroupOf H
      = Subgroup.normalizer ((Y : Set ↑H)) := normalizer_map_subtype Y
  have hC : (Subgroup.centralizer ((Y.map H.subtype : Subgroup G) : Set G)).subgroupOf H
      = Subgroup.centralizer ((Y : Set ↑H)) := centralizer_map_subtype Y
  have hmem : ∀ x : ↑(Subgroup.normalizer ((Y : Set ↑H))),
      ((x : ↑H) : G) ∈ Subgroup.normalizer ((Y.map H.subtype : Subgroup G) : Set G) := by
    intro x
    have h1 : (x : ↑H) ∈ (Subgroup.normalizer
        ((Y.map H.subtype : Subgroup G) : Set G)).subgroupOf H := by rw [hN]; exact x.2
    exact Subgroup.mem_subgroupOf.mp h1
  refine isPGroup_quotient_of_comap (h (Y.map H.subtype) (hYp.map _))
    { toFun := fun x => ⟨((x : ↑H) : G), hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl } ?_
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, ← hC,
    Subgroup.mem_subgroupOf]
  exact Iff.rfl

/-- Condition (2) passes to subgroups: `N_H(Y)` is the part of `N_G(Y)` lying in `H`. -/
theorem NormalizerHasNormalPComplement.subgroup
    (h : NormalizerHasNormalPComplement p G) (H : Subgroup G) :
    NormalizerHasNormalPComplement p ↑H := by
  intro Y hY hYp
  have hmapne : Y.map H.subtype ≠ ⊥ := fun hb =>
    hY ((Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hb)
  have hmapp : IsPGroup p ↑(Y.map H.subtype) := hYp.map _
  rw [← normalizer_map_subtype Y]
  exact hasNormalPComplement_subgroupOf (h (Y.map H.subtype) hmapne hmapp)

/-!
## Isaacs 5.26: the hard implication
-/

/-- The transfer `G → P ⧸ P*` has kernel of index `|P : P*|`. -/
theorem index_ker_transferFocal_eq [Finite G] [Fact p.Prime] (P : Sylow p G) :
    ((P : Subgroup G).transferFocal.ker).index
      = (Subgroup.focalSubgroupOf (P : Subgroup G)).index := by
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (Subgroup.transferFocal_surjective P)).toEquiv

/-- Under fusion control the focal subgroup of `P`, viewed inside `P`, is the derived subgroup
of `P`. -/
theorem focalSubgroupOf_eq_commutator_of_controlsFusion {H : Subgroup G}
    (h : ControlsFusion H) : Subgroup.focalSubgroupOf H = commutator ↑H := by
  rw [← Subgroup.map_subtype_inj, Subgroup.map_focalSubgroupOf,
    focalSubgroup_eq_commutator_of_controlsFusion h, Subgroup.map_subtype_commutator]

/-- **Isaacs 5.26, (3) ⇒ (1).**

Induction on `|G|`.  A Sylow `p`-subgroup `P` controls its own fusion by 5.28, so
`P* = ⁅P, P⁆` is proper in `P` and the transfer kernel `K` is a proper subgroup.  Condition (3)
passes to `K`, so `K` has a normal `p`-complement by induction, and then so does `G`. -/
theorem hasNormalPComplement_of_normalizerQuotient [Finite G] [Fact p.Prime]
    (h3 : NormalizerQuotientIsPGroup p G) : HasNormalPComplement p G := by
  have key : ∀ (X : Type u) [Group X] [Finite X],
      NormalizerQuotientIsPGroup p X → HasNormalPComplement p X := by
    refine induction_on_card ?_
    intro X _ _ ih h3
    by_cases hdvd : p ∣ Nat.card X
    · obtain ⟨P⟩ : Nonempty (Sylow p X) := inferInstance
      -- `P` is nontrivial
      have hfac : 0 < (Nat.card X).factorization p :=
        Nat.Prime.factorization_pos_of_dvd Fact.out (Nat.card_pos).ne' hdvd
      have hPne : (P : Subgroup X) ≠ ⊥ := by
        intro hb
        have h1 : Nat.card ↑(P : Subgroup X) = p ^ (Nat.card X).factorization p :=
          P.card_eq_multiplicity
        rw [hb, Subgroup.card_bot] at h1
        exact absurd h1.symm (Nat.one_lt_pow hfac.ne' (Fact.out : p.Prime).one_lt).ne'
      have hnt : Nontrivial ↑(P : Subgroup X) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hPne
      have hnilP : Group.IsNilpotent ↑(P : Subgroup X) := P.isPGroup'.isNilpotent
      -- fusion control, hence `P* = ⁅P, P⁆ < P`
      have hfoc : Subgroup.focalSubgroupOf (P : Subgroup X) = commutator ↑(P : Subgroup X) :=
        focalSubgroupOf_eq_commutator_of_controlsFusion (controlsFusion_sylow h3 P)
      have hfocne : Subgroup.focalSubgroupOf (P : Subgroup X) ≠ ⊤ := by
        rw [hfoc]
        exact (Group.IsSolvable.commutator_lt_top_of_nontrivial
          (G := ↑(P : Subgroup X))).ne
      -- so the transfer kernel is proper
      have hidx : 1 < ((P : Subgroup X).transferFocal.ker).index := by
        rw [index_ker_transferFocal_eq]
        have h0 : (Subgroup.focalSubgroupOf (P : Subgroup X)).index ≠ 0 :=
          Subgroup.index_ne_zero_of_finite
        have h1 : (Subgroup.focalSubgroupOf (P : Subgroup X)).index ≠ 1 := fun he =>
          hfocne (Subgroup.index_eq_one.mp he)
        omega
      have hmul := Subgroup.card_mul_index ((P : Subgroup X).transferFocal.ker)
      have hlt : Nat.card ↑((P : Subgroup X).transferFocal.ker) < Nat.card X := by
        rw [← hmul]
        exact (Nat.lt_mul_iff_one_lt_right Nat.card_pos).mpr hidx
      exact hasNormalPComplement_of_ker_transferFocal P
        (ih _ (by omega) (h3.subgroup _))
    · exact hasNormalPComplement_of_not_dvd hdvd
  exact key G h3

/-- **Isaacs, Theorem 5.26 (Frobenius' normal `p`-complement theorem).**  For a finite group `G`
and a prime `p` the following are equivalent.

1. `G` has a normal `p`-complement;
2. `N_G(X)` has a normal `p`-complement for every nonidentity `p`-subgroup `X`;
3. `N_G(X) / C_G(X)` is a `p`-group for every `p`-subgroup `X`. -/
theorem frobenius_tfae [Finite G] [Fact p.Prime] :
    List.TFAE [HasNormalPComplement p G, NormalizerHasNormalPComplement p G,
      NormalizerQuotientIsPGroup p G] := by
  tfae_have 1 → 2 := fun h X _ _ => hasNormalPComplement_normalizer h X
  tfae_have 2 → 3 := normalizerQuotientIsPGroup_of_normalizerHasNormalPComplement
  tfae_have 3 → 1 := hasNormalPComplement_of_normalizerQuotient
  tfae_finish

/-- **Isaacs 5.26, (2) ⇒ (1).** -/
theorem hasNormalPComplement_of_normalizer [Finite G] [Fact p.Prime]
    (h2 : NormalizerHasNormalPComplement p G) : HasNormalPComplement p G :=
  hasNormalPComplement_of_normalizerQuotient
    (normalizerQuotientIsPGroup_of_normalizerHasNormalPComplement h2)

end PiGroups
