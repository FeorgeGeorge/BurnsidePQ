module

public import Isaacs.BaerTheorem

/-!
# Isaacs' Theorem 2.13, and Step 7 of Burnside's theorem

Isaacs, *Finite Group Theory*, Theorem 2.13: if `t` is an involution of a finite group `X` lying
in no normal `2`-subgroup, then `t` inverts some element of odd prime order.  This is the
hypothesis `Burnside.InvolutionInvertsElement` carried by Step 7 of Burnside's `p ^ a q ^ b`
theorem; `PiGroups.involutionInvertsElement` discharges it, so Step 7 — and with it everything
proved about the minimal counterexample — no longer rests on an unproved statement.

The proof is Isaacs'.  If `⟨t⟩ ≤ F(X)` then `t` lies in the Sylow `2`-subgroup of the nilpotent
group `F(X)`, which is `O_2(F(X))`, a characteristic subgroup of a normal subgroup and hence a
normal `2`-subgroup of `X`; that puts `t` in `O_2(X)`, against the hypothesis.  So Baer's Theorem
2.12 (`PiGroups.le_fitting_iff_isNilpotent_sup_conj`) produces `g` with `⟨t, t ^ g⟩` not nilpotent.
Writing `u = t ^ g` and `c = t u`, the involution `t` inverts `c`, so `⟨t, u⟩ = ⟨c⟩ ⊔ ⟨t⟩` with
`⟨c⟩` normalized by `t`.  Were `⟨c⟩` a `2`-group, that join would be one too, hence nilpotent; so
some odd prime `r` divides `|⟨c⟩|`, and Cauchy's theorem inside `⟨c⟩` gives an element of order `r`
inverted by `t`.

This is Isaacs' Lemma 2.14 in the only form needed: the dihedral structure of `⟨t, u⟩` is not
required, just that `t` inverts `t u` and that `⟨t, u⟩ = ⟨t u⟩ ⊔ ⟨t⟩`.
-/

@[expose] public section

universe u

namespace Burnside

/-- **Isaacs, Theorem 2.13.**  If `t` is an involution of a finite group `X` that lies in no
normal `2`-subgroup, then `t` inverts some element of odd prime order.

It is carried as an explicit hypothesis on the statements of `Isaacs/BurnsidePQTheorem.lean`
that need it, exactly like `CoprimeAction.SchurZassenhausConjugacy`, so that every one of them
says so; `PiGroups.involutionInvertsElement` below discharges it, along Isaacs' route: Baer's
Theorem 2.12 (`PiGroups.le_fitting_iff_isNilpotent_sup_conj`) through Wielandt's join theorem
2.5 and zipper lemma 2.9.

It is stated here rather than with Burnside's theorem only so that this file need not import
that one: the definition is what Step 7 consumes, and this file is what produces it.

The hypothesis `t ∉ O_2(X)` is Isaacs'; in the application `X` is simple and nonabelian, so
`O_2(X) = 1` and it just says `t ≠ 1`. -/
def InvolutionInvertsElement : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (t : X), orderOf t = 2 →
      t ∉ PiGroups.piCore ({2} : Set ℕ) X →
    ∃ (r : ℕ) (x : X), r.Prime ∧ r ≠ 2 ∧ orderOf x = r ∧ t * x * t⁻¹ = x⁻¹

end Burnside

namespace PiGroups

variable {G : Type u} [Group G]

/-!
## Two involutions
-/

omit [Group G] in
/-- An involution inverts the product of itself with any other involution. -/
theorem inv_conj_of_involutions [Group G] {t u : G} (htt : t * t = 1) (huu : u * u = 1) :
    t * (t * u) * t⁻¹ = (t * u)⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  rw [mul_inv_rev, huinv, htinv]
  calc t * (t * u) * t = (t * t) * (u * t) := by group
    _ = u * t := by rw [htt, one_mul]

/-- It therefore inverts every element of the cyclic group that product generates. -/
theorem inv_conj_zpowers_of_involutions {t u : G} (htt : t * t = 1) (huu : u * u = 1) {w : G}
    (hw : w ∈ Subgroup.zpowers (t * u)) : t * w * t⁻¹ = w⁻¹ := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have h1 : (MulAut.conj t) ((t * u) ^ n) = ((MulAut.conj t) (t * u)) ^ n := map_zpow _ _ _
  have h2 : (MulAut.conj t) (t * u) = (t * u)⁻¹ := inv_conj_of_involutions htt huu
  change (MulAut.conj t) ((t * u) ^ n) = ((t * u) ^ n)⁻¹
  rw [h1, h2, inv_zpow]

/-- Two involutions generate the same subgroup as their product together with the first. -/
theorem zpowers_sup_zpowers_eq {t u : G} (htt : t * t = 1) :
    Subgroup.zpowers t ⊔ Subgroup.zpowers u
      = Subgroup.zpowers (t * u) ⊔ Subgroup.zpowers t := by
  refine le_antisymm (sup_le le_sup_right ?_) (sup_le ?_ le_sup_left)
  · rw [Subgroup.zpowers_le]
    have hmem : t * (t * u) ∈ Subgroup.zpowers (t * u) ⊔ Subgroup.zpowers t :=
      mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers (t * u)))
    have heq : t * (t * u) = u := by
      calc t * (t * u) = (t * t) * u := by group
        _ = u := by rw [htt, one_mul]
    simpa only [heq] using hmem
  · rw [Subgroup.zpowers_le]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))

/-!
## Isaacs' Theorem 2.13
-/

/-- In a finite nilpotent group every `p`-subgroup lies in the `p`-core: it lies in a Sylow
`p`-subgroup, and those are normal. -/
theorem le_piCore_of_isPGroup [Finite G] [Group.IsNilpotent G] {p : ℕ} (hp : p.Prime)
    {P : Subgroup G} (hP : IsPGroup p P) : P ≤ piCore ({p} : Set ℕ) G := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  exact hPQ.trans (le_piCore inferInstance (IsPGroup.isPiGroup hp Q.isPGroup'))

/-- An involution of the Fitting subgroup lies in `O_2(G)`. -/
theorem mem_piCore_two_of_le_fitting [Finite G] {t : G} (ht : orderOf t = 2)
    (hle : Subgroup.zpowers t ≤ fitting G) : t ∈ piCore ({2} : Set ℕ) G := by
  have htF : t ∈ fitting G := hle (Subgroup.mem_zpowers t)
  have hT2 : IsPGroup 2 ↥((Subgroup.zpowers t).subgroupOf (fitting G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, ht, pow_one]
  have h1 : (Subgroup.zpowers t).subgroupOf (fitting G) ≤ piCore ({2} : Set ℕ) ↥(fitting G) :=
    le_piCore_of_isPGroup Nat.prime_two hT2
  have h2 : (piCore ({2} : Set ℕ) ↥(fitting G)).map (fitting G).subtype
      ≤ piCore ({2} : Set ℕ) G :=
    le_piCore inferInstance (isPiGroup_piCore.of_equiv
      ((piCore ({2} : Set ℕ) ↥(fitting G)).equivMapOfInjective _ (fitting G).subtype_injective))
  exact h2 ⟨⟨t, htF⟩, h1 (Subgroup.mem_zpowers t), rfl⟩

/-- **Isaacs, Theorem 2.13.**  An involution lying in no normal `2`-subgroup inverts an element of
odd prime order. -/
theorem exists_orderOf_prime_ne_two_inverted [Finite G] {t : G} (ht : orderOf t = 2)
    (hO2 : t ∉ piCore ({2} : Set ℕ) G) :
    ∃ (r : ℕ) (x : G), r.Prime ∧ r ≠ 2 ∧ orderOf x = r ∧ t * x * t⁻¹ = x⁻¹ := by
  classical
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rwa [ht, pow_two] at h1
  -- Baer's theorem: some conjugate pair generates a non-nilpotent subgroup
  have hnotle : ¬ (Subgroup.zpowers t ≤ fitting G) := fun h =>
    hO2 (mem_piCore_two_of_le_fitting ht h)
  rw [le_fitting_iff_isNilpotent_sup_conj] at hnotle
  push Not at hnotle
  obtain ⟨g, hg⟩ := hnotle
  obtain ⟨u, hu⟩ : ∃ u : G, u = g * t * g⁻¹ := ⟨_, rfl⟩
  have hmapu : (Subgroup.zpowers t).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers u := by
    rw [hu]
    exact MonoidHom.map_zpowers _ _
  rw [hmapu, zpowers_sup_zpowers_eq htt] at hg
  have huu : u * u = 1 := by
    rw [hu]
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have hinvC : ∀ w ∈ Subgroup.zpowers (t * u), t * w * t⁻¹ = w⁻¹ := fun _ hw =>
    inv_conj_zpowers_of_involutions htt huu hw
  -- `⟨t u⟩` is normalized by `t`
  have hnormC : Subgroup.zpowers t
      ≤ Subgroup.normalizer ((Subgroup.zpowers (t * u) : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le, ← map_conj_eq_self_iff]
    refine Subgroup.eq_of_le_of_card_ge ?_ (le_of_eq (Subgroup.card_map_of_injective
      (K := Subgroup.zpowers (t * u)) (f := (MulAut.conj t).toMonoidHom)
      (MulAut.conj t).injective).symm)
    rintro _ ⟨w, hw, rfl⟩
    change t * w * t⁻¹ ∈ Subgroup.zpowers (t * u)
    rw [hinvC w hw]
    exact inv_mem hw
  -- so `⟨t u⟩` is not a `2`-group
  have hC2 : ¬ IsPGroup 2 ↥(Subgroup.zpowers (t * u)) := by
    intro hC
    have h2 : IsPGroup 2 ↥(Subgroup.zpowers t) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, ht, pow_one]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hg (hC.to_sup_of_normal_left' h2 hnormC).isNilpotent
  -- pick an odd prime divisor of its order and apply Cauchy inside it
  obtain ⟨r, hrmem, hr2⟩ : ∃ r ∈ (Nat.card ↥(Subgroup.zpowers (t * u))).primeFactors, r ≠ 2 := by
    by_contra hcon
    push Not at hcon
    exact hC2 (IsPiGroup.isPGroup (IsPiGroup.iff_card.mpr fun r hr => hcon r hr))
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hrmem
  have : Fact r.Prime := ⟨hrp⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers (t * u))) r
    (Nat.dvd_of_mem_primeFactors hrmem)
  refine ⟨r, (w : G), hrp, hr2, ?_, hinvC (w : G) w.2⟩
  rw [Subgroup.orderOf_coe, hw]

/-- **Isaacs' Theorem 2.13 discharges the hypothesis of Step 7** of Burnside's `p ^ a q ^ b`
theorem: pass `PiGroups.involutionInvertsElement` to `Burnside.IsMinCounterexample.step7`. -/
theorem involutionInvertsElement : Burnside.InvolutionInvertsElement.{u} :=
  fun _X _ _ _t ht hO2 => exists_orderOf_prime_ne_two_inverted ht hO2

end PiGroups
