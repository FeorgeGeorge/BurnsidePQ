module

public import Mathlib.GroupTheory.Commutator.Basic
public import Isaacs.CommutatorAction

/-!
# A `p`-group acting on a `p`-group

Isaacs, *Finite Group Theory*, Lemma 4.32: if the `p`-group `P` acts by automorphisms on a
nontrivial `p`-group `G`, then `⁅G, P⁆ < G` and `C_G(P) > 1`.

Note that there is no coprimality here — both groups are `p`-groups — so, unlike the results in
`Isaacs/GlaubermanLemma.lean` and its consequences, this lemma needs no Schur–Zassenhaus input.

Isaacs' proof of the first statement goes through the semidirect product `Γ = G ⋊ P`, which is a
`p`-group and hence nilpotent, so that iterated commutation with `P` drives `G` down to `1`.  We
follow it, in the form: in a nilpotent group `⁅N, Γ⁆ < N` for every nontrivial normal `N`
(`CoprimeAction.commutator_top_lt`), applied to the copy of `G` inside `Γ`.  For the second
statement we use `mathlib`'s fixed-point theorem for `p`-groups directly, which is shorter than
Isaacs' route through the last nonidentity term of the descending series.
-/

@[expose] public section

namespace CoprimeAction

open scoped commutatorElement

universe u

variable {G A : Type u} [Group G] [Group A] [MulDistribMulAction A G]

/-!
## Nilpotent groups
-/

/-- In a nilpotent group, commutation strictly decreases every nontrivial normal subgroup: if
`⁅N, Γ⁆ = N` then `N` is contained in every term of the lower central series. -/
theorem commutator_top_lt {Γ : Type*} [Group Γ] [Group.IsNilpotent Γ] (N : Subgroup Γ)
    [N.Normal] (hN : N ≠ ⊥) : ⁅N, (⊤ : Subgroup Γ)⁆ < N := by
  refine lt_of_le_of_ne (Subgroup.commutator_le_left N ⊤) fun heq ↦ hN ?_
  obtain ⟨k, hk⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp ‹Group.IsNilpotent Γ›
  have hle : ∀ n, N ≤ Subgroup.lowerCentralSeries (⊤ : Subgroup Γ) n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      calc N = ⁅N, (⊤ : Subgroup Γ)⁆ := heq.symm
        _ ≤ ⁅Subgroup.lowerCentralSeries (⊤ : Subgroup Γ) n, (⊤ : Subgroup Γ)⁆ :=
              Subgroup.commutator_mono ih le_rfl
        _ = Subgroup.lowerCentralSeries (⊤ : Subgroup Γ) (n + 1) := rfl
  exact le_bot_iff.mp (hk ▸ hle k)

/-!
## The semidirect product of two `p`-groups
-/

/-- Conjugating the copy of `G` by the copy of `A` inside `G ⋊ A` realises the action. -/
theorem inr_mul_inl_mul_inr_inv (a : A) (g : G) :
    (SemidirectProduct.inr a : Semidirect G A) * SemidirectProduct.inl g *
        (SemidirectProduct.inr a : Semidirect G A)⁻¹
      = SemidirectProduct.inl (a • g) := by
  refine SemidirectProduct.ext ?_ ?_ <;> simp

/-- The image of `⁅G, A⁆` in `G ⋊ A` consists of commutators of the copy of `G` with the whole
group: `⁅g, a⁆ = ⁅g⁻¹, a⁆` computed in `G ⋊ A`. -/
theorem map_commutatorAction_le :
    (commutatorAction A G).map (SemidirectProduct.inl (φ := MulDistribMulAction.toMulAut A G))
      ≤ ⁅Gcopy G A, (⊤ : Subgroup (Semidirect G A))⁆ := by
  rw [Subgroup.map_le_iff_le_comap]
  refine commutatorSubgroup_le fun a g _ ↦ ?_
  rw [Subgroup.mem_comap]
  have key : (SemidirectProduct.inl (g⁻¹ * (a • g)) : Semidirect G A)
      = ⁅(SemidirectProduct.inl g⁻¹ : Semidirect G A),
          (SemidirectProduct.inr a : Semidirect G A)⁆ := by
    refine SemidirectProduct.ext ?_ ?_ <;> simp [commutatorElement_def]
  rw [key]
  exact Subgroup.commutator_mem_commutator (inl_mem_Gcopy _) (Subgroup.mem_top _)

variable {p : ℕ} [Fact p.Prime] [Finite G] [Finite A]

/-- The semidirect product of two `p`-groups is a `p`-group. -/
theorem isPGroup_semidirect (hG : IsPGroup p G) (hA : IsPGroup p A) :
    IsPGroup p (Semidirect G A) := by
  obtain ⟨m, hm⟩ := hG.exists_card_eq
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  refine IsPGroup.of_card (n := m + n) ?_
  rw [SemidirectProduct.card, hm, hn, pow_add]

/-!
## Isaacs 4.32
-/

/-- **Isaacs, Lemma 4.32**, first part.  A `p`-group acting on a nontrivial `p`-group `G` has
`⁅G, P⁆ < G`. -/
theorem commutatorAction_lt_top (hG : IsPGroup p G) (hA : IsPGroup p A) [Nontrivial G] :
    commutatorAction A G < ⊤ := by
  have : Group.IsNilpotent (Semidirect G A) := (isPGroup_semidirect hG hA).isNilpotent
  have hGc : Gcopy G A ≠ ⊥ := by
    obtain ⟨x, hx⟩ := exists_ne (1 : G)
    intro hbot
    have hmem : (SemidirectProduct.inl x : Semidirect G A) ∈ (⊥ : Subgroup (Semidirect G A)) :=
      hbot ▸ inl_mem_Gcopy (A := A) x
    exact hx (SemidirectProduct.inl_injective
      (by rw [Subgroup.mem_bot.mp hmem, map_one]))
  have hlt := commutator_top_lt (Gcopy G A) hGc
  refine lt_of_le_of_ne le_top fun heq ↦ absurd hlt (not_lt_of_ge ?_)
  have hmap := map_commutatorAction_le (A := A) (G := G)
  rw [heq] at hmap
  rwa [← MonoidHom.range_eq_map] at hmap

omit [Finite A] in
/-- **Isaacs, Lemma 4.32**, second part.  A `p`-group acting on a nontrivial `p`-group `G` has
`C_G(P) > 1`: this is the fixed-point theorem for `p`-groups. -/
theorem fixedPoints_ne_bot (hG : IsPGroup p G) (hA : IsPGroup p A) [Nontrivial G] :
    FixedPoints.subgroup A G ≠ ⊥ := by
  obtain ⟨n, hn⟩ := hG.exists_card_eq
  have hcard1 : Nat.card G ≠ 1 := fun h ↦
    (not_subsingleton G) (Nat.card_eq_one_iff_unique.mp h).1
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, pow_zero] at hn
    exact hcard1 hn
  have hpdvd : p ∣ Nat.card G := hn ▸ dvd_pow_self p hn0
  have h1 : (1 : G) ∈ MulAction.fixedPoints A G := fun a ↦ smul_one a
  obtain ⟨b, hb, hab⟩ := hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point G hpdvd h1
  intro hbot
  exact hab (Subgroup.mem_bot.mp (hbot ▸ (hb : b ∈ FixedPoints.subgroup A G))).symm

end CoprimeAction
