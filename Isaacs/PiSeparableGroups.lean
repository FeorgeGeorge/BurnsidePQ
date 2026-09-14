module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Data.SetLike.Fintype

/-!
# `π`-groups and `π`-separable groups

Fix a set of primes `π`.  Following Isaacs, a *finite* group `G` is `π`-**separable** if there is a
normal series
`1 = N₀ ≤ N₁ ≤ ⋯ ≤ N_r = G`
in which every factor `Nᵢ / Nᵢ₋₁` is either a `π`-group or a `π'`-group.

This file introduces
* `PiGroups.IsPiGroup π G`: `G` is a `π`-group, i.e. the order of every element of `G` is a
  positive natural number all of whose prime factors belong to `π`;
* `PiGroups.IsPiOrCompl π G`: `G` is a `π`-group or a `π'`-group — the condition Isaacs imposes
  on each factor of the series, and the notion the three definitions below share;
* `PiGroups.IsPiSeparableAt π H`: the subgroup `H` of `G` is the top term of a normal series of
  `G` (normal in the ambient group `G`, as in Isaacs) with `π`-factors or `π'`-factors;
* `PiGroups.IsPiSeparable π G`: `G` is `π`-separable, that is, `⊤` is such a subgroup;
* `PiGroups.HasPiSeries π G`: the literal transcription of the definition, with the length `r`
  and the family `N : ℕ → Subgroup G` spelled out, shown to be equivalent to
  `PiGroups.IsPiSeparable π G` in `PiGroups.isPiSeparable_iff_hasPiSeries`;
* `PiGroups.piCore π G`: the `π`-core `O_π(G)`, the join of all normal `π`-subgroups;
* `PiGroups.IsPiSubnormalAt π H` and `PiGroups.IsPiCharacteristicAt π H`: the subnormal and the
  characteristic variants of the series, in which the terms are only normal in the next one,
  resp. characteristic in `G`.

Besides the basic theory of `π`-groups, the main results are
* `PiGroups.IsPiSeparable.quotient` and `PiGroups.IsPiSeparable.subgroup`: quotients and
  subgroups of `π`-separable groups are `π`-separable;
* `PiGroups.IsPiSeparable.piCore_ne_bot_or`: a nontrivial `π`-separable group has `O_π(G) > 1` or
  `O_π'(G) > 1`, hence a nontrivial characteristic `π`- or `π'`-subgroup
  (`PiGroups.IsPiSeparable.exists_characteristic_ne_bot`);
* `PiGroups.IsPiSeparableAt.of_normal`: a normal subgroup of a finite group that is `π`-separable
  *as a group* is the top term of a series of subgroups normal in the ambient group;
* `PiGroups.IsPiSeparable.of_normal_of_quotient`: `π`-separability is closed under extensions;
* `PiGroups.isPiSeparable_iff_isPiSubnormalAt_top` (Isaacs' Lemma 3.18) and
  `PiGroups.isPiSeparable_iff_isPiCharacteristicAt_top`: subnormal series and characteristic
  series describe the same class of finite groups as normal series do;
* `PiGroups.IsPiSeparable.of_comm` and `PiGroups.IsPiSeparable.of_isSolvable` (Isaacs'
  Corollary 3.19): finite commutative groups, and more generally finite solvable groups, are
  `π`-separable — so `π`-separability is a generalisation of solvability;
* `PiGroups.centralizer_piCore_le_piCore` (Isaacs' Theorem 3.21, Hall–Higman 1.2.3): a finite
  `π`-separable group with `O_π'(G) = 1` satisfies `C_G(O_π(G)) ≤ O_π(G)`.  This is the step
  used in the route to Burnside's `p^a q^b` theorem sketched in `Isaacs/BurnsidePQTheorem.lean`.

## Design notes

Two deviations from the literal definition are worth spelling out.

### `π`-groups

Isaacs works with finite groups, where "`G` is a `π`-group" means that every prime divisor of
`|G|` lies in `π`.  We use the element-wise formulation, exactly as `mathlib` does for
`IsPGroup`: no finiteness assumption is needed to state it, and for finite groups it is
equivalent to the condition on `Nat.card G` (`PiGroups.IsPiGroup.iff_card`).

### The normal series

Rather than transcribing the chain `1 = N₀ ≤ ⋯ ≤ N_r = G` as a function `ℕ → Subgroup G`
together with all its constraints, we define `IsPiSeparableAt` as an `inductive` predicate on
subgroups: `⊥` is the start of such a series, and a subgroup `K` is the top of one as soon as
some `N` that is itself the top of such a series sits normally inside `G` below `K`, with
`K / N` a `π`-group or a `π'`-group.  The length `r` of the chain becomes the depth of the
recursion and never has to be mentioned.

This is the same trade-off that `mathlib` makes for `Subgroup.IsSubnormal`; see
`Isaacs/IsSubnormal.lean` for a longer discussion of why the recursive form tends to be easier
to work with than the literal one.  As there, once `PiGroups.isPiSeparable_iff_hasPiSeries`
identifies the recursive form with the literal one, which of the two is "the" definition stops
mattering: `PiGroups.HasPiSeries` is available whenever an explicit chain is what one wants.

Note that `Nᵢ` is asked to be normal in the *ambient* group `G`, not merely in `Nᵢ₊₁`: this is
what "normal series" means in Isaacs.
-/

@[expose] public section

namespace PiGroups

universe u

/-!
## Induction on the order of a finite group

Several proofs in this development induct on `Nat.card` over a *varying* ambient group: the
inductive step passes to a subgroup or a quotient, so the group itself changes and `Nat.rec` does
not apply directly.  The standard workaround is to carry a fuel parameter,
`∀ (n : ℕ) (X : Type u) [Group X] [Finite X], Nat.card X ≤ n → …`, and induct on `n`.  The two
lemmas here do that once and for all, so no later proof has to repeat the boilerplate.
-/

/-- **Strong induction on the order of a finite group.**  To prove a statement for every finite
group in a fixed universe it suffices to prove it for `X` assuming it for every group of smaller
order.  The groups in the inductive hypothesis are arbitrary, so the step may pass to a subgroup,
a quotient, or any other smaller group. -/
theorem induction_on_card {motive : ∀ (X : Type u) [Group X] [Finite X], Prop}
    (step : ∀ (X : Type u) [Group X] [Finite X],
      (∀ (Y : Type u) [Group Y] [Finite Y], Nat.card Y < Nat.card X → motive Y) → motive X)
    (X : Type u) [Group X] [Finite X] : motive X := by
  suffices h : ∀ (n : ℕ) (X : Type u) [Group X] [Finite X], Nat.card X ≤ n → motive X from
    h (Nat.card X) X le_rfl
  intro n
  induction n with
  | zero =>
    intro X _ _ hcard
    have := Nat.card_pos (α := X)
    omega
  | succ n ih =>
    intro X _ _ hcard
    exact step X fun Y _ _ hlt => ih Y (by omega)

/-- **Strong induction on the index of a subgroup**, i.e. on `|G| - |K|`: to prove a statement for
every subgroup of `G` it suffices to prove it for `K` assuming it for every larger subgroup.  This
is the shape of Isaacs' "induction on `|G : H|`" arguments, which climb from `K` towards `⊤`. -/
theorem induction_on_card_compl {G : Type*} [Group G] [Finite G] {motive : Subgroup G → Prop}
    (step : ∀ K : Subgroup G,
      (∀ L : Subgroup G, Nat.card K < Nat.card L → motive L) → motive K)
    (K : Subgroup G) : motive K := by
  suffices h : ∀ (n : ℕ) (K : Subgroup G), Nat.card G - Nat.card K ≤ n → motive K from
    h (Nat.card G - Nat.card K) K le_rfl
  intro n
  induction n with
  | zero =>
    intro K hK
    refine step K fun L hlt => absurd hlt (Nat.not_lt.mpr ?_)
    have h2 : Nat.card L ≤ Nat.card G := Subgroup.card_le_card_group L
    omega
  | succ n ih =>
    intro K hK
    refine step K fun L hlt => ih L ?_
    have h2 : Nat.card L ≤ Nat.card G := Subgroup.card_le_card_group L
    omega

end PiGroups

namespace PiGroups

variable (π ρ : Set ℕ) (G : Type*) [Group G]

/--
A `π`-group, for a set of primes `π`, is a group in which every element `g` satisfies `g ^ n = 1`
for some positive `n` all of whose prime factors lie in `π`.

Equivalently (see `PiGroups.IsPiGroup.iff_orderOf`), every element has finite order and that
order is a `π`-number.  For finite groups this is Isaacs' condition that every prime divisor of
the order of the group belongs to `π`: see `PiGroups.IsPiGroup.iff_card`.
-/
def IsPiGroup : Prop :=
  ∀ g : G, ∃ n : ℕ, 0 < n ∧ (∀ p ∈ n.primeFactors, p ∈ π) ∧ g ^ n = 1

variable {π ρ G}

namespace IsPiGroup

theorem iff_orderOf :
    IsPiGroup π G ↔ ∀ g : G, 0 < orderOf g ∧ ∀ p ∈ (orderOf g).primeFactors, p ∈ π := by
  refine ⟨fun h g ↦ ?_, fun h g ↦ ⟨orderOf g, (h g).1, (h g).2, pow_orderOf_eq_one g⟩⟩
  obtain ⟨n, hn0, hnπ, hgn⟩ := h g
  have hdvd : orderOf g ∣ n := orderOf_dvd_of_pow_eq_one hgn
  have h0 : orderOf g ≠ 0 := fun h0 ↦ hn0.ne' (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  refine ⟨Nat.pos_of_ne_zero h0, fun p hp ↦ ?_⟩
  obtain ⟨hp_prime, hp_dvd, -⟩ := Nat.mem_primeFactors.mp hp
  exact hnπ p (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd.trans hdvd, hn0.ne'⟩)

/-- A group all of whose elements are trivial is a `π`-group, for every `π`. -/
theorem of_subsingleton [Subsingleton G] : IsPiGroup π G :=
  fun g ↦ ⟨1, Nat.one_pos, by
    simp only [Nat.primeFactors_one, Finset.notMem_empty, IsEmpty.forall_iff, implies_true],
    Subsingleton.elim _ _⟩

theorem of_bot : IsPiGroup π (⊥ : Subgroup G) := of_subsingleton

/-- Enlarging the set of primes preserves being a `π`-group. -/
theorem mono (hG : IsPiGroup π G) (h : π ⊆ ρ) : IsPiGroup ρ G :=
  fun g ↦ (hG g).imp fun _ ⟨h0, hπ, hg⟩ ↦ ⟨h0, fun p hp ↦ h (hπ p hp), hg⟩

/-- For a prime `p ∈ π`, every `p`-group is a `π`-group. -/
theorem of_isPGroup {p : ℕ} (hp : p.Prime) (hπ : p ∈ π) (hG : IsPGroup p G) : IsPiGroup π G := by
  intro g
  obtain ⟨k, hk⟩ := hG g
  refine ⟨p ^ k, Nat.pow_pos hp.pos, fun q hq ↦ ?_, hk⟩
  obtain ⟨hq_prime, hq_dvd, -⟩ := Nat.mem_primeFactors.mp hq
  rwa [(Nat.prime_dvd_prime_iff_eq hq_prime hp).mp (hq_prime.dvd_of_dvd_pow hq_dvd)]

theorem of_injective {H : Type*} [Group H] (hG : IsPiGroup π G) (φ : H →* G)
    (hφ : Function.Injective φ) : IsPiGroup π H := by
  intro h
  obtain ⟨n, hn0, hnπ, hn⟩ := hG (φ h)
  exact ⟨n, hn0, hnπ, hφ (by rw [map_pow, hn, map_one])⟩

theorem to_subgroup (hG : IsPiGroup π G) (H : Subgroup G) : IsPiGroup π H :=
  hG.of_injective H.subtype Subtype.coe_injective

/-- A subgroup of a `π`-subgroup is a `π`-subgroup. -/
theorem of_le {H K : Subgroup G} (hle : H ≤ K) (hK : IsPiGroup π K) : IsPiGroup π H :=
  hK.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

theorem of_surjective {H : Type*} [Group H] (hG : IsPiGroup π G) (φ : G →* H)
    (hφ : Function.Surjective φ) : IsPiGroup π H := by
  intro h
  obtain ⟨g, rfl⟩ := hφ h
  obtain ⟨n, hn0, hnπ, hn⟩ := hG g
  exact ⟨n, hn0, hnπ, by rw [← map_pow, hn, map_one]⟩

theorem to_quotient (hG : IsPiGroup π G) (H : Subgroup G) [H.Normal] : IsPiGroup π (G ⧸ H) :=
  hG.of_surjective (QuotientGroup.mk' H) Quotient.mk''_surjective

theorem of_equiv {H : Type*} [Group H] (hG : IsPiGroup π G) (φ : G ≃* H) : IsPiGroup π H :=
  hG.of_surjective (φ : G →* H) φ.surjective

/--
Transport along an equality of the subgroup being quotiented by.

Rewriting `N` inside the type `H ⧸ N` is not something `rw` can do, since the group structure of
the quotient depends on the normality instance for `N`; this lemma performs the substitution
instead.
-/
theorem quotient_congr {H : Type*} [Group H] {N₁ N₂ : Subgroup H} [N₁.Normal] [N₂.Normal]
    (hN : N₁ = N₂) (h : IsPiGroup π (H ⧸ N₁)) : IsPiGroup π (H ⧸ N₂) := by
  subst hN
  exact h

/-- The same transport for a factor `K / N` of a series, along equalities of `N` and of `K`. -/
theorem factor_congr {N₁ K₁ N₂ K₂ : Subgroup G} [N₁.Normal] [N₂.Normal] (hN : N₁ = N₂)
    (hK : K₁ = K₂) (h : IsPiGroup π (K₁ ⧸ N₁.subgroupOf K₁)) :
    IsPiGroup π (K₂ ⧸ N₂.subgroupOf K₂) := by
  subst hK
  exact quotient_congr (congrArg (fun N ↦ Subgroup.subgroupOf N K₁) hN) h

/-- For finite groups this is Isaacs' definition: every prime divisor of `|G|` lies in `π`. -/
theorem iff_card [Finite G] : IsPiGroup π G ↔ ∀ p ∈ (Nat.card G).primeFactors, p ∈ π := by
  refine ⟨fun h p hp ↦ ?_, fun h g ↦ ⟨Nat.card G, Nat.card_pos, h, pow_card_eq_one'⟩⟩
  obtain ⟨hp_prime, hp_dvd, -⟩ := Nat.mem_primeFactors.mp hp
  have : Fact p.Prime := ⟨hp_prime⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  obtain ⟨n, hn0, hnπ, hgn⟩ := h g
  exact hnπ p (Nat.mem_primeFactors.mpr
    ⟨hp_prime, hg ▸ orderOf_dvd_of_pow_eq_one hgn, hn0.ne'⟩)

/-- A group that is both a `π`-group and a `π'`-group is trivial. -/
theorem subsingleton (hG : IsPiGroup π G) (hG' : IsPiGroup πᶜ G) : Subsingleton G := by
  refine ⟨fun a b ↦ ?_⟩
  suffices h : ∀ g : G, g = 1 by rw [h a, h b]
  intro g
  obtain ⟨n, hn0, hnπ, hgn⟩ := hG g
  obtain ⟨m, hm0, hmπ, hgm⟩ := hG' g
  have hgcd : Nat.gcd n m = 1 := by
    by_contra h
    obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd h
    exact hmπ p (Nat.mem_primeFactors.mpr
        ⟨hp_prime, hp_dvd.trans (Nat.gcd_dvd_right n m), hm0.ne'⟩)
      (hnπ p (Nat.mem_primeFactors.mpr
        ⟨hp_prime, hp_dvd.trans (Nat.gcd_dvd_left n m), hn0.ne'⟩))
  refine orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one ?_)
  exact hgcd ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hgn) (orderOf_dvd_of_pow_eq_one hgm)

/-- The orders of a finite `π`-group and of a finite `π'`-group are coprime.  This is what makes
Schur–Zassenhaus applicable to a `π`-group extended by a `π'`-group. -/
theorem coprime_card {H : Type*} [Group H] [Finite G] [Finite H] (hG : IsPiGroup π G)
    (hH : IsPiGroup πᶜ H) : Nat.Coprime (Nat.card G) (Nat.card H) := by
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  exact iff_card.mp hH p (Nat.mem_primeFactors.mpr
      ⟨hp, hpdvd.trans (Nat.gcd_dvd_right _ _), Nat.card_pos.ne'⟩)
    (iff_card.mp hG p (Nat.mem_primeFactors.mpr
      ⟨hp, hpdvd.trans (Nat.gcd_dvd_left _ _), Nat.card_pos.ne'⟩))

end IsPiGroup

/-- A `p`-group is a `{p}`-group: the case `π = {p}` of `PiGroups.IsPiGroup.of_isPGroup`.
(Converse of `PiGroups.IsPiGroup.isPGroup`.) -/
theorem IsPGroup.isPiGroup {X : Type*} [Group X] {p : ℕ} (hp : p.Prime) (h : IsPGroup p X) :
    IsPiGroup ({p} : Set ℕ) X :=
  IsPiGroup.of_isPGroup hp rfl h


/--
`G` is a `π`-group or a `π'`-group.

This is the condition Isaacs imposes on each factor of the series, so it deserves a name: all
three variants of the definition below ask it of their factors, and it transports along the maps
of `PiGroups.IsPiGroup` uniformly in the set of primes, which is what
`PiGroups.IsPiOrCompl.transfer` exploits.
-/
def IsPiOrCompl (π : Set ℕ) (G : Type*) [Group G] : Prop := IsPiGroup π G ∨ IsPiGroup πᶜ G

namespace IsPiOrCompl

/-- Transport along a construction that is uniform in the set of primes.  This is what spares us
from applying every such construction twice, once for `π` and once for `π'`. -/
theorem transfer {H : Type*} [Group H] (h : IsPiOrCompl π G)
    (f : ∀ {σ : Set ℕ}, IsPiGroup σ G → IsPiGroup σ H) : IsPiOrCompl π H :=
  Or.imp f f h

/-- The condition is symmetric in `π` and `π'`. -/
theorem compl (h : IsPiOrCompl π G) : IsPiOrCompl πᶜ G :=
  Or.imp id (fun h' ↦ by rwa [compl_compl]) (Or.symm h)

end IsPiOrCompl

/--
`IsPiSeparableAt π K` means that the subgroup `K` of `G` is the top term of a normal series
`1 = N₀ ≤ N₁ ≤ ⋯ ≤ N_r = K`
of subgroups of `G`, each normal in `G`, in which every factor `Nᵢ₊₁ / Nᵢ` is a `π`-group or a
`π'`-group.

The series itself is not part of the data: the chain is recorded by the recursive structure of
the two constructors, `bot` starting a series at `1` and `step` extending a series ending at `N`
by one further term `K`.
-/
inductive IsPiSeparableAt (π : Set ℕ) {G : Type*} [Group G] : Subgroup G → Prop where
  /-- The trivial subgroup is the top of the empty series. -/
  | bot : IsPiSeparableAt π ⊥
  /-- A subgroup `K` tops such a series as soon as some normal subgroup `N ≤ K` of `G` does,
  with `K / N` a `π`-group or a `π'`-group. -/
  | step (N K : Subgroup G) [N.Normal] (hle : N ≤ K) (hN : IsPiSeparableAt π N)
      (hfactor : IsPiOrCompl π (K ⧸ N.subgroupOf K)) :
      IsPiSeparableAt π K

variable (π G) in
/--
A group `G` is `π`-separable, for a set of primes `π`, if there is a normal series
`1 = N₀ ≤ N₁ ≤ ⋯ ≤ N_r = G`
in which every factor `Nᵢ₊₁ / Nᵢ` is either a `π`-group or a `π'`-group.

This is Isaacs' definition, phrased through `PiGroups.IsPiSeparableAt`; Isaacs states it for
finite groups, we do not assume finiteness to state it.
-/
def IsPiSeparable : Prop := IsPiSeparableAt π (⊤ : Subgroup G)

namespace IsPiSeparableAt

/-- A subgroup that is a `π`-group or a `π'`-group tops a series of length one. -/
theorem of_isPiOrCompl {K : Subgroup G} (h : IsPiOrCompl π K) : IsPiSeparableAt π K :=
  .step ⊥ K bot_le .bot (h.transfer fun hg ↦ hg.to_quotient _)

/-- `π`-separability is the same notion as `π'`-separability. -/
theorem compl {K : Subgroup G} (h : IsPiSeparableAt π K) : IsPiSeparableAt πᶜ K := by
  induction h with
  | bot => exact .bot
  | step N K hle _ hfactor ih => exact .step N K hle ih hfactor.compl

end IsPiSeparableAt

namespace IsPiSeparable

/-- A group that is a `π`-group or a `π'`-group is `π`-separable: take the series `1 ≤ G`. -/
theorem of_isPiOrCompl (h : IsPiOrCompl π G) : IsPiSeparable π G :=
  IsPiSeparableAt.of_isPiOrCompl (h.transfer fun hg ↦ hg.to_subgroup ⊤)

/-- Every `π`-group is `π`-separable. -/
theorem of_isPiGroup (h : IsPiGroup π G) : IsPiSeparable π G := of_isPiOrCompl (Or.inl h)

/-- Every `π'`-group is `π`-separable. -/
theorem of_isPiGroup_compl (h : IsPiGroup πᶜ G) : IsPiSeparable π G := of_isPiOrCompl (Or.inr h)

theorem of_subsingleton [Subsingleton G] : IsPiSeparable π G :=
  of_isPiGroup IsPiGroup.of_subsingleton

/-- A `p`-group is `π`-separable, whatever the set of primes `π` is. -/
theorem of_isPGroup {p : ℕ} (hp : p.Prime) (h : IsPGroup p G) : IsPiSeparable π G := by
  by_cases hπ : p ∈ π
  · exact of_isPiGroup (IsPiGroup.of_isPGroup hp hπ h)
  · exact of_isPiGroup_compl (IsPiGroup.of_isPGroup hp hπ h)

/-- Isaacs' observation: a `π`-separable group is the same thing as a `π'`-separable group. -/
theorem compl (h : IsPiSeparable π G) : IsPiSeparable πᶜ G := IsPiSeparableAt.compl h

end IsPiSeparable

/-- Isaacs' observation: a `π`-separable group is the same thing as a `π'`-separable group. -/
theorem isPiSeparable_compl_iff : IsPiSeparable πᶜ G ↔ IsPiSeparable π G := by
  refine ⟨fun h ↦ ?_, IsPiSeparable.compl⟩
  simpa only [compl_compl] using h.compl

/-!
## Comparison with the literal definition

`IsPiSeparableAt` hides the chain `1 = N₀ ≤ N₁ ≤ ⋯ ≤ N_r = G` in its recursive structure.  We
now check that nothing was lost, by proving it equivalent to the literal transcription of
Isaacs' definition, in which the length `r` and the family `N` are spelled out.

This is the analogue of `Subgroup.IsSubnormal.isSubnormal_iff` in `mathlib`.
-/

/--
The literal transcription of "there is a normal series of `G` ending at the subgroup `K`":
a length `r` and a family `N : ℕ → Subgroup G` of subgroups normal in `G`, with `N 0 = ⊥`,
`N r = K`, increasing along the chain, and with every factor `N (i + 1) / N i` a `π`-group or a
`π'`-group.

Only `N 0, …, N r` are constrained by the chain conditions, but all the `N i` are asked to be
normal, so that the factors have a group structure; in particular `K = N r` is normal.
This is harmless: the terms beyond `r` can always be taken to be `K` itself.
-/
def HasPiSeriesAt (π : Set ℕ) {G : Type*} [Group G] (K : Subgroup G) : Prop :=
  ∃ (r : ℕ) (N : ℕ → Subgroup G) (hN : ∀ i, (N i).Normal), haveI := hN;
    N 0 = ⊥ ∧ N r = K ∧ (∀ i < r, N i ≤ N (i + 1)) ∧
      ∀ i < r, IsPiOrCompl π (N (i + 1) ⧸ (N i).subgroupOf (N (i + 1)))

variable (π G) in
/--
The literal transcription of Isaacs' definition: `G` is `π`-separable if there are `r : ℕ` and
subgroups `N 0, …, N r` of `G`, all normal in `G`, with `N 0 = 1`, `N r = G`,
`N i ≤ N (i + 1)`, and every factor `N (i + 1) / N i` a `π`-group or a `π'`-group.

See `PiGroups.isPiSeparable_iff_hasPiSeries`: this is equivalent to `PiGroups.IsPiSeparable`,
which is the form meant for actual use.
-/
def HasPiSeries : Prop := HasPiSeriesAt π (⊤ : Subgroup G)

namespace HasPiSeriesAt

/-- The trivial subgroup is the end of the series of length `0`. -/
theorem bot : HasPiSeriesAt π (⊥ : Subgroup G) :=
  ⟨0, fun _ ↦ ⊥, fun _ ↦ inferInstance, rfl, rfl,
    fun i hi ↦ (Nat.not_lt_zero i hi).elim, fun i hi ↦ (Nat.not_lt_zero i hi).elim⟩

/-- A series ending at `N` can be extended by one term `K`, provided `K / N` is a `π`-group or a
`π'`-group. -/
theorem step {N K : Subgroup G} [N.Normal] (hN : HasPiSeriesAt π N) (hK : K.Normal) (hle : N ≤ K)
    (hfactor : IsPiOrCompl π (K ⧸ N.subgroupOf K)) :
    HasPiSeriesAt π K := by
  classical
  obtain ⟨r, M, hM, h0, hr, hmono, hfac⟩ := hN
  have := hM
  -- The extended series: `M 0, …, M r, K`, and then `K` forever after.
  have hnormal : ∀ i, (if i ≤ r then M i else K).Normal := by
    intro i
    split
    · exact hM i
    · exact hK
  have := hnormal
  have hlow : ∀ i, i ≤ r → (if i ≤ r then M i else K) = M i := fun i hi ↦ if_pos hi
  have htop : (if r + 1 ≤ r then M (r + 1) else K) = K := if_neg (by omega)
  refine ⟨r + 1, fun i ↦ if i ≤ r then M i else K, hnormal, ?_, htop, ?_, ?_⟩
  · dsimp only
    rw [hlow 0 (Nat.zero_le r), h0]
  · intro i hi
    dsimp only
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
    · rw [hlow i h.le, hlow (i + 1) h]
      exact hmono i h
    · rw [hlow i le_rfl, htop, hr]
      exact hle
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
    · exact (hfac i h).transfer
        (IsPiGroup.factor_congr (hlow i h.le).symm (hlow (i + 1) h).symm)
    · exact hfactor.transfer
        (IsPiGroup.factor_congr (hr.symm.trans (hlow i le_rfl).symm) htop.symm)

/-- A literal normal series with `π`- and `π'`-factors gives a `π`-separable subgroup. -/
theorem isPiSeparableAt {K : Subgroup G} (h : HasPiSeriesAt π K) : IsPiSeparableAt π K := by
  obtain ⟨r, M, hM, h0, hr, hmono, hfac⟩ := h
  have := hM
  subst hr
  revert hmono hfac
  induction r with
  | zero =>
    intro _ _
    rw [h0]
    exact .bot
  | succ n ih =>
    intro hmono hfac
    exact .step (M n) (M (n + 1)) (hmono n (Nat.lt_succ_self n))
      (ih (fun i hi ↦ hmono i (by omega)) (fun i hi ↦ hfac i (by omega)))
      (hfac n (Nat.lt_succ_self n))

end HasPiSeriesAt

/-- Conversely, a `π`-separable normal subgroup is the top term of a literal normal series. -/
theorem IsPiSeparableAt.hasPiSeriesAt {K : Subgroup G} (h : IsPiSeparableAt π K) :
    K.Normal → HasPiSeriesAt π K := by
  induction h with
  | bot => exact fun _ ↦ .bot
  | step N K hle _ hfactor ih => exact fun hK ↦ (ih inferInstance).step hK hle hfactor

/-- The recursive definition of `π`-separability agrees with the literal one. -/
theorem isPiSeparableAt_iff_hasPiSeriesAt {K : Subgroup G} [K.Normal] :
    IsPiSeparableAt π K ↔ HasPiSeriesAt π K :=
  ⟨fun h ↦ h.hasPiSeriesAt inferInstance, HasPiSeriesAt.isPiSeparableAt⟩

/--
`PiGroups.IsPiSeparable` is equivalent to the literal transcription of Isaacs' definition:
`G` is `π`-separable if and only if there is a normal series `1 = N₀ ≤ ⋯ ≤ N_r = G` all of whose
factors are `π`-groups or `π'`-groups.
-/
theorem isPiSeparable_iff_hasPiSeries : IsPiSeparable π G ↔ HasPiSeries π G :=
  isPiSeparableAt_iff_hasPiSeriesAt

alias ⟨IsPiSeparable.hasPiSeries, HasPiSeries.isPiSeparable⟩ := isPiSeparable_iff_hasPiSeries

/-!
## Closure properties of `π`-groups

Isaacs' discussion needs `π`-groups to be closed under extensions.  Everything else in this
section follows from that: joins of normal `π`-subgroups are `π`-groups, and hence so is the
`π`-core of a finite group.
-/

namespace IsPiGroup

/-- `π`-groups are closed under extensions: if `N` is normal in `G` and both `N` and `G ⧸ N` are
`π`-groups, then so is `G`.  This is where it matters that the `π`-numbers are closed under
multiplication. -/
theorem of_normal_of_quotient {N : Subgroup G} [N.Normal] (hN : IsPiGroup π N)
    (hQ : IsPiGroup π (G ⧸ N)) : IsPiGroup π G := by
  intro g
  obtain ⟨n, hn0, hnπ, hgn⟩ := hQ (g : G ⧸ N)
  have hmem : g ^ n ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    simpa only [QuotientGroup.mk_pow] using hgn
  obtain ⟨m, hm0, hmπ, hgm⟩ := hN ⟨g ^ n, hmem⟩
  refine ⟨n * m, Nat.mul_pos hn0 hm0, fun p hp ↦ ?_, ?_⟩
  · rw [Nat.primeFactors_mul hn0.ne' hm0.ne'] at hp
    exact (Finset.mem_union.mp hp).elim (hnπ p) (hmπ p)
  · rw [pow_mul]
    simpa only [SubmonoidClass.mk_pow, OneMemClass.coe_one] using congrArg Subtype.val hgm

/-- The join of a `π`-subgroup and a normal `π`-subgroup is a `π`-subgroup: the second
isomorphism theorem identifies `(H ⊔ K) / K` with `H / (H ⊓ K)`. -/
theorem sup {H K : Subgroup G} [K.Normal] (hH : IsPiGroup π H) (hK : IsPiGroup π K) :
    IsPiGroup π ↥(H ⊔ K) :=
  (hK.of_equiv (Subgroup.subgroupOfEquivOfLe (le_sup_right : K ≤ H ⊔ K)).symm).of_normal_of_quotient
    ((hH.to_quotient (K.subgroupOf H)).of_equiv
      (QuotientGroup.quotientInfEquivProdNormalQuotient H K))

/-- In a finite group, the supremum of a family of normal `π`-subgroups is a normal
`π`-subgroup. -/
theorem sSup_of_normal [Finite G] {S : Set (Subgroup G)}
    (hS : ∀ K ∈ S, K.Normal ∧ IsPiGroup π K) : (sSup S).Normal ∧ IsPiGroup π ↥(sSup S) := by
  classical
  have hfin : S.Finite := Set.toFinite S
  rw [← hfin.coe_toFinset, ← Finset.sup_id_eq_sSup]
  refine Finset.sup_induction (p := fun L : Subgroup G ↦ L.Normal ∧ IsPiGroup π L)
    ⟨inferInstance, of_bot⟩ (fun a ha b hb ↦ ?_) (fun b hb ↦ ?_)
  · have := ha.1
    have := hb.1
    exact ⟨inferInstance, ha.2.sup hb.2⟩
  · exact hS b (hfin.mem_toFinset.mp hb)

end IsPiGroup

/-!
## The `π`-core

`O_π(G)` is the join of all the normal `π`-subgroups of `G`.  It is characteristic, and in a
finite group it is itself a `π`-group, so it is the largest normal `π`-subgroup.
-/

variable (π G) in
/-- The `π`-core `O_π(G)`: the join of all normal `π`-subgroups of `G`. -/
def piCore : Subgroup G := sSup {K : Subgroup G | K.Normal ∧ IsPiGroup π K}

/-- Every normal `π`-subgroup is contained in the `π`-core. -/
theorem le_piCore {K : Subgroup G} (hK : K.Normal) (h : IsPiGroup π K) : K ≤ piCore π G :=
  le_sSup ⟨hK, h⟩

instance piCore_characteristic : (piCore π G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK ↦ ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_piCore (hK.1.map _ φ.surjective) (hK.2.of_equiv (φ.subgroupMap K))

/-- In a finite group the `π`-core really is a `π`-group. -/
theorem isPiGroup_piCore [Finite G] : IsPiGroup π (piCore π G) :=
  (IsPiGroup.sSup_of_normal fun _ hK ↦ hK).2

/-!
## Images and preimages of `π`-separable series

Both are needed for Isaacs' induction: quotients of `π`-separable groups are `π`-separable, and
a series of `G ⧸ N` pulls back to a series of `G` sitting above `N`.
-/

namespace IsPiGroup

/-- The image of a factor under a surjective homomorphism is a quotient of that factor. -/
theorem factor_map {Q : Type*} [Group Q] (φ : G →* Q) {N K : Subgroup G} [N.Normal]
    [(N.map φ).Normal] (h : IsPiGroup π (↥K ⧸ N.subgroupOf K)) :
    IsPiGroup π (↥(K.map φ) ⧸ (N.map φ).subgroupOf (K.map φ)) := by
  have hle : N.subgroupOf K ≤
      ((QuotientGroup.mk' ((N.map φ).subgroupOf (K.map φ))).comp (φ.subgroupMap K)).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨(x : G), Subgroup.mem_subgroupOf.mp hx, rfl⟩
  refine h.of_surjective (QuotientGroup.lift _ _ hle) ?_
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective _ y
  obtain ⟨w, hw⟩ := MonoidHom.subgroupMap_surjective φ K z
  exact ⟨QuotientGroup.mk' _ w, by
    simp only [QuotientGroup.mk'_apply, QuotientGroup.lift_mk, MonoidHom.coe_comp,
      QuotientGroup.coe_mk', Function.comp_apply, hw]⟩

/-- The preimage of a factor under a surjective homomorphism is isomorphic to that factor. -/
theorem factor_comap {Q : Type*} [Group Q] (φ : G →* Q) (hφ : Function.Surjective φ)
    {N K : Subgroup Q} [N.Normal] (h : IsPiGroup π (↥K ⧸ N.subgroupOf K)) :
    IsPiGroup π (↥(K.comap φ) ⧸ (N.comap φ).subgroupOf (K.comap φ)) := by
  have hgsurj : Function.Surjective
      ((QuotientGroup.mk' (N.subgroupOf K)).comp (φ.subgroupComap K)) :=
    (QuotientGroup.mk'_surjective _).comp (φ.subgroupComap_surjective_of_surjective K hφ)
  have hker : ((QuotientGroup.mk' (N.subgroupOf K)).comp (φ.subgroupComap K)).ker =
      (N.comap φ).subgroupOf (K.comap φ) := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact Iff.rfl
  exact quotient_congr hker
    (h.of_equiv (QuotientGroup.quotientKerEquivOfSurjective _ hgsurj).symm)

end IsPiGroup

namespace IsPiSeparableAt

/-- The image of a `π`-separable series under a surjective homomorphism is one. -/
theorem map {Q : Type*} [Group Q] (φ : G →* Q) (hφ : Function.Surjective φ) {K : Subgroup G}
    (h : IsPiSeparableAt π K) : IsPiSeparableAt π (K.map φ) := by
  induction h with
  | bot => simpa only [Subgroup.map_bot] using (bot : IsPiSeparableAt π (⊥ : Subgroup Q))
  | step N K hle _ hfactor ih =>
    have : (N.map φ).Normal := ‹N.Normal›.map φ hφ
    exact .step (N.map φ) (K.map φ) (Subgroup.map_mono hle) ih
      (hfactor.transfer (IsPiGroup.factor_map φ))

/-- A `π`-separable series of the image pulls back to one of the preimage, provided the kernel
already carries a `π`-separable series. -/
theorem comap {Q : Type*} [Group Q] (φ : G →* Q) (hφ : Function.Surjective φ)
    (hker : IsPiSeparableAt π φ.ker) {K : Subgroup Q} (h : IsPiSeparableAt π K) :
    IsPiSeparableAt π (K.comap φ) := by
  induction h with
  | bot => simpa only [MonoidHom.comap_bot] using hker
  | step N K hle _ hfactor ih =>
    exact .step (N.comap φ) (K.comap φ) (Subgroup.comap_mono hle) ih
      (hfactor.transfer (IsPiGroup.factor_comap φ hφ))

end IsPiSeparableAt

namespace IsPiSeparable

/-- `π`-separability transfers along surjective homomorphisms. -/
theorem map {Q : Type*} [Group Q] (φ : G →* Q) (hφ : Function.Surjective φ)
    (h : IsPiSeparable π G) : IsPiSeparable π Q := by
  have := IsPiSeparableAt.map φ hφ h
  rwa [Subgroup.map_top_of_surjective φ hφ] at this

/-- `π`-separability is invariant under isomorphism. -/
theorem of_mulEquiv {Q : Type*} [Group Q] (e : G ≃* Q) (h : IsPiSeparable π G) :
    IsPiSeparable π Q :=
  h.map (e : G →* Q) e.surjective

/-- Quotients of `π`-separable groups are `π`-separable. -/
theorem quotient (N : Subgroup G) [N.Normal] (h : IsPiSeparable π G) :
    IsPiSeparable π (G ⧸ N) :=
  h.map (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end IsPiSeparable

/-!
## Subgroups

Intersecting a series of `G` with a subgroup `H` gives a series of `H`: the terms `Nᵢ ⊓ H` are
normal in `H`, and by the second isomorphism theorem their factors embed into the factors of the
original series, so they are still `π`-groups and `π'`-groups.
-/

namespace IsPiGroup

/-- Intersecting a factor with a subgroup `H` embeds it into the original factor.  This is the
injective counterpart of `PiGroups.IsPiGroup.factor_map`. -/
theorem factor_subgroupOf {N K : Subgroup G} [N.Normal] (H : Subgroup G)
    (h : IsPiGroup π (↥K ⧸ N.subgroupOf K)) :
    IsPiGroup π (↥(K.subgroupOf H) ⧸ (N.subgroupOf H).subgroupOf (K.subgroupOf H)) := by
  have hle : (N.subgroupOf H).subgroupOf (K.subgroupOf H) ≤
      Subgroup.comap (H.subtype.subgroupComap K) (N.subgroupOf K) := by
    intro x hx
    exact hx
  refine h.of_injective (QuotientGroup.map _ _ (H.subtype.subgroupComap K) hle) ?_
  intro a b
  induction a using QuotientGroup.induction_on with
  | _ x =>
    induction b using QuotientGroup.induction_on with
    | _ y =>
      intro hab
      have hab' : ((H.subtype.subgroupComap K) x : ↥K ⧸ N.subgroupOf K)
          = ((H.subtype.subgroupComap K) y : ↥K ⧸ N.subgroupOf K) := hab
      rw [QuotientGroup.eq] at hab'
      rw [QuotientGroup.eq]
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv]
      exact hab'

end IsPiGroup

namespace IsPiSeparableAt

/-- A `π`-separable series of `G` intersects to a `π`-separable series of any subgroup `H`. -/
theorem subgroupOf {K : Subgroup G} (h : IsPiSeparableAt π K) (H : Subgroup G) :
    IsPiSeparableAt π (K.subgroupOf H) := by
  induction h with
  | bot =>
    rw [Subgroup.bot_subgroupOf]
    exact .bot
  | step N K hle _ hfactor ih =>
    exact .step (N.subgroupOf H) (K.subgroupOf H) (Subgroup.subgroupOf_mono H hle) ih
      (hfactor.transfer (IsPiGroup.factor_subgroupOf H))

end IsPiSeparableAt

/-- Subgroups of `π`-separable groups are `π`-separable. -/
theorem IsPiSeparable.subgroup (H : Subgroup G) (h : IsPiSeparable π G) : IsPiSeparable π ↥H := by
  have hH := IsPiSeparableAt.subgroupOf h H
  rwa [Subgroup.top_subgroupOf] at hH

/-!
## Isaacs' discussion, and Lemma 3.18

Renumbering the `Nᵢ` to eliminate repeats shows that a nontrivial `π`-separable group has
`O_π(G) > 1` or `O_π'(G) > 1`, and hence a nontrivial *characteristic* subgroup that is a
`π`-group or a `π'`-group.  Iterating that observation is what makes the series of a normal
subgroup `N ⊴ G` replaceable by one consisting of subgroups normal in `G`, which is the content
of Lemma 3.18: a subnormal series with `π`-factors and `π'`-factors already forces
`π`-separability.
-/

namespace IsPiSeparableAt

/-- Isaacs' renumbering remark: the first nontrivial term of the series.  A nontrivial subgroup
that is normal in `G` and carries a `π`-separable series contains a nontrivial subgroup of `G`,
normal in `G`, that is a `π`-group or a `π'`-group. -/
theorem exists_normal_ne_bot {K : Subgroup G} (h : IsPiSeparableAt π K) :
    K.Normal → K ≠ ⊥ →
      ∃ N : Subgroup G, N ≠ ⊥ ∧ N ≤ K ∧ N.Normal ∧ IsPiOrCompl π N := by
  induction h with
  | bot => exact fun _ h ↦ absurd rfl h
  | step N K hle _ hfactor ih =>
    intro hKnormal hKbot
    rcases eq_or_ne N ⊥ with rfl | hNbot
    · -- a repeat at the bottom of the series: `K` itself is a `π`-group or a `π'`-group
      exact ⟨K, hKbot, le_rfl, hKnormal, hfactor.transfer fun hf ↦
        (IsPiGroup.quotient_congr (Subgroup.bot_subgroupOf K) hf).of_equiv
          QuotientGroup.quotientBot⟩
    · obtain ⟨M, hM0, hMle, hMnormal, hMpi⟩ := ih ‹N.Normal› hNbot
      exact ⟨M, hM0, hMle.trans hle, hMnormal, hMpi⟩

end IsPiSeparableAt

namespace IsPiSeparable

/-- Isaacs' observation: in a nontrivial `π`-separable group, `O_π(G) > 1` or `O_π'(G) > 1`. -/
theorem piCore_ne_bot_or [Nontrivial G] (h : IsPiSeparable π G) :
    piCore π G ≠ ⊥ ∨ piCore πᶜ G ≠ ⊥ := by
  obtain ⟨N, hN0, -, hNnormal, hNpi⟩ :=
    IsPiSeparableAt.exists_normal_ne_bot h inferInstance top_ne_bot
  refine Or.imp (fun hp ↦ ?_) (fun hp ↦ ?_) hNpi <;>
    exact fun hc ↦ hN0 (le_bot_iff.mp (hc ▸ le_piCore hNnormal hp))

/-- Isaacs: a nontrivial finite `π`-separable group has a nontrivial characteristic subgroup that
is either a `π`-group or a `π'`-group, namely one of its two `π`-cores. -/
theorem exists_characteristic_ne_bot [Finite G] [Nontrivial G] (h : IsPiSeparable π G) :
    ∃ C : Subgroup G, C ≠ ⊥ ∧ C.Characteristic ∧ IsPiOrCompl π C := by
  rcases h.piCore_ne_bot_or with hc | hc
  · exact ⟨piCore π G, hc, inferInstance, Or.inl isPiGroup_piCore⟩
  · exact ⟨piCore πᶜ G, hc, inferInstance, Or.inr isPiGroup_piCore⟩

end IsPiSeparable

/-- For `N ⊴ G` and any `K`, the factor `K / (K ⊓ N)` is the image of `K` in `G ⧸ N`. -/
noncomputable def quotientSubgroupOfEquivMap (N : Subgroup G) [N.Normal] (K : Subgroup G) :
    (↥K ⧸ N.subgroupOf K) ≃* ↥(K.map (QuotientGroup.mk' N)) :=
  (QuotientGroup.quotientMulEquivOfEq
        (by rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'] :
          ((QuotientGroup.mk' N).subgroupMap K).ker = N.subgroupOf K).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (MonoidHom.subgroupMap_surjective _ K))

/-- Quotienting a finite group by a nontrivial normal subgroup strictly decreases the order.
This is the measure for all the inductions below. -/
theorem card_quotient_lt [Finite G] (N : Subgroup G) [N.Normal] (h : N ≠ ⊥) :
    Nat.card (G ⧸ N) < Nat.card G := by
  rw [← Subgroup.index_eq_card, ← N.index_mul_card]
  exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (N.one_lt_card_iff_ne_bot.mpr h)

universe u

/--
Auxiliary induction on `|N|` behind `PiGroups.IsPiSeparableAt.of_normal`.

Isaacs replaces the series of `N` by a characteristic one, whose terms are then automatically
normal in `G`.  We do the same one step at a time: a nontrivial characteristic `π`- or
`π'`-subgroup `C` of `N` maps to a subgroup of `G` normal in `G`, and the rest of the series is
obtained from the induction hypothesis applied inside `G ⧸ C`, where the image of `N` is
smaller.  This is why the statement quantifies over the ambient group as well.
-/
theorem isPiSeparableAt_of_card_le (π : Set ℕ) :
    ∀ (n : ℕ) (G : Type u) [Group G] [Finite G] (N : Subgroup G), N.Normal →
      Nat.card N ≤ n → IsPiSeparable π N → IsPiSeparableAt π N := by
  intro n
  induction n with
  | zero =>
    intro G _ _ N _ hcard _
    exact absurd hcard (Nat.not_le.mpr Nat.card_pos)
  | succ n ih =>
    intro G _ _ N hN hcard hsep
    have := hN
    rcases eq_or_ne N ⊥ with rfl | hNbot
    · exact .bot
    have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNbot
    obtain ⟨C, hC0, hCchar, hCpi⟩ := IsPiSeparable.exists_characteristic_ne_bot hsep
    have := hCchar
    have : (C.map N.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
    have hCle : C.map N.subtype ≤ N := Subgroup.map_subtype_le C
    have hCpi' : IsPiOrCompl π (C.map N.subtype) :=
      hCpi.transfer fun h ↦
        h.of_equiv (C.equivMapOfInjective N.subtype (Subgroup.subtype_injective N))
    -- pass to the quotient by `C`, where the image of `N` is a smaller normal subgroup
    have hqsurj : Function.Surjective (QuotientGroup.mk' (C.map N.subtype)) :=
      QuotientGroup.mk'_surjective _
    have : (N.map (QuotientGroup.mk' (C.map N.subtype))).Normal := hN.map _ hqsurj
    have hfsurj : Function.Surjective ((QuotientGroup.mk' (C.map N.subtype)).subgroupMap N) :=
      MonoidHom.subgroupMap_surjective _ N
    -- that image is `N ⧸ C`, so it is strictly smaller than `N`
    have hker : ((QuotientGroup.mk' (C.map N.subtype)).subgroupMap N).ker = C := by
      rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk', Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective N)]
    have hcard' : Nat.card (N.map (QuotientGroup.mk' (C.map N.subtype))) ≤ n := by
      have hiso : (N ⧸ C) ≃* (N.map (QuotientGroup.mk' (C.map N.subtype))) :=
        (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective _ hfsurj)
      have hcongr := Nat.card_congr hiso.toEquiv
      have hlt := card_quotient_lt C hC0
      omega
    have hchain := IsPiSeparableAt.comap (QuotientGroup.mk' (C.map N.subtype)) hqsurj
      (by
        rw [QuotientGroup.ker_mk']
        exact IsPiSeparableAt.of_isPiOrCompl hCpi')
      (ih (G ⧸ C.map N.subtype) (N.map (QuotientGroup.mk' (C.map N.subtype))) inferInstance hcard'
        (hsep.map _ hfsurj))
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hCle] at hchain

/-- A normal subgroup of a finite group which is `π`-separable *as a group* is the top term of a
normal series of the ambient group: its series can be taken to consist of subgroups normal in the
ambient group. -/
theorem IsPiSeparableAt.of_normal [Finite G] {N : Subgroup G} [N.Normal]
    (h : IsPiSeparable π N) : IsPiSeparableAt π N :=
  isPiSeparableAt_of_card_le π (Nat.card N) G N inferInstance le_rfl h

/-- **`π`-separability is closed under extensions.**  This is the content of Isaacs' Lemma 3.18:
the series of `N` need not consist of subgroups normal in `G`, but it may be replaced by one that
does, after which it can be continued by a series of `G ⧸ N`. -/
theorem IsPiSeparable.of_normal_of_quotient [Finite G] (N : Subgroup G) [N.Normal]
    (hN : IsPiSeparable π N) (hQ : IsPiSeparable π (G ⧸ N)) : IsPiSeparable π G := by
  have h := IsPiSeparableAt.comap (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    (by
      rw [QuotientGroup.ker_mk']
      exact IsPiSeparableAt.of_normal hN)
    hQ
  rwa [Subgroup.comap_top] at h

/--
The subnormal variant of `PiGroups.IsPiSeparableAt`: each term is only asked to be normal in the
next one, not in the ambient group.  This is the weakened form of the definition that Isaacs
considers just before Lemma 3.18.
-/
inductive IsPiSubnormalAt (π : Set ℕ) {G : Type*} [Group G] : Subgroup G → Prop where
  /-- The trivial subgroup is the start of the empty series. -/
  | bot : IsPiSubnormalAt π ⊥
  /-- A subgroup `K` tops such a series as soon as some `N ≤ K` normal *in `K`* does, with
  `K / N` a `π`-group or a `π'`-group. -/
  | step (N K : Subgroup G) (hle : N ≤ K) [(N.subgroupOf K).Normal] (hN : IsPiSubnormalAt π N)
      (hfactor : IsPiOrCompl π (K ⧸ N.subgroupOf K)) :
      IsPiSubnormalAt π K

/-- A normal series is in particular a subnormal series. -/
theorem IsPiSeparableAt.isPiSubnormalAt {K : Subgroup G} (h : IsPiSeparableAt π K) :
    IsPiSubnormalAt π K := by
  induction h with
  | bot => exact .bot
  | step N K hle _ hfactor ih => exact .step N K hle ih hfactor

/-- **Isaacs, Lemma 3.18.**  If `1 = N₀ ⊴ N₁ ⊴ ⋯ ⊴ N_r = K` is a series of subgroups, each normal
in the next, whose factors are `π`-groups or `π'`-groups, then `K` is `π`-separable. -/
theorem IsPiSubnormalAt.isPiSeparable [Finite G] {K : Subgroup G} (h : IsPiSubnormalAt π K) :
    IsPiSeparable π K := by
  induction h with
  | bot => exact IsPiSeparable.of_isPiGroup IsPiGroup.of_bot
  | step N K hle _ hfactor ih =>
    exact IsPiSeparable.of_normal_of_quotient (N.subgroupOf K)
      (ih.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm)
      (IsPiSeparable.of_isPiOrCompl hfactor)

/-- Isaacs' conclusion: weakening "normal series" to "subnormal series" in the definition of
`π`-separability yields exactly the same class of finite groups. -/
theorem isPiSeparable_iff_isPiSubnormalAt_top [Finite G] :
    IsPiSeparable π G ↔ IsPiSubnormalAt π (⊤ : Subgroup G) :=
  ⟨IsPiSeparableAt.isPiSubnormalAt, fun h ↦ h.isPiSeparable.of_mulEquiv Subgroup.topEquiv⟩

/-!
## Characteristic series

Isaacs also observes that *strengthening* the definition — asking the `Nᵢ` to be characteristic
rather than merely normal — describes the same class of groups.  This is what makes the weakened,
subnormal form of the definition work, and it is proved by iterating
`PiGroups.IsPiSeparable.exists_characteristic_ne_bot`: the paragraph's "continuing like this".
-/

/--
The characteristic variant of `PiGroups.IsPiSeparableAt`: every term of the series is asked to be
characteristic in the ambient group.
-/
inductive IsPiCharacteristicAt (π : Set ℕ) {G : Type*} [Group G] : Subgroup G → Prop where
  /-- The trivial subgroup is the start of the empty series. -/
  | bot : IsPiCharacteristicAt π ⊥
  /-- A subgroup `K` tops such a series as soon as some characteristic `N ≤ K` does, with `K / N`
  a `π`-group or a `π'`-group. -/
  | step (N K : Subgroup G) [N.Characteristic] (hle : N ≤ K) (hN : IsPiCharacteristicAt π N)
      (hfactor : IsPiOrCompl π (K ⧸ N.subgroupOf K)) :
      IsPiCharacteristicAt π K

namespace IsPiCharacteristicAt

/-- A characteristic series is in particular a normal series. -/
theorem isPiSeparableAt {K : Subgroup G} (h : IsPiCharacteristicAt π K) : IsPiSeparableAt π K := by
  induction h with
  | bot => exact .bot
  | step N K hle _ hfactor ih => exact .step N K hle ih hfactor

/-- A subgroup that is a `π`-group or a `π'`-group tops a series of length one; only the *lower*
term of a step has to be characteristic, and here that term is `⊥`. -/
theorem of_isPiOrCompl {K : Subgroup G} (h : IsPiOrCompl π K) : IsPiCharacteristicAt π K :=
  .step ⊥ K bot_le .bot (h.transfer fun hg ↦ hg.to_quotient _)

/-- A characteristic series of `G ⧸ C` pulls back to one of `G`, provided `C` itself carries
one. -/
theorem comap_mk' {C : Subgroup G} [C.Characteristic] (hC : IsPiCharacteristicAt π C)
    {D : Subgroup (G ⧸ C)} (h : IsPiCharacteristicAt π D) :
    IsPiCharacteristicAt π (D.comap (QuotientGroup.mk' C)) := by
  induction h with
  | bot =>
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    exact hC
  | step M D hle _ hfactor ih =>
    have := Subgroup.Characteristic.comap_quotient_mk (H := C) ‹M.Characteristic›
    exact .step (M.comap (QuotientGroup.mk' C)) (D.comap (QuotientGroup.mk' C))
      (Subgroup.comap_mono hle) ih
      (hfactor.transfer (IsPiGroup.factor_comap _ (QuotientGroup.mk'_surjective C)))

end IsPiCharacteristicAt

/-- Auxiliary induction on `|G|` behind `PiGroups.IsPiSeparable.isPiCharacteristicAt_top`: peel
off a nontrivial characteristic `π`- or `π'`-subgroup and continue inside the quotient. -/
theorem isPiCharacteristicAt_of_card_le (π : Set ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], IsPiSeparable π G →
      IsPiCharacteristicAt π (⊤ : Subgroup G) := by
  refine induction_on_card ?_
  intro G _ _ ih hsep
  rcases subsingleton_or_nontrivial G with hs | hs
  · rw [Subsingleton.elim (⊤ : Subgroup G) ⊥]
    exact .bot
  obtain ⟨C, hC0, hCchar, hCpi⟩ := hsep.exists_characteristic_ne_bot
  have := hCchar
  have hcard' : Nat.card (G ⧸ C) < Nat.card G := card_quotient_lt C hC0
  have hchain := IsPiCharacteristicAt.comap_mk' (IsPiCharacteristicAt.of_isPiOrCompl hCpi)
    (ih (G ⧸ C) hcard' (hsep.quotient C))
  rwa [Subgroup.comap_top] at hchain

/-- **Isaacs' characteristic series.**  A finite `π`-separable group has a series of
*characteristic* subgroups whose factors are `π`-groups and `π'`-groups. -/
theorem IsPiSeparable.isPiCharacteristicAt_top [Finite G] (h : IsPiSeparable π G) :
    IsPiCharacteristicAt π (⊤ : Subgroup G) :=
  isPiCharacteristicAt_of_card_le π G h

/-- Isaacs' remark: strengthening "normal series" to "characteristic series" in the definition of
`π`-separability yields exactly the same class of finite groups.  Together with
`PiGroups.isPiSeparable_iff_isPiSubnormalAt_top`, the three variants of the definition —
characteristic, normal, subnormal — all describe the same finite groups. -/
theorem isPiSeparable_iff_isPiCharacteristicAt_top [Finite G] :
    IsPiSeparable π G ↔ IsPiCharacteristicAt π (⊤ : Subgroup G) :=
  ⟨IsPiSeparable.isPiCharacteristicAt_top, IsPiCharacteristicAt.isPiSeparableAt⟩

/-!
## Solvable groups

Isaacs' Corollary 3.19: a finite solvable group is `π`-separable, for every set of primes `π`.

Isaacs argues with a composition series: its factors are simple and solvable, hence of prime
order, and a group of prime order is a `p`-group, so every factor is a `π`-group or a
`π'`-group and Lemma 3.18 applies.  We build the same series one step at a time instead, which
is what `PiGroups.IsPiSeparable.of_normal_of_quotient` — the content of Lemma 3.18 — is for:
the group is an extension of the abelian group `G / G'` by the derived subgroup `G'`, which is
smaller by `Group.IsSolvable.commutator_lt_top_of_nontrivial`, and a finite abelian group is handled
by splitting off a subgroup of prime order provided by Cauchy's theorem.
-/

/-- Auxiliary induction on `|A|` behind `PiGroups.IsPiSeparable.of_comm`: a finite commutative
group is `π`-separable.  Commutativity is taken as a hypothesis rather than as an instance, so
that the lemma also applies to quotients that are not syntactically `CommGroup`s. -/
theorem isPiSeparable_of_card_le_of_comm (π : Set ℕ) :
    ∀ (A : Type u) [Group A] [Finite A], (∀ a b : A, a * b = b * a) →
 IsPiSeparable π A := by
  refine induction_on_card ?_
  intro A _ _ ih hcomm
  rcases subsingleton_or_nontrivial A with hs | hs
  · exact IsPiSeparable.of_subsingleton
  -- Cauchy's theorem provides a subgroup of prime order
  have hcard1 : Nat.card A ≠ 1 := fun h ↦
    (not_subsingleton A) (Nat.card_eq_one_iff_unique.mp h).1
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hCnormal : (Subgroup.zpowers x).Normal :=
    ⟨fun a ha g ↦ by rwa [hcomm g a, mul_assoc, mul_inv_cancel, mul_one]⟩
  have hCcard : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
  have hCsep : IsPiSeparable π (Subgroup.zpowers x) :=
    IsPiSeparable.of_isPGroup hp (IsPGroup.of_card (n := 1) (by rw [hCcard, pow_one]))
  -- the quotient is commutative and strictly smaller
  have hqcomm : ∀ a b : A ⧸ Subgroup.zpowers x, a * b = b * a := by
    intro a b
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm]
  have hcard' : Nat.card (A ⧸ Subgroup.zpowers x) < Nat.card A :=
    card_quotient_lt (Subgroup.zpowers x)
      ((Subgroup.one_lt_card_iff_ne_bot _).mp (by rw [hCcard]; exact hp.one_lt))
  exact IsPiSeparable.of_normal_of_quotient _ hCsep
    (ih (A ⧸ Subgroup.zpowers x) hcard' hqcomm)

/-- A finite commutative group is `π`-separable, for every set of primes `π`. -/
theorem IsPiSeparable.of_comm [Finite G] (hcomm : ∀ a b : G, a * b = b * a) :
    IsPiSeparable π G :=
  isPiSeparable_of_card_le_of_comm π G hcomm

/-- Auxiliary induction on `|G|` behind `PiGroups.IsPiSeparable.of_isSolvable`. -/
theorem isPiSeparable_of_card_le_of_isSolvable (π : Set ℕ) :
    ∀ (G : Type u) [Group G] [Finite G] [Group.IsSolvable G],
      IsPiSeparable π G := by
  refine induction_on_card ?_
  intro G _ _ ih _
  rcases subsingleton_or_nontrivial G with hs | hs
  · exact IsPiSeparable.of_subsingleton
  -- the derived subgroup is proper, hence smaller
  have hne : commutator G ≠ ⊤ := ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial G)
  have hcard' : Nat.card (commutator G) < Nat.card G := by
    rw [← (commutator G).index_mul_card]
    exact lt_mul_of_one_lt_left Nat.card_pos (Subgroup.one_lt_index_of_ne_top hne)
  -- and the quotient by it is commutative: it is the abelianization
  have hqcomm : ∀ a b : G ⧸ commutator G, a * b = b * a :=
    fun a b ↦ mul_comm (G := Abelianization G) a b
  exact IsPiSeparable.of_normal_of_quotient (commutator G) (ih _ hcard')
    (IsPiSeparable.of_comm hqcomm)

/-- **Isaacs, Corollary 3.19.**  A finite solvable group is `π`-separable, for every set of
primes `π`.  So `π`-separability is indeed a generalisation of solvability. -/
theorem IsPiSeparable.of_isSolvable [Finite G] [Group.IsSolvable G] : IsPiSeparable π G :=
  isPiSeparable_of_card_le_of_isSolvable π G


/-!
## The Hall–Higman lemma

Isaacs' Theorem 3.21 (Hall–Higman 1.2.3): a finite `π`-separable group whose `π'`-core is trivial
has `C_G(O_π(G)) ≤ O_π(G)`, i.e. the `π`-core contains its own centralizer.

The proof is Isaacs'.  Put `C = C_G(O_π(G))` and `B = C ⊓ O_π(G)`, and suppose `B < C`.  The
group `C / B` is nontrivial and `π`-separable, so it has a nontrivial characteristic subgroup
`K / B`, which is normal in `G / B` because `C / B` is; hence `K ⊴ G` with `B ≤ K ≤ C`.  Were
`K / B` a `π`-group, so would be `K`, forcing `K ≤ O_π(G)` and hence `K ≤ B`.  So `K / B` is a
`π'`-group, and Schur–Zassenhaus provides a complement `H ≠ 1` of `B` in `K`.  But `K ≤ C`
centralizes `B`, so `H` is normal in `K`, and then `1 < H ≤ O_π'(K) ⊴ G` contradicts
`O_π'(G) = 1`.
-/

/-- **Isaacs, Theorem 3.21 (Hall–Higman 1.2.3).**  In a finite `π`-separable group whose
`π'`-core is trivial, the `π`-core contains its own centralizer. -/
theorem centralizer_piCore_le_piCore [Finite G] (hG : IsPiSeparable π G)
    (hπ' : piCore πᶜ G = ⊥) :
    Subgroup.centralizer (piCore π G : Set G) ≤ piCore π G := by
  by_contra hcon
  have : (Subgroup.centralizer (piCore π G : Set G)).Normal := inferInstance
  set C : Subgroup G := Subgroup.centralizer (piCore π G : Set G) with hCdef
  have : (C ⊓ piCore π G).Normal := inferInstance
  set B : Subgroup G := C ⊓ piCore π G with hBdef
  have hBC : B ≤ C := inf_le_left
  have hBP : B ≤ piCore π G := inf_le_right
  have hBpi : IsPiGroup π B := IsPiGroup.of_le hBP isPiGroup_piCore
  have hBneC : ¬ C ≤ B := fun hle ↦ hcon (hle.trans hBP)
  have hqsurj : Function.Surjective (QuotientGroup.mk' B) := QuotientGroup.mk'_surjective B
  -- the image `C / B` of `C` in `G ⧸ B` is nontrivial, normal and `π`-separable
  have : (C.map (QuotientGroup.mk' B)).Normal := ‹C.Normal›.map _ hqsurj
  have hCbar0 : C.map (QuotientGroup.mk' B) ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hBneC
  have : Nontrivial (C.map (QuotientGroup.mk' B)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hCbar0
  have hCbarsep : IsPiSeparable π (C.map (QuotientGroup.mk' B)) :=
    ((hG.subgroup C).quotient (B.subgroupOf C)).of_mulEquiv (quotientSubgroupOfEquivMap B C)
  -- it therefore has a nontrivial characteristic `π`- or `π'`-subgroup `D`
  obtain ⟨D, hD0, hDchar, hDpi⟩ := hCbarsep.exists_characteristic_ne_bot
  have := hDchar
  -- which, being characteristic in a normal subgroup, is normal in `G ⧸ B`
  have : (D.map (C.map (QuotientGroup.mk' B)).subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hKbar0 : D.map (C.map (QuotientGroup.mk' B)).subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)]
    exact hD0
  have hKbarpi : IsPiOrCompl π (D.map (C.map (QuotientGroup.mk' B)).subtype) :=
    hDpi.transfer fun h ↦ h.of_equiv (D.equivMapOfInjective _ (Subgroup.subtype_injective _))
  -- pull it back to `K` with `B ≤ K ≤ C` and `K ⊴ G`
  set K : Subgroup G :=
    (D.map (C.map (QuotientGroup.mk' B)).subtype).comap (QuotientGroup.mk' B) with hKdef
  have : K.Normal := ‹(D.map (C.map (QuotientGroup.mk' B)).subtype).Normal›.comap _
  have hBK : B ≤ K := by
    intro x hx
    have hx1 : (QuotientGroup.mk' B) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    simpa only [hKdef, Subgroup.mem_comap, hx1] using one_mem _
  have hKC : K ≤ C := by
    have h2 := Subgroup.comap_mono (f := QuotientGroup.mk' B)
      (Subgroup.map_subtype_le (H := C.map (QuotientGroup.mk' B)) D)
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hBC] at h2
  have hKmap : K.map (QuotientGroup.mk' B) = D.map (C.map (QuotientGroup.mk' B)).subtype :=
    Subgroup.map_comap_eq_self_of_surjective hqsurj _
  -- the factor `K / B` is exactly that subgroup
  have hiso : (↥K ⧸ B.subgroupOf K) ≃* ↥(D.map (C.map (QuotientGroup.mk' B)).subtype) :=
    (quotientSubgroupOfEquivMap B K).trans (MulEquiv.subgroupCongr hKmap)
  have hBKpi : IsPiGroup π (B.subgroupOf K) :=
    hBpi.of_equiv (Subgroup.subgroupOfEquivOfLe hBK).symm
  -- if `K ≤ B` then that subgroup is trivial, which it is not
  have hKB : ¬ K ≤ B := by
    intro hle
    refine hKbar0 ?_
    rw [← hKmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hle
  rcases hKbarpi with hpi | hpi'
  · -- `K` is a normal `π`-subgroup, so `K ≤ O_π(G) ⊓ C = B`
    exact hKB (le_inf hKC (le_piCore inferInstance
      (IsPiGroup.of_normal_of_quotient hBKpi (hpi.of_equiv hiso.symm))))
  · -- Schur–Zassenhaus splits `B` off inside `K`
    have hquot : IsPiGroup πᶜ (↥K ⧸ B.subgroupOf K) := hpi'.of_equiv hiso.symm
    obtain ⟨H, hHcompl⟩ := Subgroup.exists_right_complement'_of_coprime
      (N := B.subgroupOf K) (by rw [Subgroup.index_eq_card]; exact hBKpi.coprime_card hquot)
    -- the complement is nontrivial, since `B` is not all of `K`
    have hH0 : H ≠ ⊥ := by
      rintro rfl
      refine hKB ?_
      have : B.subgroupOf K = ⊤ := by simpa using hHcompl.sup_eq_top
      simpa [Subgroup.subgroupOf_eq_top] using this
    -- and it is a `π'`-group, being isomorphic to a subgroup of `K / B`
    have hHpi : IsPiGroup πᶜ H := by
      refine hquot.of_injective ((QuotientGroup.mk' (B.subgroupOf K)).comp H.subtype) ?_
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.coe_subtype] at hx
      have : (x : ↥K) ∈ B.subgroupOf K ⊓ H := ⟨hx, x.2⟩
      rw [disjoint_iff.mp hHcompl.disjoint] at this
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp this))
    -- `K` centralizes `B`, so the complement is normal in `K`
    have : H.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hHcompl.sup_eq_top]
      refine sup_le (fun b hb ↦ Subgroup.mem_normalizer_iff.mpr fun x ↦ ?_) Subgroup.le_normalizer
      have hfix : b * x * b⁻¹ = x := by
        apply Subtype.ext
        push_cast
        rw [Subgroup.mem_centralizer_iff.mp (hKC x.2) _ (hBP (Subgroup.mem_subgroupOf.mp hb)),
          mul_inv_cancel_right]
      rw [hfix]
    -- so `1 < H ≤ O_π'(K)`, which is a normal `π'`-subgroup of `G`
    have : ((piCore πᶜ ↥K).map K.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
    have hWle : (piCore πᶜ ↥K).map K.subtype ≤ piCore πᶜ G :=
      le_piCore inferInstance (isPiGroup_piCore.of_equiv
        ((piCore πᶜ ↥K).equivMapOfInjective _ (Subgroup.subtype_injective K)))
    rw [hπ', le_bot_iff,
      Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective K)] at hWle
    exact hH0 (le_bot_iff.mp (hWle ▸ le_piCore ‹H.Normal› hHpi))
end PiGroups
