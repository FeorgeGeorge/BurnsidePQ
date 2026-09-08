module

public import PreCFSG.PLocalSubgroups

/-!
# Burnside's `p ^ a q ^ b` theorem: the minimal counterexample

Isaacs, *Finite Group Theory*, Theorem 7.8: a finite group of order `p ^ a * q ^ b`, for primes
`p` and `q`, is solvable.  `mathlib` has Burnside's *normal `p`-complement* theorem
(`Mathlib/GroupTheory/Transfer.lean`) and Burnside's counting lemma, but not this theorem.

Isaacs argues from a counterexample of smallest order.  This file sets that situation up as
`Burnside.IsMinCounterexample` and proves the reductions of the opening paragraph of his proof:

* `Burnside.IsMinCounterexample.isSolvable_subgroup` / `.isSolvable_quotient`: every proper
  subgroup and every proper quotient is solvable, because its order still has at most the two
  prime divisors `p` and `q`;
* `Burnside.IsMinCounterexample.isSimpleGroup`: hence `G` is simple, since an extension of
  solvable by solvable is solvable;
* `Burnside.IsMinCounterexample.normalizer_eq_of_isCoatom`: if `1 < K ⊴ M` with `M` maximal, then
  `N_G(K) = M` — the observation Isaacs says "will be used repeatedly";
* `Burnside.IsMinCounterexample.piCore_ne_bot_or_of_isCoatom`: a maximal subgroup `M` is solvable
  and nontrivial, so `O_p(M) > 1` or `O_q(M) > 1`.

Two remarks on the formalization.

*Minimal counterexamples.*  `IsMinCounterexample p q G` bundles Isaacs' three standing
assumptions.  `Burnside.isSolvable_of_forall_not_isMinCounterexample` shows this really does
reduce the theorem: if no group is a minimal counterexample, every `{p, q}`-group is solvable.
So the remaining work is exactly to refute `IsMinCounterexample`.

*`{p, q}`-groups.*  "The order of `G` has at most the two prime divisors `p` and `q`" is
`PiGroups.IsPiGroup {p, q} G`, which by `PiGroups.IsPiGroup.iff_card` says precisely that
`(Nat.card G).primeFactors ⊆ {p, q}`.  Phrasing it this way rather than as `∃ a b, Nat.card G =
p ^ a * q ^ b` makes the closure under subgroups and quotients immediate, and connects directly
to the `π`-separability API: `O_p(M)` is `piCore {p} M` and `O_q(M)` is `piCore {p}ᶜ M`, the two
cores that `PiGroups.IsPiSeparable.piCore_ne_bot_or` produces.

Isaacs' proof continues in nine steps; the first one is

> **Step 1.**  Suppose that `K ⊆ G` is nilpotent, and assume that `M = N_G(K)` is a maximal
> subgroup of `G`.  If both `p` and `q` divide `|K|`, then `M` is the unique maximal subgroup of
> `G` containing `K`.

and its proof needs Isaacs' Theorem 4.33 (`O_p'(H) ≤ O_p'(G)` for `p`-local `H` in a
`p`-solvable `G`), which is now available as
`PiGroups.map_piCore_compl_le_piCore_compl`.
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
## What Step 1 still needs

Isaacs' Step 1 reads:

> Suppose that `K ⊆ G` is nilpotent, and assume that `M = N_G(K)` is a maximal subgroup of `G`.
> If both `p` and `q` divide `|K|`, then `M` is the unique maximal subgroup of `G` containing `K`.

Its proof takes `K` maximal among the counterexamples, writes `K = K_p × K_q`, notes
`M = N_G(K_p)` by `Burnside.IsMinCounterexample.normalizer_eq_of_isCoatom`, and then applies
Theorem 4.33 — `PiGroups.map_piCore_compl_le_piCore_compl`, proved in
`PreCFSG/PLocalSubgroups.lean` — to the `p`-local subgroup `M ∩ X = N_X(K_p)` of another maximal
subgroup `X ⊇ K`, to get `K_q ≤ O_q(X)`.  What is still missing for Step 1 is the decomposition of
a nilpotent `{p, q}`-group as `K = O_p(K) × O_q(K)` with both factors characteristic, and the
induction on `K` maximal among counterexamples.
-/

/-!
## The reduction
-/

/-- Auxiliary induction for `Burnside.isSolvable_of_forall_not_isMinCounterexample`. -/
theorem isSolvable_of_forall_not_aux
    (hno : ∀ (X : Type u) [Group X] [Finite X], ¬ IsMinCounterexample p q X) :
    ∀ (n : ℕ) (X : Type u) [Group X] [Finite X], Nat.card X ≤ n → IsPiGroup {p, q} X →
      Group.IsSolvable X := by
  intro n
  induction n with
  | zero =>
    intro X _ _ hcard _
    exact absurd hcard (Nat.not_le.mpr Nat.card_pos)
  | succ n ih =>
    intro X _ _ hcard hX
    by_contra hcon
    refine hno X ⟨hX, hcon, fun H _ _ hH hlt ↦ ih H ?_ hH⟩
    omega

/-- **The reduction to a minimal counterexample.**  If no group is a minimal counterexample, then
every `{p, q}`-group is solvable. -/
theorem isSolvable_of_forall_not_isMinCounterexample
    (hno : ∀ (X : Type u) [Group X] [Finite X], ¬ IsMinCounterexample p q X)
    (hG : IsPiGroup {p, q} G) : Group.IsSolvable G :=
  isSolvable_of_forall_not_aux hno (Nat.card G) G le_rfl hG

/-- **Burnside's `p ^ a q ^ b` theorem**, modulo the nonexistence of a minimal counterexample. -/
theorem isSolvable_of_card_eq
    (hno : ∀ (X : Type u) [Group X] [Finite X], ¬ IsMinCounterexample p q X)
    (hp : p.Prime) (hq : q.Prime) {a b : ℕ} (hcard : Nat.card G = p ^ a * q ^ b) :
    Group.IsSolvable G :=
  isSolvable_of_forall_not_isMinCounterexample hno (isPiGroup_pair_of_card_eq hp hq hcard)

end Burnside
