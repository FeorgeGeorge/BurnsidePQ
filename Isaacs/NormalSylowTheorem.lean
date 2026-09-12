module

public import Isaacs.ElementaryAbelianGL2
public import Isaacs.PLocalSubgroups

/-!
# Isaacs' Theorem 7.5, the "normal-`P` theorem"

Isaacs, *Finite Group Theory*, Theorem 7.5:

> Let `P ∈ Syl_p(G)`, where `G` is a finite group, and assume
> (1) `G` is `p`-solvable; (2) `p ≠ 2`; (3) a Sylow `2`-subgroup of `G` is abelian;
> (4) `G` acts faithfully on some `p`-group `V`; (5) `|V : C_V(P)| ≤ p`.  Then `P ⊴ G`.

This is `PiGroups.normal_sylow_of_faithful`.  It is what Step 8 of Isaacs' Theorem 7.6 (the
normal-`J` theorem, `Isaacs/NormalJTheorem.lean`) appeals to.

**Scope.**  In that application `V` is elementary abelian — it is `Ω₁(Z(O_p(G)))` — and Isaacs'
proof stays inside elementary abelian groups, since it only ever replaces `V` by a quotient of
itself.  Everything here is therefore stated for `V` a `CommGroup` of exponent `p`; that is the
case 7.6 needs.  The restriction is deliberate, and it pays for itself twice over: it makes every
subgroup of `V` normal, so the quotient `V / U` costs nothing, and it lets the hardest step
(`isPGroup_ker_quotientAut`) use Isaacs 4.34(a) in place of 4.29, which is what keeps this file
free of the `SchurZassenhausConjugacy` hypothesis that the rest of the development carries.

The pieces, in the order the proof uses them:

* `PiGroups.fixedOf` is `C_V(H)` for `H ≤ G`, and `PiGroups.actionKernel` is the kernel in `G` of
  the action on a subgroup of `V`; `PiGroups.le_actionKernel_iff` relates them, and
  `PiGroups.index_fixedOf_sylow_eq` says conjugate subgroups have fixed points of equal index;
* `PiGroups.actionOfHom` and `PiGroups.quotientAut` build the action of `G` on `V / U` for an
  invariant `U`, which is all the quotient-action machinery the induction needs;
* `PiGroups.isPGroup_ker_quotientAut`: the kernel `K` of the action on `V / U` is a `p`-group when
  `G` acts trivially on `U`.  A subgroup `A ≤ K` of order prime to `|V|` has `⁅V, A⁆ ≤ U ≤ C_V(A)`,
  so `⁅V, A⁆ = 1` by Isaacs 4.34(a) and `A = 1` by faithfulness; Cauchy then rules out every prime
  other than `p` in `|K|`;
* `PiGroups.commutative_of_faithful_isCyclic`: a group acting faithfully on a cyclic group is
  abelian, because the automorphism group of a cyclic group is;
* `PiGroups.normal_sylow_of_faithful_card_le_sq`: **7.5 once `|V| ≤ p ^ 2`**, the endgame, and
  where the work of `Isaacs/GL2Lemma.lean` and `Isaacs/ElementaryAbelianGL2.lean` is spent.  If
  `|V| ≤ p` then `V` is cyclic and `G` is abelian; otherwise `|V| = p ^ 2`, so `G ↪ GL(2, p)`,
  every `p`-subgroup of `G` has order at most `p`, and `O_p(G) = 1` unless `P` is already normal.
  Lemma 7.3 then makes `P` centralize `L = O_p′(G)`, and Hall–Higman puts `P` inside `L`, forcing
  `P = 1`;
* `PiGroups.normal_sylow_of_faithful`: the induction on `|G|` that reduces to that case.  If `P` is
  not normal there is a second Sylow `p`-subgroup `Q`, and `⟨P, Q⟩ = G`, since otherwise induction
  inside `⟨P, Q⟩` would make `P = Q`.  So `G` acts trivially on `U = C_V(P) ⊓ C_V(Q)`, of index at
  most `p ^ 2`, and `K ≤ P` because `K` is a normal `p`-subgroup.  If `K ≠ 1`, induction in `G / K`
  acting on `V / U` makes `P / K` normal, hence `P` normal; if `K = 1`, the endgame applies.

Mathlib has none of this: it has the Sylow theory and `MulDistribMulAction`, but no normal-`P`
theorem and no `p`-solvability.
-/

@[expose] public section

namespace PiGroups

open CoprimeAction

universe u

variable {p : ℕ} [Fact p.Prime]

/-!
## `O_p(G)` inside a Sylow `p`-subgroup
-/

omit [Fact p.Prime] in
/-- The `p`-core lies in every Sylow `p`-subgroup. -/
theorem piCore_le_sylow {G : Type u} [Group G] [Finite G] (P : Sylow p G) :
    piCore ({p} : Set ℕ) G ≤ (P : Subgroup G) := by
  have hp : IsPGroup p ↥(piCore ({p} : Set ℕ) G) := IsPiGroup.isPGroup isPiGroup_piCore
  have hsup : IsPGroup p ↥(piCore ({p} : Set ℕ) G ⊔ (P : Subgroup G) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left hp P.isPGroup'
  exact (P.is_maximal' hsup le_sup_right) ▸ le_sup_left

/-- The automorphism group of a cyclic group is abelian, so a group acting faithfully on a cyclic
group is abelian. -/
theorem commutative_of_faithful_isCyclic {G V : Type u} [Group G] [Group V]
    [MulDistribMulAction G V] [FaithfulSMul G V] [IsCyclic V] (x y : G) : x * y = y * x := by
  have hcomm : ∀ σ τ : MulAut V, σ * τ = τ * σ := fun σ τ =>
    (IsCyclic.mulAutMulEquiv V).injective (by rw [map_mul, map_mul, mul_comm])
  exact toMulAut_injective (by rw [map_mul, map_mul, hcomm])

/-- Every subgroup of a group all of whose elements commute is normal. -/
theorem normal_of_forall_commute {G : Type u} [Group G] (hcomm : ∀ x y : G, x * y = y * x)
    (H : Subgroup G) : H.Normal :=
  ⟨fun n hn g => by rw [hcomm g n, mul_assoc, mul_inv_cancel, mul_one]; exact hn⟩

/-- **Isaacs 7.5 once `|V| ≤ p ^ 2`**, the endgame of his proof.

If `|V| ≤ p` then `V` is cyclic, so `G` embeds in an abelian automorphism group and every
subgroup is normal.  Otherwise `|V| = p ^ 2`; then `|P| ≤ p`, so `O_p(G) = 1` unless `P` is
normal already, Lemma 7.3 makes `P` centralize `L = O_p′(G)`, and Hall–Higman gives `P ≤ L` —
impossible for a nontrivial `p`-group inside a `p′`-group. -/
theorem normal_sylow_of_faithful_card_le_sq {G V : Type u} [Group G] [Finite G] [CommGroup V]
    [Finite V] [MulDistribMulAction G V] [FaithfulSMul G V] (hp2 : p ≠ 2)
    (hsolv : IsPiSeparable ({p} : Set ℕ) G)
    (habel2 : ∀ B : Subgroup G, IsPGroup 2 B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hexp : ∀ x : V, x ^ p = 1) (hcard : Nat.card V ≤ p ^ 2) (P : Sylow p G) :
    (P : Subgroup G).Normal := by
  have hp : p.Prime := Fact.out
  have hVp : IsPGroup p V := fun g => ⟨1, by rw [pow_one]; exact hexp g⟩
  obtain ⟨n, hn⟩ := hVp.exists_card_eq
  -- `|V| ≤ p ^ 2` forces `n ≤ 2`
  have hn2 : n ≤ 2 := by
    by_contra hcon
    have : p ^ 3 ≤ p ^ n := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · -- `V` is cyclic, so `G` is abelian
    have : IsCyclic V := by
      interval_cases n
      · have h1 : Nat.card V = 1 := by rw [hn, pow_zero]
        have : Subsingleton V := (Nat.card_eq_one_iff_unique.mp h1).1
        exact isCyclic_of_subsingleton
      · exact isCyclic_of_prime_card (p := p) (by rw [hn, pow_one])
    exact normal_of_forall_commute (commutative_of_faithful_isCyclic (V := V)) _
  · -- `|V| = p ^ 2`
    have hcard2 : Nat.card V = p ^ 2 := by rw [hn]; congr 1; omega
    by_contra hPnorm
    -- every `p`-subgroup of `G` has order at most `p`
    have hPle : Nat.card ↥(P : Subgroup G) ≤ p :=
      card_le_of_isPGroup_of_faithful hexp hcard2 P.isPGroup'
    -- so `O_p(G) = 1`, since otherwise it would be all of `P`
    have hUle : piCore ({p} : Set ℕ) G ≤ (P : Subgroup G) := piCore_le_sylow P
    have hUne : piCore ({p} : Set ℕ) G ≠ (P : Subgroup G) := fun h => hPnorm (h ▸ inferInstance)
    have hUbot : piCore ({p} : Set ℕ) G = ⊥ := by
      obtain ⟨j, hj⟩ := (IsPiGroup.isPGroup (p := p)
        (isPiGroup_piCore (π := ({p} : Set ℕ)) (G := G))).exists_card_eq
      have hlt : Nat.card ↥(piCore ({p} : Set ℕ) G) < Nat.card ↥(P : Subgroup G) :=
        card_lt_card_of_lt (lt_of_le_of_ne hUle hUne)
      rw [hj] at hlt
      have hj0 : j = 0 := by
        by_contra hj0
        have hple : p ^ 1 ≤ p ^ j := Nat.pow_le_pow_right hp.pos (by omega)
        rw [pow_one] at hple
        omega
      refine Subgroup.eq_bot_of_card_eq _ ?_
      rw [hj, hj0, pow_zero]
    -- `P` centralizes `L = O_p'(G)` by Lemma 7.3
    have hLnorm : (P : Subgroup G)
        ≤ Subgroup.normalizer ((piCore ({p}ᶜ : Set ℕ) G : Subgroup G) : Set G) := fun g _ => by
      rw [Subgroup.normalizer_eq_top (piCore ({p}ᶜ : Set ℕ) G)]
      exact Subgroup.mem_top g
    have hLp : ¬ p ∣ Nat.card ↥(piCore ({p}ᶜ : Set ℕ) G) := by
      intro hdvd
      have hmem : p ∈ (Nat.card ↥(piCore ({p}ᶜ : Set ℕ) G)).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩
      exact (IsPiGroup.iff_card.mp isPiGroup_piCore p hmem) rfl
    have hcent := lemma_7_3_of_faithful (V := V) hp2 hexp hcard2 P.isPGroup' hLnorm hLp
      (fun B _ hB => habel2 B hB)
    -- Hall–Higman then puts `P` inside `L`
    have hPC : (P : Subgroup G)
        ≤ Subgroup.centralizer ((piCore ({p}ᶜ : Set ℕ) G : Subgroup G) : Set G) := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => (hcent x hx y hy).symm
    have hPL : (P : Subgroup G) ≤ piCore ({p}ᶜ : Set ℕ) G :=
      hPC.trans (centralizer_piCore_le_piCore hsolv.compl (by rw [compl_compl]; exact hUbot))
    -- but a `p`-group inside a `p'`-group is trivial
    have hdisj : Disjoint ((P : Subgroup G)) (piCore ({p}ᶜ : Set ℕ) G) :=
      disjoint_of_isPiGroup (IsPGroup.isPiGroup hp P.isPGroup') isPiGroup_piCore
    have hPbot : (P : Subgroup G) = ⊥ :=
      le_bot_iff.mp ((disjoint_iff.mp hdisj) ▸ le_inf le_rfl hPL)
    exact hPnorm (hPbot ▸ inferInstance)

/-!
## The data of Isaacs' reduction

Isaacs reduces to `|V| ≤ p ^ 2` by passing from `V` to `V / (C_V(P) ⊓ C_V(Q))` for a second Sylow
`p`-subgroup `Q`.  This section sets up the two subgroups involved: `C_V(H)` for `H ≤ G`, and the
kernel in `G` of the action on a subgroup of `V`.
-/

section Reduction

variable {G V : Type u} [Group G] [CommGroup V] [MulDistribMulAction G V]

variable (V) in
/-- `C_V(H)`: the elements of `V` fixed by every element of the subgroup `H ≤ G`. -/
def fixedOf (H : Subgroup G) : Subgroup V where
  carrier := {v : V | ∀ g ∈ H, g • v = v}
  one_mem' g _ := smul_one g
  mul_mem' ha hb g hg := by rw [smul_mul', ha g hg, hb g hg]
  inv_mem' ha g hg := by rw [smul_inv', ha g hg]

@[simp]
theorem mem_fixedOf {H : Subgroup G} {v : V} :
    v ∈ fixedOf V H ↔ ∀ g ∈ H, g • v = v := Iff.rfl

theorem fixedOf_antitone {H K : Subgroup G} (h : H ≤ K) : fixedOf V K ≤ fixedOf V H :=
  fun _ hv g hg => hv g (h hg)

variable (V) in
/-- The kernel in `G` of the action on a subgroup `W ≤ V`. -/
def actionKernel (W : Subgroup V) : Subgroup G where
  carrier := {g : G | ∀ v ∈ W, g • v = v}
  one_mem' v _ := one_smul G v
  mul_mem' ha hb v hv := by rw [mul_smul, hb v hv, ha v hv]
  inv_mem' {g} ha v hv := by
    have h := congrArg (fun x => g⁻¹ • x) (ha v hv)
    simp only [inv_smul_smul] at h
    exact h.symm

@[simp]
theorem mem_actionKernel {W : Subgroup V} {g : G} :
    g ∈ actionKernel V W ↔ ∀ v ∈ W, g • v = v := Iff.rfl

/-- `H` acts trivially on `W` exactly when `W ≤ C_V(H)`. -/
theorem le_actionKernel_iff {H : Subgroup G} {W : Subgroup V} :
    H ≤ actionKernel V W ↔ W ≤ fixedOf V H :=
  ⟨fun h v hv _g hg => h hg v hv, fun h g hg _v hv => h hv g hg⟩

/-- Conjugating the acting subgroup translates the fixed points: `C_V(H ^ g) = g • C_V(H)`. -/
theorem fixedOf_map_conj (H : Subgroup G) (g : G) :
    fixedOf V (H.map (MulAut.conj g).toMonoidHom)
      = (fixedOf V H).map (MulDistribMulAction.toMulAut G V g).toMonoidHom := by
  ext v
  constructor
  · intro hv
    refine ⟨g⁻¹ • v, fun h hh => ?_, ?_⟩
    · have hgv := hv (g * h * g⁻¹) ⟨h, hh, by simp [MulAut.conj_apply, mul_assoc]⟩
      calc h • (g⁻¹ • v) = (g⁻¹ * (g * h * g⁻¹)) • v := by rw [← mul_smul]; group
        _ = g⁻¹ • ((g * h * g⁻¹) • v) := mul_smul _ _ _
        _ = g⁻¹ • v := by rw [hgv]
    · change g • (g⁻¹ • v) = v
      rw [smul_smul, mul_inv_cancel, one_smul]
  · rintro ⟨w, hw, rfl⟩
    rintro - ⟨h, hh, rfl⟩
    change (MulAut.conj g h) • (g • w) = g • w
    rw [MulAut.conj_apply, ← mul_smul]
    have hgh : g * h * g⁻¹ * g = g * h := by group
    rw [hgh, mul_smul, SetLike.mem_coe.mp hw h hh]

/-- Conjugate subgroups have fixed points of the same index. -/
theorem index_fixedOf_map_conj (H : Subgroup G) (g : G) :
    (fixedOf V (H.map (MulAut.conj g).toMonoidHom)).index = (fixedOf V H).index := by
  rw [fixedOf_map_conj]
  exact Subgroup.index_map_equiv _ (MulDistribMulAction.toMulAut G V g)

/-- The distributive action determined by a homomorphism into the automorphism group. -/
@[instance_reducible]
def actionOfHom {X M : Type*} [Group X] [Monoid M] (φ : X →* MulAut M) :
    MulDistribMulAction X M where
  __ := MulAction.compHom M φ
  smul_one x := (φ x).map_one
  smul_mul x m n := (φ x).map_mul m n

theorem actionOfHom_smul {X M : Type*} [Group X] [Monoid M] (φ : X →* MulAut M) (x : X) (m : M) :
    (letI := actionOfHom φ; x • m) = φ x m := rfl

/-- An invariant subgroup `U ≤ V` gives an action of `G` on `V ⧸ U`. -/
def quotientAut {U : Subgroup V}
    (hU : ∀ g : G, U.map (MulDistribMulAction.toMulAut G V g).toMonoidHom = U) :
    G →* MulAut (V ⧸ U) where
  toFun g := QuotientGroup.congr U U (MulDistribMulAction.toMulAut G V g) (hU g)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H v => simp
  map_mul' g h := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H v => simp [mul_smul]

@[simp]
theorem quotientAut_mk {U : Subgroup V}
    (hU : ∀ g : G, U.map (MulDistribMulAction.toMulAut G V g).toMonoidHom = U) (g : G) (v : V) :
    quotientAut hU g (QuotientGroup.mk v) = QuotientGroup.mk (g • v) := rfl

/-- A subgroup on which `G` acts trivially is invariant. -/
theorem map_toMulAut_eq_self_of_le_fixedOf {U : Subgroup V}
    (hU : U ≤ fixedOf V (⊤ : Subgroup G)) (g : G) :
    U.map (MulDistribMulAction.toMulAut G V g).toMonoidHom = U := by
  have htriv : ∀ (a : G), ∀ v ∈ U, a • v = v := fun a v hv => hU hv a (Subgroup.mem_top a)
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    change g • w ∈ U
    rw [htriv g w hw]
    exact hw
  · intro hv
    exact ⟨v, hv, htriv g v hv⟩

/-- `C_V(H)` agrees with `mathlib`'s fixed-point subgroup for the restricted action. -/
theorem fixedOf_eq_fixedPoints (H : Subgroup G) :
    fixedOf V H = FixedPoints.subgroup ↑H V := by
  ext v
  exact ⟨fun hv m => hv (m : G) m.2, fun hv g hg => hv ⟨g, hg⟩⟩

/-- **Isaacs 7.5: the kernel of the action on `V ⧸ U` is a `p`-group.**

If `G` acts faithfully on the `p`-group `V` and trivially on `U ≤ V`, then a subgroup `A` of the
kernel `K` whose order is prime to `|V|` satisfies `⁅V, A⁆ ≤ U ≤ C_V(A)`, so `⁅V, A⁆ = 1` by
Isaacs 4.34(a) and `A = 1` by faithfulness.  Cauchy then rules out every prime other than `p` in
`|K|`. -/
theorem isPGroup_ker_quotientAut [Finite G] [Finite V] [FaithfulSMul G V] (hVp : IsPGroup p V)
    {U : Subgroup V} (hU : U ≤ fixedOf V (⊤ : Subgroup G)) :
    IsPGroup p ↑((quotientAut (map_toMulAut_eq_self_of_le_fixedOf hU)).ker) := by
  classical
  have hp : p.Prime := Fact.out
  set K : Subgroup G := (quotientAut (map_toMulAut_eq_self_of_le_fixedOf hU)).ker with hKdef
  -- an element of `K` moves each `v` only inside `U`
  have hKU : ∀ g ∈ K, ∀ v : V, v⁻¹ * (g • v) ∈ U := by
    intro g hg v
    have h1 : quotientAut (map_toMulAut_eq_self_of_le_fixedOf hU) g = 1 := MonoidHom.mem_ker.mp hg
    have h2 : (QuotientGroup.mk (g • v) : V ⧸ U) = QuotientGroup.mk v := by
      rw [← quotientAut_mk (map_toMulAut_eq_self_of_le_fixedOf hU) g v, h1]
      rfl
    exact (QuotientGroup.eq (s := U)).mp h2.symm
  -- every prime factor of `|K|` is `p`
  refine IsPiGroup.isPGroup (IsPiGroup.iff_card.mpr fun q hq => ?_)
  by_contra hqp
  obtain ⟨hqprime, hqdvd, -⟩ := Nat.mem_primeFactors.mp hq
  have : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↑K) q hqdvd
  -- the cyclic subgroup generated by `x` acts coprimely and trivially
  set A : Subgroup G := Subgroup.zpowers ((x : G)) with hAdef
  have hAK : A ≤ K := (Subgroup.zpowers_le).mpr x.2
  have hcardA : Nat.card ↑A = q := by
    rw [hAdef, Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hcop : Nat.Coprime (Nat.card ↑A) (Nat.card V) := by
    obtain ⟨m, hm⟩ := hVp.exists_card_eq
    rw [hcardA, hm]
    exact (Nat.Coprime.pow_right m ((Nat.coprime_primes hqprime hp).mpr hqp))
  -- `⁅V, A⁆ ≤ U ≤ C_V(A)`
  have hcomm_le : commutatorAction ↑A V ≤ U := by
    refine commutatorSubgroup_le fun a v _ => ?_
    exact hKU (a : G) (hAK a.2) v
  have hUfix : U ≤ FixedPoints.subgroup ↑A V := by
    rw [← fixedOf_eq_fixedPoints]
    exact fun v hv g _ => hU hv g (Subgroup.mem_top g)
  have hbot : commutatorAction ↑A V = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← CoprimeAction.fixedPoints_inf_commutatorAction_eq_bot (A := ↑A) (V := V) hcop]
    exact le_inf (hcomm_le.trans hUfix) le_rfl
  -- so `x` acts trivially, hence is trivial
  have hxtriv : ((x : ↑K) : G) = 1 := by
    refine eq_of_smul_eq_smul (α := V) (m₁ := ((x : ↑K) : G)) (m₂ := 1) fun v => ?_
    rw [one_smul]
    have := smul_eq_self_of_commutatorAction_eq_bot hbot
      (⟨((x : ↑K) : G), Subgroup.mem_zpowers _⟩ : ↑A) v
    exact this
  rw [← Subgroup.orderOf_coe, hxtriv, orderOf_one] at hx
  exact hqprime.one_lt.ne hx

/-- `C_V(P)` does not change when the action is restricted to a subgroup containing `P`. -/
theorem fixedOf_subgroupOf {H P : Subgroup G} (hPH : P ≤ H) :
    fixedOf V (P.subgroupOf H) = fixedOf V P := by
  ext v
  constructor
  · intro hv g hg
    exact hv ⟨g, hPH hg⟩ (by rwa [Subgroup.mem_subgroupOf])
  · intro hv g hg
    exact hv (g : G) (Subgroup.mem_subgroupOf.mp hg)

/-- All Sylow `p`-subgroups have fixed points of the same index, being conjugate. -/
theorem index_fixedOf_sylow_eq [Finite G] (P Q : Sylow p G) :
    (fixedOf V (Q : Subgroup G)).index = (fixedOf V (P : Subgroup G)).index := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hQ : (Q : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]; rfl
  rw [hQ, index_fixedOf_map_conj]

/-- A subgroup above the kernel keeps its index in the quotient. -/
theorem index_map_mk' {U W : Subgroup V} (hUW : U ≤ W) :
    (W.map (QuotientGroup.mk' U)).index = W.index := by
  rw [Subgroup.index_map, QuotientGroup.ker_mk', sup_eq_left.mpr hUW,
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective U), Subgroup.index_top, mul_one]

end Reduction

section Transfer

variable {G : Type u} [Group G]

/-- The hypothesis "every `2`-subgroup is abelian" passes to subgroups. -/
theorem forall_two_commute_subgroup
    (habel2 : ∀ B : Subgroup G, IsPGroup 2 ↑B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (H : Subgroup G) :
    ∀ B : Subgroup ↑H, IsPGroup 2 ↑B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
  intro B hB x hx y hy
  have h := habel2 (B.map H.subtype) (hB.map _) (x : G) ⟨x, hx, rfl⟩ (y : G) ⟨y, hy, rfl⟩
  exact Subtype.ext (by push_cast; exact h)

/-- A subgroup containing the kernel is normal as soon as its image is. -/
theorem normal_of_map_mk'_normal {K P : Subgroup G} [K.Normal] (hKP : K ≤ P)
    (h : (P.map (QuotientGroup.mk' K)).Normal) : P.Normal := by
  have heq : (P.map (QuotientGroup.mk' K)).comap (QuotientGroup.mk' K) = P :=
    Subgroup.comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])
  exact heq ▸ h.comap _

/-- Isaacs states the hypothesis as "a Sylow `2`-subgroup of `G` is abelian".  Since every
`2`-subgroup lies in a Sylow `2`-subgroup and Sylow `2`-subgroups are conjugate, that is the same
as asking every `2`-subgroup to be abelian, which is the form used here. -/
theorem forall_two_commute_iff_sylow [Finite G] (S : Sylow 2 G) :
    (∀ B : Subgroup G, IsPGroup 2 ↑B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ↔
      ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun h => h (S : Subgroup G) S.isPGroup', fun h B hB x hx y hy => ?_⟩
  obtain ⟨T, hBT⟩ := hB.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  have hTeq : (T : Subgroup G) = (S : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]; rfl
  obtain ⟨a, ha, rfl⟩ := hTeq ▸ hBT hx
  obtain ⟨b, hb, rfl⟩ := hTeq ▸ hBT hy
  rw [← map_mul, ← map_mul, h a ha b hb]

/-- The hypothesis "every `2`-subgroup is abelian" passes along surjections: a `2`-subgroup of
the image lies in a Sylow `2`-subgroup, and every Sylow `2`-subgroup of the image is the image
of one upstairs. -/
theorem forall_two_commute_surjective [Finite G] {G' : Type u} [Group G'] {f : G →* G'}
    (hf : Function.Surjective f)
    (habel2 : ∀ B : Subgroup G, IsPGroup 2 ↑B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    ∀ B : Subgroup G', IsPGroup 2 ↑B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite G' := Finite.of_surjective f hf
  intro B hB x hx y hy
  obtain ⟨T, hBT⟩ := hB.exists_le_sylow
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hf 2 T
  have hTeq : (T : Subgroup G') = (S : Subgroup G).map f := by rw [← hS]; rfl
  obtain ⟨a, ha, rfl⟩ := hTeq ▸ hBT hx
  obtain ⟨b, hb, rfl⟩ := hTeq ▸ hBT hy
  rw [← map_mul, ← map_mul, habel2 (S : Subgroup G) S.isPGroup' a ha b hb]

end Transfer

/-!
## Isaacs' Theorem 7.5 for elementary abelian modules
-/

/-- **Isaacs, Theorem 7.5 (the normal-`P` theorem)**, for an elementary abelian module `V`.

Let `P ∈ Syl_p(G)` with `G` `p`-solvable, `p ≠ 2`, every `2`-subgroup of `G` abelian, `G` acting
faithfully on an elementary abelian `p`-group `V`, and `|V : C_V(P)| ≤ p`.  Then `P ⊴ G`.

Isaacs' induction on `|G|`.  If `P` is not normal there is a second Sylow `p`-subgroup `Q`, and
`⟨P, Q⟩ = G` since otherwise induction inside `⟨P, Q⟩` would make `P = Q`.  Then `G` acts trivially
on `U = C_V(P) ⊓ C_V(Q)`, which has index at most `p ^ 2`, and the kernel `K` of the action on
`V / U` is a `p`-group, so `K ≤ P`.  If `K ≠ 1`, induction in `G / K` acting on `V / U` makes
`P / K` normal, hence `P` normal; if `K = 1`, then `G` acts faithfully on `V / U` and
`normal_sylow_of_faithful_card_le_sq` applies.  Either way `P ⊴ G`. -/
theorem normal_sylow_of_faithful {G V : Type u} [Group G] [Finite G] [CommGroup V] [Finite V]
    [MulDistribMulAction G V] [FaithfulSMul G V] (hp2 : p ≠ 2)
    (hsolv : IsPiSeparable ({p} : Set ℕ) G)
    (habel2 : ∀ B : Subgroup G, IsPGroup 2 ↥B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hexp : ∀ x : V, x ^ p = 1) (P : Sylow p G)
    (hidx : (fixedOf V (P : Subgroup G)).index ≤ p) :
    (P : Subgroup G).Normal := by
  have key : ∀ (n : ℕ) (X : Type u) [Group X] [Finite X], Nat.card X ≤ n →
      IsPiSeparable ({p} : Set ℕ) X →
      (∀ B : Subgroup X, IsPGroup 2 ↥B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      ∀ (W : Type u) [CommGroup W] [Finite W] [MulDistribMulAction X W] [FaithfulSMul X W],
        (∀ x : W, x ^ p = 1) → ∀ R : Sylow p X,
          (fixedOf W (R : Subgroup X)).index ≤ p → (R : Subgroup X).Normal := by
    intro n
    induction n with
    | zero =>
      intro X _ _ hcard
      exact absurd (Nat.card_pos (α := X)) (by omega)
    | succ n ih =>
      intro X _ _ hcard hsolvX habelX W _ _ _ _ hexpW R hidxR
      by_contra hRnorm
      have hWp : IsPGroup p W := fun g => ⟨1, by rw [pow_one]; exact hexpW g⟩
      -- a second Sylow `p`-subgroup
      obtain ⟨Q, hQR⟩ : ∃ Q : Sylow p X, (Q : Subgroup X) ≠ (R : Subgroup X) := by
        by_contra hall
        simp only [not_exists, not_not] at hall
        have : Subsingleton (Sylow p X) :=
          ⟨fun A B => Sylow.ext ((hall A).trans (hall B).symm)⟩
        exact hRnorm (Sylow.normal_of_subsingleton R)
      have hRH : (R : Subgroup X) ≤ (R : Subgroup X) ⊔ (Q : Subgroup X) := le_sup_left
      have hQH : (Q : Subgroup X) ≤ (R : Subgroup X) ⊔ (Q : Subgroup X) := le_sup_right
      -- `⟨R, Q⟩ = ⊤`
      have hHtop : (R : Subgroup X) ⊔ (Q : Subgroup X) = ⊤ := by
        by_contra hHne
        have hlt : Nat.card ↥((R : Subgroup X) ⊔ (Q : Subgroup X)) < Nat.card X := by
          calc Nat.card ↥((R : Subgroup X) ⊔ (Q : Subgroup X))
              < Nat.card ↥(⊤ : Subgroup X) := card_lt_card_of_lt (lt_of_le_of_ne le_top hHne)
            _ = Nat.card X := Subgroup.card_top
        have hnorm := ih ↥((R : Subgroup X) ⊔ (Q : Subgroup X)) (by omega)
          (hsolvX.subgroup _) (forall_two_commute_subgroup habelX _) W hexpW (R.subtype hRH)
          (by rw [Sylow.coe_subtype, fixedOf_subgroupOf hRH]; exact hidxR)
        have hu : Unique (Sylow p ↥((R : Subgroup X) ⊔ (Q : Subgroup X))) :=
          Sylow.unique_of_normal (R.subtype hRH) hnorm
        exact hQR (by rw [Sylow.subtype_injective
          ((hu.uniq (Q.subtype hQH)).trans (hu.uniq (R.subtype hRH)).symm)])
      -- `U = C_W(R) ⊓ C_W(Q)`, on which `X` acts trivially
      set U : Subgroup W := fixedOf W (R : Subgroup X) ⊓ fixedOf W (Q : Subgroup X) with hUdef
      have hUfix : U ≤ fixedOf W (⊤ : Subgroup X) := by
        rw [← le_actionKernel_iff, ← hHtop]
        exact sup_le (le_actionKernel_iff.mpr inf_le_left)
          (le_actionKernel_iff.mpr inf_le_right)
      have hUidx : U.index ≤ p ^ 2 := by
        calc U.index
            ≤ (fixedOf W (R : Subgroup X)).index * (fixedOf W (Q : Subgroup X)).index :=
              Subgroup.index_inf_le
          _ ≤ p * p := Nat.mul_le_mul hidxR (by rw [index_fixedOf_sylow_eq R Q]; exact hidxR)
          _ = p ^ 2 := (pow_two p).symm
      have hexpWU : ∀ x : W ⧸ U, x ^ p = 1 := by
        intro x
        induction x using QuotientGroup.induction_on with
        | H v =>
          have h1 : (QuotientGroup.mk' U) (v ^ p) = 1 := by rw [hexpW v, map_one]
          rw [map_pow] at h1
          exact h1
      have hcardWU : Nat.card (W ⧸ U) ≤ p ^ 2 := by
        rw [← Subgroup.index_eq_card]; exact hUidx
      -- the kernel of the action on `W ⧸ U`
      have hinv := map_toMulAut_eq_self_of_le_fixedOf hUfix
      have hKp : IsPGroup p ↥((quotientAut hinv).ker) := isPGroup_ker_quotientAut hWp hUfix
      have hKR : (quotientAut hinv).ker ≤ (R : Subgroup X) := hKp.le_sylow_of_normal R
      rcases eq_or_ne (quotientAut hinv).ker ⊥ with hKbot | hKne
      · -- `X` acts faithfully on `W ⧸ U`, of order at most `p ^ 2`
        let actX : MulDistribMulAction X (W ⧸ U) := actionOfHom (quotientAut hinv)
        have faithX : FaithfulSMul X (W ⧸ U) := ⟨fun {m₁ m₂} h => by
          have he : quotientAut hinv m₁ = quotientAut hinv m₂ := MulEquiv.ext fun x => h x
          have hmem : m₁ * m₂⁻¹ ∈ (quotientAut hinv).ker := by
            rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
          rw [hKbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
          exact hmem⟩
        exact hRnorm (normal_sylow_of_faithful_card_le_sq hp2 hsolvX habelX hexpWU hcardWU R)
      · -- pass to `X ⧸ K`
        let actQ : MulDistribMulAction (X ⧸ (quotientAut hinv).ker) (W ⧸ U) :=
          actionOfHom (QuotientGroup.kerLift (quotientAut hinv))
        have faithQ : FaithfulSMul (X ⧸ (quotientAut hinv).ker) (W ⧸ U) :=
          ⟨fun h => QuotientGroup.kerLift_injective _ (MulEquiv.ext fun x => h x)⟩
        have hsurj : Function.Surjective (QuotientGroup.mk' (quotientAut hinv).ker) :=
          QuotientGroup.mk'_surjective _
        have hipos : 0 < (quotientAut hinv).ker.index :=
          Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
        have hlt : Nat.card (X ⧸ (quotientAut hinv).ker) < Nat.card X := by
          rw [← Subgroup.index_eq_card, ← Subgroup.card_mul_index (quotientAut hinv).ker]
          calc (quotientAut hinv).ker.index = 1 * (quotientAut hinv).ker.index := (one_mul _).symm
            _ < Nat.card ↥((quotientAut hinv).ker) * (quotientAut hinv).ker.index :=
              (Nat.mul_lt_mul_right hipos).mpr ((Subgroup.one_lt_card_iff_ne_bot _).mpr hKne)
        -- the image of `C_W(R)` is fixed by the image of `R`
        have hmaple : (fixedOf W (R : Subgroup X)).map (QuotientGroup.mk' U)
            ≤ fixedOf (W ⧸ U) ((R.mapSurjective hsurj : Sylow p (X ⧸ (quotientAut hinv).ker)) :
              Subgroup (X ⧸ (quotientAut hinv).ker)) := by
          rintro - ⟨v, hv, rfl⟩
          rintro - ⟨g, hg, rfl⟩
          have hstep : (QuotientGroup.mk' (quotientAut hinv).ker) g • ((QuotientGroup.mk' U) v)
              = (QuotientGroup.mk' U) (g • v) := rfl
          rw [hstep, hv g hg]
        have hidxbar : (fixedOf (W ⧸ U)
            ((R.mapSurjective hsurj : Sylow p (X ⧸ (quotientAut hinv).ker)) :
              Subgroup (X ⧸ (quotientAut hinv).ker))).index ≤ p := by
          calc (fixedOf (W ⧸ U) ((R.mapSurjective hsurj : Sylow p (X ⧸ (quotientAut hinv).ker)) :
              Subgroup (X ⧸ (quotientAut hinv).ker))).index
              ≤ ((fixedOf W (R : Subgroup X)).map (QuotientGroup.mk' U)).index :=
                Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
                  (Subgroup.index_dvd_of_le hmaple)
            _ = (fixedOf W (R : Subgroup X)).index := index_map_mk' inf_le_left
            _ ≤ p := hidxR
        have hbar := ih (X ⧸ (quotientAut hinv).ker) (by omega)
          (hsolvX.quotient _) (forall_two_commute_surjective hsurj habelX) (W ⧸ U) hexpWU
          (R.mapSurjective hsurj) hidxbar
        refine hRnorm (normal_of_map_mk'_normal hKR ?_)
        rwa [← Sylow.coe_mapSurjective hsurj]
  exact key (Nat.card G) G le_rfl hsolv habel2 V hexp P hidx

end PiGroups
