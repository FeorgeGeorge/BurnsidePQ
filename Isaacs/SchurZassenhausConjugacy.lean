module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.OfQuotient
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Sylow

/-!
# Conjugacy of complements: discharging `SchurZassenhausConjugacy`

`CoprimeAction.SchurZassenhausConjugacy` (`Isaacs/GlaubermanLemma.lean`) is the statement that
complements of a normal Hall subgroup are conjugate when the subgroup or the quotient is solvable
— Huppert I.18.2.  `mathlib` has only the *existence* half of Schur–Zassenhaus
(`Subgroup.exists_right_complement'_of_coprime`), so the whole development downstream of
Glauberman's lemma carried this statement as an explicit hypothesis.  This file proves it, so
those results can be instantiated unconditionally.

## Provenance

The mathematical content is ported from the Qiuzhen CFSG project
(<https://github.com/Qiuzhen-CFSG/CFSG>, Apache 2.0), which proves Huppert I.18.2 in full:

* `exists_coboundary_of_cocycle_of_coprime_card` — `FeitThompson/GroupAction/Quotient.lean`
* `exists_principal_cocycle_of_solvable_coprime` — `FeitThompson/HallSubgroups/Conjugacy.lean`
* `principal_cocycle_of_pgroup_operator`, `principal_cocycle_of_solvable_operator`,
  `complements_conjugate_of_solvable_normal`, `complements_conjugate_of_solvable_quotient`,
  `complements_conjugate_of_solvable` — `BenderSuzuki/External/Huppert/I/theorem_18_3.lean`
  (`huppert_I_18_2_*` there)

CFSG's file also proves Huppert I.18.3, the unrestricted statement, which needs the odd order
theorem; that is why it imports `FeitThompson.FinalTheorem` and cannot be imported directly (its
closure is 537 modules, 619k lines).  Only 18.2 is needed here, and it uses no such input.

Two deviations from the CFSG text:

* the conjugation action of `H` on a normal `N` is built from `MulAut.conjNormal` rather than
  CFSG's `Subgroup.conjMulDistribMulActionOfLeNormalizer`;
* in the solvable-operator induction, CFSG takes a minimal normal subgroup of the operator group
  and invokes its chief-factor development to see that it is elementary abelian.  All the argument
  needs is a nontrivial normal `p`-subgroup, so `exists_normal_isPGroup_ne_bot` supplies one
  directly, from the derived series and a Sylow subgroup of its last nontrivial term.
-/

@[expose] public section

namespace SchurZassenhausConj

universe u v

/-!
## The induced action on a quotient
-/

section QuotientAction

variable {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]

/-- The action by automorphisms induced on `G ⧸ N` by an action leaving `N` invariant. -/
@[reducible]
def quotientMulDistribMulAction {N : Subgroup G} [N.Normal]
    (hN : ∀ (a : A), ∀ n ∈ N, a • n ∈ N) : MulDistribMulAction A (G ⧸ N) where
  smul a := QuotientGroup.map N N (MulDistribMulAction.toMulAut A G a).toMonoidHom (hN a)
  one_smul x := by
    induction x using QuotientGroup.induction_on with
    | _ y => exact congrArg (QuotientGroup.mk (s := N)) (one_smul A y)
  mul_smul a b x := by
    induction x using QuotientGroup.induction_on with
    | _ y => exact congrArg (QuotientGroup.mk (s := N)) (mul_smul a b y)
  smul_mul a x y := by
    induction x using QuotientGroup.induction_on with
    | _ u =>
      induction y using QuotientGroup.induction_on with
      | _ v => exact congrArg (QuotientGroup.mk (s := N)) (smul_mul' a u v)
  smul_one a := congrArg (QuotientGroup.mk (s := N)) (smul_one a)

theorem quotientMulDistribMulAction_mk {N : Subgroup G} [N.Normal]
    (hN : ∀ (a : A), ∀ n ∈ N, a • n ∈ N) (a : A) (x : G) :
    letI := quotientMulDistribMulAction hN
    a • (x : G ⧸ N) = ((a • x : G) : G ⧸ N) := rfl

/-- The restriction of an action by automorphisms to an invariant subgroup. -/
@[reducible]
def subgroupMulDistribMulAction {N : Subgroup G} (hN : ∀ (a : A), ∀ n ∈ N, a • n ∈ N) :
    MulDistribMulAction A N where
  smul a x := ⟨a • (x : G), hN a x x.2⟩
  one_smul x := by ext; exact one_smul A (x : G)
  mul_smul a b x := by ext; exact mul_smul a b (x : G)
  smul_mul a x y := by ext; exact smul_mul' a (x : G) (y : G)
  smul_one a := by ext; exact smul_one a

/-- A characteristic subgroup is invariant under any action by automorphisms. -/
theorem smul_mem_of_characteristic (N : Subgroup G) [N.Characteristic] (a : A) {n : G}
    (hn : n ∈ N) : a • n ∈ N := by
  have h := Subgroup.characteristic_iff_map_eq.mp ‹N.Characteristic›
    (MulDistribMulAction.toMulAut A G a)
  rw [← h]
  exact ⟨n, hn, rfl⟩

end QuotientAction

/-!
## Conjugation of a normal subgroup by a subgroup
-/

section ConjAction

variable {G : Type*} [Group G]

/-- Conjugation makes a subgroup `H` act by automorphisms on a normal subgroup `N`. -/
@[reducible]
def conjAction (H N : Subgroup G) [N.Normal] : MulDistribMulAction H N :=
  MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp H.subtype)

theorem conjAction_coe (H N : Subgroup G) [N.Normal] (h : H) (n : N) :
    letI := conjAction H N
    ((h • n : N) : G) = (h : G) * (n : G) * (h : G)⁻¹ :=
  MulAut.conjNormal_apply (h : G) n

end ConjAction

/-!
## `H¹` vanishes for a coprime action on an abelian group

Ported from CFSG, `FeitThompson/GroupAction/Quotient.lean`.
-/

section CoprimeCocycle

variable {A N : Type*} [Group A] [Finite A] [CommGroup N] [Finite N]
variable [MulDistribMulAction A N]

/-- If `c : A → N` is a 1-cocycle and `|A|` is coprime to `|N|`, then `c` is a 1-coboundary. -/
theorem exists_coboundary_of_cocycle_of_coprime_card
    (c : A → N) (hc : ∀ a b : A, c (a * b) = c a * (a • c b))
    (hcop : Nat.Coprime (Nat.card A) (Nat.card N)) :
    ∃ n : N, ∀ a : A, c a = (a • n)⁻¹ * n := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype N := Fintype.ofFinite N
  let m : ℕ := Fintype.card A
  let t : N := (Finset.univ : Finset A).prod c
  have hsmul_t (b : A) : b • t = (c b)⁻¹ ^ m * t := by
    have hbca (a : A) : b • c a = (c b)⁻¹ * c (b * a) := by
      have h1 := hc b a
      have h2 := congrArg (fun x : N => (c b)⁻¹ * x) h1
      simpa [mul_assoc] using h2.symm
    have hreindex :
        (Finset.univ : Finset A).prod (fun a : A => c (b * a)) =
          (Finset.univ : Finset A).prod c := by
      simpa using
        (Finset.prod_bij
          (s := (Finset.univ : Finset A))
          (t := (Finset.univ : Finset A))
          (i := fun a _ha => b * a)
          (f := fun a : A => c (b * a))
          (g := c)
          (hi := by intro a ha; simp)
          (i_inj := by
            intro a₁ ha₁ a₂ ha₂ h
            exact mul_left_cancel h)
          (i_surj := by
            intro a ha
            refine ⟨b⁻¹ * a, by simp, ?_⟩
            simp)
          (h := by intro a ha; rfl))
    calc
      b • t
          = (Finset.univ : Finset A).prod (fun a : A => b • c a) := by
              simpa [t] using
                (Finset.smul_prod' (r := b) (f := c) (s := (Finset.univ : Finset A)))
      _ = (Finset.univ : Finset A).prod (fun a : A => (c b)⁻¹ * c (b * a)) := by
              refine Finset.prod_congr rfl (fun a _ha => ?_)
              simp [hbca]
      _ = ((Finset.univ : Finset A).prod (fun _a : A => (c b)⁻¹)) *
            (Finset.univ : Finset A).prod (fun a : A => c (b * a)) := by
              simp [Finset.prod_mul_distrib]
      _ = (c b)⁻¹ ^ m * (Finset.univ : Finset A).prod (fun a : A => c (b * a)) := by
              simp [Finset.prod_const, m]
      _ = (c b)⁻¹ ^ m * t := by
              simpa [t] using congrArg (fun x => (c b)⁻¹ ^ m * x) hreindex
  have hpow : Nat.Coprime (Nat.card N) m := by
    simpa [m, Nat.card_eq_fintype_card] using hcop.symm
  let e : N ≃ N := powCoprime (G := N) (n := m) hpow
  let n : N := e.symm t
  have hn_pow : n ^ m = t := by
    simpa [n, e] using (e.apply_symm_apply t)
  refine ⟨n, ?_⟩
  intro b
  have ht_rel : t * (b • t)⁻¹ = (c b) ^ m := by
    have hb : b • t = (c b)⁻¹ ^ m * t := hsmul_t b
    have hb' : (b • t) * t⁻¹ = (c b)⁻¹ ^ m := by
      simpa [mul_assoc] using congrArg (fun x => x * t⁻¹) hb
    calc
      t * (b • t)⁻¹ = ((b • t) * t⁻¹)⁻¹ := by simp
      _ = ((c b)⁻¹ ^ m)⁻¹ := by simp [hb']
      _ = (c b) ^ m := by simp
  have hpow_eq : ((b • n)⁻¹ * n) ^ m = (c b) ^ m := by
    have hbn_pow : (b • n) ^ m = b • t := by
      have hsm : b • (n ^ m) = (b • n) ^ m := by simp
      simpa [hn_pow] using hsm.symm
    calc
      ((b • n)⁻¹ * n) ^ m
          = (b • n)⁻¹ ^ m * (n ^ m) := by simp [mul_pow, mul_comm]
      _ = ((b • n) ^ m)⁻¹ * t := by simp [hn_pow]
      _ = (b • t)⁻¹ * t := by simp [hbn_pow]
      _ = t * (b • t)⁻¹ := by simp [mul_comm]
      _ = (c b) ^ m := by simp [ht_rel]
  have hinj : Function.Injective fun x : N => x ^ m :=
    (powCoprime (G := N) (n := m) hpow).injective
  exact (hinj hpow_eq).symm

end CoprimeCocycle


/-!
## Cocycles into a solvable module

Ported from CFSG, `FeitThompson/HallSubgroups/Conjugacy.lean`.
-/

open scoped IsMulCommutative in
/-- A 1-cocycle into a solvable module of coprime order is principal. -/
theorem exists_principal_cocycle_of_solvable_coprime {A : Type v} [Group A] [Finite A] :
    ∀ {N : Type u} [Group N] [Finite N] [MulDistribMulAction A N],
      Group.IsSolvable N →
      Nat.Coprime (Nat.card A) (Nat.card N) →
      ∀ c : A → N, (∀ a b : A, c (a * b) = c a * (a • c b)) →
        ∃ x : N, ∀ a : A, c a = x * (a • x)⁻¹ := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (N' : Type u) [Group N'] [Finite N'] [MulDistribMulAction A N'],
      Nat.card N' = n →
      Group.IsSolvable N' →
      Nat.Coprime (Nat.card A) (Nat.card N') →
      ∀ c : A → N', (∀ a b : A, c (a * b) = c a * (a • c b)) →
        ∃ x : N', ∀ a : A, c a = x * (a • x)⁻¹
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih N' _ _ _ hcard hsolv' hcop' c hc
    by_cases hcomm : IsMulCommutative N'
    · let : IsMulCommutative N' := hcomm
      obtain ⟨x, hx⟩ :=
        exists_coboundary_of_cocycle_of_coprime_card (A := A) (N := N') c hc hcop'
      refine ⟨x, ?_⟩
      intro a
      simpa [mul_comm] using hx a
    · have hnot_subsingleton : ¬ Subsingleton N' := by
        intro hsub
        exact hcomm ⟨⟨fun x y => by rw [hsub.elim x 1, hsub.elim y 1]⟩⟩
      have : Nontrivial N' := not_subsingleton_iff_nontrivial.mp hnot_subsingleton
      have : Group.IsSolvable N' := hsolv'
      have hDlt_top : commutator N' < ⊤ :=
        Group.IsSolvable.commutator_lt_top_of_nontrivial (G := N')
      have hDinv : ∀ (a : A), ∀ x ∈ commutator N', a • x ∈ commutator N' :=
        fun a _ hx => smul_mem_of_characteristic (commutator N') a hx
      let : MulDistribMulAction A (N' ⧸ commutator N') := quotientMulDistribMulAction hDinv
      let : MulDistribMulAction A (commutator N') := subgroupMulDistribMulAction hDinv
      have hsmulQ : ∀ (a : A) (x : N'),
          a • ((x : N' ⧸ commutator N')) = ((a • x : N') : N' ⧸ commutator N') := fun _ _ => rfl
      have : IsMulCommutative (N' ⧸ commutator N') :=
        (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := commutator N')).2 le_rfl
      let cQ : A → N' ⧸ commutator N' := fun a => ((c a : N') : N' ⧸ commutator N')
      have hcQ : ∀ a b : A, cQ (a * b) = cQ a * (a • cQ b) := by
        intro a b
        have h1 : cQ (a * b) = ((c a * (a • c b) : N') : N' ⧸ commutator N') :=
          congrArg (QuotientGroup.mk (s := commutator N')) (hc a b)
        rw [h1, hsmulQ]
        rfl
      have hcopQ : Nat.Coprime (Nat.card A) (Nat.card (N' ⧸ commutator N')) := by
        have hdvd : Nat.card (N' ⧸ commutator N') ∣ Nat.card N' :=
          Subgroup.card_quotient_dvd_card (s := commutator N')
        exact Nat.Coprime.of_dvd_right hdvd hcop'
      obtain ⟨xQ, hxQ⟩ :=
        exists_coboundary_of_cocycle_of_coprime_card
          (A := A) (N := N' ⧸ commutator N') cQ hcQ hcopQ
      obtain ⟨x0, rfl⟩ := QuotientGroup.mk_surjective (s := commutator N') xQ
      let cD : A → commutator N' := fun a =>
        ⟨x0⁻¹ * c a * (a • x0), by
          have hEqQ : ((c a : N') : N' ⧸ commutator N')
              = ((x0 * (a • x0)⁻¹ : N') : N' ⧸ commutator N') := by
            have h2 := hxQ a
            rw [hsmulQ] at h2
            calc ((c a : N') : N' ⧸ commutator N')
                = (((a • x0 : N') : N' ⧸ commutator N'))⁻¹ * ((x0 : N') : N' ⧸ commutator N') := h2
              _ = ((x0 : N') : N' ⧸ commutator N') * (((a • x0 : N') : N' ⧸ commutator N'))⁻¹ := by
                    rw [mul_comm]
              _ = ((x0 * (a • x0)⁻¹ : N') : N' ⧸ commutator N') := by
                    simp
          have hdiv_mem : (x0 * (a • x0)⁻¹) / c a ∈ commutator N' :=
            (QuotientGroup.eq_iff_div_mem).1 hEqQ.symm
          have hmul_mem : c a * (a • x0) * x0⁻¹ ∈ commutator N' := by
            have hdiv_inv : ((x0 * (a • x0)⁻¹) / c a)⁻¹ ∈ commutator N' :=
              (commutator N').inv_mem hdiv_mem
            simpa [div_eq_mul_inv, mul_assoc] using hdiv_inv
          have hconj : x0⁻¹ * (c a * (a • x0) * x0⁻¹) * (x0⁻¹)⁻¹ ∈ commutator N' :=
            (inferInstance : (commutator N').Normal).conj_mem _ hmul_mem x0⁻¹
          simpa [mul_assoc] using hconj⟩
      have hcD : ∀ a b : A, cD (a * b) = cD a * (a • cD b) := by
        intro a b
        ext
        change x0⁻¹ * c (a * b) * ((a * b) • x0) =
          (x0⁻¹ * c a * (a • x0)) * (a • (x0⁻¹ * c b * (b • x0)))
        simp [hc, smul_mul', smul_smul, mul_assoc]
      have hcopD : Nat.Coprime (Nat.card A) (Nat.card (commutator N')) := by
        have hdvd : Nat.card (commutator N') ∣ Nat.card N' :=
          Subgroup.card_subgroup_dvd_card (s := commutator N')
        exact Nat.Coprime.of_dvd_right hdvd hcop'
      have hDlt : Nat.card (commutator N') < n := by
        have hD_one_lt : 1 < (commutator N').index :=
          Subgroup.one_lt_index_of_ne_top (ne_of_lt hDlt_top)
        have hD_pos : 0 < Nat.card (commutator N') := Nat.card_pos
        have hlt : Nat.card (commutator N') < Nat.card (commutator N') * (commutator N').index := by
          simpa [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left hD_one_lt hD_pos
        have hEq : Nat.card (commutator N') * (commutator N').index = n := by
          calc Nat.card (commutator N') * (commutator N').index
              = (commutator N').index * Nat.card (commutator N') := by simp [Nat.mul_comm]
            _ = Nat.card N' := by simpa using (Subgroup.index_mul_card (H := commutator N'))
            _ = n := hcard
        simpa [hEq] using hlt
      obtain ⟨y, hy⟩ :=
        (ih (Nat.card (commutator N')) hDlt) (commutator N') rfl inferInstance hcopD cD hcD
      refine ⟨x0 * (y : N'), ?_⟩
      intro a
      have hy' : x0⁻¹ * c a * (a • x0) = (y : N') * (a • (y : N'))⁻¹ := by
        have htmp := congrArg Subtype.val (hy a)
        change x0⁻¹ * c a * (a • x0) = (y : N') * (a • (y : N'))⁻¹ at htmp
        exact htmp
      calc
        c a = x0 * (x0⁻¹ * c a * (a • x0)) * (a • x0)⁻¹ := by simp [mul_assoc]
        _ = x0 * ((y : N') * (a • (y : N'))⁻¹) * (a • x0)⁻¹ := by rw [hy']
        _ = (x0 * (y : N')) * (a • (x0 * (y : N')))⁻¹ := by simp [smul_mul', mul_assoc]
  exact fun {N} _ _ _ hsolv hcop c hc => hP (Nat.card N) N rfl hsolv hcop c hc


/-!
## Cocycles with a `p`-group operator

Ported from CFSG, `BenderSuzuki/External/Huppert/I/theorem_18_3.lean`
(`huppert_I_18_2_b_principal_cocycle_of_pgroup_operator`).
-/

/-- A 1-cocycle for a `p`-group acting on a group of order prime to `p` is principal: twist the
action by the cocycle and take a fixed point. -/
theorem principal_cocycle_of_pgroup_operator {X : Type u} {A : Type v}
    [Group X] [Finite X] [Group A] [Finite A]
    [MulDistribMulAction A X] {r : ℕ} [Fact r.Prime] [Fact (IsPGroup r A)]
    (hcoprime : Nat.Coprime r (Nat.card X))
    (c : A → X) (hc : ∀ a b : A, c (a * b) = c a * (a • c b)) :
    ∃ x : X, ∀ a : A, c a = x * (a • x)⁻¹ := by
  classical
  let originalSmul : A → X → X := fun a x => a • x
  have hc_one : c 1 = 1 := by
    have h : c 1 = c 1 * c 1 := by simpa using hc 1 1
    calc
      c 1 = (c 1)⁻¹ * (c 1 * c 1) := by simp
      _ = (c 1)⁻¹ * c 1 := by rw [← h]
      _ = 1 := by simp
  let : MulAction A X :=
    { smul := fun a x => c a * originalSmul a x
      one_smul := by
        intro x
        change c 1 * originalSmul 1 x = x
        dsimp [originalSmul]
        simp [hc_one]
      mul_smul := by
        intro a b x
        change c (a * b) * originalSmul (a * b) x =
          c a * originalSmul a (c b * originalSmul b x)
        dsimp [originalSmul]
        rw [hc a b]
        simp [smul_mul', smul_smul, mul_assoc] }
  have hr_not_dvd : ¬ r ∣ Nat.card X :=
    ((Fact.out : Nat.Prime r).coprime_iff_not_dvd).1 hcoprime
  rcases (Fact.out : IsPGroup r A).nonempty_fixed_point_of_prime_not_dvd_card
      X hr_not_dvd with ⟨x, hxfix⟩
  refine ⟨x, ?_⟩
  intro a
  have hx : c a * originalSmul a x = x := by
    have hfix := (MulAction.mem_fixedPoints.mp hxfix) a
    change c a * originalSmul a x = x at hfix
    exact hfix
  change c a = x * (originalSmul a x)⁻¹
  calc
    c a = (c a * originalSmul a x) * (originalSmul a x)⁻¹ := by simp
    _ = x * (originalSmul a x)⁻¹ := by rw [hx]

/-!
## A normal `p`-subgroup of a solvable group

This replaces CFSG's use of a minimal normal subgroup and its chief-factor development: the
solvable-operator induction below only needs *some* nontrivial normal `p`-subgroup, and the last
nontrivial term of the derived series supplies one through any of its Sylow subgroups.
-/

open scoped IsMulCommutative in
/-- A nontrivial finite solvable group has a nontrivial normal `p`-subgroup for some prime `p`. -/
theorem exists_normal_isPGroup_ne_bot (A : Type u) [Group A] [Finite A] [Group.IsSolvable A]
    [Nontrivial A] :
    ∃ (r : ℕ) (B : Subgroup A), r.Prime ∧ B.Normal ∧ B ≠ ⊥ ∧ IsPGroup r B := by
  classical
  have hex : ∃ k, derivedSeries A k = ⊥ := (Group.isSolvable_def A).mp ‹_›
  have h0 : derivedSeries A 0 ≠ ⊥ := by
    rw [derivedSeries_zero]
    exact top_ne_bot
  have hk : derivedSeries A (Nat.find hex) = ⊥ := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hk
    exact h0 hk
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hDne : derivedSeries A m ≠ ⊥ := Nat.find_min hex (by omega)
  -- the last nontrivial term of the derived series is abelian
  have hcomm_bot : ⁅derivedSeries A m, derivedSeries A m⁆ = ⊥ := by
    rw [← derivedSeries_succ, ← hm]
    exact hk
  have : IsMulCommutative (derivedSeries A m) :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := derivedSeries A m)).mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := derivedSeries A m)
        (H₂ := derivedSeries A m)).mp hcomm_bot)
  have : Nontrivial (derivedSeries A m) := (Subgroup.nontrivial_iff_ne_bot _).mpr hDne
  -- one of its Sylow subgroups is characteristic in it, hence normal in `A`
  obtain ⟨r, hrp, hrdvd⟩ : ∃ r, r.Prime ∧ r ∣ Nat.card (derivedSeries A m) :=
    Nat.exists_prime_and_dvd (by
      have : 1 < Nat.card (derivedSeries A m) := Finite.one_lt_card
      omega)
  have : Fact r.Prime := ⟨hrp⟩
  obtain ⟨P⟩ : Nonempty (Sylow r (derivedSeries A m)) := inferInstance
  have hPn : (P : Subgroup (derivedSeries A m)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hgx : g * x * g⁻¹ = x := by
      rw [mul_comm g x, mul_assoc, mul_inv_cancel, mul_one]
    rwa [hgx]
  have : (P : Subgroup (derivedSeries A m)).Characteristic := P.characteristic_of_normal hPn
  have hPcard : Nat.card (P : Subgroup (derivedSeries A m))
      = r ^ (Nat.card (derivedSeries A m)).factorization r := P.card_eq_multiplicity
  have hfac : (Nat.card (derivedSeries A m)).factorization r ≠ 0 :=
    (hrp.factorization_pos_of_dvd Nat.card_pos.ne' hrdvd).ne'
  have hPne : (P : Subgroup (derivedSeries A m)) ≠ ⊥ := by
    rw [Ne, ← Subgroup.card_eq_one, hPcard]
    intro hcon
    rcases Nat.pow_eq_one.mp hcon with h | h
    · exact hrp.ne_one h
    · exact hfac h
  refine ⟨r, (P : Subgroup (derivedSeries A m)).map (derivedSeries A m).subtype, hrp,
    inferInstance, ?_, ?_⟩
  · exact fun hcon =>
      hPne ((Subgroup.map_eq_bot_iff_of_injective _ (derivedSeries A m).subtype_injective).mp hcon)
  · exact P.isPGroup'.map _


/-!
## Cocycles with a solvable operator group

Ported from CFSG, `BenderSuzuki/External/Huppert/I/theorem_18_3.lean`
(`huppert_I_18_2_b_principal_cocycle_of_solvable_operator`), with the minimal normal subgroup
replaced by `exists_normal_isPGroup_ne_bot`.
-/

/-- A 1-cocycle for a solvable operator group acting coprimely is principal. -/
theorem principal_cocycle_of_solvable_operator {X : Type u} {A : Type v}
    [Group X] [Finite X] [Group A] [Finite A] [Group.IsSolvable A]
    [MulDistribMulAction A X] (hcoprime : Nat.Coprime (Nat.card A) (Nat.card X))
    (c : A → X) (hc : ∀ a b : A, c (a * b) = c a * (a • c b)) :
    ∃ x : X, ∀ a : A, c a = x * (a • x)⁻¹ := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (A' : Type v) (X' : Type u) [Group A'] [Finite A'] [Group.IsSolvable A']
      [Group X'] [Finite X'] [MulDistribMulAction A' X'],
      Nat.card A' = n →
      Nat.Coprime (Nat.card A') (Nat.card X') →
      ∀ c' : A' → X', (∀ a b : A', c' (a * b) = c' a * (a • c' b)) →
        ∃ x : X', ∀ a : A', c' a = x * (a • x)⁻¹
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih A' X' _ _ _ _ _ _ hcardA hcop c' hc'
    by_cases hA_one : Nat.card A' = 1
    · let : Subsingleton A' := (Nat.card_eq_one_iff_unique.mp hA_one).1
      have hc_one : c' 1 = 1 := by
        have h : c' 1 = c' 1 * c' 1 := by simpa using hc' 1 1
        calc
          c' 1 = (c' 1)⁻¹ * (c' 1 * c' 1) := by simp
          _ = (c' 1)⁻¹ * c' 1 := by rw [← h]
          _ = 1 := by simp
      refine ⟨1, ?_⟩
      intro a
      have ha : a = 1 := Subsingleton.elim a 1
      simp [ha, hc_one]
    · have hA_nontrivial : Nontrivial A' := by
        refine not_subsingleton_iff_nontrivial.mp fun hsub => ?_
        exact hA_one (Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩)
      -- a nontrivial normal `r`-subgroup `B` of the operator group
      obtain ⟨r, B, hrprime, hBnormal, hBne, hBp⟩ := exists_normal_isPGroup_ne_bot A'
      have : B.Normal := hBnormal
      have : Fact r.Prime := ⟨hrprime⟩
      have : Fact (IsPGroup r B) := ⟨hBp⟩
      have hr_dvd_A : r ∣ Nat.card A' := by
        obtain ⟨k, hk⟩ := hBp.exists_card_eq
        have hBcard_ne_one : Nat.card B ≠ 1 := by
          intro hcard
          exact hBne (Subgroup.card_eq_one.mp hcard)
        have hk_ne_zero : k ≠ 0 := by
          intro hk0
          apply hBcard_ne_one
          simp [hk, hk0]
        have hr_dvd_B : r ∣ Nat.card B := by
          rw [hk]
          exact dvd_pow_self r hk_ne_zero
        exact hr_dvd_B.trans (Subgroup.card_subgroup_dvd_card B)
      have hcop_r_X : Nat.Coprime r (Nat.card X') := Nat.Coprime.of_dvd_left hr_dvd_A hcop
      -- kill the cocycle on `B` by the `p`-group case
      let cB : B → X' := fun b => c' b
      have hcB : ∀ a b : B, cB (a * b) = cB a * (a • cB b) := by
        intro a b
        change c' ((a : A') * (b : A')) = c' a * ((a : A') • c' b)
        exact hc' (a : A') (b : A')
      obtain ⟨x0, hx0⟩ :=
        principal_cocycle_of_pgroup_operator (X := X') (A := B) hcop_r_X cB hcB
      -- twist by `x0`, so that the new cocycle is trivial on `B` and lands in `C_{X'}(B)`
      let c1 : A' → X' := fun a => x0⁻¹ * c' a * (a • x0)
      have hc1_def : ∀ a : A', c1 a = x0⁻¹ * c' a * (a • x0) := fun _ => rfl
      have hc1 : ∀ a b : A', c1 (a * b) = c1 a * (a • c1 b) := by
        intro a b
        dsimp [c1]
        rw [hc' a b]
        simp [smul_mul', smul_smul, mul_assoc]
      have hc1B : ∀ b : B, c1 b = 1 := by
        intro b
        dsimp [c1]
        change x0⁻¹ * cB b * (b • x0) = 1
        rw [hx0 b]
        simp
      have hc1_fixed : ∀ a : A', c1 a ∈ FixedPoints.subgroup B X' := by
        intro a
        rw [FixedPoints.mem_subgroup]
        intro b
        have hconj_mem : a⁻¹ * (b : A') * a ∈ B := by
          simpa using (inferInstance : B.Normal).conj_mem (b : A') b.property a⁻¹
        let b' : B := ⟨a⁻¹ * (b : A') * a, hconj_mem⟩
        have hba : (b : A') * a = a * (b' : A') := by
          simp [b', mul_assoc]
        have h1 : c1 ((b : A') * a) = (b : A') • c1 a := by
          simpa [hc1B b] using hc1 (b : A') a
        have h2 : c1 (a * (b' : A')) = c1 a := by
          simpa [hc1B b'] using hc1 a (b' : A')
        have hfixed : (b : A') • c1 a = c1 a := by
          calc
            (b : A') • c1 a = c1 ((b : A') * a) := h1.symm
            _ = c1 (a * (b' : A')) := by rw [hba]
            _ = c1 a := h2
        change (b : A') • c1 a = c1 a
        exact hfixed
      -- push down to `A' ⧸ B` acting on those fixed points
      have hcop_Q_F : Nat.Coprime (Nat.card (A' ⧸ B)) (Nat.card (FixedPoints.subgroup B X')) := by
        have hquot_dvd : Nat.card (A' ⧸ B) ∣ Nat.card A' := Subgroup.card_quotient_dvd_card (s := B)
        have hcop_Q_X : Nat.Coprime (Nat.card (A' ⧸ B)) (Nat.card X') :=
          Nat.Coprime.of_dvd_left hquot_dvd hcop
        exact Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card _) hcop_Q_X
      have hquot_lt : Nat.card (A' ⧸ B) < n := by
        have h1 : 1 < Nat.card B := (Subgroup.one_lt_card_iff_ne_bot _).2 hBne
        have hcard : Nat.card A' = Nat.card (A' ⧸ B) * Nat.card B := by
          simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := B))
        have hlt : Nat.card (A' ⧸ B) * 1 < Nat.card (A' ⧸ B) * Nat.card B :=
          Nat.mul_lt_mul_of_pos_left h1 Nat.card_pos
        simpa [← hcard, hcardA] using hlt
      have hc1_eq_of_mk_eq {a b : A'} (h : (a : A' ⧸ B) = b) : c1 a = c1 b := by
        rcases (QuotientGroup.mk'_eq_mk' (N := B)).mp h with ⟨z, hzB, haz⟩
        have hz : c1 z = 1 := hc1B ⟨z, hzB⟩
        calc
          c1 a = c1 (a * z) := by simpa [hz] using (hc1 a z).symm
          _ = c1 b := by rw [haz]
      let cQ : A' ⧸ B → FixedPoints.subgroup B X' := fun q => ⟨c1 q.out, hc1_fixed q.out⟩
      have hcQ_mk : ∀ a : A', cQ (a : A' ⧸ B) = ⟨c1 a, hc1_fixed a⟩ := by
        intro a
        ext
        dsimp [cQ]
        exact hc1_eq_of_mk_eq (by exact Quotient.out_eq (s := QuotientGroup.leftRel B) (a : A' ⧸ B))
      have hcQ : ∀ q s : A' ⧸ B, cQ (q * s) = cQ q * (q • cQ s) := by
        intro q s
        refine Quotient.inductionOn₂' q s ?_
        intro a b
        ext
        rw [← QuotientGroup.mk_mul (N := B) a b]
        simp only [hcQ_mk, Subgroup.coe_mul]
        have hsmul : ↑(((a : A' ⧸ B) • (⟨c1 b, hc1_fixed b⟩ : FixedPoints.subgroup B X'))) =
            a • c1 b := rfl
        rw [hsmul]
        exact hc1 a b
      obtain ⟨y, hy⟩ :=
        ih (Nat.card (A' ⧸ B)) hquot_lt (A' ⧸ B) (FixedPoints.subgroup B X') rfl hcop_Q_F cQ hcQ
      refine ⟨x0 * (y : X'), ?_⟩
      intro a
      have hy_a : c1 a = (y : X') * (a • (y : X'))⁻¹ := by
        have h := congrArg Subtype.val (hy (a : A' ⧸ B))
        have hsmul : (((a : A' ⧸ B) • y : FixedPoints.subgroup B X') : X') = a • (y : X') := rfl
        simpa [hcQ_mk, hsmul] using h
      have hc_rearrange : c' a = x0 * c1 a * (a • x0)⁻¹ := by
        have hdef := hc1_def a
        calc
          c' a = x0 * (x0⁻¹ * c' a * (a • x0)) * (a • x0)⁻¹ := by simp [mul_assoc]
          _ = x0 * c1 a * (a • x0)⁻¹ := by rw [← hdef]
      rw [hc_rearrange, hy_a]
      simp [smul_mul', mul_assoc]
  exact hP (Nat.card A) A X rfl hcoprime c hc


/-!
## Huppert I.18.2

Ported from CFSG, `BenderSuzuki/External/Huppert/I/theorem_18_3.lean` (`huppert_I_18_2_*`).  The
two branches there share their whole argument apart from the cocycle input, so it is factored out
here into `exists_conj_of_principal_cocycle`.
-/

section Huppert

variable {G : Type u} [Group G] [Finite G]

/-- If every 1-cocycle `H → N` for the conjugation action is principal, then any two complements
of the normal subgroup `N` are conjugate by an element of `N`. -/
theorem exists_conj_of_principal_cocycle (N H K : Subgroup G) [N.Normal]
    [MulDistribMulAction H N]
    (hsmul : ∀ (h : H) (n : N), ((h • n : N) : G) = (h : G) * (n : G) * (h : G)⁻¹)
    (hH : N.IsComplement' H) (hK : N.IsComplement' K)
    (hprin : ∀ c : H → N, (∀ a b : H, c (a * b) = c a * (a • c b)) →
      ∃ x : N, ∀ a : H, c a = x * (a • x)⁻¹) :
    ∃ n : N, K = H.map (MulAut.conj (n : G)).toMonoidHom := by
  classical
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let eK : G ⧸ N ≃* K := hK.symm.QuotientMulEquiv
  let sectionK : H → K := fun h => eK (q (h : G))
  have hsectionK_q : ∀ h : H, q (sectionK h : G) = q (h : G) := by
    intro h
    dsimp [sectionK, eK, q]
    exact Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv hK.symm
      (QuotientGroup.mk' N (h : G))
  let cocycle : H → N := fun h =>
    ⟨(sectionK h : G) * (h : G)⁻¹, by
      rw [← QuotientGroup.eq_one_iff (N := N)]
      change q ((sectionK h : G) * (h : G)⁻¹) = 1
      rw [map_mul, map_inv, hsectionK_q h]
      simp⟩
  have hsectionK_mul : ∀ a b : H, sectionK (a * b) = sectionK a * sectionK b := by
    intro a b
    dsimp [sectionK]
    exact eK.map_mul (q (a : G)) (q (b : G))
  have hsectionK_eq : ∀ h : H, (sectionK h : G) = (cocycle h : G) * (h : G) := by
    intro h
    dsimp [cocycle]
    simp [mul_assoc]
  have hcocycle : ∀ a b : H, cocycle (a * b) = cocycle a * (a • cocycle b) := by
    intro a b
    ext
    have hsG : (sectionK (a * b) : G) = (sectionK a : G) * (sectionK b : G) :=
      congrArg Subtype.val (hsectionK_mul a b)
    dsimp [cocycle]
    rw [hsG]
    simp [hsmul, mul_assoc]
  obtain ⟨n, hn⟩ := hprin cocycle hcocycle
  have hHn_le_K : H.map (MulAut.conj (n : G)).toMonoidHom ≤ K := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨h, hhH, rfl⟩
    let hH' : H := ⟨h, hhH⟩
    have hnG : (cocycle hH' : G) = (n : G) * (((hH' : H) • n : N) : G)⁻¹ := by
      simpa using congrArg Subtype.val (hn hH')
    have hsection_eq : (sectionK hH' : G) = (n : G) * h * (n : G)⁻¹ := by
      calc
        (sectionK hH' : G) = (cocycle hH' : G) * (hH' : G) := hsectionK_eq hH'
        _ = ((n : G) * (((hH' : H) • n : N) : G)⁻¹) * (hH' : G) := by rw [hnG]
        _ = (n : G) * h * (n : G)⁻¹ := by simp [hsmul, hH', mul_assoc]
    simpa [MulAut.conj_apply, hH', hsection_eq] using (sectionK hH').property
  have hcardK : Nat.card K = Nat.card H :=
    hK.symm.index_eq_card.symm.trans hH.symm.index_eq_card
  have hcardHn : Nat.card (H.map (MulAut.conj (n : G)).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (K := H) (f := (MulAut.conj (n : G)).toMonoidHom)
      (MulAut.conj (n : G)).injective
  have hcard_le : Nat.card K ≤ Nat.card (H.map (MulAut.conj (n : G)).toMonoidHom) := by
    rw [hcardK, hcardHn]
  exact ⟨n, (Subgroup.eq_of_le_of_card_ge hHn_le_K hcard_le).symm⟩

/-- **Huppert I.18.2(a).**  Complements of a normal Hall subgroup `N` are conjugate when `N` is
solvable. -/
theorem complements_conjugate_of_solvable_normal (N H K : Subgroup G) [N.Normal]
    (hcoprime : Nat.Coprime (Nat.card N) (Nat.card (G ⧸ N)))
    (hsolvable : Group.IsSolvable N)
    (hH : N.IsComplement' H) (hK : N.IsComplement' K) :
    ∃ n : N, K = H.map (MulAut.conj (n : G)).toMonoidHom := by
  let instConj : MulDistribMulAction H N := conjAction H N
  have hcardH : Nat.card H = Nat.card (G ⧸ N) := by
    calc
      Nat.card H = N.index := hH.symm.index_eq_card.symm
      _ = Nat.card (G ⧸ N) := Subgroup.index_eq_card N
  have hcoprimeHN : Nat.Coprime (Nat.card H) (Nat.card N) := by
    simpa [hcardH] using hcoprime.symm
  exact exists_conj_of_principal_cocycle N H K (conjAction_coe H N) hH hK
    (fun c hc => exists_principal_cocycle_of_solvable_coprime hsolvable hcoprimeHN c hc)

/-- **Huppert I.18.2(b).**  Complements of a normal Hall subgroup `N` are conjugate when `G ⧸ N`
is solvable. -/
theorem complements_conjugate_of_solvable_quotient (N H K : Subgroup G) [N.Normal]
    (hcoprime : Nat.Coprime (Nat.card N) (Nat.card (G ⧸ N)))
    (hsolvable : Group.IsSolvable (G ⧸ N))
    (hH : N.IsComplement' H) (hK : N.IsComplement' K) :
    ∃ n : N, K = H.map (MulAut.conj (n : G)).toMonoidHom := by
  let instConj : MulDistribMulAction H N := conjAction H N
  have : Group.IsSolvable H :=
    Group.isSolvable_of_surjective (f := hH.symm.QuotientMulEquiv.toMonoidHom)
      hH.symm.QuotientMulEquiv.surjective
  have hcardH : Nat.card H = Nat.card (G ⧸ N) := by
    calc
      Nat.card H = N.index := hH.symm.index_eq_card.symm
      _ = Nat.card (G ⧸ N) := Subgroup.index_eq_card N
  have hcoprimeHN : Nat.Coprime (Nat.card H) (Nat.card N) := by
    simpa [hcardH] using hcoprime.symm
  exact exists_conj_of_principal_cocycle N H K (conjAction_coe H N) hH hK
    (fun c hc => principal_cocycle_of_solvable_operator hcoprimeHN c hc)

/-- **Huppert I, Theorem 18.2.**  Complements of a normal Hall subgroup are conjugate when either
the subgroup or the quotient is solvable. -/
theorem complements_conjugate_of_solvable (N H K : Subgroup G) [N.Normal]
    (hcoprime : Nat.Coprime (Nat.card N) (Nat.card (G ⧸ N)))
    (hsolvable : Group.IsSolvable N ∨ Group.IsSolvable (G ⧸ N))
    (hH : N.IsComplement' H) (hK : N.IsComplement' K) :
    ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom := by
  rcases hsolvable with hs | hs
  · obtain ⟨n, hn⟩ := complements_conjugate_of_solvable_normal N H K hcoprime hs hH hK
    exact ⟨n, hn⟩
  · obtain ⟨n, hn⟩ := complements_conjugate_of_solvable_quotient N H K hcoprime hs hH hK
    exact ⟨n, hn⟩

end Huppert

end SchurZassenhausConj
