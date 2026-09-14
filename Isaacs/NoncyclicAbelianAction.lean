module

public import Isaacs.CoprimeQuotients
public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Sylow

/-!
# Coprime action of a noncyclic abelian group

Isaacs, *Finite Group Theory*, Theorem 6.21: a noncyclic abelian group `A` acting coprimely on a
finite group `G` satisfies `G = ⟨C_G(a) : 1 ≠ a ∈ A⟩`.  This is the input still missing for Step 3
of Isaacs' proof of Burnside's `p ^ a q ^ b` theorem (`Isaacs/BurnsidePQTheorem.lean`).

## Provenance

Ported from the Qiuzhen CFSG project (<https://github.com/Qiuzhen-CFSG/CFSG>, Apache 2.0), file
`FeitThompson/GroupAction/NoncyclicAbelianPGroup.lean`, together with the Frattini-quotient
lemmas of `FeitThompson/Frattini/Core.lean`.  The route is:

* `exists_cyclic_quotient_fix_of_simple` — a simple `k[A]`-module, `k` a finite field and `A`
  finite abelian, is fixed by a subgroup `Y ≤ A` with `A ⧸ Y` cyclic (the image of `A` in the
  units of the residue field is cyclic);
* `isSemisimpleModule_groupAlgebra_zmod` — Maschke over `ZMod q` in the coprime case;
* `eq_top_of_forall_pow_eq_one` (CFSG's `proposition_1_16_b_elementaryAbelian`) — the elementary
  abelian case, by decomposing `Additive G` into simple `ZMod q [A]`-submodules;
* `eq_top_of_isPGroup` (CFSG's `proposition_1_16_b_qgroup`) — the `q`-group case, via the
  elementary abelian Frattini quotient;
* `eq_top_iSup_cyclicQuot` and `eq_top_iSup_zpowers` — the general case, via an `A`-invariant
  Sylow subgroup for each prime.

Two deviations from the CFSG text.  Where CFSG uses its own coprime-action development for the
fixed points of a quotient, this port uses ours: `eq_top_of_isPGroup` calls Isaacs 3.28,
`CoprimeAction.fixedPoints_quotient_eq_image` from `Isaacs/CoprimeQuotients.lean`.  And CFSG's
`IsElementaryAbelian` class is replaced by the plain hypotheses that the group is commutative of
exponent dividing `q`.

## What is still needed for Step 3

`eq_top_iSup_zpowers` is Isaacs 6.21 for a `p`-group operator, which is the case Step 3 of the
proof of Burnside's theorem uses (there `A` is a conjugate of `Z(O_p(M))`).  Step 3 additionally
needs the order of the automorphism group of a cyclic `q`-group, to get `p ∣ q - 1` in the cyclic
branch.
-/

@[expose] public section

namespace NoncyclicAbelian

open scoped Pointwise

universe u

/-- A simple module over the group algebra of a finite abelian group over a finite field is fixed
by a subgroup with cyclic quotient.  Ported from CFSG. -/
theorem exists_cyclic_quotient_fix_of_simple
    {k A S : Type*} [Field k] [Finite k] [CommGroup A] [Finite A]
    [AddCommGroup S] [Module (MonoidAlgebra k A) S]
    [IsSimpleModule (MonoidAlgebra k A) S] :
    ∃ Y : Subgroup A, IsCyclic (A ⧸ Y) ∧
      ∀ y : Y, ∀ x : S, (MonoidAlgebra.of k A (y : A)) • x = x := by
  classical
  obtain ⟨I, _, ⟨e⟩⟩ :=
    (isSimpleModule_iff_quot_maximal (R := MonoidAlgebra k A) (M := S)).mp inferInstance
  let _ : Field (MonoidAlgebra k A ⧸ I) := Ideal.Quotient.field I
  let φ : A →* (MonoidAlgebra k A ⧸ I)ˣ :=
    (Units.map (Ideal.Quotient.mk I)).comp (MonoidHom.toHomUnits (MonoidAlgebra.of k A))
  let _ : Finite ↥φ.range :=
    Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  refine ⟨φ.ker, ?_, ?_⟩
  · have hrange_cyc : IsCyclic ↥φ.range := isCyclic_subgroup_units φ.range
    exact (MulEquiv.isCyclic (QuotientGroup.quotientKerEquivRange φ)).2 hrange_cyc
  · intro y x
    apply e.injective
    have hy : Ideal.Quotient.mk I ((MonoidAlgebra.of k A) (y : A)) = 1 :=
      congrArg (fun u : (MonoidAlgebra k A ⧸ I)ˣ => (u : MonoidAlgebra k A ⧸ I)) y.2
    have hy' : Ideal.Quotient.mk I (MonoidAlgebra.single (y : A) 1 : MonoidAlgebra k A) = 1 := by
      simpa [MonoidAlgebra.of] using hy
    calc
      e (((MonoidAlgebra.of k A) (y : A)) • x) = ((MonoidAlgebra.of k A) (y : A)) • e x :=
        e.map_smul ((MonoidAlgebra.of k A) (y : A)) x
      _ = (Ideal.Quotient.mk I (MonoidAlgebra.single (y : A) 1 : MonoidAlgebra k A)) * e x := rfl
      _ = e x := by rw [hy', one_mul]

/-- Maschke over `ZMod q`: modules over the group algebra of a finite abelian group of order prime
to `q` are semisimple.  Ported from CFSG. -/
theorem isSemisimpleModule_groupAlgebra_zmod
    {A : Type*} [CommGroup A] [Finite A] {q : ℕ} [Fact q.Prime]
    (hq : Nat.Coprime (Nat.card A) q) {V : Type*} [AddCommGroup V]
    [Module (MonoidAlgebra (ZMod q) A) V] :
    IsSemisimpleModule (MonoidAlgebra (ZMod q) A) V := by
  classical
  have _ : NeZero (Nat.card A : ZMod q) := by
    constructor
    intro hzero
    have hdiv : q ∣ Nat.card A := (ZMod.natCast_eq_zero_iff (Nat.card A) q).1 hzero
    exact (((Fact.out : q.Prime).coprime_iff_not_dvd).1 hq.symm) hdiv
  infer_instance

/-- **The elementary abelian case** (CFSG's `proposition_1_16_b_elementaryAbelian`).  If the
finite abelian group `G` has exponent dividing the prime `q` and the finite abelian group `A` acts
on it with `|A|` prime to `q`, then `G` is generated by the fixed points of the subgroups of `A`
with cyclic quotient.

`Additive G` is a module over the group algebra `ZMod q [A]`, which is semisimple by Maschke, and
each simple summand is fixed by such a subgroup. -/
theorem eq_top_of_forall_pow_eq_one
    {G A : Type*} [CommGroup G] [Finite G] {q : ℕ} [Fact q.Prime]
    (hexp : ∀ g : G, g ^ q = 1)
    [CommGroup A] [Finite A] [MulDistribMulAction A G]
    (hqA : Nat.Coprime (Nat.card A) q) :
    (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), FixedPoints.subgroup (↥Y) G) = ⊤ := by
  classical
  have hz : ∀ x : Additive G, q • x = 0 := by
    intro x
    apply Additive.toMul.injective
    simpa using hexp (Additive.toMul x)
  have : Module (ZMod q) (Additive G) := AddCommGroup.zmodModule hz
  let toLin : A → (Additive G →ₗ[ZMod q] Additive G) := fun a =>
    ((MulEquiv.toAdditive (MulDistribMulAction.toMulAut A G a)).toAddMonoidHom).toZModLinearMap q
  have htoLin : ∀ (a : A) (x : Additive G),
      Additive.toMul ((toLin a) x) = a • Additive.toMul x := fun _ _ => rfl
  let ρ : Representation (ZMod q) A (Additive G) := {
    toFun := toLin
    map_one' := by
      refine LinearMap.ext fun x => ?_
      apply Additive.toMul.injective
      change (1 : A) • Additive.toMul x = Additive.toMul x
      simp
    map_mul' := by
      intro a b
      refine LinearMap.ext fun x => ?_
      apply Additive.toMul.injective
      change (a * b) • Additive.toMul x = a • b • Additive.toMul x
      rw [mul_smul] }
  let _ : AddCommMonoid ρ.asModule := Representation.instAddCommMonoidAsModule ρ
  let _ : Module (ZMod q) ρ.asModule := Representation.instModuleAsModule ρ
  let _ : Module (MonoidAlgebra (ZMod q) A) ρ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule ρ
  let η : Subgroup G ≃o Submodule (ZMod q) (Additive G) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := q))
  let Y1 : Type _ := {Y : Subgroup A // IsCyclic (A ⧸ Y)}
  let pmap : Y1 → Submodule (ZMod q) (Additive G) := fun Y =>
    η (FixedPoints.subgroup (↥Y.1) G)
  have hBinv : ∀ Y : Subgroup A, η (FixedPoints.subgroup (↥Y) G) ∈ ρ.invtSubmodule := by
    intro Y
    rw [Representation.mem_invtSubmodule]
    intro b
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    change b • Additive.toMul x ∈ FixedPoints.subgroup (↥Y) G
    rw [FixedPoints.mem_subgroup]
    intro z
    have hxfix : ((z : A) • Additive.toMul x) = Additive.toMul x := by
      change Additive.toMul x ∈ FixedPoints.subgroup (↥Y) G at hx
      rw [FixedPoints.mem_subgroup] at hx
      simpa only [Subgroup.smul_def] using hx z
    have hcomm : Commute ((z : Y) : A) b := Commute.all _ _
    change ((z : A) • (b • Additive.toMul x)) = b • Additive.toMul x
    calc
      ((z : A) • (b • Additive.toMul x)) = (((z : Y) : A) * b) • Additive.toMul x :=
        smul_smul ((z : Y) : A) b (Additive.toMul x)
      _ = (b * ((z : Y) : A)) • Additive.toMul x := by simp [hcomm.eq]
      _ = b • (((z : Y) : A) • Additive.toMul x) :=
        (smul_smul b ((z : Y) : A) (Additive.toMul x)).symm
      _ = b • Additive.toMul x := by simp [hxfix]
  let H : Subgroup G := ⨆ Y : Y1, FixedPoints.subgroup (↥Y.1) G
  let L : Submodule (ZMod q) (Additive G) := ⨆ Y : Y1, pmap Y
  have hLinv : L ∈ ρ.invtSubmodule := by
    rw [Representation.mem_invtSubmodule]
    intro b
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    refine Submodule.iSup_induction pmap (motive := fun y => (ρ b) y ∈ L) hx ?_ ?_ ?_
    · intro Y y hy
      have hpYInv := hBinv Y.1
      rw [Representation.mem_invtSubmodule] at hpYInv
      exact Submodule.mem_iSup_of_mem Y <|
        (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (ρ b)).1 (hpYInv b) y hy
    · simp
    · intro y z hy hz
      simpa [map_add] using (L.add_mem hy hz)
  let K : Submodule (MonoidAlgebra (ZMod q) A) ρ.asModule := ρ.mapSubmodule ⟨L, hLinv⟩
  let hs :=
    @isSemisimpleModule_groupAlgebra_zmod A inferInstance inferInstance q inferInstance hqA
      ρ.asModule (Representation.instAddCommGroupAsModule ρ)
      (Representation.instModuleMonoidAlgebraAsModule ρ)
  have htople : (⊤ : Submodule (MonoidAlgebra (ZMod q) A) ρ.asModule) ≤ K := by
    calc
      (⊤ : Submodule (MonoidAlgebra (ZMod q) A) ρ.asModule)
          = sSup {S : Submodule (MonoidAlgebra (ZMod q) A) ρ.asModule |
              IsSimpleModule (MonoidAlgebra (ZMod q) A) S} := by
                symm
                exact @IsSemisimpleModule.sSup_simples_eq_top
                  (MonoidAlgebra (ZMod q) A) inferInstance ρ.asModule
                  (Representation.instAddCommGroupAsModule ρ)
                  (Representation.instModuleMonoidAlgebraAsModule ρ) hs
      _ ≤ K := by
            refine sSup_le ?_
            intro S hS
            let _ : IsSimpleModule (MonoidAlgebra (ZMod q) A) S := hS
            obtain ⟨Y, hYcyc, hfix⟩ :=
              exists_cyclic_quotient_fix_of_simple (k := ZMod q) (A := A) (S := S)
            let Y1' : Y1 := ⟨Y, hYcyc⟩
            have hSle : S ≤ ρ.mapSubmodule ⟨pmap Y1', hBinv Y⟩ := by
              have hle' : (ρ.mapSubmodule.symm S : Submodule (ZMod q) (Additive G)) ≤ pmap Y1' := by
                intro x hx
                change Additive.toMul x ∈ FixedPoints.subgroup (↥Y) G
                rw [FixedPoints.mem_subgroup]
                intro y
                have hyfix : ((y : Y) : A) • Additive.toMul x = Additive.toMul x := by
                  have hfix' :
                      (MonoidAlgebra.of (ZMod q) A ((y : Y) : A)) • ρ.asModuleEquiv.symm x =
                        ρ.asModuleEquiv.symm x :=
                    congrArg Subtype.val (hfix y ⟨ρ.asModuleEquiv.symm x, hx⟩)
                  have hfixρ_asModule :
                      ρ.asModuleEquiv.symm (ρ ((y : Y) : A) x) = ρ.asModuleEquiv.symm x := by
                    rw [Representation.asModuleEquiv_symm_map_rho]
                    exact hfix'
                  have hfixρ : ρ ((y : Y) : A) x = x :=
                    ρ.asModuleEquiv.symm.injective hfixρ_asModule
                  simpa [ρ, htoLin] using congrArg Additive.toMul hfixρ
                change ((y : A) • Additive.toMul x) = Additive.toMul x
                exact hyfix
              have hle'' : ρ.mapSubmodule.symm S ≤ ⟨pmap Y1', hBinv Y⟩ := hle'
              simpa using ρ.mapSubmodule.monotone hle''
            have hsub : (⟨pmap Y1', hBinv Y⟩ : ρ.invtSubmodule) ≤ ⟨L, hLinv⟩ :=
              show pmap Y1' ≤ L from le_iSup (fun Y => pmap Y) Y1'
            exact hSle.trans (ρ.mapSubmodule.monotone hsub)
  have hKtop : K = ⊤ := top_le_iff.mp htople
  have hLtoppack : (⟨L, hLinv⟩ : ρ.invtSubmodule) = ⊤ := by
    apply ρ.mapSubmodule.injective
    simpa [K] using hKtop
  have hLtop : L = ⊤ := by
    simpa using congrArg Subtype.val hLtoppack
  have hηH : η H = ⊤ := by
    calc
      η H = ⨆ Y : Y1, η (FixedPoints.subgroup (↥Y.1) G) := by simp [H]
      _ = ⨆ Y : Y1, pmap Y := rfl
      _ = ⊤ := hLtop
  have hHtop : H = ⊤ := η.injective hηH
  simpa [H, Y1, iSup_subtype] using hHtop

/-!
## The Frattini quotient of a `q`-group

Ported from CFSG, `FeitThompson/Frattini/Core.lean`: in a finite `p`-group every maximal subgroup
is normal of index `p`, so the commutator subgroup and all `p`-th powers lie in the Frattini
subgroup, i.e. the Frattini quotient is elementary abelian.
-/

section Frattini

variable {R : Type*} [Group R] [Finite R] {p : ℕ}

/-- Maximal subgroups of a `p`-group are normal. -/
theorem coatom_normal_of_isPGroup (hp : p.Prime) (hR : IsPGroup p R) {K : Subgroup R}
    (hK : IsCoatom K) : K.Normal := by
  have : Fact p.Prime := ⟨hp⟩
  have hnil : Group.IsNilpotent R := hR.isNilpotent
  have hnc : NormalizerCondition R := Group.normalizerCondition_of_isNilpotent (G := R)
  exact Subgroup.NormalizerCondition.normal_of_coatom K hnc hK

omit [Finite R] in
/-- The quotient by a maximal normal subgroup has no proper nontrivial subgroups. -/
theorem quotient_subgroup_eq_bot_or_top_of_coatom {K : Subgroup R} [K.Normal] (hK : IsCoatom K) :
    ∀ H : Subgroup (R ⧸ K), H = ⊥ ∨ H = ⊤ := by
  intro H
  have hK_le_comap : K ≤ H.comap (QuotientGroup.mk' K) := by
    intro x hx
    change QuotientGroup.mk' K x ∈ H
    have hx1 : QuotientGroup.mk' K x = 1 := (QuotientGroup.eq_one_iff (N := K) (x := x)).2 hx
    simp [hx1]
  have hmap : (H.comap (QuotientGroup.mk' K)).map (QuotientGroup.mk' K) = H := by
    simpa using (Subgroup.map_comap_eq_self_of_surjective (f := QuotientGroup.mk' K)
      (h := QuotientGroup.mk'_surjective K) H)
  by_cases hEq : H.comap (QuotientGroup.mk' K) = K
  · left
    calc
      H = (H.comap (QuotientGroup.mk' K)).map (QuotientGroup.mk' K) := hmap.symm
      _ = K.map (QuotientGroup.mk' K) := by simp [hEq]
      _ = ⊥ := by simp
  · right
    have hlt : K < H.comap (QuotientGroup.mk' K) :=
      lt_of_le_of_ne hK_le_comap (by simpa [eq_comm] using hEq)
    have hcomap_top : H.comap (QuotientGroup.mk' K) = ⊤ := hK.right _ hlt
    calc
      H = (H.comap (QuotientGroup.mk' K)).map (QuotientGroup.mk' K) := hmap.symm
      _ = (⊤ : Subgroup R).map (QuotientGroup.mk' K) := by simp [hcomap_top]
      _ = ⊤ := by
            simpa using (Subgroup.map_top_of_surjective (f := QuotientGroup.mk' K)
              (QuotientGroup.mk'_surjective K))

/-- A maximal subgroup of a `p`-group has index `p`. -/
theorem card_quotient_coatom_eq_prime (hp : p.Prime) (hR : IsPGroup p R) {K : Subgroup R}
    (hK : IsCoatom K) : Nat.card (R ⧸ K) = p := by
  have : Fact p.Prime := ⟨hp⟩
  have : K.Normal := coatom_normal_of_isPGroup hp hR hK
  have hq_pgroup : IsPGroup p (R ⧸ K) := hR.to_quotient K
  rcases hq_pgroup.exists_card_eq with ⟨n, hn⟩
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    have hcard1 : Nat.card (R ⧸ K) = 1 := by simpa [hn0] using hn
    have hsub : Subsingleton (R ⧸ K) := (Nat.card_eq_one_iff_unique.mp hcard1).1
    have hK_top : K = ⊤ := (QuotientGroup.subsingleton_iff (N := K)).1 hsub
    exact hK.left hK_top
  have hn_le_one : n ≤ 1 := by
    by_contra hnot
    have hn_ge_two : 2 ≤ n := Nat.succ_le_of_lt (lt_of_not_ge hnot)
    have h1le : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn_ge_two
    have hp_le_cardQ : p ^ 1 ≤ Nat.card (R ⧸ K) := by
      rw [hn]
      exact Nat.pow_le_pow_right hp.pos h1le
    obtain ⟨H, hHcard⟩ :=
      Sylow.exists_subgroup_card_pow_prime_of_le_card (G := (R ⧸ K)) (p := p) (n := 1)
        hp hq_pgroup hp_le_cardQ
    have hH_ne_bot : H ≠ ⊥ := by
      intro hbot
      have hcard : Nat.card H = 1 := by simp [hbot]
      exact hp.ne_one (by simpa [hHcard] using hcard)
    have hH_ne_top : H ≠ ⊤ := by
      intro htop
      have hcardH : Nat.card H = p := by simpa using hHcard
      have hpow_eq : p ^ n = p ^ 1 := by
        simpa using
          (by calc
            p ^ n = Nat.card (R ⧸ K) := hn.symm
            _ = Nat.card H := by simp [htop]
            _ = p := hcardH)
      have hn_eq_one : n = 1 := (Nat.pow_right_injective hp.two_le) hpow_eq
      exact Nat.not_succ_le_self 1 (by simp [hn_eq_one] at hn_ge_two)
    exact ((quotient_subgroup_eq_bot_or_top_of_coatom hK H).elim hH_ne_bot hH_ne_top)
  have hn_eq_one : n = 1 :=
    Nat.le_antisymm hn_le_one (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn_ne_zero))
  simp [hn, hn_eq_one]

/-- The commutator subgroup of a `p`-group lies in its Frattini subgroup. -/
theorem commutator_le_frattini_of_isPGroup (hp : p.Prime) (hR : IsPGroup p R) :
    _root_.commutator R ≤ frattini R := by
  have : Fact p.Prime := ⟨hp⟩
  intro x hx
  unfold frattini Order.radical
  simp only [Subgroup.mem_iInf]
  intro M hM
  have : M.Normal := coatom_normal_of_isPGroup hp hR hM
  have hcardQ : Nat.card (R ⧸ M) = p := card_quotient_coatom_eq_prime hp hR hM
  have hcyc : IsCyclic (R ⧸ M) := isCyclic_of_prime_card (α := (R ⧸ M)) hcardQ
  have : CommGroup (R ⧸ M) := hcyc.commGroup
  have hcommQ : IsMulCommutative (R ⧸ M) := inferInstance
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := M)).1 hcommQ hx

/-- `p`-th powers in a `p`-group lie in the Frattini subgroup. -/
theorem pow_prime_mem_frattini_of_isPGroup (hp : p.Prime) (hR : IsPGroup p R) (x : R) :
    x ^ p ∈ frattini R := by
  have : Fact p.Prime := ⟨hp⟩
  unfold frattini Order.radical
  simp only [Subgroup.mem_iInf]
  intro M hM
  have : M.Normal := coatom_normal_of_isPGroup hp hR hM
  have : Fintype (R ⧸ M) := Fintype.ofFinite (R ⧸ M)
  have hcardQ : Nat.card (R ⧸ M) = p := card_quotient_coatom_eq_prime hp hR hM
  have hcardQf : Fintype.card (R ⧸ M) = p := by
    simpa [Nat.card_eq_fintype_card] using hcardQ
  have hpowQ : ((QuotientGroup.mk' M x) : R ⧸ M) ^ p = 1 := by
    have hpc : ((QuotientGroup.mk' M x) : R ⧸ M) ^ Fintype.card (R ⧸ M) = 1 :=
      pow_card_eq_one (x := (QuotientGroup.mk' M x : R ⧸ M))
    simpa [hcardQf] using hpc
  exact (QuotientGroup.eq_one_iff (N := M) (x := x ^ p)).1 (by
    simpa [MonoidHom.map_pow] using hpowQ)

/-- The Frattini quotient of a `p`-group is abelian. -/
theorem frattiniQuotient_isMulCommutative (hp : p.Prime) (hR : IsPGroup p R) :
    IsMulCommutative (R ⧸ frattini R) :=
  (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := frattini R)).2
    (commutator_le_frattini_of_isPGroup hp hR)

/-- The Frattini quotient of a `p`-group has exponent dividing `p`. -/
theorem frattiniQuotient_pow_eq_one (hp : p.Prime) (hR : IsPGroup p R) (x : R ⧸ frattini R) :
    x ^ p = 1 := by
  induction x using QuotientGroup.induction_on with
  | _ y =>
    exact (QuotientGroup.eq_one_iff (N := frattini R) (x := y ^ p)).2
      (pow_prime_mem_frattini_of_isPGroup hp hR y)

end Frattini

/-!
## The `q`-group case

CFSG's `proposition_1_16_b_qgroup`: pass to the Frattini quotient, which is elementary abelian, and
lift back.  Where CFSG uses its own coprime-action development for the fixed points of the
quotient, this uses Isaacs 3.28 (`CoprimeAction.fixedPoints_quotient_eq_image`).
-/

open scoped IsMulCommutative in
/-- For a `q`-group `G` with a coprime action of a finite abelian group `A`, the fixed points of
the subgroups of `A` with cyclic quotient generate `G`. -/
theorem eq_top_of_isPGroup {G A : Type u} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    (hqG : IsPGroup q G) [CommGroup A] [Finite A] [MulDistribMulAction A G]
    (hAq : Nat.Coprime (Nat.card A) q) :
    (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), FixedPoints.subgroup (↥Y) G) = ⊤ := by
  classical
  have hq : q.Prime := Fact.out
  obtain ⟨n, hn⟩ := hqG.exists_card_eq
  have hcopG : Nat.Coprime (Nat.card A) (Nat.card G) := by
    rw [hn]
    exact hAq.pow_right n
  -- the action descends to the Frattini quotient
  have hΦinv : ∀ (a : A), ∀ x ∈ frattini G, a • x ∈ frattini G := fun a _ hx =>
    CoprimeAction.smul_mem_of_characteristic (frattini G) a hx
  let : MulDistribMulAction A (G ⧸ frattini G) :=
    SchurZassenhausConj.quotientMulDistribMulAction hΦinv
  -- which is elementary abelian
  have : IsMulCommutative (G ⧸ frattini G) := frattiniQuotient_isMulCommutative hq hqG
  have hbar :=
    eq_top_of_forall_pow_eq_one (G := G ⧸ frattini G) (A := A)
      (frattiniQuotient_pow_eq_one hq hqG) hAq
  -- fixed points downstairs are the image of the fixed points upstairs (Isaacs 3.28)
  have hΦsolv : Group.IsSolvable (frattini G) := by
    have := frattini_nilpotent (G := G)
    infer_instance
  have hstep : ∀ Y : Subgroup A,
      FixedPoints.subgroup (↥Y) (G ⧸ frattini G)
        = (FixedPoints.subgroup (↥Y) G).map (QuotientGroup.mk' (frattini G)) := by
    intro Y
    have hYinv : ∀ (a : ↥Y), ∀ x ∈ frattini G, a • x ∈ frattini G := fun a _ hx =>
      hΦinv (a : A) _ hx
    have hcopY : Nat.Coprime (Nat.card ↥Y) (Nat.card (frattini G)) :=
      Nat.Coprime.of_dvd_left (Subgroup.card_subgroup_dvd_card Y)
        (Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card (frattini G)) hcopG)
    have hmkY : ∀ (a : ↥Y) (x : G),
        a • ((x : G) : G ⧸ frattini G) = ((a • x : G) : G ⧸ frattini G) := fun _ _ => rfl
    have h328 := CoprimeAction.fixedPoints_quotient_eq_image (G := G) (A := ↥Y)
      CoprimeAction.schurZassenhausConjugacy (N := frattini G) hYinv hcopY (Or.inr hΦsolv) hmkY
    refine SetLike.ext' ?_
    rw [Subgroup.coe_map]
    exact h328
  -- so the join of the fixed points is everything modulo the Frattini subgroup
  set K : Subgroup G := ⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), FixedPoints.subgroup (↥Y) G
    with hKdef
  have hmapK : K.map (QuotientGroup.mk' (frattini G)) = ⊤ := by
    rw [hKdef, ← hbar]
    simp only [Subgroup.map_iSup]
    exact iSup_congr fun Y => iSup_congr fun _ => (hstep Y).symm
  have hKsup : K ⊔ frattini G = ⊤ := by
    refine top_unique fun g _ => ?_
    have hgbar : ((g : G) : G ⧸ frattini G) ∈ K.map (QuotientGroup.mk' (frattini G)) := by
      rw [hmapK]
      trivial
    obtain ⟨k, hkK, hkg⟩ := hgbar
    have hkgΦ : k⁻¹ * g ∈ frattini G := by
      refine (QuotientGroup.eq_one_iff (N := frattini G) (x := k⁻¹ * g)).1 ?_
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have hkg' : (k : G ⧸ frattini G) = (g : G ⧸ frattini G) := hkg
      rw [hkg']
      simp
    have hk : k ∈ K ⊔ frattini G := (le_sup_left : K ≤ K ⊔ frattini G) hkK
    have hrest : k⁻¹ * g ∈ K ⊔ frattini G :=
      (le_sup_right : frattini G ≤ K ⊔ frattini G) hkgΦ
    simpa using mul_mem hk hrest
  exact frattini_nongenerating hKsup

/-!
## From `q`-groups to all groups

CFSG's `exists_invariant_sylow` and `eq_top_of_exists_sylow_le`: a `p`-group acting coprimely
fixes some Sylow `q`-subgroup for each `q`, and a subgroup containing a Sylow subgroup for every
prime is everything.
-/

/-- A subgroup invariant under the action (CFSG's `IsInvariant`). -/
class IsInvariant (A G : Type*) [Group G] [SMul A G] (H : Subgroup G) : Prop where
  invariant : ∀ a : A, ∀ g : G, g ∈ H ↔ a • g ∈ H

/-- The action restricted to an invariant subgroup. -/
instance instMulDistribMulActionSubtype {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G] {H : Subgroup G} [IsInvariant A G H] :
    MulDistribMulAction A H where
  smul a x := ⟨a • x.1, (IsInvariant.invariant (A := A) (G := G) (H := H) a x.1).1 x.2⟩
  one_smul x := by
    ext
    change ((1 : A) • (x : G)) = x
    simp
  mul_smul a b x := by
    ext
    change ((a * b) • (x : G)) = a • (b • (x : G))
    simpa using (mul_smul a b (x : G))
  smul_mul a x y := by
    ext
    change a • ((x : G) * (y : G)) = a • (x : G) * a • (y : G)
    simp
  smul_one a := by
    ext
    change a • (1 : G) = (1 : G)
    simp

theorem fixedPoints_map_subtype_le {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (H : Subgroup G) [IsInvariant A G H] (Y : Subgroup A) :
    (FixedPoints.subgroup (↥Y) H).map H.subtype ≤ FixedPoints.subgroup (↥Y) G := by
  intro g hg
  rcases hg with ⟨x, hx, rfl⟩
  have hx' : ∀ y : Y, y • x = x := by
    simpa [FixedPoints.mem_subgroup] using hx
  change ∀ y : Y, ((y : A) • ((x : H) : G)) = ((x : H) : G)
  intro y
  exact congrArg Subtype.val (hx' y)

/-- A `p`-group acting coprimely on `G` leaves some Sylow `q`-subgroup invariant. -/
theorem exists_invariant_sylow {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hA : IsPGroup p A) [MulDistribMulAction A G]
    (hG : Nat.Coprime p (Nat.card G)) :
    ∃ P : Sylow q G, IsInvariant A G (P : Subgroup G) := by
  classical
  let P₀ : Sylow q G := default
  have hcard_dvd : Nat.card (Sylow q G) ∣ Nat.card G :=
    dvd_trans (Sylow.card_dvd_index P₀) (Subgroup.index_dvd_card (H := (P₀ : Subgroup G)))
  have hcop_sylow : Nat.Coprime p (Nat.card (Sylow q G)) :=
    Nat.Coprime.of_dvd_right hcard_dvd hG
  have hpSylow : ¬ p ∣ Nat.card (Sylow q G) :=
    ((Fact.out : p.Prime).coprime_iff_not_dvd).1 hcop_sylow
  rcases hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q G) hpSylow with ⟨P, hPfix⟩
  refine ⟨P, ?_⟩
  constructor
  intro a g
  have hsmulP : a • (P : Subgroup G) = (P : Subgroup G) := by
    simpa [Sylow.pointwise_smul_def] using
      congrArg (fun Q : Sylow q G => (Q : Subgroup G)) ((MulAction.mem_fixedPoints.mp hPfix) a)
  constructor
  · intro hg
    have hmem : a • g ∈ a • (P : Subgroup G) :=
      Subgroup.smul_mem_pointwise_smul g a (P : Subgroup G) hg
    simpa [hsmulP] using hmem
  · intro hg
    have hsmulPinv : a⁻¹ • (P : Subgroup G) = (P : Subgroup G) := by
      simpa [Sylow.pointwise_smul_def] using congrArg (fun Q : Sylow q G => (Q : Subgroup G))
        ((MulAction.mem_fixedPoints.mp hPfix) a⁻¹)
    have hmem : a⁻¹ • (a • g) ∈ a⁻¹ • (P : Subgroup G) :=
      Subgroup.smul_mem_pointwise_smul (a • g) a⁻¹ (P : Subgroup G) hg
    simpa [hsmulPinv] using hmem

/-- A subgroup containing a Sylow subgroup for every prime is the whole group. -/
theorem eq_top_of_exists_sylow_le {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hSyl : ∀ p : ℕ, p ∈ (Nat.card G).primeFactors → ∀ [Fact p.Prime],
      ∃ P : Sylow p G, (P : Subgroup G) ≤ H) :
    H = ⊤ := by
  rw [← Subgroup.card_eq_iff_eq_top]
  apply Nat.eq_of_factorization_eq Nat.card_pos.ne' Nat.card_pos.ne'
  intro p
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    by_cases hd : p ∈ (Nat.card G).primeFactors
    · obtain ⟨P, hPle⟩ := hSyl p hd
      refine le_antisymm
        (((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
          (Subgroup.card_subgroup_dvd_card H)) p) ?_
      rw [← pow_le_pow_iff_right₀ (Nat.Prime.one_lt hp), ← Sylow.card_eq_multiplicity P]
      have hc : Nat.card P = Nat.card (P.subgroupOf H) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).symm
      have hpP : IsPGroup p (P.subgroupOf H) := by
        refine IsPGroup.of_card (n := (Nat.card G).factorization p) ?_
        rw [← hc, ← Sylow.card_eq_multiplicity P]
      rcases IsPGroup.exists_le_sylow hpP with ⟨P', hP'⟩
      rw [← Sylow.card_eq_multiplicity P', hc]
      exact Subgroup.card_le_of_le hP'
    · have hnpG : ¬ p ∣ Nat.card G := fun hpG =>
        hd ((Nat.mem_primeFactors).2 ⟨hp, hpG, Nat.card_pos.ne'⟩)
      have hnpH : ¬ p ∣ Nat.card H := fun hpH =>
        hnpG (dvd_trans hpH (Subgroup.card_subgroup_dvd_card H))
      simp [Nat.factorization_eq_zero_of_not_dvd hnpG, Nat.factorization_eq_zero_of_not_dvd hnpH]
  · simp [Nat.factorization_eq_zero_of_not_prime (n := Nat.card G) (p := p) hp,
      Nat.factorization_eq_zero_of_not_prime (n := Nat.card H) (p := p) hp]

/-! ## Isaacs 6.21 for a `p`-group operator -/

/-- **CFSG's `iSup_fixedPointSubgroup_cyclicQuot_eq_top_of_noncyclic_abelian_pGroup_action`.**
A noncyclic abelian `p`-group acting coprimely on a finite group `G` has the property that the
fixed points of its subgroups with cyclic quotient generate `G`. -/
theorem eq_top_iSup_cyclicQuot {G A : Type u} [Group G] [Finite G] [CommGroup A] [Finite A]
    (p : ℕ) [Fact p.Prime] (hA : IsPGroup p A) (hG : Nat.Coprime p (Nat.card G))
    [MulDistribMulAction A G] :
    (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), FixedPoints.subgroup (↥Y) G) = ⊤ := by
  classical
  refine eq_top_of_exists_sylow_le _ ?_
  intro r hr _hr
  obtain ⟨Q, hQinv⟩ := exists_invariant_sylow (G := G) (A := A) (p := p) (q := r) hA hG
  have : IsInvariant A G (Q : Subgroup G) := hQinv
  have hr_dvd_G : r ∣ Nat.card G := (Nat.mem_primeFactors.mp hr).2.1
  have hp_not_dvd_r : ¬ p ∣ r := fun hpr =>
    (((Fact.out : p.Prime).coprime_iff_not_dvd).1 hG) (dvd_trans hpr hr_dvd_G)
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hAr : Nat.Coprime (Nat.card A) r := by
    rw [hn]
    exact ((Fact.out : p.Prime).coprime_pow_of_not_dvd (m := n) hp_not_dvd_r).symm
  have hQtop : (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)),
      FixedPoints.subgroup (↥Y) (Q : Subgroup G)) = ⊤ :=
    eq_top_of_isPGroup (G := (Q : Subgroup G)) (A := A) Q.isPGroup' hAr
  refine ⟨Q, ?_⟩
  calc
    (Q : Subgroup G) = (⊤ : Subgroup (Q : Subgroup G)).map (Q : Subgroup G).subtype := by
          ext x
          simp
    _ = (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)),
          FixedPoints.subgroup (↥Y) (Q : Subgroup G)).map (Q : Subgroup G).subtype := by
          rw [hQtop]
    _ = ⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)),
          (FixedPoints.subgroup (↥Y) (Q : Subgroup G)).map (Q : Subgroup G).subtype := by
          simp [Subgroup.map_iSup]
    _ ≤ _ := by
          refine iSup_le fun Y => iSup_le fun hY => ?_
          exact (fixedPoints_map_subtype_le (A := A) (G := G) (H := (Q : Subgroup G)) Y).trans
            (le_iSup_of_le Y (le_iSup_of_le hY le_rfl))

/-- **Isaacs 6.21 for a `p`-group operator** (CFSG's
`iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action`): a noncyclic abelian
`p`-group acting coprimely on a finite group `G` satisfies `G = ⟨C_G(a) : 1 ≠ a ∈ A⟩`. -/
theorem eq_top_iSup_zpowers {G A : Type u} [Group G] [Finite G] [CommGroup A] [Finite A]
    (p : ℕ) [Fact p.Prime] (hA : IsPGroup p A) (hG : Nat.Coprime p (Nat.card G))
    [MulDistribMulAction A G] (hncyc : ¬ IsCyclic A) :
    (⨆ (a : A) (_ : a ≠ 1), FixedPoints.subgroup (↥(Subgroup.zpowers a)) G) = ⊤ := by
  have hcyc := eq_top_iSup_cyclicQuot (G := G) (A := A) p hA hG
  have hle : (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), FixedPoints.subgroup (↥Y) G) ≤
      (⨆ (a : A) (_ : a ≠ 1), FixedPoints.subgroup (↥(Subgroup.zpowers a)) G) := by
    refine iSup₂_le fun Y hY => ?_
    have hY_ne_bot : Y ≠ ⊥ := by
      intro hY_bot
      subst hY_bot
      have _ : IsCyclic (A ⧸ (⊥ : Subgroup A)) := hY
      exact hncyc (isCyclic_of_surjective (QuotientGroup.quotientBot (G := A))
        (QuotientGroup.quotientBot (G := A)).surjective)
    obtain ⟨a, ha_ne_one⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hY_ne_bot
    have ha_ne_one' : (a : A) ≠ 1 := fun ha1 => ha_ne_one (Subtype.ext (by simpa using ha1))
    have hzpow_le : Subgroup.zpowers (a : A) ≤ Y := (Subgroup.zpowers_le).2 a.2
    have hfix_le : FixedPoints.subgroup (↥Y) G
        ≤ FixedPoints.subgroup (↥(Subgroup.zpowers (a : A))) G := by
      intro g hg
      rw [FixedPoints.mem_subgroup] at hg ⊢
      intro z
      change ((z : A) • g) = g
      exact hg (⟨z, hzpow_le z.2⟩ : Y)
    exact le_iSup_of_le (a : A) (le_iSup_of_le ha_ne_one' hfix_le)
  exact top_le_iff.mp (hcyc.symm.trans_le hle)

/-! ## Isaacs 6.20 for a `p`-group operator -/

/-- The fixed points of one operator form an invariant subgroup, because the operator group is
abelian. -/
instance isInvariant_fixedPoints_zpowers {G A : Type*} [Group G] [CommGroup A]
    [MulDistribMulAction A G] (a : A) :
    IsInvariant A G (FixedPoints.subgroup (↑(Subgroup.zpowers a)) G) where
  invariant b g := by
    simp only [FixedPoints.mem_subgroup]
    have key : ∀ z : ↑(Subgroup.zpowers a),
        ((z : A) • (b • g) = b • g) ↔ ((z : A) • g = g) := by
      intro z
      rw [← mul_smul, mul_comm, mul_smul, smul_left_cancel_iff]
    exact ⟨fun hg z => (key z).mpr (hg z), fun hg z => (key z).mp (hg z)⟩

/-- **Isaacs, Lemma 6.20** for a `p`-group operator.  A finite abelian `p`-group acting faithfully
and coprimely on a finite group, and trivially on every proper invariant subgroup, is cyclic.

If it were not, Isaacs 6.21 would write `G` as the join of the `C_G(a)` for `1 ≠ a ∈ A`.  None of
those is all of `G`, by faithfulness, so each is a proper invariant subgroup on which `A` acts
trivially; then `A` acts trivially on `G`, so `A = 1` — which is cyclic. -/
theorem isCyclic_of_forall_proper_invariant {G A : Type u} [Group G] [Finite G] [CommGroup A]
    [Finite A] (p : ℕ) [Fact p.Prime] (hA : IsPGroup p A) (hG : Nat.Coprime p (Nat.card G))
    [MulDistribMulAction A G] [FaithfulSMul A G]
    (htriv : ∀ H : Subgroup G, IsInvariant A G H → H ≠ ⊤ → ∀ a : A, ∀ x ∈ H, a • x = x) :
    IsCyclic A := by
  by_contra hncyc
  -- every `C_G(a)` with `a ≠ 1` is a proper invariant subgroup, so `A` is trivial on it
  have hle : (⨆ (a : A) (_ : a ≠ 1), FixedPoints.subgroup (↑(Subgroup.zpowers a)) G)
      ≤ FixedPoints.subgroup A G := by
    refine iSup₂_le fun a ha => ?_
    have hne : FixedPoints.subgroup (↑(Subgroup.zpowers a)) G ≠ ⊤ := by
      intro htop
      refine ha (eq_of_smul_eq_smul (α := G) (m₁ := a) (m₂ := 1) fun g => ?_)
      have hg : g ∈ FixedPoints.subgroup (↑(Subgroup.zpowers a)) G := htop ▸ Subgroup.mem_top g
      rw [one_smul]
      exact hg ⟨a, Subgroup.mem_zpowers a⟩
    intro x hx
    rw [FixedPoints.mem_subgroup]
    exact fun m => htriv _ (isInvariant_fixedPoints_zpowers a) hne m x hx
  -- so `A` acts trivially on `G`, and faithfulness makes `A` trivial
  have htrivG : ∀ (a : A) (g : G), a • g = g := by
    intro a g
    have : g ∈ FixedPoints.subgroup A G :=
      hle ((eq_top_iSup_zpowers p hA hG hncyc) ▸ Subgroup.mem_top g)
    exact this a
  have hone : ∀ x : A, x = 1 := fun x =>
    eq_of_smul_eq_smul (α := G) (m₁ := x) (m₂ := 1) fun g => by rw [htrivG, one_smul]
  exact hncyc ⟨1, fun x => by rw [hone x]; exact Subgroup.mem_zpowers (1 : A)⟩

end NoncyclicAbelian
