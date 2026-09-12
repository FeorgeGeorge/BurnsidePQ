module

public import Isaacs.ThompsonSubgroup
public import Isaacs.NormalSylowTheorem
public import Isaacs.Frobenius

/-!
# Thompson's normal-`J` theorem: Isaacs 7.6

Isaacs, *Finite Group Theory*, Theorem 7.6, the "normal-`J` theorem":

> Let `P ∈ Syl_p(G)`, where `G` is a finite group, and assume
> (1) `G` is `p`-solvable; (2) `p ≠ 2`; (3) a Sylow `2`-subgroup of `G` is abelian;
> (4) `O_p'(G) = 1`; (5) `P = C_G(Z(P))`.  Then `J(P) ⊴ G`.

This is `PiGroups.thompsonSubgroup_normal`.  It is used for Isaacs' Theorem 7.1 (Thompson's
normal `p`-complement theorem, `Isaacs/ThompsonNormalPComplement.lean`) and for the
group-theoretic proof of Burnside's `p ^ a q ^ b` theorem — Steps 8 and 9 of
`Isaacs/BurnsidePQTheorem.lean`.

`PiGroups.thompsonSubgroup_normal_of_sylow_two_abelian` restates it with hypothesis (3) in
Isaacs' own words — *a Sylow `2`-subgroup of `G` is abelian* — which
`PiGroups.forall_two_commute_iff_sylow` shows is the same as the elementwise form used
throughout.

Isaacs argues by minimal counterexample.  Write `U = O_p(G)`, `Ḡ = G/U` and `L̄ = O_p'(Ḡ)`, with
`L` the preimage of `L̄` (`PiGroups.bigL`), and let `A` be an elementary abelian subgroup of `P`
not inside `U`, chosen with `|A|` as large as possible.  The eight steps are:

* `PiGroups.centerOf_sylow_le_piCore` — **Step 1(a)**, `Z(P) ≤ U`;
* `PiGroups.piCore_compl_eq_bot_of_piCore_le` — **Step 1(b)**, `O_p'(H) = 1` whenever
  `U ≤ H ≤ G`;
* `PiGroups.centralizer_piCoreCompl_quotient_le` — **Step 1(c)**, `C_Ḡ(L̄) ≤ L̄`.  All three are
  consequences of the Hall–Higman Lemma 1.2.3 (`PiGroups.centralizer_piCore_le_piCore`);
* `PiGroups.thompsonSubgroup_normal_of_forall_le_piCore` — **Step 2**, in contrapositive form: if
  every member of `E(P)` lies in `U` then `J(P) ⊴ G` already, so such an `A` exists.  This is
  Lemma 7.2 (`PiGroups.thompsonSubgroup_eq_of_thompsonSubgroup_le`);
* `PiGroups.step_three` — **Step 3**: if `U A ≤ H < G` and `P ⊓ H` is a Sylow `p`-subgroup of
  `H`, then `⁅A, H ⊓ L⁆ ≤ U`, i.e. `Ā` centralizes `H̄ ⊓ L̄`.  `H` inherits the hypotheses of
  the theorem — hypothesis (5) transferring by `PiGroups.centralizer_centerOf_inf_eq` — so
  induction gives `J(P ⊓ H) ⊴ H`; since `A ∈ E(P ⊓ H)`, `A` lies in that Thompson subgroup `J`,
  and a commutator `⁅a, h⁆` with `h ∈ H ⊓ L` lies in `J ⊓ L`, hence in `U` because `J` is a
  `p`-group;
* `PiGroups.step_four` — **Step 4**: `G = LA` and `P = UA`.  `UA` is a Sylow `p`-subgroup of `LA`
  because `|LA : UA| = |L : U|` is a `p'`-number, so if `LA` were proper Step 3 would put `Ā`
  inside `C_Ḡ(L̄) ≤ L̄` — impossible for a `p`-group not already in `U`;
* `PiGroups.step_five` — **Step 5**: `|Ā| = p`.  `Ā` is elementary abelian and nontrivial, so it
  suffices that it be cyclic, and that is Lemma 6.20 applied to the faithful coprime action of
  `Ā` on `L̄`: for an `Ā`-invariant `M̄ < L̄`, Step 3 with `H = M A` — proper because
  `M A ⊓ L = M` — makes `Ā` centralize `M̄`;
* `PiGroups.centralizer_omegaOne_centerOf_piCore` — **Step 6**: `C_G(V) = U` for the module
  `V = Ω₁(Z(U))` (`PiGroups.omegaOne`), so `Ḡ` acts faithfully on `V`.  A `q`-element of
  `C_G(V)` with `q ≠ p` would centralize `Z(U)` by Corollary 4.35, hence lie in `C_G(Z(P)) = P`;
* `PiGroups.relIndex_omegaOne_le` — **Step 7**: `|V : V ⊓ A| ≤ |A : U ⊓ A|`, since `V D` is
  elementary abelian inside `P` for `D = U ⊓ A`;
* `PiGroups.step_eight` — **Step 8**: `P = UA` gives `P̄ = Ā`, which centralizes `V ⊓ A`, so
  `|V : C_V(P̄)| ≤ p` and the normal-`P` theorem 7.5 (`PiGroups.normal_sylow_of_faithful`,
  `Isaacs/NormalSylowTheorem.lean`) makes `P̄ ⊴ Ḡ`; then `P ⊴ G`, so `A ≤ P ≤ O_p(G) = U`,
  against the choice of `A`.

The subgroup constructions the proof runs on — `Z(P)` as `PiGroups.centerOf`, the module
`V = Ω₁(Z(U))` of Step 8 as `PiGroups.omegaOne`, `E(P)` and `J(P)` themselves, and the lemmas
transferring "characteristic in `Q`" to normality — are in `Isaacs/ThompsonSubgroup.lean`,
since 7.1 and 7.8 use them just as much.  What is general and kept here is
`PiGroups.commutatorElement_mem_inf`, the observation Isaacs uses in both Step 1(b) and Step 3
that two subgroups normal in `H` have their commutators in the intersection.

One place where the formalization is shorter than the book: for hypothesis (5) in Step 3, Isaacs
argues that `C_H(Z(S))` is a `p`-subgroup of `H` containing the Sylow subgroup `S`, hence equals
it.  In fact `C_G(Z(S)) ≤ C_G(Z(P)) = P` already gives `C_H(Z(S)) = P ⊓ H = S` with no appeal to
Sylow theory, which is how `PiGroups.centralizer_centerOf_inf_eq` is stated; the hypothesis
`P ⊓ H ∈ Syl_p(H)` is needed only so that the induction has a Sylow subgroup to be applied to.

Unlike most of the development this file needs no `SchurZassenhausConjugacy` hypothesis: the one
place Isaacs uses coprime-action theory, Step 6, goes through Corollary 4.35, which does not.

`mathlib` has none of this: no Thompson subgroup, and no normal-`J` theorem.
-/

@[expose] public section

namespace PiGroups

universe u

variable {G : Type u} [Group G] {p : ℕ}

/-!
## Commutators of two subgroups normalized by a common subgroup

Isaacs uses the same observation twice — for `⁅M, U⁆` in Step 1(b) and for `⁅H ⊓ L, J(S)⁆` in
Step 3 — namely that two subgroups normal in `H` have their commutators in the intersection.
-/

/-- If `M` and `N` lie in `H` and are normalized by it, then `⁅M, N⁆ ≤ M ⊓ N`, elementwise. -/
theorem commutatorElement_mem_inf {H M N : Subgroup G} (hMH : M ≤ H) (hNH : N ≤ H)
    (hMconj : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M)
    (hNconj : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    {m n : G} (hm : m ∈ M) (hn : n ∈ N) : m * n * m⁻¹ * n⁻¹ ∈ M ⊓ N := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : n * m⁻¹ * n⁻¹ ∈ M := hMconj n (hNH hn) m⁻¹ (M.inv_mem hm)
    have h2 : m * (n * m⁻¹ * n⁻¹) = m * n * m⁻¹ * n⁻¹ := by group
    rw [← h2]
    exact M.mul_mem hm h1
  · exact N.mul_mem (hNconj m (hMH hm) n hn) (N.inv_mem hn)

/-- Two subgroups normalized by a common subgroup and meeting trivially commute elementwise. -/
theorem commute_of_inf_eq_bot {H M N : Subgroup G} (hMH : M ≤ H) (hNH : N ≤ H)
    (hMconj : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M)
    (hNconj : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hdisj : M ⊓ N = ⊥) {m n : G} (hm : m ∈ M) (hn : n ∈ N) : m * n = n * m := by
  have h := commutatorElement_mem_inf hMH hNH hMconj hNconj hm hn
  rw [hdisj, Subgroup.mem_bot] at h
  have h1 : m * n * m⁻¹ = n := mul_inv_eq_one.mp h
  calc m * n = (m * n * m⁻¹) * m := by group
    _ = n * m := by rw [h1]

/-!
## Step 1 of Isaacs' proof: three consequences of Hall–Higman

Throughout, `U = O_p(G)`.  The standing hypotheses are that `G` is `p`-solvable with
`O_p′(G) = 1`, which is exactly what the Hall–Higman Lemma 1.2.3
(`PiGroups.centralizer_piCore_le_piCore`) needs.
-/

section HallHigman

variable [Finite G] [Fact p.Prime]

omit [Fact p.Prime] in
/-- **Isaacs 7.6, Step 1(a).**  `Z(P) ≤ O_p(G)`: the centre of a Sylow `p`-subgroup centralizes
`O_p(G)`, which lies inside it. -/
theorem centerOf_sylow_le_piCore (hsolv : IsPiSeparable ({p} : Set ℕ) G)
    (hcore : piCore ({p}ᶜ : Set ℕ) G = ⊥) (P : Sylow p G) :
    centerOf (P : Subgroup G) ≤ piCore ({p} : Set ℕ) G :=
  le_trans
    ((centerOf_le_centralizer _).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (piCore_le_sylow P))))
    (centralizer_piCore_le_piCore hsolv hcore)

omit [Fact p.Prime] in
/-- **Isaacs 7.6, Step 1(b).**  Every subgroup containing `O_p(G)` again has trivial `p′`-core:
`O_p′(H)` centralizes `O_p(G)` because the two are normal in `H` and meet trivially, so
Hall–Higman puts it inside `O_p(G)`, where it meets `O_p′(H)` trivially. -/
theorem piCore_compl_eq_bot_of_piCore_le (hsolv : IsPiSeparable ({p} : Set ℕ) G)
    (hcore : piCore ({p}ᶜ : Set ℕ) G = ⊥) {H : Subgroup G}
    (hUH : piCore ({p} : Set ℕ) G ≤ H) : piCore ({p}ᶜ : Set ℕ) ↑H = ⊥ := by
  set U : Subgroup G := piCore ({p} : Set ℕ) G with hUdef
  set M : Subgroup G := (piCore ({p}ᶜ : Set ℕ) ↑H).map H.subtype with hMdef
  have hMH : M ≤ H := Subgroup.map_subtype_le _
  -- `M` and `U` are `π`- and `π′`-groups, so they meet trivially
  have hMpi : IsPiGroup ({p}ᶜ : Set ℕ) ↑M :=
    isPiGroup_piCore.of_equiv ((piCore ({p}ᶜ : Set ℕ) ↑H).equivMapOfInjective _
      H.subtype_injective)
  have hUpi : IsPiGroup (({p}ᶜ : Set ℕ)ᶜ) ↑U := by
    rw [compl_compl]
    exact isPiGroup_piCore
  have hdisj : M ⊓ U = ⊥ := disjoint_iff.mp (disjoint_of_isPiGroup hMpi hUpi)
  -- both are normal in `H`
  have hMconj : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M := by
    intro h hh m hm
    have hchar : ((piCore ({p}ᶜ : Set ℕ) ↑H).map H.subtype).subgroupOf H |>.Characteristic := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
      infer_instance
    have hmap : M.map (MulAut.conj h).toMonoidHom = M :=
      map_conj_of_characteristic_subgroupOf hMH hchar
        (map_conj_eq_self_iff.mpr (Subgroup.le_normalizer hh))
    exact hmap ▸ ⟨m, hm, rfl⟩
  have hUconj : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U :=
    fun h _ u hu => (inferInstance : U.Normal).conj_mem u hu h
  -- so `M` centralizes `U`
  have hMC : M ≤ Subgroup.centralizer (U : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (commute_of_inf_eq_bot hMH hUH hMconj hUconj hdisj hx (SetLike.mem_coe.mp hu)).symm
  -- Hall–Higman then puts `M` inside `U`, where it is trivial
  have hMU : M ≤ U := hMC.trans (centralizer_piCore_le_piCore hsolv hcore)
  have hMbot : M = ⊥ := le_bot_iff.mp (hdisj ▸ le_inf le_rfl hMU)
  exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hMbot

omit [Fact p.Prime] in
/-- **Isaacs 7.6, Step 1(c).**  In `Ḡ = G/O_p(G)` the `p′`-core contains its own centralizer,
because `O_p(Ḡ) = 1`. -/
theorem centralizer_piCoreCompl_quotient_le (hsolv : IsPiSeparable ({p} : Set ℕ) G) :
    Subgroup.centralizer
        ((piCore ({p}ᶜ : Set ℕ) (G ⧸ piCore ({p} : Set ℕ) G) : Subgroup _) : Set _)
      ≤ piCore ({p}ᶜ : Set ℕ) (G ⧸ piCore ({p} : Set ℕ) G) := by
  refine centralizer_piCore_le_piCore (IsPiSeparable.compl (hsolv.quotient _)) ?_
  rw [compl_compl]
  exact piCore_quotient_piCore_eq_bot

end HallHigman

/-- **Isaacs 7.6, Step 3**, the transfer of hypothesis (5).  If `O_p(G) ≤ H ≤ G` and
`S = P ⊓ H`, then `C_H(Z(S)) = S`.

`Z(P) ≤ O_p(G) ≤ H` by Step 1(a), so `Z(P) ≤ S` and hence `Z(P) ≤ Z(S)`; therefore
`C_G(Z(S)) ≤ C_G(Z(P)) = P`, and intersecting with `H` gives `S`. -/
theorem centralizer_centerOf_inf_eq [Finite G] [Fact p.Prime]
    (hsolv : IsPiSeparable ({p} : Set ℕ) G) (hcore : piCore ({p}ᶜ : Set ℕ) G = ⊥)
    (P : Sylow p G)
    (hP5 : Subgroup.centralizer ((centerOf (P : Subgroup G) : Subgroup G) : Set G)
      = (P : Subgroup G))
    {H : Subgroup G} (hUH : piCore ({p} : Set ℕ) G ≤ H) :
    Subgroup.centralizer ((centerOf ((P : Subgroup G) ⊓ H) : Subgroup G) : Set G) ⊓ H
      = (P : Subgroup G) ⊓ H := by
  have hZS : centerOf (P : Subgroup G) ≤ (P : Subgroup G) ⊓ H :=
    le_inf (centerOf_le _) ((centerOf_sylow_le_piCore hsolv hcore P).trans hUH)
  have hZZ : centerOf (P : Subgroup G) ≤ centerOf ((P : Subgroup G) ⊓ H) :=
    centerOf_le_centerOf_of_le hZS inf_le_left
  refine le_antisymm (le_inf ?_ inf_le_right) (le_inf (le_centralizer_centerOf _) inf_le_right)
  calc Subgroup.centralizer ((centerOf ((P : Subgroup G) ⊓ H) : Subgroup G) : Set G) ⊓ H
      ≤ Subgroup.centralizer ((centerOf ((P : Subgroup G) ⊓ H) : Subgroup G) : Set G) :=
        inf_le_left
    _ ≤ Subgroup.centralizer ((centerOf (P : Subgroup G) : Subgroup G) : Set G) :=
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZZ)
    _ = (P : Subgroup G) := hP5

/-!
## Step 2 of Isaacs' proof
-/

/-- **Isaacs 7.6, Step 2**, in contrapositive form.  If every member of `E(P)` lies in `O_p(G)`
then `J(P) = J(O_p(G))` is characteristic in `O_p(G)`, hence already normal in `G`. -/
theorem thompsonSubgroup_normal_of_forall_le_piCore [Finite G] [Fact p.Prime] (P : Sylow p G)
    (h : ∀ A ∈ maxElemAb p (P : Subgroup G), A ≤ piCore ({p} : Set ℕ) G) :
    (thompsonSubgroup p (P : Subgroup G)).Normal := by
  have hJU : thompsonSubgroup p (P : Subgroup G) ≤ piCore ({p} : Set ℕ) G := iSup₂_le h
  exact normal_of_characteristic_subgroupOf hJU
    (thompsonSubgroup_characteristic_of_le hJU (piCore_le_sylow P))

/-!
## Index arithmetic

Two bookkeeping lemmas about `Subgroup.relIndex` that Step 7 needs.
-/

/-- `|K : H ⊓ K| ⬝ |H ⊓ K| = |K|`. -/
theorem relIndex_mul_card_inf [Finite G] (H K : Subgroup G) :
    H.relIndex K * Nat.card ↥(H ⊓ K) = Nat.card ↥K := by
  have hcard : Nat.card ↥(H.subgroupOf K) = Nat.card ↥(H ⊓ K) := by
    rw [← Subgroup.card_map_of_injective (f := K.subtype) K.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
  have h := Subgroup.card_mul_index (H.subgroupOf K)
  rw [hcard] at h
  rw [Subgroup.relIndex, mul_comm]
  exact h

omit [Group G] in
/-- Cancel a common positive factor on both sides of `≤`. -/
theorem le_of_mul_le_mul_pos {a b c : ℕ} (hc : 0 < c) (h : c * a ≤ c * b) : a ≤ b :=
  Nat.le_of_mul_le_mul_left h hc

/-!
## Step 7 of Isaacs' proof

`|V : V ⊓ A| ≤ |A : U ⊓ A|`.  Writing `D = U ⊓ A`, the subgroup `VD` is elementary abelian —
`V` is central in `U` and both `V` and `D` are elementary abelian — and it lies in `P`, so
maximality of `A` in `E(P)` gives `|VD| ≤ |A|`.  Since `V ⊴ G`, the second isomorphism theorem
reads `|VD : V| = |D : D ⊓ V|`, and the claim is arithmetic from there.
-/

/-- `X` centralizes `Y` exactly when `Y` centralizes `X`. -/
theorem le_centralizer_comm {X Y : Subgroup G} :
    X ≤ Subgroup.centralizer (Y : Set G) ↔ Y ≤ Subgroup.centralizer (X : Set G) := by
  constructor <;>
    exact fun h a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (Subgroup.mem_centralizer_iff.mp (h hb) a ha).symm

/-- The product of two commuting elementary abelian subgroups is elementary abelian. -/
theorem IsElementaryAbelian.sup {A B : Subgroup G} (hA : IsElementaryAbelian p A)
    (hB : IsElementaryAbelian p B) (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    IsElementaryAbelian p (A ⊔ B) := by
  have hAA : A ≤ Subgroup.centralizer (A : Set G) :=
    fun x hx => Subgroup.mem_centralizer_iff.mpr fun c hc' => hA.1 c hc' x hx
  have hBB : B ≤ Subgroup.centralizer (B : Set G) :=
    fun x hx => Subgroup.mem_centralizer_iff.mpr fun c hc' => hB.1 c hc' x hx
  have hBA : B ≤ Subgroup.centralizer (A : Set G) :=
    fun y hy => Subgroup.mem_centralizer_iff.mpr fun c hc' => hc c hc' y hy
  have hAB : A ≤ Subgroup.centralizer (B : Set G) :=
    fun x hx => Subgroup.mem_centralizer_iff.mpr fun c hc' => (hc x hx c hc').symm
  have key : (A ⊔ B : Subgroup G) ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) :=
    sup_le (le_centralizer_comm.mpr (sup_le hAA hBA)) (le_centralizer_comm.mpr (sup_le hAB hBB))
  have hcomm : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (key hx) y hy).symm
  refine ⟨hcomm, ?_⟩
  have hclosed : (A ⊔ B : Subgroup G) ≤
      ({ carrier := {x : G | x ∈ (A ⊔ B : Subgroup G) ∧ x ^ p = 1}
         one_mem' := ⟨one_mem _, one_pow p⟩
         mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
           rw [Commute.mul_pow (hcomm _ ha.1 _ hb.1), ha.2, hb.2, one_mul]⟩
         inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ } :
        Subgroup G) :=
    sup_le (fun x hx => ⟨Subgroup.mem_sup_left hx, hA.2 x hx⟩)
      fun y hy => ⟨Subgroup.mem_sup_right hy, hB.2 y hy⟩
  exact fun x hx => (hclosed hx).2

/-- The centre of a normal subgroup is normal. -/
instance centerOf_normal {U : Subgroup G} [U.Normal] : (centerOf U).Normal :=
  inferInstanceAs ((U ⊓ Subgroup.centralizer (U : Set G)).Normal)

/-- The centre of a subgroup is abelian. -/
theorem centerOf_commute (U : Subgroup G) :
    ∀ x ∈ centerOf U, ∀ y ∈ centerOf U, x * y = y * x :=
  fun _ hx _ hy => Subgroup.mem_centralizer_iff.mp hy.2 _ hx.1

/-- `V = Ω₁(Z(U))` is elementary abelian. -/
theorem isElementaryAbelian_omegaOne_centerOf (U : Subgroup G) :
    IsElementaryAbelian p (omegaOne p (centerOf U)) :=
  isElementaryAbelian_omegaOne (centerOf_commute U)

/-- Every element of `Ω₁(Z(U))` commutes with every element of `U`. -/
theorem omegaOne_centerOf_commute {U : Subgroup G} {x y : G} (hx : x ∈ U)
    (hy : y ∈ omegaOne p (centerOf U)) : x * y = y * x :=
  Subgroup.mem_centralizer_iff.mp (omegaOne_le (centerOf U) hy).2 x hx

/-- **Isaacs 7.6, Step 7.**  With `U = O_p(G)`, `V = Ω₁(Z(U))`, `A ∈ E(P)` and `D = U ⊓ A`,

`|V : V ⊓ A| ≤ |A : D|`.

`VD` is elementary abelian and lies in `P`, so `|VD| ≤ |A|` by maximality of `A`.  Since `V ⊴ G`,
the second isomorphism theorem gives `|VD : V| = |D : D ⊓ V|`, and the bound is arithmetic. -/
theorem relIndex_omegaOne_le [Finite G] [Fact p.Prime] (P : Sylow p G) {A : Subgroup G}
    (hA : A ∈ maxElemAb p (P : Subgroup G)) :
    A.relIndex (omegaOne p (centerOf (piCore ({p} : Set ℕ) G)))
      ≤ (piCore ({p} : Set ℕ) G ⊓ A).relIndex A := by
  set U : Subgroup G := piCore ({p} : Set ℕ) G with hU
  set V : Subgroup G := omegaOne p (centerOf U) with hV
  set D : Subgroup G := U ⊓ A with hD
  have hUP : U ≤ (P : Subgroup G) := piCore_le_sylow P
  have hVU : V ≤ U := (omegaOne_le (centerOf U)).trans (centerOf_le U)
  have hDA : D ≤ A := inf_le_right
  -- `A.relIndex V = D.relIndex V`
  have hVAD : V ⊓ A = V ⊓ D := by rw [hD, ← inf_assoc, inf_eq_left.mpr hVU]
  have hAV : A.relIndex V = D.relIndex V := by
    rw [← Subgroup.inf_relIndex_left V A, ← Subgroup.inf_relIndex_left V D, hVAD]
  rw [hAV]
  -- `VD` is elementary abelian inside `P`
  have hVea : IsElementaryAbelian p V := isElementaryAbelian_omegaOne_centerOf U
  have hDea : IsElementaryAbelian p D := IsElementaryAbelian.of_le hA.2.1 hDA
  have hcomm : ∀ x ∈ D, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    omegaOne_centerOf_commute (hx.1) hy
  have hsupP : D ⊔ V ≤ (P : Subgroup G) := sup_le (hDA.trans hA.1) (hVU.trans hUP)
  have hcard : Nat.card ↥(D ⊔ V) ≤ Nat.card ↥A :=
    card_le_of_mem_maxElemAb hA hsupP (IsElementaryAbelian.sup hDea hVea hcomm)
  -- the four index identities
  have h1 : V.relIndex D * Nat.card ↥(V ⊓ D) = Nat.card ↥D := relIndex_mul_card_inf V D
  have h2 : D.relIndex V * Nat.card ↥(V ⊓ D) = Nat.card ↥V := by
    rw [inf_comm V D]; exact relIndex_mul_card_inf D V
  have h3 : V.relIndex (D ⊔ V) = V.relIndex D := Subgroup.relIndex_sup_right D V
  have h4 : V.relIndex D * Nat.card ↥V = Nat.card ↥(D ⊔ V) := by
    have := relIndex_mul_card_inf V (D ⊔ V)
    rwa [inf_eq_left.mpr (le_sup_right : V ≤ D ⊔ V), h3] at this
  have h5 : D.relIndex A * Nat.card ↥D = Nat.card ↥A := by
    have := relIndex_mul_card_inf D A
    rwa [inf_eq_left.mpr hDA] at this
  -- cancel
  have hrpos : 0 < V.relIndex D := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hmpos : 0 < Nat.card ↥(V ⊓ D) := Nat.card_pos
  refine le_of_mul_le_mul_pos hmpos (le_of_mul_le_mul_pos hrpos ?_)
  calc V.relIndex D * (Nat.card ↥(V ⊓ D) * D.relIndex V)
      = V.relIndex D * Nat.card ↥V := by rw [← h2]; ring
    _ = Nat.card ↥(D ⊔ V) := h4
    _ ≤ Nat.card ↥A := hcard
    _ = D.relIndex A * Nat.card ↥D := h5.symm
    _ = D.relIndex A * (V.relIndex D * Nat.card ↥(V ⊓ D)) := by rw [h1]
    _ = V.relIndex D * (Nat.card ↥(V ⊓ D) * D.relIndex A) := by ring

/-!
## Step 6 of Isaacs' proof

`C_G(V) = U`, so the action of `Ḡ = G/U` on `V` is faithful.  If `q ≠ p` and `x ∈ C_G(V)` has
order `q`, then `⟨x⟩` acts coprimely on the abelian `p`-group `Z(U)` and fixes each of its
elements of order `p` — those lie in `V` — so Corollary 4.35 makes `⟨x⟩` centralize `Z(U)`.  But
`Z(P) ≤ Z(U)`, so `⟨x⟩ ≤ C_G(Z(P)) = P`, which has no element of order `q`.
-/

/-- **Isaacs, Corollary 4.35** for a conjugation action inside `G`.  If `Q` normalizes an abelian
`p`-subgroup `Z` of order prime to `|Q|` and centralizes every element of order `p` in `Z`, then
`Q` centralizes `Z`. -/
theorem conj_eq_of_forall_orderOf_eq_prime [Finite G] [Fact p.Prime] {Q Z : Subgroup G}
    (hcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (hQN : Q ≤ Subgroup.normalizer (Z : Set G))
    (hZp : IsPGroup p ↥Z) (hcop : Nat.Coprime (Nat.card ↥Q) (Nat.card ↥Z))
    (hfix : ∀ z ∈ Z, orderOf z = p → ∀ a ∈ Q, a * z * a⁻¹ = z) :
    ∀ a ∈ Q, ∀ z ∈ Z, a * z * a⁻¹ = z := by
  let _instC : CommGroup ↥Z :=
    { (inferInstance : Group ↥Z) with
      mul_comm := fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2) }
  let _inst := CoprimeAction.conjActionOfLeNormalizer Q Z hQN
  have hcoe : ∀ (a : ↥Q) (g : ↥Z), ((a • g : ↥Z) : G) = (a : G) * (g : G) * (a : G)⁻¹ :=
    fun a g => CoprimeAction.conjActionOfLeNormalizer_coe Q Z hQN a g
  have hfix' : ∀ x : ↥Z, orderOf x = p → ∀ a : ↥Q, a • x = x := by
    intro x hx a
    refine Subtype.ext ?_
    rw [hcoe a x]
    exact hfix (x : G) x.2 (by rwa [Subgroup.orderOf_coe]) (a : G) a.2
  intro a ha z hz
  have h1 := CoprimeAction.smul_eq_self_of_forall_orderOf_eq_prime hZp hcop hfix'
    (⟨a, ha⟩ : ↥Q) (⟨z, hz⟩ : ↥Z)
  have h2 := hcoe (⟨a, ha⟩ : ↥Q) (⟨z, hz⟩ : ↥Z)
  rw [h1] at h2
  exact h2.symm

/-- **Isaacs 7.6, Step 6.**  `C_G(Ω₁(Z(U))) = O_p(G)`, so `Ḡ = G/O_p(G)` acts faithfully on
`V = Ω₁(Z(U))`. -/
theorem centralizer_omegaOne_centerOf_piCore [Finite G] [Fact p.Prime]
    (hsolv : IsPiSeparable ({p} : Set ℕ) G) (hcore : piCore ({p}ᶜ : Set ℕ) G = ⊥) (P : Sylow p G)
    (hP5 : Subgroup.centralizer ((centerOf (P : Subgroup G) : Subgroup G) : Set G)
      = (P : Subgroup G)) :
    Subgroup.centralizer
        ((omegaOne p (centerOf (piCore ({p} : Set ℕ) G)) : Subgroup G) : Set G)
      = piCore ({p} : Set ℕ) G := by
  have hp : p.Prime := Fact.out
  set U : Subgroup G := piCore ({p} : Set ℕ) G with hU
  set Z : Subgroup G := centerOf U with hZ
  set V : Subgroup G := omegaOne p Z with hV
  set K : Subgroup G := Subgroup.centralizer (V : Set G) with hK
  have hUP : U ≤ (P : Subgroup G) := piCore_le_sylow P
  have hUp : IsPGroup p ↥U :=
    IsPiGroup.isPGroup (p := p) (isPiGroup_piCore (π := ({p} : Set ℕ)) (G := G))
  have hZp : IsPGroup p ↥Z := hUp.to_le (centerOf_le U)
  -- `U ≤ K`
  have hUK : U ≤ K := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => (omegaOne_centerOf_commute hu hv).symm
  -- `K` is a `p`-group
  have hKp : IsPGroup p ↥K := by
    refine IsPiGroup.isPGroup (IsPiGroup.iff_card.mpr fun q hq => ?_)
    by_contra hqp
    obtain ⟨hqprime, hqdvd, -⟩ := Nat.mem_primeFactors.mp hq
    have : Fact q.Prime := ⟨hqprime⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) q hqdvd
    have hordx : orderOf ((x : G)) = q := by rw [Subgroup.orderOf_coe]; exact hx
    have hQK : Subgroup.zpowers ((x : G)) ≤ K := Subgroup.zpowers_le.mpr x.2
    have hcardQ : Nat.card ↥(Subgroup.zpowers ((x : G))) = q := by
      rw [Nat.card_zpowers, hordx]
    have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers ((x : G)))) (Nat.card ↥Z) := by
      obtain ⟨m, hm⟩ := hZp.exists_card_eq
      rw [hcardQ, hm]
      exact Nat.Coprime.pow_right m ((Nat.coprime_primes hqprime hp).mpr hqp)
    have hQN : Subgroup.zpowers ((x : G)) ≤ Subgroup.normalizer (Z : Set G) := fun g _ => by
      rw [Subgroup.normalizer_eq_top Z]; exact Subgroup.mem_top g
    have hfix : ∀ z ∈ Z, orderOf z = p → ∀ a ∈ Subgroup.zpowers ((x : G)), a * z * a⁻¹ = z := by
      intro z hz hzp a ha
      have hzV : z ∈ V := mem_omegaOne hz (by rw [← hzp]; exact pow_orderOf_eq_one z)
      have h1 : z * a = a * z := Subgroup.mem_centralizer_iff.mp (hQK ha) z hzV
      calc a * z * a⁻¹ = z * a * a⁻¹ := by rw [h1]
        _ = z := by group
    have hQZ := conj_eq_of_forall_orderOf_eq_prime (centerOf_commute U) hQN hZp hcop hfix
    -- `⟨x⟩ ≤ C_G(Z) ≤ C_G(Z(P)) = P`
    have hQC : Subgroup.zpowers ((x : G)) ≤ Subgroup.centralizer (Z : Set G) := fun a ha =>
      Subgroup.mem_centralizer_iff.mpr fun z hz => by
        have h1 : a * z * a⁻¹ = z := hQZ a ha z hz
        calc z * a = a * z * a⁻¹ * a := by rw [h1]
          _ = a * z := by group
    have hZPZ : centerOf (P : Subgroup G) ≤ Z :=
      centerOf_le_centerOf_of_le (centerOf_sylow_le_piCore hsolv hcore P) hUP
    have hQP : Subgroup.zpowers ((x : G)) ≤ (P : Subgroup G) := by
      refine hQC.trans ?_
      rw [← hP5]
      exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZPZ)
    -- but `P` is a `p`-group
    have hxP : (x : G) ∈ (P : Subgroup G) := hQP (Subgroup.mem_zpowers _)
    have hord2 : orderOf (⟨(x : G), hxP⟩ : ↥(P : Subgroup G)) = q := by
      rw [← Subgroup.orderOf_coe]
      exact hordx
    obtain ⟨k, hk⟩ := P.isPGroup' (⟨(x : G), hxP⟩ : ↥(P : Subgroup G))
    have hdvd2 : q ∣ p ^ k := hord2 ▸ orderOf_dvd_of_pow_eq_one hk
    exact hqp ((Nat.prime_dvd_prime_iff_eq hqprime hp).mp (hqprime.dvd_of_dvd_pow hdvd2))
  exact le_antisymm (le_piCore inferInstance (IsPGroup.isPiGroup hp hKp)) hUK

/-!
## Step 8 of Isaacs' proof

The normal-`P` theorem applied to the faithful action of `Ḡ` on `V`.  Step 4 gives `P = UA`, so
`P̄ = Ā`, which centralizes `V ⊓ A` because `A` is abelian; with Steps 5 and 7 this bounds
`|V : C_V(P̄)|` by `p`, and 7.5 makes `P̄ ⊴ Ḡ`.  Then `P ⊴ G`, so `A ≤ P ≤ O_p(G) = U` — which
contradicts the choice of `A`.
-/

/-- A lift through a quotient is injective as soon as the kernel is contained in the subgroup
quotiented out. -/
theorem lift_injective_of_ker_le {N : Type u} [Group N] {φ : G →* N} {U : Subgroup G} [U.Normal]
    (h : ∀ g ∈ U, φ g = 1) (hker : φ.ker ≤ U) :
    Function.Injective (QuotientGroup.lift U φ h) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨a⟩ hx
  have h1 : φ a = 1 := hx
  exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff a).mpr (hker (MonoidHom.mem_ker.mpr h1)))

/-- The kernel of the conjugation action on a normal subgroup is its centralizer. -/
theorem ker_conjNormal (N : Subgroup G) [N.Normal] :
    (MulAut.conjNormal (H := N)).ker = Subgroup.centralizer (N : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h n hn
    have h1 : ((MulAut.conjNormal g (⟨n, hn⟩ : ↥N) : ↥N) : G) = n := by rw [h]; rfl
    rw [MulAut.conjNormal_apply] at h1
    calc n * g = g * n * g⁻¹ * g := by rw [h1]
      _ = g * n := by group
  · intro h
    refine MulEquiv.ext fun n => Subtype.ext ?_
    rw [MulAut.conjNormal_apply]
    change g * (n : G) * g⁻¹ = (n : G)
    have h1 : (n : G) * g = g * (n : G) := h (n : G) n.2
    calc g * (n : G) * g⁻¹ = (n : G) * g * g⁻¹ := by rw [h1]
      _ = (n : G) := by group

/-- **Isaacs 7.6, Step 8.**  Steps 4–7 together are contradictory, so the minimal counterexample
cannot exist. -/
theorem step_eight [Finite G] [Fact p.Prime] (hp2 : p ≠ 2)
    (hsolv : IsPiSeparable ({p} : Set ℕ) G)
    (habel2 : ∀ B : Subgroup G, IsPGroup 2 ↥B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hcore : piCore ({p}ᶜ : Set ℕ) G = ⊥) (P : Sylow p G)
    (hP5 : Subgroup.centralizer ((centerOf (P : Subgroup G) : Subgroup G) : Set G)
      = (P : Subgroup G))
    {A : Subgroup G} (hA : A ∈ maxElemAb p (P : Subgroup G))
    (hAU : ¬ A ≤ piCore ({p} : Set ℕ) G)
    (hstep4 : (P : Subgroup G) = piCore ({p} : Set ℕ) G ⊔ A)
    (hstep5 : (piCore ({p} : Set ℕ) G ⊓ A).relIndex A = p) : False := by
  have hp : p.Prime := Fact.out
  set U : Subgroup G := piCore ({p} : Set ℕ) G with hU
  set V : Subgroup G := omegaOne p (centerOf U) with hV
  have hUP : U ≤ (P : Subgroup G) := piCore_le_sylow P
  have hVea : IsElementaryAbelian p V := isElementaryAbelian_omegaOne_centerOf U
  -- the conjugation action of `Ḡ = G/U` on `V`, faithful by Step 6
  have hker : (MulAut.conjNormal (H := V)).ker = U := by
    rw [ker_conjNormal, centralizer_omegaOne_centerOf_piCore hsolv hcore P hP5]
  have hUker : ∀ g ∈ U, (MulAut.conjNormal (H := V)) g = 1 := fun g hg => by
    rw [← MonoidHom.mem_ker, hker]; exact hg
  have hinj : Function.Injective
      (QuotientGroup.lift U (MulAut.conjNormal (H := V)) hUker) :=
    lift_injective_of_ker_le hUker (le_of_eq hker)
  let _instC : CommGroup ↥V :=
    { (inferInstance : Group ↥V) with
      mul_comm := fun x y => Subtype.ext (hVea.1 x.1 x.2 y.1 y.2) }
  let _instA : MulDistribMulAction (G ⧸ U) ↥V :=
    actionOfHom (QuotientGroup.lift U (MulAut.conjNormal (H := V)) hUker)
  have _instF : FaithfulSMul (G ⧸ U) ↥V := ⟨fun h => hinj (MulEquiv.ext fun x => h x)⟩
  have hexpV : ∀ x : ↥V, x ^ p = 1 := fun x => Subtype.ext (by
    push_cast
    exact hVea.2 x.1 x.2)
  -- the Sylow `p`-subgroup `P̄ = Ā` of `Ḡ`
  have hsurj : Function.Surjective (QuotientGroup.mk' U) := QuotientGroup.mk'_surjective U
  set Pbar : Sylow p (G ⧸ U) := P.mapSurjective hsurj with hPbar
  have hPbarcoe : (Pbar : Subgroup (G ⧸ U)) = A.map (QuotientGroup.mk' U) := by
    have hmapU : U.map (QuotientGroup.mk' U) = ⊥ := by
      rw [eq_bot_iff]
      rintro - ⟨u, hu, rfl⟩
      exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff u).mpr hu)
    rw [hPbar, Sylow.coe_mapSurjective, hstep4, Subgroup.map_sup, hmapU, bot_sup_eq]
  -- `A` fixes `V ⊓ A` pointwise, so `|V : C_V(P̄)| ≤ p`
  have hfix : A.subgroupOf V ≤ fixedOf ↥V (Pbar : Subgroup (G ⧸ U)) := by
    intro v hv g hg
    rw [hPbarcoe] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    refine Subtype.ext ?_
    change ((QuotientGroup.lift U (MulAut.conjNormal (H := V)) hUker)
      (QuotientGroup.mk' U a) (v : ↥V) : G) = (v : G)
    rw [show (QuotientGroup.lift U (MulAut.conjNormal (H := V)) hUker) (QuotientGroup.mk' U a)
      = MulAut.conjNormal (H := V) a from rfl, MulAut.conjNormal_apply]
    have hvA : (v : G) ∈ A := Subgroup.mem_subgroupOf.mp hv
    have hcomm : a * (v : G) = (v : G) * a := (hA.2.1.1 a ha (v : G) hvA)
    calc a * (v : G) * a⁻¹ = (v : G) * a * a⁻¹ := by rw [hcomm]
      _ = (v : G) := by group
  have hidx : (fixedOf ↥V (Pbar : Subgroup (G ⧸ U))).index ≤ p := by
    have h1 : (fixedOf ↥V (Pbar : Subgroup (G ⧸ U))).index ∣ (A.subgroupOf V).index :=
      Subgroup.index_dvd_of_le hfix
    have h2 : (A.subgroupOf V).index ≤ p := by
      rw [← Subgroup.relIndex]
      calc A.relIndex V ≤ (U ⊓ A).relIndex A := relIndex_omegaOne_le P hA
        _ = p := hstep5
    exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1) h2
  -- the normal-`P` theorem
  have hPbarnormal : (Pbar : Subgroup (G ⧸ U)).Normal :=
    normal_sylow_of_faithful hp2 (hsolv.quotient U)
      (forall_two_commute_surjective hsurj habel2) hexpV Pbar hidx
  have hPnormal : (P : Subgroup G).Normal := by
    refine normal_of_map_mk'_normal hUP ?_
    rwa [← Sylow.coe_mapSurjective hsurj, ← hPbar]
  -- so `A ≤ P ≤ O_p(G) = U`
  exact hAU (hA.1.trans (le_piCore hPnormal (IsPGroup.isPiGroup hp P.isPGroup')))

/-!
## `L`, the preimage of `O_p'(Ḡ)`

Isaacs writes `Ḡ = G/U` for `U = O_p(G)` and `L̄ = O_p'(Ḡ)`; `L` is the preimage of `L̄` in `G`,
so `U ≤ L ⊴ G` and `L/U` is a `p'`-group.  The one fact used over and over is that a `p`-subgroup
of `L` already lies in `U`.
-/

/-- `L`: the preimage in `G` of `O_p'(G/O_p(G))`. -/
def bigL (p : ℕ) (X : Type u) [Group X] : Subgroup X :=
  (piCore ({p}ᶜ : Set ℕ) (X ⧸ piCore ({p} : Set ℕ) X)).comap
    (QuotientGroup.mk' (piCore ({p} : Set ℕ) X))

instance bigL_normal (p : ℕ) (X : Type u) [Group X] : (bigL p X).Normal :=
  Subgroup.Normal.comap inferInstance _

theorem piCore_le_bigL : piCore ({p} : Set ℕ) G ≤ bigL p G := by
  intro x hx
  have h1 : (QuotientGroup.mk' (piCore ({p} : Set ℕ) G)) x = 1 :=
    (QuotientGroup.eq_one_iff x).mpr hx
  change x ∈ Subgroup.comap _ _
  rw [Subgroup.mem_comap, h1]
  exact one_mem _

theorem map_bigL_le : (bigL p G).map (QuotientGroup.mk' (piCore ({p} : Set ℕ) G))
    ≤ piCore ({p}ᶜ : Set ℕ) (G ⧸ piCore ({p} : Set ℕ) G) := by
  rintro - ⟨x, hx, rfl⟩
  exact hx

/-- **A `p`-subgroup of `L` lies in `U`**, since `L/U` is a `p'`-group. -/
theorem le_piCore_of_isPGroup_of_le_bigL [Finite G] [Fact p.Prime] {X : Subgroup G}
    (hXp : IsPGroup p ↥X) (hXL : X ≤ bigL p G) : X ≤ piCore ({p} : Set ℕ) G := by
  have hp : p.Prime := Fact.out
  have hmaple : X.map (QuotientGroup.mk' (piCore ({p} : Set ℕ) G))
      ≤ piCore ({p}ᶜ : Set ℕ) (G ⧸ piCore ({p} : Set ℕ) G) :=
    (Subgroup.map_mono hXL).trans map_bigL_le
  have hdisj := disjoint_of_isPiGroup
    (IsPGroup.isPiGroup hp (hXp.map (QuotientGroup.mk' (piCore ({p} : Set ℕ) G))))
    (isPiGroup_piCore (π := ({p}ᶜ : Set ℕ)) (G := G ⧸ piCore ({p} : Set ℕ) G))
  have hbot : X.map (QuotientGroup.mk' (piCore ({p} : Set ℕ) G)) = ⊥ :=
    le_bot_iff.mp ((disjoint_iff.mp hdisj) ▸ le_inf le_rfl hmaple)
  intro x hx
  have h1 : (QuotientGroup.mk' (piCore ({p} : Set ℕ) G)) x = 1 :=
    Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_map_of_mem _ hx)
  exact (QuotientGroup.eq_one_iff x).mp h1

/-!
## Step 3 of Isaacs' proof

If `U A ≤ H < G` and `P ⊓ H` is a Sylow `p`-subgroup of `H`, then `⁅A, H ⊓ L⁆ ≤ U` — Isaacs'
"`Ā` centralizes `H̄ ⊓ L̄`".

`H` inherits the hypotheses of the theorem, so induction gives `J(P ⊓ H) ⊴ H`; and `A ∈ E(P ⊓ H)`,
so `A ≤ J := J(P ⊓ H)`.  For `a ∈ A` and `h ∈ H ⊓ L` the commutator lies in `J`, because `h`
normalizes `J`, and in `L`, because `L ⊴ G`.  But `J` is a `p`-group, so `J ⊓ L ≤ U`.
-/

/-- The centre of `K`, read inside a subgroup `H` containing `K`. -/
theorem centerOf_subgroupOf {H K : Subgroup G} (hKH : K ≤ H) :
    centerOf (K.subgroupOf H) = (centerOf K).subgroupOf H := by
  have h1 := centralizer_map_subtype (H := H) (K.subgroupOf H)
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKH] at h1
  simp only [Subgroup.subgroupOf] at h1
  simp only [centerOf, Subgroup.subgroupOf, Subgroup.comap_inf]
  rw [h1]

/-- `A`, read inside `H`, lies in the Thompson subgroup of `P ⊓ H`. -/
theorem le_thompsonSubgroup_subgroupOf {P A H : Subgroup G} (hA : A ∈ maxElemAb p P)
    (hAH : A ≤ H) :
    A.subgroupOf H ≤ thompsonSubgroup p ((P ⊓ H).subgroupOf H) := by
  refine le_thompsonSubgroup ⟨Subgroup.comap_mono (le_inf hA.1 hAH),
    hA.2.1.comap_of_injective H.subtype_injective, ?_⟩
  intro B hB hBea
  have hBmap : B.map H.subtype ≤ P := by
    refine (Subgroup.map_mono hB).trans ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (inf_le_right : P ⊓ H ≤ H)]
    exact inf_le_left
  have h1 : Nat.card ↥(B.map H.subtype) ≤ Nat.card ↥A :=
    card_le_of_mem_maxElemAb hA hBmap (hBea.map H.subtype)
  have h2 : Nat.card ↥(B.map H.subtype) = Nat.card ↥B :=
    Subgroup.card_map_of_injective H.subtype_injective
  have h3 : Nat.card ↥((A.subgroupOf H).map H.subtype) = Nat.card ↥(A.subgroupOf H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAH] at h3
  rw [h2, h3] at h1
  exact h1

/-- **Isaacs 7.6, Step 3.**  For `U A ≤ H < G` with `P ⊓ H` Sylow in `H`, every commutator
`a h a⁻¹ h⁻¹` with `a ∈ A` and `h ∈ H ⊓ L` lies in `U`. -/
theorem step_three [Finite G] [Fact p.Prime]
    (IH : ∀ (X : Type u) [Group X] [Finite X], Nat.card X < Nat.card G →
      IsPiSeparable ({p} : Set ℕ) X →
      (∀ B : Subgroup X, IsPGroup 2 ↥B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      piCore ({p}ᶜ : Set ℕ) X = ⊥ →
      ∀ S : Sylow p X,
        Subgroup.centralizer ((centerOf (S : Subgroup X) : Subgroup X) : Set X)
          = (S : Subgroup X) →
        (thompsonSubgroup p (S : Subgroup X)).Normal)
    (hsolv : IsPiSeparable ({p} : Set ℕ) G)
    (habel2 : ∀ B : Subgroup G, IsPGroup 2 ↥B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hcore : piCore ({p}ᶜ : Set ℕ) G = ⊥) (P : Sylow p G)
    (hP5 : Subgroup.centralizer ((centerOf (P : Subgroup G) : Subgroup G) : Set G)
      = (P : Subgroup G))
    {A : Subgroup G} (hA : A ∈ maxElemAb p (P : Subgroup G))
    {H : Subgroup G} (hUH : piCore ({p} : Set ℕ) G ≤ H) (hAH : A ≤ H) (hHne : H ≠ ⊤)
    (hSyl : ¬ p ∣ ((P : Subgroup G) ⊓ H).relIndex H) :
    ∀ a ∈ A, ∀ h ∈ H ⊓ bigL p G, a * h * a⁻¹ * h⁻¹ ∈ piCore ({p} : Set ℕ) G := by
  have hPHle : (P : Subgroup G) ⊓ H ≤ H := inf_le_right
  -- `P ⊓ H`, read inside `H`, is a Sylow `p`-subgroup
  have hSp : IsPGroup p ↥(((P : Subgroup G) ⊓ H).subgroupOf H) :=
    (P.isPGroup'.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe hPHle).symm
  have hSi : ¬ p ∣ (((P : Subgroup G) ⊓ H).subgroupOf H).index := hSyl
  set S : Sylow p ↥H := hSp.toSylow hSi with hS
  have hScoe : (S : Subgroup ↥H) = ((P : Subgroup G) ⊓ H).subgroupOf H := rfl
  -- the induction hypothesis applies to `H`
  have hcardH : Nat.card ↥H < Nat.card G := by
    calc Nat.card ↥H < Nat.card ↥(⊤ : Subgroup G) :=
          card_lt_card_of_lt (lt_of_le_of_ne le_top hHne)
      _ = Nat.card G := Subgroup.card_top
  have hH5 : Subgroup.centralizer ((centerOf (S : Subgroup ↥H) : Subgroup ↥H) : Set ↥H)
      = (S : Subgroup ↥H) := by
    rw [hScoe, centerOf_subgroupOf hPHle, ← centralizer_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr ((centerOf_le _).trans hPHle),
      ← Subgroup.inf_subgroupOf_right, centralizer_centerOf_inf_eq hsolv hcore P hP5 hUH]
  have hJnormal : (thompsonSubgroup p (S : Subgroup ↥H)).Normal :=
    IH ↥H hcardH (hsolv.subgroup H) (forall_two_commute_subgroup habel2 H)
      (piCore_compl_eq_bot_of_piCore_le hsolv hcore hUH) S hH5
  -- `A ≤ J`, and `J` is a `p`-subgroup normalized by `H`
  have hAJ : A.subgroupOf H ≤ thompsonSubgroup p (S : Subgroup ↥H) := by
    rw [hScoe]; exact le_thompsonSubgroup_subgroupOf hA hAH
  set J : Subgroup G := (thompsonSubgroup p (S : Subgroup ↥H)).map H.subtype with hJ
  have hJP : J ≤ (P : Subgroup G) := by
    rw [hJ]
    refine (Subgroup.map_mono (thompsonSubgroup_le p (S : Subgroup ↥H))).trans ?_
    rw [hScoe, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPHle]
    exact inf_le_left
  have hJp : IsPGroup p ↥J := P.isPGroup'.to_le hJP
  have hAJ' : A ≤ J := fun x hx =>
    ⟨⟨x, hAH hx⟩, hAJ (by rwa [Subgroup.mem_subgroupOf]), rfl⟩
  have hJconj : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J := by
    rintro h hh - ⟨j', hj', rfl⟩
    exact ⟨⟨h, hh⟩ * j' * ⟨h, hh⟩⁻¹, hJnormal.conj_mem j' hj' ⟨h, hh⟩, rfl⟩
  -- `⁅H ⊓ L, A⁆ ≤ ⁅H ⊓ L, J⁆ ≤ (H ⊓ L) ⊓ J = L ⊓ J ≤ U`
  have hJH : J ≤ H := by
    rw [hJ]; exact Subgroup.map_subtype_le _
  have hNconj : ∀ y ∈ H, ∀ z ∈ H ⊓ bigL p G, y * z * y⁻¹ ∈ H ⊓ bigL p G := fun y hy z hz =>
    Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hy hz.1) (H.inv_mem hy),
      (bigL_normal p G).conj_mem z hz.2 y⟩
  intro a ha h hh
  have hmem := commutatorElement_mem_inf hJH (inf_le_left : H ⊓ bigL p G ≤ H) hJconj hNconj
    (hAJ' ha) hh
  exact le_piCore_of_isPGroup_of_le_bigL (hJp.to_le (inf_le_left : J ⊓ bigL p G ≤ J))
    inf_le_right ⟨hmem.1, hmem.2.2⟩

/-!
## Step 4 of Isaacs' proof

`G = LA` and `P = UA`.

Writing `H = LA`, the subgroup `UA` is a `p`-subgroup of `H` with `|H : UA| = |L : U|`, a
`p'`-number, so `UA ∈ Syl_p(H)` and `UA = H ⊓ P`.  If `H < G`, Step 3 would make `Ā` centralize
`L̄`, hence lie in `L̄` by Step 1(c) — impossible for a `p`-group not inside `U`.  So `H = G`, and
then `UA = G ⊓ P = P`.
-/

/-- `|L : U|` is prime to `p`, since `L/U = O_p'(Ḡ)`. -/
theorem not_dvd_relIndex_piCore_bigL [Finite G] [Fact p.Prime] :
    ¬ p ∣ (piCore ({p} : Set ℕ) G).relIndex (bigL p G) := by
  set U : Subgroup G := piCore ({p} : Set ℕ) G with hU
  set f : ↥(bigL p G) →* G ⧸ U := (QuotientGroup.mk' U).comp (bigL p G).subtype with hf
  have hker : f.ker = U.subgroupOf (bigL p G) := by
    rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have hrange : f.range = piCore ({p}ᶜ : Set ℕ) (G ⧸ U) := by
    rw [hf, MonoidHom.range_comp, (bigL p G).range_subtype, bigL,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective U)]
  have hcard : Nat.card (↥(bigL p G) ⧸ U.subgroupOf (bigL p G))
      = Nat.card ↥(piCore ({p}ᶜ : Set ℕ) (G ⧸ U)) := by
    rw [← hrange, ← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  intro hdvd
  rw [Subgroup.relIndex, Subgroup.index_eq_card, hcard] at hdvd
  exact (IsPiGroup.iff_card.mp isPiGroup_piCore p
    (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)) rfl

/-- `U A` meets `L` in exactly `U`. -/
theorem sup_inf_bigL [Finite G] [Fact p.Prime] {A : Subgroup G} (hAp : IsPGroup p ↥A) :
    (piCore ({p} : Set ℕ) G ⊔ A) ⊓ bigL p G = piCore ({p} : Set ℕ) G := by
  refine le_antisymm ?_ (le_inf le_sup_left piCore_le_bigL)
  exact le_piCore_of_isPGroup_of_le_bigL
    ((IsPGroup.to_sup_of_normal_left
      (IsPiGroup.isPGroup (p := p) (isPiGroup_piCore (π := ({p} : Set ℕ)) (G := G)))
      hAp).to_le inf_le_left) inf_le_right

/-- `|LA : UA| = |L : U|`. -/
theorem relIndex_sup_eq [Finite G] [Fact p.Prime] {A : Subgroup G} (hAp : IsPGroup p ↥A) :
    (piCore ({p} : Set ℕ) G ⊔ A).relIndex (bigL p G ⊔ A)
      = (piCore ({p} : Set ℕ) G).relIndex (bigL p G) := by
  set U : Subgroup G := piCore ({p} : Set ℕ) G with hU
  set L : Subgroup G := bigL p G with hL
  have hUL : U ≤ L := piCore_le_bigL
  have hsup : (U ⊔ A) ⊔ L = L ⊔ A := by
    refine le_antisymm (sup_le (sup_le (hUL.trans le_sup_left) le_sup_right) le_sup_left) ?_
    exact sup_le le_sup_right ((le_sup_right : A ≤ U ⊔ A).trans le_sup_left)
  have hUAL : (U ⊔ A) ⊓ L = U := sup_inf_bigL hAp
  have h1 : L.relIndex (L ⊔ A) = U.relIndex (U ⊔ A) := by
    rw [← hsup, Subgroup.relIndex_sup_right (U ⊔ A) L, ← Subgroup.inf_relIndex_right L (U ⊔ A),
      inf_comm L (U ⊔ A), hUAL]
  have e1 : L.relIndex (L ⊔ A) * Nat.card ↥L = Nat.card ↥(L ⊔ A) := by
    have h := relIndex_mul_card_inf L (L ⊔ A)
    rwa [inf_eq_left.mpr (le_sup_left : L ≤ L ⊔ A)] at h
  have e2 : (U ⊔ A).relIndex (L ⊔ A) * Nat.card ↥(U ⊔ A) = Nat.card ↥(L ⊔ A) := by
    have h := relIndex_mul_card_inf (U ⊔ A) (L ⊔ A)
    rwa [inf_eq_left.mpr (sup_le (hUL.trans le_sup_left) le_sup_right)] at h
  have e3 : U.relIndex (U ⊔ A) * Nat.card ↥U = Nat.card ↥(U ⊔ A) := by
    have h := relIndex_mul_card_inf U (U ⊔ A)
    rwa [inf_eq_left.mpr (le_sup_left : U ≤ U ⊔ A)] at h
  have e4 : U.relIndex L * Nat.card ↥U = Nat.card ↥L := by
    have h := relIndex_mul_card_inf U L
    rwa [inf_eq_left.mpr hUL] at h
  have hpos : 0 < U.relIndex (U ⊔ A) * Nat.card ↥U :=
    Nat.mul_pos (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  calc U.relIndex (U ⊔ A) * Nat.card ↥U * ((U ⊔ A).relIndex (L ⊔ A))
      = (U ⊔ A).relIndex (L ⊔ A) * Nat.card ↥(U ⊔ A) := by rw [← e3]; ring
    _ = Nat.card ↥(L ⊔ A) := e2
    _ = L.relIndex (L ⊔ A) * Nat.card ↥L := e1.symm
    _ = U.relIndex (U ⊔ A) * (U.relIndex L * Nat.card ↥U) := by rw [h1, e4]
    _ = U.relIndex (U ⊔ A) * Nat.card ↥U * U.relIndex L := by ring

/-- A `p`-subgroup of `H` containing a subgroup of index prime to `p` equals it. -/
theorem eq_of_isPGroup_of_not_dvd_relIndex [Finite G] [Fact p.Prime] {K X H : Subgroup G}
    (hKX : K ≤ X) (hXH : X ≤ H) (hXp : IsPGroup p ↥X) (hK : ¬ p ∣ K.relIndex H) : K = X := by
  have hrel := Subgroup.relIndex_mul_relIndex K X H hKX hXH
  obtain ⟨m, hm⟩ := hXp.exists_card_eq
  have hdvd : K.relIndex X ∣ p ^ m := by
    rw [← hm]
    exact ⟨Nat.card ↥(K ⊓ X), (relIndex_mul_card_inf K X).symm⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    exact hK ⟨X.relIndex H * p ^ (k - 1), by
      rw [← hrel, hk]
      have : p ^ k = p * p ^ (k - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [this]; ring⟩
  rw [hk0, pow_zero] at hk
  have htop : K.subgroupOf X = ⊤ := Subgroup.index_eq_one.mp hk
  exact le_antisymm hKX (Subgroup.subgroupOf_eq_top.mp htop)

/-- **Isaacs 7.6, Step 4.**  `G = LA` and `P = UA`. -/
theorem step_four [Finite G] [Fact p.Prime]
    (IH : ∀ (X : Type u) [Group X] [Finite X], Nat.card X < Nat.card G →
      IsPiSeparable ({p} : Set ℕ) X →
      (∀ B : Subgroup X, IsPGroup 2 ↥B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      piCore ({p}ᶜ : Set ℕ) X = ⊥ →
      ∀ S : Sylow p X,
        Subgroup.centralizer ((centerOf (S : Subgroup X) : Subgroup X) : Set X)
          = (S : Subgroup X) →
        (thompsonSubgroup p (S : Subgroup X)).Normal)
    (hsolv : IsPiSeparable ({p} : Set ℕ) G)
    (habel2 : ∀ B : Subgroup G, IsPGroup 2 ↥B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hcore : piCore ({p}ᶜ : Set ℕ) G = ⊥) (P : Sylow p G)
    (hP5 : Subgroup.centralizer ((centerOf (P : Subgroup G) : Subgroup G) : Set G)
      = (P : Subgroup G))
    {A : Subgroup G} (hA : A ∈ maxElemAb p (P : Subgroup G))
    (hAU : ¬ A ≤ piCore ({p} : Set ℕ) G) :
    bigL p G ⊔ A = ⊤ ∧ (P : Subgroup G) = piCore ({p} : Set ℕ) G ⊔ A := by
  set U : Subgroup G := piCore ({p} : Set ℕ) G with hU
  set L : Subgroup G := bigL p G with hL
  have hUL : U ≤ L := piCore_le_bigL
  have hAp : IsPGroup p ↥A := hA.2.1.isPGroup
  have hUAP : U ⊔ A ≤ (P : Subgroup G) := sup_le (piCore_le_sylow P) hA.1
  have hUAH : U ⊔ A ≤ L ⊔ A := sup_le (hUL.trans le_sup_left) le_sup_right
  have hSylUA : ¬ p ∣ (U ⊔ A).relIndex (L ⊔ A) := by
    rw [relIndex_sup_eq hAp]; exact not_dvd_relIndex_piCore_bigL
  have hPH : (P : Subgroup G) ⊓ (L ⊔ A) = U ⊔ A :=
    (eq_of_isPGroup_of_not_dvd_relIndex (le_inf hUAP hUAH) inf_le_right
      (P.isPGroup'.to_le inf_le_left) hSylUA).symm
  -- `L A = ⊤`
  have hHtop : L ⊔ A = ⊤ := by
    by_contra hHne
    have h3 := step_three IH hsolv habel2 hcore P hP5 hA (hUL.trans le_sup_left) le_sup_right
      hHne (by rw [hPH]; exact hSylUA)
    -- `Ā` centralizes `L̄`
    have hAC : A.map (QuotientGroup.mk' U) ≤ Subgroup.centralizer
        ((piCore ({p}ᶜ : Set ℕ) (G ⧸ U) : Subgroup (G ⧸ U)) : Set (G ⧸ U)) := by
      rintro - ⟨a, ha, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro y hy
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective U y
      have hxL : x ∈ L := hy
      have hcomm : a * x * a⁻¹ * x⁻¹ ∈ U :=
        h3 a ha x ⟨(le_sup_left : L ≤ L ⊔ A) hxL, hxL⟩
      have h5 : (QuotientGroup.mk' U) (a * x * a⁻¹ * x⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hcomm
      have h7 : (QuotientGroup.mk' U) a * (QuotientGroup.mk' U) x
          * ((QuotientGroup.mk' U) a)⁻¹ * ((QuotientGroup.mk' U) x)⁻¹ = 1 := by
        simp only [← map_inv, ← map_mul]
        exact h5
      have h8 : (QuotientGroup.mk' U) a * (QuotientGroup.mk' U) x
          * ((QuotientGroup.mk' U) a)⁻¹ = (QuotientGroup.mk' U) x := mul_inv_eq_one.mp h7
      calc (QuotientGroup.mk' U) x * (QuotientGroup.mk' U) a
          = ((QuotientGroup.mk' U) a * (QuotientGroup.mk' U) x
              * ((QuotientGroup.mk' U) a)⁻¹) * (QuotientGroup.mk' U) a := by rw [h8]
        _ = (QuotientGroup.mk' U) a * (QuotientGroup.mk' U) x := by group
    have hAL' : A.map (QuotientGroup.mk' U) ≤ piCore ({p}ᶜ : Set ℕ) (G ⧸ U) :=
      hAC.trans (centralizer_piCoreCompl_quotient_le hsolv)
    have hAL : A ≤ L := fun a ha => hAL' (Subgroup.mem_map_of_mem _ ha)
    exact hAU (le_piCore_of_isPGroup_of_le_bigL hAp hAL)
  refine ⟨hHtop, ?_⟩
  rw [← hPH, hHtop, inf_top_eq]

/-!
## Step 5 of Isaacs' proof

`|Ā| = p`.

`Ā` is a nontrivial elementary abelian group, so it is enough that it be cyclic, and that is
Lemma 6.20 applied to the coprime action of `Ā` on `L̄`: the action is faithful because
`C_Ḡ(L̄) ≤ L̄` and `L̄ ⊓ Ā = 1`, and `Ā` acts trivially on every proper `Ā`-invariant subgroup
`M̄ < L̄` by Step 3 applied to `H = M A`, which is proper because `M A ⊓ L = M`.
-/

/-- If `A` normalizes `M` with `U ≤ M ≤ L`, then `M A` meets `L` in `M`. -/
theorem sup_inf_bigL_le [Finite G] [Fact p.Prime] {M A : Subgroup G} (hAp : IsPGroup p ↥A)
    (hUM : piCore ({p} : Set ℕ) G ≤ M) (hML : M ≤ bigL p G)
    (hAN : A ≤ Subgroup.normalizer (M : Set G)) :
    (M ⊔ A) ⊓ bigL p G ≤ M := by
  intro x hx
  have h1 : x ∈ ((M ⊔ A : Subgroup G) : Set G) := hx.1
  rw [Subgroup.coe_mul_of_right_le_normalizer_left M A hAN] at h1
  obtain ⟨m, hm, a, ha, rfl⟩ := h1
  have haL : a ∈ bigL p G := by
    have hmL : m ∈ bigL p G := hML hm
    have hrw : a = m⁻¹ * (m * a) := by group
    rw [hrw]
    exact mul_mem (inv_mem hmL) hx.2
  have haU : a ∈ piCore ({p} : Set ℕ) G :=
    le_piCore_of_isPGroup_of_le_bigL (hAp.to_le (inf_le_left : A ⊓ bigL p G ≤ A))
      inf_le_right ⟨ha, haL⟩
  exact mul_mem hm (hUM haU)

/-- `Ā ⊓ L̄ = 1`: the image of `A` is a `p`-group and `L̄` is a `p'`-group. -/
theorem inf_map_bigL_eq_bot [Finite G] [Fact p.Prime] {A : Subgroup G} (hAp : IsPGroup p ↥A) :
    A.map (QuotientGroup.mk' (piCore ({p} : Set ℕ) G))
        ⊓ piCore ({p}ᶜ : Set ℕ) (G ⧸ piCore ({p} : Set ℕ) G) = ⊥ :=
  disjoint_iff.mp (disjoint_of_isPiGroup
    (IsPGroup.isPiGroup Fact.out (hAp.map (QuotientGroup.mk' (piCore ({p} : Set ℕ) G))))
    isPiGroup_piCore)

/-- `|Ā| = |A : U ⊓ A|`. -/
theorem card_map_mk'_eq_relIndex [Finite G] {A : Subgroup G} :
    Nat.card ↥(A.map (QuotientGroup.mk' (piCore ({p} : Set ℕ) G)))
      = (piCore ({p} : Set ℕ) G ⊓ A).relIndex A := by
  set U : Subgroup G := piCore ({p} : Set ℕ) G with hU
  set f : ↥A →* G ⧸ U := (QuotientGroup.mk' U).comp A.subtype with hf
  have hker : f.ker = U.subgroupOf A := by
    rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have hrange : f.range = A.map (QuotientGroup.mk' U) := by
    rw [hf, MonoidHom.range_comp, A.range_subtype]
  rw [← hrange, Subgroup.inf_relIndex_right, Subgroup.relIndex, ← hker,
    Subgroup.index_eq_card]
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv).symm

/-- **Isaacs 7.6, Step 5.**  `|Ā| = p`, i.e. `|A : U ⊓ A| = p`. -/
theorem step_five [Finite G] [Fact p.Prime]
    (IH : ∀ (X : Type u) [Group X] [Finite X], Nat.card X < Nat.card G →
      IsPiSeparable ({p} : Set ℕ) X →
      (∀ B : Subgroup X, IsPGroup 2 ↥B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      piCore ({p}ᶜ : Set ℕ) X = ⊥ →
      ∀ S : Sylow p X,
        Subgroup.centralizer ((centerOf (S : Subgroup X) : Subgroup X) : Set X)
          = (S : Subgroup X) →
        (thompsonSubgroup p (S : Subgroup X)).Normal)
    (hsolv : IsPiSeparable ({p} : Set ℕ) G)
    (habel2 : ∀ B : Subgroup G, IsPGroup 2 ↥B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hcore : piCore ({p}ᶜ : Set ℕ) G = ⊥) (P : Sylow p G)
    (hP5 : Subgroup.centralizer ((centerOf (P : Subgroup G) : Subgroup G) : Set G)
      = (P : Subgroup G))
    {A : Subgroup G} (hA : A ∈ maxElemAb p (P : Subgroup G))
    (hAU : ¬ A ≤ piCore ({p} : Set ℕ) G)
    (hstep4 : (P : Subgroup G) = piCore ({p} : Set ℕ) G ⊔ A) :
    (piCore ({p} : Set ℕ) G ⊓ A).relIndex A = p := by
  have hp : p.Prime := Fact.out
  set U : Subgroup G := piCore ({p} : Set ℕ) G with hU
  set Q : G →* G ⧸ U := QuotientGroup.mk' U with hQ
  set Lb : Subgroup (G ⧸ U) := piCore ({p}ᶜ : Set ℕ) (G ⧸ U) with hLb
  set Ab : Subgroup (G ⧸ U) := A.map Q with hAb
  have hAp : IsPGroup p ↥A := hA.2.1.isPGroup
  have hAbea : IsElementaryAbelian p Ab := hA.2.1.map Q
  have hAbp : IsPGroup p ↥Ab := hAbea.isPGroup
  have hbigL : bigL p G = Lb.comap Q := rfl
  -- `Ā` is nontrivial
  have hAbne : Ab ≠ ⊥ := by
    intro hbot
    refine hAU fun a ha => ?_
    have h1 : Q a = 1 := Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_map_of_mem Q ha)
    exact (QuotientGroup.eq_one_iff a).mp h1
  -- the coprime conjugation action of `Ā` on `L̄`
  have hcopL : ¬ p ∣ Nat.card ↥Lb := fun hdvd =>
    (IsPiGroup.iff_card.mp isPiGroup_piCore p
      (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩)) rfl
  have hcop : Nat.Coprime p (Nat.card ↥Lb) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hcopL
  have hAbN : Ab ≤ Subgroup.normalizer (Lb : Set (G ⧸ U)) := fun g _ => by
    rw [Subgroup.normalizer_eq_top Lb]; exact Subgroup.mem_top g
  let _instC : CommGroup ↥Ab :=
    { (inferInstance : Group ↥Ab) with
      mul_comm := fun x y => Subtype.ext (hAbea.1 x.1 x.2 y.1 y.2) }
  let _instA : MulDistribMulAction ↥Ab ↥Lb := CoprimeAction.conjActionOfLeNormalizer Ab Lb hAbN
  have hcoe : ∀ (a : ↥Ab) (g : ↥Lb),
      ((a • g : ↥Lb) : G ⧸ U) = (a : G ⧸ U) * (g : G ⧸ U) * (a : G ⧸ U)⁻¹ :=
    fun a g => CoprimeAction.conjActionOfLeNormalizer_coe Ab Lb hAbN a g
  -- faithfulness, from Step 1(c) and `Ā ⊓ L̄ = 1`
  have hbotAL : Ab ⊓ Lb = ⊥ := inf_map_bigL_eq_bot hAp
  have instF : FaithfulSMul ↥Ab ↥Lb := ⟨fun {a b} h => by
    have hc : ((b : G ⧸ U))⁻¹ * (a : G ⧸ U) ∈ Subgroup.centralizer (Lb : Set (G ⧸ U)) := by
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      have h1 := congrArg (Subtype.val) (h (⟨y, hy⟩ : ↥Lb))
      rw [hcoe, hcoe] at h1
      calc y * (((b : G ⧸ U))⁻¹ * (a : G ⧸ U))
          = (b : G ⧸ U)⁻¹ * ((b : G ⧸ U) * y * (b : G ⧸ U)⁻¹) * (b : G ⧸ U)
            * ((b : G ⧸ U)⁻¹ * (a : G ⧸ U)) := by group
        _ = (b : G ⧸ U)⁻¹ * ((a : G ⧸ U) * y * (a : G ⧸ U)⁻¹) * (b : G ⧸ U)
            * ((b : G ⧸ U)⁻¹ * (a : G ⧸ U)) := by rw [← h1]
        _ = ((b : G ⧸ U))⁻¹ * (a : G ⧸ U) * y := by group
    have hmem : ((b : G ⧸ U))⁻¹ * (a : G ⧸ U) ∈ Ab ⊓ Lb :=
      ⟨mul_mem (Ab.inv_mem b.2) a.2, centralizer_piCoreCompl_quotient_le hsolv hc⟩
    rw [hbotAL, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact Subtype.ext hmem.symm⟩
  -- Lemma 6.20: `Ā` is cyclic
  have htriv : ∀ Ht : Subgroup ↥Lb, NoncyclicAbelian.IsInvariant ↥Ab ↥Lb Ht → Ht ≠ ⊤ →
      ∀ a : ↥Ab, ∀ x ∈ Ht, a • x = x := by
    intro Ht hinv hne a x hx
    set Mb : Subgroup (G ⧸ U) := Ht.map Lb.subtype with hMb
    set M : Subgroup G := Mb.comap Q with hM
    have hMbL : Mb ≤ Lb := Subgroup.map_subtype_le _
    have hUM : U ≤ M := fun u hu => by
      have h1 : Q u = 1 := (QuotientGroup.eq_one_iff u).mpr hu
      rw [hM, Subgroup.mem_comap, h1]
      exact one_mem _
    have hML : M ≤ bigL p G := fun y hy => hMbL hy
    have hmapM : M.map Q = Mb :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective U) Mb
    -- `A` normalizes `M`
    have hAN : A ≤ Subgroup.normalizer (M : Set G) := by
      intro a₀ ha₀
      have hstep : ∀ b₀ ∈ A, ∀ y ∈ M, b₀ * y * b₀⁻¹ ∈ M := by
        intro b₀ hb₀ y hy
        have hyL : Q y ∈ Lb := hMbL hy
        have hyH : (⟨Q y, hyL⟩ : ↥Lb) ∈ Ht := (mem_map_subtype_iff Ht ⟨Q y, hyL⟩).mp hy
        have hb : (⟨Q b₀, Subgroup.mem_map_of_mem Q hb₀⟩ : ↥Ab) • (⟨Q y, hyL⟩ : ↥Lb) ∈ Ht :=
          (NoncyclicAbelian.IsInvariant.invariant (A := ↥Ab) (G := ↥Lb) (H := Ht)
            ⟨Q b₀, Subgroup.mem_map_of_mem Q hb₀⟩ ⟨Q y, hyL⟩).mp hyH
        have hval := (mem_map_subtype_iff Ht _).mpr hb
        rw [hcoe] at hval
        change Q (b₀ * y * b₀⁻¹) ∈ Mb
        rw [map_mul, map_mul, map_inv]
        exact hval
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => hstep a₀ ha₀ y hy, fun hy => ?_⟩
      have h2 := hstep a₀⁻¹ (inv_mem ha₀) _ hy
      have h3 : a₀⁻¹ * (a₀ * y * a₀⁻¹) * a₀⁻¹⁻¹ = y := by group
      rwa [h3] at h2
    -- `M A` is a proper subgroup containing `P`
    have hPle : (P : Subgroup G) ≤ M ⊔ A := by
      rw [hstep4]; exact sup_le (hUM.trans le_sup_left) le_sup_right
    have hHne : M ⊔ A ≠ ⊤ := by
      intro htop
      have hLM : bigL p G ≤ M := by
        intro y hy
        exact sup_inf_bigL_le hAp hUM hML hAN ⟨htop ▸ Subgroup.mem_top y, hy⟩
      have hMeqL : M = bigL p G := le_antisymm hML hLM
      refine hne ?_
      have hMbeq : Mb = Lb := by
        rw [← hmapM, hMeqL, hbigL,
          Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective U)]
      refine eq_top_iff.mpr fun z _ => ?_
      have hz : (z : G ⧸ U) ∈ Mb := by rw [hMbeq]; exact z.2
      exact (mem_map_subtype_iff Ht z).mp hz
    have hSyl : ¬ p ∣ ((P : Subgroup G) ⊓ (M ⊔ A)).relIndex (M ⊔ A) := by
      rw [inf_eq_left.mpr hPle]
      exact fun h => P.not_dvd_index
        (h.trans (Subgroup.relIndex_dvd_index_of_le hPle))
    have h3 := step_three IH hsolv habel2 hcore P hP5 hA (hUM.trans le_sup_left) le_sup_right
      hHne hSyl
    -- translate back
    obtain ⟨a₀, ha₀, hQa₀⟩ := a.2
    have hxM : (x : G ⧸ U) ∈ Mb := (mem_map_subtype_iff Ht x).mpr hx
    obtain ⟨x₀, hx₀M, hQx₀⟩ : ∃ x₀ ∈ M, Q x₀ = (x : G ⧸ U) := by
      rw [← hmapM] at hxM
      obtain ⟨x₀, hx₀, hval⟩ := hxM
      exact ⟨x₀, hx₀, hval⟩
    have hcommU : a₀ * x₀ * a₀⁻¹ * x₀⁻¹ ∈ U :=
      h3 a₀ ha₀ x₀ ⟨(le_sup_left : M ≤ M ⊔ A) hx₀M, hML hx₀M⟩
    have hQcomm : Q (a₀ * x₀ * a₀⁻¹ * x₀⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hcommU
    refine Subtype.ext ?_
    rw [hcoe, ← hQa₀, ← hQx₀]
    have h4 : Q a₀ * Q x₀ * (Q a₀)⁻¹ * (Q x₀)⁻¹ = 1 := by
      simp only [← map_inv, ← map_mul]; exact hQcomm
    exact mul_inv_eq_one.mp h4
  have hcyc : IsCyclic ↥Ab :=
    @NoncyclicAbelian.isCyclic_of_forall_proper_invariant ↥Lb ↥Ab inferInstance inferInstance
      _instC inferInstance p inferInstance hAbp hcop _instA instF htriv
  -- a nontrivial cyclic elementary abelian group has order `p`
  rw [← card_map_mk'_eq_relIndex, ← hAb]
  obtain ⟨g, hg⟩ := hcyc
  have htop : Subgroup.zpowers g = ⊤ := eq_top_iff.mpr fun x _ => hg x
  have hcard : Nat.card ↥Ab = orderOf g := by
    rw [← Nat.card_zpowers g, htop, Subgroup.card_top]
  have hgp : g ^ p = 1 := Subtype.ext (by push_cast; exact hAbea.2 g.1 g.2)
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  have hne1 : orderOf g ≠ 1 := by
    intro h1
    refine hAbne ?_
    have : Nat.card ↥Ab = 1 := by rw [hcard, h1]
    exact Subgroup.eq_bot_of_card_eq _ this
  rw [hcard]
  exact ((Nat.dvd_prime hp).mp hdvd).resolve_left hne1

/-!
## Theorem 7.6

The minimal counterexample.  Step 2 produces `A ∈ E(P)` outside `U = O_p(G)`, Step 4 makes
`P = UA`, Step 5 makes `|Ā| = p`, and Step 8 derives a contradiction from the normal-`P` theorem.
-/

/-- **Isaacs, Theorem 7.6: Thompson's normal-`J` theorem.**

Let `P ∈ Syl_p(G)` with `G` finite, and assume (1) `G` is `p`-solvable; (2) `p ≠ 2`; (3) every
`2`-subgroup of `G` is abelian; (4) `O_p'(G) = 1`; (5) `P = C_G(Z(P))`.  Then `J(P) ⊴ G`. -/
theorem thompsonSubgroup_normal [Finite G] [Fact p.Prime] (hp2 : p ≠ 2)
    (hsolv : IsPiSeparable ({p} : Set ℕ) G)
    (habel2 : ∀ B : Subgroup G, IsPGroup 2 ↥B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hcore : piCore ({p}ᶜ : Set ℕ) G = ⊥) (P : Sylow p G)
    (hP5 : Subgroup.centralizer ((centerOf (P : Subgroup G) : Subgroup G) : Set G)
      = (P : Subgroup G)) :
    (thompsonSubgroup p (P : Subgroup G)).Normal := by
  have key : ∀ (n : ℕ) (X : Type u) [Group X] [Finite X], Nat.card X ≤ n →
      IsPiSeparable ({p} : Set ℕ) X →
      (∀ B : Subgroup X, IsPGroup 2 ↥B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      piCore ({p}ᶜ : Set ℕ) X = ⊥ →
      ∀ S : Sylow p X,
        Subgroup.centralizer ((centerOf (S : Subgroup X) : Subgroup X) : Set X)
          = (S : Subgroup X) →
        (thompsonSubgroup p (S : Subgroup X)).Normal := by
    intro n
    induction n with
    | zero =>
      intro X _ _ hcard
      exact absurd (Nat.card_pos (α := X)) (by omega)
    | succ n ih =>
      intro X _ _ hcard hsolvX habelX hcoreX S hS5
      by_contra hJ
      -- Step 2: some `A ∈ E(S)` escapes `O_p(X)`
      obtain ⟨A, hA, hAU⟩ : ∃ A ∈ maxElemAb p (S : Subgroup X),
          ¬ A ≤ piCore ({p} : Set ℕ) X := by
        by_contra hall
        simp only [not_exists, not_and, not_not] at hall
        exact hJ (thompsonSubgroup_normal_of_forall_le_piCore S hall)
      -- the induction hypothesis, in the shape Steps 3–5 use
      have IH : ∀ (Y : Type u) [Group Y] [Finite Y], Nat.card Y < Nat.card X →
          IsPiSeparable ({p} : Set ℕ) Y →
          (∀ B : Subgroup Y, IsPGroup 2 ↥B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
          piCore ({p}ᶜ : Set ℕ) Y = ⊥ →
          ∀ T : Sylow p Y,
            Subgroup.centralizer ((centerOf (T : Subgroup Y) : Subgroup Y) : Set Y)
              = (T : Subgroup Y) →
            (thompsonSubgroup p (T : Subgroup Y)).Normal :=
        fun Y _ _ hlt => ih Y (by omega)
      obtain ⟨-, hstep4⟩ := step_four IH hsolvX habelX hcoreX S hS5 hA hAU
      exact step_eight hp2 hsolvX habelX hcoreX S hS5 hA hAU hstep4
        (step_five IH hsolvX habelX hcoreX S hS5 hA hAU hstep4)
  exact key (Nat.card G) G le_rfl hsolv habel2 hcore P hP5

/-- **Isaacs, Theorem 7.6**, stated with hypothesis (3) in his own words: *a Sylow `2`-subgroup
of `G` is abelian*.  By `forall_two_commute_iff_sylow` this is the same hypothesis. -/
theorem thompsonSubgroup_normal_of_sylow_two_abelian [Finite G] [Fact p.Prime] (hp2 : p ≠ 2)
    (hsolv : IsPiSeparable ({p} : Set ℕ) G) (S : Sylow 2 G)
    (habel : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y = y * x)
    (hcore : piCore ({p}ᶜ : Set ℕ) G = ⊥) (P : Sylow p G)
    (hP5 : Subgroup.centralizer ((centerOf (P : Subgroup G) : Subgroup G) : Set G)
      = (P : Subgroup G)) :
    (thompsonSubgroup p (P : Subgroup G)).Normal :=
  thompsonSubgroup_normal hp2 hsolv ((forall_two_commute_iff_sylow S).mpr habel) hcore P hP5

end PiGroups
