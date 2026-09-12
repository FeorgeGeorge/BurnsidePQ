# Isaacs — *Finite Group Theory*, towards Burnside's `p^a q^b` theorem

A Lean 4 / Mathlib formalization of the chain of results in I. M. Isaacs, *Finite Group Theory*
(AMS, 2008) that leads to Burnside's solvability theorem — π-separability, coprime action,
Thompson's `P × Q` lemma, `p`-local subgroups, normal `p`-complements and the Thompson subgroup —
ending with the theorem itself:

```lean
theorem Burnside.isSolvable_of_card_eq_pow_mul_pow {p q : ℕ} {G : Type u} [Group G] [Finite G]
    (hp : p.Prime) (hq : q.Prime) {a b : ℕ} (hcard : Nat.card G = p ^ a * q ^ b) :
    Group.IsSolvable G
```

Everything is formalized in full generality — no finite-group case splits, no `sorry`, and the
main results, Burnside's theorem included, depend only on `propext`, `Classical.choice` and
`Quot.sound`.

Built with **Lean v4.33.1** and **Mathlib v4.33.1** (the same 4.33 series as the
[Qiuzhen CFSG](https://github.com/Qiuzhen-CFSG/CFSG) development, which pins v4.33.0).

```
lake exe cache get   # fetch Mathlib's prebuilt oleans
lake build
```

## What is proved

In Isaacs’ numbering, which is not the dependency order: Theorem 7.1 rests on 7.5–7.7, and 2.13 on 2.1–2.12.

| Module | Isaacs | Contents |
| --- | --- | --- |
| `SchurZassenhausConjugacy` | — | Huppert I.18.2: complements of a normal Hall subgroup are conjugate when the subgroup or the quotient is solvable (ported from CFSG), which discharges the hypothesis carried throughout |
| `FittingSubgroup` | 2.1, 2.2 | the Fitting subgroup `F(G)` (absent from Mathlib), Fitting's theorem that it is nilpotent, and `H ≤ F(G) ↔ H` nilpotent and subnormal |
| `SubnormalJoin` | 2.5–2.7, 2.9 | minimal normal subgroups and the socle; Wielandt's theorem that a join of subnormal subgroups is subnormal; Wielandt's zipper lemma |
| `BaerTheorem` | 2.12 | Baer's theorem: `H ≤ F(G)` iff `⟨H, H^x⟩` is nilpotent for all `x` |
| `InvolutionInverts` | 2.13 | an involution outside every normal `2`-subgroup inverts an element of odd prime order; states `Burnside.InvolutionInvertsElement`, the hypothesis of Step 7, and discharges it |
| `PLocalSubgroups` | 2.17, 4.33 | `p`-local subgroups; `N_{G/N}(PN/N) = N_G(P)N/N`; and `O_p'(H) ≤ O_p'(G)` for `p`-local `H` |
| `PiSeparableGroups` | 3.15–3.21 | π-groups, π-separability, the π-core `O_π(G)`, closure under subgroups/quotients/extensions, solvable ⇒ π-separable, and Hall–Higman 1.2.3 (`centralizer_piCore_le_piCore`) |
| `GlaubermanLemma` | 3.24 | Glauberman's lemma: a coprime action on a transitive `G`-set fixes a point, and the transitive-action corollary |
| `InvariantCosets` | 3.27 | `A`-invariant cosets of an `A`-invariant subgroup contain fixed points |
| `CoprimeQuotients` | 3.28–3.30 | fixed points of a coprime action pass to quotients; the Frattini and faithfulness corollaries |
| `CommutatorAction` | 4.28–4.29, 4.34(a), 4.35 | `⁅G, A⁆` for an action, `G = C_G(A)⁅G, A⁆`, `⁅G, A, A⁆ = ⁅G, A⁆`, `C_G(A) ⊓ ⁅G, A⁆ = 1` for abelian `G`, and that a coprime operator group fixing every element of order `p` of an abelian `p`-group acts trivially |
| `ThompsonPxQ` | 4.31 | **Thompson's `P × Q` lemma** |
| `PGroupAction` | 4.32 | a `p`-group acting on a `p`-group: `⁅G, P⁆ < G` and `C_G(P) > 1` |
| `Frobenius` | 5.25–5.28 | **Frobenius’ normal `p`-complement theorem** (`PiGroups.frobenius_tfae`): `G` has a normal `p`-complement iff every `N_G(X)` does (`X` a nonidentity `p`-subgroup) iff every `N_G(X)/C_G(X)` is a `p`-group; via control of fusion, the transfer to `P ⧸ P*`, and Lemma 5.28 |
| `NoncyclicAbelianAction` | 6.20–6.21 | a noncyclic abelian `p`-group acting coprimely satisfies `G = ⟨C_G(a) : 1 ≠ a⟩` (ported from CFSG); and Lemma 6.20, that an abelian `p`-group acting faithfully and coprimely, trivially on every proper invariant subgroup, is cyclic |
| `ThompsonNormalPComplement` | 7.1, 7.7 | **Thompson’s normal `p`-complement theorem** (`PiGroups.hasNormalPComplement_of_thompson`): for `P ∈ Syl_p(G)` with `p ≠ 2`, if `C_G(Z(P))` and `N_G(J(P))` have normal `p`-complements then so does `G`; all seven steps of Isaacs’ minimal-counterexample argument, together with Lemma 7.7 (`N_Ḡ(P̄) = N_G(P)‾` and `C_Ḡ(P̄) = C_G(P)‾` modulo a normal `p′`-subgroup), proved by Isaacs’ Frattini argument so as to avoid the Schur–Zassenhaus hypothesis |
| `ThompsonSubgroup` | 7.2 | the subgroup constructions Chapter 7 runs on, ambiently: `Z(P)` (`PiGroups.centerOf`), elementary abelian subgroups, `Ω₁(A)` (`PiGroups.omegaOne`, with its elementary abelianness, normality and nontriviality), `E(P)` and the Thompson subgroup `J(P)`; Lemma 7.2, that `J(P) = J(Q)` for `J(P) ≤ Q ≤ P`, and `J(Q)` characteristic in `Q`; and the transfer of that to normality and normalizer bounds, which 7.1, 7.6 and 7.8 all use |
| `GL2Lemma` | 7.3 | a `p`-subgroup of `GL(2, p)` normalizing a `p′`-subgroup with abelian Sylow `2`-subgroups centralizes it |
| `ElementaryAbelianGL2` | 7.3 | `Aut(E) ↪ GL(2, p)` for `E` elementary abelian of order `p ^ 2`, and Lemma 7.3 restated for a group acting faithfully on such an `E` |
| `SL2Involution` | 7.4 | over any domain with `2 ≠ 0`, `-I` is the unique involution of `SL(2, R)`; and `|SL(2, q)| = q (q - 1) (q + 1)` |
| `NormalSylowTheorem` | 7.5 | **Isaacs’ normal-`P` theorem** (`PiGroups.normal_sylow_of_faithful`): for `G` `p`-solvable with `p ≠ 2` and abelian Sylow `2`-subgroups acting faithfully on an elementary abelian `p`-group `V` with `|V : C_V(P)| ≤ p`, the Sylow `p`-subgroup `P` is normal |
| `NormalJTheorem` | 7.6 | **Thompson’s normal-`J` theorem** (`PiGroups.thompsonSubgroup_normal`): for `P ∈ Syl_p(G)` with `G` `p`-solvable, `p ≠ 2`, the `2`-subgroups of `G` abelian, `O_p′(G) = 1` and `P = C_G(Z(P))`, `J(P) ⊴ G`; all eight steps of Isaacs’ minimal-counterexample argument, and the theorem also stated with hypothesis (3) in Isaacs’ own form, *a Sylow `2`-subgroup is abelian* |
| `NormalPComplement` | 7.7 | normal `p`-complements and their inheritance by subgroups and quotients; `N` and `C` of a `p`-subgroup modulo a normal `p′`-subgroup |
| `BurnsidePQTheorem` | 7.8 | **Burnside's `p ^ a q ^ b` theorem** (`Burnside.isSolvable_of_card_eq_pow_mul_pow`): the minimal-counterexample setting, the reductions of Isaacs' opening paragraph, the `p`-type/`q`-type dichotomy for maximal subgroups, and all nine steps — ending with Step 8, that a Sylow `p`-subgroup `S` of a `p`-type maximal subgroup `M` satisfies `J(S) ⊴ M` and is Sylow in `G`, and Step 9, the contradiction from a pair of Sylow `p`-subgroups with `J(S) ≠ J(T)` and `|S ∩ T|` maximal |

Two results are proved in more generality than the book states them:

* **Thompson's `P × Q` lemma** (`CoprimeAction.thompson_pq`) is stated for any pair of commuting
  subgroups `P, Q` of any group acting on a `p`-group, rather than for an internal direct product
  `A = P × Q`. Normality of `P` — which is what makes `⁅G, P⁆` invariant — comes for free by
  restricting the action to `Q ⊔ P`.
* **Isaacs 4.33** in the case `O_p'(G) = 1` (`PiGroups.piCore_compl_eq_bot_of_piCore_compl_eq_bot`)
  needs neither `P ≠ 1` nor `H = N_G(P)`: it suffices that `P` is a `p`-subgroup normal in `H`
  with `C_{O_p(G)}(P) ≤ H`.

## Complement conjugacy

Mathlib has the existence half of Schur–Zassenhaus but not the conjugacy half, so everything
downstream of Glauberman's lemma carries it as an explicit hypothesis:

```lean
def SchurZassenhausConjugacy : Prop :=
  ∀ (Γ : Type u) [Group Γ] [Finite Γ] (N H K : Subgroup Γ) [N.Normal],
    Nat.Coprime (Nat.card N) N.index → (Group.IsSolvable N ∨ Group.IsSolvable (Γ ⧸ N)) →
      N.IsComplement' H → N.IsComplement' K → ∃ g : Γ, K = H.map (MulAut.conj g).toMonoidHom
```

This is not an axiom: `Isaacs/SchurZassenhausConjugacy.lean` proves it as
`CoprimeAction.schurZassenhausConjugacy`, from a port of the Qiuzhen CFSG development's Huppert
I.18.2. It is kept on the statements that need it so that each one records exactly where
complement conjugacy is used, and instantiated when they are applied; Burnside's theorem
therefore depends on no unproved statement.

Step 7 of Burnside likewise carries Isaacs' Theorem 2.13 as the hypothesis
`Burnside.InvolutionInvertsElement`, and that too is a theorem here:
`PiGroups.involutionInvertsElement`, reached along Isaacs' own route — the Fitting subgroup and
Theorem 2.2, Wielandt's join theorem 2.5 and zipper lemma 2.9, and Baer's Theorem 2.12. None of
those are in Mathlib, which has `Subgroup.IsSubnormal` with the intersection of subnormal
subgroups but not the join, and no Fitting subgroup for groups.

Two further hypotheses of Isaacs' proofs were avoided rather than carried. Lemma 7.7 is proved by
Isaacs' own Frattini argument instead of the conjugacy-of-complements route, which keeps it — and
with it Thompson's normal `p`-complement theorem — free of `SchurZassenhausConjugacy`; and
Theorem 7.5 is proved for elementary abelian `V` only, the case its own induction and Theorem 7.6
ever need, which lets it appeal to Corollary 4.34(a) rather than Theorem 4.29.

## Relation to the Qiuzhen CFSG project

[Qiuzhen CFSG](https://github.com/Qiuzhen-CFSG/CFSG) (Apache 2.0) is a Lean 4 development aimed at
the classification of finite simple groups. It is not a dependency of this project: nothing here
is imported from it. Two of its results are **ported** — reproved in this repository, in this
development's own idiom — and each of the two files records its provenance declaration by
declaration in its module docstring, along with the source file it came from and the license of
the source.

**Huppert I.18.2** (`Isaacs/SchurZassenhausConjugacy.lean`): complements of a normal Hall subgroup
are conjugate when the subgroup or the quotient is solvable. This is the conjugacy half of
Schur–Zassenhaus, which Mathlib does not have, and the whole development downstream of
Glauberman's lemma needs it. Ported from CFSG's `FeitThompson/GroupAction/Quotient.lean`,
`FeitThompson/HallSubgroups/Conjugacy.lean` and
`BenderSuzuki/External/Huppert/I/theorem_18_3.lean` (its `huppert_I_18_2_*`). It is ported rather
than imported because CFSG's file proves Huppert I.18.3 as well — the unrestricted statement,
which needs the odd order theorem — so it imports `FeitThompson.FinalTheorem`, giving it a
closure of 537 modules and 619k lines. Only 18.2 is wanted here, and 18.2 itself needs no such
input. Two deviations: the conjugation action of `H` on a normal `N` is built from
`MulAut.conjNormal` instead of CFSG's `Subgroup.conjMulDistribMulActionOfLeNormalizer`, and where
CFSG's solvable-operator induction takes a minimal normal subgroup and calls its chief-factor
development to see that it is elementary abelian, this port supplies a nontrivial normal
`p`-subgroup directly from the derived series and a Sylow subgroup of its last nontrivial term.

**Isaacs 6.21** (`Isaacs/NoncyclicAbelianAction.lean`): a noncyclic abelian `p`-group acting
coprimely on `G` satisfies `G = ⟨C_G(a) : 1 ≠ a⟩`, needed for Step 3 of Burnside's theorem. This
is CFSG's `proposition_1_16_b`, ported from `FeitThompson/GroupAction/NoncyclicAbelianPGroup.lean`
together with the Frattini-quotient lemmas of `FeitThompson/Frattini/Core.lean`: the simple-module
step, Maschke over `ZMod q`, the elementary abelian case, the `q`-group case via the Frattini
quotient, and the general case via an invariant Sylow subgroup for each prime. Two deviations:
for the fixed points of a quotient this port calls Isaacs 3.28 from this development
(`CoprimeAction.fixedPoints_quotient_eq_image`) rather than CFSG's own coprime-action theory, and
CFSG's `IsElementaryAbelian` class is replaced by the plain hypotheses of commutativity and
exponent dividing `q`.

Beyond those two, the contact is a matter of convention and of knowing what not to duplicate.
`CoprimeAction.commutatorSubgroup` deliberately matches CFSG's naming and conventions so the two
can be compared. Both developments sit on the 4.33 series — CFSG pins Lean v4.33.0, this pins
v4.33.1. And in three places the two overlap without either being used by the other:

* CFSG defines the same Fitting subgroup (`FeitThompson/Fitting/Core.lean`) and proves it
  nilpotent and equal to the join of the `p`-cores, and it has Isaacs 2.1 twice over; what it does
  not have is Isaacs 2.2, which is what this development needs — nothing there connects
  `Subgroup.IsSubnormal` to the Fitting subgroup;
* CFSG also defines a `thompsonSubgroup`, but for the *abelian* subgroups of largest order —
  Gorenstein's `J`, a different subgroup in general from Isaacs' `J`, which is generated by the
  *elementary* abelian subgroups of largest order and is the one used here;
* CFSG proves the Baer–Suzuki theorem, whose contrapositive at `p = 2` gives a shorter route to
  Isaacs 2.13 than the one taken here through Baer's Theorem 2.12 and the Fitting subgroup.

## Notes on the formalization

* `Nat.card`, not `Fintype.card`, throughout; finiteness is `[Finite G]`.
* Inductions that must vary the ambient group are phrased as
  `∀ (n : ℕ) (G : Type u) [Group G] …, Nat.card G ≤ n → …`, since the ambient group changes when
  passing to a quotient.
* π-separability is an inductive predicate over `Subgroup G` (mirroring `Subgroup.IsSubnormal`)
  rather than a literal chain; `PiGroups.isPiSeparable_iff_hasPiSeries` proves the two agree.

## Status

**This is not a proposal for Mathlib.** Nothing here has been submitted to Mathlib or prepared for
submission. The definitions, names, generality and API choices are this project's own and were
made to serve Isaacs' text and the proof of Burnside's theorem; several of them would have to be
reconsidered, and much of the material restructured, before any of it could be proposed upstream.

**It is a work in progress.** The repository will keep changing. Files have already been split,
merged and renamed more than once, and further reorganization, restatement of definitions and
rewriting of proofs should be expected. Nothing here should be treated as a stable API.

**It has not been independently reviewed.** Everything compiles against Mathlib v4.33.1 with no
`sorry` and no added axioms, and the main results depend only on `propext`, `Classical.choice` and
`Quot.sound` — but that only rules out gaps and cheating in the *proofs*. It says nothing about
whether each theorem *states* what its name and docstring claim: a statement can be accidentally
weaker than intended, or vacuous under its hypotheses, and still compile. Read the statements and
definitions and check them against the book yourself before relying on anything here.
