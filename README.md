# PreCFSG — Isaacs' *Finite Group Theory* towards Burnside's `p^a q^b` theorem

A Lean 4 / Mathlib formalization of the chain of results in I. M. Isaacs, *Finite Group Theory*
(AMS, 2008) that leads to Burnside's solvability theorem: π-separability, coprime action,
Thompson's `P × Q` lemma, and `p`-local subgroups.

Everything is formalized in full generality — no finite-group case splits, no `sorry`, and the
main results depend only on `propext`, `Classical.choice` and `Quot.sound`.

Built with **Lean v4.33.1** and **Mathlib v4.33.1** (the same 4.33 series as the
[Qiuzhen CFSG](https://github.com/Qiuzhen-CFSG/CFSG) development, which pins v4.33.0).

```
lake exe cache get   # fetch Mathlib's prebuilt oleans
lake build
```

## What is proved

| Module | Isaacs | Contents |
| --- | --- | --- |
| `PiSeparableGroups` | 3.15–3.21 | π-groups, π-separability, the π-core `O_π(G)`, closure under subgroups/quotients/extensions, solvable ⇒ π-separable, and Hall–Higman 1.2.3 (`centralizer_piCore_le_piCore`) |
| `GlaubermanLemma` | 3.24 | Glauberman's lemma: a coprime action on a transitive `G`-set fixes a point, and the transitive-action corollary |
| `InvariantCosets` | 3.27 | `A`-invariant cosets of an `A`-invariant subgroup contain fixed points |
| `CoprimeQuotients` | 3.28–3.30 | fixed points of a coprime action pass to quotients; the Frattini and faithfulness corollaries |
| `CommutatorAction` | 4.28–4.29 | `⁅G, A⁆` for an action, `G = C_G(A)⁅G, A⁆`, and `⁅G, A, A⁆ = ⁅G, A⁆` |
| `PGroupAction` | 4.32 | a `p`-group acting on a `p`-group: `⁅G, P⁆ < G` and `C_G(P) > 1` |
| `ThompsonPxQ` | 4.31 | **Thompson's `P × Q` lemma** |
| `PLocalSubgroups` | 2.17, 4.33 | `p`-local subgroups; `N_{G/N}(PN/N) = N_G(P)N/N`; and `O_p'(H) ≤ O_p'(G)` for `p`-local `H` |
| `BurnsidePQTheorem` | 7.8 | the minimal-counterexample setting for Burnside's theorem and the reductions of Isaacs' opening paragraph |

Two results are proved in more generality than the book states them:

* **Thompson's `P × Q` lemma** (`CoprimeAction.thompson_pq`) is stated for any pair of commuting
  subgroups `P, Q` of any group acting on a `p`-group, rather than for an internal direct product
  `A = P × Q`. Normality of `P` — which is what makes `⁅G, P⁆` invariant — comes for free by
  restricting the action to `Q ⊔ P`.
* **Isaacs 4.33** in the case `O_p'(G) = 1` (`PiGroups.piCore_compl_eq_bot_of_piCore_compl_eq_bot`)
  needs neither `P ≠ 1` nor `H = N_G(P)`: it suffices that `P` is a `p`-subgroup normal in `H`
  with `C_{O_p(G)}(P) ≤ H`.

## The standing hypothesis

Mathlib has the existence half of Schur–Zassenhaus but not the conjugacy half, so everything
downstream of Glauberman's lemma carries it as an explicit hypothesis rather than an axiom:

```lean
def SchurZassenhausConjugacy : Prop :=
  ∀ (Γ : Type u) [Group Γ] [Finite Γ] (N H K : Subgroup Γ) [N.Normal],
    Nat.Coprime (Nat.card N) N.index → (Group.IsSolvable N ∨ Group.IsSolvable (Γ ⧸ N)) →
      N.IsComplement' H → N.IsComplement' K → ∃ g : Γ, K = H.map (MulAut.conj g).toMonoidHom
```

It is discharged by the Qiuzhen CFSG development's
`huppert_I_18_2_complements_conjugate_of_solvable_normal_or_quotient`; the instantiation is
recorded in a comment at the end of `PreCFSG/GlaubermanLemma.lean`.

## What is not done yet

Burnside's theorem itself. `Burnside.isSolvable_of_forall_not_isMinCounterexample` reduces it to
refuting `Burnside.IsMinCounterexample`, and the opening reductions (the counterexample is simple;
maximal subgroups are solvable, nontrivial, and self-normalizing on their nontrivial normal
subgroups; `O_p(M) > 1` or `O_q(M) > 1`) are proved. Isaacs' nine steps are not.

Step 1 needs, besides Theorem 4.33 (available), the decomposition of a nilpotent `{p, q}`-group as
`K = O_p(K) × O_q(K)` with both factors characteristic, plus an induction over subgroups maximal
among counterexamples.

## Notes on the formalization

* `Nat.card`, not `Fintype.card`, throughout; finiteness is `[Finite G]`.
* Inductions that must vary the ambient group are phrased as
  `∀ (n : ℕ) (G : Type u) [Group G] …, Nat.card G ≤ n → …`, since the ambient group changes when
  passing to a quotient.
* π-separability is an inductive predicate over `Subgroup G` (mirroring `Subgroup.IsSubnormal`)
  rather than a literal chain; `PiGroups.isPiSeparable_iff_hasPiSeries` proves the two agree.
* The commutator of an action is `CoprimeAction.commutatorSubgroup`, whose naming and conventions
  deliberately match the Qiuzhen CFSG development's, to keep the two comparable.
