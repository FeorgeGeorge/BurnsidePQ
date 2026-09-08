module

public import PreCFSG.InvariantCosets
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Nilpotent

/-!
# Coprime action on quotients

Three corollaries of Isaacs' Theorem 3.27 (`PreCFSG/InvariantCosets.lean`):

* `CoprimeAction.fixedPoints_quotient_eq_image` (Isaacs 3.28): for an `A`-invariant normal
  subgroup `N` with `(|A|,|N|) = 1` and one of `A`, `N` solvable, `C_{G/N}(A) = C_G(A)N/N`;
* `CoprimeAction.smul_eq_self_of_smul_mk_eq` (Isaacs 3.29): a coprime action that is trivial on
  the Frattini factor `G/Φ(G)` is trivial;
* `CoprimeAction.faithfulSMul_quotient_frattini` (Isaacs 3.30): a faithful coprime action stays
  faithful on `G/Φ(G)`.

The induced action on `G ⧸ N` is taken as a hypothesis (`[MulAction A (G ⧸ N)]` together with the
compatibility `hmk`) rather than built into the statements, so that any construction of it can be
used; `CoprimeAction.quotientAction` is the canonical one.

## Deviation from Isaacs

Isaacs proves 3.29 by reducing to a cyclic — hence solvable — group `A`, because he wants the
solvability hypothesis of 3.28 to be met.  We instead observe that `Φ(G)` is nilpotent
(`frattini_nilpotent`), hence solvable, so 3.28 applies to `N = Φ(G)` for *any* `A` and no
reduction is needed.  The cyclic reduction reappears in 3.30, where it is the subgroup of `A`
acting trivially on `G ⧸ Φ(G)` that must be shown trivial.
-/

@[expose] public section

namespace CoprimeAction

open scoped Pointwise

universe u

variable {G A : Type u} [Group G] [Group A] [MulDistribMulAction A G]

/-!
## The induced action on a quotient
-/

/-- A characteristic subgroup is invariant under every action by automorphisms. -/
theorem smul_mem_of_characteristic (N : Subgroup G) [N.Characteristic] (a : A) {n : G}
    (hn : n ∈ N) : a • n ∈ N := by
  have h := Subgroup.characteristic_iff_map_eq.mp ‹N.Characteristic›
    (MulDistribMulAction.toMulAut A G a)
  rw [← h]
  exact ⟨n, hn, rfl⟩

/-- The action induced on `G ⧸ N` by an action of `A` leaving `N` invariant. -/
@[reducible]
def quotientAction {N : Subgroup G} [N.Normal] (hN : ∀ (a : A), ∀ n ∈ N, a • n ∈ N) :
    MulAction A (G ⧸ N) where
  smul a := QuotientGroup.map N N (MulDistribMulAction.toMulAut A G a).toMonoidHom (hN a)
  one_smul x := by
    induction x using QuotientGroup.induction_on with
    | _ y => exact congrArg (QuotientGroup.mk (s := N)) (one_smul A y)
  mul_smul a b x := by
    induction x using QuotientGroup.induction_on with
    | _ y => exact congrArg (QuotientGroup.mk (s := N)) (mul_smul a b y)

theorem quotientAction_mk {N : Subgroup G} [N.Normal] (hN : ∀ (a : A), ∀ n ∈ N, a • n ∈ N)
    (a : A) (x : G) :
    letI := quotientAction hN
    a • (x : G ⧸ N) = ((a • x : G) : G ⧸ N) := rfl

/-- A coset is `A`-invariant exactly when it is a fixed point of the induced action. -/
theorem smul_leftCoset_iff {N : Subgroup G} [N.Normal] (hNinv : ∀ (a : A), ∀ n ∈ N, a • n ∈ N)
    [MulAction A (G ⧸ N)] (hmk : ∀ (a : A) (x : G), a • (x : G ⧸ N) = ((a • x : G) : G ⧸ N))
    (y : G) (a : A) :
    a • (y • (N : Set G)) = y • (N : Set G) ↔ a • (y : G ⧸ N) = (y : G ⧸ N) := by
  rw [smul_smul_set, smul_coe_eq hNinv, hmk]
  constructor
  · intro h
    refine QuotientGroup.eq.mpr ?_
    have hmem : y ∈ (a • y) • (N : Set G) := by
      rw [h]
      exact mem_leftCoset_iff'.mpr (by simp)
    exact mem_leftCoset_iff'.mp hmem
  · intro h
    refine leftCoset_eq_of_mem ?_
    have hy : (a • y)⁻¹ * y ∈ N := QuotientGroup.eq.mp h
    exact mem_leftCoset_iff'.mpr (by simpa using N.inv_mem hy)

variable [Finite G] [Finite A]

/-!
## Isaacs 3.28
-/

/-- **Isaacs, Corollary 3.28.**  For a coprime action leaving the normal subgroup `N` invariant,
the fixed points on `G ⧸ N` are exactly the images of the fixed points on `G`: in Isaacs'
notation, `C_{G/N}(A) = C_G(A)N/N`. -/
theorem fixedPoints_quotient_eq_image (hSZ : SchurZassenhausConjugacy.{u}) {N : Subgroup G}
    [N.Normal] (hNinv : ∀ (a : A), ∀ n ∈ N, a • n ∈ N)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card N)) (hsolv : Group.IsSolvable A ∨ Group.IsSolvable N)
    [MulAction A (G ⧸ N)] (hmk : ∀ (a : A) (x : G), a • (x : G ⧸ N) = ((a • x : G) : G ⧸ N)) :
    {x : G ⧸ N | ∀ a : A, a • x = x}
      = (fun c : G ↦ (c : G ⧸ N)) '' {c : G | ∀ a : A, a • c = c} := by
  ext x
  induction x using QuotientGroup.induction_on with
  | _ y =>
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hy
      have hcoset : ∀ a : A, a • (y • (N : Set G)) = y • (N : Set G) := fun a ↦
        (smul_leftCoset_iff hNinv hmk y a).mpr (hy a)
      obtain ⟨c, hcy, hc⟩ := exists_fixed_mem_of_smul_eq hSZ hNinv hcop hsolv hcoset
      refine ⟨c, hc, QuotientGroup.eq.mpr ?_⟩
      simpa using N.inv_mem (mem_leftCoset_iff'.mp hcy)
    · rintro ⟨c, hc, hcy⟩ a
      rw [← hcy, hmk, hc a]

/-- If the induced action on `G ⧸ N` is trivial, then `C_G(A) N = G`.  This is the shape in which
Isaacs uses 3.28, both for the Frattini factor (3.29) and for `G ⧸ ⁅G, A⁆` (4.28). -/
theorem fixedPoints_sup_eq_top (hSZ : SchurZassenhausConjugacy.{u}) {N : Subgroup G} [N.Normal]
    (hNinv : ∀ (a : A), ∀ n ∈ N, a • n ∈ N) (hcop : Nat.Coprime (Nat.card A) (Nat.card N))
    (hsolv : Group.IsSolvable A ∨ Group.IsSolvable N) [MulAction A (G ⧸ N)]
    (hmk : ∀ (a : A) (x : G), a • (x : G ⧸ N) = ((a • x : G) : G ⧸ N))
    (htriv : ∀ (a : A) (x : G ⧸ N), a • x = x) :
    FixedPoints.subgroup A G ⊔ N = ⊤ := by
  have h328 := fixedPoints_quotient_eq_image hSZ hNinv hcop hsolv hmk
  have hmaptop : Subgroup.map (QuotientGroup.mk' N) (FixedPoints.subgroup A G) = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    have hx : x ∈ {x : G ⧸ N | ∀ a : A, a • x = x} := fun a ↦ htriv a x
    rw [h328] at hx
    obtain ⟨c, hc, hcx⟩ := hx
    exact ⟨c, hc, hcx⟩
  have hcomap := congrArg (Subgroup.comap (QuotientGroup.mk' N)) hmaptop
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at hcomap

/-!
## Isaacs 3.29 and 3.30
-/

/-- **Isaacs, Corollary 3.29.**  A coprime action that induces the trivial action on the Frattini
factor group `G ⧸ Φ(G)` is itself trivial. -/
theorem smul_eq_self_of_smul_frattini_eq (hSZ : SchurZassenhausConjugacy.{u})
    (hcop : Nat.Coprime (Nat.card A) (Nat.card G)) [MulAction A (G ⧸ frattini G)]
    (hmk : ∀ (a : A) (x : G),
      a • (x : G ⧸ frattini G) = ((a • x : G) : G ⧸ frattini G))
    (htriv : ∀ (a : A) (x : G ⧸ frattini G), a • x = x) (a : A) (g : G) : a • g = g := by
  have : Group.IsNilpotent (frattini G) := frattini_nilpotent
  have hNinv : ∀ (a : A), ∀ n ∈ frattini G, a • n ∈ frattini G := fun a _ hn ↦
    smul_mem_of_characteristic _ a hn
  have hcop' : Nat.Coprime (Nat.card A) (Nat.card (frattini G)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_subgroup_dvd_card _) hcop
  have hsup : FixedPoints.subgroup A G ⊔ frattini G = ⊤ :=
    fixedPoints_sup_eq_top hSZ hNinv hcop' (Or.inr IsNilpotent.to_isSolvable) hmk htriv
  have htop : FixedPoints.subgroup A G = ⊤ := frattini_nongenerating hsup
  have : g ∈ FixedPoints.subgroup A G := htop ▸ Subgroup.mem_top g
  exact this a

/-- **Isaacs, Corollary 3.29**, elementwise: a single coprime automorphism acting trivially on
`G ⧸ Φ(G)` acts trivially on `G`.  Applying 3.29 to the subgroup of `A` acting trivially on the
Frattini factor. -/
theorem smul_eq_self_of_smul_mk_eq (hSZ : SchurZassenhausConjugacy.{u})
    (hcop : Nat.Coprime (Nat.card A) (Nat.card G)) [MulAction A (G ⧸ frattini G)]
    (hmk : ∀ (a : A) (x : G),
      a • (x : G ⧸ frattini G) = ((a • x : G) : G ⧸ frattini G))
    {a : A} (ha : ∀ x : G ⧸ frattini G, a • x = x) (g : G) : a • g = g := by
  -- the elements of `A` acting trivially on `G ⧸ Φ(G)` form a subgroup
  let K : Subgroup A :=
    { carrier := {b : A | ∀ x : G ⧸ frattini G, b • x = x}
      one_mem' := fun x ↦ one_smul A x
      mul_mem' := fun {b c} hb hc x ↦ by rw [mul_smul, hc x, hb x]
      inv_mem' := fun {b} hb x ↦ by
        conv_lhs => rw [← hb x]
        rw [inv_smul_smul] }
  let : MulDistribMulAction K G := MulDistribMulAction.compHom G K.subtype
  let : MulAction K (G ⧸ frattini G) := MulAction.compHom _ K.subtype
  have hcopK : Nat.Coprime (Nat.card K) (Nat.card G) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _) hcop
  have hmkK : ∀ (b : K) (x : G),
      b • (x : G ⧸ frattini G) = ((b • x : G) : G ⧸ frattini G) := fun b x ↦ hmk (b : A) x
  have htrivK : ∀ (b : K) (x : G ⧸ frattini G), b • x = x := fun b x ↦ b.2 x
  exact smul_eq_self_of_smul_frattini_eq hSZ hcopK hmkK htrivK ⟨a, ha⟩ g

/-- **Isaacs, Corollary 3.30.**  A faithful coprime action on `G` induces a faithful action on the
Frattini factor group `G ⧸ Φ(G)`. -/
theorem faithfulSMul_quotient_frattini (hSZ : SchurZassenhausConjugacy.{u})
    (hcop : Nat.Coprime (Nat.card A) (Nat.card G)) [MulAction A (G ⧸ frattini G)]
    (hmk : ∀ (a : A) (x : G),
      a • (x : G ⧸ frattini G) = ((a • x : G) : G ⧸ frattini G))
    [FaithfulSMul A G] : FaithfulSMul A (G ⧸ frattini G) := by
  refine ⟨fun {a₁ a₂} h ↦ ?_⟩
  have hb : ∀ x : G ⧸ frattini G, (a₂⁻¹ * a₁) • x = x := by
    intro x
    rw [mul_smul, h x, inv_smul_smul]
  have hg : ∀ g : G, (a₂⁻¹ * a₁) • g = g :=
    fun g ↦ smul_eq_self_of_smul_mk_eq hSZ hcop hmk hb g
  have h1 : a₂⁻¹ * a₁ = 1 :=
    FaithfulSMul.eq_of_smul_eq_smul (α := G) fun g ↦ by rw [hg g, one_smul]
  rw [← mul_one a₂, ← h1, mul_inv_cancel_left]

end CoprimeAction
