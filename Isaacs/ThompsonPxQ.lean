module

public import Isaacs.PGroupAction

/-!
# Thompson's `P × Q` lemma

Isaacs, *Finite Group Theory*, Theorem 4.31: let `A` act by automorphisms on a `p`-group `G`, and
let `P, Q ≤ A` with `P` a `p`-group, `Q` a `p'`-group, and `P`, `Q` centralizing each other.  If
`Q` fixes every element of `G` fixed by `P`, then `Q` acts trivially on `G`.

Isaacs states this for `A = P × Q` an internal direct product.  All that is really needed is that
`P` and `Q` commute elementwise: the induction runs inside `Q ⊔ P`, where `P` is automatically
normal — being normalized by itself and centralized by `Q` — and normality is what makes `⁅G, P⁆`
invariant.  So `P` and `Q` may be any pair of commuting subgroups of any group acting on `G`,
which is more general than the book's statement.

The proof is Isaacs': induct on `|G|`.  `⁅G, P⁆ < G` by 4.32 and it is `A`-invariant, so the
inductive hypothesis gives `⁅G, P, Q⁆ = 1`.  Since `P` and `Q` commute, `⁅P, Q, G⁆ = 1`, so the
three-subgroups lemma yields `⁅Q, G, P⁆ = 1`; hence `⁅G, Q⁆ ≤ C_G(P) ≤ C_G(Q)`, giving
`⁅G, Q, Q⁆ = 1`.  Finally `⁅G, Q, Q⁆ = ⁅G, Q⁆` by 4.29, so `⁅G, Q⁆ = 1`.

The commutators in that argument are commutators of subgroups of `G ⋊ A`, which is where
`mathlib`'s three-subgroups lemma `Subgroup.commutator_commutator_eq_bot_of_rotate` lives;
`CoprimeAction.map_inl_commutatorSubgroup` is the dictionary between those and the commutators of
the action.
-/

@[expose] public section

namespace CoprimeAction

open scoped commutatorElement

universe u

variable {G A : Type u} [Group G] [Group A] [MulDistribMulAction A G]

/-!
## Commutators of an action inside the semidirect product
-/

theorem commutatorSubgroup_eq_bot_iff {X : Type u} [Group X] [MulDistribMulAction X G]
    {H : Subgroup G} :
    commutatorSubgroup X G H = ⊥ ↔ ∀ (x : X), ∀ h ∈ H, x • h = h := by
  constructor
  · intro hbot x h hh
    have hmem : h⁻¹ * (x • h) ∈ (⊥ : Subgroup G) := hbot ▸ mem_commutatorSubgroup_gen x hh
    rw [Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem.symm
  · intro hfix
    rw [eq_bot_iff]
    refine commutatorSubgroup_le fun x h hh ↦ ?_
    rw [hfix x h hh, inv_mul_cancel]
    exact Subgroup.mem_bot.mpr rfl

/-- The dictionary between commutators of the action and commutators inside `G ⋊ A`: both
inclusions come from `⁅inl h, inr x⁆ = inl (h * (x • h⁻¹))`. -/
theorem map_inl_commutatorSubgroup (X : Subgroup A) (H : Subgroup G) :
    letI : MulDistribMulAction X G := MulDistribMulAction.compHom G X.subtype
    Subgroup.map (SemidirectProduct.inl (φ := MulDistribMulAction.toMulAut A G))
        (commutatorSubgroup X G H)
      = ⁅Subgroup.map (SemidirectProduct.inl (φ := MulDistribMulAction.toMulAut A G)) H,
          Subgroup.map (SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut A G)) X⁆ := by
  let : MulDistribMulAction X G := MulDistribMulAction.compHom G X.subtype
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    refine commutatorSubgroup_le fun x h hh ↦ ?_
    rw [Subgroup.mem_comap]
    change (SemidirectProduct.inl (h⁻¹ * ((x : A) • h)) : Semidirect G A) ∈ _
    have key : (SemidirectProduct.inl (h⁻¹ * ((x : A) • h)) : Semidirect G A)
        = ⁅(SemidirectProduct.inl h⁻¹ : Semidirect G A),
            (SemidirectProduct.inr (x : A) : Semidirect G A)⁆ := by
      refine SemidirectProduct.ext ?_ ?_ <;> simp [commutatorElement_def]
    rw [key]
    exact Subgroup.commutator_mem_commutator ⟨h⁻¹, H.inv_mem hh, rfl⟩ ⟨(x : A), x.2, rfl⟩
  · rw [Subgroup.commutator_le]
    rintro u ⟨h, hh, rfl⟩ v ⟨x, hx, rfl⟩
    have key : ⁅(SemidirectProduct.inl h : Semidirect G A),
          (SemidirectProduct.inr x : Semidirect G A)⁆
        = SemidirectProduct.inl ((h⁻¹)⁻¹ * (x • h⁻¹)) := by
      refine SemidirectProduct.ext ?_ ?_ <;> simp [commutatorElement_def]
    rw [key]
    exact ⟨_, mem_commutatorSubgroup_gen (⟨x, hx⟩ : X) (H.inv_mem hh), rfl⟩

/-- Triviality of a commutator of copies inside `G ⋊ A` is triviality of the action. -/
theorem commutator_copies_eq_bot_iff (X : Subgroup A) (H : Subgroup G) :
    ⁅Subgroup.map (SemidirectProduct.inl (φ := MulDistribMulAction.toMulAut A G)) H,
        Subgroup.map (SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut A G)) X⁆ = ⊥
      ↔ ∀ x ∈ X, ∀ h ∈ H, x • h = h := by
  let : MulDistribMulAction X G := MulDistribMulAction.compHom G X.subtype
  rw [← map_inl_commutatorSubgroup X H, Subgroup.map_eq_bot_iff_of_injective _
    SemidirectProduct.inl_injective, commutatorSubgroup_eq_bot_iff]
  exact ⟨fun h x hx g hg ↦ h ⟨x, hx⟩ g hg, fun h x g hg ↦ h (x : A) x.2 g hg⟩

/-!
## Isaacs 4.31
-/

variable {p : ℕ} [Fact p.Prime]

/-- Auxiliary induction on `|G|` for `CoprimeAction.thompson_pq`. -/
theorem thompson_aux (hSZ : SchurZassenhausConjugacy.{u}) [Finite A] {P Q : Subgroup A} [P.Normal]
    (hP : IsPGroup p P) (hQ : ¬ p ∣ Nat.card Q) (hcomm : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) :
    ∀ (n : ℕ) (G : Type u) [Group G] [Finite G] [MulDistribMulAction A G], Nat.card G ≤ n →
      IsPGroup p G → (∀ g : G, (∀ x ∈ P, x • g = g) → ∀ y ∈ Q, y • g = g) →
      ∀ y ∈ Q, ∀ g : G, y • g = g := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ hcard _ _ _ _ _
    exact absurd hcard (Nat.not_le.mpr Nat.card_pos)
  | succ n ih =>
    intro G _ _ _ hcard hG hfix y hy g
    rcases subsingleton_or_nontrivial G with hs | hs
    · exact Subsingleton.elim _ _
    let : MulDistribMulAction P G := MulDistribMulAction.compHom G P.subtype
    let : MulDistribMulAction Q G := MulDistribMulAction.compHom G Q.subtype
    -- `⁅G, P⁆` is a proper subgroup (4.32) and is `A`-invariant, because `P ⊴ A`
    have hHlt : commutatorAction P G < ⊤ := commutatorAction_lt_top hG hP
    have hHinv : ∀ (a : A), ∀ h ∈ commutatorAction P G, a • h ∈ commutatorAction P G := by
      intro a n hn
      induction hn using Subgroup.closure_induction with
      | mem z hz =>
        obtain ⟨x, h, -, rfl⟩ := hz
        change a • (h⁻¹ * ((x : A) • h)) ∈ _
        have key : a • (h⁻¹ * ((x : A) • h))
            = (a • h)⁻¹ * ((⟨a * (x : A) * a⁻¹, ‹P.Normal›.conj_mem _ x.2 a⟩ : P) • (a • h)) := by
          change a • (h⁻¹ * ((x : A) • h)) = (a • h)⁻¹ * ((a * (x : A) * a⁻¹) • (a • h))
          rw [smul_mul', smul_inv', ← mul_smul, ← mul_smul]
          congr 2
          group
        rw [key]
        exact mem_commutatorSubgroup_gen _ (Subgroup.mem_top _)
      | one => simp
      | mul z w _ _ hz hw =>
        rw [smul_mul']
        exact mul_mem hz hw
      | inv z _ hz =>
        rw [smul_inv']
        exact inv_mem hz
    let : MulDistribMulAction A (commutatorAction P G) :=
      { smul := fun a h ↦ ⟨a • (h : G), hHinv a (h : G) h.2⟩
        one_smul := fun h ↦ Subtype.ext (one_smul A (h : G))
        mul_smul := fun a b h ↦ Subtype.ext (mul_smul a b (h : G))
        smul_mul := fun a h k ↦ Subtype.ext (smul_mul' a (h : G) (k : G))
        smul_one := fun a ↦ Subtype.ext (smul_one a) }
    have hcoeH : ∀ (a : A) (h : commutatorAction P G),
        ((a • h : commutatorAction P G) : G) = a • (h : G) := fun _ _ ↦ rfl
    -- the inductive hypothesis applies to `⁅G, P⁆`
    have hcardH : Nat.card (commutatorAction P G) ≤ n := by
      have hlt : Nat.card (commutatorAction P G) < Nat.card G := by
        rw [← (commutatorAction P G).index_mul_card]
        exact lt_mul_of_one_lt_left Nat.card_pos
          (Subgroup.one_lt_index_of_ne_top (ne_of_lt hHlt))
      omega
    have hfixH : ∀ h : commutatorAction P G, (∀ x ∈ P, x • h = h) → ∀ z ∈ Q, z • h = h := by
      intro h hh z hz
      refine Subtype.ext ?_
      rw [hcoeH]
      refine hfix (h : G) (fun x hx ↦ ?_) z hz
      have hx' := hh x hx
      rw [← hcoeH x h]
      exact congrArg Subtype.val hx'
    have hQH : ∀ z ∈ Q, ∀ h : commutatorAction P G, z • h = h :=
      ih (commutatorAction P G) hcardH (hG.to_subgroup _) hfixH
    -- `⁅G, P, Q⁆ = 1`
    have h1 : ⁅⁅Subgroup.map (SemidirectProduct.inl (φ := MulDistribMulAction.toMulAut A G))
            (⊤ : Subgroup G),
          Subgroup.map (SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut A G)) P⁆,
        Subgroup.map (SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut A G)) Q⁆ = ⊥ := by
      rw [← map_inl_commutatorSubgroup P ⊤, commutator_copies_eq_bot_iff]
      intro z hz h hh
      have := hQH z hz ⟨h, hh⟩
      rw [← hcoeH z ⟨h, hh⟩]
      exact congrArg Subtype.val this
    -- `⁅P, Q, G⁆ = 1`, since `P` and `Q` commute
    have h2 : ⁅⁅Subgroup.map (SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut A G)) P,
          Subgroup.map (SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut A G)) Q⁆,
        Subgroup.map (SemidirectProduct.inl (φ := MulDistribMulAction.toMulAut A G))
          (⊤ : Subgroup G)⁆ = ⊥ := by
      have hPQ : ⁅Subgroup.map (SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut A G)) P,
          Subgroup.map (SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut A G)) Q⁆
            = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        rintro u ⟨x, hx, rfl⟩ v ⟨z, hz, rfl⟩
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm, ← map_mul, ← map_mul,
          hcomm x hx z hz]
      rw [hPQ]
      simp
    -- the three-subgroups lemma gives `⁅Q, G, P⁆ = 1`
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    -- so `P` acts trivially on `⁅G, Q⁆`
    have h4 : ∀ x ∈ P, ∀ h ∈ commutatorAction Q G, x • h = h := by
      rw [← commutator_copies_eq_bot_iff P (commutatorAction Q G),
        map_inl_commutatorSubgroup Q ⊤,
        Subgroup.commutator_comm
          (Subgroup.map (SemidirectProduct.inl (φ := MulDistribMulAction.toMulAut A G))
            (⊤ : Subgroup G))]
      exact h3
    -- by hypothesis `Q` acts trivially on it too, that is, `⁅G, Q, Q⁆ = 1`
    have h5 : commutatorAction₂ Q G = ⊥ := by
      rw [commutatorSubgroup_eq_bot_iff]
      intro z h hh
      exact hfix h (fun x hx ↦ h4 x hx h hh) (z : A) z.2
    -- and `⁅G, Q, Q⁆ = ⁅G, Q⁆` by 4.29
    have hcopQ : Nat.Coprime (Nat.card Q) (Nat.card G) := by
      obtain ⟨m, hm⟩ := hG.exists_card_eq
      rw [hm]
      exact (((Nat.Prime.coprime_iff_not_dvd ‹Fact p.Prime›.out).mpr hQ).symm).pow_right m
    have h6 : commutatorAction Q G = ⊥ := by
      rw [← commutatorAction₂_eq hSZ hcopQ]
      exact h5
    have hmem : g⁻¹ * ((⟨y, hy⟩ : Q) • g) ∈ (⊥ : Subgroup G) :=
      h6 ▸ mem_commutatorSubgroup_gen (⟨y, hy⟩ : Q) (Subgroup.mem_top g)
    rw [Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem.symm

/-- **Isaacs, Theorem 4.31 (Thompson's `P × Q` lemma).**  If the `p`-group `P` and the `p'`-group
`Q` are commuting subgroups of a group `A` acting on a `p`-group `G`, and `Q` fixes every element
of `G` that `P` fixes, then `Q` acts trivially on `G`.

No normality is assumed: `P` is normalized by itself and centralized by `Q`, so it is normal in
`Q ⊔ P`, and restricting the action to that subgroup — which is all that the conclusion involves —
puts us in the situation of `CoprimeAction.thompson_aux`. -/
theorem thompson_pq (hSZ : SchurZassenhausConjugacy.{u}) [Finite G] [Finite A]
    (hG : IsPGroup p G) {P Q : Subgroup A} (hP : IsPGroup p P)
    (hQ : ¬ p ∣ Nat.card Q) (hcomm : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x)
    (hfix : ∀ g : G, (∀ x ∈ P, x • g = g) → ∀ y ∈ Q, y • g = g) :
    ∀ y ∈ Q, ∀ g : G, y • g = g := by
  -- `Q` centralizes `P`, so it normalizes it
  have hconj : ∀ y ∈ Q, ∀ x ∈ P, y * x * y⁻¹ = x := by
    intro y hy x hx
    rw [← hcomm x hx y hy]
    group
  have hQnorm : Q ≤ Subgroup.normalizer (P : Set _) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    refine fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · rw [hconj y hy x hx]
      exact hx
    · have h := hconj y⁻¹ (Q.inv_mem hy) _ hx
      have hx' : x = y * x * y⁻¹ := by rw [← h]; group
      rw [hx']
      exact hx
  -- restrict the action to `Q ⊔ P`, in which `P` is normal
  have : (P.subgroupOf (Q ⊔ P)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hQnorm
  let : MulDistribMulAction (Q ⊔ P : Subgroup A) G :=
    MulDistribMulAction.compHom G (Q ⊔ P : Subgroup A).subtype
  have hPS : P ≤ Q ⊔ P := le_sup_right
  have hQS : Q ≤ Q ⊔ P := le_sup_left
  have hP' : IsPGroup p (P.subgroupOf (Q ⊔ P)) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPS).symm
  have hQ' : ¬ p ∣ Nat.card (Q.subgroupOf (Q ⊔ P)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv]
  have hcomm' : ∀ x ∈ P.subgroupOf (Q ⊔ P), ∀ y ∈ Q.subgroupOf (Q ⊔ P), x * y = y * x :=
    fun x hx y hy ↦ Subtype.ext (hcomm (x : A) hx (y : A) hy)
  have hfix' : ∀ g : G, (∀ x ∈ P.subgroupOf (Q ⊔ P), x • g = g) →
      ∀ y ∈ Q.subgroupOf (Q ⊔ P), y • g = g :=
    fun g hg y hy ↦ hfix g (fun x hx ↦ hg ⟨x, hPS hx⟩ hx) (y : A) hy
  exact fun y hy g ↦
    thompson_aux hSZ hP' hQ' hcomm' (Nat.card G) G le_rfl hG hfix' ⟨y, hQS hy⟩ hy g

end CoprimeAction
