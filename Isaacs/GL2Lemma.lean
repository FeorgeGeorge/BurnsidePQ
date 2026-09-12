module

public import Isaacs.SL2Involution
public import Isaacs.NoncyclicAbelianAction
public import Isaacs.CommutatorAction
public import Isaacs.GlaubermanLemma
public import Isaacs.FittingSubgroup

/-!
# Isaacs' Lemma 7.3

Isaacs, *Finite Group Theory*, Lemma 7.3:

> Let `G = GL(2, p)`, where `p ≠ 2` is prime, and let `P ⊆ G` be a `p`-subgroup.  Suppose
> `P ⊆ N_G(L)` for some subgroup `L` of `G`, where `|L|` is not divisible by `p`, and assume
> further that a Sylow `2`-subgroup of `L` is abelian.  Then `P ⊆ C_G(L)`.

Isaacs uses this for Theorem 7.1, through the identification of `Aut(E)` with `GL(2, p)` for an
elementary abelian group `E` of order `p ^ 2`.

The hypothesis on Sylow `2`-subgroups is stated here as "every `2`-subgroup of `L` is abelian",
which is the same condition (every `2`-subgroup lies in a Sylow `2`-subgroup) and is what the
proof uses: the argument only needs it once `L` has turned out to be a `2`-group.

This file collects the pieces of the proof; the main induction is `PiGroups.lemma_7_3`.
-/

@[expose] public section

namespace PiGroups

open CoprimeAction NoncyclicAbelian

universe u

/-!
## Trivial actions and trivial commutators
-/

/-- A trivial commutator subgroup means the action is trivial. -/
theorem smul_eq_self_of_commutatorAction_eq_bot {A V : Type u} [Group A] [Group V]
    [MulDistribMulAction A V] (h : commutatorAction A V = ⊥) (a : A) (g : V) : a • g = g := by
  have hmem : g⁻¹ * (a • g) ∈ commutatorAction A V :=
    mem_commutatorSubgroup_gen a (Subgroup.mem_top g)
  rw [h, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem.symm

/-- A trivial action means a trivial commutator subgroup. -/
theorem commutatorAction_eq_bot_of_smul_eq_self {A V : Type u} [Group A] [Group V]
    [MulDistribMulAction A V] (h : ∀ (a : A) (g : V), a • g = g) : commutatorAction A V = ⊥ := by
  rw [eq_bot_iff]
  refine commutatorSubgroup_le fun a g _ => ?_
  rw [h a g, inv_mul_cancel]
  exact Subgroup.mem_bot.mpr rfl

/-!
## Orbit counting
-/

/-- A `p`-group acting nontrivially on a finite group has `p + 1 ≤ |L|`: the identity is a fixed
point and the noncentral part is a union of orbits of size divisible by `p`. -/
theorem card_ge_of_smul_ne {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V] {p : ℕ} [Fact p.Prime] (hA : IsPGroup p A) {a : A} {x : V}
    (hax : a • x ≠ x) : p + 1 ≤ Nat.card V := by
  classical
  have hmod := hA.card_modEq_card_fixedPoints (α := V)
  have hone : (1 : V) ∈ MulAction.fixedPoints A V := fun b => smul_one b
  have hfix_pos : 0 < Nat.card (MulAction.fixedPoints A V) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, hone⟩⟩, inferInstance⟩
  have hxnot : x ∉ MulAction.fixedPoints A V := fun hx => hax (hx a)
  have hlt : Nat.card (MulAction.fixedPoints A V) < Nat.card V := by
    have hss : MulAction.fixedPoints A V ⊂ Set.univ :=
      ⟨Set.subset_univ _, fun hcon => hxnot (hcon (Set.mem_univ x))⟩
    have hcard := Set.ncard_lt_ncard hss Set.finite_univ
    rwa [Set.ncard_univ, ← Nat.card_coe_set_eq] at hcard
  have hdvd : p ∣ Nat.card V - Nat.card (MulAction.fixedPoints A V) :=
    (Nat.modEq_iff_dvd' hlt.le).mp hmod.symm
  have hpos : 0 < Nat.card V - Nat.card (MulAction.fixedPoints A V) := by omega
  have := Nat.le_of_dvd hpos hdvd
  omega

/-!
## An arithmetic step
-/

/-- If an odd prime power divides `a * b` where `gcd a b ∣ 2`, it divides one of the factors. -/
theorem pow_dvd_or_pow_dvd_of_ne_two {q k a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hab : Nat.gcd a b ∣ 2) (h : q ^ k ∣ a * b) : q ^ k ∣ a ∨ q ^ k ∣ b := by
  by_cases hqa : q ∣ a
  · have hqb : ¬ q ∣ b := by
      intro hb
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
        ((Nat.dvd_gcd hqa hb).trans hab))
    exact Or.inl (Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqb)) h)
  · exact Or.inr (Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqa)) h)

/-!
## The setting of Lemma 7.3
-/

section Lemma73

/-- The ambient group of Lemma 7.3. -/
abbrev GL2 (p : ℕ) := Matrix.GeneralLinearGroup (Fin 2) (ZMod p)

/-- `SL(2, p)` seen inside `GL(2, p)`, as the kernel of the determinant. -/
abbrev slKer (p : ℕ) [Fact p.Prime] : Subgroup (GL2 p) :=
  (Matrix.GeneralLinearGroup.det : GL2 p →* (ZMod p)ˣ).ker

/-- `|SL(2, p)| = p (p - 1) (p + 1)`. -/
theorem card_slKer (p : ℕ) [Fact p.Prime] : Nat.card (slKer p) = p * ((p - 1) * (p + 1)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [← Matrix.card_specialLinearGroup_eq_card_ker_det,
    Matrix.card_specialLinearGroup_fin_two', ZMod.card p]

/-- A subgroup carried into itself by conjugation by `P` is normalized by `P`. -/
theorem le_normalizer_of_conj_mem {X : Type*} [Group X] {P M : Subgroup X}
    (hinv : ∀ a ∈ P, ∀ y ∈ M, a * y * a⁻¹ ∈ M) : P ≤ Subgroup.normalizer (M : Set X) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hinv a ha y hy, fun hy => ?_⟩
  have h1 : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ ∈ M := hinv a⁻¹ (inv_mem ha) _ hy
  have h2 : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
  rwa [h2] at h1

variable {p : ℕ}

private theorem lemma_7_3_aux [Fact p.Prime] (hp2 : p ≠ 2) (P : Subgroup (GL2 p))
    (hP : IsPGroup p P) :
    ∀ (n : ℕ) (L : Subgroup (GL2 p)), Nat.card L ≤ n →
      P ≤ Subgroup.normalizer (L : Set (GL2 p)) → ¬ p ∣ Nat.card L →
      (∀ A : Subgroup (GL2 p), A ≤ L → IsPGroup 2 A → ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      ∀ x ∈ P, ∀ y ∈ L, x * y = y * x := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · obtain ⟨m, hm⟩ := h
      have := hp.two_le
      omega
  intro n
  induction n with
  | zero =>
    intro L hcard
    have := Nat.card_pos (α := ↥L)
    omega
  | succ n ih =>
    intro L hcard hPN hLp hL2 x hx y hy
    let _inst := conjActionOfLeNormalizer P L hPN
    have hcoe : ∀ (a : ↥P) (g : ↥L),
        ((a • g : ↥L) : GL2 p) = (a : GL2 p) * (g : GL2 p) * (a : GL2 p)⁻¹ :=
      fun a g => conjActionOfLeNormalizer_coe P L hPN a g
    -- it is enough to show that the conjugation action of `P` on `L` is trivial
    suffices hact : ∀ (a : ↥P) (g : ↥L), a • g = g by
      have h1 : ((⟨x, hx⟩ : ↥P) • (⟨y, hy⟩ : ↥L) : ↥L) = ⟨y, hy⟩ := hact _ _
      have h2 := hcoe ⟨x, hx⟩ ⟨y, hy⟩
      rw [h1] at h2
      calc x * y = x * y * x⁻¹ * x := by group
        _ = y * x := by rw [← h2]
    by_contra hcon
    push Not at hcon
    obtain ⟨a₀, g₀, hg₀⟩ := hcon
    have hLne : Nontrivial ↥L := by
      rcases subsingleton_or_nontrivial ↥L with h | h
      · exact absurd (Subsingleton.elim _ _) hg₀
      · exact h
    have hKne : commutatorAction ↥P ↥L ≠ ⊥ := fun h =>
      hg₀ (smul_eq_self_of_commutatorAction_eq_bot h a₀ g₀)
    have hcop : Nat.Coprime p (Nat.card ↥L) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hLp
    have hcopPL : Nat.Coprime (Nat.card ↥P) (Nat.card ↥L) := by
      obtain ⟨m, hm⟩ := hP.exists_card_eq
      rw [hm]
      exact Nat.Coprime.pow_left m hcop
    -- Step 1: some prime `q` divides the index of the fixed points
    have hFne : FixedPoints.subgroup ↥P ↥L ≠ ⊤ := by
      intro htop
      have hmem : g₀ ∈ FixedPoints.subgroup ↥P ↥L := htop ▸ Subgroup.mem_top g₀
      exact hg₀ (hmem a₀)
    obtain ⟨q, hq, hqdvd⟩ : ∃ q, q.Prime ∧ q ∣ (FixedPoints.subgroup ↥P ↥L).index :=
      Nat.exists_prime_and_dvd fun h => hFne (Subgroup.index_eq_one.mp h)
    have : Fact q.Prime := ⟨hq⟩
    -- Step 2: a `P`-invariant Sylow `q`-subgroup of `L`
    obtain ⟨Q, hQinv⟩ := exists_invariant_sylow (A := ↥P) (G := ↥L) hP hcop (q := q)
    have hQmapinv : ∀ a ∈ P, ∀ z ∈ (Q : Subgroup ↥L).map L.subtype,
        a * z * a⁻¹ ∈ (Q : Subgroup ↥L).map L.subtype := by
      rintro a ha _ ⟨g, hg, rfl⟩
      refine ⟨(⟨a, ha⟩ : ↥P) • g, (IsInvariant.invariant (A := ↥P) (G := ↥L) ⟨a, ha⟩ g).mp hg, ?_⟩
      exact (hcoe ⟨a, ha⟩ g).symm
    -- if it is proper, induction makes it centralize `P`, contradicting the choice of `q`
    have hQtop : (Q : Subgroup ↥L) = ⊤ := by
      by_contra hQne
      have hQlt : (Q : Subgroup ↥L) < ⊤ := lt_of_le_of_ne le_top hQne
      have hcardQ : Nat.card ((Q : Subgroup ↥L).map L.subtype) < Nat.card ↥L := by
        rw [Subgroup.card_map_of_injective L.subtype_injective]
        have h1 := card_lt_card_of_lt hQlt
        rwa [Subgroup.card_top] at h1
      have hcent := ih ((Q : Subgroup ↥L).map L.subtype) (by omega)
        (le_normalizer_of_conj_mem hQmapinv)
        (fun hdvd => hLp (hdvd.trans (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))))
        (fun A hA => hL2 A (hA.trans (Subgroup.map_subtype_le _)))
      have hQF : (Q : Subgroup ↥L) ≤ FixedPoints.subgroup ↥P ↥L := by
        intro g hg
        change ∀ a : ↥P, a • g = g
        intro a
        refine Subtype.ext ?_
        rw [hcoe]
        have hcomm := hcent (a : GL2 p) a.2 (g : GL2 p) ⟨g, hg, rfl⟩
        calc (a : GL2 p) * (g : GL2 p) * (a : GL2 p)⁻¹
            = ((g : GL2 p) * (a : GL2 p)) * (a : GL2 p)⁻¹ := by rw [hcomm]
          _ = (g : GL2 p) := by group
      exact Q.not_dvd_index (hqdvd.trans (Subgroup.index_dvd_of_le hQF))
    have hLq : IsPGroup q ↥L := Q.isPGroup'.of_equiv (hQtop ▸ Subgroup.topEquiv)
    -- Step 3: `⁅L, P⁆ = L`, else induction and Isaacs 4.29 make the action trivial
    have hKtop : commutatorAction ↥P ↥L = ⊤ := by
      by_contra hKne'
      have hKlt : commutatorAction ↥P ↥L < ⊤ := lt_of_le_of_ne le_top hKne'
      have hKmapinv : ∀ a ∈ P, ∀ z ∈ (commutatorAction ↥P ↥L).map L.subtype,
          a * z * a⁻¹ ∈ (commutatorAction ↥P ↥L).map L.subtype := by
        rintro a ha _ ⟨g, hg, rfl⟩
        exact ⟨(⟨a, ha⟩ : ↥P) • g, smul_mem_commutatorAction _ hg, (hcoe ⟨a, ha⟩ g).symm⟩
      have hcardK : Nat.card ((commutatorAction ↥P ↥L).map L.subtype) < Nat.card ↥L := by
        rw [Subgroup.card_map_of_injective L.subtype_injective]
        have h1 := card_lt_card_of_lt hKlt
        rwa [Subgroup.card_top] at h1
      have hcent := ih ((commutatorAction ↥P ↥L).map L.subtype) (by omega)
        (le_normalizer_of_conj_mem hKmapinv)
        (fun hdvd => hLp (hdvd.trans (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))))
        (fun A hA => hL2 A (hA.trans (Subgroup.map_subtype_le _)))
      -- so `⁅L, P, P⁆ = 1`, and by Isaacs 4.29 that is `⁅L, P⁆`
      have h2 : commutatorAction₂ ↥P ↥L = ⊥ := by
        rw [eq_bot_iff]
        refine commutatorSubgroup_le fun a g hg => ?_
        have hcomm := hcent (a : GL2 p) a.2 (g : GL2 p) ⟨g, hg, rfl⟩
        refine Subgroup.mem_bot.mpr (Subtype.ext ?_)
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hcoe, Subgroup.coe_one]
        calc (g : GL2 p)⁻¹ * ((a : GL2 p) * (g : GL2 p) * (a : GL2 p)⁻¹)
            = (g : GL2 p)⁻¹ * ((g : GL2 p) * (a : GL2 p) * (a : GL2 p)⁻¹) := by rw [hcomm]
          _ = 1 := by group
      rw [commutatorAction₂_eq schurZassenhausConjugacy hcopPL] at h2
      exact hKne h2
    -- Step 4: `L = ⁅L, P⁆` lies in `SL(2, p)`
    have hLSL : L ≤ slKer p := by
      intro z hz
      have hz' : (⟨z, hz⟩ : ↥L) ∈ commutatorAction ↥P ↥L := hKtop ▸ Subgroup.mem_top _
      have hdet : ∀ u v : (ZMod p)ˣ, u⁻¹ * (v * u * v⁻¹) = 1 := by
        intro u v
        rw [mul_comm v u, mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel]
      have hle : commutatorAction ↥P ↥L ≤ (slKer p).subgroupOf L := by
        refine commutatorSubgroup_le fun a g _ => ?_
        change ((g⁻¹ * (a • g) : ↥L) : GL2 p) ∈ slKer p
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hcoe]
        simp only [MonoidHom.mem_ker, map_mul, map_inv]
        exact hdet _ _
      exact hle hz'
    -- Step 5: the two cases for `q`
    rcases eq_or_ne q 2 with rfl | hq2
    · -- `L` is an abelian `2`-group with a unique involution, which `P` must fix
      have hLab : ∀ v ∈ L, ∀ w ∈ L, v * w = w * v := hL2 L le_rfl hLq
      let _instC : CommGroup ↥L :=
        { (inferInstance : Group ↥L) with
          mul_comm := fun v w => Subtype.ext (hLab (v : GL2 p) v.2 (w : GL2 p) w.2) }
      have h2dvd : 2 ∣ Nat.card ↥L := by
        obtain ⟨m, hm⟩ := hLq.exists_card_eq
        rw [hm]
        refine dvd_pow_self 2 fun h0 => ?_
        rw [h0, pow_zero, Nat.card_eq_one_iff_unique] at hm
        exact (not_subsingleton ↥L) hm.1
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 h2dvd
      have htt : t * t = 1 := by
        have h1 := pow_orderOf_eq_one t
        rwa [ht, pow_two] at h1
      have ht1 : t ≠ 1 := by
        intro hcon2
        rw [hcon2, orderOf_one] at ht
        omega
      -- every involution of `L` is `-I`, hence equal to `t`
      have key : ∀ s : ↥L, s * s = 1 → s ≠ 1 →
          ((s : GL2 p) : Matrix (Fin 2) (Fin 2) (ZMod p)) = -1 := by
        intro s hs hs1
        refine Matrix.eq_neg_one_of_mul_self_eq_one
          (Matrix.SpecialLinearGroup.two_ne_zero_zmod_of_prime_ne_two hp hp2) ?_ ?_ ?_
        · exact congrArg Units.val (MonoidHom.mem_ker.mp (hLSL s.2))
        · exact congrArg (fun u : GL2 p => (u : Matrix (Fin 2) (Fin 2) (ZMod p)))
            (congrArg Subtype.val hs)
        · intro hcon2
          exact hs1 (Subtype.ext (Units.ext hcon2))
      have huniq : ∀ s : ↥L, s * s = 1 → s ≠ 1 → s = t := fun s hs hs1 =>
        Subtype.ext (Units.ext ((key s hs hs1).trans (key t htt ht1).symm))
      -- `t` is fixed by `P`
      have htfix : t ∈ FixedPoints.subgroup ↥P ↥L := by
        change ∀ a : ↥P, a • t = t
        intro a
        refine (huniq (a • t) ?_ ?_).symm ▸ rfl
        · rw [← smul_mul', htt, smul_one]
        · intro hcon2
          refine ht1 ?_
          have h3 := congrArg (fun z : ↥L => a⁻¹ • z) hcon2
          simpa [← mul_smul] using h3
      have hbot := fixedPoints_inf_commutatorAction_eq_bot (A := ↥P) (V := ↥L) hcopPL
      rw [hKtop, inf_top_eq] at hbot
      exact ht1 (Subgroup.mem_bot.mp (hbot ▸ htfix))
    · -- `q` is odd: counting in `SL(2, p)` bounds `|L|`, and the orbits bound it below
      obtain ⟨k, hk⟩ := hLq.exists_card_eq
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · rw [pow_zero, Nat.card_eq_one_iff_unique] at hk
          exact absurd hk.1 (not_subsingleton ↥L)
        · exact h
      have hqp : q ≠ p := by
        rintro rfl
        refine hLp ?_
        rw [hk]
        exact dvd_pow_self q (by omega)
      have hdvdSL : Nat.card ↥L ∣ p * ((p - 1) * (p + 1)) := by
        rw [← card_slKer p]
        exact Subgroup.card_dvd_of_le hLSL
      have hcopqp : Nat.Coprime (q ^ k) p :=
        Nat.Coprime.pow_left k ((Nat.coprime_primes hq hp).mpr hqp)
      have hdvd2 : q ^ k ∣ (p - 1) * (p + 1) := by
        rw [hk] at hdvdSL
        exact hcopqp.dvd_of_dvd_mul_left hdvdSL
      have hgcd : Nat.gcd (p - 1) (p + 1) ∣ 2 := by
        have h1 : Nat.gcd (p - 1) (p + 1) ∣ (p - 1) := Nat.gcd_dvd_left _ _
        have h2 : Nat.gcd (p - 1) (p + 1) ∣ (p + 1) := Nat.gcd_dvd_right _ _
        have h4 : Nat.gcd (p - 1) (p + 1) ∣ (p - 1) + 2 := by
          have h3 : (p - 1) + 2 = p + 1 := by omega
          rw [h3]
          exact h2
        exact (Nat.dvd_add_right h1).mp h4
      have hle : Nat.card ↥L ≤ p + 1 := by
        rw [hk]
        rcases pow_dvd_or_pow_dvd_of_ne_two hq hq2 hgcd hdvd2 with h | h
        · exact le_trans (Nat.le_of_dvd (by omega) h) (by omega)
        · exact Nat.le_of_dvd (by omega) h
      have hge : p + 1 ≤ Nat.card ↥L := card_ge_of_smul_ne hP hg₀
      have hcardL : Nat.card ↥L = p + 1 := le_antisymm hle hge
      have h2dvd : 2 ∣ Nat.card ↥L := by
        rw [hcardL]
        rcases hp.eq_two_or_odd with h | h
        · exact absurd h hp2
        · omega
      rw [hk] at h2dvd
      exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2dvd)).symm

/-- **Isaacs, Lemma 7.3.**  In `GL(2, p)` with `p` an odd prime, a `p`-subgroup that normalizes a
subgroup `L` of order prime to `p` whose `2`-subgroups are abelian centralizes `L`. -/
theorem lemma_7_3 [Fact p.Prime] (hp2 : p ≠ 2) {P L : Subgroup (GL2 p)} (hP : IsPGroup p P)
    (hPN : P ≤ Subgroup.normalizer (L : Set (GL2 p))) (hLp : ¬ p ∣ Nat.card L)
    (hL2 : ∀ A : Subgroup (GL2 p), A ≤ L → IsPGroup 2 A → ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    ∀ x ∈ P, ∀ y ∈ L, x * y = y * x :=
  lemma_7_3_aux hp2 P hP (Nat.card L) L le_rfl hPN hLp hL2

end Lemma73

end PiGroups
