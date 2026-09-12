module

public import Isaacs.FittingSubgroup
public import Mathlib.Data.Fintype.Lattice

/-!
# Joins of subnormal subgroups: Isaacs 2.5–2.7

Isaacs, *Finite Group Theory*, Theorem 2.5 (Wielandt, 1939): in a finite group the join of two
subnormal subgroups is subnormal.  `mathlib`'s `Subgroup.IsSubnormal` has the intersection
(`Subgroup.IsSubnormal.inf`, Isaacs 2.3–2.4) but not the join, and the join is the deeper half.

The proof is Isaacs', through minimal normal subgroups and the socle:

* `PiGroups.IsMinimalNormal`: a nontrivial normal subgroup with no nontrivial normal subgroup of
  the ambient group properly inside it, and `PiGroups.exists_isMinimalNormal_le`: in a finite
  group every nontrivial normal subgroup contains one;
* `PiGroups.socle`: the join of all minimal normal subgroups, a characteristic subgroup;
* `PiGroups.IsMinimalNormal.le_normalizer` (**Theorem 2.6**): a minimal normal subgroup of `G`
  normalizes every subnormal subgroup of `G`.  Induction on `|G|`: with `S ⊴⊴ N ⊴ G` and `N < G`,
  either `M ⊓ N = 1`, and then `M` centralizes `N ⊇ S` by Isaacs 2.7
  (`Subgroup.commute_of_normal_of_disjoint`), or `M ≤ N`, and then induction inside `N` puts
  `Soc(N)` in `N_N(S)` while minimality of `M` forces `M ≤ Soc(N)`;
* `PiGroups.isSubnormal_sup` (**Theorem 2.5**): induction on `|G|` again.  In `G ⧸ M` the join of
  the images is subnormal, so `(S ⊔ T) M ⊴⊴ G` by the correspondence theorem
  (`Subgroup.IsSubnormal.comap`), and `M` normalizes `S ⊔ T` by 2.6, so `S ⊔ T` is normal in
  `(S ⊔ T) M`.

This is the first prerequisite of Wielandt's zipper lemma (Isaacs 2.9), which is what Baer's
Theorem 2.12 needs; 2.12 together with `PiGroups.le_fitting_iff` (Theorem 2.2, in
`Isaacs/FittingSubgroup.lean`) is Isaacs' route to Theorem 2.13, the hypothesis
`Burnside.InvolutionInvertsElement` of Step 7 of Burnside's `p ^ a q ^ b` theorem.
-/

@[expose] public section

namespace PiGroups

universe u

variable {G : Type u} [Group G]

/-!
## Minimal normal subgroups
-/

/-- A minimal normal subgroup: a nontrivial normal subgroup containing no smaller nontrivial
normal subgroup of the ambient group. -/
structure IsMinimalNormal (M : Subgroup G) : Prop where
  /-- A minimal normal subgroup is normal. -/
  normal : M.Normal
  /-- A minimal normal subgroup is nontrivial. -/
  ne_bot : M ≠ ⊥
  /-- It contains no smaller nontrivial normal subgroup. -/
  minimal : ∀ K : Subgroup G, K.Normal → K ≠ ⊥ → K ≤ M → K = M

/-- Automorphisms permute the minimal normal subgroups. -/
theorem IsMinimalNormal.map {M : Subgroup G} (hM : IsMinimalNormal M) (φ : G ≃* G) :
    IsMinimalNormal (M.map φ.toMonoidHom) := by
  have hinj : Function.Injective φ.toMonoidHom := φ.injective
  have hsurj : Function.Surjective φ.toMonoidHom := φ.surjective
  refine ⟨hM.normal.map _ hsurj, ?_, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hinj]
    exact hM.ne_bot
  · intro K hK hKbot hKle
    have h1 : K.comap φ.toMonoidHom ≤ M := by
      have h2 := Subgroup.comap_mono (f := φ.toMonoidHom) hKle
      rwa [Subgroup.comap_map_eq_self_of_injective hinj] at h2
    have h3 : K.comap φ.toMonoidHom ≠ ⊥ := by
      intro hbot
      refine hKbot ?_
      have h4 := Subgroup.map_comap_eq_self_of_surjective hsurj K
      rwa [hbot, Subgroup.map_bot, eq_comm] at h4
    have h5 := hM.minimal _ (hK.comap _) h3 h1
    rw [← h5, Subgroup.map_comap_eq_self_of_surjective hsurj]

/-- In a finite group, every nontrivial normal subgroup contains a minimal normal subgroup: take
one of smallest order. -/
theorem exists_isMinimalNormal_le [Finite G] {N : Subgroup G} (hN : N.Normal) (hNbot : N ≠ ⊥) :
    ∃ M : Subgroup G, IsMinimalNormal M ∧ M ≤ N := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun U : Subgroup G => (U : Set G)) SetLike.coe_injective
  set 𝒩 : Set (Subgroup G) := {K : Subgroup G | K.Normal ∧ K ≠ ⊥ ∧ K ≤ N} with h𝒩
  have hmem : ∀ K : Subgroup G, K ∈ 𝒩 ↔ (K.Normal ∧ K ≠ ⊥ ∧ K ≤ N) := by
    intro K
    rw [h𝒩]
    exact Iff.rfl
  have : Nonempty ↥𝒩 := ⟨⟨N, (hmem N).mpr ⟨hN, hNbot, le_rfl⟩⟩⟩
  obtain ⟨M₀, hM₀⟩ := Finite.exists_min fun K : ↥𝒩 => Nat.card (K : Subgroup G)
  obtain ⟨hMnormal, hMbot, hMN⟩ := (hmem _).mp M₀.2
  refine ⟨(M₀ : Subgroup G), ⟨hMnormal, hMbot, fun K hK hKbot hKle => ?_⟩, hMN⟩
  exact Subgroup.eq_of_le_of_card_ge hKle (hM₀ ⟨K, (hmem K).mpr ⟨hK, hKbot, hKle.trans hMN⟩⟩)

/-!
## The socle
-/

variable (G) in
/-- The socle `Soc(G)`: the join of all minimal normal subgroups of `G`. -/
def socle : Subgroup G := ⨆ (M : Subgroup G) (_ : IsMinimalNormal M), M

theorem le_socle {M : Subgroup G} (hM : IsMinimalNormal M) : M ≤ socle G :=
  le_iSup₂ (f := fun (M : Subgroup G) (_ : IsMinimalNormal M) => M) M hM

instance socle_characteristic : (socle G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [Subgroup.map_le_iff_le_comap, socle]
  refine iSup₂_le fun M hM => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_socle (hM.map φ)

/-!
## Isaacs' Theorem 2.6
-/

/-- Normalizing inside `N` is normalizing in `G`, for a subgroup `S ≤ N`. -/
theorem mem_normalizer_of_mem_normalizer_subgroupOf {N S : Subgroup G} (hSN : S ≤ N) {w : G}
    (hwN : w ∈ N)
    (h : (⟨w, hwN⟩ : ↥N) ∈ Subgroup.normalizer ((S.subgroupOf N : Subgroup ↥N) : Set ↥N)) :
    w ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact (Subgroup.mem_normalizer_iff.mp h ⟨y, hSN hy⟩).mp hy
  · intro hy
    have hyN : y ∈ N := by
      have h1 : w * y * w⁻¹ ∈ N := hSN hy
      have h2 : y = w⁻¹ * (w * y * w⁻¹) * w := by group
      rw [h2]
      exact mul_mem (mul_mem (inv_mem hwN) h1) hwN
    exact (Subgroup.mem_normalizer_iff.mp h ⟨y, hyN⟩).mpr hy

private theorem minimalNormal_le_normalizer_aux :
    ∀ (n : ℕ) (X : Type u) [Group X] [Finite X], Nat.card X ≤ n →
      ∀ M S : Subgroup X, IsMinimalNormal M → S.IsSubnormal →
        M ≤ Subgroup.normalizer (S : Set X) := by
  intro n
  induction n with
  | zero =>
    intro X _ _ hcard
    have := Nat.card_pos (α := X)
    omega
  | succ n ih =>
    intro X _ _ hcard M S hM hS
    rcases eq_or_ne S ⊤ with rfl | hSne
    · rw [Subgroup.normalizer_eq_top]
      exact le_top
    obtain ⟨N, hNnormal, hSN, hNlt⟩ := hS.exists_normal_and_le_and_lt_top_of_ne hSne
    have := hNnormal
    have := hM.normal
    by_cases hMN : M ⊓ N = ⊥
    · -- `M` centralizes `N`, and `S ≤ N`
      have hcomm := Subgroup.commute_of_normal_of_disjoint M N hM.normal hNnormal
        (disjoint_iff.mpr hMN)
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hfix : ∀ z ∈ N, m * z * m⁻¹ = z := by
        intro z hz
        calc m * z * m⁻¹ = z * m * m⁻¹ := by rw [(hcomm m z hm hz).eq]
          _ = z := by group
      constructor
      · intro hy
        rw [hfix y (hSN hy)]
        exact hy
      · intro hy
        have h3 : m * y * m⁻¹ = y := by
          have h4 : m * (m * y * m⁻¹) = m * y :=
            calc m * (m * y * m⁻¹) = (m * y * m⁻¹) * m :=
                  (hcomm m (m * y * m⁻¹) hm (hSN hy)).eq
              _ = m * y := by group
          exact mul_left_cancel h4
        rwa [h3] at hy
    · -- `M ≤ N`, and we induct inside `N`
      have hMle : M ≤ N := by
        have h1 := hM.minimal (M ⊓ N) inferInstance hMN inf_le_left
        exact h1 ▸ inf_le_right
      have hcardN : Nat.card ↥N < Nat.card X := by
        have h1 := card_lt_card_of_lt hNlt
        rwa [Subgroup.card_top] at h1
      have hsocle : socle ↥N ≤
          Subgroup.normalizer ((S.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
        rw [socle]
        exact iSup₂_le fun L hL => ih ↥N (by omega) L (S.subgroupOf N) hL hS.subgroupOf
      have hMsub_ne : M.subgroupOf N ≠ ⊥ := by
        intro hbot
        refine hM.ne_bot ?_
        have h1 := congrArg (Subgroup.map N.subtype) hbot
        rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hMle, Subgroup.map_bot] at h1
      obtain ⟨L, hL, hLM⟩ := exists_isMinimalNormal_le (hM.normal.subgroupOf N) hMsub_ne
      have hinf_ne : (M.subgroupOf N ⊓ socle ↥N) ≠ ⊥ := by
        intro hbot
        exact hL.ne_bot (le_bot_iff.mp (hbot ▸ le_inf hLM (le_socle hL)))
      have hmapinf : (M.subgroupOf N ⊓ socle ↥N).map N.subtype
          = M ⊓ (socle ↥N).map N.subtype := by
        rw [Subgroup.map_inf _ _ _ N.subtype_injective, Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hMle]
      have hMW_ne : M ⊓ (socle ↥N).map N.subtype ≠ ⊥ := by
        rw [← hmapinf]
        intro hbot
        exact hinf_ne (by rwa [Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at hbot)
      have hMW : M ≤ (socle ↥N).map N.subtype := by
        have h1 := hM.minimal _ inferInstance hMW_ne inf_le_left
        exact h1 ▸ inf_le_right
      intro m hm
      obtain ⟨w, hw, rfl⟩ := hMW hm
      exact mem_normalizer_of_mem_normalizer_subgroupOf hSN w.2 (hsocle hw)

/-- **Isaacs, Theorem 2.6.**  A minimal normal subgroup of a finite group normalizes every
subnormal subgroup. -/
theorem IsMinimalNormal.le_normalizer [Finite G] {M S : Subgroup G} (hM : IsMinimalNormal M)
    (hS : S.IsSubnormal) : M ≤ Subgroup.normalizer (S : Set G) :=
  minimalNormal_le_normalizer_aux (Nat.card G) G le_rfl M S hM hS

/-!
## Isaacs' Theorem 2.5
-/

private theorem isSubnormal_sup_aux :
    ∀ (n : ℕ) (X : Type u) [Group X] [Finite X], Nat.card X ≤ n →
      ∀ S T : Subgroup X, S.IsSubnormal → T.IsSubnormal → (S ⊔ T).IsSubnormal := by
  intro n
  induction n with
  | zero =>
    intro X _ _ hcard
    have := Nat.card_pos (α := X)
    omega
  | succ n ih =>
    intro X _ _ hcard S T hS hT
    rcases subsingleton_or_nontrivial X with _ | _
    · exact Subgroup.IsSubnormal.of_subsingleton
    · have htop : (⊤ : Subgroup X) ≠ ⊥ :=
        (Subgroup.nontrivial_iff_ne_bot ⊤).mp Subgroup.topEquiv.symm.nontrivial
      obtain ⟨M, hM, -⟩ := exists_isMinimalNormal_le (N := (⊤ : Subgroup X)) inferInstance htop
      have := hM.normal
      -- the join of the images is subnormal in `X ⧸ M`
      have hsupq : ((S ⊔ T).map (QuotientGroup.mk' M)).IsSubnormal := by
        rw [Subgroup.map_sup]
        exact ih (X ⧸ M) (by have := card_quotient_lt M hM.ne_bot; omega) _ _
          hS.quotient hT.quotient
      -- so `(S ⊔ T) M` is subnormal in `X`
      have hcomap := hsupq.comap (QuotientGroup.mk' M)
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hcomap
      -- and `M` normalizes `S ⊔ T` by Theorem 2.6
      have hMnorm : M ≤ Subgroup.normalizer ((S ⊔ T : Subgroup X) : Set X) := by
        intro m hm
        have h1 := hM.le_normalizer hS hm
        have h2 := hM.le_normalizer hT hm
        rw [← map_conj_eq_self_iff] at h1 h2 ⊢
        rw [Subgroup.map_sup, h1, h2]
      exact Subgroup.IsSubnormal.step (S ⊔ T) ((S ⊔ T) ⊔ M) le_sup_left hcomap
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
          (sup_le Subgroup.le_normalizer hMnorm))

/-- **Isaacs, Theorem 2.5** (Wielandt).  In a finite group the join of two subnormal subgroups is
subnormal. -/
theorem isSubnormal_sup [Finite G] {S T : Subgroup G} (hS : S.IsSubnormal) (hT : T.IsSubnormal) :
    (S ⊔ T).IsSubnormal :=
  isSubnormal_sup_aux (Nat.card G) G le_rfl S T hS hT

/-!
## Towards the zipper lemma

Two ingredients: subnormality inside an overgroup survives conjugation, and a subnormal but
non-normal subgroup has a conjugate, by an element outside its normalizer, that still sits inside
that normalizer — the pair `(H₁, H₂)` at the bottom of a subnormal chain in Isaacs' proof of the
zipper lemma.
-/

/-- Conjugation carries `S ⊴⊴ H` to `S ^ x ⊴⊴ H ^ x`. -/
theorem isSubnormal_subgroupOf_conj {S H : Subgroup G} (hSH : S ≤ H) (x : G)
    (h : (S.subgroupOf H).IsSubnormal) :
    ((S.map (MulAut.conj x).toMonoidHom).subgroupOf
      (H.map (MulAut.conj x).toMonoidHom)).IsSubnormal := by
  set e : ↥H ≃* ↥(H.map (MulAut.conj x).toMonoidHom) := (MulAut.conj x).subgroupMap H with he
  have key : (S.subgroupOf H).map e.toMonoidHom
      = (S.map (MulAut.conj x).toMonoidHom).subgroupOf (H.map (MulAut.conj x).toMonoidHom) := by
    ext u
    constructor
    · rintro ⟨⟨w, hwH⟩, hwS, rfl⟩
      exact ⟨w, hwS, rfl⟩
    · rintro ⟨s, hs, hsu⟩
      exact ⟨⟨s, hSH hs⟩, hs, Subtype.ext hsu⟩
  rw [← key]
  exact h.map e.surjective

/-- The last index at which a predicate that holds at `0` and fails at `n` still holds. -/
private theorem exists_step {n : ℕ} (P : ℕ → Prop) (h0 : P 0) (hn : ¬ P n) :
    ∃ i, i < n ∧ P i ∧ ¬ P (i + 1) := by
  classical
  have hspec : P (Nat.findGreatest P n) := Nat.findGreatest_spec (P := P) (Nat.zero_le n) h0
  have hlt : Nat.findGreatest P n < n :=
    lt_of_le_of_ne (Nat.findGreatest_le n) fun h => hn (h ▸ hspec)
  exact ⟨Nat.findGreatest P n, hlt, hspec,
    Nat.findGreatest_is_greatest (P := P) (Nat.lt_succ_self _) hlt⟩

/-- If `S` is subnormal but not normal in `G`, then some element outside `N_G(S)` conjugates `S`
into `N_G(S)`: take the last term of a subnormal chain that still lies in `N_G(S)`, and an element
of the next term. -/
theorem exists_conj_le_normalizer [Finite G] {S : Subgroup G} (hS : S.IsSubnormal)
    (hnn : ¬ S.Normal) :
    ∃ x : G, x ∉ Subgroup.normalizer (S : Set G) ∧
      S.map (MulAut.conj x).toMonoidHom ≤ Subgroup.normalizer (S : Set G) := by
  classical
  obtain ⟨n, f, hmono, hnormal, hf0, hfn⟩ := hS.exists_chain
  have hWtop : Subgroup.normalizer (S : Set G) ≠ ⊤ := fun h =>
    hnn (Subgroup.normalizer_eq_top_iff.mp h)
  have hP0 : f 0 ≤ Subgroup.normalizer (S : Set G) := by
    rw [hf0]
    exact Subgroup.le_normalizer
  have hPn : ¬ (f n ≤ Subgroup.normalizer (S : Set G)) := by
    rw [hfn]
    exact fun h => hWtop (top_le_iff.mp h)
  obtain ⟨i, -, hPi, hPi1⟩ :=
    exists_step (fun k => f k ≤ Subgroup.normalizer (S : Set G)) hP0 hPn
  obtain ⟨x, hxf, hxW⟩ := SetLike.not_le_iff_exists.mp hPi1
  refine ⟨x, hxW, ?_⟩
  have hSfi : S ≤ f i := hf0 ▸ hmono (Nat.zero_le i)
  have hnorm : f (i + 1) ≤ Subgroup.normalizer ((f i : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hmono (Nat.le_succ i))).mp (hnormal i)
  calc S.map (MulAut.conj x).toMonoidHom ≤ (f i).map (MulAut.conj x).toMonoidHom :=
        Subgroup.map_mono hSfi
    _ = f i := map_conj_eq_self_iff.mpr (hnorm hxf)
    _ ≤ Subgroup.normalizer (S : Set G) := hPi

/-!
## Isaacs' Theorem 2.9: Wielandt's zipper lemma
-/

/-- Conjugating back and forth. -/
theorem map_conj_conj_inv (H : Subgroup G) (y : G) :
    (H.map (MulAut.conj y⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj y).toMonoidHom.comp (MulAut.conj y⁻¹).toMonoidHom
      = MonoidHom.id G := by
    ext u
    change y * (y⁻¹ * u * y⁻¹⁻¹) * y⁻¹ = u
    group
  rw [hcomp, Subgroup.map_id]

private theorem zipper_aux [Finite G] :
    ∀ (n : ℕ) (S : Subgroup G), Nat.card G - Nat.card S ≤ n →
      (∀ H : Subgroup G, S ≤ H → H ≠ ⊤ → (S.subgroupOf H).IsSubnormal) →
      ¬ S.IsSubnormal →
      ∃ M : Subgroup G, IsCoatom M ∧ S ≤ M ∧ ∀ K : Subgroup G, IsCoatom K → S ≤ K → K = M := by
  intro n
  induction n with
  | zero =>
    intro S hcard _ hns
    refine absurd ?_ hns
    have hle : Nat.card S ≤ Nat.card G := Subgroup.card_le_card_group S
    rw [Subgroup.eq_top_of_card_eq S (by omega)]
    exact Subgroup.IsSubnormal.top
  | succ n ih =>
    intro S hcard hsub hns
    -- `S` is not normal, so its normalizer sits in a maximal subgroup `M`
    have hSnn : ¬ (S.subgroupOf ⊤ : Subgroup ↥(⊤ : Subgroup G)).Normal := fun h => hns
      (Subgroup.IsSubnormal.step S ⊤ le_top Subgroup.IsSubnormal.top h)
    have hSnn' : ¬ S.Normal := fun h => hns h.isSubnormal
    have hNtop : Subgroup.normalizer (S : Set G) ≠ ⊤ := fun h =>
      hSnn' (Subgroup.normalizer_eq_top_iff.mp h)
    obtain ⟨M, hM, hNM⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom (Subgroup.normalizer (S : Set G))).resolve_left hNtop
    refine ⟨M, hM, Subgroup.le_normalizer.trans hNM, ?_⟩
    intro K hK hSK
    have hSKsub : (S.subgroupOf K).IsSubnormal := hsub K hSK hK.1
    by_cases hnormalK : (S.subgroupOf K).Normal
    · -- `S ⊴ K`, so `K ≤ N_G(S) ≤ M`, and `K` is maximal
      have hKM : K ≤ M :=
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hSK).mp hnormalK).trans hNM
      rcases eq_or_lt_of_le hKM with heq | hlt
      · exact heq
      · exact absurd (hK.2 M hlt) hM.1
    · -- otherwise `T = ⟨S, S ^ y⟩` is a strictly larger subgroup with the same properties
      obtain ⟨x, hxW, hxle⟩ := exists_conj_le_normalizer hSKsub hnormalK
      set y : G := (x : G) with hy
      have hyK : y ∈ K := x.2
      have hyW : y ∉ Subgroup.normalizer (S : Set G) := by
        rw [← Subgroup.subgroupOf_normalizer_eq hSK] at hxW
        exact hxW
      have hyle : S.map (MulAut.conj y).toMonoidHom ≤ Subgroup.normalizer (S : Set G) := by
        rintro _ ⟨s, hs, rfl⟩
        have h1 := hxle ⟨⟨s, hSK hs⟩, hs, rfl⟩
        rw [← Subgroup.subgroupOf_normalizer_eq hSK] at h1
        exact h1
      have hSy_ne : S.map (MulAut.conj y).toMonoidHom ≠ S := fun h =>
        hyW (map_conj_eq_self_iff.mp h)
      set T : Subgroup G := S ⊔ S.map (MulAut.conj y).toMonoidHom with hT
      have hTnorm : T ≤ Subgroup.normalizer (S : Set G) := sup_le Subgroup.le_normalizer hyle
      have hSlt : S < T := by
        refine lt_of_le_of_ne le_sup_left fun h => hSy_ne ?_
        have h1 : S.map (MulAut.conj y).toMonoidHom ≤ S := le_sup_right.trans h.ge
        refine Subgroup.eq_of_le_of_card_ge h1 (le_of_eq ?_)
        exact (Subgroup.card_map_of_injective (K := S) (f := (MulAut.conj y).toMonoidHom)
          (MulAut.conj y).injective).symm
      have hTK : T ≤ K := by
        refine sup_le hSK ?_
        rintro _ ⟨s, hs, rfl⟩
        exact mul_mem (mul_mem hyK (hSK hs)) (inv_mem hyK)
      -- `T` inherits the hypothesis, by Wielandt's join theorem
      have hTsub : ∀ H : Subgroup G, T ≤ H → H ≠ ⊤ → (T.subgroupOf H).IsSubnormal := by
        intro H hTH hHtop
        have hSH : S ≤ H := le_sup_left.trans hTH
        have hSyH : S.map (MulAut.conj y).toMonoidHom ≤ H := le_sup_right.trans hTH
        have hSH' : S ≤ H.map (MulAut.conj y⁻¹).toMonoidHom := by
          intro s hs
          refine ⟨y * s * y⁻¹, hSyH ⟨s, hs, rfl⟩, ?_⟩
          change y⁻¹ * (y * s * y⁻¹) * y⁻¹⁻¹ = s
          group
        have hHtop' : H.map (MulAut.conj y⁻¹).toMonoidHom ≠ ⊤ := by
          intro htop
          refine hHtop ?_
          have h1 := map_conj_conj_inv H y
          rw [htop, Subgroup.map_top_of_surjective _ (MulAut.conj y).surjective] at h1
          exact h1.symm
        have h2 := isSubnormal_subgroupOf_conj hSH' y (hsub _ hSH' hHtop')
        rw [map_conj_conj_inv H y] at h2
        rw [hT, Subgroup.subgroupOf_sup hSH hSyH]
        exact isSubnormal_sup (hsub H hSH hHtop) h2
      -- but `T` is not subnormal, since `S` is normal in `T`
      have hTns : ¬ T.IsSubnormal := by
        intro hTsn
        refine hns (Subgroup.IsSubnormal.trans le_sup_left ?_ hTsn)
        exact Subgroup.Normal.isSubnormal
          ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hTnorm)
      -- so induction applies to `T`, which lies in both `K` and `M`
      have hcardT : Nat.card S < Nat.card T := card_lt_card_of_lt hSlt
      have hcardTG : Nat.card T ≤ Nat.card G := Subgroup.card_le_card_group T
      obtain ⟨M', -, -, huniq⟩ := ih T (by omega) hTsub hTns
      rw [huniq K hK hTK, huniq M hM (hTnorm.trans hNM)]

/-- **Isaacs, Theorem 2.9** (Wielandt's zipper lemma).  If every proper subgroup of `G` containing
`S` contains it *subnormally*, but `S` is not subnormal in `G`, then `S` lies in a unique maximal
subgroup of `G`. -/
theorem exists_unique_coatom_of_not_isSubnormal [Finite G] {S : Subgroup G}
    (hsub : ∀ H : Subgroup G, S ≤ H → H ≠ ⊤ → (S.subgroupOf H).IsSubnormal)
    (hns : ¬ S.IsSubnormal) :
    ∃ M : Subgroup G, IsCoatom M ∧ S ≤ M ∧ ∀ K : Subgroup G, IsCoatom K → S ≤ K → K = M :=
  zipper_aux (Nat.card G) S (Nat.sub_le _ _) hsub hns

end PiGroups
