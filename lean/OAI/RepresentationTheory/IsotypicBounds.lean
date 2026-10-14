import Mathlib

open scoped MonoidAlgebra

namespace OAI

namespace IsotypicBounds

open Representation

variable {G : Type*} [Group G] [Fintype G]

/-- Precomposition with a representation equivalence is a linear equivalence on
intertwining-map spaces. -/
def homCongrLeft {V W X : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup X]
    [Module ℂ V] [Module ℂ W] [Module ℂ X]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G X}
    (e : Representation.Equiv ρ σ) :
    Representation.IntertwiningMap ρ τ ≃ₗ[ℂ] Representation.IntertwiningMap σ τ where
  toFun f := f.comp e.symm.toIntertwiningMap
  map_add' f g := by
    apply Representation.IntertwiningMap.ext
    simp [Representation.IntertwiningMap.comp_add]
  map_smul' c f := by
    apply Representation.IntertwiningMap.ext
    simp [Representation.IntertwiningMap.smul_comp]
  invFun f := f.comp e.toIntertwiningMap
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    simp
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    simp

/-- Intertwining maps into a product representation split as a product. -/
noncomputable def homProdCongr {V W X : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup X]
    [Module ℂ V] [Module ℂ W] [Module ℂ X]
    {σ : Representation ℂ G V} {τ₁ : Representation ℂ G W} {τ₂ : Representation ℂ G X} :
    Representation.IntertwiningMap σ (τ₁.prod τ₂) ≃ₗ[ℂ]
      (Representation.IntertwiningMap σ τ₁ × Representation.IntertwiningMap σ τ₂) where
  toFun h := ((IntertwiningMap.fst ℂ τ₁ τ₂).comp h, (IntertwiningMap.snd ℂ τ₁ τ₂).comp h)
  map_add' f g := by
    apply Prod.ext
    · apply Representation.IntertwiningMap.ext
      simp [Representation.IntertwiningMap.add_comp]
    · apply Representation.IntertwiningMap.ext
      simp [Representation.IntertwiningMap.add_comp]
  map_smul' c f := by
    apply Prod.ext
    · apply Representation.IntertwiningMap.ext
      simp [Representation.IntertwiningMap.comp_smul]
    · apply Representation.IntertwiningMap.ext
      simp [Representation.IntertwiningMap.comp_smul]
  invFun fg := fg.1.prod fg.2
  left_inv h := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    simp [IntertwiningMap.prod]
  right_inv fg := by
    apply Prod.ext
    · simp
    · simp

/-- Two complementary subrepresentations identify the ambient representation with
their product. -/
noncomputable def repEquivOfIsCompl {W : Type*} [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ G W} (S Q : Subrepresentation τ) (h : IsCompl S Q) :
    Representation.Equiv (S.toRepresentation.prod Q.toRepresentation) τ := by
  have hcompl : IsCompl S.toSubmodule Q.toSubmodule := by
    constructor
    · rw [disjoint_iff, ← Subrepresentation.toSubmodule_inf, disjoint_iff.mp h.1]
      rfl
    · rw [codisjoint_iff, ← Subrepresentation.toSubmodule_sup, codisjoint_iff.mp h.2]
      rfl
  apply Representation.Equiv.mk (Submodule.prodEquivOfIsCompl S.toSubmodule Q.toSubmodule hcompl)
  intro g
  apply LinearMap.ext
  rintro ⟨x, y⟩
  simp [Representation.prod, Subrepresentation.toRepresentation,
    LinearMap.restrict_apply, map_add]

/-- An injective intertwiner is an equivalence with its range representation. -/
noncomputable def rangeEquivOfInjective {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℂ V] [Module ℂ W]
    {σ : Representation ℂ G V} {τ : Representation ℂ G W}
    (f : Representation.IntertwiningMap σ τ) (hf : Function.Injective f) :
    Representation.Equiv σ f.range.toRepresentation := by
  have hbij : Function.Bijective f.toLinearMap.rangeRestrict := by
    constructor
    · intro x y h
      exact hf (Subtype.ext_iff.mp h)
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, by apply Subtype.ext; exact hx⟩
  apply Representation.Equiv.mk (LinearEquiv.ofBijective f.toLinearMap.rangeRestrict hbij)
  intro g
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (f.isIntertwining' g) x

/-- Postcomposition with a representation equivalence is a linear equivalence on
intertwining-map spaces (target-side transport). -/
noncomputable def homCongrTarget {V W X : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup X]
    [Module ℂ V] [Module ℂ W] [Module ℂ X]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G X}
    (e : Representation.Equiv ρ σ) :
    Representation.IntertwiningMap τ ρ ≃ₗ[ℂ] Representation.IntertwiningMap τ σ where
  toFun g := (e.toIntertwiningMap).comp g
  map_add' f g := by
    apply Representation.IntertwiningMap.ext
    simp [Representation.IntertwiningMap.add_comp]
  map_smul' c f := by
    apply Representation.IntertwiningMap.ext
    simp [Representation.IntertwiningMap.comp_smul]
  invFun g := (e.symm.toIntertwiningMap).comp g
  left_inv g := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    simp
  right_inv g := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    simp

/-- ML-1: for an irreducible `σ`, the multiplicity of `σ` in any finite-dimensional `τ`
satisfies `multiplicity · finrank σ ≤ finrank τ`. The proof is by strong induction on
`finrank τ`: split off one nonzero intertwiner with a Maschke complement and compute
dimensions over the direct sum decomposition. -/
theorem finrank_intertwiningMap_mul_finrank_le {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (σ : Representation ℂ G V) [σ.IsIrreducible] :
    ∀ n : ℕ, ∀ {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (τ : Representation ℂ G W), Module.finrank ℂ W = n →
      Module.finrank ℂ (Representation.IntertwiningMap σ τ) * Module.finrank ℂ V ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W _ _ _ τ hn
    by_cases hc : Module.finrank ℂ (Representation.IntertwiningMap σ τ) = 0
    · rw [hc, zero_mul]
      exact Nat.zero_le n
    · obtain ⟨f, hf⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℂ)
        (M := Representation.IntertwiningMap σ τ)).mp (Nat.pos_of_ne_zero hc)
      have hinj : Function.Injective f := by
        rcases Representation.IsIrreducible.injective_or_eq_zero f with h | h
        · exact h
        · exact absurd h hf
      obtain ⟨Q, hQ⟩ := exists_isCompl f.range
      have hdim : Module.finrank ℂ (Representation.IntertwiningMap σ τ) =
          1 + Module.finrank ℂ (Representation.IntertwiningMap σ Q.toRepresentation) := by
        rw [(homCongrTarget (repEquivOfIsCompl f.range Q hQ).symm).finrank_eq,
          homProdCongr.finrank_eq, Module.finrank_prod]
        have h1 : Module.finrank ℂ (Representation.IntertwiningMap σ f.range.toRepresentation) = 1 := by
          rw [← (homCongrTarget (rangeEquivOfInjective f hinj)).finrank_eq]
          apply Representation.IsIrreducible.finrank_intertwiningMap_self
        rw [h1]
      have hcompl : IsCompl f.range.toSubmodule Q.toSubmodule := by
        constructor
        · rw [disjoint_iff, ← Subrepresentation.toSubmodule_inf, disjoint_iff.mp hQ.1]
          rfl
        · rw [codisjoint_iff, ← Subrepresentation.toSubmodule_sup, codisjoint_iff.mp hQ.2]
          rfl
      have hdecomp : Module.finrank ℂ W = Module.finrank ℂ f.range.toSubmodule +
          Module.finrank ℂ Q.toSubmodule := by
        rw [← (Submodule.prodEquivOfIsCompl f.range.toSubmodule Q.toSubmodule hcompl).finrank_eq]
        exact Module.finrank_prod
      have hr : Module.finrank ℂ f.range.toSubmodule = Module.finrank ℂ V :=
        (rangeEquivOfInjective f hinj).toLinearEquiv.finrank_eq.symm
      have hQlt : Module.finrank ℂ Q.toSubmodule < n := by
        have hV : Nontrivial V := IsSimpleModule.nontrivial (R := MonoidAlgebra ℂ G) (M := σ.asModule)
        have hVpos : 0 < Module.finrank ℂ V := Module.finrank_pos_iff.mpr hV
        rw [← hn, hdecomp, hr]
        exact Nat.lt_add_of_pos_left hVpos
      calc Module.finrank ℂ (Representation.IntertwiningMap σ τ) * Module.finrank ℂ V
          = (1 + Module.finrank ℂ (Representation.IntertwiningMap σ Q.toRepresentation)) *
            Module.finrank ℂ V := by rw [hdim]
        _ = Module.finrank ℂ V + Module.finrank ℂ (Representation.IntertwiningMap σ Q.toRepresentation) *
            Module.finrank ℂ V := by rw [add_mul, one_mul]
        _ ≤ Module.finrank ℂ V + Module.finrank ℂ Q.toSubmodule :=
            Nat.add_le_add_left (ih _ hQlt Q.toRepresentation rfl) _
        _ = Module.finrank ℂ W := by rw [← hr, ← hdecomp]
        _ = n := hn

end IsotypicBounds

end OAI
