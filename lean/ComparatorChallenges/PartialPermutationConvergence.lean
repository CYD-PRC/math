import Mathlib
import OAI.Probability.BinarySweep.Model
import OAI.RepresentationTheory.PartialPermutation.Model

namespace OAI

/-!
# Partial-permutation convergence corollaries (family 238, gap G1)

The scope note `lean/docs/238.md` records for the partial-permutation
formalization: "The paper's asymptotic conclusion about the product of two
random permutations is outside this selected finite estimate." This challenge
states the excluded segment: the amplification proposition and the two
convergence corollaries.

The definitions are the repository's own: `BinarySweep/Model.lean` supplies
`convolution`/`convolutionPower`/`totalVariation`/`uniformLaw`/`realSign`
(typeclass-generic), and `RepresentationTheory/PartialPermutation/Model.lean`
supplies `mass`/`complexFourier`/`IsUnitary`/`blockSubgroup`. No parallel
copies are made (the G8 lesson: self-built parallel types cannot re-attach
to the tree).

Verbatim paper text (from "From partial permutation information to Fourier
bounds"; the extracted text mangles displayed formulas across lines —
reconstructions are marked [reconstructed]):

- Prop 2.5 (Fourier amplification), paper L449–458:
  "Let µn be probabilities on Sn with µ̂n(sgn) = o(1). Suppose either fn is a
  nonnegative subprobability with fn ≤ µn and mass tending to one, or fn is a
  probability with ∥fn − µn∥TV = o(1). If, uniformly for every irreducible of
  degree D > 1, ∥f̂n∥op ≤ AD^{−β}, where A, β > 0 are fixed, then
  ∥µ∗r_n − U∥TV → 0 for every fixed integer r with 2 − 2rβ < 0. If instead
  ∥f̂n∥²HS ≤ AD^{−γ}, the sufficient condition is 1 − rγ < 0."
  (The two forms below are the operator form and the Hilbert–Schmidt form;
  both are stated in the mass-tending-to-one variant that Corollary 3.3
  uses.)
- Cor 3.3, paper L618–625 (extraction interleaves the display lines):
  "Let n → ∞ through multiples of eight. Suppose probabilities µn on Sn have
  sign mean o(1) and" [L618–619] "E_{|M|=n/8} ∥µ_{n,H_M} − U_{G/H_M}∥TV = o(1)."
  [L625, intact line]  "Then ∥µ∗4_n − U_G∥TV → 0."  [reconstructed by splicing
  L621 "Then ∥µ∗4" with L623 "n − UG∥TV → 0."]
- Cor 3.6, paper L774–776:
  "Under the hypotheses of Corollary 3.3, ∥µ∗2_n − U_G∥TV → 0."
  [L774 intact; conclusion spliced from L775 "∥µ∗2" + L776 "n − UG∥TV → 0."]
  (Prop 2.5's own display is likewise split: its conclusion "∥µ∗r_n − U∥TV → 0"
  is spliced from L455 + L460, with the HS variant's clause at L456–458.)

Only the four terminal theorems carry `sorry`; every definition above them is
meant to typecheck, and `eightDivisible_neBot` is proved (the filter is
nontrivial — the asymptotic statements are not vacuous).
-/

noncomputable section
open scoped BigOperators
open Filter

namespace PartialPermutation

/-- The left-coset mass law of `μ` along `H`, as a function on `G ⧸ H`
(the quotient by `QuotientGroup.leftRel H`; classes are the left cosets
`gH`). This is the paper's `µ_H` on `G/H`. -/
def cosetMassLaw {G : Type*} [Group G] [Fintype G] (μ : G → ℝ) (H : Subgroup G) :
    G ⧸ H → ℝ := by
  classical
  refine Quotient.lift (fun g => ∑ h : H, μ (g * h)) ?_
  intro a b hab
  have hab2 : a⁻¹ * b ∈ H := (QuotientGroup.leftRel_apply).mp hab
  refine Fintype.sum_equiv (Equiv.mulLeft ⟨(a⁻¹ * b)⁻¹, inv_mem hab2⟩) _ _ ?_
  intro h
  apply congrArg μ
  show (a : G) * (h : G) = b * (((⟨(a⁻¹ * b)⁻¹, inv_mem hab2⟩ : H) * h : H) : G)
  simp only [Subgroup.coe_mul]
  group

/-- The uniform average, over the `n/8`-subsets `M` of `Fin n`, of the
marginal TV of `μ n` along the block subgroup `Sym(M)` (the permutations
fixing the complement of `M` pointwise — the repository's `blockSubgroup`). -/
def avgMarginalTV (μ : (n : ℕ) → Equiv.Perm (Fin n) → ℝ) (n : ℕ) : ℝ := by
  classical
  exact (∑ M : {M : Finset (Fin n) // M.card = n / 8},
      BinaryCoordinateSweeps.totalVariation
        (cosetMassLaw (μ n) (blockSubgroup (M.1 : Set (Fin n))))
        (BinaryCoordinateSweeps.uniformLaw _)) /
    (Fintype.card {M : Finset (Fin n) // M.card = n / 8} : ℝ)

/-- The filter `n → ∞` through multiples of eight (the paper's time
convention for the convergence corollaries). -/
def eightDivisible : Filter ℕ := Filter.atTop ⊓ Filter.principal {n | 8 ∣ n}

/-- The filter is nontrivial — the convergence statements are not vacuous. -/
theorem eightDivisible_neBot : eightDivisible.NeBot := by
  rw [eightDivisible, Filter.inf_principal_neBot_iff]
  intro U hU
  obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp hU
  exact ⟨8 * N, hN (8 * N) (by omega), dvd_mul_right 8 N⟩

/-- Proposition 2.5, operator-norm form: a uniform power saving of the
Fourier transform at every irreducible of degree > 1 amplifies to
total-variation convergence after `r` convolutions whenever
`2 − 2rβ < 0`. -/
theorem fourier_amplification_operator
    (A β : ℝ) (hA : 0 < A) (hβ : 0 < β) (r : ℕ)
    (hr : (2 : ℝ) - 2 * (r : ℝ) * β < 0)
    (μ f : (n : ℕ) → Equiv.Perm (Fin n) → ℝ)
    (hμ : ∀ n, (∀ g, 0 ≤ μ n g) ∧ mass (μ n) = 1)
    (hf : ∀ n, (∀ g, 0 ≤ f n g) ∧ ∀ g, f n g ≤ μ n g)
    (hmass : Tendsto (fun n => mass (f n)) Filter.atTop (nhds 1))
    (hsign : Tendsto (fun n => mass (fun g => μ n g *
      BinaryCoordinateSweeps.realSign g)) Filter.atTop (nhds 0))
    (hop : ∀ n, ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V),
        Representation.IsIrreducible ρ → IsUnitary ρ → 1 < Module.finrank ℂ V →
        ‖LinearMap.toContinuousLinearMap (complexFourier ρ (fun g => (f n g : ℂ)))‖
          ≤ A * (Module.finrank ℂ V : ℝ) ^ (-β)) :
    Tendsto (fun n => BinaryCoordinateSweeps.totalVariation
        (BinaryCoordinateSweeps.convolutionPower (μ n) r)
        (BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n))))
      Filter.atTop (nhds 0) := by
  sorry

/-- Proposition 2.5, Hilbert–Schmidt form: the same conclusion from a squared
Hilbert–Schmidt bound `A·D^{−γ}` whenever `1 − rγ < 0`. -/
theorem fourier_amplification_hs
    (A γ : ℝ) (hA : 0 < A) (hγ : 0 < γ) (r : ℕ)
    (hr : (1 : ℝ) - (r : ℝ) * γ < 0)
    (μ f : (n : ℕ) → Equiv.Perm (Fin n) → ℝ)
    (hμ : ∀ n, (∀ g, 0 ≤ μ n g) ∧ mass (μ n) = 1)
    (hf : ∀ n, (∀ g, 0 ≤ f n g) ∧ ∀ g, f n g ≤ μ n g)
    (hmass : Tendsto (fun n => mass (f n)) Filter.atTop (nhds 1))
    (hsign : Tendsto (fun n => mass (fun g => μ n g *
      BinaryCoordinateSweeps.realSign g)) Filter.atTop (nhds 0))
    (hhs : ∀ n, ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V),
        Representation.IsIrreducible ρ → IsUnitary ρ → 1 < Module.finrank ℂ V →
        hsNormSq (complexFourier ρ (fun g => (f n g : ℂ)))
          ≤ A * (Module.finrank ℂ V : ℝ) ^ (-γ)) :
    Tendsto (fun n => BinaryCoordinateSweeps.totalVariation
        (BinaryCoordinateSweeps.convolutionPower (μ n) r)
        (BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n))))
      Filter.atTop (nhds 0) := by
  sorry

/-- Corollary 3.3: four convolutions by the orbit argument. -/
theorem four_convolution_convergence
    (μ : (n : ℕ) → Equiv.Perm (Fin n) → ℝ)
    (hμ : ∀ n, 8 ∣ n → (∀ g, 0 ≤ μ n g) ∧ mass (μ n) = 1)
    (hsign : Tendsto (fun n => mass (fun g => μ n g *
      BinaryCoordinateSweeps.realSign g)) eightDivisible (nhds 0))
    (hmarg : Tendsto (fun n => avgMarginalTV μ n) eightDivisible (nhds 0)) :
    Tendsto (fun n => BinaryCoordinateSweeps.totalVariation
        (BinaryCoordinateSweeps.convolutionPower (μ n) 4)
        (BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n))))
      eightDivisible (nhds 0) := by
  sorry

/-- Corollary 3.6: two convolutions from eight complements. -/
theorem two_convolution_convergence
    (μ : (n : ℕ) → Equiv.Perm (Fin n) → ℝ)
    (hμ : ∀ n, 8 ∣ n → (∀ g, 0 ≤ μ n g) ∧ mass (μ n) = 1)
    (hsign : Tendsto (fun n => mass (fun g => μ n g *
      BinaryCoordinateSweeps.realSign g)) eightDivisible (nhds 0))
    (hmarg : Tendsto (fun n => avgMarginalTV μ n) eightDivisible (nhds 0)) :
    Tendsto (fun n => BinaryCoordinateSweeps.totalVariation
        (BinaryCoordinateSweeps.convolutionPower (μ n) 2)
        (BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n))))
      eightDivisible (nhds 0) := by
  sorry

end PartialPermutation
end

end OAI
