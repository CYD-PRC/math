import Mathlib

namespace OAI

/-!
# The Thorp mixing consequence of the four-row moment recursion

Companion to `ComparatorChallenges/FourRowPermanent.lean`. That challenge states
the robust four-row permanent inequality (Theorem 1.1 of "A strict four-row
permanent inequality and permutation moments", 2026-09-26). The paper's scope
note in `lean/docs/238.md` records that the Thorp mixing consequence is *outside*
the selected statement. This file states the missing segment:

- `FixedMomentDegreeSaving` — Theorem 1.2: one fixed even moment of the sweep's
  Fourier transform saves a power of the representation dimension,
  `D · Tr B^r ≤ D^{1-η}` with absolute `r`, `η`;
- `OptimalOrderThorpMixing` — the consequence the paper's title claims:
  an absolute number of sweeps brings the full permutation law to uniform in
  total variation, uniformly over starting decks, *and* the matching lower order
  `2d − O(1)` physical shuffles from the support estimate (equation (3)).

The shuffle-side machinery (slots, coordinate layers, sweep laws, total
variation, uniform laws, convolution) follows the conventions of
`ComparatorChallenges/BinarySweep.lean`; the statement-side additions are the
Fourier operator of the sweep law at an irreducible unitary representation and
the physical-step law with its coordinate rotation.

Only the two terminal theorems carry `sorry`; every definition above them is
meant to typecheck.
-/

noncomputable section
open scoped BigOperators

namespace ThorpFourRow

/-- The positions of a binary deck of dimension `d`. -/
abbrev Slot (d : ℕ) := Fin d → Bool

/-- Independent switches on the edges parallel to one coordinate. -/
def coordinateLayer (d : ℕ) (j : Fin d)
    (c : (({i : Fin d // i ≠ j} → Bool) → Bool)) : Equiv.Perm (Slot d) :=
  let e := Equiv.piSplitAt j (fun _ : Fin d => Bool)
  let sw : Equiv.Perm (Bool × ({i : Fin d // i ≠ j} → Bool)) :=
    { toFun := fun x => (x.1 ^^ c x.2, x.2)
      invFun := fun x => (x.1 ^^ c x.2, x.2)
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  e.trans (sw.trans e.symm)

/-- The coin strings of one full coordinate sweep. -/
abbrev SweepCoins (d : ℕ) :=
  (j : Fin d) → ({i : Fin d // i ≠ j} → Bool) → Bool

/-- The coordinate layers are applied in increasing coordinate order. -/
def binarySweep (d : ℕ) (c : SweepCoins d) : Equiv.Perm (Slot d) :=
  (List.ofFn (fun j => coordinateLayer d j (c j))).reverse.prod

/-- The law of a uniform random point of `Ω` pushed forward along `f`. -/
def finiteLaw {Ω G : Type*} [Fintype Ω] [Fintype G] (f : Ω → G) (g : G) : ℝ := by
  classical
  exact ∑ ω, if f ω = g then (Fintype.card Ω : ℝ)⁻¹ else 0

/-- Half the unnormalized sum of absolute probability-mass differences. -/
def totalVariation {G : Type*} [Fintype G] (p q : G → ℝ) : ℝ :=
  (1 / ((2 : ℕ) : ℝ)) * ∑ g, |p g - q g|

/-- The uniform law on a finite type. -/
def uniformLaw (G : Type*) [Fintype G] : G → ℝ :=
  fun _ => (Fintype.card G : ℝ)⁻¹

/-- The law of one sweep on a dyadic deck. -/
def binaryLaw (d : ℕ) : Equiv.Perm (Slot d) → ℝ :=
  finiteLaw (binarySweep d)

section FiniteLaws
variable {G : Type*} [Fintype G] [Group G]

/-- Convolution of finite-group laws. -/
def convolution (p q : G → ℝ) (g : G) : ℝ := ∑ x, p x * q (x⁻¹ * g)

/-- The point mass at the identity. -/
def pointMassOne (g : G) : ℝ := by
  classical
  exact if g = 1 then 1 else 0

/-- The law of independent repetitions, with the empty product at the identity. -/
def convolutionPower (p : G → ℝ) : ℕ → G → ℝ
  | 0 => pointMassOne
  | n + 1 => convolution p (convolutionPower p n)

/-- The law of `t` independent forward sweeps. -/
def sweepLaw (d t : ℕ) : Equiv.Perm (Slot d) → ℝ :=
  convolutionPower (binaryLaw d) t

end FiniteLaws

/-- Representation spaces are finite-dimensional complex Hilbert spaces. -/
abbrev RepSpace (D : ℕ) := EuclideanSpace ℂ (Fin D)

/-- A representation is unitary when it preserves the norm pointwise. -/
def IsUnitaryRep {G : Type*} [Monoid G]
    {D : ℕ} (ρ : Representation ℂ G (RepSpace D)) : Prop :=
  ∀ g x, ‖ρ g x‖ = ‖x‖

/-- The Fourier transform of a finite-group law at a representation:
the average operator `∑ p(g) ρ(g)`. -/
def fourierAt {G : Type*} [Fintype G] [Monoid G] {D : ℕ}
    (p : G → ℝ) (ρ : Representation ℂ G (RepSpace D)) :
    RepSpace D →L[ℂ] RepSpace D :=
  LinearMap.toContinuousLinearMap (∑ g, (p g : ℂ) • ρ g)

/-- The sweep's second-moment operator `B = T T*`, on the representation where
`T` is the sweep law's Fourier transform. -/
def sweepSecondMoment {d D : ℕ} (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D)) :
    RepSpace D →L[ℂ] RepSpace D :=
  let T := fourierAt (convolutionPower (binaryLaw d) 1) ρ
  T.comp (ContinuousLinearMap.adjoint T)

/-- The trace of a positive power of the sweep's second-moment operator. -/
def sweepMomentTrace {d D : ℕ} (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D))
    (r : ℕ) : ℝ := by
  classical
  let B := sweepSecondMoment ρ
  let Bm : Matrix (Fin D) (Fin D) ℂ :=
    Matrix.of (fun i j => (B ^ r) (EuclideanSpace.single i 1) j)
  exact (Matrix.trace Bm).re

/-- Theorem 1.2: a fixed moment with a degree saving.

There exist an even integer `r ≥ 2` and `η > 0`, independent of `N`, such that
for every dyadic deck size and every irreducible unitary representation,
`D · Tr B^r ≤ D^{1-η}`. The paper quantifies over partitions `λ ⊢ N`; the
quantifier here ranges over irreducible unitary representations directly, which
is the content the classification supplies. -/
def FixedMomentDegreeSaving : Prop :=
  ∃ r : ℕ, 2 ≤ r ∧ Even r ∧ ∃ η : ℝ, 0 < η ∧ ∀ d : ℕ, 0 < d →
    ∀ D : ℕ, ∀ ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D),
      ρ.IsIrreducible → IsUnitaryRep ρ →
      (D : ℝ) * sweepMomentTrace ρ r ≤ (D : ℝ) ^ (1 - η)

section PhysicalSteps
variable {d : ℕ}

/-- The cyclic rotation of the coordinates, `R(x₀,…,x_{d-1}) = (x₁,…,x_{d-1},x₀)`. -/
def rotateCoords (d : ℕ) : Equiv.Perm (Slot d) :=
  Equiv.arrowCongr (finRotate d) (Equiv.refl Bool)

/-- One physical Thorp step: independent fair switches along coordinate `j`,
followed by the cyclic rotation of the coordinates. -/
def physicalStep (d : ℕ) (j : Fin d)
    (c : (({i : Fin d // i ≠ j} → Bool) → Bool)) : Equiv.Perm (Slot d) :=
  (rotateCoords d).trans (coordinateLayer d j c)

/-- The law of one physical step at coordinate `j`. -/
def physicalStepLaw (d : ℕ) (j : Fin d) : Equiv.Perm (Slot d) → ℝ :=
  finiteLaw (physicalStep d j)

/-- The law of `t` physical steps, the coordinate rotating cyclically. -/
def physicalLaw (d : ℕ) (hd : 0 < d) (t : ℕ) : Equiv.Perm (Slot d) → ℝ :=
  (List.range t).foldl
    (fun law k => convolution law (physicalStepLaw d ⟨k % d, Nat.mod_lt _ hd⟩))
    pointMassOne

end PhysicalSteps

/-- The paper's mixing consequence, at optimal order.

Upper bound: an absolute number of sweeps brings the full permutation law to
uniform in total variation, uniformly over deterministic starting decks.
Lower order (equation (3)): after `t` physical shuffles only `2^{t·2^{d-1}}`
decks are reachable, so the distance to uniform stays at least
`1 − 2^{t·2^{d-1}} / N!`. -/
def OptimalOrderThorpMixing : Prop :=
  (∃ q : ℕ, ∀ ε : ℝ, 0 < ε → ∃ d₀ : ℕ, ∀ d ≥ d₀,
    ∀ τ : Equiv.Perm (Slot d),
      totalVariation (fun g => convolutionPower (binaryLaw d) q (g * τ⁻¹))
        (uniformLaw (Equiv.Perm (Slot d))) ≤ ε)
  ∧ (∀ d : ℕ, ∀ hd : 0 < d, ∀ t : ℕ,
      totalVariation (physicalLaw d hd t) (uniformLaw (Equiv.Perm (Slot d))) ≥
        1 - (2 : ℝ) ^ (t * 2 ^ (d - 1)) / (Nat.factorial (2 ^ d) : ℝ))

end ThorpFourRow
end

open scoped BigOperators

/-- The segment `lean/docs/238.md` excludes: from the strict four-row permanent
inequality to the Thorp mixing consequence. -/
theorem four_row_moment_mixing_consequence :
    ThorpFourRow.FixedMomentDegreeSaving ∧ ThorpFourRow.OptimalOrderThorpMixing := by
  sorry

end OAI
