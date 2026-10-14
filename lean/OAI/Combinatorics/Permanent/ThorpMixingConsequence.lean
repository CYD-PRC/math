import Mathlib
import OAI.Probability.BinarySweep.Model
import OAI.Probability.BinarySweep.Processes.Basic
import OAI.Combinatorics.Permanent.LawBridge
import OAI.Combinatorics.Permanent.RepNormBridge
import OAI.Probability.CubeShuffle.WeightedModel
import OAI.Probability.CubeShuffle.WeightedMoments
import OAI.Probability.BinarySweep.Mixing.BinaryMixingBounds

/-!
# The Thorp mixing consequence of the four-row moment recursion (solution module)

Solution module for `ComparatorChallenges/FourRowMixingConsequence.lean`
(family 238, gap G8). The `ThorpFourRow` definitions below are verbatim copies
of the challenge file's, per the comparator convention (the two environments
are loaded separately; the terminal theorem's statement must match the
challenge's over these copies).

**Divergence note (ruling G-1).** The `physicalLaw` below is NOT the
repository's `BinarySweep/Processes/Basic.physicalLaw`: this copy is the
foldl-convolution over `Slot d` with the rotating coordinate `k % d`, while the
repository's is the finite pullback law of `physicalHistory` over
`Slot (d + 1)`. They are different formalizations of the physical shuffle; the
lower bound (paper's equation (3)) is proved on this copy alone and needs no
bridge (ruling G-2). The upper bound consumes only the sweep side
(`binaryLaw`/`sweepLaw`), which bridges to the repository by `rfl`.
-/

namespace OAI

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

/-! ## Bridges to the repository objects

The copies above coincide with `BinarySweep/Model.lean`'s definitions
definitionally (the bodies are identical). The bridges are stated pointwise:
a bare `f = g` between constants whose signatures carry instance-implicit
binders does not elaborate (the binders become metavariables and typeclass
resolution gets stuck), so each bridge is quantified over the explicit
arguments. `fourierAt` is the repository's `averageOperator` under its
challenge-side name. There is deliberately no bridge for `physicalLaw`
(see the header). -/

theorem ThorpFourRow.coordinateLayer_eq (d : ℕ) (j : Fin d)
    (c : ({i : Fin d // i ≠ j} → Bool) → Bool) :
    ThorpFourRow.coordinateLayer d j c = BinaryCoordinateSweeps.coordinateLayer d j c := rfl

theorem ThorpFourRow.binarySweep_eq (d : ℕ) (c : ThorpFourRow.SweepCoins d) :
    ThorpFourRow.binarySweep d c = BinaryCoordinateSweeps.binarySweep d c := rfl

theorem ThorpFourRow.finiteLaw_eq {Ω G : Type*} [Fintype Ω] [Fintype G] (f : Ω → G) (g : G) :
    ThorpFourRow.finiteLaw f g = BinaryCoordinateSweeps.finiteLaw f g := rfl

theorem ThorpFourRow.totalVariation_eq {G : Type*} [Fintype G] (p q : G → ℝ) :
    ThorpFourRow.totalVariation p q = BinaryCoordinateSweeps.totalVariation p q := rfl

theorem ThorpFourRow.uniformLaw_eq (G : Type*) [Fintype G] :
    ThorpFourRow.uniformLaw G = BinaryCoordinateSweeps.uniformLaw G := rfl

theorem ThorpFourRow.convolution_eq {G : Type*} [Fintype G] [Group G] (p q : G → ℝ) (g : G) :
    ThorpFourRow.convolution p q g = BinaryCoordinateSweeps.convolution p q g := rfl

theorem ThorpFourRow.pointMassOne_eq {G : Type*} [Fintype G] [Group G] (g : G) :
    ThorpFourRow.pointMassOne g = BinaryCoordinateSweeps.pointMassOne g := rfl

theorem ThorpFourRow.convolutionPower_eq {G : Type*} [Fintype G] [Group G] (p : G → ℝ) (t : ℕ)
    (g : G) :
    ThorpFourRow.convolutionPower p t g = BinaryCoordinateSweeps.convolutionPower p t g := by
  induction t generalizing g with
  | zero => rfl
  | succ t ih =>
    show ThorpFourRow.convolution p (ThorpFourRow.convolutionPower p t) g =
      BinaryCoordinateSweeps.convolution p (BinaryCoordinateSweeps.convolutionPower p t) g
    rw [funext ih]
    rfl

theorem ThorpFourRow.binaryLaw_eq (d : ℕ) (g : Equiv.Perm (Slot d)) :
    ThorpFourRow.binaryLaw d g = BinaryCoordinateSweeps.binaryLaw d g := rfl

/-- The sweep laws coincide as functions (assembled from the pointwise
bridges). -/
theorem ThorpFourRow.sweepLaw_eq (d t : ℕ) (g : Equiv.Perm (Slot d)) :
    ThorpFourRow.sweepLaw d t g = BinaryCoordinateSweeps.sweepLaw d t g := by
  show ThorpFourRow.convolutionPower (ThorpFourRow.binaryLaw d) t g =
    BinaryCoordinateSweeps.convolutionPower (BinaryCoordinateSweeps.binaryLaw d) t g
  rw [ThorpFourRow.convolutionPower_eq,
    show ThorpFourRow.binaryLaw d = BinaryCoordinateSweeps.binaryLaw d from
      funext (ThorpFourRow.binaryLaw_eq d)]

/-- `fourierAt` is the repository's `averageOperator`. -/
theorem ThorpFourRow.fourierAt_eq {G : Type*} [Fintype G] [Monoid G] {D : ℕ}
    (p : G → ℝ) (ρ : Representation ℂ G (ThorpFourRow.RepSpace D)) :
    ThorpFourRow.fourierAt p ρ = BinaryCoordinateSweeps.averageOperator p ρ := rfl

/-! ## Slice G8-β: the support lower bound (paper's equation (3))

After `t` physical steps only `2^{t·2^{d-1}}` decks are reachable: each step's
law is the pushforward of the uniform law on `2^{2^{d-1}}` coins, convolution
multiplies supports, and a probability law putting mass one on a set `S` stays
at TV-distance `≥ 1 − |S|/N!` from uniform. All over the challenge's own
`ThorpFourRow` definitions (ruling G-2); no use of the repository's
`physicalHistory`. The counting claim is proved, not quoted (ruling G-3). -/

namespace ThorpFourRow

/-- The support of a law, as a finset. -/
noncomputable def lawSupport {G : Type*} [Fintype G] (p : G → ℝ) : Finset G := by
  classical
  exact Finset.univ.filter (fun g => p g ≠ 0)

lemma mem_lawSupport {G : Type*} [Fintype G] (p : G → ℝ) (g : G) :
    g ∈ lawSupport p ↔ p g ≠ 0 := by
  classical
  show g ∈ Finset.univ.filter (fun g => p g ≠ 0) ↔ p g ≠ 0
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ _)

/-- The support of a pushforward law is contained in the image. -/
lemma lawSupport_finiteLaw_subset {Ω G : Type*} [Fintype Ω] [Fintype G] [Nonempty Ω]
    [DecidableEq G]
    (f : Ω → G) :
    lawSupport (finiteLaw f) ⊆ Finset.univ.image f := by
  classical
  intro g hg
  rw [mem_lawSupport] at hg
  by_contra hcon
  apply hg
  unfold finiteLaw
  apply Finset.sum_eq_zero
  intro ω _
  split_ifs with hfg
  · exact absurd (Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, hfg⟩) hcon
  · rfl

lemma lawSupport_finiteLaw_card_le {Ω G : Type*} [Fintype Ω] [Fintype G] [Nonempty Ω]
    [DecidableEq G]
    (f : Ω → G) :
    (lawSupport (finiteLaw f)).card ≤ Fintype.card Ω := by
  classical
  exact (Finset.card_le_card (lawSupport_finiteLaw_subset f)).trans
    (Finset.card_image_le.trans_eq Finset.card_univ)

/-- The coin space of one physical step has `2^{2^{d-1}}` points. -/
lemma card_coins (d : ℕ) (_hd : 0 < d) (j : Fin d) :
    Fintype.card (({i : Fin d // i ≠ j} → Bool) → Bool) = 2 ^ (2 ^ (d - 1)) := by
  classical
  have hsub : Fintype.card {i : Fin d // i ≠ j} = d - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq j]
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, hsub]

/-- One physical step's law has at most `2^{2^{d-1}}`-point support. -/
lemma lawSupport_stepLaw_le (d : ℕ) (hd : 0 < d) (j : Fin d) :
    (lawSupport (physicalStepLaw d j)).card ≤ 2 ^ (2 ^ (d - 1)) := by
  classical
  exact (lawSupport_finiteLaw_card_le (physicalStep d j)).trans_eq (card_coins d hd j)

/-- Convolution multiplies supports (up to the product image). -/
lemma lawSupport_convolution_le {G : Type*} [Fintype G] [Group G] [DecidableEq G] (p q : G → ℝ) :
    (lawSupport (convolution p q)).card ≤ (lawSupport p).card * (lawSupport q).card := by
  classical
  refine (Finset.card_le_card ?_).trans ((Finset.card_image_le
      (s := lawSupport p ×ˢ lawSupport q) (f := fun xy : G × G => xy.1 * xy.2)).trans_eq
    (Finset.card_product _ _))
  intro g hg
  rw [mem_lawSupport] at hg
  obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg
  obtain ⟨hpx, hqx⟩ := mul_ne_zero_iff.mp hx
  rw [Finset.mem_image]
  refine ⟨(x, x⁻¹ * g), ?_, ?_⟩
  · rw [Finset.mem_product, mem_lawSupport, mem_lawSupport]
    exact ⟨hpx, hqx⟩
  · show x * (x⁻¹ * g) = g
    exact mul_inv_cancel_left x g

/-- The support bound after `t` physical steps: at most `2^{t·2^{d-1}}`
reachable decks. -/
lemma lawSupport_physicalLaw_le (d : ℕ) (hd : 0 < d) (t : ℕ) :
    (lawSupport (physicalLaw d hd t)).card ≤ 2 ^ (t * 2 ^ (d - 1)) := by
  classical
  induction t with
  | zero =>
    show (lawSupport pointMassOne).card ≤ 2 ^ (0 * 2 ^ (d - 1))
    rw [Nat.zero_mul, pow_zero]
    refine (Finset.card_le_card ?_).trans
      (le_of_eq (Finset.card_singleton (1 : Equiv.Perm (Slot d))))
    intro g hg
    rw [mem_lawSupport] at hg
    rw [Finset.mem_singleton]
    by_contra hg1
    apply hg
    show pointMassOne g = 0
    unfold pointMassOne
    exact ite_eq_right hg1
  | succ t ih =>
    have hstep : physicalLaw d hd (t + 1) =
        convolution (physicalLaw d hd t) (physicalStepLaw d ⟨t % d, Nat.mod_lt _ hd⟩) := by
      unfold physicalLaw
      rw [List.range_succ, List.foldl_concat]
    rw [hstep]
    refine (lawSupport_convolution_le _ _).trans ?_
    calc (lawSupport (physicalLaw d hd t)).card *
            (lawSupport (physicalStepLaw d ⟨t % d, Nat.mod_lt _ hd⟩)).card
        ≤ (2 ^ (t * 2 ^ (d - 1))) * 2 ^ (2 ^ (d - 1)) :=
          mul_le_mul ih (lawSupport_stepLaw_le d hd _) (Nat.zero_le _) (Nat.zero_le _)
      _ = 2 ^ ((t + 1) * 2 ^ (d - 1)) := by
          rw [Nat.succ_mul, ← pow_add]

/-- The mass of a convolution is the product of the masses. -/
lemma mass_convolution {G : Type*} [Fintype G] [Group G] (p q : G → ℝ) :
    (∑ g : G, convolution p q g) = (∑ g, p g) * (∑ g, q g) := by
  classical
  show (∑ g, ∑ x, p x * q (x⁻¹ * g)) = (∑ x, p x) * ∑ x, q x
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum]
  apply congrArg (p x * ·)
  exact Equiv.sum_comp (Equiv.mulLeft x⁻¹) (fun g' => q g')

/-- The mass of the point mass at one is one. -/
lemma mass_pointMassOne {G : Type*} [Fintype G] [Group G] :
    (∑ g : G, pointMassOne g) = 1 := by
  classical
  show (∑ g : G, (if g = 1 then (1:ℝ) else 0)) = 1
  rw [Finset.sum_ite_eq' Finset.univ 1 (fun _ => (1:ℝ))]
  simp

/-- The mass of a pushforward of the uniform law is one. -/
lemma mass_finiteLaw {Ω G : Type*} [Fintype Ω] [Fintype G] [Nonempty Ω] (f : Ω → G) :
    (∑ g : G, finiteLaw f g) = 1 := by
  classical
  have hpt : ∀ g : G, finiteLaw f g = ((Finset.univ.filter (fun ω => f ω = g)).card : ℝ) *
      (Fintype.card Ω : ℝ)⁻¹ := by
    intro g
    show finiteLaw f g = _
    unfold finiteLaw
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  calc (∑ g : G, finiteLaw f g)
      = ∑ g : G, ((Finset.univ.filter (fun ω => f ω = g)).card : ℝ) *
          (Fintype.card Ω : ℝ)⁻¹ := Finset.sum_congr rfl (fun g _ => hpt g)
    _ = (∑ g : G, ((Finset.univ.filter (fun ω => f ω = g)).card : ℝ)) *
          (Fintype.card Ω : ℝ)⁻¹ := (Finset.sum_mul _ _ _).symm
    _ = (Fintype.card Ω : ℝ) * (Fintype.card Ω : ℝ)⁻¹ := by
        congr 1
        have h := Finset.card_eq_sum_card_fiberwise (t := (Finset.univ : Finset G))
          (s := (Finset.univ : Finset Ω)) (f := f) (fun ω _ => Finset.mem_univ (f ω))
        rw [Finset.card_univ] at h
        exact_mod_cast h.symm
    _ = 1 := mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- The physical law after any number of steps is a probability (mass one). -/
lemma mass_physicalLaw (d : ℕ) (hd : 0 < d) (t : ℕ) :
    (∑ g : Equiv.Perm (Slot d), physicalLaw d hd t g) = 1 := by
  classical
  induction t with
  | zero =>
    show (∑ g : Equiv.Perm (Slot d), pointMassOne g) = 1
    exact mass_pointMassOne
  | succ t ih =>
    have hstep : physicalLaw d hd (t + 1) =
        convolution (physicalLaw d hd t) (physicalStepLaw d ⟨t % d, Nat.mod_lt _ hd⟩) := by
      unfold physicalLaw
      rw [List.range_succ, List.foldl_concat]
    rw [hstep]
    show (∑ g : Equiv.Perm (Slot d), convolution _ _ g) = 1
    rw [mass_convolution, ih]
    show (1:ℝ) * (∑ g : Equiv.Perm (Slot d),
        finiteLaw (physicalStep d ⟨t % d, Nat.mod_lt _ hd⟩) g) = 1
    rw [mass_finiteLaw, mul_one]

/-- The physical law is pointwise nonnegative. -/
lemma physicalLaw_nonneg (d : ℕ) (hd : 0 < d) (t : ℕ) :
    ∀ g : Equiv.Perm (Slot d), 0 ≤ physicalLaw d hd t g := by
  classical
  induction t with
  | zero =>
    intro g
    show 0 ≤ pointMassOne g
    unfold pointMassOne
    split_ifs <;> norm_num
  | succ t ih =>
    have hstep : physicalLaw d hd (t + 1) =
        convolution (physicalLaw d hd t) (physicalStepLaw d ⟨t % d, Nat.mod_lt _ hd⟩) := by
      unfold physicalLaw
      rw [List.range_succ, List.foldl_concat]
    intro g
    rw [hstep]
    show 0 ≤ ∑ x, (physicalLaw d hd t) x * (physicalStepLaw d ⟨t % d, Nat.mod_lt _ hd⟩) (x⁻¹ * g)
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg (ih x)
    show 0 ≤ finiteLaw (physicalStep d ⟨t % d, Nat.mod_lt _ hd⟩) (x⁻¹ * g)
    unfold finiteLaw
    apply Finset.sum_nonneg
    intro ω _
    split_ifs <;> positivity

/-- A probability law putting mass one on a set `S` stays at TV-distance
`≥ 1 − |S|/|G|` from uniform. -/
lemma one_sub_card_support_le_tv {G : Type*} [Fintype G] [Nonempty G] (p : G → ℝ)
    (hm : (∑ g : G, p g) = 1) :
    1 - (lawSupport p).card / (Fintype.card G : ℝ) ≤
      totalVariation p (uniformLaw G) := by
  classical
  have hG0 : (0:ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  set S := lawSupport p with hS
  set c := (Fintype.card G : ℝ) with hc
  have hU : ∀ g : G, uniformLaw G g = c⁻¹ := fun g => rfl
  have hsc : (∑ g ∈ S, p g) = 1 := by
    rw [← hm]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hxS
    by_contra hne
    exact hxS (by rw [hS]; exact (mem_lawSupport p x).mpr hne)
  have hSbound : 1 - (S.card : ℝ) / c ≤ ∑ g ∈ S, |p g - uniformLaw G g| := by
    calc ∑ g ∈ S, |p g - uniformLaw G g|
        ≥ ∑ g ∈ S, (p g - c⁻¹) := by
          apply Finset.sum_le_sum
          intro g _
          rw [hU g]
          exact le_abs_self _
      _ = 1 - (S.card : ℝ) / c := by
          rw [Finset.sum_sub_distrib, hsc, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have hScbound : (∑ g ∈ Sᶜ, |p g - uniformLaw G g|) = (Sᶜ.card : ℝ) / c := by
    rw [div_eq_mul_inv, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro g hg
    rw [Finset.mem_compl] at hg
    have hpg : p g = 0 := by
      by_contra hne
      exact hg (by rw [hS]; exact (mem_lawSupport p g).mpr hne)
    rw [hU g, hpg, zero_sub, abs_neg, abs_of_pos (inv_pos.mpr hG0)]
  have hsum : (∑ g : G, |p g - uniformLaw G g|) =
      (∑ g ∈ S, |p g - uniformLaw G g|) + (∑ g ∈ Sᶜ, |p g - uniformLaw G g|) := by
    rw [← Finset.sum_add_sum_compl S]
  have hle : S.card ≤ Fintype.card G := by
    rw [hS]
    exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ
  have hcard : (Sᶜ.card : ℝ) = c - (S.card : ℝ) := by
    rw [Finset.card_compl, Nat.cast_sub hle, ← hc]
  have halg : (1:ℝ) - (S.card : ℝ) / c =
      (1 / ((2:ℕ):ℝ)) * ((1 - (S.card : ℝ) / c) + (Sᶜ.card : ℝ) / c) := by
    rw [hcard]
    field_simp [hG0.ne']
    ring
  unfold totalVariation
  rw [hsum, halg]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact add_le_add hSbound hScbound.ge

/-- Paper's equation (3): the support lower bound. After `t` physical steps
the distance to uniform is at least `1 − 2^{t·2^{d−1}}/N!`. -/
lemma physicalLaw_tv_ge (d : ℕ) (hd : 0 < d) (t : ℕ) :
    1 - (2 : ℝ) ^ (t * 2 ^ (d - 1)) / (Nat.factorial (2 ^ d) : ℝ) ≤
      totalVariation (physicalLaw d hd t) (uniformLaw (Equiv.Perm (Slot d))) := by
  classical
  have hbase := one_sub_card_support_le_tv (physicalLaw d hd t)
    (mass_physicalLaw d hd t)
  have hcard : (Fintype.card (Equiv.Perm (Slot d)) : ℝ) = (Nat.factorial (2 ^ d) : ℝ) := by
    have hslot : Fintype.card (Slot d) = 2 ^ d := by
      show Fintype.card (Fin d → Bool) = 2 ^ d
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [Fintype.card_perm, hslot]
  rw [← hcard]
  refine (sub_le_sub_left ?_ (1 : ℝ)).trans hbase
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast lawSupport_physicalLaw_le d hd t

end ThorpFourRow

/-! ## Slice G8-γa/γb: the moment trace — diagonal expansion and PSD bound -/

namespace ThorpFourRow

/-- The second-moment operator `T T*` is self-adjoint. -/
lemma isSelfAdjoint_sweepSecondMoment {d D : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D)) :
    IsSelfAdjoint (sweepSecondMoment ρ) := by
  classical
  rw [isSelfAdjoint_iff]
  unfold sweepSecondMoment
  simp only []
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

/-- The moment trace is the sum of the diagonal entries' real parts. -/
lemma sweepMomentTrace_eq_sum_re {d D : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D)) (r : ℕ) :
    sweepMomentTrace ρ r =
      ∑ i : Fin D, Complex.re (inner ℂ (EuclideanSpace.single i (1 : ℂ))
        (((sweepSecondMoment ρ)^r) (EuclideanSpace.single i (1 : ℂ)))) := by
  classical
  unfold sweepMomentTrace
  simp only []
  rw [show Matrix.trace (Matrix.of (fun i j => ((sweepSecondMoment ρ)^r)
        (EuclideanSpace.single i (1 : ℂ)) j)) =
      ∑ i : Fin D, ((sweepSecondMoment ρ)^r) (EuclideanSpace.single i (1 : ℂ)) i from rfl]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [EuclideanSpace.inner_single_left, map_one, one_mul]

/-- For `r = 2k`, each diagonal entry of `B^r` has real part a squared norm. -/
lemma sweepMomentTrace_entry {d D : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D)) {k : ℕ} (e : RepSpace D) :
    Complex.re (inner ℂ e (((sweepSecondMoment ρ)^(2 * k)) e)) =
      ‖((sweepSecondMoment ρ)^k) e‖^2 := by
  classical
  have hSA : IsSelfAdjoint (sweepSecondMoment ρ) := isSelfAdjoint_sweepSecondMoment ρ
  have hpow : (sweepSecondMoment ρ)^(2 * k) =
      star ((sweepSecondMoment ρ)^k) * (sweepSecondMoment ρ)^k := by
    rw [show (2:ℕ) * k = k + k from two_mul k, pow_add]
    rw [show star ((sweepSecondMoment ρ)^k) = (sweepSecondMoment ρ)^k from hSA.pow k]
  rw [hpow, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  show RCLike.re (inner ℂ (((sweepSecondMoment ρ)^k) e) (((sweepSecondMoment ρ)^k) e)) = _
  exact inner_self_eq_norm_sq _

/-- The moment trace of an even power `r ≥ 2` is at most `D · ‖B‖^r`. -/
lemma sweepMomentTrace_le {d D : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D)) {r : ℕ} (hr : Even r)
    (hr0 : 2 ≤ r) :
    sweepMomentTrace ρ r ≤ (D : ℝ) * ‖sweepSecondMoment ρ‖ ^ r := by
  classical
  obtain ⟨k, hk⟩ := hr
  have hr2 : r = 2 * k := by rw [hk, two_mul]
  have hk0 : 0 < k := by omega
  rw [sweepMomentTrace_eq_sum_re]
  have hper : ∀ i : Fin D, Complex.re (inner ℂ (EuclideanSpace.single i (1 : ℂ))
        (((sweepSecondMoment ρ)^r) (EuclideanSpace.single i (1 : ℂ)))) ≤
      ‖sweepSecondMoment ρ‖ ^ r := by
    intro i
    rw [hr2, sweepMomentTrace_entry]
    have hnorm1 : ‖EuclideanSpace.single i (1 : ℂ)‖ = 1 := by
      rw [show EuclideanSpace.single i (1 : ℂ) = PiLp.single 2 i (1 : ℂ) from rfl]
      rw [PiLp.norm_single]
      simp
    have hle : ‖((sweepSecondMoment ρ)^k) (EuclideanSpace.single i (1 : ℂ))‖ ≤
        ‖sweepSecondMoment ρ‖ ^ k := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [hnorm1, mul_one]
      exact norm_pow_le' _ hk0
    refine (pow_le_pow_left₀ (norm_nonneg _) hle 2).trans (le_of_eq ?_)
    rw [← pow_mul, mul_comm k 2, ← hr2]
  have hsum := Finset.sum_le_card_nsmul Finset.univ _ (‖sweepSecondMoment ρ‖ ^ r)
    (fun i _ => hper i)
  rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  exact hsum

end ThorpFourRow


/-! ## Slice G8-γc: the representation-equivalence chain (merged from the RepChain scratch module) -/

namespace ThorpFourRow

open scoped BigOperators

/-- 标准桥：二值卡组与 `Fin (2^d)` 的等价（`Slot d` 与 `Card d` 同为 `Fin d → Bool`）。 -/
def slotFinEquiv (d : ℕ) : Slot d ≃ Fin (2^d) :=
  (Fintype.equivFin (CubeShuffle.Card d)).trans (finCongr (CubeShuffle.card_positions d))

/-- `ρ` 沿桥传输到标准对称群 `Perm (Fin (2^d))` 上的表示。 -/
def transportedRep {d D : ℕ} (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D)) :
    Representation ℂ (Equiv.Perm (Fin (2^d))) (RepSpace D) :=
  ρ.comp (slotFinEquiv d).symm.permCongrHom.toMonoidHom

lemma transportedRep_apply {d D : ℕ} (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D))
    (h : Equiv.Perm (Fin (2^d))) (v : RepSpace D) :
    transportedRep ρ h v = ρ ((slotFinEquiv d).symm.permCongr h) v := rfl

instance transportedRep_isIrreducible {d D : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D)) [Representation.IsIrreducible ρ] :
    Representation.IsIrreducible (transportedRep ρ) :=
  CubeShuffle.UnitaryFinite.irreducible_comp_equiv ρ (slotFinEquiv d).symm.permCongrHom

/-- 范数保持（挑战侧 `IsUnitaryRep`）蕴涵内积保持（`PartialPermutation.IsUnitary`）：
极化恒等式把内积写成范数的整系数组合，逐项用 `‖ρ g u‖ = ‖u‖` 改写。 -/
lemma isUnitary_of_isUnitaryRep {d D : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D)) (hU : IsUnitaryRep ρ) :
    OAI.PartialPermutation.IsUnitary ρ := by
  intro g x y
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  simp only [← map_add, ← map_sub, ← map_smul, hU g]

/-- 同一等价先顺后逆地共轭一个置换等于不动。 -/
lemma permCongr_symm_permCongr (d : ℕ) (g : Equiv.Perm (Slot d)) :
    (slotFinEquiv d).symm.permCongr ((slotFinEquiv d).permCongr g) = g := by
  ext x
  simp [Equiv.permCongr_apply, Equiv.symm_symm]

/-- `cardLabels` 的共轭作用分解为「桥共轭 ∘ 标签共轭」：
`cardLabels d μ = (slotFinEquiv d).trans (labels μ).symm` 的定义展开，
经 `Equiv.permCongrHom_trans`（该等式本身是 `rfl`）落到逐点形式。 -/
lemma cardLabels_permCongr (d : ℕ) (μ : CubeShuffle.Specht.Shapes (2^d))
    (g : Equiv.Perm (Slot d)) :
    (CubeShuffle.Specht.cardLabels d μ).permCongr g =
      (CubeShuffle.Specht.labels μ).symm.permCongr ((slotFinEquiv d).permCongr g) := by
  have h1 : (CubeShuffle.Specht.cardLabels d μ).permCongrHom =
      (slotFinEquiv d).permCongrHom.trans (CubeShuffle.Specht.labels μ).symm.permCongrHom := by
    show ((slotFinEquiv d).trans (CubeShuffle.Specht.labels μ).symm).permCongrHom = _
    rw [Equiv.permCongrHom_trans]
  exact DFunLike.congr_fun h1 g

/-- 分类侧的标记表示沿桥拉回到 `Perm (Slot d)` 上。 -/
def deckLabelledRep {d : ℕ} (μ : CubeShuffle.Specht.Shapes (2^d)) :
    Representation ℂ (Equiv.Perm (Slot d)) (CubeShuffle.Specht.space μ.1) :=
  (CubeShuffle.Specht.labelledRepresentation μ).comp (slotFinEquiv d).permCongrHom.toMonoidHom

lemma deckLabelledRep_apply {d : ℕ} (μ : CubeShuffle.Specht.Shapes (2^d))
    (g : Equiv.Perm (Slot d)) (v : CubeShuffle.Specht.space μ.1) :
    deckLabelledRep μ g v = CubeShuffle.Specht.representation μ.1
      ((CubeShuffle.Specht.labels μ).symm.permCongr ((slotFinEquiv d).permCongr g)) v := rfl

/-- 拉回标记表示 ≅ `cardRepresentation d μ`：交织子是 Hilbert 模型映射
`spaceHilbertEquiv μ.1`（即 `unitaryEquiv` 的底层等价），群作用经
`cardLabels_permCongr` 对齐。 -/
def spechtToCardEquiv {d : ℕ} (μ : CubeShuffle.Specht.Shapes (2^d)) :
    Representation.Equiv (deckLabelledRep μ) (CubeShuffle.Specht.cardRepresentation d μ) :=
  Representation.Equiv.mk (CubeShuffle.Specht.spaceHilbertEquiv μ.1) fun g =>
    LinearMap.ext fun v =>
      calc CubeShuffle.Specht.spaceHilbertEquiv μ.1 (deckLabelledRep μ g v)
          = CubeShuffle.Specht.spaceHilbertEquiv μ.1 (CubeShuffle.Specht.representation μ.1
              ((CubeShuffle.Specht.labels μ).symm.permCongr ((slotFinEquiv d).permCongr g)) v) :=
            congrArg (CubeShuffle.Specht.spaceHilbertEquiv μ.1) (deckLabelledRep_apply μ g v)
        _ = CubeShuffle.Specht.unitaryRepresentation μ.1
              ((CubeShuffle.Specht.labels μ).symm.permCongr ((slotFinEquiv d).permCongr g))
              (CubeShuffle.Specht.spaceHilbertEquiv μ.1 v) :=
            Representation.IntertwiningMap.isIntertwining _ _
              (CubeShuffle.Specht.unitaryEquiv μ.1).toIntertwiningMap _ _
        _ = CubeShuffle.Specht.unitaryRepresentation μ.1
              ((CubeShuffle.Specht.cardLabels d μ).permCongr g)
              (CubeShuffle.Specht.spaceHilbertEquiv μ.1 v) := by
            rw [← cardLabels_permCongr]
        _ = (CubeShuffle.Specht.cardRepresentation d μ) g
              (CubeShuffle.Specht.spaceHilbertEquiv μ.1 v) := rfl

/-- 拉回标记表示 ≅ `ρ`：把分类等价 `T₀` 沿桥读回（`T₀` 的底层线性等价不变，
群作用经 `permCongr_symm_permCongr` 对齐）。 -/
def labelledToRepEquiv {d D : ℕ} (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D))
    (μ : CubeShuffle.Specht.Shapes (2^d))
    (T₀ : Representation.Equiv (CubeShuffle.Specht.labelledRepresentation μ) (transportedRep ρ)) :
    Representation.Equiv (deckLabelledRep μ) ρ :=
  Representation.Equiv.mk T₀.toLinearEquiv fun g =>
    LinearMap.ext fun v =>
      calc T₀.toLinearEquiv (deckLabelledRep μ g v)
          = T₀.toLinearEquiv (CubeShuffle.Specht.representation μ.1
              ((CubeShuffle.Specht.labels μ).symm.permCongr ((slotFinEquiv d).permCongr g)) v) :=
            congrArg T₀.toLinearEquiv (deckLabelledRep_apply μ g v)
        _ = T₀.toLinearEquiv (CubeShuffle.Specht.labelledRepresentation μ
              ((slotFinEquiv d).permCongr g) v) := rfl
        _ = transportedRep ρ ((slotFinEquiv d).permCongr g) (T₀.toLinearEquiv v) :=
            Representation.IntertwiningMap.isIntertwining _ _ T₀.toIntertwiningMap _ _
        _ = ρ g (T₀.toLinearEquiv v) := by
            rw [transportedRep_apply, permCongr_symm_permCongr]

/-- 主等价：`ρ ≅ cardRepresentation d μ`（同在 `Perm (Slot d)` 上）。 -/
def repEquivCard {d D : ℕ} (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D))
    (μ : CubeShuffle.Specht.Shapes (2^d))
    (T₀ : Representation.Equiv (CubeShuffle.Specht.labelledRepresentation μ) (transportedRep ρ)) :
    Representation.Equiv ρ (CubeShuffle.Specht.cardRepresentation d μ) :=
  (labelledToRepEquiv ρ μ T₀).symm.trans (spechtToCardEquiv μ)

lemma repEquivCard_intertwines {d D : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D))
    (μ : CubeShuffle.Specht.Shapes (2^d))
    (T₀ : Representation.Equiv (CubeShuffle.Specht.labelledRepresentation μ) (transportedRep ρ))
    (g : Equiv.Perm (Slot d)) (v : RepSpace D) :
    (repEquivCard ρ μ T₀).toLinearEquiv (ρ g v) =
      (CubeShuffle.Specht.cardRepresentation d μ) g ((repEquivCard ρ μ T₀).toLinearEquiv v) :=
  Representation.IntertwiningMap.isIntertwining _ _
    (repEquivCard ρ μ T₀).toIntertwiningMap g v

/-- 主等价的底层线性映射非零（Specht 空间有非零 polytabloid，经 Hilbert 模型映射
送入 `hilbertSpace μ.1`）。 -/
lemma repEquivCard_ne_zero {d D : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D))
    (μ : CubeShuffle.Specht.Shapes (2^d))
    (T₀ : Representation.Equiv (CubeShuffle.Specht.labelledRepresentation μ) (transportedRep ρ)) :
    (repEquivCard ρ μ T₀).toLinearEquiv.toLinearMap ≠ 0 := by
  intro h0
  have hw : (CubeShuffle.Specht.spaceHilbertEquiv μ.1
      ⟨CubeShuffle.Specht.polytabloid μ.1, CubeShuffle.Specht.polytabloid_mem_space μ.1⟩ :
      CubeShuffle.Specht.hilbertSpace μ.1) ≠ 0 := by
    intro hz
    apply CubeShuffle.Specht.polytabloid_ne_zero μ.1
    have h0' : (⟨CubeShuffle.Specht.polytabloid μ.1,
          CubeShuffle.Specht.polytabloid_mem_space μ.1⟩ : CubeShuffle.Specht.space μ.1) = 0 :=
      (CubeShuffle.Specht.spaceHilbertEquiv μ.1).injective (by
        rw [hz]; exact (map_zero _).symm)
    exact congrArg Subtype.val h0'
  have happ : (repEquivCard ρ μ T₀).toLinearEquiv ((repEquivCard ρ μ T₀).toLinearEquiv.symm
      (CubeShuffle.Specht.spaceHilbertEquiv μ.1
        ⟨CubeShuffle.Specht.polytabloid μ.1, CubeShuffle.Specht.polytabloid_mem_space μ.1⟩)) = 0 :=
    LinearMap.ext_iff.mp h0 _
  rw [LinearEquiv.apply_symm_apply] at happ
  exact hw happ

open CubeShuffle.Specht CubeShuffle.WeightedSweep in
/-- 每个不可约酉表示的扫描 Fourier 算子范数等于某个 cardRepresentation 上的引擎算子范数。 -/
theorem exists_equiv_opNorm_fourierAt_eq {d : ℕ} (hd : 0 < d) {D : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D))
    [Representation.IsIrreducible ρ] (hU : IsUnitaryRep ρ) :
    ∃ μ : Shapes (2^d), (dimension μ.1 = (D : ℝ)) ∧
      ‖ThorpFourRow.fourierAt (ThorpFourRow.binaryLaw d) ρ‖ =
        ‖CubeShuffle.WeightedSweep.fourierSweep d μ‖ := by
  classical
  obtain ⟨μ, ⟨T₀⟩⟩ := labelled_complete (transportedRep ρ)
  refine ⟨μ, ?_, ?_⟩
  · -- 维数：等价 ⟹ finrank 相等，两端各自对齐到 `space μ.1` 与 `D`
    have hfin : Module.finrank ℂ (RepSpace D) = Module.finrank ℂ (space μ.1) := by
      have h1 : Module.finrank ℂ (RepSpace D) = Module.finrank ℂ (hilbertSpace μ.1) :=
        (repEquivCard ρ μ T₀).toLinearEquiv.finrank_eq
      rw [finrank_hilbertSpace] at h1
      exact h1
    have hfinD : Module.finrank ℂ (RepSpace D) = D := by
      show Module.finrank ℂ (EuclideanSpace ℂ (Fin D)) = D
      exact finrank_euclideanSpace_fin
    have hfinN : Module.finrank ℂ (space μ.1) = D := hfin.symm.trans hfinD
    show ((Module.finrank ℂ (space μ.1) : ℕ) : ℝ) = (D : ℝ)
    rw [hfinN]
  · -- 范数：律桥对齐两侧律，交织传输对齐两侧算子
    have hlaw : ∀ g : Equiv.Perm (Slot d),
        CubeShuffle.WeightedSweep.sweepLaw d g = ThorpFourRow.binaryLaw d g := by
      intro g
      rw [LawBridge.cube_sweepLaw_eq_sweepLaw d hd]
      show BinaryCoordinateSweeps.convolutionPower (BinaryCoordinateSweeps.binaryLaw d) 1 g = _
      rw [BinaryCoordinateSweeps.convolutionPower_one]
      exact (ThorpFourRow.binaryLaw_eq d g).symm
    have hnorm := OAI.PartialPermutation.opNorm_fourier_eq_of_intertwining ρ
      (cardRepresentation d μ) (isUnitary_of_isUnitaryRep ρ hU)
      (fun g v w => cardRepresentation_unitary d μ g v w)
      (repEquivCard ρ μ T₀).toLinearEquiv (repEquivCard_intertwines ρ μ T₀)
      (repEquivCard_ne_zero ρ μ T₀) (CubeShuffle.WeightedSweep.sweepLaw d)
    -- 引擎侧：`fourierSweep` 的 CLM 和与 `toCLM (complexFourier …)` 逐点相同
    have hfR : ‖fourierSweep d μ‖ =
        ‖LinearMap.toContinuousLinearMap (OAI.PartialPermutation.complexFourier
          (cardRepresentation d μ) (fun g => (CubeShuffle.WeightedSweep.sweepLaw d g : ℂ)))‖ := by
      rw [fourierSweep_eq_group_sum]
      congr 1
      apply ContinuousLinearMap.ext
      intro v
      rw [sum_apply]
      simp only [smul_apply,
        CubeShuffle.UnitaryFinite.continuousRepresentation_apply]
      show (∑ g : Equiv.Perm (CubeShuffle.Card d), (CubeShuffle.WeightedSweep.sweepLaw d g : ℂ) •
          (cardRepresentation d μ) g v) =
        (∑ g : Equiv.Perm (CubeShuffle.Card d), (CubeShuffle.WeightedSweep.sweepLaw d g : ℂ) •
          (cardRepresentation d μ) g) v
      rw [LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro g _
      rw [LinearMap.smul_apply]
    calc ‖ThorpFourRow.fourierAt (ThorpFourRow.binaryLaw d) ρ‖
        = ‖ThorpFourRow.fourierAt (CubeShuffle.WeightedSweep.sweepLaw d) ρ‖ := by
            have hfun : ThorpFourRow.binaryLaw d = CubeShuffle.WeightedSweep.sweepLaw d :=
              funext fun g => (hlaw g).symm
            rw [hfun]
      _ = ‖LinearMap.toContinuousLinearMap (OAI.PartialPermutation.complexFourier ρ
            (fun g => (CubeShuffle.WeightedSweep.sweepLaw d g : ℂ)))‖ := rfl
      _ = ‖LinearMap.toContinuousLinearMap (OAI.PartialPermutation.complexFourier
            (cardRepresentation d μ)
            (fun g => (CubeShuffle.WeightedSweep.sweepLaw d g : ℂ)))‖ := hnorm.symm
      _ = ‖fourierSweep d μ‖ := hfR.symm

end ThorpFourRow

/-! ## Slice G8-δ: the terminal assembly

`FixedMomentDegreeSaving` from the engine through the chain; the upper bound
re-exported from the tree's `binary_main` through the pointwise bridges; the
lower bound is `physicalLaw_tv_ge` (slice G8-β). -/

namespace ThorpFourRow

/-- `convolutionPower p 1 = p` on the challenge's copies (via the pointwise
bridge to the repository's `PointMassOne.convolutionPower_one`). -/
lemma convolutionPower_one {G : Type*} [Group G] [Fintype G] (p : G → ℝ) :
    convolutionPower p 1 = p := by
  classical
  funext g
  rw [convolutionPower_eq, BinaryCoordinateSweeps.convolutionPower_one]

/-- The second-moment norm is the squared Fourier norm (the C* identity
`‖T T*‖ = ‖T‖²`, via `norm_adjoint_comp_self`). -/
lemma sweepSecondMoment_norm {d D : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D)) :
    ‖sweepSecondMoment ρ‖ = ‖fourierAt (convolutionPower (binaryLaw d) 1) ρ‖ ^ 2 := by
  classical
  unfold sweepSecondMoment
  simp only []
  have h := ContinuousLinearMap.norm_adjoint_comp_self
    (ContinuousLinearMap.adjoint (fourierAt (convolutionPower (binaryLaw d) 1) ρ))
  rw [ContinuousLinearMap.adjoint_adjoint, LinearIsometryEquiv.norm_map] at h
  rw [h, pow_two]

/-- Theorem 1.2 (a fixed moment with a degree saving): the weighted-Schatten
engine through the representation chain. The witnesses are `r = 2⌈pStar⌉` and
`η = 3/4`. -/
theorem fixedMomentDegreeSaving : FixedMomentDegreeSaving := by
  classical
  obtain ⟨W, pStar, p, hW, hpStar2, hp, hbound⟩ := CubeShuffle.WeightedSweep.weighted_sweep_moments
  have hceil : 2 ≤ Nat.ceil pStar := by
    have h := hpStar2.trans (Nat.le_ceil _)
    exact_mod_cast h
  have hr2 : 2 ≤ 2 * Nat.ceil pStar := by omega
  refine ⟨2 * Nat.ceil pStar, hr2, ⟨Nat.ceil pStar, two_mul _⟩, 3/4, by norm_num, ?_⟩
  intro d hd D ρ hirr hU
  obtain ⟨μ, hdim, hnorm⟩ := @exists_equiv_opNorm_fourierAt_eq _ hd _ ρ hirr hU
  have htr := sweepMomentTrace_le ρ (r := 2 * Nat.ceil pStar) ⟨Nat.ceil pStar, two_mul _⟩ hr2
  have hB : ‖sweepSecondMoment ρ‖ = ‖fourierAt (binaryLaw d) ρ‖ ^ 2 := by
    rw [sweepSecondMoment_norm, convolutionPower_one]
  have hD : (1:ℝ) ≤ (D : ℝ) := by
    rw [← hdim]
    exact CubeShuffle.WeightedSweep.dimension_one_le μ.1
  have heng : ‖CubeShuffle.WeightedSweep.fourierSweep d μ‖ ≤ (D : ℝ) ^ (-3 / (4 * pStar)) := by
    rw [← hdim]
    exact (hbound d (by omega) μ).2.2.2
  calc (D : ℝ) * sweepMomentTrace ρ (2 * Nat.ceil pStar)
      ≤ (D : ℝ) * ((D : ℝ) * ‖sweepSecondMoment ρ‖ ^ (2 * Nat.ceil pStar)) :=
        mul_le_mul_of_nonneg_left htr (Nat.cast_nonneg _)
    _ = (D : ℝ)^2 * ‖sweepSecondMoment ρ‖ ^ (2 * Nat.ceil pStar) := by ring
    _ = (D : ℝ)^2 * (‖fourierAt (binaryLaw d) ρ‖ ^ 2) ^ (2 * Nat.ceil pStar) := by
        rw [hB]
    _ = (D : ℝ)^2 * ‖fourierAt (binaryLaw d) ρ‖ ^ (2 * (2 * Nat.ceil pStar)) := by
        rw [← pow_mul]
    _ = (D : ℝ)^2 * ‖CubeShuffle.WeightedSweep.fourierSweep d μ‖ ^ (2 * (2 * Nat.ceil pStar)) := by rw [hnorm]
    _ ≤ (D : ℝ)^2 * ((D : ℝ) ^ (-3 / (4 * pStar))) ^ (2 * (2 * Nat.ceil pStar)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg _) heng _
    _ = (D : ℝ) ^ (2 + (-3 / (4 * pStar)) * (4 * (Nat.ceil pStar : ℝ))) := by
        have hD0 : (0:ℝ) < (D : ℝ) := lt_of_lt_of_le zero_lt_one hD
        have hN : ((2 * (2 * Nat.ceil pStar) : ℕ) : ℝ) = 4 * (Nat.ceil pStar : ℝ) := by
          push_cast
          ring
        rw [← Real.rpow_natCast ((D : ℝ) ^ (-3 / (4 * pStar))) (2 * (2 * Nat.ceil pStar)),
          hN, ← Real.rpow_mul (Nat.cast_nonneg (D : ℕ)),
          ← Real.rpow_natCast (D : ℝ) 2, ← Real.rpow_add hD0]
        congr 1
    _ ≤ (D : ℝ) ^ ((1 - 3/4 : ℝ)) := by
        have hcs : (pStar : ℝ) ≤ (Nat.ceil pStar : ℝ) := Nat.le_ceil _
        have hpc : (0:ℝ) < pStar := by linarith [hpStar2]
        have hpne : pStar ≠ 0 := hpc.ne'
        have hdiv : (3:ℝ) ≤ 3 * (Nat.ceil pStar : ℝ) / pStar := by
          rw [le_div_iff₀ hpc]
          exact mul_le_mul_of_nonneg_left hcs (by norm_num)
        have hrewrite : (2:ℝ) + (-3 / (4 * pStar)) * (4 * (Nat.ceil pStar : ℝ)) =
            2 - 3 * (Nat.ceil pStar : ℝ) / pStar := by
          field_simp
          ring
        have hexp : (2:ℝ) + (-3 / (4 * pStar)) * (4 * (Nat.ceil pStar : ℝ)) ≤ 1 - 3/4 := by
          rw [hrewrite]
          linarith [hdiv]
        exact Real.rpow_le_rpow_of_exponent_le hD hexp

/-- The upper bound: an absolute number of sweeps mixes, uniformly over decks
(re-export of the tree's `binary_main` through the pointwise bridges). -/
theorem optimalOrderThorpMixing_upper :
    (∃ q : ℕ, ∀ ε : ℝ, 0 < ε → ∃ d₀ : ℕ, ∀ d ≥ d₀,
      ∀ τ : Equiv.Perm (Slot d),
        totalVariation (fun g => convolutionPower (binaryLaw d) q (g * τ⁻¹))
          (uniformLaw (Equiv.Perm (Slot d))) ≤ ε) := by
  classical
  obtain ⟨w, hw⟩ := BinaryCoordinateSweeps.binary_main.2.2
  refine ⟨w, fun ε hε => ?_⟩
  obtain ⟨d₀, hd₀⟩ := hw ε hε
  refine ⟨d₀, fun d hd τ => ?_⟩
  have hpoint : ∀ g : Equiv.Perm (Slot d),
      convolutionPower (binaryLaw d) w (g * τ⁻¹) =
        BinaryCoordinateSweeps.sweepLaw d w (g * τ⁻¹) := by
    intro g
    show convolutionPower (binaryLaw d) w (g * τ⁻¹) =
      BinaryCoordinateSweeps.convolutionPower (BinaryCoordinateSweeps.binaryLaw d) w (g * τ⁻¹)
    rw [show binaryLaw d = BinaryCoordinateSweeps.binaryLaw d from funext (binaryLaw_eq d)]
    exact convolutionPower_eq _ _ _
  have hTV : totalVariation (fun g => convolutionPower (binaryLaw d) w (g * τ⁻¹))
      (uniformLaw (Equiv.Perm (Slot d))) =
      BinaryCoordinateSweeps.totalVariation (fun g => BinaryCoordinateSweeps.sweepLaw d w (g * τ⁻¹))
        (BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Slot d))) := by
    rw [totalVariation_eq]
    congr 1
    funext g
    exact hpoint g
  rw [hTV]
  exact hd₀ d hd τ

/-- The lower bound (paper's equation (3)): slice G8-β's `physicalLaw_tv_ge`. -/
theorem optimalOrderThorpMixing_lower :
    (∀ d : ℕ, ∀ hd : 0 < d, ∀ t : ℕ,
      totalVariation (physicalLaw d hd t) (uniformLaw (Equiv.Perm (Slot d))) ≥
        1 - (2 : ℝ) ^ (t * 2 ^ (d - 1)) / (Nat.factorial (2 ^ d) : ℝ)) :=
  fun d hd t => physicalLaw_tv_ge d hd t

end ThorpFourRow

/-- The segment `lean/docs/238.md` excludes: from the strict four-row permanent
inequality to the Thorp mixing consequence. -/
theorem four_row_moment_mixing_consequence :
    ThorpFourRow.FixedMomentDegreeSaving ∧ ThorpFourRow.OptimalOrderThorpMixing :=
  ⟨ThorpFourRow.fixedMomentDegreeSaving, ThorpFourRow.optimalOrderThorpMixing_upper,
    ThorpFourRow.optimalOrderThorpMixing_lower⟩

end

end OAI
