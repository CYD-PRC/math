import Mathlib
import OAI.Probability.BinarySweep.Model
import OAI.RepresentationTheory.PartialPermutation.Model
import OAI.RepresentationTheory.PartialPermutation.OperatorNorm
import OAI.RepresentationTheory.PartialPermutation.Plancherel
import OAI.RepresentationTheory.PartialPermutation.TrivialRepresentation
import OAI.RepresentationTheory.PartialPermutation.AlternatingTabloids
import OAI.RepresentationTheory.PartialPermutation.RowBounds
import OAI.RepresentationTheory.PartialPermutation.TailBounds
import OAI.RepresentationTheory.PartialPermutation.StandardTableaux
import OAI.RepresentationTheory.PartialPermutation.Tabloids
import OAI.RepresentationTheory.PartialPermutation.Polytabloids
import OAI.RepresentationTheory.PartialPermutation.SpechtModules
import OAI.RepresentationTheory.PartialPermutation.SpechtShapes
import OAI.RepresentationTheory.PartialPermutation.SpechtClassification
import OAI.RepresentationTheory.PartialPermutation.TableauLimits
import OAI.RepresentationTheory.PartialPermutation.DeficitPlancherel

/-!
# G1 solution module, slice 1: Fourier core of the amplification (Prop 2.5)

The Fourier transform of a convolution is the product of Fourier transforms
(operator multiplication in `Module.End`), with its real/ℂ cast bridge and
power forms; plus the operator-norm power bound. Later slices add the energy
bound, the sign bookkeeping, and the assembly over the facility's Plancherel /
degree-sum / TV-export machinery.
-/

namespace OAI

namespace PartialPermutation

open scoped BigOperators

noncomputable section
section ConvolutionCore

variable {G : Type*} [Group G] [Fintype G]

/-- Convolution of complex mass functions on a finite group. -/
def complexConvolution (f g : G → ℂ) (y : G) : ℂ := ∑ x, f x * g (x⁻¹ * y)

/-- The Fourier transform turns convolution into operator composition. -/
lemma complexFourier_conv {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (f g : G → ℂ) :
    complexFourier ρ (complexConvolution f g) =
      complexFourier ρ f * complexFourier ρ g := by
  classical
  unfold complexFourier complexConvolution
  simp_rw [Finset.sum_smul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  symm
  apply Fintype.sum_equiv (Equiv.mulLeft x)
  intro h
  simp only [Equiv.coe_mulLeft, smul_mul_smul_comm, ← map_mul, inv_mul_cancel_left]

/-- The real convolution casts to the complex one pointwise. -/
lemma complexConvolution_ofReal (f g : G → ℝ) :
    complexConvolution (fun x => (f x : ℂ)) (fun x => (g x : ℂ)) =
      fun y => ((BinaryCoordinateSweeps.convolution f g y : ℝ) : ℂ) := by
  funext y
  simp only [complexConvolution, BinaryCoordinateSweeps.convolution]
  push_cast
  rfl

/-- The complex unit mass at `1`. -/
def complexPointMassOne {G : Type*} [Group G] [Fintype G] (y : G) : ℂ := by
  classical
  exact if y = 1 then 1 else 0

/-- `r`-fold complex convolution. -/
def complexConvolutionPower (f : G → ℂ) : ℕ → G → ℂ
  | 0 => complexPointMassOne
  | n + 1 => complexConvolution f (complexConvolutionPower f n)

lemma complexConvolutionPower_ofReal (f : G → ℝ) (r : ℕ) :
    complexConvolutionPower (fun x => (f x : ℂ)) r =
      fun y => ((BinaryCoordinateSweeps.convolutionPower f r y : ℝ) : ℂ) := by
  induction r with
  | zero =>
    funext y
    show complexPointMassOne y = ((BinaryCoordinateSweeps.pointMassOne y : ℝ) : ℂ)
    simp only [complexPointMassOne, BinaryCoordinateSweeps.pointMassOne]
    split_ifs with h <;> simp
  | succ n ih =>
    funext y
    simp only [complexConvolutionPower, BinaryCoordinateSweeps.convolutionPower]
    rw [congrArg (complexConvolution (fun x => (f x : ℂ))) ih, complexConvolution_ofReal]

lemma complexFourier_convPower {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (f : G → ℂ) (r : ℕ) :
    complexFourier ρ (complexConvolutionPower f r) = (complexFourier ρ f) ^ r := by
  induction r with
  | zero =>
    simp only [complexConvolutionPower, pow_zero]
    unfold complexFourier
    rw [Finset.sum_eq_single 1]
    · show complexPointMassOne (1 : G) • ρ 1 = 1
      simp [complexPointMassOne, map_one]
    · intro x _ hx
      show complexPointMassOne x • ρ x = 0
      simp [complexPointMassOne, hx]
    · simp
  | succ n ih =>
    simp only [complexConvolutionPower, pow_succ']
    rw [complexFourier_conv, ih]

end ConvolutionCore

/-- The operator norm of a power is at most the power of the operator norm. -/
lemma opNorm_pow_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (A : Module.End ℂ V) (r : ℕ) :
    ‖LinearMap.toContinuousLinearMap (A ^ r)‖ ≤
      ‖LinearMap.toContinuousLinearMap A‖ ^ r := by
  induction r with
  | zero =>
    show ‖LinearMap.toContinuousLinearMap (1 : Module.End ℂ V)‖ ≤ 1
    rw [show LinearMap.toContinuousLinearMap (1 : Module.End ℂ V) =
        ContinuousLinearMap.id ℂ V from rfl]
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    have hmul : LinearMap.toContinuousLinearMap (A ^ (n + 1)) =
        (LinearMap.toContinuousLinearMap A).comp
          (LinearMap.toContinuousLinearMap (A ^ n)) := by
      apply ContinuousLinearMap.ext
      intro x
      show (A ^ (n + 1)) x = A ((A ^ n) x)
      rw [pow_succ']
      rfl
    rw [hmul, pow_succ']
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

/-- HS² ≤ dim · op² (the direction the amplification needs). -/
lemma hsNormSq_le_finrank_mul_opNormSq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (A : Module.End ℂ V) :
    hsNormSq A ≤ (Module.finrank ℂ V : ℝ) *
      ‖LinearMap.toContinuousLinearMap A‖ ^ 2 := by
  let e := stdOrthonormalBasis ℂ V
  rw [hsNormSq_eq_sum e]
  calc ∑ i : Fin (Module.finrank ℂ V), ‖A (e i)‖ ^ 2
      ≤ ∑ i : Fin (Module.finrank ℂ V),
          ‖LinearMap.toContinuousLinearMap A‖ ^ 2 * ‖e i‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        calc ‖A (e i)‖ ^ 2
            = ‖LinearMap.toContinuousLinearMap A (e i)‖ ^ 2 := rfl
          _ ≤ (‖LinearMap.toContinuousLinearMap A‖ * ‖e i‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.le_opNorm _ _) 2
          _ = ‖LinearMap.toContinuousLinearMap A‖ ^ 2 * ‖e i‖ ^ 2 := mul_pow _ _ 2
    _ = (Module.finrank ℂ V : ℝ) * ‖LinearMap.toContinuousLinearMap A‖ ^ 2 := by
        simp only [e.orthonormal.1, one_pow, mul_one]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Submultiplicativity of the Hilbert–Schmidt norm across powers. -/
lemma hsNormSq_pow_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (A : Module.End ℂ V) {r : ℕ} (hr : 1 ≤ r) :
    hsNormSq (A ^ r) ≤ hsNormSq A ^ r := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  clear hr
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    calc hsNormSq (A * A ^ (n + 1))
        ≤ hsNormSq A * hsNormSq (A ^ (n + 1)) := hsNormSq_mul_le _ _
      _ ≤ hsNormSq A * hsNormSq A ^ (n + 1) :=
          mul_le_mul_of_nonneg_left ih (hsNormSq_nonneg A)
      _ = hsNormSq A ^ (n + 2) := (pow_succ' _ _).symm

/-- HS² of the `r`-th convolution power, bounded by the `2r`-th power of the
operator norm of the Fourier transform — the paper's amplification step
`D‖f̂ʳ‖²HS ≤ D²‖f̂‖²ʳop`. -/
lemma hsNormSq_convPower_le {G : Type*} [Group G] [Fintype G]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (f : G → ℝ) (r : ℕ) :
    hsNormSq (complexFourier ρ
        (fun g => ((BinaryCoordinateSweeps.convolutionPower f r g : ℝ) : ℂ)))
      ≤ (Module.finrank ℂ V : ℝ) *
        ‖LinearMap.toContinuousLinearMap (complexFourier ρ (fun g => (f g : ℂ)))‖
          ^ (2 * r) := by
  rw [← complexConvolutionPower_ofReal, complexFourier_convPower]
  set F := complexFourier ρ (fun g => (f g : ℂ))
  calc hsNormSq (F ^ r)
      ≤ (Module.finrank ℂ V : ℝ) * ‖LinearMap.toContinuousLinearMap (F ^ r)‖ ^ 2 :=
        hsNormSq_le_finrank_mul_opNormSq _
    _ ≤ (Module.finrank ℂ V : ℝ) *
          (‖LinearMap.toContinuousLinearMap F‖ ^ r) ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (opNorm_pow_le _ _) _) (by positivity)
    _ = (Module.finrank ℂ V : ℝ) *
          ‖LinearMap.toContinuousLinearMap F‖ ^ (2 * r) := by
        rw [Nat.mul_comm 2 r, ← pow_mul]

/-! ## Slice 2a: the sign index

The one-dimensional sign representation, extracted into the facility's
irreducible-index machinery exactly as `trivialIndex` was. -/

section SignIndex

/-- The one-dimensional sign representation on `ℂ`. -/
def signRep {X : Type*} [Fintype X] [DecidableEq X] :
    Representation ℂ (Equiv.Perm X) ℂ where
  toFun g := YoungTabloid.signC g • 1
  map_one' := by simp
  map_mul' := fun g h => by
    simp only [YoungTabloid.signC_mul]
    rw [smul_mul_smul_comm, mul_one]

/-- The subrepresentations of `signRep` are just the `ℂ`-submodules of `ℂ`:
the action is by scalars. -/
def signSubmoduleEquiv {X : Type*} [Fintype X] [DecidableEq X] :
    Subrepresentation (signRep (X := X)) ≃o Submodule ℂ ℂ where
  toFun := Subrepresentation.toSubmodule
  invFun S := ⟨S, fun g x hx => by
    show YoungTabloid.signC g • x ∈ S
    exact S.smul_mem _ hx⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

instance signRep_irreducible {X : Type*} [Fintype X] [DecidableEq X] :
    Representation.IsIrreducible (signRep (X := X)) :=
  (OrderIso.isSimpleOrder_iff signSubmoduleEquiv).mpr inferInstance

/-- The sign representation's index, mirroring `trivialIndex`. -/
def signIndex (n : ℕ) : IrreducibleIndex (Equiv.Perm (Fin n)) :=
  (irreducibleRep_complete (signRep (X := Fin n))).choose

lemma signIndex_equiv (n : ℕ) :
    Nonempty (Representation.Equiv (irreducibleRep (signIndex n))
      (signRep (X := Fin n))) :=
  (irreducibleRep_complete (signRep (X := Fin n))).choose_spec.1

@[simp] lemma irreducibleDegree_signIndex (n : ℕ) :
    irreducibleDegree (signIndex n) = 1 := by
  obtain ⟨e⟩ := signIndex_equiv n
  exact e.toLinearEquiv.finrank_eq.trans (Module.finrank_self ℂ)

/-- Fourier transfer across an intertwining linear map. -/
lemma complexFourier_transfer {G V W : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (E : V →ₗ[ℂ] W) (hE : ∀ g, E ∘ₗ ρ g = σ g ∘ₗ E) (f : G → ℂ) :
    E ∘ₗ complexFourier ρ f = complexFourier σ f ∘ₗ E := by
  ext v
  show E ((∑ g, f g • ρ g) v) = (∑ g, f g • σ g) (E v)
  simp only [LinearMap.sum_apply, map_sum, map_smul, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro g _
  exact congrArg (f g • ·) (LinearMap.congr_fun (hE g) v)

/-- The Fourier transform at the concrete sign representation is the sign-mean
scalar operator. -/
lemma complexFourier_signRep {n : ℕ} (f : Equiv.Perm (Fin n) → ℝ) :
    complexFourier (signRep (X := Fin n)) (fun g => (f g : ℂ)) =
      (∑ g, (f g : ℂ) * YoungTabloid.signC g) • 1 := by
  unfold complexFourier
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro g _
  show (f g : ℂ) • (YoungTabloid.signC g • (1 : Module.End ℂ ℂ)) =
    ((f g : ℂ) * YoungTabloid.signC g) • (1 : Module.End ℂ ℂ)
  rw [smul_smul]

/-- The Fourier transform at the sign index is the same sign-mean scalar:
the conjugating equivalence absorbs nothing because the scalar is central. -/
lemma complexFourier_signIndex (n : ℕ) (f : Equiv.Perm (Fin n) → ℝ) :
    complexFourier (irreducibleRep (signIndex n)) (fun g => (f g : ℂ)) =
      (∑ g, (f g : ℂ) * YoungTabloid.signC g) • 1 := by
  obtain ⟨e⟩ := signIndex_equiv n
  have htr := complexFourier_transfer (irreducibleRep (signIndex n))
    (signRep (X := Fin n)) e.toLinearEquiv.toLinearMap
    (fun g => e.isIntertwining' g) (fun g => (f g : ℂ))
  rw [complexFourier_signRep f] at htr
  apply LinearMap.ext
  intro v
  apply e.toLinearEquiv.injective
  have hv := LinearMap.congr_fun htr v
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
    Module.End.one_apply] at hv ⊢
  rw [map_smul]
  exact hv

/-- The two distinguished indices differ (from `n ≥ 2` on, where a swap
exists): the swap acts as `−1` in `signRep` and as `+1` in the trivial
representation. -/
lemma signIndex_ne_trivialIndex {n : ℕ} (hn : 2 ≤ n) :
    signIndex n ≠ trivialIndex (Equiv.Perm (Fin n)) := by
  intro h
  obtain ⟨e⟩ := signIndex_equiv n
  rw [h] at e
  obtain ⟨eT⟩ := trivialIndex_equiv (G := Equiv.Perm (Fin n))
  -- compose: an intertwining equivalence between signRep and trivial
  set E : Representation.Equiv (signRep (X := Fin n))
      (Representation.trivial ℂ (Equiv.Perm (Fin n)) ℂ) := e.symm.trans eT
  obtain ⟨x, y, hxy⟩ : ∃ x y : Fin n, x ≠ y :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  have hsign : (signRep (X := Fin n)) (Equiv.swap x y) 1 = (-1 : ℂ) := by
    show YoungTabloid.signC (Equiv.swap x y) • (1 : Module.End ℂ ℂ) 1 = -1
    rw [YoungTabloid.signC_swap x y hxy]
    simp
  have hz := LinearMap.congr_fun (E.isIntertwining' (Equiv.swap x y)) 1
  simp only [LinearMap.coe_comp, Function.comp_apply] at hz
  rw [hsign, Representation.trivial_apply] at hz
  -- hz : E(-1) = E(1)
  have hcon : (-1 : ℂ) = 1 := by
    apply E.toLinearEquiv.injective
    simpa using hz
  rw [Complex.ext_iff] at hcon
  norm_num at hcon

/-- The facility's two sign conventions agree: `signC` is `realSign` cast. -/
lemma signC_eq_realSign {X : Type*} [Fintype X] [DecidableEq X] (g : Equiv.Perm X) :
    YoungTabloid.signC g = ((BinaryCoordinateSweeps.realSign g : ℝ) : ℂ) := by
  simp [YoungTabloid.signC, BinaryCoordinateSweeps.realSign]

end SignIndex

/-! ## Slice 2b: degree-one classification via characters

A degree-one index's representation is a family of scalars, hence a
multiplicative character `χ`. Swaps square to one (`χ τ = ±1`), swaps are
mutually conjugate (`Equiv.Perm.isConj_swap`), so `χ` is constant on swaps;
`swap_induction_on` then determines `χ` as trivial or sign. -/

section DegreeOne

/-- Endomorphisms of a one-dimensional space are scalar multiples of the
identity; the scalar is the trace. -/
lemma end_eq_trace_smul_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (hV : Module.finrank ℂ V = 1) (A : Module.End ℂ V) :
    A = (LinearMap.trace ℂ V A) • 1 := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hV
  obtain ⟨c, hc⟩ := hv (A v)
  have hA : A = c • (1 : Module.End ℂ V) := by
    ext w
    obtain ⟨a, rfl⟩ := hv w
    rw [map_smul, ← hc, LinearMap.smul_apply, Module.End.one_apply]
    rw [smul_smul, smul_smul, mul_comm a c]
  have htr : LinearMap.trace ℂ V A = c := by
    rw [hA, map_smul]
    rw [show (1 : Module.End ℂ V) = LinearMap.id from rfl, LinearMap.trace_id, hV]
    simp
  subst htr
  exact hA

/-- In dimension one the trace is multiplicative. -/
lemma trace_mul_of_finrank_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (hV : Module.finrank ℂ V = 1) (A B : Module.End ℂ V) :
    LinearMap.trace ℂ V (A * B) = LinearMap.trace ℂ V A * LinearMap.trace ℂ V B := by
  have hab : A * B = (LinearMap.trace ℂ V A * LinearMap.trace ℂ V B) • 1 := by
    conv_lhs => rw [end_eq_trace_smul_one hV A, end_eq_trace_smul_one hV B]
    rw [smul_mul_smul_comm, mul_one]
  rw [hab, map_smul]
  rw [show (1 : Module.End ℂ V) = LinearMap.id from rfl, LinearMap.trace_id, hV]
  simp

/-- The character of a degree-one index: the trace of the (scalar) action. -/
def degOneChar {n : ℕ} (c : IrreducibleIndex (Equiv.Perm (Fin n))) :
    Equiv.Perm (Fin n) → ℂ :=
  fun g => LinearMap.trace ℂ (irreducibleSpace c) (irreducibleRep c g)

lemma degOneChar_mul {n : ℕ} (c : IrreducibleIndex (Equiv.Perm (Fin n)))
    (hdeg : irreducibleDegree c = 1) (g h : Equiv.Perm (Fin n)) :
    degOneChar c (g * h) = degOneChar c g * degOneChar c h := by
  show LinearMap.trace ℂ (irreducibleSpace c) (irreducibleRep c (g * h)) =
    LinearMap.trace ℂ (irreducibleSpace c) (irreducibleRep c g) *
      LinearMap.trace ℂ (irreducibleSpace c) (irreducibleRep c h)
  rw [map_mul]
  exact trace_mul_of_finrank_one hdeg _ _

lemma degOneChar_one {n : ℕ} (c : IrreducibleIndex (Equiv.Perm (Fin n)))
    (hdeg : irreducibleDegree c = 1) :
    degOneChar c 1 = 1 := by
  show LinearMap.trace ℂ (irreducibleSpace c) (irreducibleRep c 1) = 1
  rw [map_one]
  rw [show (1 : Module.End ℂ (irreducibleSpace c)) = LinearMap.id from rfl,
    LinearMap.trace_id]
  rw [show Module.finrank ℂ ↥(irreducibleSpace c) = irreducibleDegree c from rfl, hdeg]
  simp

lemma degOneChar_ne_zero {n : ℕ} (c : IrreducibleIndex (Equiv.Perm (Fin n)))
    (hdeg : irreducibleDegree c = 1) (g : Equiv.Perm (Fin n)) :
    degOneChar c g ≠ 0 := by
  intro hz
  have hmul := degOneChar_mul c hdeg g g⁻¹
  rw [mul_inv_cancel, degOneChar_one c hdeg, hz] at hmul
  simp at hmul

lemma degOneChar_swap {n : ℕ} (c : IrreducibleIndex (Equiv.Perm (Fin n)))
    (hdeg : irreducibleDegree c = 1) {x y : Fin n} (_hxy : x ≠ y) :
    degOneChar c (Equiv.swap x y) = 1 ∨ degOneChar c (Equiv.swap x y) = -1 := by
  have hsq : degOneChar c (Equiv.swap x y) ^ 2 = 1 := by
    rw [sq, ← degOneChar_mul c hdeg, Equiv.swap_mul_self]
    exact degOneChar_one c hdeg
  exact sq_eq_one_iff.mp hsq

/-- The character is constant on swaps (they are mutually conjugate). -/
lemma degOneChar_swap_const {n : ℕ} (c : IrreducibleIndex (Equiv.Perm (Fin n)))
    (hdeg : irreducibleDegree c = 1) {w x y z : Fin n} (hw : w ≠ x) (hy : y ≠ z) :
    degOneChar c (Equiv.swap w x) = degOneChar c (Equiv.swap y z) := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.isConj_swap hw hy
  have h1 : degOneChar c (↑σ * Equiv.swap w x) =
      degOneChar c ↑σ * degOneChar c (Equiv.swap w x) := degOneChar_mul c hdeg _ _
  have h2 : degOneChar c (Equiv.swap y z * ↑σ) =
      degOneChar c (Equiv.swap y z) * degOneChar c ↑σ := degOneChar_mul c hdeg _ _
  rw [hσ.eq] at h1
  rw [h2] at h1
  have h3 : degOneChar c ↑σ * degOneChar c (Equiv.swap y z) =
      degOneChar c ↑σ * degOneChar c (Equiv.swap w x) :=
    (mul_comm _ _).trans h1
  exact (mul_left_cancel₀ (degOneChar_ne_zero c hdeg ↑σ) h3).symm

/-- A degree-one character is determined by its value at a swap: it is either
trivial or the sign. -/
lemma degOneChar_eq_one_or_sign {n : ℕ} (hn : 2 ≤ n)
    (c : IrreducibleIndex (Equiv.Perm (Fin n))) (hdeg : irreducibleDegree c = 1) :
    (∀ g, degOneChar c g = 1) ∨ (∀ g, degOneChar c g = YoungTabloid.signC g) := by
  obtain ⟨x, y, hxy⟩ : ∃ x y : Fin n, x ≠ y := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  cases degOneChar_swap c hdeg hxy with
  | inl h1 =>
    left
    intro g
    induction g using Equiv.Perm.swap_induction_on with
    | one => exact degOneChar_one c hdeg
    | swap_mul f x' y' hne hf =>
      rw [degOneChar_mul c hdeg, degOneChar_swap_const c hdeg hne hxy, h1, hf,
        mul_one]
  | inr hneg =>
    right
    intro g
    induction g using Equiv.Perm.swap_induction_on with
    | one =>
      rw [degOneChar_one c hdeg, YoungTabloid.signC_one]
    | swap_mul f x' y' hne hf =>
      rw [degOneChar_mul c hdeg, degOneChar_swap_const c hdeg hne hxy, hneg, hf,
        YoungTabloid.signC_mul, YoungTabloid.signC_swap x' y' hne]

/-- The degree-one index's action is the character times the identity. -/
lemma irreducibleRep_eq_degOneChar_smul {n : ℕ} (c : IrreducibleIndex (Equiv.Perm (Fin n)))
    (hdeg : irreducibleDegree c = 1) (g : Equiv.Perm (Fin n)) :
    irreducibleRep c g = degOneChar c g • 1 :=
  end_eq_trace_smul_one hdeg _

/-- The representation of a degree-one index with trivial character is
equivalent to the trivial representation. -/
def repEquivTrivialOfChar {n : ℕ} (c : IrreducibleIndex (Equiv.Perm (Fin n)))
    (hdeg : irreducibleDegree c = 1) (hχ : ∀ g, degOneChar c g = 1) :
    Representation.Equiv (irreducibleRep c)
      (Representation.trivial ℂ (Equiv.Perm (Fin n)) ℂ) := by
  let E := LinearEquiv.ofFinrankEq (irreducibleSpace c) ℂ (by
    rw [show Module.finrank ℂ ↥(irreducibleSpace c) = irreducibleDegree c from rfl,
      hdeg, Module.finrank_self])
  exact Representation.Equiv.mk E (fun g => by
    ext v
    rw [irreducibleRep_eq_degOneChar_smul c hdeg g, hχ g]
    simp [Representation.trivial_apply, Module.End.one_apply])

/-- The representation of a degree-one index whose character is the sign is
equivalent to `signRep`. -/
def repEquivSignOfChar {n : ℕ} (c : IrreducibleIndex (Equiv.Perm (Fin n)))
    (hdeg : irreducibleDegree c = 1) (hχ : ∀ g, degOneChar c g = YoungTabloid.signC g) :
    Representation.Equiv (irreducibleRep c) (signRep (X := Fin n)) := by
  let E := LinearEquiv.ofFinrankEq (irreducibleSpace c) ℂ (by
    rw [show Module.finrank ℂ ↥(irreducibleSpace c) = irreducibleDegree c from rfl,
      hdeg, Module.finrank_self])
  exact Representation.Equiv.mk E (fun g => by
    ext v
    rw [irreducibleRep_eq_degOneChar_smul c hdeg g, hχ g]
    simp [signRep, Module.End.one_apply, smul_eq_mul])

/-- The degree-one classification: a degree-one index of the symmetric group
is the trivial or the sign index. -/
lemma degree_one_eq_trivial_or_sign {n : ℕ} (hn : 2 ≤ n)
    (c : IrreducibleIndex (Equiv.Perm (Fin n))) (hdeg : irreducibleDegree c = 1) :
    c = trivialIndex _ ∨ c = signIndex n := by
  rcases degOneChar_eq_one_or_sign hn c hdeg with h1 | hsign
  · left
    exact (trivialIndex_unique c).mp ⟨(repEquivTrivialOfChar c hdeg h1).symm⟩
  · right
    exact (irreducibleRep_complete (signRep (X := Fin n))).choose_spec.2 c
      ⟨repEquivSignOfChar c hdeg hsign⟩

end DegreeOne

/-! ## Slice 3a: line shapes and the deficit-zero characterization -/

section LineShapes

/-- The single-row diagram on `n` cells. -/
def rowDiagram (n : ℕ) : YoungDiagram := YoungDiagram.ofRowLens [n] (by
  simp [List.sortedGE_iff_pairwise])

lemma rowDiagram_rowLen_zero (n : ℕ) : (rowDiagram n).rowLen 0 = n := by
  have h := YoungDiagram.rowLen_ofRowLens (w := [n]) (hw := by
    simp [List.sortedGE_iff_pairwise]) ⟨0, by simp⟩
  simpa [rowDiagram] using h

lemma rowDiagram_card (n : ℕ) : (rowDiagram n).cells.card = n := by
  have hrow : (rowDiagram n).row 0 = (rowDiagram n).cells := by
    ext ⟨i, j⟩
    rw [YoungDiagram.mem_row_iff]
    constructor
    · rintro ⟨h, -⟩
      exact h
    · intro hc
      have h2 := YoungDiagram.mem_ofRowLens.mp hc
      obtain ⟨h1, -⟩ := h2
      have hi : i = 0 := by simp at h1; omega
      exact ⟨hc, hi⟩
  rw [← hrow, ← YoungDiagram.rowLen_eq_card, rowDiagram_rowLen_zero]

/-- The single-column diagram. -/
def colDiagram (n : ℕ) : YoungDiagram := (rowDiagram n).transpose

lemma colDiagram_card (n : ℕ) : (colDiagram n).cells.card = n := by
  rw [colDiagram, Tableau.card_transpose, rowDiagram_card]

lemma colDiagram_colLen_zero (n : ℕ) : (colDiagram n).colLen 0 = n := by
  rw [colDiagram, YoungDiagram.colLen_transpose, rowDiagram_rowLen_zero]

/-- A diagram fills one line iff its deficit vanishes. -/
lemma deficit_eq_zero_iff_line (μ : YoungDiagram) :
    Tableau.deficit μ = 0 ↔
      μ.rowLen 0 = μ.cells.card ∨ μ.colLen 0 = μ.cells.card := by
  have h1 : μ.rowLen 0 ≤ μ.cells.card := Tableau.topRow_le_card μ
  have h2 : μ.colLen 0 ≤ μ.cells.card := by
    rw [← YoungDiagram.rowLen_transpose, ← Tableau.card_transpose μ]
    exact Tableau.topRow_le_card μ.transpose
  unfold Tableau.deficit Tableau.maxLine
  omega

/-- Every diagram whose first row exhausts its cells is the row diagram. -/
lemma eq_rowDiagram_of_rowLen_card (μ : YoungDiagram) (h : μ.rowLen 0 = μ.cells.card) :
    μ = rowDiagram μ.cells.card := by
  apply YoungDiagram.ext
  ext ⟨i, j⟩
  rw [rowDiagram]
  show (i, j) ∈ μ.cells ↔ (i, j) ∈ YoungDiagram.ofRowLens [μ.cells.card] _
  rw [YoungDiagram.mem_ofRowLens]
  have hmem : μ.row 0 = μ.cells := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      exact (YoungDiagram.mem_row_iff.mp hx).1
    · rw [← YoungDiagram.rowLen_eq_card, h]
  constructor
  · intro hc
    have hc0 : (i, j) ∈ μ.row 0 := by rw [hmem]; exact hc
    have hfst : i = 0 := (YoungDiagram.mem_row_iff.mp hc0).2
    have hlt : j < μ.cells.card := by
      have h3 := μ.mem_iff_lt_rowLen.mp hc
      rw [hfst, h] at h3
      exact h3
    subst hfst
    refine ⟨by simp, ?_⟩
    simp
    exact hlt
  · rintro ⟨h1, h2⟩
    have hi : i = 0 := by simp at h1; omega
    subst hi
    simp at h2
    exact μ.mem_iff_lt_rowLen.mpr (by rwa [h])

/-- Every deficit-zero diagram is the row or the column. -/
lemma eq_row_or_col_of_deficit_zero (μ : YoungDiagram) (h : Tableau.deficit μ = 0) :
    μ = rowDiagram μ.cells.card ∨ μ = colDiagram μ.cells.card := by
  rcases deficit_eq_zero_iff_line μ |>.mp h with hrow | hcol
  · exact Or.inl (eq_rowDiagram_of_rowLen_card μ hrow)
  · right
    have hμ : μ.transpose = rowDiagram (μ.transpose).cells.card := by
      apply eq_rowDiagram_of_rowLen_card
      rw [YoungDiagram.rowLen_transpose, Tableau.card_transpose]
      exact hcol
    have h2 := congrArg YoungDiagram.transpose hμ
    rw [YoungDiagram.transpose_transpose] at h2
    simp only [Tableau.card_transpose] at h2
    exact h2

end LineShapes

/-! ## Slice 3b: the row/column Specht representations are trivial/sign -/

section RepLine

/-- The row index of a cell of the row diagram is zero. -/
lemma rowDiagram_row_eq_zero (n : ℕ) (y : (rowDiagram n).cells) :
    YoungTabloid.row (rowDiagram n) y = 0 := by
  have hy := y.2
  have h2 := YoungDiagram.mem_ofRowLens.mp hy
  obtain ⟨h1, -⟩ := h2
  show y.1.1 = 0
  simp at h1
  omega

/-- Tabloids of the row diagram are all equal. -/
lemma tabloid_row_subsingleton (n : ℕ) :
    Subsingleton (YoungTabloid.Tabloid (rowDiagram n)) := by
  constructor
  intro r s
  apply Subtype.ext
  funext x
  obtain ⟨p, hp⟩ := r.2
  obtain ⟨q, hq⟩ := s.2
  rw [hp, hq]
  show YoungTabloid.row (rowDiagram n) (p x) = YoungTabloid.row (rowDiagram n) (q x)
  rw [rowDiagram_row_eq_zero, rowDiagram_row_eq_zero]

/-- Relabeling a row tabloid does nothing. -/
lemma relabel_row_id (n : ℕ) (g : Equiv.Perm (rowDiagram n).cells)
    (r : YoungTabloid.Tabloid (rowDiagram n)) :
    YoungTabloid.relabel (rowDiagram n) g r = r := by
  apply Subtype.ext
  funext x
  rw [YoungTabloid.relabel_apply]
  obtain ⟨p, hp⟩ := r.2
  rw [hp]
  show YoungTabloid.row (rowDiagram n) (p (g⁻¹ x)) =
    YoungTabloid.row (rowDiagram n) (p x)
  rw [rowDiagram_row_eq_zero, rowDiagram_row_eq_zero]

/-- The tabloid space of the row diagram is one-dimensional. -/
lemma finrank_tabloidRep_row (n : ℕ) :
    Module.finrank ℂ (EuclideanSpace ℂ (YoungTabloid.Tabloid (rowDiagram n))) = 1 := by
  have hsub := tabloid_row_subsingleton n
  rw [finrank_euclideanSpace]
  have : Fintype.card (YoungTabloid.Tabloid (rowDiagram n)) = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨YoungTabloid.canonical _, fun b => Subsingleton.elim b _⟩
  rw [this]

/-- Every cell of the column diagram has column index zero. -/
lemma colDiagram_col_eq_zero (n : ℕ) (y : (colDiagram n).cells) :
    YoungTabloid.col (colDiagram n) y = 0 := by
  show y.1.2 = 0
  have hy : y.1 ∈ (rowDiagram n).transpose.cells := y.2
  have h2 := YoungDiagram.mem_transpose.mp hy
  have h3 := YoungDiagram.mem_ofRowLens.mp h2
  obtain ⟨h1, -⟩ := h3
  simp at h1
  omega

/-- Every permutation of the column diagram's cells lies in the column group. -/
lemma columnGroup_col_top (n : ℕ) :
    YoungTabloid.columnGroup (colDiagram n) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  show ∀ x, YoungTabloid.col (colDiagram n) (g x) = YoungTabloid.col (colDiagram n) x
  intro x
  rw [colDiagram_col_eq_zero, colDiagram_col_eq_zero]

/-- The Specht submodule of the row diagram is one-dimensional: it is a
nonzero submodule of the one-dimensional tabloid space (it contains the
polytabloid). -/
lemma finrank_spechtSub_row (n : ℕ) :
    Module.finrank ℂ ↥(YoungTabloid.spechtSub (rowDiagram n)).toSubmodule = 1 := by
  have hle : Module.finrank ℂ ↥(YoungTabloid.spechtSub (rowDiagram n)).toSubmodule ≤ 1 := by
    calc Module.finrank ℂ ↥(YoungTabloid.spechtSub (rowDiagram n)).toSubmodule
        ≤ Module.finrank ℂ (EuclideanSpace ℂ (YoungTabloid.Tabloid (rowDiagram n))) :=
          Submodule.finrank_le _
      _ = 1 := finrank_tabloidRep_row n
  have hpos : 0 < Module.finrank ℂ ↥(YoungTabloid.spechtSub (rowDiagram n)).toSubmodule := by
    have hne : (⟨YoungTabloid.polytabloid (rowDiagram n),
        YoungTabloid.polytabloid_mem_specht _⟩ :
        ↥(YoungTabloid.spechtSub (rowDiagram n)).toSubmodule) ≠ 0 := by
      intro h
      exact YoungTabloid.polytabloid_ne_zero _ (congrArg Subtype.val h)
    set_option linter.style.haveILetI false in
    haveI : Nontrivial ↥(YoungTabloid.spechtSub (rowDiagram n)).toSubmodule :=
      nontrivial_iff.mpr ⟨_, 0, hne⟩
    exact Module.finrank_pos
  omega

/-- The column group acts on the column polytabloid by the sign. -/
lemma tabloidRep_col_polytabloid (n : ℕ) (g : Equiv.Perm (colDiagram n).cells) :
    YoungTabloid.tabloidRep (colDiagram n) g (YoungTabloid.polytabloid (colDiagram n)) =
      YoungTabloid.signC g • YoungTabloid.polytabloid (colDiagram n) := by
  have hg : g ∈ YoungTabloid.columnGroup (colDiagram n) := by
    rw [columnGroup_col_top n]
    trivial
  have h := congrArg Subtype.val
    (YoungTabloid.polytabloid_specht_sign (colDiagram n) ⟨g, hg⟩)
  exact h

/-- The Specht submodule of the column diagram is one-dimensional: every
generator is a scalar multiple of the polytabloid (the column group is
everything and acts by the sign), and the polytabloid is nonzero. -/
lemma finrank_spechtSub_col (n : ℕ) :
    Module.finrank ℂ ↥(YoungTabloid.spechtSub (colDiagram n)).toSubmodule = 1 := by
  have hspan : (YoungTabloid.spechtSub (colDiagram n)).toSubmodule ≤
      Submodule.span ℂ {YoungTabloid.polytabloid (colDiagram n)} := by
    show Submodule.span ℂ (Set.range fun g => YoungTabloid.tabloidRep (colDiagram n) g
        (YoungTabloid.polytabloid (colDiagram n))) ≤ _
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    show YoungTabloid.tabloidRep (colDiagram n) g (YoungTabloid.polytabloid (colDiagram n)) ∈
      Submodule.span ℂ {YoungTabloid.polytabloid (colDiagram n)}
    rw [tabloidRep_col_polytabloid n g]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have hle : Module.finrank ℂ ↥(YoungTabloid.spechtSub (colDiagram n)).toSubmodule ≤ 1 :=
    (Submodule.finrank_mono hspan).trans
      (finrank_span_singleton (YoungTabloid.polytabloid_ne_zero _)).le
  have hpos : 0 < Module.finrank ℂ ↥(YoungTabloid.spechtSub (colDiagram n)).toSubmodule := by
    have hne : (⟨YoungTabloid.polytabloid (colDiagram n),
        YoungTabloid.polytabloid_mem_specht _⟩ :
        ↥(YoungTabloid.spechtSub (colDiagram n)).toSubmodule) ≠ 0 := by
      intro h
      exact YoungTabloid.polytabloid_ne_zero _ (congrArg Subtype.val h)
    set_option linter.style.haveILetI false in
    haveI : Nontrivial ↥(YoungTabloid.spechtSub (colDiagram n)).toSubmodule :=
      nontrivial_iff.mpr ⟨_, 0, hne⟩
    exact Module.finrank_pos
  omega

/-- The row shape, as an element of `Shape n`. -/
def rowShape (n : ℕ) : DiagramCounting.Shape n := ⟨rowDiagram n, rowDiagram_card n⟩

/-- The column shape, as an element of `Shape n`. -/
def colShape (n : ℕ) : DiagramCounting.Shape n := ⟨colDiagram n, colDiagram_card n⟩

/-- The row shape has zero deficit. -/
lemma deficit_rowShape (n : ℕ) : Tableau.deficit (rowShape n).1 = 0 := by
  show Tableau.deficit (rowDiagram n) = 0
  rw [deficit_eq_zero_iff_line]
  left
  rw [rowDiagram_rowLen_zero, rowDiagram_card]

/-- The column shape has zero deficit. -/
lemma deficit_colShape (n : ℕ) : Tableau.deficit (colShape n).1 = 0 := by
  show Tableau.deficit (colDiagram n) = 0
  rw [deficit_eq_zero_iff_line]
  right
  rw [colDiagram_colLen_zero, colDiagram_card]

/-- The degree of the index of a shape is the dimension of its Specht
submodule. -/
lemma irreducibleDegree_index_eq_finrank_specht {n : ℕ} (μ : DiagramCounting.Shape n) :
    irreducibleDegree (SpechtActual.index μ) =
      Module.finrank ℂ ↥(YoungTabloid.spechtSub μ.1).toSubmodule := by
  obtain ⟨e⟩ := SpechtActual.index_spec μ
  exact e.toLinearEquiv.finrank_eq

/-- The row shape has degree one. -/
lemma irreducibleDegree_index_rowShape (n : ℕ) :
    irreducibleDegree (SpechtActual.index (rowShape n)) = 1 := by
  rw [irreducibleDegree_index_eq_finrank_specht]
  exact finrank_spechtSub_row n

/-- The column shape has degree one. -/
lemma irreducibleDegree_index_colShape (n : ℕ) :
    irreducibleDegree (SpechtActual.index (colShape n)) = 1 := by
  rw [irreducibleDegree_index_eq_finrank_specht]
  exact finrank_spechtSub_col n

/-- Relabeling acts trivially on the row tabloid space. -/
lemma tabloidRep_row_apply (n : ℕ) (g : Equiv.Perm (rowDiagram n).cells)
    (f : EuclideanSpace ℂ (YoungTabloid.Tabloid (rowDiagram n))) :
    YoungTabloid.tabloidRep (rowDiagram n) g f = f := by
  apply PiLp.ext
  intro r
  rw [YoungTabloid.tabloidRep_apply, relabel_row_id]

/-- The same statement with the diagram seen through `rowShape`. -/
lemma tabloidRep_rowShape_apply (n : ℕ) (g : Equiv.Perm (rowShape n).1.cells)
    (f : EuclideanSpace ℂ (YoungTabloid.Tabloid (rowShape n).1)) :
    YoungTabloid.tabloidRep (rowShape n).1 g f = f :=
  tabloidRep_row_apply n g f

/-- The row representation of the symmetric group is the trivial action. -/
lemma rep_rowShape_one (n : ℕ) (g : Equiv.Perm (Fin n)) :
    SpechtActual.rep (rowShape n) g = 1 := by
  ext v r
  rw [Module.End.one_apply]
  show YoungTabloid.tabloidRep (rowShape n).1
      ((SpechtActual.labels (rowShape n)).symm.permCongrHom.toMonoidHom g) v.1 r = v.1 r
  rw [tabloidRep_rowShape_apply]

/-- The row representation is equivalent to the trivial representation. -/
def repEquivTrivialRow (n : ℕ) :
    Representation.Equiv (SpechtActual.rep (rowShape n))
      (Representation.trivial ℂ (Equiv.Perm (Fin n)) ℂ) := by
  let E := LinearEquiv.ofFinrankEq (YoungTabloid.spechtSub (rowDiagram n)).toSubmodule ℂ (by
    rw [finrank_spechtSub_row, Module.finrank_self])
  exact Representation.Equiv.mk E (fun g => by
    ext v
    rw [rep_rowShape_one]
    simp [Representation.trivial_apply, Module.End.one_apply])

/-- The index of the row shape is the trivial index. -/
lemma index_rowShape (n : ℕ) :
    SpechtActual.index (rowShape n) = trivialIndex (Equiv.Perm (Fin n)) := by
  obtain ⟨e₁⟩ := SpechtActual.index_spec (rowShape n)
  exact (trivialIndex_unique _).mp ⟨(repEquivTrivialRow n).symm.trans e₁.symm⟩

/-- For `n ≥ 2` the row and column diagrams differ. -/
lemma rowDiagram_ne_colDiagram {n : ℕ} (hn : 2 ≤ n) : rowDiagram n ≠ colDiagram n := by
  intro heq
  have hcell : ((0, 1) : ℕ × ℕ) ∈ (rowDiagram n).cells := by
    apply YoungDiagram.mem_iff_lt_rowLen.mpr
    rw [rowDiagram_rowLen_zero]
    omega
  have h1 := colDiagram_col_eq_zero n ⟨(0, 1), heq ▸ hcell⟩
  change (1 : ℕ) = 0 at h1
  exact Nat.one_ne_zero h1

/-- The index of the column shape is the sign index (for `n ≥ 2`): it has
degree one, and it is not the trivial index since the row shape already
occupies it (the index map is injective). -/
lemma index_colShape {n : ℕ} (hn : 2 ≤ n) :
    SpechtActual.index (colShape n) = signIndex n := by
  rcases degree_one_eq_trivial_or_sign hn _ (irreducibleDegree_index_colShape n) with
    h | h
  · exfalso
    have hsr : colShape n = rowShape n :=
      SpechtActual.index_injective n (h.trans (index_rowShape n).symm)
    exact rowDiagram_ne_colDiagram hn (congrArg Subtype.val hsr).symm
  · exact h

end RepLine

/-! ## Slice 3c: the degree-sum bridge to the tableau majorant

The sum of `(degree)^{-s}` over the indices of degree `> 1` is, after
reindexing along `indexEquiv`, pointwise majorized by the inverse tableau
weights (negative powers flip `standardCount ≤ degree`), hence by
`nontrivialSum`, which tends to zero (`TableauLimits`). -/

section SumBridge

open Filter

/-- A shape of zero deficit is the row or the column shape. -/
lemma eq_rowShape_or_colShape_of_deficit_zero {n : ℕ} (μ : DiagramCounting.Shape n)
    (h : Tableau.deficit μ.1 = 0) : μ = rowShape n ∨ μ = colShape n := by
  rcases eq_row_or_col_of_deficit_zero μ.1 h with hrow | hcol
  · left
    exact Subtype.ext (hrow.trans (congrArg rowDiagram μ.2))
  · right
    exact Subtype.ext (hcol.trans (congrArg colDiagram μ.2))

/-- Every index has degree at least one (its Specht module contains the
nonzero polytabloid). -/
lemma one_le_irreducibleDegree_index {n : ℕ} (μ : DiagramCounting.Shape n) :
    1 ≤ irreducibleDegree (SpechtActual.index μ) := by
  rw [irreducibleDegree_index_eq_finrank_specht]
  have hne : (⟨YoungTabloid.polytabloid μ.1, YoungTabloid.polytabloid_mem_specht μ.1⟩ :
      ↥(YoungTabloid.spechtSub μ.1).toSubmodule) ≠ 0 := by
    intro h
    exact YoungTabloid.polytabloid_ne_zero _ (congrArg Subtype.val h)
  set_option linter.style.haveILetI false in
  haveI : Nontrivial ↥(YoungTabloid.spechtSub μ.1).toSubmodule :=
    nontrivial_iff.mpr ⟨_, 0, hne⟩
  have hpos : 0 < Module.finrank ℂ ↥(YoungTabloid.spechtSub μ.1).toSubmodule :=
    Module.finrank_pos
  omega

/-- For `n ≥ 2`, an index has degree greater than one iff its shape is
neither the row nor the column. -/
lemma deg_gt_one_iff {n : ℕ} (hn : 2 ≤ n) (μ : DiagramCounting.Shape n) :
    1 < irreducibleDegree (SpechtActual.index μ) ↔ μ ≠ rowShape n ∧ μ ≠ colShape n := by
  constructor
  · intro h
    constructor
    · intro heq
      subst heq
      rw [irreducibleDegree_index_rowShape] at h
      exact (lt_irrefl 1 h).elim
    · intro heq
      subst heq
      rw [irreducibleDegree_index_colShape] at h
      exact (lt_irrefl 1 h).elim
  · intro h
    by_contra hle
    replace hle := not_lt.mp hle
    have h1 : irreducibleDegree (SpechtActual.index μ) = 1 :=
      le_antisymm hle (one_le_irreducibleDegree_index μ)
    rcases degree_one_eq_trivial_or_sign hn _ h1 with ht | hs
    · exact h.1 (SpechtActual.index_injective n (ht.trans (index_rowShape n).symm))
    · exact h.2 (SpechtActual.index_injective n (hs.trans (index_colShape hn).symm))

/-- For `n ≥ 2`, degree greater than one corresponds to positive deficit. -/
lemma deg_gt_one_iff_deficit_ne_zero {n : ℕ} (hn : 2 ≤ n) (μ : DiagramCounting.Shape n) :
    1 < irreducibleDegree (SpechtActual.index μ) ↔ Tableau.deficit μ.1 ≠ 0 := by
  rw [deg_gt_one_iff hn μ]
  constructor
  · rintro ⟨h1, h2⟩ hd0
    rcases eq_rowShape_or_colShape_of_deficit_zero μ hd0 with hrow | hcol
    · exact h1 hrow
    · exact h2 hcol
  · intro hd
    constructor
    · intro heq
      subst heq
      exact hd (deficit_rowShape n)
    · intro heq
      subst heq
      exact hd (deficit_colShape n)

/-- The degree-sum over indices of degree greater than one is majorized by
the nontrivial tableau sum. -/
lemma degreeSum_le_nontrivialSum {n : ℕ} (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s) :
    (∑ c : IrreducibleIndex (Equiv.Perm (Fin n)),
      if 1 < irreducibleDegree c then (irreducibleDegree c : ℝ)^(-s) else 0)
      ≤ TableauZeta.nontrivialSum n s := by
  classical
  calc (∑ c : IrreducibleIndex (Equiv.Perm (Fin n)),
        if 1 < irreducibleDegree c then (irreducibleDegree c : ℝ)^(-s) else 0)
      = ∑ μ : DiagramCounting.Shape n,
        (if 1 < irreducibleDegree (SpechtActual.index μ)
          then (irreducibleDegree (SpechtActual.index μ) : ℝ)^(-s) else 0) := by
        rw [← Equiv.sum_comp (SpechtActual.indexEquiv n)
          (fun c => if 1 < irreducibleDegree c then (irreducibleDegree c : ℝ)^(-s) else 0)]
        exact Finset.sum_congr rfl (fun μ _ => rfl)
    _ = ∑ μ : DiagramCounting.Shape n,
        (if Tableau.deficit μ.1 ≠ 0
          then (irreducibleDegree (SpechtActual.index μ) : ℝ)^(-s) else 0) := by
        apply Finset.sum_congr rfl
        intro μ _
        exact if_congr (deg_gt_one_iff_deficit_ne_zero hn μ) rfl rfl
    _ ≤ ∑ μ : DiagramCounting.Shape n, TableauZeta.inverseWeight s μ.1 := by
        apply Finset.sum_le_sum
        intro μ _
        unfold TableauZeta.inverseWeight
        by_cases hd : Tableau.deficit μ.1 = 0
        · rw [ite_eq_right (not_not.mpr hd), ite_eq_left hd]
        · rw [ite_eq_left hd, ite_eq_right hd]
          exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast Tableau.standardCount_pos μ.1)
            (by exact_mod_cast SpechtActual.standardCount_le_degree μ)
            (neg_nonpos.mpr hs.le)
    _ = TableauZeta.nontrivialSum n s := rfl

/-- The degree sum tends to zero along `n → ∞`. -/
theorem degreeSum_tendsto_zero (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n => ∑ c : IrreducibleIndex (Equiv.Perm (Fin n)),
      if 1 < irreducibleDegree c then (irreducibleDegree c : ℝ)^(-s) else 0)
      atTop (nhds 0) := by
  classical
  refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_
    (TableauZeta.nontrivialSum_tendsto_zero s hs)
  · apply Finset.sum_nonneg
    intro c _
    split_ifs
    · positivity
    · exact le_refl 0
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact degreeSum_le_nontrivialSum hn s hs

end SumBridge

/-! ## Slice 3c (cont.): the energy split

The nontrivial energy of the `r`-th convolution power splits into the sign
term (exactly the `2r`-th power of the sign mean, the sign index being
one-dimensional) and the degree->1 terms, each bounded pointwise by the
operator-norm hypothesis through `hsNormSq_convPower_le`; the degree sum is
then majorized by the bridge of the previous section. -/

section EnergySplit

/-- Every irreducible index has degree at least one (pull back along the
index bijection to the shape side, where the polytabloid is nonzero). -/
lemma one_le_irreducibleDegree {n : ℕ} (c : IrreducibleIndex (Equiv.Perm (Fin n))) :
    1 ≤ irreducibleDegree c := by
  have h := one_le_irreducibleDegree_index ((SpechtActual.indexEquiv n).symm c)
  rwa [show SpechtActual.index ((SpechtActual.indexEquiv n).symm c) = c from
    Equiv.apply_symm_apply (SpechtActual.indexEquiv n) c] at h

/-- The nontrivial energy splits off the sign term (which has degree one). -/
lemma nontrivialEnergy_eq_sign_add {n : ℕ} (hn : 2 ≤ n) (f : Equiv.Perm (Fin n) → ℝ) :
    nontrivialEnergy f =
      hsNormSq (V := irreducibleSpace (signIndex n))
        (complexFourier (V := irreducibleSpace (signIndex n)) (irreducibleRep (signIndex n))
          (fun g => (f g : ℂ))) +
        ∑ c ∈ (Finset.univ.erase (trivialIndex (Equiv.Perm (Fin n)))).erase (signIndex n),
          (irreducibleDegree c : ℝ) *
            hsNormSq (V := irreducibleSpace c) (complexFourier (V := irreducibleSpace c)
              (irreducibleRep c) (fun g => (f g : ℂ))) := by
  classical
  have hmem : signIndex n ∈ Finset.univ.erase (trivialIndex (Equiv.Perm (Fin n))) :=
    Finset.mem_erase.mpr ⟨signIndex_ne_trivialIndex hn, Finset.mem_univ _⟩
  unfold nontrivialEnergy
  rw [← Finset.sum_erase_add _ _ hmem, irreducibleDegree_signIndex]
  simp only [Nat.cast_one, one_mul]
  exact add_comm _ _

/-- The Hilbert–Schmidt norm squared of a scalar multiple of the identity. -/
lemma hsNormSq_smul_one {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (z : ℂ) :
    hsNormSq (z • 1 : Module.End ℂ V) = ‖z‖ ^ 2 * (Module.finrank ℂ V : ℝ) := by
  rw [hsNormSq_eq_sum (stdOrthonormalBasis ℂ V)]
  have hterm : ∀ i : Fin (Module.finrank ℂ V),
      ‖(z • 1 : Module.End ℂ V) ((stdOrthonormalBasis ℂ V) i)‖ ^ 2 = ‖z‖ ^ 2 := by
    intro i
    rw [LinearMap.smul_apply, Module.End.one_apply, norm_smul,
      (stdOrthonormalBasis ℂ V).orthonormal.1, mul_one]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_comm]

/-- The energy of the `r`-th convolution power at the sign index is the
`2r`-th power of the sign mean. -/
lemma hsNormSq_signIndex_convPower (n : ℕ) (f : Equiv.Perm (Fin n) → ℝ) (r : ℕ) :
    hsNormSq (V := irreducibleSpace (signIndex n))
        (complexFourier (V := irreducibleSpace (signIndex n)) (irreducibleRep (signIndex n))
          (fun g => ((BinaryCoordinateSweeps.convolutionPower f r g : ℝ) : ℂ))) =
      (∑ g, f g * BinaryCoordinateSweeps.realSign g) ^ (2 * r) := by
  have hS : (∑ g, (f g : ℂ) * YoungTabloid.signC g) =
      ((∑ g, f g * BinaryCoordinateSweeps.realSign g : ℝ) : ℂ) := by
    simp only [signC_eq_realSign, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  have hpow : ∀ (S : ℂ) (k : ℕ),
      (S • 1 : Module.End ℂ ↥(irreducibleSpace (signIndex n))) ^ k = S ^ k • 1 := by
    intro S k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, smul_mul_assoc, one_mul, smul_smul, ← pow_succ]
  rw [← complexConvolutionPower_ofReal, complexFourier_convPower, complexFourier_signIndex,
    hS, hpow, hsNormSq_smul_one]
  show ‖((∑ g, f g * BinaryCoordinateSweeps.realSign g : ℝ) : ℂ) ^ r‖ ^ 2 *
      (irreducibleDegree (signIndex n) : ℝ) =
    (∑ g, f g * BinaryCoordinateSweeps.realSign g) ^ (2 * r)
  rw [irreducibleDegree_signIndex, Nat.cast_one, mul_one, ← Complex.ofReal_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, ← pow_mul, mul_comm r 2]

/-- Pointwise bound on a degree->1 energy term from the operator-norm bound
at that index. (The bound is taken already instantiated at `irreducibleRep c`;
the challenge's `Type*`-quantified hypothesis cannot be applied to the
`Type 0` carrier inside a universe-polymorphic proof — instantiation happens
at the assembly site.) -/
lemma deg_gt_one_energy_term_le {n : ℕ} {A β : ℝ} (_hA : 0 < A) (r : ℕ)
    (f : Equiv.Perm (Fin n) → ℝ)
    (c : IrreducibleIndex (Equiv.Perm (Fin n))) (hc : 1 < irreducibleDegree c)
    (hF : ‖LinearMap.toContinuousLinearMap (complexFourier (V := irreducibleSpace c)
        (irreducibleRep c) (fun g => (f g : ℂ)))‖
      ≤ A * (irreducibleDegree c : ℝ) ^ (-β)) :
    (irreducibleDegree c : ℝ) * hsNormSq (V := irreducibleSpace c)
        (complexFourier (V := irreducibleSpace c) (irreducibleRep c)
          (fun g => ((BinaryCoordinateSweeps.convolutionPower f r g : ℝ) : ℂ))) ≤
      A ^ (2 * r) * (irreducibleDegree c : ℝ) ^ (2 - 2 * (r : ℝ) * β) := by
  have hD : (0 : ℝ) < irreducibleDegree c := by exact_mod_cast zero_lt_one.trans hc
  have hpow : ((irreducibleDegree c : ℝ) ^ (-β)) ^ (2 * r) =
      (irreducibleDegree c : ℝ) ^ (-(2 * (r : ℝ) * β)) := by
    rw [← Real.rpow_natCast _ (2 * r), ← Real.rpow_mul hD.le]
    congr 1
    push_cast
    ring
  have hcomb : (irreducibleDegree c : ℝ) * ((irreducibleDegree c : ℝ) *
      ((irreducibleDegree c : ℝ) ^ (-(2 * (r : ℝ) * β)))) =
      (irreducibleDegree c : ℝ) ^ (2 - 2 * (r : ℝ) * β) := by
    rw [show (2 : ℝ) - 2 * (r : ℝ) * β = 1 + 1 + (-(2 * (r : ℝ) * β)) by ring,
      Real.rpow_add hD, Real.rpow_add hD, Real.rpow_one]
    ring
  calc (irreducibleDegree c : ℝ) * hsNormSq (V := irreducibleSpace c)
        (complexFourier (V := irreducibleSpace c) (irreducibleRep c)
          (fun g => ((BinaryCoordinateSweeps.convolutionPower f r g : ℝ) : ℂ)))
      ≤ (irreducibleDegree c : ℝ) * ((irreducibleDegree c : ℝ) *
          ‖LinearMap.toContinuousLinearMap
            (complexFourier (irreducibleRep c) (fun g => (f g : ℂ)))‖ ^ (2 * r)) :=
        mul_le_mul_of_nonneg_left (hsNormSq_convPower_le _ _ _) hD.le
    _ ≤ (irreducibleDegree c : ℝ) * ((irreducibleDegree c : ℝ) *
          (A * (irreducibleDegree c : ℝ) ^ (-β)) ^ (2 * r)) := by
        apply mul_le_mul_of_nonneg_left _ hD.le
        apply mul_le_mul_of_nonneg_left _ hD.le
        have h0 : (0 : ℝ) ≤ ‖LinearMap.toContinuousLinearMap
            (complexFourier (V := irreducibleSpace c) (irreducibleRep c)
              (fun g => (f g : ℂ)))‖ := by positivity
        exact pow_le_pow_left₀ h0 hF _
    _ = A ^ (2 * r) * (irreducibleDegree c : ℝ) ^ (2 - 2 * (r : ℝ) * β) := by
        rw [mul_pow, hpow]
        have hcomm : (irreducibleDegree c : ℝ) * ((irreducibleDegree c : ℝ) *
            (A ^ (2 * r) * (irreducibleDegree c : ℝ) ^ (-(2 * (r : ℝ) * β)))) =
            A ^ (2 * r) * ((irreducibleDegree c : ℝ) * ((irreducibleDegree c : ℝ) *
              (irreducibleDegree c : ℝ) ^ (-(2 * (r : ℝ) * β)))) := by ring
        rw [hcomm, hcomb]

/-- The nontrivial energy of the `r`-th convolution power is bounded by the
`2r`-th power of the sign mean plus `A^{2r}` times the degree sum. The
operator-norm bound is taken already instantiated at each `irreducibleRep c`
(see `deg_gt_one_energy_term_le` for why the challenge's `Type*` hypothesis
cannot be applied directly inside a universe-polymorphic proof). -/
lemma nontrivialEnergy_convPower_le {n : ℕ} (hn : 2 ≤ n) {A β : ℝ} (hA : 0 < A) (r : ℕ)
    (f : Equiv.Perm (Fin n) → ℝ)
    (hopc : ∀ c : IrreducibleIndex (Equiv.Perm (Fin n)), 1 < irreducibleDegree c →
      ‖LinearMap.toContinuousLinearMap (complexFourier (V := irreducibleSpace c)
          (irreducibleRep c) (fun g => (f g : ℂ)))‖
        ≤ A * (irreducibleDegree c : ℝ) ^ (-β)) :
    nontrivialEnergy (BinaryCoordinateSweeps.convolutionPower f r) ≤
      (∑ g, f g * BinaryCoordinateSweeps.realSign g) ^ (2 * r) +
        A ^ (2 * r) * (∑ c : IrreducibleIndex (Equiv.Perm (Fin n)),
          if 1 < irreducibleDegree c
            then (irreducibleDegree c : ℝ) ^ (2 - 2 * (r : ℝ) * β) else 0) := by
  classical
  have hdeg1 : ∀ c ∈ (Finset.univ.erase (trivialIndex (Equiv.Perm (Fin n)))).erase
      (signIndex n), 1 < irreducibleDegree c := by
    intro c hc
    obtain ⟨hneS, hmem1⟩ := Finset.mem_erase.mp hc
    obtain ⟨hneT, -⟩ := Finset.mem_erase.mp hmem1
    by_contra hlt
    rw [not_lt] at hlt
    have h1 : irreducibleDegree c = 1 := le_antisymm hlt (one_le_irreducibleDegree c)
    rcases degree_one_eq_trivial_or_sign hn c h1 with ht | hs
    · exact hneT ht
    · exact hneS hs
  rw [nontrivialEnergy_eq_sign_add hn, hsNormSq_signIndex_convPower]
  apply add_le_add_right
  calc ∑ c ∈ (Finset.univ.erase (trivialIndex (Equiv.Perm (Fin n)))).erase (signIndex n),
        (irreducibleDegree c : ℝ) * hsNormSq (V := irreducibleSpace c)
          (complexFourier (V := irreducibleSpace c) (irreducibleRep c)
            (fun g => ((BinaryCoordinateSweeps.convolutionPower f r g : ℝ) : ℂ)))
      ≤ ∑ c ∈ (Finset.univ.erase (trivialIndex (Equiv.Perm (Fin n)))).erase (signIndex n),
        A ^ (2 * r) * (irreducibleDegree c : ℝ) ^ (2 - 2 * (r : ℝ) * β) := by
        apply Finset.sum_le_sum
        intro c hc
        exact deg_gt_one_energy_term_le hA r f c (hdeg1 c hc) (hopc c (hdeg1 c hc))
    _ = A ^ (2 * r) * ∑ c ∈ (Finset.univ.erase (trivialIndex (Equiv.Perm (Fin n)))).erase
          (signIndex n), (irreducibleDegree c : ℝ) ^ (2 - 2 * (r : ℝ) * β) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ A ^ (2 * r) * ∑ c : IrreducibleIndex (Equiv.Perm (Fin n)),
          if 1 < irreducibleDegree c
            then (irreducibleDegree c : ℝ) ^ (2 - 2 * (r : ℝ) * β) else 0 := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hA.le _)
        rw [← Finset.sum_filter]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro c hc
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hdeg1 c hc⟩
        · intro c _ _
          positivity

end EnergySplit

end
end PartialPermutation

end OAI
