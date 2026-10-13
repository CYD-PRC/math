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

/-- The Hilbert–Schmidt norm of a convolution power, in pure HS form:
`hsNormSq (f̂^{*r}) ≤ (hsNormSq f̂)^r` (submultiplicativity `hsNormSq_pow_le`
behind the Fourier–convolution bridge). Generic in `V` — do NOT inline this
rewrite at a giant subtype carrier (the `irreducibleSpace c` elaboration wall);
apply it, as `deg_gt_one_energy_term_le_hs` does. -/
lemma hsNormSq_convPower_le_hs {G : Type*} [Group G] [Fintype G]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (f : G → ℝ) {r : ℕ} (hr : 1 ≤ r) :
    hsNormSq (complexFourier ρ
        (fun g => ((BinaryCoordinateSweeps.convolutionPower f r g : ℝ) : ℂ)))
      ≤ (hsNormSq (complexFourier ρ (fun g => (f g : ℂ)))) ^ r := by
  rw [← complexConvolutionPower_ofReal, complexFourier_convPower]
  exact hsNormSq_pow_le _ hr

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

/-- Pointwise bound on a degree->1 energy term from the Hilbert–Schmidt bound
at that index (the HS analogue of `deg_gt_one_energy_term_le`, via the
submultiplicativity `hsNormSq_pow_le` in place of `hsNormSq_convPower_le`). -/
lemma deg_gt_one_energy_term_le_hs {n : ℕ} {A γ : ℝ} (_hA : 0 < A) (r : ℕ) (hr1 : 1 ≤ r)
    (f : Equiv.Perm (Fin n) → ℝ)
    (c : IrreducibleIndex (Equiv.Perm (Fin n))) (hc : 1 < irreducibleDegree c)
    (hF : hsNormSq (V := irreducibleSpace c) (complexFourier (V := irreducibleSpace c)
        (irreducibleRep c) (fun g => (f g : ℂ)))
      ≤ A * (irreducibleDegree c : ℝ) ^ (-γ)) :
    (irreducibleDegree c : ℝ) * hsNormSq (V := irreducibleSpace c)
        (complexFourier (V := irreducibleSpace c) (irreducibleRep c)
          (fun g => ((BinaryCoordinateSweeps.convolutionPower f r g : ℝ) : ℂ))) ≤
      A ^ r * (irreducibleDegree c : ℝ) ^ (1 - (r : ℝ) * γ) := by
  have hD : (0 : ℝ) < irreducibleDegree c := by exact_mod_cast zero_lt_one.trans hc
  have h0 : (0 : ℝ) ≤ hsNormSq (V := irreducibleSpace c)
      (complexFourier (V := irreducibleSpace c) (irreducibleRep c) fun g => (f g : ℂ)) :=
    hsNormSq_nonneg _
  have hpow : ((irreducibleDegree c : ℝ) ^ (-γ)) ^ r =
      (irreducibleDegree c : ℝ) ^ (-((r : ℝ) * γ)) := by
    rw [← Real.rpow_natCast _ r, ← Real.rpow_mul hD.le]
    congr 1
    ring
  have hcomb : (irreducibleDegree c : ℝ) * (irreducibleDegree c : ℝ) ^ (-((r : ℝ) * γ)) =
      (irreducibleDegree c : ℝ) ^ (1 - (r : ℝ) * γ) := by
    rw [show (1 : ℝ) - (r : ℝ) * γ = 1 + (-((r : ℝ) * γ)) by ring,
      Real.rpow_add hD, Real.rpow_one]
  calc (irreducibleDegree c : ℝ) * hsNormSq (V := irreducibleSpace c)
        (complexFourier (V := irreducibleSpace c) (irreducibleRep c)
          (fun g => ((BinaryCoordinateSweeps.convolutionPower f r g : ℝ) : ℂ)))
      ≤ (irreducibleDegree c : ℝ) *
          (hsNormSq (V := irreducibleSpace c) (complexFourier (V := irreducibleSpace c)
            (irreducibleRep c) fun g => (f g : ℂ))) ^ r :=
        mul_le_mul_of_nonneg_left (hsNormSq_convPower_le_hs _ _ hr1) hD.le
    _ ≤ (irreducibleDegree c : ℝ) * (A * (irreducibleDegree c : ℝ) ^ (-γ)) ^ r :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hF r) hD.le
    _ = A ^ r * (irreducibleDegree c : ℝ) ^ (1 - (r : ℝ) * γ) := by
        rw [mul_pow, hpow]
        have hcomm : (irreducibleDegree c : ℝ) * (A ^ r *
            (irreducibleDegree c : ℝ) ^ (-((r : ℝ) * γ))) =
            A ^ r * ((irreducibleDegree c : ℝ) *
              (irreducibleDegree c : ℝ) ^ (-((r : ℝ) * γ))) := by ring
        rw [hcomm, hcomb]

/-- The Hilbert–Schmidt analogue of `nontrivialEnergy_convPower_le`: the
nontrivial energy of the `r`-th convolution power is bounded by the `2r`-th
power of the sign mean plus `A^r` times the degree sum with exponent
`1 − rγ` (paper Prop 2.5's HS case: `D‖f̂ʳ‖²_HS ≤ A^r D^{1−rγ}`). -/
lemma nontrivialEnergy_convPower_le_hs {n : ℕ} (hn : 2 ≤ n) {A γ : ℝ} (hA : 0 < A) (r : ℕ)
    (hr1 : 1 ≤ r)
    (f : Equiv.Perm (Fin n) → ℝ)
    (hhsc : ∀ c : IrreducibleIndex (Equiv.Perm (Fin n)), 1 < irreducibleDegree c →
      hsNormSq (V := irreducibleSpace c) (complexFourier (V := irreducibleSpace c)
          (irreducibleRep c) (fun g => (f g : ℂ)))
        ≤ A * (irreducibleDegree c : ℝ) ^ (-γ)) :
    nontrivialEnergy (BinaryCoordinateSweeps.convolutionPower f r) ≤
      (∑ g, f g * BinaryCoordinateSweeps.realSign g) ^ (2 * r) +
        A ^ r * (∑ c : IrreducibleIndex (Equiv.Perm (Fin n)),
          if 1 < irreducibleDegree c
            then (irreducibleDegree c : ℝ) ^ (1 - (r : ℝ) * γ) else 0) := by
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
        A ^ r * (irreducibleDegree c : ℝ) ^ (1 - (r : ℝ) * γ) := by
        apply Finset.sum_le_sum
        intro c hc
        exact deg_gt_one_energy_term_le_hs hA r hr1 f c (hdeg1 c hc) (hhsc c (hdeg1 c hc))
    _ = A ^ r * ∑ c ∈ (Finset.univ.erase (trivialIndex (Equiv.Perm (Fin n)))).erase
          (signIndex n), (irreducibleDegree c : ℝ) ^ (1 - (r : ℝ) * γ) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ A ^ r * ∑ c : IrreducibleIndex (Equiv.Perm (Fin n)),
          if 1 < irreducibleDegree c
            then (irreducibleDegree c : ℝ) ^ (1 - (r : ℝ) * γ) else 0 := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hA.le _)
        rw [← Finset.sum_filter]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro c hc
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hdeg1 c hc⟩
        · intro c _ _
          positivity

end EnergySplit

/-! ## Slice 4a: presentation transport along a linear equivalence

Why this exists (the probe record of 2026-10-11, RECON-G1 §19): applying the
challenge's `Type*`-quantified operator-norm hypothesis directly at
`irreducibleRep c` does not elaborate — the instance-path unification over the
giant subtype carrier `↥(irreducibleSpace c)` diverges (whnf/isDefEq timeouts
at 200k and 1.6M heartbeats). The clean carrier `EuclideanSpace ℂ (ULift (Fin d))`
accepts the same application quickly (probe Q13). So each irreducible
representation is transported along a linear (isometry) equivalence to the
clean carrier, the hypothesis is consumed there, and the bound is transported
back through norm invariance under conjugation.

What the transport preserves (per R-2): the dimension (`conjRep_finrank`),
irreducibility (`conjRep_isIrreducible`), unitarity (`conjRep_isUnitary`),
the operator-norm value of any endomorphism (`opNorm_conj`), and the
Hilbert–Schmidt norm value (`hsNormSq_conj`).

Binder-order discipline: every `Representation`/`Module.End`-typed argument
is elaborated in a plain `[AddCommGroup] [Module]` context (before any normed
binders enter the telescope) — the idiom that keeps applications to
`irreducibleRep c` cheap (the `complexFourier` idiom of DeficitPlancherel).
-/

section PresentationTransport

variable {G : Type} [Group G] [Fintype G]

/-- Conjugating a representation along a linear equivalence: `e ∘ ρ g ∘ e⁻¹`. -/
noncomputable def conjRep {V : Type*} [AddCommGroup V] [Module ℂ V] {W : Type*}
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) (ρ : Representation ℂ G V) :
    Representation ℂ G W :=
  (LinearEquiv.conjRingEquiv e).toMonoidHom.comp ρ

omit [Fintype G] in
lemma conjRep_apply {V : Type*} [AddCommGroup V] [Module ℂ V] {W : Type*}
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) (ρ : Representation ℂ G V) (g : G) (w : W) :
    conjRep e ρ g w = e (ρ g (e.symm w)) := rfl

omit [Fintype G] in
lemma conjRep_eq_conj {V : Type*} [AddCommGroup V] [Module ℂ V] {W : Type*}
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) (ρ : Representation ℂ G V) (g : G) :
    conjRep e ρ g = e.conj (ρ g) :=
  LinearMap.ext fun w => (conjRep_apply e ρ g w).trans
    (LinearEquiv.conj_apply_apply e (ρ g) w).symm

/-- The transported representation has the same dimension. -/
lemma conjRep_finrank {V : Type*} [AddCommGroup V] [Module ℂ V] {W : Type*}
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) :
    Module.finrank ℂ V = Module.finrank ℂ W := e.finrank_eq

/-- The Fourier transform of the transported representation is the
conjugation of the Fourier transform. -/
lemma complexFourier_conjRep {V : Type*} [AddCommGroup V] [Module ℂ V] {W : Type*}
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) (ρ : Representation ℂ G V) (F : G → ℂ) :
    complexFourier (conjRep e ρ) F = e.conj (complexFourier ρ F) := by
  show (∑ g, F g • conjRep e ρ g) = e.conj (∑ g, F g • ρ g)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [map_smul, conjRep_eq_conj]

/-- Conjugation by a linear equivalence transports subrepresentations. -/
noncomputable def subrepConjOrderIso {V : Type*} [AddCommGroup V] [Module ℂ V] {W : Type*}
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) (ρ : Representation ℂ G V) :
    Subrepresentation (conjRep e ρ) ≃o Subrepresentation ρ where
  toFun U := ⟨U.toSubmodule.map e.symm.toLinearMap, by
    intro g v hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    apply Submodule.mem_map.mpr
    refine ⟨conjRep e ρ g w, U.apply_mem_toSubmodule g hw, ?_⟩
    show e.symm (e (ρ g (e.symm w))) = ρ g (e.symm w)
    rw [LinearEquiv.symm_apply_apply]⟩
  invFun T := ⟨T.toSubmodule.map e.toLinearMap, by
    intro g v hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    apply Submodule.mem_map.mpr
    refine ⟨ρ g w, T.apply_mem_toSubmodule g hw, ?_⟩
    show e (ρ g w) = e (ρ g (e.symm (e w)))
    rw [LinearEquiv.symm_apply_apply]⟩
  left_inv U := Subrepresentation.ext (by
    show (U.toSubmodule.map e.symm.toLinearMap).map e.toLinearMap = U.toSubmodule
    rw [← Submodule.map_comp]
    have hid : e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id :=
      LinearMap.ext fun w => e.apply_symm_apply w
    rw [hid, Submodule.map_id])
  right_inv T := Subrepresentation.ext (by
    show (T.toSubmodule.map e.toLinearMap).map e.symm.toLinearMap = T.toSubmodule
    rw [← Submodule.map_comp]
    have hid : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id :=
      LinearMap.ext fun v => e.symm_apply_apply v
    rw [hid, Submodule.map_id])
  map_rel_iff' := by
    intro U₁ U₂
    show (U₁.toSubmodule.map e.symm.toLinearMap ≤ U₂.toSubmodule.map e.symm.toLinearMap) ↔
      U₁.toSubmodule ≤ U₂.toSubmodule
    constructor
    · intro h v hv
      have hmem : e.symm v ∈ U₁.toSubmodule.map e.symm.toLinearMap :=
        Submodule.mem_map.mpr ⟨v, hv, rfl⟩
      obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.mp (h hmem)
      have h2 : e.symm.toEquiv w = e.symm.toEquiv v := hwe
      have : w = v := e.symm.toEquiv.injective h2
      subst this
      exact hw
    · intro h
      exact Submodule.map_mono h

omit [Fintype G] in
/-- Conjugation preserves irreducibility (the subrepresentation lattices are
order-isomorphic). -/
lemma conjRep_isIrreducible {V : Type*} [AddCommGroup V] [Module ℂ V] {W : Type*}
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) (ρ : Representation ℂ G V)
    (h : Representation.IsIrreducible ρ) : Representation.IsIrreducible (conjRep e ρ) :=
  (OrderIso.isSimpleOrder_iff (subrepConjOrderIso e ρ)).mpr h

omit [Fintype G] in
/-- Conjugation by a linear isometry equivalence preserves unitarity. NOTE:
declared and proved here for the record (R-2); `hopc_of_hop` inlines the same
argument instead of applying this lemma, because applying a normed-context
lemma to `irreducibleRep c` hits the instance-path elaboration pathology
(RECord: the whnf timeout at this exact application). -/
lemma conjRep_isUnitary {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ρ : Representation ℂ G V) (e : V ≃ₗᵢ[ℂ] W) (hρ : IsUnitary ρ) :
    IsUnitary (conjRep e.toLinearEquiv ρ) := by
  intro g x y
  show inner ℂ (conjRep e.toLinearEquiv ρ g x) (conjRep e.toLinearEquiv ρ g y) = inner ℂ x y
  rw [conjRep_apply, conjRep_apply]
  have he : ∀ u v : V, inner ℂ (e.toLinearEquiv u) (e.toLinearEquiv v) = inner ℂ u v :=
    fun u v => LinearIsometryEquiv.inner_map_map e u v
  rw [he, hρ g]
  have h2 := he ((e.toLinearEquiv).symm x) ((e.toLinearEquiv).symm y)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h2
  exact h2.symm

/-- Conjugation by an isometry shrinks the operator norm by at most one. -/
lemma opNorm_conj_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (X : Module.End ℂ V) (e : V ≃ₗᵢ[ℂ] W) :
    ‖LinearMap.toContinuousLinearMap (e.toLinearEquiv.conj X)‖ ≤
      ‖LinearMap.toContinuousLinearMap X‖ := by
  have hE : LinearMap.toContinuousLinearMap (e.toLinearEquiv.conj X) =
      (LinearMap.toContinuousLinearMap e.toLinearEquiv.toLinearMap).comp
        ((LinearMap.toContinuousLinearMap X).comp
          (LinearMap.toContinuousLinearMap (e.toLinearEquiv).symm.toLinearMap)) := by
    ext w
    simp only [ContinuousLinearMap.comp_apply]
    rfl
  have he1 : ‖LinearMap.toContinuousLinearMap e.toLinearEquiv.toLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    calc ‖(LinearMap.toContinuousLinearMap e.toLinearEquiv.toLinearMap) x‖
        = ‖e x‖ := rfl
      _ = ‖x‖ := e.toLinearIsometry.norm_map x
      _ ≤ 1 * ‖x‖ := by rw [one_mul]
  have hs1 : ‖LinearMap.toContinuousLinearMap (e.toLinearEquiv).symm.toLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro w
    calc ‖(LinearMap.toContinuousLinearMap (e.toLinearEquiv).symm.toLinearMap) w‖
        = ‖e.symm w‖ := rfl
      _ = ‖w‖ := e.symm.toLinearIsometry.norm_map w
      _ ≤ 1 * ‖w‖ := by rw [one_mul]
  rw [hE]
  calc ‖_‖ ≤ ‖LinearMap.toContinuousLinearMap e.toLinearEquiv.toLinearMap‖ *
        ‖(LinearMap.toContinuousLinearMap X).comp
          (LinearMap.toContinuousLinearMap (e.toLinearEquiv).symm.toLinearMap)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖LinearMap.toContinuousLinearMap e.toLinearEquiv.toLinearMap‖ *
        (‖LinearMap.toContinuousLinearMap X‖ *
          ‖LinearMap.toContinuousLinearMap (e.toLinearEquiv).symm.toLinearMap‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ 1 * (‖LinearMap.toContinuousLinearMap X‖ * 1) := by
        apply mul_le_mul (he1)
        · exact mul_le_mul_of_nonneg_left hs1 (norm_nonneg _)
        · positivity
        · norm_num
    _ = ‖LinearMap.toContinuousLinearMap X‖ := by rw [one_mul, mul_one]

/-- Conjugating twice by inverse equivalences returns the endomorphism. -/
lemma conj_conj_symm {V : Type*} [AddCommGroup V] [Module ℂ V] {W : Type*}
    [AddCommGroup W] [Module ℂ W] (E : V ≃ₗ[ℂ] W) (X : Module.End ℂ V) :
    E.symm.conj (E.conj X) = X := by
  ext v
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
    LinearEquiv.symm_apply_apply]

/-- Conjugation by an isometry preserves the operator norm. -/
lemma opNorm_conj {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (X : Module.End ℂ V) (e : V ≃ₗᵢ[ℂ] W) :
    ‖LinearMap.toContinuousLinearMap (e.toLinearEquiv.conj X)‖ =
      ‖LinearMap.toContinuousLinearMap X‖ := by
  apply le_antisymm (opNorm_conj_le X e)
  have hE2 : e.symm.toLinearEquiv = (e.toLinearEquiv).symm := by
    ext w
    rfl
  have h2 := opNorm_conj_le (e.toLinearEquiv.conj X) e.symm
  rw [hE2, conj_conj_symm] at h2
  exact h2

/-- Conjugation by an isometry preserves the Hilbert–Schmidt norm squared. -/
lemma hsNormSq_conj {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (X : Module.End ℂ V)
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (e : V ≃ₗᵢ[ℂ] W) :
    hsNormSq (e.toLinearEquiv.conj X) = hsNormSq X := by
  let b := stdOrthonormalBasis ℂ V
  rw [hsNormSq_eq_sum (b.map e), hsNormSq_eq_sum b]
  apply Finset.sum_congr rfl
  intro i _
  rw [OrthonormalBasis.map_apply]
  have hsym : ∀ x : V, (e.toLinearEquiv).symm (e x) = x :=
    fun x => LinearIsometryEquiv.symm_apply_apply e x
  rw [LinearEquiv.conj_apply_apply, hsym]
  have hn : ∀ y : V, ‖e.toLinearEquiv y‖ = ‖y‖ := fun y => e.toLinearIsometry.norm_map y
  rw [hn]

universe u

/-- The operator-norm bound at `irreducibleRep c`, obtained by transporting
the representation to the clean carrier `EuclideanSpace ℂ (ULift (Fin d))`,
consuming the hypothesis there (fast: probe Q13), and transporting the bound
back through the conjugation invariances above. Direct consumption at the
subtype carrier does not elaborate (probes P0/P0b/Q8, whnf/isDefEq timeouts).

Universe note: `hop` here quantifies over `V : Type u` with `u` the lemma's
own universe parameter — when this lemma is applied to the challenge's
hypothesis (universe `u_1` of the theorem under proof), `u := u_1`, and the
transport carrier lives in `Type u₁` as required. -/
lemma hopc_of_hop {A β : ℝ} {f : (n : ℕ) → Equiv.Perm (Fin n) → ℝ}
    (hop : ∀ n, ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V),
        Representation.IsIrreducible ρ → IsUnitary ρ → 1 < Module.finrank ℂ V →
          ‖LinearMap.toContinuousLinearMap (complexFourier ρ (fun g => (f n g : ℂ)))‖
            ≤ A * (Module.finrank ℂ V : ℝ) ^ (-β))
    (n : ℕ) (c : IrreducibleIndex (Equiv.Perm (Fin n))) (hc : 1 < irreducibleDegree c) :
    ‖LinearMap.toContinuousLinearMap (complexFourier (V := irreducibleSpace c)
        (irreducibleRep c) (fun g => (f n g : ℂ)))‖
      ≤ A * (irreducibleDegree c : ℝ) ^ (-β) := by
  classical
  have hfr : Module.finrank ℂ ↥(irreducibleSpace c) = irreducibleDegree c := rfl
  let e : ↥(irreducibleSpace c) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (ULift.{u} (Fin (irreducibleDegree c))) :=
    (stdOrthonormalBasis ℂ ↥(irreducibleSpace c)).repr.trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        ((Equiv.cast (congrArg Fin hfr)).trans (Equiv.ulift.{u, 0}.symm)))
  have hfinW : Module.finrank ℂ (EuclideanSpace ℂ (ULift.{u} (Fin (irreducibleDegree c)))) =
      irreducibleDegree c := by
    rw [← hfr]
    exact e.toLinearEquiv.finrank_eq.symm
  have hρ'U : IsUnitary (conjRep e.toLinearEquiv (irreducibleRep c)) := by
    intro g x y
    rw [conjRep_apply, conjRep_apply]
    -- normalize the coercions: ⇑e.toLinearEquiv → ⇑e, ⇑(e.toLinearEquiv).symm → ⇑e.symm
    have hsymm : ∀ w : EuclideanSpace ℂ (ULift.{u} (Fin (irreducibleDegree c))),
        (e.toLinearEquiv).symm w = e.symm w := fun w => rfl
    rw [LinearIsometryEquiv.coe_toLinearEquiv, hsymm, hsymm]
    -- e preserves inner — via polarization (norms only; the LIE-slot
    -- application of `inner_map_map` does not elaborate on this carrier)
    have he : ∀ A B : ↥(irreducibleSpace c), inner ℂ (e A) (e B) = inner ℂ A B := by
      intro A B
      rw [Submodule.coe_inner]
      rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
      have he_norm : ∀ w : ↥(irreducibleSpace c), ‖e w‖ = ‖w‖ :=
        fun w => e.toLinearIsometry.norm_map w
      simp only [← map_add, ← map_sub, ← map_smul, he_norm, ← Submodule.coe_add,
        ← Submodule.coe_sub, ← Submodule.coe_smul, Submodule.norm_coe]
    rw [he]
    -- now: inner (ρc g (e.symm x)) (ρc g (e.symm y)) = inner x y — ρc is unitary
    rw [irreducibleRep_unitary c g]
    -- now: inner (e.symm x)(e.symm y) = inner x y — same polarization chain on e.symm
    have heS : ∀ u v : EuclideanSpace ℂ (ULift.{u} (Fin (irreducibleDegree c))),
        inner ℂ (e.symm u) (e.symm v) = inner ℂ u v := by
      intro u v
      rw [Submodule.coe_inner]
      rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
      have heS_norm : ∀ w : EuclideanSpace ℂ (ULift.{u} (Fin (irreducibleDegree c))),
          ‖e.symm w‖ = ‖w‖ := fun w => e.symm.toLinearIsometry.norm_map w
      simp only [← map_add, ← map_sub, ← map_smul, heS_norm, ← Submodule.coe_add,
        ← Submodule.coe_sub, ← Submodule.coe_smul, Submodule.norm_coe]
    exact heS x y
  have hb := hop n (EuclideanSpace ℂ (ULift.{u} (Fin (irreducibleDegree c))))
    (conjRep e.toLinearEquiv (irreducibleRep c))
    (conjRep_isIrreducible e.toLinearEquiv (irreducibleRep c) inferInstance)
    hρ'U
    (by rw [hfinW]; exact hc)
  rw [hfinW] at hb
  rw [complexFourier_conjRep e.toLinearEquiv (irreducibleRep c), opNorm_conj] at hb
  exact hb

/-- The HS-side bridge: the Hilbert–Schmidt bound at `irreducibleRep c` from
`hhs` consumed at the transported representation, with `hsNormSq_conj` giving
exact-value preservation. Mirrors `hopc_of_hop`'s proven inline structure
(the `transportEquiv`/`transportRep` def-form refactor made the rewrite
patterns unmatchable — the let-bound form is what compiles). Lives in this
section (next to `hopc_of_hop`) because `hs_energy_tendsto_zero` consumes it. -/
lemma hopcHs_of_hhs {A γ : ℝ} {f : (n : ℕ) → Equiv.Perm (Fin n) → ℝ}
    (hhs : ∀ n, ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V),
        Representation.IsIrreducible ρ → IsUnitary ρ → 1 < Module.finrank ℂ V →
          hsNormSq (complexFourier ρ (fun g => (f n g : ℂ))) ≤
            A * (Module.finrank ℂ V : ℝ) ^ (-γ))
    (n : ℕ) (c : IrreducibleIndex (Equiv.Perm (Fin n))) (hc : 1 < irreducibleDegree c) :
    hsNormSq (V := irreducibleSpace c) (complexFourier (V := irreducibleSpace c)
        (irreducibleRep c) (fun g => (f n g : ℂ))) ≤
      A * (irreducibleDegree c : ℝ) ^ (-γ) := by
  classical
  have hfr : Module.finrank ℂ ↥(irreducibleSpace c) = irreducibleDegree c := rfl
  let e : ↥(irreducibleSpace c) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (ULift.{u} (Fin (irreducibleDegree c))) :=
    (stdOrthonormalBasis ℂ ↥(irreducibleSpace c)).repr.trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        ((Equiv.cast (congrArg Fin hfr)).trans (Equiv.ulift.{u, 0}.symm)))
  have hfinW : Module.finrank ℂ (EuclideanSpace ℂ (ULift.{u} (Fin (irreducibleDegree c)))) =
      irreducibleDegree c := by
    rw [← hfr]
    exact e.toLinearEquiv.finrank_eq.symm
  have hρ'U : IsUnitary (conjRep e.toLinearEquiv (irreducibleRep c)) := by
    intro g x y
    rw [conjRep_apply, conjRep_apply]
    have hsymm : ∀ w : EuclideanSpace ℂ (ULift.{u} (Fin (irreducibleDegree c))),
        (e.toLinearEquiv).symm w = e.symm w := fun w => rfl
    rw [LinearIsometryEquiv.coe_toLinearEquiv, hsymm, hsymm]
    have he : ∀ A B : ↥(irreducibleSpace c), inner ℂ (e A) (e B) = inner ℂ A B := by
      intro A B
      rw [Submodule.coe_inner]
      rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
      have he_norm : ∀ w : ↥(irreducibleSpace c), ‖e w‖ = ‖w‖ :=
        fun w => e.toLinearIsometry.norm_map w
      simp only [← map_add, ← map_sub, ← map_smul, he_norm, ← Submodule.coe_add,
        ← Submodule.coe_sub, ← Submodule.coe_smul, Submodule.norm_coe]
    rw [he]
    rw [irreducibleRep_unitary c g]
    have heS : ∀ u v : EuclideanSpace ℂ (ULift.{u} (Fin (irreducibleDegree c))),
        inner ℂ (e.symm u) (e.symm v) = inner ℂ u v := by
      intro u v
      rw [Submodule.coe_inner]
      rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
      have heS_norm : ∀ w : EuclideanSpace ℂ (ULift.{u} (Fin (irreducibleDegree c))),
          ‖e.symm w‖ = ‖w‖ := fun w => e.symm.toLinearIsometry.norm_map w
      simp only [← map_add, ← map_sub, ← map_smul, heS_norm, ← Submodule.coe_add,
        ← Submodule.coe_sub, ← Submodule.coe_smul, Submodule.norm_coe]
    exact heS x y
  have hb := hhs n (EuclideanSpace ℂ (ULift.{u} (Fin (irreducibleDegree c))))
    (conjRep e.toLinearEquiv (irreducibleRep c))
    (conjRep_isIrreducible e.toLinearEquiv (irreducibleRep c) inferInstance)
    hρ'U
    (by rw [hfinW]; exact hc)
  rw [hfinW] at hb
  rw [complexFourier_conjRep e.toLinearEquiv (irreducibleRep c), hsNormSq_conj] at hb
  exact hb

end PresentationTransport

/-! ## Slice 4b: assembly of Proposition 2.5 (operator and Hilbert–Schmidt forms)

The convergence exit: `totalVariation (μ^{*r}) U ≤ (1 − mass f^{*r})/2 +
totalVariation (f^{*r}) U`, the second term squared-controlled by
`deficit_plancherel` + the energy split of slice 3c, and the energy pieces
tend to zero (sign-mean squeeze, the degree-sum bridge of slice 3c, and
`hopc_of_hop`/`hopcHs_of_hhs` for the transported hypothesis). -/

section Assembly

open Filter

/-- Mass of a convolution is the product of the masses. -/
lemma mass_convolution {G : Type*} [Group G] [Fintype G] (p q : G → ℝ) :
    mass (BinaryCoordinateSweeps.convolution p q) = mass p * mass q := by
  show (∑ g, ∑ x, p x * q (x⁻¹ * g)) = (∑ x, p x) * ∑ x, q x
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum]
  apply congrArg (p x * ·)
  exact Equiv.sum_comp (Equiv.mulLeft x⁻¹) (fun g' => q g')

/-- Mass of the empty convolution power (the point mass at 1). -/
lemma mass_pointMassOne {G : Type*} [Group G] [Fintype G] :
    mass (BinaryCoordinateSweeps.pointMassOne (G := G)) = 1 := by
  classical
  show (∑ g, BinaryCoordinateSweeps.pointMassOne (G := G) g) = 1
  simp only [BinaryCoordinateSweeps.pointMassOne]
  rw [Finset.sum_ite_eq']
  simp

/-- Mass of a convolution power is the power of the mass. -/
lemma mass_convolutionPower {G : Type*} [Group G] [Fintype G] (p : G → ℝ) (r : ℕ) :
    mass (BinaryCoordinateSweeps.convolutionPower p r) = mass p ^ r := by
  induction r with
  | zero =>
    show mass BinaryCoordinateSweeps.pointMassOne = 1
    exact mass_pointMassOne
  | succ k ih =>
    show mass (BinaryCoordinateSweeps.convolution p
        (BinaryCoordinateSweeps.convolutionPower p k)) = mass p ^ (k + 1)
    rw [mass_convolution, ih, pow_succ, mul_comm]

/-- Convolution of nonnegative functions is nonnegative. -/
lemma convolution_nonneg {G : Type*} [Group G] [Fintype G] {p q : G → ℝ}
    (hp : ∀ g, 0 ≤ p g) (hq : ∀ g, 0 ≤ q g) :
    ∀ g, 0 ≤ BinaryCoordinateSweeps.convolution p q g :=
  fun _ => Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (hq _))

/-- Convolution powers of a nonnegative function are nonnegative. -/
lemma convolutionPower_nonneg {G : Type*} [Group G] [Fintype G] {p : G → ℝ}
    (hp : ∀ g, 0 ≤ p g) (r : ℕ) : ∀ g, 0 ≤ BinaryCoordinateSweeps.convolutionPower p r g := by
  induction r with
  | zero =>
    intro g
    show 0 ≤ BinaryCoordinateSweeps.pointMassOne g
    unfold BinaryCoordinateSweeps.pointMassOne
    split_ifs <;> norm_num
  | succ k ih =>
    intro g
    show 0 ≤ BinaryCoordinateSweeps.convolution p (BinaryCoordinateSweeps.convolutionPower p k) g
    exact convolution_nonneg hp ih g

/-- Convolution is monotone in both arguments for nonnegative functions. -/
lemma convolution_le_convolution {G : Type*} [Group G] [Fintype G] {p₁ p₂ q₁ q₂ : G → ℝ}
    (h1 : ∀ g, p₁ g ≤ p₂ g) (h2 : ∀ g, q₁ g ≤ q₂ g)
    (hp : ∀ g, 0 ≤ p₁ g) (hq : ∀ g, 0 ≤ q₁ g) :
    ∀ g, BinaryCoordinateSweeps.convolution p₁ q₁ g ≤
      BinaryCoordinateSweeps.convolution p₂ q₂ g := by
  intro g
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul (h1 x) (h2 _) (hq _) ((hp x).trans (h1 x))

/-- Convolution powers inherit pointwise domination. -/
lemma convolutionPower_le {G : Type*} [Group G] [Fintype G] {p q : G → ℝ}
    (hp : ∀ g, 0 ≤ p g) (h : ∀ g, p g ≤ q g) (r : ℕ) :
    ∀ g, BinaryCoordinateSweeps.convolutionPower p r g ≤
      BinaryCoordinateSweeps.convolutionPower q r g := by
  induction r with
  | zero => intro g; exact le_refl _
  | succ k ih =>
    intro g
    show BinaryCoordinateSweeps.convolution p (BinaryCoordinateSweeps.convolutionPower p k) g ≤
      BinaryCoordinateSweeps.convolution q (BinaryCoordinateSweeps.convolutionPower q k) g
    exact convolution_le_convolution h ih hp (convolutionPower_nonneg hp k) g

/-- `realSign` takes values in `{±1}`, so its absolute value is 1. -/
lemma abs_realSign {n : ℕ} (g : Equiv.Perm (Fin n)) :
    |BinaryCoordinateSweeps.realSign g| = 1 := by
  have h : (BinaryCoordinateSweeps.realSign g)^2 = 1 := by
    have hc : YoungTabloid.signC g * YoungTabloid.signC g = 1 := YoungTabloid.signC_sq g
    rw [signC_eq_realSign, ← Complex.ofReal_mul] at hc
    rw [pow_two]
    exact Complex.ofReal_inj.mp (hc.trans Complex.ofReal_one.symm)
  rw [sq_eq_one_iff] at h
  rcases h with h | h <;> rw [h] <;> norm_num

/-- The sign mean of the subprobability is squeezed to zero by the ambient
sign mean and the mass convergence: `signMean f = signMean μ − mass((μ−f)·s)`
where the second term is bounded by `1 − mass f`. -/
lemma signMean_tendsto_zero {l : Filter ℕ} {μ f : (n : ℕ) → Equiv.Perm (Fin n) → ℝ}
    (hμ : ∀ᶠ n in l, (∀ g, 0 ≤ μ n g) ∧ mass (μ n) = 1)
    (hf : ∀ᶠ n in l, (∀ g, 0 ≤ f n g) ∧ ∀ g, f n g ≤ μ n g)
    (hmass : Tendsto (fun n => mass (f n)) l (nhds 1))
    (hsign : Tendsto (fun n => mass (fun g => μ n g * BinaryCoordinateSweeps.realSign g))
      l (nhds 0)) :
    Tendsto (fun n => mass (fun g => f n g * BinaryCoordinateSweeps.realSign g))
      l (nhds 0) := by
  have hdecomp : ∀ n, mass (fun g => f n g * BinaryCoordinateSweeps.realSign g) =
      mass (fun g => μ n g * BinaryCoordinateSweeps.realSign g) -
        mass (fun g => (μ n g - f n g) * BinaryCoordinateSweeps.realSign g) := by
    intro n
    show (∑ g, f n g * BinaryCoordinateSweeps.realSign g) =
      (∑ g, μ n g * BinaryCoordinateSweeps.realSign g) -
        ∑ g, (μ n g - f n g) * BinaryCoordinateSweeps.realSign g
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro g _
    ring
  have hbound : ∀ᶠ n in l, |mass (fun g => (μ n g - f n g) * BinaryCoordinateSweeps.realSign g)| ≤
      1 - mass (f n) := by
    filter_upwards [hμ, hf] with n hμn hfn
    calc |∑ g, (μ n g - f n g) * BinaryCoordinateSweeps.realSign g|
        ≤ ∑ g, |(μ n g - f n g) * BinaryCoordinateSweeps.realSign g| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ g, (μ n g - f n g) := by
          apply Finset.sum_congr rfl
          intro g _
          rw [abs_mul, abs_realSign, mul_one]
          exact abs_of_nonneg (sub_nonneg.mpr (hfn.2 g))
      _ = mass (μ n) - mass (f n) := by
          show (∑ g, (μ n g - f n g)) = (∑ g, μ n g) - ∑ g, f n g
          rw [← Finset.sum_sub_distrib]
      _ = 1 - mass (f n) := by rw [hμn.2]
  have hdiff0 : Tendsto (fun n => mass (fun g => (μ n g - f n g) *
      BinaryCoordinateSweeps.realSign g)) l (nhds 0) := by
    have hU : Tendsto (fun n => 1 - mass (f n)) l (nhds 0) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hmass
      simpa using h
    have hL : Tendsto (fun n => -(1 - mass (f n))) l (nhds 0) := by
      have h := hU.neg
      simpa using h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU
    · filter_upwards [hbound] with n h; exact (abs_le.mp h).1
    · filter_upwards [hbound] with n h; exact (abs_le.mp h).2
  have hlim := hsign.sub hdiff0
  have hlim' : Tendsto (fun n => mass (fun g => f n g * BinaryCoordinateSweeps.realSign g))
      l (nhds (0 - 0)) := hlim.congr' (Eventually.of_forall fun n => (hdecomp n).symm)
  simpa using hlim'

end Assembly

/-! ## Slice 4b (cont.): the convergence exit and Prop 2.5, operator form -/

section AssemblyProp

open Filter

/-- Total variation is nonnegative. -/
lemma tv_nonneg {G : Type*} [Fintype G] (p q : G → ℝ) :
    0 ≤ BinaryCoordinateSweeps.totalVariation p q := by
  unfold BinaryCoordinateSweeps.totalVariation
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

/-- The total-variation split: `TV(μ^{*r}, U) ≤ (1 − mass f^{*r})/2 + TV(f^{*r}, U)`. -/
lemma tv_split_subprob {n : ℕ} {μ f : Equiv.Perm (Fin n) → ℝ}
    (_hμ_nonneg : ∀ g, 0 ≤ μ g) (hμ_mass : mass μ = 1)
    (hf_nonneg : ∀ g, 0 ≤ f g) (hf_le : ∀ g, f g ≤ μ g) (r : ℕ) :
    BinaryCoordinateSweeps.totalVariation (BinaryCoordinateSweeps.convolutionPower μ r)
        (BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n))) ≤
      (1 - mass (BinaryCoordinateSweeps.convolutionPower f r)) / 2 +
        BinaryCoordinateSweeps.totalVariation (BinaryCoordinateSweeps.convolutionPower f r)
          (BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n))) := by
  classical
  unfold BinaryCoordinateSweeps.totalVariation
  have hmass : (1 - mass (BinaryCoordinateSweeps.convolutionPower f r)) / 2 =
      (1/((2:ℕ):ℝ)) * ∑ g, (BinaryCoordinateSweeps.convolutionPower μ r g -
        BinaryCoordinateSweeps.convolutionPower f r g) := by
    have h1 : ∑ g, (BinaryCoordinateSweeps.convolutionPower μ r g -
        BinaryCoordinateSweeps.convolutionPower f r g) =
        (∑ g, BinaryCoordinateSweeps.convolutionPower μ r g) -
          (∑ g, BinaryCoordinateSweeps.convolutionPower f r g) :=
      Finset.sum_sub_distrib _ _
    rw [h1]
    rw [show (∑ g, BinaryCoordinateSweeps.convolutionPower μ r g) =
        mass (BinaryCoordinateSweeps.convolutionPower μ r) from rfl,
      show (∑ g, BinaryCoordinateSweeps.convolutionPower f r g) =
        mass (BinaryCoordinateSweeps.convolutionPower f r) from rfl,
      mass_convolutionPower, mass_convolutionPower, hμ_mass, one_pow]
    push_cast
    ring
  rw [hmass, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 1/((2:ℕ):ℝ))
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g _
  have hle : BinaryCoordinateSweeps.convolutionPower f r g ≤
      BinaryCoordinateSweeps.convolutionPower μ r g :=
    convolutionPower_le hf_nonneg hf_le r g
  calc |BinaryCoordinateSweeps.convolutionPower μ r g -
        BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n)) g|
      = |(BinaryCoordinateSweeps.convolutionPower μ r g -
          BinaryCoordinateSweeps.convolutionPower f r g) +
        (BinaryCoordinateSweeps.convolutionPower f r g -
          BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n)) g)| :=
        congrArg _ (by ring)
    _ ≤ |BinaryCoordinateSweeps.convolutionPower μ r g -
          BinaryCoordinateSweeps.convolutionPower f r g| +
        |BinaryCoordinateSweeps.convolutionPower f r g -
          BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n)) g| := by
        have h := norm_add_le (BinaryCoordinateSweeps.convolutionPower μ r g -
          BinaryCoordinateSweeps.convolutionPower f r g)
          (BinaryCoordinateSweeps.convolutionPower f r g -
            BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n)) g)
        rwa [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h
    _ = (BinaryCoordinateSweeps.convolutionPower μ r g -
          BinaryCoordinateSweeps.convolutionPower f r g) +
        |BinaryCoordinateSweeps.convolutionPower f r g -
          BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n)) g| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hle)]

/-- `(2·TV(f,U))² ≤ (1 − mass f)² + nontrivialEnergy f`. -/
lemma tv_deficit_sq {n : ℕ} (f : Equiv.Perm (Fin n) → ℝ) :
    (2 * BinaryCoordinateSweeps.totalVariation f
        (BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n))))^2 ≤
      (1 - mass f)^2 + nontrivialEnergy f := by
  have h := deficit_plancherel f
  have h2 : 2 * BinaryCoordinateSweeps.totalVariation f
      (BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n))) =
      ∑ g, |f g - 1 / Fintype.card (Equiv.Perm (Fin n))| := by
    unfold BinaryCoordinateSweeps.totalVariation BinaryCoordinateSweeps.uniformLaw
    rw [← mul_assoc]
    rw [show (2:ℝ) * (1/((2:ℕ):ℝ)) = 1 from by push_cast; norm_num]
    rw [one_mul]
    apply Finset.sum_congr rfl
    intro g _
    rw [one_div]
  rw [h2]
  exact h

/-- The energy of the subprobability's `r`-th convolution power tends to zero
(operator form): the sign term via the squeeze, the degree-`>1` terms via the
transported operator bound and the degree-sum bridge. Filter-generic: the
hypotheses are `l`-indexed; the atTop-proved degree sum is pulled back along
`hl`. (Both `atTop` and `eightDivisible` are `≤ atTop`.) -/
lemma operator_energy_tendsto_zero {l : Filter ℕ} (hl : l ≤ atTop)
    {A β : ℝ} (hA : 0 < A) (_hβ : 0 < β) (r : ℕ)
    (hr : (2:ℝ) - 2 * (r:ℝ) * β < 0)
    {μ f : (n : ℕ) → Equiv.Perm (Fin n) → ℝ}
    (hμ : ∀ᶠ n in l, (∀ g, 0 ≤ μ n g) ∧ mass (μ n) = 1)
    (hf : ∀ᶠ n in l, (∀ g, 0 ≤ f n g) ∧ ∀ g, f n g ≤ μ n g)
    (hmass : Tendsto (fun n => mass (f n)) l (nhds 1))
    (hsign : Tendsto (fun n => mass (fun g => μ n g * BinaryCoordinateSweeps.realSign g))
      l (nhds 0))
    (hop : ∀ n, ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V),
        Representation.IsIrreducible ρ → IsUnitary ρ → 1 < Module.finrank ℂ V →
          ‖LinearMap.toContinuousLinearMap (complexFourier ρ (fun g => (f n g : ℂ)))‖
            ≤ A * (Module.finrank ℂ V : ℝ) ^ (-β)) :
    Tendsto (fun n => nontrivialEnergy (BinaryCoordinateSweeps.convolutionPower (f n) r))
      l (nhds 0) := by
  classical
  have hr1 : 1 ≤ r := by
    by_contra h
    rw [not_le] at h
    obtain rfl := Nat.lt_one_iff.mp h
    norm_num at hr
  have hsignf := signMean_tendsto_zero hμ hf hmass hsign
  have hp1 : Tendsto (fun n => (mass (fun g => f n g *
      BinaryCoordinateSweeps.realSign g))^(2*r)) l (nhds 0) := by
    have h := hsignf.pow (2*r)
    rwa [zero_pow (by omega : 2*r ≠ 0)] at h
  have hp2 : Tendsto (fun n => A^(2*r) * ∑ c : IrreducibleIndex (Equiv.Perm (Fin n)),
      if 1 < irreducibleDegree c then (irreducibleDegree c : ℝ)^(2 - 2*(r:ℝ)*β) else 0)
      l (nhds 0) := by
    have hexp : (2:ℝ) - 2*(r:ℝ)*β = -((2:ℝ)*(r:ℝ)*β - 2) := by ring
    have hs : 0 < (2:ℝ)*(r:ℝ)*β - 2 := by linarith
    have hbridge := (degreeSum_tendsto_zero ((2:ℝ)*(r:ℝ)*β - 2) hs).mono_left hl
    have hEq : (fun n => A^(2*r) * ∑ c : IrreducibleIndex (Equiv.Perm (Fin n)),
        if 1 < irreducibleDegree c then (irreducibleDegree c : ℝ)^(2 - 2*(r:ℝ)*β) else 0) =
        (fun n => A^(2*r) * ∑ c : IrreducibleIndex (Equiv.Perm (Fin n)),
        if 1 < irreducibleDegree c then (irreducibleDegree c : ℝ)^(-((2:ℝ)*(r:ℝ)*β - 2))
          else 0) := by
      funext n
      apply congrArg (A^(2*r) * ·)
      apply Finset.sum_congr rfl
      intro c _
      rw [hexp]
    rw [hEq]
    have h := hbridge.const_mul (A^(2*r))
    rwa [mul_zero] at h
  have hlim : Tendsto (fun n => (mass (fun g => f n g * BinaryCoordinateSweeps.realSign g))^(2*r) +
      A^(2*r) * ∑ c : IrreducibleIndex (Equiv.Perm (Fin n)),
        if 1 < irreducibleDegree c then (irreducibleDegree c : ℝ)^(2 - 2*(r:ℝ)*β) else 0)
      l (nhds 0) := by
    have h := hp1.add hp2
    simpa using h
  have hnn : ∀ n, 0 ≤ nontrivialEnergy (BinaryCoordinateSweeps.convolutionPower (f n) r) := by
    intro n
    unfold nontrivialEnergy
    apply Finset.sum_nonneg
    intro c _
    exact mul_nonneg (Nat.cast_nonneg _) (hsNormSq_nonneg _)
  have hle : ∀ᶠ n in l, nontrivialEnergy (BinaryCoordinateSweeps.convolutionPower (f n) r) ≤
      (mass (fun g => f n g * BinaryCoordinateSweeps.realSign g))^(2*r) +
        A^(2*r) * ∑ c : IrreducibleIndex (Equiv.Perm (Fin n)),
          if 1 < irreducibleDegree c then (irreducibleDegree c : ℝ)^(2 - 2*(r:ℝ)*β) else 0 := by
    filter_upwards [(eventually_ge_atTop 2).filter_mono hl] with n hn
    exact nontrivialEnergy_convPower_le hn hA r (f n) (fun c hc => hopc_of_hop hop n c hc)
  exact squeeze_zero' (Eventually.of_forall hnn) hle hlim

/-- The energy of the subprobability's `r`-th convolution power tends to zero
(Hilbert–Schmidt form): the sign term via the squeeze, the degree-`>1` terms via
the transported HS bound and the degree-sum bridge with exponent `rγ − 1`. -/
lemma hs_energy_tendsto_zero {l : Filter ℕ} (hl : l ≤ atTop)
    {A γ : ℝ} (hA : 0 < A) (_hγ : 0 < γ) (r : ℕ)
    (hr : (1:ℝ) - (r:ℝ) * γ < 0)
    {μ f : (n : ℕ) → Equiv.Perm (Fin n) → ℝ}
    (hμ : ∀ᶠ n in l, (∀ g, 0 ≤ μ n g) ∧ mass (μ n) = 1)
    (hf : ∀ᶠ n in l, (∀ g, 0 ≤ f n g) ∧ ∀ g, f n g ≤ μ n g)
    (hmass : Tendsto (fun n => mass (f n)) l (nhds 1))
    (hsign : Tendsto (fun n => mass (fun g => μ n g * BinaryCoordinateSweeps.realSign g))
      l (nhds 0))
    (hhs : ∀ n, ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V),
        Representation.IsIrreducible ρ → IsUnitary ρ → 1 < Module.finrank ℂ V →
          hsNormSq (complexFourier ρ (fun g => (f n g : ℂ)))
            ≤ A * (Module.finrank ℂ V : ℝ) ^ (-γ)) :
    Tendsto (fun n => nontrivialEnergy (BinaryCoordinateSweeps.convolutionPower (f n) r))
      l (nhds 0) := by
  classical
  have hr1 : 1 ≤ r := by
    by_contra h
    rw [not_le] at h
    obtain rfl := Nat.lt_one_iff.mp h
    norm_num at hr
  have hsignf := signMean_tendsto_zero hμ hf hmass hsign
  have hp1 : Tendsto (fun n => (mass (fun g => f n g *
      BinaryCoordinateSweeps.realSign g))^(2*r)) l (nhds 0) := by
    have h := hsignf.pow (2*r)
    rwa [zero_pow (by omega : 2*r ≠ 0)] at h
  have hp2 : Tendsto (fun n => A^r * ∑ c : IrreducibleIndex (Equiv.Perm (Fin n)),
      if 1 < irreducibleDegree c then (irreducibleDegree c : ℝ)^(1 - (r:ℝ)*γ) else 0)
      l (nhds 0) := by
    have hexp : (1:ℝ) - (r:ℝ)*γ = -((r:ℝ)*γ - 1) := by ring
    have hs : 0 < (r:ℝ)*γ - 1 := by linarith
    have hbridge := (degreeSum_tendsto_zero ((r:ℝ)*γ - 1) hs).mono_left hl
    have hEq : (fun n => A^r * ∑ c : IrreducibleIndex (Equiv.Perm (Fin n)),
        if 1 < irreducibleDegree c then (irreducibleDegree c : ℝ)^(1 - (r:ℝ)*γ) else 0) =
        (fun n => A^r * ∑ c : IrreducibleIndex (Equiv.Perm (Fin n)),
        if 1 < irreducibleDegree c then (irreducibleDegree c : ℝ)^(-((r:ℝ)*γ - 1))
          else 0) := by
      funext n
      apply congrArg (A^r * ·)
      apply Finset.sum_congr rfl
      intro c _
      rw [hexp]
    rw [hEq]
    have h := hbridge.const_mul (A^r)
    rwa [mul_zero] at h
  have hlim : Tendsto (fun n => (mass (fun g => f n g * BinaryCoordinateSweeps.realSign g))^(2*r) +
      A^r * ∑ c : IrreducibleIndex (Equiv.Perm (Fin n)),
        if 1 < irreducibleDegree c then (irreducibleDegree c : ℝ)^(1 - (r:ℝ)*γ) else 0)
      l (nhds 0) := by
    have h := hp1.add hp2
    simpa using h
  have hnn : ∀ n, 0 ≤ nontrivialEnergy (BinaryCoordinateSweeps.convolutionPower (f n) r) := by
    intro n
    unfold nontrivialEnergy
    apply Finset.sum_nonneg
    intro c _
    exact mul_nonneg (Nat.cast_nonneg _) (hsNormSq_nonneg _)
  have hle : ∀ᶠ n in l, nontrivialEnergy (BinaryCoordinateSweeps.convolutionPower (f n) r) ≤
      (mass (fun g => f n g * BinaryCoordinateSweeps.realSign g))^(2*r) +
        A^r * ∑ c : IrreducibleIndex (Equiv.Perm (Fin n)),
          if 1 < irreducibleDegree c then (irreducibleDegree c : ℝ)^(1 - (r:ℝ)*γ) else 0 := by
    filter_upwards [(eventually_ge_atTop 2).filter_mono hl] with n hn
    exact nontrivialEnergy_convPower_le_hs hn hA r hr1 (f n)
      (fun c hc => hopcHs_of_hhs hhs n c hc)
  exact squeeze_zero' (Eventually.of_forall hnn) hle hlim

/-- The shared convergence exit of Proposition 2.5 (both norms) and the two
convergence corollaries: given a subprobability `f ≤ μ` (eventually along `l`)
whose mass tends to one and whose `r`-fold convolution energy tends to zero,
`μ^{*r}` tends to uniform in total variation along `l`. -/
theorem tv_tendsto_zero_of_energy {l : Filter ℕ} (r : ℕ)
    {μ f : (n : ℕ) → Equiv.Perm (Fin n) → ℝ}
    (hμ : ∀ᶠ n in l, (∀ g, 0 ≤ μ n g) ∧ mass (μ n) = 1)
    (hf : ∀ᶠ n in l, (∀ g, 0 ≤ f n g) ∧ ∀ g, f n g ≤ μ n g)
    (hmass : Tendsto (fun n => mass (f n)) l (nhds 1))
    (henergy : Tendsto (fun n => nontrivialEnergy
      (BinaryCoordinateSweeps.convolutionPower (f n) r)) l (nhds 0)) :
    Tendsto (fun n => BinaryCoordinateSweeps.totalVariation
        (BinaryCoordinateSweeps.convolutionPower (μ n) r)
        (BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n)))) l (nhds 0) := by
  classical
  have hm1 : Tendsto (fun n => mass (BinaryCoordinateSweeps.convolutionPower (f n) r))
      l (nhds 1) := by
    have h1 : Tendsto (fun n => mass (f n)^r) l (nhds (1^r)) := hmass.pow r
    have h2 : (fun n => mass (BinaryCoordinateSweeps.convolutionPower (f n) r)) =
        (fun n => mass (f n)^r) := funext fun n => mass_convolutionPower _ _
    rw [h2]
    simpa using h1
  have hpiece1 : Tendsto (fun n =>
      (1 - mass (BinaryCoordinateSweeps.convolutionPower (f n) r))/2) l (nhds 0) := by
    have h := ((tendsto_const_nhds (x := (1:ℝ))).sub hm1).div_const 2
    simpa using h
  have hpiece2 : Tendsto (fun n => BinaryCoordinateSweeps.totalVariation
      (BinaryCoordinateSweeps.convolutionPower (f n) r)
      (BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n)))) l (nhds 0) := by
    have hR : Tendsto (fun n => (1 - mass (BinaryCoordinateSweeps.convolutionPower (f n) r))^2 +
        nontrivialEnergy (BinaryCoordinateSweeps.convolutionPower (f n) r)) l (nhds 0) := by
      have h1 : Tendsto (fun n => (1 - mass (BinaryCoordinateSweeps.convolutionPower (f n) r))^2)
          l (nhds ((1-1)^2)) := ((tendsto_const_nhds (x := (1:ℝ))).sub hm1).pow 2
      have h3 := h1.add henergy
      simpa using h3
    have hbound : ∀ n, BinaryCoordinateSweeps.totalVariation
        (BinaryCoordinateSweeps.convolutionPower (f n) r)
        (BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n))) ≤
        Real.sqrt ((1 - mass (BinaryCoordinateSweeps.convolutionPower (f n) r))^2 +
          nontrivialEnergy (BinaryCoordinateSweeps.convolutionPower (f n) r)) / 2 := by
      intro n
      have hdef := tv_deficit_sq (BinaryCoordinateSweeps.convolutionPower (f n) r)
      have hnn := tv_nonneg (BinaryCoordinateSweeps.convolutionPower (f n) r)
        (BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n)))
      have h2 : 2 * BinaryCoordinateSweeps.totalVariation
          (BinaryCoordinateSweeps.convolutionPower (f n) r)
          (BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n))) ≤
          Real.sqrt ((1 - mass (BinaryCoordinateSweeps.convolutionPower (f n) r))^2 +
            nontrivialEnergy (BinaryCoordinateSweeps.convolutionPower (f n) r)) := by
        rw [← Real.sqrt_sq (show 0 ≤ 2 * BinaryCoordinateSweeps.totalVariation
            (BinaryCoordinateSweeps.convolutionPower (f n) r)
            (BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n))) from
          mul_nonneg zero_le_two hnn)]
        exact Real.sqrt_le_sqrt hdef
      have h3 := h2
      linarith
    apply squeeze_zero (fun n => tv_nonneg _ _) hbound
    have hsqrt : Tendsto (fun n => Real.sqrt ((1 -
        mass (BinaryCoordinateSweeps.convolutionPower (f n) r))^2 +
        nontrivialEnergy (BinaryCoordinateSweeps.convolutionPower (f n) r))) l
        (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hR
    rw [Real.sqrt_zero] at hsqrt
    have hsqrt2 := hsqrt.div_const 2
    rwa [zero_div] at hsqrt2
  apply squeeze_zero' (Eventually.of_forall fun n => tv_nonneg _ _)
  · filter_upwards [hμ, hf] with n hμn hfn
    exact tv_split_subprob hμn.1 hμn.2 hfn.1 hfn.2 r
  · have htot := hpiece1.add hpiece2
    simpa using htot

/-- Proposition 2.5, operator-norm form: a uniform power saving of the
Fourier transform at every irreducible of degree > 1 amplifies to
total-variation convergence after `r` convolutions whenever `2 − 2rβ < 0`. -/
theorem fourier_amplification_operator
    (A β : ℝ) (hA : 0 < A) (hβ : 0 < β) (r : ℕ)
    (hr : (2 : ℝ) - 2 * (r : ℝ) * β < 0)
    (μ f : (n : ℕ) → Equiv.Perm (Fin n) → ℝ)
    (hμ : ∀ n, (∀ g, 0 ≤ μ n g) ∧ mass (μ n) = 1)
    (hf : ∀ n, (∀ g, 0 ≤ f n g) ∧ ∀ g, f n g ≤ μ n g)
    (hmass : Tendsto (fun n => mass (f n)) atTop (nhds 1))
    (hsign : Tendsto (fun n => mass (fun g => μ n g *
      BinaryCoordinateSweeps.realSign g)) atTop (nhds 0))
    (hop : ∀ n, ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V),
        Representation.IsIrreducible ρ → IsUnitary ρ → 1 < Module.finrank ℂ V →
          ‖LinearMap.toContinuousLinearMap (complexFourier ρ (fun g => (f n g : ℂ)))‖
            ≤ A * (Module.finrank ℂ V : ℝ) ^ (-β)) :
    Tendsto (fun n => BinaryCoordinateSweeps.totalVariation
        (BinaryCoordinateSweeps.convolutionPower (μ n) r)
        (BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n))))
      atTop (nhds 0) := by
  classical
  exact tv_tendsto_zero_of_energy r (Eventually.of_forall hμ) (Eventually.of_forall hf) hmass
    (operator_energy_tendsto_zero (le_refl atTop) hA hβ r hr
      (Eventually.of_forall hμ) (Eventually.of_forall hf) hmass hsign hop)

/-- Proposition 2.5, Hilbert–Schmidt form: the same conclusion from a squared
Hilbert–Schmidt bound `A·D^{−γ}` whenever `1 − rγ < 0`. -/
theorem fourier_amplification_hs
    (A γ : ℝ) (hA : 0 < A) (hγ : 0 < γ) (r : ℕ)
    (hr : (1 : ℝ) - (r : ℝ) * γ < 0)
    (μ f : (n : ℕ) → Equiv.Perm (Fin n) → ℝ)
    (hμ : ∀ n, (∀ g, 0 ≤ μ n g) ∧ mass (μ n) = 1)
    (hf : ∀ n, (∀ g, 0 ≤ f n g) ∧ ∀ g, f n g ≤ μ n g)
    (hmass : Tendsto (fun n => mass (f n)) atTop (nhds 1))
    (hsign : Tendsto (fun n => mass (fun g => μ n g *
      BinaryCoordinateSweeps.realSign g)) atTop (nhds 0))
    (hhs : ∀ n, ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V),
        Representation.IsIrreducible ρ → IsUnitary ρ → 1 < Module.finrank ℂ V →
          hsNormSq (complexFourier ρ (fun g => (f n g : ℂ)))
            ≤ A * (Module.finrank ℂ V : ℝ) ^ (-γ)) :
    Tendsto (fun n => BinaryCoordinateSweeps.totalVariation
        (BinaryCoordinateSweeps.convolutionPower (μ n) r)
        (BinaryCoordinateSweeps.uniformLaw (Equiv.Perm (Fin n))))
      atTop (nhds 0) := by
  classical
  exact tv_tendsto_zero_of_energy r (Eventually.of_forall hμ) (Eventually.of_forall hf) hmass
    (hs_energy_tendsto_zero (le_refl atTop) hA hγ r hr
      (Eventually.of_forall hμ) (Eventually.of_forall hf) hmass hsign hhs)

end AssemblyProp

/-! ## Slice 4c (corollary infrastructure): challenge-side definitions

Verbatim copies of the challenge file's local definitions
(`ComparatorChallenges/PartialPermutationConvergence.lean`), so the two
corollary theorems below are stated over the repository's own objects — the
G7 convention (the challenge carries the same copies; the comparator loads
the two environments separately). -/

section CorollaryInfrastructure

open Filter

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

end CorollaryInfrastructure

/-! ## Slice 4c-β: trimming (paper Lemma 2.3)

Per coset system, scale every over-cap left coset down to the uniform mass
`1/[G:H]`; across the (finitely many) systems, take the pointwise minimum.
The mass lost to system `i` is exactly `‖µ_{Hᵢ} − U‖TV` — the positive-part
form of total variation for equal-mass functions. -/

section Trimming

open scoped Classical

variable {G : Type*} [Group G] [Fintype G]

/-- The mass of the uniform law is one. -/
lemma mass_uniformLaw {α : Type*} [Fintype α] [Nonempty α] :
    mass (BinaryCoordinateSweeps.uniformLaw α) = 1 := by
  show (∑ _ : α, (Fintype.card α : ℝ)⁻¹) = 1
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

/-- Total variation between equal-mass functions is the summed positive part. -/
lemma totalVariation_eq_sum_posPart {α : Type*} [Fintype α] (p q : α → ℝ)
    (h : mass p = mass q) :
    BinaryCoordinateSweeps.totalVariation p q = ∑ a, max (p a - q a) 0 := by
  have hmax : ∀ x : ℝ, |x| = max x 0 + max (-x) 0 := by
    intro x
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx, max_eq_left hx, max_eq_right (show (-x) ≤ 0 by linarith)]
      ring
    · rw [abs_of_neg hx, max_eq_right (show x ≤ 0 by linarith),
        max_eq_left (show 0 ≤ -x by linarith)]
      ring
  have hdiff : ∀ x : ℝ, max x 0 - max (-x) 0 = x := by
    intro x
    rcases le_or_gt 0 x with hx | hx
    · rw [max_eq_left hx, max_eq_right (show (-x) ≤ 0 by linarith)]; ring
    · rw [max_eq_right (show x ≤ 0 by linarith), max_eq_left (show 0 ≤ -x by linarith)]; ring
  have hsum : (∑ a, max (p a - q a) 0) - (∑ a, max (q a - p a) 0) = 0 := by
    calc (∑ a, max (p a - q a) 0) - (∑ a, max (q a - p a) 0)
        = ∑ a, (max (p a - q a) 0 - max (q a - p a) 0) := by
          rw [Finset.sum_sub_distrib]
      _ = ∑ a, (p a - q a) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [show q a - p a = -(p a - q a) from by ring]
          exact hdiff _
      _ = (∑ a, p a) - ∑ a, q a := by
          rw [Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr h
  have key : (∑ a, max (p a - q a) 0) = ∑ a, max (q a - p a) 0 := sub_eq_zero.mp hsum
  show (1 / ((2 : ℕ) : ℝ)) * ∑ a, |p a - q a| = _
  rw [Finset.sum_congr rfl (fun a _ => hmax (p a - q a)), Finset.sum_add_distrib]
  have hT : (∑ a, max (-(p a - q a)) 0) = ∑ a, max (p a - q a) 0 := by
    trans (∑ a, max (q a - p a) 0)
    · apply Finset.sum_congr rfl
      intro a _
      rw [show q a - p a = -(p a - q a) from by ring]
    · exact key.symm
  rw [hT]
  push_cast
  ring

/-- The left cosets of `H` as the fibers of `QuotientGroup.mk`: the bijection
with `H` itself used to disintegrate sums over `G`. -/
def fiberMkEquiv (H : Subgroup G) (Q : G ⧸ H) :
    H ≃ {g : G // QuotientGroup.mk g = Q} := by
  classical
  refine Equiv.ofBijective (fun h => ⟨Quotient.out Q * (h : G), ?_⟩) ⟨?_, ?_⟩
  · exact (QuotientGroup.mk_mul_of_mem _ h.2).trans (Quotient.out_eq Q)
  · intro h₁ h₂ hEq
    apply Subtype.ext
    exact mul_left_cancel (congrArg Subtype.val hEq)
  · intro g
    have hmk : QuotientGroup.mk (s := H) g.1 = QuotientGroup.mk (s := H) (Quotient.out Q) :=
      g.2.trans (Quotient.out_eq Q).symm
    rw [QuotientGroup.eq] at hmk
    have hmem : (Quotient.out Q)⁻¹ * g.1 ∈ H := by
      have := inv_mem hmk
      rwa [mul_inv_rev, inv_inv] at this
    refine ⟨⟨(Quotient.out Q)⁻¹ * g.1, hmem⟩, ?_⟩
    apply Subtype.ext
    show Quotient.out Q * ((Quotient.out Q)⁻¹ * g.1) = g.1
    exact mul_inv_cancel_left _ _

/-- coset mass law evaluated on a representative. -/
lemma cosetMassLaw_mk_eq (μ : G → ℝ) (H : Subgroup G) (g : G) :
    cosetMassLaw μ H (QuotientGroup.mk g) = ∑ h : H, μ (g * h) := rfl

/-- Sums over `G` disintegrate over the cosets: the fiber sum is the coset
mass law. -/
lemma sum_fiber_mk (μ : G → ℝ) (H : Subgroup G) (Q : G ⧸ H) :
    (∑ g : {g : G // QuotientGroup.mk g = Q}, μ g.1) = cosetMassLaw μ H Q := by
  classical
  have h1 : (∑ g : {g : G // QuotientGroup.mk g = Q}, μ g.1) =
      ∑ h : H, μ (Quotient.out Q * (h : G)) :=
    (Fintype.sum_equiv (fiberMkEquiv H Q) (fun h => μ (Quotient.out Q * (h : G)))
      (fun g => μ g.1) (fun h => rfl)).symm
  have h2 : cosetMassLaw μ H Q = ∑ h : H, μ (Quotient.out Q * (h : G)) := by
    conv_lhs => rw [← Quotient.out_eq Q]
    exact cosetMassLaw_mk_eq μ H (Quotient.out Q)
  rw [h1, h2]

/-- The coset mass law has the same total mass as `µ`. -/
lemma sum_cosetMassLaw (μ : G → ℝ) (H : Subgroup G) :
    (∑ Q : G ⧸ H, cosetMassLaw μ H Q) = mass μ := by
  classical
  show (∑ Q : G ⧸ H, cosetMassLaw μ H Q) = ∑ g : G, μ g
  rw [← Fintype.sum_fiberwise (QuotientGroup.mk (s := H)) μ]
  apply Finset.sum_congr rfl
  intro Q _
  exact (sum_fiber_mk μ H Q).symm

/-- The per-system trim (paper Lemma 2.3's first operation): within each left
coset whose `µ`-mass exceeds the uniform mass `1/[G:H]`, scale all point
masses by the ratio cap/mass. -/
def trimCoset (μ : G → ℝ) (H : Subgroup G) (g : G) : ℝ :=
  μ g * min 1 ((H.index : ℝ)⁻¹ / cosetMassLaw μ H (QuotientGroup.mk g))

lemma trimCoset_nonneg (hμ : ∀ g, 0 ≤ μ g) (H : Subgroup G) (g : G) :
    0 ≤ trimCoset μ H g := by
  apply mul_nonneg (hμ g)
  refine le_min zero_le_one (div_nonneg (by positivity) ?_)
  rw [cosetMassLaw_mk_eq]
  exact Finset.sum_nonneg (fun h _ => hμ _)

lemma trimCoset_le (hμ : ∀ g, 0 ≤ μ g) (H : Subgroup G) (g : G) :
    trimCoset μ H g ≤ μ g := by
  have h1 := mul_le_mul_of_nonneg_left (min_le_left (1 : ℝ)
    ((H.index : ℝ)⁻¹ / cosetMassLaw μ H (QuotientGroup.mk g))) (hμ g)
  rwa [mul_one] at h1

/-- The trim enforces the coset cap `1/[G:H]` (i.e. `LeftCosetCap … H 1`). -/
lemma trimCoset_cosetCap (hμ : ∀ g, 0 ≤ μ g) (H : Subgroup G) :
    LeftCosetCap (trimCoset μ H) H 1 := by
  classical
  intro g
  have hconst : ∀ h : H, cosetMassLaw μ H (QuotientGroup.mk (g * h))
      = cosetMassLaw μ H (QuotientGroup.mk g) :=
    fun h => congrArg _ (QuotientGroup.mk_mul_of_mem g h.2)
  have hsum : (∑ h : H, trimCoset μ H (g * h)) =
      cosetMassLaw μ H (QuotientGroup.mk g) *
        min 1 ((H.index : ℝ)⁻¹ / cosetMassLaw μ H (QuotientGroup.mk g)) := by
    rw [cosetMassLaw_mk_eq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro h _
    show μ (g * (h : G)) * min 1 ((H.index:ℝ)⁻¹ / cosetMassLaw μ H (QuotientGroup.mk (g * h))) =
        μ (g * (h : G)) * min 1 ((H.index:ℝ)⁻¹ / cosetMassLaw μ H (QuotientGroup.mk g))
    rw [hconst h]
  rw [one_div, hsum]
  set L := cosetMassLaw μ H (QuotientGroup.mk g) with hL
  set c := (H.index : ℝ)⁻¹ with hc
  have hL0 : 0 ≤ L := by
    rw [hL, cosetMassLaw_mk_eq]
    exact Finset.sum_nonneg (fun h _ => hμ _)
  have hc0 : 0 < c := by
    rw [hc]
    exact inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero H.index_ne_zero_of_finite))
  by_cases hLc : L ≤ c
  · calc L * min 1 (c / L) ≤ L * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) hL0
      _ = L := mul_one _
      _ ≤ c := hLc
  · rw [not_le] at hLc
    have hLpos : 0 < L := hc0.trans hLc
    have hmin : min 1 (c / L) = c / L := min_eq_right ((div_lt_one hLpos).mpr hLc).le
    have hcc : L * min 1 (c / L) = c := by
      rw [hmin]
      exact mul_div_cancel₀ _ hLpos.ne'
    exact hcc.le

/-- The mass lost to the trim of one system is the summed positive excess of
the coset mass law over the uniform mass. -/
lemma trimCoset_loss (hμ : ∀ g, 0 ≤ μ g) (H : Subgroup G) :
    mass μ - mass (trimCoset μ H) =
      ∑ Q : G ⧸ H, max (cosetMassLaw μ H Q - (H.index : ℝ)⁻¹) 0 := by
  classical
  have hdiff : mass μ - mass (trimCoset μ H) =
      ∑ g : G, μ g * (1 - min 1 ((H.index:ℝ)⁻¹ / cosetMassLaw μ H (QuotientGroup.mk g))) := by
    show (∑ g, μ g) - ∑ g, trimCoset μ H g = _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro g _
    show μ g - μ g * min 1 ((H.index:ℝ)⁻¹ / cosetMassLaw μ H (QuotientGroup.mk g)) = _
    ring
  rw [hdiff, ← Fintype.sum_fiberwise (QuotientGroup.mk (s := H))
    (fun g => μ g * (1 - min 1 ((H.index:ℝ)⁻¹ / cosetMassLaw μ H (QuotientGroup.mk g))))]
  apply Finset.sum_congr rfl
  intro Q _
  have hconst : ∀ g : {g : G // QuotientGroup.mk g = Q},
      cosetMassLaw μ H (QuotientGroup.mk g.1) = cosetMassLaw μ H Q :=
    fun g => congrArg _ g.2
  calc ∑ g : {g : G // QuotientGroup.mk g = Q},
        μ g.1 * (1 - min 1 ((H.index:ℝ)⁻¹ / cosetMassLaw μ H (QuotientGroup.mk g.1)))
      = ∑ g : {g : G // QuotientGroup.mk g = Q},
        μ g.1 * (1 - min 1 ((H.index:ℝ)⁻¹ / cosetMassLaw μ H Q)) := by
        apply Finset.sum_congr rfl
        intro g _
        rw [hconst g]
    _ = cosetMassLaw μ H Q * (1 - min 1 ((H.index:ℝ)⁻¹ / cosetMassLaw μ H Q)) := by
        rw [← Finset.sum_mul]
        congr 1
        exact sum_fiber_mk μ H Q
    _ = max (cosetMassLaw μ H Q - (H.index:ℝ)⁻¹) 0 := by
        set L := cosetMassLaw μ H Q with hL
        set c := (H.index : ℝ)⁻¹ with hc
        have hL0 : 0 ≤ L := by
          rw [hL, ← Quotient.out_eq Q, cosetMassLaw_mk_eq]
          exact Finset.sum_nonneg (fun h _ => hμ _)
        have hc0 : 0 < c := by
          rw [hc]
          exact inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero H.index_ne_zero_of_finite))
        by_cases hLc : L ≤ c
        · by_cases hLpos : 0 < L
          · have hmin : min 1 (c / L) = 1 := min_eq_left ((one_le_div hLpos).mpr hLc)
            rw [hmin, sub_self, mul_zero]
            exact (max_eq_right (sub_nonpos.mpr hLc)).symm
          · have hLz : L = 0 := le_antisymm (not_lt.mp hLpos) hL0
            rw [hLz, div_zero, min_eq_right zero_le_one, zero_mul]
            exact (max_eq_right (by linarith)).symm
        · rw [not_le] at hLc
          have hLpos : 0 < L := hc0.trans hLc
          have hmin : min 1 (c / L) = c / L := min_eq_right ((div_lt_one hLpos).mpr hLc).le
          rw [hmin]
          have hrewrite : L * (1 - c / L) = L - c := by
            rw [mul_sub, mul_one, mul_comm L (c / L), div_mul_cancel₀ c hLpos.ne']
          rw [hrewrite]
          exact (max_eq_left (sub_nonneg.mpr hLc.le)).symm

/-- The mass lost to the trim of one system equals the quotient TV. -/
lemma trimCoset_loss_eq_tv (hμ : ∀ g, 0 ≤ μ g) (hμ1 : mass μ = 1) (H : Subgroup G) :
    mass μ - mass (trimCoset μ H) =
      BinaryCoordinateSweeps.totalVariation (cosetMassLaw μ H)
        (BinaryCoordinateSweeps.uniformLaw (G ⧸ H)) := by
  classical
  rw [trimCoset_loss hμ H, totalVariation_eq_sum_posPart]
  · apply Finset.sum_congr rfl
    intro Q _
    congr 1
    show cosetMassLaw μ H Q - (H.index : ℝ)⁻¹ =
      cosetMassLaw μ H Q - (Fintype.card (G ⧸ H) : ℝ)⁻¹
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  · show (∑ Q, cosetMassLaw μ H Q) = ∑ Q, (Fintype.card (G ⧸ H) : ℝ)⁻¹
    rw [sum_cosetMassLaw μ H, hμ1]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

/-- The common trimmed subprobability (paper Lemma 2.3, the simultaneous
`min` construction): pointwise minimum of the per-system trims. -/
def trimMin {ι : Type*} [Fintype ι] [Nonempty ι] (μ : G → ℝ) (H : ι → Subgroup G) (g : G) : ℝ :=
  Finset.inf' Finset.univ Finset.univ_nonempty (fun i => trimCoset μ (H i) g)

/-- The minimum is attained by some system. -/
lemma trimMin_eq_some {ι : Type*} [Fintype ι] [Nonempty ι] (μ : G → ℝ) (H : ι → Subgroup G)
    (g : G) : ∃ i, trimMin μ H g = trimCoset μ (H i) g := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun i => trimCoset μ (H i) g)
  exact ⟨i, hi⟩

lemma trimMin_nonneg {ι : Type*} [Fintype ι] [Nonempty ι] (hμ : ∀ g, 0 ≤ μ g)
    (H : ι → Subgroup G) (g : G) : 0 ≤ trimMin μ H g := by
  show 0 ≤ Finset.inf' _ _ _
  exact Finset.le_inf' _ _ (fun i _ => trimCoset_nonneg hμ (H i) g)

lemma trimMin_le {ι : Type*} [Fintype ι] [Nonempty ι] (hμ : ∀ g, 0 ≤ μ g)
    (H : ι → Subgroup G) (g : G) : trimMin μ H g ≤ μ g := by
  obtain ⟨i, hi⟩ := trimMin_eq_some μ H g
  rw [hi]
  exact trimCoset_le hμ (H i) g

/-- The common trim inherits every system's coset cap. -/
lemma trimMin_cosetCap {ι : Type*} [Fintype ι] [Nonempty ι] (hμ : ∀ g, 0 ≤ μ g)
    (H : ι → Subgroup G) (i₀ : ι) : LeftCosetCap (trimMin μ H) (H i₀) 1 := by
  intro g
  refine le_trans ?_ (trimCoset_cosetCap hμ (H i₀) g)
  apply Finset.sum_le_sum
  intro h _
  exact Finset.inf'_le _ (Finset.mem_univ i₀)

/-- The common trim loses at most the summed marginal TVs. -/
lemma trimMin_mass_ge {ι : Type*} [Fintype ι] [Nonempty ι] (hμ : ∀ g, 0 ≤ μ g)
    (hμ1 : mass μ = 1) (H : ι → Subgroup G) :
    1 - (∑ i, BinaryCoordinateSweeps.totalVariation (cosetMassLaw μ (H i))
        (BinaryCoordinateSweeps.uniformLaw (G ⧸ (H i)))) ≤ mass (trimMin μ H) := by
  have hpoint : ∀ g : G, μ g - trimMin μ H g ≤ ∑ i, (μ g - trimCoset μ (H i) g) := by
    intro g
    obtain ⟨i₀, hi₀⟩ := trimMin_eq_some μ H g
    calc μ g - trimMin μ H g = μ g - trimCoset μ (H i₀) g := by rw [hi₀]
      _ ≤ ∑ i, (μ g - trimCoset μ (H i) g) :=
        Finset.single_le_sum (fun i _ => sub_nonneg.mpr (trimCoset_le hμ (H i) g))
          (Finset.mem_univ i₀)
  have hloss : mass μ - mass (trimMin μ H) ≤
      ∑ i, (mass μ - mass (trimCoset μ (H i))) := by
    show (∑ g, μ g) - (∑ g, trimMin μ H g) ≤ _
    rw [← Finset.sum_sub_distrib]
    calc ∑ g, (μ g - trimMin μ H g) ≤ ∑ g, ∑ i, (μ g - trimCoset μ (H i) g) :=
          Finset.sum_le_sum (fun g _ => hpoint g)
      _ = ∑ i, ∑ g, (μ g - trimCoset μ (H i) g) := Finset.sum_comm
      _ = ∑ i, (mass μ - mass (trimCoset μ (H i))) := by
          apply Finset.sum_congr rfl
          intro i _
          show (∑ g, (μ g - trimCoset μ (H i) g)) = (∑ g, μ g) - ∑ g, trimCoset μ (H i) g
          rw [Finset.sum_sub_distrib]
  have htv : mass μ - mass (trimMin μ H) ≤
      ∑ i, BinaryCoordinateSweeps.totalVariation (cosetMassLaw μ (H i))
        (BinaryCoordinateSweeps.uniformLaw (G ⧸ (H i))) := by
    refine hloss.trans ?_
    apply Finset.sum_le_sum
    intro i _
    rw [trimCoset_loss_eq_tv hμ hμ1 (H i)]
  linarith [hμ1]

/-- Lemma 2.3 (trimming), as needed by the convergence corollaries: a common
subprobability below `µ` with coset cap one on every system, losing at most
the summed marginal TV. -/
theorem exists_trimmed_subprobability {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : G → ℝ) (hμ0 : ∀ g, 0 ≤ μ g) (hμ1 : mass μ = 1) (H : ι → Subgroup G) :
    ∃ f : G → ℝ, (∀ g, 0 ≤ f g) ∧ (∀ g, f g ≤ μ g) ∧
      1 - (∑ i, BinaryCoordinateSweeps.totalVariation (cosetMassLaw μ (H i))
          (BinaryCoordinateSweeps.uniformLaw (G ⧸ (H i)))) ≤ mass f ∧
      ∀ i, LeftCosetCap f (H i) 1 :=
  ⟨trimMin μ H, trimMin_nonneg hμ0 H, trimMin_le hμ0 H,
    trimMin_mass_ge hμ0 hμ1 H, fun i => trimMin_cosetCap hμ0 H i⟩

end Trimming

/-! ## Slice 4c-γ: selecting one partition (paper Lemma 2.2)

Every block of a uniformly chosen ordered equal partition is a uniform
`n/8`-subset; hence the average over ordered partitions of the summed
marginal error is `8 ×` the average over subsets, and some partition attains
at most that. All counting is by symmetry (permutation transport of
partitions) and fiberwise sums — no probability spaces. -/

section PartitionSelection

open scoped Classical

/-- Ordered equal partitions of `Fin n` into `b` blocks, carried as finsets. -/
def ordEqualPartitions (n b : ℕ) : Type := {M : Fin b → Finset (Fin n) //
  (∀ i, (M i).card = n / b) ∧ Pairwise (Function.onFun Disjoint M)}

noncomputable instance (n b : ℕ) : Fintype (ordEqualPartitions n b) := by
  classical
  show Fintype {M : Fin b → Finset (Fin n) //
    (∀ i, (M i).card = n / b) ∧ Pairwise (Function.onFun Disjoint M)}
  infer_instance

/-- The marginal TV error of a subset (the summand of `avgMarginalTV`). -/
noncomputable def marginalErr (μ : Equiv.Perm (Fin n) → ℝ) (M : Finset (Fin n)) : ℝ :=
  BinaryCoordinateSweeps.totalVariation (cosetMassLaw μ (blockSubgroup (M : Set (Fin n))))
    (BinaryCoordinateSweeps.uniformLaw _)

/-- `avgMarginalTV` is the plain average of `marginalErr` over the
`n/8`-subsets. -/
lemma avgMarginalTV_eq (μ : (n : ℕ) → Equiv.Perm (Fin n) → ℝ) (n : ℕ) :
    avgMarginalTV μ n =
      (∑ M : {M : Finset (Fin n) // M.card = n / 8}, marginalErr (μ n) M.1) /
        (Fintype.card {M : Finset (Fin n) // M.card = n / 8} : ℝ) := rfl

/-- The non-membership subtype is the complement finset's subtype. -/
def notMemEquivCompl {m : ℕ} (M : Finset (Fin m)) : {a : Fin m // a ∉ M} ≃ ↥(Mᶜ) :=
  Equiv.subtypeEquivRight (fun _ => Finset.mem_compl.symm)

/-- A permutation of `Fin m` carrying one finset onto another of the same
cardinality (via `sumCompl` gluing of a block equivalence and a complement
equivalence). -/
lemma exists_perm_map_finset {m : ℕ} {M₀ M₁ : Finset (Fin m)} (h : M₀.card = M₁.card) :
    ∃ σ : Equiv.Perm (Fin m), M₀.map σ.toEmbedding = M₁ := by
  classical
  have hC : Fintype.card ↥M₀ = Fintype.card ↥M₁ := by
    rw [Fintype.card_coe, Fintype.card_coe]
    exact h
  obtain ⟨e₁⟩ := Fintype.card_eq.mp hC
  have key : ∀ M : Finset (Fin m), Fintype.card {a : Fin m // a ∉ M} = m - M.card := by
    intro M
    calc Fintype.card {a : Fin m // a ∉ M} = Fintype.card ↥(Mᶜ) :=
          Fintype.card_congr (notMemEquivCompl M)
      _ = (Mᶜ).card := Fintype.card_coe _
      _ = m - M.card := by rw [Finset.card_compl, Fintype.card_fin]
  obtain ⟨e₂⟩ := Fintype.card_eq.mp (show
      Fintype.card {a : Fin m // a ∉ M₀} = Fintype.card {a : Fin m // a ∉ M₁} by
    rw [key M₀, key M₁, h])
  set σ : Equiv.Perm (Fin m) := (Equiv.sumCompl (· ∈ M₀)).symm.trans
    ((e₁.sumCongr e₂).trans (Equiv.sumCompl (· ∈ M₁))) with hσ
  refine ⟨σ, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
    rw [← hyx]
    show σ y ∈ M₁
    have hσy : σ y = (e₁ ⟨y, hy⟩ : Fin m) := by
      rw [hσ]
      simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hy]
      rw [show (e₁.sumCongr e₂) (Sum.inl ⟨y, hy⟩) = Sum.inl (e₁ ⟨y, hy⟩) from rfl]
      exact Equiv.sumCompl_apply_inl _
    rw [hσy]
    exact (e₁ ⟨y, hy⟩).2
  · rw [Finset.card_map]
    exact h.symm.le

/-- An ordered equal partition exists whenever `8 ∣ n`. -/
lemma ordEqualPartitions_nonempty {n : ℕ} (h8 : 8 ∣ n) :
    Nonempty (ordEqualPartitions n 8) := by
  classical
  have hcard : Fintype.card (Fin n) = Fintype.card (Fin 8 × Fin (n / 8)) := by
    rw [Fintype.card_fin, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Nat.mul_div_cancel' h8]
  obtain ⟨e⟩ := Fintype.card_eq.mp hcard
  have hinj : ∀ i : Fin 8, Function.Injective (fun k : Fin (n / 8) => e.symm (i, k)) := by
    intro i a b hab
    exact (Prod.mk.inj (e.symm.injective hab)).2
  refine ⟨⟨fun i => Finset.univ.image (fun k : Fin (n / 8) => e.symm (i, k)), fun i => ?_, ?_⟩⟩
  · rw [Finset.card_image_of_injective _ (hinj i), Finset.card_univ, Fintype.card_fin]
  · intro i j hij
    show Disjoint (Finset.univ.image (fun k => e.symm (i, k)))
      (Finset.univ.image (fun k => e.symm (j, k)))
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_image] at hx1 hx2
    obtain ⟨k₁, -, hk₁⟩ := hx1
    obtain ⟨k₂, -, hk₂⟩ := hx2
    have hcon : (i, k₁) = (j, k₂) := e.symm.injective (hk₁.trans hk₂.symm)
    exact hij (Prod.mk.inj hcon).1

/-- The `i`-th block of an ordered equal partition, as an `n/8`-subset. -/
def evalPart {n : ℕ} (i : Fin 8) (P : ordEqualPartitions n 8) :
    {M : Finset (Fin n) // M.card = n / 8} :=
  ⟨P.1 i, P.2.1 i⟩

/-- Transport of ordered equal partitions along a permutation of the
underlying set. -/
def transportPart {n b : ℕ} (σ : Equiv.Perm (Fin n)) (P : ordEqualPartitions n b) :
    ordEqualPartitions n b := by
  classical
  refine ⟨fun i => (P.1 i).map σ.toEmbedding, fun i => ?_, fun i j hij => ?_⟩
  · rw [Finset.card_map]
    exact P.2.1 i
  · exact (Finset.disjoint_map _).mpr (P.2.2 hij)

/-- Transport by `σ.symm` undoes transport by `σ`. -/
lemma transportPart_symm_left_inv {n b : ℕ} (σ : Equiv.Perm (Fin n))
    (P : ordEqualPartitions n b) :
    transportPart σ.symm (transportPart σ P) = P := by
  apply Subtype.ext
  funext i
  show ((P.1 i).map σ.toEmbedding).map σ.symm.toEmbedding = P.1 i
  rw [Finset.map_map]
  have hid : σ.toEmbedding.trans σ.symm.toEmbedding = Function.Embedding.refl (Fin n) :=
    Function.Embedding.ext (fun x => Equiv.symm_apply_apply σ x)
  rw [hid, Finset.map_refl]

/-- Transport as an equivalence of the partition type. -/
def transportPartEquiv {n b : ℕ} (σ : Equiv.Perm (Fin n)) :
    ordEqualPartitions n b ≃ ordEqualPartitions n b :=
  ⟨transportPart σ, transportPart σ.symm, transportPart_symm_left_inv σ,
    fun P => transportPart_symm_left_inv σ.symm P⟩

/-- Reindexing of ordered equal partitions along a permutation of the block
index set. -/
def reindexPartEquiv {n : ℕ} (τ : Equiv.Perm (Fin 8)) :
    ordEqualPartitions n 8 ≃ ordEqualPartitions n 8 := by
  refine ⟨fun P => ⟨fun i => P.1 (τ i), fun i => P.2.1 (τ i), fun i j hij =>
      P.2.2 (τ.injective.ne hij)⟩,
    fun P => ⟨fun i => P.1 (τ.symm i), fun i => P.2.1 (τ.symm i), fun i j hij =>
      P.2.2 (τ.symm.injective.ne hij)⟩, ?_, ?_⟩
  · intro P
    apply Subtype.ext
    funext i
    show P.1 (τ (τ.symm i)) = P.1 i
    rw [Equiv.apply_symm_apply]
  · intro P
    apply Subtype.ext
    funext i
    show P.1 (τ.symm (τ i)) = P.1 i
    rw [Equiv.symm_apply_apply]

/-- Block evaluation of a transported partition. -/
lemma evalPart_transport {n : ℕ} (i : Fin 8) (σ : Equiv.Perm (Fin n))
    (P : ordEqualPartitions n 8) :
    evalPart i (transportPartEquiv σ P) =
      ⟨(P.1 i).map σ.toEmbedding, by rw [Finset.card_map]; exact P.2.1 i⟩ := rfl

/-- Block evaluation of a reindexed partition along a swap. -/
lemma evalPart_reindex_swap {n : ℕ} (i j : Fin 8) (P : ordEqualPartitions n 8) :
    evalPart j (reindexPartEquiv (Equiv.swap i j) P) = evalPart i P := by
  apply Subtype.ext
  show P.1 (Equiv.swap i j j) = P.1 i
  rw [Equiv.swap_apply_right]

/-- Fibers of block evaluation have constant cardinality: content transport
(fixed index). -/
lemma fiber_card_const_content {n : ℕ} (i : Fin 8)
    (M₀ M₁ : {M : Finset (Fin n) // M.card = n / 8}) :
    Fintype.card {P : ordEqualPartitions n 8 // evalPart i P = M₀} =
      Fintype.card {P : ordEqualPartitions n 8 // evalPart i P = M₁} := by
  classical
  obtain ⟨σ, hσ⟩ := exists_perm_map_finset (M₀ := M₀.1) (M₁ := M₁.1) (by rw [M₀.2, M₁.2])
  apply Fintype.card_congr
  refine Equiv.subtypeEquiv (transportPartEquiv σ) (fun P => ?_)
  constructor
  · intro h
    apply Subtype.ext
    show (P.1 i).map σ.toEmbedding = M₁.1
    have hval : P.1 i = M₀.1 := congrArg Subtype.val h
    rw [← hσ, hval]
  · intro h
    apply Subtype.ext
    show P.1 i = M₀.1
    have hval0 : (evalPart i (transportPartEquiv σ P)).1 = M₁.1 := congrArg Subtype.val h
    have hval : (P.1 i).map σ.toEmbedding = M₁.1 := hval0
    rw [← hσ] at hval
    exact Finset.map_injective _ hval

/-- Fibers of block evaluation have constant cardinality: index transport
(fixed subset). -/
lemma fiber_card_const_index {n : ℕ} (i j : Fin 8)
    (M : {M : Finset (Fin n) // M.card = n / 8}) :
    Fintype.card {P : ordEqualPartitions n 8 // evalPart i P = M} =
      Fintype.card {P : ordEqualPartitions n 8 // evalPart j P = M} := by
  classical
  apply Fintype.card_congr
  refine Equiv.subtypeEquiv (reindexPartEquiv (Equiv.swap i j)) (fun P => ?_)
  constructor
  · intro h
    rw [evalPart_reindex_swap]
    exact h
  · intro h
    rw [evalPart_reindex_swap] at h
    exact h

/-- All fibers of block evaluation share one cardinality. -/
lemma fiber_card_const {n : ℕ} (i : Fin 8)
    (M Mref : {M : Finset (Fin n) // M.card = n / 8}) :
    Fintype.card {P : ordEqualPartitions n 8 // evalPart i P = M} =
      Fintype.card {P : ordEqualPartitions n 8 // evalPart 0 P = Mref} :=
  (fiber_card_const_index i 0 M).trans (fiber_card_const_content 0 M Mref)

/-- The per-index double count: summing a subset function over block `i` of
all ordered equal partitions equals the common fiber cardinality times the
total over subsets (paper Lemma 2.2's "every block is a uniform subset"). -/
lemma sum_eval_eq {n : ℕ} (i : Fin 8)
    (w : {M : Finset (Fin n) // M.card = n / 8} → ℝ) (N₁ : ℕ)
    (hN₁ : ∀ M : {M : Finset (Fin n) // M.card = n / 8},
      Fintype.card {P : ordEqualPartitions n 8 // evalPart i P = M} = N₁) :
    ∑ P : ordEqualPartitions n 8, w (evalPart i P) =
      (N₁ : ℝ) * ∑ M : {M : Finset (Fin n) // M.card = n / 8}, w M := by
  classical
  calc ∑ P : ordEqualPartitions n 8, w (evalPart i P)
      = ∑ M : {M : Finset (Fin n) // M.card = n / 8},
          ∑ P : {P : ordEqualPartitions n 8 // evalPart i P = M}, w (evalPart i P.1) :=
        (Fintype.sum_fiberwise (evalPart i) (fun P => w (evalPart i P))).symm
    _ = ∑ M : {M : Finset (Fin n) // M.card = n / 8}, (N₁ : ℝ) * w M := by
        apply Finset.sum_congr rfl
        intro M _
        have hconst : ∀ P : {P : ordEqualPartitions n 8 // evalPart i P = M},
            w (evalPart i P.1) = w M := fun P => congrArg w P.2
        rw [Finset.sum_congr rfl (fun P _ => hconst P), Finset.sum_const, Finset.card_univ,
          hN₁ M, nsmul_eq_mul]
    _ = (N₁ : ℝ) * ∑ M : {M : Finset (Fin n) // M.card = n / 8}, w M :=
        (Finset.mul_sum _ _ _).symm

/-- Lemma 2.2 (selecting one partition): some ordered equal partition has
summed marginal error at most `8 × avgMarginalTV`. -/
lemma exists_partition_avgMarginal_le (μF : (n : ℕ) → Equiv.Perm (Fin n) → ℝ)
    (n : ℕ) (h8 : 8 ∣ n) :
    ∃ M : Fin 8 → Finset (Fin n), (∀ i, (M i).card = n / 8) ∧
      Pairwise (Function.onFun Disjoint M) ∧
      (∑ i, marginalErr (μF n) (M i)) ≤ 8 * avgMarginalTV μF n := by
  classical
  have hSub : Nonempty {M : Finset (Fin n) // M.card = n / 8} := by
    have hex : ∃ M ⊆ (Finset.univ : Finset (Fin n)), M.card = n / 8 :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n))) (n := n / 8)
        (by rw [Finset.card_univ, Fintype.card_fin]; exact Nat.div_le_self _ _)
    obtain ⟨M, -, hM⟩ := hex
    exact ⟨M, hM⟩
  obtain ⟨Mref⟩ := hSub
  set N₁ := Fintype.card {P : ordEqualPartitions n 8 // evalPart 0 P = Mref}
    with hN₁def
  have hN₁ : ∀ (i : Fin 8) (M : {M : Finset (Fin n) // M.card = n / 8}),
      Fintype.card {P : ordEqualPartitions n 8 // evalPart i P = M} = N₁ :=
    fun i M => fiber_card_const i M Mref
  have hN₁pos : 0 < N₁ := by
    obtain ⟨Q⟩ := ordEqualPartitions_nonempty h8
    obtain ⟨σ, hσ⟩ := exists_perm_map_finset (M₀ := Q.1 0) (M₁ := Mref.1) (by
      rw [Q.2.1 0, Mref.2])
    have hmem : evalPart 0 (transportPartEquiv σ Q) = Mref := by
      apply Subtype.ext
      show (Q.1 0).map σ.toEmbedding = Mref.1
      exact hσ
    rw [hN₁def, Fintype.card_pos_iff]
    exact ⟨⟨_, hmem⟩⟩
  have hN₂ : 0 < Fintype.card {M : Finset (Fin n) // M.card = n / 8} := by
    rw [Fintype.card_pos_iff]
    exact ⟨Mref⟩
  have hN₂' : (Fintype.card {M : Finset (Fin n) // M.card = n / 8} : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  have hdouble : ∀ i : Fin 8, ∑ P : ordEqualPartitions n 8, marginalErr (μF n) (P.1 i) =
      (N₁ : ℝ) * ∑ M : {M : Finset (Fin n) // M.card = n / 8}, marginalErr (μF n) M.1 :=
    fun i => sum_eval_eq i (fun M => marginalErr (μF n) M.1) N₁ (fun M => hN₁ i M)
  have hcard : (Fintype.card (ordEqualPartitions n 8) : ℝ) =
      (N₁ : ℝ) * Fintype.card {M : Finset (Fin n) // M.card = n / 8} := by
    have h1 := sum_eval_eq 0 (fun _ => (1 : ℝ)) N₁ (fun M => hN₁ 0 M)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h1
  have hsum : ∑ P : ordEqualPartitions n 8, ∑ i : Fin 8, marginalErr (μF n) (P.1 i) =
      8 * (N₁ : ℝ) * ∑ M : {M : Finset (Fin n) // M.card = n / 8},
        marginalErr (μF n) M.1 := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun i _ => hdouble i)]
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    push_cast
    ring
  obtain ⟨P, -, hP⟩ := Finset.exists_le_of_sum_le (s := (Finset.univ :
      Finset (ordEqualPartitions n 8)))
    (f := fun P => ∑ i : Fin 8, marginalErr (μF n) (P.1 i))
    (g := fun _ => 8 * avgMarginalTV μF n)
    (@Finset.univ_nonempty _ _ (ordEqualPartitions_nonempty h8)) (by
      have heq : (∑ P : ordEqualPartitions n 8, ∑ i : Fin 8, marginalErr (μF n) (P.1 i))
          = ∑ P : ordEqualPartitions n 8, (8 * avgMarginalTV μF n) := by
        calc ∑ P : ordEqualPartitions n 8, ∑ i : Fin 8, marginalErr (μF n) (P.1 i)
            = 8 * (N₁:ℝ) * ∑ M : {M : Finset (Fin n) // M.card = n / 8},
                marginalErr (μF n) M.1 := hsum
          _ = ∑ P : ordEqualPartitions n 8, (8 * avgMarginalTV μF n) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, avgMarginalTV_eq, hcard]
              field_simp [hN₂']
      exact heq.le)
  exact ⟨P.1, P.2.1, P.2.2, hP⟩

end PartitionSelection

end
end PartialPermutation

end OAI
