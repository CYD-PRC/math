import Mathlib
import OAI.Probability.BinarySweep.Model
import OAI.Probability.BinarySweep.Processes.Basic

/-!
# G7 solution: the physical-shuffle law identification

Proves `ComparatorChallenges/PhysicalSweepIdentification.lean` over the
repository's own objects (`BinarySweep/Model.lean`, `Processes/Basic.lean`).

Architecture (all conventions pinned by exhaustive probes at d=1 and d=2
before any of this was written — see the challenge file's header):

* `physical d c = rot d * switchZero d c` — a physical step is a switch of
  coordinate `0` followed by the cyclic rotation.
* Telescope: `t` physical steps factor as `rot^t` times a product of
  conjugated switches; at `t = d+1` the rotation vanishes (`rot^(d+1) = 1`)
  and the conjugated switch at step `j` is exactly `coordinateLayer j` with
  the coin reindexed by `i ↦ i+1+j (mod d+1)`.
* The law-level statement follows from bijectivity of the coin
  reparameterization.
-/

namespace OAI

namespace BinaryCoordinateSweeps

open scoped BigOperators

/-- Coordinate rotation by one: pointwise `(rot d x) i = x (finRotate (d+1) i)`,
i.e. coordinate `0` moves to the last position. -/
def rot (d : ℕ) : Equiv.Perm (Slot (d + 1)) :=
  Equiv.piCongrLeft' (fun _ : Fin (d + 1) => Bool) (finRotate (d + 1)).symm

/-- Switch of coordinate `0` by `c` evaluated on the tail — the other half of
`physical`. -/
def switchZero (d : ℕ) (c : Coins d) : Equiv.Perm (Slot (d + 1)) where
  toFun x := Fin.cons (x 0 ^^ c (Fin.tail x)) (Fin.tail x)
  invFun x := Fin.cons (x 0 ^^ c (Fin.tail x)) (Fin.tail x)
  left_inv x := by simp
  right_inv x := by simp

@[simp] lemma rot_apply (d : ℕ) (x : Slot (d + 1)) (i : Fin (d + 1)) :
    rot d x i = x (finRotate (d + 1) i) := rfl

lemma rot_iterate (d k : ℕ) (x : Slot (d + 1)) :
    (⇑(rot d))^[k] x = fun i => x ((finRotate (d + 1))^[k] i) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply, ih]
    funext i
    rw [rot_apply, Function.iterate_succ, Function.comp_apply]

/-- A physical step is switch-then-rotate. -/
theorem physical_eq (d : ℕ) (c : Coins d) :
    physical d c = rot d * switchZero d c := by
  ext x i
  show (Fin.snoc (Fin.tail x) (x 0 ^^ c (Fin.tail x)) : Slot (d + 1)) i =
    (rot d * switchZero d c) x i
  rw [Fin.snoc_eq_cons_rotate]
  simp only [Equiv.Perm.mul_apply, rot_apply, switchZero, Equiv.coe_fn_mk]

/-- Powers of `finRotate` act as addition modulo the modulus. -/
lemma finRotate_pow_val (d k : ℕ) (i : Fin (d + 1)) :
    (((finRotate (d + 1)) ^ k) i).val = (i.val + k) % (d + 1) := by
  induction k generalizing i with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, coe_finRotate]
    split_ifs with hlt
    · have hid : i.val = d := by rw [hlt]; exact Fin.val_last d
      rw [Nat.zero_add, hid, show d + (k + 1) = (d + 1) + k by omega, Nat.add_mod_left]
    · congr 1
      omega

/-- Powers of `rot` act pointwise through powers of `finRotate`. -/
lemma rot_pow_apply (d k : ℕ) (x : Slot (d + 1)) (i : Fin (d + 1)) :
    ((rot d) ^ k) x i = x (((finRotate (d + 1)) ^ k) i) := by
  rw [Equiv.Perm.coe_pow, rot_iterate, Equiv.Perm.iterate_eq_pow]

lemma rot_pow_apply_fun (d k : ℕ) (x : Slot (d + 1)) :
    ((rot d) ^ k) x = fun i => x (((finRotate (d + 1)) ^ k) i) :=
  funext (rot_pow_apply d k x)

/-- The `d+1`-fold rotation is trivial. -/
theorem rot_pow_card (d : ℕ) : (rot d) ^ (d + 1) = 1 := by
  ext x i
  have hfin : (finRotate (d + 1)) ^ (d + 1) = 1 := by
    cases d with
    | zero => rw [pow_one, finRotate_one]; rfl
    | succ d' =>
      have hcyc : Equiv.Perm.IsCycle (finRotate (d' + 2)) := isCycle_finRotate
      have hsupp : (finRotate (d' + 2)).support = Finset.univ := support_finRotate
      have hord : orderOf (finRotate (d' + 2)) = d' + 2 := by
        rw [hcyc.orderOf, hsupp]
        simp
      calc (finRotate (d' + 2)) ^ (d' + 2)
          = (finRotate (d' + 2)) ^ orderOf (finRotate (d' + 2)) := by rw [hord]
        _ = 1 := pow_orderOf_eq_one _
  have hi : (finRotate (d + 1))^[d + 1] i = i := by
    rw [Equiv.Perm.iterate_eq_pow, hfin, Equiv.Perm.coe_one]
    rfl
  simp only [Equiv.Perm.coe_pow, rot_iterate, Equiv.Perm.coe_one, hi]
  rfl

/-- The `k`-fold conjugate of the zero switch by the rotation. -/
def conjSwitch (d k : ℕ) (c : Coins d) : Equiv.Perm (Slot (d + 1)) :=
  ((rot d) ^ k)⁻¹ * switchZero d c * (rot d) ^ k

/-- Group bookkeeping: the conjugate absorbs a rotation factor. -/
theorem switchZero_mul_rot_pow (d : ℕ) (c : Coins d) (k : ℕ) :
    switchZero d c * (rot d) ^ k = (rot d) ^ k * conjSwitch d k c := by
  rw [conjSwitch]; group

/-- The rotated-coin reindex, shared by the commute lemma and the
reparameterization: physical step `k`'s coin sees coordinate `i+1+k`. -/
def rotatedCoin (d : ℕ) (k : Fin (d + 1)) (c : Coins d) :
    (({i : Fin (d + 1) // i ≠ k} → Bool)) → Bool :=
  fun f => c fun i =>
    f ⟨⟨(i.val + 1 + k.val) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩,
        Fin.ne_of_val_ne (by
          have hi := i.isLt
          have hk := k.isLt
          show (i.val + 1 + k.val) % (d + 1) ≠ k.val
          by_cases hle : i.val + 1 + k.val < d + 1
          · rw [Nat.mod_eq_of_lt hle]; omega
          · rw [Nat.mod_eq_sub_mod (by omega : d + 1 ≤ i.val + 1 + k.val),
              Nat.mod_eq_of_lt (by omega : i.val + 1 + k.val - (d + 1) < d + 1)]
            omega)⟩

/-- Pointwise behavior of a coordinate layer at its own coordinate. -/
lemma coordinateLayer_apply_self (d : ℕ) (k : Fin (d + 1))
    (c' : (({i : Fin (d + 1) // i ≠ k} → Bool)) → Bool) (x : Slot (d + 1)) :
    coordinateLayer (d + 1) k c' x k = (x k ^^ c' (fun j => x ↑j)) := by
  simp only [coordinateLayer, Equiv.trans_apply, Equiv.piSplitAt_apply,
    Equiv.coe_fn_mk, Equiv.piSplitAt_symm_apply]
  split_ifs <;> rfl

/-- Pointwise behavior of a coordinate layer off its own coordinate. -/
lemma coordinateLayer_apply_ne (d : ℕ) (k j' : Fin (d + 1)) (h : j' ≠ k)
    (c' : (({i : Fin (d + 1) // i ≠ k} → Bool)) → Bool) (x : Slot (d + 1)) :
    coordinateLayer (d + 1) k c' x j' = x j' := by
  simp only [coordinateLayer, Equiv.trans_apply, Equiv.piSplitAt_apply,
    Equiv.coe_fn_mk, Equiv.piSplitAt_symm_apply]
  split_ifs with hne
  · exact absurd hne h
  · rfl

/-- Commutation, pointwise: pushing the zero switch across `k` rotations gives
the coordinate layer at `k` with the rotated coin. -/
theorem switchZero_mul_rot_pow_eq_layer (d : ℕ) (k : Fin (d + 1)) (c : Coins d) :
    switchZero d c * (rot d) ^ k.val =
      (rot d) ^ k.val * coordinateLayer (d + 1) k (rotatedCoin d k c) := by
  ext x i
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, rot_pow_apply, rot_pow_apply_fun]
  set y := (fun j => x (((finRotate (d + 1)) ^ k.val) j)) with hy
  have hk0 : ((finRotate (d + 1)) ^ k.val) (0 : Fin (d + 1)) = k :=
    Fin.ext (by rw [finRotate_pow_val]; simp [Nat.mod_eq_of_lt k.isLt])
  have hy0 : y 0 = x k := congrArg x hk0
  have hytail : Fin.tail y = fun i₀ => x ⟨(i₀.val + 1 + k.val) % (d + 1),
      Nat.mod_lt _ (Nat.succ_pos d)⟩ :=
    funext fun i₀ => congrArg x (Fin.ext (by rw [finRotate_pow_val, Fin.val_succ]))
  obtain rfl | ⟨i', rfl⟩ := Fin.eq_zero_or_eq_succ i
  · show switchZero d c y 0 = coordinateLayer (d + 1) k (rotatedCoin d k c) x _
    rw [show switchZero d c y = Fin.cons (y 0 ^^ c (Fin.tail y)) (Fin.tail y) from rfl,
      Fin.cons_zero, hy0, hytail, hk0, coordinateLayer_apply_self]
    rfl
  · show switchZero d c y i'.succ =
      coordinateLayer (d + 1) k (rotatedCoin d k c) x _
    rw [show switchZero d c y = Fin.cons (y 0 ^^ c (Fin.tail y)) (Fin.tail y) from rfl,
      Fin.cons_succ]
    rw [coordinateLayer_apply_ne]
    · rfl
    · exact Fin.ne_of_val_ne (by
        rw [finRotate_pow_val, Fin.val_succ]
        have hi' := i'.isLt
        have hk := k.isLt
        show (i'.val + 1 + k.val) % (d + 1) ≠ k.val
        by_cases hle : i'.val + 1 + k.val < d + 1
        · rw [Nat.mod_eq_of_lt hle]; omega
        · rw [Nat.mod_eq_sub_mod (by omega : d + 1 ≤ i'.val + 1 + k.val),
            Nat.mod_eq_of_lt (by omega : i'.val + 1 + k.val - (d + 1) < d + 1)]
          omega)

/-- The core conjugation lemma: the `k`-fold conjugate of the zero switch is
the coordinate layer at coordinate `k`, with the coin reindexed by the
rotation `i ↦ i+1+k (mod d+1)`. -/
theorem conjSwitch_eq_layer (d : ℕ) (k : Fin (d + 1)) (c : Coins d) :
    conjSwitch d k.val c = coordinateLayer (d + 1) k (rotatedCoin d k c) := by
  rw [conjSwitch, mul_assoc, switchZero_mul_rot_pow_eq_layer]
  group

/-- List step for the history: the `t+1`-step history is the newest physical
step followed by the `t`-step history on the first `t` coins. -/
lemma physicalHistory_succ (d t : ℕ) (c : Fin (t + 1) → Coins d) :
    physicalHistory d (t + 1) c =
      physical d (c (Fin.last t)) * physicalHistory d t (fun i => c i.castSucc) := by
  show ((List.ofFn fun i : Fin (t + 1) => physical d (c i)).reverse).prod =
    physical d (c (Fin.last t)) *
      ((List.ofFn fun i : Fin t => physical d (c i.castSucc)).reverse).prod
  rw [List.ofFn_succ_last, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.prod_cons]

/-- List step for the conjugated-switch product, same shape. -/
lemma conjProd_succ (d t : ℕ) (c : Fin (t + 1) → Coins d) :
    ((List.ofFn fun k : Fin (t + 1) => conjSwitch d k.val (c k)).reverse).prod =
      conjSwitch d t (c (Fin.last t)) *
        ((List.ofFn fun k : Fin t => conjSwitch d k.val (c k.castSucc)).reverse).prod := by
  rw [List.ofFn_succ_last, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.prod_cons]
  rfl

/-- Telescope: `t` physical steps factor as `rot^t` times the product of the
conjugated switches, in chronological coin order. -/
theorem physicalHistory_eq (d t : ℕ) (c : Fin t → Coins d) :
    physicalHistory d t c =
      (rot d) ^ t *
        (List.ofFn (fun k : Fin t => conjSwitch d k.val (c k))).reverse.prod := by
  induction t with
  | zero => simp [physicalHistory]
  | succ t ih =>
    rw [physicalHistory_succ, ih, physical_eq, conjProd_succ]
    set M := ((List.ofFn fun k : Fin t => conjSwitch d k.val (c k.castSucc)).reverse).prod
      with hM
    have key := switchZero_mul_rot_pow d (c (Fin.last t)) t
    calc (rot d * switchZero d (c (Fin.last t))) * ((rot d) ^ t * M)
        = rot d * (switchZero d (c (Fin.last t)) * (rot d) ^ t) * M := by group
      _ = rot d * ((rot d) ^ t * conjSwitch d t (c (Fin.last t))) * M := by rw [key]
      _ = (rot d) ^ (t + 1) * (conjSwitch d t (c (Fin.last t)) * M) := by group

/-- The coin reparameterization, solution-side. -/
def sweepCoinsOfPhysical (d : ℕ) (c : Fin (d + 1) → Coins d) : SweepCoins (d + 1) :=
  fun j => rotatedCoin d j (c j)

/-- Permutation level: `d+1` physical steps are exactly one sweep. -/
theorem physical_sweep_identification (d : ℕ) (c : Fin (d + 1) → Coins d) :
    physicalHistory d (d + 1) c = binarySweep (d + 1) (sweepCoinsOfPhysical d c) := by
  rw [physicalHistory_eq, rot_pow_card, one_mul]
  show ((List.ofFn fun k : Fin (d + 1) => conjSwitch d k.val (c k)).reverse).prod =
    ((List.ofFn fun j : Fin (d + 1) =>
      coordinateLayer (d + 1) j (sweepCoinsOfPhysical d c j)).reverse).prod
  exact congrArg (List.prod ∘ List.reverse) (congrArg List.ofFn
    (funext fun j => conjSwitch_eq_layer d j (c j)))

/-- The rotated index never collides with the layer's own coordinate. -/
lemma rotate_ne_self (d : ℕ) (j : Fin (d + 1)) (i : Fin d) :
    (i.val + 1 + j.val) % (d + 1) ≠ j.val := by
  have hi := i.isLt; have hj := j.isLt
  by_cases hle : i.val + 1 + j.val < d + 1
  · rw [Nat.mod_eq_of_lt hle]; omega
  · rw [Nat.mod_eq_sub_mod (by omega : d + 1 ≤ i.val + 1 + j.val),
      Nat.mod_eq_of_lt (by omega : i.val + 1 + j.val - (d + 1) < d + 1)]; omega

/-- The rotation reindex `i ↦ i+1+j (mod d+1)` as an equivalence between the
physical coin's domain and the layer coin's domain. -/
def reindexEquiv (d : ℕ) (j : Fin (d + 1)) : Fin d ≃ {i : Fin (d + 1) // i ≠ j} where
  toFun w := ⟨⟨(w.val + 1 + j.val) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩,
    Fin.ne_of_val_ne (rotate_ne_self d j w)⟩
  invFun i' := ⟨(i'.1.val + d - j.val) % (d + 1), by
    have hlt : (i'.1.val + d - j.val) % (d + 1) < d + 1 := Nat.mod_lt _ (Nat.succ_pos d)
    have hne : i'.1.val ≠ j.val := fun h => i'.2 (Fin.ext h)
    have hj := j.isLt
    have hi' := i'.1.isLt
    by_contra h
    have hwd : (i'.1.val + d - j.val) % (d + 1) = d := by omega
    have hme : (i'.1.val + d - j.val) ≡ d [MOD (d + 1)] :=
      hwd.trans (Nat.mod_eq_of_lt (Nat.lt_succ_self d)).symm
    have h1 : i'.1.val + d - j.val = i'.1.val + (d - j.val) := by omega
    rw [h1] at hme
    have hme2 : i'.1.val + d ≡ j.val + d [MOD (d + 1)] := by
      have h2 := hme.add_right j.val
      rwa [Nat.add_assoc, Nat.sub_add_cancel (by omega : j.val ≤ d),
        Nat.add_comm d j.val] at h2
    have hfin : i'.1.val ≡ j.val [MOD (d + 1)] :=
      Nat.ModEq.add_right_cancel (n := d + 1) (c := d) (d := d)
        (Nat.ModEq.refl (a := d)) hme2
    exact hne (Nat.ModEq.eq_of_lt_of_lt hfin hi' hj)⟩
  left_inv w := by
    apply Fin.ext
    show (((w.val + 1 + j.val) % (d + 1)) + d - j.val) % (d + 1) = w.val
    have hw := w.isLt; have hj := j.isLt
    by_cases hq : w.val + 1 + j.val < d + 1
    · rw [Nat.mod_eq_of_lt hq]
      have e1 : w.val + 1 + j.val + d - j.val = w.val + (d + 1) := by omega
      rw [e1, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
        Nat.mod_eq_of_lt (by omega : w.val < d + 1)]
    · rw [Nat.mod_eq_sub_mod (by omega : d + 1 ≤ w.val + 1 + j.val),
        Nat.mod_eq_of_lt (by omega : w.val + 1 + j.val - (d + 1) < d + 1)]
      have e2 : w.val + 1 + j.val - (d + 1) + d - j.val = w.val := by omega
      rw [e2, Nat.mod_eq_of_lt (by omega : w.val < d + 1)]
  right_inv i' := by
    apply Subtype.ext
    apply Fin.ext
    show ((((i'.1.val + d - j.val) % (d + 1)) + 1 + j.val) % (d + 1)) = i'.1.val
    have hi' := i'.1.isLt; have hj := j.isLt
    rw [Nat.add_assoc, Nat.mod_add_mod]
    have e3 : i'.1.val + d - j.val + (1 + j.val) = i'.1.val + (d + 1) := by omega
    rw [e3, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
      Nat.mod_eq_of_lt hi']

/-- The rotated coin, unfolded through the reindex equivalence. -/
lemma rotatedCoin_apply (d : ℕ) (j : Fin (d + 1)) (c : Coins d)
    (f : ({i : Fin (d + 1) // i ≠ j} → Bool)) :
    rotatedCoin d j c f = c (fun i => f ((reindexEquiv d j) i)) := rfl

/-- The coin reparameterization is bijective: injectivity from the reindex's
left inverse, surjectivity from its right inverse. -/
theorem sweepCoinsOfPhysical_bijective (d : ℕ) :
    Function.Bijective (sweepCoinsOfPhysical d) := by
  constructor
  · intro c₁ c₂ h
    funext j s
    have h2 := congrFun (congrFun h j) (fun i' => s ((reindexEquiv d j).symm i'))
    simp only [sweepCoinsOfPhysical] at h2
    rw [rotatedCoin_apply, rotatedCoin_apply] at h2
    have key : (fun i => (fun i' => s ((reindexEquiv d j).symm i'))
        ((reindexEquiv d j) i)) = s := by
      funext i
      exact congrArg s (Equiv.symm_apply_apply _ _)
    rwa [key] at h2
  · intro c'
    refine ⟨fun j s => c' j (fun i' => s ((reindexEquiv d j).symm i')), ?_⟩
    funext j f
    show rotatedCoin d j (fun s => c' j (fun i' => s ((reindexEquiv d j).symm i'))) f =
      c' j f
    rw [rotatedCoin_apply]
    apply congrArg (c' j)
    funext i'
    exact congrArg f (Equiv.apply_symm_apply _ i')

/-- Law level: the law of `d+1` physical steps is the sweep law. -/
theorem physical_law_is_sweep_law (d : ℕ) :
    physicalLaw d (d + 1) = binaryLaw (d + 1) := by
  have hid : physicalHistory d (d + 1) = binarySweep (d + 1) ∘ sweepCoinsOfPhysical d :=
    funext (physical_sweep_identification d)
  funext g
  show finiteLaw _ g = finiteLaw _ g
  rw [hid]
  classical
  simp only [finiteLaw, Function.comp_apply]
  rw [show (Fintype.card (Fin (d + 1) → Coins d) : ℝ)⁻¹ =
      (Fintype.card (SweepCoins (d + 1)) : ℝ)⁻¹ by
    rw [Fintype.card_of_bijective (sweepCoinsOfPhysical_bijective d)]]
  exact (sweepCoinsOfPhysical_bijective d).sum_comp
    (fun c' => @ite ℝ (binarySweep (d + 1) c' = g) (Classical.propDecidable _)
      (Fintype.card (SweepCoins (d + 1)) : ℝ)⁻¹ 0)

end BinaryCoordinateSweeps

end OAI
