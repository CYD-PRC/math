import Mathlib

namespace OAI

/-!
# Physical-shuffle law identification (family 238, gap G7)

`lean/docs/238.md` records for the binary-sweep formalization that
"Physical-shuffle law identification is not included." This challenge states
the missing identification: `d+1` physical Thorp steps — each an independent
switch of the current coordinate followed by a cyclic coordinate rotation —
compose to *exactly one coordinate sweep*, with the physical coins carried to
sweep coins by an explicit reparameterization.

The definitions below are verbatim copies of the solution-side model
(`OAI/Probability/BinarySweep/Model.lean` for the sweep side and
`OAI/Probability/BinarySweep/Processes/Basic.lean` for the physical side), so
the statement is about the repository's own objects up to a definitional copy.

Conventions pinned empirically before writing this statement (exhaustive
finite checks, not paper inference):
- application order of the reversed list products,
- rotation direction of the physical step,
- the layer↔step coin correspondence (layer `j` uses step `j`'s coin),
- the rotation reindex `i ↦ i+1+j (mod d+1)` of the coin domains
  (d=1: 16/16 histories; d=2: 4096/4096 histories, against the
  order-preserving alternative which matches only 2048/4096).

Only the two terminal theorems carry `sorry`; every definition above them is
meant to typecheck.
-/

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

/-- The positions of a binary deck of dimension `d`. -/
abbrev Slot (d : ℕ) := Fin d → Bool

/-- The coins of one physical step: one switch bit per position of the other
coordinates. -/
abbrev Coins (d : ℕ) := Slot d → Bool

/-- One physical step on a `d+1`-coordinate deck: switch coordinate `0` by
`c` evaluated on the remaining coordinates, then rotate the coordinates
cyclically (coordinate `0` moves to the last position). -/
def physical (d : ℕ) (c : Coins d) : Equiv.Perm (Slot (d + 1)) where
  toFun x := Fin.snoc (Fin.tail x) (x 0 ^^ c (Fin.tail x))
  invFun y := Fin.cons (y (Fin.last d) ^^ c (Fin.init y)) (Fin.init y)
  left_inv x := by simp
  right_inv y := by simp

/-- The permutation of `t` consecutive physical steps, coin `c i` used at the
`i`-th step in chronological order. -/
def physicalHistory (d t : ℕ) (c : Fin t → Coins d) : Equiv.Perm (Slot (d + 1)) :=
  (List.ofFn (fun i => physical d (c i))).reverse.prod

/-- Independent switches on the edges parallel to one coordinate. -/
def coordinateLayer (d : ℕ) (j : Fin d)
    (c : (({i : Fin d // i ≠ j} → Bool)) → Bool) : Equiv.Perm (Slot d) :=
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

/-- The coordinate layers of one sweep. -/
def binarySweep (d : ℕ) (c : SweepCoins d) : Equiv.Perm (Slot d) :=
  (List.ofFn (fun j => coordinateLayer d j (c j))).reverse.prod

/-- The law of a uniform random point of `Ω` pushed forward along `f`. -/
def finiteLaw {Ω G : Type*} [Fintype Ω] [Fintype G] (f : Ω → G) (g : G) : ℝ := by
  classical
  exact ∑ ω, if f ω = g then (Fintype.card Ω : ℝ)⁻¹ else 0

/-- The law of `t` physical steps on a `d+1`-coordinate deck. -/
def physicalLaw (d t : ℕ) : Equiv.Perm (Slot (d + 1)) → ℝ :=
  finiteLaw (physicalHistory d t)

/-- The law of one sweep on a dyadic deck. -/
def binaryLaw (d : ℕ) : Equiv.Perm (Slot d) → ℝ :=
  finiteLaw (binarySweep d)

/-- The rotated-coin reindex: physical step `j`'s coin sees coordinate
`i+1+j (mod d+1)` — the frame after `j` rotations. -/
def rotatedCoin (d : ℕ) (j : Fin (d + 1)) (c : Coins d) :
    (({i : Fin (d + 1) // i ≠ j} → Bool)) → Bool :=
  fun f => c fun i =>
    f ⟨⟨(i.val + 1 + j.val) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩,
        Fin.ne_of_val_ne (by
          have hi := i.isLt
          have hj := j.isLt
          show (i.val + 1 + j.val) % (d + 1) ≠ j.val
          by_cases hle : i.val + 1 + j.val < d + 1
          · rw [Nat.mod_eq_of_lt hle]; omega
          · rw [Nat.mod_eq_sub_mod (by omega : d + 1 ≤ i.val + 1 + j.val),
              Nat.mod_eq_of_lt (by omega : i.val + 1 + j.val - (d + 1) < d + 1)]
            omega)⟩

/-- The coin reparameterization: physical step `j`'s coin becomes sweep layer
`j`'s coin via `rotatedCoin`. -/
def sweepCoinsOfPhysical (d : ℕ) (c : Fin (d + 1) → Coins d) : SweepCoins (d + 1) :=
  fun j => rotatedCoin d j (c j)

/-- Permutation level: `d+1` physical steps with cyclic coordinate rotation
compose to exactly one coordinate sweep, coins reparameterized by
`sweepCoinsOfPhysical`. -/
theorem physical_sweep_identification (d : ℕ) (c : Fin (d + 1) → Coins d) :
    physicalHistory d (d + 1) c = binarySweep (d + 1) (sweepCoinsOfPhysical d c) := by
  sorry

/-- Law level (the consequence the scope note names): the law of `d+1`
physical steps is the sweep law. -/
theorem physical_law_is_sweep_law (d : ℕ) :
    physicalLaw d (d + 1) = binaryLaw (d + 1) := by
  sorry

end BinaryCoordinateSweeps
end

end OAI
