import Mathlib

open scoped BigOperators

namespace OAI

/-- Every multinomial coefficient is at most `(card s)^(sum of multiplicities)`.
This is the elementary second half of equation (15) in the four-row paper. -/
theorem multinomial_le_card_pow {α : Type*} [Fintype α] (s : Finset α) (f : α → ℕ) :
    Nat.multinomial s f ≤ s.card ^ (∑ i ∈ s, f i) := by
  classical
  let g : α → ℕ := fun i => if i ∈ s then f i else 0
  have hg : Nat.multinomial s f = Nat.multinomial s g := by
    apply Nat.multinomial_congr
    intro a ha
    simp only [g, ite_eq_left ha]
  have hterm : g ∈ Finset.piAntidiag s (∑ i ∈ s, g i) := by
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, ?_⟩
    · simp [g]
    · intro i hi
      by_contra h
      simp only [g, ite_eq_right h] at hi
      exact hi rfl
  rw [hg]
  calc Nat.multinomial s g
      ≤ ∑ k ∈ Finset.piAntidiag s (∑ i ∈ s, g i), Nat.multinomial s k := by
        exact Finset.single_le_sum (fun k _ => le_of_lt (Nat.multinomial_pos (s := s) (f := k))) hterm
    _ = s.card ^ (∑ i ∈ s, g i) := by
        have h := Finset.sum_pow_eq_sum_piAntidiag s (fun _ => 1) (∑ i ∈ s, g i)
        simpa using h.symm
    _ = s.card ^ (∑ i ∈ s, f i) := by
        congr 1
        exact Finset.sum_congr rfl (fun i hi => by simp only [g, ite_eq_left hi])

end OAI
