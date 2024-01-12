import Mathlib

#check 2

open Real
#check π

open Complex
#check π+I

#check true

def f (n : ℤ) := n^2 - 1
#check (f)
#eval f 0

variable (n : ℕ) (K : Type) [Field K]
#check (0 : (Fin n → K))

#check ℕ
#check ℤ
#check Bool
#check ℤ → ℤ
#check Fin n → K

#check Type
#check Type 32

#check Prop

#check 1+1=2
#check 1+1=3

#check ∀ (x : ℕ) (y : ℕ), x + y = y + x

#check ∀ n : ℕ, ∃ a b c d : ℕ, a^2+b^2+c^2+d^2=n
example : ∀ n : ℕ, ∃ a b c d : ℕ, a^2+b^2+c^2+d^2=n := by 
  apply?
--  apply Nat.sum_four_squares -- found theorem name using "apply?"

open Polynomial
variable (R : Type u) [CommRing R]
#check IsNoetherianRing R → IsNoetherianRing R[X]

example : IsNoetherianRing R → IsNoetherianRing R[X] := by sorry --apply Polynomial.isNoetherianRing

example (P Q : Prop) (h : ¬ (P ∨ Q)) : ¬ Q ∧  ¬ P := by tauto

variable (P Q : Prop) (T : P → Q) (pfP : P)

#check T pfP

example : ∀ n, ∃ p ≥ n, Nat.Prime p := by apply Nat.exists_infinite_primes

example (x : ℝ) (h : x > 0): x/x=1 := by
--  have : x ≠ 0 := by apply? -- this will find the proof of the second line
  have : x ≠ 0 := by exact _root_.ne_of_gt h--by exact _root_.ne_of_gt h
  simp [this]
--  simp? [this] -- could be used instead, and will lead to:
--  simp only [ne_eq, this, not_false_eq_true, div_self]
