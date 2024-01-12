import Mathlib
--Intro1 example (x y z w : ℕ) : x + y + (z + w) = w + z + (y + x) := by
rw [add_comm (x+y) (z+w)]
rw [add_comm x y]
rw [add_comm z w]

--Intro2 example (x y : ℕ) (hx : x + 0 = 1 * y) : x + y = y + y := by

rw [add_zero] at hx
rw [one_mul] at hx
rw [hx]------?

--Intro3 example (P Q R : Prop) (hPQ : P ↔ Q) (hQR : Q ↔ ¬R) : (¬P ↔ (Q ↔ P)) ↔ R := by

rw [hPQ]
rw [iff_self]
rw [iff_true]
rw [hQR]
rw [not_not]

--Intro4 example (P Q : Prop) (h : Q ∧ P ∧ Q) : (P ∨ ¬ Q) ∧ Q := by

rw [or_and_right]
rw [not_and_self_iff]
rw [or_false]
rw [and_comm] at h
rw [and_assoc] at h
rw [and_self] at h
exact h

--I1 example (A B : Set X) (x : X) (h : A = B) : x ∈ A → x ∈ B := by

intro
rw [h] at a
exact a

--I2 example : Continuous (fun (x : ℝ) => 5 * x ^ 2 + x + 6) := by

apply Continuous.add
apply Continuous.add
apply Continuous.mul
apply continuous_const
apply Continuous.pow
apply continuous_id
apply continuous_id------------?
apply continuous_const


--I3 example : ∃ n : ℕ, 8 < n ∧ n < 10 := by

use 9
constructor
apply Nat.lt_succ_self
apply Nat.lt_succ_self -----how to apply twice on one line?


--I4 example {G : Type} [Group G] {x : G} : [x ; x] = 1 := by
simp[commutator_def]



--I5 example {G : Type*} [Group G] {x y z : G} : [[x ; y⁻¹]; z] ^ y * [[y; z⁻¹]; x] ^ z * [[z; x⁻¹]; y] ^ x = 1 := by
simp[conjugate_def]
simp[commutator_def]
simp[<-mul_assoc]

----how does one know when to use simp/apply/rw? and how?

--I6 example (X Y Z : Type*) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by

rw [continuous_def] at hf
rw [continuous_def] at hg
rw [continuous_def]
intro
rw [Set.preimage_comp]
intro
apply hf
apply hg
apply a  ----exact a
