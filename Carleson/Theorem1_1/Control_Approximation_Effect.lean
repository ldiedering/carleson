/- This file formalizes section 10.8 (The error bound) from the paper. -/
import Carleson.Carleson
import Carleson.HomogeneousType
import Carleson.Theorem1_1.Basic
import Carleson.Theorem1_1.Carleson_on_the_real_line

import Mathlib.Analysis.Fourier.AddCircle


noncomputable section


/-Slightly more general version of Lemma 10.3 (control approximation effect).-/
--TODO : review measurability assumption
--added subset assumption
--changed interval to match the interval in the theorem
lemma control_approximation_effect {ε : ℝ} (hε : 0 < ε ∧ ε ≤ 2 * Real.pi)
    {h : ℝ → ℂ} (hh: Measurable h ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi), Complex.abs (h x) ≤ (2 ^ (- (2 ^ 50 : ℝ))) * ε ^ 2 ):
    ∃ E ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E ∧ MeasureTheory.volume.real E ≤ ε ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E,
      ∀ N, Complex.abs (partialFourierSum h N x) ≤ ε / 4 := by
  set E := {x ∈ Set.Icc 0 (2 * Real.pi) | ∃ N, Complex.abs (partialFourierSum h N x) > ε / 4} with Edef
  use E
  constructor
  . intro x hx
    rw [Edef] at hx
    simp at hx
    exact hx.1
  constructor
  . sorry
  sorry