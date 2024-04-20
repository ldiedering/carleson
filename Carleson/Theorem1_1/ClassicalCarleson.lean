import Carleson.Carleson
import Carleson.HomogeneousType

--import Mathlib.Tactic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.BigOperators.Basic

--TODO: add local notation for f₀


noncomputable section
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

#check theorem1_1C
/- Specialize this to get the usual version of Carleson's theorem,
by taking `X = ℝ`, `K x y := 1 / (x - y)` and `𝓠 = {linear functions}`.
-/

def K : ℝ → ℝ → ℂ := fun x y ↦ 1 / (x - y)

instance : IsSpaceOfHomogeneousType ℝ 2 := by
  have : IsSpaceOfHomogeneousType ℝ (2 ^ FiniteDimensional.finrank ℝ ℝ) := inferInstance
  simpa

#check theorem1_1C K (by norm_num)

#check Complex.abs

#check Finset.range

#check AddCircle (2 * Real.pi)

--variable [IsSpaceOfHomogeneousType ℝ 2] (μ : MeasureTheory.Measure ℝ)

open BigOperators
open Finset

#check fourier
--def stdCircle : AddCircle (2 * Real.pi)

#check Finset.Icc

def partialFourierSum (f : ℝ → ℂ) (N : ℕ) : ℝ → ℂ := fun x ↦ ∑ n in Icc (-Int.ofNat ↑N) N, fourierCoeffOn Real.two_pi_pos f n * fourier n (x : AddCircle (2 * Real.pi))
#check partialFourierSum

variable {f : ℝ → ℂ} {N : ℕ}

--TODO : add reasonable notation
--local notation "S_" => partialFourierSum f

--TODO : seems like theorem1_1 is actually Theorem 1.2 from the paper
--TODO : check and compare to version in mathlib has_pointwise_sum_fourier_series_of_summable and similar
theorem classical_carleson --{f : ℝ → ℂ}
  (unicontf : UniformContinuous f) (periodicf : Function.Periodic f (2 * Real.pi)) (bdd_one : ∀ x, Complex.abs (f x) ≤ 1)
  {ε : ℝ} (hε : 0 < ε ∧ ε ≤ 2 * Real.pi) :
  --need condition E ⊆ Set.Icc 0 (2 * Real.pi) to ensure the E has finite volume
  ∃ E ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E ∧ MeasureTheory.volume.real E ≤ ε ∧
  ∃ N₀, ∀ x ∈ (Set.Icc 0 (2 * Real.pi)) \ E, ∀ N > N₀,
  Complex.abs (f x - partialFourierSum f N x) ≤ ε := by
    --TODO : use some scaled ε for the choose
    have ε2pos : ε / 2 > 0 := by linarith
    --TODO : ensure that we choose δ < Real.pi
    choose δ δpos hδ using Metric.uniformContinuous_iff.mp unicontf (ε / 2) ε2pos
    have δltpi : δ < Real.pi := sorry

    --definitions from section 10.1 depending on the choice of δ
    set K := Nat.floor ((2 * Real.pi) / δ) + 1 with Kdef
    have Kgt2 : (2 : ℝ) < K := by
      rw [Kdef]
      have : 2 < 2 * Real.pi / δ := (lt_div_iff δpos).mpr ((mul_lt_mul_left (by norm_num)).mpr δltpi)
      convert this.trans (Nat.lt_floor_add_one ((2 * Real.pi) / δ))
      simp
    let f₀ : ℝ → ℂ := fun x ↦ f ((2 * Real.pi * Int.floor ((K * x) / (2 * Real.pi))) / K)
    let E₁ : Set ℝ := ⋃ k ∈ range (K + 1), Set.Icc ((2 * Real.pi) / K * (k - ε / (16 * Real.pi))) ((2 * Real.pi) / K * (k + ε / (16 * Real.pi)))
    --added helper lemma
    have E₁measurable : MeasurableSet E₁ := by
      --rw [E₁def]
      apply measurableSet_biUnion
      intro k hk
      exact measurableSet_Icc
    have E₁volume : MeasureTheory.volume.real E₁ ≤ (ε / 2) := by
      calc MeasureTheory.volume.real E₁
      _ ≤ ∑ k in range (K + 1), MeasureTheory.volume.real (Set.Icc ((2 * Real.pi) / K * (k - ε / (16 * Real.pi))) ((2 * Real.pi) / K * (k + ε / (16 * Real.pi)))) := by
        apply MeasureTheory.measureReal_biUnion_finset_le
      _ = ∑ k in range (K + 1), ε / (4 * K) := by
        apply sum_congr
        . trivial
        intro k hk
        have : 2 * Real.pi / K * (k + ε / (16 * Real.pi)) - 2 * Real.pi / K * (k - ε / (16 * Real.pi)) = ε / (4 * K) := by
          field_simp
          ring
        rw [MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal]
        . exact this
        . rw [this]
          apply div_nonneg_iff.mpr
          left
          use hε.1.le
          linarith
      _ ≤ (K + 1) * (ε / (4 * K)) := by
        rw [Finset.sum_const]
        simp
      _ = ε / 2 * ((K + 1)/(2 * K)) := by ring
      _ ≤ ε / 2 := by
        rewrite (config := {occs := .pos [2]}) [← mul_one (ε / 2)]
        gcongr
        rw [div_le_iff (by linarith)]
        linarith
    --TODO : correct size of N₀
    let N₀ := Nat.ceil (K^2 / ε^3)
    --Lemma 10.2 from the paper
    --changed interval to Icc to match the interval in the theorem
    have piecePartialFourierSumApprox {N : ℕ} (hN : N > N₀) :
      ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E₁, Complex.abs (f₀ x - partialFourierSum f₀ N x) ≤ ε / 4:= by
      sorry
    --Lemma 10.3 from the paper
    --TODO : review measurability assumption
    --added subset assumption
    --changed interval to match the interval in the theorem
    /-
    have diffPartialFourierSums : ∃ E₂ ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E₂ ∧ MeasureTheory.volume.real E₂ ≤ ε / 2 ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E₂,
      sSup {Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) | N : ℕ} ≤ ε / 4 := by
      sorry
    -/
    --simplified statement so that we do not have to worry about a sSup
    have diffPartialFourierSums : ∃ E₂ ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E₂ ∧ MeasureTheory.volume.real E₂ ≤ ε / 2 ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E₂,
      ∀ N, Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) ≤ ε / 4 := by
      sorry
    obtain ⟨E₂, E₂subset, E₂measurable, E₂volume, hE₂⟩ := diffPartialFourierSums


    --TODO : change definition of E₁ to be able to prove this
    have E₁subset : E₁ ⊆ Set.Icc 0 (2 * Real.pi) := by
      rw [Set.iUnion_subset_iff]
      simp
      intro k klt x
      simp
      intro lex xle
      sorry

    --set E := E₁ ∪ E₂

    -- Definition of E, slightly changed compared to the paper
    /-
    use (E₁ ∪ E₂) ∩ Set.Icc 0 (2 * Real.pi)
    --use Set.union_subset E₁subset E₂subset
    constructor
    . apply Set.inter_subset_right
    use (E₁measurable.union E₂measurable).inter measurableSet_Icc
    constructor
    . calc MeasureTheory.volume.real ((E₁ ∪ E₂) ∩ Set.Icc 0 (2 * Real.pi))
      _ ≤ MeasureTheory.volume.real (E₁ ∪ E₂) := by
        apply MeasureTheory.measureReal_mono (Set.inter_subset_left (E₁ ∪ E₂) (Set.Icc 0 (2 * Real.pi))) _
        finiteness
      _ ≤ MeasureTheory.volume.real E₁ + MeasureTheory.volume.real E₂ := by apply MeasureTheory.measureReal_union_le
      _ ≤ ε / 2 + ε / 2 := by
          apply add_le_add E₁volume E₂volume
      _ = ε := by simp
    -/
    --Definition of E
    use E₁ ∪ E₂
    use Set.union_subset E₁subset E₂subset
    use E₁measurable.union E₂measurable
    constructor
    . calc MeasureTheory.volume.real (E₁ ∪ E₂)
      _ ≤ MeasureTheory.volume.real E₁ + MeasureTheory.volume.real E₂ := by apply MeasureTheory.measureReal_union_le
      _ ≤ ε / 2 + ε / 2 := by
          apply add_le_add E₁volume E₂volume
      _ = ε := by simp
    . use N₀
      intro x hx N NgtN₀
      --use "telescope" sum
      calc Complex.abs (f x - partialFourierSum f N x)
      _ = Complex.abs ((f x - f₀ x) + (f₀ x - partialFourierSum f₀ N x) + (partialFourierSum f₀ N x - partialFourierSum f N x)) := by congr; ring
      _ ≤ Complex.abs ((f x - f₀ x) + (f₀ x - partialFourierSum f₀ N x)) + Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) := by
        apply AbsoluteValue.add_le
      _ ≤ Complex.abs (f x - f₀ x) + Complex.abs (f₀ x - partialFourierSum f₀ N x) + Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) := by
        apply add_le_add_right
        apply AbsoluteValue.add_le
      _ ≤ (ε / 2) + (ε / 4) + (ε/4) := by
        gcongr
        .  --obtain this from hδ somehow
          apply le_of_lt
          apply hδ
          rw [Real.dist_eq]
          calc |x - 2 * Real.pi * ⌊K * x / (2 * Real.pi)⌋ / K|
          _ = |2 * Real.pi * (K * x / (2 * Real.pi)) / K - 2 * Real.pi * ⌊K * x / (2 * Real.pi)⌋ / K| := by congr; field_simp; ring
          _ = |2 * Real.pi * (K * x / (2 * Real.pi) - ⌊K * x / (2 * Real.pi)⌋) / K| := by
            ring_nf
          _ = 2 * Real.pi * |K * x / (2 * Real.pi) - ⌊K * x / (2 * Real.pi)⌋| / K := by
            rw [abs_div, abs_mul, abs_eq_self.mpr Real.two_pi_pos.le, abs_eq_self.mpr ((zero_lt_two).trans Kgt2).le]
          _ ≤ 2 * Real.pi * 1 / K := by
            apply (div_le_div_right ((zero_lt_two).trans Kgt2)).mpr
            apply (mul_le_mul_left Real.two_pi_pos).mpr
            rw [abs_eq_self.mpr]
            apply le_of_lt
            rw [sub_lt_iff_lt_add, add_comm]
            apply Int.lt_floor_add_one
            rw [le_sub_iff_add_le, zero_add]
            apply Int.floor_le
          _ < δ := by
            rw [div_lt_iff, mul_one, ← div_lt_iff' δpos]
            . push_cast
              apply Nat.lt_floor_add_one
            exact (zero_lt_two).trans Kgt2
        . have : x ∈ Set.Icc 0 (2 * Real.pi) \ E₁ := ⟨hx.1, fun xE₁ ↦ hx.2 (Set.mem_union_left E₂ xE₁)⟩
          apply piecePartialFourierSumApprox NgtN₀ x this
        . have : x ∈ Set.Icc 0 (2 * Real.pi) \ E₂ := ⟨hx.1, fun xE₂ ↦ hx.2 (Set.mem_union_right E₁ xE₂)⟩
          apply hE₂ x this N
      _ ≤ ε := by linarith


#check classical_carleson