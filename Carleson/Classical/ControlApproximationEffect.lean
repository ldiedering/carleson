import Carleson.Classical.CarlesonOnTheRealLine

/- This file contains most of Section 11.6 (The error bound) from the blueprint.
   The main result is control_approximation_effect.
-/

noncomputable section

local notation "T" => carlesonOperatorReal K
local notation "S_" => partialFourierSum

open scoped Real
open MeasureTheory
open Real (pi_pos)


/- TODO: might be generalized. -/
lemma ENNReal.le_on_subset {X : Type} [MeasurableSpace X] (μ : Measure X) {f g : X → ENNReal}
    {E : Set X} (hE : MeasurableSet E)
    (hf : Measurable f) (hg : Measurable g) {a : ENNReal} (h : ∀ x ∈ E, a ≤ f x + g x) :
    ∃ E' ⊆ E, MeasurableSet E' ∧ μ E ≤ 2 * μ E'
      ∧ ((∀ x ∈ E', a / 2 ≤ f x) ∨ (∀ x ∈ E', a / 2 ≤ g x)) := by
  set Ef := E ∩ f⁻¹' (Set.Ici (a / 2)) with Ef_def
  set Eg := E ∩ g⁻¹' (Set.Ici (a / 2)) with Eg_def
  have : E ⊆ Ef ∪ Eg := by
    intro x hx
    rw [Ef_def, Eg_def]
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici]
    by_contra! hx'
    absurd le_refl a
    push_neg
    calc a
      _ ≤ f x + g x := h x hx
      _ < a / 2 + a / 2 := by
        gcongr
        · exact hx'.1 hx
        · exact hx'.2 hx
      _ = a := by
        ring_nf
        apply ENNReal.div_mul_cancel <;> norm_num
  have : μ E ≤ 2 * μ Ef ∨ μ E ≤ 2 * μ Eg := by
    by_contra! hEfg
    absurd le_refl (2 * μ E)
    push_neg
    calc 2 * μ E
    _ ≤ 2 * μ (Ef ∪ Eg) := by
      gcongr
    _ ≤ 2 * (μ Ef + μ Eg) := by
      gcongr
      exact measure_union_le _ _
    _ = 2 * μ Ef + 2 * μ Eg := by ring
    _ < μ E + μ E := by
      gcongr
      · exact hEfg.1
      · exact hEfg.2
    _ = 2 * μ E := by ring
  rcases this with hEf | hEg
  · refine ⟨Ef, Set.inter_subset_left, hE.inter (hf measurableSet_Ici), hEf, Or.inl ?_⟩
    simp [Ef_def]
  · refine ⟨Eg, Set.inter_subset_left, hE.inter (hg measurableSet_Ici), hEg, Or.inr ?_⟩
    simp [Eg_def]

open Complex ComplexConjugate

lemma Dirichlet_Hilbert_eq {N : ℕ} {x : ℝ} :
    (max (1 - |x|) 0) * dirichletKernel' N (x) =
      exp (I * (-N * x)) * k x + conj (exp (I * (-N * x)) * k x) := by
  simp [dirichletKernel', k, conj_ofReal, ← exp_conj, mul_comm, ← mul_assoc]
  ring

lemma Dirichlet_Hilbert_diff {N : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (-π) π) :
    ‖dirichletKernel' N (x) - (exp (I * (-N * x)) * k x + conj (exp (I * (-N * x)) * k x))‖ ≤ π := by
  rw [← Dirichlet_Hilbert_eq]
  by_cases h : 1 - cexp (I * ↑x) = 0
  · rw [sub_eq_zero] at h
    rw [dirichletKernel'_eq_zero h.symm]
    simp [pi_pos.le]
  push_neg at h
  conv => pattern (dirichletKernel' N x); rw [← (one_mul (dirichletKernel' N x))]
  rw [← sub_mul]
  norm_cast
  rw [← min_sub_sub_left]
  simp only [sub_sub_cancel, sub_zero]
  rw [dirichletKernel', mul_add]
  calc ‖  (min |x| 1) * (exp (I * N * x) / (1 - exp (-I * x)))
        + (min |x| 1) * (exp (-I * N * x) / (1 - exp (I * x)))‖
    _ ≤   ‖(min |x| 1) * (exp (I * N * x) / (1 - exp (-I * x)))‖
        + ‖(min |x| 1) * (exp (-I * N * x) / (1 - exp (I * x)))‖ := by
      apply norm_add_le
    _ ≤ |x| * (1 / ‖1 - exp (I * x)‖) + |x| * (1 / ‖1 - exp (I * x)‖) := by
      simp only [neg_mul, norm_mul, norm_real, norm_div]
      rw [Real.norm_of_nonneg (by simp)]
      gcongr
      · apply min_le_left
      · rw [mul_assoc I, mul_comm I]
        norm_cast
        rw [norm_exp_ofReal_mul_I]
      · rw [← norm_conj, map_sub, map_one, ←exp_conj, ← neg_mul, map_mul, conj_I, conj_ofReal]
      · apply min_le_left
      · /-Duplicate from above:
        TODO: how to remove duplicate goals? -/
        rw [mul_assoc I, mul_comm I, ← neg_mul]
        norm_cast
        rw [norm_exp_ofReal_mul_I]
    _ = 2 * (|x| / ‖1 - exp (I * x)‖) := by ring
    _ ≤ 2 * (π / 2) := by
      gcongr 2 * ?_
      rw [div_le_iff₀' (by rwa [norm_pos_iff]), ← div_le_iff₀ (by linarith [pi_pos]),
        div_div_eq_mul_div, mul_div_assoc, mul_comm]
      apply lower_secant_bound' (by rfl)
      have : |x| ≤ π := by
        rwa [abs_le]
      linarith
    _ = π := by ring

section

open Filter Topology

lemma le_iSup_of_tendsto {α β} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (ha : Tendsto f atTop (𝓝 a)) : a ≤ iSup f := by
  apply le_of_forall_lt
  intro c hc
  have : ∀ᶠ (x : β) in atTop, c < f x := Filter.Tendsto.eventually_const_lt hc ha
  rcases this.exists with ⟨x, hx⟩
  exact lt_of_lt_of_le hx (le_iSup _ _)

lemma integrable_annulus {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * π)) {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume (-π) (3 * π)) {r : ℝ} (r_nonneg : 0 ≤ r) (rle1 : r < 1) :
    Integrable (fun x ↦ f x) (volume.restrict {y | dist x y ∈ Set.Ioo r 1}) := by
  rw [← IntegrableOn, annulus_real_eq r_nonneg]
  apply IntegrableOn.union <;>
  · rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)]
    apply hf.mono_set
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith [pi_pos])]
    intro y hy
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2, Real.two_le_pi]

lemma intervalIntegrable_mul_dirichletKernel' {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * π)) {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume (-π) (3 * π)) {N : ℕ} :
    IntervalIntegrable (fun y ↦ f y * dirichletKernel' N (x - y)) volume (x - π) (x + π) := by
  apply (hf.mono_set _).mul_bdd
    (dirichletKernel'_measurable.comp (measurable_id.const_sub _)).aestronglyMeasurable
  · use (2 * N + 1)
    intro y
    apply norm_dirichletKernel'_le
  · rw [Set.uIcc_of_le, Set.uIcc_of_le]
    on_goal 1 => apply Set.Icc_subset_Icc
    all_goals linarith [hx.1, hx.2, pi_pos]

lemma intervalIntegrable_mul_dirichletKernel'_max {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * π)) {f : ℝ → ℂ}
   (hf : IntervalIntegrable f volume (-π) (3 * π)) {N : ℕ} :
    IntervalIntegrable (fun y ↦ f y * ((max (1 - |x - y|) 0)
      * dirichletKernel' N (x - y))) volume (x - π) (x + π) := by
  conv => pattern ((f _) * _); rw [← mul_assoc]
  apply intervalIntegrable_mul_dirichletKernel' hx
    (IntervalIntegrable.mul_bdd hf (Complex.measurable_ofReal.comp
      ((Measurable.const_sub (_root_.continuous_abs.measurable.comp
        (measurable_id.const_sub _)) _).max measurable_const)).aestronglyMeasurable _)
  use 1
  intro y
  simp [Real.norm_of_nonneg (le_max_right _ _)]

lemma intervalIntegrable_mul_dirichletKernel'_max' {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * π)) {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume (-π) (3 * π)) {N : ℕ} :
    IntervalIntegrable (fun y ↦ f y
      * (dirichletKernel' N (x - y) - (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)))
      volume (x - π) (x + π) := by
  conv => pattern ((f _) * _); rw [mul_sub]
  exact (intervalIntegrable_mul_dirichletKernel' hx hf).sub
    (intervalIntegrable_mul_dirichletKernel'_max hx hf)

lemma domain_reformulation {g : ℝ → ℂ} (hg : IntervalIntegrable g volume (-π) (3 * π)) {N : ℕ}
    {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * π)) :
    ∫ (y : ℝ) in x - π..x + π, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))
    = ∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo 0 1},
        g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)) := by
  calc _
    _ = ∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo 0 π}, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)) := by
      rw [annulus_real_eq (le_refl 0),
        setIntegral_union (by simp) measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
        ← setIntegral_union (Set.disjoint_of_subset_right Set.Ioo_subset_Ioc_self (by simp)) measurableSet_Ioo,
        intervalIntegral.integral_of_le (by linarith [pi_pos]), integral_Ioc_eq_integral_Ioo,
        sub_zero, add_zero, Set.Ioc_union_Ioo_eq_Ioo (by linarith [pi_pos]) (by linarith [pi_pos])]
      --TODO: Many similar goals => improve this further?
      · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [pi_pos])]
        apply (intervalIntegrable_mul_dirichletKernel'_max hx hg).mono_set
        rw [Set.uIcc_of_le (by linarith [pi_pos]), Set.uIcc_of_le (by linarith [pi_pos])]
        apply Set.Icc_subset_Icc_right (by linarith [pi_pos])
      all_goals
        rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [pi_pos])]
        apply (intervalIntegrable_mul_dirichletKernel'_max hx hg).mono_set
        rw [Set.uIcc_of_le (by linarith [pi_pos]), Set.uIcc_of_le (by linarith [pi_pos])]
      · apply Set.Icc_subset_Icc_left (by linarith [pi_pos])
      · apply Set.Icc_subset_Icc_right (by linarith [pi_pos])
      · apply Set.Icc_subset_Icc_left (by linarith [pi_pos])
    _ = ∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo 0 1}, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)) := by
      rw [←integral_indicator annulus_measurableSet, ←integral_indicator annulus_measurableSet]
      congr with y
      rw [Set.indicator_apply, Set.indicator_apply, Dirichlet_Hilbert_eq]
      split_ifs with h₀ h₁ h₂
      · trivial
      · dsimp at h₀ h₁
        rw [Real.dist_eq, Set.mem_Ioo] at h₀ h₁
        push_neg at h₁
        rw [k_of_one_le_abs (h₁ h₀.1)]
        simp
      · rw [k_of_one_le_abs]
        · simp
        dsimp at h₀ h₂
        rw [Real.dist_eq, Set.mem_Ioo] at h₀ h₂
        push_neg at h₀
        exact le_trans' (h₀ h₂.1) (by linarith [Real.two_le_pi])
      · trivial

lemma intervalIntegrable_mul_dirichletKernel'_specific {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * π))
    {f : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) (3 * π)) {N : ℕ} :
    IntegrableOn (fun y ↦ f y * ((max (1 - |x - y|) 0)
      * dirichletKernel' N (x - y))) {y | dist x y ∈ Set.Ioo 0 1} volume := by
  have : IntervalIntegrable (fun y ↦ f y * ((max (1 - |x - y|) 0)
      * dirichletKernel' N (x - y))) volume (x - π) (x + π) :=
    intervalIntegrable_mul_dirichletKernel'_max hx hf
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [pi_pos])] at this
  apply this.mono_set
  intro y hy
  rw [annulus_real_eq (by rfl)] at hy
  rcases hy with h | h <;> constructor <;> linarith [h.1, h.2, hx.1, hx.2, Real.two_le_pi]

attribute [gcongr] iSup_congr

lemma le_CarlesonOperatorReal {g : ℝ → ℂ} (hg : IntervalIntegrable g volume (-π) (3 * π)) {N : ℕ} {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * π)) :
    ‖∫ (y : ℝ) in x - π..x + π, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖ₑ
    ≤ T g x + T (conj ∘ g) x := by
  rw [domain_reformulation hg hx]
  set s : ℕ → Set ℝ := fun n ↦ {y | dist x y ∈ Set.Ioo (1 / (n + 2 : ℝ)) 1} with sdef
  have hs : {y | dist x y ∈ Set.Ioo 0 1} = ⋃ n, s n := by
    ext y
    constructor
    · intro hy
      rw [Set.mem_setOf_eq, Set.mem_Ioo] at hy
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / dist x y)
      rw [Set.mem_iUnion]
      use n
      rw [sdef, Set.mem_setOf_eq, one_div]
      refine ⟨?_, hy.2⟩
      rw [inv_lt_comm₀ (by linarith) hy.1, inv_eq_one_div]
      apply lt_trans hn
      linarith
    · intro hy
      simp only [Set.mem_iUnion] at hy
      rcases hy with ⟨n, hn⟩
      rw [sdef] at hn
      simp only [one_div, Set.mem_Ioo, Set.mem_setOf_eq] at hn
      refine ⟨lt_trans' hn.1 ?_, hn.2⟩
      norm_num
      linarith
  have : Tendsto (fun i => ∫ y in s i, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)))
          atTop (𝓝 (∫ y in ⋃ n, s n, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)))) := by
    apply tendsto_setIntegral_of_monotone
    · exact fun n ↦ annulus_measurableSet
    · intro n m nlem
      simp only [Set.le_eq_subset]
      intro y hy
      rw [sdef] at *
      simp only [one_div, Set.mem_Ioo, Set.mem_setOf_eq] at *
      refine ⟨lt_of_le_of_lt ?_ hy.1, hy.2⟩
      rw [inv_le_inv₀]
      on_goal 1 => norm_cast
      all_goals linarith
    · rw [← hs]
      --uses that dirichletKernel' is bounded
      exact intervalIntegrable_mul_dirichletKernel'_specific hx hg
  calc
    _ = ‖∫ y in ⋃ n, s n, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖ₑ := by congr
    _ ≤ ⨆ (i : ℕ), ↑‖∫ y in s i, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖ₑ := by
      apply le_iSup_of_tendsto
      exact Tendsto.enorm this
    _ ≤ ⨆ (r : ℝ) (_ : 0 < r) (_ : r < 1), ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖ₑ := by
      apply iSup_le
      intro n
      apply le_iSup_of_le (1 / (n + 2 : ℝ))
      apply le_iSup₂_of_le (by simp only [one_div, inv_pos]; linarith)
        (by rw [div_lt_iff₀] <;> linarith)
      rfl
    _ = ⨆ (r : ℝ) (_ : 0 < r) (_ : r < 1), ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-(Int.ofNat N) * x)) * K x y * exp (I * N * y) + conj (exp (I * (-(Int.ofNat N) * x)) * K x y * exp (I * (Int.ofNat N) * y)))‖ₑ := by
      gcongr
      congr with y
      congr
      rw [Dirichlet_Hilbert_eq]
      simp only [ofReal_sub, mul_comm, mul_neg, ← mul_assoc, k, map_mul, ← exp_conj, map_neg,
        conj_I, map_sub, conj_ofReal, map_natCast, neg_neg, map_div₀, map_one, Int.ofNat_eq_coe,
        Int.cast_natCast, K, ← exp_add, map_add]
      ring_nf
    _ ≤ ⨆ (n : ℤ) (r : ℝ) (_ : 0 < r) (_ : r < 1), ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-n * x)) * K x y * exp (I * n * y) + conj (exp (I * (-n * x)) * K x y * exp (I * n * y)))‖ₑ := by
      let F : ℤ → ENNReal := fun (n : ℤ) ↦ ⨆ (r : ℝ) (_ : 0 < r) (_ : r < 1), ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-n * x)) * K x y * exp (I * n * y) + conj (exp (I * (-n * x)) * K x y * exp (I * n * y)))‖ₑ
      exact le_iSup F ((Int.ofNat N))
    _ ≤ ⨆ (n : ℤ) (r : ℝ) (_ : 0 < r) (_ : r < 1),
        (‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * K x y * exp (I * n * y)‖ₑ
        + ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, (conj ∘ g) y * K x y * exp (I * n * y)‖ₑ) := by
      gcongr with n r rpos rle1
      norm_cast
      push_cast
      calc
        _ = ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-n * x)) * K x y * exp (I * n * y)) + g y * conj (exp (I * (-n * x)) * K x y * exp (I * n * y))‖ₑ := by
          congr with y
          rw [mul_add]
        _ = ‖(∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-n * x)) * K x y * exp (I * n * y)))
            + ∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * conj (exp (I * (-n * x)) * K x y * exp (I * n * y))‖ₑ := by
          congr
          -- Integrability follows from r > 0
          have measurable₁ : Measurable fun x_1 ↦ (I * (-↑n * ↑x)).exp * K x x_1 * (I * ↑n * ↑x_1).exp := by
            apply Measurable.mul (Measurable.mul _ Hilbert_kernel_measurable.of_uncurry_left) <;>
              fun_prop
          have boundedness₁ {y : ℝ} (h : r ≤ dist x y) : ‖(I * (-↑n * ↑x)).exp * K x y * (I * ↑n * ↑y).exp‖ ≤ (2 ^ (2 : ℝ) / (2 * r)) := by
            calc ‖(I * (-↑n * ↑x)).exp * K x y * (I * ↑n * ↑y).exp‖
              _ = ‖(I * (-↑n * ↑x)).exp‖ * ‖K x y‖ * ‖(I * ↑n * ↑y).exp‖ := by
                rw [norm_mul, norm_mul]
              _ ≤ 1 * (2 ^ (2 : ℝ) / (2 * |x - y|)) * 1 := by
                gcongr
                · rw [mul_comm]
                  norm_cast
                  rw [norm_exp_ofReal_mul_I]
                · exact Hilbert_kernel_bound
                · rw [mul_assoc, mul_comm]
                  norm_cast
                  rw [norm_exp_ofReal_mul_I]
              _ ≤ (2 ^ (2 : ℝ) / (2 * r)) := by
                rw [one_mul, mul_one, ← Real.dist_eq]
                gcongr
          have integrable₁ := integrable_annulus hx hg rpos.le rle1
          rw [integral_add]
          · conv => pattern ((g _) * _); rw [mul_comm]
            apply Integrable.bdd_mul' integrable₁ measurable₁.aestronglyMeasurable
            · rw [ae_restrict_iff' annulus_measurableSet]
              on_goal 1 => apply Eventually.of_forall
              exact fun _ hy ↦ boundedness₁ hy.1.le
          · conv => pattern ((g _) * _); rw [mul_comm]
            apply Integrable.bdd_mul' integrable₁ (by fun_prop)
            · rw [ae_restrict_iff' annulus_measurableSet]
              · apply Eventually.of_forall
                intro y hy
                rw [RCLike.norm_conj]
                exact boundedness₁ hy.1.le
        _ ≤   ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-n * x)) * K x y * exp (I * n * y))‖ₑ
            + ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * conj (exp (I * (-n * x)) * K x y * exp (I * n * y))‖ₑ := by
          apply enorm_add_le
        _ =   ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, exp (I * (-n * x)) * (g y * K x y * exp (I * n * y))‖ₑ
            + ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, exp (I * (-n * x)) * ((conj ∘ g) y * K x y * exp (I * n * y))‖ₑ := by
            congr 1
            · congr! 3 with y; ring
            · rw [← RCLike.enorm_conj, ← integral_conj]; congr! 3 with _ y; simp; ring
        _ =   ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * K x y * exp (I * n * y)‖ₑ
            + ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, (conj ∘ g) y * K x y * exp (I * n * y)‖ₑ := by
          congr 1 <;>
          rw [integral_const_mul, enorm_mul, show (-n * x : ℂ) = (-n * x : ℝ) by norm_cast,
            enorm_exp_I_mul_ofReal, one_mul]
    _ ≤ T g x + T (conj ∘ g) x := by
      simp_rw [carlesonOperatorReal]
      apply iSup₂_le
      intro n r
      apply iSup₂_le
      intro rpos rle1
      gcongr <;>
      · apply le_iSup₂_of_le n r
        apply le_iSup₂_of_le rpos rle1
        trivial

lemma partialFourierSum_bound {δ : ℝ} (hδ : 0 < δ) {g : ℝ → ℂ} (measurable_g : AEStronglyMeasurable g)
    (periodic_g : Function.Periodic g (2 * π))
    (bound_g : eLpNorm g 1 (volume.restrict (Set.Ico 0 (2 * π))) ≤ δ.toNNReal)
    {N : ℕ} {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * π)) :
    ‖S_ N g x‖ₑ ≤
    (T g x + T (conj ∘ g) x) / (ENNReal.ofReal (2 * π)) + ENNReal.ofReal (π * δ) := by
  have intervalIntegrable_g : IntervalIntegrable g volume (-π) (3 * π) := sorry --intervalIntegrable_of_bdd measurable_g bound_g
  have decomposition : S_ N g x
      = (  (∫ (y : ℝ) in (x - π)..(x + π),
              g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)))
         + (∫ (y : ℝ) in (x - π)..(x + π),
              g y * (dirichletKernel' N (x - y) - (max (1 - |x - y|) 0) * dirichletKernel' N (x - y))))
        / (2 * π) := by
    calc S_ N g x
      _ = (∫ (y : ℝ) in (0 : ℝ)..(2 * π), g y * dirichletKernel' N (x - y)) / (2 * π) := by
        rw [partialFourierSum_eq_conv_dirichletKernel' (intervalIntegrable_g.mono_set _)]
        · ring
        rw [Set.uIcc_of_le, Set.uIcc_of_le]
        on_goal 1 => apply Set.Icc_subset_Icc
        all_goals linarith [pi_pos]
      _ = (∫ (y : ℝ) in (x - π)..(x + π), g y * dirichletKernel' N (x - y)) / (2 * π) := by
        --Shift domain of integration using periodicity
        congr 1
        rw [← zero_add (2 * π), Function.Periodic.intervalIntegral_add_eq _ 0 (x - π)]
        · congr 1
          ring
        exact (periodic_g.mul (dirichletKernel'_periodic.const_sub x))
      _ = (  (∫ (y : ℝ) in (x - π)..(x + π), g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)))
           + (∫ (y : ℝ) in (x - π)..(x + π), g y * (dirichletKernel' N (x - y) - (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)))) / (2 * π) := by
        --Split into two parts
        rw [← intervalIntegral.integral_add (intervalIntegrable_mul_dirichletKernel'_max hx intervalIntegrable_g) (intervalIntegrable_mul_dirichletKernel'_max' hx intervalIntegrable_g)]
        congr with y
        ring

  calc
    _ ≤ (‖∫ y in (x - π)..(x + π), g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖ₑ
        + ‖∫ y in (x - π)..(x + π), g y * (dirichletKernel' N (x - y) - (max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖ₑ) / ENNReal.ofReal (2 * π) := by
      rw [decomposition, div_eq_mul_inv, enorm_mul, enorm_inv (by simp [pi_pos.ne']),
        ← div_eq_mul_inv]
      norm_cast; gcongr
      · apply enorm_add_le
      · rw [Real.enorm_eq_ofReal Real.two_pi_pos.le]
    _ ≤ (T g x + T (⇑conj ∘ g) x + ENNReal.ofReal (π * δ * (2 * π))) / ENNReal.ofReal (2 * π) := by
      gcongr
      · apply le_CarlesonOperatorReal intervalIntegrable_g hx
      · rw [ENNReal.ofReal]
        norm_cast
        apply NNReal.le_toNNReal_of_coe_le
        rw [coe_nnnorm]

        calc ‖∫ (y : ℝ) in x - π..x + π, g y * (dirichletKernel' N (x - y) - (max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖
          _ ≤ (δ * π) * |(x + π) - (x - π)| := by
            /-
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro y hy
            rw [Set.uIoc_of_le (by linarith [pi_pos])] at hy
            rw [norm_mul]
            gcongr
            · apply bound_g
            · rw [Dirichlet_Hilbert_eq]
              apply Dirichlet_Hilbert_diff
              constructor <;> linarith [hy.1, hy.2]
            -/
            sorry
          _ = π * δ * (2 * π) := by
            simp only [add_sub_sub_cancel]
            rw [←two_mul, _root_.abs_of_nonneg Real.two_pi_pos.le]
            ring
    _ = (T g x + T (conj ∘ g) x) / ENNReal.ofReal (2 * π) + ENNReal.ofReal (π * δ) := by
      rw [ENNReal.add_div]
      congr
      rw [← ENNReal.ofReal_div_of_pos Real.two_pi_pos, mul_div_assoc, div_self Real.two_pi_pos.ne', mul_one]

end

set_option linter.flexible false in
lemma rcarleson_exceptional_set_estimate {f : ℝ → ℂ}
    {p : NNReal} (hp : p ∈ Set.Ioo 1 2) (hf : MemLp f p volume)
    {E : Set ℝ} (measurableSetE : MeasurableSet E) {ε : ENNReal} (hE : ∀ x ∈ E, ε ≤ T f x) :
      ε ^ p.toReal * volume E ≤ ((C_carleson_hasStrongType 4 p) * eLpNorm f p) ^ p.toReal := by
  calc ε ^ p.toReal * volume E
    _ = ∫⁻ _ in E, ε ^ p.toReal := by
      symm
      apply setLIntegral_const
    _ ≤ ∫⁻ x in E, T f x ^ p.toReal := by
      apply setLIntegral_mono' measurableSetE
      intro x hx
      gcongr
      exact hE x hx
    _ ≤ ∫⁻ x, T f x ^ p.toReal := by
      apply setLIntegral_le_lintegral
    _ = eLpNorm (T f) p ^ p.toReal := Eq.symm (eLpNorm_nnreal_pow_eq_lintegral (zero_lt_one.trans hp.1).ne.symm)
    _ ≤ _ := by
      gcongr
      apply rcarleson' hp hf


lemma rcarleson_exceptional_set_estimate_specific {δ : NNReal} (δpos : 0 < δ) {f : ℝ → ℂ} (hmf : AEStronglyMeasurable f)
  {p : NNReal} (hp : p ∈ Set.Ioo 1 2)
  (hf : eLpNorm f p (volume.restrict (Set.Ico 0 (2 * π))) ≤ δ) (f_periodic : f.Periodic (2 * π))
    {E : Set ℝ} (measurableSetE : MeasurableSet E) (E_subset : E ⊆ Set.Icc 0 (2 * π)) {ε : ENNReal} (hE : ∀ x ∈ E, ε ≤ T f x) :
      ε ^ p.toReal * volume E ≤ ((C_carleson_hasStrongType 4 p) * (2 * ENNReal.ofReal δ)) ^ p.toReal := by
  --rw [ENNReal.ofReal_mul (by have := @C10_0_1_pos 4 2 one_lt_two; positivity),
  --  ← ENNReal.ofReal_rpow_of_pos (by positivity)]
  /-
  set F := (Set.Ioo (0 - 1) (2 * π + 1))
  set h := F.indicator f with hdef
  have hh : ∀ x, ‖h x‖ ≤ δ * F.indicator 1 x := by
    intro x
    rw [hdef, norm_indicator_eq_indicator_norm, Set.indicator, Set.indicator]
    split_ifs with hx
    · simp only [Pi.one_apply, mul_one]; exact hf x
    · simp
  -/
  --rw [← carlesonOperatorReal_eq_of_restrict_interval (E_subset hx)]
  apply le_trans (rcarleson_exceptional_set_estimate (f := (Set.Ioo (0 - 1) (2 * π + 1)).indicator f) hp _ measurableSetE _)
  · gcongr
    sorry --get this from hf and periodicity of f
  · use (hmf.indicator measurableSet_Ioo)
    sorry --follows from the last sorry
  · intro x hx
    rw [← carlesonOperatorReal_eq_of_restrict_interval (E_subset hx)]
    exact hE x hx

/-
def C_control_approximation_effect (ε : ℝ) := (C10_0_1 4 2 * (8 / (π * ε)) ^ (2 : ℝ)⁻¹) + π

/-
lemma lt_C_control_approximation_effect {ε : ℝ} (εpos : 0 < ε) : π < C_control_approximation_effect ε := by
  rw [C_control_approximation_effect]
  apply lt_add_of_pos_of_le _ (by rfl)
  have := @C10_0_1_pos 4 2 (by norm_num)
  positivity
-/

lemma C_control_approximation_effect_pos {ε : ℝ} (εpos : 0 < ε) : 0 < C_control_approximation_effect ε :=
  sorry
  --lt_trans' (lt_C_control_approximation_effect εpos) pi_pos


lemma C_control_approximation_effect_eq {ε : ℝ} {δ : ℝ} (ε_nonneg : 0 ≤ ε) :
    C_control_approximation_effect ε * δ =
      ((δ * C10_0_1 4 2 * (4 * π) ^ (2 : ℝ)⁻¹ * (2 / ε) ^ (2 : ℝ)⁻¹) / π) + π * δ := by
  symm
  rw [C_control_approximation_effect, mul_comm, mul_div_right_comm, mul_comm δ, mul_assoc,
    mul_comm δ, ← mul_assoc, ← mul_assoc, ← add_mul, mul_comm _ (C10_0_1 4 2 : ℝ), mul_assoc]
  congr
  rw [Real.div_rpow, Real.div_rpow _ (mul_nonneg _ _), Real.mul_rpow, Real.mul_rpow]
  all_goals
    ring_nf
    try rw [mul_assoc, mul_comm (2 ^ _), mul_assoc, mul_assoc, mul_assoc, mul_comm (4 ^ _), ← mul_assoc π⁻¹,
      ← Real.rpow_neg_one π, ← Real.rpow_add, mul_comm (π ^ _), ← mul_assoc (2 ^ _), ← Real.mul_rpow]
  on_goal 1 =>
    field_simp
    ring_nf
    calc _
      _ = (π ^ (1 / (2 : ℝ))) ^ 2 * 2 ^ (1 / (2 : ℝ)) * (ε ^ (1 / (2 : ℝ)))⁻¹ * 2 := by ring
      _ = π * 2 ^ (1 / (2 : ℝ)) * (ε ^ (1 / (2 : ℝ)))⁻¹ * 2 := by
        -- Golfing of this proof welcome!
        congr
        rw [← Real.sqrt_eq_rpow π, Real.sq_sqrt', max_eq_left_iff]
        positivity
      _ = π * (2 ^ (1 / (2 : ℝ)) * 2) * (ε ^ (1 / (2 : ℝ)))⁻¹ := by ring
      _ = π * 8 ^ (1 / (2 : ℝ)) * (ε ^ (1 / (2 : ℝ)))⁻¹  := by
        congr
        -- Golfing of this computation is very welcome!
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
        have : Real.sqrt 4 = 2 := Real.sqrt_eq_cases.mpr <| Or.inl ⟨by norm_num, by positivity⟩
        nth_rw 2 [← this]
        rw [← Real.sqrt_mul (by positivity) 4]
        norm_num
      _ = (ε ^ (1 / (2 : ℝ)))⁻¹ * π * 8 ^ (1 / (2 : ℝ)) := by ring
  all_goals linarith [pi_pos]
-/

def C_control_approximation_effect (ε p : NNReal) : NNReal := (C_carleson_hasStrongType 4 p)⁻¹ * (ε / 2) ^ ((1 + p) / p).toReal

lemma C_control_approximation_effect_pos {ε p : NNReal} (εpos : 0 < ε) : 0 < C_control_approximation_effect ε p := by
  unfold C_control_approximation_effect
  apply mul_pos
  · apply inv_pos_of_pos
    apply C_carleson_hasStrongType_pos
  apply NNReal.rpow_pos
  simpa

/- This is Lemma 11.6.4 (partial Fourier sums of small) in the blueprint.-/
lemma control_approximation_effect {ε : ℝ} (εpos : 0 < ε) --{δ : ℝ} (hδ : 0 < δ)
    {h : ℝ → ℂ} (h_measurable : AEStronglyMeasurable h)
    (h_periodic : h.Periodic (2 * π))
    {p : NNReal} (hp : p ∈ Set.Ioo 1 2)
    (h_bound : eLpNorm h p (volume.restrict (Set.Ico 0 (2 * π))) ≤ C_control_approximation_effect ε.toNNReal p) :
    ∃ E ⊆ Set.Icc 0 (2 * π), MeasurableSet E ∧ volume.real E ≤ ε ∧ ∀ x ∈ Set.Icc 0 (2 * π) \ E,
      ∀ N, ‖S_ N h x‖ ≤ ε / π + π * C_control_approximation_effect ε.toNNReal p := by
  set δ := C_control_approximation_effect ε.toNNReal p with δdef
  have hδ : 0 < δ := by
    apply C_control_approximation_effect_pos
    simpa
  set ε' := ε / π + π * δ with ε'def
  have ε_eq : ε = (ε' - π * δ) * π := by
    rw [ε'def]
    simp
  set E := {x ∈ Set.Icc 0 (2 * π) | ∃ N, ε' < ‖S_ N h x‖} with Edef
  have E_eq: E = Set.Icc 0 (2 * π) ∩ ⋃ N : ℕ, {x | ε' < ‖S_ N h x‖} := by
      rw [Edef]
      ext x
      simp
  have measurableSetE : MeasurableSet E := by
    rw [E_eq]
    apply measurableSet_Icc.inter (MeasurableSet.iUnion _)
    intro N
    apply measurableSet_lt measurable_const (Measurable.norm partialFourierSum_uniformContinuous.continuous.measurable)
  have Esubset : E ⊆ Set.Icc 0 (2 * π) := fun x hx ↦ by simpa using hx.1
  use E, Esubset, measurableSetE
  --Change order of proofs to start with the simple part
  rw [and_comm]
  constructor
  · rw [Edef]
    simp only [Set.mem_Icc, Set.mem_diff, Set.mem_setOf_eq, not_and, not_exists, not_lt, and_imp]
    exact fun x x_nonneg x_le_two_pi h ↦ h x_nonneg x_le_two_pi
  -- This is needed later but better fits in here.
  have conj_h_bound : eLpNorm (star ∘ h) p (volume.restrict (Set.Ico 0 (2 * π))) ≤ δ := by
    /-
    simp
    intro x
    simp only [RCLike.star_def, Function.comp_apply, RingHomIsometric.norm_map]
    exact h_bound x
    -/
    sorry
  have conj_h_periodic : (star ∘ h).Periodic (2 * π) := by
    sorry
  have locallyInt_h : LocallyIntegrable h := sorry --TODO: get this from h_periodic and h_bound
  have locallyInt_conj_h : LocallyIntegrable (star ∘ h) := sorry --TODO: get this from h_periodic and h_bound
  have le_operator_add : ∀ x ∈ E, ENNReal.ofReal ((ε' - π * δ) * (2 * π)) ≤ T h x + T (conj ∘ h) x := by
    intro x hx
    obtain ⟨xIcc, N, hN⟩ := hx
    have : ENNReal.ofReal (π * δ * (2 * π)) ≠ ⊤ := by finiteness
    rw [← (ENNReal.add_le_add_iff_right this)]
    calc ENNReal.ofReal ((ε' - π * δ) * (2 * π)) + ENNReal.ofReal (π * δ * (2 * π))
      _ = ENNReal.ofReal (2 * π) * ENNReal.ofReal ε' := by
        rw [← ENNReal.ofReal_add, ← ENNReal.ofReal_mul Real.two_pi_pos.le]
        · ring_nf
        · rw [ε'def, add_sub_cancel_right]
          positivity
        · positivity
      _ ≤ ENNReal.ofReal (2 * π) * ‖S_ N h x‖ₑ := by rw [← ofReal_norm_eq_enorm]; gcongr
      _ ≤ ENNReal.ofReal (2 * π) * ((T h x + T (conj ∘ h) x) / (ENNReal.ofReal (2 * π)) + ENNReal.ofReal (π * δ)) := by
        gcongr
        apply partialFourierSum_bound hδ h_measurable h_periodic _ xIcc
        --TODO: add lemma for this
        sorry --TODO : get this from h_bound
      _ = (T h x + T (conj ∘ h) x) + ENNReal.ofReal (π * δ * (2 * π)) := by
        rw [mul_add]
        congr
        · rw [ENNReal.mul_div_cancel (by simp [pi_pos]) (by finiteness)]
        · rw [← ENNReal.ofReal_mul (by positivity)]
          ring_nf
  have Evolume : volume E < ⊤ := by
    calc volume E
      _ ≤ volume (Set.Icc 0 (2 * π)) := by
        apply measure_mono
        rw [E_eq]
        apply Set.inter_subset_left
      _ = ENNReal.ofReal (2 * π) := by
        rw [Real.volume_Icc, sub_zero]
      _ < ⊤ := ENNReal.ofReal_lt_top
  obtain ⟨E', E'subset, measurableSetE', E'measure, h⟩ :=
    ENNReal.le_on_subset volume measurableSetE (carlesonOperatorReal_measurable' h_measurable locallyInt_h)
      (carlesonOperatorReal_measurable' (continuous_star.measurable.comp_aemeasurable h_measurable.aemeasurable).aestronglyMeasurable locallyInt_conj_h)
      le_operator_add
  have E'volume : volume E' < ⊤ := lt_of_le_of_lt (measure_mono E'subset) Evolume
  have aux := @C10_0_1_pos 4 2 one_lt_two
  rw [volume.real_def]
  apply ENNReal.toReal_le_of_le_ofReal εpos.le
  calc volume E
    _ ≤ 2 * volume E' := E'measure
    _ = 2 / ε.toNNReal ^ p.toReal * (ε.toNNReal ^ p.toReal * volume E') := by
      rw [← mul_assoc, ENNReal.div_mul_cancel]
      · apply (ENNReal.rpow_pos_of_nonneg _ _).ne.symm
        simpa
        simp
      · apply ENNReal.rpow_ne_top' (by simpa) (by simp)
    _ ≤ 2 / ε.toNNReal ^ p.toReal * (((C_carleson_hasStrongType 4 p) * (2 * ENNReal.ofReal δ)) ^ p.toReal) := by
      gcongr
      rcases h with hE' | hE'
      ·
        apply rcarleson_exceptional_set_estimate_specific hδ h_measurable hp h_bound h_periodic measurableSetE' (E'subset.trans Esubset)
        convert hE'
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_div_of_pos (by simp), ε_eq, ← ENNReal.ofReal]
        congr 1
        ring
      · apply rcarleson_exceptional_set_estimate_specific hδ (by fun_prop) hp conj_h_bound conj_h_periodic measurableSetE' (E'subset.trans Esubset)
        convert hE'
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_div_of_pos (by simp), ε_eq, ← ENNReal.ofReal]
        congr 1
        ring
    _ = ε.toNNReal := by
      --We have chosen δ such that this works.
      rw [δdef]
      unfold C_control_approximation_effect
      rw [← mul_assoc, mul_comm _ 2, mul_assoc, ENNReal.ofReal]
      norm_cast
      rw [Real.toNNReal_coe, ← mul_assoc (C_carleson_hasStrongType 4 p), mul_inv_cancel₀ C_carleson_hasStrongType_pos.ne.symm, one_mul]
      rw [ENNReal.coe_mul, ENNReal.coe_mul_rpow]
      push_cast
      rw [← ENNReal.coe_rpow_of_nonneg _ (by simp), ← ENNReal.coe_rpow_of_nonneg _ (by simp),
        ← NNReal.rpow_mul, div_mul_cancel₀ _ (by simp only [ne_eq, NNReal.coe_eq_zero]; intro p_zero; rw [p_zero] at hp; simp at hp),
        NNReal.rpow_add (by simpa), NNReal.rpow_one, NNReal.div_rpow]
      push_cast
      rw [ENNReal.coe_div (by simp), ENNReal.coe_div (by simp)]
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      simp only [ENNReal.coe_ofNat]
      ring_nf
      rw [mul_comm (_⁻¹ * 2 ^ _), mul_comm, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc,
        ENNReal.mul_inv_cancel (by simp) (by simp), one_mul,
        mul_comm, ← mul_assoc, ← mul_assoc, ← mul_assoc, ENNReal.mul_inv_cancel _ (by simp), one_mul,
        mul_comm, ← mul_assoc, ENNReal.coe_rpow_of_nonneg _ (by simp), ENNReal.coe_ofNat,
        ENNReal.inv_mul_cancel (ENNReal.rpow_pos zero_lt_two (by simp)).ne.symm
          (ENNReal.rpow_ne_top' (by simp) (by simp)), one_mul]
      · simp only [ne_eq, ENNReal.coe_eq_zero, NNReal.rpow_eq_zero_iff, Real.toNNReal_eq_zero,
        NNReal.coe_eq_zero, not_and, Decidable.not_not]
        intro h
        linarith
end
