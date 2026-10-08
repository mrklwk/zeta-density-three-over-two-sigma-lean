module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.DensityTheorem
public import MathCollab.Density.DetectorAdmissibility
public import MathCollab.Density.DetectorTaylorFamily
public import MathCollab.Density.DetectorIdentity
public import MathCollab.Density.DetectorGamma
public import MathCollab.Density.LocalZeroCount
public import MathCollab.Density.DetectorParameters
public import MathCollab.Density.LargeValues
public import MathCollab.Density.BootstrapAbsorption
public import MathCollab.Density.AllFrequency
public import MathCollab.Density.FixedBandError
public import MathCollab.Density.CompletePairs
public import MathCollab.Density.Reflection

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option pp.proofs false
open MathCollab.Density

#print norm_gmReflectionIntegral_le_left
#print norm_gmReflectionIntegral_le_right
#print norm_gmReflectionIntegral_le_length_div
#print norm_gmReflectionIntegral_le_six_div_sqrt
#print norm_oscillatoryIntegral_le
#print uniform_offBand_modeIntegral
#print uniform_discarded_modes
#print uniform_zero_modes
#print Transforms.scaled_modulated_poisson
#print Transforms.mellin_inversion_line_one
#print Transforms.norm_mellin_line_one_le_seminorm_div_scaledPower
#print integrable_mellin_line_one
#print cutoff_mellin_inversion
#print hKernel_poisson
#print completePairEnergy_coefficient_domination
#print uniform_fixedBand_and_diagonal_error

-- Oscillatory
#print axioms MathCollab.Density.hasDerivAt_gmReflectionPrimitive
#print axioms MathCollab.Density.hasDerivAt_gmReflectionRatio
#print axioms MathCollab.Density.hasDerivAt_gmReflectionRatioReal
#print axioms MathCollab.Density.gmReflectionRatio_mul_primitiveDeriv
#print axioms MathCollab.Density.gmReflectionIntegral_eq_parts
#print axioms MathCollab.Density.norm_gmReflectionPrimitive
#print axioms MathCollab.Density.norm_gmReflectionRatio
#print axioms MathCollab.Density.norm_gmReflectionIntegrand
#print axioms MathCollab.Density.norm_gmReflectionIntegral_le_endpoint_variation
#print axioms MathCollab.Density.norm_gmReflectionIntegral_le_left
#print axioms MathCollab.Density.norm_gmReflectionIntegral_le_right
#print axioms MathCollab.Density.norm_gmReflectionIntegral_le_length_div
#print axioms MathCollab.Density.intervalIntegrable_gmReflectionIntegrand

-- AllFrequency
#print axioms MathCollab.Density.gmReflectionIntegral_add
#print axioms MathCollab.Density.norm_gmReflectionIntegral_le_six_div_sqrt
#print axioms MathCollab.Density.norm_oscillatoryIntegral_le

-- UniformIBP
#print axioms MathCollab.Density.phaseQuotient_contDiffAt
#print axioms MathCollab.Density.ibpAmplitude_contDiffAt
#print axioms MathCollab.Density.ibpAmplitude_tsupport_subset
#print axioms MathCollab.Density.offBandParameters_isCompact
#print axioms MathCollab.Density.ibpAmplitude_uniform_bound
#print axioms MathCollab.Density.offBand_denominator_gap
#print axioms MathCollab.Density.normalized_offBand_mem
#print axioms MathCollab.Density.norm_logOscillation
#print axioms MathCollab.Density.hasDerivAt_logOscillation
#print axioms MathCollab.Density.ibpAmplitude_contDiffAt_slice
#print axioms MathCollab.Density.phaseQuotient_contDiffAt_slice
#print axioms MathCollab.Density.offBandParameters_ne
#print axioms MathCollab.Density.ibpIntegral_recurrence
#print axioms MathCollab.Density.ibpIntegral_norm_recurrence
#print axioms MathCollab.Density.uniform_normalized_decay
#print axioms MathCollab.Density.uniform_offBand_decay

-- ReflectionDefinitions
#print axioms MathCollab.Density.modeIntegral_eq_interval
#print axioms MathCollab.Density.uniform_offBand_modeIntegral
#print axioms MathCollab.Density.outsideBand_scaled
#print axioms MathCollab.Density.summable_integerPowerMajorant
#print axioms MathCollab.Density.uniform_discarded_modes
#print axioms MathCollab.Density.zero_normalized_mem
#print axioms MathCollab.Density.uniform_zero_modeIntegral
#print axioms MathCollab.Density.uniform_zero_modes

-- AnalyticTransforms
#print axioms MathCollab.Density.Transforms.schwartz_poisson_at_zero
#print axioms MathCollab.Density.Transforms.fourier_scaled_modulated
#print axioms MathCollab.Density.Transforms.scaled_modulated_poisson
#print axioms MathCollab.Density.Transforms.mellinConvergent_one_of_compactSupport
#print axioms MathCollab.Density.Transforms.verticalIntegrable_mellin_of_quadratic_decay
#print axioms MathCollab.Density.Transforms.mellin_inversion_line_one
#print axioms MathCollab.Density.Transforms.mellinLogLift_contDiff
#print axioms MathCollab.Density.Transforms.mellinLogLift_hasCompactSupport
#print axioms MathCollab.Density.Transforms.mellin_line_one_eq_fourier_logLift
#print axioms MathCollab.Density.Transforms.scaledPower_mul_norm_mellin_line_one_le_seminorm
#print axioms MathCollab.Density.Transforms.norm_mellin_line_one_le_seminorm_div_scaledPower

-- CutoffTransforms
#print axioms MathCollab.Density.compactSupport_of_cutoff_support
#print axioms MathCollab.Density.logCutoff_hasCompactSupport
#print axioms MathCollab.Density.logCutoff_contDiff
#print axioms MathCollab.Density.fourier_logCutoff
#print axioms MathCollab.Density.scaled_log_poisson
#print axioms MathCollab.Density.integrable_mellin_line_one
#print axioms MathCollab.Density.cutoff_mellin_inversion
#print axioms MathCollab.Density.summable_modeIntegral
#print axioms MathCollab.Density.summable_nat_logCutoff
#print axioms MathCollab.Density.tsum_int_logCutoff_eq_nat
#print axioms MathCollab.Density.poisson_nonzero_modes
#print axioms MathCollab.Density.ReflectionCutoff.complex_smooth
#print axioms MathCollab.Density.ReflectionCutoff.complex_support
#print axioms MathCollab.Density.modeIntegral_zero_frequency
#print axioms MathCollab.Density.hKernel_poisson

-- CompletePairs
#print axioms MathCollab.Density.complete_pair_expansion
#print axioms MathCollab.Density.complete_pair_coefficient_domination
#print axioms MathCollab.Density.dirichletPhase_sub
#print axioms MathCollab.Density.completePairEnergy_coefficient_domination

-- FixedBandError
#print axioms MathCollab.Density.mem_reflectionBand
#print axioms MathCollab.Density.tsum_retainedMode_eq_finite
#print axioms MathCollab.Density.summable_retainedMode
#print axioms MathCollab.Density.summable_discardedMode
#print axioms MathCollab.Density.nonzeroMode_eq_retained_add_discarded
#print axioms MathCollab.Density.hKernel_sub_bandContribution
#print axioms MathCollab.Density.uniform_fixedBand_and_diagonal_error

-- Completed reflection contract and analytic interchanges
#print scaled_mellin_phase
#print integrable_mellin_kernel
#print mellin_kernel_integral_swap
#print band_modeIntegral_mellin
#print mellinLine_eq_cutoffIntegral
#print dirichletPhase_eq_cpow
#print norm_reflectionKernel_sq_le
#print norm_bandContribution_sq_le
#print mem_reflectionBlocks_iff
#print reflectionBlocks_card_le
#print reflectionBlock_scale_bounds
#print pair_mem_localSet
#print tsum_card_localSet
#print localSet_pair_distance
#print close_pairs_block_le_local
#print positiveShell_bandContribution_le
#print uniform_reflection

-- MellinKernel
#print axioms MathCollab.Density.norm_dirichletPhase
#print axioms MathCollab.Density.norm_oscillatoryKernel
#print axioms MathCollab.Density.mellin_cpow_eq
#print axioms MathCollab.Density.cutoff_mellin_inversion_phase
#print axioms MathCollab.Density.scaled_mellin_phase
#print axioms MathCollab.Density.integrable_mellin_kernel
#print axioms MathCollab.Density.integrable_mellin_kernel_slice
#print axioms MathCollab.Density.mellin_kernel_integral_swap
#print axioms MathCollab.Density.modeIntegral_scaled
#print axioms MathCollab.Density.scaled_cutoff_mellin
#print axioms MathCollab.Density.modeIntegral_mellin_common
#print axioms MathCollab.Density.reflection_interval_pos
#print axioms MathCollab.Density.reflection_interval_order
#print axioms MathCollab.Density.band_modeIntegral_mellin
#print axioms MathCollab.Density.integrable_reflection_kernel
#print axioms MathCollab.Density.norm_reflectionKernel_sq_le
#print axioms MathCollab.Density.measurable_reflectionKernel
#print axioms MathCollab.Density.mellinLine_eq_cutoffIntegral
#print axioms MathCollab.Density.dirichletPhase_eq_cpow

-- WeightedSquare
#print axioms MathCollab.Density.weighted_integral_sq_le
#print axioms MathCollab.Density.integrable_weighted_norm_sq
#print axioms MathCollab.Density.norm_integral_mul_sq_le

-- BandEnergy
#print axioms MathCollab.Density.mellinMass_nonneg
#print axioms MathCollab.Density.measurable_bandPhaseSum
#print axioms MathCollab.Density.norm_bandPhaseSum_le
#print axioms MathCollab.Density.bandContribution_mellin
#print axioms MathCollab.Density.norm_bandContribution_sq_le

-- DyadicBlocks
#print axioms MathCollab.Density.mem_reflectionNatBand
#print axioms MathCollab.Density.sum_reflectionBand_eq_nat
#print axioms MathCollab.Density.log2_block_bounds
#print axioms MathCollab.Density.mem_dyadicExponents
#print axioms MathCollab.Density.dyadicExponent_scale_bounds
#print axioms MathCollab.Density.dyadicExponents_card_le
#print axioms MathCollab.Density.reflectionBlocks_card_le
#print axioms MathCollab.Density.reflectionBlock_scale_bounds
#print axioms MathCollab.Density.log2_eq_iff_block
#print axioms MathCollab.Density.natBand_filter_log2
#print axioms MathCollab.Density.dirichletPhase_add
#print axioms MathCollab.Density.dirichletPhase_mul
#print axioms MathCollab.Density.norm_blockCoefficient_le
#print axioms MathCollab.Density.fiber_phaseSum_eq
#print axioms MathCollab.Density.sum_reflectionBlocks
#print axioms MathCollab.Density.mem_reflectionBlocks_iff

-- LocalCover
#print axioms MathCollab.Density.mem_localSet_iff_floor
#print axioms MathCollab.Density.mem_localIndices_iff
#print axioms MathCollab.Density.localSet_eq_empty_of_notMem
#print axioms MathCollab.Density.pair_mem_localSet
#print axioms MathCollab.Density.sum_pairs_indicator
#print axioms MathCollab.Density.close_pairs_le_local_pairs
#print axioms MathCollab.Density.tsum_completePairEnergy_localSet
#print axioms MathCollab.Density.localIndices_filter_point
#print axioms MathCollab.Density.sum_card_localSet
#print axioms MathCollab.Density.tsum_card_localSet
#print axioms MathCollab.Density.localSet_pair_distance

-- ReflectionAssembly
#print axioms MathCollab.Density.norm_bandPhaseSum_sq_le_blocks
#print axioms MathCollab.Density.complete_pairs_block_le
#print axioms MathCollab.Density.close_pairs_block_le_local
#print axioms MathCollab.Density.localReflectionEnergy_nonneg
#print axioms MathCollab.Density.positiveShell_bandPhaseSum_le
#print axioms MathCollab.Density.positiveShell_integral
#print axioms MathCollab.Density.integrable_positiveShell
#print axioms MathCollab.Density.positiveShell_const_mul
#print axioms MathCollab.Density.positiveShell_mono
#print axioms MathCollab.Density.positiveShell_bandContribution_le

-- Reflection
#print axioms MathCollab.Density.dirichletPhase_neg
#print axioms MathCollab.Density.hKernel_neg
#print axioms MathCollab.Density.norm_hKernel_neg
#print axioms MathCollab.Density.shellEnergy_eq_twice_positive
#print axioms MathCollab.Density.positiveShell_add
#print axioms MathCollab.Density.positiveShell_const_le
#print axioms MathCollab.Density.error_power_eq
#print axioms MathCollab.Density.hKernel_sq_le_band_error
#print axioms MathCollab.Density.uniform_reflection

-- Step 4 verified comparison and absorption core.
#check MathCollab.Density.ComparisonCutoff
#check MathCollab.Density.LargeValueData
#check MathCollab.Density.detectingPolynomial
#check MathCollab.Density.divisorMaximum
#check MathCollab.Density.bootstrapScalar
#check MathCollab.Density.bootstrapValues
#check MathCollab.Density.bootstrapBound
#check MathCollab.Density.uniform_comparison
#check MathCollab.Density.product_grouping_cutoff
#check MathCollab.Density.uniform_reflection_application
#check MathCollab.Density.reflection_recursive_scale
#check MathCollab.Density.localSet_localDiameter_le
#check MathCollab.Density.bootstrapValues_bddAbove
#check MathCollab.Density.bootstrap_one_shell
#check MathCollab.Density.bootstrap_preabsorption
#check MathCollab.Density.bootstrap_absorption_inequality
#check MathCollab.Density.bootstrap_absorbed
#print axioms MathCollab.Density.bootstrap_preabsorption
#print axioms MathCollab.Density.bootstrap_absorption_inequality
#print axioms MathCollab.Density.bootstrap_absorbed
#print axioms MathCollab.Density.LargeValueData.scalar_lower
#print axioms MathCollab.Density.LargeValueData.scalar_pos
#print axioms MathCollab.Density.mem_bootstrapFamily
#print axioms MathCollab.Density.bootstrapFamily_nonempty
#print axioms MathCollab.Density.localSet_subset_original
#print axioms MathCollab.Density.bootstrapFamily_local_closed
#print axioms MathCollab.Density.LargeValueData.normalization_lower
#print axioms MathCollab.Density.comparisonConstant_nonneg
#print axioms MathCollab.Density.local_comparison_from_supremum
#print axioms MathCollab.Density.reflectionBlock_scaled_square
#print axioms MathCollab.Density.localReflectionEnergy_from_supremum
#print axioms MathCollab.Density.bootstrap_one_shell
#print axioms MathCollab.Density.shellIndex_bounds
#print axioms MathCollab.Density.exists_shellIndex
#print axioms MathCollab.Density.shellIndices_sum_le
#print axioms MathCollab.Density.shellIndices_card_le_log
#print axioms MathCollab.Density.shellIndices_card_le_diameter
#print axioms MathCollab.Density.shellEnergy_nonneg
#print axioms MathCollab.Density.kernelEnergy_le_dyadic_shells
#print axioms MathCollab.Density.crude_kernel_bound
#print axioms MathCollab.Density.bootstrapValues_nonempty
#print axioms MathCollab.Density.bootstrapValues_bddAbove
#print axioms MathCollab.Density.bootstrapBound_nonneg
#print axioms MathCollab.Density.kernelEnergy_le_bootstrapBound
#print axioms MathCollab.Density.comparison_extension_bound
#print axioms MathCollab.Density.dyadicPolynomial_norm_le
#print axioms MathCollab.Density.detecting_pair_division_bound
#print axioms MathCollab.Density.bootstrapScalar_nonneg
#print axioms MathCollab.Density.comparison_continuous_bound
#print axioms MathCollab.Density.comparison_remainder_bound
#print axioms MathCollab.Density.uniform_comparison
#print axioms MathCollab.Density.completePairEnergy_gram
#print axioms MathCollab.Density.completePairEnergy_diagonal_lower
#print axioms MathCollab.Density.norm_sum_mul_sq_le
#print axioms MathCollab.Density.detecting_insertion_bound
#print axioms MathCollab.Density.normalized_product_phase
#print axioms MathCollab.Density.cutoffIntegral_quadratic_decay
#print axioms MathCollab.Density.weighted_mode_expansion
#print axioms MathCollab.Density.cutoff_finite_sum
#print axioms MathCollab.Density.comparisonExtension_nonneg
#print axioms MathCollab.Density.comparisonExtension_identity
#print axioms MathCollab.Density.detectingPolynomial_norm_le
#print axioms MathCollab.Density.LargeValueData.height_le_length
#print axioms MathCollab.Density.kernelEnergy_nonneg
#print axioms MathCollab.Density.oneSeparated_subset
#print axioms MathCollab.Density.intervalSpan_nonneg
#print axioms MathCollab.Density.localDiameter_ge_one
#print axioms MathCollab.Density.abs_sub_le_intervalSpan
#print axioms MathCollab.Density.intervalSpan_le_of_forall
#print axioms MathCollab.Density.separated_floor_shift_injOn
#print axioms MathCollab.Density.separated_card_le_localDiameter
#print axioms MathCollab.Density.summable_separation_majorant
#print axioms MathCollab.Density.separationMass_nonneg
#print axioms MathCollab.Density.decay_le_floor_majorant
#print axioms MathCollab.Density.separated_decay_row
#print axioms MathCollab.Density.separated_decay_pairs
#print axioms MathCollab.Density.LargeValueData.local_card_le
#print axioms MathCollab.Density.productMultiplicity_le_divisors
#print axioms MathCollab.Density.product_range
#print axioms MathCollab.Density.divisorMaximum_ge_one
#print axioms MathCollab.Density.original_product_divisors_le
#print axioms MathCollab.Density.product_cutoff_one
#print axioms MathCollab.Density.product_grouping_cutoff
#print axioms MathCollab.Density.localSet_localDiameter_le
#print axioms MathCollab.Density.reflection_recursive_scale
#print axioms MathCollab.Density.reflection_scale_error_power
#print axioms MathCollab.Density.reflection_error_specialization
#print axioms MathCollab.Density.uniform_reflection_application

-- Completed Step 4: uniform arithmetic threshold and final large values.
#print MathCollab.Density.divisor_card_subpower
#print MathCollab.Density.divisorMaximum_subpower
#print MathCollab.Density.uniform_scalar_decay
#print MathCollab.Density.uniform_absorption_threshold
#print MathCollab.Density.uniform_absorbed_kernel
#print MathCollab.Density.optimal_integer_scale
#print MathCollab.Density.large_values_with_divisors
#print MathCollab.Density.large_values_data
#print MathCollab.Density.large_values
#print axioms MathCollab.Density.exponent_linear_le_geometric
#print axioms MathCollab.Density.exponent_linear_le_two_pow
#print axioms MathCollab.Density.divisor_card_subpower
#print axioms MathCollab.Density.divisorMaximum_subpower
#print axioms MathCollab.Density.LargeValueData.scalar_square_le
#print axioms MathCollab.Density.uniform_scalar_decay
#print axioms MathCollab.Density.tendsto_power_log_two_mul
#print axioms MathCollab.Density.uniform_absorption_threshold
#print axioms MathCollab.Density.uniform_absorbed_kernel
#print axioms MathCollab.Density.cardinality_at_length
#print axioms MathCollab.Density.optimal_integer_scale
#print axioms MathCollab.Density.large_values_with_divisors
#print axioms MathCollab.Density.large_values_data
#print axioms MathCollab.Density.large_values

-- Step 5 checkpoint: actual zeros, multiplicity and conditional detecting-family bridge.
#print MathCollab.Density.zetaDensityCount
#print MathCollab.Density.zetaMultiplicity
#print MathCollab.Density.mem_zetaDensityFinset
#print MathCollab.Density.zeta_analyticOrder_ne_top
#print MathCollab.Density.zetaMultiplicity_pos
#print MathCollab.Density.zetaMultiplicity_local_factorization
#print MathCollab.Density.zetaZeroRegion_finite
#print MathCollab.Density.weighted_separated_extraction
#print MathCollab.Density.zetaSlab_separated_representatives
#print MathCollab.Density.zetaSlab_large_values_cover
#print MathCollab.Density.mollifierCoefficient_vanishes
#print MathCollab.Density.first_detector_error_scale
#print MathCollab.Density.density_margin_choice
#print axioms MathCollab.Density.zeta_analyticOrder_ne_top
#print axioms MathCollab.Density.nontrivialZetaZero_ne_one
#print axioms MathCollab.Density.zetaMultiplicity_cast
#print axioms MathCollab.Density.zetaMultiplicity_pos
#print axioms MathCollab.Density.zetaMultiplicity_local_factorization
#print axioms MathCollab.Density.zetaZeroRegion_finite
#print axioms MathCollab.Density.mem_zetaZeroFinset
#print axioms MathCollab.Density.mem_zetaDensityFinset
#print axioms MathCollab.Density.zetaZeroFinset_card_le_count
#print axioms MathCollab.Density.zetaSlabCount_mono
#print axioms MathCollab.Density.zetaDensityCount_mono
#print axioms MathCollab.Density.ordinateBin_eq_iff
#print axioms MathCollab.Density.occupied_bins_parity
#print axioms MathCollab.Density.same_parity_bins_separated
#print axioms MathCollab.Density.weighted_separated_extraction
#print axioms MathCollab.Density.zetaSlab_separated_representatives
#print axioms MathCollab.Density.zetaSlab_large_values_cover
#print axioms MathCollab.Density.mollifierCoefficient_eq_full
#print axioms MathCollab.Density.mollifierCoefficient_one
#print axioms MathCollab.Density.mollifierCoefficient_vanishes
#print axioms MathCollab.Density.mollifierCoefficient_abs_le
#print axioms MathCollab.Density.mollifierCoefficient_norm_le
#print axioms MathCollab.Density.first_detector_error_scale
#print axioms MathCollab.Density.first_detector_majorant_tendsto_zero
#print axioms MathCollab.Density.density_margin_choice

-- Step 5: proved gamma decay and actual local multiplicity input.
#print MathCollab.Density.norm_Gamma_detector_strip
#print MathCollab.Density.norm_Gamma_contour_strip
#print MathCollab.Density.norm_Gamma_one_sub_zero_le
#print MathCollab.Density.uniform_detector_gamma_mass
#print MathCollab.Density.ZetaGrowth.riemannZeta_eq_abel
#print MathCollab.Density.ZetaGrowth.norm_riemannZeta_le_five_mul_norm
#print MathCollab.Density.ZetaGrowth.euler_product_lower_bound_2
#print MathCollab.Density.zeta_unit_bin_sum_le_jensen
#print MathCollab.Density.zeta_local_multiplicity_bound
#print MathCollab.Density.zeta_separated_representatives
#print axioms MathCollab.Density.GammaBounds.one_sub_centralPoint
#print axioms MathCollab.Density.GammaBounds.sin_pi_mul_centralPoint
#print axioms MathCollab.Density.GammaBounds.norm_Gamma_centralPoint_sq
#print axioms MathCollab.Density.GammaBounds.two_mul_cosh_abs
#print axioms MathCollab.Density.GammaBounds.exp_abs_le_two_mul_cosh
#print axioms MathCollab.Density.GammaBounds.norm_Gamma_centralPoint_le_exp
#print axioms MathCollab.Density.GammaBounds.norm_betaIntegral_le_real_integral
#print axioms MathCollab.Density.GammaBounds.betaIntegral_ofReal_eq_ofReal_integral
#print axioms MathCollab.Density.GammaBounds.real_beta_integral_eq_Gamma_div
#print axioms MathCollab.Density.GammaBounds.norm_betaIntegral_le_Gamma_div
#print axioms MathCollab.Density.GammaBounds.Gamma_half_sq
#print axioms MathCollab.Density.GammaBounds.one_le_Gamma_half
#print axioms MathCollab.Density.GammaBounds.Gamma_half_le_two
#print axioms MathCollab.Density.GammaBounds.Gamma_real_Icc_half_three_half_le_two
#print axioms MathCollab.Density.GammaBounds.stripPoint_re
#print axioms MathCollab.Density.GammaBounds.stripPoint_im
#print axioms MathCollab.Density.GammaBounds.stripPoint_add_real
#print axioms MathCollab.Density.GammaBounds.Gamma_three_half_ge_half
#print axioms MathCollab.Density.GammaBounds.norm_Gamma_stripPoint_le_four_upper
#print axioms MathCollab.Density.GammaBounds.centralPoint_add_one
#print axioms MathCollab.Density.GammaBounds.norm_centralPoint_le_one_add_abs
#print axioms MathCollab.Density.GammaBounds.norm_Gamma_upperPoint_le_exp
#print axioms MathCollab.Density.GammaBounds.norm_Gamma_positive_strip_le_exp
#print axioms MathCollab.Density.GammaBounds.stripPoint_add_one
#print axioms MathCollab.Density.GammaBounds.norm_Gamma_compactStrip_le_exp
#print axioms MathCollab.Density.norm_Gamma_detector_strip
#print axioms MathCollab.Density.continuous_Gamma_detector_strip
#print axioms MathCollab.Density.norm_Gamma_contour_strip
#print axioms MathCollab.Density.norm_Gamma_one_sub_zero_le
#print axioms MathCollab.Density.integrable_detectorGammaMajorant
#print axioms MathCollab.Density.uniform_detector_gamma_mass
#print axioms MathCollab.Density.ZetaGrowth.abelZetaKernel_eq_of_one_lt
#print axioms MathCollab.Density.ZetaGrowth.abelZetaKernel_eq_zero_of_le_one
#print axioms MathCollab.Density.ZetaGrowth.norm_abelZetaKernel_le_one
#print axioms MathCollab.Density.ZetaGrowth.measurable_abelZetaKernel
#print axioms MathCollab.Density.ZetaGrowth.locallyIntegrableOn_abelZetaKernel
#print axioms MathCollab.Density.ZetaGrowth.abelZetaKernel_isBigO_atTop
#print axioms MathCollab.Density.ZetaGrowth.abelZetaKernel_isBigO_zero
#print axioms MathCollab.Density.ZetaGrowth.differentiableAt_abelZetaRemainder
#print axioms MathCollab.Density.ZetaGrowth.mellinConvergent_abelZetaKernel
#print axioms MathCollab.Density.ZetaGrowth.abelZetaRemainder_eq_integral
#print axioms MathCollab.Density.ZetaGrowth.integrableOn_abelZetaRemainder_integrand
#print axioms MathCollab.Density.ZetaGrowth.differentiableAt_regularizedRiemannZeta
#print axioms MathCollab.Density.ZetaGrowth.differentiableAt_regularizedAbelZeta
#print axioms MathCollab.Density.ZetaGrowth.sum_one_Icc
#print axioms MathCollab.Density.ZetaGrowth.sum_one_Icc_isBigO
#print axioms MathCollab.Density.ZetaGrowth.natFloor_cast_complex
#print axioms MathCollab.Density.ZetaGrowth.integral_Ioi_cpow_neg
#print axioms MathCollab.Density.ZetaGrowth.riemannZeta_eq_abel_of_one_lt_re
#print axioms MathCollab.Density.ZetaGrowth.regularized_zeta_eq_abel_of_one_lt_re
#print axioms MathCollab.Density.ZetaGrowth.regularized_zeta_eq_abel
#print axioms MathCollab.Density.ZetaGrowth.riemannZeta_eq_abel
#print axioms MathCollab.Density.ZetaGrowth.norm_abelZetaRemainder_le
#print axioms MathCollab.Density.ZetaGrowth.norm_riemannZeta_le_five_mul_norm
#print axioms MathCollab.Density.ZetaGrowth.finset_analyticOrderNatAt_le_finsum_divisor
#print axioms MathCollab.Density.ZetaGrowth.zeta_jensen_sphere_bound
#print axioms MathCollab.Density.ZetaGrowth.moebius_coeff_norm_le_one
#print axioms MathCollab.Density.ZetaGrowth.moebius_LSeries_norm_lt_five_thirds
#print axioms MathCollab.Density.ZetaGrowth.euler_product_lower_bound_2
#print axioms MathCollab.Density.zeta_unit_bin_sum_le_jensen
#print axioms MathCollab.Density.zeta_local_multiplicity_bound
#print axioms MathCollab.Density.zeta_separated_representatives

-- Generic actual-zeta contour detector.
#print riemannZeta_mul_zetaMollifier_eq_LSeries
#print mollifierDirichletCoeff_LSeriesSummable
#print GammaMellin.mellinInv_Gamma_eq_exp_neg
#print smoothedDetector_eq_rightContour
#print detector_finite_rectangle_kernel
#print integrable_detectorKernel_left
#print integrable_detectorKernel_right
#print norm_detectorKernel_horizontal
#print summable_zeta_detector_series
#print zeta_detector_identity

#print axioms MathCollab.Density.GammaMellin.norm_Gamma_le_realGamma_re
#print axioms MathCollab.Density.GammaMellin.im_sq_mul_norm_Gamma_vertical_le
#print axioms MathCollab.Density.GammaMellin.norm_Gamma_vertical_le_inv_one_add_sq
#print axioms MathCollab.Density.GammaMellin.verticalIntegrable_Gamma
#print axioms MathCollab.Density.GammaMellin.mellinConvergent_exp_neg
#print axioms MathCollab.Density.GammaMellin.verticalIntegrable_mellin_exp_neg
#print axioms MathCollab.Density.GammaMellin.mellinInv_GammaIntegral_eq_exp_neg
#print axioms MathCollab.Density.GammaMellin.mellinInv_Gamma_eq_exp_neg
#print axioms MathCollab.Density.GammaMellin.exp_neg_eq_gamma_vertical_integral
#print axioms MathCollab.Density.GammaMellin.cpow_neg_div_eq_reverse_cpow
#print axioms MathCollab.Density.GammaMellin.exp_neg_nat_div_eq_detector_right_line
#print axioms MathCollab.Density.truncatedMoebius_apply
#print axioms MathCollab.Density.truncatedMoebius_hasFiniteSupport
#print axioms MathCollab.Density.truncatedMoebius_LSeriesSummable
#print axioms MathCollab.Density.zetaMollifier_eq_LSeries
#print axioms MathCollab.Density.zeta_mul_truncatedMoebius_apply
#print axioms MathCollab.Density.riemannZeta_mul_zetaMollifier_eq_LSeries
#print axioms MathCollab.Density.mollifierDirichletCoeff_LSeriesSummable
#print axioms MathCollab.Density.mollifierDirichletCoeff_zero
#print axioms MathCollab.Density.norm_mollifierDirichletCoeff_le_cutoff
#print axioms MathCollab.Density.differentiableAt_zetaMollifier
#print axioms MathCollab.Density.integrable_tsum_of_summable_integral_norm
#print axioms MathCollab.Density.norm_mollifier_LSeries_term_le_cutoff
#print axioms MathCollab.Density.summable_smoothedDetector
#print axioms MathCollab.Density.hasSum_smoothedDetector
#print axioms MathCollab.Density.norm_LSeries_term_div_rpow_eq_add
#print axioms MathCollab.Density.Gamma_mul_term_div_cpow_eq_add
#print axioms MathCollab.Density.mellin_smoothedDetector_eq
#print axioms MathCollab.Density.summable_detectorPSeries
#print axioms MathCollab.Density.detectorPSeries_nonneg
#print axioms MathCollab.Density.norm_mollifier_LSeries_le_cutoff_pSeries
#print axioms MathCollab.Density.verticalIntegrable_mellin_smoothedDetector
#print axioms MathCollab.Density.continuousAt_smoothedDetector
#print axioms MathCollab.Density.mellinConvergent_smoothedDetector
#print axioms MathCollab.Density.smoothedDetector_eq_mellinInv
#print axioms MathCollab.Density.smoothedDetector_eq_rightContour
#print axioms MathCollab.Density.Contour.mem_Rect
#print axioms MathCollab.Density.Contour.Set.left_not_mem_uIoo
#print axioms MathCollab.Density.Contour.Set.right_not_mem_uIoo
#print axioms MathCollab.Density.Contour.Set.ne_left_of_mem_uIoo
#print axioms MathCollab.Density.Contour.Set.ne_right_of_mem_uIoo
#print axioms MathCollab.Density.Contour.rectangleBorder_subset_rectangle
#print axioms MathCollab.Density.Contour.rectangleBorder_disjoint_singleton
#print axioms MathCollab.Density.Contour.rectangle_mem_nhds_iff
#print axioms MathCollab.Density.Contour.mapsTo_rectangleBorder_left_re
#print axioms MathCollab.Density.Contour.mapsTo_rectangleBorder_right_re
#print axioms MathCollab.Density.Contour.mapsTo_rectangleBorder_left_im
#print axioms MathCollab.Density.Contour.mapsTo_rectangleBorder_right_im
#print axioms MathCollab.Density.Contour.not_mem_rectangleBorder_of_rectangle_mem_nhds
#print axioms MathCollab.Density.Contour.HolomorphicOn.vanishesOnRectangle
#print axioms MathCollab.Density.Contour.RectangleIntegral_congr
#print axioms MathCollab.Density.Contour.RectangleIntegral'_congr
#print axioms MathCollab.Density.Contour.RectangleBorderIntegrable.add
#print axioms MathCollab.Density.Contour.ContinuousOn.rectangleBorder_integrable
#print axioms MathCollab.Density.Contour.ContinuousOn.rectangleBorderIntegrable
#print axioms MathCollab.Density.Contour.ContinuousOn.rectangleBorderNoPIntegrable
#print axioms MathCollab.Density.Contour.HolomorphicOn.rectangleBorderIntegrable'
#print axioms MathCollab.Density.Contour.HolomorphicOn.rectangleBorderIntegrable
#print axioms MathCollab.Density.Contour.RectangleIntegral.translate
#print axioms MathCollab.Density.Contour.RectangleIntegral.translate'
#print axioms MathCollab.Density.Contour.Complex.inv_re_add_im
#print axioms MathCollab.Density.Contour.sq_add_sq_ne_zero
#print axioms MathCollab.Density.Contour.continuous_self_div_sq_add_sq
#print axioms MathCollab.Density.Contour.integral_self_div_sq_add_sq
#print axioms MathCollab.Density.Contour.integral_const_div_sq_add_sq
#print axioms MathCollab.Density.Contour.integral_const_div_self_add_im
#print axioms MathCollab.Density.Contour.integral_const_div_re_add_self
#print axioms MathCollab.Density.Contour.ResidueTheoremAtOrigin'
#print axioms MathCollab.Density.Contour.ResidueTheoremInRectangle
#print axioms MathCollab.Density.Contour.ResidueTheoremOnRectangleWithSimplePole
#print axioms MathCollab.Density.shiftedRegularizedZeta_zero
#print axioms MathCollab.Density.shiftedRegularizedZeta_eq
#print axioms MathCollab.Density.detectorContourNumerator_div_eq_integrand
#print axioms MathCollab.Density.detectorContourNumerator_at_pole
#print axioms MathCollab.Density.differentiableAt_shiftedRegularizedZeta
#print axioms MathCollab.Density.differentiableAt_zetaZeroQuotient
#print axioms MathCollab.Density.differentiableOn_detectorContourNumerator
#print axioms MathCollab.Density.detector_finite_rectangle_residue
#print axioms MathCollab.Density.detector_finite_rectangle_kernel
#print axioms MathCollab.Density.norm_zetaMollifier_le_cutoff
#print axioms MathCollab.Density.norm_riemannZeta_critical_le_linear
#print axioms MathCollab.Density.integrable_detectorKernel_right
#print axioms MathCollab.Density.integrable_detectorKernel_left
#print axioms MathCollab.Density.norm_detectorKernel_horizontal
#print axioms MathCollab.Density.tendsto_detector_horizontal_majorant
#print axioms MathCollab.Density.tendsto_detector_horizontal_integral
#print axioms MathCollab.Density.smoothedDetector_contour_identity
#print axioms MathCollab.Density.smoothedDetector_term_eq
#print axioms MathCollab.Density.summable_zeta_detector_series
#print axioms MathCollab.Density.zeta_detector_identity

-- Step 5 sharp estimates and conditional finite detection.
#check @MathCollab.Density.norm_zetaMollifier_le_two_sqrt
#check @MathCollab.Density.uniform_detector_integral_bound
#check @MathCollab.Density.norm_firstDetector_residue_le
#check @MathCollab.Density.firstDetector_eventually_small_of_zeta_bound
#check @MathCollab.Density.norm_firstDetector_tail_le
#check @MathCollab.Density.firstDetectorCoefficient_real_support
#check @MathCollab.Density.finiteDetector_eventually_large_of_zeta_bound
#check @MathCollab.Density.sum_abs_detectorTaylorWeight_le
#check @MathCollab.Density.exists_large_taylor_component
#check @MathCollab.Density.norm_detectorTaylor_tail_le
#print axioms MathCollab.Density.sum_inv_sqrt_le
#print axioms MathCollab.Density.norm_zetaMollifier_le_two_sqrt
#print axioms MathCollab.Density.detector_shifted_rpow_le
#print axioms MathCollab.Density.uniform_detector_integral_bound
#print axioms MathCollab.Density.norm_detectorResidue_le
#print axioms MathCollab.Density.norm_firstDetector_residue_le
#print axioms MathCollab.Density.firstDetector_residue_eventually_small
#print axioms MathCollab.Density.firstDetector_eventually_small_of_zeta_bound
#print axioms MathCollab.Density.norm_detectorTerm_le
#print axioms MathCollab.Density.norm_detector_tail_le
#print axioms MathCollab.Density.detector_geometric_factor_le
#print axioms MathCollab.Density.norm_firstDetector_tail_le
#print axioms MathCollab.Density.firstDetector_tail_eventually_small
#print axioms MathCollab.Density.firstDetectorCoefficient_support
#print axioms MathCollab.Density.firstDetectorCoefficient_real_support
#print axioms MathCollab.Density.firstDetectorCoefficient_norm_le
#print axioms MathCollab.Density.firstDetectorX_one_le
#print axioms MathCollab.Density.detectorTerm_finite_split
#print axioms MathCollab.Density.finiteDetector_decomposition
#print axioms MathCollab.Density.finiteDetector_eventually_large_of_zeta_bound
#print axioms MathCollab.Density.detectorTaylorRatio_bounds
#print axioms MathCollab.Density.abs_detectorTaylorWeight_le
#print axioms MathCollab.Density.sum_abs_detectorTaylorWeight_le
#print axioms MathCollab.Density.norm_detectorTaylorCoefficient_le
#print axioms MathCollab.Density.exists_large_taylor_component
#print axioms MathCollab.Density.norm_detectorTaylorPolynomial_le
#print axioms MathCollab.Density.norm_detectorTaylor_tail_le

-- Fixed-family and powering checkpoint.
#check @MathCollab.Density.hasSum_detector_rpow
#check @MathCollab.Density.hasSum_detectorTaylorPolynomial
#check @MathCollab.Density.fixedDetector_cover_of_zeta_bound
#check @MathCollab.Density.arithmeticFunction_pow_norm_le
#check @MathCollab.Density.exists_poweredDetector_piece
#check @MathCollab.Density.detectorPower_spec
#check @MathCollab.Density.poweredDetectorCoefficient_eventually_le
#check @MathCollab.Density.poweredDetectorFamily_cover_of_zeta_bound
#check @MathCollab.Density.poweredDetectorFamily_admissible
#print axioms MathCollab.Density.densityAmbient_eventually_cubeRoot_le
#print axioms MathCollab.Density.detectorHeight_ge_scale
#print axioms MathCollab.Density.poweredDetectorFamily_admissible
#print axioms MathCollab.Density.detectorTaylorRatio_eq_prod_div
#print axioms MathCollab.Density.detector_descPochhammer_neg
#print axioms MathCollab.Density.choose_neg_eq_detectorTaylorRatio
#print axioms MathCollab.Density.hasSum_detector_binomial
#print axioms MathCollab.Density.hasSum_detector_rpow
#print axioms MathCollab.Density.cpow_neg_eq_real_phase
#print axioms MathCollab.Density.detectorBlock_eq_normalized
#print axioms MathCollab.Density.norm_normalizedDetectorBlock
#print axioms MathCollab.Density.hasSum_detectorTaylorPolynomial
#print axioms MathCollab.Density.norm_detectorTaylor_tsum_ge
#print axioms MathCollab.Density.detectorBlockCoefficients_apply
#print axioms MathCollab.Density.detectorBlockCoefficients_norm_le
#print axioms MathCollab.Density.arithmeticFunction_pow_norm_le
#print axioms MathCollab.Density.detectorBlockCoefficients_pow_support
#print axioms MathCollab.Density.detectorBlockCoefficients_pow_lower
#print axioms MathCollab.Density.detectorBlockCoefficients_pow_LSeriesSummable
#print axioms MathCollab.Density.detectorBlockCoefficients_LSeries_pow
#print axioms MathCollab.Density.sum_dyadic_Ioc
#print axioms MathCollab.Density.finiteDetector_eq_dyadic_sum
#print axioms MathCollab.Density.exists_detector_dyadic_block
#print axioms MathCollab.Density.detectorBlock_scale_bounds
#print axioms MathCollab.Density.firstDetectorCutoff_eventually_le_sq
#print axioms MathCollab.Density.detectorDyadicCount_le_log
#print axioms MathCollab.Density.detectorTaylorCutoff_le_log
#print axioms MathCollab.Density.detectorTaylorCutoff_geometric_le
#print axioms MathCollab.Density.detector_family_scales_eventually
#print axioms MathCollab.Density.poweredDetectorCoefficient_subpower
#print axioms MathCollab.Density.densityAmbient_eventually_le_sq
#print axioms MathCollab.Density.poweredDetectorCoefficient_eventually_le
#print axioms MathCollab.Density.normalizedPoweredCoefficient_eventually
#print axioms MathCollab.Density.detectingPolynomial_normalizedPowered
#print axioms MathCollab.Density.detectorPower_spec
#print axioms MathCollab.Density.detectorPower_base_le
#print axioms MathCollab.Density.detectorPower_piece_scales
#print axioms MathCollab.Density.detectorPower_support_scale
#print axioms MathCollab.Density.exists_poweredDetector_height
#print axioms MathCollab.Density.detectorHeightConstant_eventually
#print axioms MathCollab.Density.exists_normalizedPowered_height
#print axioms MathCollab.Density.dirichletPhase_div
#print axioms MathCollab.Density.dirichletPhase_conj
#print axioms MathCollab.Density.norm_detectingPolynomial_conj
#print axioms MathCollab.Density.norm_detectingPolynomial_eq_cpow_sum
#print axioms MathCollab.Density.detectorBlockCoefficients_LSeries
#print axioms MathCollab.Density.norm_detectorTaylorPolynomial_LSeries
#print axioms MathCollab.Density.sum_scaled_dyadic_Ioc
#print axioms MathCollab.Density.detectorBlockCoefficients_pow_LSeries_sum
#print axioms MathCollab.Density.exists_poweredDetector_piece
#print axioms MathCollab.Density.fixedDetectorIndices_card_le
#print axioms MathCollab.Density.norm_fixedDetector_tail_le
#print axioms MathCollab.Density.exists_fixedDetector_component
#print axioms MathCollab.Density.fixedDetector_cover_of_zeta_bound
#print axioms MathCollab.Density.poweredDetectorIndices_card_le
#print axioms MathCollab.Density.poweredDetectorFamily_scales
#print axioms MathCollab.Density.poweredDetectorFamily_cover_of_zeta_bound
#print axioms MathCollab.Density.poweredDetectorFamily_coefficients

-- Complete counting and actual-zeta integration.
#check @MathCollab.Density.normalizedHeight_quotient
#check @MathCollab.Density.density_family_sum_eventually
#check @MathCollab.Density.zetaSlab_density_bound_of_weyl
#check @MathCollab.Density.zetaMultiplicity_conj
#check @MathCollab.Density.zetaSlabCount_conj
#check @MathCollab.Density.zetaDensity_bound_of_eventual_slabs
#check @MathCollab.Density.densityCountingEta_margins
#check @MathCollab.Density.zeta_density_bound_of_weyl
#check @MathCollab.Density.actual_zeta_weyl_input
#check @MathCollab.Density.zeta_density_bound
#print axioms MathCollab.Density.densityCountingEta_margins
#print axioms MathCollab.Density.zetaDensityCount_eq_zero_of_one_le
#print axioms MathCollab.Density.zeta_density_bound_of_weyl
#print axioms MathCollab.Density.zetaSlab_extend_power_bound
#print axioms MathCollab.Density.zetaPositive_bound_of_slabs
#print axioms MathCollab.Density.zetaDensity_bound_of_eventual_slabs
#print axioms MathCollab.Density.normalizedHeight_quotient
#print axioms MathCollab.Density.densityAmbient_small_rpow
#print axioms MathCollab.Density.density_largeValue_term_le
#print axioms MathCollab.Density.density_logarithms_eventually
#print axioms MathCollab.Density.density_family_sum_eventually
#print axioms MathCollab.Density.zetaSlab_density_bound_of_weyl
#print axioms MathCollab.Density.zeta_density_bound
#print axioms MathCollab.Density.zetaSlab_large_values_cover_indexed
#print axioms MathCollab.Density.actual_zeta_weyl_input
#print axioms MathCollab.Density.analyticAt_conj_conj_local
#print axioms MathCollab.Density.isNontrivialZetaZero_conj
#print axioms MathCollab.Density.zetaMultiplicity_conj
#print axioms MathCollab.Density.zetaSlabCount_conj
#print axioms MathCollab.Density.zetaSlabCount_split_le
#print axioms MathCollab.Density.zetaDensityCount_le_twice_positive
