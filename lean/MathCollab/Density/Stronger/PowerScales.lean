module
-- Reversible module-visibility port of the audited development.
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Real Filter
open scoped Topology
set_option autoImplicit false
noncomputable section

namespace MathCollab.Density.Stronger

/-- The ceiling power closes the gap between the target exponent and three
halves of that exponent. The upper bound on k is fixed before x varies. -/
theorem bounded_power_exponent {a d x : ℝ}
    (ha : 0 < a) (hd : 0 < d) (hdx : d ≤ x) (hx : x ≤ 3*a/4) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ ⌈a/d⌉₊ ∧ a ≤ (k : ℝ)*x ∧ (k : ℝ)*x ≤ 3*a/2 := by
  have hxpos : 0 < x := hd.trans_le hdx
  refine ⟨⌈a/x⌉₊, ?_, ?_, ?_, ?_⟩
  · have hc := Nat.le_ceil (a/x)
    by_contra h
    have hz : ⌈a/x⌉₊ = 0 := by omega
    rw [hz, Nat.cast_zero] at hc
    exact (not_le_of_gt (div_pos ha hxpos)) hc
  · exact Nat.ceil_mono (div_le_div_of_nonneg_left ha.le hd hdx)
  · exact (div_le_iff₀ hxpos).mp (Nat.le_ceil (a/x))
  · by_cases hsmall : x ≤ a/2
    · have hc := Nat.ceil_lt_add_one (show 0 ≤ a/x by positivity)
      have hm := mul_lt_mul_of_pos_right hc hxpos
      have he : (a/x+1)*x = a+x := by field_simp
      rw [he] at hm
      linarith
    · have hc : ⌈a/x⌉₊ ≤ 2 := Nat.ceil_le.mpr ((div_le_iff₀ hxpos).mpr (by norm_num; linarith))
      have hcR : (⌈a/x⌉₊ : ℝ) ≤ 2 := by exact_mod_cast hc
      nlinarith

/-- Scale form of the bounded-power lemma, with M an arbitrary positive
real scale. This keeps the dyadic half-scale endpoint exact. -/
theorem bounded_power_scale {T M a d : ℝ}
    (hT : 1 < T) (ha : 0 < a) (hd : 0 < d)
    (hlo : T^d ≤ M) (hhi : M ≤ T^(3*a/4)) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ ⌈a/d⌉₊ ∧ T^a ≤ M^k ∧ M^k ≤ T^(3*a/2) := by
  have hTpos : 0 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hMpos : 0 < M := (Real.rpow_pos_of_pos hTpos d).trans_le hlo
  let x := Real.log M / Real.log T
  have hxlo : d ≤ x := by
    apply (le_div_iff₀ hlogT).mpr
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hTpos d) hlo
    rwa [Real.log_rpow hTpos] at hh
  have hxhi : x ≤ 3*a/4 := by
    apply (div_le_iff₀ hlogT).mpr
    have hh := Real.log_le_log hMpos hhi
    rwa [Real.log_rpow hTpos] at hh
  obtain ⟨k, hk, hkK, hlow, hupp⟩ := bounded_power_exponent ha hd hxlo hxhi
  refine ⟨k, hk, hkK, ?_, ?_⟩
  · apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hTpos a) (pow_pos hMpos k)).mp
    rw [Real.log_rpow hTpos, Real.log_pow]
    have hh := mul_le_mul_of_nonneg_right hlow hlogT.le
    dsimp [x] at hh
    simpa only [mul_assoc, div_mul_cancel₀ _ hlogT.ne'] using hh
  · apply (Real.log_le_log_iff (pow_pos hMpos k) (Real.rpow_pos_of_pos hTpos _)).mp
    rw [Real.log_pow, Real.log_rpow hTpos]
    have hh := mul_le_mul_of_nonneg_right hupp hlogT.le
    dsimp [x] at hh
    simpa only [mul_assoc, div_mul_cancel₀ _ hlogT.ne'] using hh

/-- The factor 1/4 is absorbed before all short scales
vary. In particular, the exponent bound is uniform in M and T. -/
theorem short_scale_bounded_power {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ M : ℝ,
      T^δ/4 ≤ M → M ≤ T^(3*a/4) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ ⌈2*a/δ⌉₊ ∧ T^a ≤ M^k ∧ M^k ≤ T^(3*a/2) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop (show 0 < δ/2 by positivity)).eventually_ge_atTop 4]
    with T hT hlarge
  intro M hlo hhi
  have hTpos : 0 < T := by linarith
  have hpow : T^(δ/2) ≤ T^δ/4 := by
    have hh := mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg hTpos.le (δ/2))
    rw [← Real.rpow_add hTpos, show δ/2+δ/2 = δ by ring] at hh
    linarith
  have he : a/(δ/2) = 2*a/δ := by ring
  simpa only [he] using bounded_power_scale hT ha (show 0 < δ/2 by positivity)
    (hpow.trans hlo) hhi

/-- Each of the k consecutive dyadic support pieces retains the lower scale;
the upper endpoint incurs a fixed factor, which must not be omitted. -/
theorem bounded_power_piece_scales {T M a c : ℝ} {k K ℓ : ℕ}
    (hM : 0 ≤ M) (hkK : k ≤ K) (hℓ : ℓ < k)
    (hlo : T^a ≤ M^k) (hhi : M^k ≤ T^c) :
    T^a ≤ (2 : ℝ)^ℓ*M^k ∧ (2 : ℝ)^ℓ*M^k ≤ (2 : ℝ)^K*T^c := by
  have htwo : (1 : ℝ) ≤ 2^ℓ := one_le_pow₀ (by norm_num)
  have hpow : 0 ≤ M^k := pow_nonneg hM k
  have htwoK : (2 : ℝ)^ℓ ≤ 2^K :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  refine ⟨hlo.trans ?_, ?_⟩
  · nlinarith
  · exact mul_le_mul htwoK hhi hpow (by positivity)

/-- The complete convolution support obeys the same fixed upper factor. -/
theorem bounded_power_support_scale {T M c : ℝ} {k K : ℕ}
    (hM : 0 ≤ M) (hkK : k ≤ K) (hhi : M^k ≤ T^c) :
    (2*M)^k ≤ (2 : ℝ)^K*T^c := by
  rw [mul_pow]
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hkK) hhi
    (pow_nonneg hM k) (by positivity)

/-- A fixed dyadic enlargement stays below the original height once c<1.
This is the precise eventual assertion needed after convolution splitting. -/
theorem fixed_scale_factor_eventually_below_height {C c : ℝ} (hc : c < 1) :
    ∀ᶠ T : ℝ in atTop, C*T^c ≤ T := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (tendsto_rpow_atTop (show 0 < 1-c by linarith)).eventually_ge_atTop C]
    with T hT hlarge
  calc
    C*T^c ≤ T^(1-c)*T^c := mul_le_mul_of_nonneg_right hlarge (by positivity)
    _ = T := by rw [← Real.rpow_add hT]; norm_num

end MathCollab.Density.Stronger
