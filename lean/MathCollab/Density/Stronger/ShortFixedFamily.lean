module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.SmoothDetector
public import MathCollab.Density.Stronger.SmoothShortBlock
public import MathCollab.Density.Stronger.FiniteConvolution
public import MathCollab.Density.Stronger.PowerScales

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set Filter
open scoped BigOperators Topology ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Natural half-block scales indexed before the zero. For positive j,
e=0 gives 2^j/2, and e=1 gives 2^j. -/
def smoothHalfScale (j : ℤ) (e : ℕ) : ℕ := 2^(j.toNat-1+e)

theorem smoothHalfScale_pos (j : ℤ) (e : ℕ) : 0 < smoothHalfScale j e := by
  unfold smoothHalfScale
  positivity

theorem smoothDetectorBlock_index_pos {ρ : ℂ} {X Y : ℝ} {j : ℤ}
    (hb : smoothDetectorBlock ρ X Y j ≠ 0) : 0 < j := by
  by_contra hj
  exact hb (smoothDetectorBlock_zero_of_nonpos ρ X Y (le_of_not_gt hj))

theorem smoothHalfScale_zero_eq {j : ℤ} (hj : 0 < j) :
    (2 : ℝ)^j = 2*(smoothHalfScale j 0 : ℝ) := by
  have hjn : 1 ≤ j.toNat := by omega
  have he : j = (j.toNat : ℤ) := (Int.toNat_of_nonneg hj.le).symm
  simp only [smoothHalfScale, add_zero, Nat.cast_pow, Nat.cast_ofNat]
  conv_lhs => rw [he, zpow_natCast, show j.toNat = j.toNat-1+1 by omega, pow_succ]
  ring

theorem smoothHalfScale_one_eq (j : ℤ) :
    smoothHalfScale j 1 = 2*smoothHalfScale j 0 := by
  simp only [smoothHalfScale, add_zero, pow_succ]
  ring

theorem smoothHalfScale_bounds {j : ℤ} (hj : 0 < j) {e : ℕ} (he : e < 2) :
    (2 : ℝ)^j/2 ≤ smoothHalfScale j e ∧
      (smoothHalfScale j e : ℝ) ≤ (2 : ℝ)^j := by
  have hz := smoothHalfScale_zero_eq hj
  have h1 := smoothHalfScale_one_eq j
  have hp : (0 : ℝ) < smoothHalfScale j 0 := by exact_mod_cast smoothHalfScale_pos j 0
  have hh : e = 0 ∨ e = 1 := by omega
  rcases hh with rfl | rfl
  · constructor <;> linarith
  · rw [h1]
    push_cast
    constructor <;> linarith

/-- Exact actual smooth-block split at every nonzero detecting dyadic scale. -/
theorem smoothDetectorBlock_eq_halves (ρ : ℂ) (X Y : ℝ) {j : ℤ} (hj : 0 < j) :
    smoothDetectorBlock ρ X Y j =
      genericBlock ρ (smoothShortCoefficient X Y ((2 : ℝ)^j)) (smoothHalfScale j 0) +
      genericBlock ρ (smoothShortCoefficient X Y ((2 : ℝ)^j)) (smoothHalfScale j 1) := by
  have hs := smoothDetector_tail_half_split ρ X Y (smoothHalfScale_pos j 0)
  rw [← smoothHalfScale_zero_eq hj, ← smoothHalfScale_one_eq] at hs
  exact hs

/-- The actual original smooth block yields a beta-independent Taylor member.
The original smooth scale 2^j is kept in the coefficient, including e=0. -/
theorem exists_smoothBlock_Taylor_member {ρ : ℂ} {X Y T D : ℝ} {j : ℤ}
    (hY : 0 < Y) (hT : 1 ≤ T) (hD : 0 < D)
    (hβ : 0 ≤ ρ.re) (hβ' : ρ.re ≤ 1)
    (hN : (2 : ℝ)^j ≤ T^2)
    (hsmall : 3*T^(-1 : ℝ) ≤ 1/(4*D))
    (hblock : 1/D ≤ ‖smoothDetectorBlock ρ X Y j‖) :
    0 < j ∧ ∃ e ∈ Finset.range 2, ∃ r ∈ Finset.range (detectorTaylorCutoff T+1),
      (smoothHalfScale j e : ℝ)^ρ.re/(8*D) ≤
        ‖genericTaylorPolynomial (smoothShortCoefficient X Y ((2 : ℝ)^j))
          (smoothHalfScale j e) r ρ.im‖ := by
  have hj : 0 < j := smoothDetectorBlock_index_pos
    (norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hblock))
  refine ⟨hj, ?_⟩
  obtain ⟨L, hL, hb⟩ := exists_smoothShort_half ρ X Y (smoothHalfScale_pos j 0)
  rw [← smoothHalfScale_zero_eq hj] at hb
  rw [← smoothHalfScale_one_eq] at hL
  change L ∈ ({smoothHalfScale j 0, smoothHalfScale j 1} : Finset ℕ) at hL
  have he : ∃ e ∈ Finset.range 2, L = smoothHalfScale j e := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with hL | hL
    · exact ⟨0, by simp, hL⟩
    · exact ⟨1, by simp, hL⟩
  obtain ⟨e, he, rfl⟩ := he
  have hhalf : 1/(2*D) ≤
      ‖genericBlock ρ (smoothShortCoefficient X Y ((2 : ℝ)^j)) (smoothHalfScale j e)‖ := by
    have hh := div_le_div_of_nonneg_right hblock (by norm_num : (0 : ℝ) ≤ 2)
    exact (show 1/(2*D) = (1/D)/2 by ring).trans_le (hh.trans hb)
  obtain ⟨r, hr, hb⟩ := exists_smoothShortTaylor_component X ((2 : ℝ)^j) hY hT
    (smoothHalfScale_pos j e) ((smoothHalfScale_bounds hj (Finset.mem_range.mp he)).2.trans hN)
    hβ hβ' hD hsmall hhalf
  exact ⟨e, he, r, hr, hb⟩

/-- The actual fixed Taylor coefficient restricted to its natural support. -/
def smoothTaylorArithmetic (X Y : ℝ) (j : ℤ) (e r : ℕ) : ArithmeticFunction ℂ where
  toFun n := if n ∈ Finset.Ioc (smoothHalfScale j e) (2*smoothHalfScale j e) then
    genericTaylorCoefficient (smoothShortCoefficient X Y ((2 : ℝ)^j)) (smoothHalfScale j e) r n
    else 0
  map_zero' := by simp

theorem smoothTaylorArithmetic_support (X Y : ℝ) (j : ℤ) (e r n : ℕ)
    (hn : smoothTaylorArithmetic X Y j e r n ≠ 0) :
    n ∈ Finset.Ioc (smoothHalfScale j e) (2*smoothHalfScale j e) := by
  by_contra hh
  apply hn
  change (if n ∈ Finset.Ioc (smoothHalfScale j e) (2*smoothHalfScale j e) then _ else 0) = 0
  exact ite_eq_right hh

theorem smoothTaylorArithmetic_norm_le (X : ℝ) {Y : ℝ} (hY : 0 < Y)
    (j : ℤ) (e r n : ℕ) : ‖smoothTaylorArithmetic X Y j e r n‖ ≤ (n.divisors.card : ℝ) := by
  change ‖if n ∈ Finset.Ioc (smoothHalfScale j e) (2*smoothHalfScale j e) then _ else 0‖ ≤ _
  split_ifs with hn
  · exact norm_smoothShortTaylorCoefficient_le X ((2 : ℝ)^j) hY (smoothHalfScale_pos j e) hn r
  · simp

theorem smoothTaylorArithmetic_LSeries (X Y : ℝ) (j : ℤ) (e r : ℕ) (s : ℂ) :
    LSeries (smoothTaylorArithmetic X Y j e r) s =
      ∑ n ∈ Finset.Ioc (smoothHalfScale j e) (2*smoothHalfScale j e),
        genericTaylorCoefficient (smoothShortCoefficient X Y ((2 : ℝ)^j))
          (smoothHalfScale j e) r n * (n : ℂ)^(-s) := by
  rw [LSeries, tsum_eq_sum (s := Finset.Ioc (smoothHalfScale j e) (2*smoothHalfScale j e))]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [LSeries.term_def₀ (smoothTaylorArithmetic X Y j e r).map_zero]
    change (if n ∈ Finset.Ioc (smoothHalfScale j e) (2*smoothHalfScale j e) then _ else 0) * _ = _
    rw [ite_eq_left hn]
  · intro n hn
    rw [LSeries.term_def₀ (smoothTaylorArithmetic X Y j e r).map_zero]
    change (if n ∈ Finset.Ioc (smoothHalfScale j e) (2*smoothHalfScale j e) then _ else 0) * _ = 0
    rw [ite_eq_right hn, zero_mul]

theorem norm_smoothTaylor_LSeries (X Y t : ℝ) (j : ℤ) (e r : ℕ) :
    ‖genericTaylorPolynomial (smoothShortCoefficient X Y ((2 : ℝ)^j))
      (smoothHalfScale j e) r t‖ =
    ‖LSeries (smoothTaylorArithmetic X Y j e r) (Complex.I*(t : ℂ))‖ := by
  rw [genericTaylorPolynomial, norm_detectingPolynomial_eq_cpow_sum (smoothHalfScale_pos j e),
    smoothTaylorArithmetic_LSeries]

/-- Full conjugated Dirichlet convolution coefficients at the original scale. -/
def smoothPoweredCoefficient (X Y : ℝ) (j : ℤ) (e r k n : ℕ) : ℂ :=
  conj (((smoothTaylorArithmetic X Y j e r)^k) n)

theorem exists_smoothTaylor_powered_piece (X Y t : ℝ) (j : ℤ) (e r : ℕ) {k : ℕ}
    (hk : 0 < k) :
    ∃ l ∈ Finset.range k,
      ‖genericTaylorPolynomial (smoothShortCoefficient X Y ((2 : ℝ)^j))
        (smoothHalfScale j e) r t‖^k/(k : ℝ) ≤
      ‖detectingPolynomial (2^l*(smoothHalfScale j e)^k)
        (smoothPoweredCoefficient X Y j e r k) t‖ := by
  rw [norm_smoothTaylor_LSeries]
  exact exists_finiteBlock_powered_piece (smoothHalfScale_pos j e) hk
    (smoothTaylorArithmetic_support X Y j e r) t

end MathCollab.Density.Stronger
