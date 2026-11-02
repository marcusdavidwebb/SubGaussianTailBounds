import SingularValueBounds.KL.Lower.Covariance

/-! # Orthogonal Gaussian averaging at K=1

The retained fourth-order deficit in supplementary S1.5 is obtained by
averaging the two directions `sqrt h u ± sqrt j g`. Pairing the directions
eliminates odd terms before applying Tonelli; no coordinate independence of
the original row is assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators ENNReal NNReal

namespace SingularValueBounds.KL
noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ι → ℝ}

set_option maxHeartbeats 1600000 in
/-- The diagonal form of the orthogonal fourth-order averaging inequality.
The spectral wrapper below removes the choice of basis. -/
theorem endpoint_diagonal_quartic (hsg : SubGaussianMGF μ X 1)
    (hiso : CentredIsotropic μ X) (u b : ι → ℝ)
    (hu : u ⬝ᵥ u = 1) (hb : ∀ i, 0 ≤ b i) (hub : ∀ i, b i * u i = 0)
    {h j : ℝ} (hh : 0 ≤ h) (hj : 0 ≤ j) :
    h ^ 2 * (∫ ω, (u ⬝ᵥ X ω) ^ 4 ∂μ) +
      6 * h * j * (∫ ω, (u ⬝ᵥ X ω) ^ 2 * (∑ i, b i * X ω i ^ 2) ∂μ) +
      3 * j ^ 2 * (∫ ω, (∑ i, b i * X ω i ^ 2) ^ 2 ∂μ) ≤
      3 * (h ^ 2 + 2 * h * j * (∑ i, b i) +
        j ^ 2 * ((∑ i, b i) ^ 2 + 2 * ∑ i, b i ^ 2)) := by
  let a : ι → ℝ := fun i => Real.sqrt (b i)
  have ha (i : ι) : a i ^ 2 = b i := Real.sq_sqrt (hb i)
  have hau (i : ι) : a i * u i = 0 := by
    by_cases hi : b i = 0
    · simp [a, hi]
    · have hui : u i = 0 := (mul_eq_zero.mp (hub i)).resolve_left hi
      simp [hui]
  let V : (ι → ℝ) → ι → ℝ := fun g i => a i * g i
  let Y : Ω → ℝ := fun ω => ∑ i, b i * X ω i ^ 2
  let Z : Ω → ℝ := fun ω => u ⬝ᵥ X ω
  let Q : (ι → ℝ) → ℝ := fun g => ∑ i, b i * g i ^ 2
  let W : Ω → (ι → ℝ) → ℝ := fun ω g => ∑ i, a i * g i * X ω i
  let F : Ω → (ι → ℝ) → ℝ := fun ω g =>
    h ^ 2 * Z ω ^ 4 + 6 * h * j * Z ω ^ 2 * W ω g ^ 2 + j ^ 2 * W ω g ^ 4
  have hFnonneg (ω : Ω) (g : ι → ℝ) : 0 ≤ F ω g := by
    dsimp [F]
    positivity
  have hFmeas : Measurable (Function.uncurry F) := by
    have hm := hiso.measurable
    dsimp [F, Z, W, dotProduct, Function.uncurry]
    fun_prop
  have hvg (g : ι → ℝ) : V g ⬝ᵥ V g = Q g := by
    simp only [V, Q, dotProduct, ← sq, mul_pow, ha]
  have huv (g : ι → ℝ) : u ⬝ᵥ V g = 0 := by
    dsimp [V, dotProduct]
    apply Finset.sum_eq_zero
    intro i _
    rw [← mul_assoc, mul_comm (u i) (a i), hau, zero_mul]
  have hd (g : ι → ℝ) (s : ℝ) :
      (Real.sqrt h • u + s • V g) ⬝ᵥ (Real.sqrt h • u + s • V g) =
        h + s ^ 2 * Q g := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hu, huv, dotProduct_comm (V g) u, hvg]
    nlinarith only [Real.sq_sqrt hh]
  have hp (ω : Ω) (g : ι → ℝ) :
      (((Real.sqrt h • u + Real.sqrt j • V g) ⬝ᵥ X ω) ^ 4 +
        ((Real.sqrt h • u + (-Real.sqrt j) • V g) ⬝ᵥ X ω) ^ 4) / 2 = F ω g := by
    have hw : V g ⬝ᵥ X ω = W ω g := rfl
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, hw]
    dsimp [F, Z]
    have hh2 := Real.sq_sqrt hh
    have hj2 := Real.sq_sqrt hj
    calc
      _ = (Real.sqrt h)^4 * (u ⬝ᵥ X ω)^4 +
          6 * (Real.sqrt h)^2 * (Real.sqrt j)^2 * (u ⬝ᵥ X ω)^2 * W ω g^2 +
          (Real.sqrt j)^4 * W ω g^4 := by ring
      _ = _ := by
        rw [show (Real.sqrt h)^4 = ((Real.sqrt h)^2)^2 by ring,
          show (Real.sqrt j)^4 = ((Real.sqrt j)^2)^2 by ring, hh2, hj2]
  have hinner (g : ι → ℝ) :
      (∫⁻ ω, ENNReal.ofReal (F ω g) ∂μ) ≤ ENNReal.ofReal (3 * (h + j * Q g) ^ 2) := by
    let vp := Real.sqrt h • u + Real.sqrt j • V g
    let vm := Real.sqrt h • u + (-Real.sqrt j) • V g
    have hi : Integrable (F · g) μ := by
      convert! ((hsg.directional_integrable_pow vp 4).add
        (hsg.directional_integrable_pow vm 4)).div_const 2 using 1
      funext ω
      exact (hp ω g).symm
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun ω => hFnonneg ω g))]
    apply ENNReal.ofReal_le_ofReal
    have hf (v : ι → ℝ) := directional_fourth hsg hiso (by norm_num) v
    norm_num [fourthMomentConstant] at hf
    have hp4 := hf vp
    have hm4 := hf vm
    have he : (∫ ω, F ω g ∂μ) =
        ((∫ ω, (vp ⬝ᵥ X ω) ^ 4 ∂μ) + (∫ ω, (vm ⬝ᵥ X ω) ^ 4 ∂μ)) / 2 := by
      simp_rw [← hp]
      rw [integral_div, integral_add (hsg.directional_integrable_pow _ _)
        (hsg.directional_integrable_pow _ _)]
    rw [he]
    have hdp : vp ⬝ᵥ vp = h + j * Q g := by
      dsimp [vp]
      rw [hd, Real.sq_sqrt hj]
    have hdm : vm ⬝ᵥ vm = h + j * Q g := by
      dsimp [vm]
      rw [hd, neg_sq, Real.sq_sqrt hj]
    rw [hdp] at hp4
    rw [hdm] at hm4
    linarith
  have hgW (ω : Ω) (n : ℕ) : Integrable (fun g => W ω g ^ n) (standardGaussian ι) := by
    simpa only [W, mul_assoc, mul_comm, mul_left_comm] using
      standardGaussian_linear_pow_integrable (fun i => a i * X ω i) n
  have hg2 (ω : Ω) : (∫ g, W ω g ^ 2 ∂standardGaussian ι) = Y ω := by
    have he := (standardGaussian_linear_moments (fun i => a i * X ω i)).1
    simpa only [W, Y, mul_assoc, mul_comm, mul_left_comm, mul_pow, ha] using he
  have hg4 (ω : Ω) : (∫ g, W ω g ^ 4 ∂standardGaussian ι) = 3 * Y ω ^ 2 := by
    have he := (standardGaussian_linear_moments (fun i => a i * X ω i)).2
    simpa only [W, Y, mul_assoc, mul_comm, mul_left_comm, mul_pow, ha] using he
  have hid (ω : Ω) : (∫⁻ g, ENNReal.ofReal (F ω g) ∂standardGaussian ι) =
      ENNReal.ofReal (h ^ 2 * Z ω ^ 4 + (6*h*j)*(Z ω ^ 2*Y ω) +
        3 * j ^ 2 * Y ω ^ 2) := by
    have hi : Integrable (F ω) (standardGaussian ι) :=
      ((integrable_const _).add ((hgW ω 2).const_mul _)).add ((hgW ω 4).const_mul _)
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (hFnonneg ω))]
    congr 1
    dsimp [F]
    rw [integral_add (f := fun g => h ^ 2 * Z ω ^ 4 + 6*h*j*Z ω ^ 2*W ω g ^ 2)
      (g := fun g => j ^ 2 * W ω g ^ 4)
      ((integrable_const _).add ((hgW ω 2).const_mul _)) ((hgW ω 4).const_mul _),
      integral_add (f := fun _ => h ^ 2 * Z ω ^ 4)
        (g := fun g => 6*h*j*Z ω ^ 2*W ω g ^ 2)
        (integrable_const _) ((hgW ω 2).const_mul _)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
      integral_const_mul, hg2, hg4]
    ring
  have hY : MemLp Y 2 μ := by
    convert! hsg.quadratic_memLp_two (Matrix.diagonal b) using 1
    ext ω
    simp only [Y, quadraticForm, Matrix.mulVec_diagonal, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hZ2 : MemLp (fun ω => Z ω ^ 2) 2 μ := by
    convert! hsg.quadratic_memLp_two (Matrix.vecMulVec u u) using 1
    ext ω
    exact (outer_quadratic u (X ω)).symm
  have hYn (ω : Ω) : 0 ≤ Y ω := Finset.sum_nonneg fun i _ => mul_nonneg (hb i) (sq_nonneg _)
  have hbs : 0 ≤ ∑ i, b i := Finset.sum_nonneg fun i _ => hb i
  have hlefti : Integrable (fun ω => h ^ 2 * Z ω ^ 4 +
      (6*h*j)*(Z ω ^ 2*Y ω) + 3*j^2*Y ω^2) μ := by
    have hi4 : Integrable (fun ω => Z ω ^ 4) μ := hsg.directional_integrable_pow u 4
    exact ((hi4.const_mul _).add ((hZ2.integrable_mul hY).const_mul _)).add
      (hY.integrable_sq.const_mul _)
  have hbound :
      (∫⁻ ω, ENNReal.ofReal (h ^ 2 * Z ω ^ 4 + (6*h*j)*(Z ω ^ 2*Y ω) +
        3*j^2*Y ω^2) ∂μ) ≤
      ENNReal.ofReal (3 * (h ^ 2 + 2*h*j*(∑ i, b i) +
        j ^ 2 * ((∑ i, b i)^2 + 2*∑ i, b i ^ 2))) := by
    calc
      _ = ∫⁻ ω, ∫⁻ g, ENNReal.ofReal (F ω g) ∂standardGaussian ι ∂μ := by
        apply lintegral_congr
        intro ω
        exact (hid ω).symm
      _ = ∫⁻ g, ∫⁻ ω, ENNReal.ofReal (F ω g) ∂μ ∂standardGaussian ι :=
        lintegral_lintegral_swap hFmeas.ennreal_ofReal.aemeasurable
      _ ≤ ∫⁻ g, ENNReal.ofReal (3 * (h + j * Q g)^2) ∂standardGaussian ι :=
        lintegral_mono hinner
      _ = _ := by
        have hQi : Integrable Q (standardGaussian ι) := by
          dsimp [Q]
          exact integrable_finsetSum _ (fun i _ =>
            (by
              have hi := standardGaussian_linear_pow_integrable (Pi.single i (1 : ℝ)) 2
              simpa [Pi.single_apply] using hi.const_mul (b i)))
        have hQ2i := standardGaussian_quadratic_sq_integrable b
        have hQmean : (∫ g, Q g ∂standardGaussian ι) = ∑ i, b i := by
          dsimp [Q]
          rw [integral_finsetSum]
          · simp only [integral_const_mul]
            have hc (i : ι) : (∫ g, g i ^ 2 ∂standardGaussian ι) = 1 := by
              simpa [Pi.single_apply] using (standardGaussian_linear_moments (Pi.single i (1 : ℝ))).1
            simp only [hc, mul_one]
          · intro i _
            have hi := standardGaussian_linear_pow_integrable (Pi.single i 1) 2
            simpa [Pi.single_apply] using hi.const_mul (b i)
        have hi : Integrable (fun g => 3*(h+j*Q g)^2) (standardGaussian ι) := by
          convert! (((integrable_const (h^2)).add (hQi.const_mul (2*h*j))).add
            (hQ2i.const_mul (j^2))).const_mul 3 using 1
          funext g
          dsimp [Q]
          ring
        rw [← ofReal_integral_eq_lintegral_ofReal hi
          (Filter.Eventually.of_forall (fun _ => by positivity))]
        congr 1
        have he (g : ι → ℝ) : 3*(h+j*Q g)^2 =
            3 * (h^2 + 2*h*j*Q g + j^2*Q g^2) := by ring
        simp_rw [he]
        rw [integral_const_mul, integral_add
          (f := fun g => h^2+2*h*j*Q g) (g := fun g => j^2*Q g^2)
          ((integrable_const _).add (hQi.const_mul _)) (hQ2i.const_mul _),
          integral_add (f := fun _ => h^2) (g := fun g => 2*h*j*Q g)
            (integrable_const _) (hQi.const_mul _)]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
          integral_const_mul, hQmean, Q, standardGaussian_quadratic_second]
  rw [← ofReal_integral_eq_lintegral_ofReal hlefti
    (Filter.Eventually.of_forall (fun ω => by have := hYn ω; positivity))] at hbound
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hbound
  rw [integral_add (f := fun ω => h^2*Z ω^4+(6*h*j)*(Z ω^2*Y ω))
      (g := fun ω => 3*j^2*Y ω^2)
      (((hsg.directional_integrable_pow u 4).const_mul _).add
        ((hZ2.integrable_mul hY).const_mul _)) (hY.integrable_sq.const_mul _),
    integral_add (f := fun ω => h^2*Z ω^4) (g := fun ω => (6*h*j)*(Z ω^2*Y ω))
      ((hsg.directional_integrable_pow u 4).const_mul _)
      ((hZ2.integrable_mul hY).const_mul _)] at hreal
  simp only [integral_const_mul] at hreal
  exact hreal

/-- Basis-free orthogonal Gaussian averaging. Only `B u = 0` is assumed;
there is no simultaneous diagonalization of other matrices. -/
theorem endpoint_orthogonal_quartic_raw (hsg : SubGaussianMGF μ X 1)
    (hiso : CentredIsotropic μ X) (u : ι → ℝ) (B : Matrix ι ι ℝ)
    (hu : u ⬝ᵥ u = 1) (hB : B.PosSemidef) (hBu : B *ᵥ u = 0)
    {h j : ℝ} (hh : 0 ≤ h) (hj : 0 ≤ j) :
    h ^ 2 * (∫ ω, (u ⬝ᵥ X ω) ^ 4 ∂μ) +
      6*h*j * (∫ ω, (u ⬝ᵥ X ω)^2 * quadraticForm B X ω ∂μ) +
      3*j^2 * (∫ ω, quadraticForm B X ω ^ 2 ∂μ) ≤
      3 * (h^2 + 2*h*j*Matrix.trace B +
        j^2 * (Matrix.trace B ^ 2 + 2 * Matrix.trace (B^2))) := by
  let U := hB.isHermitian.eigenvectorUnitary
  let b := hB.isHermitian.eigenvalues
  let ur := star (U : Matrix ι ι ℝ) *ᵥ u
  let XR := fun ω => star (U : Matrix ι ι ℝ) *ᵥ X ω
  have hud (x : ι → ℝ) : ur ⬝ᵥ (star (U : Matrix ι ι ℝ) *ᵥ x) = u ⬝ᵥ x := by
    rw [dot_unitary_star_mulVec]
    dsimp only [ur]
    rw [Matrix.mulVec_mulVec, U.2.2, Matrix.one_mulVec]
  have hur : ur ⬝ᵥ ur = 1 := (hud u).trans hu
  have hbr : Matrix.diagonal b *ᵥ ur = 0 := by
    have he := congrArg (fun v => star (U : Matrix ι ι ℝ) *ᵥ v) hBu
    rw [real_spectral_decomposition hB.isHermitian] at he
    dsimp only [U] at he
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      hB.isHermitian.eigenvectorUnitary.2.1, one_mul, Matrix.mulVec_zero] at he
    simpa only [b, ur, Matrix.mulVec_mulVec] using he
  have hub (i : ι) : b i * ur i = 0 := by
    have hi := congrFun hbr i
    simpa only [Matrix.mulVec_diagonal, Pi.zero_apply] using hi
  have hq (ω : Ω) : quadraticForm B X ω = ∑ i, b i * XR ω i ^ 2 := by
    dsimp only [quadraticForm]
    rw [real_spectral_decomposition hB.isHermitian, quadratic_conjugate_diagonal]
    simp only [U, b, XR, mul_comm]
  have he := endpoint_diagonal_quartic (hsg.unitary U) (hiso.unitary U)
    ur b hur hB.eigenvalues_nonneg hub hh hj
  have hq' (ω : Ω) : (∑ i, b i * (star (U : Matrix ι ι ℝ) *ᵥ X ω) i ^ 2) =
      quadraticForm B X ω := (hq ω).symm
  simp_rw [hq', hud] at he
  simpa only [real_spectral_trace hB.isHermitian,
    real_spectral_trace_square hB.isHermitian, b] using he

/-- The retained cumulant inequality in supplementary S1.5. -/
theorem endpoint_orthogonal_quartic (hsg : SubGaussianMGF μ X 1)
    (hiso : CentredIsotropic μ X) (u : ι → ℝ) (B : Matrix ι ι ℝ)
    (hu : u ⬝ᵥ u = 1) (hB : B.PosSemidef) (hBu : B *ᵥ u = 0)
    {h j : ℝ} (hh : 0 ≤ h) (hj : 0 ≤ j) :
    0 ≤ (2 - quadraticCovariance μ X (Matrix.vecMulVec u u) (Matrix.vecMulVec u u)) * h^2 -
      6 * quadraticCovariance μ X (Matrix.vecMulVec u u) B * h*j +
      3 * (2*Matrix.trace (B^2) - quadraticCovariance μ X B B) * j^2 := by
  have he := endpoint_orthogonal_quartic_raw hsg hiso u B hu hB hBu hh hj
  have ht : Matrix.trace (Matrix.vecMulVec u u) = 1 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply] 
    exact hu
  have hq (ω : Ω) : quadraticForm (Matrix.vecMulVec u u) X ω = (u ⬝ᵥ X ω)^2 :=
    outer_quadratic u (X ω)
  rw [quadraticCovariance_eq_mixed hsg hiso,
    quadraticCovariance_eq_mixed hsg hiso,
    quadraticCovariance_eq_mixed hsg hiso, ht]
  simp_rw [hq, ← pow_two, ← pow_mul] 
  norm_num only [show 2*2=4 from rfl]
  nlinarith only [he]

end
end SingularValueBounds.KL
