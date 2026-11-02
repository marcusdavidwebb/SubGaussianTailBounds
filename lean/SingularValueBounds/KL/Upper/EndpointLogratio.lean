import SingularValueBounds.KL.Upper.CertificateBridges

/-! # Concentrated-spectrum logarithmic ratio (supplementary S1.6.4)

The sole extra premise is a finite rational tensor Bernstein certificate.
The logarithm bound, derivative and monotonicity consequences are Lean proofs.
-/
open Polynomial Set
open scoped Polynomial BigOperators
namespace SingularValueBounds.KL
open Certificates
noncomputable section
set_option maxHeartbeats 1500000

def endpointLogratioZ (A x : ℝ) : ℝ := (12/5 : ℝ)*(x+A*x^2-2*x^3)

def endpointLogratioZQ : Polynomial (Polynomial ℚ) :=
  C (C (12/5))*(X+C X*X^2-2*X^3)

def endpointLogratioZDerivativeQ : Polynomial (Polynomial ℚ) :=
  C (C (12/5))*(1+2*C X*X-6*X^2)

def endpointLogratioCleared : Polynomial (Polynomial ℚ) :=
  X*endpointLogratioZDerivativeQ*endpointLogratioZQ*padeDQ endpointLogratioZQ-
    2*(padeNQ endpointLogratioZQ-endpointLogratioZQ*padeDQ endpointLogratioZQ)*
      (1-endpointLogratioZQ)

def endpointLogratioBox : RationalBox := ⟨1/2,1,0,7/20⟩

def EndpointLogratioCertificateConditions : Prop :=
  BoxCertificate endpointLogratioCleared 6 18 endpointLogratioBox

theorem endpointLogratioCleared_eval (A x : ℝ) :
    realEval₂ endpointLogratioCleared A x =
      x*((12/5 : ℝ)*(1+2*A*x-6*x^2))*endpointLogratioZ A x*
        upperPadeD (endpointLogratioZ A x)-
      2*(upperPadeN (endpointLogratioZ A x)-endpointLogratioZ A x*
        upperPadeD (endpointLogratioZ A x))*(1-endpointLogratioZ A x) := by
  simp only [realEval₂,endpointLogratioCleared,endpointLogratioZQ,
    endpointLogratioZDerivativeQ,padeDQ,padeNQ,Polynomial.eval₂_mul,
    Polynomial.eval₂_add,Polynomial.eval₂_sub,Polynomial.eval₂_C,
    Polynomial.eval₂_X,Polynomial.eval₂_pow,Polynomial.eval₂_one,
    Polynomial.coe_eval₂RingHom]
  norm_num [endpointLogratioZ,upperPadeD,upperPadeN]

/-- The normalized comparison cubic is increasing throughout the small-coordinate interval. -/
theorem upper_comparison_cubic_monotone {A : ℝ} (hA : 0≤A) :
    MonotoneOn (fun x : ℝ => x+A*x^2-2*x^3) (Icc 0 (7/20)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · fun_prop
  · fun_prop
  · intro x hx
    have hx' : x∈Icc (0 : ℝ) (7/20) := interior_subset hx
    have hd : HasDerivAt (fun x : ℝ => x+A*x^2-2*x^3) (1+2*A*x-6*x^2) x := by
      convert! ((hasDerivAt_id x).add (((hasDerivAt_id x).pow 2).const_mul A)).sub
        (((hasDerivAt_id x).pow 3).const_mul 2) using 1 <;> simp only [id_eq] <;> ring
    rw [hd.deriv]
    have hx2 := pow_le_pow_left₀ hx'.1 hx'.2 2
    nlinarith [mul_nonneg hA hx'.1]

theorem endpointLogratioZ_bounds {A x : ℝ} (hA : A∈Icc (1/2 : ℝ) 1)
    (hx : x∈Icc (0 : ℝ) (7/20)) :
    0≤endpointLogratioZ A x ∧ endpointLogratioZ A x<1 := by
  have hmono := upper_comparison_cubic_monotone
    (show 0 ≤ A from (by norm_num : (0 : ℝ) ≤ 1/2).trans hA.1)
  have hl := hmono ⟨le_rfl,by norm_num⟩ hx hx.1
  have hh := hmono hx ⟨by norm_num,le_rfl⟩ hx.2
  norm_num at hl hh
  dsimp [endpointLogratioZ]
  constructor
  · linarith
  · nlinarith [hA.2]

def endpointLogratio (A x : ℝ) : ℝ :=
  (-Real.log (1-endpointLogratioZ A x)-endpointLogratioZ A x)/x^2

theorem endpointLogratio_monotone (hcert : EndpointLogratioCertificateConditions)
    {A : ℝ} (hA : A∈Icc (1/2 : ℝ) 1) :
    MonotoneOn (endpointLogratio A) (Ioc (0 : ℝ) (7/20)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioc _ _)
  · apply ContinuousOn.div
    · apply ContinuousOn.sub
      · apply ContinuousOn.neg
        apply ContinuousOn.log (by dsimp [endpointLogratioZ]; fun_prop)
        intro x hx
        exact ne_of_gt (by linarith [(endpointLogratioZ_bounds hA ⟨hx.1.le,hx.2⟩).2])
      · have hC : Continuous (endpointLogratioZ A) := by
          unfold endpointLogratioZ
          fun_prop
        exact hC.continuousOn
    · fun_prop
    · intro x hx
      exact pow_ne_zero 2 hx.1.ne'
  · intro x hx
    have hx' : x∈Ioc (0 : ℝ) (7/20) := interior_subset hx
    have hg := endpointLogratioZ_bounds hA ⟨hx'.1.le,hx'.2⟩
    have hh : 1-endpointLogratioZ A x≠0 := ne_of_gt (by linarith)
    have hxne : x≠0 := hx'.1.ne'
    apply DifferentiableAt.differentiableWithinAt
    unfold endpointLogratio
    apply DifferentiableAt.div
    · apply DifferentiableAt.sub
      · apply DifferentiableAt.neg
        exact (show DifferentiableAt ℝ (fun y : ℝ => 1-endpointLogratioZ A y) x by
          unfold endpointLogratioZ
          fun_prop).log hh
      · unfold endpointLogratioZ
        fun_prop
    · fun_prop
    · exact pow_ne_zero 2 hxne
  · intro x hx
    have hx' : x∈Ioc (0 : ℝ) (7/20) := interior_subset hx
    have hg := endpointLogratioZ_bounds hA ⟨hx'.1.le,hx'.2⟩
    let z := endpointLogratioZ A x
    let zp := (12/5 : ℝ)*(1+2*A*x-6*x^2)
    have hz : 1-z≠0 := ne_of_gt (by dsimp [z]; linarith)
    have hdZ : HasDerivAt (endpointLogratioZ A) zp x := by
      convert! (((hasDerivAt_id x).add (((hasDerivAt_id x).pow 2).const_mul A)).sub
        (((hasDerivAt_id x).pow 3).const_mul 2)).const_mul (12/5 : ℝ) using 1 <;>
        dsimp [endpointLogratioZ,zp] <;> ring
    have hd := ((((hasDerivAt_const x 1).sub hdZ).log hz).neg.sub hdZ).div
      ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx'.1.ne')
    have hd' : HasDerivAt (endpointLogratio A)
        (((zp/(1-z)-zp)*x^2-(-Real.log (1-z)-z)*(2*x))/(x^2)^2) x := by
      simpa only [endpointLogratio,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,
        mul_one,zero_sub,neg_div,neg_neg,Pi.sub_apply,Pi.neg_apply,Pi.pow_apply,
        Pi.div_apply] using! hd
    rw [hd'.deriv]
    have hP := hcert.nonneg (show endpointLogratioBox.contains A x by
      simpa [endpointLogratioBox,RationalBox.contains] using
        (show A∈Icc (1/2 : ℝ) 1 ∧ 0≤x ∧ x≤7/20 from ⟨hA,hx'.1.le,hx'.2⟩))
    rw [endpointLogratioCleared_eval] at hP
    change 0≤x*zp*z*upperPadeD z-2*(upperPadeN z-z*upperPadeD z)*(1-z) at hP
    have hD : 0<upperPadeD z := upperPadeD_pos (by exact hg.2)
    have hlog := neg_log_one_sub_le_upperPade (by exact hg.2)
    have hzpos : 0<1-z := by dsimp [z]; linarith
    have hmul := mul_le_mul_of_nonneg_right hlog (mul_nonneg hD.le hzpos.le)
    have hclear : (-Real.log (1-z)-z)*(upperPadeD z*(1-z))≤
        (upperPadeN z-z*upperPadeD z)*(1-z) := by
      have hdc : upperPadeN z/upperPadeD z*upperPadeD z=upperPadeN z :=
        div_mul_cancel₀ _ hD.ne'
      nlinarith
    have hnum : 0≤x*zp*z-2*(-Real.log (1-z)-z)*(1-z) := by
      apply nonneg_of_mul_nonneg_left (b := upperPadeD z) _ hD
      nlinarith
    apply div_nonneg _ (sq_nonneg _)
    apply nonneg_of_mul_nonneg_left (b := 1-z) _ hzpos
    have hn := mul_nonneg hx'.1.le hnum
    convert! hn using 1
    field_simp [hz]
    <;> ring

end
end SingularValueBounds.KL
