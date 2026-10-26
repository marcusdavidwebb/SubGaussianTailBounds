import SingularValueBounds.KL.Lower.EndpointCertificates

/-!
Concrete kernel proofs for the five endpoint lower-cost interval certificates.
The rational coefficient identities and their signs are checked in Lean.
-/

open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Exact conversion of a quartic to its degree-four Bernstein expansion. -/
theorem quartic_bernstein_identity (a b c d e : ℚ) :
    C a+C b*X+C c*X^2+C d*X^3+C e*X^4 =
      bernsteinExpansion 4 (bernsteinCoefficients (C a+C b*X+C c*X^2+C d*X^3+C e*X^4) 4) := by
  norm_num [bernsteinExpansion, Fin.sum_univ_succ,
    bernsteinCoefficients, Finset.sum_range_succ,
    Polynomial.coeff_add, Polynomial.coeff_C,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_X, Nat.choose, bernsteinPolynomial]
  ring_nf
  norm_num [← map_mul, ← map_add, ← map_pow]
  ext k
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul,
    Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_mul_ofNat, ← map_mul]
  split_ifs <;> ring

private theorem endpoint_far_certificate_0 :
    IntervalCertificate (C (7/100)-endpointFarG) 0 (1/4) 4
      (bernsteinCoefficients ((C (7/100)-endpointFarG).comp (affine 0 ((1/4)-0))) 4) := by
  refine Or.inr ⟨by norm_num, ?_⟩
  have hpoly : (C (7/100)-endpointFarG).comp (affine 0 ((1/4)-0)) =
      C (7/100) + C (-1/128)*X + C (-1849/20480)*X^2 + C (399/8192)*X^3 + C (-245/65536)*X^4 := by
    norm_num [endpointFarG, endpointFarDerivative, affine, Polynomial.sub_comp,
      Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.C_comp, Polynomial.X_comp]
    ring_nf
    norm_num [← map_mul, ← map_pow]
  rw [hpoly]
  constructor
  · exact quartic_bernstein_identity (7/100) (-1/128) (-1849/20480) (399/8192) (-245/65536)
  · intro i
    fin_cases i <;> norm_num [bernsteinCoefficients, Finset.sum_range_succ,
      Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_X, Nat.choose]

private theorem endpoint_far_certificate_1 :
    IntervalCertificate (C (7/100)-endpointFarG) (1/4) (3/8) 4
      (bernsteinCoefficients ((C (7/100)-endpointFarG).comp (affine (1/4) ((3/8)-(1/4)))) 4) := by
  refine Or.inr ⟨by norm_num, ?_⟩
  have hpoly : (C (7/100)-endpointFarG).comp (affine (1/4) ((3/8)-(1/4))) =
      C (27643/1638400) + C (-4687/163840)*X + C (5473/655360)*X^2 + C (553/131072)*X^3 + C (-245/1048576)*X^4 := by
    norm_num [endpointFarG, endpointFarDerivative, affine, Polynomial.sub_comp,
      Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.C_comp, Polynomial.X_comp]
    ring_nf
    norm_num [← map_mul, ← map_pow]
    all_goals
      ext k
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg, Polynomial.coeff_mul_C,
        Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
        Polynomial.coeff_mul_ofNat, ← map_mul]
      split_ifs <;> simp_all [Polynomial.coeff_X, Polynomial.coeff_C] <;> norm_num
  rw [hpoly]
  constructor
  · exact quartic_bernstein_identity (27643/1638400) (-4687/163840) (5473/655360) (553/131072) (-245/1048576)
  · intro i
    fin_cases i <;> norm_num [bernsteinCoefficients, Finset.sum_range_succ,
      Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_X, Nat.choose]

private theorem endpoint_far_certificate_2 :
    IntervalCertificate (C (7/100)-endpointFarG) (3/8) (1/2) 4
      (bernsteinCoefficients ((C (7/100)-endpointFarG).comp (affine (3/8) ((1/2)-(3/8)))) 4) := by
  refine Or.inr ⟨by norm_num, ?_⟩
  have hpoly : (C (7/100)-endpointFarG).comp (affine (3/8) ((1/2)-(3/8))) =
      C (15763/26214400) + C (-239/1310720)*X + C (51397/2621440)*X^2 + C (861/262144)*X^3 + C (-245/1048576)*X^4 := by
    norm_num [endpointFarG, endpointFarDerivative, affine, Polynomial.sub_comp,
      Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.C_comp, Polynomial.X_comp]
    ring_nf
    norm_num [← map_mul, ← map_pow]
    all_goals
      ext k
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg, Polynomial.coeff_mul_C,
        Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
        Polynomial.coeff_mul_ofNat, ← map_mul]
      split_ifs <;> simp_all [Polynomial.coeff_X, Polynomial.coeff_C] <;> norm_num
  rw [hpoly]
  constructor
  · exact quartic_bernstein_identity (15763/26214400) (-239/1310720) (51397/2621440) (861/262144) (-245/1048576)
  · intro i
    fin_cases i <;> norm_num [bernsteinCoefficients, Finset.sum_range_succ,
      Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_X, Nat.choose]

private theorem endpoint_far_certificate_3 :
    IntervalCertificate (C (7/100)-endpointFarG) (1/2) 1 4
      (bernsteinCoefficients ((C (7/100)-endpointFarG).comp (affine (1/2) (1-(1/2)))) 4) := by
  refine Or.inr ⟨by norm_num, ?_⟩
  have hpoly : (C (7/100)-endpointFarG).comp (affine (1/2) (1-(1/2))) =
      C (2363/102400) + C (491/2560)*X + C (4597/10240)*X^2 + C (77/512)*X^3 + C (-245/4096)*X^4 := by
    norm_num [endpointFarG, endpointFarDerivative, affine, Polynomial.sub_comp,
      Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.C_comp, Polynomial.X_comp]
    ring_nf
    norm_num [← map_mul, ← map_pow]
    all_goals
      ext k
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg, Polynomial.coeff_mul_C,
        Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
        Polynomial.coeff_mul_ofNat, ← map_mul]
      split_ifs <;> simp_all [Polynomial.coeff_X, Polynomial.coeff_C] <;> norm_num
  rw [hpoly]
  constructor
  · exact quartic_bernstein_identity (2363/102400) (491/2560) (4597/10240) (77/512) (-245/4096)
  · intro i
    fin_cases i <;> norm_num [bernsteinCoefficients, Finset.sum_range_succ,
      Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_X, Nat.choose]

private theorem endpoint_far_certificate_4 :
    IntervalCertificate endpointFarDerivative (3/4) 1 4
      (bernsteinCoefficients (endpointFarDerivative.comp (affine (3/4) (1-(3/4)))) 4) := by
  refine Or.inr ⟨by norm_num, ?_⟩
  have hpoly : endpointFarDerivative.comp (affine (3/4) (1-(3/4))) =
      C (1292653/819200) + C (20097/10240)*X + C (50741/81920)*X^2 + C (-105/4096)*X^3 + C (-735/32768)*X^4 := by
    norm_num [endpointFarG, endpointFarDerivative, affine, Polynomial.sub_comp,
      Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.C_comp, Polynomial.X_comp]
    ring_nf
    norm_num [← map_mul, ← map_pow]
    all_goals
      ext k
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg, Polynomial.coeff_mul_C,
        Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
        Polynomial.coeff_mul_ofNat, ← map_mul]
      split_ifs <;> simp_all [Polynomial.coeff_X, Polynomial.coeff_C] <;> norm_num
  rw [hpoly]
  constructor
  · exact quartic_bernstein_identity (1292653/819200) (20097/10240) (50741/81920) (-105/4096) (-735/32768)
  · intro i
    fin_cases i <;> norm_num [bernsteinCoefficients, Finset.sum_range_succ,
      Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_X, Nat.choose]

/-- All four far-region boxes and the derivative interval have concrete proofs. -/
theorem endpointFarConditions : EndpointFarConditions := by
  constructor
  · intro j
    fin_cases j
    · simpa [endpointFarLo, endpointFarHi] using endpoint_far_certificate_0
    · simpa [endpointFarLo, endpointFarHi] using endpoint_far_certificate_1
    · simpa [endpointFarLo, endpointFarHi] using endpoint_far_certificate_2
    · simpa [endpointFarLo, endpointFarHi] using endpoint_far_certificate_3
  · convert endpoint_far_certificate_4 using 1
    norm_num

end SingularValueBounds.KL.Certificates
