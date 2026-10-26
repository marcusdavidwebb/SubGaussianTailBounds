import SingularValueBounds.KL.Certificates.EndpointMeanPolynomialIdentity
import SingularValueBounds.KL.Certificates.IntegerCoefficientStages
/-! Exact affine coefficients and Bernstein signs for endpoint mean rectangles. -/
open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 20000

private theorem endpoint_mean_box_59_40 :
    BoxCertificate (endpointMeanTestQ 59 40) 4 1 (endpointMeanBox 59 40) := by
  have hd : endpointBilinearCoefficients 59 40 = ![(20845708589289/6161000000000), (-289492168/96265625), (-50351817211/38506250000), (62464384/19253125)] := by decide +kernel
  have hh : endpointMeanChoice 59 40 = 3 := by rfl
  have hb : endpointMeanBox 59 40 = ⟨(493039/512000), (39/40), (79/80), (1/1)⟩ := by
    norm_num [endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
  rw [endpointMeanTestQ_eq, hd, hh, hb, endpointMeanPolynomial_identity_3]
  let xAffine : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(35125317744431654724770911/13743895347200000000000000), (423676852713831264745889/3435973836800000000000000), (5962432826234021531933/6871947673600000000000000), (37195975489625859489/3435973836800000000000000), (966779327416943711/13743895347200000000000000)],
    ![(-4541499/2500000), (-488003/12500000), (0/1), (0/1), (0/1)]]) l k
  let xBernstein : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(10470252389143340868770911/13743895347200000000000000), (840739434701176500931/1073741824000000000000), (202416954653604533/251658240000000000), (27060244424439/32768000000000), (54236392051/64000000000)],
    ![(-4541499/200000000), (-91317983/4000000000), (-45902993/2000000000), (-92293989/4000000000), (-11597749/500000000)]]) l k
  let coefficients : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(10470252389143340868770911/13743895347200000000000000), (291212375031718343145889/3435973836800000000000000), (5962432826234021531933/6871947673600000000000000), (37195975489625859489/3435973836800000000000000), (966779327416943711/13743895347200000000000000)],
    ![(-4541499/200000000), (-488003/1000000000), (0/1), (0/1), (0/1)]]) l k
  apply boxCertificate_of_tensorStages 4 1 _ xAffine coefficients xBernstein _ (by norm_num) (by norm_num)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private theorem endpoint_mean_box_59_41 :
    BoxCertificate (endpointMeanTestQ 59 41) 4 1 (endpointMeanBox 59 41) := by
  have hd : endpointBilinearCoefficients 59 41 = ![(3407095901/1000000000), (-74428287/25000000), (-4154947/3125000), (501873/156250)] := by decide +kernel
  have hh : endpointMeanChoice 59 41 = 3 := by rfl
  have hb : endpointMeanBox 59 41 = ⟨(39/40), (1/1), (79/80), (1/1)⟩ := by
    norm_num [endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
  rw [endpointMeanTestQ_eq, hd, hh, hb, endpointMeanPolynomial_identity_3]
  let xAffine : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(168124640563/64000000000), (4145601217/16000000000), (995093/256000000), (12749/128000000), (671/512000000)],
    ![(-11263153/6250000), (-501873/6250000), (0/1), (0/1), (0/1)]]) l k
  let xBernstein : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(54231637427/64000000000), (571085037/640000000), (5627515517/6000000000), (3936763531/4000000000), (1031161471/1000000000)],
    ![(-11263153/500000000), (-9110897/400000000), (-23028179/1000000000), (-46558231/2000000000), (-5882513/250000000)]]) l k
  let coefficients : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(54231637427/64000000000), (2876866273/16000000000), (995093/256000000), (12749/128000000), (671/512000000)],
    ![(-11263153/500000000), (-501873/500000000), (0/1), (0/1), (0/1)]]) l k
  apply boxCertificate_of_tensorStages 4 1 _ xAffine coefficients xBernstein _ (by norm_num) (by norm_num)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

theorem endpointMeanPolynomial_row59 (ai : Fin 42) :
    endpointMeanActive 59 ai → ∃ n m, BoxCertificate (endpointMeanTestQ 59 ai) n m (endpointMeanBox 59 ai) := by
  fin_cases ai
  · intro h
    have hn : ¬ endpointMeanActive 59 0 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 1 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 2 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 3 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 4 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 5 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 6 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 7 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 8 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 9 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 10 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 11 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 12 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 13 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 14 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 15 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 16 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 17 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 18 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 19 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 20 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 21 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 22 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 23 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 24 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 25 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 26 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 27 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 28 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 29 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 30 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 31 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 32 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 33 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 34 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 35 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 36 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 37 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 38 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 59 39 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · exact fun _ => ⟨4, 1, endpoint_mean_box_59_40⟩
  · exact fun _ => ⟨4, 1, endpoint_mean_box_59_41⟩

end SingularValueBounds.KL.Certificates
