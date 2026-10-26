import SingularValueBounds.KL.Certificates.EndpointMeanPolynomialIdentity
import SingularValueBounds.KL.Certificates.EndpointPolynomialStages
/-! Exact affine coefficients and Bernstein signs for endpoint mean rectangles. -/
open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 20000

private theorem endpoint_mean_box_58_39 :
    BoxCertificate (endpointMeanTestQ 58 39) 8 16 (endpointMeanBox 58 39) := by
  have hd : endpointBilinearCoefficients 58 39 = ![(4808260571281/1481000000000), (-65872981/23140625), (-11156762349/9256250000), (577616/185125)] := by decide +kernel
  have hh : endpointMeanChoice 58 39 = 3 := by rfl
  have hb : endpointMeanBox 58 39 = ⟨(59319/64000), (19/20), (39/40), (79/80)⟩ := by
    norm_num [endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
  rw [endpointMeanTestQ_eq, hd, hh, hb, endpointMeanPolynomial_identity_3]
  let xAffine : Fin 9 → Fin 17 → ℚ :=
    fun k l => (![![(7319073501197817864191/3355443200000000000000), (187857850341745659009/838860800000000000000), (4802280085587973373/1677721600000000000000), (59545986397185409/838860800000000000000), (3228068591611391/3355443200000000000000), (0/1), (0/1), (0/1), (0/1)],
    ![(-21082617/12500000), (-36101/500000), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)]]) l k
  let xBernstein : Fin 9 → Fin 17 → ℚ :=
    fun k l => (![![(1801234640831174664191/3355443200000000000000), (3731273890209534987391/6710886400000000000000), (3860764538768947499739/6710886400000000000000), (27936648137370505243391/46976204800000000000000), (144264332605152393275391/234881024000000000000000), (9304396174867620801/14680064000000000000), (428296782028959/655360000000000), (689515585289/1024000000000), (2773164567/4000000000)],
    ![(-21082617/1000000000), (-169563461/8000000000), (-85232993/4000000000), (-171368511/8000000000), (-43067759/2000000000), (-173173561/8000000000), (-87038043/4000000000), (-174978611/8000000000), (-10992571/500000000)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)]]) l k
  let coefficients : Fin 9 → Fin 17 → ℚ :=
    fun k l => (![![(1801234640831174664191/3355443200000000000000), (128804608547185659009/838860800000000000000), (4802280085587973373/1677721600000000000000), (59545986397185409/838860800000000000000), (3228068591611391/3355443200000000000000), (0/1), (0/1), (0/1), (0/1)],
    ![(-21082617/1000000000), (-36101/40000000), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)]]) l k
  apply boxCertificate_of_tensorStages 8 16 _ xAffine coefficients xBernstein _ (by norm_num) (by norm_num)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private theorem endpoint_mean_box_58_40 :
    BoxCertificate (endpointMeanTestQ 58 40) 8 16 (endpointMeanBox 58 40) := by
  have hd : endpointBilinearCoefficients 58 40 = ![(3262053619/1000000000), (-69434229/25000000), (-3043577/2500000), (951717/312500)] := by decide +kernel
  have hh : endpointMeanChoice 58 40 = 3 := by rfl
  have hb : endpointMeanBox 58 40 = ⟨(19/20), (39/40), (39/40), (79/80)⟩ := by
    norm_num [endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
  rw [endpointMeanTestQ_eq, hd, hh, hb, endpointMeanPolynomial_identity_3]
  let xAffine : Fin 9 → Fin 17 → ℚ :=
    fun k l => (![![(9307617207/4000000000), (493250833/2000000000), (230153/64000000), (6039/64000000), (671/512000000), (0/1), (0/1), (0/1), (0/1)],
    ![(-20947361/12500000), (-951717/12500000), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)]]) l k
  let xBernstein : Fin 9 → Fin 17 → ℚ :=
    fun k l => (![![(110881623/160000000), (11432945281/16000000000), (23559566399/32000000000), (339603684429/448000000000), (698864991319/896000000000), (143728453971/179200000000), (738540764541/896000000000), (108366007461/128000000000), (55621980467/64000000000)],
    ![(-20947361/1000000000), (-33706121/1600000000), (-84741161/4000000000), (-170434039/8000000000), (-42846439/2000000000), (-172337473/8000000000), (-17328919/800000000), (-174240907/8000000000), (-10949539/500000000)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)]]) l k
  let coefficients : Fin 9 → Fin 17 → ℚ :=
    fun k l => (![![(110881623/160000000), (344782981/2000000000), (230153/64000000), (6039/64000000), (671/512000000), (0/1), (0/1), (0/1), (0/1)],
    ![(-20947361/1000000000), (-951717/1000000000), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)]]) l k
  apply boxCertificate_of_tensorStages 8 16 _ xAffine coefficients xBernstein _ (by norm_num) (by norm_num)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private theorem endpoint_mean_box_58_41 :
    BoxCertificate (endpointMeanTestQ 58 41) 8 16 (endpointMeanBox 58 41) := by
  have hd : endpointBilinearCoefficients 58 41 = ![(1639692867/500000000), (-16955507/6250000), (-15394929/12500000), (232497/78125)] := by decide +kernel
  have hh : endpointMeanChoice 58 41 = 3 := by rfl
  have hb : endpointMeanBox 58 41 = ⟨(39/40), (1/1), (39/40), (79/80)⟩ := by
    norm_num [endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
  rw [endpointMeanTestQ_eq, hd, hh, hb, endpointMeanPolynomial_identity_3]
  let xAffine : Fin 9 → Fin 17 → ℚ :=
    fun k l => (![![(159808868787/64000000000), (4039901073/16000000000), (995093/256000000), (12749/128000000), (671/512000000), (0/1), (0/1), (0/1), (0/1)],
    ![(-20874603/12500000), (-232497/3125000), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)]]) l k
  let xBernstein : Fin 9 → Fin 17 → ℚ :=
    fun k l => (![![(55602850611/64000000000), (114084977271/128000000000), (163774831973/179200000000), (839279459083/896000000000), (859812348951/896000000000), (220118614161/224000000000), (14082303533/14000000000), (411693267/400000000), (131592161/125000000)],
    ![(-20874603/1000000000), (-41981703/2000000000), (-211071/10000000), (-42446697/2000000000), (-21339597/1000000000), (-42911691/2000000000), (-10786047/500000000), (-8675337/400000000), (-21804591/1000000000)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)]]) l k
  let coefficients : Fin 9 → Fin 17 → ℚ :=
    fun k l => (![![(55602850611/64000000000), (2879276049/16000000000), (995093/256000000), (12749/128000000), (671/512000000), (0/1), (0/1), (0/1), (0/1)],
    ![(-20874603/1000000000), (-232497/250000000), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![(0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)]]) l k
  apply boxCertificate_of_tensorStages 8 16 _ xAffine coefficients xBernstein _ (by norm_num) (by norm_num)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

theorem endpointMeanPolynomial_row58 (ai : Fin 42) :
    endpointMeanActive 58 ai → BoxCertificate (endpointMeanTestQ 58 ai) 8 16 (endpointMeanBox 58 ai) := by
  fin_cases ai
  · intro h
    have hn : ¬ endpointMeanActive 58 0 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 1 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 2 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 3 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 4 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 5 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 6 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 7 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 8 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 9 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 10 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 11 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 12 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 13 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 14 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 15 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 16 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 17 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 18 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 19 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 20 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 21 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 22 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 23 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 24 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 25 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 26 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 27 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 28 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 29 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 30 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 31 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 32 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 33 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 34 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 35 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 36 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 37 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 58 38 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · exact fun _ => endpoint_mean_box_58_39
  · exact fun _ => endpoint_mean_box_58_40
  · exact fun _ => endpoint_mean_box_58_41

end SingularValueBounds.KL.Certificates
