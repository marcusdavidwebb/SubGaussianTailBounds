import SingularValueBounds.KL.Certificates.EndpointMeanPolynomialIdentity
import SingularValueBounds.KL.Certificates.IntegerCoefficientStages
/-! Exact affine coefficients and Bernstein signs for endpoint mean rectangles. -/
open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 20000

private theorem endpoint_mean_box_57_37 :
    BoxCertificate (endpointMeanTestQ 57 37) 4 1 (endpointMeanBox 57 37) := by
  have hd : endpointBilinearCoefficients 57 37 = ![(426803032757/133343750000), (-196807968/66671875), (-4013823717/3333593750), (43707648/13334375)] := by decide +kernel
  have hh : endpointMeanChoice 57 37 = 3 := by rfl
  have hb : endpointMeanBox 57 37 = ⟨(456533/512000), (9/10), (77/80), (39/40)⟩ := by
    norm_num [endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
  rw [endpointMeanTestQ_eq, hd, hh, hb, endpointMeanPolynomial_identity_3]
  let xAffine : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(27305716411706711121706991/13743895347200000000000000), (269952193210210473582609/3435973836800000000000000), (2274534644322802663373/6871947673600000000000000), (10453850854539681809/3435973836800000000000000), (222440105101508591/13743895347200000000000000)],
    ![(-10741659/6250000), (-170733/6250000), (0/1), (0/1), (0/1)]]) l k
  let xBernstein : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(4570351890405124382506991/13743895347200000000000000), (23193175922701490227/67108864000000000000), (5642316222093407/15728640000000000), (95208519969/256000000000), (19257223/50000000)],
    ![(-10741659/500000000), (-43137369/2000000000), (-21654051/1000000000), (-8695767/400000000), (-1364049/62500000)]]) l k
  let coefficients : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(4570351890405124382506991/13743895347200000000000000), (179610538564140815982609/3435973836800000000000000), (2274534644322802663373/6871947673600000000000000), (10453850854539681809/3435973836800000000000000), (222440105101508591/13743895347200000000000000)],
    ![(-10741659/500000000), (-170733/500000000), (0/1), (0/1), (0/1)]]) l k
  apply boxCertificate_of_tensorStages 4 1 _ xAffine coefficients xBernstein _ (by norm_num) (by norm_num)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private theorem endpoint_mean_box_57_38 :
    BoxCertificate (endpointMeanTestQ 57 38) 4 1 (endpointMeanBox 57 38) := by
  have hd : endpointBilinearCoefficients 57 38 = ![(642325881/200000000), (-14501049/5000000), (-3031987/2500000), (251688/78125)] := by decide +kernel
  have hh : endpointMeanChoice 57 38 = 3 := by rfl
  have hb : endpointMeanBox 57 38 = ⟨(9/10), (37/40), (77/80), (39/40)⟩ := by
    norm_num [endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
  rw [endpointMeanTestQ_eq, hd, hh, hb, endpointMeanPolynomial_identity_3]
  let xAffine : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(401656983/200000000), (47280449/200000000), (48983/16000000), (671/8000000), (671/512000000)],
    ![(-21083137/12500000), (-31461/390625), (0/1), (0/1), (0/1)]]) l k
  let xBernstein : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(192441683/500000000), (339683161/800000000), (5578017313/12000000000), (2022387237/4000000000), (35002389123/64000000000)],
    ![(-21083137/1000000000), (-853393/40000000), (-21586513/1000000000), (-21838201/1000000000), (-22089889/1000000000)]]) l k
  let coefficients : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(192441683/500000000), (158882341/1000000000), (48983/16000000), (671/8000000), (671/512000000)],
    ![(-21083137/1000000000), (-31461/31250000), (0/1), (0/1), (0/1)]]) l k
  apply boxCertificate_of_tensorStages 4 1 _ xAffine coefficients xBernstein _ (by norm_num) (by norm_num)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private theorem endpoint_mean_box_57_39 :
    BoxCertificate (endpointMeanTestQ 57 39) 4 1 (endpointMeanBox 57 39) := by
  have hd : endpointBilinearCoefficients 57 39 = ![(3224420213/1000000000), (-70419203/25000000), (-15272789/12500000), (48918/15625)] := by decide +kernel
  have hh : endpointMeanChoice 57 39 = 3 := by rfl
  have hb : endpointMeanBox 57 39 = ⟨(37/40), (19/20), (77/80), (39/40)⟩ := by
    norm_num [endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
  rw [endpointMeanTestQ_eq, hd, hh, hb, endpointMeanPolynomial_identity_3]
  let xAffine : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(138103002947/64000000000), (3851135123/16000000000), (850157/256000000), (11407/128000000), (671/512000000)],
    ![(-20926531/12500000), (-24459/312500), (0/1), (0/1), (0/1)]]) l k
  let xBernstein : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(34977058179/64000000000), (18811426891/32000000000), (6045610889/9600000000), (5377767561/8000000000), (2861160451/4000000000)],
    ![(-20926531/1000000000), (-21171121/1000000000), (-21415711/1000000000), (-21660301/1000000000), (-21904891/1000000000)]]) l k
  let coefficients : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(34977058179/64000000000), (2645795603/16000000000), (850157/256000000), (11407/128000000), (671/512000000)],
    ![(-20926531/1000000000), (-24459/25000000), (0/1), (0/1), (0/1)]]) l k
  apply boxCertificate_of_tensorStages 4 1 _ xAffine coefficients xBernstein _ (by norm_num) (by norm_num)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private theorem endpoint_mean_box_57_40 :
    BoxCertificate (endpointMeanTestQ 57 40) 4 1 (endpointMeanBox 57 40) := by
  have hd : endpointBilinearCoefficients 57 40 = ![(3237560437/1000000000), (-4280119/1562500), (-7695551/6250000), (47598/15625)] := by decide +kernel
  have hh : endpointMeanChoice 57 40 = 3 := by rfl
  have hb : endpointMeanBox 57 40 = ⟨(19/20), (39/40), (77/80), (39/40)⟩ := by
    norm_num [endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
  rw [endpointMeanTestQ_eq, hd, hh, hb, endpointMeanPolynomial_identity_3]
  let xAffine : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(1852167307/800000000), (491346183/2000000000), (230153/64000000), (6039/64000000), (671/512000000)],
    ![(-10391689/6250000), (-23799/312500), (0/1), (0/1), (0/1)]]) l k
  let xBernstein : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(2859556111/4000000000), (1212771313/1600000000), (38480374573/48000000000), (27071674129/32000000000), (57020992627/64000000000)],
    ![(-10391689/500000000), (-2627671/125000000), (-10629679/500000000), (-5374337/250000000), (-10867669/500000000)]]) l k
  let coefficients : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(2859556111/4000000000), (344744343/2000000000), (230153/64000000), (6039/64000000), (671/512000000)],
    ![(-10391689/500000000), (-23799/25000000), (0/1), (0/1), (0/1)]]) l k
  apply boxCertificate_of_tensorStages 4 1 _ xAffine coefficients xBernstein _ (by norm_num) (by norm_num)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private theorem endpoint_mean_box_57_41 :
    BoxCertificate (endpointMeanTestQ 57 41) 4 1 (endpointMeanBox 57 41) := by
  have hd : endpointBilinearCoefficients 57 41 = ![(1625388337/500000000), (-66663271/25000000), (-3102171/2500000), (231787/78125)] := by decide +kernel
  have hh : endpointMeanChoice 57 41 = 3 := by rfl
  have hb : endpointMeanBox 57 41 = ⟨(39/40), (1/1), (77/80), (39/40)⟩ := by
    norm_num [endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
  rw [endpointMeanTestQ_eq, hd, hh, hb, endpointMeanPolynomial_identity_3]
  let xAffine : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(31749518231/12800000000), (4021360961/16000000000), (995093/256000000), (12749/128000000), (671/512000000)],
    ![(-20647917/12500000), (-231787/3125000), (0/1), (0/1), (0/1)]]) l k
  let xBernstein : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(56994656179/64000000000), (14968442701/16000000000), (5886970091/6000000000), (4109873769/4000000000), (1074474161/1000000000)],
    ![(-20647917/1000000000), (-2609963/125000000), (-21111491/1000000000), (-10671639/500000000), (-4315013/200000000)]]) l k
  let coefficients : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(56994656179/64000000000), (23032917/128000000), (995093/256000000), (12749/128000000), (671/512000000)],
    ![(-20647917/1000000000), (-231787/250000000), (0/1), (0/1), (0/1)]]) l k
  apply boxCertificate_of_tensorStages 4 1 _ xAffine coefficients xBernstein _ (by norm_num) (by norm_num)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

theorem endpointMeanPolynomial_row57 (ai : Fin 42) :
    endpointMeanActive 57 ai → ∃ n m, BoxCertificate (endpointMeanTestQ 57 ai) n m (endpointMeanBox 57 ai) := by
  fin_cases ai
  · intro h
    have hn : ¬ endpointMeanActive 57 0 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 1 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 2 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 3 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 4 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 5 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 6 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 7 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 8 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 9 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 10 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 11 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 12 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 13 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 14 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 15 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 16 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 17 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 18 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 19 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 20 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 21 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 22 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 23 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 24 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 25 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 26 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 27 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 28 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 29 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 30 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 31 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 32 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 33 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 34 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 35 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 57 36 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · exact fun _ => ⟨4, 1, endpoint_mean_box_57_37⟩
  · exact fun _ => ⟨4, 1, endpoint_mean_box_57_38⟩
  · exact fun _ => ⟨4, 1, endpoint_mean_box_57_39⟩
  · exact fun _ => ⟨4, 1, endpoint_mean_box_57_40⟩
  · exact fun _ => ⟨4, 1, endpoint_mean_box_57_41⟩

end SingularValueBounds.KL.Certificates
