import SingularValueBounds.KL.Certificates.EndpointMeanPolynomialIdentity
import SingularValueBounds.KL.Certificates.IntegerCoefficientStages
/-! Exact affine coefficients and Bernstein signs for endpoint mean rectangles. -/
open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 20000

private theorem endpoint_mean_box_56_36 :
    BoxCertificate (endpointMeanTestQ 56 36) 4 1 (endpointMeanBox 56 36) := by
  have hd : endpointBilinearCoefficients 56 36 = ![(9293154849/2937500000), (-1778103/587500), (-711134743/587500000), (500254/146875)] := by decide +kernel
  have hh : endpointMeanChoice 56 36 = 3 := by rfl
  have hb : endpointMeanBox 56 36 = ⟨(6859/8000), (7/8), (19/20), (77/80)⟩ := by
    norm_num [endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
  rw [endpointMeanTestQ_eq, hd, hh, hb, endpointMeanPolynomial_identity_3]
  let xAffine : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(1450020355235650031/819200000000000000), (33183334775076969/204800000000000000), (540564836388093/409600000000000000), (5377668330969/204800000000000000), (265215542031/819200000000000000)],
    ![(-427441/250000), (-750381/12500000), (0/1), (0/1), (0/1)]]) l k
  let xBernstein : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(119413619875650031/819200000000000000), (140917424461927/819200000000000), (162601417327/819200000000), (115294360087/512000000000), (16135292483/64000000000)],
    ![(-427441/20000000), (-86238581/4000000000), (-43494481/2000000000), (-87739343/4000000000), (-22122431/1000000000)]]) l k
  let coefficients : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(119413619875650031/819200000000000000), (21503804586276969/204800000000000000), (540564836388093/409600000000000000), (5377668330969/204800000000000000), (265215542031/819200000000000000)],
    ![(-427441/20000000), (-750381/1000000000), (0/1), (0/1), (0/1)]]) l k
  apply boxCertificate_of_tensorStages 4 1 _ xAffine coefficients xBernstein _ (by norm_num) (by norm_num)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private theorem endpoint_mean_box_56_37 :
    BoxCertificate (endpointMeanTestQ 56 37) 4 1 (endpointMeanBox 56 37) := by
  have hd : endpointBilinearCoefficients 56 37 = ![(794325077/250000000), (-73878329/25000000), (-15267081/12500000), (519889/156250)] := by decide +kernel
  have hh : endpointMeanChoice 56 37 = 3 := by rfl
  have hb : endpointMeanBox 56 37 = ⟨(7/8), (9/10), (19/20), (77/80)⟩ := by
    norm_num [endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
  rw [endpointMeanTestQ_eq, hd, hh, hb, endpointMeanPolynomial_identity_3]
  let xAffine : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(118863909123/64000000000), (3710381389/16000000000), (28853/10240000), (2013/25600000), (671/512000000)],
    ![(-21125149/12500000), (-519889/6250000), (0/1), (0/1), (0/1)]]) l k
  let xBernstein : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(16111184387/64000000000), (1159824733/4000000000), (3943736677/12000000000), (294258027/800000000), (50938823/125000000)],
    ![(-21125149/1000000000), (-42770187/2000000000), (-10822519/500000000), (-8761993/400000000), (-22164927/1000000000)]]) l k
  let coefficients : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(16111184387/64000000000), (2446011341/16000000000), (28853/10240000), (2013/25600000), (671/512000000)],
    ![(-21125149/1000000000), (-519889/500000000), (0/1), (0/1), (0/1)]]) l k
  apply boxCertificate_of_tensorStages 4 1 _ xAffine coefficients xBernstein _ (by norm_num) (by norm_num)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private theorem endpoint_mean_box_56_38 :
    BoxCertificate (endpointMeanTestQ 56 38) 4 1 (endpointMeanBox 56 38) := by
  have hd : endpointBilinearCoefficients 56 38 = ![(3192713777/1000000000), (-7184241/2500000), (-192711/156250), (40467/12500)] := by decide +kernel
  have hh : endpointMeanChoice 56 38 = 3 := by rfl
  have hb : endpointMeanBox 56 38 = ⟨(9/10), (37/40), (19/20), (77/80)⟩ := by
    norm_num [endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
  rw [endpointMeanTestQ_eq, hd, hh, hb, endpointMeanPolynomial_identity_3]
  let xAffine : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(2003338483/1000000000), (23573941/100000000), (48983/16000000), (671/8000000), (671/512000000)],
    ![(-1050171/625000), (-40467/500000), (0/1), (0/1), (0/1)]]) l k
  let xBernstein : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(407078563/1000000000), (893583181/2000000000), (5844178291/12000000000), (527769333/1000000000), (36420946947/64000000000)],
    ![(-1050171/50000000), (-17005071/800000000), (-8603703/400000000), (-17409741/800000000), (-4403019/200000000)]]) l k
  let coefficients : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(407078563/1000000000), (15885211/100000000), (48983/16000000), (671/8000000), (671/512000000)],
    ![(-1050171/50000000), (-40467/40000000), (0/1), (0/1), (0/1)]]) l k
  apply boxCertificate_of_tensorStages 4 1 _ xAffine coefficients xBernstein _ (by norm_num) (by norm_num)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private theorem endpoint_mean_box_56_39 :
    BoxCertificate (endpointMeanTestQ 56 39) 4 1 (endpointMeanBox 56 39) := by
  have hd : endpointBilinearCoefficients 56 39 = ![(3205804147/1000000000), (-2791557/1000000), (-7766723/6250000), (983317/312500)] := by decide +kernel
  have hh : endpointMeanChoice 56 39 = 3 := by rfl
  have hb : endpointMeanBox 56 39 = ⟨(37/40), (19/20), (19/20), (77/80)⟩ := by
    norm_num [endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
  rw [endpointMeanTestQ_eq, hd, hh, hb, endpointMeanPolynomial_identity_3]
  let xAffine : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(137801932867/64000000000), (153642027/640000000), (850157/256000000), (11407/128000000), (671/512000000)],
    ![(-20849283/12500000), (-983317/12500000), (0/1), (0/1), (0/1)]]) l k
  let xBernstein : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(7278204071/12800000000), (19518178779/32000000000), (31287838477/48000000000), (5554340933/8000000000), (2949418487/4000000000)],
    ![(-20849283/1000000000), (-84380449/4000000000), (-42681883/2000000000), (-86347083/4000000000), (-109163/5000000)]]) l k
  let coefficients : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(7278204071/12800000000), (2645337203/16000000000), (850157/256000000), (11407/128000000), (671/512000000)],
    ![(-20849283/1000000000), (-983317/1000000000), (0/1), (0/1), (0/1)]]) l k
  apply boxCertificate_of_tensorStages 4 1 _ xAffine coefficients xBernstein _ (by norm_num) (by norm_num)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private theorem endpoint_mean_box_56_40 :
    BoxCertificate (endpointMeanTestQ 56 40) 4 1 (endpointMeanBox 56 40) := by
  have hd : endpointBilinearCoefficients 56 40 = ![(804715799/250000000), (-67861641/25000000), (-7825121/6250000), (38267/12500)] := by decide +kernel
  have hh : endpointMeanChoice 56 40 = 3 := by rfl
  have hb : endpointMeanBox 56 40 = ⟨(19/20), (39/40), (19/20), (77/80)⟩ := by
    norm_num [endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
  rw [endpointMeanTestQ_eq, hd, hh, hb, endpointMeanPolynomial_identity_3]
  let xAffine : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(9241345523/4000000000), (490105657/2000000000), (230153/64000000), (6039/64000000), (671/512000000)],
    ![(-1293963/781250), (-38267/500000), (0/1), (0/1), (0/1)]]) l k
  let xBernstein : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(2947509491/4000000000), (6239710039/8000000000), (39535175701/48000000000), (27774661737/32000000000), (11685308311/12800000000)],
    ![(-1293963/62500000), (-83770307/4000000000), (-42363491/2000000000), (-85683657/4000000000), (-21660083/1000000000)]]) l k
  let coefficients : Fin 5 → Fin 2 → ℚ :=
    fun k l => (![![(2947509491/4000000000), (344691057/2000000000), (230153/64000000), (6039/64000000), (671/512000000)],
    ![(-1293963/62500000), (-38267/40000000), (0/1), (0/1), (0/1)]]) l k
  apply boxCertificate_of_tensorStages 4 1 _ xAffine coefficients xBernstein _ (by norm_num) (by norm_num)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

theorem endpointMeanPolynomial_row56 (ai : Fin 42) :
    endpointMeanActive 56 ai → ∃ n m, BoxCertificate (endpointMeanTestQ 56 ai) n m (endpointMeanBox 56 ai) := by
  fin_cases ai
  · intro h
    have hn : ¬ endpointMeanActive 56 0 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 1 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 2 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 3 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 4 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 5 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 6 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 7 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 8 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 9 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 10 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 11 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 12 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 13 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 14 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 15 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 16 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 17 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 18 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 19 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 20 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 21 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 22 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 23 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 24 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 25 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 26 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 27 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 28 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 29 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 30 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 31 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 32 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 33 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 34 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · intro h
    have hn : ¬ endpointMeanActive 56 35 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim
  · exact fun _ => ⟨4, 1, endpoint_mean_box_56_36⟩
  · exact fun _ => ⟨4, 1, endpoint_mean_box_56_37⟩
  · exact fun _ => ⟨4, 1, endpoint_mean_box_56_38⟩
  · exact fun _ => ⟨4, 1, endpoint_mean_box_56_39⟩
  · exact fun _ => ⟨4, 1, endpoint_mean_box_56_40⟩
  · intro h
    have hn : ¬ endpointMeanActive 56 41 := by
      norm_num [endpointMeanActive, endpointMeanBox, endpointMeanAPoint, Fin.coe_ofNat_eq_mod]
    exact (hn h).elim

end SingularValueBounds.KL.Certificates
