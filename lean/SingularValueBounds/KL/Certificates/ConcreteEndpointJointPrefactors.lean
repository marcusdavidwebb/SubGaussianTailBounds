import SingularValueBounds.KL.Certificates.IntegerRoundedLogEvaluation
import SingularValueBounds.KL.Certificates.ConcreteEndpointPrefactors
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanRates

/-!
Joint endpoint-prefactor bounds for every grid node and clipped rectangle.
A small exact table covers only the spectral grid and the 111 possible rates;
uniform monotonicity then supplies all third-moment parameters and grid nodes.
-/
namespace SingularValueBounds.KL.Certificates

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem roundUpQ_mono {x y : ℚ} (h : x ≤ y) : roundUpQ x ≤ roundUpQ y := by
  unfold roundUpQ
  apply div_le_div_of_nonneg_right _ roundingScale_pos.le
  apply neg_le_neg
  exact_mod_cast Int.floor_mono (neg_le_neg (mul_le_mul_of_nonneg_right h roundingScale_pos.le))

theorem endpointJointLog_le_unitMax {k a q : ℚ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    endpointJointLogUpperQ k a q ≤ roundUpQ (q/2) +
      roundUpQ (max 0 ((-(logRoundedQ (1-q*k^2)).1-roundDownQ (q*k^2))/(2*k^3))) := by
  unfold endpointJointLogUpperQ
  apply add_le_add_left
  apply roundUpQ_mono
  rw [mul_div_assoc]
  by_cases hz : 0 ≤ (-(logRoundedQ (1-q*k^2)).1-roundDownQ (q*k^2))/(2*k^3)
  · rw [max_eq_right hz]
    simpa using mul_le_mul_of_nonneg_right ha1 hz
  · rw [max_eq_left (le_of_not_ge hz)]
    exact mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_ge hz)

def endpointJointGridDomain (ki : Fin 61) : Prop :=
  ∀ qi : Fin 111,
    ((qi.val+90 : ℚ)/100) * ((ki.val+20 : ℚ)/80)^2 < 1 →
    roundUpQ (roundUpQ (((qi.val+90 : ℚ)/100)/2) +
      roundUpQ (max 0
        ((-(logRoundedQ (1-((qi.val+90 : ℚ)/100)*((ki.val+20 : ℚ)/80)^2)).1 -
          roundDownQ (((qi.val+90 : ℚ)/100)*((ki.val+20 : ℚ)/80)^2)) /
            (2*((ki.val+20 : ℚ)/80)^3)))) < 82

private theorem endpointJoint_grid_expDomain_0 : endpointJointGridDomain 0 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_1 : endpointJointGridDomain 1 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_2 : endpointJointGridDomain 2 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_3 : endpointJointGridDomain 3 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_4 : endpointJointGridDomain 4 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_5 : endpointJointGridDomain 5 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_6 : endpointJointGridDomain 6 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_7 : endpointJointGridDomain 7 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_8 : endpointJointGridDomain 8 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_9 : endpointJointGridDomain 9 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_10 : endpointJointGridDomain 10 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_11 : endpointJointGridDomain 11 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_12 : endpointJointGridDomain 12 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_13 : endpointJointGridDomain 13 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_14 : endpointJointGridDomain 14 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_15 : endpointJointGridDomain 15 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_16 : endpointJointGridDomain 16 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_17 : endpointJointGridDomain 17 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_18 : endpointJointGridDomain 18 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_19 : endpointJointGridDomain 19 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_20 : endpointJointGridDomain 20 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_21 : endpointJointGridDomain 21 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_22 : endpointJointGridDomain 22 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_23 : endpointJointGridDomain 23 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_24 : endpointJointGridDomain 24 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_25 : endpointJointGridDomain 25 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_26 : endpointJointGridDomain 26 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_27 : endpointJointGridDomain 27 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_28 : endpointJointGridDomain 28 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_29 : endpointJointGridDomain 29 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_30 : endpointJointGridDomain 30 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_31 : endpointJointGridDomain 31 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_32 : endpointJointGridDomain 32 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_33 : endpointJointGridDomain 33 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_34 : endpointJointGridDomain 34 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_35 : endpointJointGridDomain 35 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_36 : endpointJointGridDomain 36 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_37 : endpointJointGridDomain 37 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_38 : endpointJointGridDomain 38 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_39 : endpointJointGridDomain 39 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_40 : endpointJointGridDomain 40 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_41 : endpointJointGridDomain 41 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_42 : endpointJointGridDomain 42 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_43 : endpointJointGridDomain 43 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_44 : endpointJointGridDomain 44 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_45 : endpointJointGridDomain 45 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_46 : endpointJointGridDomain 46 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_47 : endpointJointGridDomain 47 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_48 : endpointJointGridDomain 48 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_49 : endpointJointGridDomain 49 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_50 : endpointJointGridDomain 50 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_51 : endpointJointGridDomain 51 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_52 : endpointJointGridDomain 52 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_53 : endpointJointGridDomain 53 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_54 : endpointJointGridDomain 54 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_55 : endpointJointGridDomain 55 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_56 : endpointJointGridDomain 56 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_57 : endpointJointGridDomain 57 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_58 : endpointJointGridDomain 58 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_59 : endpointJointGridDomain 59 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

private theorem endpointJoint_grid_expDomain_60 : endpointJointGridDomain 60 := by
  unfold endpointJointGridDomain
  simp only [logRoundedQ_eq_integer]
  decide +kernel

theorem endpointJoint_grid_expDomain (ki : Fin 61) : endpointJointGridDomain ki := by
  fin_cases ki
  · exact endpointJoint_grid_expDomain_0
  · exact endpointJoint_grid_expDomain_1
  · exact endpointJoint_grid_expDomain_2
  · exact endpointJoint_grid_expDomain_3
  · exact endpointJoint_grid_expDomain_4
  · exact endpointJoint_grid_expDomain_5
  · exact endpointJoint_grid_expDomain_6
  · exact endpointJoint_grid_expDomain_7
  · exact endpointJoint_grid_expDomain_8
  · exact endpointJoint_grid_expDomain_9
  · exact endpointJoint_grid_expDomain_10
  · exact endpointJoint_grid_expDomain_11
  · exact endpointJoint_grid_expDomain_12
  · exact endpointJoint_grid_expDomain_13
  · exact endpointJoint_grid_expDomain_14
  · exact endpointJoint_grid_expDomain_15
  · exact endpointJoint_grid_expDomain_16
  · exact endpointJoint_grid_expDomain_17
  · exact endpointJoint_grid_expDomain_18
  · exact endpointJoint_grid_expDomain_19
  · exact endpointJoint_grid_expDomain_20
  · exact endpointJoint_grid_expDomain_21
  · exact endpointJoint_grid_expDomain_22
  · exact endpointJoint_grid_expDomain_23
  · exact endpointJoint_grid_expDomain_24
  · exact endpointJoint_grid_expDomain_25
  · exact endpointJoint_grid_expDomain_26
  · exact endpointJoint_grid_expDomain_27
  · exact endpointJoint_grid_expDomain_28
  · exact endpointJoint_grid_expDomain_29
  · exact endpointJoint_grid_expDomain_30
  · exact endpointJoint_grid_expDomain_31
  · exact endpointJoint_grid_expDomain_32
  · exact endpointJoint_grid_expDomain_33
  · exact endpointJoint_grid_expDomain_34
  · exact endpointJoint_grid_expDomain_35
  · exact endpointJoint_grid_expDomain_36
  · exact endpointJoint_grid_expDomain_37
  · exact endpointJoint_grid_expDomain_38
  · exact endpointJoint_grid_expDomain_39
  · exact endpointJoint_grid_expDomain_40
  · exact endpointJoint_grid_expDomain_41
  · exact endpointJoint_grid_expDomain_42
  · exact endpointJoint_grid_expDomain_43
  · exact endpointJoint_grid_expDomain_44
  · exact endpointJoint_grid_expDomain_45
  · exact endpointJoint_grid_expDomain_46
  · exact endpointJoint_grid_expDomain_47
  · exact endpointJoint_grid_expDomain_48
  · exact endpointJoint_grid_expDomain_49
  · exact endpointJoint_grid_expDomain_50
  · exact endpointJoint_grid_expDomain_51
  · exact endpointJoint_grid_expDomain_52
  · exact endpointJoint_grid_expDomain_53
  · exact endpointJoint_grid_expDomain_54
  · exact endpointJoint_grid_expDomain_55
  · exact endpointJoint_grid_expDomain_56
  · exact endpointJoint_grid_expDomain_57
  · exact endpointJoint_grid_expDomain_58
  · exact endpointJoint_grid_expDomain_59
  · exact endpointJoint_grid_expDomain_60

end SingularValueBounds.KL.Certificates
