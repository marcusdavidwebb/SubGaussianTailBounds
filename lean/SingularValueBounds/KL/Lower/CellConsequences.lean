import SingularValueBounds.KL.Lower.CellEnclosures

/-! Whole-cell consequences of the finite P11 conditions. -/
open Set MeasureTheory
open scoped BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1400000

def lowerMomentU (p k : ℝ) : ℝ := 4*p/((p-1)*generalLowerProfile k)

theorem lowerMomentU_pos {p k : ℝ} (hp : 1 < p) : 0 < lowerMomentU p k := by
  have hh := (generalLowerProfile_bounds k).1
  exact div_pos (by linarith) (mul_pos (by linarith) (by linarith))

theorem lowerMomentU_antitone {p a b : ℝ} (hp : 1 < p)
    (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) (hab : a ≤ b) :
    lowerMomentU p b ≤ lowerMomentU p a := by
  have hh := generalLowerProfile_mono ha hb hab
  have hpa := (generalLowerProfile_bounds a).1
  have hpb := (generalLowerProfile_bounds b).1
  exact div_le_div_of_nonneg_left (by linarith) (mul_pos (by linarith) (by linarith))
    (mul_le_mul_of_nonneg_left hh (by linarith))

namespace LowerCertificates
open SingularValueBounds.KL.Certificates
open SingularValueBounds.KL.Certificates.NumericalCertificateConditions

@[simp] theorem cast_lowerMPartialQ (N : ℕ) (q : ℚ) :
    (lowerMPartialQ N q:ℝ) = ∑ r ∈ Finset.range N,2*(q:ℝ)^(r+2)/((r+2:ℝ)*(r+3:ℝ)) := by
  simp [lowerMPartialQ]

@[simp] theorem cast_lowerMomentU (p a : ℚ) :
    ((4*p/((p-1)*generalLowerProfileQ a):ℚ):ℝ) = lowerMomentU p a := by
  simp [lowerMomentU]

theorem MomentCellCertificate.shape_bounds {a b p : ℚ} (h : MomentCellCertificate a b p)
    {k : ℝ} (hk : k ∈ Icc (a:ℝ) (b:ℝ)) :
    lowerMomentU (p:ℝ) k*k < 1 ∧
    k^2 < lowerM (lowerMomentU (p:ℝ) k*k) ∧
    lowerJ (lowerMomentU (p:ℝ) k*k)/(2*k^2) ≤
      ((logUpperQ (1/(1-(4*p/((p-1)*generalLowerProfileQ a))*b))-
        (4*p/((p-1)*generalLowerProfileQ a))*b)/(2*b^2):ℚ) := by
  have ha : (0:ℝ) < a := by exact_mod_cast h.a_pos
  have hb : (b:ℝ) ≤ 1 := by exact_mod_cast h.b_le.trans (by norm_num : (711:ℚ)/1000 ≤ 1)
  have hab : (a:ℝ) ≤ b := by exact_mod_cast h.a_le_b
  have hk0 : 0 < k := ha.trans_le hk.1
  have hk1 : k ≤ 1 := hk.2.trans hb
  have hp : (19:ℝ)/4 ≤ p := by
    have hh := (Rat.cast_le (K:=ℝ)).2 h.power
    norm_num at hh
    exact hh
  have huA := lowerMomentU_pos (k:=(a:ℝ)) (by linarith : 1 < (p:ℝ))
  have huB := lowerMomentU_pos (k:=(b:ℝ)) (by linarith : 1 < (p:ℝ))
  have hu := lowerMomentU_pos (k:=k) (by linarith : 1 < (p:ℝ))
  have hUa := lowerMomentU_antitone (by linarith : 1 < (p:ℝ)) ⟨ha.le,hab.trans hb⟩ ⟨hk0.le,hk1⟩ hk.1
  have hUb := lowerMomentU_antitone (by linarith : 1 < (p:ℝ)) ⟨hk0.le,hk1⟩ ⟨ha.le.trans hab,hb⟩ hk.2
  have hdomain : lowerMomentU (p:ℝ) (a:ℝ)*(b:ℝ) < 1 := by
    have hc : ((4*p/((p-1)*generalLowerProfileQ a))*b:ℚ) < 1 := h.u_domain
    have hh := (Rat.cast_lt (K:=ℝ)).2 hc
    simpa only [Rat.cast_mul,cast_lowerMomentU,Rat.cast_one] using hh
  have huk := (mul_le_mul hUa hk.2 hk0.le huA.le).trans_lt hdomain
  have huBa := (mul_le_mul hUb hk.1 ha.le hu.le).trans_lt huk
  have hpartial : (a:ℝ)^2 < lowerM (lowerMomentU (p:ℝ) (b:ℝ)*(a:ℝ)) := by
    have hs : (a:ℝ)^2 < ∑ r ∈ Finset.range 59,
        2*(lowerMomentU (p:ℝ) (b:ℝ)*(a:ℝ))^(r+2)/((r+2:ℝ)*(r+3:ℝ)) := by
      have hh := h.shape
      have hc := (Rat.cast_lt (K:=ℝ)).2 hh
      simpa only [Rat.cast_pow,cast_lowerMPartialQ,Rat.cast_mul,cast_lowerMomentU] using hc
    exact hs.trans_le (lowerM_partial_le (mul_pos huB ha) huBa 59)
  have hM := lowerM_scaled_mono huB hUb ha hk.1 huk
  have hshape : k^2 < lowerM (lowerMomentU (p:ℝ) k*k) := by
    have hdiv : 1 < lowerM (lowerMomentU (p:ℝ) (b:ℝ)*(a:ℝ))/(a:ℝ)^2 :=
      (lt_div_iff₀ (sq_pos_of_pos ha)).2 (by simpa using hpartial)
    have hh := hdiv.trans_le hM
    simpa only [one_mul] using (lt_div_iff₀ (sq_pos_of_pos hk0)).1 hh
  have hJ := lowerJ_scaled_mono hu.le hUa hk0 hk.2 hdomain
  have hQ : (0:ℚ) ≤ (4*p/((p-1)*generalLowerProfileQ a))*b := by
    have hq : (0:ℝ) ≤ lowerMomentU (p:ℝ) (a:ℝ)*(b:ℝ) := mul_nonneg huA.le (ha.le.trans hab)
    apply (Rat.cast_nonneg (K:=ℝ)).1
    simpa only [Rat.cast_mul,cast_lowerMomentU] using hq
  have hjUpper := lowerJ_upperQ hQ h.u_domain
  have hjUpper' : lowerJ (lowerMomentU (p:ℝ) (a:ℝ)*(b:ℝ)) ≤
      (logUpperQ (1/(1-(4*p/((p-1)*generalLowerProfileQ a))*b))-
        (4*p/((p-1)*generalLowerProfileQ a))*b:ℚ) := by simpa [lowerMomentU] using hjUpper
  have hjDiv := div_le_div_of_nonneg_right hjUpper' (sq_nonneg (b:ℝ))
  refine ⟨huk,hshape,?_⟩
  have hfinal := div_le_div_of_nonneg_right (hJ.trans hjDiv) (by norm_num : (0:ℝ) ≤ 2)
  convert! hfinal using 1 <;> push_cast <;> ring

theorem momentB_pos_and_product {k p : ℝ} (hk : 0 ≤ k) (hk1 : k ≤ 1)
    (hp : (19:ℝ)/4 ≤ p) : 0 < momentB k p ∧ 1 ≤ p*momentB k p := by
  have hk2 : k^2 ≤ 1 := by nlinarith
  have hd : 0 < p-2*k^2 := by linarith
  have hB : 0 < momentB k p := by dsimp [momentB]; positivity
  refine ⟨hB,?_⟩
  have hid : p*momentB k p-1 = 2*k^2*(p+1/(p-2*k^2)) := by
    dsimp [momentB]
    field_simp
    <;> ring
  have hh : 0 ≤ 2*k^2*(p+1/(p-2*k^2)) := by positivity
  linarith

theorem MomentCellCertificate.entropy_condition {a b p : ℚ} (h : MomentCellCertificate a b p)
    {k : ℝ} (hk : k ∈ Icc (a:ℝ) (b:ℝ)) :
    ((p:ℝ)-1)*(lowerJ (lowerMomentU (p:ℝ) k*k)/(2*k^2))+
      Real.log (Real.exp (momentLogM k (p:ℝ))-1)+
      (p:ℝ)*Real.log ((p:ℝ)*momentB k (p:ℝ))-
      Real.log (1-Real.exp (-((p:ℝ)-1/20))) < 3*(p:ℝ) := by
  have ha : (0:ℝ) < a := by exact_mod_cast h.a_pos
  have hb : (b:ℝ) ≤ 1 := by
    have hh := (Rat.cast_le (K:=ℝ)).2 h.b_le
    norm_num at hh
    linarith
  have hk0 : 0 < k := ha.trans_le hk.1
  have hk1 : k ≤ 1 := hk.2.trans hb
  have hp : (19:ℝ)/4 ≤ p := by
    have hh := (Rat.cast_le (K:=ℝ)).2 h.power
    norm_num at hh
    exact hh
  have hshape := h.shape_bounds hk
  have hLM := (momentLogM_antitone hp ⟨ha,hk.1.trans hk1⟩ ⟨hk0,hk1⟩ hk.1).trans
    (momentEll_upper h.a_pos (by exact_mod_cast hk.1.trans hk1) h.power)
  have hLMpos : 0 < momentLogM k (p:ℝ) := div_pos
    (Real.log_pos (momentD_gt_one hk0 hk1 hp)) (by positivity)
  have hLog := Real.log_le_log (sub_pos.mpr (Real.one_lt_exp_iff.mpr hLMpos))
    (sub_le_sub_right (Real.exp_le_exp.mpr hLM) 1)
  have hV := moment_log_minus_one_upper h.ell_pos h.v_nonneg h.v_lt h.v_exp
  have hLogV := hLog.trans hV
  have hBprops := momentB_pos_and_product hk0.le hk1 hp
  have hBmono := momentB_mono hk0.le hk.2 hb hp
  have hBlog := Real.log_le_log (mul_pos (by linarith : 0 < (p:ℝ)) hBprops.1)
    (mul_le_mul_of_nonneg_left hBmono (by linarith : 0 ≤ (p:ℝ)))
  have hProdB : 1 ≤ p*momentBq b p := by
    have hh := (momentB_pos_and_product (ha.le.trans (hk.1.trans hk.2)) hb hp).2
    rw [← cast_momentBq] at hh
    exact_mod_cast hh
  have hBupper := log_le_logUpperQ hProdB
  have hBupper' : Real.log ((p:ℝ)*momentB (b:ℝ) (p:ℝ)) ≤
      (logUpperQ (p*momentBq b p):ℝ) := by simpa using hBupper
  have hBfinal := mul_le_mul_of_nonneg_left (hBlog.trans hBupper') (by linarith : 0 ≤ (p:ℝ))
  have hEps := epsilon_upper h.power
  have hG := mul_le_mul_of_nonneg_left hshape.2.2 (by linarith : 0 ≤ (p:ℝ)-1)
  have hcert' : ((p:ℝ)-1)*(((logUpperQ (1/(1-(4*p/((p-1)*generalLowerProfileQ a))*b))-
        (4*p/((p-1)*generalLowerProfileQ a))*b)/(2*b^2):ℚ):ℝ)+
      (momentLogMinusOneQ (momentEllQ a p):ℝ)+(p:ℝ)*(logUpperQ (p*momentBq b p):ℝ)+
      1/((expTaylorQ 24 (p-1/20):ℝ)-1) < 3*(p:ℝ) := by
    convert! (Rat.cast_lt (K:=ℝ)).2 h.entropy using 1 <;> push_cast <;> ring
  linarith

end LowerCertificates
end
end SingularValueBounds.KL
