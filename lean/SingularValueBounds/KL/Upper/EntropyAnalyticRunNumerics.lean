import SingularValueBounds.KL.Upper.EntropyAnalyticRuns
import SingularValueBounds.KL.Upper.GeneralMeanNumerics
import SingularValueBounds.KL.Certificates.ConcreteLog

/-! Rational enclosures for exact exponential entropy integrals. The lower
primitive is set to zero beyond the useful domain of the short exponential
calculation. Logarithms of the two endpoints are reused separately. -/
namespace SingularValueBounds.KL.Certificates
noncomputable section

def primitiveUpperQ (c q u : ℚ) : ℚ :=
  (2/q)*generalMeanExpUpperQ (-q*u/2)*
    (1+(logRoundedQ u).2-(logRoundedQ c).1+resolventUpperQ (q*u/2))

def primitiveLowerQ (c q u : ℚ) : ℚ :=
  if q*u/2<24 then
    (2/q)/generalMeanExpUpperQ (q*u/2)*
      (1+max 0 ((logRoundedQ u).1-(logRoundedQ c).2)+resolventLowerQ (q*u/2))
  else 0

/-- Final ceiling to ten decimal places; the primitive arithmetic may retain
its own internal precision. -/
def entropyExpWeightUpperQ (c q a b : ℚ) : ℚ :=
  -(⌊-((primitiveUpperQ c q a-primitiveLowerQ c q b)*10000000000)⌋ : ℚ)/10000000000

private theorem roundUpQ_mono {x y : ℚ} (hxy : x≤y) : roundUpQ x≤roundUpQ y := by
  have hf := Int.floor_le_floor (neg_le_neg (mul_le_mul_of_nonneg_right hxy roundingScale_pos.le))
  unfold roundUpQ
  apply div_le_div_of_nonneg_right _ roundingScale_pos.le
  exact neg_le_neg (by exact_mod_cast hf)

private theorem short_exp_domain {x : ℚ} (hx : x<24) : roundUpQ x<26 :=
  (roundUpQ_mono hx.le).trans_lt (by norm_num [roundUpQ,roundingScale])

private theorem primitive_bracket_nonneg {c q u : ℝ} (hc : 0<c) (hcu : c≤u) (hq : 0<q) :
    0≤1+Real.log (u/c)+exponentialResolvent (q*u/2) := by
  have hu := hc.trans_le hcu
  have hlu : 0≤Real.log (u/c) := Real.log_nonneg ((one_le_div hc).mpr hcu)
  have hR := exponentialResolvent_nonneg (q*u/2) (by positivity)
  linarith

theorem primitiveUpperQ_sound {c q u : ℚ} (hc : 0<c) (hcu : c≤u) (hq : 0<q) :
    entropyExpPrimitive (c:ℝ) (q:ℝ) (u:ℝ)≤(primitiveUpperQ c q u:ℝ) := by
  have hu := hc.trans_le hcu
  have hcr : (0:ℝ)<c := by exact_mod_cast hc
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hur : (0:ℝ)<u := by exact_mod_cast hu
  have hcur : (c:ℝ)≤u := by exact_mod_cast hcu
  have hlu := (roundedLogConditions hu).sound.2
  have hlc := (roundedLogConditions hc).sound.1
  have hR := (resolvent_bounds_cast (show 0<q*u/2 by positivity)).2
  have he := generalMeanExpUpper_sound
    (generalMeanExpDomain_nonpos (show -q*u/2≤0 by
      have hx : 0≤q*u/2 := by positivity
      linarith))
  push_cast at he hR
  have hbr : 1+Real.log ((u:ℝ)/c)+exponentialResolvent ((q:ℝ)*u/2)≤
      1+((logRoundedQ u).2:ℝ)-((logRoundedQ c).1:ℝ)+(resolventUpperQ (q*u/2):ℝ) := by
    rw [Real.log_div hur.ne' hcr.ne']
    push_cast at hR
    linarith
  have hm := mul_le_mul he hbr (primitive_bracket_nonneg hcr hcur hqr)
    ((Real.exp_nonneg _).trans he)
  have hh := mul_le_mul_of_nonneg_left hm (div_nonneg (by norm_num : (0:ℝ)≤2) hqr.le)
  unfold entropyExpPrimitive primitiveUpperQ
  push_cast
  convert! hh using 1 <;> ring

theorem primitiveLowerQ_sound {c q u : ℚ} (hc : 0<c) (hcu : c≤u) (hq : 0<q) :
    (primitiveLowerQ c q u:ℝ)≤entropyExpPrimitive (c:ℝ) (q:ℝ) (u:ℝ) := by
  have hu := hc.trans_le hcu
  have hcr : (0:ℝ)<c := by exact_mod_cast hc
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hur : (0:ℝ)<u := by exact_mod_cast hu
  have hcur : (c:ℝ)≤u := by exact_mod_cast hcu
  have harg : 0<q*u/2 := by positivity
  unfold primitiveLowerQ
  split_ifs with hsmall
  · have hlu := (roundedLogConditions hu).sound.1
    have hlc := (roundedLogConditions hc).sound.2
    have hR := (resolvent_bounds_cast harg).1
    have he := generalMeanExpUpper_sound (short_exp_domain hsmall)
    have hInv := one_div_le_one_div_of_le (Real.exp_pos (q*u/2:ℚ)) he
    rw [one_div,one_div,← Real.exp_neg] at hInv
    push_cast at hInv hR
    rw [show -((q:ℝ)*u/2)=-(q:ℝ)*u/2 by ring] at hInv
    have hlog : (max 0 ((logRoundedQ u).1-(logRoundedQ c).2):ℝ)≤Real.log ((u:ℝ)/c) := by
      push_cast
      apply max_le (Real.log_nonneg ((one_le_div hcr).mpr hcur))
      rw [Real.log_div hur.ne' hcr.ne']
      linarith
    have hbr : 1+(max 0 ((logRoundedQ u).1-(logRoundedQ c).2):ℝ)+
        (resolventLowerQ (q*u/2):ℝ)≤1+Real.log ((u:ℝ)/c)+exponentialResolvent ((q:ℝ)*u/2) := by
      linarith
    have hR0 : (0:ℝ)≤(resolventLowerQ (q*u/2):ℝ) := by
      exact_mod_cast (show (0:ℚ)≤resolventLowerQ (q*u/2) by unfold resolventLowerQ; positivity)
    have hbr0 : 0≤1+(max 0 ((logRoundedQ u).1-(logRoundedQ c).2):ℝ)+
        (resolventLowerQ (q*u/2):ℝ) := by
      have hm : (0:ℝ)≤(max 0 ((logRoundedQ u).1-(logRoundedQ c).2):ℝ) := by
        exact_mod_cast (le_max_left 0 ((logRoundedQ u).1-(logRoundedQ c).2))
      linarith
    have hm := mul_le_mul hInv hbr hbr0 (Real.exp_nonneg _)
    have hh := mul_le_mul_of_nonneg_left hm (div_nonneg (by norm_num : (0:ℝ)≤2) hqr.le)
    unfold entropyExpPrimitive
    push_cast
    convert! hh using 1 <;> ring
  · simp only [Rat.cast_zero]
    unfold entropyExpPrimitive
    exact mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hqr.le) (Real.exp_nonneg _))
      (primitive_bracket_nonneg hcr hcur hqr)

theorem entropyExpWeightUpperQ_inflates (c q a b : ℚ) :
    primitiveUpperQ c q a-primitiveLowerQ c q b≤entropyExpWeightUpperQ c q a b := by
  unfold entropyExpWeightUpperQ
  rw [le_div_iff₀ (by norm_num : (0:ℚ)<10000000000)]
  have h := Int.floor_le (-((primitiveUpperQ c q a-primitiveLowerQ c q b)*10000000000))
  linarith

theorem entropyExpWeightUpperQ_sound {c q a b : ℚ}
    (hc : 0<c) (hca : c≤a) (hab : a≤b) (hq : 0<q) :
    entropyExpPrimitive (c:ℝ) (q:ℝ) (a:ℝ)-entropyExpPrimitive (c:ℝ) (q:ℝ) (b:ℝ)≤
      (entropyExpWeightUpperQ c q a b:ℝ) := by
  have ha := primitiveUpperQ_sound hc hca hq
  have hb := primitiveLowerQ_sound hc (hca.trans hab) hq
  have hr : (primitiveUpperQ c q a:ℝ)-(primitiveLowerQ c q b:ℝ)≤
      (entropyExpWeightUpperQ c q a b:ℝ) := by exact_mod_cast entropyExpWeightUpperQ_inflates c q a b
  linarith

theorem entropyExpWeightUpperQ_nonneg {c q a b : ℚ}
    (hc : 0<c) (hca : c≤a) (hab : a≤b) (hq : 0<q) : 0≤entropyExpWeightUpperQ c q a b := by
  have hn := entropy_exp_weight_nonneg (by exact_mod_cast hc : (0:ℝ)<c)
    (by exact_mod_cast hca : (c:ℝ)≤a) (by exact_mod_cast hab : (a:ℝ)≤b)
    (by exact_mod_cast hq : (0:ℝ)<q)
  exact_mod_cast hn.trans (entropyExpWeightUpperQ_sound hc hca hab hq)

end
end SingularValueBounds.KL.Certificates
