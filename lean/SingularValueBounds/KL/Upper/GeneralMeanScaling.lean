import SingularValueBounds.KL.Upper.GeneralMeanEntropyIntegral

open MeasureTheory Set
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1600000

def generalMeanExponentialPrimitive (a v β : ℝ) : ℝ :=
  Real.exp (-(β*v))/β*(1+Real.log (v/a)+exponentialResolvent (β*v))

theorem generalMean_exponential_primitive_integral {a v β : ℝ}
    (ha : 0<a) (hav : a≤v) (hβ : 0<β) :
    (∫u in Ioi v,entropyKernel a u*Real.exp (-(β*u)))=
      generalMeanExponentialPrimitive a v β :=
  generalMean_entropy_exponential_integral ha hav hβ

theorem generalMean_exp_scale {K L : ℝ} (hK : 0<K) (hKL : L=1+Real.log K) :
    Real.exp (2*L-2)=K^2 := by
  rw [hKL,show 2*(1+Real.log K)-2=Real.log K+Real.log K by ring,Real.exp_add,
    Real.exp_log hK]
  ring

theorem generalMean_log_cutoff {K L c : ℝ} (hK : 0<K) (hL : 1≤L) (hc : 0<c)
    (hKL : L=1+Real.log K) :
    Real.log (c*K^2*L)=2*L-2+Real.log (c*L) := by
  have hK2 : K^2≠0 := pow_ne_zero 2 hK.ne'
  rw [show c*K^2*L=K^2*(c*L) by ring,Real.log_mul hK2 (by positivity),Real.log_pow,hKL]
  ring

theorem generalMean_exp_scale_factor {K L z : ℝ} (hK : 0<K) (hKL : L=1+Real.log K) :
    K^2*Real.exp (-z*L/2)=Real.exp (-2-(z/2-2)*L) := by
  rw [← generalMean_exp_scale hK hKL,← Real.exp_add]
  congr 1
  ring

theorem generalMean_base_integral_scale {A K L q c : ℝ}
    (hK : 0<K) (hL : 1≤L) (hq : 0<q) (hc : 0<c) (hKL : L=1+Real.log K) :
    A*generalMeanExponentialPrimitive (c*K^2*L) (c*K^2*L) (q/(2*K^2))=
      generalMeanRemainder A q c L := by
  have ha : c*K^2*L≠0 := by positivity
  have harg : q/(2*K^2)*(c*K^2*L)=q*c*L/2 := by field_simp;ring
  unfold generalMeanExponentialPrimitive generalMeanRemainder
  rw [harg,div_self ha,Real.log_one,add_zero]
  have hdiv : Real.exp (-(q*c*L/2))/(q/(2*K^2))=
      (2/q)*(K^2*Real.exp (-(q*c)*L/2)) := by simp only [div_div,div_eq_mul_inv,inv_inv,mul_inv_rev];ring
  rw [hdiv,generalMean_exp_scale_factor hK hKL]
  ring

theorem generalMean_continuation_integral_scale {A K L q c s : ℝ}
    (hK : 0<K) (hL : 1≤L) (hq : 1<q) (hc : 0<c) (hcs : c≤s)
    (hKL : L=1+Real.log K) :
    A*Real.exp (-(q-1)*s*L/2)*
        generalMeanExponentialPrimitive (c*K^2*L) (s*K^2*L) (1/(2*K^2))-
      A*generalMeanExponentialPrimitive (c*K^2*L) (s*K^2*L) (q/(2*K^2))=
      generalMeanContinuation A q c s L := by
  have hs : 0<s := hc.trans_le hcs
  have hq0 : 0<q := by linarith
  have hratio : s*K^2*L/(c*K^2*L)=s/c := by field_simp;ring
  have harg1 : 1/(2*K^2)*(s*K^2*L)=s*L/2 := by field_simp;ring
  have hargq : q/(2*K^2)*(s*K^2*L)=q*s*L/2 := by field_simp;ring
  unfold generalMeanExponentialPrimitive generalMeanContinuation
  rw [hratio,harg1,hargq]
  have hd1 : Real.exp (-(s*L/2))/(1/(2*K^2))=2*K^2*Real.exp (-s*L/2) := by simp only [div_div,div_eq_mul_inv,inv_inv,mul_inv_rev];ring
  have hdq : Real.exp (-(q*s*L/2))/(q/(2*K^2))=(2/q)*K^2*Real.exp (-(q*s)*L/2) := by simp only [div_div,div_eq_mul_inv,inv_inv,mul_inv_rev];ring
  rw [hd1,hdq]
  have he : Real.exp (-(q-1)*s*L/2)*Real.exp (-s*L/2)=Real.exp (-(q*s)*L/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfactor := generalMean_exp_scale_factor (z := q*s) hK hKL
  have hcommon : Real.exp (-(q-1)*s*L/2)*(K^2*Real.exp (-s*L/2))=
      Real.exp (-2-(q*s/2-2)*L) := by
    rw [← mul_assoc,mul_comm _ (K^2),mul_assoc,he,hfactor]
  calc
    _ = 2*A*(Real.exp (-(q-1)*s*L/2)*(K^2*Real.exp (-s*L/2)))*
        (1+Real.log (s/c)+exponentialResolvent (s*L/2))-
        (2*A/q)*(K^2*Real.exp (-(q*s)*L/2))*
          (1+Real.log (s/c)+exponentialResolvent (q*s*L/2)) := by ring
    _ = _ := by rw [hcommon,hfactor];ring

end
end SingularValueBounds.KL
