import SingularValueBounds.KL.Upper.EndpointDeterminants
import SingularValueBounds.KL.Upper.EndpointCoefficients

/-! # Endpoint rare-event numerical comparisons (supplementary S1.6.4)

The small Taylor comparisons are proved directly in Lean. Only the larger
tensor polynomial certificate remains an external numerical premise.
-/
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1800000

def endpointTopLog (i : Fin 3) : ℝ := if i=0 then 67/500 else if i=1 then 16/125 else 101/1000
def endpointRestLog (i : Fin 3) : ℝ := if i=0 then 219/100 else if i=1 then 527/250 else 1833/1000
def endpointLogMGFCost (i : Fin 3) : ℝ :=
  (endpointTopLog i+endpointRestLog i-(12/5 : ℝ)*
    ((endpointSpectralRow i).topBound+(endpointSpectralRow i).restBound))/2

private theorem log_bound_of_taylor_order (N : ℕ) {z l : ℝ} (hz : z<1) (hl : 0≤l)
    (hfinite : 1/(1-z)≤Certificates.expTaylor N l) :
    -Real.log (1-z)≤l := by
  have hh := Real.log_le_log (one_div_pos.mpr (show 0<1-z by linarith))
    (hfinite.trans (Certificates.expTaylor_le_exp N hl))
  rw [Real.log_div (by norm_num) (by linarith : 1-z≠0),Real.log_one,Real.log_exp] at hh
  simpa using hh

theorem log_bound_of_taylor {z l : ℝ} (hz : z<1) (hl : 0≤l)
    (hfinite : 1/(1-z)≤Certificates.expTaylor 24 l) :
    -Real.log (1-z)≤l :=
  log_bound_of_taylor_order 24 hz hl hfinite

private theorem exp_neg_bound_of_taylor_order (N : ℕ) {x p : ℝ} (hx : 0≤x) (hp : 0<p)
    (hfinite : 1/p≤Certificates.expTaylor N x) :
    Real.exp (-x)≤p := by
  have hi := one_div_le_one_div_of_le (one_div_pos.mpr hp)
    (hfinite.trans (Certificates.expTaylor_le_exp N hx))
  rw [one_div_one_div,one_div,← Real.exp_neg] at hi
  exact hi

theorem exp_neg_bound_of_taylor {x p : ℝ} (hx : 0≤x) (hp : 0<p)
    (hfinite : 1/p≤Certificates.expTaylor 24 x) :
    Real.exp (-x)≤p :=
  exp_neg_bound_of_taylor_order 24 hx hp hfinite

theorem endpoint_row_log_bounds (i : Fin 3) :
    -Real.log (1-(12/5 : ℝ)*(endpointSpectralRow i).topBound)≤endpointTopLog i ∧
    -Real.log (1-(12/5 : ℝ)*(endpointSpectralRow i).restBound)≤endpointRestLog i := by
  constructor
  · apply log_bound_of_taylor_order 3
    · fin_cases i <;> norm_num [endpointSpectralRow]
    · fin_cases i <;> norm_num [endpointTopLog]
    · fin_cases i <;> norm_num [endpointSpectralRow,endpointTopLog,
        Certificates.expTaylor,Finset.sum_range_succ]
  · apply log_bound_of_taylor_order 8
    · fin_cases i <;> norm_num [endpointSpectralRow]
    · fin_cases i <;> norm_num [endpointRestLog]
    · fin_cases i <;> norm_num [endpointSpectralRow,endpointRestLog,
        Certificates.expTaylor,Finset.sum_range_succ]

theorem endpoint_row_probability_exponential (i : Fin 3) :
    Real.exp (endpointLogMGFCost i-(6/5 : ℝ)*(endpointSpectralRow i).gap)≤
      (endpointRareRow i).probability := by
  rw [show endpointLogMGFCost i-(6/5 : ℝ)*(endpointSpectralRow i).gap=
    -((6/5 : ℝ)*(endpointSpectralRow i).gap-endpointLogMGFCost i) by ring]
  apply exp_neg_bound_of_taylor_order 9
  · fin_cases i <;> norm_num [endpointSpectralRow,endpointLogMGFCost,endpointTopLog,endpointRestLog]
  · exact (endpointRareRow_bounds i).1
  · fin_cases i <;> norm_num [endpointRareRow,endpointSpectralRow,endpointLogMGFCost,
      endpointTopLog,endpointRestLog,Certificates.expTaylor,Finset.sum_range_succ]

theorem endpoint_row_cutoff (i : Fin 3) :
    (177/50 : ℝ)*Real.exp (-((23/50 : ℝ)*(endpointRareRow i).cutoff))≤
      (endpointRareRow i).probability := by
  have hh : Real.exp (-((23/50 : ℝ)*(endpointRareRow i).cutoff))≤
      (endpointRareRow i).probability/(177/50 : ℝ) := by
    apply exp_neg_bound_of_taylor_order 11
    · exact mul_nonneg (by norm_num) (endpointRareRow_bounds i).2.1
    · exact div_pos (endpointRareRow_bounds i).1 (by norm_num)
    · fin_cases i <;> norm_num [endpointRareRow,Certificates.expTaylor,Finset.sum_range_succ]
  linarith

end
end SingularValueBounds.KL
