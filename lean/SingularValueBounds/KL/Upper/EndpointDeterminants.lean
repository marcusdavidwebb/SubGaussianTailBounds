import SingularValueBounds.KL.Upper.EndpointSpectra
import SingularValueBounds.KL.Upper.NormDeterminants

/-! # Two-coordinate Gaussian determinant bound (supplementary S1.6.4)

The finite logratio certificate controls all the smaller eigenvalues by
their remaining square mass. The largest contribution is retained separately.
-/
open Set
open scoped BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1500000

def endpointLogExcess (z : ℝ) : ℝ := -Real.log (1-z)-z

theorem endpointLogExcess_nonneg {z : ℝ} (hz : z<1) : 0≤endpointLogExcess z := by
  have hh := Real.log_le_sub_one_of_pos (show 0<1-z by linarith)
  dsimp [endpointLogExcess]
  linarith

theorem endpointLogExcess_monotone : MonotoneOn endpointLogExcess (Ico 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ico _ _)
  · unfold endpointLogExcess
    apply ContinuousOn.sub
    · apply ContinuousOn.neg
      apply ContinuousOn.log (by fun_prop)
      intro z hz
      exact ne_of_gt (by linarith [hz.2])
    · fun_prop
  · intro z hz
    have hz' : z∈Ico (0 : ℝ) 1 := interior_subset hz
    have hf := (((hasDerivAt_const z 1).sub (hasDerivAt_id z)).log
      (ne_of_gt (show 0<1-z by linarith [hz'.2]))).neg.sub (hasDerivAt_id z)
    exact hf.differentiableAt.differentiableWithinAt
  · intro z hz
    have hz' : z∈Ico (0 : ℝ) 1 := interior_subset hz
    have hd := (((hasDerivAt_const z 1).sub (hasDerivAt_id z)).log
      (ne_of_gt (show 0<1-z by linarith [hz'.2]))).neg.sub (hasDerivAt_id z)
    have hd' : HasDerivAt endpointLogExcess (z/(1-z)) z := by
      convert! hd using 1
      simp only [zero_sub,neg_div,neg_neg,id_eq,Pi.sub_apply]
      field_simp [show 1-z≠0 by linarith [hz'.2]]
      <;> ring
    rw [hd'.deriv]
    exact div_nonneg hz'.1 (by linarith [hz'.2])

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem endpoint_spectral_logdet (hcert : EndpointLogratioCertificateConditions)
    (i : Fin 3) {x : ι → ℝ} (hx : ∀j,0<x j) (h2 : ∑j,x j^2=1)
    (top : ι) (hκ : x top∈Icc (endpointSpectralRow i).lo (endpointSpectralRow i).hi) :
    (∀j,0<1-(12/5 : ℝ)*normalizedUpperEigenvalue x j) ∧
      (∑j,endpointLogExcess ((12/5 : ℝ)*normalizedUpperEigenvalue x j))≤
        endpointLogExcess ((12/5 : ℝ)*(endpointSpectralRow i).topBound)+
        endpointLogExcess ((12/5 : ℝ)*(endpointSpectralRow i).restBound) := by
  let row := endpointSpectralRow i
  obtain ⟨hA,htop,hrest,hrest2,hpoly,hcr,hgap⟩ := endpoint_spectral_row_bounds i
    (fun j => (hx j).le) h2 top hκ
  have hmean : row.meanBound∈Icc (1/2 : ℝ) 1 := by
    fin_cases i <;> norm_num [row,endpointSpectralRow]
  have hr : row.radius∈Ioc (0 : ℝ) (7/20) := by
    fin_cases i <;> norm_num [row,endpointSpectralRow]
  have hqt : (12/5 : ℝ)*row.topBound∈Ico (0 : ℝ) 1 := by
    fin_cases i <;> norm_num [row,endpointSpectralRow]
  have hct : (12/5 : ℝ)*row.restBound∈Ico (0 : ℝ) 1 := by
    fin_cases i <;> norm_num [row,endpointSpectralRow]
  have hc0 : ∀j,0≤normalizedUpperEigenvalue x j :=
    fun j => normalized_upper_eigenvalue_nonneg (fun k => (hx k).le) j
  have hcrest (j : ι) (hj : j≠top) : normalizedUpperEigenvalue x j≤row.restBound := by
    have hh := endpoint_cubic_monotone (show 0≤row.meanBound by linarith [hmean.1])
      ⟨(hx j).le,(hrest j hj).trans hr.2⟩ ⟨hr.1.le,hr.2⟩ (hrest j hj)
    exact (hpoly j hj).trans (hh.trans hcr)
  have hci (j : ι) : (12/5 : ℝ)*normalizedUpperEigenvalue x j∈Ico (0 : ℝ) 1 := by
    refine ⟨mul_nonneg (by norm_num) (hc0 j), ?_⟩
    by_cases hj : j=top
    · subst j
      nlinarith [hqt.2]
    · nlinarith [hcrest j hj,hct.2]
  refine ⟨fun j => by linarith [(hci j).2], ?_⟩
  have htopLog := endpointLogExcess_monotone (hci top) hqt
    (mul_le_mul_of_nonneg_left htop (by norm_num : (0 : ℝ)≤12/5))
  have hrestTerm (j : ι) (hj : j≠top) :
      endpointLogExcess ((12/5 : ℝ)*normalizedUpperEigenvalue x j)≤
        (x j)^2/row.radius^2*endpointLogExcess ((12/5 : ℝ)*row.restBound) := by
    have hxrange : x j∈Ioc (0 : ℝ) (7/20) := ⟨hx j,(hrest j hj).trans hr.2⟩
    have hz := endpointLogratioZ_bounds hmean ⟨(hx j).le,hxrange.2⟩
    have hzR := endpointLogratioZ_bounds hmean ⟨hr.1.le,hr.2⟩
    have hstep1 := endpointLogExcess_monotone (hci j) hz
      (mul_le_mul_of_nonneg_left (hpoly j hj) (by norm_num : (0 : ℝ)≤12/5))
    have hratio := endpointLogratio_monotone hcert hmean hxrange hr (hrest j hj)
    change endpointLogExcess (endpointLogratioZ row.meanBound (x j))/(x j)^2≤
      endpointLogExcess (endpointLogratioZ row.meanBound row.radius)/row.radius^2 at hratio
    have hstep2 := (div_le_iff₀ (sq_pos_of_pos (hx j))).1 hratio
    have hstep3 := endpointLogExcess_monotone hzR hct
      (mul_le_mul_of_nonneg_left hcr (by norm_num : (0 : ℝ)≤12/5))
    have hmul := mul_le_mul_of_nonneg_left hstep3
      (div_nonneg (sq_nonneg (x j)) (sq_nonneg row.radius))
    have he : endpointLogExcess (endpointLogratioZ row.meanBound row.radius)/row.radius^2*(x j)^2=
        (x j)^2/row.radius^2*endpointLogExcess (endpointLogratioZ row.meanBound row.radius) := by ring
    rw [he] at hstep2
    exact hstep1.trans (hstep2.trans hmul)
  have hsum := Finset.sum_le_sum (s := Finset.univ.erase top)
    (fun j hj => hrestTerm j (Finset.mem_erase.mp hj).1)
  rw [← Finset.sum_mul,← Finset.sum_div] at hsum
  have hmass : (∑j∈Finset.univ.erase top,(x j)^2)/row.radius^2≤1 :=
    (div_le_one (sq_pos_of_pos hr.1)).2 hrest2
  have hlast := mul_le_mul_of_nonneg_right hmass (endpointLogExcess_nonneg hct.2)
  rw [one_mul] at hlast
  have hErase := Finset.sum_erase_add Finset.univ
    (fun j => endpointLogExcess ((12/5 : ℝ)*normalizedUpperEigenvalue x j)) (Finset.mem_univ top)
  linarith

end
end SingularValueBounds.KL
