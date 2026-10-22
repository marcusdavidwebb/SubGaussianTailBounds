import SingularValueBounds.KL.Upper.EndpointLogratio
import SingularValueBounds.KL.Upper.ComparisonNormMatrices

/-! # Concentrated spectral rows for the endpoint MGF (supplementary S1.6.4)

The interval restrictions, complementary norm and largest comparison
eigenvalue bounds are analytic consequences of the normalized spectrum.
-/
open Set
open scoped BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1500000

structure EndpointSpectralRow where
  lo : ℝ
  hi : ℝ
  radius : ℝ
  meanBound : ℝ
  topBound : ℝ
  restBound : ℝ
  gap : ℝ

def endpointSpectralRow (i : Fin 3) : EndpointSpectralRow :=
  if i=0 then ⟨15/16,47/50,87/250,1087991/1250000,13/250,37/100,31239/10000⟩
  else if i=1 then ⟨47/50,19/20,171/500,111/125,1/20,183/500,313/100⟩
  else ⟨19/20,1,5/16,1,1/25,7/20,63/20⟩

def spectralComplementMoment (x : ℝ) : ℝ := x^3+Real.sqrt (1-x^2)^3

theorem spectralComplementMoment_monotone :
    MonotoneOn spectralComplementMoment (Icc (9/10 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · unfold spectralComplementMoment; fun_prop
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0<x := by linarith [hx.1]
    have hd : 0<1-x^2 := by nlinarith [hx.2]
    have hf := ((hasDerivAt_id x).pow 3).add
      (((hasDerivAt_const x 1).sub ((hasDerivAt_id x).pow 2)).sqrt hd.ne' |>.pow 3)
    exact hf.differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0<x := by linarith [hx.1]
    have hd : 0<1-x^2 := by nlinarith [hx.2]
    have hs0 : 0<Real.sqrt (1-x^2) := Real.sqrt_pos.mpr hd
    have hs2 := Real.sq_sqrt hd.le
    have hsx : Real.sqrt (1-x^2)≤x := by nlinarith [hx.1]
    have hf := ((hasDerivAt_id x).pow 3).add
      (((hasDerivAt_const x 1).sub ((hasDerivAt_id x).pow 2)).sqrt hd.ne' |>.pow 3)
    have he : HasDerivAt spectralComplementMoment
        (3*x*(x-Real.sqrt (1-x^2))) x := by
      convert hf using 1
      simp only [spectralComplementMoment,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,zero_sub]
      field_simp [hs0.ne']
      nlinarith [hs2]
    rw [he.deriv]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hsx)

theorem endpoint_cubic_monotone {A : ℝ} (hA : 0≤A) :
    MonotoneOn (fun x : ℝ => x+A*x^2-2*x^3) (Icc 0 (7/20)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · fun_prop
  · fun_prop
  · intro x hx
    have hx' : x∈Icc (0 : ℝ) (7/20) := interior_subset hx
    have hd : HasDerivAt (fun x : ℝ => x+A*x^2-2*x^3) (1+2*A*x-6*x^2) x := by
      convert ((hasDerivAt_id x).add (((hasDerivAt_id x).pow 2).const_mul A)).sub
        (((hasDerivAt_id x).pow 3).const_mul 2) using 1 <;> simp only [id_eq] <;> ring
    rw [hd.deriv]
    have hx2 := pow_le_pow_left₀ hx'.1 hx'.2 2
    nlinarith [mul_nonneg hA hx'.1]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem endpoint_spectral_row_bounds (i : Fin 3) {x : ι → ℝ}
    (hx : ∀j,0≤x j) (h2 : ∑j,x j^2=1) (top : ι)
    (hκ : x top∈Icc (endpointSpectralRow i).lo (endpointSpectralRow i).hi) :
    normalizedUpperMean x≤(endpointSpectralRow i).meanBound ∧
    normalizedUpperEigenvalue x top≤(endpointSpectralRow i).topBound ∧
    (∀j,j≠top → x j≤(endpointSpectralRow i).radius) ∧
    (∑j∈Finset.univ.erase top,x j^2)≤(endpointSpectralRow i).radius^2 ∧
    (∀j,j≠top → normalizedUpperEigenvalue x j≤
      x j+(endpointSpectralRow i).meanBound*x j^2-2*x j^3) ∧
    (endpointSpectralRow i).radius+(endpointSpectralRow i).meanBound*
      (endpointSpectralRow i).radius^2-2*(endpointSpectralRow i).radius^3≤
        (endpointSpectralRow i).restBound ∧
    (endpointSpectralRow i).gap≤23/10+normalizedUpperMean x := by
  let row := endpointSpectralRow i
  have hrowLo : (9/10 : ℝ)≤row.lo := by fin_cases i <;> norm_num [row,endpointSpectralRow]
  have hrowHi : row.hi≤1 := by fin_cases i <;> norm_num [row,endpointSpectralRow]
  have hr0 : 0≤row.radius := by fin_cases i <;> norm_num [row,endpointSpectralRow]
  have hr2 : 1-row.lo^2≤row.radius^2 := by fin_cases i <;> norm_num [row,endpointSpectralRow]
  have hmA : (1/2 : ℝ)≤row.meanBound := by fin_cases i <;> norm_num [row,endpointSpectralRow]
  have heps : 0≤1-(x top)^2 := by
    have hs := normalized_upper_coordinate_le_one hx h2 top
    nlinarith [hx top]
  have hepslo : 1-(x top)^2≤1-row.lo^2 := by
    have hlo0 : 0≤row.lo := by linarith
    have hh := pow_le_pow_left₀ hlo0 hκ.1 2
    linarith
  have hrest : Real.sqrt (1-(x top)^2)≤row.radius := by
    have hs := Real.sq_sqrt heps
    have hs0 := Real.sqrt_nonneg (1-(x top)^2)
    nlinarith
  have haComplement := normalized_upper_mean_le_complement hx h2 top
  have hA : normalizedUpperMean x≤row.meanBound := by
    by_cases hiLast : i=2
    · subst i
      simpa [row,endpointSpectralRow] using (normalized_upper_mean_bounds hx h2).2
    · have hmono := spectralComplementMoment_monotone
        ⟨hrowLo.trans hκ.1,hκ.2.trans hrowHi⟩ ⟨hrowLo.trans (hκ.1.trans hκ.2),hrowHi⟩ hκ.2
      have hhi0 : 0≤1-row.hi^2 := by
        have hh : 0≤row.hi := (hx top).trans hκ.2
        nlinarith
      have hS := Real.sq_sqrt hhi0
      have hS0 := Real.sqrt_nonneg (1-row.hi^2)
      have hnumeric : row.hi^3+(1-row.hi^2)*
          (if i=0 then (171/500 : ℝ) else 5/16)≤row.meanBound := by
        fin_cases i <;> norm_num [row,endpointSpectralRow] at *
      have hSupper : Real.sqrt (1-row.hi^2)≤
          (if i=0 then (171/500 : ℝ) else 5/16) := by
        fin_cases i <;> norm_num [row,endpointSpectralRow] at * <;> nlinarith
      have hcube : Real.sqrt (1-row.hi^2)^3≤(1-row.hi^2)*
          (if i=0 then (171/500 : ℝ) else 5/16) := by
        rw [pow_succ,hS]
        exact mul_le_mul_of_nonneg_left hSupper hhi0
      dsimp [spectralComplementMoment] at hmono
      linarith
  have htop : normalizedUpperEigenvalue x top≤row.topBound := by
    have hcomp : normalizedUpperEigenvalue x top≤
        x top*(1-(x top)^2)^2+(x top)^2*(1-(x top)^2)*Real.sqrt (1-(x top)^2) := by
      have hh := mul_le_mul_of_nonneg_right haComplement (sq_nonneg (x top))
      dsimp [normalizedUpperEigenvalue]
      have hc : Real.sqrt (1-(x top)^2)^3=(1-(x top)^2)*Real.sqrt (1-(x top)^2) := by
        rw [pow_succ,Real.sq_sqrt heps]
      rw [hc] at hh
      nlinarith
    have hκ0 := hx top
    have hhi0 : 0≤row.hi := hκ0.trans hκ.2
    have heps0 : 0≤1-row.lo^2 := heps.trans hepslo
    have hfirst := mul_le_mul hκ.2 (pow_le_pow_left₀ heps hepslo 2)
      (sq_nonneg _) hhi0
    have hsecond := mul_le_mul (mul_le_mul (pow_le_pow_left₀ hκ0 hκ.2 2) hepslo
      heps (sq_nonneg row.hi)) hrest (Real.sqrt_nonneg _) (by positivity : 0≤row.hi^2*(1-row.lo^2))
    have hnumeric : row.hi*(1-row.lo^2)^2+row.hi^2*(1-row.lo^2)*row.radius≤row.topBound := by
      fin_cases i <;> norm_num [row,endpointSpectralRow]
    linarith
  have hsumErase : (∑j∈Finset.univ.erase top,x j^2)=1-(x top)^2 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ top),h2]
  have hrestj (j : ι) (hj : j≠top) : x j≤row.radius := by
    have hs := Finset.single_le_sum (s := Finset.univ.erase top)
      (fun k hk => sq_nonneg (x k)) (show j∈Finset.univ.erase top by simp [hj])
    rw [hsumErase] at hs
    nlinarith [hx j]
  refine ⟨hA,htop,hrestj,?_,?_,?_,?_⟩
  · rw [hsumErase]
    exact hepslo.trans hr2
  · intro j hj
    have hh := mul_le_mul_of_nonneg_right hA (sq_nonneg (x j))
    dsimp [normalizedUpperEigenvalue]
    linarith
  · fin_cases i <;> norm_num [row,endpointSpectralRow]
  · have hc : (x top)^3≤normalizedUpperMean x :=
      Finset.single_le_sum (s := Finset.univ) (fun j hj => pow_nonneg (hx j) _) (Finset.mem_univ top)
    have hlo0 : 0≤row.lo := by linarith
    have hp := pow_le_pow_left₀ hlo0 hκ.1 3
    have hn : row.gap≤23/10+row.lo^3 := by fin_cases i <;> norm_num [row,endpointSpectralRow]
    linarith

end
end SingularValueBounds.KL
