import SingularValueBounds.KL.Upper.GeneralMeanCoverage

/-! Continuous determinant bounds for every general-mean spectral cell. -/
open Polynomial Set
open scoped Polynomial Matrix BigOperators
namespace SingularValueBounds.KL
open Certificates
noncomputable section
set_option maxHeartbeats 1800000

lemma generalMeanJointCleared_eval (J : ℚ) (i : Fin 6) (a k : ℝ) :
    realEval₂ (generalMeanJointCleared J i) a k =
      ((J:ℝ)-upperMajorantB i a+upperMajorantH i a k)*upperPadeD (upperComparisonZ a k)-
        upperPadeN (upperComparisonZ a k) := by
  have hD : realEval₂ (padeDQ comparisonZQ) a k=upperPadeD (upperComparisonZ a k) := by
    simp only [realEval₂,padeDQ,comparisonZQ,Polynomial.eval₂_mul,Polynomial.eval₂_add,
      Polynomial.eval₂_sub,Polynomial.eval₂_C,Polynomial.eval₂_X,Polynomial.eval₂_pow,
      Polynomial.eval₂_one,Polynomial.coe_eval₂RingHom]
    norm_num [upperPadeD,upperComparisonZ]
  change realEval₂ (C (C J-majorantBQ i)*padeDQ comparisonZQ+majorantCleared i) a k=_
  simp only [realEval₂,Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_C,
    Polynomial.coe_eval₂RingHom,Polynomial.eval₂_sub]
  change ((J:ℝ)-realEval (majorantBQ i) a)*realEval₂ (padeDQ comparisonZQ) a k+
    realEval₂ (majorantCleared i) a k=_
  rw [majorantBQ_eval,hD,majorantCleared_eval]
  ring

lemma generalMeanNormQ_eval (J B : ℚ) (a k : ℝ) :
    realEval₂ (C (C J-generalMeanNormQ B)) a k=
      (J:ℝ)-(-2*a+(B:ℝ)*(1-a^2-a^2*(1-a)^2)) := by
  simp [realEval₂,generalMeanNormQ,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_sub,
    Polynomial.eval₂_pow]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A finite row certificate bounds the actual scale-invariant matrix log determinant. -/
theorem general_mean_row_logdet (hmajor : MajorantCertificateConditions)
    (hnorm : NormDeterminantCertificateConditions) {r : GeneralMeanRow}
    (h : GeneralMeanRowConditions r) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (hm : r.box.contains (upperComparisonShapeMean R hR) (spectralRatio R hR)) :
    upperComparisonMatrixLogdet R ≤ (r.J:ℝ) := by
  let a:=upperComparisonShapeMean R hR
  let k:=spectralRatio R hR
  have hrest := h.2.2.2.2.2
  by_cases hi : r.majorant.val<6
  · rw [dif_pos hi] at hrest
    let i : Fin 6:=⟨r.majorant.val,hi⟩
    have hlo : ((majorantBoxes i).left:ℝ)≤r.alo := by exact_mod_cast hrest.1
    have hhi : (r.ahi:ℝ)≤(majorantBoxes i).right := by exact_mod_cast hrest.2.1
    have htop : (r.khi:ℝ)≤(majorantBoxes i).top := by exact_mod_cast hrest.2.2.1
    have ha : a∈Icc ((majorantBoxes i).left:ℝ) ((majorantBoxes i).right:ℝ) :=
      ⟨hlo.trans hm.1.1,hm.1.2.trans hhi⟩
    have hk : k≤((majorantBoxes i).top:ℝ) := hm.2.2.trans htop
    have hJ := upperComparisonMatrixLogdet_joint_max hmajor i hR ha hk
    have hp := hrest.2.2.2.nonneg hm
    rw [generalMeanJointCleared_eval] at hp
    have hak := majorant_domain_bounds i
      (show (majorantBoxes i).contains a k from ⟨ha,by
        have hzall : ∀ j : Fin 6,(majorantBoxes j).bottom=0 := by
          intro j
          fin_cases j <;> norm_num [majorantBoxes]
        have hz := hzall i
        rw [hz,Rat.cast_zero]
        exact (spectralRatio_pos_le_one hR).1.le,hk⟩)
    have hz := upperComparisonZ_lt_one hak.1 hak.2.1
    have hD := upperPadeD_pos hz
    have hdiv : upperPadeN (upperComparisonZ a k)/upperPadeD (upperComparisonZ a k)≤
        (r.J:ℝ)-upperMajorantB i a+upperMajorantH i a k :=
      (div_le_iff₀ hD).2 (by simpa [i,a,k] using hp)
    dsimp [a,k] at hdiv
    linarith
  · rw [dif_neg hi] at hrest
    have hp := hrest.2.nonneg hm
    rw [generalMeanNormQ_eval] at hp
    rcases hrest.1 with ⟨h6,hlo⟩|⟨h7,hlo⟩
    · norm_num [h6] at hp
      have hJ := upperComparisonMatrixLogdet_J0 hnorm hR
      linarith
    · have hne : ¬r.majorant.val=6 := by omega
      simp only [if_neg hne] at hp
      have hloR : (37/40:ℝ)≤r.klo := by
        have hh := (Rat.cast_le (K:=ℝ)).2 hlo
        norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
        exact hh
      have hJ := upperComparisonMatrixLogdet_J1 hnorm hR (hloR.trans hm.2.1)
      norm_num only [Rat.cast_div,Rat.cast_ofNat] at hp
      linarith

/-- Every feasible spectrum above κ=2/5 has one certified row, including boundaries. -/
theorem general_mean_spectral_row (hcells : GeneralMeanCellConditions)
    (hmajor : MajorantCertificateConditions) (hnorm : NormDeterminantCertificateConditions)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hk : (2/5:ℝ)≤spectralRatio R hR) :
    ∃ i : Fin 1330,(generalMeanRows i).box.contains (upperComparisonShapeMean R hR)
      (spectralRatio R hR) ∧ upperComparisonMatrixLogdet R≤((generalMeanRows i).J:ℝ) := by
  obtain ⟨i,hi⟩ := general_mean_cells_cover hcells ⟨hk,(spectralRatio_pos_le_one hR).2⟩
    (upperComparisonShapeMean_ratio_bounds hR)
  exact ⟨i,hi,general_mean_row_logdet hmajor hnorm (hcells.2.2 i) hR hi⟩

/-- The separate small-shape row uses the constant fifth scalar majorant. -/
theorem general_mean_small_logdet (hmajor : MajorantCertificateConditions)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hk : spectralRatio R hR≤2/5) :
    upperComparisonMatrixLogdet R≤(generalMeanSmallRow.J:ℝ) := by
  have ha:=upperComparisonShapeMean_ratio_bounds hR
  have hk0 := (spectralRatio_pos_le_one hR).1.le
  have ha0 : 0≤upperComparisonShapeMean R hR := (pow_nonneg hk0 3).trans ha.1
  have hh := upperComparisonMatrixLogdet_six hmajor (i:=⟨4,by decide⟩) hR
    (show upperComparisonShapeMean R hR∈Icc ((majorantBoxes ⟨4,by decide⟩).left:ℝ)
      ((majorantBoxes ⟨4,by decide⟩).right:ℝ) by
        norm_num [majorantBoxes];exact ⟨ha0,by linarith [ha.2]⟩)
    (show spectralRatio R hR≤((majorantBoxes ⟨4,by decide⟩).top:ℝ) by
      norm_num [majorantBoxes];linarith)
  norm_num [upperMajorantB] at hh
  norm_num [generalMeanSmallRow]
  exact hh

end
end SingularValueBounds.KL
