import SingularValueBounds.KL.Upper.EndpointMeanFinite

open Polynomial Set
open scoped Polynomial BigOperators Matrix
namespace SingularValueBounds.KL
open Certificates
noncomputable section
set_option maxHeartbeats 1800000

theorem endpointMeanBilinear_eval (ki : Fin 60) (ai : Fin 42) (a k : ℝ) :
    realEval₂ (endpointMeanBilinearQ ki ai) a k=
      let b := endpointMeanBox ki ai
      let D := endpointMeanCorner ki ai
      let ac : ℝ := (D 1-D 0 : ℚ)/(b.right-b.left)
      let kc : ℝ := (D 2-D 0 : ℚ)/(b.top-b.bottom)
      let cross : ℝ := (D 3-D 2-D 1+D 0 : ℚ)/((b.right-b.left)*(b.top-b.bottom))
      D 0+ac*(a-b.left)+kc*(k-b.bottom)+cross*(a-b.left)*(k-b.bottom) := by
  dsimp only [endpointMeanBilinearQ,realEval₂]
  simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_C,
    Polynomial.eval₂_X,Polynomial.coe_eval₂RingHom]
  simp only [Rat.coe_castHom]
  push_cast
  ring

theorem endpointMeanBilinear_eq_corners (ki : Fin 60) (ai : Fin 42)
    (h : endpointMeanActive ki ai) (a k : ℝ) :
    realEval₂ (endpointMeanBilinearQ ki ai) a k=
      let b := endpointMeanBox ki ai
      let D := endpointMeanCorner ki ai
      ((b.right-a)/(b.right-b.left))*((b.top-k)/(b.top-b.bottom))*D 0+
      ((a-b.left)/(b.right-b.left))*((b.top-k)/(b.top-b.bottom))*D 1+
      ((b.right-a)/(b.right-b.left))*((k-b.bottom)/(b.top-b.bottom))*D 2+
      ((a-b.left)/(b.right-b.left))*((k-b.bottom)/(b.top-b.bottom))*D 3 := by
  have ha : ((endpointMeanBox ki ai).right : ℝ)-(endpointMeanBox ki ai).left≠0 := by
    have hh : ((endpointMeanBox ki ai).left : ℝ)<(endpointMeanBox ki ai).right := by exact_mod_cast h.1
    linarith
  have hk : ((endpointMeanBox ki ai).top : ℝ)-(endpointMeanBox ki ai).bottom≠0 := by
    dsimp [endpointMeanBox]
    push_cast
    linarith
  rw [endpointMeanBilinear_eval]
  dsimp only
  push_cast
  field_simp [ha,hk]
  <;> ring

theorem endpointMeanTest_eval (ki : Fin 60) (ai : Fin 42) (a k : ℝ) :
    realEval₂ (endpointMeanTestQ ki ai) a k=
      let E := realEval₂ (endpointMeanBilinearQ ki ai) a k
      let i := endpointMeanMajorantIndex (endpointMeanChoice ki ai)
      if endpointMeanChoice ki ai=3 then
        58/25-E-(-2*a+(671/100)*(1-a^2-a^2*(1-a)^2))/2 else
        (58/25-E-upperMajorantB i a/2+upperMajorantH i a k/2)*upperPadeD (upperComparisonZ a k)-
          upperPadeN (upperComparisonZ a k)/2 := by
  let e : Polynomial (Polynomial ℚ) →+* ℝ :=
    Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Rat.castHom ℝ) a) k
  have he (p : Polynomial (Polynomial ℚ)) : e p=realEval₂ p a k := rfl
  have hC (p : ℚ[X]) : e (C p)=realEval p a := by simp [e,realEval]
  have hCC (q : ℚ) : e (C (C q))=(q : ℝ) := by simp [e]
  have hX : e X=k := by simp [e]
  have hCX : e (C X)=a := by simp [e]
  have hZ : e comparisonZQ=upperComparisonZ a k := by
    simp only [comparisonZQ,map_mul,map_sub,map_add,map_pow,map_ofNat,hX,hCX]
    rfl
  have hB (i : Fin 6) : e (C (majorantBQ i))=upperMajorantB i a := by
    rw [hC,majorantBQ_eval]
  have hA (i : Fin 6) : e (C (majorantAQ i))=upperMajorantA i a := by
    rw [hC,majorantAQ_eval]
  have hH (i : Fin 6) : e (majorantHQ i)=upperMajorantH i a k := by
    simp only [majorantHQ,map_add,map_sub,map_mul,map_pow,map_ofNat,hX,hCX,hB,hA]
    rfl
  have hD : e (padeDQ comparisonZQ)=upperPadeD (upperComparisonZ a k) := by
    simp only [padeDQ,map_sub,map_add,map_mul,map_pow,map_one,hCC,hZ]
    norm_num [upperPadeD]
  have hN : e (padeNQ comparisonZQ)=upperPadeN (upperComparisonZ a k) := by
    simp only [padeNQ,map_sub,map_add,map_mul,map_pow,hCC,hZ]
    norm_num [upperPadeN]
  have hJ : e endpointMeanJ0Q=-2*a+(671/100)*(1-a^2-a^2*(1-a)^2) := by
    simp [endpointMeanJ0Q,e,Polynomial.eval₂_pow,Polynomial.eval₂_sub]
  change e (endpointMeanTestQ ki ai)=_
  dsimp only [endpointMeanTestQ]
  split_ifs with hh
  · simp only [map_sub,map_mul,hCC,hJ,hh,if_true]
    rw [he (endpointMeanBilinearQ ki ai)]
    norm_num
    ring
  · simp only [map_sub,map_mul,map_add,hCC,hB,hH,hD,hN,hh,if_false]
    rw [he (endpointMeanBilinearQ ki ai)]
    norm_num
    ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem endpoint_mean_polynomial_cost (h : EndpointMeanCertificateConditions)
    (hmajor : MajorantCertificateConditions) (hnorm : NormDeterminantCertificateConditions)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (ki : Fin 60) (ai : Fin 42)
    (hact : endpointMeanActive ki ai)
    (hbox : (endpointMeanBox ki ai).contains (upperComparisonShapeMean R hR) (spectralRatio R hR))
    {D : ℝ} (hD : D≤realEval₂ (endpointMeanBilinearQ ki ai)
      (upperComparisonShapeMean R hR) (spectralRatio R hR)) :
    D+upperComparisonMatrixLogdet R/2≤58/25 := by
  let a := upperComparisonShapeMean R hR
  let k := spectralRatio R hR
  let i := endpointMeanMajorantIndex (endpointMeanChoice ki ai)
  obtain ⟨n, m, hCertificate⟩ := h.polynomialTests ki ai hact
  have hPoly := hCertificate.nonneg hbox
  rw [endpointMeanTest_eval] at hPoly
  have hDomain := h.chosenDomain ki ai hact
  by_cases hn : endpointMeanChoice ki ai=3
  · rw [if_pos hn] at hPoly
    have hJ := upperComparisonMatrixLogdet_J0 hnorm hR
    try dsimp only at hPoly
    linarith
  · rw [if_neg hn] at hPoly hDomain
    have hdl : ((majorantBoxes i).left : ℝ)≤(endpointMeanBox ki ai).left := by exact_mod_cast hDomain.1
    have hdr : ((endpointMeanBox ki ai).right : ℝ)≤(majorantBoxes i).right := by exact_mod_cast hDomain.2.1
    have hdt : ((endpointMeanBox ki ai).top : ℝ)≤(majorantBoxes i).top := by exact_mod_cast hDomain.2.2
    have ha : a∈Icc ((majorantBoxes i).left : ℝ) ((majorantBoxes i).right : ℝ) :=
      ⟨hdl.trans hbox.1.1,hbox.1.2.trans hdr⟩
    have hk : k≤((majorantBoxes i).top : ℝ) := hbox.2.2.trans hdt
    have hJ := upperComparisonMatrixLogdet_joint_max hmajor i hR ha hk
    have ha1 : a≤5/6 := by
      have hh : ∀j : Fin 6,((majorantBoxes j).right : ℝ)≤5/6 := by
        intro j
        fin_cases j <;> norm_num [majorantBoxes]
      exact ha.2.trans (hh i)
    have hk0 := (spectralRatio_pos_le_one hR).1.le
    have hk1 := (spectralRatio_pos_le_one hR).2
    have hPD := upperPadeD_pos (upperComparisonZ_lt_one ha1 hk0 hk1)
    have hRatio : upperPadeN (upperComparisonZ a k)/upperPadeD (upperComparisonZ a k)≤
        2*(58/25-realEval₂ (endpointMeanBilinearQ ki ai) a k)-upperMajorantB i a+upperMajorantH i a k := by
      apply (div_le_iff₀ hPD).2
      try dsimp only at hPoly
      change 0≤(58/25-realEval₂ (endpointMeanBilinearQ ki ai) a k-upperMajorantB i a/2+
        upperMajorantH i a k/2)*upperPadeD (upperComparisonZ a k)-upperPadeN (upperComparisonZ a k)/2 at hPoly
      nlinarith
    dsimp [a,k] at hRatio
    linarith

end
end SingularValueBounds.KL
