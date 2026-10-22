import SingularValueBounds.KL.Upper.EndpointMeanEnvelope

open MeasureTheory Set
open scoped BigOperators
namespace SingularValueBounds.KL
open Certificates
noncomputable section
set_option maxHeartbeats 1800000

theorem endpoint_mean_joint_survival (h : EndpointMeanCertificateConditions)
    (ki : Fin 60) (ai : Fin 42) (hact : endpointMeanActive ki ai) {a k : ℝ}
    (hbox : (endpointMeanBox ki ai).contains a k) {T : ℝ → ℝ}
    (hT : Antitone T) (hT0 : ∀u,0≤T u)
    (hTail : ∀u,0≤u → T u≤(31623/10000 : ℝ)*Real.exp (-((9/20 : ℝ)*u)))
    (hJoint : ∀j∈Finset.Ico (endpointMeanCutoff ki ai) 8000,
      T ((j : ℝ)/200)≤upperJointPrefactor ((endpointMeanRate ki ai j : ℝ)/100) a k*
        Real.exp (-(((endpointMeanRate ki ai j : ℝ)/100)*((j : ℝ)/200)/2))) :
    Real.log ((endpointMeanCutoff ki ai : ℝ)/200)+
      (∫u in Ioi ((endpointMeanCutoff ki ai : ℝ)/200),
        entropyKernel ((endpointMeanCutoff ki ai : ℝ)/200) u*T u)≤
      realEval₂ (endpointMeanBilinearQ ki ai) a k := by
  have hc := h.jointCutoff ki ai hact
  have hd : Real.exp (-(18 : ℝ))≤(endpointDecayQ 90 8000 : ℝ) := by
    convert (h.decays 90 (by norm_num)).sound (j := 8000) (by norm_num) using 1 <;> norm_num
  have hg := entropy_grid_bound_real hc.1 hc.2 hT hT0 hTail
    (h.gridLogs _ (by simp only [Finset.mem_Icc]; omega))
    (fun j hj => by
      simpa only [Nat.cast_add,Nat.cast_one] using
        h.gridLogs (j+1) (by simp only [Finset.mem_Icc]; have := Finset.mem_Ico.mp hj; omega))
    (B := fun j => upperJointPrefactor ((endpointMeanRate ki ai j : ℝ)/100) a k*
      (endpointDecayQ (endpointMeanRate ki ai j) j : ℝ)) (by
      intro j hj
      have hr := h.jointRates ki ai hact j hj
      have hdec := (h.decays _ (Finset.mem_Icc.mpr ⟨hr.1,hr.2.1⟩)).sound
        (j := j) (by have := Finset.mem_Ico.mp hj; omega)
      exact (hJoint j hj).trans (mul_le_mul_of_nonneg_left hdec (Real.exp_nonneg _))) hd
  rw [← endpointMeanEnvelope_eq_grid] at hg
  exact hg.trans (endpointMeanEnvelope_bilinear h ki ai hact hbox)

theorem endpoint_mean_small_survival (h : EndpointMeanCertificateConditions)
    (i : Fin 50) {T : ℝ → ℝ} (hT : Antitone T) (hT0 : ∀u,0≤T u)
    (hT1 : ∀u,T u≤1)
    (hTail : ∀u,0≤u → T u≤(31623/10000 : ℝ)*Real.exp (-((9/20 : ℝ)*u)))
    (hMargin : ∀j∈Finset.Ico (endpointSmallCutoff i) 8000,∀v : Fin 23,
      let q : ℚ := (endpointSmallQ v : ℚ)/100
      ((j : ℚ)/200*endpointSmallK i*(q-1)≤58/25) →
      T ((j : ℝ)/200)≤Real.exp (-Real.log (1-(q : ℝ)*(endpointSmallK i : ℝ)^2)/
        (2*(endpointSmallK i : ℝ)^2)-(q : ℝ)*((j : ℝ)/200)/2)) :
    Real.log ((endpointSmallCutoff i : ℝ)/200)+
      (∫u in Ioi ((endpointSmallCutoff i : ℝ)/200),
        entropyKernel ((endpointSmallCutoff i : ℝ)/200) u*T u)≤(endpointSmallTarget i : ℝ) := by
  have hc := h.smallCutoff i
  have hd : Real.exp (-(18 : ℝ))≤(endpointDecayQ 90 8000 : ℝ) := by
    convert (h.decays 90 (by norm_num)).sound (j := 8000) (by norm_num) using 1 <;> norm_num
  have hg := entropy_grid_bound_real hc.1 hc.2 hT hT0 hTail
    (h.gridLogs _ (by simp only [Finset.mem_Icc]; omega))
    (fun j hj => by
      simpa only [Nat.cast_add,Nat.cast_one] using
        h.gridLogs (j+1) (by simp only [Finset.mem_Icc]; have := Finset.mem_Ico.mp hj; omega))
    (B := fun j => (endpointSmallBound i j : ℝ)) (by
      intro j hj
      have hRat : ∀v : Fin 23,T ((j : ℝ)/200)≤(endpointSmallBoundTerm i j v : ℝ) := by
        intro v
        unfold endpointSmallBoundTerm
        dsimp only
        split_ifs with hm
        · have htail := hMargin j hj v hm
          have hp := (h.smallPrefactors i v).sound
          push_cast at hp
          have hqi : endpointSmallQ v∈Finset.Icc 90 200 := by
            simp only [endpointSmallQ,Finset.mem_Icc]
            have hv := v.isLt
            omega
          have hdec := (h.decays _ hqi).sound (j := j) (by have := Finset.mem_Ico.mp hj; omega)
          rw [Real.exp_sub] at htail
          have he : Real.exp (-Real.log (1-((endpointSmallQ v : ℚ)/100 : ℚ)*
              (endpointSmallK i : ℝ)^2)/(2*(endpointSmallK i : ℝ)^2)-
                ((endpointSmallQ v : ℚ)/100 : ℚ)*((j : ℝ)/200)/2)=
              Real.exp (-Real.log (1-((endpointSmallQ v : ℚ)/100 : ℚ)*
                (endpointSmallK i : ℝ)^2)/(2*(endpointSmallK i : ℝ)^2))*
                  Real.exp (-((endpointSmallQ v : ℝ)/100*((j : ℝ)/200)/2)) := by
            rw [Real.exp_sub,Real.exp_neg]
            push_cast
            rfl
          have hb := hMargin j hj v hm
          rw [he] at hb
          have hRound : ((endpointSmallPrefactorQ (endpointSmallK i) ((endpointSmallQ v : ℚ)/100)*
              endpointDecayQ (endpointSmallQ v) j : ℚ) : ℝ)≤
              (roundUpQ (endpointSmallPrefactorQ (endpointSmallK i) ((endpointSmallQ v : ℚ)/100)*
                endpointDecayQ (endpointSmallQ v) j) : ℝ) := by exact_mod_cast h.smallRounding i j hj v
          apply hb.trans
          apply le_trans _ hRound
          push_cast
          exact mul_le_mul hp hdec (Real.exp_nonneg _) ((Real.exp_nonneg _).trans hp)
        · simpa only [Rat.cast_one] using hT1 ((j : ℝ)/200)
      unfold endpointSmallBound
      push_cast
      apply le_min (hT1 _)
      obtain ⟨v,hv,hInf⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (endpointSmallBoundTerm i j)
      rw [hInf]
      exact hRat v) hd
  have hn : (entropyGridBoundQ (endpointSmallCutoff i) (endpointSmallBound i)
      (endpointDecayQ 90 8000) : ℝ)≤(endpointSmallTarget i : ℝ) := by exact_mod_cast h.smallNumerical i
  apply hg.trans
  convert hn using 1 <;> unfold entropyGridBoundReal entropyGridBoundQ <;> push_cast <;> rfl

end
end SingularValueBounds.KL
