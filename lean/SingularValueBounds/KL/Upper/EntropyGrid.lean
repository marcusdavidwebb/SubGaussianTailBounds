import SingularValueBounds.KL.Upper.EntropyQuadrature
import SingularValueBounds.KL.Upper.RoundedAlgorithmSoundness

/-! # The printed 1/200 entropy grid, interpreted analytically -/
open MeasureTheory Set
open scoped BigOperators
namespace SingularValueBounds.KL
open Certificates
noncomputable section
set_option maxHeartbeats 1500000

def entropyGridKernelQ (j0 j : ℕ) : ℚ :=
  1+(logRoundedQ ((j+1 : ℚ)/200)).2-(logRoundedQ ((j0 : ℚ)/200)).1

def entropyGridTailQ (j0 : ℕ) (decay : ℚ) : ℚ :=
  (31623/10000)*decay*(1/(9/20)+40/(((j0 : ℚ)/200)*(9/20))+
    1/(((j0 : ℚ)/200)*(9/20)^2))

def entropyGridBoundQ (j0 : ℕ) (B : ℕ → ℚ) (decay : ℚ) : ℚ :=
  (logRoundedQ ((j0 : ℚ)/200)).2+
    (∑j∈Finset.Ico j0 8000,entropyGridKernelQ j0 j*B j/200)+entropyGridTailQ j0 decay

theorem entropyGridKernel_bound {j0 j : ℕ} (hj0 : 0<j0) (hj : j0≤j)
    (hl0 : RoundedLogConditions ((j0 : ℚ)/200))
    (hlj : RoundedLogConditions ((j+1 : ℚ)/200)) :
    0≤entropyKernel ((j0 : ℝ)/200) ((j+1 : ℝ)/200) ∧
      entropyKernel ((j0 : ℝ)/200) ((j+1 : ℝ)/200)≤(entropyGridKernelQ j0 j : ℝ) := by
  have hc : (0 : ℝ)<(j0 : ℝ)/200 := by positivity
  have hu : (0 : ℝ)<(j+1 : ℝ)/200 := by positivity
  have hle : (j0 : ℝ)/200≤(j+1 : ℝ)/200 := by
    have hh : (j0 : ℝ)≤(j : ℝ)+1 := by exact_mod_cast (by omega : j0≤j+1)
    linarith
  refine ⟨entropyKernel_nonneg hc hle,?_⟩
  have h0 := hl0.sound.1
  have hj' := hlj.sound.2
  norm_num only [Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_add,Rat.cast_one] at h0 hj'
  dsimp [entropyKernel,entropyGridKernelQ]
  push_cast
  rw [Real.log_div hu.ne' hc.ne']
  linarith

theorem entropyGridKernel_nonneg {j0 j : ℕ} (hj0 : 0<j0) (hj : j0≤j)
    (hl0 : RoundedLogConditions ((j0 : ℚ)/200))
    (hlj : RoundedLogConditions ((j+1 : ℚ)/200)) :
    0≤entropyGridKernelQ j0 j := by
  exact_mod_cast (entropyGridKernel_bound hj0 hj hl0 hlj).1.trans
    (entropyGridKernel_bound hj0 hj hl0 hlj).2

def entropyGridBoundReal (j0 : ℕ) (B : ℕ → ℝ) (decay : ℚ) : ℝ :=
  ((logRoundedQ ((j0 : ℚ)/200)).2 : ℝ)+
    (∑j∈Finset.Ico j0 8000,(entropyGridKernelQ j0 j : ℝ)*B j/200)+(entropyGridTailQ j0 decay : ℝ)

/-- Every analytic ingredient of the long entropy sum. The logarithmic and
decay enclosures are supplied by finite rounded-arithmetic transcripts. -/
theorem entropy_grid_bound_real {T : ℝ → ℝ} {j0 : ℕ} {B : ℕ → ℝ} {decay : ℚ}
    (hj0 : 0<j0) (hjEnd : j0≤8000) (hT : Antitone T) (hT0 : ∀u,0≤T u)
    (hTail : ∀u,0≤u → T u≤(31623/10000 : ℝ)*Real.exp (-((9/20 : ℝ)*u)))
    (hl0 : RoundedLogConditions ((j0 : ℚ)/200))
    (hlj : ∀j∈Finset.Ico j0 8000,RoundedLogConditions ((j+1 : ℚ)/200))
    (hB : ∀j∈Finset.Ico j0 8000,T ((j : ℝ)/200)≤B j)
    (hd : Real.exp (-(18 : ℝ))≤(decay : ℝ)) :
    Real.log ((j0 : ℝ)/200)+
      (∫u in Ioi ((j0 : ℝ)/200),entropyKernel ((j0 : ℝ)/200) u*T u)≤
        entropyGridBoundReal j0 B decay := by
  let c : ℝ := (j0 : ℝ)/200
  have hc : 0<c := by dsimp [c]; positivity
  have hc40 : c≤40 := by
    have hh : (j0 : ℝ)≤8000 := by exact_mod_cast hjEnd
    dsimp [c]; linarith
  have hTm : Measurable T := hT.measurable
  have hi := entropy_tail_integrable hc (by norm_num : (0 : ℝ)≤31623/10000)
    (by norm_num : (0 : ℝ)<9/20) hTm hT0
    (fun u hu => hTail u (hc.le.trans hu.le))
  have hQuad := entropy_quadrature_sum (x := fun j : ℕ => (j : ℝ)/200)
    (B := fun j => B j) hc hjEnd
    (fun i j hij => div_le_div_of_nonneg_right (by exact_mod_cast hij) (by norm_num))
    (by rfl) hT hT0 hB (by
      intro j hj
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by push_cast; linarith)).2
      apply hi.mono_set
      intro u hu
      have hh : c≤(j : ℝ)/200 := by
        dsimp [c]
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact_mod_cast (Finset.mem_Ico.mp hj).1
      exact hh.trans_lt hu.1)
  have hSum : (∑j∈Finset.Ico j0 8000,
      (((j+1 : ℕ) : ℝ)/200-(j : ℝ)/200)*entropyKernel c ((j+1 : ℝ)/200)*B j)≤
      ∑j∈Finset.Ico j0 8000,(entropyGridKernelQ j0 j : ℝ)*B j/200 := by
    apply Finset.sum_le_sum
    intro j hj
    have hK := (entropyGridKernel_bound hj0 (Finset.mem_Ico.mp hj).1 hl0 (hlj j hj)).2
    have hB0 : 0≤B j := (hT0 _).trans (hB j hj)
    have hh := mul_le_mul_of_nonneg_right hK hB0
    convert! div_le_div_of_nonneg_right hh (by norm_num : (0 : ℝ)≤200) using 1 <;>
      push_cast <;> dsimp [c] <;> ring
  have hRem := entropy_remainder_bound hc (by norm_num : (0 : ℝ)≤31623/10000)
    (by norm_num : (0 : ℝ)<9/20) hc40 hTm hT0
    (fun u hu => hTail u (hc.le.trans hu.le))
  have hRem' : (∫u in Ioi 40,entropyKernel c u*T u)≤(entropyGridTailQ j0 decay : ℝ) := by
    have hFac : 0≤1/(9/20 : ℝ)+40/(c*(9/20))+1/(c*(9/20)^2) := by positivity
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ)≤31623/10000)) hFac
    norm_num only [show (9/20 : ℝ)*40=18 by norm_num] at hRem
    apply hRem.trans
    convert! hh using 1 <;> dsimp [entropyGridTailQ,c] <;> push_cast <;> norm_num
  have hLog := hl0.sound.2
  norm_num only [Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] at hLog
  rw [entropy_integral_split hc40 hi]
  norm_num only [show (8000 : ℝ)/200=40 by norm_num] at hQuad
  simp only [Nat.cast_add,Nat.cast_one] at hQuad hSum
  have hh := hQuad.trans hSum
  have hTotal := add_le_add (add_le_add hLog hh) hRem'
  convert! hTotal using 1 <;> (try dsimp [entropyGridBoundReal,c]) <;> push_cast <;> ring

end
end SingularValueBounds.KL
