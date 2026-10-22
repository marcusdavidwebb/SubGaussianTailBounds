import SingularValueBounds.KL.Barrier.MixedEnvelope

/-! The scalar cap g(x)=a+x h(ψ_n(x)) from supplementary Lemma S1.6. -/
open Set
open scoped Matrix
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000

def mixedScalarCap (n : ℕ) (a : ℝ) (h : ℝ→ℝ) (x : ℝ) : ℝ :=
  a+x*h (mixedShapeEnvelope n x)

theorem mixedScalarCap_continuous {n : ℕ} (hn : 0<n) (a : ℝ) {h : ℝ→ℝ}
    (hc : Continuous h) : ContinuousOn (mixedScalarCap n a h) (Icc (1/Real.sqrt n) 1) := by
  exact continuousOn_const.add (continuousOn_id.mul
    (hc.comp_continuousOn (mixedShapeEnvelope_continuous hn)))

theorem mixedScalarCap_strictMono {n : ℕ} (hn : 0<n) (a : ℝ) {h : ℝ→ℝ}
    (hm : MonotoneOn h (Icc (0:ℝ) 1))
    (hp : ∀k∈Ioc (0:ℝ) 1,0<h k) :
    StrictMonoOn (mixedScalarCap n a h) (Icc (1/Real.sqrt n) 1) := by
  intro x hx y hy hxy
  have hs : 0<Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hx0 : 0<x := (div_pos zero_lt_one hs).trans_le hx.1
  have hy0 : 0<y := hx0.trans hxy
  have hxr := mixedShapeEnvelope_range hn hx
  have hyr := mixedShapeEnvelope_range hn hy
  have hxp : 0< mixedShapeEnvelope n x := (div_pos zero_lt_one hs).trans_le hxr.1
  have hyp : 0< mixedShapeEnvelope n y := (div_pos zero_lt_one hs).trans_le hyr.1
  have hh := hm ⟨hxp.le,hxr.2⟩ ⟨hyp.le,hyr.2⟩
    (mixedShapeEnvelope_monotone hn hx hy hxy.le)
  have hhp := hp _ ⟨hxp,hxr.2⟩
  unfold mixedScalarCap
  have hstrict := mul_lt_mul_of_pos_right hxy hhp
  have hmono := mul_le_mul_of_nonneg_left hh hy0.le
  linarith

theorem mixedScalarCap_base {n : ℕ} (hn : 0<n) (a : ℝ) (h : ℝ→ℝ) :
    mixedScalarCap n a h (1/Real.sqrt n)=a+(1/Real.sqrt n)*h (1/Real.sqrt n) := by
  rw [mixedScalarCap,mixedShapeEnvelope_base hn]

theorem mixedScalarCap_one {n : ℕ} (hn : 0<n) (a : ℝ) (h : ℝ→ℝ) :
    mixedScalarCap n a h 1=a+h 1 := by rw [mixedScalarCap,mixedShapeEnvelope_one hn,one_mul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem mixedCost_le_scalarCap (a : ℝ) {h : ℝ→ℝ}
    (hm : MonotoneOn h (Icc (0:ℝ) 1)) (R : PositiveResolvent ι) :
    mixedCost a h R≤Matrix.trace R.1*
      mixedScalarCap (Fintype.card ι) a h (frobenius R.1/Matrix.trace R.1) := by
  have hk := spectralRatio_pos_le_one R.2
  have hx := frobenius_trace_ratio_bounds R.2
  have henv := mixedShapeEnvelope_range Fintype.card_pos hx
  have hpsi0 : 0≤ mixedShapeEnvelope (Fintype.card ι) (frobenius R.1/Matrix.trace R.1) :=
    (by positivity : (0:ℝ)≤1/Real.sqrt (Fintype.card ι)).trans henv.1
  have hh := hm ⟨hk.1.le,hk.2⟩ ⟨hpsi0,henv.2⟩ (mixedShapeEnvelope_spectralRatio R.2)
  have ht := trace_pos R.2
  have hmul := mul_le_mul_of_nonneg_left hh (frobenius_nonneg R.1)
  unfold mixedCost mixedScalarCap
  have hid : Matrix.trace R.1*(a+(frobenius R.1/Matrix.trace R.1)*
      h (mixedShapeEnvelope (Fintype.card ι) (frobenius R.1/Matrix.trace R.1)))=
      a*Matrix.trace R.1+frobenius R.1*
        h (mixedShapeEnvelope (Fintype.card ι) (frobenius R.1/Matrix.trace R.1)) := by
    field_simp
  rw [hid]
  linarith

end
end SingularValueBounds.KL
