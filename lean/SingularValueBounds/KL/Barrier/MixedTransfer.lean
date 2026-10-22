import SingularValueBounds.KL.Barrier.MixedInitialization
import SingularValueBounds.KL.Transfer
import SingularValueBounds.KL.Lower.RowEstimates
import SingularValueBounds.KL.Barrier.MixedPathwise

/-! Independent-row transfer for the actual mixed correction rule. The
generic budget constructor is an intermediate analytic interface; its
application is supplied by the proved pathwise mixed-cap budget. -/
open MeasureTheory ProbabilityTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1600000
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m n : ℕ} [NeZero n]

def MixedLowerRowEstimate (X : Ω→Fin n→ℝ) (a : ℝ) (h : ℝ→ℝ) (ν : ℝ) : Prop :=
  ∀ R : PositiveResolvent (Fin n),∀b:ℝ,0<b→mixedCost a h R≤b→∀ℓ:ℝ,0<ℓ→
    Integrable (fun ω=>Real.exp (-ℓ*(1+b)*lowerShift R.1 R.2 (X ω))) μ ∧
      (∫ω,Real.exp (-ℓ*(1+b)*lowerShift R.1 R.2 (X ω)) ∂μ)≤Real.exp (-ℓ/(1+ν*ℓ))

def mixedLowerTransferInput_of_budget
    (X : Fin m→Ω→Fin n→ℝ) (hX : ∀i,Measurable (X i)) (hind : iIndepFun X μ)
    {a : ℝ} (ha : 0≤a) {h : ℝ→ℝ} (hc : Continuous h)
    (hm : MonotoneOn h (Icc (0:ℝ) 1)) (h0 : ∀k∈Icc (0:ℝ) 1,0≤h k)
    {b N ν u : ℝ} (hb : 0<b) (hu : 0<u)
    (hrow : ∀i,MixedLowerRowEstimate (μ:=μ) (X i) a h ν)
    (hbudget : ∀ω,u+(rowProcess (mixedCorrectionRule ha hc hm h0 hb) false
      (scalarResolvent u hu) X m ω).outward≤N/b) : LowerTransferInput μ X N ν b := by
  let c := mixedCorrectionRule (ι:=Fin n) ha hc hm h0 hb
  let R0 := scalarResolvent (ι:=Fin n) u hu
  have hprocess (θ:ℝ) (hθ:θ<0) :
      Integrable (fun ω=>Real.exp (θ*(1+b)*(rowProcess c false R0 X m ω).shifts)) μ ∧
      (∫ω,Real.exp (θ*(1+b)*(rowProcess c false R0 X m ω).shifts) ∂μ)≤
        Real.exp ((m:ℝ)*θ/(1-ν*θ)) := by
    apply rowProcess_mgf c false R0 X hX hind (1+b) θ ν
    intro i R
    have hh := hrow i (c.prepared R) b hb
      (mixedCorrectionRule_cap ha hc hm h0 hb R) (-θ) (neg_pos.mpr hθ)
    simpa only [exactShift,Bool.false_eq_true,if_false,neg_neg,mul_neg,sub_eq_add_neg,
      neg_div,neg_mul] using hh
  refine ⟨(fun ω=>(rowProcess c false R0 X m ω).shifts),?_,?_,?_⟩
  · intro θ hθ
    simpa only [mul_assoc] using (hprocess θ hθ).1
  · intro θ hθ
    simpa only [mul_assoc] using (hprocess θ hθ).2
  · intro ω
    have hg := rowProcess_lower_sq c u hu X ω
    have hbq := hbudget ω
    dsimp [c,R0] at hg ⊢
    linarith

theorem lower_mixed_row_general_of_certificates {X : Ω→Fin n→ℝ} {K : ℝ}
    (hdata : GeneralLowerCertificateConditions) (hsg : SubGaussianMGF μ X K)
    (hiso : CentredIsotropic μ X) (hK : 1≤K) :
    MixedLowerRowEstimate (μ:=μ) X (K^2)
      (fun k=>K^2*logParameter K*generalLowerProfile k)
      ((499/100:ℝ)*K^2*logParameter K) := by
  intro R b hb hcap ℓ hℓ
  have hc : K^2*Matrix.trace R.1+K^2*logParameter K*frobenius R.1*
      generalLowerProfile (spectralRatio R.1 R.2)≤b := by
    change K^2*Matrix.trace R.1+frobenius R.1*(K^2*logParameter K*
      generalLowerProfile (spectralRatio R.1 R.2))≤b at hcap
    nlinarith only [hcap]
  exact lowerShift_general_laplace_of_certificates hdata hsg hiso hK R.2 hc hb hℓ.le

theorem lower_mixed_row_one_of_certificates {X : Ω→Fin n→ℝ}
    (htable : Certificates.EndpointTableConditions) (hfar : Certificates.EndpointFarConditions)
    (hsg : SubGaussianMGF μ X 1) (hiso : CentredIsotropic μ X) :
    MixedLowerRowEstimate (μ:=μ) X 1 (fun k=>min (2*k) (73/50)) (5/2) := by
  intro R b hb hcap ℓ hℓ
  have hc : Matrix.trace R.1+frobenius R.1*min (2*spectralRatio R.1 R.2) (73/50)≤b := by
    simpa only [mixedCost,one_mul] using hcap
  exact lowerShift_endpoint_laplace_of_certificates htable hfar hsg hiso R.2 hc hb hℓ.le

/-- The actual mixed construction discharges the complete pathwise budget;
only the stated row estimates remain as an intermediate analytic input. -/
def mixedLowerTransferInput
    (X : Fin m→Ω→Fin n→ℝ) (hX : ∀i,Measurable (X i)) (hind : iIndepFun X μ)
    {a : ℝ} (ha : 0≤a) {h : ℝ→ℝ} (hc : Continuous h)
    (hm : MonotoneOn h (Icc (0:ℝ) 1)) (h0 : ∀k∈Icc (0:ℝ) 1,0≤h k)
    (hp : ∀k∈Ioc (0:ℝ) 1,0<h k)
    (hside : h 1≤2*(∫k in (0:ℝ)..1,h k)) {b : ℝ} (hb : 0<b)
    (ν : ℝ) (hrow : ∀i,MixedLowerRowEstimate (μ:=μ) (X i) a h ν) :
    LowerTransferInput μ X (a*n+2*profileAngularCost h*Real.sqrt n) ν b := by
  let u := mixedInitialDistance n a h b
  have hu : 0<u := mixedInitialDistance_pos (NeZero.pos n) ha hp hb
  apply mixedLowerTransferInput_of_budget X hX hind ha hc hm h0 hb hu hrow
  intro ω
  have hh := mixed_process_total_cost (ι:=Fin n) ha hc hm h0 hp hside hb false
    (fun j=>spectralRow X j ω) m
  simpa only [Fintype.card_fin,rowProcess,u] using hh

end
end SingularValueBounds.KL
