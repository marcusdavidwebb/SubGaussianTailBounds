import SingularValueBounds.KL.Certificates.EndpointAnalyticLogs
import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.IntegerResolventEvaluation

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SingularValueBounds.KL.Certificates

namespace EndpointAnalyticSmall00
private noncomputable def weights : IntegerLookupTree := (.leaf (155480510400000:ℤ))
private noncomputable def prefactors : IntegerLookupTree := (.leaf (2718349789616264:ℤ))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 0) 8000 (endpointSmallRuns 0) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 0, EndpointRunConditions (endpointSmallCutoff 0) (endpointSmallK 0) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 0, roundUpQ (endpointSmall24Argument (endpointSmallK 0) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 0, endpointSmall24Q (endpointSmallK 0) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 0, endpointRunWeightQ (endpointSmallCutoff 0) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 0) = (91488579/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 0 = (logRoundedQ ((endpointSmallCutoff 0:ℚ)/200)).2+(91488579/200000000000000:ℚ)+((endpointSmallRuns 0).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 0).map (fun r => endpointRunWeightQ (endpointSmallCutoff 0) r*endpointSmall24Q (endpointSmallK 0) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 0).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 0≤endpointSmallTarget 0 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 0 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall00

namespace EndpointAnalyticSmall01
private noncomputable def weights : IntegerLookupTree := (.leaf (155480510400000:ℤ))
private noncomputable def prefactors : IntegerLookupTree := (.leaf (2718553706757538:ℤ))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 1) 8000 (endpointSmallRuns 1) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 1, EndpointRunConditions (endpointSmallCutoff 1) (endpointSmallK 1) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 1, roundUpQ (endpointSmall24Argument (endpointSmallK 1) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 1, endpointSmall24Q (endpointSmallK 1) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 1, endpointRunWeightQ (endpointSmallCutoff 1) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 1) = (91488579/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 1 = (logRoundedQ ((endpointSmallCutoff 1:ℚ)/200)).2+(91488579/200000000000000:ℚ)+((endpointSmallRuns 1).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 1).map (fun r => endpointRunWeightQ (endpointSmallCutoff 1) r*endpointSmall24Q (endpointSmallK 1) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 1).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 1≤endpointSmallTarget 1 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 1 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall01

namespace EndpointAnalyticSmall02
private noncomputable def weights : IntegerLookupTree := (.leaf (155480510400000:ℤ))
private noncomputable def prefactors : IntegerLookupTree := (.leaf (2718893694388716:ℤ))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 2) 8000 (endpointSmallRuns 2) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 2, EndpointRunConditions (endpointSmallCutoff 2) (endpointSmallK 2) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 2, roundUpQ (endpointSmall24Argument (endpointSmallK 2) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 2, endpointSmall24Q (endpointSmallK 2) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 2, endpointRunWeightQ (endpointSmallCutoff 2) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 2) = (91488579/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 2 = (logRoundedQ ((endpointSmallCutoff 2:ℚ)/200)).2+(91488579/200000000000000:ℚ)+((endpointSmallRuns 2).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 2).map (fun r => endpointRunWeightQ (endpointSmallCutoff 2) r*endpointSmall24Q (endpointSmallK 2) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 2).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 2≤endpointSmallTarget 2 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 2 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall02

namespace EndpointAnalyticSmall03
private noncomputable def weights : IntegerLookupTree := (.leaf (155480510400000:ℤ))
private noncomputable def prefactors : IntegerLookupTree := (.leaf (2719369939223222:ℤ))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 3) 8000 (endpointSmallRuns 3) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 3, EndpointRunConditions (endpointSmallCutoff 3) (endpointSmallK 3) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 3, roundUpQ (endpointSmall24Argument (endpointSmallK 3) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 3, endpointSmall24Q (endpointSmallK 3) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 3, endpointRunWeightQ (endpointSmallCutoff 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 3) = (91488579/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 3 = (logRoundedQ ((endpointSmallCutoff 3:ℚ)/200)).2+(91488579/200000000000000:ℚ)+((endpointSmallRuns 3).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 3).map (fun r => endpointRunWeightQ (endpointSmallCutoff 3) r*endpointSmall24Q (endpointSmallK 3) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 3).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 3≤endpointSmallTarget 3 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall03

namespace EndpointAnalyticSmall04
private noncomputable def weights : IntegerLookupTree := (.leaf (155480510400000:ℤ))
private noncomputable def prefactors : IntegerLookupTree := (.leaf (2719982703653604:ℤ))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 4) 8000 (endpointSmallRuns 4) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 4, EndpointRunConditions (endpointSmallCutoff 4) (endpointSmallK 4) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 4, roundUpQ (endpointSmall24Argument (endpointSmallK 4) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 4, endpointSmall24Q (endpointSmallK 4) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 4, endpointRunWeightQ (endpointSmallCutoff 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 4) = (91488579/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 4 = (logRoundedQ ((endpointSmallCutoff 4:ℚ)/200)).2+(91488579/200000000000000:ℚ)+((endpointSmallRuns 4).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 4).map (fun r => endpointRunWeightQ (endpointSmallCutoff 4) r*endpointSmall24Q (endpointSmallK 4) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 4).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 4≤endpointSmallTarget 4 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall04

namespace EndpointAnalyticSmall05
private noncomputable def weights : IntegerLookupTree := (.leaf (155480510400000:ℤ))
private noncomputable def prefactors : IntegerLookupTree := (.leaf (2720732325727960:ℤ))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 5) 8000 (endpointSmallRuns 5) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 5, EndpointRunConditions (endpointSmallCutoff 5) (endpointSmallK 5) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 5, roundUpQ (endpointSmall24Argument (endpointSmallK 5) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 5, endpointSmall24Q (endpointSmallK 5) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 5, endpointRunWeightQ (endpointSmallCutoff 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 5) = (91488579/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 5 = (logRoundedQ ((endpointSmallCutoff 5:ℚ)/200)).2+(91488579/200000000000000:ℚ)+((endpointSmallRuns 5).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 5).map (fun r => endpointRunWeightQ (endpointSmallCutoff 5) r*endpointSmall24Q (endpointSmallK 5) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 5).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 5≤endpointSmallTarget 5 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall05

namespace EndpointAnalyticSmall06
private noncomputable def weights : IntegerLookupTree := (.leaf (155480510400000:ℤ))
private noncomputable def prefactors : IntegerLookupTree := (.leaf (2721619219640858:ℤ))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 6) 8000 (endpointSmallRuns 6) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 6, EndpointRunConditions (endpointSmallCutoff 6) (endpointSmallK 6) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 6, roundUpQ (endpointSmall24Argument (endpointSmallK 6) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 6, endpointSmall24Q (endpointSmallK 6) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 6, endpointRunWeightQ (endpointSmallCutoff 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 6) = (91488579/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 6 = (logRoundedQ ((endpointSmallCutoff 6:ℚ)/200)).2+(91488579/200000000000000:ℚ)+((endpointSmallRuns 6).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 6).map (fun r => endpointRunWeightQ (endpointSmallCutoff 6) r*endpointSmall24Q (endpointSmallK 6) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 6).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 6≤endpointSmallTarget 6 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall06

namespace EndpointAnalyticSmall07
private noncomputable def weights : IntegerLookupTree := (.leaf (155480510400000:ℤ))
private noncomputable def prefactors : IntegerLookupTree := (.leaf (2722643876293935:ℤ))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 7) 8000 (endpointSmallRuns 7) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 7, EndpointRunConditions (endpointSmallCutoff 7) (endpointSmallK 7) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 7, roundUpQ (endpointSmall24Argument (endpointSmallK 7) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 7, endpointSmall24Q (endpointSmallK 7) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 7, endpointRunWeightQ (endpointSmallCutoff 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 7) = (91488579/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 7 = (logRoundedQ ((endpointSmallCutoff 7:ℚ)/200)).2+(91488579/200000000000000:ℚ)+((endpointSmallRuns 7).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 7).map (fun r => endpointRunWeightQ (endpointSmallCutoff 7) r*endpointSmall24Q (endpointSmallK 7) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 7).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 7≤endpointSmallTarget 7 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall07

namespace EndpointAnalyticSmall08
private noncomputable def weights : IntegerLookupTree := (.leaf (155480510400000:ℤ))
private noncomputable def prefactors : IntegerLookupTree := (.leaf (2723806864019965:ℤ))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 8) 8000 (endpointSmallRuns 8) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 8, EndpointRunConditions (endpointSmallCutoff 8) (endpointSmallK 8) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 8, roundUpQ (endpointSmall24Argument (endpointSmallK 8) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 8, endpointSmall24Q (endpointSmallK 8) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 8, endpointRunWeightQ (endpointSmallCutoff 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 8) = (91488579/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 8 = (logRoundedQ ((endpointSmallCutoff 8:ℚ)/200)).2+(91488579/200000000000000:ℚ)+((endpointSmallRuns 8).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 8).map (fun r => endpointRunWeightQ (endpointSmallCutoff 8) r*endpointSmall24Q (endpointSmallK 8) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 8).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 8≤endpointSmallTarget 8 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall08

namespace EndpointAnalyticSmall09
private noncomputable def weights : IntegerLookupTree := (.leaf (154633868600000:ℤ))
private noncomputable def prefactors : IntegerLookupTree := (.leaf (2725108829400492:ℤ))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 9) 8000 (endpointSmallRuns 9) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 9, EndpointRunConditions (endpointSmallCutoff 9) (endpointSmallK 9) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 9, roundUpQ (endpointSmall24Argument (endpointSmallK 9) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 9, endpointSmall24Q (endpointSmallK 9) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 9, endpointRunWeightQ (endpointSmallCutoff 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 9) = (457176113/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 9 = (logRoundedQ ((endpointSmallCutoff 9:ℚ)/200)).2+(457176113/1000000000000000:ℚ)+((endpointSmallRuns 9).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 9).map (fun r => endpointRunWeightQ (endpointSmallCutoff 9) r*endpointSmall24Q (endpointSmallK 9) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 9).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 9≤endpointSmallTarget 9 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall09

namespace EndpointAnalyticSmall10
private noncomputable def weights : IntegerLookupTree := (.leaf (154633868600000:ℤ))
private noncomputable def prefactors : IntegerLookupTree := (.leaf (2726550498200357:ℤ))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 10) 8000 (endpointSmallRuns 10) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 10, EndpointRunConditions (endpointSmallCutoff 10) (endpointSmallK 10) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 10, roundUpQ (endpointSmall24Argument (endpointSmallK 10) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 10, endpointSmall24Q (endpointSmallK 10) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 10, endpointRunWeightQ (endpointSmallCutoff 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 10) = (457176113/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 10 = (logRoundedQ ((endpointSmallCutoff 10:ℚ)/200)).2+(457176113/1000000000000000:ℚ)+((endpointSmallRuns 10).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 10).map (fun r => endpointRunWeightQ (endpointSmallCutoff 10) r*endpointSmall24Q (endpointSmallK 10) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 10).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 10≤endpointSmallTarget 10 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall10

namespace EndpointAnalyticSmall11
private noncomputable def weights : IntegerLookupTree := (.branch 6111 (.leaf (154633868600000:ℤ)) (.leaf (100000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2660298543605349:ℤ)) (.leaf (2728132676434720:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 11) 8000 (endpointSmallRuns 11) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 11, EndpointRunConditions (endpointSmallCutoff 11) (endpointSmallK 11) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 11, roundUpQ (endpointSmall24Argument (endpointSmallK 11) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 11, endpointSmall24Q (endpointSmallK 11) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 11, endpointRunWeightQ (endpointSmallCutoff 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 11) = (457176113/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 11 = (logRoundedQ ((endpointSmallCutoff 11:ℚ)/200)).2+(457176113/1000000000000000:ℚ)+((endpointSmallRuns 11).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 11).map (fun r => endpointRunWeightQ (endpointSmallCutoff 11) r*endpointSmall24Q (endpointSmallK 11) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 11).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 11≤endpointSmallTarget 11 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall11

namespace EndpointAnalyticSmall12
private noncomputable def weights : IntegerLookupTree := (.branch 6111 (.leaf (154633868600000:ℤ)) (.leaf (100000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2300034869559789:ℤ)) (.leaf (2729856251548893:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 12) 8000 (endpointSmallRuns 12) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 12, EndpointRunConditions (endpointSmallCutoff 12) (endpointSmallK 12) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 12, roundUpQ (endpointSmall24Argument (endpointSmallK 12) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 12, endpointSmall24Q (endpointSmallK 12) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 12, endpointRunWeightQ (endpointSmallCutoff 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 12) = (457176113/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 12 = (logRoundedQ ((endpointSmallCutoff 12:ℚ)/200)).2+(457176113/1000000000000000:ℚ)+((endpointSmallRuns 12).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 12).map (fun r => endpointRunWeightQ (endpointSmallCutoff 12) r*endpointSmall24Q (endpointSmallK 12) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 12).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 12≤endpointSmallTarget 12 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall12

namespace EndpointAnalyticSmall13
private noncomputable def weights : IntegerLookupTree := (.branch 6111 (.leaf (153792072700000:ℤ)) (.leaf (100000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2301115550277266:ℤ)) (.leaf (2731722193724790:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 13) 8000 (endpointSmallRuns 13) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 13, EndpointRunConditions (endpointSmallCutoff 13) (endpointSmallK 13) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 13, roundUpQ (endpointSmall24Argument (endpointSmallK 13) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 13, endpointSmall24Q (endpointSmallK 13) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 13, endpointRunWeightQ (endpointSmallCutoff 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 13) = (456909947/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 13 = (logRoundedQ ((endpointSmallCutoff 13:ℚ)/200)).2+(456909947/1000000000000000:ℚ)+((endpointSmallRuns 13).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 13).map (fun r => endpointRunWeightQ (endpointSmallCutoff 13) r*endpointSmall24Q (endpointSmallK 13) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 13).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 13≤endpointSmallTarget 13 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall13

namespace EndpointAnalyticSmall14
private noncomputable def weights : IntegerLookupTree := (.branch 6111 (.leaf (153792072700000:ℤ)) (.leaf (100000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2302278661693020:ℤ)) (.leaf (2733731557320028:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 14) 8000 (endpointSmallRuns 14) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 14, EndpointRunConditions (endpointSmallCutoff 14) (endpointSmallK 14) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 14, roundUpQ (endpointSmall24Argument (endpointSmallK 14) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 14, endpointSmall24Q (endpointSmallK 14) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 14, endpointRunWeightQ (endpointSmallCutoff 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 14) = (456909947/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 14 = (logRoundedQ ((endpointSmallCutoff 14:ℚ)/200)).2+(456909947/1000000000000000:ℚ)+((endpointSmallRuns 14).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 14).map (fun r => endpointRunWeightQ (endpointSmallCutoff 14) r*endpointSmall24Q (endpointSmallK 14) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 14).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 14≤endpointSmallTarget 14 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall14

namespace EndpointAnalyticSmall15
private noncomputable def weights : IntegerLookupTree := (.branch 5801 (.leaf (153792072700000:ℤ)) (.leaf (200000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2338718151222087:ℤ)) (.leaf (2735885482435816:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 15) 8000 (endpointSmallRuns 15) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 15, EndpointRunConditions (endpointSmallCutoff 15) (endpointSmallK 15) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 15, roundUpQ (endpointSmall24Argument (endpointSmallK 15) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 15, endpointSmall24Q (endpointSmallK 15) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 15, endpointRunWeightQ (endpointSmallCutoff 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 15) = (456909947/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 15 = (logRoundedQ ((endpointSmallCutoff 15:ℚ)/200)).2+(456909947/1000000000000000:ℚ)+((endpointSmallRuns 15).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 15).map (fun r => endpointRunWeightQ (endpointSmallCutoff 15) r*endpointSmall24Q (endpointSmallK 15) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 15).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 15≤endpointSmallTarget 15 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall15

namespace EndpointAnalyticSmall16
private noncomputable def weights : IntegerLookupTree := (.branch 5459 (.leaf (152955092400000:ℤ)) (.leaf (800000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2328302804148764:ℤ)) (.leaf (2738185196624560:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 16) 8000 (endpointSmallRuns 16) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 16, EndpointRunConditions (endpointSmallCutoff 16) (endpointSmallK 16) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 16, roundUpQ (endpointSmall24Argument (endpointSmallK 16) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 16, endpointSmall24Q (endpointSmallK 16) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 16, endpointRunWeightQ (endpointSmallCutoff 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 16) = (91328879/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 16 = (logRoundedQ ((endpointSmallCutoff 16:ℚ)/200)).2+(91328879/200000000000000:ℚ)+((endpointSmallRuns 16).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 16).map (fun r => endpointRunWeightQ (endpointSmallCutoff 16) r*endpointSmall24Q (endpointSmallK 16) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 16).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 16≤endpointSmallTarget 16 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall16

namespace EndpointAnalyticSmall17
private noncomputable def weights : IntegerLookupTree := (.branch 5156 (.leaf (152955092400000:ℤ)) (.leaf (3700000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2283010939802013:ℤ)) (.leaf (2740632016743854:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 17) 8000 (endpointSmallRuns 17) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 17, EndpointRunConditions (endpointSmallCutoff 17) (endpointSmallK 17) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 17, roundUpQ (endpointSmall24Argument (endpointSmallK 17) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 17, endpointSmall24Q (endpointSmallK 17) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 17, endpointRunWeightQ (endpointSmallCutoff 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 17) = (91328879/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 17 = (logRoundedQ ((endpointSmallCutoff 17:ℚ)/200)).2+(91328879/200000000000000:ℚ)+((endpointSmallRuns 17).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 17).map (fun r => endpointRunWeightQ (endpointSmallCutoff 17) r*endpointSmall24Q (endpointSmallK 17) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 17).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 17≤endpointSmallTarget 17 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall17

namespace EndpointAnalyticSmall18
private noncomputable def weights : IntegerLookupTree := (.branch 4885 (.leaf (152122897700000:ℤ)) (.leaf (14600000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2249944845936041:ℤ)) (.leaf (2743227350952140:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 18) 8000 (endpointSmallRuns 18) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 18, EndpointRunConditions (endpointSmallCutoff 18) (endpointSmallK 18) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 18, roundUpQ (endpointSmall24Argument (endpointSmallK 18) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 18, endpointSmall24Q (endpointSmallK 18) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 18, endpointRunWeightQ (endpointSmallCutoff 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 18) = (91275891/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 18 = (logRoundedQ ((endpointSmallCutoff 18:ℚ)/200)).2+(91275891/200000000000000:ℚ)+((endpointSmallRuns 18).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 18).map (fun r => endpointRunWeightQ (endpointSmallCutoff 18) r*endpointSmall24Q (endpointSmallK 18) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 18).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 18≤endpointSmallTarget 18 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall18

namespace EndpointAnalyticSmall19
private noncomputable def weights : IntegerLookupTree := (.branch 4641 (.leaf (152122897500000:ℤ)) (.leaf (51600000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2217338333095890:ℤ)) (.leaf (2745972700862310:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 19) 8000 (endpointSmallRuns 19) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 19, EndpointRunConditions (endpointSmallCutoff 19) (endpointSmallK 19) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 19, roundUpQ (endpointSmall24Argument (endpointSmallK 19) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 19, endpointSmall24Q (endpointSmallK 19) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 19, endpointRunWeightQ (endpointSmallCutoff 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 19) = (91275891/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 19 = (logRoundedQ ((endpointSmallCutoff 19:ℚ)/200)).2+(91275891/200000000000000:ℚ)+((endpointSmallRuns 19).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 19).map (fun r => endpointRunWeightQ (endpointSmallCutoff 19) r*endpointSmall24Q (endpointSmallK 19) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 19).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 19≤endpointSmallTarget 19 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall19

namespace EndpointAnalyticSmall20
private noncomputable def weights : IntegerLookupTree := (.branch 4420 (.leaf (151295458100000:ℤ)) (.leaf (166400000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2185180231163268:ℤ)) (.leaf (2748869663854059:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 20) 8000 (endpointSmallRuns 20) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 20, EndpointRunConditions (endpointSmallCutoff 20) (endpointSmallK 20) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 20, roundUpQ (endpointSmall24Argument (endpointSmallK 20) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 20, endpointSmall24Q (endpointSmallK 20) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 20, endpointRunWeightQ (endpointSmallCutoff 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 20) = (456115123/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 20 = (logRoundedQ ((endpointSmallCutoff 20:ℚ)/200)).2+(456115123/1000000000000000:ℚ)+((endpointSmallRuns 20).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 20).map (fun r => endpointRunWeightQ (endpointSmallCutoff 20) r*endpointSmall24Q (endpointSmallK 20) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 20).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 20≤endpointSmallTarget 20 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall20

namespace EndpointAnalyticSmall21
private noncomputable def weights : IntegerLookupTree := (.branch 4219 (.leaf (151295456700000:ℤ)) (.leaf (490200000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2153460005962900:ℤ)) (.leaf (2751919935556862:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 21) 8000 (endpointSmallRuns 21) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 21, EndpointRunConditions (endpointSmallCutoff 21) (endpointSmallK 21) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 21, roundUpQ (endpointSmall24Argument (endpointSmallK 21) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 21, endpointSmall24Q (endpointSmallK 21) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 21, endpointRunWeightQ (endpointSmallCutoff 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 21) = (456115123/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 21 = (logRoundedQ ((endpointSmallCutoff 21:ℚ)/200)).2+(456115123/1000000000000000:ℚ)+((endpointSmallRuns 21).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 21).map (fun r => endpointRunWeightQ (endpointSmallCutoff 21) r*endpointSmall24Q (endpointSmallK 21) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 21).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 21≤endpointSmallTarget 21 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall21

namespace EndpointAnalyticSmall22
private noncomputable def weights : IntegerLookupTree := (.branch 4035 (.leaf (150472740900000:ℤ)) (.leaf (1194100000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2133020246461572:ℤ)) (.leaf (2755125312501661:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 22) 8000 (endpointSmallRuns 22) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 22, EndpointRunConditions (endpointSmallCutoff 22) (endpointSmallK 22) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 22, roundUpQ (endpointSmall24Argument (endpointSmallK 22) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 22, endpointSmall24Q (endpointSmallK 22) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 22, endpointRunWeightQ (endpointSmallCutoff 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 22) = (113962849/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 22 = (logRoundedQ ((endpointSmallCutoff 22:ℚ)/200)).2+(113962849/250000000000000:ℚ)+((endpointSmallRuns 22).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 22).map (fun r => endpointRunWeightQ (endpointSmallCutoff 22) r*endpointSmall24Q (endpointSmallK 22) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 22).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 22≤endpointSmallTarget 22 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall22

namespace EndpointAnalyticSmall23
private noncomputable def weights : IntegerLookupTree := (.branch 3867 (.leaf (150472733700000:ℤ)) (.leaf (2708100000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2112768765028124:ℤ)) (.leaf (2758487694961135:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 23) 8000 (endpointSmallRuns 23) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 23, EndpointRunConditions (endpointSmallCutoff 23) (endpointSmallK 23) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 23, roundUpQ (endpointSmall24Argument (endpointSmallK 23) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 23, endpointSmall24Q (endpointSmallK 23) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 23, endpointRunWeightQ (endpointSmallCutoff 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 23) = (113962849/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 23 = (logRoundedQ ((endpointSmallCutoff 23:ℚ)/200)).2+(113962849/250000000000000:ℚ)+((endpointSmallRuns 23).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 23).map (fun r => endpointRunWeightQ (endpointSmallCutoff 23) r*endpointSmall24Q (endpointSmallK 23) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 23).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 23≤endpointSmallTarget 23 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall23

namespace EndpointAnalyticSmall24
private noncomputable def weights : IntegerLookupTree := (.branch 3713 (.leaf (149654703500000:ℤ)) (.leaf (5753800000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2092700636798935:ℤ)) (.leaf (2762009089977946:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 24) 8000 (endpointSmallRuns 24) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 24, EndpointRunConditions (endpointSmallCutoff 24) (endpointSmallK 24) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 24, roundUpQ (endpointSmall24Argument (endpointSmallK 24) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 24, endpointSmall24Q (endpointSmallK 24) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 24, endpointRunWeightQ (endpointSmallCutoff 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 24) = (28474267/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 24 = (logRoundedQ ((endpointSmallCutoff 24:ℚ)/200)).2+(28474267/62500000000000:ℚ)+((endpointSmallRuns 24).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 24).map (fun r => endpointRunWeightQ (endpointSmallCutoff 24) r*endpointSmall24Q (endpointSmallK 24) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 24).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 24≤endpointSmallTarget 24 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall24

namespace EndpointAnalyticSmall25
private noncomputable def weights : IntegerLookupTree := (.branch 3570 (.leaf (149654675300000:ℤ)) (.leaf (11602000000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2072811179476445:ℤ)) (.leaf (2765691614595944:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 25) 8000 (endpointSmallRuns 25) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 25, EndpointRunConditions (endpointSmallCutoff 25) (endpointSmallK 25) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 25, roundUpQ (endpointSmall24Argument (endpointSmallK 25) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 25, endpointSmall24Q (endpointSmallK 25) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 25, endpointRunWeightQ (endpointSmallCutoff 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 25) = (28474267/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 25 = (logRoundedQ ((endpointSmallCutoff 25:ℚ)/200)).2+(28474267/62500000000000:ℚ)+((endpointSmallRuns 25).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 25).map (fun r => endpointRunWeightQ (endpointSmallCutoff 25) r*endpointSmall24Q (endpointSmallK 25) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 25).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 25≤endpointSmallTarget 25 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall25

namespace EndpointAnalyticSmall26
private noncomputable def weights : IntegerLookupTree := (.branch 3438 (.leaf (148841276700000:ℤ)) (.leaf (22194000000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2053095945662941:ℤ)) (.leaf (2769537499301232:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 26) 8000 (endpointSmallRuns 26) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 26, EndpointRunConditions (endpointSmallCutoff 26) (endpointSmallK 26) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 26, roundUpQ (endpointSmall24Argument (endpointSmallK 26) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 26, endpointSmall24Q (endpointSmallK 26) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 26, endpointRunWeightQ (endpointSmallCutoff 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 26) = (455325749/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 26 = (logRoundedQ ((endpointSmallCutoff 26:ℚ)/200)).2+(455325749/1000000000000000:ℚ)+((endpointSmallRuns 26).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 26).map (fun r => endpointRunWeightQ (endpointSmallCutoff 26) r*endpointSmall24Q (endpointSmallK 26) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 26).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 26≤endpointSmallTarget 26 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall26

namespace EndpointAnalyticSmall27
private noncomputable def weights : IntegerLookupTree := (.branch 3315 (.leaf (148032479400000:ℤ)) (.leaf (37135900000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2044033323283120:ℤ)) (.leaf (2773549091686273:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 27) 8000 (endpointSmallRuns 27) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 27, EndpointRunConditions (endpointSmallCutoff 27) (endpointSmallK 27) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 27, roundUpQ (endpointSmall24Argument (endpointSmallK 27) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 27, endpointSmall24Q (endpointSmallK 27) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 27, endpointRunWeightQ (endpointSmallCutoff 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 27) = (227531911/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 27 = (logRoundedQ ((endpointSmallCutoff 27:ℚ)/200)).2+(227531911/500000000000000:ℚ)+((endpointSmallRuns 27).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 27).map (fun r => endpointRunWeightQ (endpointSmallCutoff 27) r*endpointSmall24Q (endpointSmallK 27) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 27).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 27≤endpointSmallTarget 27 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall27

namespace EndpointAnalyticSmall28
private noncomputable def weights : IntegerLookupTree := (.branch 3201 (.leaf (148032332700000:ℤ)) (.leaf (59919900000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2035026793730419:ℤ)) (.leaf (2777728860348451:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 28) 8000 (endpointSmallRuns 28) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 28, EndpointRunConditions (endpointSmallCutoff 28) (endpointSmallK 28) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 28, roundUpQ (endpointSmall24Argument (endpointSmallK 28) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 28, endpointSmall24Q (endpointSmallK 28) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 28, endpointRunWeightQ (endpointSmallCutoff 28) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 28) = (227531911/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 28 = (logRoundedQ ((endpointSmallCutoff 28:ℚ)/200)).2+(227531911/500000000000000:ℚ)+((endpointSmallRuns 28).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 28).map (fun r => endpointRunWeightQ (endpointSmallCutoff 28) r*endpointSmall24Q (endpointSmallK 28) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 28).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 28≤endpointSmallTarget 28 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 28 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall28

namespace EndpointAnalyticSmall29
private noncomputable def weights : IntegerLookupTree := (.branch 3094 (.leaf (147227998600000:ℤ)) (.leaf (102080500000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2015645092065473:ℤ)) (.leaf (2782079399033982:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 29) 8000 (endpointSmallRuns 29) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 29, EndpointRunConditions (endpointSmallCutoff 29) (endpointSmallK 29) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 29, roundUpQ (endpointSmall24Argument (endpointSmallK 29) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 29, endpointSmall24Q (endpointSmallK 29) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 29, endpointRunWeightQ (endpointSmallCutoff 29) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 29) = (45480249/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 29 = (logRoundedQ ((endpointSmallCutoff 29:ℚ)/200)).2+(45480249/100000000000000:ℚ)+((endpointSmallRuns 29).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 29).map (fun r => endpointRunWeightQ (endpointSmallCutoff 29) r*endpointSmall24Q (endpointSmallK 29) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 29).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 29≤endpointSmallTarget 29 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 29 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall29

namespace EndpointAnalyticSmall30
private noncomputable def weights : IntegerLookupTree := (.branch 2994 (.leaf (146428117400000:ℤ)) (.leaf (154816700000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (2006770606840768:ℤ)) (.leaf (2786603431043894:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 30) 8000 (endpointSmallRuns 30) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 30, EndpointRunConditions (endpointSmallCutoff 30) (endpointSmallK 30) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 30, roundUpQ (endpointSmall24Argument (endpointSmallK 30) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 30, endpointSmall24Q (endpointSmallK 30) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 30, endpointRunWeightQ (endpointSmallCutoff 30) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 30) = (1818167/4000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 30 = (logRoundedQ ((endpointSmallCutoff 30:ℚ)/200)).2+(1818167/4000000000000:ℚ)+((endpointSmallRuns 30).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 30).map (fun r => endpointRunWeightQ (endpointSmallCutoff 30) r*endpointSmall24Q (endpointSmallK 30) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 30).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 30≤endpointSmallTarget 30 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 30 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall30

namespace EndpointAnalyticSmall31
private noncomputable def weights : IntegerLookupTree := (.branch 2901 (.leaf (146427574300000:ℤ)) (.leaf (228398200000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (1997945844645254:ℤ)) (.leaf (2791303813914762:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 31) 8000 (endpointSmallRuns 31) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 31, EndpointRunConditions (endpointSmallCutoff 31) (endpointSmallK 31) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 31, roundUpQ (endpointSmall24Argument (endpointSmallK 31) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 31, endpointSmall24Q (endpointSmallK 31) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 31, endpointRunWeightQ (endpointSmallCutoff 31) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 31) = (1818167/4000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 31 = (logRoundedQ ((endpointSmallCutoff 31:ℚ)/200)).2+(1818167/4000000000000:ℚ)+((endpointSmallRuns 31).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 31).map (fun r => endpointRunWeightQ (endpointSmallCutoff 31) r*endpointSmall24Q (endpointSmallK 31) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 31).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 31≤endpointSmallTarget 31 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 31 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall31

namespace EndpointAnalyticSmall32
private noncomputable def weights : IntegerLookupTree := (.branch 2813 (.leaf (145631814100000:ℤ)) (.leaf (329605400000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (1989168995862059:ℤ)) (.leaf (2796183544390951:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 32) 8000 (endpointSmallRuns 32) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 32, EndpointRunConditions (endpointSmallCutoff 32) (endpointSmallK 32) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 32, roundUpQ (endpointSmall24Argument (endpointSmallK 32) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 32, endpointSmall24Q (endpointSmallK 32) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 32, endpointRunWeightQ (endpointSmallCutoff 32) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 32) = (141963/312500000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 32 = (logRoundedQ ((endpointSmallCutoff 32:ℚ)/200)).2+(141963/312500000000:ℚ)+((endpointSmallRuns 32).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 32).map (fun r => endpointRunWeightQ (endpointSmallCutoff 32) r*endpointSmall24Q (endpointSmallK 32) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 32).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 32≤endpointSmallTarget 32 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 32 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall32

namespace EndpointAnalyticSmall33
private noncomputable def weights : IntegerLookupTree := (.branch 2730 (.leaf (144840237900000:ℤ)) (.leaf (465829400000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (1980438298542703:ℤ)) (.leaf (2801245763705204:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 33) 8000 (endpointSmallRuns 33) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 33, EndpointRunConditions (endpointSmallCutoff 33) (endpointSmallK 33) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 33, roundUpQ (endpointSmall24Argument (endpointSmallK 33) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 33, endpointSmall24Q (endpointSmallK 33) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 33, endpointRunWeightQ (endpointSmallCutoff 33) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 33) = (113505509/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 33 = (logRoundedQ ((endpointSmallCutoff 33:ℚ)/200)).2+(113505509/250000000000000:ℚ)+((endpointSmallRuns 33).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 33).map (fun r => endpointRunWeightQ (endpointSmallCutoff 33) r*endpointSmall24Q (endpointSmallK 33) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 33).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 33≤endpointSmallTarget 33 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 33 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall33

namespace EndpointAnalyticSmall34
private noncomputable def weights : IntegerLookupTree := (.branch 2652 (.leaf (144052717000000:ℤ)) (.leaf (645014300000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (1971752037294529:ℤ)) (.leaf (2806493763187467:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 34) 8000 (endpointSmallRuns 34) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 34, EndpointRunConditions (endpointSmallCutoff 34) (endpointSmallK 34) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 34, roundUpQ (endpointSmall24Argument (endpointSmallK 34) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 34, endpointSmall24Q (endpointSmallK 34) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 34, endpointRunWeightQ (endpointSmallCutoff 34) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 34) = (28360191/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 34 = (logRoundedQ ((endpointSmallCutoff 34:ℚ)/200)).2+(28360191/62500000000000:ℚ)+((endpointSmallRuns 34).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 34).map (fun r => endpointRunWeightQ (endpointSmallCutoff 34) r*endpointSmall24Q (endpointSmallK 34) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 34).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 34≤endpointSmallTarget 34 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 34 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall34

namespace EndpointAnalyticSmall35
private noncomputable def weights : IntegerLookupTree := (.branch 2578 (.leaf (144050544900000:ℤ)) (.leaf (878866500000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (1963108542230167:ℤ)) (.leaf (2811930990219925:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 35) 8000 (endpointSmallRuns 35) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 35, EndpointRunConditions (endpointSmallCutoff 35) (endpointSmallK 35) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 35, roundUpQ (endpointSmall24Argument (endpointSmallK 35) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 35, endpointSmall24Q (endpointSmallK 35) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 35, endpointRunWeightQ (endpointSmallCutoff 35) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 35) = (28360191/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 35 = (logRoundedQ ((endpointSmallCutoff 35:ℚ)/200)).2+(28360191/62500000000000:ℚ)+((endpointSmallRuns 35).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 35).map (fun r => endpointRunWeightQ (endpointSmallCutoff 35) r*endpointSmall24Q (endpointSmallK 35) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 35).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 35≤endpointSmallTarget 35 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 35 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall35

namespace EndpointAnalyticSmall36
private noncomputable def weights : IntegerLookupTree := (.branch 2509 (.leaf (143266217200000:ℤ)) (.leaf (1173235300000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (1954506187978309:ℤ)) (.leaf (2817561054561529:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 36) 8000 (endpointSmallRuns 36) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 36, EndpointRunConditions (endpointSmallCutoff 36) (endpointSmallK 36) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 36, roundUpQ (endpointSmall24Argument (endpointSmallK 36) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 36, endpointSmall24Q (endpointSmallK 36) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 36, endpointRunWeightQ (endpointSmallCutoff 36) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 36) = (453504657/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 36 = (logRoundedQ ((endpointSmallCutoff 36:ℚ)/200)).2+(453504657/1000000000000000:ℚ)+((endpointSmallRuns 36).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 36).map (fun r => endpointRunWeightQ (endpointSmallCutoff 36) r*endpointSmall24Q (endpointSmallK 36) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 36).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 36≤endpointSmallTarget 36 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 36 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall36

namespace EndpointAnalyticSmall37
private noncomputable def weights : IntegerLookupTree := (.branch 2443 (.leaf (142485401700000:ℤ)) (.leaf (1545918000000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (1945943392752224:ℤ)) (.leaf (2823387735064560:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 37) 8000 (endpointSmallRuns 37) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 37, EndpointRunConditions (endpointSmallCutoff 37) (endpointSmallK 37) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 37, roundUpQ (endpointSmall24Argument (endpointSmallK 37) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 37, endpointSmall24Q (endpointSmallK 37) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 37, endpointRunWeightQ (endpointSmallCutoff 37) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 37) = (453246837/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 37 = (logRoundedQ ((endpointSmallCutoff 37:ℚ)/200)).2+(453246837/1000000000000000:ℚ)+((endpointSmallRuns 37).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 37).map (fun r => endpointRunWeightQ (endpointSmallCutoff 37) r*endpointSmall24Q (endpointSmallK 37) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 37).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 37≤endpointSmallTarget 37 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 37 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall37

namespace EndpointAnalyticSmall38
private noncomputable def weights : IntegerLookupTree := (.branch 2380 (.leaf (141707852800000:ℤ)) (.leaf (2011103700000:ℤ)))
private noncomputable def prefactors : IntegerLookupTree := (.branch 200 (.leaf (1937418617474506:ℤ)) (.leaf (2829414986808714:ℤ)))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 38) 8000 (endpointSmallRuns 38) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 38, EndpointRunConditions (endpointSmallCutoff 38) (endpointSmallK 38) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 38, roundUpQ (endpointSmall24Argument (endpointSmallK 38) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 38, endpointSmall24Q (endpointSmallK 38) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 38, endpointRunWeightQ (endpointSmallCutoff 38) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 38) = (452989593/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 38 = (logRoundedQ ((endpointSmallCutoff 38:ℚ)/200)).2+(452989593/1000000000000000:ℚ)+((endpointSmallRuns 38).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 38).map (fun r => endpointRunWeightQ (endpointSmallCutoff 38) r*endpointSmall24Q (endpointSmallK 38) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 38).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 38≤endpointSmallTarget 38 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 38 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall38

namespace EndpointAnalyticSmall39
private noncomputable def weights : IntegerLookupTree := (.branch 2321 (.leaf (140933426100000:ℤ)) (.branch 3315 (.leaf (165287900000:ℤ)) (.leaf (109185300000:ℤ))))
private noncomputable def prefactors : IntegerLookupTree := (.branch 170 (.leaf (1939124456044394:ℤ)) (.branch 200 (.leaf (2411576791051574:ℤ)) (.leaf (2835646948679591:ℤ))))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 39) 8000 (endpointSmallRuns 39) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 39, EndpointRunConditions (endpointSmallCutoff 39) (endpointSmallK 39) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 39, roundUpQ (endpointSmall24Argument (endpointSmallK 39) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 39, endpointSmall24Q (endpointSmallK 39) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 39, endpointRunWeightQ (endpointSmallCutoff 39) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 39) = (226366461/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 39 = (logRoundedQ ((endpointSmallCutoff 39:ℚ)/200)).2+(226366461/500000000000000:ℚ)+((endpointSmallRuns 39).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 39).map (fun r => endpointRunWeightQ (endpointSmallCutoff 39) r*endpointSmall24Q (endpointSmallK 39) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 39).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 39≤endpointSmallTarget 39 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 39 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall39

namespace EndpointAnalyticSmall40
private noncomputable def weights : IntegerLookupTree := (.branch 2264 (.leaf (140161640000000:ℤ)) (.branch 3234 (.leaf (208294400000:ℤ)) (.leaf (153685300000:ℤ))))
private noncomputable def prefactors : IntegerLookupTree := (.branch 170 (.leaf (1930650056837753:ℤ)) (.branch 200 (.leaf (2415463999976818:ℤ)) (.leaf (2842087951421598:ℤ))))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 40) 8000 (endpointSmallRuns 40) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 40, EndpointRunConditions (endpointSmallCutoff 40) (endpointSmallK 40) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 40, roundUpQ (endpointSmall24Argument (endpointSmallK 40) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 40, endpointSmall24Q (endpointSmallK 40) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 40, endpointRunWeightQ (endpointSmallCutoff 40) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 40) = (452476823/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 40 = (logRoundedQ ((endpointSmallCutoff 40:ℚ)/200)).2+(452476823/1000000000000000:ℚ)+((endpointSmallRuns 40).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 40).map (fun r => endpointRunWeightQ (endpointSmallCutoff 40) r*endpointSmall24Q (endpointSmallK 40) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 40).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 40≤endpointSmallTarget 40 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 40 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall40

namespace EndpointAnalyticSmall41
private noncomputable def weights : IntegerLookupTree := (.branch 2210 (.leaf (139392310700000:ℤ)) (.branch 3157 (.leaf (259184000000:ℤ)) (.leaf (212779200000:ℤ))))
private noncomputable def prefactors : IntegerLookupTree := (.branch 170 (.leaf (1922209634253635:ℤ)) (.branch 200 (.leaf (2419473598067857:ℤ)) (.leaf (2848742526196529:ℤ))))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 41) 8000 (endpointSmallRuns 41) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 41, EndpointRunConditions (endpointSmallCutoff 41) (endpointSmallK 41) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 41, roundUpQ (endpointSmall24Argument (endpointSmallK 41) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 41, endpointSmall24Q (endpointSmallK 41) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 41, endpointRunWeightQ (endpointSmallCutoff 41) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 41) = (113055323/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 41 = (logRoundedQ ((endpointSmallCutoff 41:ℚ)/200)).2+(113055323/250000000000000:ℚ)+((endpointSmallRuns 41).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 41).map (fun r => endpointRunWeightQ (endpointSmallCutoff 41) r*endpointSmall24Q (endpointSmallK 41) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 41).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 41≤endpointSmallTarget 41 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 41 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall41

namespace EndpointAnalyticSmall42
private noncomputable def weights : IntegerLookupTree := (.branch 2159 (.leaf (138625181800000:ℤ)) (.branch 3084 (.leaf (318454200000:ℤ)) (.leaf (289862700000:ℤ))))
private noncomputable def prefactors : IntegerLookupTree := (.branch 170 (.leaf (1913801789613875:ℤ)) (.branch 200 (.leaf (2423607812220807:ℤ)) (.leaf (2855615413681701:ℤ))))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 42) 8000 (endpointSmallRuns 42) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 42, EndpointRunConditions (endpointSmallCutoff 42) (endpointSmallK 42) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 42, roundUpQ (endpointSmall24Argument (endpointSmallK 42) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 42, endpointSmall24Q (endpointSmallK 42) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 42, endpointRunWeightQ (endpointSmallCutoff 42) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 42) = (451966327/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 42 = (logRoundedQ ((endpointSmallCutoff 42:ℚ)/200)).2+(451966327/1000000000000000:ℚ)+((endpointSmallRuns 42).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 42).map (fun r => endpointRunWeightQ (endpointSmallCutoff 42) r*endpointSmall24Q (endpointSmallK 42) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 42).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 42≤endpointSmallTarget 42 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 42 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall42

namespace EndpointAnalyticSmall43
private noncomputable def weights : IntegerLookupTree := (.branch 2110 (.leaf (137859702100000:ℤ)) (.branch 3013 (.leaf (387917500000:ℤ)) (.leaf (359685400000:ℤ))))
private noncomputable def prefactors : IntegerLookupTree := (.branch 170 (.leaf (1915595456652701:ℤ)) (.branch 200 (.leaf (2427868963139516:ℤ)) (.leaf (2862711573747050:ℤ))))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 43) 8000 (endpointSmallRuns 43) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 43, EndpointRunConditions (endpointSmallCutoff 43) (endpointSmallK 43) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 43, roundUpQ (endpointSmall24Argument (endpointSmallK 43) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 43, endpointSmall24Q (endpointSmallK 43) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 43, endpointRunWeightQ (endpointSmallCutoff 43) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 43) = (225855963/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 43 = (logRoundedQ ((endpointSmallCutoff 43:ℚ)/200)).2+(225855963/500000000000000:ℚ)+((endpointSmallRuns 43).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 43).map (fun r => endpointRunWeightQ (endpointSmallCutoff 43) r*endpointSmall24Q (endpointSmallK 43) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 43).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 43≤endpointSmallTarget 43 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 43 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall43

namespace EndpointAnalyticSmall44
private noncomputable def weights : IntegerLookupTree := (.branch 2063 (.leaf (137095468500000:ℤ)) (.branch 2947 (.leaf (468629500000:ℤ)) (.leaf (476976800000:ℤ))))
private noncomputable def prefactors : IntegerLookupTree := (.branch 170 (.leaf (1907228949159568:ℤ)) (.branch 200 (.leaf (2432259469076993:ℤ)) (.leaf (2870036195747893:ℤ))))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 44) 8000 (endpointSmallRuns 44) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 44, EndpointRunConditions (endpointSmallCutoff 44) (endpointSmallK 44) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 44, roundUpQ (endpointSmall24Argument (endpointSmallK 44) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 44, endpointSmall24Q (endpointSmallK 44) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 44, endpointRunWeightQ (endpointSmallCutoff 44) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 44) = (90291617/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 44 = (logRoundedQ ((endpointSmallCutoff 44:ℚ)/200)).2+(90291617/200000000000000:ℚ)+((endpointSmallRuns 44).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 44).map (fun r => endpointRunWeightQ (endpointSmallCutoff 44) r*endpointSmall24Q (endpointSmallK 44) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 44).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 44≤endpointSmallTarget 44 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 44 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall44

namespace EndpointAnalyticSmall45
private noncomputable def weights : IntegerLookupTree := (.branch 2018 (.leaf (136332079200000:ℤ)) (.branch 3104 (.leaf (756825100000:ℤ)) (.leaf (296469300000:ℤ))))
private noncomputable def prefactors : IntegerLookupTree := (.branch 165 (.leaf (1909082403678967:ℤ)) (.branch 200 (.leaf (2370847966201299:ℤ)) (.leaf (2877594709480994:ℤ))))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 45) 8000 (endpointSmallRuns 45) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 45, EndpointRunConditions (endpointSmallCutoff 45) (endpointSmallK 45) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 45, roundUpQ (endpointSmall24Argument (endpointSmallK 45) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 45, endpointSmall24Q (endpointSmallK 45) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 45, endpointRunWeightQ (endpointSmallCutoff 45) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 45) = (451204803/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 45 = (logRoundedQ ((endpointSmallCutoff 45:ℚ)/200)).2+(451204803/1000000000000000:ℚ)+((endpointSmallRuns 45).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 45).map (fun r => endpointRunWeightQ (endpointSmallCutoff 45) r*endpointSmall24Q (endpointSmallK 45) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 45).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 45≤endpointSmallTarget 45 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 45 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall45

namespace EndpointAnalyticSmall46
private noncomputable def weights : IntegerLookupTree := (.branch 1975 (.leaf (135569150300000:ℤ)) (.branch 3038 (.leaf (894999800000:ℤ)) (.leaf (393512600000:ℤ))))
private noncomputable def prefactors : IntegerLookupTree := (.branch 165 (.leaf (1900753323123183:ℤ)) (.branch 200 (.leaf (2375099239660951:ℤ)) (.leaf (2885392796848453:ℤ))))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 46) 8000 (endpointSmallRuns 46) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 46, EndpointRunConditions (endpointSmallCutoff 46) (endpointSmallK 46) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 46, roundUpQ (endpointSmall24Argument (endpointSmallK 46) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 46, endpointSmall24Q (endpointSmallK 46) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 46, endpointRunWeightQ (endpointSmallCutoff 46) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 46) = (225476039/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 46 = (logRoundedQ ((endpointSmallCutoff 46:ℚ)/200)).2+(225476039/500000000000000:ℚ)+((endpointSmallRuns 46).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 46).map (fun r => endpointRunWeightQ (endpointSmallCutoff 46) r*endpointSmall24Q (endpointSmallK 46) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 46).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 46≤endpointSmallTarget 46 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 46 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall46

namespace EndpointAnalyticSmall47
private noncomputable def weights : IntegerLookupTree := (.branch 1934 (.leaf (134806335400000:ℤ)) (.branch 2975 (.leaf (1049783600000:ℤ)) (.leaf (474980700000:ℤ))))
private noncomputable def prefactors : IntegerLookupTree := (.branch 165 (.leaf (1902665189258179:ℤ)) (.branch 200 (.leaf (2379474453481283:ℤ)) (.leaf (2893436404282211:ℤ))))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 47) 8000 (endpointSmallRuns 47) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 47, EndpointRunConditions (endpointSmallCutoff 47) (endpointSmallK 47) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 47, roundUpQ (endpointSmall24Argument (endpointSmallK 47) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 47, endpointSmall24Q (endpointSmallK 47) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 47, endpointRunWeightQ (endpointSmallCutoff 47) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 47) = (90139981/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 47 = (logRoundedQ ((endpointSmallCutoff 47:ℚ)/200)).2+(90139981/200000000000000:ℚ)+((endpointSmallRuns 47).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 47).map (fun r => endpointRunWeightQ (endpointSmallCutoff 47) r*endpointSmall24Q (endpointSmallK 47) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 47).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 47≤endpointSmallTarget 47 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 47 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall47

namespace EndpointAnalyticSmall48
private noncomputable def weights : IntegerLookupTree := (.branch 1894 (.leaf (134042411900000:ℤ)) (.branch 2914 (.leaf (1226158500000:ℤ)) (.leaf (617973700000:ℤ))))
private noncomputable def prefactors : IntegerLookupTree := (.branch 165 (.leaf (1894369712978879:ℤ)) (.branch 200 (.leaf (2383976090495647:ℤ)) (.leaf (2901731755984791:ℤ))))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 48) 8000 (endpointSmallRuns 48) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 48, EndpointRunConditions (endpointSmallCutoff 48) (endpointSmallK 48) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 48, roundUpQ (endpointSmall24Argument (endpointSmallK 48) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 48, endpointSmall24Q (endpointSmallK 48) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 48, endpointRunWeightQ (endpointSmallCutoff 48) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 48) = (112612071/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 48 = (logRoundedQ ((endpointSmallCutoff 48:ℚ)/200)).2+(112612071/250000000000000:ℚ)+((endpointSmallRuns 48).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 48).map (fun r => endpointRunWeightQ (endpointSmallCutoff 48) r*endpointSmall24Q (endpointSmallK 48) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 48).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 48≤endpointSmallTarget 48 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 48 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall48

namespace EndpointAnalyticSmall49
private noncomputable def weights : IntegerLookupTree := (.branch 1857 (.leaf (133278865800000:ℤ)) (.branch 2856 (.leaf (1414881900000:ℤ)) (.leaf (733518500000:ℤ))))
private noncomputable def prefactors : IntegerLookupTree := (.branch 165 (.leaf (1896338659139275:ℤ)) (.branch 200 (.leaf (2388606735912029:ℤ)) (.leaf (2910285368046952:ℤ))))
private theorem cover : EndpointRunsCover (endpointSmallCutoff 49) 8000 (endpointSmallRuns 49) := by decide +kernel
private theorem domains : ∀r∈endpointSmallRuns 49, EndpointRunConditions (endpointSmallCutoff 49) (endpointSmallK 49) r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀r∈endpointSmallRuns 49, roundUpQ (endpointSmall24Argument (endpointSmallK 49) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointSmall24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀r∈endpointSmallRuns 49, endpointSmall24Q (endpointSmallK 49) ((r.rate:ℚ)/100) = fixedQ (prefactors.get r.rate) := by
  simp only [endpointSmall24Q,endpointSmall24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointSmallRuns 49, endpointRunWeightQ (endpointSmallCutoff 49) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointSmallCutoff 49) = (112549303/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : endpointSmallNumeric 49 = (logRoundedQ ((endpointSmallCutoff 49:ℚ)/200)).2+(112549303/250000000000000:ℚ)+((endpointSmallRuns 49).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate))).sum := by
  have hm : (endpointSmallRuns 49).map (fun r => endpointRunWeightQ (endpointSmallCutoff 49) r*endpointSmall24Q (endpointSmallK 49) ((r.rate:ℚ)/100)) =
      (endpointSmallRuns 49).map (fun r => fixedQ (weights.get r.start)*fixedQ (prefactors.get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues r hr]
  unfold endpointSmallNumeric
  rw [hm,tailValue]
private theorem totals : endpointSmallNumeric 49≤endpointSmallTarget 49 := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointSmallNumericalConditions 49 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticSmall49

end SingularValueBounds.KL.Certificates
