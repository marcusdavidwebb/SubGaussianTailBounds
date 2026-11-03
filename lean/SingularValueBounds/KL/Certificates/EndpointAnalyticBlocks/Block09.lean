import SingularValueBounds.KL.Certificates.EndpointAnalyticLogs
import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.IntegerResolventEvaluation

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SingularValueBounds.KL.Certificates

namespace EndpointAnalyticJoint54_32
private noncomputable def weights : IntegerLookupTree := (.leaf (93301537600000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3126470671931403:ℤ)), (.leaf (3147640462880750:ℤ)), (.leaf (3360531984049704:ℤ)), (.leaf (3385925364945037:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 54 32) 8000 (endpointMeanRuns 54 32) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 54 32, EndpointRunConditions (endpointMeanCutoff 54 32) (endpointMeanBox 54 32).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 54 32, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 54 32 h) (endpointMeanCornerA 54 32 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 54 32, endpointJoint24Q (endpointMeanCornerK 54 32 h) (endpointMeanCornerA 54 32 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 54 32, endpointRunWeightQ (endpointMeanCutoff 54 32) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 54 32) = (41698207/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 54 32 h = (logRoundedQ ((endpointMeanCutoff 54 32:ℚ)/200)).2+(41698207/125000000000000:ℚ)+((endpointMeanRuns 54 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 54 32).map (fun r => endpointRunWeightQ (endpointMeanCutoff 54 32) r*endpointJoint24Q (endpointMeanCornerK 54 32 h) (endpointMeanCornerA 54 32 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 54 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 54 32 h≤endpointMeanCorner 54 32 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 54 32 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint54_32

namespace EndpointAnalyticJoint54_33
private noncomputable def weights : IntegerLookupTree := (.leaf (91552735100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3147640462880750:ℤ)), (.leaf (3210389510202996:ℤ)), (.leaf (3385925364945037:ℤ)), (.leaf (3461309004445914:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 54 33) 8000 (endpointMeanRuns 54 33) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 54 33, EndpointRunConditions (endpointMeanCutoff 54 33) (endpointMeanBox 54 33).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 54 33, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 54 33 h) (endpointMeanCornerA 54 33 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 54 33, endpointJoint24Q (endpointMeanCornerK 54 33 h) (endpointMeanCornerA 54 33 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 54 33, endpointRunWeightQ (endpointMeanCutoff 54 33) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 54 33) = (166474951/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 54 33 h = (logRoundedQ ((endpointMeanCutoff 54 33:ℚ)/200)).2+(166474951/500000000000000:ℚ)+((endpointMeanRuns 54 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 54 33).map (fun r => endpointRunWeightQ (endpointMeanCutoff 54 33) r*endpointJoint24Q (endpointMeanCornerK 54 33 h) (endpointMeanCornerA 54 33 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 54 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 54 33 h≤endpointMeanCorner 54 33 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 54 33 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint54_33

namespace EndpointAnalyticJoint54_34
private noncomputable def weights : IntegerLookupTree := (.leaf (89837390000000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3210389510202996:ℤ)), (.leaf (3231582619932890:ℤ)), (.leaf (3461309004445914:ℤ)), (.leaf (3486808017724146:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 54 34) 8000 (endpointMeanRuns 54 34) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 54 34, EndpointRunConditions (endpointMeanCutoff 54 34) (endpointMeanBox 54 34).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 54 34, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 54 34 h) (endpointMeanCornerA 54 34 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 54 34, endpointJoint24Q (endpointMeanCornerK 54 34 h) (endpointMeanCornerA 54 34 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 54 34, endpointRunWeightQ (endpointMeanCutoff 54 34) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 54 34) = (8307941/25000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 54 34 h = (logRoundedQ ((endpointMeanCutoff 54 34:ℚ)/200)).2+(8307941/25000000000000:ℚ)+((endpointMeanRuns 54 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 54 34).map (fun r => endpointRunWeightQ (endpointMeanCutoff 54 34) r*endpointJoint24Q (endpointMeanCornerK 54 34 h) (endpointMeanCornerA 54 34 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 54 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 54 34 h≤endpointMeanCorner 54 34 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 54 34 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint54_34

namespace EndpointAnalyticJoint54_35
private noncomputable def weights : IntegerLookupTree := (.leaf (92316993300000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3113772682267009:ℤ)), (.leaf (3152991780130162:ℤ)), (.leaf (3331968292421493:ℤ)), (.leaf (3378508947404308:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 54 35) 8000 (endpointMeanRuns 54 35) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 54 35, EndpointRunConditions (endpointMeanCutoff 54 35) (endpointMeanBox 54 35).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 54 35, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 54 35 h) (endpointMeanCornerA 54 35 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 54 35, endpointJoint24Q (endpointMeanCornerK 54 35 h) (endpointMeanCornerA 54 35 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 54 35, endpointRunWeightQ (endpointMeanCutoff 54 35) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 54 35) = (331778451/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 54 35 h = (logRoundedQ ((endpointMeanCutoff 54 35:ℚ)/200)).2+(331778451/1000000000000000:ℚ)+((endpointMeanRuns 54 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 54 35).map (fun r => endpointRunWeightQ (endpointMeanCutoff 54 35) r*endpointJoint24Q (endpointMeanCornerK 54 35 h) (endpointMeanCornerA 54 35 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 54 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 54 35 h≤endpointMeanCorner 54 35 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 54 35 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint54_35

namespace EndpointAnalyticJoint54_36
private noncomputable def weights : IntegerLookupTree := (.leaf (90361964300000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3152991780130162:ℤ)), (.leaf (3212748578417256:ℤ)), (.leaf (3378508947404308:ℤ)), (.leaf (3449541654979454:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 54 36) 8000 (endpointMeanRuns 54 36) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 54 36, EndpointRunConditions (endpointMeanCutoff 54 36) (endpointMeanBox 54 36).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 54 36, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 54 36 h) (endpointMeanCornerA 54 36 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 54 36, endpointJoint24Q (endpointMeanCornerK 54 36 h) (endpointMeanCornerA 54 36 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 54 36, endpointRunWeightQ (endpointMeanCutoff 54 36) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 54 36) = (165531719/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 54 36 h = (logRoundedQ ((endpointMeanCutoff 54 36:ℚ)/200)).2+(165531719/500000000000000:ℚ)+((endpointMeanRuns 54 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 54 36).map (fun r => endpointRunWeightQ (endpointMeanCutoff 54 36) r*endpointJoint24Q (endpointMeanCornerK 54 36 h) (endpointMeanCornerA 54 36 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 54 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 54 36 h≤endpointMeanCorner 54 36 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 54 36 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint54_36

namespace EndpointAnalyticJoint54_37
private noncomputable def weights : IntegerLookupTree := (.leaf (87742584100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3212748578417256:ℤ)), (.leaf (3273637912147044:ℤ)), (.leaf (3449541654979454:ℤ)), (.leaf (3522067815916430:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 54 37) 8000 (endpointMeanRuns 54 37) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 54 37, EndpointRunConditions (endpointMeanCutoff 54 37) (endpointMeanBox 54 37).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 54 37, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 54 37 h) (endpointMeanCornerA 54 37 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 54 37, endpointJoint24Q (endpointMeanCornerK 54 37 h) (endpointMeanCornerA 54 37 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 54 37, endpointRunWeightQ (endpointMeanCutoff 54 37) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 54 37) = (82521873/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 54 37 h = (logRoundedQ ((endpointMeanCutoff 54 37:ℚ)/200)).2+(82521873/250000000000000:ℚ)+((endpointMeanRuns 54 37).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 54 37).map (fun r => endpointRunWeightQ (endpointMeanCutoff 54 37) r*endpointJoint24Q (endpointMeanCornerK 54 37 h) (endpointMeanCornerA 54 37 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 54 37).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 54 37 h≤endpointMeanCorner 54 37 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 54 37 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint54_37

namespace EndpointAnalyticJoint54_38
private noncomputable def weights : IntegerLookupTree := (.leaf (85200637000000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3273637912147044:ℤ)), (.leaf (3335681245597490:ℤ)), (.leaf (3522067815916430:ℤ)), (.leaf (3596118829876313:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 54 38) 8000 (endpointMeanRuns 54 38) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 54 38, EndpointRunConditions (endpointMeanCutoff 54 38) (endpointMeanBox 54 38).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 54 38, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 54 38 h) (endpointMeanCornerA 54 38 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 54 38, endpointJoint24Q (endpointMeanCornerK 54 38 h) (endpointMeanCornerA 54 38 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 54 38, endpointRunWeightQ (endpointMeanCutoff 54 38) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 54 38) = (1316479/4000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 54 38 h = (logRoundedQ ((endpointMeanCutoff 54 38:ℚ)/200)).2+(1316479/4000000000000:ℚ)+((endpointMeanRuns 54 38).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 54 38).map (fun r => endpointRunWeightQ (endpointMeanCutoff 54 38) r*endpointJoint24Q (endpointMeanCornerK 54 38 h) (endpointMeanCornerA 54 38 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 54 38).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 54 38 h≤endpointMeanCorner 54 38 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 54 38 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint54_38

namespace EndpointAnalyticJoint54_39
private noncomputable def weights : IntegerLookupTree := (.leaf (86732165800000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3211224885474887:ℤ)), (.leaf (3269166133122598:ℤ)), (.leaf (3435100395479907:ℤ)), (.leaf (3503456674933095:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 54 39) 8000 (endpointMeanRuns 54 39) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 54 39, EndpointRunConditions (endpointMeanCutoff 54 39) (endpointMeanBox 54 39).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 54 39, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 54 39 h) (endpointMeanCornerA 54 39 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 54 39, endpointJoint24Q (endpointMeanCornerK 54 39 h) (endpointMeanCornerA 54 39 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 54 39, endpointRunWeightQ (endpointMeanCutoff 54 39) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 54 39) = (328246989/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 54 39 h = (logRoundedQ ((endpointMeanCutoff 54 39:ℚ)/200)).2+(328246989/1000000000000000:ℚ)+((endpointMeanRuns 54 39).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 54 39).map (fun r => endpointRunWeightQ (endpointMeanCutoff 54 39) r*endpointJoint24Q (endpointMeanCornerK 54 39 h) (endpointMeanCornerA 54 39 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 54 39).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 54 39 h≤endpointMeanCorner 54 39 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 54 39 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint54_39

namespace EndpointAnalyticJoint55_33
private noncomputable def weights : IntegerLookupTree := (.leaf (92177966900000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3172189940591665:ℤ)), (.leaf (3174754645005764:ℤ)), (.leaf (3429020120013482:ℤ)), (.leaf (3432124968958918:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 55 33) 8000 (endpointMeanRuns 55 33) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 55 33, EndpointRunConditions (endpointMeanCutoff 55 33) (endpointMeanBox 55 33).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 55 33, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 55 33 h) (endpointMeanCornerA 55 33 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 55 33, endpointJoint24Q (endpointMeanCornerK 55 33 h) (endpointMeanCornerA 55 33 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 55 33, endpointRunWeightQ (endpointMeanCutoff 55 33) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 55 33) = (330264323/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 55 33 h = (logRoundedQ ((endpointMeanCutoff 55 33:ℚ)/200)).2+(330264323/1000000000000000:ℚ)+((endpointMeanRuns 55 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 55 33).map (fun r => endpointRunWeightQ (endpointMeanCutoff 55 33) r*endpointJoint24Q (endpointMeanCornerK 55 33 h) (endpointMeanCornerA 55 33 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 55 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 55 33 h≤endpointMeanCorner 55 33 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 55 33 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint55_33

namespace EndpointAnalyticJoint55_34
private noncomputable def weights : IntegerLookupTree := (.leaf (91690865400000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3174754645005764:ℤ)), (.leaf (3195675007763299:ℤ)), (.leaf (3432124968958918:ℤ)), (.leaf (3457462516427266:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 55 34) 8000 (endpointMeanRuns 55 34) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 55 34, EndpointRunConditions (endpointMeanCutoff 55 34) (endpointMeanBox 55 34).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 55 34, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 55 34 h) (endpointMeanCornerA 55 34 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 55 34, endpointJoint24Q (endpointMeanCornerK 55 34 h) (endpointMeanCornerA 55 34 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 55 34, endpointRunWeightQ (endpointMeanCutoff 55 34) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 55 34) = (82521873/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 55 34 h = (logRoundedQ ((endpointMeanCutoff 55 34:ℚ)/200)).2+(82521873/250000000000000:ℚ)+((endpointMeanRuns 55 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 55 34).map (fun r => endpointRunWeightQ (endpointMeanCutoff 55 34) r*endpointJoint24Q (endpointMeanCornerK 55 34 h) (endpointMeanCornerA 55 34 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 55 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 55 34 h≤endpointMeanCorner 55 34 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 55 34 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint55_34

namespace EndpointAnalyticJoint55_35
private noncomputable def weights : IntegerLookupTree := (.branch 1653 (.leaf (51880494200000:ℤ)) (.leaf (41526108800000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 102 (.leaf (2867631791426592:ℤ)) (.leaf (3331968292421493:ℤ))), (.branch 102 (.leaf (2900132019568227:ℤ)) (.leaf (3378508947404308:ℤ))), (.branch 102 (.leaf (3031157089915934:ℤ)) (.leaf (3645292279163833:ℤ))), (.branch 102 (.leaf (3068912649329208:ℤ)) (.leaf (3702859205779056:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 55 35) 8000 (endpointMeanRuns 55 35) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 55 35, EndpointRunConditions (endpointMeanCutoff 55 35) (endpointMeanBox 55 35).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 55 35, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 55 35 h) (endpointMeanCornerA 55 35 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 55 35, endpointJoint24Q (endpointMeanCornerK 55 35 h) (endpointMeanCornerA 55 35 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 55 35, endpointRunWeightQ (endpointMeanCutoff 55 35) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 55 35) = (2636469/8000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 55 35 h = (logRoundedQ ((endpointMeanCutoff 55 35:ℚ)/200)).2+(2636469/8000000000000:ℚ)+((endpointMeanRuns 55 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 55 35).map (fun r => endpointRunWeightQ (endpointMeanCutoff 55 35) r*endpointJoint24Q (endpointMeanCornerK 55 35 h) (endpointMeanCornerA 55 35 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 55 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 55 35 h≤endpointMeanCorner 55 35 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 55 35 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint55_35

namespace EndpointAnalyticJoint55_36
private noncomputable def weights : IntegerLookupTree := (.leaf (92372471800000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3113050003120136:ℤ)), (.leaf (3171793366050625:ℤ)), (.leaf (3342004941509787:ℤ)), (.leaf (3412183490243550:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 55 36) 8000 (endpointMeanRuns 55 36) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 55 36, EndpointRunConditions (endpointMeanCutoff 55 36) (endpointMeanBox 55 36).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 55 36, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 55 36 h) (endpointMeanCornerA 55 36 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 55 36, endpointJoint24Q (endpointMeanCornerK 55 36 h) (endpointMeanCornerA 55 36 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 55 36, endpointRunWeightQ (endpointMeanCutoff 55 36) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 55 36) = (328857227/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 55 36 h = (logRoundedQ ((endpointMeanCutoff 55 36:ℚ)/200)).2+(328857227/1000000000000000:ℚ)+((endpointMeanRuns 55 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 55 36).map (fun r => endpointRunWeightQ (endpointMeanCutoff 55 36) r*endpointJoint24Q (endpointMeanCornerK 55 36 h) (endpointMeanCornerA 55 36 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 55 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 55 36 h≤endpointMeanCorner 55 36 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 55 36 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint55_36

namespace EndpointAnalyticJoint55_37
private noncomputable def weights : IntegerLookupTree := (.leaf (89746428400000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3171793366050625:ℤ)), (.leaf (3231645218303461:ℤ)), (.leaf (3412183490243550:ℤ)), (.leaf (3483835713848706:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 55 37) 8000 (endpointMeanRuns 55 37) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 55 37, EndpointRunConditions (endpointMeanCutoff 55 37) (endpointMeanBox 55 37).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 55 37, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 55 37 h) (endpointMeanCornerA 55 37 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 55 37, endpointJoint24Q (endpointMeanCornerK 55 37 h) (endpointMeanCornerA 55 37 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 55 37, endpointRunWeightQ (endpointMeanCutoff 55 37) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 55 37) = (327899729/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 55 37 h = (logRoundedQ ((endpointMeanCutoff 55 37:ℚ)/200)).2+(327899729/1000000000000000:ℚ)+((endpointMeanRuns 55 37).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 55 37).map (fun r => endpointRunWeightQ (endpointMeanCutoff 55 37) r*endpointJoint24Q (endpointMeanCornerK 55 37 h) (endpointMeanCornerA 55 37 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 55 37).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 55 37 h≤endpointMeanCorner 55 37 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 55 37 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint55_37

namespace EndpointAnalyticJoint55_38
private noncomputable def weights : IntegerLookupTree := (.leaf (87196522100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3231645218303461:ℤ)), (.leaf (3292626477111100:ℤ)), (.leaf (3483835713848706:ℤ)), (.leaf (3556992557929943:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 55 38) 8000 (endpointMeanRuns 55 38) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 55 38, EndpointRunConditions (endpointMeanCutoff 55 38) (endpointMeanBox 55 38).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 55 38, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 55 38 h) (endpointMeanCornerA 55 38 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 55 38, endpointJoint24Q (endpointMeanCornerK 55 38 h) (endpointMeanCornerA 55 38 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 55 38, endpointRunWeightQ (endpointMeanCutoff 55 38) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 55 38) = (326950131/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 55 38 h = (logRoundedQ ((endpointMeanCutoff 55 38:ℚ)/200)).2+(326950131/1000000000000000:ℚ)+((endpointMeanRuns 55 38).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 55 38).map (fun r => endpointRunWeightQ (endpointMeanCutoff 55 38) r*endpointJoint24Q (endpointMeanCornerK 55 38 h) (endpointMeanCornerA 55 38 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 55 38).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 55 38 h≤endpointMeanCorner 55 38 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 55 38 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint55_38

namespace EndpointAnalyticJoint55_39
private noncomputable def weights : IntegerLookupTree := (.leaf (88886291900000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3165432567729534:ℤ)), (.leaf (3222167615242461:ℤ)), (.leaf (3390674564752839:ℤ)), (.leaf (3457864806509868:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 55 39) 8000 (endpointMeanRuns 55 39) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 55 39, EndpointRunConditions (endpointMeanCutoff 55 39) (endpointMeanBox 55 39).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 55 39, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 55 39 h) (endpointMeanCornerA 55 39 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 55 39, endpointJoint24Q (endpointMeanCornerK 55 39 h) (endpointMeanCornerA 55 39 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 55 39, endpointRunWeightQ (endpointMeanCutoff 55 39) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 55 39) = (81523401/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 55 39 h = (logRoundedQ ((endpointMeanCutoff 55 39:ℚ)/200)).2+(81523401/250000000000000:ℚ)+((endpointMeanRuns 55 39).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 55 39).map (fun r => endpointRunWeightQ (endpointMeanCutoff 55 39) r*endpointJoint24Q (endpointMeanCornerK 55 39 h) (endpointMeanCornerA 55 39 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 55 39).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 55 39 h≤endpointMeanCorner 55 39 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 55 39 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint55_39

namespace EndpointAnalyticJoint55_40
private noncomputable def weights : IntegerLookupTree := (.leaf (86386689000000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3222167615242461:ℤ)), (.leaf (3279919542928132:ℤ)), (.leaf (3457864806509868:ℤ)), (.leaf (3526386502672548:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 55 40) 8000 (endpointMeanRuns 55 40) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 55 40, EndpointRunConditions (endpointMeanCutoff 55 40) (endpointMeanBox 55 40).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 55 40, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 55 40 h) (endpointMeanCornerA 55 40 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 55 40, endpointJoint24Q (endpointMeanCornerK 55 40 h) (endpointMeanCornerA 55 40 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 55 40, endpointRunWeightQ (endpointMeanCutoff 55 40) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 55 40) = (40644841/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 55 40 h = (logRoundedQ ((endpointMeanCutoff 55 40:ℚ)/200)).2+(40644841/125000000000000:ℚ)+((endpointMeanRuns 55 40).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 55 40).map (fun r => endpointRunWeightQ (endpointMeanCutoff 55 40) r*endpointJoint24Q (endpointMeanCornerK 55 40 h) (endpointMeanCornerA 55 40 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 55 40).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 55 40 h≤endpointMeanCorner 55 40 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 55 40 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint55_40

namespace EndpointAnalyticJoint56_36
private noncomputable def weights : IntegerLookupTree := (.leaf (94227958500000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3085769228877112:ℤ)), (.leaf (3126429584770545:ℤ)), (.leaf (3320071150478006:ℤ)), (.leaf (3368883393541824:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 56 36) 8000 (endpointMeanRuns 56 36) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 56 36, EndpointRunConditions (endpointMeanCutoff 56 36) (endpointMeanBox 56 36).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 56 36, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 56 36 h) (endpointMeanCornerA 56 36 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 56 36, endpointJoint24Q (endpointMeanCornerK 56 36 h) (endpointMeanCornerA 56 36 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 56 36, endpointRunWeightQ (endpointMeanCutoff 56 36) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 56 36) = (326521071/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 56 36 h = (logRoundedQ ((endpointMeanCutoff 56 36:ℚ)/200)).2+(326521071/1000000000000000:ℚ)+((endpointMeanRuns 56 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 56 36).map (fun r => endpointRunWeightQ (endpointMeanCutoff 56 36) r*endpointJoint24Q (endpointMeanCornerK 56 36 h) (endpointMeanCornerA 56 36 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 56 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 56 36 h≤endpointMeanCorner 56 36 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 56 36 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint56_36

namespace EndpointAnalyticJoint56_37
private noncomputable def weights : IntegerLookupTree := (.leaf (92073821700000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3126429584770545:ℤ)), (.leaf (3185024490894197:ℤ)), (.leaf (3368883393541824:ℤ)), (.leaf (3439354046530164:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 56 37) 8000 (endpointMeanRuns 56 37) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 56 37, EndpointRunConditions (endpointMeanCutoff 56 37) (endpointMeanBox 56 37).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 56 37, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 56 37 h) (endpointMeanCornerA 56 37 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 56 37, endpointJoint24Q (endpointMeanCornerK 56 37 h) (endpointMeanCornerA 56 37 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 56 37, endpointRunWeightQ (endpointMeanCutoff 56 37) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 56 37) = (32575277/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 56 37 h = (logRoundedQ ((endpointMeanCutoff 56 37:ℚ)/200)).2+(32575277/100000000000000:ℚ)+((endpointMeanRuns 56 37).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 56 37).map (fun r => endpointRunWeightQ (endpointMeanCutoff 56 37) r*endpointJoint24Q (endpointMeanCornerK 56 37 h) (endpointMeanCornerA 56 37 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 56 37).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 56 37 h≤endpointMeanCorner 56 37 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 56 37 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint56_37

namespace EndpointAnalyticJoint56_38
private noncomputable def weights : IntegerLookupTree := (.leaf (89509082000000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3185024490894197:ℤ)), (.leaf (3244717570807004:ℤ)), (.leaf (3439354046530164:ℤ)), (.leaf (3511298811962445:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 56 38) 8000 (endpointMeanRuns 56 38) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 56 38, EndpointRunConditions (endpointMeanCutoff 56 38) (endpointMeanBox 56 38).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 56 38, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 56 38 h) (endpointMeanCornerA 56 38 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 56 38, endpointJoint24Q (endpointMeanCornerK 56 38 h) (endpointMeanCornerA 56 38 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 56 38, endpointRunWeightQ (endpointMeanCutoff 56 38) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 56 38) = (324820647/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 56 38 h = (logRoundedQ ((endpointMeanCutoff 56 38:ℚ)/200)).2+(324820647/1000000000000000:ℚ)+((endpointMeanRuns 56 38).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 56 38).map (fun r => endpointRunWeightQ (endpointMeanCutoff 56 38) r*endpointJoint24Q (endpointMeanCornerK 56 38 h) (endpointMeanCornerA 56 38 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 56 38).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 56 38 h≤endpointMeanCorner 56 38 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 56 38 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint56_38

namespace EndpointAnalyticJoint56_39
private noncomputable def weights : IntegerLookupTree := (.leaf (91138311200000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3115309691356258:ℤ)), (.leaf (3170635501475496:ℤ)), (.leaf (3340395154959347:ℤ)), (.leaf (3406134275610754:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 56 39) 8000 (endpointMeanRuns 56 39) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 56 39, EndpointRunConditions (endpointMeanCutoff 56 39) (endpointMeanBox 56 39).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 56 39, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 56 39 h) (endpointMeanCornerA 56 39 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 56 39, endpointJoint24Q (endpointMeanCornerK 56 39 h) (endpointMeanCornerA 56 39 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 56 39, endpointRunWeightQ (endpointMeanCutoff 56 39) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 56 39) = (323896011/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 56 39 h = (logRoundedQ ((endpointMeanCutoff 56 39:ℚ)/200)).2+(323896011/1000000000000000:ℚ)+((endpointMeanRuns 56 39).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 56 39).map (fun r => endpointRunWeightQ (endpointMeanCutoff 56 39) r*endpointJoint24Q (endpointMeanCornerK 56 39 h) (endpointMeanCornerA 56 39 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 56 39).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 56 39 h≤endpointMeanCorner 56 39 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 56 39 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint56_39

namespace EndpointAnalyticJoint56_40
private noncomputable def weights : IntegerLookupTree := (.leaf (88626191400000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3170635501475496:ℤ)), (.leaf (3226943860865461:ℤ)), (.leaf (3406134275610754:ℤ)), (.leaf (3473167144990534:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 56 40) 8000 (endpointMeanRuns 56 40) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 56 40, EndpointRunConditions (endpointMeanCutoff 56 40) (endpointMeanBox 56 40).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 56 40, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 56 40 h) (endpointMeanCornerA 56 40 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 56 40, endpointJoint24Q (endpointMeanCornerK 56 40 h) (endpointMeanCornerA 56 40 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 56 40, endpointRunWeightQ (endpointMeanCutoff 56 40) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 56 40) = (161489371/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 56 40 h = (logRoundedQ ((endpointMeanCutoff 56 40:ℚ)/200)).2+(161489371/500000000000000:ℚ)+((endpointMeanRuns 56 40).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 56 40).map (fun r => endpointRunWeightQ (endpointMeanCutoff 56 40) r*endpointJoint24Q (endpointMeanCornerK 56 40 h) (endpointMeanCornerA 56 40 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 56 40).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 56 40 h≤endpointMeanCorner 56 40 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 56 40 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint56_40

namespace EndpointAnalyticJoint57_37
private noncomputable def weights : IntegerLookupTree := (.leaf (93800033100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3114337989576153:ℤ)), (.leaf (3133492151660633:ℤ)), (.leaf (3364851763118666:ℤ)), (.leaf (3387995692089367:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 57 37) 8000 (endpointMeanRuns 57 37) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 57 37, EndpointRunConditions (endpointMeanCutoff 57 37) (endpointMeanBox 57 37).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 57 37, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 57 37 h) (endpointMeanCornerA 57 37 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 57 37, endpointJoint24Q (endpointMeanCornerK 57 37 h) (endpointMeanCornerA 57 37 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 57 37, endpointRunWeightQ (endpointMeanCutoff 57 37) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 57 37) = (323311449/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 57 37 h = (logRoundedQ ((endpointMeanCutoff 57 37:ℚ)/200)).2+(323311449/1000000000000000:ℚ)+((endpointMeanRuns 57 37).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 57 37).map (fun r => endpointRunWeightQ (endpointMeanCutoff 57 37) r*endpointJoint24Q (endpointMeanCornerK 57 37 h) (endpointMeanCornerA 57 37 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 57 37).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 57 37 h≤endpointMeanCorner 57 37 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 57 37 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint57_37

namespace EndpointAnalyticJoint57_38
private noncomputable def weights : IntegerLookupTree := (.leaf (96586090900000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3007911631680127:ℤ)), (.leaf (3060694193594472:ℤ)), (.leaf (3221108454919101:ℤ)), (.leaf (3283872849531028:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 57 38) 8000 (endpointMeanRuns 57 38) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 57 38, EndpointRunConditions (endpointMeanCutoff 57 38) (endpointMeanBox 57 38).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 57 38, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 57 38 h) (endpointMeanCornerA 57 38 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 57 38, endpointJoint24Q (endpointMeanCornerK 57 38 h) (endpointMeanCornerA 57 38 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 57 38, endpointRunWeightQ (endpointMeanCutoff 57 38) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 57 38) = (322729841/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 57 38 h = (logRoundedQ ((endpointMeanCutoff 57 38:ℚ)/200)).2+(322729841/1000000000000000:ℚ)+((endpointMeanRuns 57 38).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 57 38).map (fun r => endpointRunWeightQ (endpointMeanCutoff 57 38) r*endpointJoint24Q (endpointMeanCornerK 57 38 h) (endpointMeanCornerA 57 38 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 57 38).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 57 38 h≤endpointMeanCorner 57 38 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 57 38 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint57_38

namespace EndpointAnalyticJoint57_39
private noncomputable def weights : IntegerLookupTree := (.leaf (93975993900000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3060694193594472:ℤ)), (.leaf (3114402979142814:ℤ)), (.leaf (3283872849531028:ℤ)), (.leaf (3347860229735069:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 57 39) 8000 (endpointMeanRuns 57 39) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 57 39, EndpointRunConditions (endpointMeanCutoff 57 39) (endpointMeanBox 57 39).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 57 39, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 57 39 h) (endpointMeanCornerA 57 39 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 57 39, endpointJoint24Q (endpointMeanCornerK 57 39 h) (endpointMeanCornerA 57 39 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 57 39, endpointRunWeightQ (endpointMeanCutoff 57 39) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 57 39) = (321821781/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 57 39 h = (logRoundedQ ((endpointMeanCutoff 57 39:ℚ)/200)).2+(321821781/1000000000000000:ℚ)+((endpointMeanRuns 57 39).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 57 39).map (fun r => endpointRunWeightQ (endpointMeanCutoff 57 39) r*endpointJoint24Q (endpointMeanCornerK 57 39 h) (endpointMeanCornerA 57 39 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 57 39).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 57 39 h≤endpointMeanCorner 57 39 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 57 39 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint57_39

namespace EndpointAnalyticJoint57_40
private noncomputable def weights : IntegerLookupTree := (.leaf (91437828200000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3114402979142814:ℤ)), (.leaf (3169054241613915:ℤ)), (.leaf (3347860229735069:ℤ)), (.leaf (3413094425821754:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 57 40) 8000 (endpointMeanRuns 57 40) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 57 40, EndpointRunConditions (endpointMeanCutoff 57 40) (endpointMeanBox 57 40).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 57 40, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 57 40 h) (endpointMeanCornerA 57 40 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 57 40, endpointJoint24Q (endpointMeanCornerK 57 40 h) (endpointMeanCornerA 57 40 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 57 40, endpointRunWeightQ (endpointMeanCutoff 57 40) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 57 40) = (320920829/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 57 40 h = (logRoundedQ ((endpointMeanCutoff 57 40:ℚ)/200)).2+(320920829/1000000000000000:ℚ)+((endpointMeanRuns 57 40).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 57 40).map (fun r => endpointRunWeightQ (endpointMeanCutoff 57 40) r*endpointJoint24Q (endpointMeanCornerK 57 40 h) (endpointMeanCornerA 57 40 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 57 40).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 57 40 h≤endpointMeanCorner 57 40 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 57 40 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint57_40

namespace EndpointAnalyticJoint57_41
private noncomputable def weights : IntegerLookupTree := (.leaf (88969549400000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3169054241613915:ℤ)), (.leaf (3224664519507778:ℤ)), (.leaf (3413094425821754:ℤ)), (.leaf (3479599732422933:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 57 41) 8000 (endpointMeanRuns 57 41) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 57 41, EndpointRunConditions (endpointMeanCutoff 57 41) (endpointMeanBox 57 41).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 57 41, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 57 41 h) (endpointMeanCornerA 57 41 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 57 41, endpointJoint24Q (endpointMeanCornerK 57 41 h) (endpointMeanCornerA 57 41 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 57 41, endpointRunWeightQ (endpointMeanCutoff 57 41) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 57 41) = (40003359/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 57 41 h = (logRoundedQ ((endpointMeanCutoff 57 41:ℚ)/200)).2+(40003359/125000000000000:ℚ)+((endpointMeanRuns 57 41).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 57 41).map (fun r => endpointRunWeightQ (endpointMeanCutoff 57 41) r*endpointJoint24Q (endpointMeanCornerK 57 41 h) (endpointMeanCornerA 57 41 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 57 41).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 57 41 h≤endpointMeanCorner 57 41 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 57 41 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint57_41

namespace EndpointAnalyticJoint58_39
private noncomputable def weights : IntegerLookupTree := (.leaf (96962974300000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3005344660738535:ℤ)), (.leaf (3053400563798673:ℤ)), (.leaf (3225415721073741:ℤ)), (.leaf (3282777575597977:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 58 39) 8000 (endpointMeanRuns 58 39) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 58 39, EndpointRunConditions (endpointMeanCutoff 58 39) (endpointMeanBox 58 39).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 58 39, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 58 39 h) (endpointMeanCornerA 58 39 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 58 39, endpointJoint24Q (endpointMeanCornerK 58 39 h) (endpointMeanCornerA 58 39 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 58 39, endpointRunWeightQ (endpointMeanCutoff 58 39) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 58 39) = (319703511/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 58 39 h = (logRoundedQ ((endpointMeanCutoff 58 39:ℚ)/200)).2+(319703511/1000000000000000:ℚ)+((endpointMeanRuns 58 39).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 58 39).map (fun r => endpointRunWeightQ (endpointMeanCutoff 58 39) r*endpointJoint24Q (endpointMeanCornerK 58 39 h) (endpointMeanCornerA 58 39 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 58 39).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 58 39 h≤endpointMeanCorner 58 39 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 58 39 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint58_39

namespace EndpointAnalyticJoint58_40
private noncomputable def weights : IntegerLookupTree := (.leaf (94398003700000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3053400563798673:ℤ)), (.leaf (3106181697436191:ℤ)), (.leaf (3282777575597977:ℤ)), (.leaf (3345895452482681:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 58 40) 8000 (endpointMeanRuns 58 40) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 58 40, EndpointRunConditions (endpointMeanCutoff 58 40) (endpointMeanBox 58 40).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 58 40, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 58 40 h) (endpointMeanCornerA 58 40 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 58 40, endpointJoint24Q (endpointMeanCornerK 58 40 h) (endpointMeanCornerA 58 40 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 58 40, endpointRunWeightQ (endpointMeanCutoff 58 40) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 58 40) = (159409461/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 58 40 h = (logRoundedQ ((endpointMeanCutoff 58 40:ℚ)/200)).2+(159409461/500000000000000:ℚ)+((endpointMeanRuns 58 40).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 58 40).map (fun r => endpointRunWeightQ (endpointMeanCutoff 58 40) r*endpointJoint24Q (endpointMeanCornerK 58 40 h) (endpointMeanCornerA 58 40 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 58 40).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 58 40 h≤endpointMeanCorner 58 40 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 58 40 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint58_40

namespace EndpointAnalyticJoint58_41
private noncomputable def weights : IntegerLookupTree := (.leaf (91902215200000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3106181697436191:ℤ)), (.leaf (3159875206639858:ℤ)), (.leaf (3345895452482681:ℤ)), (.leaf (3410226895102709:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 58 41) 8000 (endpointMeanRuns 58 41) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 58 41, EndpointRunConditions (endpointMeanCutoff 58 41) (endpointMeanBox 58 41).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 58 41, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 58 41 h) (endpointMeanCornerA 58 41 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 58 41, endpointJoint24Q (endpointMeanCornerK 58 41 h) (endpointMeanCornerA 58 41 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 58 41, endpointRunWeightQ (endpointMeanCutoff 58 41) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 58 41) = (317941079/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 58 41 h = (logRoundedQ ((endpointMeanCutoff 58 41:ℚ)/200)).2+(317941079/1000000000000000:ℚ)+((endpointMeanRuns 58 41).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 58 41).map (fun r => endpointRunWeightQ (endpointMeanCutoff 58 41) r*endpointJoint24Q (endpointMeanCornerK 58 41 h) (endpointMeanCornerA 58 41 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 58 41).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 58 41 h≤endpointMeanCorner 58 41 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 58 41 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint58_41

namespace EndpointAnalyticJoint59_40
private noncomputable def weights : IntegerLookupTree := (.leaf (97300234900000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3013873105742343:ℤ)), (.leaf (3038385259311521:ℤ)), (.leaf (3242147576004648:ℤ)), (.leaf (3271499636504187:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 59 40) 8000 (endpointMeanRuns 59 40) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 59 40, EndpointRunConditions (endpointMeanCutoff 59 40) (endpointMeanBox 59 40).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 59 40, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 59 40 h) (endpointMeanCornerA 59 40 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 59 40, endpointJoint24Q (endpointMeanCornerK 59 40 h) (endpointMeanCornerA 59 40 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 59 40, endpointRunWeightQ (endpointMeanCutoff 59 40) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 59 40) = (79149361/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 59 40 h = (logRoundedQ ((endpointMeanCutoff 59 40:ℚ)/200)).2+(79149361/250000000000000:ℚ)+((endpointMeanRuns 59 40).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 59 40).map (fun r => endpointRunWeightQ (endpointMeanCutoff 59 40) r*endpointJoint24Q (endpointMeanCornerK 59 40 h) (endpointMeanCornerA 59 40 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 59 40).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 59 40 h≤endpointMeanCorner 59 40 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 59 40 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint59_40

namespace EndpointAnalyticJoint59_41
private noncomputable def weights : IntegerLookupTree := (.leaf (95462033400000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3038385259311521:ℤ)), (.leaf (3089950547601909:ℤ)), (.leaf (3271499636504187:ℤ)), (.leaf (3333333333333442:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 59 41) 8000 (endpointMeanRuns 59 41) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 59 41, EndpointRunConditions (endpointMeanCutoff 59 41) (endpointMeanBox 59 41).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 59 41, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 59 41 h) (endpointMeanCornerA 59 41 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 59 41, endpointJoint24Q (endpointMeanCornerK 59 41 h) (endpointMeanCornerA 59 41 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 59 41, endpointRunWeightQ (endpointMeanCutoff 59 41) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 59 41) = (315970531/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 59 41 h = (logRoundedQ ((endpointMeanCutoff 59 41:ℚ)/200)).2+(315970531/1000000000000000:ℚ)+((endpointMeanRuns 59 41).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 59 41).map (fun r => endpointRunWeightQ (endpointMeanCutoff 59 41) r*endpointJoint24Q (endpointMeanCornerK 59 41 h) (endpointMeanCornerA 59 41 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 59 41).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 59 41 h≤endpointMeanCorner 59 41 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 59 41 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint59_41

private theorem activeIndices54 : ∀ai : Fin 42, endpointMeanActive 54 ai → ai∈
    ([32, 33, 34, 35, 36, 37, 38, 39] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow54 (ai : Fin 42) : endpointMeanActive 54 ai →
    EndpointJointNumericalConditions 54 ai := by
  intro hact
  have hi := activeIndices54 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint54_32.conditions
  · exact EndpointAnalyticJoint54_33.conditions
  · exact EndpointAnalyticJoint54_34.conditions
  · exact EndpointAnalyticJoint54_35.conditions
  · exact EndpointAnalyticJoint54_36.conditions
  · exact EndpointAnalyticJoint54_37.conditions
  · exact EndpointAnalyticJoint54_38.conditions
  · exact EndpointAnalyticJoint54_39.conditions

private theorem activeIndices55 : ∀ai : Fin 42, endpointMeanActive 55 ai → ai∈
    ([33, 34, 35, 36, 37, 38, 39, 40] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow55 (ai : Fin 42) : endpointMeanActive 55 ai →
    EndpointJointNumericalConditions 55 ai := by
  intro hact
  have hi := activeIndices55 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint55_33.conditions
  · exact EndpointAnalyticJoint55_34.conditions
  · exact EndpointAnalyticJoint55_35.conditions
  · exact EndpointAnalyticJoint55_36.conditions
  · exact EndpointAnalyticJoint55_37.conditions
  · exact EndpointAnalyticJoint55_38.conditions
  · exact EndpointAnalyticJoint55_39.conditions
  · exact EndpointAnalyticJoint55_40.conditions

private theorem activeIndices56 : ∀ai : Fin 42, endpointMeanActive 56 ai → ai∈
    ([36, 37, 38, 39, 40] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow56 (ai : Fin 42) : endpointMeanActive 56 ai →
    EndpointJointNumericalConditions 56 ai := by
  intro hact
  have hi := activeIndices56 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint56_36.conditions
  · exact EndpointAnalyticJoint56_37.conditions
  · exact EndpointAnalyticJoint56_38.conditions
  · exact EndpointAnalyticJoint56_39.conditions
  · exact EndpointAnalyticJoint56_40.conditions

private theorem activeIndices57 : ∀ai : Fin 42, endpointMeanActive 57 ai → ai∈
    ([37, 38, 39, 40, 41] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow57 (ai : Fin 42) : endpointMeanActive 57 ai →
    EndpointJointNumericalConditions 57 ai := by
  intro hact
  have hi := activeIndices57 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint57_37.conditions
  · exact EndpointAnalyticJoint57_38.conditions
  · exact EndpointAnalyticJoint57_39.conditions
  · exact EndpointAnalyticJoint57_40.conditions
  · exact EndpointAnalyticJoint57_41.conditions

private theorem activeIndices58 : ∀ai : Fin 42, endpointMeanActive 58 ai → ai∈
    ([39, 40, 41] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow58 (ai : Fin 42) : endpointMeanActive 58 ai →
    EndpointJointNumericalConditions 58 ai := by
  intro hact
  have hi := activeIndices58 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint58_39.conditions
  · exact EndpointAnalyticJoint58_40.conditions
  · exact EndpointAnalyticJoint58_41.conditions

private theorem activeIndices59 : ∀ai : Fin 42, endpointMeanActive 59 ai → ai∈
    ([40, 41] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow59 (ai : Fin 42) : endpointMeanActive 59 ai →
    EndpointJointNumericalConditions 59 ai := by
  intro hact
  have hi := activeIndices59 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint59_40.conditions
  · exact EndpointAnalyticJoint59_41.conditions

end SingularValueBounds.KL.Certificates
